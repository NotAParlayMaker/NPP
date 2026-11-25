import Mathlib
import PEqualNP.Defs

-- The proof uses a finite five-input cofactor certificate and an explicit monotone circuit.

namespace PEqualNP.Outside.L_meta_12783

namespace Upper12783
open PEqualNP.CircuitLowerBounds

def index (x : Fin 6 → Bool) : ℕ := ∑ i : Fin 6, if x i then 2^(i : ℕ) else 0
def target (x : Fin 6 → Bool) := Nat.testBit (4278124266 * 2^32 + 4278124264) (index x)
def gates : List Gate := [⟨.or, [0, 1]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [8, 13]⟩]
def circuit : Circuit := ⟨gates, 14⟩

theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem size : circuit.size = 9 := rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem correct : ∀ x : Fin 6 → Bool, circuit.eval (List.ofFn x) = target x := by
  decide +kernel

end Upper12783

namespace FreeAIG
abbrev Fn (α : Type*) := α → Bool
def neg {α} (f : Fn α) : Fn α := fun x => !(f x)
def meet {α} (a b : Fn α) : Fn α := fun x => a x && b x

inductive Avail {α : Type*} (S : Set (Fn α)) : Fn α → Prop where
  | src {f} : f∈S → Avail S f
  | const (b : Bool) : Avail S (fun _ => b)
  | neg {f} : Avail S f → Avail S (FreeAIG.neg f)

inductive Has {α : Type*} : Set (Fn α) → Nat → Fn α → Prop where
  | done {S k f} : Avail S f → Has S k f
  | step {S k a b f} : Avail S a → Avail S b → Has (insert (meet a b) S) k f → Has S (k+1) f

theorem Avail.lift {α : Type*} {S T : Set (Fn α)} (h : ∀g∈S,Avail T g) {f} (p : Avail S f) :
    Avail T f := by
  induction p with
  | src hs => exact h _ hs
  | const b => exact .const b
  | neg _ ih => exact .neg ih

theorem Avail.extend {α : Type*} {S : Set (Fn α)} {a f} (p : Avail S f) :
    Avail (insert a S) f := p.lift (fun _ hs=>.src (Set.mem_insert_of_mem _ hs))

theorem Avail.map {α β : Type*} {S : Set (Fn α)} {T : Set (Fn β)} (φ : β→α)
    (h : ∀g∈S,Avail T (g∘φ)) {f} (p : Avail S f) : Avail T (f∘φ) := by
  induction p with
  | src hs => exact h _ hs
  | const b => exact .const b
  | neg _ ih => exact .neg ih

theorem Has.map {α β : Type*} {S : Set (Fn α)} {T : Set (Fn β)} (φ : β→α)
    (h : ∀g∈S,Avail T (g∘φ)) {k f} (p : Has S k f) : Has T k (f∘φ) := by
  induction p generalizing T with
  | done hp => exact .done (hp.map φ h)
  | @step S k a b f ha hb _ ih =>
    apply Has.step (ha.map φ h) (hb.map φ h)
    apply ih
    rintro g (rfl|hg)
    · exact .src (Set.mem_insert _ _)
    · exact (h g hg).extend

def Inputs {n} : Set (Fn (Fin n→Bool)) := {g | ∃ i : Fin n,g=fun x=>x i}

end FreeAIG

namespace FreeAIG
theorem meetFalseR {α} (a : Fn α) : meet a (fun _=>false)=(fun _=>false) := by funext x;simp [meet]
theorem meetTrueR {α} (a : Fn α) : meet a (fun _=>true)=a := by funext x;simp [meet]
theorem meetFalseL {α} (b : Fn α) : meet (fun _=>false) b=(fun _=>false) := by funext x;simp [meet]
theorem meetTrueL {α} (b : Fn α) : meet (fun _=>true) b=b := by funext x;simp [meet]

def Restricted {α} (φ : α→α) (f : Fn α) := f∘φ=f ∨ ∃ b : Bool, f∘φ=fun _=>b

theorem Avail.restricted {α : Type*} {φ : α→α} {S : Set (Fn α)}
    (h : ∀g∈S,Restricted φ g) {f} (p : Avail S f) : Restricted φ f := by
  induction p with
  | src hs => exact h _ hs
  | const b => exact Or.inl rfl
  | @neg g _ ih =>
    rcases ih with eq|⟨b,eq⟩
    · exact Or.inl (congrArg FreeAIG.neg eq)
    · exact Or.inr ⟨!b,congrArg FreeAIG.neg eq⟩

theorem Has.save {α : Type*} {S T : Set (Fn α)} (φ : α→α) (mapS : ∀g∈S,Avail T (g∘φ))
    (good : ∀g∈S,Restricted φ g) {k f} (p : Has S k f) (hn : ¬Restricted φ f) :
    ∃ t, t+1≤k ∧ Has T t (f∘φ) := by
  induction p generalizing T with
  | done hp => exact (hn (hp.restricted good)).elim
  | @step S k a b f ha hb tail ih =>
    have ma := ha.map φ mapS
    have mb := hb.map φ mapS
    have finish (cheap : Avail T ((meet a b)∘φ)) : ∃ t, t+1≤k+1 ∧ Has T t (f∘φ) := by
      refine ⟨k,le_rfl,tail.map φ ?_⟩
      rintro g (rfl|hg)
      · exact cheap
      · exact mapS g hg
    rcases ha.restricted good with ea|⟨ba,ea⟩
    · rcases hb.restricted good with eb|⟨bb,eb⟩
      · have join : (meet a b)∘φ=meet a b := congrArg₂ meet ea eb
        obtain ⟨t,ht,sm⟩ := ih (T:=insert (meet (a∘φ) (b∘φ)) T) (by
          rintro g (rfl|hg)
          · exact .src (Set.mem_insert _ _)
          · exact (mapS g hg).extend) (by
          rintro g (rfl|hg)
          · exact Or.inl join
          · exact good g hg) hn
        exact ⟨t+1,by omega,.step ma mb sm⟩
      · apply finish
        change Avail T (meet (a∘φ) (b∘φ))
        rw [eb]
        cases bb
        · rw [meetFalseR];exact .const false
        · rw [meetTrueR];exact ma
    · apply finish
      change Avail T (meet (a∘φ) (b∘φ))
      rw [ea]
      cases ba
      · rw [meetFalseL];exact .const false
      · rw [meetTrueL];exact mb

theorem fixSave {n} (f : Fn (Fin n→Bool)) (i : Fin n) (b : Bool)
    (dep : ∃ x, f (Function.update x i b) ≠ f x)
    (nc : ∃ x x', f (Function.update x i b) ≠ f (Function.update x' i b))
    {k} (p : Has Inputs k f) :
    ∃ t, t+1≤k ∧ Has Inputs t (fun x=>f (Function.update x i b)) := by
  let φ : (Fin n→Bool)→(Fin n→Bool) := fun x=>Function.update x i b
  have other {j : Fin n} (ne : j≠i) : ((fun x : Fin n→Bool=>x j)∘φ)=(fun x=>x j) := by
    funext x;simp [φ,ne]
  have same : ((fun x : Fin n→Bool=>x i)∘φ)=(fun _=>b) := by funext x;simp [φ]
  apply p.save φ
  · rintro g ⟨j,rfl⟩
    by_cases e : j=i
    · subst j;rw [same];exact .const b
    · rw [other e];exact .src ⟨j,rfl⟩
  · rintro g ⟨j,rfl⟩
    by_cases e : j=i
    · subst j; exact Or.inr ⟨b,same⟩
    · exact Or.inl (other e)
  · rintro (eq|⟨v,eq⟩)
    · obtain ⟨x,h⟩ := dep
      exact h (congrFun eq x)
    · obtain ⟨x,x',h⟩ := nc
      exact h ((congrFun eq x).trans (congrFun eq x').symm)
end FreeAIG

namespace FreeAIG

def PinPattern {α : Type*} (φ : Bool→α→α) (g : Fn α) : Prop :=
  (∀ b,g∘φ b=g) ∨ ∃ q : Bool,∀ b,g∘φ b=(fun _=>decide (b≠q))

theorem PinPattern.restrict {α : Type*} {φ : Bool→α→α} {g : Fn α}
    (h : PinPattern φ g) (b : Bool) : Restricted (φ b) g := by
  rcases h with same|⟨q,eq⟩
  · exact .inl (same b)
  · exact .inr ⟨_,eq b⟩

theorem Avail.pattern {α : Type*} {φ : Bool→α→α} {S : Set (Fn α)} {g : Fn α}
    (h : ∀ f∈S,PinPattern φ f) (a : Avail S g) : PinPattern φ g := by
  induction a with
  | src hs=>exact h _ hs
  | const v=>exact .inl (fun _=>rfl)
  | @neg f orig ih=>
    rcases ih with same|⟨q,eq⟩
    · exact .inl (fun b=>congrArg FreeAIG.neg (same b))
    · refine .inr ⟨!q,?_⟩
      intro v
      have z:=congrArg FreeAIG.neg (eq v)
      cases q <;> cases v <;> exact z

theorem Has.saveTwo {α : Type*} {S : Set (Fn α)} {k : Nat} {f : Fn α}
    (p : Has S k f) (φ : Bool→α→α) {T : Bool→Set (Fn α)}
    (maps : ∀ v g,g∈S → Avail (T v) (g∘φ v))
    (shapes : ∀g∈S,PinPattern φ g) (nontrivial : ∀v,¬Restricted (φ v) f) :
    ∃ v t,t+2≤k ∧ Has (T v) t (f∘φ v) := by
  induction p generalizing T with
  | done last=>exact (nontrivial false ((last.pattern shapes).restrict false)).elim
  | @step S k a b f ha hb tail ih=>
    have finish (v : Bool) (dead : (meet a b)∘φ v=(fun _=>false)) :
        ∃ v t,t+2≤k+1 ∧ Has (T v) t (f∘φ v) := by
      obtain ⟨q,sz,net⟩:=tail.save (T:=T v) (φ v) (by
        rintro g (rfl|m)
        · rw [dead];exact .const false
        · exact maps _ _ m) (by
        rintro g (rfl|m)
        · exact .inr ⟨false,dead⟩
        · exact (shapes _ m).restrict v) (nontrivial v)
      exact ⟨v,q,by omega,net⟩
    rcases ha.pattern shapes with sa|⟨v,eq⟩
    · rcases hb.pattern shapes with sb|⟨v,eq⟩
      · obtain ⟨v,q,sz,net⟩:=ih (T:=fun v=>insert (meet (a∘φ v) (b∘φ v)) (T v))
          (by intro v g m;rcases m with rfl|m
              · exact .src (Set.mem_insert _ _)
              · exact (maps _ _ m).extend)
          (by rintro g (rfl|m)
              · exact .inl (fun v=>congrArg₂ meet (sa v) (sb v))
              · exact shapes _ m) nontrivial
        exact ⟨v,q+1,by omega,.step (ha.map _ (maps v)) (hb.map _ (maps v)) net⟩
      · apply finish v
        change meet (a∘φ v) (b∘φ v) = _
        rw [eq v];simp [meetFalseL,meetFalseR]
    · apply finish v
      change meet (a∘φ v) (b∘φ v) = _
      rw [eq v];simp [meetFalseL,meetFalseR]

theorem pinTwo {n} (f : Fn (Fin n→Bool)) (i : Fin n)
    (dep : ∀b,∃ x, f (Function.update x i b) ≠ f x)
    (nc : ∀b,∃ x y,f (Function.update x i b) ≠ f (Function.update y i b))
    {k} (p : Has Inputs k f) :
    ∃ b t,t+2≤k ∧ Has Inputs t (fun x=>f (Function.update x i b)) := by
  let φ := fun (b : Bool) (x : Fin n→Bool)=>Function.update x i b
  have own (b : Bool) : ((fun x : Fin n→Bool=>x i)∘φ b)=(fun _=>b) := by funext x;simp [φ]
  have other (j : Fin n) (h : j≠i) (b : Bool) : ((fun x : Fin n→Bool=>x j)∘φ b)=(fun x=>x j) := by
    funext x;simp [φ,h]
  apply p.saveTwo (T:=fun _=>Inputs) φ
  · rintro b _ ⟨j,rfl⟩
    by_cases e:j=i
    · subst j;rw [own];exact .const b
    · rw [other j e];exact .src ⟨j,rfl⟩
  · rintro g ⟨j,rfl⟩
    by_cases e:j=i
    · subst j
      exact .inr ⟨false,fun b=>by cases b <;> exact own _⟩
    · exact .inl (other j e)
  · intro b
    rintro (same|⟨v,eq⟩)
    · obtain ⟨x,h⟩:=dep b
      exact h (congrFun same x)
    · obtain ⟨x,y,h⟩:=nc b
      exact h ((congrFun eq x).trans (congrFun eq y).symm)

end FreeAIG

namespace FreeAIG

variable {n : Nat}

def cofactorAt (f : Fn (Fin (n + 1) → Bool)) (i : Fin (n + 1)) (b : Bool) :
    Fn (Fin n → Bool) :=
  fun x => f (i.insertNth (α := fun _ => Bool) b x)

variable {f : Fn (Fin (n + 1) → Bool)} {i : Fin (n + 1)} {b : Bool} {k m : Nat}

theorem Has.cofactorAt (h : Has Inputs k f) (i : Fin (n + 1)) (b : Bool) :
    Has Inputs k (cofactorAt f i b) := by
  apply h.map (i.insertNth (α := fun _ => Bool) b)
  rintro _ ⟨j, rfl⟩
  refine Fin.succAboveCases i ?_ (fun a => ?_) j
  · simpa [Function.comp_def] using (Avail.const (S := Inputs) b)
  · simpa [Function.comp_def] using
      (Avail.src (S := Inputs) (show (fun x : Fin n → Bool => x a) ∈ Inputs from ⟨a, rfl⟩))

private theorem canChange (dep : ∃ x, cofactorAt f i false x ≠ cofactorAt f i true x)
    (b : Bool) : ∃ x, f (Function.update x i b) ≠ f x := by
  obtain ⟨x, hx⟩ := dep
  refine ⟨i.insertNth (α := fun _ => Bool) (!b) x, ?_⟩
  cases b
  · simpa only [FreeAIG.cofactorAt, Bool.not_false, Fin.update_insertNth] using hx
  · simpa only [FreeAIG.cofactorAt, Bool.not_true, Fin.update_insertNth] using Ne.symm hx

private theorem canVary (nc : ∃ x y, cofactorAt f i b x ≠ cofactorAt f i b y) :
    ∃ x y, f (Function.update x i b) ≠ f (Function.update y i b) := by
  obtain ⟨x, y, h⟩ := nc
  exact ⟨i.insertNth (α := fun _ => Bool) b x, i.insertNth (α := fun _ => Bool) b y,
    by simpa only [FreeAIG.cofactorAt, Fin.update_insertNth] using h⟩

private theorem shrink {q : Nat} (h : Has Inputs q (fun x => f (Function.update x i b))) :
    Has Inputs q (cofactorAt f i b) := by
  have eq : cofactorAt (fun x => f (Function.update x i b)) i b = cofactorAt f i b := by
    funext x
    exact congrArg f (Fin.update_insertNth (α := fun _ => Bool) i b b x)
  exact eq ▸ h.cofactorAt i b

theorem saveOneCofactor (dep : ∃ x, cofactorAt f i false x ≠ cofactorAt f i true x)
    (nc : ∃ x y, cofactorAt f i b x ≠ cofactorAt f i b y) (h : Has Inputs k f) :
    ∃ q, q + 1 ≤ k ∧ Has Inputs q (cofactorAt f i b) := by
  obtain ⟨q, hq, net⟩ := fixSave f i b (canChange dep b) (canVary nc) h
  exact ⟨q, hq, shrink net⟩

theorem saveTwoCofactors (dep : ∃ x, cofactorAt f i false x ≠ cofactorAt f i true x)
    (nc : ∀ v, ∃ x y, cofactorAt f i v x ≠ cofactorAt f i v y) (h : Has Inputs k f) :
    ∃ v q, q + 2 ≤ k ∧ Has Inputs q (cofactorAt f i v) := by
  obtain ⟨v, q, hq, net⟩ := pinTwo f i (canChange dep) (fun v => canVary (nc v)) h
  exact ⟨v, q, hq, shrink net⟩

private theorem variesOfPositiveLower {g : Fn (Fin n → Bool)} (positive : 0 < m)
    (lower : ∀ {q}, Has Inputs q g → m ≤ q) : ∃ x y, g x ≠ g y := by
  classical
  by_contra! h
  let zero : Fin n → Bool := fun _ => false
  have eq : g = fun _ => g zero := funext (fun x => h x zero)
  have trivial : Has Inputs 0 g := by
    conv => arg 3; rw [eq]
    exact .done (.const _)
  exact (Nat.not_le_of_gt positive) (lower trivial)

theorem oneCofactorLower (positive : 0 < m)
    (dep : ∃ x, cofactorAt f i false x ≠ cofactorAt f i true x)
    (lower : ∀ {q}, Has Inputs q (cofactorAt f i b) → m ≤ q)
    (h : Has Inputs k f) : m + 1 ≤ k := by
  obtain ⟨q, hq, net⟩ := saveOneCofactor dep (variesOfPositiveLower positive lower) h
  exact le_trans (Nat.add_le_add_right (lower net) 1) hq

theorem twoCofactorsLower (positive : 0 < m)
    (dep : ∃ x, cofactorAt f i false x ≠ cofactorAt f i true x)
    (lower : ∀ v {q}, Has Inputs q (cofactorAt f i v) → m ≤ q)
    (h : Has Inputs k f) : m + 2 ≤ k := by
  obtain ⟨v, q, hq, net⟩ := saveTwoCofactors dep (fun v => variesOfPositiveLower positive (lower v)) h
  exact le_trans (Nat.add_le_add_right (lower v net) 2) hq

end FreeAIG

namespace K4Core
def pack {n:Nat} (f : Fin n→Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)

theorem pack_get {n:Nat} (f : Fin n→Bool) (i:Fin n) : (pack f)[i.val] = f i := by
  have h : (BitVec.ofBoolListLE (List.ofFn f)).getLsbD i.val = f i := by
    rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD]
    simp
  exact h

end K4Core

namespace LiveAIG
abbrev W := BitVec 128
abbrev R := Fin 128
abbrev X := Fin 7→Bool
def signed (w : W) (s : Bool) := if s then ~~~w else w
def norm (w : W) := signed w w[0]
def made (a b : W) (s t : Bool) := norm (signed a s &&& signed b t)
def drop (s : List W) (a : W) (keep : Bool) := if keep then s else s.erase a
def after (s : List W) (a b g : W) (ka kb : Bool) := g :: drop (drop s a ka) b kb
def row (r : R) (i : Fin 7) := r.val.testBit i.val
def word (f : X→Bool) : W := K4Core.pack fun r=>f (row r)
def inputs : List W := (List.finRange 7).map fun i=>word (fun x=>x i)
def depends (f : X→Bool) := ∀ i : Fin 7, ∃ r q : R, (∀ j : Fin 7,j≠i → row r j=row q j) ∧ f (row r)≠f (row q)

inductive Run (t : W) : List W→Nat→Nat→Prop where
  | done : Run t [norm t] 0 0
  | gate {s n c} (a b : W) (sa sb ka kb : Bool) (left : a∈s) (right : b∈s) (different : a≠b)
      (nz : made a b sa sb ≠ 0) (newWord : made a b sa sb ∉ s)
      (rest : Run t (after s a b (made a b sa sb) ka kb) n c) :
      Run t s (n+1) (c+ka.toNat+kb.toNat)

theorem signedTwice (w : W) (b : Bool) : signed (signed w b) b=w := by cases b <;> simp [signed]
theorem orient (w : W) : signed (norm w) w[0]=w := signedTwice w w[0]
theorem normNeg (w : W) : norm (~~~w)=norm w := by
  unfold norm
  cases h:w[0] <;> simp [signed,h]
theorem normEq (x y : W) (k : norm x=norm y) : x=y ∨ x= ~~~y := by
  cases a:x[0] <;> cases b:y[0] <;> simp [norm,signed,a,b] at k
  · exact Or.inl k
  · exact Or.inr k
  · right; rw [←k];simp
  · exact Or.inl k

def agree (s : List W) (r q : R) := ∀w∈s,w[r.val]=w[q.val]
theorem dropSubset (s : List W) (a : W) (b : Bool) : ∀x∈drop s a b,x∈s := by
  cases b
  · exact fun _ h=>List.mem_of_mem_erase h
  · exact fun _ h=>h
theorem signedCong {w : W} (b : Bool) {r q : R} (h : w[r.val]=w[q.val]) :
    (signed w b)[r.val]=(signed w b)[q.val] := by cases b <;> simp [signed,h]
theorem agreeRun {s n c t} (rt : Run t s n c) {r q : R} (same : agree s r q) : t[r.val]=t[q.val] := by
  induction rt with
  | done =>
    have e := same (norm t) List.mem_cons_self
    have e' := signedCong t[0] e
    rwa [orient] at e'
  | @gate s n c a b sa sb ka kb ha hb _ _ _ tail ih =>
    apply ih
    intro w mem
    rcases List.mem_cons.mp mem with rfl|old
    · apply signedCong
      have x:=signedCong sa (same a ha)
      have y:=signedCong sb (same b hb)
      simp only [BitVec.getElem_and,x,y]
    · exact same w (dropSubset _ _ _ _ (dropSubset _ _ _ _ old))

theorem dropLength {s : List W} {a : W} (h:a∈s) (keep : Bool) :
    (drop s a keep).length+1=s.length+keep.toNat := by
  cases keep
  · have pos := List.length_pos_of_mem h
    simp [drop,h,List.length_erase_of_mem];omega
  · simp [drop]

theorem rightStays {s : List W} {a b : W} (hb:b∈s) (ne:a≠b) (k : Bool) : b∈drop s a k := by
  cases k <;> simp [drop,hb,ne.symm]

theorem balance {s n c t} (r : Run t s n c) : s.length+c=n+1 := by
  induction r with
  | done=>rfl
  | @gate s n c a b sa sb ka kb ha hb ne _ _ tail ih =>
    have da:=dropLength ha ka
    have db:=dropLength (rightStays hb ne ka) kb
    simp only [after,List.length_cons] at ih
    omega

theorem wordBit (f : X→Bool) (r : R) : (word f)[r.val]=f (row r) := K4Core.pack_get _ r
theorem wordNeg (f : X→Bool) : word (FreeAIG.neg f)= ~~~word f := by
  ext j hj
  rw [BitVec.getElem_not]
  exact (wordBit _ ⟨j,hj⟩).trans (congrArg Bool.not (wordBit f ⟨j,hj⟩)).symm
theorem wordAnd (f g : X→Bool) : word (FreeAIG.meet f g)=word f &&& word g := by
  ext j hj
  rw [BitVec.getElem_and,show (word f)[j]=f (row ⟨j,hj⟩) from wordBit f ⟨j,hj⟩,
    show (word g)[j]=g (row ⟨j,hj⟩) from wordBit g ⟨j,hj⟩]
  exact wordBit _ ⟨j,hj⟩

theorem rawNorm : ∀i:Fin 7,norm (word (fun x=>x i))=word (fun x=>x i) := by decide +kernel
theorem uniqueInputs : inputs.Nodup := by decide +kernel
theorem inputLength : inputs.length=7 := by simp [inputs]
end LiveAIG

namespace LiveAIG
open FreeAIG
private theorem normZero : norm 0=0 := by decide +kernel
private theorem zeroSide {u : W} (h : norm u=0) (v : W) : norm (u&&&v)=0 ∨ norm (u&&&v)=norm v := by
  rcases normEq u 0 (h.trans normZero.symm) with rfl|rfl
  · left;have eq : (0:W) &&& v=0 := by ext i hi;simp
    rw [eq];exact normZero
  · right;change norm (BitVec.allOnes 128 &&& v)=norm v;rw [BitVec.allOnes_and]
private theorem equalSide {u v : W} (h : norm u=norm v) : norm (u&&&v)=0 ∨ norm (u&&&v)=norm v := by
  rcases normEq u v h with rfl|rfl
  · right;rw [BitVec.and_self]
  · left;rw [BitVec.not_and_self];exact normZero

def Represents (S : Set (Fn X)) (A : Finset W) := ∀g∈S,norm (word g)=0 ∨ norm (word g)∈A
theorem availRep {S A} (rep : Represents S A) {g} (av : Avail S g) : norm (word g)=0 ∨ norm (word g)∈A := by
  induction av with
  | src m => exact rep _ m
  | const b => left; cases b <;> decide +kernel
  | neg _ ih => simpa [wordNeg,normNeg] using ih

theorem operands (u v : W) (A : Finset W) (hu : norm u=0 ∨ norm u∈A) (hv : norm v=0 ∨ norm v∈A)
    (nz : norm (u&&&v)≠0) (nf : norm (u&&&v)∉A) :
    norm u∈A ∧ norm v∈A ∧ norm u≠norm v ∧ norm u≠0 ∧ norm v≠0 := by
  have unu : norm u≠0 := by
    intro e
    have eq: norm (u&&&v)=norm v := (zeroSide e v).resolve_left nz
    rcases hv with v0|vm
    · exact nz (eq.trans v0)
    · exact nf (eq ▸ vm)
  have vnu : norm v≠0 := by
    intro e
    have x:=zeroSide e u
    rw [BitVec.and_comm] at x
    have eq:=x.resolve_left nz
    exact nf (eq ▸ hu.resolve_left unu)
  have um:=hu.resolve_left unu
  have vm:=hv.resolve_left vnu
  exact ⟨um,vm,fun e=>nf ((equalSide e).resolve_left nz ▸ vm),unu,vnu⟩

def Trim (A : Finset W) (k : Nat) (t : W) : Prop :=
  ∃ U : Finset W, U⊆A ∧ 0∉U ∧ ∃ n≤k,∃ c,∀s : List W,s.Nodup → s.toFinset=U → Run t s n c

private theorem dropDedup {s : List W} (nd : s.Nodup) (w : W) (k : Bool) : (drop s w k).Nodup := by
  cases k
  · exact nd.erase w
  · exact nd

private theorem inDrop {s : List W} (nd : s.Nodup) (w x : W) (k : Bool) :
    x∈drop s w k ↔ x∈s ∧ (k=true ∨ x≠w) := by
  cases k <;> simp [drop,nd.mem_erase_iff,and_comm]

private theorem arrange (V : Finset W) (g a b : W) (s : List W) (nd : s.Nodup)
    (eq : s.toFinset=insert a (insert b V)) (new : g∉s) :
    let ka := decide (a∈V)
    let kb := decide (b∈V)
    let dest := after s a b g ka kb
    dest.Nodup ∧ dest.toFinset=insert g V := by
  dsimp only
  have dn:=dropDedup nd a (decide (a∈V))
  have dnn:=dropDedup dn b (decide (b∈V))
  constructor
  · apply List.nodup_cons.mpr
    exact ⟨fun m=>new (dropSubset _ _ _ _ (dropSubset _ _ _ _ m)),dnn⟩
  · ext x
    have ex : x∈s ↔ x=a ∨ x=b ∨ x∈V := by
      rw [←List.mem_toFinset]
      rw [eq]
      simp
    simp only [after,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,inDrop dn,inDrop nd,
      decide_eq_true_eq,ex]
    grind

theorem trim {S : Set (Fn X)} {k : Nat} {f : Fn X} (p : Has S k f) (A : Finset W)
    (rep : Represents S A) (nz : norm (word f)≠0) : Trim A k (word f) := by
  classical
  induction p generalizing A with
  | @done S k f h =>
    have mf := (availRep rep h).resolve_left nz
    refine ⟨{norm (word f)},by simpa using mf,by simpa only [Finset.mem_singleton] using (Ne.symm nz),0,Nat.zero_le _,0,?_⟩
    intro s nd eq
    have eq' : s=[norm (word f)] := by
      have sz : s.length=1 := by simpa [List.toFinset_card_of_nodup nd] using congrArg Finset.card eq
      obtain ⟨w,rfl⟩ := List.length_eq_one_iff.mp sz
      simpa using eq
    rw [eq'];exact .done
  | @step S k f g z hf hg tail ih =>
    let u:=word f
    let v:=word g
    let w:=norm (u&&&v)
    have ex : norm (word (meet f g))=w := by rw [wordAnd]
    have rep' : Represents (insert (meet f g) S) (insert w A) := by
      rintro x (rfl|hx)
      · exact Or.inr (ex ▸ Finset.mem_insert_self ..)
      · exact (rep x hx).imp_right (Finset.mem_insert_of_mem)
    obtain ⟨U,inA,valid,n,cap,c,uses⟩ := ih (insert w A) rep' nz
    by_cases ss : U⊆A
    · exact ⟨U,ss,valid,n,by omega,c,uses⟩
    have picked : w∈U ∧ w∉A := by
      by_contra! no
      apply ss
      intro t mt
      rcases Finset.mem_insert.mp (inA mt) with eq|old
      · subst t;exact no mt
      · exact old
    have w0 : w≠0 := fun e=>valid (e ▸ picked.1)
    obtain ⟨ua,va,ne,uz,vz⟩ := operands u v A (availRep rep hf) (availRep rep hg) w0 picked.2
    let V:=U.erase w
    let a:=norm u
    let b:=norm v
    have sub : V⊆A := by
      intro x hx
      obtain ⟨diff,m⟩ := Finset.mem_erase.mp hx
      exact (Finset.mem_insert.mp (inA m)).resolve_left diff
    have pre : insert a (insert b V) ⊆ A := Finset.insert_subset ua (Finset.insert_subset va sub)
    have good : 0∉insert a (insert b V) := by
      simp only [Finset.mem_insert,not_or]
      exact ⟨Ne.symm uz,Ne.symm vz,fun h=>valid (Finset.mem_of_mem_erase h)⟩
    let ka:=decide (a∈V)
    let kb:=decide (b∈V)
    refine ⟨_,pre,good,n+1,by omega,c+ka.toNat+kb.toNat,?_⟩
    intro s nd eq
    have ga : a∈s := List.mem_toFinset.mp (eq ▸ Finset.mem_insert_self ..)
    have gb : b∈s := List.mem_toFinset.mp (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have fresh : w∉s := fun hh=>picked.2 (pre (eq ▸ List.mem_toFinset.mpr hh))
    have wm : made a b u[0] v[0]=w := by simp [made,a,b,orient,w]
    apply Run.gate a b u[0] v[0] ka kb ga gb ne (wm ▸ w0) (wm ▸ fresh)
    rw [wm]
    obtain ⟨nd',newSet⟩:=arrange V w a b s nd eq fresh
    apply uses _ nd'
    exact newSet.trans (Finset.insert_erase picked.1)
end LiveAIG

namespace LiveAIG

def mixed (t m : W) : Bool := (m &&& t != 0) && (m &&& ~~~t != 0)
def split (t : W) (cells : List W) (w : W) : List W :=
  cells.flatMap fun m => [m &&& w, m &&& ~~~w].filter (mixed t)
def classes (t : W) (remaining : List W) : List W :=
  remaining.foldl (split t) [~~~0]
def accept (t : W) (cells : List W) (w : W) : Bool :=
  cells.all fun m => !mixed t (m &&& w) && !mixed t (m &&& ~~~w)

theorem someRow {m : W} (nonzero : m ≠ 0) : ∃ r : R, m[r.val]=true := by
  by_contra! none
  apply nonzero
  ext j hj
  simpa using none ⟨j,hj⟩

theorem mixedRows {t m : W} (h : mixed t m=true) :
    ∃ p q : R, m[p.val]=true ∧ m[q.val]=true ∧ t[p.val]=true ∧ t[q.val]=false := by
  simp [mixed] at h
  obtain ⟨p,hp⟩:=someRow h.1
  obtain ⟨q,hq⟩:=someRow h.2
  simp at hp hq
  exact ⟨p,q,hp.1,hq.1,hp.2,hq.2⟩

def coherent (cells : List W) (seen : List W) : Prop :=
  ∀ m∈cells, ∀ p q : R, m[p.val]=true → m[q.val]=true → agree seen p q

theorem splitCoherent {t w cells seen} (h : coherent cells seen) :
    coherent (split t cells w) (w::seen) := by
  intro child cm p q hp hq
  obtain ⟨m,mm,sub⟩:=List.mem_flatMap.mp cm
  have parts : child=m &&& w ∨ child=m &&& ~~~w := by
    simpa using (List.mem_filter.mp sub).1
  rcases parts with rfl|rfl
  all_goals
    simp at hp hq
    intro z zm
    rcases List.mem_cons.mp zm with rfl|zm
    · exact hp.2.trans hq.2.symm
    · exact h m mm p q hp.1 hq.1 z zm

theorem foldCoherent (t : W) (suffix : List W) {cells seen}
    (h : coherent cells seen) :
    coherent (suffix.foldl (split t) cells) (suffix++seen) := by
  induction suffix generalizing cells seen with
  | nil => simpa using h
  | cons w ws ih =>
    have stable := ih (splitCoherent (t:=t) (w:=w) h)
    intro m hm p q hp hq z hz
    apply stable m hm p q hp hq z
    simp only [List.cons_append,List.mem_cons,List.mem_append] at hz ⊢
    tauto

theorem classesCoherent (t : W) (s : List W) : coherent (classes t s) s := by
  have initial : coherent [~~~0] [] := by intro m hm p q hp hq z hz; simp at hz
  simpa [classes] using foldCoherent t s initial

theorem acceptOfAgree {t w : W} {s : List W}
    (dep : ∀ p q : R, agree (w::s) p q → t[p.val]=t[q.val]) :
    accept t (classes t s) w=true := by
  apply List.all_eq_true.mpr
  intro m hm
  have cell := classesCoherent t s m hm
  have pure (z : W) (side : ∀ p q : R, z[p.val]=true → z[q.val]=true → w[p.val]=w[q.val]) :
      mixed t (m &&& z)=false := by
    cases test : mixed t (m &&& z) with
    | false => rfl
    | true =>
      obtain ⟨p,q,hp,hq,tp,tq⟩:=mixedRows test
      simp at hp hq
      have agreeAll : agree (w::s) p q := by
        intro v vm
        rcases List.mem_cons.mp vm with rfl|vm
        · exact side p q hp.2 hq.2
        · exact cell p q hp.1 hq.1 v vm
      have same := dep p q agreeAll
      simp [tp,tq] at same
  have pos:=pure w (fun p q hp hq=> hp.trans hq.symm)
  have neg:=pure (~~~w) (by intro p q hp hq; simp at hp hq; exact hp.trans hq.symm)
  simp [pos,neg]

theorem runAccept {t w : W} {remaining : List W} {n c : Nat}
    (h : Run t (w::remaining) n c) : accept t (classes t remaining) w=true :=
  acceptOfAgree fun _ _ same => agreeRun h same

end LiveAIG

namespace LiveAIG

def canon (s : List W) := s.insertionSort (fun a b=>a.toNat≤b.toNat)
def flags : List Bool := [false,true]
def phaseKids (t : W) (s : List W) (budget : Nat) (a b : W) (ka kb : Bool) :
    List (List W × Nat) :=
  let spent := ka.toNat+kb.toNat
  if spent≤budget then
    let left := drop (drop s a ka) b kb
    let cells := classes t left
    flags.flatMap fun sa=>flags.filterMap fun sb=>
      let g:=made a b sa sb
      if g != 0 && !s.contains g && accept t cells g then
        some (canon (g::left),budget-spent) else none
  else []
def children (t : W) (s : List W) (budget : Nat) : List (List W × Nat) :=
  s.flatMap fun a=>s.flatMap fun b=>
    if a.toNat<b.toNat then flags.flatMap fun ka=>flags.flatMap fun kb=>phaseKids t s budget a b ka kb else []

theorem dropPerm {s u : List W} (p : s.Perm u) (a : W) (k : Bool) :
    (drop s a k).Perm (drop u a k) := by
  cases k
  · exact List.Perm.erase a p
  · exact p

theorem runPerm {t s n c} (rt : Run t s n c) {u} (perm : s.Perm u) : Run t u n c := by
  induction rt generalizing u with
  | done =>
    have single := List.perm_singleton.mp perm.symm
    rw [single]
    exact .done
  | @gate s n c a b sa sb ka kb ha hb ne nz fresh _ ih =>
    apply Run.gate a b sa sb ka kb (perm.mem_iff.mp ha) (perm.mem_iff.mp hb) ne nz
      (fun m=>fresh (perm.mem_iff.mpr m))
    exact ih ((dropPerm (dropPerm perm a ka) b kb).cons _)

theorem canonRun {t s n c} (rt : Run t s n c) : Run t (canon s) n c :=
  runPerm rt (List.perm_insertionSort _ _).symm

theorem swapAfter (s : List W) (a b : W) (sa sb ka kb : Bool) :
    after s a b (made a b sa sb) ka kb = after s b a (made b a sb sa) kb ka := by
  unfold after made
  rw [BitVec.and_comm (signed a sa) (signed b sb)]
  cases ka <;> cases kb <;> simp [drop,List.erase_comm a b]

theorem hasFlag (b : Bool) : b∈flags := by cases b <;> simp [flags]
theorem childOf {t s n c budget a b sa sb ka kb}
    (ha : a∈s) (hb : b∈s) (lt : a.toNat<b.toNat)
    (nz : made a b sa sb ≠ 0) (fresh : made a b sa sb ∉ s)
    (run : Run t (after s a b (made a b sa sb) ka kb) n c)
    (bound : c+ka.toNat+kb.toNat≤budget) :
    ∃p∈children t s budget, Run t p.1 n c ∧ c≤p.2 := by
  let g:=made a b sa sb
  let remaining:=drop (drop s a ka) b kb
  let spent:=ka.toNat+kb.toNat
  have spentOk : spent≤budget := by dsimp [spent];omega
  have checked : accept t (classes t remaining) g=true := runAccept run
  refine ⟨(canon (g::remaining),budget-spent),?_,canonRun run,by dsimp [spent];omega⟩
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  rw [if_pos lt]
  refine List.mem_flatMap.mpr ⟨ka,hasFlag ka,List.mem_flatMap.mpr ⟨kb,hasFlag kb,?_⟩⟩
  unfold phaseKids
  rw [if_pos spentOk]
  refine List.mem_flatMap.mpr ⟨sa,hasFlag sa,List.mem_filterMap.mpr ⟨sb,hasFlag sb,?_⟩⟩
  change (if g != 0 && !s.contains g && accept t (classes t remaining) g then
      some (canon (g::remaining),budget-spent) else none) = some _
  have avoid : g∉s := fresh
  have val : g≠0 := nz
  simp [avoid,checked]
  exact val

theorem continueRun {t s n c budget} (rt : Run t s (n+1) c) (bound : c≤budget) :
    ∃p∈children t s budget, ∃d≤p.2, Run t p.1 n d := by
  cases rt with
  | @gate s n c a b sa sb ka kb ha hb ne nz fresh rest =>
    have ext : ∃p∈children t s budget, Run t p.1 n c ∧ c≤p.2 := by
      have diff : a.toNat≠b.toNat := fun h=>ne (BitVec.eq_of_toNat_eq h)
      rcases lt_or_gt_of_ne diff with lt|gt
      · exact childOf ha hb lt nz fresh rest bound
      · have eq : made a b sa sb=made b a sb sa := by unfold made; rw [BitVec.and_comm]
        rw [swapAfter] at rest
        exact childOf hb ha gt (eq ▸ nz) (eq ▸ fresh) rest (by omega)
    obtain ⟨p,m,r,b⟩:=ext
    exact ⟨p,m,c,b,r⟩

theorem runStep {t s n c budget} (rt : Run t s n c) (bound : c≤budget) :
    norm t∈s ∨ ∃k, n=k+1 ∧ ∃p∈children t s budget, ∃d≤p.2, Run t p.1 k d := by
  cases n with
  | zero => cases rt; exact Or.inl List.mem_cons_self
  | succ k => exact Or.inr ⟨k,rfl,continueRun rt bound⟩

def searchWith (t : W) (allow : List W→Nat→Bool) : Nat→List W→Nat→Bool
  | 0,s,_=>s.contains (norm t)
  | n+1,s,b=>s.contains (norm t) || (allow s b && (children t s b).any fun p=>searchWith t allow n p.1 p.2)

theorem searchSound {t : W} {allow : List W→Nat→Bool}
    (pass : ∀ {s k c b}, Run t s k c → c≤b → allow s b=true)
    {s k c fuel budget} (run : Run t s k c) (depth : k≤fuel) (bound : c≤budget) :
    searchWith t allow fuel s budget=true := by
  induction fuel generalizing s k c budget with
  | zero =>
    have z : k=0 := by omega
    subst k
    cases run
    simp [searchWith]
  | succ n ih =>
    rcases runStep run bound with endNow|⟨k',rfl,p,pm,d,db,child⟩
    · simp [searchWith,endNow]
    · have allows:=pass run bound
      have kept : (children t s budget).any (fun z=>searchWith t allow n z.1 z.2)=true := List.any_eq_true.mpr ⟨p,pm,ih child (by omega) db⟩
      simp [searchWith,allows,kept]

end LiveAIG

namespace LiveAIG
open FreeAIG

def liveInitial (t : W) (s : List W) : Bool :=
  match s with
  | []=>false
  | a::rest=>accept t (classes t rest) a

theorem initialOk {t : W} {s : List W} {n c : Nat} (run : Run t s n c) : liveInitial t s=true := by
  cases s with
  | nil=>
    cases run with
    | gate _ _ _ _ _ _ h _ _ _ _ _=>simp at h
  | cons w rest=>exact runAccept run

def initialSearch (t : W) (A : List W) (max : Nat) (allow : List W→Nat→Bool) : Bool :=
  A.sublists.any fun s=>liveInitial t s && searchWith t allow max s (max+1-s.length)

theorem initialSearchSound {S : Set (Fn X)} {f : Fn X} {A : List W} {k max : Nat}
    (allow : List W→Nat→Bool)
    (ok : ∀ {s n c budget}, Run (word f) s n c → c≤budget → allow s budget=true)
    (h : Has S k f) (rep : Represents S A.toFinset) (proper : norm (word f)≠0)
    (distinct : A.Nodup) (small : k ≤ max) : initialSearch (word f) A max allow=true := by
  classical
  obtain ⟨U,sub,_,n,sz,c,applyRun⟩:=trim h A.toFinset rep proper
  let s:= A.filter (fun w=> decide (w∈U))
  have setEq : s.toFinset=U := by
    ext w
    change w∈(A.filter (fun w=>decide (w∈U))).toFinset ↔ w∈U
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun hw=>⟨List.mem_toFinset.mp (sub hw),hw⟩⟩
  have run := applyRun s (distinct.filter _) setEq
  have lengths:=balance run
  apply List.any_eq_true.mpr
  refine ⟨s,List.mem_sublists.mpr List.filter_sublist,?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨initialOk run,searchSound ok run (by omega) (by omega)⟩

end LiveAIG

namespace Data12783
open LiveAIG
def repeated (x : Nat) : W := BitVec.ofNat 128 (x * 18446744073709551617)
def raw : List W := [repeated 0xaaaaaaaaaaaaaaaa,repeated 0xcccccccccccccccc,repeated 0xf0f0f0f0f0f0f0f0,repeated 0xff00ff00ff00ff00,repeated 0xffff0000ffff0000]
def tokens0 : Array Nat := #[0xc2259,0x32361,0x1a361,0x32651,0xc2159,0xc214d,0x6214d,0x2a571,0x62361,0x32571,0x2a361,0x92455,0x52561,0x92453,0x182179,0x24c,0x8a253,0xa2155,0x4a349,0x4a253,0x1a349,0x62661,0x10a463,0x62259,0x48,0x6c,0x78,0xb4,0x1a671,0x24,0xa8,0x92253]
def tokens1 : Array Nat := #[0xa2571,0x0,0xc,0x18,0x84,0x90,0x32349,0x54,0x60,0x4a14d,0x52155,0x122269,0x30,0x3c,0x9c,0x4a155,0x5224b,0x8a463,0x112465,0x108,0x120,0x1bc,0x1c8,0x1e0,0x1ec,0x258,0xc0,0xcc,0xd8,0xe4,0xf0,0xfc]
def tokens2 : Array Nat := #[0x12c,0x144,0x150,0x15c,0x168,0x174,0x180,0x18c,0x198,0x1a4,0x1b0,0x1d4,0x1f8,0x264,0x270,0x2b8,0x2d0,0x2dc,0x2e8,0x300,0x324,0x330,0x33c,0x354,0x378,0x39c,0x3c0,0x3cc,0x3d8,0x3214d,0x52671,0x112473]
def tokens3 : Array Nat := #[0x122475,0x114,0x138,0x204,0x210,0x21c,0x240,0x27c,0x288,0x294,0x2ac,0x2c4,0x30c,0x348,0x36c,0x384,0x390,0x3a8,0x3b4,0x4a165,0x4a24b,0xa2169,0x142169,0x228,0x234,0x2a0,0x2f4,0x318,0x360,0x450,0x4a4,0x4c8]
def tokens4 : Array Nat := #[0x4e0,0x4ec,0x4f8,0x504,0x510,0x5f4,0x52453,0xa2259,0x10a453,0x10a465,0x112455,0x142259,0x3e4,0x3f0,0x3fc,0x408,0x414,0x420,0x42c,0x438,0x444,0x45c,0x468,0x474,0x480,0x48c,0x498,0x4b0,0x4bc,0x4d4,0x51c,0x528]
def tokens5 : Array Nat := #[0x534,0x540,0x54c,0x558,0x564,0x570,0x57c,0x588,0x594,0x5a0,0x5ac,0x5b8,0x5c4,0x5d0,0x5dc,0x5e8,0x4a473,0x62179,0x8a455,0x8a465,0x92465,0xa2475,0x112263,0x122165]
def tokenTable : Array (Array Nat) := #[tokens0,tokens1,tokens2,tokens3,tokens4,tokens5]
def decodeStep (_b stream : Nat) : Nat × Nat :=
  let k:=stream % 256
  ((((tokenTable[k/32]?).getD #[])[k % 32]?.getD 0),stream/256)
def words0 : Array Nat := #[0xaa000000aa,0xcc000000cc,0xf0000000f0,0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xa0a0a0a0a0a0a0a,0xa0a0aaa0a0a0aaa,0xa0aaaaa0a0aaaaa,0xaaa0aaa0aaa0aaa,0xc0c0c0c0c0c0c0c,0xc0c0ccc0c0c0ccc,0xc0ccccc0c0ccccc,0xccc0ccc0ccc0ccc,0xf000f000f000f00,0xf00ff000f00ff00,0xf0f00000f0f0000,0xf0f0f000f0f0f00,0xfff00000fff0000,0x2222222222222222,0x222222aa222222aa,0x2222aaaa2222aaaa,0x22aa22aa22aa22aa,0x2a2a2a2a2a2a2a2a,0x3030303030303030,0x303030f0303030f0,0x3030f0f03030f0f0]
def words1 : Array Nat := #[0x30f030f030f030f0,0x3300330033003300,0x3300ff003300ff00,0x3333000033330000,0x3333330033333300,0x33ff000033ff0000,0x3f003f003f003f00,0x3f3f00003f3f0000,0x3f3f3f003f3f3f00,0x4444444444444444,0x444444cc444444cc,0x4444cccc4444cccc,0x44cc44cc44cc44cc,0x4c4c4c4c4c4c4c4c,0x5050505050505050,0x505050f0505050f0,0x5050f0f05050f0f0,0x50f050f050f050f0,0x5500550055005500,0x5500ff005500ff00,0x5555000055550000,0x5555550055555500,0x55ff000055ff0000,0x5f005f005f005f00,0x5f5f00005f5f0000,0x5f5f5f005f5f5f00,0x7070707070707070,0x7700770077007700,0x7777000077770000,0x7777770077777700,0x8888888888888888,0xa0a0a0a0a0a0a0a0]
def words2 : Array Nat := #[0xaa00aa00aa00aa00,0xaa00ff00aa00ff00,0xaaaa0000aaaa0000,0xaaaaaa00aaaaaa00,0xaaff0000aaff0000,0xc0c0c0c0c0c0c0c0,0xcc00cc00cc00cc00,0xcc00ff00cc00ff00,0xcccc0000cccc0000,0xcccccc00cccccc00,0xccff0000ccff0000,0xeaeaeaeaeaeaeaea,0xecececececececec,0xeeaaeeaaeeaaeeaa,0xeecceecceecceecc,0xeeeeaaaaeeeeaaaa,0xeeeecccceeeecccc,0xeeeeeeaaeeeeeeaa,0xeeeeeecceeeeeecc,0xeeeeeeeeeeeeeeee,0xf000f000f000f000,0xf000ff00f000ff00,0xf0f00000f0f00000,0xf0f0f000f0f0f000,0xf0ff0000f0ff0000,0xf8f8f8f8f8f8f8f8,0xfaaafaaafaaafaaa,0xfaf0faf0faf0faf0,0xfafaaaaafafaaaaa,0xfafaf0f0fafaf0f0,0xfafafaaafafafaaa,0xfafafaf0fafafaf0]
def words3 : Array Nat := #[0xfafafafafafafafa,0xfcccfcccfcccfccc,0xfcf0fcf0fcf0fcf0,0xfcfcccccfcfccccc,0xfcfcf0f0fcfcf0f0,0xfcfcfcccfcfcfccc,0xfcfcfcf0fcfcfcf0,0xfcfcfcfcfcfcfcfc,0xff000000ff000000,0xff0fff00ff0fff00,0xff33ff00ff33ff00,0xff3fff00ff3fff00,0xff55ff00ff55ff00,0xff5fff00ff5fff00,0xff77ff00ff77ff00,0xff88ff88ff88ff88,0xffa0ffa0ffa0ffa0,0xffaaff00ffaaff00,0xffaaffaaffaaffaa,0xffc0ffc0ffc0ffc0,0xffccff00ffccff00,0xffccffccffccffcc,0xfff0ff00fff0ff00,0xfff0fff0fff0fff0,0xffff0f00ffff0f00,0xffff3300ffff3300,0xffff3f00ffff3f00,0xffff5500ffff5500,0xffff5f00ffff5f00,0xffff7700ffff7700,0xffff8888ffff8888,0xffffa0a0ffffa0a0]
def words4 : Array Nat := #[0xffffaa00ffffaa00,0xffffaaaaffffaaaa,0xffffc0c0ffffc0c0,0xffffcc00ffffcc00,0xffffccccffffcccc,0xfffff000fffff000,0xfffff0f0fffff0f0,0xffffff00ffffff00,0xffffff88ffffff88,0xffffffa0ffffffa0,0xffffffaaffffffaa,0xffffffc0ffffffc0,0xffffffccffffffcc,0xfffffff0fffffff0]
def wordBlocks : Array (Array Nat) := #[words0,words1,words2,words3,words4]
def extraWord (i : Nat) : W := repeated (((wordBlocks[i/32]?).getD #[])[i % 32]?.getD 0)
def extras : Nat → Nat → List W
  | 0,_=>[]
  | k+1,n=>extraWord (n % 256) :: extras k (n / 256)
def decodeState (n : Nat) : List W × Nat :=
  let used:=(n/8) % 64
  let base:=raw.zipIdx.filterMap fun (w,i)=>if used.testBit i then some w else none
  (canon (base++extras ((n/512) % 8) (n/4096)),n % 8)
def m0b0 : Array Nat := #[0xfb]
def m0 : Array (Array Nat) := #[m0b0]
def m1b0 : Array Nat := #[0x32f9,0x42f9,0x52f9,0x62f9,0x72f9,0x82f9,0x92f9,0xa2f9,0xb2f9,0xf2f9,0x132f9,0x152f9,0x182f9,0x1d2f9,0x212f9,0x232f9,0x292f9,0x2e2f9,0x322f9,0x342f9,0x3e2f9,0x3f2f9,0x402f9,0x422f9,0x452f9,0x462f9,0x482f9,0x532f9,0x542f9,0x562f9,0x602f9,0x672f9]
def m1b1 : Array Nat := #[0x682f9,0x722f9,0x752f9,0x772f9,0x812f9,0x842f9,0x862f9,0x872f9,0x62ba,0xa27a,0x8727a,0x872ba,0x8723b]
def m1 : Array (Array Nat) := #[m1b0,m1b1]
def m2b0 : Array Nat := #[0x67604d8,0x67534e8,0x60534f0,0x8700439,0x8701439,0x8702439,0x8703439,0x8704439,0x8705439,0x62b9,0x8706439,0x8707439,0x8708439,0x8709439,0xa279,0x870a439,0x870b439,0xd2f1,0xe2f1,0x870f439,0x112e9,0x122e9,0x8713439,0x142b9,0x8715439,0x8716439,0x17279,0x8718439,0x1a2f1,0x1b2f1,0x1c2f1,0x871d439]
def m2b1 : Array Nat := #[0x1f2d9,0x202d9,0x8721439,0x222b9,0x8723439,0x8724439,0x25279,0x262b9,0x27279,0x8729439,0x2b2e9,0x2c2e9,0x2d2e9,0x872e439,0x302d9,0x312d9,0x8732439,0x332b9,0x8734439,0x8735439,0x36279,0x372b9,0x38279,0x3a2d9,0x3b2b9,0x3c279,0x873e439,0x533e4e1,0x873f439,0x603f4d1,0x8740439,0x412b9]
def m2b2 : Array Nat := #[0x8742439,0x8743439,0x44279,0x8745439,0x67454c9,0x8746439,0x472b9,0x8748439,0x8749439,0x4a279,0x8753439,0x8754439,0x552b9,0x8756439,0x8757439,0x58279,0x8760439,0x8767439,0x8768439,0x78279,0x79279,0x7b279,0x7e279,0x7f279,0x80279,0x82279,0x83279,0x85279,0x87279,0x692b9,0x6a2b9,0x6c2b9]
def m2b3 : Array Nat := #[0x6f2b9,0x702b9,0x712b9,0x8772439,0x732b9,0x742b9,0x8775439,0x762b9,0x8777439,0x872b9,0x8781439,0x8784439,0x8786439,0x8a87439,0x8c87439,0x8d87439,0x592d9,0x5b2d9,0x5d2d9,0x622d9,0x642d9,0x4c2e9,0x4e2e9,0x502e9,0x612e9,0x632e9,0x4b2f1,0x4d2f1,0x4f2f1,0x5a2f1,0x5c2f1,0x8723a]
def m2 : Array (Array Nat) := #[m2b0,m2b1,m2b2,m2b3]
def m3b0 : Array Nat := #[0x8c8a438,0x8d8a438,0x8d8c438,0x876760618,0x8d8760618,0x8d8767618,0x876753628,0x8c8753628,0x8c8767628,0x876053630,0x8a8753630,0x8a8760630,0x6760536c0,0x870c431,0x870d431,0x870e431,0x8710429,0x8711429,0x8712429,0x8719431,0x871a431,0x871b431,0x871c431,0x871e419,0x871f419,0x8720419,0x28239,0x872a429,0x872b429,0x872c429,0x872d429,0x872f419]
def m3b1 : Array Nat := #[0x8730419,0x8731419,0x39239,0x873a419,0x3d239,0x87533e621,0x87603f611,0x8a43431,0x876745609,0x8c49429,0x8d57419,0x6b239,0x6d239,0x6e239,0x7a239,0x7c239,0x7d239,0x87239,0x88239,0x89239,0x8b239,0x8759419,0x875b419,0x875d419,0x875f419,0x8762419,0x8764419,0x8766419,0x874c429,0x874e429,0x8750429,0x8752429]
def m3b2 : Array Nat := #[0x8761429,0x8763429,0x8765429,0x8267449,0x7367489,0x874b431,0x874d431,0x874f431,0x8751431,0x875a431,0x875c431,0x875e431,0x7f60451,0x7060491,0x674b4c1,0x604c4c1,0x7e53461,0x6f534a1,0x59534c1]
def m3 : Array (Array Nat) := #[m3b0,m3b1,m3b2]
def m4b0 : Array Nat := #[0x8d8c67608,0x8d8a60610,0x8c8a53620,0x87676053800,0x8d65409,0x8c66409,0x8b67409,0x8d5e411,0x8a5f411,0x8960411,0x87674b601,0x87604c601,0x8c51421,0x8a52421,0x8853421,0x875953601]
def m4 : Array (Array Nat) := #[m4b0]
def m5 : Array (Array Nat) := #[]
def mLevels : Array (Array (Array Nat)) := #[m0,m1,m2,m3,m4,m5]
def h0b0 : Array Nat := #[0x4b271d464c3863376436242343491a1842351b2262481e2d40452e19344a3d2161473c2c33443b283f413a253e]
def h0 : Array (Array Nat) := #[h0b0]
def h1b0 : Array Nat := #[0x605060518000500000b0000000003030200000b020000000000000000,0xc0e0c0e27002000000d04000000070702040110020401000000000000,0x108010828010808010d08110801020202010101001004010111000100,0x1050105011a010508010c050e050605050501027d0102020201011604010106000100,0x605060524000506000b0000000303000000030b020000000000000000,0xc0e0c0e2504200a020d04040407030400040716020401020404000400,0x10801082e010808011f08110802020100010201021004010111000100,0x1050101051b0105080100050e05000505050102010281020200000000000000000000,0x1573152f3a03000300005e0a0000000303000003020000000b000000000000,0xc0e0c0e3d0904090404090a02040407030400070204010410020404000400,0x105010533080101080c0506050101020201008c72010201021604010106000100,0x10501053408010108000500050100000002020000957001020000000000000000,0x150e150e41030003000b000000000003000000030200000b02000000000000,0x10801084501080108090d0d0a110802000100020201010d040d1011000100,0x10501054801052005090a06050101020001008d6e0504020a0101090706000100,0x60506054a0d052005090000050500000503060000966d0b0a0000090700000000,0xc0e0c0e38090009040d04000000000700000007060401160a040100000000,0x108010865010801081f085e080b0a02000100020601010800100401010b0b,0x10501056601050c05050503060105020001008e7b050002010101160401010303,0x6050605390d050005050503000500000503010000977a0b010000000000000303,0xc0e0c0e4f000000006b0020030000008f6a002003010000987900070b010000a16900000000,0x10801085000080b0051000802000000906800080201000099670801000000000000a6640000,0x10501055200050300000502000000914e0501000802010000a278000000000000a7630000,0x6050605530005030005000005030100009a0f00290b010000a377000000000000a84c0000,0xa0e0a0e54040d1002550473020001009237042f020101009b4b0d010204040100000104ab44,0x6050605560405070204050200010093360501040d02010100a4470204040100000104ac43,0x6050605570005070005000005030100009c49000d0b010000a5460000000000000000ad42,0x760e8b0e5802000000130176021401260217002b042204000017002b0023000000000000006b,0x20102016f02010201020102000100946201010101100100000602a93f2b0100001202ae3c,0x2010201590201020101000001020100009d610101100000000600aa3e030000001200af3b,0x32608a605a07000c030701b7022a11321100001430040421112f0b890b010b00000b0b51230b,0x165f885f5b13000d030301b602130d161f0404130d160d010d04040d105514060000211f220d]
def h1b1 : Array Nat := #[0x20102015c01001e010119020001000700000003000000,0x3000603030603067e0000070d01023206131504042b0601030000030389032b03,0x7000c03070c070c7f0404030c0102160c0109040409071609130c00002b0c2b09,0x20001020201020180010101010102010203000404160116010701000032013201,0x30001020300030682070001002a000200000017000003000003032f031703,0x70401020700070c8313040102130000090000090713090200000017001709,0x101020101020201020184000101020102130d0404130d1301071100002a0d2a01,0x10100010101020101021b1a5c0201010202010102020101020706040407060c0607010c06030600000306060603010601,0x10508010c050e055f080e0e0605050560082f080e0e0e0e011a8185010105050e0e050505050505,0x10508010c050e055f080e0e06050505600873080e0e0e0e011b7d85010105050e0e050505050505,0x11e1b020101020201010280332e6f07060c0607010c067f48255616010c0a03060606030106017e66245232011501760c150c,0x1191a02010102020101028434285907060c0607060c06834a275788010c0a0306060603060606823918538a0115018b0c150c,0xa0402d719f352c7c5b453d549e4d1d6c5a653a505838414f]
def h1 : Array (Array Nat) := #[h1b0,h1b1]
def h2b0 : Array Nat := #[0x1d03070325,0x18020a0325,0x19020a0925,0x506000b00000000030b020000000000000000,0x42029040d040404040731020401040404000400,0x10808011f081108010201021004010111000100,0x6000b000000030200000b020000000000000000,0x29040d0400000702040010020401000000000000,0x8010d0811080202010101001004010111000100,0x1020f,0x102020200013100010006000100,0x6000b000000030200000b020000000000000000,0x29040d0400000702040010020401000000000000,0x8010d0811080202010001021004010111000100,0x20f,0x2020200000000000000000000,0x300005e0a00000003030000000b000000000000,0x20002011e,0x20002011b,0x90404090a020404070704040410020404000400,0x20002013b,0x20002013c,0x200020000000000000000,0x10102010f,0x200020000000000000000,0x801010830050605010201027404060406000600,0x2000f,0x3000b0000000000031400000b02000000000000,0x20002013e,0x20002013f,0x200020133,0x108090d0d0a1108020201010d040d1011000100]
def h2b1 : Array Nat := #[0x108010834,0x108010840,0x102020a0001060706000100,0x10102010f,0x140b0a0000060700000000,0x26052005092906050504140a0601090706000600,0x502000f,0x105020177,0x5020063,0x9040d040000000007060404310a040100000000,0x200020142,0x200020143,0x200020144,0x1081f085e080b0a020601010800100401010b0b,0x108010846,0x108010847,0x50002010001100001000303,0x10502010f,0x5060b010000000000000303,0x2605300505050306050014010601740406040303,0x502000f,0x105020178,0x5020064,0x108010849,0x105020166,0x5020065,0x35002003010000394a00070b010000674900000000,0x30003153503001c035a03151c035b030731035c0717,0x80b00360008020100004d48080100000000000050440000,0x100010836010002017001080201590a2a010a170172,0x501000702010000684700000000000051430000,0x10502010f]
def h2b2 : Array Nat := #[0x501000702010000694600000000000052420000,0x503004b050600290b01000079450000000000007a410000,0x502000f,0x40d100237042f020101004e620d0102040401000001045633,0x704070c370704020154070c02015502867501010771,0x501000d020100006a4000000000000000006d3f,0x60502010f,0x501000d020100004f340000000000000000573e,0x4050704380506040d140104006b6104040404000004047c3d,0x102000f,0x2060114140126022704180400001a00190000000000000035,0x1010101070100000602533c0301000012026e1b,0x20002010f,0x10101010700000006006c3b030000001200581e,0x20102014c010101011001000006027b3a5d01000012026f2e,0x20102000f,0x7060c142c110000143004041d11240b010b00000b0b36190b,0x30615142d1f0404280d010d04040d1037140600001d1f180d,0x101020001000700000003000000,0x20002010f010207010301,0x20002000f020000000301,0x20002000f020007010000,0x300030c39030909035a,0x20002014d03010a0270,0x20002010f0301,0x20102014e07010a0254,0x20002010f0701,0x20002000f0200,0x20001020701000003010000,0x20002010f010007000300,0x20002010f020000000300,0x20002010f020007000000]
def h2b3 : Array Nat := #[0x300030c39030909035b,0x20002014d03010a0259,0x30002010f0300,0x3000003070001021015000003030103b3037503,0x20102014e07010a0255,0x30002010f0700,0x700040303040102060601063109100c00007509,0x20002010f0200,0x20001020102000003000404310107010000b401,0x101020001000700000003000000,0x3010002070001000200000003030003b2038703,0x70104020b040102060600061009020000008709,0x2000102010200000b0004041001070400000b01,0x70d01022206021f040421060603000003034b24031a03,0x40403b5010223300609040409073828090211000021302709,0x1010101010201024c0300040423262d010704000022262c01,0x300030c67030109015c,0x20002016803010c02,0x30003066903001c03,0x20102016a07011202,0x30003064f07001109,0x20002015003010a0272,0x20002015103010c02,0x30003065203001c03,0xa060a06530a060201,0x30603066c0a060201,0x20102015609010a0271,0x20102016d09011202,0x90009265709001109,0xa5d09136e0a130201,0x9030a03580a030201,0x20101020706040410010404030600000b01000000000000]
def h2 : Array (Array Nat) := #[h2b0,h2b1,h2b2,h2b3]
def h3b0 : Array Nat := #[0x3060323,0x2020322,0x2020721,0x307031d,0x3020122,0x7020721,0x20a031d,0x3060323,0xa120721,0x20a091d,0x9120323,0xa120a22,0x1d020202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def h3b1 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x3151c031e0307b0031b0717,0x1080201190a2a010a170124,0x6030374120328031217032e,0x70c0201180286b10101071a,0xc09062912062d0606060625,0x101130106022c2a010a0227,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x30909031e,0x3010a0219,0x7010a0218,0x30109011b,0x0,0x0,0x306120328,0x0,0x0,0x70612092d,0x3010a0224,0x0,0x0,0x30612032e]
def h3b2 : Array Nat := #[0x0,0x0,0xa0602012c,0x201020118,0x201020118,0x9010a021a,0x0,0x0,0x926120925,0x0,0x0,0xa13020127,0x201020119,0x201020119,0x20102011a,0x201020124,0x12031c031e,0x1c0312031e,0x20102011b]
def h3 : Array (Array Nat) := #[h3b0,h3b1,h3b2]
def h4b0 : Array Nat := #[0x25d02,0x21c02,0x1c1c5d,0x20202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def h4 : Array (Array Nat) := #[h4b0]
def h5 : Array (Array Nat) := #[]
def hLevels : Array (Array (Array Nat)) := #[h0,h1,h2,h3,h4,h5]
def lengths : Array Nat := #[1,45,128,83,16,0]
def levelSize (level : Nat) : Nat := lengths[level]?.getD 0

def blockGet (all : Array (Array (Array Nat))) (level id : Nat) : Option Nat := do
  let base←all[level]?
  let slab←base[id/32]?
  slab[id % 32]?

def stateAt (level id : Nat) : Option (List W × Nat) :=
  if id < levelSize level then (blockGet mLevels level id).map decodeState else none

def hintAt (level id : Nat) : Nat := (blockGet hLevels level id).getD 0
end Data12783

namespace LiveAIG.InputSym

def bank (i : Fin 6) : Nat := ![0xfac688,0xf9ab08,0xf74650,0xf59d10,0xef2a60,0xee9ca0] i
def digit (i : Fin 6) (j : Nat) := (bank i >>> (3*j)) % 8
def rowIndex (i : Fin 6) (r : Nat) := r/8*8 + digit i (r % 8)
def stripe : W := 0x01010101010101010101010101010101
def channel (w : W) (src dst : Nat) := ((w >>> src) &&& stripe) <<< dst

def move (i : Fin 6) (w : W) : W :=
  channel w (digit i 0) 0 |||
  channel w (digit i 1) 1 |||
  channel w (digit i 2) 2 |||
  channel w (digit i 3) 3 |||
  channel w (digit i 4) 4 |||
  channel w (digit i 5) 5 |||
  channel w (digit i 6) 6 |||
  channel w (digit i 7) 7

theorem cardStripe : ∀(r : R) (d : Fin 8),
    (!decide (r.val<d.val) && stripe.getLsbD (r.val-d.val)) = decide (r.val % 8=d.val) := by
  decide +kernel

theorem atChannel (w : W) (src : Nat) (d : Fin 8) (r : R) :
    (channel w src d.val).getLsbD r.val =
      if r.val % 8=d.val then w.getLsbD (r.val/8*8+src) else false := by
  simp only [channel, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    r.isLt, decide_true, Bool.true_and]
  rw [Bool.and_comm (w.getLsbD _) _, ←Bool.and_assoc, cardStripe]
  by_cases h:r.val % 8=d.val
  · simp [h, show src+(r.val-d.val)=r.val/8*8+src by omega]
  · simp [h]

theorem bit_move (i : Fin 6) (w : W) (r : R) :
    (move i w).getLsbD r.val = w.getLsbD (rowIndex i r.val) := by
  have eq (k : Nat) (hk : k<8) : (channel w (digit i k) k).getLsbD r.val =
      if r.val % 8=k then w.getLsbD (r.val/8*8+digit i k) else false :=
    atChannel w (digit i k) ⟨k,hk⟩ r
  simp only [move,BitVec.getLsbD_or]
  rw [eq 0 (by decide)]
  rw [eq 1 (by decide)]
  rw [eq 2 (by decide)]
  rw [eq 3 (by decide)]
  rw [eq 4 (by decide)]
  rw [eq 5 (by decide)]
  rw [eq 6 (by decide)]
  rw [eq 7 (by decide)]
  have bound := Nat.mod_lt r.val (by decide : 0<8)
  generalize h : r.val % 8 = j at *
  interval_cases j <;> simp_all [rowIndex]

theorem inv : ∀i : Fin 6, ∃j : Fin 6, ∀r:R, rowIndex i (rowIndex j r.val)=r.val := by
  decide +kernel
theorem indexBound : ∀i : Fin 6, ∀r:R, rowIndex i r.val<128 := by decide +kernel
theorem indexOrigin : ∀i : Fin 6, rowIndex i 0=0 := by decide +kernel

theorem moveInj (i : Fin 6) : Function.Injective (move i) := by
  intro w z same
  obtain ⟨j,ij⟩:=inv i
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  let r' : R := ⟨rowIndex j r, indexBound j ⟨r,hr⟩⟩
  have h:=congrArg (fun u : W=>u.getLsbD r'.val) same
  change (move i w).getLsbD r'.val=(move i z).getLsbD r'.val at h
  rw [bit_move i w r', bit_move i z r'] at h
  have sameRow : rowIndex i (rowIndex j r)=r := ij ⟨r,hr⟩
  change w.getLsbD (rowIndex i (rowIndex j r))=z.getLsbD (rowIndex i (rowIndex j r)) at h
  rwa [sameRow] at h

theorem moveZero (i : Fin 6) : move i 0=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rw [bit_move i 0 ⟨r,hr⟩]
  simp

theorem moveAnd (i : Fin 6) (w z : W) : move i (w &&& z)=move i w &&& move i z := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rw [bit_move i _ ⟨r,hr⟩, BitVec.getLsbD_and, BitVec.getLsbD_and, bit_move i w ⟨r,hr⟩, bit_move i z ⟨r,hr⟩]

theorem moveNeg (i : Fin 6) (w : W) : move i (~~~w) = ~~~(move i w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rw [bit_move i _ ⟨r,hr⟩]
  simp only [BitVec.getLsbD_not, indexBound i ⟨r,hr⟩, hr, decide_true, Bool.true_and]
  rw [bit_move i w ⟨r,hr⟩]

theorem moveSigned (i : Fin 6) (w : W) (s : Bool) : move i (signed w s)=signed (move i w) s := by
  cases s
  · rfl
  · exact moveNeg i w

theorem moveNorm (i : Fin 6) (w : W) : move i (norm w)=norm (move i w) := by
  have h : (move i w)[0]=w[0] := by
    have eq:=bit_move i w 0
    simpa only [Fin.val_zero, indexOrigin, BitVec.getLsbD_eq_getElem (by decide : 0<128)] using eq
  simp only [norm,moveSigned,h]

theorem moveMade (i : Fin 6) (a b : W) (sa sb : Bool) :
    move i (made a b sa sb)=made (move i a) (move i b) sa sb := by
  simp only [made,moveNorm,moveAnd,moveSigned]

theorem mappedDrop (i : Fin 6) (s : List W) (a : W) (k : Bool) :
    (drop s a k).map (move i)=drop (s.map (move i)) (move i a) k := by
  cases k
  · exact List.map_erase (moveInj i) _
  · rfl

theorem mapRun (i : Fin 6) {t s n c} (r : Run t s n c) :
    Run (move i t) (s.map (move i)) n c := by
  induction r with
  | done=>simpa only [List.map_cons, List.map_nil, moveNorm] using (Run.done (t:=move i t))
  | @gate s n c a b sa sb ka kb ha hb ne nz fresh _ ih=>
    have injective:=moveInj i
    have nz' : made (move i a) (move i b) sa sb≠0 := by
      rw [←moveMade, ←moveZero i]
      exact fun e=>nz (injective e)
    have fresh' : made (move i a) (move i b) sa sb∉s.map (move i) := by
      rintro el
      obtain ⟨w,mem,e⟩:=List.mem_map.mp el
      rw [←moveMade] at e
      exact fresh (injective e ▸ mem)
    apply Run.gate _ _ sa sb ka kb (List.mem_map_of_mem ha) (List.mem_map_of_mem hb)
      (fun e=>ne (injective e)) nz' fresh'
    simpa only [after,List.map_cons,mappedDrop,moveMade] using ih

theorem closedRun (i : Fin 6) {t s n c} (r : Run t s n c) (fixed : move i t=t) :
    Run t (canon (s.map (move i))) n c := by
  exact fixed ▸ canonRun (mapRun i r)

theorem keeps12122 : ∀i : Fin 6, move i 0xfee8e880fe008000fee8e880fe008000 =
    0xfee8e880fe008000fee8e880fe008000 := by decide +kernel

end LiveAIG.InputSym

namespace LiveAIG.SparseConflicts
abbrev Board := BitVec 4096
def stripe (i : Nat) : Board := BitVec.ofNat 4096 ((2^4096-1)/(2^(2^i)+1))
def differences (p n : Board) (d : Nat) := (p &&& (n >>> d)) ||| (n &&& (p >>> d))

structure Column where
  w : W
  stride : Nat
  low : Board
  single : Board

structure Rules where
  a0 : Bool
  a1 : Bool
  b0 : Bool
  b1 : Bool
  eq : Bool
  ne : Bool

def restrictions (p n : Board) (a b : Column) : Rules :=
  let s0:=a.single &&& b.low
  let s1:=a.single &&& ~~~b.low
  let t0:=b.single &&& a.low
  let t1:=b.single &&& ~~~a.low
  let lo:=a.low &&& b.low
  let mid:=(~~~a.low) &&& b.low
  ⟨s0 != 0,s1 != 0,t0 != 0,t1 != 0,
   differences p n (b.stride+a.stride) &&& lo != 0,
   differences p n (b.stride-a.stride) &&& mid != 0⟩

def legal (r : Rules) (ka kb sa sb : Bool) :=
  (ka || ((!r.a0 || sb) && (!r.a1 || !sb))) &&
  (kb || ((!r.b0 || sa) && (!r.b1 || !sa))) &&
  (ka || kb || ((!r.eq || sa == sb) && (!r.ne || sa != sb)))

def options (s : List W) (budget : Nat) (a b : W) (rules : Rules) (ka kb : Bool) :=
  let spent:=ka.toNat+kb.toNat
  if spent≤budget then
    let left:=drop (drop s a ka) b kb
    flags.flatMap fun sa=>flags.filterMap fun sb=>
      if legal rules ka kb sa sb then
        let g:=made a b sa sb
        if g != 0 && !s.contains g then some (canon (g::left),budget-spent) else none
      else none
  else []

def transpose (r : Rules) : Rules := ⟨r.b0,r.b1,r.a0,r.a1,r.eq,r.ne⟩

end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts

def Point (t : W) (s : List W) (a b : W) (x y u v : Bool) : Prop :=
  ∃ p q : R, t[p.val] ≠ t[q.val] ∧ a[p.val]=x ∧ b[p.val]=y ∧ a[q.val]=u ∧ b[q.val]=v ∧
    ∀w∈s,w≠a → w≠b → w[p.val]=w[q.val]

def Justified (t : W) (s : List W) (a b : W) (r : Rules) : Prop :=
  (r.a0=true → Point t s a b false false true false) ∧
  (r.a1=true → Point t s a b false true true true) ∧
  (r.b0=true → Point t s a b false false false true) ∧
  (r.b1=true → Point t s a b true false true true) ∧
  (r.eq=true → Point t s a b false false true true) ∧
  (r.ne=true → Point t s a b true false false true)

def distinguishes (ka kb sa sb x y u v : Bool) : Bool :=
  (ka && (x != u)) || (kb && (y != v)) || (((x != sa) && (y != sb)) != ((u != sa) && (v != sb)))

theorem onePass {t s a b x y u v sa sb ka kb k c} (nd:s.Nodup)
    (pt : Point t s a b x y u v) (run : Run t (after s a b (made a b sa sb) ka kb) k c) :
    distinguishes ka kb sa sb x y u v=true := by
  obtain ⟨p,q,tar,ax,by',au,bv,other⟩ := pt
  by_contra fail
  have no : distinguishes ka kb sa sb x y u v = false := by simpa using fail
  simp only [distinguishes,Bool.or_eq_false_iff,bne_eq_false_iff_eq] at no
  apply tar (agreeRun run ?_)
  intro w hm
  rcases List.mem_cons.mp hm with rfl|tail
  · apply signedCong
    have evalBit (z:W) (sg:Bool) (row:R) : (signed z sg)[row.val]=(z[row.val] != sg) := by
      cases sg <;> simp [signed]
    simp only [BitVec.getElem_and,evalBit,ax,by',au,bv]
    exact no.2
  · have old:=dropSubset _ _ _ _ (dropSubset _ _ _ _ tail)
    by_cases wa:w=a
    · subst w
      by_cases keep:ka=true
      · rw [keep] at no
        simpa [ax,au] using no.1.1
      · have cut : ka=false := by simpa using keep
        have inList := dropSubset _ _ _ _ tail
        rw [cut] at inList
        exact ((nd.mem_erase_iff.mp inList).1 rfl).elim
    by_cases wb:w=b
    · subst w
      by_cases keep:kb=true
      · rw [keep] at no
        simpa [by',bv] using no.1.2
      · have cut : kb=false := by simpa using keep
        have kept : (drop s a ka).Nodup := by cases ka <;> simp [drop,nd,nd.erase]
        rw [cut] at tail
        exact ((kept.mem_erase_iff.mp tail).1 rfl).elim
    exact other w old wa wb

theorem allPass : ∀a0 a1 b0 b1 eq ne ka kb sa sb : Bool,
    (a0=true → distinguishes ka kb sa sb false false true false=true) →
    (a1=true → distinguishes ka kb sa sb false true true true=true) →
    (b0=true → distinguishes ka kb sa sb false false false true=true) →
    (b1=true → distinguishes ka kb sa sb true false true true=true) →
    (eq=true → distinguishes ka kb sa sb false false true true=true) →
    (ne=true → distinguishes ka kb sa sb true false false true=true) →
    legal ⟨a0,a1,b0,b1,eq,ne⟩ ka kb sa sb=true := by decide +kernel

theorem legalSound {t s a b sa sb ka kb k c} {r : Rules} (nd:s.Nodup)
    (data : Justified t s a b r) (run : Run t (after s a b (made a b sa sb) ka kb) k c) :
    legal r ka kb sa sb=true := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩:=data
  exact allPass _ _ _ _ _ _ _ _ _ _ (fun h=>onePass nd (h1 h) run) (fun h=>onePass nd (h2 h) run)
    (fun h=>onePass nd (h3 h) run) (fun h=>onePass nd (h4 h) run)
    (fun h=>onePass nd (h5 h) run) (fun h=>onePass nd (h6 h) run)
end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts
abbrev CubeTag := Fin 4096

def Realizes (s : List W) (index : W → Nat) (r : R) (x : Nat) :=
  ∀w∈s,w[r.val]=x.testBit (index w)

def Cover (t : W) (s : List W) (index : W → Nat) (p n : Board) :=
  ∀u : CubeTag, (p[u.val]=true → ∃r:R, t[r.val]=true ∧ Realizes s index r u.val) ∧
    (n[u.val]=true → ∃r:R, t[r.val]=false ∧ Realizes s index r u.val)

def Opp (p n : Board) (u v : CubeTag) := (p[u.val]=true ∧ n[v.val]=true) ∨ (n[u.val]=true ∧ p[v.val]=true)

theorem findHit {p n mask:Board} {d:Nat} (bad : (differences p n d &&& mask) != 0) :
    ∃u v : CubeTag,mask[u.val]=true ∧ v.val=u.val+d ∧ Opp p n u v := by
  have any : ∃ u : CubeTag,(differences p n d &&& mask)[u.val]=true := by
    by_contra! none
    apply (bne_iff_ne.mp bad)
    ext j hj
    simpa using none ⟨j,hj⟩
  obtain ⟨u,atU⟩:=any
  simp only [BitVec.getElem_and,Bool.and_eq_true] at atU
  have bits:=atU.1
  simp only [differences,BitVec.getElem_or,Bool.or_eq_true,BitVec.getElem_and,Bool.and_eq_true,
    BitVec.getElem_ushiftRight_eq_decide_getElem,decide_eq_true_eq] at bits
  rcases bits with ⟨pos,z,neg⟩|⟨neg,z,pos⟩
  · exact ⟨u,⟨d+u.val,z⟩,atU.2,Nat.add_comm ..,Or.inl ⟨pos,neg⟩⟩
  · exact ⟨u,⟨d+u.val,z⟩,atU.2,Nat.add_comm ..,Or.inr ⟨neg,pos⟩⟩

def changeMask (i j : Nat) (a b : Bool) := (if a then 2^i else 0) ^^^ (if b then 2^j else 0)

theorem changeBit (i j k : Nat) (a b : Bool) :
    (changeMask i j a b).testBit k = ((a && (i==k)) != (b && (j==k))) := by
  cases a <;> cases b <;> simp [changeMask,Nat.testBit_xor,Nat.testBit_two_pow] <;> grind

theorem emitPoint {t s index p n a b i j da db x y} {u v : CubeTag}
    (cov:Cover t s index p n) (ia:index a=i) (ib:index b=j) (ij:i≠j) (aa:a∈s) (bb:b∈s)
    (uniq:∀w∈s,∀z∈s,index w=index z → w=z)
    (both:Opp p n u v) (atA:u.val.testBit i=x) (atB:u.val.testBit j=y)
    (jump:v.val=u.val ^^^ changeMask i j da db) :
    Point t s a b x y (x != da) (y != db) := by
  have rows : ∃r q : R, t[r.val] ≠ t[q.val] ∧ Realizes s index r u.val ∧ Realizes s index q v.val := by
    rcases both with ⟨h,k⟩|⟨h,k⟩
    · obtain ⟨r,rs,good⟩:=(cov u).1 h
      obtain ⟨q,qs,after⟩:=(cov v).2 k
      exact ⟨r,q,by simp [rs,qs],good,after⟩
    · obtain ⟨r,rs,good⟩:=(cov u).2 h
      obtain ⟨q,qs,after⟩:=(cov v).1 k
      exact ⟨r,q,by simp [rs,qs],good,after⟩
  obtain ⟨r,q,tar,raw,last⟩:=rows
  refine ⟨r,q,tar,by simpa [ia,atA] using raw a aa,by simpa [ib,atB] using raw b bb,?_,?_,?_⟩
  · rw [last a aa,ia,jump,Nat.testBit_xor,changeBit,atA]
    simp [beq_eq_false_iff_ne.mpr (Ne.symm ij)]
  · rw [last b bb,ib,jump,Nat.testBit_xor,changeBit,atB]
    simp [beq_eq_false_iff_ne.mpr ij]
  · intro w wm wa wb
    have ni:index w≠i:=fun h=>wa (uniq w wm a aa (h.trans ia.symm))
    have nj:index w≠j:=fun h=>wb (uniq w wm b bb (h.trans ib.symm))
    rw [raw w wm,last w wm,jump,Nat.testBit_xor,changeBit]
    simp [beq_eq_false_iff_ne.mpr (Ne.symm ni),beq_eq_false_iff_ne.mpr (Ne.symm nj)]
end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts
abbrev Idx := Fin 12
abbrev Tag := Fin 4096

abbrev indexGeometry (i : Idx) (u : Tag) :=
  (stripe i.val)[u.val] = !(u.val.testBit i.val) ∧
  (u.val.testBit i.val = false → u.val + 2^i.val = u.val ^^^ 2^i.val ∧ u.val + 2^i.val < 4096) ∧
  (u.val.testBit i.val = true → u.val - 2^i.val = u.val ^^^ 2^i.val ∧ 2^i.val ≤ u.val)
end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts

def valueBand (j : Idx) (value : Bool) : Board := if value then ~~~stripe j.val else stripe j.val

variable (geom : ∀i : Idx,∀u : Tag,indexGeometry i u)

include geom in
theorem atBand {u:Tag} {j:Idx} {v:Bool} (h : (valueBand j v)[u.val]=true) : u.val.testBit j.val=v := by
  have z := (geom j u).1
  cases v with
  | false =>
    change (stripe j.val)[u.val]=true at h
    rw [z] at h
    simpa only [Bool.not_eq_true'] using h
  | true =>
    change (~~~stripe j.val)[u.val]=true at h
    rw [BitVec.getElem_not,z] at h
    simpa only [Bool.not_not] using h

theorem complementCoord {i j : Idx} (ne : i≠j) (x:Nat) :
    (x ^^^ 2^i.val).testBit j.val = x.testBit j.val := by
  have n:i.val≠j.val:=fun h=>ne (Fin.ext h)
  simp [Nat.testBit_xor,Nat.testBit_two_pow,n,Ne.symm n]

include geom in
theorem singleMaterial {t s index p n a b} {i j:Idx} {v:Bool}
    (cov:Cover t s index p n) (ia:index a=i.val) (ib:index b=j.val) (ij:i≠j) (aa:a∈s) (bb:b∈s)
    (uniq:∀w∈s,∀z∈s,index w=index z → w=z)
    (hit : (differences p n (2^i.val) &&& stripe i.val &&& valueBand j v) != 0) :
    Point t s a b false v true v := by
  rw [BitVec.and_assoc] at hit
  obtain ⟨u,z,part,off,rows⟩:=findHit hit
  simp only [BitVec.getElem_and,Bool.and_eq_true] at part
  have atI : u.val.testBit i.val=false := by simpa [(geom i u).1] using part.1
  have atJ := atBand geom part.2
  have jump : z.val=u.val ^^^ changeMask i.val j.val true false := by
    simpa [changeMask] using off.trans ((geom i u).2.1 atI).1
  exact (by simpa using emitPoint cov ia ib (fun h=>ij (Fin.ext h)) aa bb uniq rows atI atJ jump)

theorem flipPoint {t s a b x y u v} (h : Point t s a b x y u v) : Point t s b a y x v u := by
  obtain ⟨r,q,op,ax,by',au,bv,rest⟩:=h
  exact ⟨r,q,op,by',ax,bv,au,fun w wm wb wa=>rest w wm wa wb⟩

include geom in
theorem bothMaterial {t s index p n a b} {i j:Idx} {v:Bool}
    (cov:Cover t s index p n) (ia:index a=i.val) (ib:index b=j.val) (ij:i<j) (aa:a∈s) (bb:b∈s)
    (uniq:∀w∈s,∀z∈s,index w=index z → w=z)
    (hit : (differences p n (if v then 2^j.val-2^i.val else 2^j.val+2^i.val) &&&
      (valueBand i v &&& stripe j.val)) != 0) : Point t s a b v false (!v) true := by
  obtain ⟨u,z,part,off,rows⟩:=findHit hit
  simp only [BitVec.getElem_and,Bool.and_eq_true] at part
  have atI := atBand geom part.1
  have atJ : u.val.testBit j.val=false := by simpa [(geom j u).1] using part.2
  have ne : i≠j := ne_of_lt ij
  have n : i.val ≠ j.val := fun h=>ne (Fin.ext h)
  have upper : 2^i.val ≤ 2^j.val := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt ij)
  have jump : z.val=u.val ^^^ changeMask i.val j.val true true := by
    cases v with
    | false =>
      obtain ⟨first,bd⟩ := (geom i u).2.1 atI
      let m : Tag := ⟨u.val+2^i.val,bd⟩
      have x : m.val=u.val ^^^ 2^i.val := first
      have low:m.val.testBit j.val=false := by rw [x,complementCoord ne];exact atJ
      have second:=((geom j m).2.1 low).1
      simp [changeMask,←Nat.xor_assoc,←x,←second] at *
      omega
    | true =>
      obtain ⟨first,le⟩ := (geom i u).2.2 atI
      let m : Tag := ⟨u.val-2^i.val,lt_of_le_of_lt (Nat.sub_le ..) u.isLt⟩
      have x : m.val=u.val ^^^ 2^i.val := first
      have low:m.val.testBit j.val=false := by rw [x,complementCoord ne];exact atJ
      have second:=((geom j m).2.1 low).1
      simp [changeMask,←Nat.xor_assoc,←x,←second] at *
      omega
  simpa using emitPoint cov ia ib n aa bb uniq rows atI atJ jump
end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts

def denseSig (s : List W) (r:R) : Nat := s.foldr (fun w acc=>Nat.bit (w[r.val]) acc) 0

def denseWords (s : List W) : List R → Board
  | [] => 0
  | r::rs=> ((1 : Board) <<< denseSig s r) ||| denseWords s rs

def stateBoards (t : W) (s : List W) :=
  let rs:=List.finRange 128
  (denseWords s (rs.filter fun r=>t[r.val]),denseWords s (rs.filter fun r=> !t[r.val]))

theorem signatureColumn {s : List W} {w : W} (wm : w∈s) (r:R) :
    (denseSig s r).testBit (s.idxOf w)=w[r.val] := by
  induction s with
  | nil => simp at wm
  | cons a xs ih=>
    change (Nat.bit (a[r.val]) (denseSig xs r)).testBit ((a::xs).idxOf w)=w[r.val]
    by_cases same:w=a
    · subst w;simp
    · have old : w∈xs := (List.mem_cons.mp wm).resolve_left same
      rw [List.idxOf_cons_ne _ (Ne.symm same),Nat.testBit_bit_succ]
      exact ih old

theorem denseHit {s rows} {i:CubeTag} (hit : (denseWords s rows)[i.val]=true) :
    ∃ r∈rows,denseSig s r=i.val := by
  induction rows with
  | nil=> simp [denseWords] at hit
  | cons a xs ih=>
    simp only [denseWords,BitVec.getElem_or,Bool.or_eq_true] at hit
    rcases hit with current|other
    · refine ⟨a,by simp,?_⟩
      rw [BitVec.getElem_shiftLeft] at current
      have two := Bool.and_eq_true_iff.mp current
      have little : i.val - denseSig s a < 4096 := lt_of_le_of_lt (Nat.sub_le ..) i.isLt
      have one : ((1 : Board)[i.val-denseSig s a]'little) = decide (i.val-denseSig s a=0) := BitVec.getElem_one little
      rw [one] at two
      simp at two
      omega
    · obtain ⟨r,rm,val⟩:=ih other
      exact ⟨r,by simp [rm],val⟩

theorem denseCover (t : W) (s : List W) : Cover t s (fun w=>s.idxOf w) (stateBoards t s).1 (stateBoards t s).2 := by
  intro u
  constructor <;> intro h
  · obtain ⟨r,rm,tag⟩:=denseHit h
    refine ⟨r,(List.mem_filter.mp rm).2,fun w wm=>?_⟩
    rw [←tag,signatureColumn wm]
  · obtain ⟨r,rm,tag⟩:=denseHit h
    refine ⟨r,by simpa using (List.mem_filter.mp rm).2,fun w wm=>?_⟩
    rw [←tag,signatureColumn wm]
end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts

def entry (p n : Board) (w:W) (i:Nat) : Column :=
  ⟨w,2^i,stripe i,differences p n (2^i) &&& stripe i⟩

theorem fromMasks (geom : ∀i:Idx,∀u:Tag,indexGeometry i u) {t s index p n a b} {i j:Idx}
    (cov:Cover t s index p n) (ia:index a=i.val) (ib:index b=j.val) (ij:i<j) (aa:a∈s) (bb:b∈s)
    (uniq:∀w∈s,∀z∈s,index w=index z → w=z) :
    Justified t s a b (restrictions p n (entry p n a i.val) (entry p n b j.val)) := by
  have first := @singleMaterial geom t s index p n a b i j
  have second := @singleMaterial geom t s index p n b a j i
  have dbl := @bothMaterial geom t s index p n a b i j
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact fun hit=>first (v:=false) cov ia ib (ne_of_lt ij) aa bb uniq hit
  · exact fun hit=>first (v:=true) cov ia ib (ne_of_lt ij) aa bb uniq hit
  · exact fun hit=>flipPoint (second (v:=false) cov ib ia (ne_of_gt ij) bb aa uniq hit)
  · exact fun hit=>flipPoint (second (v:=true) cov ib ia (ne_of_gt ij) bb aa uniq hit)
  · exact fun hit=>dbl (v:=false) cov ia ib ij aa bb uniq hit
  · exact fun hit=>dbl (v:=true) cov ia ib ij aa bb uniq hit

theorem reversePoint {t s a b x y u v} (h : Point t s a b x y u v) : Point t s a b u v x y := by
  obtain ⟨p,q,op,ax,by',au,bv,rest⟩:=h
  exact ⟨q,p,Ne.symm op,au,bv,ax,by',fun w wm wa wb=>(rest w wm wa wb).symm⟩

theorem transposeRules {t s a b r} (j:Justified t s a b r) : Justified t s b a (transpose r) := by
  obtain ⟨j1,j2,j3,j4,j5,j6⟩:=j
  exact ⟨fun h=>flipPoint (j3 h),fun h=>flipPoint (j4 h),fun h=>flipPoint (j1 h),fun h=>flipPoint (j2 h),
    fun h=>flipPoint (j5 h),fun h=>reversePoint (flipPoint (j6 h))⟩

def ruleFor (p n : Board) (a b : Column) :=
  if a.stride < b.stride then restrictions p n a b else transpose (restrictions p n b a)

def candidateChildren (s : List W) (budget : Nat) (index : W→Nat) (p n : Board) :=
  let ws:=s.map fun w=>entry p n w (index w)
  ws.flatMap fun a=>ws.flatMap fun b=>
    if a.w.toNat < b.w.toNat then
      let r:=ruleFor p n a b
      flags.flatMap fun ka=>flags.flatMap fun kb=>options s budget a.w b.w r ka kb
    else []

def verifiedChildren (t : W) (s : List W) (budget : Nat) :=
  if s.length ≤ 12 ∧ s.Nodup then
    let (p,n):=stateBoards t s
    candidateChildren s budget (fun w=>s.idxOf w) p n
  else children t s budget

end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts

def checkGeometry (i u : Nat) :=
  let b:=u.testBit i
  let d:=2^i
  let z:=u ^^^ d
  ((stripe i).getLsbD u == !b) &&
    (if b then (u-d == z) && decide (d≤u) else (u+d == z) && decide (u+d<4096))

def checkIndex (i : Nat) := (List.range 4096).all (checkGeometry i)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem allGeometric : (List.range 12).all checkIndex=true := by decide +kernel

theorem geometryFast (i : Idx) (u : Tag) : indexGeometry i u := by
  have hi := List.all_eq_true.mp allGeometric i.val (List.mem_range.mpr i.isLt)
  have hu := List.all_eq_true.mp hi u.val (List.mem_range.mpr u.isLt)
  cases b : u.val.testBit i.val <;> simpa [indexGeometry,checkGeometry,b,BitVec.getLsbD_eq_getElem] using hu
end LiveAIG.SparseConflicts

namespace LiveAIG.SparseConflicts

theorem ruleForTrue {t s index p n a b} (cov:Cover t s index p n)
    (bounds:∀w∈s,index w<12) (uniq:∀w∈s,∀z∈s,index w=index z → w=z)
    (aa:a∈s) (bb:b∈s) (ne:a≠b) :
    Justified t s a b (ruleFor p n (entry p n a (index a)) (entry p n b (index b))) := by
  let i : Idx := ⟨index a,bounds a aa⟩
  let j : Idx := ⟨index b,bounds b bb⟩
  have nn : index a ≠ index b := fun h=>ne (uniq a aa b bb h)
  by_cases ij:index a < index b
  · have pw : 2^index a < 2^index b := Nat.pow_lt_pow_right (by decide) ij
    unfold ruleFor
    split <;> rename_i choice
    · exact fromMasks geometryFast cov (i:=i) (j:=j) rfl rfl ij aa bb uniq
    · exact (choice pw).elim
  · have ji:index b < index a := by omega
    have pw : ¬2^index a < 2^index b := by
      have := Nat.pow_lt_pow_right (by decide : 1 < 2) ji
      omega
    unfold ruleFor
    split <;> rename_i choice
    · exact (pw choice).elim
    · exact transposeRules (fromMasks geometryFast cov (i:=j) (j:=i) rfl rfl ji bb aa uniq)

theorem candidateOf {t s index p n a b sa sb ka kb k c budget} (nd:s.Nodup)
    (cov:Cover t s index p n) (bounds:∀w∈s,index w<12) (uniq:∀w∈s,∀z∈s,index w=index z → w=z)
    (aa:a∈s) (bb:b∈s) (lt:a.toNat<b.toNat) (nz:made a b sa sb≠0) (fresh:made a b sa sb∉s)
    (run:Run t (after s a b (made a b sa sb) ka kb) k c) (bound:c+ka.toNat+kb.toNat≤budget) :
    ∃q∈candidateChildren s budget index p n, Run t q.1 k c ∧ c≤q.2 := by
  let A:=entry p n a (index a)
  let B:=entry p n b (index b)
  have ne : a≠b := by intro h;subst b;omega
  have pass:=legalSound nd (ruleForTrue cov bounds uniq aa bb ne) run
  let spent:=ka.toNat+kb.toNat
  let rest:=drop (drop s a ka) b kb
  have paid : spent≤budget := by dsimp [spent];omega
  refine ⟨(canon (made a b sa sb::rest),budget-spent),?_,canonRun run,by dsimp [spent];omega⟩
  unfold candidateChildren
  refine List.mem_flatMap.mpr ⟨A,List.mem_map.mpr ⟨a,aa,rfl⟩,List.mem_flatMap.mpr ⟨B,List.mem_map.mpr ⟨b,bb,rfl⟩,?_⟩⟩
  have vals : A.w.toNat < B.w.toNat := lt
  rw [if_pos vals]
  refine List.mem_flatMap.mpr ⟨ka,hasFlag ka,List.mem_flatMap.mpr ⟨kb,hasFlag kb,?_⟩⟩
  unfold options
  rw [if_pos paid]
  refine List.mem_flatMap.mpr ⟨sa,hasFlag sa,List.mem_filterMap.mpr ⟨sb,hasFlag sb,?_⟩⟩
  change (if legal (ruleFor p n A B) ka kb sa sb then
    if made a b sa sb != 0 && !s.contains (made a b sa sb) then some _ else none else none) = some _
  simp [A,B,pass,fresh,rest,spent]
  exact ⟨nz,rfl⟩

theorem continueFast {t s n c budget} (rt:Run t s (n+1) c) (bound:c≤budget) :
    ∃q∈verifiedChildren t s budget,∃d≤q.2,Run t q.1 n d := by
  unfold verifiedChildren
  split <;> rename_i cond
  · obtain ⟨small,nd⟩:=cond
    have bounds : ∀w∈s,s.idxOf w<12 := fun w h=>lt_of_lt_of_le (List.idxOf_lt_length_of_mem h) small
    have uniq : ∀w∈s,∀z∈s,s.idxOf w=s.idxOf z → w=z := by
      intro w h z m eq
      have hw:=List.getElem_idxOf (x:=w) (xs:=s) (List.idxOf_lt_length_of_mem h)
      have hz:=List.getElem_idxOf (x:=z) (xs:=s) (List.idxOf_lt_length_of_mem m)
      rw [←hw,←hz];simp [eq]
    cases rt with
    | @gate _ _ c' a b sa sb ka kb aa bb ne nz fresh rest =>
      have out : ∃ q∈candidateChildren s budget (fun w=>s.idxOf w) (stateBoards t s).1 (stateBoards t s).2,
          Run t q.1 n c' ∧ c'≤q.2 := by
        have non : a.toNat≠b.toNat:=fun h=>ne (BitVec.eq_of_toNat_eq h)
        rcases lt_or_gt_of_ne non with l|l
        · exact candidateOf nd (denseCover t s) bounds uniq aa bb l nz fresh rest bound
        · have eq : made a b sa sb=made b a sb sa := by unfold made;rw [BitVec.and_comm]
          rw [swapAfter] at rest
          exact candidateOf nd (denseCover t s) bounds uniq bb aa l (eq ▸ nz) (eq ▸ fresh) rest (by omega)
      obtain ⟨q,mem,rr,db⟩:=out
      exact ⟨q,mem,c',db,rr⟩
  · exact continueRun rt bound
theorem runStepFast {t s n c budget} (rt : Run t s n c) (bound : c≤budget) :
    norm t∈s ∨ ∃k,n=k+1 ∧ ∃p∈verifiedChildren t s budget,∃d≤p.2,Run t p.1 k d := by
  cases n with
  | zero => cases rt;exact Or.inl List.mem_cons_self
  | succ k=>exact Or.inr ⟨k,rfl,continueFast rt bound⟩
end LiveAIG.SparseConflicts

namespace LiveAIG.InputSym
open SparseConflicts
theorem knownBasic {t s n c budget a b sa sb ka kb}
    (ha : a∈s) (hb : b∈s) (lt : a.toNat<b.toNat)
    (nz : made a b sa sb ≠ 0) (fresh : made a b sa sb ∉ s)
    (run : Run t (after s a b (made a b sa sb) ka kb) n c)
    (bound : c+ka.toNat+kb.toNat≤budget) :
    (canon (after s a b (made a b sa sb) ka kb), budget-(ka.toNat+kb.toNat))∈children t s budget := by
  let g:=made a b sa sb
  let remaining:=drop (drop s a ka) b kb
  let spent:=ka.toNat+kb.toNat
  have spentOk : spent≤budget := by dsimp [spent];omega
  have checked : accept t (classes t remaining) g=true := runAccept run
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  rw [if_pos lt]
  refine List.mem_flatMap.mpr ⟨ka,hasFlag ka,List.mem_flatMap.mpr ⟨kb,hasFlag kb,?_⟩⟩
  unfold phaseKids
  rw [if_pos spentOk]
  refine List.mem_flatMap.mpr ⟨sa,hasFlag sa,List.mem_filterMap.mpr ⟨sb,hasFlag sb,?_⟩⟩
  change (if g != 0 && !s.contains g && accept t (classes t remaining) g then
      some (canon (g::remaining),budget-spent) else none) = some _
  have avoid : g∉s := fresh
  have val : g≠0 := nz
  simp [avoid,checked]
  exact ⟨val,rfl,rfl⟩

theorem knownSparse {t s index p n a b sa sb ka kb k c budget} (nd:s.Nodup)
    (cov:Cover t s index p n) (bounds:∀w∈s,index w<12) (uniq:∀w∈s,∀z∈s,index w=index z → w=z)
    (aa:a∈s) (bb:b∈s) (lt:a.toNat<b.toNat) (nz:made a b sa sb≠0) (fresh:made a b sa sb∉s)
    (run:Run t (after s a b (made a b sa sb) ka kb) k c) (bound:c+ka.toNat+kb.toNat≤budget) :
    (canon (after s a b (made a b sa sb) ka kb), budget-(ka.toNat+kb.toNat))∈candidateChildren s budget index p n := by
  let A:=entry p n a (index a)
  let B:=entry p n b (index b)
  have ne : a≠b := by intro h;subst b;omega
  have pass:=legalSound nd (ruleForTrue cov bounds uniq aa bb ne) run
  let spent:=ka.toNat+kb.toNat
  let rest:=drop (drop s a ka) b kb
  have paid : spent≤budget := by dsimp [spent];omega
  unfold candidateChildren
  refine List.mem_flatMap.mpr ⟨A,List.mem_map.mpr ⟨a,aa,rfl⟩,List.mem_flatMap.mpr ⟨B,List.mem_map.mpr ⟨b,bb,rfl⟩,?_⟩⟩
  have vals : A.w.toNat < B.w.toNat := lt
  rw [if_pos vals]
  refine List.mem_flatMap.mpr ⟨ka,hasFlag ka,List.mem_flatMap.mpr ⟨kb,hasFlag kb,?_⟩⟩
  unfold options
  rw [if_pos paid]
  refine List.mem_flatMap.mpr ⟨sa,hasFlag sa,List.mem_filterMap.mpr ⟨sb,hasFlag sb,?_⟩⟩
  change (if legal (ruleFor p n A B) ka kb sa sb then
    if made a b sa sb != 0 && !s.contains (made a b sa sb) then some _ else none else none) = some _
  simp [A,B,pass,fresh,rest,spent]
  exact ⟨nz,rfl⟩

theorem knownLT {t s n c a b sa sb ka kb budget}
    (ha:a∈s) (hb:b∈s) (lt:a.toNat<b.toNat) (nz:made a b sa sb≠0)
    (fresh:made a b sa sb∉s) (tail:Run t (after s a b (made a b sa sb) ka kb) n c)
    (bound:c+ka.toNat+kb.toNat≤budget) :
    (canon (after s a b (made a b sa sb) ka kb), budget-(ka.toNat+kb.toNat))∈verifiedChildren t s budget := by
  unfold verifiedChildren
  split <;> rename_i cond
  · obtain ⟨small,nd⟩:=cond
    have bounds : ∀w∈s,s.idxOf w<12 := fun w h=>lt_of_lt_of_le (List.idxOf_lt_length_of_mem h) small
    have uniq : ∀w∈s,∀z∈s,s.idxOf w=s.idxOf z → w=z := by
      intro w h z m eq
      have hw:=List.getElem_idxOf (x:=w) (xs:=s) (List.idxOf_lt_length_of_mem h)
      have hz:=List.getElem_idxOf (x:=z) (xs:=s) (List.idxOf_lt_length_of_mem m)
      rw [←hw,←hz];simp [eq]
    exact knownSparse nd (denseCover t s) bounds uniq ha hb lt nz fresh tail bound
  · exact knownBasic ha hb lt nz fresh tail bound

theorem known {t s n c a b sa sb ka kb budget}
    (ha:a∈s) (hb:b∈s) (ne:a≠b) (nz:made a b sa sb≠0)
    (fresh:made a b sa sb∉s) (tail:Run t (after s a b (made a b sa sb) ka kb) n c)
    (bound:c+ka.toNat+kb.toNat≤budget) :
    (canon (after s a b (made a b sa sb) ka kb),budget-(ka.toNat+kb.toNat))∈verifiedChildren t s budget := by
  have diff : a.toNat≠b.toNat:=fun h=>ne (BitVec.eq_of_toNat_eq h)
  rcases lt_or_gt_of_ne diff with low|high
  · exact knownLT ha hb low nz fresh tail bound
  · have e : made a b sa sb=made b a sb sa := by unfold made;rw [BitVec.and_comm]
    rw [swapAfter] at tail ⊢
    rw [Nat.add_comm ka.toNat kb.toNat]
    exact knownLT hb ha high (e ▸ nz) (e ▸ fresh) tail (by omega)

def born (s next : List W) := (next.find? (fun w=> !s.contains w)).getD 0

theorem freshBorn {s next : List W} {g : W} (fresh:g∉s) (one:g∈next)
    (subset : ∀w∈next,w=g∨w∈s) : born s next=g := by
  unfold born
  cases h : next.find? (fun w=> !s.contains w) with
  | none =>
    have no := List.find?_eq_none.mp h g one
    simp [fresh] at no
  | some v =>
    obtain same|old := subset v (List.mem_of_find?_eq_some h)
    · simpa [same]
    · have yes := List.find?_some h
      simp [old] at yes

theorem canonSubset {s : List W} {a b g : W} {ka kb : Bool} :
    ∀w∈canon (after s a b g ka kb),w=g ∨ w∈s := by
  intro w m
  have z:= (List.perm_insertionSort _ _).mem_iff.mp m
  rcases List.mem_cons.mp z with eq|old
  · exact .inl eq
  · exact .inr (dropSubset _ _ _ _ (dropSubset _ _ _ _ old))

end LiveAIG.InputSym

namespace LiveAIG.IdentityLayers
open InputSym SparseConflicts
abbrev State := List W × Nat
abbrev Reader := Nat→Nat→Nat×Nat
abbrev Next := Nat→Option State

structure Setup where
  t : W
  cut : Nat→State→Nat→Bool
  sound : ∀{d p z n c},p.1.Nodup → cut d p z=true → n≤d → c≤p.2 → ¬Run t p.1 n c

def index (z : Nat) : Fin 6 := ⟨(z/2) % 6,by omega⟩
def shifted (i : Fin 6) (p : State) : State := (canon (p.1.map (move i)),p.2)
def tagOk (cfg : Setup) (next : Next) (d : Nat) (p : State) (z : Nat) :=
  if z % 2=0 then next (z/12)==some p
  else cfg.cut d p (z/2)
def checks (cfg : Setup) (read : Reader) (next : Next) (d : Nat) : List State→Nat→Bool
  | [],_=>true
  | p::ps,n=>
    let bits:=read p.2 n
    tagOk cfg next d p bits.1 && checks cfg read next d ps bits.2
def checked (cfg : Setup) (read : Reader) (next : Next) (d : Nat) (s : List W) (b data : Nat) :=
  decide s.Nodup && !(s.contains (norm cfg.t)) && checks cfg read next d (verifiedChildren cfg.t s b) data

theorem aTag {cfg read next d ps n} (yes : checks cfg read next d ps n=true)
    {p} (mem:p∈ps) : ∃z,tagOk cfg next d p z=true := by
  induction ps generalizing n with
  | nil=>simp at mem
  | cons u us ih=>
    simp only [checks,Bool.and_eq_true] at yes
    rcases List.mem_cons.mp mem with rfl|old
    · exact ⟨_,yes.1⟩
    · exact ih yes.2 old

def Dead (cfg : Setup) (d : Nat) (p : State) : Prop :=
  ∀{n c : Nat},n≤d → c≤p.2 → ¬Run cfg.t p.1 n c

theorem checkedSound {cfg read next s b data d}
    (yes : checked cfg read next d s b data=true)
    (later : ∀j p,next j=some p → Dead cfg d p) : Dead cfg (d+1) (s,b) := by
  intro n c rem cap run
  simp only [checked,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq] at yes
  change Run cfg.t s n c at run
  change c≤b at cap
  cases run with
  | done=>simpa using yes.1.2
  | @gate s n c a h sa sh ka kh aa hh ne nz fresh tail=>
    let child:=canon (after s a h (made a h sa sh) ka kh)
    let p : State := (child,b-(ka.toNat+kh.toNat))
    have mem : p∈verifiedChildren cfg.t s b := known aa hh ne nz fresh tail cap
    obtain ⟨z,ok⟩:=aTag yes.2 mem
    have budget : c≤p.2 := by change c≤b-(ka.toNat+kh.toNat);omega
    have small : n≤d := by omega
    have rest : Run cfg.t child n c := canonRun tail
    unfold tagOk at ok
    split at ok
    · exact later _ _ (eq_of_beq ok) small budget rest
    · have nd : child.Nodup := by
        apply (List.perm_insertionSort ..).nodup_iff.mpr
        apply List.nodup_cons.mpr
        refine ⟨fun old=>fresh (dropSubset _ _ _ _ (dropSubset _ _ _ _ old)),?_⟩
        have nds:=yes.1.1
        cases ka <;> cases kh <;> simp [drop,nds,nds.erase a,nds.erase h,(nds.erase a).erase h]
      exact cfg.sound nd ok small budget rest

end LiveAIG.IdentityLayers

namespace LiveAIG

def Pivot (t:W) (s:List W) (x:W) (r:R) : Prop :=
  ∃q:R,t[r.val]≠t[q.val] ∧ ∀w∈s,w≠x → w[r.val]=w[q.val]

private theorem madeCom (u v:W) (a b:Bool) : made u v a b=made v u b a := by
  unfold made;rw [BitVec.and_comm]

private theorem newPivot {t x g s r} {d:List W} (h:Pivot t s x r)
    (old:∀w∈d,w∈s ∧ w≠x) : Pivot t (g::d) g r := by
  obtain ⟨q,diff,agree⟩ := h
  refine ⟨q,diff,?_⟩
  intro w hmem neq
  rcases List.mem_cons.mp hmem with head|tail
  · exact (neq head).elim
  · exact agree _ (old _ tail).1 (old _ tail).2

private theorem forceOther {t u v:W} {s d:List W} {r:R} {a b:Bool} {k c}
    (pv:Pivot t s u r) (vm:v∈s) (vu:v≠u) (keep:∀w∈d,w∈s ∧ w≠u)
    (rest:Run t (made u v a b::d) k c) : (signed v b)[r.val]=true := by
  obtain ⟨q,tw,base⟩ := pv
  have other := signedCong b (base v vm vu)
  by_contra! no
  have zero:(signed v b)[r.val]=false := by cases h:(signed v b)[r.val] <;> simp_all
  have zero':(signed v b)[q.val]=false := other.symm.trans zero
  apply tw (agreeRun rest ?_)
  intro x hx
  rcases List.mem_cons.mp hx with rfl|old
  · apply signedCong
    simp only [BitVec.getElem_and,zero,zero',Bool.and_false]
  · exact base x (keep _ old).1 (keep _ old).2

private theorem signedDiff {u:W} {p n:R} (s:Bool) (h:u[p.val]≠u[n.val]) :
    (signed u s)[p.val]≠(signed u s)[n.val] := by
  cases s <;> simpa [signed] using h
private theorem resultDiff {u v:W} {p n:R} {a b:Bool}
    (d:u[p.val]≠u[n.val]) (pp:(signed v b)[p.val]=true) (nn:(signed v b)[n.val]=true) :
    (made u v a b)[p.val]≠(made u v a b)[n.val] := by
  have inner : (signed u a &&& signed v b)[p.val]≠(signed u a &&& signed v b)[n.val] := by
    simpa only [BitVec.getElem_and,pp,nn,Bool.and_true] using signedDiff a d
  exact signedDiff _ inner

private def mappedPivot (x u v g:W) := if x=u ∨ x=v then g else x

private theorem trackPivot {t u v x:W} {s d:List W} {p n:R} {a b:Bool} {k c}
    (um:u∈s) (vm:v∈s) (ne:u≠v) (xm:x∈s)
    (hd:∀w,w∈d ↔ w∈s ∧ w≠u ∧ w≠v)
    (px:Pivot t s x p) (nx:Pivot t s x n) (diff:x[p.val]≠x[n.val])
    (rest:Run t (made u v a b::d) k c) :
    let g := made u v a b
    let y := mappedPivot x u v g
    y∈g::d ∧ Pivot t (g::d) y p ∧ Pivot t (g::d) y n ∧ y[p.val]≠y[n.val] := by
  dsimp only
  have left : ∀w∈d,w∈s∧w≠u := fun w m=>⟨((hd w).mp m).1,((hd w).mp m).2.1⟩
  have right : ∀w∈d,w∈s∧w≠v := fun w m=>⟨((hd w).mp m).1,((hd w).mp m).2.2⟩
  by_cases one:x=u
  · subst x
    simp only [mappedPivot,eq_self, true_or,ite_true]
    exact ⟨List.mem_cons_self ..,newPivot px left,newPivot nx left,resultDiff diff
      (forceOther px vm ne.symm left rest) (forceOther nx vm ne.symm left rest)⟩
  by_cases two:x=v
  · subst x
    simp only [mappedPivot,eq_self,or_true,ite_true]
    have r' : Run t (made v u b a::d) k c := by rwa [madeCom v u b a]
    have dp := resultDiff (a:=b) diff (forceOther px um ne right r') (forceOther nx um ne right r')
    rw [madeCom v u b a] at dp
    exact ⟨List.mem_cons_self ..,newPivot px right,newPivot nx right,dp⟩
  simp only [mappedPivot,one,two,or_self,ite_false]
  have stay {r:R} (pv:Pivot t s x r) : Pivot t (made u v a b::d) x r := by
    obtain ⟨q,tw,z⟩ := pv
    refine ⟨q,tw,?_⟩
    intro w hw neq
    rcases List.mem_cons.mp hw with rfl|old
    · apply signedCong
      simp only [BitVec.getElem_and,signedCong a (z u um (Ne.symm one)),signedCong b (z v vm (Ne.symm two))]
    · exact z _ ((hd _).mp old).1 neq
  exact ⟨List.mem_cons_of_mem _ ((hd _).mpr ⟨xm,one,two⟩),stay px,stay nx,diff⟩

private theorem clashBoth {t u v:W} {s d:List W} {p n:R} {a b:Bool} {k c}
    (um:u∈s) (ne:u≠v) (right:∀w∈d,w∈s∧w≠v)
    (vp:Pivot t s v p) (vn:Pivot t s v n) (ud:u[p.val]≠u[n.val])
    (rest:Run t (made u v a b::d) k c) : False := by
  have r' : Run t (made v u b a::d) k c := by rwa [madeCom v u b a]
  exact signedDiff a ud ((forceOther vp um ne right r').trans (forceOther vn um ne right r').symm)

private theorem mainPivot {t s k cost} (run:Run t s k cost) : cost=0 → s.Nodup →
    ∀(x y:W) (p n:R), x∈s → y∈s → x≠y → Pivot t s x p → Pivot t s x n →
      Pivot t s y p → Pivot t s y n → x[p.val]≠x[n.val] → y[p.val]≠y[n.val] → False := by
  induction run with
  | done =>
    intro _ _ x y p n hx hy neq
    simp only [List.mem_singleton] at hx hy
    exact (neq (hx.trans hy.symm)).elim
  | @gate s k cost u v a b ka kb um vm ne nz newWord rest ih =>
    intro eq nd x y p n xm ym xy xp xn yp yn xd yd
    have zero : cost=0 ∧ ka=false ∧ kb=false := by
      cases ka <;> cases kb <;> simp_all [Bool.toNat]
    obtain ⟨rfl,rfl,rfl⟩ := zero
    let d := (s.erase u).erase v
    let g := made u v a b
    have hd : ∀w,w∈d ↔ w∈s ∧ w≠u ∧ w≠v := by
      intro w
      rw [show d=(s.erase u).erase v by rfl,(nd.erase u).mem_erase_iff,nd.mem_erase_iff]
      tauto
    have rr : Run t (g::d) k 0 := rest
    have nd' : (g::d).Nodup := by
      apply List.nodup_cons.mpr
      exact ⟨fun h=>newWord ((hd _).mp h).1,(nd.erase u).erase v⟩
    have l := trackPivot um vm ne xm hd xp xn xd rr
    have r := trackPivot um vm ne ym hd yp yn yd rr
    apply ih rfl nd' _ _ p n l.1 r.1 _ l.2.1 l.2.2.1 r.2.1 r.2.2.1 l.2.2.2 r.2.2.2
    by_cases hx:x=u ∨ x=v <;> by_cases hy:y=u ∨ y=v
    · exfalso
      rcases hx with e|e <;> rcases hy with f|f
      · exact xy (e.trans f.symm)
      · subst x;subst y
        exact clashBoth um ne (fun w h=>⟨((hd w).mp h).1,((hd w).mp h).2.2⟩) yp yn xd rr
      · subst x;subst y
        exact clashBoth um ne (fun w h=>⟨((hd w).mp h).1,((hd w).mp h).2.2⟩) xp xn yd rr
      · exact xy (e.trans f.symm)
    · simp only [mappedPivot,hx,hy,ite_true,ite_false]
      exact fun h=>newWord (h ▸ ym)
    · simp only [mappedPivot,hx,hy,ite_true,ite_false]
      exact fun h=>newWord (h ▸ xm)
    · simpa only [mappedPivot,hx,hy,ite_false] using xy

theorem dualPivot {t:W} {s:List W} {k:Nat} {a b:W} {p n:R} (run:Run t s k 0)
    (nd:s.Nodup) (ha:a∈s) (hb:b∈s) (different:a≠b)
    (ap:Pivot t s a p) (an:Pivot t s a n) (bp:Pivot t s b p) (bn:Pivot t s b n)
    (ad:a[p.val]≠a[n.val]) (bd:b[p.val]≠b[n.val]) : False :=
  mainPivot run rfl nd a b p n ha hb different ap an bp bn ad bd

private theorem singleAux {t s k cost} (run:Run t s k cost) : cost=0 → s.Nodup →
    ∀(x:W) (p n:R),x∈s → Pivot t s x p → Pivot t s x n → x[p.val]≠x[n.val] →
      t[p.val]≠t[n.val] := by
  induction run with
  | done =>
    intro _ _ x p n xm _ _ diff same
    have eq : x=norm t := by simpa using xm
    subst x
    exact diff (signedCong _ same)
  | @gate s k cost u v a b ka kb um vm ne nz newWord rest ih =>
    intro eq nd x p n xm xp xn xd
    have zero : cost=0 ∧ ka=false ∧ kb=false := by
      cases ka <;> cases kb <;> simp_all [Bool.toNat]
    obtain ⟨rfl,rfl,rfl⟩ := zero
    let d := (s.erase u).erase v
    let g := made u v a b
    have hd : ∀w,w∈d ↔ w∈s ∧ w≠u ∧ w≠v := by
      intro w
      rw [show d=(s.erase u).erase v by rfl,(nd.erase u).mem_erase_iff,nd.mem_erase_iff]
      tauto
    have rr : Run t (g::d) k 0 := rest
    have nd' : (g::d).Nodup := List.nodup_cons.mpr ⟨fun h=>newWord ((hd _).mp h).1,(nd.erase u).erase v⟩
    have l := trackPivot um vm ne xm hd xp xn xd rr
    exact ih rfl nd' _ p n l.1 l.2.1 l.2.2.1 l.2.2.2

theorem singlePivot {t:W} {s:List W} {k:Nat} {a:W} {p n:R} (run:Run t s k 0)
    (nd:s.Nodup) (ha:a∈s) (ap:Pivot t s a p) (an:Pivot t s a n)
    (ad:a[p.val]≠a[n.val]) : t[p.val]≠t[n.val] :=
  singleAux run rfl nd a p n ha ap an ad
end LiveAIG

namespace LiveAIG.Strong
private theorem madeCom (u v:W) (a b:Bool) : made u v a b=made v u b a := by
  unfold made;rw [BitVec.and_comm]

private theorem newPivot {t x g s r} {d:List W} (h:Pivot t s x r)
    (old:∀w∈d,w∈s ∧ w≠x) : Pivot t (g::d) g r := by
  obtain ⟨q,diff,agree⟩ := h
  refine ⟨q,diff,?_⟩
  intro w hmem neq
  rcases List.mem_cons.mp hmem with head|tail
  · exact (neq head).elim
  · exact agree _ (old _ tail).1 (old _ tail).2

private theorem forceOther {t u v:W} {s d:List W} {r:R} {a b:Bool} {k c}
    (pv:Pivot t s u r) (vm:v∈s) (vu:v≠u) (keep:∀w∈d,w∈s ∧ w≠u)
    (rest:Run t (made u v a b::d) k c) : (signed v b)[r.val]=true := by
  obtain ⟨q,tw,base⟩ := pv
  have other := signedCong b (base v vm vu)
  by_contra! no
  have zero:(signed v b)[r.val]=false := by cases h:(signed v b)[r.val] <;> simp_all
  have zero':(signed v b)[q.val]=false := other.symm.trans zero
  apply tw (agreeRun rest ?_)
  intro x hx
  rcases List.mem_cons.mp hx with rfl|old
  · apply signedCong
    simp only [BitVec.getElem_and,zero,zero',Bool.and_false]
  · exact base x (keep _ old).1 (keep _ old).2

private theorem signedDiff {u:W} {p n:R} (s:Bool) (h:u[p.val]≠u[n.val]) :
    (signed u s)[p.val]≠(signed u s)[n.val] := by
  cases s <;> simpa [signed] using h
private theorem resultDiff {u v:W} {p n:R} {a b:Bool}
    (d:u[p.val]≠u[n.val]) (pp:(signed v b)[p.val]=true) (nn:(signed v b)[n.val]=true) :
    (made u v a b)[p.val]≠(made u v a b)[n.val] := by
  have inner : (signed u a &&& signed v b)[p.val]≠(signed u a &&& signed v b)[n.val] := by
    simpa only [BitVec.getElem_and,pp,nn,Bool.and_true] using signedDiff a d
  exact signedDiff _ inner

private def mappedPivot (x u v g:W) := if x=u ∨ x=v then g else x

private theorem clashBoth {t u v:W} {s d:List W} {p n:R} {a b:Bool} {k c}
    (um:u∈s) (ne:u≠v) (right:∀w∈d,w∈s∧w≠v)
    (vp:Pivot t s v p) (vn:Pivot t s v n) (ud:u[p.val]≠u[n.val])
    (rest:Run t (made u v a b::d) k c) : False := by
  have r' : Run t (made v u b a::d) k c := by rwa [madeCom v u b a]
  exact signedDiff a ud ((forceOther vp um ne right r').trans (forceOther vn um ne right r').symm)

def witness (t:W) (s:List W) (p n:R) (x:W) : Prop :=
  x∈s ∧ Pivot t s x p ∧ Pivot t s x n ∧ x[p.val]≠x[n.val]

private theorem transfer {t u v x : W} {s d : List W} {p n : R} {a b : Bool} {k c}
    (um:u∈s) (vm:v∈s) (ne:u≠v) (old:∀w∈d,w∈s)
    (other:∀w∈s,w≠u → w≠v → w∈d)
    (consumed:x=u → u∉d) (consumed':x=v → v∉d)
    (h:witness t s p n x) (rr:Run t (made u v a b::d) k c) :
    witness t (made u v a b::d) p n (mappedPivot x u v (made u v a b)) := by
  obtain ⟨xm,xp,xn,xd⟩:=h
  by_cases one:x=u
  · subst x
    have left : ∀w∈d,w∈s∧w≠u := fun w m=>⟨old w m,fun e=> consumed rfl (e ▸ m)⟩
    exact ⟨by simp [mappedPivot],by simpa [mappedPivot] using newPivot (g:=made u v a b) xp left,
      by simpa [mappedPivot] using newPivot (g:=made u v a b) xn left,by
      simpa [mappedPivot] using resultDiff (a:=a) xd (forceOther xp vm ne.symm left rr) (forceOther xn vm ne.symm left rr)⟩
  by_cases two:x=v
  · subst x
    have right : ∀w∈d,w∈s∧w≠v := fun w m=>⟨old w m,fun e=>consumed' rfl (e ▸ m)⟩
    have rr' : Run t (made v u b a::d) k c := by rwa [madeCom v u b a]
    have de:=resultDiff (a:=b) xd (forceOther xp um ne right rr') (forceOther xn um ne right rr')
    rw [madeCom v u b a] at de
    exact ⟨by simp [mappedPivot],by simpa [mappedPivot] using newPivot (g:=made u v a b) xp right,
      by simpa [mappedPivot] using newPivot (g:=made u v a b) xn right,by simpa [mappedPivot] using de⟩
  have stay {r:R} (pv:Pivot t s x r) : Pivot t (made u v a b::d) x r := by
    obtain ⟨q,diff,z⟩:=pv
    refine ⟨q,diff,?_⟩
    intro w hw neq
    rcases List.mem_cons.mp hw with rfl|mem
    · apply signedCong
      simp only [BitVec.getElem_and,signedCong a (z u um (Ne.symm one)),signedCong b (z v vm (Ne.symm two))]
    · exact z _ (old _ mem) neq
  simpa [witness,mappedPivot,one,two] using
    (show x∈made u v a b::d ∧ Pivot t (made u v a b::d) x p ∧ Pivot t (made u v a b::d) x n ∧ x[p.val]≠x[n.val]
      from ⟨List.mem_cons_of_mem _ (other x xm one two),stay xp,stay xn,xd⟩)

theorem countSigned {t s k c} (run:Run t s k c) (nd:s.Nodup) (p n:R) (P:Finset W)
    (good:∀x∈P,witness t s p n x) : P.card≤c+(decide (t[p.val]≠t[n.val])).toNat := by
  induction run generalizing P with
  | done =>
    have sub : P ⊆ {norm t} := fun x hx=>by simpa using (good x hx).1
    by_cases e : t[p.val]=t[n.val]
    · have empty : P=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have wx:=good x hx
        have xx : x=norm t := by simpa using wx.1
        exact wx.2.2.2 (xx ▸ signedCong _ e)
      simp [empty]
    · simpa [e] using Finset.card_le_card sub
  | @gate s k c u v a b ka kb um vm ne nz fresh rest ih =>
    let d:=drop (drop s u ka) v kb
    let g:=made u v a b
    let K : Finset W := (if ka then {u} else ∅) ∪ (if kb then {v} else ∅)
    let U:=P \ K
    have hd : ∀w,w∈d ↔ w∈s ∧ (w=u → ka=true) ∧ (w=v → kb=true) := by
      intro w
      cases ka <;> cases kb <;> simp [d,drop,(nd.erase u).mem_erase_iff,nd.mem_erase_iff] <;> tauto
    have old : ∀w∈d,w∈s := fun w h1=>(hd w).mp h1 |>.1
    have other : ∀w∈s,w≠u → w≠v → w∈d := fun w hw e f=>(hd w).mpr ⟨hw,fun z=>(e z).elim,fun z=>(f z).elim⟩
    have spent {x} (h:x∈U) : (x=u → u∉d) ∧ (x=v → v∉d) := by
      have out:= (Finset.mem_sdiff.mp h).2
      constructor
      · rintro rfl mem
        have eq:=((hd _).mp mem).2.1 rfl
        exact out (by simp [K,eq])
      · rintro rfl mem
        have eq:=((hd _).mp mem).2.2 rfl
        exact out (by simp [K,eq])
    have preserves {x} (hx:x∈U) := transfer um vm ne old other (spent hx).1 (spent hx).2
      (good x (Finset.mem_sdiff.mp hx).1) rest
    have injective : Set.InjOn (fun x=>mappedPivot x u v g) (↑U : Set W) := by
      intro x hx y hy e
      by_contra xy
      have wx:=good x (Finset.mem_sdiff.mp hx).1
      have wy:=good y (Finset.mem_sdiff.mp hy).1
      by_cases X:x=u ∨ x=v <;> by_cases Y:y=u ∨ y=v
      · rcases X with rfl|rfl <;> rcases Y with e'|e'
        · exact xy e'.symm
        · subst y
          exact clashBoth um ne (fun w m=>⟨old w m,fun q=>(spent hy).2 rfl (q ▸ m)⟩)
            wy.2.1 wy.2.2.1 wx.2.2.2 rest
        · subst y
          exact clashBoth um ne (fun w m=>⟨old w m,fun q=>(spent hx).2 rfl (q ▸ m)⟩)
            wx.2.1 wx.2.2.1 wy.2.2.2 rest
        · exact xy e'.symm
      · simp only [mappedPivot,X,Y,ite_true,ite_false] at e
        apply fresh
        change g ∈ s
        rw [e];exact wy.1
      · simp only [mappedPivot,X,Y,ite_true,ite_false] at e
        apply fresh
        change g ∈ s
        rw [←e];exact wx.1
      · exact xy (by simpa [mappedPivot,X,Y] using e)
    have nd' : (g::d).Nodup := by
      refine List.nodup_cons.mpr ⟨fun h=>fresh (old _ h),?_⟩
      cases ka <;> cases kb <;> simp [d,drop,nd,nd.erase u,nd.erase v,(nd.erase u).erase v]
    have hsize:=ih nd' (U.image (fun x=>mappedPivot x u v g)) (by
      intro y hy
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
      exact preserves hx)
    rw [Finset.card_image_of_injOn injective] at hsize
    have sub : P ⊆ U ∪ K := by intro x hx; by_cases h:x∈K <;> simp [U,h,hx]
    have diff := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    have card : K.card≤ka.toNat+kb.toNat := by
      cases ka <;> cases kb <;> simp [K,ne,Bool.toNat]
    omega
theorem count {t s k c} (run:Run t s k c) (nd:s.Nodup) (p n:R) (P:Finset W)
    (good:∀x∈P,witness t s p n x) : P.card≤c+1 := by
  have h:=countSigned run nd p n P good
  cases e:(decide (t[p.val]≠t[n.val])) <;> simp [e,Bool.toNat] at h <;> omega
end LiveAIG.Strong

namespace LiveAIG

def unionWords (xs:List W) : W := xs.foldr (fun x y=>x|||y) 0
theorem inUnion {xs:List W} {r:R} (h:(unionWords xs)[r.val]=true) : ∃m∈xs,m[r.val]=true := by
  induction xs with
  | nil => simp [unionWords] at h
  | cons x xs ih =>
    change (x|||unionWords xs)[r.val]=true at h
    rw [BitVec.getElem_or,Bool.or_eq_true] at h
    rcases h with h|h
    · exact ⟨x,List.mem_cons_self ..,h⟩
    · obtain ⟨m,hm,q⟩ := ih h
      exact ⟨m,List.mem_cons_of_mem _ hm,q⟩

def pivotMask (t:W) (s:List W) (a:W) : W :=
  unionWords ((classes t (s.erase a)).filter (mixed t))
theorem pivotAt {t s a r} (h:(pivotMask t s a)[r.val]=true) : Pivot t s a r := by
  obtain ⟨m,mem,mr⟩ := inUnion h
  obtain ⟨cell,mix⟩ := List.mem_filter.mp mem
  obtain ⟨p,n,mp,mn,tp,tn⟩ := mixedRows mix
  have coh {u:R} (um:m[u.val]=true) : ∀w∈s,w≠a → w[r.val]=w[u.val] := by
    intro w ws ne
    exact classesCoherent t (s.erase a) m cell r u mr um w (by simpa [ne] using ws)
  cases tr:t[r.val] with
  | true => exact ⟨n,by simp [tr,tn],coh mn⟩
  | false => exact ⟨p,by simp [tr,tp],coh mp⟩

def corners (rows a b:W) : Bool :=
  ((rows &&& a &&& b != 0) && (rows &&& ~~~a &&& ~~~b != 0)) ||
  ((rows &&& a &&& ~~~b != 0) && (rows &&& ~~~a &&& b != 0))
private theorem cornerRows {rows a b:W} (h:corners rows a b=true) :
    ∃p n:R,rows[p.val]=true ∧ rows[n.val]=true ∧ a[p.val]≠a[n.val] ∧ b[p.val]≠b[n.val] := by
  simp only [corners,Bool.or_eq_true,Bool.and_eq_true,bne_iff_ne] at h
  rcases h with h|h
  all_goals
    obtain ⟨p,hp⟩ := someRow h.1
    obtain ⟨n,hn⟩ := someRow h.2
    simp only [BitVec.getElem_and,BitVec.getElem_not,Bool.and_eq_true,Bool.not_eq_true'] at hp hn
    refine ⟨p,n,hp.1.1,hn.1.1,?_,?_⟩ <;> simp [hp.1.2,hn.1.2,hp.2,hn.2]

def dualColumns (t:W) (s:List W) (a b:W) : Bool :=
  corners (pivotMask t s a &&& pivotMask t s b) a b
theorem dualBlock {t s k a b} (nd:s.Nodup) (ha:a∈s) (hb:b∈s) (ne:a≠b)
    (bad:dualColumns t s a b=true) (h:Run t s k 0) : False := by
  obtain ⟨p,n,hp,hn,ad,bd⟩ := cornerRows bad
  simp only [BitVec.getElem_and,Bool.and_eq_true] at hp hn
  exact dualPivot h nd ha hb ne (pivotAt hp.1) (pivotAt hn.1)
    (pivotAt hp.2) (pivotAt hn.2) ad bd

def pivotWords (t:W) (s:List W) : List (W×W) := s.map (fun a=>(a,pivotMask t s a))
def pairExists (xs:List (W×W)) : Bool :=
  xs.any fun x=>xs.any fun y=>x.1.toNat<y.1.toNat && corners (x.2&&&y.2) x.1 y.1
def allBlocked (t:W) (s:List W) : Bool := pairExists (pivotWords t s)
theorem allBlockedSound {t s k} (nd:s.Nodup) (bad:allBlocked t s=true) (h:Run t s k 0) : False := by
  obtain ⟨x,hx,bad⟩ := List.any_eq_true.mp bad
  obtain ⟨y,hy,pair⟩ := List.any_eq_true.mp bad
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
  obtain ⟨lt,pair⟩ := Bool.and_eq_true_iff.mp pair
  have less : a.toNat<b.toNat := of_decide_eq_true lt
  exact dualBlock nd ha hb (fun eq=> (Nat.ne_of_lt less) (congrArg BitVec.toNat eq)) pair h

def hintBlocked (t:W) (s:List W) (byte:Nat) : Bool :=
  match s[byte % 16]?,s[(byte/16) % 16]? with
  | some a,some b => a != b && dualColumns t s a b
  | _,_ => false
theorem hintBlockedSound {t s k byte} (nd:s.Nodup) (bad:hintBlocked t s byte=true) (h:Run t s k 0) : False := by
  unfold hintBlocked at bad
  split at bad <;> rename_i hm hn
  · obtain ⟨ne,pair⟩ := Bool.and_eq_true_iff.mp bad
    exact dualBlock nd (List.mem_of_getElem? hm) (List.mem_of_getElem? hn) (bne_iff_ne.mp ne) pair h
  all_goals contradiction

def guardZero (bad:List W→Bool) (s:List W) (budget:Nat) : Bool :=
  if budget=0 ∧ s.Nodup then !(bad s) else true
theorem guardZeroSound {t:W} {bad:List W→Bool}
    (sound:∀{s k},s.Nodup → bad s=true → Run t s k 0 → False)
    {s k c b} (h:Run t s k c) (budget:c≤b) : guardZero bad s b=true := by
  unfold guardZero
  split <;> rename_i f
  · have z:c=0 := by omega
    subst c
    cases v:bad s with
    | false => rfl
    | true => exact (sound f.2 v h).elim
  · rfl

def allowAllPivot (t:W) := guardZero (allBlocked t)
def allowHint (t:W) (hint:List W→Nat) := guardZero (fun s=>hintBlocked t s (hint s))
theorem allowAllPivotSound {t s k c b} (h:Run t s k c) (bound:c≤b) : allowAllPivot t s b=true :=
  guardZeroSound allBlockedSound h bound
theorem allowHintSound {t s k c b} (hint:List W→Nat) (h:Run t s k c) (bound:c≤b) : allowHint t hint s b=true :=
  guardZeroSound (fun nd bad tr=>hintBlockedSound nd bad tr) h bound
end LiveAIG

namespace LiveAIG

def literalAt (w:W) (r:R) := if w[r.val] then w else ~~~w
theorem litEq {w:W} {r q:R} (atq:(literalAt w r)[q.val]=true) : w[r.val]=w[q.val] := by
  cases val:w[r.val] <;> simp [literalAt,val] at atq <;> simp [val,atq]
theorem litNe {w:W} {r q:R} (atq:(~~~literalAt w r)[q.val]=true) : w[r.val]≠w[q.val] := by
  cases val:w[r.val] <;> simp [literalAt,val] at atq <;> simp [val,atq]

def sameMask (a b:W) (r:R) (s:List W) : W :=
  s.foldr (fun w m=>if w=a ∨ w=b then m else m&&&literalAt w r) (~~~0)
theorem keptEqual {a b:W} {r q:R} {s:List W} (h:(sameMask a b r s)[q.val]=true) :
    ∀w∈s,w≠a → w≠b → w[r.val]=w[q.val] := by
  induction s with
  | nil => simp
  | cons x xs ih =>
    change (if x=a ∨ x=b then sameMask a b r xs else sameMask a b r xs&&&literalAt x r)[q.val]=true at h
    by_cases e:x=a ∨ x=b
    · rw [ite_eq_left e] at h
      intro w wm wa wb
      rcases List.mem_cons.mp wm with rfl|old
      · exact (e.elim wa wb).elim
      · exact ih h _ old wa wb
    · rw [ite_eq_right e,BitVec.getElem_and,Bool.and_eq_true] at h
      intro w wm wa wb
      rcases List.mem_cons.mp wm with rfl|old
      · exact litEq h.2
      · exact ih h.1 _ old wa wb

def localPivots (t:W) (s:List W) (a b:W) (r:R) :=
  let pool:=sameMask a b r s &&& ~~~literalAt t r
  let u:=literalAt a r
  let v:=literalAt b r
  (pool &&& ~~~u &&& v != 0) && (pool &&& u &&& ~~~v != 0)
theorem localSound {t s a b r} (h:localPivots t s a b r=true) : Pivot t s a r ∧ Pivot t s b r := by
  simp only [localPivots,Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨q,hq⟩ := someRow h.1
  obtain ⟨v,hv⟩ := someRow h.2
  simp only [BitVec.getElem_and,Bool.and_eq_true] at hq hv
  constructor
  · refine ⟨q,litNe hq.1.1.2,?_⟩
    intro w wm wa
    by_cases eq:w=b
    · subst w;exact litEq hq.2
    · exact keptEqual hq.1.1.1 w wm wa eq
  · refine ⟨v,litNe hv.1.1.2,?_⟩
    intro w wm wb
    by_cases eq:w=a
    · subst w;exact litEq hv.1.2
    · exact keptEqual hv.1.1.1 w wm eq wb

def anchor (code:Nat) : R := ⟨code % 128,Nat.mod_lt _ (by decide)⟩
def anchored (t:W) (s:List W) (a b:W) (code:Nat) :=
  let p := anchor code
  let n := anchor (code/128)
  a[p.val] != a[n.val] && b[p.val] != b[n.val] && localPivots t s a b p && localPivots t s a b n
theorem anchorSound {t s a b c k} (nd:s.Nodup) (aa:a∈s) (bb:b∈s) (ne:a≠b)
    (bad:anchored t s a b c=true) (run:Run t s k 0) : False := by
  simp only [anchored,Bool.and_eq_true,bne_iff_ne] at bad
  obtain ⟨ap,bp⟩ := localSound bad.1.2
  obtain ⟨an,bn⟩ := localSound bad.2
  exact dualPivot run nd aa bb ne ap an bp bn bad.1.1.1 bad.1.1.2

def anchorHint (t:W) (s:List W) (code:Nat) :=
  match s[code % 16]?,s[(code/16) % 16]? with
  | some a,some b => a != b && anchored t s a b (code/256)
  | _,_ => false
theorem anchorHintSound {t s k code} (nd:s.Nodup) (bad:anchorHint t s code=true) (h:Run t s k 0) : False := by
  unfold anchorHint at bad
  split at bad <;> rename_i hm hn
  · obtain ⟨ne,pair⟩ := Bool.and_eq_true_iff.mp bad
    exact anchorSound nd (List.mem_of_getElem? hm) (List.mem_of_getElem? hn) (bne_iff_ne.mp ne) pair h
  all_goals contradiction
end LiveAIG

namespace LiveAIG.PivotCertificate

def chosen (s : List W) (mask : Nat) := s.filter (fun w=>mask.testBit (s.idxOf w))
def alone (t : W) (s : List W) (w : W) (r : R) :=
  (sameMask w w r s &&& ~~~literalAt t r) != 0
theorem aloneSound {t s w r} (hit : alone t s w r=true) : Pivot t s w r := by
  have h:=bne_iff_ne.mp hit
  obtain ⟨q,yes⟩:=someRow h
  simp only [BitVec.getElem_and,Bool.and_eq_true] at yes
  exact ⟨q,litNe yes.2,fun a m ne=>keptEqual yes.1 a m ne ne⟩

def tests (t : W) (s : List W) (p n : R) (w : W) :=
  w[p.val] != w[n.val] && alone t s w p && alone t s w n
def verify (t : W) (s : List W) (budget code : Nat) :=
  let p := anchor code
  let n := anchor (code/128)
  let xs := chosen s (code/16384)
  decide (budget+(decide (t[p.val]≠t[n.val])).toNat<xs.length) && xs.all (tests t s p n)

theorem verifySound {t s k c budget code} (ds : s.Nodup) (yes : verify t s budget code=true)
    (small : c≤budget) (run : Run t s k c) : False := by
  simp only [verify,Bool.and_eq_true,decide_eq_true_eq] at yes
  let xs:=chosen s (code/16384)
  have ns : xs.Nodup := ds.filter _
  have limit:=Strong.countSigned run ds (anchor code) (anchor (code/128)) xs.toFinset (by
    intro x mem
    have original : x∈xs := List.mem_toFinset.mp mem
    have inS:=List.mem_of_mem_filter original
    have check:=List.all_eq_true.mp yes.2 x original
    simp only [tests,Bool.and_eq_true,bne_iff_ne] at check
    exact ⟨inS,aloneSound check.1.2,aloneSound check.2,check.1.1⟩)
  rw [List.toFinset_card_of_nodup ns] at limit
  have gt : budget+(decide (t[(anchor code).val]≠t[(anchor (code/128)).val])).toNat<xs.length := yes.1
  omega

end LiveAIG.PivotCertificate

namespace Cof12783
open FreeAIG LiveAIG
def f (x : Fin 5 → Bool) : Bool := Nat.testBit 4278124264 (∑ i : Fin 5, if x i then 2^i.val else 0)
def cut (x : X) (i : Fin 5) : Bool := x ⟨i.val, by omega⟩
def padded : X → Bool := f ∘ cut
def t : W := 0xfefefee8fefefee8fefefee8fefefee8
def A : List W := Data12783.raw
def S : Set (Fn X) := {g | ∃ i : Fin 5,g=fun x=>cut x i}
set_option maxRecDepth 65536 in
theorem wordF : word padded=t := by decide +kernel
theorem compile {k : Nat} (h : Has Inputs k f) :
    ∃ n≤k,∃c,Run t A n c := by
  classical
  have p : Has S k padded := h.map cut (by
    rintro g ⟨i,rfl⟩;exact .src ⟨i,rfl⟩)
  have rep : Represents S A.toFinset := by
    rintro g ⟨i,rfl⟩;right;revert i;decide +kernel
  have nz : norm (word padded)≠0 := by rw [wordF];decide +kernel
  obtain ⟨U,sub,_,n,small,c,ok⟩:=trim p A.toFinset rep nz
  let s:=A.filter (fun w=>decide (w∈U))
  have eq : s.toFinset=U := by
    ext w
    change w∈(A.filter (fun w=>decide (w∈U))).toFinset ↔ w∈U
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun hw=>⟨List.mem_toFinset.mp (sub hw),hw⟩⟩
  have nd : A.Nodup := by decide +kernel
  have r:=ok s (nd.filter _) eq
  rw [wordF] at r
  have valid := initialOk r
  have all : A.sublists.all (fun xs=> !liveInitial t xs || xs==A)=true := by decide +kernel
  have one:=List.all_eq_true.mp all s (List.mem_sublists.mpr List.filter_sublist)
  have se : s=A := by simpa [valid] using one
  exact ⟨n,small,c,se ▸ r⟩

def cfg : IdentityLayers.Setup where
  t := t
  cut := fun _ p z=>PivotCertificate.verify t p.1 p.2 z
  sound := fun ds ok _ small run=>PivotCertificate.verifySound ds ok small run

end Cof12783

namespace LiveAIG.IdentityLayers
abbrev Levels := Nat → Next
abbrev Hints := Nat → Nat → Nat

def site (cfg : Setup) (read : Reader) (levels : Levels) (hints : Hints) (d k i : Nat) : Bool :=
  match levels k i with
  | none=>true
  | some p=>checked cfg read (levels (k+1)) d p.1 p.2 (hints k i)
def block (cfg : Setup) (read : Reader) (levels : Levels) (hints : Hints) (d width k b : Nat) :=
  (List.range width).all fun i=>site cfg read levels hints d k (width*b+i)

theorem groupSound {cfg read levels hints width k d size}
    (pos : 0<width)
    (bounded : ∀{i p},levels k i=some p → i<size)
    (next : ∀ j p,levels (k+1) j=some p → Dead cfg d p)
    (groups : ∀b, b<(size+width-1)/width → block cfg read levels hints d width k b=true) :
    ∀ i p, levels k i=some p → Dead cfg (d+1) p := by
  intro i p eq
  have lt := bounded eq
  have bb : i/width < (size+width-1)/width := by
    have inc : i/width*width+width ≤ size+width-1 := by
      have := Nat.div_mul_le_self i width
      omega
    have one : (i/width+1)*width ≤ size+width-1 := by simpa [Nat.add_mul] using inc
    exact (Nat.le_div_iff_mul_le pos).mpr one
  have yes:=List.all_eq_true.mp (groups _ bb) (i % width) (List.mem_range.mpr (Nat.mod_lt _ pos))
  have ii : width*(i/width)+i % width=i := Nat.div_add_mod i width
  simp only [ii,site,eq] at yes
  intro n c hn hc
  exact checkedSound yes next hn hc

end LiveAIG.IdentityLayers

namespace Cof12783
open LiveAIG IdentityLayers Data12783
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem bounded {lev i : Nat} {s : State} (h : stateAt lev i=some s) : i<levelSize lev := by
  unfold stateAt at h
  split at h
  · assumption
  · contradiction

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem layer5 : ∀i p,stateAt 5 i=some p → Dead cfg 2 p := by
  intro i p he
  have lt:=bounded he
  change i<0 at lt
  omega
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b4_0 : block cfg decodeStep stateAt hintAt 2 16 4 0=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem layer4 : ∀i p,stateAt 4 i=some p → Dead cfg 3 p := by
  apply groupSound (hints:=hintAt) (read:=decodeStep) (width:=16) (size:=levelSize 4) (by decide) (@bounded 4) layer5
  intro b hb
  change b<1 at hb
  interval_cases b
  · exact b4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b3_0 : block cfg decodeStep stateAt hintAt 3 16 3 0=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b3_1 : block cfg decodeStep stateAt hintAt 3 16 3 1=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b3_2 : block cfg decodeStep stateAt hintAt 3 16 3 2=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b3_3 : block cfg decodeStep stateAt hintAt 3 16 3 3=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b3_4 : block cfg decodeStep stateAt hintAt 3 16 3 4=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b3_5 : block cfg decodeStep stateAt hintAt 3 16 3 5=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem layer3 : ∀i p,stateAt 3 i=some p → Dead cfg 4 p := by
  apply groupSound (hints:=hintAt) (read:=decodeStep) (width:=16) (size:=levelSize 3) (by decide) (@bounded 3) layer4
  intro b hb
  change b<6 at hb
  interval_cases b
  · exact b3_0
  · exact b3_1
  · exact b3_2
  · exact b3_3
  · exact b3_4
  · exact b3_5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b2_0 : block cfg decodeStep stateAt hintAt 4 16 2 0=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b2_1 : block cfg decodeStep stateAt hintAt 4 16 2 1=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b2_2 : block cfg decodeStep stateAt hintAt 4 16 2 2=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b2_3 : block cfg decodeStep stateAt hintAt 4 16 2 3=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b2_4 : block cfg decodeStep stateAt hintAt 4 16 2 4=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b2_5 : block cfg decodeStep stateAt hintAt 4 16 2 5=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b2_6 : block cfg decodeStep stateAt hintAt 4 16 2 6=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b2_7 : block cfg decodeStep stateAt hintAt 4 16 2 7=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem layer2 : ∀i p,stateAt 2 i=some p → Dead cfg 5 p := by
  apply groupSound (hints:=hintAt) (read:=decodeStep) (width:=16) (size:=levelSize 2) (by decide) (@bounded 2) layer3
  intro b hb
  change b<8 at hb
  interval_cases b
  · exact b2_0
  · exact b2_1
  · exact b2_2
  · exact b2_3
  · exact b2_4
  · exact b2_5
  · exact b2_6
  · exact b2_7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b1_0 : block cfg decodeStep stateAt hintAt 5 16 1 0=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b1_1 : block cfg decodeStep stateAt hintAt 5 16 1 1=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b1_2 : block cfg decodeStep stateAt hintAt 5 16 1 2=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem layer1 : ∀i p,stateAt 1 i=some p → Dead cfg 6 p := by
  apply groupSound (hints:=hintAt) (read:=decodeStep) (width:=16) (size:=levelSize 1) (by decide) (@bounded 1) layer2
  intro b hb
  change b<3 at hb
  interval_cases b
  · exact b1_0
  · exact b1_1
  · exact b1_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem b0_0 : block cfg decodeStep stateAt hintAt 6 16 0 0=true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem layer0 : ∀i p,stateAt 0 i=some p → Dead cfg 7 p := by
  apply groupSound (hints:=hintAt) (read:=decodeStep) (width:=16) (size:=levelSize 0) (by decide) (@bounded 0) layer1
  intro b hb
  change b<1 at hb
  interval_cases b
  · exact b0_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem lower {k} (h : FreeAIG.Has FreeAIG.Inputs k f) : 8≤k := by
  by_contra! small
  obtain ⟨n,hn,c,run⟩:=compile h
  have bal:=balance run
  have sizeA : A.length=5 := by decide +kernel
  rw [sizeA] at bal
  have start : stateAt 0 0=some (A,3) := by decide +kernel
  exact layer0 0 (A,3) start (by omega) (by show c≤3; omega) run
end Cof12783

namespace Upper12783
open FreeAIG

theorem signedLower {k : Nat} (h : Has Inputs k target) : 9 ≤ k := by
  apply oneCofactorLower (f := target) (i := 5) (b := false) (m := 8) (by decide) _ _ h
  · decide +kernel
  · have eq : cofactorAt target 5 false = Cof12783.f := by
      funext x
      exact (show ∀y, cofactorAt target 5 false y = Cof12783.f y from by decide +kernel) x
    rw [eq]
    intro q net
    exact Cof12783.lower net

end Upper12783

namespace FreeAIG
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def price : GateOp → Nat | .not => 0 | _ => 1
def binaryCount : List Gate → Nat
  | [] => 0
  | g::gs => price g.op + binaryCount gs

theorem leLength (gs : List Gate) : binaryCount gs ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h:g.op <;> simp [binaryCount,h,price] <;> omega

theorem notDiscount {gs : List Gate} (h : ∃ g∈gs,g.op=.not) : binaryCount gs+1≤gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨u,hu,op⟩ := h
    rcases List.mem_cons.mp hu with rfl|hg
    · simpa [binaryCount,op,price] using leLength gs
    · have hlt := ih ⟨u,hg,op⟩
      cases h:g.op <;> simp [binaryCount,h,price] <;> omega

theorem Has.bump {α : Type*} {S : Set (Fn α)} {k f} (p : Has S k f) : Has S (k+1) f := by
  induction p with
  | done h => exact .done h
  | step a b _ ih => exact .step a b ih

def applied {α} (g : Gate) (state : List (Fn α)) : Fn α := fun x =>
  g.op.eval (g.inputs.map (fun i => (state.getD i (fun _=>false)) x))
def run {α} (gs : List Gate) (state : List (Fn α)) : List (Fn α) :=
  gs.foldl (fun s g=>s++[applied g s]) state

theorem availGet {α : Type*} {S : Set (Fn α)} {st : List (Fn α)} (hs : ∀f∈st,Avail S f)
    (i : Nat) : Avail S (st.getD i (fun _=>false)) := by
  by_cases h : i<st.length
  · rw [List.getD_eq_getElem _ _ h]; exact hs _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]; exact .const false

theorem Has.same {α : Type*} {S T : Set (Fn α)} {k f} (p : Has S k f) (h : ∀g∈S,Avail T g) :
    Has T k f := p.map id h

theorem gateCost {α : Type*} {S : Set (Fn α)} (g : Gate) (st : List (Fn α))
    (old : ∀f∈st,Avail S f)
    (legal : (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    {f k} (tail : ∀ T : Set (Fn α), (∀ a∈st,Avail T a) → Avail T (applied g st) → Has T k f) :
    Has S (price g.op + k) f := by
  have base (A : Avail S (applied g st)) : Has S k f := tail S old A
  have ext (a : Fn α) : ∀u∈st,Avail (insert a S) u := fun u hu=>(old u hu).extend
  obtain ⟨op,len⟩ := legal
  cases g with | mk opg ins =>
  change opg=.and ∨ opg=.or ∨ opg=.not at op
  change ins.length≤2 at len
  match ins,len with
  | [],_ =>
    have free := base (Avail.const (opg.eval []))
    rcases op with rfl|rfl|rfl <;> simp [price,Nat.add_comm] <;> first | exact free.bump | exact free
  | [i],_ =>
    let a := st.getD i (fun _=>false)
    have ha : Avail S a := availGet old i
    rcases op with rfl|rfl|rfl
    · have e : applied ⟨.and,[i]⟩ st=a := by funext x;simp [applied,a,GateOp.eval]
      simpa [price,Nat.add_comm] using (base (e ▸ ha)).bump
    · have e : applied ⟨.or,[i]⟩ st=a := by funext x;simp [applied,a,GateOp.eval]
      simpa [price,Nat.add_comm] using (base (e ▸ ha)).bump
    · simpa [price] using base ha.neg
  | [i,j],_ =>
    let a := st.getD i (fun _=>false)
    let b := st.getD j (fun _=>false)
    have ha : Avail S a := availGet old i
    have hb : Avail S b := availGet old j
    rcases op with rfl|rfl|rfl
    · have e : applied ⟨.and,[i,j]⟩ st=meet a b := by funext x;simp [applied,a,b,meet,GateOp.eval]
      have h := tail (insert (meet a b) S) (ext _) (e ▸ Avail.src (Set.mem_insert _ _))
      simpa [price,Nat.add_comm] using Has.step ha hb h
    · have e : applied ⟨.or,[i,j]⟩ st=neg (meet (neg a) (neg b)) := by
        funext x;simp [applied,a,b,meet,neg,GateOp.eval]
      have h := tail (insert (meet (neg a) (neg b)) S) (ext _)
        (e ▸ (Avail.src (Set.mem_insert _ _)).neg)
      simpa [price,Nat.add_comm] using Has.step ha.neg hb.neg h
    · simpa [price] using base ha.neg

theorem listAIG {α : Type*} (gs : List Gate) (legal : ∀g∈gs,
    (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    (st : List (Fn α)) (S : Set (Fn α)) (old : ∀f∈st,Avail S f) (o) :
    Has S (binaryCount gs) ((run gs st).getD o (fun _=>false)) := by
  induction gs generalizing st S with
  | nil => exact .done (availGet old o)
  | cons g gs ih =>
    apply gateCost g st old (legal g (by simp))
    intro T prev h
    apply ih (fun u hu=>legal u (by simp [hu])) (st++[applied g st]) T
    intro u hu
    rcases List.mem_append.mp hu with u0|u1
    · exact prev u u0
    · have eq := List.mem_singleton.mp u1;exact eq ▸ h

theorem mapRun {α} (gs : List Gate) (st : List (Fn α)) (x : α) :
    (run gs st).map (fun a=>a x) =
    gs.foldl (fun s g=>s++[g.op.eval (g.inputs.map (fun j=>s.getD j false))]) (st.map (fun a=>a x)) := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih =>
    simp only [run,List.foldl_cons] at ih ⊢
    rw [ih]
    congr 1
    simp only [List.map_append,List.map_cons,List.map_nil,List.append_cancel_left_eq]
    congr 2
    unfold applied
    congr 1
    apply List.map_congr_left
    intro i _
    exact (List.getD_map st (fun _=>false) (n:=i) (fun a : Fn α=>a x)).symm

theorem circuitAIG {n} (C : Circuit) (legal : ∀g∈C.gates,
    (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) :
    Has Inputs (binaryCount C.gates) (fun x : Fin n→Bool=>C.eval (List.ofFn x)) := by
  let st : List (Fn (Fin n→Bool)) := List.ofFn (fun i x=>x i)
  have h := listAIG C.gates legal st Inputs (by
    intro f hf
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp hf
    exact .src ⟨i,eq.symm⟩) C.output
  convert h using 1
  funext x
  have hst : st.map (fun a=>a x)=List.ofFn x := by simp [st,List.map_ofFn,Function.comp_def]
  have eq := mapRun C.gates st x
  rw [hst] at eq
  change (C.wires (List.ofFn x)).getD C.output false=_
  rw [show C.wires (List.ofFn x)=(run C.gates st).map (fun a=>a x) from eq.symm]
  exact List.getD_map _ (fun _=>false) (n:=C.output) (fun a : Fn (Fin n→Bool)=>a x)

end FreeAIG

namespace Upper12783
open FreeAIG PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem replacement (s : Nat) (h : HasCircuitSize 6 target s) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧ ∀x : Fin 6→Bool,D.eval (List.ofFn x)=target x := by
  obtain ⟨C,legal,len,ok⟩ := h
  have net := circuitAIG (n := 6) C (by simpa [FanInTwo] using legal)
  rw [funext ok] at net
  have lb := signedLower net
  have shape := leLength C.gates
  refine ⟨circuit, monotone, ?_, correct⟩
  rw [size]
  exact (lb.trans shape).trans len

end Upper12783

end PEqualNP.Outside.L_meta_12783

theorem PEqualNP.Outside.L_meta_12783 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4278124264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4278124264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_12783.Upper12783.replacement
