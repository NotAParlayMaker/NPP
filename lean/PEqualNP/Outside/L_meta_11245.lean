import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11245

namespace K4Core
def pack {n:Nat} (f : Fin n→Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)

theorem pack_get {n:Nat} (f : Fin n→Bool) (i:Fin n) : (pack f)[i.val] = f i := by
  have h : (BitVec.ofBoolListLE (List.ofFn f)).getLsbD i.val = f i := by
    rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD]
    simp
  exact h

end K4Core

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

namespace LiveAIG.Stream
def width : Nat→Nat→Nat × Nat
  | 0,x=>(0,x)
  | k+1,x=> if x % 2=0 then (0,x/2) else
    let q:=width k (x/2)
    (q.1+1,q.2)
end LiveAIG.Stream

namespace LiveAIG.Layers

abbrev State := List W × Nat
abbrev Table := Array (Array Nat)
def lookup (a : Table) (i : Nat) : Option Nat := do
  let g←a[i/32]?
  g[i % 32]?
def unpack (symbols : Nat→W) : Nat→Nat→List W
  | 0,_=>[]
  | k+1,n=>symbols (n % 4096)::unpack symbols k (n/4096)
def decode (initial : List W) (symbols : Nat→W) (n : Nat) : State :=
  let mask:=(n/8) % 128
  let extras:=unpack symbols ((n/1024) % 8) (n/8192)
  (canon ((initial.zipIdx.filterMap (fun z=>if mask.testBit z.2 then some z.1 else none))++extras),n % 8)
def extract (b n : Nat) : Bool × Nat × Nat :=
  let x:=if b=0 then
    let w:=Stream.width 10 n
    let d:=2^w.1
    (d-1+w.2 % d,w.2/d)
    else (511,n)
  if x.1=511 then (true,x.2 % 4096,x.2/4096) else (false,x)
def links (t : W) (dict : Nat→List Nat) (next : Nat→Option State) : List State→Nat→Bool
  | [],_=>true
  | p::ps,n=>
    let e:=extract p.2 n
    let ok:=if e.1 then next e.2.1==some p else
      p.2==0 && decide p.1.Nodup && anchorHint t p.1 ((dict p.1.length).getD e.2.1 0)
    ok && links t dict next ps e.2.2
def check (t : W) (dict : Nat→List Nat) (dec : Nat→State) (next : Table) (own data : Nat) : Bool :=
  let p:=dec own
  !(p.1.contains (norm t)) && links t dict (fun i=>(lookup next i).map dec) (children t p.1 p.2) data

theorem forChild {t dict next ps n} (yes : links t dict next ps n=true)
    {p : State} (pm : p∈ps) :
    (∃j,next j=some p) ∨
    ∃i,p.2=0 ∧ p.1.Nodup ∧ anchorHint t p.1 ((dict p.1.length).getD i 0)=true := by
  induction ps generalizing n with
  | nil=>simp at pm
  | cons x xs ih=>
    simp only [links,Bool.and_eq_true] at yes
    rcases List.mem_cons.mp pm with rfl|old
    · cases flag : (extract p.2 n).1 with
      | false=>
        right
        simp only [flag,Bool.false_eq_true,ite_false,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at yes
        exact ⟨_,yes.1.1.1,yes.1.1.2,yes.1.2⟩
      | true=>
        left
        simp only [flag,ite_true,beq_iff_eq] at yes
        exact ⟨_,yes.1⟩
    · exact ih yes.2 old

def Dead (t : W) (p : State) : Prop := ∀{k d},d≤p.2 → ¬Run t p.1 k d

theorem checkSound {t dict dec next own data} (yes : check t dict dec next own data=true)
    (others : ∀i q,lookup next i=some q → Dead t (dec q)) :
    Dead t (dec own) := by
  intro k d db run
  simp only [check,Bool.and_eq_true,Bool.not_eq_true'] at yes
  rcases runStep run db with hit|⟨j,_,p,pm,c,cb,child⟩
  · simpa [hit] using yes.1
  · rcases forChild yes.2 pm with ⟨i,here⟩|⟨i,zero,nd,bad⟩
    · cases eq:lookup next i with
      | none=>simp [eq] at here
      | some q=>
        have e:dec q=p := by simpa [eq] using here
        subst p;exact others i q eq cb child
    · have z:c=0 := by omega
      subst c;exact anchorHintSound nd bad child

def groupCheck (t : W) (dict : Nat→List Nat) (dec : Nat→State) (next : Table) :
    List Nat→List Nat→Bool
  | [],[]=>true
  | m::ms,h::hs=>check t dict dec next m h && groupCheck t dict dec next ms hs
  | _,_=>false

theorem groupSound {t dict dec next ms hs} (h : groupCheck t dict dec next ms hs=true)
    (others : ∀i q,lookup next i=some q → Dead t (dec q)) :
    ∀m∈ms,Dead t (dec m) := by
  induction ms generalizing hs with
  | nil=>simp
  | cons m ms ih=>
    cases hs with
    | nil=>simp [groupCheck] at h
    | cons z zs=>
      simp only [groupCheck,Bool.and_eq_true] at h
      intro q qm
      rcases List.mem_cons.mp qm with rfl|old
      · exact checkSound h.1 others
      · exact ih h.2 _ old

theorem lookGroup {t : W} {dec : Nat→State} {own:Table}
    (h : ∀a∈own.toList,∀m∈a.toList,Dead t (dec m)) :
    ∀i m,lookup own i=some m → Dead t (dec m) := by
  intro i m hm
  unfold lookup at hm
  cases eq:own[i/32]? with
  | none=>simp [eq] at hm
  | some a=>
    have valid : a∈own.toList := by simpa using List.mem_of_getElem? (by simpa using eq : own.toList[i/32]?=some a)
    have el : a[i % 32]?=some m := by simpa [eq] using hm
    intro k d bd
    exact h _ valid _ (List.mem_of_getElem? (by simpa using el : a.toList[i % 32]?=some m)) bd

end LiveAIG.Layers

namespace LiveAIG.Layers

def hybrid (t : W) (dict : Nat→List Nat) (dec : Nat→State) (next cuts : Table) (own mode : Nat) : Bool :=
  if mode % 2=0 then check t dict dec next own (mode/2)
  else lookup cuts (mode/2)==some own
def groupHybrid (t : W) (dict : Nat→List Nat) (dec : Nat→State) (next cuts : Table) :
    List Nat→List Nat→Bool
  | [],[]=>true
  | m::ms,z::zs=>hybrid t dict dec next cuts m z && groupHybrid t dict dec next cuts ms zs
  | _,_=>false

theorem hybridSound {t dict dec next cuts own mode} (h : hybrid t dict dec next cuts own mode=true)
    (others : ∀i m,lookup next i=some m → Dead t (dec m))
    (excluded : ∀{i m},lookup cuts i=some m → Dead t (dec m)) : Dead t (dec own) := by
  unfold hybrid at h
  split at h
  · exact checkSound h others
  · intro k d b
    exact excluded (beq_iff_eq.mp h) b

theorem hybridGroupSound {t dict dec next cuts ms hs}
    (h : groupHybrid t dict dec next cuts ms hs=true)
    (others : ∀i m,lookup next i=some m → Dead t (dec m))
    (excluded : ∀{i m},lookup cuts i=some m → Dead t (dec m)) :
    ∀m∈ms,Dead t (dec m) := by
  induction ms generalizing hs with
  | nil=>simp
  | cons v vs ih=>
    cases hs with
    | nil=>simp [groupHybrid] at h
    | cons z zs=>
      simp only [groupHybrid,Bool.and_eq_true] at h
      intro q qm
      rcases List.mem_cons.mp qm with rfl|old
      · exact hybridSound h.1 others @excluded
      · exact ih h.2 _ old
end LiveAIG.Layers

namespace LiveAIG
def anchors11246 : Nat→List Nat
  | 6 => [3148372,2106161,2100529,2884436,3671120,3675220,2632770,2137168,2630705,2884434,2236721,2240578,2099488,1086032,3670612,560720,2109008,2108500,2101074,2099489,2167888,2634802,1086034,2302036,2630193,790864,2626097,2299988,559665,559648]
  | 7 => [3146341,3673189,1086049,2634818,559713,2132065,2885477,1609264,3671137,2105922,3675237,2177121,2766896,2106433,2101058,2236769,2100528,1086018,1086000,1608288,2100033,2168933,2132581,1121377,2172976,2361185,1089125,2135137,1086051,2756197,3146848,3147109,2106416,2099505,2764865,2169953,1086048,2105921,2136160,1608257,2359651,1119280,3675233,691809,2110547,559682,3146593,2236773,1383525,1609317,1087041,2764897,2630753,2107680,559665,1089121,2367810,2636849,2764849,2630994,2883941,2764866,2170946,1608289,2764883,690736,2135141,2238563,2112613,2106690,2133601,2359600,2359648,1121346,3677280,2167909,1154147,3146336,2105953,2171233,2636865,2632275,2240593,2630466,690784,2367845,1608290,3670627,2110531,3148389,1121345,2236738,3409253,3183717,2144353,1119328,559648,2764832,2106432,1088083,1086001,2168929,2100049,2242642,2171237,2106161,1121329,2761059,2100065,2236770,2105648,3670885,1089123,1154145,2135136,2632240,2236512,2140208,2630755,2892115,1152066,2236720,560741,2360677,2106689,2766913,690753,2629186,2106211,558689,3152962,1087074,1083233,2099520,3149396,2200657,559664,3179877,2173025,1086305,2359649,2238561,2099522,2360163,2099521,1154096,2133093,1381473,2884453,2107697,2360674,2132576,625249,3183713,1088048,3670880,2175041,2892131,1381443,2133603,2268257,2242656,2106213,2760805,2656321,2236480,2167904,1381459,2364976,560739,2892097,3199077]
  | 8 => [3146870,3670902,1086034,2634834,2132081,2105938,2168945,2099538,3677302,1609280,559698,2099521,1383506,2099520,691825,1086065,3148406,3675249,1608257,2885494,1152099,2106706,2106723,2764864,2171249,1088081,2168946,559730,2242674,1089088,2764899,2099504,2766930,2132086,1383538,2132082,2168950,2632786,1089089,2634816,2236785,2630482,1089106,2135153,1383489,1608240,2099537,2106449,691776,2105939,2764865,1383537,1086051,3675254,2632018,2883956,2359616,2171250,1086000,2632787,3146353,1608273,1608305,2167921,2359665,3180662,1152082,1608256,2105937,3408246,2106211,2359670,1086066,2101074,1089137,2630465,2359666,2625345,2112612,1154112,2135154,2766946,2105970,2634817,2625344,1119330,3671414,559696,2099505,690787,2624834,2106466,2632274,691777,2630722,1088083,2106481,1088066,2634832,2238580,1383542,1383523,2367826,691824,2173010,1609298,2170944,1152116,2132593,2625363,3673718,2236480,2632001,2764913,691826,2133057,2761074,691830,2240595,3673201,2135158,2167926,2764848,2883955,2885475,3146614,2140273,1383505,1152113,690771,1089122,2112594,2167922,691793,3184753,3675250,2107680,1085984,2105936,1088118,1121362,2170994,2142322,2106740,691828,1383490,690770,2107968,2112611,2634833,2764882,2168897,691812,1086064,2892131,2761075,1089140,3152997,2236498,2177137,2892096,1086017,1086001,2105956,559665,1086049,3150966,3670646,2106688,1086016,2633298,1609331,2167905,2110034,2132050,2630738,2630994,1381458,2142321,2132594,1383507,2238578,3937398,2764900,690802,1152065,1085968,2236528,2171235,2106482,2100081,3672694,2107730,2169969,2132598,559729,2764914,2100016,2656369,2105954,2101090,2198641,3180150,2171252,1121393,2632305,1089138,1348690,1154145,2236496,3413105,3675235,1608291,1121345,1609332,1608290,2762849,3217523,591186,2892130,528210,2171254,2106230,2304099,1121328,1088082,2108498,2636882,2107712,2100032,2106194,691794,2173041,2106416,559648,2883953,2106177,2360180,2884434,3932785,3153012,2142290,2168914,1152100,559682,2240577,1606226,2142273,2099536,2132032,1575745]
  | 9 => [3146887,559714,3146375,691793,1383522,2236547,1086050,3675271,1086033,2099537,1119347,2167939,2168962,2634850,2106210,2107713,2359683,2099520,691776,2634851,691810,2108531,2764930,559697,1383505,1086034,2132098,2764915,2106227,691792,2099538,690785,1087041,2099504,2106740,2171267,2634834,1383521,2764931,2106466,2883972,2171010,1121394,2238596,2132096,2764898,2360709,1119330,2167938,1608273,2630481,2108001,2099536,2764914,2100033,2892163,2892147]
  | _ => []

end LiveAIG

namespace LiveAIG.TableHybrid
open Layers
def target : W := 340282366920937254519035908547186436608
def start : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
def sym0 : Array W := #[0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000,0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000,0xf0f0f0f00000000,0x3333333300000000,0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000,0xaaaa0000ffff0000,0xaaaaaaaa00000000,0xaaaaaaaaaaaaaaaa,0xcccccccc00000000,0xcccccccccccccccc,0xf0f0f0f000000000,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xff00ff00ff00ff00,0xffff000000000000,0xffff0000ffff0000,0xffffaaaaffffaaaa,0xffffff00ffffff00,0xffffffff00000000,0xffffffffaaaaaaaa,0xffffffffff00ff00,0xffffffffffff0000,0xffff0000000000000000,0xaa00aa0000000000aa00aa,0xaa00aaaaaaaaaaaaaaaaaa,0xcc00cc0000000000cc00cc,0xcc00cccccccccccccccccc,0xf000f00000000000f000f0,0xf000f0f0f0f0f0f0f0f0f0,0xff00000000000000ff0000,0xff0000ffff0000ffff0000,0xff00ff0000000000000000,0xf0f0f0f0000000000000000,0x303030303030303030303030,0x333333330000000000000000,0x444444440000000044444444,0x44444444cccccccccccccccc,0x505050500000000050505050,0x50505050f0f0f0f0f0f0f0f0,0x550055000000000055005500,0x55005500ff00ff00ff00ff00,0x555500000000000055550000,0x55550000ffff0000ffff0000,0x555555550000000000000000,0xaaaaaaaa0000000000000000,0xaaaaaaaa00000000aaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaa]
def sym1 : Array W := #[0xcccccccc0000000000000000,0xcccccccc00000000cccccccc,0xcccccccccccccccccccccccc,0xf0f0f0f00000000000000000,0xf0f0f0f000000000f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfcfcfcfcfc,0xff00ff000000000000000000,0xff00ff0000000000ff00ff00,0xff00ff000000ff00ff00ff00,0xff00ff00ff00ff00ff00ff00,0xffff00000000000000000000,0xffff000000000000ffff0000,0xffff000000ff0000ffff0000,0xffff0000ffff0000ffff0000,0xffffffff0000000000000000,0xffffffff00000000aaaaaaaa,0xffffffff00000000ff00ff00,0xffffffff00000000ffff0000,0xffffffffffff0000ffff0000,0xffffffffffffffff00000000,0xff00000000000000ff00000000,0xff000000ff0000000000000000,0x5555000000000000555500000000,0x5555000055550000000000000000,0xaaaa0000aaaa0000aaaa0000aaaa,0xcccc0000cccc0000cccc0000cccc,0xf0f00000f0f00000f0f00000f0f0,0xff000000ff000000ff000000ff00,0xffff000000000000000000000000,0xffff000000000000ffff00000000,0xffff0000aaaa0000ffff0000aaaa,0xffff0000eeee0000ffff0000eeee,0xffff0000ff000000ffff0000ff00,0xffff0000ffff0000000000000000,0xffff0000ffff0000aaaa0000aaaa,0xffff0000ffff0000eeee0000eeee,0xffff0000ffff0000ff000000ff00,0xffff0000ffff0000ffff00000000,0xf000f00000000000f000f00000000,0xf000f000f000f0000000000000000,0x330033000000000033003300000000,0x330033003300330000000000000000,0x550055000000000055005500000000,0x550055005500550000000000000000,0xaa00aa0000000000aa00aa00000000,0xaa00aa00aa00aa0000000000000000,0xaa00aa00aa00aa00aa00aa00aa00aa,0xaa00aa00aa00aaaaaaaaaaaaaaaaaa,0xaa00aa00ff00ff00aa00aa00aa00aa,0xcc00cc0000000000cc00cc00000000,0xcc00cc00cc00cc0000000000000000,0xcc00cc00cc00cc00cc00cc00cc00cc,0xcc00cc00cc00cccccccccccccccccc,0xf000f00000000000f000f000000000,0xf000f000f000f00000000000000000,0xf000f000f000f000f000f000f000f0,0xf000f000f000f0f0f0f0f0f0f0f0f0,0xff00000000000000ff000000000000,0xff000000000000ffff0000ffff0000,0xff000000ff00000000000000000000,0xff000000ff000000ff000000ff0000,0xff00ff000000000000000000000000,0xff00ff0000000000ff00ff00000000]
def sym2 : Array W := #[0xff00ff00000000ffffffff00000000,0xff00ff00aa00aa00ff00ff00aa00aa,0xff00ff00ff00ff0000000000000000,0xff00ff00ff00ff00aa00aa00aa00aa,0xff00ff00ff00ff00ee00ee00ee00ee,0xff00ff00ff00ff00fa00fa00fa00fa,0xff00ff00ff00ff00ff000000ff0000,0xff00ff00ff00ff00ff00aa00ff00aa,0xff00ff00ff00ff00ff00ff00000000,0xff00ff00ff00ff00ff00ff00aa00aa,0xff00ff00ff00ffffff0000ffff0000,0xff00ffffffffff00ff0000ffff0000,0x3030303030303030303030300000000,0x5050505000000000505050500000000,0x5050505050505050000000000000000,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0xf000f000f000f000f000f000f000f00,0xf0f00000f0f00000f0f00000f0f0000,0xf0f0f0f000000000000000000000000,0xf0f0f0f000000000f0f0f0f00000000,0xf0f0f0f00000000ffffffff00000000,0xf0f0f0f000f000f0f0f0f0f00000000,0xf0f0f0f050505050f0f0f0f00000000,0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a,0xf0f0f0f0f000f000f0f0f0f0f000f00,0xf0f0f0f0f0f0f0f0000000000000000,0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xf0f0f0f0f0f0f0f0f000f000f000f00,0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0xf0f0f0f0f0f0f0f0f0f0f0f00000000,0xf0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a,0xf0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c,0xf0f0f0f0f0f0f0f0f0f0f0f0f000f00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0000,0xf0f0f0fffffffff0000000000000000,0x11111111000000001111111100000000,0x11111111111111110000000000000000,0x22222222222222222222222222222222,0x30303030303030303030303000000000,0x30303030303030303030303030303030,0x33003300330033003300330033003300,0x33330000333300003333000033330000,0x33333333000000000000000000000000,0x33333333000000003333333300000000,0x3333333300000000ffffffff00000000,0x33333333222222223333333322222222,0x33333333303030303030303030303030,0x33333333330033003333333333003300,0x33333333333333330000000000000000,0x33333333333333332222222222222222,0x33333333333333333300330033003300,0x33333333333333333333000033330000,0x33333333333333333333333300000000,0x33333333333333333333333333330000,0x33333333ffffffff0000000000000000,0x44444444000000004444444400000000,0x44444444444444440000000000000000,0x44444444444444444444444444444444,0x44444444444444444444cccc4444cccc,0x4444444444444444cccccccccccccccc,0x44cc44cc44cc44cc44cc44cc44cc44cc,0x50505050000000005050505000000000,0x50505050505050500000000000000000]
def sym3 : Array W := #[0x50505050505050505050505050505050,0x50505050505050505050f0f05050f0f0,0x5050505050505050f0f0f0f0f0f0f0f0,0x50f050f050f050f050f050f050f050f0,0x55005500000000005500550000000000,0x55005500550055000000000000000000,0x55005500550055005500550055005500,0x55005500550055005500ff005500ff00,0x5500550055005500ff00ff00ff00ff00,0x55550000000000005555000000000000,0x5555000000000000ffff0000ffff0000,0x55550000555500000000000000000000,0x55550000555500005555000055550000,0x55555555000000000000000000000000,0x55555555000000005555555500000000,0x55555555000000005555ffff00000000,0x5555555500000000ffff5555ffff0000,0x5555555500000000ffffffff00000000,0x55555555550055005555555555005500,0x55555555555555550000000000000000,0x55555555555555555500550055005500,0x55555555555555555555000055550000,0x55555555555555555555550055555500,0x55555555555555555555555500000000,0x5555555555555555ffff0000ffff0000,0x55555555ffffffff0000000000000000,0x5555ffff000000005555ffff00000000,0x5555ffff5555ffff0000000000000000,0x55ff55ff0000000055ff55ff00000000,0x55ff55ff55ff55ff0000000000000000,0x55ff55ff55ff55ff55ff000055ff0000,0x88888888888888888888888888888888,0x8888888888888888cccccccccccccccc,0x88888888aaaaaaaaaaaaaaaaaaaaaaaa,0x88888888cccccccc88888888cccccccc,0x88888888cccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xa0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0,0xa0a0a0a0aaaaaaaaaaaaaaaaaaaaaaaa,0xa0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0,0xa0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0,0xaa00aa00aa00aa00aa00aa00aa00aa00,0xaa00aa00aa00aa00aaaaaaaaaaaaaaaa,0xaa00aa00aa00aa00ff00ff00ff00ff00,0xaa00aa00aaaaaaaaaa00aa00aaaaaaaa,0xaa00aa00aaaaaaaaaaaaaaaaaaaaaaaa,0xaa00aa00ff00ff00aa00aa00aa00aa00,0xaa00aa00ff00ff00aa00aa00ff00ff00,0xaa00aa00ff00ff00ff00ff00ff00ff00,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xaaaa0000aaaa0000aaaa0000ffff0000,0xaaaa0000aaaa0000ffff0000ffff0000,0xaaaa0000ffff0000aaaa0000ffff0000,0xaaaa0000ffff0000ffff0000ffff0000,0xaaaaaa00aaaaaaaaaaaaaa00aaaaaaaa,0xaaaaaaaa000000000000000000000000,0xaaaaaaaa00000000aaaaaaaa00000000,0xaaaaaaaa00000000aaaaaaaaaaaaaaaa,0xaaaaaaaa00000000ffffffff00000000,0xaaaaaaaaaa00aa00aaaaaaaaaa00aa00,0xaaaaaaaaaaaaaaaa0000000000000000,0xaaaaaaaaaaaaaaaa00000000aaaaaaaa,0xaaaaaaaaaaaaaaaaaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000]
def sym4 : Array W := #[0xaaaaaaaaaaaaaaaaaaaaaa00aaaaaa00,0xaaaaaaaaaaaaaaaaaaaaaaaa00000000,0xaaaaaaaaaaaaaaaaffff0000ffff0000,0xaaaaaaaaaaaaaaaaffffffffaaaaaaaa,0xaaaaaaaaffffffff0000000000000000,0xaaaaaaaaffffffffaaaa0000ffff0000,0xaaaaaaaaffffffffaaaaaaaaaaaaaaaa,0xaaaaaaffaaaaaaaaaaaaaaffaaaaaaaa,0xaaffaaffaaaaaaaaaaaaaaaaaaaaaaaa,0xaaffaaffaaaaaaaaaaffaaffaaaaaaaa,0xaaffaaffaaffaaffaaaaaaaaaaaaaaaa,0xafafafafaaaaaaaaaaaaaaaaaaaaaaaa,0xbbbbbbbbaaaaaaaaaaaaaaaaaaaaaaaa,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,0xc0c0c0c0cccccccccccccccccccccccc,0xc0c0c0c0f0f0f0f0f0f0f0f0f0f0f0f0,0xcc00cc00cc00cc00cc00cc00cc00cc00,0xcc00cc00cc00cc00cccccccccccccccc,0xcc00cc00cccccccccc00cc00cccccccc,0xcc00cc00cccccccccccccccccccccccc,0xcc00cc00ff00ff00ff00ff00ff00ff00,0xcccc0000cccc0000cccc0000cccc0000,0xcccc0000cccc0000ccff0000ccff0000,0xcccc0000ffff0000ffff0000ffff0000,0xcccccccc000000000000000000000000,0xcccccccc00000000cccccccc00000000,0xcccccccc00000000cccccccccccccccc,0xcccccccc44444444cccccccc44444444,0xcccccccc88888888cccccccc88888888,0xcccccccccc00cc00cccccccccc00cc00,0xcccccccccccccccc0000000000000000,0xcccccccccccccccc00000000cccccccc,0xcccccccccccccccc8888888888888888,0xcccccccccccccccccc00cc00cc00cc00,0xcccccccccccccccccccc0000cccc0000,0xcccccccccccccccccccccccc00000000,0xcccccccccccccccccccccccccccc0000,0xccccccccccccccccffffffffcccccccc,0xcccccccceeeeeeeecccccccceeeeeeee,0xccccccccffffffffcccccccccccccccc,0xccffccffcccccccccccccccccccccccc,0xccffccffccccccccccffccffcccccccc,0xccffccffccffccffcccccccccccccccc,0xcfcfcfcfcccccccccccccccccccccccc,0xcfcfcfcfcfcfcfcfcfcfcfcf00000000,0xcfcfcfcfcfcfcfcfcfcfcfcfcccccccc,0xddddddddcccccccccccccccccccccccc,0xddddddddccccccccddddddddcccccccc,0xddddddddddddddddcccccccccccccccc,0xee00ee00ff00ff00ee00ee00ff00ff00,0xeecceecceecceecceecceecceecceecc,0xeeee0000eeee0000ffff0000ffff0000,0xeeee0000ffff0000eeee0000ffff0000,0xeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaa,0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeeecccccccccccccccc,0xeeeeeeeeeeeeeeeeeeeecccceeeecccc,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xf000f000f000f000f000f000f000f000,0xf000f000f000f000f0f0f0f0f0f0f0f0,0xf000f000f0f0f0f0f000f000f0f0f0f0,0xf000f000f0f0f0f0f0f0f0f0f0f0f0f0,0xf000f000ff00ff00ff00ff00ff00ff00,0xf0f00000f0f00000f0f00000f0f00000]
def sym5 : Array W := #[0xf0f00000ffff0000ffff0000ffff0000,0xf0f0f0f0000000000000000000000000,0xf0f0f0f000000000f0f0f0f000000000,0xf0f0f0f000000000f0f0f0f0f0f0f0f0,0xf0f0f0f000f000f0f0f0f0f000000000,0xf0f0f0f000f000f0f0f0f0f000f000f0,0xf0f0f0f050505050f0f0f0f000000000,0xf0f0f0f050505050f0f0f0f050505050,0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0,0xf0f0f0f0f000f000f0f0f0f0f000f000,0xf0f0f0f0f0f0f0f00000000000000000,0xf0f0f0f0f0f0f0f000000000f0f0f0f0,0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0,0xf0f0f0f0f0f0f0f0f000f000f000f000,0xf0f0f0f0f0f0f0f0f0f00000f0f00000,0xf0f0f0f0f0f0f0f0f0f0f0f000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0,0xf0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0,0xf0f0f0f0f0f0f0f0f0f0f0f0f000f000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f00000,0xf0f0f0f0f0f0f0f0fffffffff0f0f0f0,0xf0f0f0f0fafafafaf0f0f0f0fafafafa,0xf0f0f0f0fff0fff0f0f0f0f0fff0fff0,0xf0f0f0f0fffffffff0f0f0f0f0f0f0f0,0xf0fff0fff0f0f0f0f0f0f0f0f0f0f0f0,0xf0fff0fff0f0f0f0f0fff0fff0f0f0f0,0xf0fff0fff0fff0fff0f0f0f0f0f0f0f0,0xf3f3f3f3f0f0f0f0f0f0f0f0f0f0f0f0,0xf5f5f5f5f0f0f0f0f0f0f0f0f0f0f0f0,0xf5f5f5f5f0f0f0f0f5f5f5f5f0f0f0f0,0xf5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0,0xfa00fa00ff00ff00fa00fa00ff00ff00,0xfaf0faf0faf0faf0faf0faf0faf0faf0,0xfafa0000fafa0000ffff0000ffff0000,0xfafa0000ffff0000fafa0000ffff0000,0xfafafafaaaaaaaaafafafafaaaaaaaaa,0xfafafafafafafafaaaaaaaaaaaaaaaaa,0xfafafafafafafafaf0f0f0f0f0f0f0f0,0xfafafafafafafafafafaf0f0fafaf0f0,0xfafafafafafafafafafafafafafafafa,0xfcfcfcfcfcfcfcfcfcfcfcfc00000000,0xfcfcfcfcfcfcfcfcfcfcfcfccccccccc,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xff000000ff000000ff000000ff000000,0xff000000ff000000ffff0000ffff0000,0xff000000ffff0000ff000000ffff0000,0xff000000ffff0000ffff0000ffff0000,0xff00ff00000000000000000000000000,0xff00ff0000000000ff00ff0000000000,0xff00ff0000000000ff00ff00ff00ff00,0xff00ff0000000000ffffffff00000000,0xff00ff00aa00aa00ff00ff00aa00aa00,0xff00ff00ff00ff000000000000000000,0xff00ff00ff00ff0000000000ff00ff00,0xff00ff00ff00ff00aa00aa00aa00aa00,0xff00ff00ff00ff00aa00aa00ff00ff00,0xff00ff00ff00ff00ee00ee00ee00ee00,0xff00ff00ff00ff00fa00fa00fa00fa00,0xff00ff00ff00ff00ff000000ff000000,0xff00ff00ff00ff00ff00aa00ff00aa00,0xff00ff00ff00ff00ff00ff0000000000,0xff00ff00ff00ff00ff00ff00aa00aa00,0xff00ff00ff00ff00ff55ff55ff00ff00,0xff00ff00ff00ff00ffff0000ffff0000]
def sym6 : Array W := #[0xff00ff00ff00ff00ffffaa00ffffaa00,0xff00ff00ff00ff00ffffff00ffffff00,0xff00ff00ff00ff00ffffffffff00ff00,0xff00ff00ffffffff0000000000000000,0xff00ff00ffffffffff00ff00ff00ff00,0xff05ff05ff00ff00ff05ff05ff00ff00,0xff0fff0fff00ff00ff00ff00ff00ff00,0xff11ff11ff00ff00ff11ff11ff00ff00,0xff33ff33ff00ff00ff00ff00ff00ff00,0xff55ff55ff00ff00ff00ff00ff00ff00,0xff55ff55ff00ff00ff55ff55ff00ff00,0xff55ff55ff55ff550000000000000000,0xff55ff55ff55ff55ff00ff00ff00ff00,0xffaaffaaffaaffaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaff00ff00ff00ff00,0xffaaffaaffaaffaaffaaff00ffaaff00,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xffcc0000ffcc0000ffff0000ffff0000,0xffccffccff00ff00ffccffccff00ff00,0xffccffccffccffcccccccccccccccccc,0xffccffccffccffccff00ff00ff00ff00,0xffccffccffccffccffccffccffccffcc,0xfff00000fff00000ffff0000ffff0000,0xfff0fff0ff00ff00fff0fff0ff00ff00,0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0ff00ff00ff00ff00,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffff0000000000000000000000000000,0xffff000000000000ffff000000000000,0xffff000000000000ffff0000ffff0000,0xffff0000aaaa0000ffff0000aaaa0000,0xffff0000aaaa0000ffff0000ffff0000,0xffff0000cccc0000ffff0000ffff0000,0xffff0000eeee0000ffff0000eeee0000,0xffff0000f0f00000ffff0000ffff0000,0xffff0000ff000000ffff0000ff000000,0xffff0000ff000000ffff0000ffff0000,0xffff0000ffff00000000000000000000,0xffff0000ffff000000000000ffff0000,0xffff0000ffff0000aaaa0000aaaa0000,0xffff0000ffff0000aaaa0000ffff0000,0xffff0000ffff0000eeee0000eeee0000,0xffff0000ffff0000ff000000ff000000,0xffff0000ffff0000ffff000000000000,0xffff0000ffff0000ffff5555ffff0000,0xffff0000ffff0000ffffffffffff0000,0xffff0000ffff00ffffff0000ffff0000,0xffff0000ffff0f0fffff0000ffff0000,0xffff0000ffff3333ffff0000ffff0000,0xffff0000ffff5555ffff0000ffff0000,0xffff0000ffffffffffff0000ffff0000,0xffff000fffff000fffff0000ffff0000,0xffff0033ffff0033ffff0000ffff0000,0xffff00ffffff0000ffff0000ffff0000,0xffff00ffffff0000ffff00ffffff0000,0xffff00ffffff00ffffff0000ffff0000,0xffff0505ffff0000ffff0505ffff0000,0xffff0505ffff0505ffff0000ffff0000,0xffff0f0fffff0000ffff0000ffff0000,0xffff1111ffff0000ffff1111ffff0000,0xffff1111ffff1111ffff0000ffff0000,0xffff3333ffff0000ffff0000ffff0000,0xffff3333ffff3333ffff3300ffff3300,0xffff5555ffff0000ffff0000ffff0000]
def sym7 : Array W := #[0xffff5555ffff0000ffff5555ffff0000,0xffff5555ffff5555ffff0000ffff0000,0xffff5555ffff5555ffff5555ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffaaaaffffffffffff0000ffff0000,0xffffccccffffccccffffccccffffcccc,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffff00ff00ff00ffffff00ff00ff00,0xffffff00ffffff00ffffff00ffffff00,0xffffff00ffffffffffff0000ffff0000,0xffffffff000000000000000000000000,0xffffffff00000000aaaaaaaa00000000,0xffffffff00000000ff00ff0000000000,0xffffffff00000000ffff000000000000,0xffffffff00000000ffff0000ffff0000,0xffffffff00ff00ffffffffff00000000,0xffffffff303030303030303030303030,0xffffffff555555550000000000000000,0xffffffff55555555ffffffff00000000,0xffffffffaa00aa00ffffffffaa00aa00,0xffffffffaaaa0000ffffffffaaaa0000,0xffffffffaaaaaaaa0000000000000000,0xffffffffaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffaaaaaaaaffffffff00000000,0xffffffffaaaaaaaaffffffffaaaa0000,0xffffffffaaaaaaaaffffffffaaaaaaaa,0xffffffffcccccccccccccccccccccccc,0xffffffffccccccccffffffff00000000,0xffffffffccccccccffffffffcccccccc,0xffffffffeeeeeeeecccccccccccccccc,0xffffffffeeeeeeeeffffffffeeeeeeee,0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffff0f0f0f0ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0,0xfffffffffafafafaf0f0f0f0f0f0f0f0,0xfffffffffafafafafffffffffafafafa,0xfffffffffcfcfcfcfcfcfcfcfcfcfcfc,0xffffffffff00ff000000000000000000,0xffffffffff00ff00ff00ff00ff00ff00,0xffffffffff00ff00ffffff00ff00ff00,0xffffffffff00ff00ffffffff00000000,0xffffffffff00ff00ffffffffff00ff00,0xffffffffffaaffaaaaaaaaaaaaaaaaaa,0xffffffffffaaffaaff00ff00ff00ff00,0xffffffffffaaffaaffffffffffaaffaa,0xffffffffffccffcccccccccccccccccc,0xffffffffffccffccffffffffffccffcc,0xfffffffffff0fff0f0f0f0f0f0f0f0f0,0xfffffffffff0fff0fffffffffff0fff0,0xffffffffffff0000ffff0000ffff0000,0xffffffffffff0000ffffff00ffff0000,0xffffffffffff0000ffffffffffff0000,0xffffffffffffaaaaffff0000ffff0000,0xffffffffffffaaaaffffffffffffaaaa,0xffffffffffffff00ffff0000ffff0000,0xffffffffffffff00ffffffffffffff00,0xffffffffffffffff00000000aaaaaaaa,0xffffffffffffffff0000aaaa0000aaaa,0xffffffffffffffff0000ff000000ff00,0xffffffffffffffff0000ffff00000000,0xffffffffffffffff00aa00aa00aa00aa,0xffffffffffffffff00ff00ff00000000,0xffffffffffffffff5555555500000000,0xffffffffffffffffaa00aa00aa00aa00]
def sym8 : Array W := #[0xffffffffffffffffaaaa0000aaaa0000,0xffffffffffffffffaaaaaaaa00000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffcccccccc00000000,0xffffffffffffffffcccccccccccccccc,0xffffffffffffffffeeee0000eeee0000,0xffffffffffffffffeeeeeeeeeeeeeeee,0xfffffffffffffffff0f0f0f000000000,0xfffffffffffffffff0f0f0f0f0f0f0f0,0xfffffffffffffffffafafafafafafafa,0xffffffffffffffffff00ff00ff00ff00,0xffffffffffffffffffaaffaaffaaffaa,0xffffffffffffffffffccffccffccffcc,0xfffffffffffffffffff0fff0fff0fff0,0xffffffffffffffffffff0000ffff0000,0xffffffffffffffffffff5555ffff0000,0xffffffffffffffffffffaa00ffffaa00,0xffffffffffffffffffffaaaaffffaaaa,0xffffffffffffffffffffccccffffcccc,0xfffffffffffffffffffff0f0fffff0f0,0xffffffffffffffffffffff00ffff0000,0xffffffffffffffffffffff00ffffff00,0xffffffffffffffffffffffff00000000,0xffffffffffffffffffffffffaaaaaaaa,0xffffffffffffffffffffffffcccccccc,0xfffffffffffffffffffffffff0f0f0f0,0xffffffffffffffffffffffffff00ff00,0xffffffffffffffffffffffffffff0000]
def wordBank : Array (Array W) := #[sym0,sym1,sym2,sym3,sym4,sym5,sym6,sym7,sym8]
def symbol (i:Nat) : W := ((wordBank[i/64]?).getD #[])[i % 64]?.getD 0
def pool := decode start symbol
def v0b0 : Array Nat := #[0x3fc]
def v0 : Table := #[v0b0]
def v1b0 : Array Nat := #[0x307fa,0x347fa,0x387fa,0x3c7fa,0x407fa,0x467fa,0x7c7fa,0x827fa,0x887fa,0x907fa,0x987fa,0x9e7fa,0xb27fa,0xb47fa,0xb67fa,0xb87fa,0xbc7fa,0xc47fa,0xde7fa,0xe87fa,0xf07fa,0xfa7fa,0xfe7fa,0x1047fa,0x11e7fa,0x1207fa,0x1227fa,0x1247fa,0x1287fa,0x1347fa,0x14c7fa,0x1507fa]
def v1b1 : Array Nat := #[0x1527fa,0x1547fa,0x1587fa,0x1627fa,0x1747fa,0x1807fa,0x18c7fa,0x1987fa,0x19c7fa,0x1a67fa,0x1be7fa,0x1c87fa,0x1d27fa,0x1e27fa,0x1f07fa,0x1f87fa,0x21a7fa,0x2207fa,0x22a7fa,0x2327fa,0x23c7fa,0x2727fa,0x2747fa,0x27e7fa,0x2847fa,0x2947fa,0x2ce7fa,0x2d47fa,0x2d67fa,0x2e07fa,0x2e87fa,0x3207fa]
def v1b2 : Array Nat := #[0x32a7fa,0x3347fa,0x3387fa,0x34a7fa,0x3867fa,0x38a7fa,0x38c7fa,0x3907fa,0x3947fa,0x3b27fa,0x3b87fa,0x3c27fa,0x3d27fa,0x3e67fa,0x4047fa,0x4087fa,0x4107fa,0x4147fa,0x41c7fa,0x42c7fa,0x4077b,0x1507db,0x41c77b,0x2d47db]
def v1 : Table := #[v1b0,v1b1,v1b2]
def v2b0 : Array Nat := #[0x27209ebf8,0x42c0b2bf8,0x42c14cbf8,0x404158bf8,0x42c272bf8,0x4042d4bf8,0x42c386bf8,0x42c390bf8,0x4083b2bf8,0x4043b8bf8,0x7f9,0x27f9,0x47f9,0x67f9,0x87f9,0x41c00ab79,0x41c00cb79,0x41c00eb79,0x41c010b79,0x127f9,0x41c012b79,0x147f9,0x167f9,0x187f9,0x1a7f9,0x1c7f9,0x1e7f9,0x207f9,0x227f9,0x247f9,0x267f9,0x287f9]
def v2b1 : Array Nat := #[0x2a7f9,0x2e7f9,0x1a60309f9,0x1a6030bf1,0x307f9,0x4040309f9,0x41c030b79,0x3b2030bf1,0x327f9,0x41c034b79,0x367f9,0x41c038b79,0x3a7f9,0x10403c9f9,0x10403cbb9,0x3c7f9,0x41403c9f9,0x41c03cb79,0x3d203cbb9,0x3e7f9,0x46040b79,0x9e040b79,0xfe040b79,0x104040b79,0x19c040b79,0x1a6040b79,0x394040b79,0x3b2040b79,0x3d2040b79,0x404040b79,0x414040b79,0x41c040b79]
def v2b2 : Array Nat := #[0x42c040b79,0x9e0469f9,0x9e046af9,0xfe046af9,0x128046af9,0x150046bd9,0x158046af9,0x19c046af9,0x394046af9,0x467f9,0x42c0469f9,0x3b2046af9,0x3b8046af9,0x3c2046af9,0x3d2046af9,0x41c046b79,0x2d4046bd9,0x487f9,0x4a7f9,0x4e7f9,0x507f9,0x547f9,0x587f9,0x5c7f9,0x607f9,0x627f9,0x667f9,0x687f9,0x6c7f9,0x707f9,0x747f9,0x787f9]
def v2b3 : Array Nat := #[0x7a7f9,0x19c07caf9,0x19c07cbf1,0x7c7f9,0x3b207caf9,0x41c07cb79,0x40407cbf1,0x7e7f9,0x39407ebf1,0x807f9,0x41c082b79,0x847f9,0x394084be9,0x867f9,0x41c088b79,0x8a7f9,0x39408abd9,0x8e7f9,0xfe090af9,0xfe090bb9,0x907f9,0x3d2090af9,0x41c090b79,0x414090bb9,0x947f9,0x394094bb9,0x967f9,0x9c7f9,0x39409cb79,0x13409e9f9,0x15009ebd9,0x16209e9f9]
def v2b4 : Array Nat := #[0x33a09eb79,0x39409e9f9,0x9e7f9,0x40809e9f9,0x41009e9f9,0x42c09eaf9,0x36409eb79,0x41c09eb79,0x2d409ebd9,0xa07f9,0xa27f9,0x41c0a4b79,0xaa7f9,0xac7f9,0xae7f9,0xb07f9,0x1040b8bb9,0x3d20b8bb9,0xba7f9,0x19c0bcaf9,0x3b20bcaf9,0xbe7f9,0xc27f9,0x1a60c49f9,0x4040c49f9,0xc67f9,0xca7f9,0xcc7f9,0xce7f9,0xd07f9,0xd27f9,0xd47f9]
def v2b5 : Array Nat := #[0xd67f9,0xd87f9,0xda7f9,0xdc7f9,0x1040debb9,0x41c0deb79,0x3d20debb9,0x4040debf1,0xe47f9,0xe67f9,0x41c0e8b79,0xec7f9,0xee7f9,0x41c0f0b79,0xf47f9,0xf87f9,0xfc7f9,0x1500febd9,0x19c0feaf9,0x2e00feaf9,0xfe7f9,0x3b20feaf9,0x42c0feaf9,0x41c0feb79,0x3d20febb9,0x2d40febd9,0x1027f9,0x150104bd9,0x1a61049f9,0x1d2104bb9,0x2d8104b79,0x2e81049f9]
def v2b6 : Array Nat := #[0x1047f9,0x4041049f9,0x36e104b79,0x41c104b79,0x390104bb9,0x414104bb9,0x2d4104bd9,0x1067f9,0x404106bb9,0x41c10cb79,0x1107f9,0x11a7f9,0x11c7f9,0x41c11eb79,0x3b211ebf1,0x40411ebf1,0x41c120b79,0x41c122b79,0x3d2122bb9,0x414122bb9,0x1267f9,0x42c128af9,0x41c128b79,0x1307f9,0x1327f9,0x42c1349f9,0x41c134b79,0x1367f9,0x1387f9,0x41c13ab79,0x13c7f9,0x42c13cbd9]
def v2b7 : Array Nat := #[0x1487f9,0x14a7f9,0x41c14cb79,0x3b214cbf1,0x40414cbf1,0x19c150bd9,0x1a6150bd9,0x41c150b79,0x394150bd9,0x3b2150bd9,0x3d2150bd9,0x404150bd9,0x414150bd9,0x42c150bd9,0x41c152b79,0x3d2152bb9,0x414152bb9,0x1567f9,0x42c158af9,0x41c158b79,0x15c7f9,0x1607f9,0x42c1629f9,0x41c162b79,0x1647f9,0x1667f9,0x41c168b79,0x16a7f9,0x1707f9,0x1727f9,0x41c174b79,0x17c7f9]
def v2b8 : Array Nat := #[0x17e7f9,0x41c180b79,0x1887f9,0x18a7f9,0x41c18cb79,0x41418cbb9,0x1927f9,0x1967f9,0x19a7f9,0x1de19cbb9,0x1e819cb79,0x1f019caf9,0x19c7f9,0x3d219caf9,0x3e619caf9,0x42c19caf9,0x38019cb79,0x41c19cb79,0x31419cbb9,0x2d419cbd9,0x3b219cbf1,0x1a47f9,0x1e61a6b79,0x1f81a69f9,0x1a67f9,0x4141a69f9,0x41c1a69f9,0x3821a6b79,0x41c1a6b79,0x2d41a6bd9,0x4041a6bf1,0x1a87f9]
def v2b9 : Array Nat := #[0x41c1aab79,0x1ae7f9,0x41c1beb79,0x1c07f9,0x1c47f9,0x41c1c8b79,0x1ca7f9,0x1ce7f9,0x41c1d2b79,0x3d21d2bb9,0x1d47f9,0x1d67f9,0x1d87f9,0x1de7f9,0x1e67f9,0x1e87f9,0x1ee7f9,0x1f07f9,0x3b21f0af9,0x41c1f0b79,0x3b21f0bf1,0x1f27f9,0x1f47f9,0x1f67f9,0x1f87f9,0x4041f89f9,0x41c1f8b79,0x4041f8bf1,0x1fa7f9,0x1fc7f9,0x41c1feb79,0x2027f9]
def v2b10 : Array Nat := #[0x2067f9,0x2087f9,0x20c7f9,0x2127f9,0x2147f9,0x41c21ab79,0x41c220b79,0x2227f9,0x2247f9,0x2307f9,0x41c232b79,0x2347f9,0x2387f9,0x23a7f9,0x41c23cb79,0x23e7f9,0x2407f9,0x2427f9,0x41c244b79,0x2467f9,0x24a7f9,0x24e7f9,0x2527f9,0x2547f9,0x25e7f9,0x2607f9,0x41c272b79,0x41c274b79,0x2767f9,0x2787f9,0x2827f9,0x41c284b79]
def v2b11 : Array Nat := #[0x2867f9,0x2907f9,0x2927f9,0x41c294b79,0x2967f9,0x2987f9,0x29a7f9,0x41c29cb79,0x29e7f9,0x42c29ebd9,0x2a87f9,0x2ae7f9,0x2b27f9,0x2b47f9,0x2ba7f9,0x2bc7f9,0x41c2ceb79,0x41c2d4b79,0x2d87f9,0x2da7f9,0x2de7f9,0x2e07f9,0x3d22e0af9,0x41c2e0b79,0x3d22e0bb9,0x2e27f9,0x2e47f9,0x2e67f9,0x2e87f9,0x4142e89f9,0x41c2e8b79,0x4142e8bb9]
def v2b12 : Array Nat := #[0x2ea7f9,0x2ec7f9,0x4042ecbb9,0x41c2f4b79,0x2f87f9,0x3047f9,0x3067f9,0x3087f9,0x3147f9,0x3187f9,0x41c320b79,0x41c32ab79,0x41c334b79,0x3367f9,0x33a7f9,0x33c7f9,0x3467f9,0x34c7f9,0x34e7f9,0x3547f9,0x3567f9,0x35a7f9,0x3647f9,0x36c7f9,0x36e7f9,0x3807f9,0x3827f9,0x3947f9,0x42c3949f9,0x42c394af9,0x3967f9,0x3987f9]
def v2b13 : Array Nat := #[0x39e7f9,0x3a47f9,0x3aa7f9,0x3ac7f9,0x3b27f9,0x3b47f9,0x3bc7f9,0x3be7f9,0x3c67f9,0x3ca7f9,0x3cc7f9,0x3d27f9,0x3d87f9,0x3dc7f9,0x3e07f9,0x3e27f9,0x3ea7f9,0x3ee7f9,0x3fa7f9,0x3fc7f9,0x4047f9,0x40c7f9,0x4127f9,0x4147f9,0x4167f9,0x4187f9,0x41a7f9,0x4227f9,0x42a7f9,0x42c7f9,0x42e7f9,0x4307f9]
def v2b14 : Array Nat := #[0x4327f9,0x4347f9,0x4367f9,0x4144049f9,0x41c4049f9,0x42c4089f9,0x42c4109f9,0x3d23b2af9,0x3e63b2af9,0x42c3b2af9,0x42c3b8af9,0x42c3c2af9,0x42c3d2af9,0x3e2394b79,0x41c394b79,0x41c39ab79,0x41c3b2b79,0x41c3b8b79,0x41c3c2b79,0x41c3d2b79,0x41c404b79,0x41c408b79,0x41c410b79,0x41c414b79,0x42241cb79,0x42441cb79,0x42641cb79,0x42a41cb79,0x42c41cb79,0x43641cb79,0x414320bb9,0x3d232abb9]
def v2b15 : Array Nat := #[0x41432abb9,0x3d2334bb9,0x414334bb9,0x3d2390bb9,0x3cc394bb9,0x4143d2bb9,0x3942d4bd9,0x3b22d4bd9,0x3d22d4bd9,0x4042d4bd9,0x4142d4bd9,0x42c2d4bd9,0x3be394bd9,0x3b4394be9,0x3b2272bf1,0x404272bf1,0x3b22cebf1,0x4042cebf1,0x404320bf1,0x3ac394bf1,0x4043b2bf1,0x4077a,0x41c04097a,0x7e7f2,0x847ea,0x8a7da,0x947ba,0x9c77a,0x1067ba,0x13c7da,0x41c150b5a,0x41c16297a]
def v2b16 : Array Nat := #[0x41c1a697a,0x1de7ba,0x1e677a,0x1e877a,0x29e7da,0x2d877a,0x2ec7ba,0x33a77a,0x36477a,0x36e77a,0x38077a,0x38277a,0x3e277a,0x41c40497a,0x41c40897a,0x3147ba,0x3cc7ba,0x41c2d4b5a,0x3be7da,0x3b47ea,0x3ac7f2]
def v2 : Table := #[v2b0,v2b1,v2b2,v2b3,v2b4,v2b5,v2b6,v2b7,v2b8,v2b9,v2b10,v2b11,v2b12,v2b13,v2b14,v2b15,v2b16]
def v3b0 : Array Nat := #[0x40827209ede8,0x2d427209efc8,0x42c272158ee8,0x404272158fe0,0x2d420cbd8,0x42c4083b2cf8,0x39e390bb8,0x42c3b22d4ed8,0x27224ebe8,0x42c408272de8,0x42c2d4272fc8,0x4083b22d4fc8,0x4043b82d4fc8,0x27220cbf0,0x4043b22d4fd0,0x4042d4272fe0,0x2d4002bc9,0x2d4022bc9,0x41c028979,0x2c779,0x7e040b71,0x84040b69,0x8a040b59,0x94040b39,0x106040b39,0x13c040b59,0x1de040b39,0x29e040b59,0x2ec040b39,0x314040b39,0x3cc040b39,0x3be040b59]
def v3b1 : Array Nat := #[0x3b4040b69,0x3ac040b71,0x41c042979,0x41c044979,0x314046ab9,0x3cc046ab9,0x3be046ad9,0x3b4046ae9,0x3b82d4046ec9,0x3ac046af1,0x41c04c979,0x527f1,0x567e9,0x5a7d9,0x5e779,0x647d9,0x3b4064bc9,0x2d4068bc9,0x6a7e9,0x6e7d9,0x727b9,0x76779,0x41c40407cd71,0x8407ebe1,0x8a07ebd1,0x9407ebb1,0x9c07eb71,0x15007ebd1,0x7e7f1,0x3e207eb71,0x41c07eb71,0x3cc07ebb1]
def v3b2 : Array Nat := #[0x2d407ebd1,0x3be07ebd1,0x3b407ebe1,0x8a084bc9,0x94084ba9,0x9c084b69,0x150084bc9,0x847e9,0x3e2084b69,0x41c084b69,0x3cc084ba9,0x2d4084bc9,0x3be084bc9,0x3ac084be1,0x9408ab99,0x9c08ab59,0x8a7d9,0x3e208ab59,0x41c08ab59,0x3cc08ab99,0x3b408abc9,0x3ac08abd1,0x8c7d9,0x41c092b39,0x9c094b39,0x150094b99,0x947b9,0x3e2094b39,0x41c094b39,0x2d4094b99,0x3be094b99,0x3b4094ba9]
def v3b3 : Array Nat := #[0x3ac094bb1,0x9a779,0x15009cb59,0x9c779,0x3cc09cb39,0x2d409cb59,0x3be09cb59,0x3b409cb69,0x3ac09cb71,0x3be09e9d9,0x3b409e9e9,0x4082d409edc9,0xa6779,0xa85f9,0xa86f9,0xc0779,0xc8779,0x41c4040ded71,0x41c0e0b71,0xe27b9,0x41c0eab69,0x41c0f2b59,0xf6779,0x1006f9,0x41c100a79,0x150106b99,0x41c106b39,0x41c404106d39,0x2d4106b99,0x1087b9,0x10a7b9,0x41c10eb39]
def v3b4 : Array Nat := #[0x1127b9,0x114779,0x116779,0x1187d9,0x41c40411ed71,0x42c134128cd9,0x29e128ad9,0x12a6f9,0x12c7d9,0x12e7d9,0x29e1349d9,0x13c7d9,0x41c13cb59,0x13e7d9,0x1407d9,0x1427d9,0x1447d9,0x41c144b59,0x1465f9,0x41c14a979,0x41c40414cd71,0x14e7d9,0x41c1a6150d59,0x1de150b99,0x1e6150b59,0x1e8150b59,0x2d8150b59,0x2ec150b99,0x33a150b59,0x364150b59,0x36e150b59,0x380150b59]
def v3b5 : Array Nat := #[0x382150b59,0x3e2150b59,0x41c404150d59,0x314150b99,0x3cc150b99,0x3b4150bc9,0x3ac150bd1,0x15a6f9,0x15e7d9,0x364162979,0x41c164979,0x16c7e9,0x41c16cb69,0x16e5f9,0x41c176b69,0x41c178b69,0x41c17ab69,0x41c182b59,0x41c184b59,0x41c186b59,0x41c18eb39,0x41c190b39,0x194779,0x41c19ea79,0x1a0779,0x1a26f9,0x41c1a2a79,0x2041a6979,0x41c1a6979,0x41c2d41a6d59,0x41c4041a6d71,0x41c4041aad71]
def v3b6 : Array Nat := #[0x1ac7f1,0x41c1acb71,0x1b0779,0x41c1b2979,0x1b46f9,0x1b65f9,0x41c1b8a79,0x41c1ba979,0x1bc779,0x2d41c0bc9,0x1c27f1,0x2d41c4bc9,0x1c67e9,0x1cc7f1,0x1d07d9,0x1da7f1,0x1dc7b9,0x1e81deb39,0x1de7b9,0x3801deb39,0x41c1deb39,0x2d41deb99,0x1e07b9,0x1e4779,0x1e6779,0x41c1e6979,0x2d41e6b59,0x1e8779,0x3e61e8a79,0x3141e8b39,0x2d41e8b59,0x1ea779]
def v3b7 : Array Nat := #[0x1ec7f1,0x41c4041fed71,0x2007f1,0x41c200b71,0x204779,0x41c204979,0x20a779,0x21c7e9,0x21e7d9,0x2d4222bc9,0x2d4224bc9,0x2267e9,0x2287b9,0x22c779,0x22e779,0x2d4234bc9,0x41c236b69,0x2d423ebc9,0x2487e9,0x41c248b69,0x2587d9,0x25a7d9,0x41c260979,0x2627b9,0x266779,0x268779,0x27a7d9,0x27c7b9,0x280779,0x2887d9,0x41c28ab59,0x28c7d9]
def v3b8 : Array Nat := #[0x41c28eb59,0x29e7d9,0x41c29eb59,0x2a07d9,0x2a27d9,0x2a47d9,0x2a67d9,0x41c2a6b59,0x2be7b9,0x2c2779,0x2c4779,0x2d8779,0x2dc779,0x2ec7b9,0x41c2ecb39,0x41c4042ecd39,0x2ee7b9,0x2f07b9,0x2f27b9,0x41c2f6b39,0x2fa7b9,0x2fe779,0x41c316979,0x322779,0x32c779,0x33a779,0x33e779,0x340779,0x342779,0x344779,0x348779,0x350779]
def v3b9 : Array Nat := #[0x352779,0x3f9,0x4005f9,0x4065f9,0x40e5f9,0x3a86f9,0x3ae6f9,0x3b66f9,0x3c06f9,0x3d06f9,0x358779,0x35c779,0x35e779,0x360779,0x362779,0x364779,0x408364979,0x366779,0x368779,0x36a779,0x36e779,0x370779,0x372779,0x374779,0x376779,0x378779,0x37a779,0x37c779,0x37e779,0x380779,0x382779,0x384779]
def v3b10 : Array Nat := #[0x388779,0x392779,0x39c779,0x41c3a2979,0x3e2779,0x3e4779,0x3e8779,0x3ec779,0x41e779,0x420779,0x428779,0x41c3f0979,0x41c3f2979,0x41c3f4979,0x41c3f6979,0x41c3f8979,0x41c3fe979,0x41c400979,0x41c402979,0x41c404979,0x41c40c979,0x41c3a6a79,0x41c3aea79,0x41c3b0a79,0x41c3d0a79,0x2fc7b9,0x3027b9,0x30a7b9,0x30c7b9,0x30e7b9,0x3107b9,0x3127b9]
def v3b11 : Array Nat := #[0x42c314ab9,0x380314b39,0x41c314b39,0x41c31cb39,0x41c31eb39,0x3247b9,0x3287b9,0x32e7b9,0x3327b9,0x38e7b9,0x3cc7b9,0x3d67b9,0x42c3ccab9,0x3e23ccb39,0x41c3ccb39,0x41c3ceb39,0x41c2aab59,0x41c2acb59,0x2b07d9,0x2b67d9,0x2b87d9,0x41c2c0b59,0x41c2cab59,0x41c2ccb59,0x2d07d9,0x2d82d4b59,0x2ec2d4b99,0x33a2d4b59,0x3642d4b59,0x36e2d4b59,0x3802d4b59,0x3822d4b59]
def v3b12 : Array Nat := #[0x3e22d4b59,0x41c4042d4d59,0x3142d4b99,0x3cc2d4b99,0x41c330b59,0x3a07d9,0x3be7d9,0x42c3be9d9,0x3c47d9,0x3c87d9,0x3de7d9,0x42c3bead9,0x42c4103c2cd9,0x3e23beb59,0x41c3beb59,0x3cc3beb99,0x2d424abc9,0x41c24cb69,0x2d424ebc9,0x2507e9,0x2d4252bc9,0x2d4254bc9,0x2567e9,0x25c7e9,0x2d425ebc9,0x2d4260bc9,0x41c264b69,0x41c26eb69,0x41c270b69,0x41c326b69,0x3b47e9,0x42c3b49e9]
def v3b13 : Array Nat := #[0x3ba7e9,0x3da7e9,0x42c3b4ae9,0x42c4083b8ce9,0x3e23b4b69,0x41c3b4b69,0x3cc3b4ba9,0x42c2d2bc9,0x3b42d4bc9,0x3bc2d4bc9,0x40c2d4bc9,0x4302d4bc9,0x42c4082d4dc9,0x42c3b82d4ec9,0x3be3b4bc9,0x3c83b4bc9,0x20e7f1,0x2107f1,0x2167f1,0x2187f1,0x26a7f1,0x26c7f1,0x2ec272bb1,0x41c404272d71,0x2c67f1,0x2c87f1,0x41c4042ced71,0x41c31ab71,0x41c404320d71,0x3ac7f1,0x3d47f1,0x42c3acaf1]
def v3b14 : Array Nat := #[0x3e23acb71,0x41c3acb71,0x41c4043b2d71,0x3cc3acbb1,0x3ac2d4bd1,0x3be3acbd1,0x3b22d4272fc1,0x4042d4272fc1,0x3b43acbe1]
def v3 : Table := #[v3b0,v3b1,v3b2,v3b3,v3b4,v3b5,v3b6,v3b7,v3b8,v3b9,v3b10,v3b11,v3b12,v3b13,v3b14]
def v4b0 : Array Nat := #[0x2d427220cfc0,0x40a579,0x300739,0x41c2d4260d49,0x2d27c9,0x3422d4b49,0x3522d4b49,0x4083642d4d49,0x41c40c2d4d49,0x41c4043b0c71,0x41c40431ed31,0x41c4042aad51,0x41c4042ccd51,0x41c40424cd61,0x41c404270d61,0x2ec2d4272f81,0x41c4042d4273141]
def v4 : Table := #[v4b0]
def v5b0 : Array Nat := #[0x40a2d4949]
def v5 : Table := #[v5b0]
def v6 : Table := #[]
def projectBlock0 : Array Nat := #[0x307fa,0x347fa,0x387fa,0x3c7fa,0x407fa,0x7c7fa,0x827fa,0x887fa,0x907fa,0x987fa,0xb27fa,0xb47fa,0xb67fa,0xb87fa,0xbc7fa,0xc47fa,0xde7fa,0xe87fa,0xf07fa,0xfa7fa,0x11e7fa,0x1207fa,0x1227fa,0x1247fa,0x1287fa,0x1347fa,0x14c7fa,0x1507fa,0x1527fa,0x1547fa,0x1587fa,0x1627fa]
def projectBlock1 : Array Nat := #[0x1747fa,0x1807fa,0x18c7fa,0x1987fa,0x1be7fa,0x1c87fa,0x1d27fa,0x1e27fa,0x1f07fa,0x1f87fa,0x21a7fa,0x2207fa,0x22a7fa,0x2327fa,0x23c7fa,0x2727fa,0x2747fa,0x27e7fa,0x2847fa,0x2947fa,0x2ce7fa,0x2d47fa,0x2d67fa,0x2e07fa,0x2e87fa,0x3207fa,0x32a7fa,0x3347fa,0x3387fa,0x34a7fa,0x3867fa,0x38a7fa]
def projectBlock2 : Array Nat := #[0x38c7fa,0x3907fa,0x3b87fa,0x3c27fa,0x3e67fa,0x4087fa,0x4107fa,0x41c7fa,0x4077b,0x1507db,0x2d47db,0x7f9,0x27f9,0x47f9,0x67f9,0x87f9,0x41c00cb79,0x41c00eb79,0x147f9,0x167f9,0x187f9,0x1a7f9,0x227f9,0x247f9,0x267f9,0x287f9,0x2e7f9,0x1a60309f9,0x1a6030bf1,0x307f9,0x4040309f9,0x3b2030bf1]
def projectBlock3 : Array Nat := #[0x327f9,0x41c034b79,0x367f9,0x41c038b79,0x3a7f9,0x10403c9f9,0x10403cbb9,0x3c7f9,0x41403c9f9,0x3d203cbb9,0x3e7f9,0x41c040b79,0x4e7f9,0x507f9,0x547f9,0x587f9,0x5c7f9,0x687f9,0x6c7f9,0x707f9,0x747f9,0x7a7f9,0x19c07caf9,0x19c07cbf1,0x7c7f9,0x3b207caf9,0x40407cbf1,0x7e7f9,0x807f9,0x41c082b79,0x847f9,0x867f9]
def projectBlock4 : Array Nat := #[0x41c088b79,0x8a7f9,0x8e7f9,0xfe090af9,0xfe090bb9,0x907f9,0x3d2090af9,0x414090bb9,0x947f9,0x967f9,0x9c7f9,0xac7f9,0xae7f9,0xb07f9,0x1040b8bb9,0x3d20b8bb9,0xba7f9,0xbe7f9,0xc67f9,0xd67f9,0xd87f9,0xda7f9,0xdc7f9,0x1040debb9,0x3d20debb9,0x4040debf1,0xe47f9,0xe67f9,0x41c0e8b79,0xec7f9,0xee7f9,0x41c0f0b79]
def projectBlock5 : Array Nat := #[0xf47f9,0xf87f9,0x19c0feaf9,0x2e00feaf9,0xfe7f9,0x3b20feaf9,0x1027f9,0x1a61049f9,0x1d2104bb9,0x2e81049f9,0x1047f9,0x4041049f9,0x1067f9,0x41c11eb79,0x3b211ebf1,0x40411ebf1,0x41c120b79,0x41c122b79,0x3d2122bb9,0x414122bb9,0x41c128b79,0x41c134b79,0x41c13ab79,0x41c14cb79,0x3b214cbf1,0x40414cbf1,0x41c150b79,0x41c152b79,0x3d2152bb9,0x414152bb9,0x41c158b79,0x41c162b79]
def projectBlock6 : Array Nat := #[0x41c168b79,0x1707f9,0x1727f9,0x41c174b79,0x17c7f9,0x17e7f9,0x41c180b79,0x1887f9,0x18a7f9,0x41418cbb9,0x1927f9,0x1967f9,0x1de19cbb9,0x1f019caf9,0x19c7f9,0x3d219caf9,0x1a47f9,0x1f81a69f9,0x1a67f9,0x4141a69f9,0x1a87f9,0x41c1beb79,0x1c07f9,0x1c47f9,0x41c1c8b79,0x1ca7f9,0x1ce7f9,0x3d21d2bb9,0x1d47f9,0x1d67f9,0x1d87f9,0x1de7f9]
def projectBlock7 : Array Nat := #[0x1e67f9,0x1e87f9,0x1ee7f9,0x1f07f9,0x3b21f0af9,0x3b21f0bf1,0x1f27f9,0x1f67f9,0x1f87f9,0x4041f89f9,0x4041f8bf1,0x1fa7f9,0x1fc7f9,0x2027f9,0x2127f9,0x2147f9,0x41c21ab79,0x41c220b79,0x2227f9,0x2247f9,0x2307f9,0x41c232b79,0x2347f9,0x2387f9,0x23a7f9,0x41c23cb79,0x23e7f9,0x2407f9,0x2427f9,0x41c244b79,0x2467f9,0x41c272b79]
def projectBlock8 : Array Nat := #[0x41c274b79,0x2767f9,0x2787f9,0x2827f9,0x41c284b79,0x2867f9,0x2907f9,0x2927f9,0x41c294b79,0x2967f9,0x2987f9,0x29a7f9,0x41c29cb79,0x29e7f9,0x41c2ceb79,0x41c2d4b79,0x2d87f9,0x2da7f9,0x2de7f9,0x2e07f9,0x3d22e0af9,0x3d22e0bb9,0x2e27f9,0x2e67f9,0x2e87f9,0x4142e89f9,0x4142e8bb9,0x2ea7f9,0x2ec7f9,0x4042ecbb9,0x2f87f9,0x3147f9]
def projectBlock9 : Array Nat := #[0x3187f9,0x41c32ab79,0x41c334b79,0x3367f9,0x33a7f9,0x33c7f9,0x3467f9,0x34c7f9,0x34e7f9,0x3547f9,0x3567f9,0x3647f9,0x36e7f9,0x3807f9,0x3827f9,0x3b27f9,0x3d27f9,0x3d87f9,0x3e27f9,0x3ea7f9,0x4047f9,0x4147f9,0x4167f9,0x4227f9,0x4144049f9,0x3d23b2af9,0x41c3b8b79,0x41c3c2b79,0x41c408b79,0x41c410b79,0x42441cb79,0x42641cb79]
def projectBlock10 : Array Nat := #[0x414320bb9,0x404320bf1,0x4077a,0x41c04097a,0x7e7f2,0x847ea,0x8a7da,0x947ba,0x9c77a,0x41c150b5a,0x41c16297a,0x1de7ba,0x1e677a,0x1e877a,0x29e7da,0x2d877a,0x2ec7ba,0x33a77a,0x36477a,0x36e77a,0x38077a,0x38277a,0x3e277a,0x41c40897a,0x41c2d4b5a,0x2d4002bc9,0x2d4022bc9,0x41c028979,0x2c779,0x84040b69,0x8a040b59,0x29e040b59]
def projectBlock11 : Array Nat := #[0x527f1,0x567e9,0x5a7d9,0x5e779,0x647d9,0x2d4068bc9,0x6a7e9,0x6e7d9,0x727b9,0x76779,0x9407ebb1,0x7e7f1,0x9c084b69,0x150084bc9,0x847e9,0x3e2084b69,0x41c084b69,0x2d4084bc9,0x9c08ab59,0x8a7d9,0x3e208ab59,0x41c08ab59,0x947b9,0x9a779,0x15009cb59,0x9c779,0x2d409cb59,0xc0779,0xc8779,0x41c0eab69,0x41c0f2b59,0xf6779]
def projectBlock12 : Array Nat := #[0x1006f9,0x29e128ad9,0x12a6f9,0x29e1349d9,0x1465f9,0x14e7d9,0x1e6150b59,0x1e8150b59,0x2d8150b59,0x33a150b59,0x364150b59,0x36e150b59,0x380150b59,0x382150b59,0x3e2150b59,0x15a6f9,0x364162979,0x16e5f9,0x41c176b69,0x41c178b69,0x41c17ab69,0x41c182b59,0x41c184b59,0x41c186b59,0x194779,0x1a26f9,0x1ac7f1,0x1b0779,0x1b46f9,0x1b65f9,0x2d41c0bc9,0x1c27f1]
def projectBlock13 : Array Nat := #[0x2d41c4bc9,0x1c67e9,0x1cc7f1,0x1d07d9,0x1da7f1,0x1dc7b9,0x1de7b9,0x1e07b9,0x1e4779,0x1e6779,0x41c1e6979,0x2d41e6b59,0x1e8779,0x3e61e8a79,0x2d41e8b59,0x1ea779,0x1ec7f1,0x2007f1,0x21c7e9,0x21e7d9,0x2d4222bc9,0x2d4224bc9,0x2267e9,0x2287b9,0x22c779,0x22e779,0x2d4234bc9,0x41c236b69,0x2d423ebc9,0x2487e9,0x41c248b69,0x2627b9]
def projectBlock14 : Array Nat := #[0x266779,0x268779,0x27a7d9,0x27c7b9,0x280779,0x2887d9,0x41c28ab59,0x28c7d9,0x41c28eb59,0x29e7d9,0x41c29eb59,0x2a07d9,0x2a27d9,0x2a47d9,0x2a67d9,0x41c2a6b59,0x2be7b9,0x2c2779,0x2c4779,0x2d8779,0x2dc779,0x2ec7b9,0x2ee7b9,0x2f07b9,0x2f27b9,0x2fa7b9,0x2fe779,0x322779,0x32c779,0x33a779,0x33e779,0x340779]
def projectBlock15 : Array Nat := #[0x342779,0x344779,0x348779,0x350779,0x352779,0x3f9,0x4005f9,0x4065f9,0x40e5f9,0x3a86f9,0x3ae6f9,0x3b66f9,0x3c06f9,0x3d06f9,0x358779,0x35c779,0x35e779,0x360779,0x362779,0x364779,0x408364979,0x366779,0x368779,0x36a779,0x36e779,0x370779,0x372779,0x374779,0x376779,0x378779,0x37a779,0x37e779]
def projectBlock16 : Array Nat := #[0x380779,0x382779,0x384779,0x388779,0x392779,0x3e2779,0x3e8779,0x3ec779,0x41c400979,0x3027b9,0x3247b9,0x3287b9,0x32e7b9,0x3327b9,0x38e7b9,0x2d82d4b59,0x33a2d4b59,0x3642d4b59,0x36e2d4b59,0x3802d4b59,0x3822d4b59,0x3e22d4b59,0x20e7f1,0x26a7f1,0x26c7f1,0x2ec272bb1,0x2c67f1,0x2c87f1,0x40a579,0x300739,0x2d27c9,0x3422d4b49]
def projectBlock17 : Array Nat := #[0x3522d4b49,0x4083642d4d49,0x40a2d4949]
def projectionMetas : Table := #[projectBlock0,projectBlock1,projectBlock2,projectBlock3,projectBlock4,projectBlock5,projectBlock6,projectBlock7,projectBlock8,projectBlock9,projectBlock10,projectBlock11,projectBlock12,projectBlock13,projectBlock14,projectBlock15,projectBlock16,projectBlock17]
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h0b0 : List Nat := [0xa601600a0900a40220080860ac0a809a0200140840a202e00607c09802c01207a08e02a01e0780a003a00407209603801007008c03601c06e08203402806c09e04600206809404400e06608a04201a06408004002606207603e0320600ae0aa09c05200005e09205000c05c08804e01805a07e04c02405807404a03005606a04803c054]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good0b0 : groupHybrid target anchors11246 pool v1 projectionMetas v0b0.toList h0b0=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h1b0 : List Nat := [0x1,0x3,0x5,0x7,0x9,0x6460940820840900f36fd82781a5731eb8c9d8c9d827021d78f1f63276327609a08838e77b27632538c94e09808c0fb7dbd381f253a7253828022d3cc735cc7209608f5e3c78fb8f1e3ecc72f7edf1e38c1286f460903375eb9232a322026067bd9230a300032059bd922d42c80340549d3922a829e0360511e392280278040042,0xb,0xd,0xf,0x11,0x13,0x1918208408428212cb7d84381a83cfbc1e32763276b7dbb7d8c9d84203e8c9d8db9dec9d8c94e1060fe325383fdfef4e07c94e9c94e1100fcb2dcd3cb72b7dbb76fb6eddbecb72000007ffdeddb8c20466c610a37a0f079210c10032c31c0a60f441040fbd9230e2f20b00e3bd922d62c00b20da9d3922aa2960b40d2ddb9228426a0be0c0,0x15,0x17,0x19,0x1b,0x1d,0x1f,0x21,0x23,0x25,0x27,0x648c2d810d66df30b7036998f3193319983905985c039ce3c798c9d8c9d8e39dec9d8c94e3253cedf6f4f3253a725385c858acc73331c85a8594e3c78f38f1e3ecc72c7edf1e38f648d90c300c8584c2cc5d6732465c5cc2302b86170357bd922d82ba1381569d3922ac29013c1511e392286258140144,0x648d65bec30c0dd1e75ecf19d81685f8628170c9db3dbb7d8620480c9d8c9d8db9dec9d8c96e3240fb3f5e37f5ecf25b81f275e18c176b2dc86085e53cb72cf6eddbedbb76e14817bb2dc8df1beddbec2fc5f07b246805e81602c19ecf243082f86605c82342bc824814618a36fbd922da2b813a15807c0f922ae28e13e152ddb92288254142146,0x29,0x2b,0x2d,0x2f,0x31,0x33,0x35,0x37]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good1b0 : groupHybrid target anchors11246 pool v2 projectionMetas v1b0.toList h1b0=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h1b1 : List Nat := [0x39,0x3b,0x3d,0x3f,0x41,0x43,0x45,0x47,0x192310f047c79b7cc4440e2663cc43824c64cc64cc4342ca71e3cc64ec64ec71cef64ec64a71929e76fb7a79929d3929c44c3969e6399c720c22162280c538f1e3ce3c78fb31cb1fb7c78e34e48d98a0810084110b1319c7244404286644bc23841882880e64911210918812d0a010220f201d9245b849c32c3fd39245604903803f26228348,0x1923596fb11a09711c039200479d7b3c64ec4642f064ed9eddbec64ec64ec6dcef64ec64b719207d9faf1bfaf6792dc0f93af11d0e65b7204422e23c0474f2dcb3dbb76fb6eddbecb7237c6fb76e445c4e06491a113605f10867b72446c4586684b823c41c82c80b64918912b0a1103d9245bc4983304000f92456448c3843f5623c368,0x49,0x4b,0x4d,0x4f,0x51,0x53,0x55,0x57,0x59,0x5b,0x5d,0x5f,0x61,0x63,0x65,0x67,0x69,0x6b,0x6d,0x6f,0x71,0x73]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good1b1 : groupHybrid target anchors11246 pool v2 projectionMetas v1b1.toList h1b1=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h1b2 : List Nat := [0x75,0x77,0x79,0x7b,0x7d,0x7f,0x81,0x83,0x378c633810233a0903081082182402489f183cb8e701d0bc75c5e2f1d72e35e1240f631a39a0f84183f66f18cb9bc632e6f18cb8d505803c0ba0f203c9080fd35faf5cb9bc632e2f18cb8bc632e34e1a80de2bc3d80e04243f22f1d72e5c632e6f18c9e2f18eb8bc63ae34a1e20d62923da0d84263f02f0783c9fcf18c9e4f18eb8f307405f1d718bc75c62f1d718d18840338980f983410a0fb8bebd7ae5ebd7ae5eb8eba5f07d7ae,0xbf4fae17c6f817c1446882fd3eb8bc72412e60c60c967e9f32e3a00762f9cc5e36012a0bc31e2f9cc5e39012817e9f32eef9ccb8d605d02e8bdbbe732e38e16aef9ccb85fa7d72e2faf5cb8d406b82e0b08bebd72e2f9d79979d79804001ffa7ce62f9ce634c1e80b62982f9ce62f9ce6ef9ce697ebce63ce1d217e9f398fa013cc43045273983209908a09a0be739979ce65ebce63e019d39ce63dc1c6,0x85,0x87,0xde319bc7041601486a4de319bc73013860e80eb2f1acb8e981e3bd6b778d884b02b8c83bc73779bc632e3ca06430b40b818cb83a8bb05c0bc3bd6b2e3c61226f18cb9bc632e35c1b00ac2c46f18cb9bc6b99718e63c21a46f18d66f18e635a1ea0aa29a6f18e6ef9ce6ef18e63be1dfcf18e63d01d52f1ac6ef5ad635822a0a826eef1ac638e21aef5ad65d6b58530949758d739ad6,0x89,0x581201285f5f70be37c11204033c17d74f0bf2f5af38dd84c80f8c94bd6b2e3881303a807a41a57d1fdd0fcbd6b2e37018e03c3021903043f840d2f5acb8e1860cbd7dcbe75acbcbd6b2e36c1b603a2cb2f5acb85fa7f72f9d6b2e5d6b2e57d7dd636a1f00382a057d68f5804801ff003003fe8f47e7ee8fef9fbafb802801ffee8fee3d21d6b11811e5ad604a27223c27617e9eb58fa033675ad65d6b58f9053975ad63e219e8f47ad63de1c8,0x8b,0x8d,0x18178181bc63378e084500c8cf9bc6337cbd6b2e3781340303272f1acb8eb81f15f1f7e78c300314632e0602fa18a2fe6f18cb8f283be75acb9bc632e3741b802e2cc6f18cb9bc632f9c6b2e5c632e3c41a66f18d1e3721f202c2a26f18d66f18d1f9fba3fbe718fb8f007873c63ee3d41d92f5ad637023e02a27b2f1ac638623217c6b1e75ad65d6b58ef0829758d68f47ad6,0x8f,0x18248250c20821463378250ce0428ce89f183f9e38413601c32827c60f2e3b808027c60fe79bc632e38219401a3086f18cb9bc632e39816c00e007fc1f4f2e6f18cb8e006f0060b406f8b48fe9021bc632e38c1b26f18cb8e586a9bc60f2e5c632e6f18c9e37e1f60162a66f18c9e38a1ec6f18c9e3941e427c1e0f27f3c632793c63278f587685f183c637c24201427e17c74f185f1d3c639221e00c007fc1e002007fc1e5e9f4fa797078c1e008007fc1e004007fc1e,0x91,0x93,0x7e3ea3ec3ba11602839e3b810e09e39c3b61920243063ae1860622fc3a616e0ec2ee3b41ba0222ce3ac1b40562c63a41ac0dc2be3181a215a2b63b21f40202a43aa1ee05229c41c3fe3a21e60d42943161dc15428c2e21ce1a028a4223fc3b024001e27c3a823804c27441a4003a02220ca26631420814a2502e020219a24a2b41fc1c4244,0x95]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good1b2 : groupHybrid target anchors11246 pool v2 projectionMetas v1b2.toList h1b2=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b0 : List Nat := [0xaf7be000007fc00400ff974bd4010007fc01a007fc,0x7bc2cf21df03e,0x167ae7e9dde27ce,0x7bc8fb1f003003fecfcaff5677c6,0xa7227a73fce4012007fc00800ff805001ff67ae7e,0x3cfeb33d8f92cf63e4a9f4f9e322fe300f003fe,0xc82,0x197062ea3e2,0x9f4fbbf600a007fd27ee7c6016007fca7fb12fe,0x9eac0fa4fd7af00c003feb1fc6,0x97,0x99,0x9b,0x9d,0x9f,0x1ef91f9ef57fbe0fccbce7357fbe730bf36be2980f03f398c7398aff3ce7efcf39ce6,0xa1,0xa3,0x4cbc9f9c9f9fbe4fce4ffbd5f5e4ffbe0fcd5f393f30bf3078a683c1f39cc60fcf39fbf3ce739ce6,0x11c3acb0eb2e5c3ac6bdaf7b2db2b24444,0x1c3c70e1e3c70f1c3c7c7fbf1fef0f1c0fc703e29d1c0f8c71e79f3c79e7cf1e3fbe71e6,0xa5,0xa7,0xa9,0xab,0x11c3acb6f43d4f77b2d77b34e72d54,0x143c70edeadbd6eb6f5bd4f77b2db55de72d54,0xb0f1c3af6b6f6fdad3af645b2db2b2bcf54,0xad,0xaf,0xb1,0xb3]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b0 : groupHybrid target anchors11246 pool v3 projectionMetas v2b0.toList h2b0=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b1 : List Nat := [0x11c3d0eb6fb567ddda4425423f6ed42b2221b34e755a,0xb5,0xb7,0xb9,0xbb,0xbd,0x1ef57fbe0fce7357ce60f98e60f9fbe617c0fce73078a983c1f398c73983f3ce7efcf39ce6,0xbf,0xc1,0xc3,0xc5,0xc7,0xc9,0xcb,0xcd,0xcf,0xd1,0x127e7357e3e7df1f3c7f757d7c7f7c7cd5f393e17c0fce730783c1f39cc60fcf39fbebce739ce6,0xd3,0xd5,0x7e7f3c391f478747874787e7edf47878e1d6b072c872b076df07078e1c3870e1c38,0x1cf0e1f9e1f9e1f9e1f9e1d61e3acfcaf3df21cbdf072bcaf078e1c3870e0d8,0x1d1e347a3f9e1f9fb7d1f1e3870e8f23d6b21cac1db7c1c1e3870e1c38,0x77f6fc9f3be7bfe7abf9fcfe7edf0a7f5abc3c9f9acfcabc9efcaf2bcaf2be6af57abd5e102,0x74791f4787e78d1e27d71d5e1c3a3c1f9eb0700e80d2c872b0709fc3e1e3870e1c3870e070e170026,0x2bf9e7bfe79dfe7cd5fcf0a7f0eaf0eef2bcb3f2af27bf2bd39abe6178af57abd5e184,0x2c3c70e1c3870eb0e2d5e03c02eb0e2d5e03e02cb0e2c8f81000aac8fd70e09f581080a2c1eba78a12d6,0xa7d5f77eb8a7fdbe57dbe57dbf87d5e4e1f91f987d2fbb7f1cfe1c4f827c4fcbf0fe1fc3f87c1f87f0f987f0fe1fc3e,0x15d5f77eb8df23e0a7f46fe1d1e23d6b23e4ac8fac8f8b23eb23f5f6f95c8fedfdbeb07ad62d6,0xa7eef875cd5e49f980c00e4d5f35792a7ca7e71f83eaf9939bb7f98e62bf9f1f9ce64c1e2a739ce6,0x15d5e1d6af93e49f98a7f93f35793393f5d5e5793fc7e0fcd5e4d5f393f399307ce6,0xd7]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b1 : groupHybrid target anchors11246 pool v3 projectionMetas v2b1.toList h2b1=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b2 : List Nat := [0x70e1c3875878f5c5e0df0f1c4edf8e0320371c3c70f32470f1c3c7dbea7c829fc3c78e4703f1e3c78e,0x1da7e1e870e1ebdf0ef7c3870e0da,0x1f9e1da7e1e870e0dfeafbdf0ef7c3d5fabe1e870e0dc,0x7478769f870f1c3b7ab0eb0f57c387a1c3ac3d5f0e1c3870e0ee,0x747b4fc391f69f8769fd5f69f87c7bdf0eb0edeac3d5f0e1e870eb0e1c3870e10e,0xdda7ed3f6f8fe7b769fb769fe1f69fb70edd6dcdedd6b175372cdd87cdcdcb72,0x1d1e1da7f69fede1f1ef7c3ac3ac3b75d5f0e1e3ac3870eb0e1c3870e14e,0x7478769f87c7bdf0e1d1e1cd7eb0e048b0eb0f687ab0eb0e1c3a1f0e1c3870e172,0x70f1c3ac3d0eb6e04b43adb8132c3af604eb6f43ee814d4f76242,0x14387b1c3d0f43ac3adbd0f53ddecb6d5b34e72d54,0x1c3d0eded0eb0eb6f43d4e24377bb9d6,0x157e92ff6fdabf6afe1fb0ff87f0f9dfa1eeee1fb7d3bf77b2fbb68,0x1ec70eb0eb0e6f6e1dbadbadb81461f0eb4eb4e5d6ddb8,0x1ec70f439bdb876eb0eb6f43d4f76ddb92,0x55fbdc8f9bdb876eb23f48fd6eb23eb6eb6f6afc0fd17f53dd925a,0x70e1e3c70e1e3f70f1c3c70f1c3c7c792ff1e4bf0e07c0fc79c703f1c1e0f1c79e7cf1e79f3c78ea7e71e6,0x2c3875c70eb0eb0e6f6eb0eb6e05047d6ddbe1f0f87c8fad3ad3972daf2d9f3ad6b5e72c3201e2ef2c,0x16afa9fbbf43bbc77f6afeebbddf59fbdaec5db56cd2ef3bd54,0x16afd7bbf6afd6ec7dbb1f6f43d4e9f6bb176d54f34d3cc7d54,0xd9,0xdb,0xdd,0xdf,0xe1,0x16afd757d76eb3f57f9f6eaf57d4f53da5d425623d69f4f34b0fd554,0x50f1c3d76edec76f7753da5d425823b4f55cf9d554,0x143c70e6f6f1dbd4f53da4425a2374f56734dcf54,0xe3,0xe5,0xe7,0xe9,0x5abf5d5fe7db9dfb7753da4425c2354f553cd2c3f55a]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b2 : groupHybrid target anchors11246 pool v3 projectionMetas v2b2.toList h2b2=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b3 : List Nat := [0xeb,0xed,0xef,0xf1,0xf3,0x1ef9bfef83f39be0f981b4eefe7983e7ef985f6bf39ce60f07ce62962873078c739ce60fcf398b80804e7efcf398c88784e6,0xf5,0xf7,0x1ba9edb683d6326f381e81d6e9b4e07e073ba6d382081c27a15fd82101ba74fb13e37a,0xf9,0xfb,0xfd,0x2db9bf6ddbef7dc8f8c8b23e09008ab6e2f9e094088b6e2f9e098087cf6e09fd82681bacaf8cf2d6,0xff,0x101,0x103,0x2db9bdbb76eddbd757ac8b57828827adb8b578298272db8be782a021d76e6d382a81c2f630c9d6,0x105,0x107,0x109,0x10b,0x10d,0x6efe4ff7c7cf1f8f9cf1fdd5fdf1fdf1f357c9f93e17cc7f3983c1f39cc1f31ce60fcf398b887f7bf3ce739ce6,0x10f,0x111,0x2db9bdbb76eddbd757ac8b5782d82c2db8b5782f0272db8be782f8222c8fd76e6d383001caf62d4,0x113,0x115,0xb0f1c3870e1c3ac38b5783202c2c38b57833027ac38b23e0ce08ab23f5c39bce0d00740f5af6288,0xd3f0e1da7e1f1ef7c38792fedebdf0e1e870e1c38df0e1c3870e124,0x34fdbb769fe3f9edda7edc3b78edd6dcdeddb971704e84e537473740fcdcdcb72,0x769f87c7bdf0e1ec7e37c3b78e1e870f1c3854870f0f0e1c3870e15a]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b3 : groupHybrid target anchors11246 pool v3 projectionMetas v2b3.toList h2b3=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b4 : List Nat := [0x1ed0f1c3bdf57d0f1c3c76f53d4f40f897d3d59f3db9d554,0x70f1c39bdbd0e6f6e0d31c39bdb835476e77edddd890da,0x7b43c70f43c70f1dbddd4f697509788cd3d59cd39d554,0x1e3c70e1db9bdbf9f6f1dbc76e0d6000007fdb7f1d3c74f1e3972e260ddb8,0x1e876e6f6f5bc70f1dbd6f7753daddb92,0x1c3c70eded0f1c3c76f53890d4f6d3ee7b9eda,0x7b43c70f43c70f1dbd4f53d03e2334fa7db9f3db9cbdb6da,0x70e1e3c70f1c3c70f1f1f5d5f40f8a14707c703e0f1d79e7cf1e79f3c78f5e75e6,0x78f1c3c70f1c3877bf1c39bdb8359bdbb6fe3b76e002007fdb7f1d3c74f1e397170be0bdb0fde7d9f3c75c78f9d1c3241de008007fde7c,0x16afd7bbf8bf81fdabf4fa3dfd67e3dad6797553d54f34aafd554,0x16aff757dabf5bf9f6fe7db8f6b5397553d54f34ed554,0x70e1e3c70f1c3fbe47f1c3c70f1c3c76dfc8fe47fef9bf1c0f81f07ce3c703e5bf1d79e7cf1e79f3c78fef9fbe6,0x11c3acacacb970e34eb2b2f6bdecac912d6443601c0,0x117,0x119,0x11b,0x11d,0x11f,0x121,0x71874be1d1e1c38727ac3dbcbc70e1d6b0e1c3a1f0e1c3870e188,0x1ef3df959727972e32e1edfb2e5cb8cbdbd6f1ecb8,0x123,0x5723eb2b2eb2eb2eb2e5c9e34e5cec5ac7b2db2b24444,0x4f69f93e27e1c3907f27daaf7785e0df2793c9f0f27870f57c9e18a,0x18eafb49e5cb93e9dfa5e97a5cb8df4c62a65e8,0x125,0x4cabed757d2f4b972e5cbd27d2e32eaff74cc65d45cd24444,0x470f1c3970e5c3972e5c38cba9d571c65c5c224444,0x50f1c3adbadbd6e9e9f6acecb5ddde72d54,0x4d5f36eb3f57cdbb7be7dbabd5e37ca7ddb697509888c5a7da7b0fd554,0x470f1c3adbadbdbf69e9ebab112f7b2b2bcf54,0x15d5f5dbbbd5e36eef6eaf578df27ddb69109908bda7d3cd35df54]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b4 : groupHybrid target anchors11246 pool v3 projectionMetas v2b4.toList h2b4=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b5 : List Nat := [0x127,0x129,0x12b,0x12d,0x12f,0x49f9c9f9fbe4fce4ffbd5f5e4ffbe0fcd5e0f9838ce4fce617c739cdde0f1ce629e22c0f07ce73183f3ce7efcf39ce6,0x131,0x133,0x135,0x137,0x139,0x13b,0x13d,0x13f,0x141,0x143,0x143c70eb6f1e9ebdd5910998862f62d56ed42e41f56e750c9875db5436219e,0x3769fe3f9e4f0e8fd7a5f4bedd66faddb872c5c8f5acdd87cdcdcb72,0x145,0x147,0x149,0x14b,0x1c3c70e4f63eded0f1c3c76f6afc7a7d3e9bd3e7b9e3da,0x70f1c3e3fbf7c7c70f1f1f5f1f5c381f03f1e383c1f1e3f71f707e7cf1e79f3c78f5e71e6,0x1bdbb76fdd1eb47d76ed7d77624377b5ed69d75d6,0x470f1c393d6b6e1d66f6eb6e47d6ddbe1f0f87c8fa703eb5ac5cb2d3e72eb5ad79cb0ca07561f2c,0x14d,0x63f9e4fabf07dc7e3bf71f8efda7ee3f48fedddf57c6faddbb71df971704f04d41f9f9f370efcdcdcb72,0x14f,0x151,0x3737cdbcd5eef579bc77eef6eaf579bce7f66f5cc75c7e2689c9bca71bcef1bc,0x153]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b5 : groupHybrid target anchors11246 pool v3 projectionMetas v2b5.toList h2b5=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b6 : List Nat := [0x155,0x157,0x135793c6fcdbcd5eef6f6afabd5e37e9e9f3da6f71f885cc74f2f6bbcbdb6da,0xaf57927f93eafefdf1fdd5fdf1f357c9f93f4622bdc60fcf5e3f70783f3ce7c7f3d78f39ce6,0x1d7c6fcd5f357f1f1dfabd5e7bf1dfbbc77eef20feaf57bbd5e37c00c007fd67f37782b4ef77945fd67eef77bbdde,0xddbcd5fde4f9be0fabd5f36f4624346e7ebce69e69ebce6,0x773df93fb7e6f6eef3df8db9bdbbbddeddbbbc83f9efcf7eef77f6fc9f3f9f5bbcde5c5c2fa2f26f1b0fcbf9f5bbddeef3bc32a1d2ef3bc,0x159,0x2bd5ea7e07e47d7357abd735792fe4f83dcd5eafaa7cf7e47d7c7e0fabe6af57ce68dfe677e7c7e74621aaf57ce6,0x2bd5fef91f972fbbf93e49fe4f972fef57fbe0fccbcd5f27e4f97181f1ce65bf1d78fbbf0be3cf39fbf3d78f39ce6,0x5717d76f5db972e5cbd23e275a9d69717574e224444,0x143c70f5badbeeb3f3dabdd59109a8855bb50ad8845de755a,0x1357cdbb7be7db9dfa37f69f76d379109b084d3d569ec3f55a,0x15b,0x15d,0x15f,0x161,0x163,0x165,0x167,0x143d0f1c3adb8dfcebdd59109b87e5bb50ae07daf630d6e750cb073db5436419a,0x1c3c70e1d6de84350ede842d6f1c3c76f5bbdfce1c3e7b4fa6f4f9e3da,0x169,0x5abfdd5eafb6fc3f55f87f0f9dfb55e9e9f6eca916d56fde1f5bd54,0x148fd723f5dbac8fb7ab6f5badbc0fd17f5ba7a7dbb2bb2db52f74f2d54,0x1c3d0e1defb7a11543b7a10b1c3c76f43bdfd870fbb5ef9bd3e7a,0x16b,0x4d5f35791fac7c77e77d55e32a9f769153d5367cbcc7d54,0x4d5f5d36eded6fe7db8caa7dda5d54f54d3ed554,0x16d,0x471bdbb7a6f6ede80002736a736801bc600,0x376eddbb737b737b2fcb8cbfdbe6f2e1bdb9bc86f6e6f6f13f244fdbd4e202ddbb76e9cde]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b6 : groupHybrid target anchors11246 pool v3 projectionMetas v2b6.toList h2b6=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b7 : List Nat := [0x50f1c3ac3adbeeb3f3dab559109c07cdbb50ae87becd373da,0xef27d7578498dbbbdb8ec3c9f76d3df9109c87c53d54f34d77da,0x16f,0x171,0x173,0x3769fe3f9e4f4bedd2fa5f27dbf3a9f8eddb93cde27e4413e132dcd7f4dc14612eb375bededd6ddb92,0xefda7f8fe784b3769fc2fc9f31df93c6f6eddbb789f9105004c53779f374e6dddeddb92,0x175,0xb6e6f6eddbb76fdc8fac8b23e1420c4b6e2c8f85202cadb8be78528235bdb9b4e14c076ba6d630a05eb4e,0xa7db8efcdf13fc3e12fd2fdbc96f2e6f4be5bd2f9bf0f88dfededede5bedfe3fb7dbe936fd7dbede,0x1bdbb7379bdb9dc8facb895fd2fb74788f5ac8fadb8b23e6f45f96f6e97d17eba4ad6b4e,0xa7e07edd7324cba1f83e145323e41f983c84dcc77ea7da3f8de64e68dfe677e71bf9ce9331ce6,0x6f6edd732e7783ede0f907e695fe0f9bdb86f93f3c3e4dbce4fce9339cc6,0x376eddbb75b737b2fcb8cbfdbe6f2e1bdbcc86f6e6f6ea7c913f6e6f129cde1e812a6fa6fa6f4e,0x177,0x179,0x17b,0x50f43c70eb6e37f3aed59109d07755ed42bc1d957b50b98742d38cf5b54366194,0x70f1c3c70ede3c70e1d71c3c76e004007fdb7ef7f3870f9ed1f8f9e39bd3da,0x17d,0x1e7ec3ffbe47f6f279bddf87f0fd77fb7dbf69e9eefbb1645b5bdb36f26f4f54,0x1e7c8ff723e6f6eb23eb6eb6eb6f23f45f857f23e9e9ec7ea71645b2c03f2b2b4f54,0x70f1c3d0eded0e1e1f1c3c76f43bdfce1c3db5efe7a6f4e,0x17f,0xef27d729f8550ddeef68ff0dfc5eef778ca9f3d59101f2cabf2c7c8c754,0x77579bc8dbf9f6eef6e32a7b6d579109d876d3d5af348c754,0x181,0x4726f6e6f6e124a72ea7559111122210612a6f4e44,0x183,0x185,0x187,0x189]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b7 : groupHybrid target anchors11246 pool v3 projectionMetas v2b7.toList h2b7=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b8 : List Nat := [0x18b,0x18d,0x18f,0x191,0x1bbf93e4bf93fef57fbe4fce7357c9f93e39fbe617e73983e73983ebce727e60f9ce7ef8f398c6,0x193,0x195,0x197,0x143c70eb6ef7e87b439109e06fd6fb50af86b56fb50ba0675de750cb8666f637a,0x199,0x1d1e47d1e1e27e8f47dbd5f1c38747c77be1c3a3c1c17eb0706e868ac872b075bedf5627a,0x19b,0x19d,0x19f,0x470f1c3870eb0eb0eb0eb0eb2793c393c3acb0e06e2c8fe75ec6,0x70f1c3c70f48fb7b43c70f1db93d0fbdfb6d0f5bd3e8b067b9e9df3be,0x143c70eb0f43adb93c3ee81fb687a1d61b75becd22c21a7b34e734ef6,0x70f1c3c70fdc3c70f1f1fefc7ddf0e0fcf1def81fcf1e38a407303ebc78e1e71f1e0f9c798b106a679c79e78f1e383c1e,0x143c70eb0f43adbd5f0fba07eda1ed0fb5da2c21bade8696edb9d76ef6,0x11c3c70eb0eb0e1d6cbf6eb6e47d6ddb93c3ebf3e1f23ecfceb5872c3910bf06f2dbebcb0c106ae72b2b6f9cb0cc065ebf5e,0x77eda0f13fbb7eeebede1f77624377bb7eedfcfdebf6,0x1a1,0x2be27e7bf89ff5f3bf357abe27f35785e2be27e77c29fc3abc3bbcaf2cfcabc9efcaf4e75de27c,0x1a3,0x1a5,0x1a7,0x4f57f6ff1f37fbbbc9eef57abddfdd5eaffbeef9bf37e1eef1df93e1eef57abd5f83f3bd5eaf5781b2ef778c6,0x3bc9f35785e5abeef6e4f878ec3ea7b6abdde1b14f34d3cd2ef348c6,0x57abc1bfabf1fde6af57f79abd5fdfbabf1fdfbe3e6af5783e617caf98722be60f8f5e38e73983e739f1f8f5e383c1e,0xef27f73df85ebbc83f8db9bdbbbddeddb93e1e377bbddf0f275f9f5bbcf7e442fe1b4c3f3bcc3f3e7cbbdbbbcef0cc8648c6,0x168e83e617d318e8e74624347b7cef8e7cf1f3cef8c6,0x1a9]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b8 : groupHybrid target anchors11246 pool v3 projectionMetas v2b8.toList h2b8=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b9 : List Nat := [0xaf57ccbfbd5fef93e5cb85f9cd5ed7e617f39979abd5e07e73980905e24fe3fbe38e7398e739fbe3fbe385f0be,0x7726af92cfa77eb3d6a75a49109f86b91089133d9e,0x1ab,0x1ad,0x1af,0x1b1,0x1b3,0x1b5,0x127e727e7ef93f393fef57d793fef93f39cd5f393e39fbe732e17e7398a48644d5e0f9ce62a018f343e0f8f398aa86349f9ce4f83e7398ba859cfdfef8f398cd0584e6,0x1b7,0x1b9,0x1bb,0x1bd,0x1bf,0x1c1,0x1c3,0x1c5,0x1c7,0x1c9,0x470f1f1f387cc383e607e739cc383e7398a9061878e39ce79e739e78f39ce6,0x1cb,0x1cd,0x1ec70f43d0eb0eb6f43a7b41eecb6d5b34e72d54,0x1cf,0x1d1,0x1d3,0x1dd5fdf1f35783e65e6184af985e4f1e0f8f398ab05d4f1e39ce62c616b3c783e7398bb0594f1fef8f398cd857ce6,0x1d5,0x1d7,0x1d9,0x7be47e7bd5fef93f32e17e7357b5f9870ce65e735781f9ce62a2179343e0f8f398ab85bce4f8e7398b205a4e4f8afe7398bb858cfdfef8f398ce0574e6,0x1db]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b9 : groupHybrid target anchors11246 pool v3 projectionMetas v2b9.toList h2b9=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b10 : List Nat := [0x29fdbf6afbbf0fb3ed6ea916d5b34bbcef33edbbaef77da,0xf7ed7bf5d5f5efe77bf9e3bdfb5efa7b417355e5d428016d4f56734e755abf68,0x5abf5d5e008007fe07e3aacfb444af57d3d40e61a14f34cbc73f5a77ed3ed3e806801ff59fda,0x1dd,0x1df,0x1e1,0x1e3,0x1e5,0x1e7,0x1e9,0x1eb,0x1ed,0x1ef,0x1f1,0x1f3,0x1f5,0x1f7,0x1f9,0x1fb,0x1fd,0x19defe75a7ab27aa454f2d9caca75af3e75e758c82d6ef58,0x677bf9def8eb3a75c7116d6f6731cda9e3b0fe3e78f9e38c95b2fd3e004001ff8e,0x675e75a75a7abce9cd91272d9caca75af3ebd79d79d6328b5e1f58,0x1c7cf7e9fcfbbcf7e31de9d7a7f64433bc03f3e7cda9ddec3f8eeff3ec3f778cada7bf3dfbbdde3bd6,0x19d79d79d6cfabce9cd916bcb672b207d6bcf9d79d63316ebf3a75987d6,0xef20ffc7cf7e1ec31de9d7a7f645b3bc03f3e7cda9ddec3f77bbfcfb0fdde33368dde3778ef8e,0x1ff,0x201,0x203,0x205,0x207,0x209]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b10 : groupHybrid target anchors11246 pool v3 projectionMetas v2b10.toList h2b10=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b11 : List Nat := [0x20b,0x20d,0x20f,0x211,0x213,0x215,0x217,0x219,0x21b,0x16db775381f8e481f8e9e929ed37845a7a9ea78e9cde9caf3a7a9e3a737a7378d39df369dfbcf4e,0x6defe758ed3ba77b2db527b776e7599eee8,0x677bf9defa7a738ed25d54f55ce9ed3edb9e99ed3e94fa,0x675e75ee8eddec77b2db527b77bb6e7599eee8,0xf59fa7b45fea71a78edd9752755da7b4fb680fe8c3fb6d3e94fa,0x675e758eddec7645b501fb776e7a67bcfdee9ba,0x3d67e9c69e3b76454f5597a7b4fb680fe8c3fbcfa7b3e94fa,0x21d,0x21f,0x221,0x223,0x225,0x227,0x229,0x3ee0f98dde07e7318a504103e731f78f3983e73ce3ee39c798e63ee39ce6,0x22b,0x22d,0xf7f79d7b5a7b4bbb2db56d7ba4e75ebd667bb5ee8,0x22f,0x231,0x233,0x5f98fb83e6ef9840f798fb83e3cc62b00f13983e73ce0f98c203a8fb8e71e707c633a0e8398fbce639ce707c63760e4,0x235]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b11 : groupHybrid target anchors11246 pool v3 projectionMetas v2b11.toList h2b11=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b12 : List Nat := [0x237,0x239,0x23b,0xcb85f983e65e60f9cc60f8f31ce60f9cf38dde39c798e6377ce639ce6,0x23d,0x3d69ed6eb7b2c9eddeedbba4eed3d66beebeed7ba5a,0x47a7d3e383e3c7b4f8e9ed03bd3e39750a083b53c6fd3e94f8f4fa481f8e07e807ed3e8,0x14f06fe0f59f8ea9e9ed175597a7b6d3e934fbba30feb0fed3e94fa,0x23f,0x241,0x1f9cc60f9cc60f8f3185f983e73983e73ce3778e71e6398dde83f18de4c7398c6,0x243,0x245,0x247,0x249,0x24b,0x24d,0x24f,0x251,0x253,0x255,0x3ab0cb635af6b5ed66d7b593b597592175975ed6485d6,0x257,0x3ab4e33635af6b5ec8d66d7b593b592175975ed6485d6,0x259,0x25b,0x25d,0x6ea7b6da0f58c9b58a2031ee9b58b502d6e9b58c302827a15f58cf023a75ee827f637a078,0x16da0db6ed7b59bf7bbbbb58c3a75a7a57d633e9d627f6,0x5b68375a07e3d3e3a7ae7cde2d86f4e9ea7ae7cde3169ea7ae7cde3449cde77e874e37e,0x7e8eb7683d6359ba6e807d601f5ee89fdee827f637a,0x27a3adda0f58c9b58a2830eeed7ba6d62d5ba27a275ee8]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b12 : groupHybrid target anchors11246 pool v3 projectionMetas v2b12.toList h2b12=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b13 : List Nat := [0x2751d4f683c53f8cb8e7cde9e89e803001ff89f8c49bd384407ea7a9c89fcfa737b3c877ec4fe27e,0x2751d4f683c53f8cb89e89e8c49bd384487fa7a9c89fcfa737edf4ecf21dfa,0x5bba9eed77ba24c0fae3a6eb8a301aee9bae2d6069ba6eb8c4019a7a15f378d00192737eeedfdee9b7f637a,0x3ad9dfbb5d83eb8c9ba6e9abfb79abfb7edf3bfbddda5fdef697f7bdf3f7bdf3f7bdeafc4fef6,0x25f,0xe93a78e9d69cbd81f58c89d62758e7d631205ee7cdeb4f56e7d6b4e6bf5ac0fa75ad3a75a75ad38d4052eafd678fd657d6,0x27aef4e9f0f893fc3e3261f4e0de23832e9d6f89d6f92e7cdf6f379bd3a737a7378d4ac7f4eb4e,0x27a77ba9eecdd83d6326e8d7ebaf757b5af7b5af7b5af69e89d6b4fba6d75d6,0x3b769eda0fc3e326e88dfedf6df6fda7b789edfb7f776,0x16a7a9ea75da7a2520fae3235fae28e05c9eb5fafba35fae2d403fae9e8d7eb8c5016a7a39f378d08162737cbe9b7d38df015d7ae,0xe93a7bb5d83d63235faf5d3d5ed6bded6bdee9b5af69e89d6b4e9d7ba6ebd7ae,0x261,0x263,0x9eadf4e9d635f58c8d7ebad7af5a7592e7d6b5a75a75be57ae,0x3b53a7a483d6358d7ebd5ed6d7d756bda7589d7ba57ae,0x265,0x267,0xeadf18d7d6b5ad63593b58c8358d6320d6,0x5a9eb77632e03e3a7a27ad7cde3129ea7227a9cdecf219fa,0x16a7addd8e80f8e2900260f8ecfa33e8c481facf233eb3d4fb3c8cfa1d9e,0x269,0x9f4fdd8c8a7c60e02403a63f53e2a8358a7c60fa222cf5be4bbc707c6353ea7c6354ef194fc6,0x168edd8c80f9b3e936783f089599df9b3dde33e759fb7d9e,0x26b,0x26d,0x9edebd8c8d7ebbbebb5f9a7b793463378dde0c6,0x48edd8e80f9d9b5f9d9a7a279b3e867e6,0x26f,0xd6faf76617e693f9979cc6d7e7318cb922bf98c9ef98e6398c8318600710dde398e6,0x16db77538cb807e3a7a27a3126f4e1162029ea7a9c89ea78e9cdecf21dfa,0x5b68c863f53e9c8a7d9e100228cfa312a7d9e11a2069c8cf53e59fcf67b3d9e,0xb5c78e3201f9a720c4cd3847082137a79ccde3569c8]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b13 : groupHybrid target anchors11246 pool v3 projectionMetas v2b13.toList h2b13=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b14 : List Nat := [0x5b68c01f8e30378458c0e630,0x16da32e35faf6b8c4d74e11e20a9eba72279a737a7219fa,0x2d71e3978e07e3c703e32e0e38c4b2fc612020c38e320c61561e438e38e38e365f8c838fef8e,0x271,0x6189159817e73180924ffdf3078cbcc639cc639cc1e3778e7ef98e60c6ef1d97f18e739c1f18b7f18c6,0x1ad3891c78ebdc74e32e9e39bd3a78e9e386f4f4de9e3b9f378d1a737a737a7378d6002801ff8e012007fd97e,0x53d4e2496ddd4e9e926f4f4de9eb9f378c62737a7a9e3a7379dfa77cde,0x273,0xcabfb61892a4ff4f97b796fd8cb8ede3b78ede3c3e3b7a8fc60c6bddbedf73f18c6,0x16b7538935dd4e32e99fc53f99fa9ec4fcef9dfa9e802801ffa9fcf803801ff89f877cefedf3bf4eff3cefdcfee7e,0xb593d4e24eb4f538cb81f8e9e39bd3a78e9e386f4e9e3b9f378d1c737a737a7378d6a78e,0x169dd4e251775381f8e9e926f4e9eb9f378c6537a7a9e3a737a7a,0x5a4f53894d4f53d1f1be1bd3b9f37d37d1f1be6f4e9ea7a9cde9ea7f3e9cde9cdecf29e8df1be,0x3d7b8f4f5c78eb5831ad7b5ac7b58b682ded6bded631a0a207d6bae6bf58d202401f5ed75d61f638007a,0x2d607e381f8f1e3836478f1e383e3cc60fae2dc0b80f8f3ce0fae31c0a407e381f8f1e743fee34a09207fb83fb83e3ce61c1e38207c,0x2d607e381f8e07e3c78e07e3cc1f1e3b5f8f31a4ffb8b782b81f8f3ce07e381f8f1e607fba4ffb83e3ce6,0x61fc3e17fdfef49f98feba9f0785ff7a67f25fce60faf3183eb83fbcf3a4ff4fa4ffdf1f3a4fc97e0f25f9a7f078e14707ce60f079a7f07a4fd27e,0x275,0x277,0x2d617ebd76bed7ebd707d1fef3985ff783fbc7ef31f70783ebcf383fba4febb5fef1f3b5fee93fee0fae0faf3983fbfbfde,0xbf3981f9ce7331fd78e0f4cff5c97e0f07ce6325f83c1e84381f398c1f39e707ce60f31fd78f5df7f5fdf5df7e87dafb5f983e73983c1e17c69fc1e83f07a0fc1efbf6be,0x279,0x27b,0x5f9cc1f39ce6d7fbc707927f07cfbcc7dc1e0fee0f9cf383fbb5fef1f3befebb5feefbfee0f9ce60f983c97e,0x4e7398114e617fdf1c1e07e731eefc2f83f88985f985f9cf385fef1f385fae17d0fcc2fce617c2f85f985f0be,0x27d,0x27f,0x4e739811ce617fdf1c0f85ff7cf77f31eefc2f927f0be17f77e17e73ced7f77e17fdf1f3fbfde17eb85fddf85f43e07e73985f0be1821c617e617e617f77e,0x7e3cc0fc78f1e3c78f1c0fc703f1c0fb5faf31d1f8e07e3cf3b2fc0f84608101f8e07e381f8f1f381f8e07e381f65f98ffbce699fc1bfa67f8e,0x478f1e3815478f1e3c703f1c0f85faf3185ff781f8f3ce87c0f84888381f8e07e3c7ce17c0f85607981f8e07e381f8e07d0f85ff7ce7eff785fedf85f8e,0x281,0x2763e9d635f58d6d7eb8bd8b28bda3d69d6e7d62d3ad69d66bd75ebebd6]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b14 : groupHybrid target anchors11246 pool v3 projectionMetas v2b14.toList h2b14=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b15 : List Nat := [0x9fcf8cbb5fae5718b315c6d7cde9eb831b9f1cc633783778eb8c6,0x9ea7a03d7b5b5fae4af62ce4af7b5b5f592bdaf6b5a75a759bb5ebed6,0x9e8afe83e64cd38b41334ed7e64cd3b5f99bd3ce69e69e61dfa77e677e6,0xb3f01fd1f58d7eb8bd8b48bdb5f58bded6b5ed7b5ebd68f5af4febd7bb7ed75ebed6,0x6cdee7d66faeb582d2d604a0f5ed6bded62da0c9b5af7b58c7829a3d6b4f5634c0948f5ed75d6df638607e,0x15ebaf75daf8b55797d76bebdcc6e7cdf39b5fae0f14fed7ebb5faed7cded7cdee7d2bfd7aed7ebb5faecf53e,0x278e9d71e3ad607d63201f58c0032a7588f58c182eaf3a758e7d63120ace7d6e7d69d639f58d4025ac0fad7abf5827d38e202078fd6,0xcff3eef4e00e007ff0f893fc3e320cba7f3e6bf0fa7c3e4e1fc3e016007ff5e9f0f897f5e35206297f5fafd7dbede01c007ff5ebd79afd7f8ff5fafd7ebf5e38c,0x9fcfb1f4e9d624fd6358e7cdeb58b4faf5a75acbad87e9d6e7d69d625f5af5e9d6b5a763e6bd671fd8febd6,0x33f17eb03e320cbbeff8f8c08d671f183e0bd0ddecf63e48dde18fc6354022a3f1806001ff18c739bbc60c601c007fc707c645fc6318c638e,0x27f3eb4e32e3eff8fbbcde1bc6e7cde9fcfacba7378dde39f1b9f18c6337ce637783778f8f8c6,0xb5c78eb4f1d38cb807e3a72e278e32f39bd38418bc278e9e3a7239f378d5808278ee7cde3589e3b9f378d6b2fc0f9bcdecf2003801ff8e014007fd97e,0x6cdee7d66fae0d2b58282d604c0f5ed6bded631a0cdb5af7b58c782f39f5b9f5ad3d58d70266d75d6df638a082,0x57cdee7d66f378352d608eb5813d0fd66bf5ad39afd63480cee7d6b4f5634c0be0bf5b9f5ad3d58d702a15f595f5b72be390084,0xcf77dcff0f893fc3e3232e6bf0f94ff5e6f5e3686f5f87f0ff3f5e25ff5e6f7bda5fd7a5fd7ebfc7fe3fd78e36f6,0xcf1efe3232efbfe3e36e71f18db0dde0c636a0c6b1fc7c7f8ff3c7cf1831a8fc6006007fc707c707c638df807801ff18e38c6,0x1cfdf3f61a7f97dcff7cfdedfd93be78dc6cbef9fb7f64ef5fbd79aff7cfdef7cfdf8ff6,0x73e9e2dfcba0fc57e37477f9fcfa79277f9e373b2e77f9fb7ceff3cef9231edf3be77f9e2dfc7cf33e31f3c57e45fc57e,0x283,0x9f3be1f677cefef6079bd8148713e1f7be787d8e00346dfdef9edf63860c01f7be7b7d8e282a87d89fdb713e39009a27f6,0x1bded2f9dfdbe37bbdbe77f6fec4f8e0fedf3be31d97f3be69fddbf8e128fc68dff6fedf3bfb7cefedf33fb7cefedf3be53f86feb1febbf807001ff46fe,0x285,0x287,0x289,0x28b,0x28d,0x28f,0x291,0x113f5791f5cd5eafa0f4030b23e47d7357abeac8f91fab57abef1f5791f5ac8f91f5ac8f91f5ac8f91f583e03ccd5eaf57c4fc8f82fc8fbbd5eaf57d57abd5e7bf23e7bf23f3aaf57ae91f23eb5abd5f6abd5eb591f23eaf57abd5e,0x6f6edcdecbf2e04600cb2fcb86f6e1bdb806f6e1bdb80113f6e44fdb80006faddb9beb76e0001ea1060,0x293,0x295]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b15 : groupHybrid target anchors11246 pool v3 projectionMetas v2b15.toList h2b15=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h2b16 : List Nat := [0x76fe6fe3fbcd5eaf77d7c7abfbcd5eaffbfdf1f8fefdd5eafefc7e6fcdf87f7c7e3fbf757e3fbf7c7e3fb85e84b4d5eaf5792ff1f37e1eef57abd5fdd5eaf57c3e6fcdf87abc2ec397be3d5eafeeaf57abfbabd5eafef0f57abc3d824e617c2a6,0x297,0x299,0x29b,0x29d,0x29f,0x2a1,0x2a3,0x2a5,0x2a7,0x2a9,0x2ab,0x2ad,0x2fce6d7c0485442ffbfde93f31fd753e0f0bf398c1f398c1ec43c1f5e630bf3983c1f3983c1e4bf983c1f3983c2ffbfdfef31fd7f7d71540aa49ffbfdfef1cebccf3fcfdf31810a20bf39cc2fc386617817c0ff7ce638406c39ce63780e20f9ce6374109eff7ce636e128,0x2af,0x1fb762c004807eae5e2c403bb5af677ed97eedded77607eddeedded777bb7607eaeebd6bcfaf5af3ebeaee7aba30414677edbbb6ed76f5eedbbb6e1f5dbd6,0x35faf5dafb9faebd8b6012ed6bdb5faeb4e2dc03db5af7b5af6d7ebaf7b5af7b5af7b5af6e7ebad3ebd6b4e8f5ad3a3d6b47a75ad38c185235faf5ebeebd7afb5d75ed75d7b5d75a3d75d6,0x2b1,0xd7ebaf6e7ebaf630e0d231604db5af6d7ebad38c700fed6bded6bdb5faf5d3ed6bded6bded6bdb9faeb4ee7d6b4e312150e7d6b4e6bf5ac0fa75ad3b5faf5ebed75d7b5d75ed75d7baf5ebf8fd75d6,0x39f37adcfb9f37acaf8cf8350d1013b9f5acaf897f37ad38d28101afd6b35f9afd6b2bee7cde6f4ee7d6b4ee7d6b4e57d6b03ee7cdeb4ee7d6b4e35e060e7d6b4e57d6b03e9d6b4f03f3795f379afd657d657d657d657d657d657caf95f2be57d657d6,0x1b7cefef6f873bfb13e37e05297f7b13e1cefcbf9e38204297f7b13e1f7b13fb7cefcbf9e97f7be7a5fdef9e27f7b13e1cefef9fb7f7be787def9e27f7b13fcfdef9e1cef89f13e97f627f61f627f627e5e27e5e27e5e27e5e27f627f638814c]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good2b16 : groupHybrid target anchors11246 pool v3 projectionMetas v2b16.toList h2b16=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b0 : List Nat := [0x6e,0x15edc2f2000007fc,0x0,0xa1fc7ce,0x26179000003fe,0xf23fee,0x0,0x25f91f87ee,0x0,0x87ee,0x97c390e2f33eee,0x3dcfe47f55e,0x1e69bf983d77e,0x3fe2,0xf4dfabd77e,0x1dfc,0x2b3,0x2b5,0x2b7,0x2b9,0x28,0x2bb,0x2bd,0x58,0x14fa7d3d3d3e9e,0x58,0x3858,0x2bf,0xb8b800a0004,0xafdcfbcece6,0x2bf73dcece6,0x13ee27fbcfbcece6]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b0 : groupHybrid target anchors11246 pool v4 projectionMetas v3b0.toList h3b0=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b1 : List Nat := [0x4db89fef34bf347ce6,0x10f2ef07bbfbbbdde,0x57140,0x93f5700500,0xbdcfbcc5e,0xbdcf730e,0xbef3ef30e,0x2fbcd9f30e,0x2fba1fef30f30ede6de6,0x14bbc9eefee,0x8bf5cf73ef5f7566d7d6,0x2c1,0x2c3,0x2c5,0x2c7,0x2c9,0x4dcfddf67ad2fce9e,0x2cb,0x2cd,0x2cf,0x2d1,0x2d3,0x9ed0d3a9fb5df4afe7b6f3e805da3a01a,0x50,0x270,0x2d5,0x14,0x270,0x2d7,0x50c5e,0x3478d3da,0x79d9ef6]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b1 : groupHybrid target anchors11246 pool v4 projectionMetas v3b1.toList h3b1=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b2 : List Nat := [0x30721c80,0x1c5e1e7661c5e,0x1c5e1e68f9d3e6,0x670,0x15f0,0x2d9,0x2db,0x2dd,0x2df,0x2e1,0x1bf6bdce6,0x2e3,0x4dcf9bc8fad2fce6,0x7777f77783c1e,0x1af0,0x2e5,0x2e7,0x2e9,0x2eb,0x2bf6bdee6,0x4c8fddf67ad2fd3e6,0x7727d0783dde,0xb5df33200,0x2f5ebce9f5e,0x2c,0x670,0x2ed,0x2d3a3e,0x2f5ebce9f5e,0xb0ccc80,0x4dcfddfa7acdf373e,0x1323f77d9eba7cd9e]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b2 : groupHybrid target anchors11246 pool v4 projectionMetas v3b2.toList h3b2=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b3 : List Nat := [0x10f27d77bbc1e,0x2ef,0x2f1,0x2f3,0xafdcf766,0x2f5,0x4fb89fef3ef66,0x4db89f6f367a3e6,0x43cbbc1fddde,0x27fb93c393c9e,0x5df73e27c389f13e,0x1dd5e27c389f0e27c4fd6e00ede6,0xafdabcdeafef4,0x2bfbf7ee,0xbdcfbf7ee,0x2f7,0x2f9,0x27a9ed4f538d38d3e7b7395fb73f3e8c6,0x3478d3da,0x4fa794fcdf3b3e,0x2fb,0x2fd,0x2ff,0x301,0x1bdaf5ebee17f5e,0x19e9f67e6,0x1be9ecbfd7b2ff3a7d7ad6,0x53d3ad43fb2ff3a74faf4f53d4ecbf4f5ea74e,0x32fe9e36bf3a7b5f9d9fb3ed7dafce6,0x28fe9f3b3e,0x2737cc1e,0x14fa7ac6faf3a71be]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b3 : groupHybrid target anchors11246 pool v4 projectionMetas v3b3.toList h3b3=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b4 : List Nat := [0x3f0,0x27124de5272,0x3737b76edcdf4,0xb5df377c80,0x27a34f9edce0fb9ede78c6,0x6be7ddcfabfbebd5eafee,0x303,0x305,0xb5df00,0x2d1bf0,0x307,0xb0,0xbef1bfd78d6,0x31f0,0xb0,0xb0,0x9f0,0x9fef1bf5dfd13e,0x309,0xbd7fbcad1eb6be,0x2718d38eb5f195fb9c7cf18c6,0x30b,0x172f5e9d3ebd6,0x6bc2e0,0x30d,0x30f,0x311,0x9c9781e000,0x313,0x315,0x317,0x319]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b4 : groupHybrid target anchors11246 pool v4 projectionMetas v3b4.toList h3b4=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b5 : List Nat := [0x31b,0x31d,0x13e74ebee9d3ebd3d4f53c6fd3a71a74e,0x13fbafbcc5e,0x2bf6bdcf6,0x1373f77d9eb4bf39d3e6,0x7727d07bbc1e,0x31f,0x13ee4feebef30e,0x321,0x2fbbbd5eb9ae3ad7d6,0x30,0xcafd7abbfa,0x323,0x325,0x327,0x329,0x32b,0x32d,0x32f,0xbd7af5e9f5e,0xbd7af5e9f5e,0x331,0x6f6bcebee17c6fae77e,0xafdcfbd9ccde,0x333,0x6f6bcebee17f5e,0x1ef2f2f2eb2c,0xbd7cbc8f5da,0xd7ebadafebf5f5daffbcbae8f58018c6,0x27a34eb1aebbee7aefa3a,0x6329c634e6dba7e87f9c7cfe78c6]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b5 : groupHybrid target anchors11246 pool v4 projectionMetas v3b5.toList h3b5=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b6 : List Nat := [0x335,0x4e6358d75d6,0x337,0xbef2f23d756,0x339,0x33b,0x6f6bcebee17f3af5e,0xbef2f23d756,0x372dfb76edcb7e5cb7f4,0x33d,0x33f,0x341,0x343,0x345,0x347,0x349,0x34b,0x3bcb29e278,0x34d,0xb37cdbce9f36e,0xbd7af5e9f5ebd7af5e,0xb0dbcdb80a78,0x34f,0x351,0x353,0x355,0x357,0x359,0x35b,0xafdcfbd9cf6,0x35d,0x35f]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b6 : groupHybrid target anchors11246 pool v4 projectionMetas v3b6.toList h3b6=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b7 : List Nat := [0x361,0x9e8d391ade783e804d4f9e80554fcfa019463a01c,0x363,0x311fa71a71d0fd399f4e48eb8d38d38db8eb8c2f8d38d38c6,0x97d0978c,0x4bd60978,0x19fe77e23f9df88fd5f5a7e77e23f4cfe,0x365,0x367,0x369,0x36b,0x36d,0x36f,0x371,0x373,0x375,0x377,0x379,0x37b,0x37d,0x526b9578,0x30,0x1afb5f47a3d68f5a3d68f5801ad76bb5f6be,0x37f,0x381,0x383,0x385,0x387,0x389,0x38b,0x38d,0x38f]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b7 : groupHybrid target anchors11246 pool v4 projectionMetas v3b7.toList h3b7=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b8 : List Nat := [0x391,0x393,0x395,0x397,0x399,0x39b,0x39d,0x39f,0x3a1,0x3a3,0x3a5,0x3a7,0x3a9,0x3ab,0x15bdaf42fd4e3af9c634e31daf9e8c6,0x75bd74f42fd4f6be718d38ed7a57ee7a57e8c6,0x3ad,0x3af,0x3b1,0x15b8eb8d38c76b8c6,0x3b3,0x3b5,0x23d68f5d5e7a,0x3b7,0x3b9,0x3bb,0x3bd,0x3bf,0x3c1,0x3c3,0x3c5,0x3c7]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b8 : groupHybrid target anchors11246 pool v4 projectionMetas v3b8.toList h3b8=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b9 : List Nat := [0x3c9,0x3cb,0x3cd,0x3cf,0x3d1,0x3d3,0x3d5,0x3d7,0x3d9,0x3db,0x3dd,0x3df,0x3e1,0x3e3,0x3e5,0x3e7,0x3e9,0x3eb,0x3ed,0x3ef,0x3f1,0x3f3,0x3f5,0x3f7,0x3f9,0x3fb,0x3fd,0x15b0,0x3ff,0x401,0x403,0x405]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b9 : groupHybrid target anchors11246 pool v4 projectionMetas v3b9.toList h3b9=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b10 : List Nat := [0x407,0x409,0xbd5b98be6,0x358d756efa,0x40b,0x54798e6,0x40d,0x40f,0x4e6358d756,0x9ea7b53d4e3ae34e34e31daf538c6,0x156358d756,0xa358d3d5d5f3e8c6,0x2a7b6b8d38ed58c6,0xbbabb5756358d635daf76,0xab40d75756,0x69eaed5d5d58d635d5d4e,0x52a7a9ed4f538d634e34e31d5d4f9e8c6,0x411,0x75635d5d5f7a,0x69ed58d38eae95fb9ef3e8c6,0x461800aeac79c6358bc60115ef7a,0x54e3ae34e34f6b8c6,0xd635d595fa,0xd635d595fa012,0x1e7d3d58d635d5a74e,0x598be6,0x413,0x2f9d98be6,0x2f9d98be6,0x2f9d98be6,0x2f9d98be6,0x2f9d98be6]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b10 : groupHybrid target anchors11246 pool v4 projectionMetas v3b10.toList h3b10=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b11 : List Nat := [0x1398bd5e4f178bd5e2f578bc9e,0x2f9d98be6,0x1398bd62f58bd756,0xd635d595fa,0xc47e48eb8d38db8eba9f18050c6,0x415,0x417,0x419,0x41b,0x41d,0x79d9ee6,0x727d11f87bbf1eba9f0e,0x1398bd5eaf0e1c9e1c9e1d5e,0x598be677e6,0x1398bd68f5a3d756,0x139aafc47e2f5aafd6abf5d0fd6,0xeb8d76b95fa016,0x1e7d3d58d635d5a74e,0x2f9d98be6,0x2f578be7661e6,0x2f9d98be6,0x54e3ae35dae,0xd635d595fa,0x311f8d6358d6a7c6018,0x2bc5e2f99df98bd5e2f98be62f98bd5e1e62f9879cc5e0be600897e697c5e97e6,0x41f,0xcaec786720f200001e,0x421,0x423,0x425,0x427,0x429]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b11 : groupHybrid target anchors11246 pool v4 projectionMetas v3b11.toList h3b11=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b12 : List Nat := [0x42b,0x1b2fc6318d7a7c60109bf1a74e31ac69bf1e71f3c6318c6020,0xbe62f9ccefd9f983e7317ce697e6,0x79a3e73dc2fe7b9cf739ee6,0x1e7d3d5a3d68f5d5a74e,0x727879d9879b3e6,0x1c9e1e7661e6,0x13c393c9e1e61e61e6,0x7278727d29f8727a9f0e,0x713e1e730e8f9c2fe739d3e733be5dfe6,0x1c9e1c9f477f0bfc791fc7872794ff1e,0x4e64f0e1c9f0f13e1c9e1c9e,0x3cc38393c3cc393c3872787278713e1c9e,0x5991f5c3e677e6,0x139d9f5c3d68f5a3d756,0x1bbbf0f9d9ee6,0x2f57a79879872097e6,0x3ae34f6b95fa01a,0xbd5e2f57abc33f8721c4f80bee7e,0x2f9d98be6,0x2f98be7b9ccef879872097e6,0xdaf8d0ff1f6be1c8743e0d7daff1fe3e,0x2f578be7661e6,0x2f9d98be6,0xbe62f98be733bf9e61c803c5e1e6,0x1c7f77e36be0061c8743e19f8fe7e3e,0x156358d756,0xd635d595fa,0xc47e48eb8d38df18eba9f18070c6,0x6758df1e75a3c68f5e758c6,0x713e1e68f9d3e6,0x9f13e1e777c3d3e61e6]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b12 : groupHybrid target anchors11246 pool v4 projectionMetas v3b12.toList h3b12=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b13 : List Nat := [0x1d0f8767a3c83fd3d9e4f0e,0x1d0f87c7a3c77e4fc798ff1f0bfc798ff1e,0x4e61c4fd9f13f77c38713f0bfbbe,0x43cc390e27c3cc389f0f67db8713f77c38713e1c4f8713e,0x8f99df5d9f9d3e6,0x4e68f5d9f5d9f5a3d67dfd6,0x6eef9afe68f9ee6,0x13993c9f30e4f0f67c4f967c4f872781c9e1d31787278713f67c9e4afc9e,0x721c4f8798728f9853e731783e6,0x743e1d0f928f4be25f0e00a0f6e376ebbf0f30e,0x48743e0f3803676fa7c60103ce71fceafce,0x13989f13e59f4e5df0e0081c,0x4389f13e27c3d9f6e1c4fcc5f77c38713f23f13e,0x13990f30f67dbd9f13f317ddf0e1c4f8713e,0x53e64fbbe6bf9a3e6,0x10bf9ce74fbbf0bf9ce9f4f9a3e73a7d3e6,0x42d,0x2f9d98be6,0x2f9d98be6,0x2f9d98be6,0x42f,0x431,0x433,0xcbf19231d1c9f1e71f3c637c631d0fc79c638df877f18080c6,0x435,0x437,0x52bfcf2bf4aff3ef3e8dfb4779fcfb6f3f9fcfa,0x67a37ee7a57edcf9ee7a,0x3cf7395fa37edcf6f3ee71e7a,0x7777f77783dde,0x1be6f95f41f83e6fa9f0df91f0783c8f83c37e,0xef77c0fe1fdfbf787f787f7ee]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b13 : groupHybrid target anchors11246 pool v4 projectionMetas v3b13.toList h3b13=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h3b14 : List Nat := [0x1dddfdec0fc8ff7ee,0x3bdde57ef7b03fbdef7a,0x143fe7d2be37c773db4af95fa57ef3ef777c9f93e9bfa,0x6c97f03fd95fdef6,0x1dddfdddeef77abc1f4f07abc1e0f07bbdde,0xaf6df89fee27fbabdde,0x67f8ff74be26fd2f83db83db80f4bf303e97d2fabe3924a5f4be,0x19f7dfe76f9dbe9f180803ce01f9f8fcc0f924aeff38c6,0x2bf5e4fee27fb8bd5e]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good3b14 : groupHybrid target anchors11246 pool v4 projectionMetas v3b14.toList h3b14=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h4b0 : List Nat := [0x0,0x439,0x43b,0x3676,0x43d,0x43f,0x441,0x443,0x14880033cecd2,0x4b8,0x4b8,0x33cb8,0x4b8,0x4b8,0x4b8,0x459600,0x33c848]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good4b0 : groupHybrid target anchors11246 pool v5 projectionMetas v4b0.toList h4b0=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
def h5b0 : List Nat := [0x445]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem good5b0 : groupHybrid target anchors11246 pool v6 projectionMetas v5b0.toList h5b0=true := by decide +kernel
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
theorem level5 (excluded : ∀{i m},lookup projectionMetas i=some m → Dead target (pool m)) : ∀i m,lookup v5 i=some m → Dead target (pool m) := by
  have next : ∀i m,lookup v6 i=some m → Dead target (pool m) := by
    intro i m hm; simp [lookup,v6] at hm
  apply lookGroup
  intro group belongs
  change group∈[v5b0] at belongs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at belongs
  rcases belongs with rfl
  · exact hybridGroupSound good5b0 next @excluded
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
theorem level4 (excluded : ∀{i m},lookup projectionMetas i=some m → Dead target (pool m)) : ∀i m,lookup v4 i=some m → Dead target (pool m) := by
  have next:=level5 @excluded
  apply lookGroup
  intro group belongs
  change group∈[v4b0] at belongs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at belongs
  rcases belongs with rfl
  · exact hybridGroupSound good4b0 next @excluded
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
theorem level3 (excluded : ∀{i m},lookup projectionMetas i=some m → Dead target (pool m)) : ∀i m,lookup v3 i=some m → Dead target (pool m) := by
  have next:=level4 @excluded
  apply lookGroup
  intro group belongs
  change group∈[v3b0,v3b1,v3b2,v3b3,v3b4,v3b5,v3b6,v3b7,v3b8,v3b9,v3b10,v3b11,v3b12,v3b13,v3b14] at belongs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at belongs
  rcases belongs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hybridGroupSound good3b0 next @excluded
  · exact hybridGroupSound good3b1 next @excluded
  · exact hybridGroupSound good3b2 next @excluded
  · exact hybridGroupSound good3b3 next @excluded
  · exact hybridGroupSound good3b4 next @excluded
  · exact hybridGroupSound good3b5 next @excluded
  · exact hybridGroupSound good3b6 next @excluded
  · exact hybridGroupSound good3b7 next @excluded
  · exact hybridGroupSound good3b8 next @excluded
  · exact hybridGroupSound good3b9 next @excluded
  · exact hybridGroupSound good3b10 next @excluded
  · exact hybridGroupSound good3b11 next @excluded
  · exact hybridGroupSound good3b12 next @excluded
  · exact hybridGroupSound good3b13 next @excluded
  · exact hybridGroupSound good3b14 next @excluded
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
theorem level2 (excluded : ∀{i m},lookup projectionMetas i=some m → Dead target (pool m)) : ∀i m,lookup v2 i=some m → Dead target (pool m) := by
  have next:=level3 @excluded
  apply lookGroup
  intro group belongs
  change group∈[v2b0,v2b1,v2b2,v2b3,v2b4,v2b5,v2b6,v2b7,v2b8,v2b9,v2b10,v2b11,v2b12,v2b13,v2b14,v2b15,v2b16] at belongs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at belongs
  rcases belongs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hybridGroupSound good2b0 next @excluded
  · exact hybridGroupSound good2b1 next @excluded
  · exact hybridGroupSound good2b2 next @excluded
  · exact hybridGroupSound good2b3 next @excluded
  · exact hybridGroupSound good2b4 next @excluded
  · exact hybridGroupSound good2b5 next @excluded
  · exact hybridGroupSound good2b6 next @excluded
  · exact hybridGroupSound good2b7 next @excluded
  · exact hybridGroupSound good2b8 next @excluded
  · exact hybridGroupSound good2b9 next @excluded
  · exact hybridGroupSound good2b10 next @excluded
  · exact hybridGroupSound good2b11 next @excluded
  · exact hybridGroupSound good2b12 next @excluded
  · exact hybridGroupSound good2b13 next @excluded
  · exact hybridGroupSound good2b14 next @excluded
  · exact hybridGroupSound good2b15 next @excluded
  · exact hybridGroupSound good2b16 next @excluded
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
theorem level1 (excluded : ∀{i m},lookup projectionMetas i=some m → Dead target (pool m)) : ∀i m,lookup v1 i=some m → Dead target (pool m) := by
  have next:=level2 @excluded
  apply lookGroup
  intro group belongs
  change group∈[v1b0,v1b1,v1b2] at belongs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at belongs
  rcases belongs with rfl|rfl|rfl
  · exact hybridGroupSound good1b0 next @excluded
  · exact hybridGroupSound good1b1 next @excluded
  · exact hybridGroupSound good1b2 next @excluded
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
theorem level0 (excluded : ∀{i m},lookup projectionMetas i=some m → Dead target (pool m)) : ∀i m,lookup v0 i=some m → Dead target (pool m) := by
  have next:=level1 @excluded
  apply lookGroup
  intro group belongs
  change group∈[v0b0] at belongs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at belongs
  rcases belongs with rfl
  · exact hybridGroupSound good0b0 next @excluded
end LiveAIG.TableHybrid

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
open FreeAIG
theorem nonzero {f : X→Bool} (dep : depends f) : norm (word f)≠0 := by
  intro h
  obtain ⟨r,q,_,ne⟩ := dep 0
  have eq : (norm (word f))[r.val]=(norm (word f))[q.val] := by rw [h];simp
  have v:=signedCong (word f)[0] eq
  rw [orient,wordBit,wordBit] at v
  exact ne v

theorem mustUse {f : X→Bool} (dep : depends f) {U : Finset W} (sub : U⊆inputs.toFinset)
    {n c} (runU : Run (word f) U.toList n c) : U=inputs.toFinset := by
  apply Finset.Subset.antisymm sub
  intro w mw
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp mw)
  by_contra missing
  obtain ⟨r,q,neigh,changed⟩ := dep i
  apply changed
  rw [←wordBit f r,←wordBit f q]
  apply agreeRun runU
  intro u hu
  have ui : u∈U := Finset.mem_toList.mp hu
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (sub ui))
  have ne : j≠i := fun eq=>missing (eq ▸ ui)
  rw [wordBit,wordBit]
  exact neigh j ne

theorem compile {f : X→Bool} {k : Nat} (h : Has Inputs k f) (dep : depends f) :
    ∃n≤k,∃c,Run (word f) inputs n c ∧ c+6=n := by
  classical
  have rep : Represents Inputs inputs.toFinset := by
    rintro g ⟨i,rfl⟩
    right
    rw [rawNorm]
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
  obtain ⟨U,sub,_,n,sz,c,ok⟩ := trim h inputs.toFinset rep (nonzero dep)
  have all := mustUse dep sub (ok U.toList U.nodup_toList U.toList_toFinset)
  have runAll := ok inputs uniqueInputs all.symm
  have length:=balance runAll
  rw [inputLength] at length
  exact ⟨n,sz,c,runAll,by omega⟩

end LiveAIG

namespace OneNot11246
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def original (x : Fin 7→Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def wires : List Gate := [⟨.or, [0, 1]⟩,⟨.or, [1, 2]⟩,⟨.or, [0, 8]⟩,⟨.or, [9, 3]⟩,⟨.or, [10, 5]⟩,⟨.and, [3, 0]⟩,⟨.and, [4, 7]⟩,⟨.and, [5, 8]⟩,⟨.and, [6, 11]⟩,⟨.or, [12, 13]⟩,⟨.or, [16, 14]⟩,⟨.or, [17, 15]⟩]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def witness : Circuit := ⟨wires,18⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem upperBound : wires.length=12 ∧ (∀ g∈wires,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) := by
  constructor
  · rfl
  · intro g hg
    simp only [wires,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem witnessCorrect : ∀ x : Fin 7→Bool,witness.eval (List.ofFn x)=original x := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def monotone (gs : List Gate) := ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def fits (C : Circuit) := ∀ x : Fin 7→Bool,C.eval (List.ofFn x)=original x
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def oneNot (gs : List Gate) := (∀ g∈gs,(g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) ∧
  (∀ i j : Fin gs.length,(gs.get i).op=.not → (gs.get j).op=.not → i=j)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
def Replacement (C : Circuit) := ∃ D : Circuit,monotone D.gates ∧ D.gates.length≤C.gates.length ∧ fits D
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem large (C : Circuit) (big : 12≤C.gates.length) : Replacement C :=
  ⟨witness,upperBound.2,(upperBound.1.le.trans big),witnessCorrect⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem noNot (C : Circuit) (legal : oneNot C.gates) (ok : fits C) (none : ∀ g∈C.gates,g.op≠.not) : Replacement C := by
  refine ⟨C,?_,le_rfl,ok⟩
  intro g hg
  obtain ⟨ops,len⟩ := legal.1 g hg
  exact ⟨ops.imp_right (fun x=>x.resolve_right (none g hg)),len⟩
end OneNot11246

namespace LiveAIG.Row11246
def t : W := 340282366920937254519035908547186436608
theorem inputsExplicit : inputs=[226854911280625642308916404954512140970,272225893536750770770699685945414569164,320265757102059730318470218759311257840,338958311018522360492699998064329424640,340277174703306882242637262502835978240,340282366841710300967557013907638845440,340282366920938463444927863358058659840] := by decide +kernel
theorem wordOriginal : word OneNot11246.original = t := by
  set_option maxRecDepth 32768 in decide +kernel
def pos (i : Fin 7) : R := ![9,18,36,9,17,34,65] i
def neg (i : Fin 7) : R := ![8,16,32,1,1,2,1] i
theorem essential : depends OneNot11246.original := by
  intro i
  refine ⟨pos i,neg i,?_,?_⟩
  · revert i;decide +kernel
  · revert i;decide +kernel
theorem ifTen {k : Nat} (h : FreeAIG.Has FreeAIG.Inputs k OneNot11246.original) (sz : k≤10) :
    ∃n≤10,∃c≤4,Run t inputs n c ∧ c+6=n := by
  obtain ⟨n,le,c,r,eq⟩ := compile h essential
  rw [wordOriginal] at r
  exact ⟨n,by omega,c,by omega,r,eq⟩
end LiveAIG.Row11246

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

-- The following restriction certificates are adapted from L-meta-10482 in this project.
-- That proof credits L-meta-10802, L-meta-1674, L-meta-670 and L-meta-1667.
namespace MinorArchive82
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffefffefffefefeeca0fffffffffffffffefffefffefefeeca0fffffffffffffffefffefffefefeeca0fffffffffffffffefffefffefefeeca0
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 583
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 583 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 583 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 583 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 583 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 583) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 583) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 583) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 583) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 583 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 583) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 583 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 583) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 583) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096 ≤ marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 583) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [4, 5]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [0, 8]⟩,
    ⟨.or, [1, 11]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.and, [10, 9]⟩,
    ⟨.and, [14, 12]⟩,
    ⟨.and, [13, 3]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [17, 18]⟩], 19⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 13 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim

def sevenInputs : List Sig := vars 127
def sampleSeven (r : Row) (i : Fin 7) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 7 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 7) : Row := Fin.ofNat 512 (1 <<< ([2, 3, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([2, 3, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 7, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 7, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 11 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim

def g37Y : Array (Bits × Bits) := #[(0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000),
    (0x0, 0x0)]
def g37C : List ColumnInfo := []
def g37D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g37L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g37D3)
  | _ => emptyPacking
def g37I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g37 : Forest := ⟨37, 3, fun i => (g37Y[i]?).getD (0,0), g37C, [[], [82], [32], [32, 82], [80, 82], [80]], g37L, g37I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g37P3n0 : block g37 3 0 1 = true := by decide +kernel
theorem g37B3 : block g37 3 0 1 = true := g37P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g37T : checkedTables g37 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g37 0 0 0 = true)
  · exact (rfl : block g37 1 0 0 = true)
  · exact (rfl : block g37 2 0 0 = true)
  · exact g37B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g37G : graphValid g37 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low37 : Lower true (varsX 37) (graphGoal 37) 4 := lower_forest (g:=g37) (i:=0) (hints:=2) (before_sound [] baseKnown) g37G g37T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K37 := extendKnown [] 4 [(37,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V37 : Known true K37 := extend_ok (m:=37) baseKnown low37 (by decide +kernel)

def g42Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x0, 0x0),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000),
    (0x0, 0x0)]
def g42C : List ColumnInfo := []
def g42D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g42L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g42D3)
  | _ => emptyPacking
def g42I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g42 : Forest := ⟨42, 3, fun i => (g42Y[i]?).getD (0,0), g42C, [[], [83], [49], [49, 83], [81, 83], [81]], g42L, g42I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g42P3n0 : block g42 3 0 1 = true := by decide +kernel
theorem g42B3 : block g42 3 0 1 = true := g42P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g42T : checkedTables g42 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g42 0 0 0 = true)
  · exact (rfl : block g42 1 0 0 = true)
  · exact (rfl : block g42 2 0 0 = true)
  · exact g42B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g42G : graphValid g42 (boundsBefore K37) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low42 : Lower true (varsX 42) (graphGoal 42) 4 := lower_forest (g:=g42) (i:=0) (hints:=1052720) (before_sound K37 V37) g42G g42T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K42 := extendKnown K37 4 [(42,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V42 : Known true K42 := extend_ok (m:=42) V37 low42 (by decide +kernel)

def g69Y : Array (Bits × Bits) := #[(0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g69C : List ColumnInfo := []
def g69D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g69L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g69D3)
  | _ => emptyPacking
def g69I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g69 : Forest := ⟨69, 3, fun i => (g69Y[i]?).getD (0,0), g69C, [[], [98], [32], [32, 98], [96, 98], [96]], g69L, g69I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g69P3n0 : block g69 3 0 1 = true := by decide +kernel
theorem g69B3 : block g69 3 0 1 = true := g69P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g69T : checkedTables g69 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g69 0 0 0 = true)
  · exact (rfl : block g69 1 0 0 = true)
  · exact (rfl : block g69 2 0 0 = true)
  · exact g69B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g69G : graphValid g69 (boundsBefore K42) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low69 : Lower true (varsX 69) (graphGoal 69) 4 := lower_forest (g:=g69) (i:=0) (hints:=2) (before_sound K42 V42) g69G g69T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K69 := extendKnown K42 4 [(69,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V69 : Known true K69 := extend_ok (m:=69) V42 low69 (by decide +kernel)

def g74Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g74C : List ColumnInfo := []
def g74D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g74L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g74D3)
  | _ => emptyPacking
def g74I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g74 : Forest := ⟨74, 3, fun i => (g74Y[i]?).getD (0,0), g74C, [[], [99], [49], [49, 99], [97, 99], [97]], g74L, g74I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g74P3n0 : block g74 3 0 1 = true := by decide +kernel
theorem g74B3 : block g74 3 0 1 = true := g74P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g74T : checkedTables g74 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g74 0 0 0 = true)
  · exact (rfl : block g74 1 0 0 = true)
  · exact (rfl : block g74 2 0 0 = true)
  · exact g74B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g74G : graphValid g74 (boundsBefore K69) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low74 : Lower true (varsX 74) (graphGoal 74) 4 := lower_forest (g:=g74) (i:=0) (hints:=16781360) (before_sound K69 V69) g74G g74T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K74 := extendKnown K69 4 [(74,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V74 : Known true K74 := extend_ok (m:=74) V69 low74 (by decide +kernel)

def g97Y : Array (Bits × Bits) := #[(0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g97C : List ColumnInfo := []
def g97D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g97L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g97D3)
  | _ => emptyPacking
def g97I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g97 : Forest := ⟨97, 3, fun i => (g97Y[i]?).getD (0,0), g97C, [[], [101], [80], [80, 101], [96, 101], [96]], g97L, g97I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g97P3n0 : block g97 3 0 1 = true := by decide +kernel
theorem g97B3 : block g97 3 0 1 = true := g97P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g97T : checkedTables g97 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g97 0 0 0 = true)
  · exact (rfl : block g97 1 0 0 = true)
  · exact (rfl : block g97 2 0 0 = true)
  · exact g97B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g97G : graphValid g97 (boundsBefore K74) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low97 : Lower true (varsX 97) (graphGoal 97) 4 := lower_forest (g:=g97) (i:=0) (hints:=5) (before_sound K74 V74) g97G g97T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K97 := extendKnown K74 4 [(97,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V97 : Known true K97 := extend_ok (m:=97) V74 low97 (by decide +kernel)

def g98Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g98C : List ColumnInfo := []
def g98D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g98L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g98D3)
  | _ => emptyPacking
def g98I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g98 : Forest := ⟨98, 3, fun i => (g98Y[i]?).getD (0,0), g98C, [[], [101], [81], [81, 101], [97, 101], [97]], g98L, g98I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g98P3n0 : block g98 3 0 1 = true := by decide +kernel
theorem g98B3 : block g98 3 0 1 = true := g98P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g98T : checkedTables g98 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g98 0 0 0 = true)
  · exact (rfl : block g98 1 0 0 = true)
  · exact (rfl : block g98 2 0 0 = true)
  · exact g98B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g98G : graphValid g98 (boundsBefore K97) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low98 : Lower true (varsX 98) (graphGoal 98) 4 := lower_forest (g:=g98) (i:=0) (hints:=17825872) (before_sound K97 V97) g98G g98T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K98 := extendKnown K97 4 [(98,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V98 : Known true K98 := extend_ok (m:=98) V97 low98 (by decide +kernel)

def g100Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g100C : List ColumnInfo := []
def g100D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g100L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g100D3)
  | _ => emptyPacking
def g100I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g100 : Forest := ⟨100, 3, fun i => (g100Y[i]?).getD (0,0), g100C, [[], [101], [82], [82, 101], [98, 101], [98]], g100L, g100I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g100P3n0 : block g100 3 0 1 = true := by decide +kernel
theorem g100B3 : block g100 3 0 1 = true := g100P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g100T : checkedTables g100 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g100 0 0 0 = true)
  · exact (rfl : block g100 1 0 0 = true)
  · exact (rfl : block g100 2 0 0 = true)
  · exact g100B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g100G : graphValid g100 (boundsBefore K98) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low100 : Lower true (varsX 100) (graphGoal 100) 4 := lower_forest (g:=g100) (i:=0) (hints:=35652864) (before_sound K98 V98) g100G g100T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K100 := extendKnown K98 4 [(100,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V100 : Known true K100 := extend_ok (m:=100) V98 low100 (by decide +kernel)

def g104Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x3bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, 0x7000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0),
    (0x0, 0x0),
    (0x5ddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00),
    (0x6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000)]
def g104C : List ColumnInfo := []
def g104D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g104L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g104D3)
  | _ => emptyPacking
def g104I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g104 : Forest := ⟨104, 3, fun i => (g104Y[i]?).getD (0,0), g104C, [[], [101], [83], [83, 101], [99, 101], [99]], g104L, g104I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g104P3n0 : block g104 3 0 1 = true := by decide +kernel
theorem g104B3 : block g104 3 0 1 = true := g104P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g104T : checkedTables g104 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g104 0 0 0 = true)
  · exact (rfl : block g104 1 0 0 = true)
  · exact (rfl : block g104 2 0 0 = true)
  · exact g104B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g104G : graphValid g104 (boundsBefore K100) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low104 : Lower true (varsX 104) (graphGoal 104) 4 := lower_forest (g:=g104) (i:=0) (hints:=53497856) (before_sound K100 V100) g104G g104T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K104 := extendKnown K100 4 [(104,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V104 : Known true K104 := extend_ok (m:=104) V100 low104 (by decide +kernel)

def g39Y : Array (Bits × Bits) := #[(0x57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x7f000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe00),
    (0x1acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359a, 0x3fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000),
    (0x63f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0x3ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000),
    (0x0, 0x0)]
def g39C : List ColumnInfo := [(2,0,37,0,4)]
def g39D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g39L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g39D4)
  | _ => emptyPacking
def g39I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g39 : Forest := ⟨39, 4, fun i => (g39Y[i]?).getD (0,0), g39C, [[], [32]], g39L, g39I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39P4n0 : block g39 4 0 1 = true := by decide +kernel
theorem g39B4 : block g39 4 0 1 = true := g39P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39T : checkedTables g39 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g39 0 0 0 = true)
  · exact (rfl : block g39 1 0 0 = true)
  · exact (rfl : block g39 2 0 0 = true)
  · exact (rfl : block g39 3 0 0 = true)
  · exact g39B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39G : graphValid g39 (boundsBefore K104) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low39 : Lower true (varsX 39) (graphGoal 39) 5 := lower_forest (g:=g39) (i:=0) (hints:=82) (before_sound K104 V104) g39G g39T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K39 := extendKnown K104 5 [(39,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V39 : Known true K39 := extend_ok (m:=39) V104 low39 (by decide +kernel)

def g43Y : Array (Bits × Bits) := #[(0x56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56, 0x7f00003fe00ff803fe00007fc01ff007fc0000ff803fe00ff80001ff007fc01ff00003fe00ff803fe00007fc01ff007fc0000ff803fe00ff80001ff007fc01ff00003fe00ff803fe00),
    (0x1bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379b, 0xffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc0000),
    (0x0, 0x0),
    (0x63f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0x3ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000),
    (0x0, 0x0)]
def g43C : List ColumnInfo := [(1,0,42,0,4)]
def g43D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g43L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g43D4)
  | _ => emptyPacking
def g43I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g43 : Forest := ⟨43, 4, fun i => (g43Y[i]?).getD (0,0), g43C, [[], [49]], g43L, g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P4n0 : block g43 4 0 1 = true := by decide +kernel
theorem g43B4 : block g43 4 0 1 = true := g43P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact (rfl : block g43 3 0 0 = true)
  · exact g43B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K39) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := lower_forest (g:=g43) (i:=0) (hints:=4149) (before_sound K39 V39) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K39 5 [(43,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V39 low43 (by decide +kernel)

def g45Y : Array (Bits × Bits) := #[(0x57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x7f0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe00),
    (0x0, 0x0),
    (0x1bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379b, 0x3fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000),
    (0x62f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2, 0x3ffffff8000000007ffffff000000000ffffffe000000001ffffffc000000003ffffff8000000007ffffff000000000ffffffe000000001ffffffc000000003ffffff8000000),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000),
    (0x0, 0x0)]
def g45C : List ColumnInfo := [(8,0,37,0,4)]
def g45D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g45L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g45D4)
  | _ => emptyPacking
def g45I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g45 : Forest := ⟨45, 4, fun i => (g45Y[i]?).getD (0,0), g45C, [[], [32]], g45L, g45I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P4n0 : block g45 4 0 1 = true := by decide +kernel
theorem g45B4 : block g45 4 0 1 = true := g45P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45T : checkedTables g45 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g45 0 0 0 = true)
  · exact (rfl : block g45 1 0 0 = true)
  · exact (rfl : block g45 2 0 0 = true)
  · exact (rfl : block g45 3 0 0 = true)
  · exact g45B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45G : graphValid g45 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (graphGoal 45) 5 := lower_forest (g:=g45) (i:=0) (hints:=20482) (before_sound K43 V43) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K43 5 [(45,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V43 low45 (by decide +kernel)

def g46Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x7f000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe00),
    (0x1acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359a, 0x3fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000),
    (0x63f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0x3ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000),
    (0x0, 0x0)]
def g46C : List ColumnInfo := [(4,0,42,0,4)]
def g46D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g46L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g46D4)
  | _ => emptyPacking
def g46I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g46 : Forest := ⟨46, 4, fun i => (g46Y[i]?).getD (0,0), g46C, [[], [49]], g46L, g46I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g46P4n0 : block g46 4 0 1 = true := by decide +kernel
theorem g46B4 : block g46 4 0 1 = true := g46P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g46T : checkedTables g46 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g46 0 0 0 = true)
  · exact (rfl : block g46 1 0 0 = true)
  · exact (rfl : block g46 2 0 0 = true)
  · exact (rfl : block g46 3 0 0 = true)
  · exact g46B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g46G : graphValid g46 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low46 : Lower true (varsX 46) (graphGoal 46) 5 := lower_forest (g:=g46) (i:=0) (hints:=1054000) (before_sound K45 V45) g46G g46T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K46 := extendKnown K45 5 [(46,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V46 : Known true K46 := extend_ok (m:=46) V45 low46 (by decide +kernel)

def g71Y : Array (Bits × Bits) := #[(0x57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x7f000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe00),
    (0x1acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359a, 0x3fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000),
    (0x63f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0x3ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g71C : List ColumnInfo := [(2,0,69,0,4)]
def g71D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g71L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g71D4)
  | _ => emptyPacking
def g71I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g71 : Forest := ⟨71, 4, fun i => (g71Y[i]?).getD (0,0), g71C, [[], [32]], g71L, g71I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g71P4n0 : block g71 4 0 1 = true := by decide +kernel
theorem g71B4 : block g71 4 0 1 = true := g71P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g71T : checkedTables g71 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g71 0 0 0 = true)
  · exact (rfl : block g71 1 0 0 = true)
  · exact (rfl : block g71 2 0 0 = true)
  · exact (rfl : block g71 3 0 0 = true)
  · exact g71B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g71G : graphValid g71 (boundsBefore K46) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low71 : Lower true (varsX 71) (graphGoal 71) 5 := lower_forest (g:=g71) (i:=0) (hints:=98) (before_sound K46 V46) g71G g71T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K71 := extendKnown K46 5 [(71,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V71 : Known true K71 := extend_ok (m:=71) V46 low71 (by decide +kernel)

def g75Y : Array (Bits × Bits) := #[(0x56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56ab55aad56, 0x7f00003fe00ff803fe00007fc01ff007fc0000ff803fe00ff80001ff007fc01ff00003fe00ff803fe00007fc01ff007fc0000ff803fe00ff80001ff007fc01ff00003fe00ff803fe00),
    (0x1bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379b, 0xffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc0000),
    (0x0, 0x0),
    (0x63f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0x3ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g75C : List ColumnInfo := [(1,0,74,0,4)]
def g75D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g75L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g75D4)
  | _ => emptyPacking
def g75I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g75 : Forest := ⟨75, 4, fun i => (g75Y[i]?).getD (0,0), g75C, [[], [49]], g75L, g75I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75P4n0 : block g75 4 0 1 = true := by decide +kernel
theorem g75B4 : block g75 4 0 1 = true := g75P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75T : checkedTables g75 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g75 0 0 0 = true)
  · exact (rfl : block g75 1 0 0 = true)
  · exact (rfl : block g75 2 0 0 = true)
  · exact (rfl : block g75 3 0 0 = true)
  · exact g75B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75G : graphValid g75 (boundsBefore K71) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low75 : Lower true (varsX 75) (graphGoal 75) 5 := lower_forest (g:=g75) (i:=0) (hints:=4150) (before_sound K71 V71) g75G g75T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K75 := extendKnown K71 5 [(75,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V75 : Known true K75 := extend_ok (m:=75) V71 low75 (by decide +kernel)

def g77Y : Array (Bits × Bits) := #[(0x57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x7f0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe00),
    (0x0, 0x0),
    (0x1bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379bcde6f379b, 0x3fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000007fc0000ff8000000ff80001ff0000001ff00003fe0000003fe00007fc0000),
    (0x62f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2f178bc5e2, 0x3ffffff8000000007ffffff000000000ffffffe000000001ffffffc000000003ffffff8000000007ffffff000000000ffffffe000000001ffffffc000000003ffffff8000000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g77C : List ColumnInfo := [(8,0,69,0,4)]
def g77D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g77L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g77D4)
  | _ => emptyPacking
def g77I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g77 : Forest := ⟨77, 4, fun i => (g77Y[i]?).getD (0,0), g77C, [[], [32]], g77L, g77I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77P4n0 : block g77 4 0 1 = true := by decide +kernel
theorem g77B4 : block g77 4 0 1 = true := g77P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77T : checkedTables g77 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g77 0 0 0 = true)
  · exact (rfl : block g77 1 0 0 = true)
  · exact (rfl : block g77 2 0 0 = true)
  · exact (rfl : block g77 3 0 0 = true)
  · exact g77B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77G : graphValid g77 (boundsBefore K75) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low77 : Lower true (varsX 77) (graphGoal 77) 5 := lower_forest (g:=g77) (i:=0) (hints:=24578) (before_sound K75 V75) g77G g77T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K77 := extendKnown K75 5 [(77,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V77 : Known true K77 := extend_ok (m:=77) V75 low77 (by decide +kernel)

def g78Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57abd5eaf57, 0x7f000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe000000001ff007fc000000003fe00ff8000000007fc01ff000000000ff803fe00),
    (0x1acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359acd66b359a, 0x3fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000007fc01ffff8000000ff803ffff0000001ff007fffe0000003fe00ffffc0000),
    (0x63f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3f1f8fc7e3, 0x3ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000007fffe00000000000ffffc00000000001ffff800000000003ffff000000000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x7cfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fcfe7f3f9fc, 0x7fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000ff80000000000001ff00000000000003fe00000000000007fc0000000000000)]
def g78C : List ColumnInfo := [(4,0,74,0,4)]
def g78D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g78L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g78D4)
  | _ => emptyPacking
def g78I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g78 : Forest := ⟨78, 4, fun i => (g78Y[i]?).getD (0,0), g78C, [[], [49]], g78L, g78I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78P4n0 : block g78 4 0 1 = true := by decide +kernel
theorem g78B4 : block g78 4 0 1 = true := g78P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78T : checkedTables g78 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g78 0 0 0 = true)
  · exact (rfl : block g78 1 0 0 = true)
  · exact (rfl : block g78 2 0 0 = true)
  · exact (rfl : block g78 3 0 0 = true)
  · exact g78B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78G : graphValid g78 (boundsBefore K77) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low78 : Lower true (varsX 78) (graphGoal 78) 5 := lower_forest (g:=g78) (i:=0) (hints:=16782896) (before_sound K77 V77) g78G g78T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K78 := extendKnown K77 5 [(78,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V78 : Known true K78 := extend_ok (m:=78) V77 low78 (by decide +kernel)

def g101Y : Array (Bits × Bits) := #[(0x55bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5b, 0xffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800),
    (0x0, 0x0),
    (0x66dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6d, 0x7ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x78ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778e, 0x7ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000),
    (0x7f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0, 0x3ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000)]
def g101C : List ColumnInfo := [(1,0,100,0,4), (4,0,97,0,4), (32,0,69,0,4), (64,0,37,0,4)]
def g101D3 (j : Nat) : Nat := if j = 0 then 0x8028023ea6a1203e11240901 else 0
def g101D4 (j : Nat) : Nat := if j = 0 then 0x6090858702fd0901bd42407e40901 else 0
def g101D5 (j : Nat) : Nat := if j = 0 then 0x1a2047d01 else 0
def g101D6 (j : Nat) : Nat := if j = 0 then 0x7208f else 0
def g101L : Nat → Packing
  | 3 => (2, 3, 2, 0, 0, 5, 0, g101D3)
  | 4 => (3, 2, 2, 0, 0, 5, 0, g101D4)
  | 5 => (1, 1, 2, 0, 0, 1, 0, g101D5)
  | 6 => (1, 0, 2, 0, 0, 1, 0, g101D6)
  | _ => emptyPacking
def g101I : Nat → Nat → Option (Nat × Nat)
  | 4, tag => lookupShort 1 3 1 3 1 0 (fun j => if j=0 then 0x206 else 0) tag
  | 5, tag => lookupShort 4 13 1 7 2 3 (fun j => if j=0 then 0x3cca13100c1600c68 else 0) tag
  | 6, tag => lookupShort 3 13 2 8 1 5 (fun j => if j=0 then 0x3000383186800031000000000602 else 0) tag
  | _, _ => none
def g101 : Forest := ⟨101, 6, fun i => (g101Y[i]?).getD (0,0), g101C, [[], [101], [82], [82, 101], [98, 101], [98], [32], [32, 101], [32, 82], [32, 82, 101], [32, 98, 101], [32, 98], [80, 82], [80, 82, 101], [80], [80, 101], [80, 98], [80, 98, 101], [96, 98, 101], [96, 98], [96, 101], [96], [96, 82, 101], [96, 82]], g101L, g101I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P3n0 : block g101 3 0 2 = true := by decide +kernel
theorem g101B3 : block g101 3 0 2 = true := g101P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P4n0 : block g101 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P4n2 : block g101 4 2 1 = true := by decide +kernel
theorem g101B4 : block g101 4 0 3 = true := (@block_merge g101 4 0 2 1 g101P4n0 g101P4n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P5n0 : block g101 5 0 1 = true := by decide +kernel
theorem g101B5 : block g101 5 0 1 = true := g101P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P6n0 : block g101 6 0 1 = true := by decide +kernel
theorem g101B6 : block g101 6 0 1 = true := g101P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101T : checkedTables g101 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g101 0 0 0 = true)
  · exact (rfl : block g101 1 0 0 = true)
  · exact (rfl : block g101 2 0 0 = true)
  · exact g101B3
  · exact g101B4
  · exact g101B5
  · exact g101B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101G : graphValid g101 (boundsBefore K78) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low101 : Lower true (varsX 101) (graphGoal 101) 7 := lower_forest (g:=g101) (i:=0) (hints:=2) (before_sound K78 V78) g101G g101T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K101 := extendKnown K78 7 [(101,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V101 : Known true K101 := extend_ok (m:=101) V78 low101 (by decide +kernel)

def g105Y : Array (Bits × Bits) := #[(0x5ab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6ad, 0xffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc00),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x6cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36, 0xfffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff00000),
    (0x0, 0x0),
    (0x7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7, 0x70000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000),
    (0xfe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8, 0xffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000)]
def g105C : List ColumnInfo := [(1,0,104,0,4)]
def g105D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g105L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g105D4)
  | _ => emptyPacking
def g105I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g105 : Forest := ⟨105, 4, fun i => (g105Y[i]?).getD (0,0), g105C, [[], [101], [48], [48, 101]], g105L, g105I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P4n0 : block g105 4 0 1 = true := by decide +kernel
theorem g105B4 : block g105 4 0 1 = true := g105P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105T : checkedTables g105 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g105 0 0 0 = true)
  · exact (rfl : block g105 1 0 0 = true)
  · exact (rfl : block g105 2 0 0 = true)
  · exact (rfl : block g105 3 0 0 = true)
  · exact g105B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105G : graphValid g105 (boundsBefore K101) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low105 : Lower true (varsX 105) (graphGoal 105) 5 := lower_forest (g:=g105) (i:=0) (hints:=20485) (before_sound K101 V101) g105G g105T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K105 := extendKnown K101 5 [(105,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V105 : Known true K105 := extend_ok (m:=105) V101 low105 (by decide +kernel)

def g106Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x55bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5b, 0xffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800),
    (0x0, 0x0),
    (0x66dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6d, 0x7ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000),
    (0x0, 0x0),
    (0x78ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778e, 0x7ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000),
    (0x7f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0, 0x3ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000ffe00000000001ffc00000000003ff800000000007ff00000000000)]
def g106C : List ColumnInfo := [(2,0,104,0,4), (8,0,98,0,4), (32,0,74,0,4), (64,0,42,0,4)]
def g106D3 (j : Nat) : Nat := if j = 0 then 0x8028023ea6a1203e11240901 else 0
def g106D4 (j : Nat) : Nat := if j = 0 then 0x6090858702fd0901bd42407e40901 else 0
def g106D5 (j : Nat) : Nat := if j = 0 then 0x1a2047d01 else 0
def g106D6 (j : Nat) : Nat := if j = 0 then 0x7208f else 0
def g106L : Nat → Packing
  | 3 => (2, 3, 2, 0, 0, 5, 0, g106D3)
  | 4 => (3, 2, 2, 0, 0, 5, 0, g106D4)
  | 5 => (1, 1, 2, 0, 0, 1, 0, g106D5)
  | 6 => (1, 0, 2, 0, 0, 1, 0, g106D6)
  | _ => emptyPacking
def g106I : Nat → Nat → Option (Nat × Nat)
  | 4, tag => lookupShort 1 3 1 3 1 0 (fun j => if j=0 then 0x180 else 0) tag
  | 5, tag => lookupShort 4 16 3 7 2 3 (fun j => if j=0 then 0xd09c00c3940000081e004800000a00 else 0) tag
  | 6, tag => lookupShort 3 9 1 8 1 5 (fun j => if j=0 then 0x70600c00432d00621 else 0) tag
  | _, _ => none
def g106 : Forest := ⟨106, 6, fun i => (g106Y[i]?).getD (0,0), g106C, [[], [101], [83], [83, 101], [99, 101], [99], [49], [49, 101], [49, 83], [49, 83, 101], [49, 99, 101], [49, 99], [81, 83], [81, 83, 101], [81], [81, 101], [81, 99], [81, 99, 101], [97, 99, 101], [97, 99], [97, 101], [97], [97, 83, 101], [97, 83]], g106L, g106I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P3n0 : block g106 3 0 2 = true := by decide +kernel
theorem g106B3 : block g106 3 0 2 = true := g106P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P4n0 : block g106 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P4n2 : block g106 4 2 1 = true := by decide +kernel
theorem g106B4 : block g106 4 0 3 = true := (@block_merge g106 4 0 2 1 g106P4n0 g106P4n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P5n0 : block g106 5 0 1 = true := by decide +kernel
theorem g106B5 : block g106 5 0 1 = true := g106P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P6n0 : block g106 6 0 1 = true := by decide +kernel
theorem g106B6 : block g106 6 0 1 = true := g106P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106T : checkedTables g106 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g106 0 0 0 = true)
  · exact (rfl : block g106 1 0 0 = true)
  · exact (rfl : block g106 2 0 0 = true)
  · exact g106B3
  · exact g106B4
  · exact g106B5
  · exact g106B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106G : graphValid g106 (boundsBefore K105) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low106 : Lower true (varsX 106) (graphGoal 106) 7 := lower_forest (g:=g106) (i:=0) (hints:=17829936) (before_sound K105 V105) g106G g106T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K106 := extendKnown K105 7 [(106,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V106 : Known true K106 := extend_ok (m:=106) V105 low106 (by decide +kernel)

def g108Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0x5ab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6ad, 0xffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc0000000ffc00ffc00),
    (0x6cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36, 0xfffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff0000000000fffff00000),
    (0x0, 0x0),
    (0x7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7f1fc7, 0x70000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000003ff0000000000),
    (0xfe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8fe3f8, 0xffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000ffc000000000000)]
def g108C : List ColumnInfo := [(4,0,104,0,4)]
def g108D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g108L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g108D4)
  | _ => emptyPacking
def g108I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g108 : Forest := ⟨108, 4, fun i => (g108Y[i]?).getD (0,0), g108C, [[], [101], [50], [50, 101]], g108L, g108I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108P4n0 : block g108 4 0 1 = true := by decide +kernel
theorem g108B4 : block g108 4 0 1 = true := g108P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108T : checkedTables g108 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g108 0 0 0 = true)
  · exact (rfl : block g108 1 0 0 = true)
  · exact (rfl : block g108 2 0 0 = true)
  · exact (rfl : block g108 3 0 0 = true)
  · exact g108B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108G : graphValid g108 (boundsBefore K106) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low108 : Lower true (varsX 108) (graphGoal 108) 5 := lower_forest (g:=g108) (i:=0) (hints:=35673344) (before_sound K106 V106) g108G g108T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K108 := extendKnown K106 5 [(108,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V108 : Known true K108 := extend_ok (m:=108) V106 low108 (by decide +kernel)

def g47Y : Array (Bits × Bits) := #[(0x2dbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadbaaab6eaaadb, 0xfffffc00000fffffc0000000000000000fffffc0000000000000000fffffc00000fffffc0000000000000000fffffc0000000000000000fffffc00000fffffc00000),
    (0x36ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336ecccdbb3336e, 0xfffffc00000fffffffffff000000000000000000000000000000000fffffc00000fffffffffff000000000000000000000000000000000fffffc00000fffffffffff00000000000),
    (0x473f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73f0f1cfc3c73, 0xfffffffffff0000000000000000000000000003fffff00000000000fffffffffff0000000000000000000000000003fffff00000000000fffffffffff0000000000000000000000),
    (0x7cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07cff01f3fc07c, 0x7ff000000000000000000000000000000000000003ffffffffffffffff000000000000000000000000000000000000003ffffffffffffffff000000000000000000000000000000000),
    (0x0, 0x0),
    (0x780fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80fffe03fff80, 0xfffffc0000000000000000000000000000000000000000000000000fffffc0000000000000000000000000000000000000000000000000),
    (0x0, 0x0)]
def g47C : List ColumnInfo := [(1,0,46,0,5), (2,0,45,0,5), (4,0,43,0,5), (5,0,42,0,4), (8,0,39,0,5), (10,0,37,0,4)]
def g47D4 (j : Nat) : Nat := if j = 0 then 0x31825f63546049b899544066d6215101 else 0
def g47D5 (j : Nat) : Nat := if j = 0 then 0x202204002400800082088208045042db8ae568d01d2a2002faa3027b89504b712a097e15413f408825fd5101bf2a2037d54406f8a880fe41101 else 0
def g47D6 (j : Nat) : Nat := if j = 0 then 0x21d1080c864202ae21d1081101300fe04fd04fd01 else 0
def g47D7 (j : Nat) : Nat := if j = 0 then 0x2c68819f else 0
def g47L : Nat → Packing
  | 4 => (3, 3, 3, 0, 0, 4, 0, g47D4)
  | 5 => (10, 2, 3, 0, 0, 7, 0, g47D5)
  | 6 => (3, 1, 3, 0, 0, 7, 0, g47D6)
  | 7 => (1, 0, 3, 0, 0, 1, 0, g47D7)
  | _ => emptyPacking
def g47I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 3 11 1 6 2 2 (fun j => if j=0 then 0x1800001c0003208010 else 0) tag
  | 6, tag => lookupShort 8 27 2 8 4 2 (fun j => if j=0 then 0x4200c45600d000830046000000121388000060c10000450700c9d90484 else 0) tag
  | 7, tag => lookupShort 6 21 3 7 2 3 (fun j => if j=0 then 0x1148010e99435a6e00c3900000300200003e00 else 0) tag
  | _, _ => none
def g47 : Forest := ⟨47, 7, fun i => (g47Y[i]?).getD (0,0), g47C, [[], [49], [16, 50], [16, 33, 50], [32], [32, 49], [48, 49, 50], [48, 33]], g47L, g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P4n0 : block g47 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P4n2 : block g47 4 2 1 = true := by decide +kernel
theorem g47B4 : block g47 4 0 3 = true := (@block_merge g47 4 0 2 1 g47P4n0 g47P4n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5n0 : block g47 5 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5n2 : block g47 5 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5n4 : block g47 5 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5n6 : block g47 5 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5n8 : block g47 5 8 2 = true := by decide +kernel
theorem g47B5 : block g47 5 0 10 = true := (@block_merge g47 5 0 4 6 (@block_merge g47 5 0 2 2 g47P5n0 g47P5n2) (@block_merge g47 5 4 2 4 g47P5n4 (@block_merge g47 5 6 2 2 g47P5n6 g47P5n8)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6n0 : block g47 6 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6n2 : block g47 6 2 1 = true := by decide +kernel
theorem g47B6 : block g47 6 0 3 = true := (@block_merge g47 6 0 2 1 g47P6n0 g47P6n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P7n0 : block g47 7 0 1 = true := by decide +kernel
theorem g47B7 : block g47 7 0 1 = true := g47P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact g47B4
  · exact g47B5
  · exact g47B6
  · exact g47B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K108) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 8 := lower_forest (g:=g47) (i:=0) (hints:=4146) (before_sound K108 V108) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end MinorArchive82

namespace LiveAIG.FlatProjection
open FreeAIG
variable {B : Type*}

def read (σ : B → R) (w : W) : Fn B := fun x => w[(σ x).val]
def constant (f : Fn B) : Prop := ∃ b : Bool, f = (fun _ => b)
noncomputable def flat (σ : B → R) (w : W) : Bool := by
  classical
  exact decide (constant (read σ w))

theorem flat_spec (σ : B → R) (w : W) : flat σ w = true ↔ constant (read σ w) := by
  classical
  simp [flat]

theorem readSign (σ : B → R) (w : W) (b : Bool) :
    read σ (signed w b) = if b then neg (read σ w) else read σ w := by
  cases b <;> funext x <;> simp [signed,read,neg]

theorem readAnd (σ : B → R) (u v : W) : read σ (u &&& v) = meet (read σ u) (read σ v) := by
  funext x
  simp [read,meet]

theorem signAvail {σ : B → R} {w : W} {S : Set (Fn B)}
    (h : Avail S (read σ w)) (b : Bool) : Avail S (read σ (signed w b)) := by
  rw [readSign];cases b
  · exact h
  · exact .neg h

theorem flatSign {σ : B → R} {w : W} (b : Bool) (h : flat σ w=true) :
    flat σ (signed w b)=true := by
  obtain ⟨k,hk⟩ := (flat_spec _ _).mp h
  apply (flat_spec _ _).mpr
  rw [readSign,hk]
  cases b
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩

theorem countDrop (p : W → Bool) {s : List W} {w : W} (hw : w∈s) (keep : Bool) :
    s.countP p = (drop s w keep).countP p + (p w && !keep).toNat := by
  cases keep
  · have h := (List.perm_cons_erase hw).countP_eq p
    simpa [drop,List.countP_cons, Bool.toNat, Nat.add_comm] using h
  · simp [drop]

theorem contract {σ : B → R} {a b : W} (sa sb : Bool) {S : Set (Fn B)}
    (ha : Avail S (read σ a)) (hb : Avail S (read σ b))
    (cheap : flat σ a=true ∨ flat σ b=true) :
    Avail S (read σ (made a b sa sb)) := by
  apply signAvail
  rw [readAnd]
  rcases cheap with left|right
  · obtain ⟨k,hk⟩ := (flat_spec _ _).mp (flatSign sa left)
    rw [hk];cases k
    · rw [meetFalseL];exact .const false
    · rw [meetTrueL];exact signAvail hb _
  · obtain ⟨k,hk⟩ := (flat_spec _ _).mp (flatSign sb right)
    rw [hk];cases k
    · rw [meetFalseR];exact .const false
    · rw [meetTrueR];exact signAvail ha _

theorem bothFlat {σ : B → R} {a b : W} (sa sb : Bool) (ha : flat σ a=true)
    (hb : flat σ b=true) : flat σ (made a b sa sb)=true := by
  apply flatSign
  obtain ⟨i,hi⟩ := (flat_spec _ _).mp (flatSign sa ha)
  obtain ⟨j,hj⟩ := (flat_spec _ _).mp (flatSign sb hb)
  apply (flat_spec _ _).mpr
  rw [readAnd,hi,hj]
  exact ⟨_,rfl⟩

theorem saves (σ : B → R) {S : Set (Fn B)} {t : W} {s : List W} {n c : Nat}
    (run : Run t s n c) (proper : ¬constant (read σ t))
    (src : ∀ w∈s, Avail S (read σ w)) :
    ∃ k, k+s.countP (flat σ)≤n ∧ Has S k (read σ t) := by
  induction run generalizing S with
  | done =>
    have z : flat σ (norm t)=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have again := flatSign t[0] h
      rw [orient] at again
      exact proper ((flat_spec _ _).mp again)
    refine ⟨0,by simp [List.countP_cons,z],.done ?_⟩
    have v := signAvail (src (norm t) List.mem_cons_self) t[0]
    rwa [orient] at v
  | @gate s n c a b sa sb ka kb ha hb ne nz fresh tail ih =>
    let g := made a b sa sb
    let rest := drop (drop s a ka) b kb
    have old : ∀ w∈rest, w∈s := fun _ h=>dropSubset _ _ _ _ (dropSubset _ _ _ _ h)
    have ac := countDrop (flat σ) ha ka
    have bc := countDrop (flat σ) (rightStays hb ne ka) kb
    change (drop s a ka).countP (flat σ) = rest.countP (flat σ) + _ at bc
    have tally : (after s a b g ka kb).countP (flat σ) = rest.countP (flat σ) + (flat σ g).toNat := by
      simp [after,rest,List.countP_cons,Bool.toNat]
    by_cases cheap : flat σ a=true ∨ flat σ b=true
    · obtain ⟨k,sz,r⟩ := ih (S:=S) (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl|hv
        · exact contract sa sb (src a ha) (src b hb) cheap
        · exact src w (old w hv))
      change k+(after s a b g ka kb).countP (flat σ)≤n at sz
      rw [tally] at sz
      refine ⟨k,?_,r⟩
      have both : flat σ a=true → flat σ b=true → flat σ g=true := bothFlat sa sb
      cases aa : flat σ a <;> cases bb : flat σ b <;> cases ka <;> cases kb <;>
        simp_all only [Bool.and_true,Bool.and_false,Bool.not_false,Bool.not_true,Bool.true_and,Bool.false_and,Bool.toNat_true,Bool.toNat_false] <;> omega
    · let u := signed a sa
      let v := signed b sb
      let H := meet (read σ u) (read σ v)
      obtain ⟨k,sz,r⟩ := ih (S:=insert H S) (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl|hv
        · apply signAvail
          rw [readAnd]
          exact .src (Set.mem_insert _ _)
        · exact (src w (old w hv)).extend)
      change k+(after s a b g ka kb).countP (flat σ)≤n at sz
      rw [tally] at sz
      have af : flat σ a = false := Bool.eq_false_iff.mpr (fun h=>cheap (.inl h))
      have bf : flat σ b = false := Bool.eq_false_iff.mpr (fun h=>cheap (.inr h))
      refine ⟨k+1,?_,.step (signAvail (src _ ha) sa) (signAvail (src _ hb) sb) r⟩
      simp [af,bf] at ac bc
      omega
end LiveAIG.FlatProjection

namespace LiveAIG.MinorTransfer
open MinorArchive82
open FreeAIG
private theorem offer {B : Type} {S : Set (Fn B)} {pool : List (Wire B)} {f : Fn B}
    (ha : Avail S f) (supply : ∀ g∈S,Available true pool g) : Available true pool f := by
  induction ha with
  | src h => exact supply _ h
  | const b => exact .inr (.inl ⟨b,rfl⟩)
  | @neg g _ ih =>
    rcases ih with mem | ⟨b,hb⟩ | ⟨_,mem⟩
    · apply Or.inr;right;refine ⟨rfl,?_⟩
      have double : inv (FreeAIG.neg g) = g := by funext x;simp [inv,FreeAIG.neg]
      rwa [double]
    · subst g;exact .inr (.inl ⟨!b,rfl⟩)
    · exact .inl mem

private theorem extendReach {B : Type} {S : Set (Fn B)} {roots bank : List (Wire B)} {j k : Nat}
    {f : Fn B} (h : Has S k f) (p : Reach true roots j bank)
    (supply : ∀ g∈S, Available true bank g) :
    ∃ z ≤ j+k, ∃ out, Reach true roots z out ∧ Available true out f := by
  induction h generalizing j bank with
  | done hf => exact ⟨_,by omega,_,p,offer hf supply⟩
  | @step S k a b f ha hb tail ih =>
    have step := Reach.two false p (offer ha supply) (offer hb supply)
    obtain ⟨z,le,out,rep,av⟩ := ih step (by
      rintro g (rfl|hg)
      · exact .inl List.mem_cons_self
      · rcases supply g hg with m|con|⟨h,m⟩
        · exact .inl (List.mem_cons_of_mem _ m)
        · exact .inr (.inl con)
        · exact .inr (.inr ⟨h,List.mem_cons_of_mem _ m⟩))
    exact ⟨z,by omega,out,rep,av⟩

theorem imported {roots : List Sig} {T : Sig} {L : Nat} (bound : Lower true roots T L)
    {k : Nat} (run : Has {g | g∈roots.map observe} k (observe T)) : L≤k := by
  obtain ⟨z,le,out,r,h⟩ := extendReach (j:=0) run
    (Reach.start (roots:=roots.map observe)) (fun _ mem=>Or.inl mem)
  exact (bound _ _ r h).trans (by omega)

end LiveAIG.MinorTransfer

namespace LiveAIG.MinorTransfer
open MinorArchive82
open FlatProjection FreeAIG

def scatter (codes : List Nat) (r : Row) : R :=
  Fin.ofNat 128 ((codes.zipIdx).foldl (fun a p =>
    let i := p.1
    let v := if i<2 then i==1 else (r.val.testBit (i/2-1)) != (i % 2==1)
    if v then a+2^p.2 else a) 0)

def flatWord (q : Sig) := q==zero || q==one
def cheapWord (roots : List Sig) (q : Sig) :=
  flatWord q || roots.contains q || roots.contains (MinorArchive82.neg q)

private theorem oneBit (i : Row) : bit i one=true := by
  unfold bit one
  rw [BitVec.getLsbD_allOnes]
  simp

theorem flatWordSound {q : Sig} (h : flatWord q=true) : constant (observe q) := by
  simp only [flatWord,Bool.or_eq_true,beq_iff_eq] at h
  rcases h with rfl|rfl
  · refine ⟨false,?_⟩;funext i;simp [observe,bit,zero]
  · refine ⟨true,?_⟩;funext i;exact oneBit i

theorem cheapWordSound {roots : List Sig} {q : Sig} (h : cheapWord roots q=true) :
    Avail {g | g∈roots.map observe} (observe q) := by
  simp only [cheapWord,Bool.or_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  rcases h with (hc|hm)|hn
  · obtain ⟨b,e⟩:=flatWordSound hc
    rw [e];exact .const b
  · exact .src (List.mem_map_of_mem hm)
  · have e : FreeAIG.neg (observe (MinorArchive82.neg q)) = observe q := by
      rw [obs_neg];funext x;simp [FreeAIG.neg,inv]
    exact e ▸ Avail.neg (Avail.src (List.mem_map_of_mem hn))

def wordImage (σ : Row→R) (w : W) : Sig := table (read σ w)
def usable (σ : Row→R) (t : W) (s : List W) (roots : List Sig) (T : Sig) (L max : Nat) : Bool :=
  wordImage σ t == T && !flatWord T &&
    s.all (fun w=>cheapWord roots (wordImage σ w)) &&
    decide (max < L+s.countP (fun w=>flatWord (wordImage σ w)))

theorem excludes {σ : Row→R} {t : W} {s : List W} {roots : List Sig} {T : Sig} {L max n c : Nat}
    (bound : Lower true roots T L) (test : usable σ t s roots T L max=true) (small : n ≤ max) :
    ¬ Run t s n c := by
  intro run
  simp only [usable,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',List.all_eq_true,
    decide_eq_true_eq] at test
  obtain ⟨⟨⟨eq,proper⟩,src⟩,limit⟩:=test
  have idn (w : W) : observe (wordImage σ w)=read σ w := observe_table _
  have targetEq : read σ t=observe T := (idn t).symm.trans (congrArg observe eq)
  have nc : ¬constant (read σ t) := by
    rw [targetEq]
    rintro ⟨b,hb⟩
    have wrong : flatWord T=true := by
      cases b
      · have e : T=zero := bit_ext (fun i=>by
          have v:=congrFun hb i
          simpa [observe,bit,zero] using v)
        simp [flatWord,e]
      · have e : T=one := bit_ext (fun i=>by
          have v:=congrFun hb i
          exact v.trans (oneBit i).symm)
        simp [flatWord,e]
    simp_all
  obtain ⟨k,sp,hk⟩:=saves σ run nc (S:={g | g∈roots.map observe}) (by
    intro w hw
    rw [←idn w]
    exact cheapWordSound (src w hw))
  have lower:=imported bound (targetEq ▸ hk)
  have count : s.countP (fun w=>flatWord (wordImage σ w)) ≤ s.countP (flat σ) :=
    List.countP_mono_left (fun w _ h=> (flat_spec _ _).mpr (idn w ▸ flatWordSound h))
  omega
end LiveAIG.MinorTransfer

namespace LiveAIG.MinorTransfer
open MinorArchive82
open FlatProjection
structure Lens (t : W) where
  σ : Row → R
  roots : List Sig
  goal : Sig
  cost : Nat
  target : read σ t=observe goal
  proper : flatWord goal=false
  bound : Lower true roots goal cost

theorem observation {σ : Row→R} {w : W} {q : Sig} (e : wordImage σ w=q) : read σ w=observe q :=
  (observe_table _).symm.trans (congrArg observe e)
end LiveAIG.MinorTransfer

namespace LiveAIG.MinorTransfer
open MinorArchive82
open FlatProjection

structure Rule where
  off : W
  onMask : W
  image : Sig

def Rule.covers (σ : Row→R) (rule : Rule) : Bool :=
  (List.finRange 512).all fun r=>
    (if bit r rule.image then rule.onMask else rule.off)[(σ r).val]

def Rule.fits (rule : Rule) (w : W) : Bool :=
  (w &&& rule.off)==0 && ((~~~w) &&& rule.onMask)==0

theorem Rule.sound {σ : Row→R} {z : Rule} (h : z.covers σ=true) {w : W} (m : z.fits w=true) :
    read σ w=observe z.image := by
  funext r
  have seen := List.all_eq_true.mp h r (List.mem_finRange r)
  simp only [Rule.fits,Bool.and_eq_true,beq_iff_eq] at m
  have lo:=congrArg (fun a : W=>a[(σ r).val]) m.1
  have hi:=congrArg (fun a : W=>a[(σ r).val]) m.2
  simp only [BitVec.getElem_and,BitVec.getElem_not,BitVec.getElem_zero] at lo hi
  change w[(σ r).val]=bit r z.image
  cases v:bit r z.image <;> simp [v] at seen <;> simp_all

def selectImage (rules : List Rule) (w : W) : Sig :=
  ((rules.find? (fun z=>z.fits w)).map Rule.image).getD zero
def scanned (rules : List Rule) (w : W) := rules.any (fun z=>z.fits w)

theorem imageOfScan {σ : Row→R} {rules : List Rule}
    (ok : rules.all (Rule.covers σ)=true) {w : W} (h : scanned rules w=true) :
    read σ w=observe (selectImage rules w) := by
  induction rules with
  | nil=>simp [scanned] at h
  | cons z zs ih=>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    cases m:z.fits w
    · exact (by simpa [selectImage,m] using ih ok.2 (by simpa [scanned,m] using h))
    · simpa [selectImage,m] using Rule.sound ok.1 m

structure MaskLens (t : W) where
  lens : Lens t
  rules : List Rule
  ok : rules.all (Rule.covers lens.σ)=true

def MaskLens.reject {t : W} (p : MaskLens t) (s : List W) (budget : Nat) :=
  s.all (scanned p.rules) && s.all (fun w=>cheapWord p.lens.roots (selectImage p.rules w)) &&
    decide (s.length+budget < 1+p.lens.cost+s.countP (fun w=>flatWord (selectImage p.rules w)))

theorem MaskLens.noRun {t : W} {s : List W} {budget n c : Nat}
    (p : MaskLens t) (cert : p.reject s budget=true) (cap : c≤budget) : ¬Run t s n c := by
  intro run
  simp only [MaskLens.reject,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at cert
  have eq (w : W) (hw:w∈s) : wordImage p.lens.σ w=selectImage p.rules w :=
    bit_ext (fun i=>(bit_table _ i).trans (congrFun (imageOfScan p.ok (cert.1.1 w hw)) i))
  have cnt : s.countP (fun w=>flatWord (wordImage p.lens.σ w))=s.countP (fun w=>flatWord (selectImage p.rules w)) :=
    List.countP_congr (fun w hw=>by rw [eq w hw])
  apply excludes (σ:=p.lens.σ) p.lens.bound (max:=n) _ (Nat.le_refl _) run
  have targetEq : wordImage p.lens.σ t=p.lens.goal :=
    bit_ext (fun i=>(bit_table _ i).trans (congrFun p.lens.target i))
  simp only [usable,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,decide_eq_true_eq]
  refine ⟨⟨⟨targetEq,by simp [p.lens.proper]⟩,?_⟩,?_⟩
  · intro w hw;rw [eq w hw];exact cert.1.2 w hw
  · rw [cnt]
    have len:=balance run
    omega
end LiveAIG.MinorTransfer

namespace LiveAIG.Row11246.Projection
open MinorTransfer
open MinorArchive82
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def lens0 : Lens t where
  σ := scatter [2, 0, 4, 6, 0, 8, 12]
  roots := varsX 47
  goal := graphGoal 47
  cost := 8
  target := observation (by decide +kernel)
  proper := by decide +kernel
  bound := low47
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def rules0 : List Rule := [⟨0x3333000033330000333300003333, 0x0, 0x0⟩,
⟨0x0, 0x3333000033330000333300003333, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩,
⟨0x1111000011110000111100001111, 0x2222000022220000222200002222, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩,
⟨0x303000003030000030300000303, 0x3030000030300000303000003030, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc⟩,
⟨0x33000000330000003300000033, 0x3300000033000000330000003300, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩,
⟨0x33330000000000003333, 0x3333000000000000333300000000, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩,
⟨0x333300003333, 0x3333000033330000000000000000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩,
⟨0x2222000022220000222200002222, 0x1111000011110000111100001111, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩,
⟨0x3030000030300000303000003030, 0x303000003030000030300000303, 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333⟩,
⟨0x3300000033000000330000003300, 0x33000000330000003300000033, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩,
⟨0x3333000000000000333300000000, 0x33330000000000003333, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩,
⟨0x3333000033330000000000000000, 0x333300003333, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def p0 : MaskLens t where
  lens := lens0
  rules := rules0
  ok := by decide +kernel
end LiveAIG.Row11246.Projection

namespace LiveAIG.Row11246.Projection
open MinorTransfer
open MinorArchive82
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def lens1 : Lens t where
  σ := scatter [2, 0, 4, 6, 12, 8, 12]
  roots := varsX 47
  goal := graphGoal 47
  cost := 8
  target := observation (by decide +kernel)
  proper := by decide +kernel
  bound := low47
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def rules1 : List Rule := [⟨0x33330000333300000000333300003333, 0x0, 0x0⟩,
⟨0x0, 0x33330000333300000000333300003333, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩,
⟨0x11110000111100000000111100001111, 0x22220000222200000000222200002222, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩,
⟨0x3030000030300000000030300000303, 0x30300000303000000000303000003030, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc⟩,
⟨0x330000003300000000003300000033, 0x33000000330000000000330000003300, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩,
⟨0x333300000000000000003333, 0x33330000000000000000333300000000, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩,
⟨0x333300003333, 0x33330000333300000000000000000000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩,
⟨0x22220000222200000000222200002222, 0x11110000111100000000111100001111, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩,
⟨0x30300000303000000000303000003030, 0x3030000030300000000030300000303, 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333⟩,
⟨0x33000000330000000000330000003300, 0x330000003300000000003300000033, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩,
⟨0x33330000000000000000333300000000, 0x333300000000000000003333, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩,
⟨0x33330000333300000000000000000000, 0x333300003333, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def p1 : MaskLens t where
  lens := lens1
  rules := rules1
  ok := by decide +kernel
end LiveAIG.Row11246.Projection

namespace LiveAIG.Row11246.Projection
open MinorTransfer
open MinorArchive82
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def lens2 : Lens t where
  σ := scatter [2, 0, 4, 6, 3, 8, 12]
  roots := varsX 47
  goal := graphGoal 47
  cost := 8
  target := observation (by decide +kernel)
  proper := by decide +kernel
  bound := low47
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def rules2 : List Rule := [⟨0x11112222111122221111222211112222, 0x0, 0x0⟩,
⟨0x0, 0x11112222111122221111222211112222, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩,
⟨0x11110000111100001111000011110000, 0x2222000022220000222200002222, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩,
⟨0x1010202010102020101020201010202, 0x10102020101020201010202010102020, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc⟩,
⟨0x110022001100220011002200110022, 0x11002200110022001100220011002200, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩,
⟨0x111122220000000011112222, 0x11112222000000001111222200000000, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩,
⟨0x1111222211112222, 0x11112222111122220000000000000000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩,
⟨0x2222000022220000222200002222, 0x11110000111100001111000011110000, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩,
⟨0x10102020101020201010202010102020, 0x1010202010102020101020201010202, 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333⟩,
⟨0x11002200110022001100220011002200, 0x110022001100220011002200110022, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩,
⟨0x11112222000000001111222200000000, 0x111122220000000011112222, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩,
⟨0x11112222111122220000000000000000, 0x1111222211112222, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def p2 : MaskLens t where
  lens := lens2
  rules := rules2
  ok := by decide +kernel
end LiveAIG.Row11246.Projection

namespace LiveAIG.Row11246.Projection
open MinorTransfer
open MinorArchive82
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def lens3 : Lens t where
  σ := scatter [2, 0, 4, 6, 6, 8, 12]
  roots := varsX 47
  goal := graphGoal 47
  cost := 8
  target := observation (by decide +kernel)
  proper := by decide +kernel
  bound := low47
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def rules3 : List Rule := [⟨0x33000033330000333300003333000033, 0x0, 0x0⟩,
⟨0x0, 0x33000033330000333300003333000033, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩,
⟨0x11000011110000111100001111000011, 0x22000022220000222200002222000022, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩,
⟨0x3000003030000030300000303000003, 0x30000030300000303000003030000030, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc⟩,
⟨0x33000000330000003300000033, 0x33000000330000003300000033000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩,
⟨0x330000330000000033000033, 0x33000033000000003300003300000000, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩,
⟨0x3300003333000033, 0x33000033330000330000000000000000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩,
⟨0x22000022220000222200002222000022, 0x11000011110000111100001111000011, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩,
⟨0x30000030300000303000003030000030, 0x3000003030000030300000303000003, 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333⟩,
⟨0x33000000330000003300000033000000, 0x33000000330000003300000033, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩,
⟨0x33000033000000003300003300000000, 0x330000330000000033000033, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩,
⟨0x33000033330000330000000000000000, 0x3300003333000033, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def p3 : MaskLens t where
  lens := lens3
  rules := rules3
  ok := by decide +kernel
end LiveAIG.Row11246.Projection

namespace LiveAIG.Row11246.Projection
open MinorTransfer
open MinorArchive82
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def lens4 : Lens t where
  σ := scatter [2, 4, 0, 6, 0, 8, 12]
  roots := varsX 47
  goal := graphGoal 47
  cost := 8
  target := observation (by decide +kernel)
  proper := by decide +kernel
  bound := low47
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def rules4 : List Rule := [⟨0xf0f00000f0f00000f0f00000f0f, 0x0, 0x0⟩,
⟨0x0, 0xf0f00000f0f00000f0f00000f0f, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩,
⟨0x505000005050000050500000505, 0xa0a00000a0a00000a0a00000a0a, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩,
⟨0x303000003030000030300000303, 0xc0c00000c0c00000c0c00000c0c, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc⟩,
⟨0xf0000000f0000000f0000000f, 0xf0000000f0000000f0000000f00, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩,
⟨0xf0f0000000000000f0f, 0xf0f0000000000000f0f00000000, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩,
⟨0xf0f00000f0f, 0xf0f00000f0f0000000000000000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩,
⟨0xa0a00000a0a00000a0a00000a0a, 0x505000005050000050500000505, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩,
⟨0xc0c00000c0c00000c0c00000c0c, 0x303000003030000030300000303, 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333⟩,
⟨0xf0000000f0000000f0000000f00, 0xf0000000f0000000f0000000f, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩,
⟨0xf0f0000000000000f0f00000000, 0xf0f0000000000000f0f, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩,
⟨0xf0f00000f0f0000000000000000, 0xf0f00000f0f, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def p4 : MaskLens t where
  lens := lens4
  rules := rules4
  ok := by decide +kernel
end LiveAIG.Row11246.Projection

namespace LiveAIG.Row11246.Projection
open MinorTransfer
open MinorArchive82
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def lens5 : Lens t where
  σ := scatter [2, 4, 0, 6, 12, 8, 12]
  roots := varsX 47
  goal := graphGoal 47
  cost := 8
  target := observation (by decide +kernel)
  proper := by decide +kernel
  bound := low47
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def rules5 : List Rule := [⟨0xf0f00000f0f000000000f0f00000f0f, 0x0, 0x0⟩,
⟨0x0, 0xf0f00000f0f000000000f0f00000f0f, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩,
⟨0x5050000050500000000050500000505, 0xa0a00000a0a000000000a0a00000a0a, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩,
⟨0x3030000030300000000030300000303, 0xc0c00000c0c000000000c0c00000c0c, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc⟩,
⟨0xf0000000f00000000000f0000000f, 0xf0000000f00000000000f0000000f00, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩,
⟨0xf0f00000000000000000f0f, 0xf0f00000000000000000f0f00000000, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00⟩,
⟨0xf0f00000f0f, 0xf0f00000f0f00000000000000000000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩,
⟨0xa0a00000a0a000000000a0a00000a0a, 0x5050000050500000000050500000505, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩,
⟨0xc0c00000c0c000000000c0c00000c0c, 0x3030000030300000000030300000303, 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333⟩,
⟨0xf0000000f00000000000f0000000f00, 0xf0000000f00000000000f0000000f, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩,
⟨0xf0f00000000000000000f0f00000000, 0xf0f00000000000000000f0f, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff⟩,
⟨0xf0f00000f0f00000000000000000000, 0xf0f00000f0f, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def p5 : MaskLens t where
  lens := lens5
  rules := rules5
  ok := by decide +kernel
end LiveAIG.Row11246.Projection

namespace LiveAIG.Row11246.Projection
open MinorTransfer
open MinorArchive82
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def lens8 : Lens t where
  σ := scatter [0, 2, 6, 0, 6, 12, 14]
  roots := varsX 101
  goal := graphGoal 101
  cost := 7
  target := observation (by decide +kernel)
  proper := by decide +kernel
  bound := low101
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def rules8 : List Rule := [⟨0x500005005000050050000500500005, 0x0, 0x0⟩,
⟨0x0, 0x500005005000050050000500500005, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩,
⟨0x100001001000010010000100100001, 0x400004004000040040000400400004, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa⟩,
⟨0x5000000050000000500000005, 0x500000005000000050000000500000, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0⟩,
⟨0x5000050000000000500005, 0x500005000000000050000500000000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000⟩,
⟨0x50000500500005, 0x500005005000050000000000000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000⟩,
⟨0x400004004000040040000400400004, 0x100001001000010010000100100001, 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555⟩,
⟨0x500000005000000050000000500000, 0x5000000050000000500000005, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f⟩,
⟨0x500005000000000050000500000000, 0x5000050000000000500005, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff⟩,
⟨0x500005005000050000000000000000, 0x50000500500005, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff⟩]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def p8 : MaskLens t where
  lens := lens8
  rules := rules8
  ok := by decide +kernel
end LiveAIG.Row11246.Projection

namespace LiveAIG.TableHybrid
open MinorTransfer Layers
open Row11246.Projection
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def maskAt : Nat → MaskLens target
  | 1 => p1
  | 2 => p2
  | 3 => p3
  | 4 => p4
  | 5 => p5
  | 8 => p8
  | _ => p0
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def testMask (p : Nat×Nat) := (maskAt p.2).reject (pool p.1).1 (pool p.1).2
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem testMaskSound {b : Array Nat} {rows : List (Nat×Nat)}
    (complete : rows.map Prod.fst=b.toList) (checked : rows.all testMask=true) :
    ∀m∈b.toList, Dead target (pool m) := by
  intro m mem
  rw [←complete] at mem
  obtain ⟨p,hm,rfl⟩:=List.mem_map.mp mem
  intro n d budget
  exact (maskAt p.2).noRun (List.all_eq_true.mp checked p hm) budget
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile0 := projectBlock0.toList.zip [8, 0, 4, 8, 0, 8, 0, 4, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 4, 0, 4, 0, 4, 0, 4, 4, 0, 0, 0, 0, 0, 0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample0 : ∀m∈projectBlock0.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile0) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile1 := projectBlock1.toList.zip [0, 4, 8, 0, 0, 4, 8, 0, 8, 8, 0, 0, 0, 0, 0, 0, 4, 0, 4, 4, 4, 0, 0, 8, 8, 8, 0, 4, 0, 0, 0, 0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample1 : ∀m∈projectBlock1.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile1) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile2 := projectBlock2.toList.zip [0, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 8, 0, 4, 8, 0, 0, 4, 8, 0, 4, 0, 0, 4, 8, 0, 8, 8, 8, 8, 8, 8]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample2 : ∀m∈projectBlock2.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile2) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile3 := projectBlock3.toList.zip [0, 0, 4, 4, 8, 8, 8, 8, 8, 8, 0, 0, 1, 8, 0, 4, 0, 0, 4, 8, 0, 8, 8, 8, 8, 8, 8, 8, 0, 0, 0, 4]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample3 : ∀m∈projectBlock3.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile3) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile4 := projectBlock4.toList.zip [4, 4, 8, 8, 8, 8, 8, 8, 8, 0, 0, 1, 2, 1, 8, 8, 1, 2, 2, 8, 8, 8, 8, 8, 8, 8, 0, 0, 0, 4, 4, 4]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample4 : ∀m∈projectBlock4.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile4) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile5 := projectBlock5.toList.zip [0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 8, 8, 0, 4, 8, 8, 4, 4, 4, 0, 8, 8, 0, 0, 8, 8, 0, 0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample5 : ∀m∈projectBlock5.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile5) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile6 := projectBlock6.toList.zip [0, 0, 0, 0, 4, 4, 4, 8, 8, 8, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 0, 0, 4, 4, 4, 8, 8, 8, 8, 8]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample6 : ∀m∈projectBlock6.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile6) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile7 := projectBlock7.toList.zip [0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample7 : ∀m∈projectBlock7.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile7) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile8 := projectBlock8.toList.zip [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample8 : ∀m∈projectBlock8.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile8) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile9 := projectBlock9.toList.zip [8, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 8, 8, 8, 1, 2, 8, 8, 8, 2, 8, 8, 0, 4, 0, 4, 0, 4]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample9 : ∀m∈projectBlock9.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile9) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile10 := projectBlock10.toList.zip [8, 8, 0, 0, 8, 0, 4, 8, 0, 0, 0, 8, 0, 0, 4, 0, 8, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 4, 4]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample10 : ∀m∈projectBlock10.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile10) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile11 := projectBlock11.toList.zip [8, 0, 4, 0, 4, 0, 0, 4, 8, 0, 8, 8, 0, 0, 0, 1, 0, 0, 4, 4, 5, 4, 8, 0, 0, 0, 0, 2, 2, 0, 4, 0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample11 : ∀m∈projectBlock11.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile11) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile12 := projectBlock12.toList.zip [8, 4, 4, 4, 4, 4, 0, 0, 0, 0, 1, 1, 2, 1, 1, 0, 1, 0, 0, 0, 0, 4, 4, 4, 0, 8, 2, 2, 0, 0, 0, 8]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample12 : ∀m∈projectBlock12.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile12) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile13 := projectBlock13.toList.zip [0, 0, 8, 4, 8, 8, 8, 8, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 0, 4, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample13 : ∀m∈projectBlock13.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile13) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile14 := projectBlock14.toList.zip [0, 0, 4, 8, 0, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8, 0, 0, 0, 0, 8, 8, 8, 8, 8, 3, 0, 0, 0, 0, 0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample14 : ∀m∈projectBlock14.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile14) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile15 := projectBlock15.toList.zip [0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 8, 0, 4, 8, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample15 : ∀m∈projectBlock15.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile15) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile16 := projectBlock16.toList.zip [2, 1, 2, 1, 1, 1, 1, 1, 0, 0, 0, 0, 4, 4, 0, 0, 0, 1, 1, 2, 1, 1, 2, 0, 0, 8, 4, 4, 0, 3, 4, 0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample16 : ∀m∈projectBlock16.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile16) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def profile17 := projectBlock17.toList.zip [0, 1, 0]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem sample17 : ∀m∈projectBlock17.toList, Dead target (pool m) :=
  testMaskSound (rows:=profile17) (by decide +kernel) (by decide +kernel)
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
open Layers
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem projectionSound {i m} (member : lookup projectionMetas i=some m) : Dead target (pool m) := by
  have all : ∀i m, lookup projectionMetas i=some m → Dead target (pool m) := by
    apply lookGroup
    intro group belongs
    change group∈[projectBlock0,projectBlock1,projectBlock2,projectBlock3,projectBlock4,projectBlock5,projectBlock6,projectBlock7,projectBlock8,projectBlock9,projectBlock10,projectBlock11,projectBlock12,projectBlock13,projectBlock14,projectBlock15,projectBlock16,projectBlock17] at belongs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at belongs
    rcases belongs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact sample0
    · exact sample1
    · exact sample2
    · exact sample3
    · exact sample4
    · exact sample5
    · exact sample6
    · exact sample7
    · exact sample8
    · exact sample9
    · exact sample10
    · exact sample11
    · exact sample12
    · exact sample13
    · exact sample14
    · exact sample15
    · exact sample16
    · exact sample17
  intro k d bd
  exact all i m member (k:=k) (d:=d) bd
end LiveAIG.TableHybrid

namespace LiveAIG.TableHybrid
theorem noTen {n c : Nat} (_small : n≤10) (budget : c≤4) : ¬Run Row11246.t inputs n c := by
  have table := level0 @projectionSound 0 1020 (by decide +kernel) (k:=n) (d:=c)
  have same : (pool 1020).1=inputs := by decide +kernel
  rw [←same]
  exact table (by exact budget)
end LiveAIG.TableHybrid

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

namespace OneNot11246
open LiveAIG

def NoTen := ∀ {n c : Nat}, n ≤ 10 → c ≤ 4 → ¬Run Row11246.t inputs n c

theorem finish (imp : NoTen) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : oneNot C.gates) (ok : fits C) : Replacement C := by
  by_cases has : ∃ g ∈ C.gates, g.op = .not
  · have a := FreeAIG.circuitAIG (n := 7) C legal.1
    rw [funext ok] at a
    have le := FreeAIG.notDiscount has
    apply large
    by_contra! h
    obtain ⟨n, small, c, budget, run, _⟩ := Row11246.ifTen a (by omega)
    exact imp small budget run
  · exact noNot C legal ok (by simpa using has)

theorem positive (imp : NoTen) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal atMostOne ok
  obtain ⟨D, allowed, size, represented⟩ :=
    finish imp ⟨gs,o⟩ ⟨legal,atMostOne⟩ ok
  exact ⟨D.gates,D.output,allowed,size,represented⟩
end OneNot11246

end PEqualNP.Outside.L_meta_11245

theorem PEqualNP.Outside.L_meta_11245 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_11245.OneNot11246.positive (PEqualNP.Outside.L_meta_11245.LiveAIG.TableHybrid.noTen)
