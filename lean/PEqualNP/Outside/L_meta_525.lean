import Mathlib
import PEqualNP.Defs
-- Adapted from the live-set circuit search of IanAbusamra in PR 532.
-- The sample assignments and bounded search below are for the eight-cycle with one leaf.
namespace PEqualNP.Outside.G525

abbrev B := BitVec 410
abbrev Sig := B × B
def top : B := BitVec.allOnes 410
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  g != zero && g != one && !(v.contains g) &&
    (let d := decide (0<t)
     let base := sep d g ||| unionSep d rest
     keep.any (fun h => decide (rest.length+h.length+1 ≤ k-t+1) &&
       (base ||| unionSep d h == top) && r (g::(h++rest))))

def before (a b : Sig) : Bool :=
  if a.1 = b.1 then decide (a.2.toNat < b.2.toNat) else decide (a.1.toNat < b.1.toNat)


def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (a : Sig) : Bool :=
  tryGate k t r v (dropped [a] v) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  v.any (unaryAt k t r v)

def binaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (a b : Sig) : Bool :=
  before a b &&
    (let rest := dropped [a,b] v
     let keep := [[],[a],[b],[a,b]]
     tryGate k t r v rest (bin false a b) keep || tryGate k t r v rest (bin true a b) keep)

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  v.any (fun a => v.any (binaryAt k t r v a))

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v.contains target
  | k+1,t,v =>
    if t>k+1 ∨ v.length>k+1-t+1 then false else
    v.contains target ||
    (decide (0<t) && unaryMoves k (t-1) (search k (t-1)) v) ||
    binaryMoves k t (search k t) v

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



def raw0 : Sig := (495444318637521457311345694719344085380287537853294990055335384703160966530748999507550732400156628661530158702591,1232614707404978357017308729232472708554685113511866436199050060449939024921780299529112689264001085)
def raw1 : Sig := (1503853595553788566289729002134605862868023110492426816827539819249472709715466356475573949904569404314496100745239714594815,1503853595476756296182782810506649368355572161098642602166125588944846703420464233683472499477154986406609993279352117670594)
def raw2 : Sig := (392562743809574866207384041416042709828761204966734565025531360880151586684652537312495640986946749962569860860045149855744,392562740077117127428054256173636005894603877281110621223931663147614682002213536800265595599358709156785090144524302601508)
def raw3 : Sig := (1984379286425248495892850918327260896138131295338858906725546911617739932208428773595527689813188690719835730594463360221184,1984379285805683587080350863447226518033280774064760550001890409361949553056974678481349247004015642147861407824342590099544)
def raw4 : Sig := (81342127103490252786723985578381462375555927148140926093132686878771053984175157985167999372381383047403929750706644320256,81340974594057474621631909739289252272804141962962380079748833418764776538972461968240327861562591020905376913104030664608)
def raw5 : Sig := (2561593139921601794938923096916839290598448104414511171328569001695154955721019000022962245604860878003428492687140232101888,2561593036491335525007916108159049376326385327936000109713801106746777032355062120667152070944710042291659244387546265917452)
def raw6 : Sig := (2644222614296796115771323671165256579221486650006723085994455856283685374997365594579775998957538831005255176559802594623488,27543578411527601144610532884402207347790721762946541422552821078106657855061911225601677416194056699484101271624972370416)
def raw7 : Sig := (2644223875160994391220664000150941136091976941368743084782781398184631902472909605830857462574717347958920193809131459575808,2616680296749466794472112459959336744297674889709910905763136193820612046891359949157471681148615873794778721391152830881280)
def raw8 : Sig := (2644223875160994395807661232131084159313618731741332787901278985674052179936557475447486857093220575350907264092180303577088,2644223875160994395807659999516376754335261714434471347404244590809096468326882235814815600339863987710414350662395728764864)

def raw : List Sig := [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8]

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U))

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 410
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 410 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 410
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 410 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 410)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 410) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 410 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 410)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩

private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  simp only [tryGate,Bool.and_eq_true,bne_iff_ne,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not,
    List.any_eq_true,decide_eq_true_eq,beq_iff_eq]
  exact ⟨⟨⟨hp.1,hp.2⟩,ha⟩,h,hh,⟨hl,cov⟩,hr⟩

private lemma ordered {a b : Sig} (h : a≠b) : before a b = true ∨ before b a = true := by
  by_cases e : a.1=b.1
  · have h2 : a.2.toNat≠b.2.toNat := fun h2 => h (Prod.ext e (BitVec.eq_of_toNat_eq h2))
    simp [before,e]; omega
  · have h1 : a.1.toNat≠b.1.toNat := fun h1 => e (BitVec.eq_of_toNat_eq h1)
    simp [before,e,Ne.symm e]; omega

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (l : Live m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → search k t v = true) :
    unaryMoves k t (search k t) v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  exact List.any_eq_true.mpr ⟨a,ah,gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (ord : before a b=true) (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → search k t v = true) :
    binaryMoves k t (search k t) v = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have ok := gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)
  apply List.any_eq_true.mpr
  refine ⟨a,ah,List.any_eq_true.mpr ⟨b,bh,Bool.and_eq_true_iff.mpr ⟨ord,?_⟩⟩⟩
  cases d
  · exact Bool.or_eq_true_iff.mpr (Or.inl ok)
  · exact Bool.or_eq_true_iff.mpr (Or.inr ok)

private lemma search_complete {m t S} (l : Live m t S) (K : Nat) (hle : m ≤ K)
    (v : List Sig) (hv : v.Nodup) (he : v.toFinset=S) : search K t v = true := by
  have size := live_size l
  rw [←he,List.toFinset_card_of_nodup hv] at size
  induction l generalizing K v with
  | stop =>
    have ht : v.contains target = true := List.contains_iff_mem.mpr (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
    cases K with
    | zero => exact ht
    | succ k =>
      rw [search,if_neg (by omega),ht]
      rfl
  | @unary m t U a ha hf tail ih =>
    cases K with
    | zero => omega
    | succ k =>
      rw [search,if_neg (by omega)]
      apply Bool.or_eq_true_iff.mpr; left
      apply Bool.or_eq_true_iff.mpr; right
      apply Bool.and_eq_true_iff.mpr
      refine ⟨by simp,unary_found hv he (by omega) hf tail ?_⟩
      intro w hn eq
      have sz := live_size tail
      rw [←eq,List.toFinset_card_of_nodup hn] at sz
      exact ih k (by omega) w hn eq sz
  | @binary m t U a b d ha hb hab hf tail ih =>
    cases K with
    | zero => omega
    | succ k =>
      rw [search,if_neg (by omega)]
      apply Bool.or_eq_true_iff.mpr
      right
      have cont (w : List Sig) (hn : w.Nodup) (eq : w.toFinset=insert (bin d a b) U) : search k t w = true := by
        have sz := live_size tail
        rw [←eq,List.toFinset_card_of_nodup hn] at sz
        exact ih k (by omega) w hn eq sz
      rcases ordered hab with o | o
      · exact binary_found hv he (by omega) o hab hf tail cont
      · rw [Finset.insert_comm a b] at he hf
        rw [bin_comm d a b] at hf tail cont
        exact binary_found hv he (by omega) o hab.symm hf tail cont

open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (side : Bool) (i : Fin 410) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 410).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
private lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

private lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

private lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]

def sample (s : Bool) (i : Fin 410) (j : Fin 9) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 0 && x 7) || (x 0 && x 8)

set_option maxRecDepth 10000 in
private lemma sample_ok : ∀ (s : Bool) (i : Fin 410), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 9 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 9 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 11)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 3, search 11 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=9 := rfl
  change C.gates.length ≤ 11 at hc
  exact ⟨t,by omega,search_complete ht 11 (by omega) raw raw_nd eq⟩


-- A finite list of rejected successor states can be reused by the checker.
-- The closed Boolean check verifies that the list covers every enabled move.
def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
  v.contains target || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

private lemma try_mono {k t v rest g opts} {r s : List Sig → Bool}
    (h : ∀ w, r w = true → s w = true)
    (hr : tryGate k t r v rest g opts = true) : tryGate k t s v rest g opts = true := by
  simp only [tryGate,Bool.and_eq_true,List.any_eq_true] at hr ⊢
  obtain ⟨base,a,ha,hc,hit⟩ := hr
  exact ⟨base,a,ha,hc,h _ hit⟩

private lemma umove_mono {k t v} {r s : List Sig → Bool}
    (h : ∀ w, r w = true → s w = true)
    (hr : unaryMoves k t r v = true) : unaryMoves k t s v = true := by
  obtain ⟨a,ha,move⟩ := List.any_eq_true.mp hr
  exact List.any_eq_true.mpr ⟨a,ha,try_mono h move⟩

private lemma bmove_mono {k t v} {r s : List Sig → Bool}
    (h : ∀ w, r w = true → s w = true)
    (hr : binaryMoves k t r v = true) : binaryMoves k t s v = true := by
  obtain ⟨a,ha,m⟩ := List.any_eq_true.mp hr
  obtain ⟨b,hb,z⟩ := List.any_eq_true.mp m
  obtain ⟨o,w⟩ := Bool.and_eq_true_iff.mp z
  apply List.any_eq_true.mpr
  refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,Bool.and_eq_true_iff.mpr ⟨o,?_⟩⟩⟩
  rcases Bool.or_eq_true_iff.mp w with p | p
  · exact Bool.or_eq_true_iff.mpr (Or.inl (try_mono h p))
  · exact Bool.or_eq_true_iff.mpr (Or.inr (try_mono h p))

private lemma reject_step (k t : Nat) (v : List Sig) (U A : List (List Sig))
    (hu : ∀ w ∈ U, search k (t-1) w = false)
    (hb : ∀ w ∈ A, search k t w = false)
    (hc : stepTest k t v (fun w => !(U.contains w)) (fun w => !(A.contains w)) = false) :
    search (k+1) t v = false := by
  cases ht : search (k+1) t v with
  | false => rfl
  | true =>
    exfalso
    have mono (n : Nat) (L : List (List Sig)) (hL : ∀ w ∈ L, search k n w=false) (w : List Sig)
        (hp : search k n w=true) : !(L.contains w) = true := by
      have hn : w ∉ L := fun hm => by have eq := hL _ hm; simp [hp] at eq
      simp [List.contains_eq_mem,hn]
    simp only [search] at ht
    unfold stepTest at hc
    split at ht
    · contradiction
    next hn =>
      rw [if_neg hn] at hc
      apply Bool.noConfusion (show false = true from hc.symm.trans ?_)
      rcases Bool.or_eq_true_iff.mp ht with a | b
      · rcases Bool.or_eq_true_iff.mp a with hit | u
        · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl hit)))
        · obtain ⟨hn,p⟩ := Bool.and_eq_true_iff.mp u
          exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr
            (Or.inr (Bool.and_eq_true_iff.mpr ⟨hn,umove_mono (mono _ U hu) p⟩))))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (bmove_mono (mono _ A hb) b))


private lemma certifiedStep (k t : Nat) (v : List Sig)
    (u : List {w : List Sig // search k (t-1) w = false})
    (b : List {w : List Sig // search k t w = false})
    (checked : stepTest k t v
      (fun w => !((u.map Subtype.val).contains w))
      (fun w => !((b.map Subtype.val).contains w)) = false) :
    search (k+1) t v = false := by
  apply reject_step k t v (u.map Subtype.val) (b.map Subtype.val) _ _ checked
  all_goals
    intro w hw
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hw
    exact p.property


private def w0 : Sig := bin false raw0 raw1

private def w1 : Sig := bin false w0 raw2

private def w2 : Sig := bin true w0 raw2

private def w3 : Sig := bin false w0 raw3

private def w4 : Sig := bin true w0 raw3

private def w5 : Sig := bin false w0 raw4

private def w6 : Sig := bin true w0 raw4

private def w7 : Sig := bin false w0 raw5

private def w8 : Sig := bin true w0 raw5

private def w9 : Sig := bin false w0 raw6

private def w10 : Sig := bin true w0 raw6

private def w11 : Sig := bin false w0 raw7

private def w12 : Sig := bin true w0 raw7

private def w13 : Sig := bin false w0 raw8

private def w14 : Sig := bin true w0 raw8

private def w15 : Sig := bin false raw0 raw8

private def w16 : Sig := bin true raw1 raw3

private def w17 : Sig := bin true raw1 raw8

private def w18 : Sig := bin false raw1 raw2

private def w19 : Sig := bin true raw7 raw8

private def w20 : Sig := bin true raw0 raw1

private def w21 : Sig := bin false w20 raw3

private def w22 : Sig := bin true w20 raw3

private def w23 : Sig := bin false w20 raw5

private def w24 : Sig := bin true w20 raw5

private def w25 : Sig := bin false w20 raw6

private def w26 : Sig := bin true w20 raw6

private def w27 : Sig := bin false w20 raw7

private def w28 : Sig := bin true w20 raw7

private def w29 : Sig := bin false w20 raw8

private def w30 : Sig := bin true w20 raw8

private def w31 : Sig := bin true raw0 raw2

private def w32 : Sig := bin true raw1 raw7

private def w33 : Sig := bin false w20 raw2

private def w34 : Sig := bin true w20 raw2

private def w35 : Sig := bin false w20 raw4

private def w36 : Sig := bin true w20 raw4

private def w37 : Sig := bin false raw0 raw2

private def w38 : Sig := bin false w31 raw1

private def w39 : Sig := bin false w31 raw3

private def w40 : Sig := bin true w31 raw3

private def w41 : Sig := bin false w31 raw5

private def w42 : Sig := bin true w31 raw5

private def w43 : Sig := bin false w31 raw6

private def w44 : Sig := bin true w31 raw6

private def w45 : Sig := bin false w31 raw7

private def w46 : Sig := bin true w31 raw7

private def w47 : Sig := bin false w31 raw8

private def w48 : Sig := bin true w31 raw8

private def w49 : Sig := bin true raw0 raw3

private def w50 : Sig := bin true raw2 raw1

private def w51 : Sig := bin false raw2 raw3

private def w52 : Sig := bin true raw2 raw7

private def w53 : Sig := bin true raw2 raw8

private def w54 : Sig := bin false w31 raw4

private def w55 : Sig := bin true w31 raw4

private def w56 : Sig := bin true raw2 raw4

private def w57 : Sig := bin false raw0 raw3

private def w58 : Sig := bin false w49 raw5

private def w59 : Sig := bin true w49 raw5

private def w60 : Sig := bin false w49 raw6

private def w61 : Sig := bin true w49 raw6

private def w62 : Sig := bin false w49 raw7

private def w63 : Sig := bin true w49 raw7

private def w64 : Sig := bin false w49 raw8

private def w65 : Sig := bin true w49 raw8

private def w66 : Sig := bin true raw0 raw4

private def w67 : Sig := bin true raw3 raw7

private def w68 : Sig := bin true raw3 raw8

private def w69 : Sig := bin false w49 raw1

private def w70 : Sig := bin false w49 raw2

private def w71 : Sig := bin false w49 raw4

private def w72 : Sig := bin true w49 raw4

private def w73 : Sig := bin false raw0 raw4

private def w74 : Sig := bin true w73 raw1

private def w75 : Sig := bin false w73 raw2

private def w76 : Sig := bin true w73 raw2

private def w77 : Sig := bin false w73 raw3

private def w78 : Sig := bin true w73 raw3

private def w79 : Sig := bin false w73 raw5

private def w80 : Sig := bin true w73 raw5

private def w81 : Sig := bin false w73 raw6

private def w82 : Sig := bin true w73 raw6

private def w83 : Sig := bin false w73 raw7

private def w84 : Sig := bin true w73 raw7

private def w85 : Sig := bin false w73 raw8

private def w86 : Sig := bin true w73 raw8

private def w87 : Sig := bin false raw0 raw5

private def w88 : Sig := bin true raw0 raw5

private def w89 : Sig := bin false w88 raw6

private def w90 : Sig := bin true w88 raw6

private def w91 : Sig := bin false w88 raw7

private def w92 : Sig := bin true w88 raw7

private def w93 : Sig := bin false w88 raw8

private def w94 : Sig := bin true w88 raw8

private def w95 : Sig := bin true raw0 raw6

private def w96 : Sig := bin true raw5 raw7

private def w97 : Sig := bin true raw5 raw8

private def w98 : Sig := bin false w88 raw1

private def w99 : Sig := bin true raw5 raw1

private def w100 : Sig := bin false w88 raw2

private def w101 : Sig := bin false w88 raw3

private def w102 : Sig := bin false w88 raw4

private def w103 : Sig := bin true w88 raw4

private def w104 : Sig := bin false raw0 raw6

private def w105 : Sig := bin false w95 raw7

private def w106 : Sig := bin true w95 raw7

private def w107 : Sig := bin false w95 raw8

private def w108 : Sig := bin true w95 raw8

private def w109 : Sig := bin true raw0 raw7

private def w110 : Sig := bin true raw6 raw7

private def w111 : Sig := bin true raw6 raw8

private def w112 : Sig := bin false w95 raw1

private def w113 : Sig := bin true raw6 raw1

private def w114 : Sig := bin false w95 raw2

private def w115 : Sig := bin false w95 raw3

private def w116 : Sig := bin false w95 raw4

private def w117 : Sig := bin true w95 raw4

private def w118 : Sig := bin true raw6 raw4

private def w119 : Sig := bin false w95 raw5

private def w120 : Sig := bin false raw6 raw5

private def w121 : Sig := bin false raw0 raw7

private def w122 : Sig := bin true w121 raw1

private def w123 : Sig := bin false w121 raw2

private def w124 : Sig := bin true w121 raw2

private def w125 : Sig := bin false w121 raw3

private def w126 : Sig := bin true w121 raw3

private def w127 : Sig := bin true w121 raw4

private def w128 : Sig := bin false w121 raw5

private def w129 : Sig := bin true w121 raw5

private def w130 : Sig := bin false w121 raw6

private def w131 : Sig := bin true w121 raw6

private def w132 : Sig := bin false w121 raw8

private def w133 : Sig := bin true w121 raw8

private def w134 : Sig := bin false raw7 raw6

private def w135 : Sig := bin false w109 raw8

private def w136 : Sig := bin true w109 raw8

private def w137 : Sig := bin false w109 raw1

private def w138 : Sig := bin false w109 raw2

private def w139 : Sig := bin false w109 raw3

private def w140 : Sig := bin false w109 raw4

private def w141 : Sig := bin true w109 raw4

private def w142 : Sig := bin false w109 raw5

private def w143 : Sig := bin false w109 raw6

private def w144 : Sig := bin true w15 raw1

private def w145 : Sig := bin false w144 raw3

private def w146 : Sig := bin true w144 raw3

private def w147 : Sig := bin false w144 raw5

private def w148 : Sig := bin true w144 raw5

private def w149 : Sig := bin false w144 raw6

private def w150 : Sig := bin true w144 raw6

private def w151 : Sig := bin false w144 raw7

private def w152 : Sig := bin true w144 raw7

private def w153 : Sig := bin false w144 raw0

private def w154 : Sig := bin false w144 raw2

private def w155 : Sig := bin true w144 raw2

private def w156 : Sig := bin true raw2 raw3

private def w157 : Sig := bin false raw2 raw5

private def w158 : Sig := bin true raw2 raw5

private def w159 : Sig := bin false raw2 raw6

private def w160 : Sig := bin true raw2 raw6

private def w161 : Sig := bin false raw2 raw7

private def w162 : Sig := bin false raw3 raw5

private def w163 : Sig := bin true raw3 raw5

private def w164 : Sig := bin false raw3 raw6

private def w165 : Sig := bin true raw3 raw6

private def w166 : Sig := bin false raw3 raw7

private def w167 : Sig := bin false w144 raw4

private def w168 : Sig := bin true w144 raw4

private def w169 : Sig := bin false raw2 raw4

private def w170 : Sig := bin false raw3 raw4

private def w171 : Sig := bin true raw3 raw4

private def w172 : Sig := bin false raw4 raw5

private def w173 : Sig := bin true raw4 raw5

private def w174 : Sig := bin false raw4 raw6

private def w175 : Sig := bin false raw4 raw7

private def w176 : Sig := bin true raw4 raw7

private def w177 : Sig := bin true raw5 raw6

private def w178 : Sig := bin false raw5 raw7

private def w179 : Sig := bin false w15 raw2

private def w180 : Sig := bin true w15 raw2

private def w181 : Sig := bin false w15 raw3

private def w182 : Sig := bin true w15 raw3

private def w183 : Sig := bin true w15 raw4

private def w184 : Sig := bin false w15 raw5

private def w185 : Sig := bin true w15 raw5

private def w186 : Sig := bin false w15 raw6

private def w187 : Sig := bin true w15 raw6

private def w188 : Sig := bin true w15 raw7

private def w189 : Sig := bin false w188 raw0

private def w190 : Sig := bin false w188 raw1

private def w191 : Sig := bin false raw1 raw3

private def w192 : Sig := bin false raw1 raw5

private def w193 : Sig := bin false raw1 raw6

private def w194 : Sig := bin false w188 raw2

private def w195 : Sig := bin true w188 raw2

private def w196 : Sig := bin false w188 raw3

private def w197 : Sig := bin true w188 raw3

private def w198 : Sig := bin false w188 raw4

private def w199 : Sig := bin true w188 raw4

private def w200 : Sig := bin false raw1 raw4

private def w201 : Sig := bin true raw1 raw4

private def w202 : Sig := bin false w188 raw5

private def w203 : Sig := bin true w188 raw5

private def w204 : Sig := bin false w188 raw6

private def w205 : Sig := bin true w188 raw6

private def w206 : Sig := bin false raw1 raw7

private def w207 : Sig := bin true raw0 raw8

private def w208 : Sig := bin false raw8 raw1

private def w209 : Sig := bin false raw8 raw2

private def w210 : Sig := bin false raw8 raw3

private def w211 : Sig := bin false raw8 raw4

private def w212 : Sig := bin true raw8 raw4

private def w213 : Sig := bin false raw8 raw5

private def w214 : Sig := bin false raw8 raw6

private def w215 : Sig := bin false raw8 raw7

private def w216 : Sig := bin false w16 raw5

private def w217 : Sig := bin true w16 raw5

private def w218 : Sig := bin false w16 raw6

private def w219 : Sig := bin true w16 raw6

private def w220 : Sig := bin false w16 raw7

private def w221 : Sig := bin true w16 raw7

private def w222 : Sig := bin false w16 raw8

private def w223 : Sig := bin true w16 raw8

private def w224 : Sig := bin false w17 w16

private def w225 : Sig := bin false w16 raw2

private def w226 : Sig := bin true w17 raw7

private def w227 : Sig := bin false w16 raw0

private def w228 : Sig := bin true w225 raw1

private def w229 : Sig := bin true w225 raw3

private def w230 : Sig := bin true w225 raw4

private def w231 : Sig := bin true w225 raw5

private def w232 : Sig := bin true w225 raw6

private def w233 : Sig := bin true w225 raw7

private def w234 : Sig := bin true w225 raw8

private def w235 : Sig := bin true w225 raw0

private def w236 : Sig := bin true w16 raw2

private def w237 : Sig := bin false w16 raw4

private def w238 : Sig := bin true w16 raw4

private def w239 : Sig := bin false w192 raw3

private def w240 : Sig := bin true w192 raw3

private def w241 : Sig := bin false w192 raw6

private def w242 : Sig := bin true w192 raw6

private def w243 : Sig := bin false w192 raw7

private def w244 : Sig := bin true w192 raw7

private def w245 : Sig := bin false w192 raw8

private def w246 : Sig := bin true w192 raw8

private def w247 : Sig := bin true w192 raw0

private def w248 : Sig := bin false w192 raw2

private def w249 : Sig := bin true w192 raw2

private def w250 : Sig := bin false w192 raw4

private def w251 : Sig := bin true w192 raw4

private def w252 : Sig := bin false w32 raw8

private def w253 : Sig := bin false w226 raw0

private def w254 : Sig := bin false w32 raw0

private def w255 : Sig := bin false w32 raw2

private def w256 : Sig := bin true w32 raw2

private def w257 : Sig := bin false w32 raw3

private def w258 : Sig := bin false w32 raw4

private def w259 : Sig := bin true w32 raw4

private def w260 : Sig := bin false w32 raw5

private def w261 : Sig := bin true w32 raw5

private def w262 : Sig := bin false w32 raw6

private def w263 : Sig := bin true w32 raw6

private def w264 : Sig := bin true w153 raw2

private def w265 : Sig := bin true w153 raw3

private def w266 : Sig := bin true w153 raw4

private def w267 : Sig := bin true w153 raw5

private def w268 : Sig := bin true w153 raw6

private def w269 : Sig := bin true w153 raw7

private def w270 : Sig := bin false w17 raw2

private def w271 : Sig := bin true w17 raw2

private def w272 : Sig := bin true w18 raw4

private def w273 : Sig := bin true w18 raw5

private def w274 : Sig := bin true w18 raw6

private def w275 : Sig := bin true w18 raw7

private def w276 : Sig := bin true w18 raw0

private def w277 : Sig := bin false w17 raw3

private def w278 : Sig := bin false w17 raw4

private def w279 : Sig := bin true w17 raw4

private def w280 : Sig := bin false w17 raw5

private def w281 : Sig := bin true w17 raw5

private def w282 : Sig := bin false w17 raw6

private def w283 : Sig := bin true w17 raw6

private def w284 : Sig := bin false w17 raw7

private def w285 : Sig := bin false w18 raw3

private def w286 : Sig := bin false w18 raw4

private def w287 : Sig := bin false w18 raw6

private def w288 : Sig := bin false w18 raw7

private def w289 : Sig := bin false w18 raw8

private def w290 : Sig := bin true w18 raw8

private def w291 : Sig := bin false w51 raw4

private def w292 : Sig := bin true w51 raw4

private def w293 : Sig := bin false w51 raw5

private def w294 : Sig := bin true w51 raw5

private def w295 : Sig := bin false w51 raw6

private def w296 : Sig := bin true w51 raw6

private def w297 : Sig := bin false w51 raw7

private def w298 : Sig := bin true w51 raw7

private def w299 : Sig := bin false w51 raw8

private def w300 : Sig := bin true w51 raw8

private def w301 : Sig := bin false w51 raw0

private def w302 : Sig := bin true w51 raw0

private def w303 : Sig := bin true w159 raw1

private def w304 : Sig := bin true w159 raw3

private def w305 : Sig := bin false w159 raw5

private def w306 : Sig := bin true w159 raw5

private def w307 : Sig := bin false w159 raw7

private def w308 : Sig := bin true w159 raw7

private def w309 : Sig := bin false w159 raw8

private def w310 : Sig := bin true w159 raw8

private def w311 : Sig := bin false w159 raw0

private def w312 : Sig := bin true w159 raw0

private def w313 : Sig := bin false w159 raw4

private def w314 : Sig := bin true w159 raw4

private def w315 : Sig := bin false w163 raw6

private def w316 : Sig := bin true w163 raw6

private def w317 : Sig := bin false w163 raw7

private def w318 : Sig := bin true w163 raw7

private def w319 : Sig := bin false w163 raw8

private def w320 : Sig := bin true w163 raw8

private def w321 : Sig := bin false w163 raw0

private def w322 : Sig := bin false w163 raw1

private def w323 : Sig := bin false w163 raw2

private def w324 : Sig := bin true w163 raw2

private def w325 : Sig := bin false w163 raw4

private def w326 : Sig := bin true w163 raw4

private def w327 : Sig := bin false w166 raw5

private def w328 : Sig := bin true w166 raw5

private def w329 : Sig := bin false w166 raw6

private def w330 : Sig := bin true w166 raw6

private def w331 : Sig := bin false w166 raw8

private def w332 : Sig := bin true w166 raw8

private def w333 : Sig := bin true w166 raw0

private def w334 : Sig := bin false w166 raw1

private def w335 : Sig := bin true w166 raw1

private def w336 : Sig := bin true w166 raw2

private def w337 : Sig := bin false w166 raw4

private def w338 : Sig := bin true w166 raw4

private def w339 : Sig := bin false w56 raw1

private def w340 : Sig := bin true w56 raw1

private def w341 : Sig := bin false w56 raw3

private def w342 : Sig := bin true w56 raw3

private def w343 : Sig := bin false w56 raw5

private def w344 : Sig := bin true w56 raw5

private def w345 : Sig := bin false w56 raw6

private def w346 : Sig := bin true w56 raw6

private def w347 : Sig := bin false w56 raw7

private def w348 : Sig := bin true w56 raw7

private def w349 : Sig := bin false w56 raw8

private def w350 : Sig := bin true w56 raw8

private def w351 : Sig := bin false w56 raw0

private def w352 : Sig := bin false w170 raw1

private def w353 : Sig := bin true w170 raw1

private def w354 : Sig := bin true w170 raw2

private def w355 : Sig := bin false w170 raw5

private def w356 : Sig := bin true w170 raw5

private def w357 : Sig := bin false w170 raw6

private def w358 : Sig := bin true w170 raw6

private def w359 : Sig := bin true w170 raw7

private def w360 : Sig := bin false w170 raw8

private def w361 : Sig := bin true w170 raw8

private def w362 : Sig := bin true w170 raw0

private def w363 : Sig := bin true w172 raw1

private def w364 : Sig := bin false w172 raw2

private def w365 : Sig := bin true w172 raw2

private def w366 : Sig := bin true w172 raw3

private def w367 : Sig := bin false w172 raw6

private def w368 : Sig := bin true w172 raw6

private def w369 : Sig := bin false w172 raw7

private def w370 : Sig := bin true w172 raw7

private def w371 : Sig := bin false w172 raw8

private def w372 : Sig := bin true w172 raw8

private def w373 : Sig := bin true w172 raw0

private def w374 : Sig := bin false w118 raw7

private def w375 : Sig := bin true w118 raw7

private def w376 : Sig := bin false w118 raw8

private def w377 : Sig := bin true w118 raw8

private def w378 : Sig := bin false w118 raw0

private def w379 : Sig := bin false w118 raw1

private def w380 : Sig := bin true w118 raw1

private def w381 : Sig := bin false w118 raw2

private def w382 : Sig := bin false w118 raw3

private def w383 : Sig := bin true w118 raw3

private def w384 : Sig := bin false w118 raw5

private def w385 : Sig := bin true w118 raw5

private def w386 : Sig := bin false w120 raw7

private def w387 : Sig := bin true w120 raw7

private def w388 : Sig := bin false w120 raw8

private def w389 : Sig := bin true w120 raw8

private def w390 : Sig := bin false w120 raw0

private def w391 : Sig := bin true w120 raw0

private def w392 : Sig := bin true w120 raw1

private def w393 : Sig := bin true w120 raw2

private def w394 : Sig := bin false w120 raw3

private def w395 : Sig := bin true w120 raw3

private def w396 : Sig := bin true w120 raw4

private def w397 : Sig := bin false w96 raw8

private def w398 : Sig := bin true w96 raw8

private def w399 : Sig := bin false w19 w96

private def w400 : Sig := bin false w96 raw6

private def w401 : Sig := bin false w96 raw0

private def w402 : Sig := bin false w96 raw1

private def w403 : Sig := bin false w96 raw2

private def w404 : Sig := bin true w96 raw2

private def w405 : Sig := bin false w96 raw3

private def w406 : Sig := bin false w96 raw4

private def w407 : Sig := bin true w96 raw4

private def w408 : Sig := bin true w400 raw8

private def w409 : Sig := bin true w400 raw5

private def w410 : Sig := bin true w400 raw0

private def w411 : Sig := bin true w400 raw1

private def w412 : Sig := bin true w400 raw2

private def w413 : Sig := bin true w400 raw3

private def w414 : Sig := bin true w400 raw4

private def w415 : Sig := bin true w96 raw6

private def w416 : Sig := bin false w134 raw8

private def w417 : Sig := bin true w134 raw8

private def w418 : Sig := bin true w134 raw0

private def w419 : Sig := bin true w134 raw1

private def w420 : Sig := bin true w134 raw2

private def w421 : Sig := bin true w134 raw3

private def w422 : Sig := bin true w134 raw4

private def w423 : Sig := bin false w134 raw1

private def w424 : Sig := bin false w134 raw4

private def w425 : Sig := bin true w189 raw1

private def w426 : Sig := bin true w189 raw2

private def w427 : Sig := bin true w189 raw3

private def w428 : Sig := bin true w189 raw4

private def w429 : Sig := bin true w189 raw5

private def w430 : Sig := bin true w189 raw6

private def w431 : Sig := bin false w19 raw1

private def w432 : Sig := bin false w19 raw2

private def w433 : Sig := bin true w19 raw2

private def w434 : Sig := bin false w19 raw3

private def w435 : Sig := bin true w19 raw3

private def w436 : Sig := bin false w19 raw4

private def w437 : Sig := bin true w19 raw4

private def w438 : Sig := bin false w19 raw5

private def w439 : Sig := bin false w19 raw6

private def w440 : Sig := bin true w19 raw6

private def w441 : Sig := neg raw0

private def w442 : Sig := neg w15

private def w443 : Sig := neg raw1

private def w444 : Sig := neg raw2

private def w445 : Sig := neg raw3

private def w446 : Sig := neg raw4

private def w447 : Sig := neg raw5

private def w448 : Sig := neg raw6

private def w449 : Sig := neg raw7

private def w450 : Sig := neg raw8

private def v4 : List Sig := [w0, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

private def v5 : List Sig := [w1, raw2, raw0, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv5 : search 9 0 v5 = false := by decide +kernel

private def v6 : List Sig := [w2, raw0, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv6 : search 9 0 v6 = false := by decide +kernel

private def v7 : List Sig := [w2, w0, raw0, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv7 : search 9 0 v7 = false := by decide +kernel

private def v8 : List Sig := [w2, raw2, raw0, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv8 : search 9 0 v8 = false := by decide +kernel

private def v9 : List Sig := [w3, raw3, raw0, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv9 : search 9 0 v9 = false := by decide +kernel

private def v10 : List Sig := [w4, raw0, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv10 : search 9 0 v10 = false := by decide +kernel

private def v11 : List Sig := [w4, w0, raw0, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv11 : search 9 0 v11 = false := by decide +kernel

private def v12 : List Sig := [w4, raw3, raw0, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv12 : search 9 0 v12 = false := by decide +kernel

private def v13 : List Sig := [w5, raw4, raw0, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv13 : search 9 0 v13 = false := by decide +kernel

private def v14 : List Sig := [w6, raw0, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv14 : search 9 0 v14 = false := by decide +kernel

private def v15 : List Sig := [w6, w0, raw0, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv15 : search 9 0 v15 = false := by decide +kernel

private def v16 : List Sig := [w6, raw4, raw0, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv16 : search 9 0 v16 = false := by decide +kernel

private def v17 : List Sig := [w7, raw5, raw0, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv17 : search 9 0 v17 = false := by decide +kernel

private def v18 : List Sig := [w8, raw0, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv18 : search 9 0 v18 = false := by decide +kernel

private def v19 : List Sig := [w8, w0, raw0, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv19 : search 9 0 v19 = false := by decide +kernel

private def v20 : List Sig := [w8, raw5, raw0, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv20 : search 9 0 v20 = false := by decide +kernel

private def v21 : List Sig := [w9, raw6, raw0, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv21 : search 9 0 v21 = false := by decide +kernel

private def v22 : List Sig := [w10, raw0, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv22 : search 9 0 v22 = false := by decide +kernel

private def v23 : List Sig := [w10, w0, raw0, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv23 : search 9 0 v23 = false := by decide +kernel

private def v24 : List Sig := [w10, raw6, raw0, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv24 : search 9 0 v24 = false := by decide +kernel

private def v25 : List Sig := [w11, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv25 : search 9 0 v25 = false := by decide +kernel

private def v26 : List Sig := [w12, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv26 : search 9 0 v26 = false := by decide +kernel

private def v27 : List Sig := [w12, w0, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv27 : search 9 0 v27 = false := by decide +kernel

private def v28 : List Sig := [w12, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv28 : search 9 0 v28 = false := by decide +kernel

private def v29 : List Sig := [w13, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv29 : search 9 0 v29 = false := by decide +kernel

private def v30 : List Sig := [w14, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv30 : search 9 0 v30 = false := by decide +kernel

private def v31 : List Sig := [w14, w0, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv31 : search 9 0 v31 = false := by decide +kernel

private def v32 : List Sig := [w14, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv32 : search 9 0 v32 = false := by decide +kernel

private def v33 : List Sig := [w15, raw0, w0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv33 : search 9 0 v33 = false := by decide +kernel

private def v34 : List Sig := [w16, raw3, w0, raw0, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv34 : search 9 0 v34 = false := by decide +kernel

private def v35 : List Sig := [w17, raw1, w0, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv35 : search 9 0 v35 = false := by decide +kernel

private def v36 : List Sig := [w18, raw2, w0, raw0, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv36 : search 9 0 v36 = false := by decide +kernel

private def v37 : List Sig := [w19, raw7, w0, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv37 : search 9 0 v37 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv4 : search 10 0 v4 = false := certifiedStep 9 0 v4
    []
    [⟨v5, rejectv5⟩, ⟨v6, rejectv6⟩, ⟨v7, rejectv7⟩, ⟨v8, rejectv8⟩, ⟨v9, rejectv9⟩, ⟨v10, rejectv10⟩, ⟨v11, rejectv11⟩, ⟨v12, rejectv12⟩, ⟨v13, rejectv13⟩, ⟨v14, rejectv14⟩, ⟨v15, rejectv15⟩, ⟨v16, rejectv16⟩, ⟨v17, rejectv17⟩, ⟨v18, rejectv18⟩, ⟨v19, rejectv19⟩, ⟨v20, rejectv20⟩, ⟨v21, rejectv21⟩, ⟨v22, rejectv22⟩, ⟨v23, rejectv23⟩, ⟨v24, rejectv24⟩, ⟨v25, rejectv25⟩, ⟨v26, rejectv26⟩, ⟨v27, rejectv27⟩, ⟨v28, rejectv28⟩, ⟨v29, rejectv29⟩, ⟨v30, rejectv30⟩, ⟨v31, rejectv31⟩, ⟨v32, rejectv32⟩, ⟨v33, rejectv33⟩, ⟨v34, rejectv34⟩, ⟨v35, rejectv35⟩, ⟨v36, rejectv36⟩, ⟨v37, rejectv37⟩]
    (by decide +kernel)

private def v38 : List Sig := [w20, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

private def v39 : List Sig := [w21, raw3, raw0, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv39 : search 9 0 v39 = false := by decide +kernel

private def v40 : List Sig := [w22, raw3, raw0, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv40 : search 9 0 v40 = false := by decide +kernel

private def v41 : List Sig := [w23, raw5, raw0, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv41 : search 9 0 v41 = false := by decide +kernel

private def v42 : List Sig := [w24, raw5, raw0, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv42 : search 9 0 v42 = false := by decide +kernel

private def v43 : List Sig := [w25, raw6, raw0, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv43 : search 9 0 v43 = false := by decide +kernel

private def v44 : List Sig := [w26, raw6, raw0, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv44 : search 9 0 v44 = false := by decide +kernel

private def v45 : List Sig := [w27, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv45 : search 9 0 v45 = false := by decide +kernel

private def v46 : List Sig := [w28, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv46 : search 9 0 v46 = false := by decide +kernel

private def v47 : List Sig := [w29, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv47 : search 9 0 v47 = false := by decide +kernel

private def v48 : List Sig := [w29, w20, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv48 : search 9 0 v48 = false := by decide +kernel

private def v49 : List Sig := [w29, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv49 : search 9 0 v49 = false := by decide +kernel

private def v50 : List Sig := [w30, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv50 : search 9 0 v50 = false := by decide +kernel

private def v51 : List Sig := [w31, raw2, w20, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv51 : search 9 0 v51 = false := by decide +kernel

private def v52 : List Sig := [w15, raw0, w20, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv52 : search 9 0 v52 = false := by decide +kernel

private def v53 : List Sig := [w32, raw7, w20, raw0, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv53 : search 9 0 v53 = false := by decide +kernel

private def v54 : List Sig := [w17, w20, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv54 : search 9 0 v54 = false := by decide +kernel

private def v55 : List Sig := [w17, raw1, w20, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv55 : search 9 0 v55 = false := by decide +kernel

private def v56 : List Sig := [w17, raw8, w20, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv56 : search 9 0 v56 = false := by decide +kernel

private def v57 : List Sig := [w33, raw2, raw0, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv57 : search 9 0 v57 = false := by decide +kernel

private def v58 : List Sig := [w34, raw2, raw0, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv58 : search 9 0 v58 = false := by decide +kernel

private def v59 : List Sig := [w35, raw4, raw0, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv59 : search 9 0 v59 = false := by decide +kernel

private def v60 : List Sig := [w36, raw4, raw0, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv60 : search 9 0 v60 = false := by decide +kernel

private def v61 : List Sig := [w19, raw7, w20, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv61 : search 9 0 v61 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv38 : search 10 0 v38 = false := certifiedStep 9 0 v38
    []
    [⟨v39, rejectv39⟩, ⟨v40, rejectv40⟩, ⟨v41, rejectv41⟩, ⟨v42, rejectv42⟩, ⟨v43, rejectv43⟩, ⟨v44, rejectv44⟩, ⟨v45, rejectv45⟩, ⟨v46, rejectv46⟩, ⟨v47, rejectv47⟩, ⟨v48, rejectv48⟩, ⟨v49, rejectv49⟩, ⟨v50, rejectv50⟩, ⟨v51, rejectv51⟩, ⟨v52, rejectv52⟩, ⟨v53, rejectv53⟩, ⟨v54, rejectv54⟩, ⟨v55, rejectv55⟩, ⟨v56, rejectv56⟩, ⟨v57, rejectv57⟩, ⟨v58, rejectv58⟩, ⟨v59, rejectv59⟩, ⟨v60, rejectv60⟩, ⟨v61, rejectv61⟩]
    (by decide +kernel)

private def v62 : List Sig := [w37, raw0, raw2, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv62 : search 10 0 v62 = false := by decide +kernel

private def v63 : List Sig := [w31, raw0, raw2, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

private def v64 : List Sig := [w38, raw0, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv64 : search 9 0 v64 = false := by decide +kernel

private def v65 : List Sig := [w38, w31, raw0, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv65 : search 9 0 v65 = false := by decide +kernel

private def v66 : List Sig := [w38, raw1, raw0, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv66 : search 9 0 v66 = false := by decide +kernel

private def v67 : List Sig := [w34, raw1, raw0, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv67 : search 9 0 v67 = false := by decide +kernel

private def v68 : List Sig := [w39, raw3, raw0, raw2, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv68 : search 9 0 v68 = false := by decide +kernel

private def v69 : List Sig := [w40, raw3, raw0, raw2, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv69 : search 9 0 v69 = false := by decide +kernel

private def v70 : List Sig := [w41, raw5, raw0, raw2, raw1, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv70 : search 9 0 v70 = false := by decide +kernel

private def v71 : List Sig := [w42, raw5, raw0, raw2, raw1, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv71 : search 9 0 v71 = false := by decide +kernel

private def v72 : List Sig := [w43, raw6, raw0, raw2, raw1, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv72 : search 9 0 v72 = false := by decide +kernel

private def v73 : List Sig := [w44, raw6, raw0, raw2, raw1, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv73 : search 9 0 v73 = false := by decide +kernel

private def v74 : List Sig := [w45, raw7, raw0, raw2, raw1, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv74 : search 9 0 v74 = false := by decide +kernel

private def v75 : List Sig := [w46, raw7, raw0, raw2, raw1, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv75 : search 9 0 v75 = false := by decide +kernel

private def v76 : List Sig := [w47, raw0, raw2, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv76 : search 9 0 v76 = false := by decide +kernel

private def v77 : List Sig := [w47, w31, raw0, raw2, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv77 : search 9 0 v77 = false := by decide +kernel

private def v78 : List Sig := [w47, raw8, raw0, raw2, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv78 : search 9 0 v78 = false := by decide +kernel

private def v79 : List Sig := [w48, raw8, raw0, raw2, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv79 : search 9 0 v79 = false := by decide +kernel

private def v80 : List Sig := [w20, raw1, w31, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv80 : search 9 0 v80 = false := by decide +kernel

private def v81 : List Sig := [w49, raw3, w31, raw2, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv81 : search 9 0 v81 = false := by decide +kernel

private def v82 : List Sig := [w15, raw0, w31, raw2, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv82 : search 9 0 v82 = false := by decide +kernel

private def v83 : List Sig := [w50, raw1, w31, raw0, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv83 : search 9 0 v83 = false := by decide +kernel

private def v84 : List Sig := [w51, raw3, w31, raw0, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv84 : search 9 0 v84 = false := by decide +kernel

private def v85 : List Sig := [w52, raw7, w31, raw0, raw1, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv85 : search 9 0 v85 = false := by decide +kernel

private def v86 : List Sig := [w53, raw8, w31, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv86 : search 9 0 v86 = false := by decide +kernel

private def v87 : List Sig := [w17, raw1, w31, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv87 : search 9 0 v87 = false := by decide +kernel

private def v88 : List Sig := [w54, raw4, raw0, raw2, raw1, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv88 : search 9 0 v88 = false := by decide +kernel

private def v89 : List Sig := [w55, raw4, raw0, raw2, raw1, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv89 : search 9 0 v89 = false := by decide +kernel

private def v90 : List Sig := [w56, raw4, w31, raw0, raw1, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv90 : search 9 0 v90 = false := by decide +kernel

private def v91 : List Sig := [w19, raw7, w31, raw0, raw2, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv91 : search 9 0 v91 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv63 : search 10 0 v63 = false := certifiedStep 9 0 v63
    []
    [⟨v64, rejectv64⟩, ⟨v65, rejectv65⟩, ⟨v66, rejectv66⟩, ⟨v67, rejectv67⟩, ⟨v68, rejectv68⟩, ⟨v69, rejectv69⟩, ⟨v70, rejectv70⟩, ⟨v71, rejectv71⟩, ⟨v72, rejectv72⟩, ⟨v73, rejectv73⟩, ⟨v74, rejectv74⟩, ⟨v75, rejectv75⟩, ⟨v76, rejectv76⟩, ⟨v77, rejectv77⟩, ⟨v78, rejectv78⟩, ⟨v79, rejectv79⟩, ⟨v80, rejectv80⟩, ⟨v81, rejectv81⟩, ⟨v82, rejectv82⟩, ⟨v83, rejectv83⟩, ⟨v84, rejectv84⟩, ⟨v85, rejectv85⟩, ⟨v86, rejectv86⟩, ⟨v87, rejectv87⟩, ⟨v88, rejectv88⟩, ⟨v89, rejectv89⟩, ⟨v90, rejectv90⟩, ⟨v91, rejectv91⟩]
    (by decide +kernel)

private def v92 : List Sig := [w57, raw0, raw3, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv92 : search 10 0 v92 = false := by decide +kernel

private def v93 : List Sig := [w49, raw0, raw3, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

private def v94 : List Sig := [w58, raw5, raw0, raw3, raw1, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv94 : search 9 0 v94 = false := by decide +kernel

private def v95 : List Sig := [w59, raw5, raw0, raw3, raw1, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv95 : search 9 0 v95 = false := by decide +kernel

private def v96 : List Sig := [w60, raw6, raw0, raw3, raw1, raw2, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv96 : search 9 0 v96 = false := by decide +kernel

private def v97 : List Sig := [w61, raw6, raw0, raw3, raw1, raw2, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv97 : search 9 0 v97 = false := by decide +kernel

private def v98 : List Sig := [w62, raw7, raw0, raw3, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv98 : search 9 0 v98 = false := by decide +kernel

private def v99 : List Sig := [w63, raw7, raw0, raw3, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv99 : search 9 0 v99 = false := by decide +kernel

private def v100 : List Sig := [w64, raw0, raw3, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv100 : search 9 0 v100 = false := by decide +kernel

private def v101 : List Sig := [w64, w49, raw0, raw3, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv101 : search 9 0 v101 = false := by decide +kernel

private def v102 : List Sig := [w64, raw8, raw0, raw3, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv102 : search 9 0 v102 = false := by decide +kernel

private def v103 : List Sig := [w65, raw8, raw0, raw3, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv103 : search 9 0 v103 = false := by decide +kernel

private def v104 : List Sig := [w31, raw2, w49, raw3, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv104 : search 9 0 v104 = false := by decide +kernel

private def v105 : List Sig := [w66, raw4, w49, raw3, raw1, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv105 : search 9 0 v105 = false := by decide +kernel

private def v106 : List Sig := [w15, raw0, w49, raw3, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv106 : search 9 0 v106 = false := by decide +kernel

private def v107 : List Sig := [w67, raw7, w49, raw0, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv107 : search 9 0 v107 = false := by decide +kernel

private def v108 : List Sig := [w68, raw8, w49, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv108 : search 9 0 v108 = false := by decide +kernel

private def v109 : List Sig := [w69, raw1, raw0, raw3, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv109 : search 9 0 v109 = false := by decide +kernel

private def v110 : List Sig := [w22, raw1, raw0, raw3, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv110 : search 9 0 v110 = false := by decide +kernel

private def v111 : List Sig := [w16, raw1, w49, raw0, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv111 : search 9 0 v111 = false := by decide +kernel

private def v112 : List Sig := [w17, raw1, w49, raw0, raw3, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv112 : search 9 0 v112 = false := by decide +kernel

private def v113 : List Sig := [w70, raw2, raw0, raw3, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv113 : search 9 0 v113 = false := by decide +kernel

private def v114 : List Sig := [w40, raw2, raw0, raw3, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv114 : search 9 0 v114 = false := by decide +kernel

private def v115 : List Sig := [w71, raw4, raw0, raw3, raw1, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv115 : search 9 0 v115 = false := by decide +kernel

private def v116 : List Sig := [w72, raw4, raw0, raw3, raw1, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv116 : search 9 0 v116 = false := by decide +kernel

private def v117 : List Sig := [w19, raw7, w49, raw0, raw3, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv117 : search 9 0 v117 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv93 : search 10 0 v93 = false := certifiedStep 9 0 v93
    []
    [⟨v94, rejectv94⟩, ⟨v95, rejectv95⟩, ⟨v96, rejectv96⟩, ⟨v97, rejectv97⟩, ⟨v98, rejectv98⟩, ⟨v99, rejectv99⟩, ⟨v100, rejectv100⟩, ⟨v101, rejectv101⟩, ⟨v102, rejectv102⟩, ⟨v103, rejectv103⟩, ⟨v104, rejectv104⟩, ⟨v105, rejectv105⟩, ⟨v106, rejectv106⟩, ⟨v107, rejectv107⟩, ⟨v108, rejectv108⟩, ⟨v109, rejectv109⟩, ⟨v110, rejectv110⟩, ⟨v111, rejectv111⟩, ⟨v112, rejectv112⟩, ⟨v113, rejectv113⟩, ⟨v114, rejectv114⟩, ⟨v115, rejectv115⟩, ⟨v116, rejectv116⟩, ⟨v117, rejectv117⟩]
    (by decide +kernel)

private def v118 : List Sig := [w73, raw0, raw4, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

private def v119 : List Sig := [w5, raw1, raw0, raw4, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv119 : search 9 0 v119 = false := by decide +kernel

private def v120 : List Sig := [w74, raw1, raw0, raw4, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv120 : search 9 0 v120 = false := by decide +kernel

private def v121 : List Sig := [w75, raw2, raw0, raw4, raw1, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv121 : search 9 0 v121 = false := by decide +kernel

private def v122 : List Sig := [w76, raw0, raw4, raw1, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv122 : search 9 0 v122 = false := by decide +kernel

private def v123 : List Sig := [w76, w73, raw0, raw4, raw1, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv123 : search 9 0 v123 = false := by decide +kernel

private def v124 : List Sig := [w76, raw2, raw0, raw4, raw1, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv124 : search 9 0 v124 = false := by decide +kernel

private def v125 : List Sig := [w77, raw3, raw0, raw4, raw1, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv125 : search 9 0 v125 = false := by decide +kernel

private def v126 : List Sig := [w78, raw3, raw0, raw4, raw1, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv126 : search 9 0 v126 = false := by decide +kernel

private def v127 : List Sig := [w79, raw5, raw0, raw4, raw1, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv127 : search 9 0 v127 = false := by decide +kernel

private def v128 : List Sig := [w80, raw5, raw0, raw4, raw1, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv128 : search 9 0 v128 = false := by decide +kernel

private def v129 : List Sig := [w81, raw6, raw0, raw4, raw1, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv129 : search 9 0 v129 = false := by decide +kernel

private def v130 : List Sig := [w82, raw0, raw4, raw1, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv130 : search 9 0 v130 = false := by decide +kernel

private def v131 : List Sig := [w82, w73, raw0, raw4, raw1, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv131 : search 9 0 v131 = false := by decide +kernel

private def v132 : List Sig := [w82, raw6, raw0, raw4, raw1, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv132 : search 9 0 v132 = false := by decide +kernel

private def v133 : List Sig := [w83, raw7, raw0, raw4, raw1, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv133 : search 9 0 v133 = false := by decide +kernel

private def v134 : List Sig := [w84, raw7, raw0, raw4, raw1, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv134 : search 9 0 v134 = false := by decide +kernel

private def v135 : List Sig := [w85, raw8, raw0, raw4, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv135 : search 9 0 v135 = false := by decide +kernel

private def v136 : List Sig := [w86, raw8, raw0, raw4, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv136 : search 9 0 v136 = false := by decide +kernel

private def v137 : List Sig := [w15, raw0, w73, raw4, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv137 : search 9 0 v137 = false := by decide +kernel

private def v138 : List Sig := [w17, raw1, w73, raw0, raw4, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv138 : search 9 0 v138 = false := by decide +kernel

private def v139 : List Sig := [w19, raw7, w73, raw0, raw4, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv139 : search 9 0 v139 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv118 : search 10 0 v118 = false := certifiedStep 9 0 v118
    []
    [⟨v119, rejectv119⟩, ⟨v120, rejectv120⟩, ⟨v121, rejectv121⟩, ⟨v122, rejectv122⟩, ⟨v123, rejectv123⟩, ⟨v124, rejectv124⟩, ⟨v125, rejectv125⟩, ⟨v126, rejectv126⟩, ⟨v127, rejectv127⟩, ⟨v128, rejectv128⟩, ⟨v129, rejectv129⟩, ⟨v130, rejectv130⟩, ⟨v131, rejectv131⟩, ⟨v132, rejectv132⟩, ⟨v133, rejectv133⟩, ⟨v134, rejectv134⟩, ⟨v135, rejectv135⟩, ⟨v136, rejectv136⟩, ⟨v137, rejectv137⟩, ⟨v138, rejectv138⟩, ⟨v139, rejectv139⟩]
    (by decide +kernel)

private def v140 : List Sig := [w66, raw0, raw4, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv140 : search 10 0 v140 = false := by decide +kernel

private def v141 : List Sig := [w87, raw0, raw5, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv141 : search 10 0 v141 = false := by decide +kernel

private def v142 : List Sig := [w88, raw0, raw5, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

private def v143 : List Sig := [w89, raw6, raw0, raw5, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv143 : search 9 0 v143 = false := by decide +kernel

private def v144 : List Sig := [w90, raw6, raw0, raw5, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv144 : search 9 0 v144 = false := by decide +kernel

private def v145 : List Sig := [w91, raw7, raw0, raw5, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv145 : search 9 0 v145 = false := by decide +kernel

private def v146 : List Sig := [w92, raw7, raw0, raw5, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv146 : search 9 0 v146 = false := by decide +kernel

private def v147 : List Sig := [w93, raw0, raw5, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv147 : search 9 0 v147 = false := by decide +kernel

private def v148 : List Sig := [w93, w88, raw0, raw5, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv148 : search 9 0 v148 = false := by decide +kernel

private def v149 : List Sig := [w93, raw8, raw0, raw5, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv149 : search 9 0 v149 = false := by decide +kernel

private def v150 : List Sig := [w94, raw8, raw0, raw5, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv150 : search 9 0 v150 = false := by decide +kernel

private def v151 : List Sig := [w66, raw4, w88, raw5, raw1, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv151 : search 9 0 v151 = false := by decide +kernel

private def v152 : List Sig := [w95, raw6, w88, raw5, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv152 : search 9 0 v152 = false := by decide +kernel

private def v153 : List Sig := [w15, raw0, w88, raw5, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv153 : search 9 0 v153 = false := by decide +kernel

private def v154 : List Sig := [w96, raw7, w88, raw0, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv154 : search 9 0 v154 = false := by decide +kernel

private def v155 : List Sig := [w97, raw8, w88, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv155 : search 9 0 v155 = false := by decide +kernel

private def v156 : List Sig := [w98, raw1, raw0, raw5, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv156 : search 9 0 v156 = false := by decide +kernel

private def v157 : List Sig := [w24, raw1, raw0, raw5, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv157 : search 9 0 v157 = false := by decide +kernel

private def v158 : List Sig := [w99, raw1, w88, raw0, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv158 : search 9 0 v158 = false := by decide +kernel

private def v159 : List Sig := [w17, raw1, w88, raw0, raw5, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv159 : search 9 0 v159 = false := by decide +kernel

private def v160 : List Sig := [w100, raw2, raw0, raw5, raw1, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv160 : search 9 0 v160 = false := by decide +kernel

private def v161 : List Sig := [w42, raw2, raw0, raw5, raw1, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv161 : search 9 0 v161 = false := by decide +kernel

private def v162 : List Sig := [w101, raw3, raw0, raw5, raw1, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv162 : search 9 0 v162 = false := by decide +kernel

private def v163 : List Sig := [w59, raw3, raw0, raw5, raw1, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv163 : search 9 0 v163 = false := by decide +kernel

private def v164 : List Sig := [w102, raw4, raw0, raw5, raw1, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv164 : search 9 0 v164 = false := by decide +kernel

private def v165 : List Sig := [w103, raw4, raw0, raw5, raw1, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv165 : search 9 0 v165 = false := by decide +kernel

private def v166 : List Sig := [w19, raw7, w88, raw0, raw5, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv166 : search 9 0 v166 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv142 : search 10 0 v142 = false := certifiedStep 9 0 v142
    []
    [⟨v143, rejectv143⟩, ⟨v144, rejectv144⟩, ⟨v145, rejectv145⟩, ⟨v146, rejectv146⟩, ⟨v147, rejectv147⟩, ⟨v148, rejectv148⟩, ⟨v149, rejectv149⟩, ⟨v150, rejectv150⟩, ⟨v151, rejectv151⟩, ⟨v152, rejectv152⟩, ⟨v153, rejectv153⟩, ⟨v154, rejectv154⟩, ⟨v155, rejectv155⟩, ⟨v156, rejectv156⟩, ⟨v157, rejectv157⟩, ⟨v158, rejectv158⟩, ⟨v159, rejectv159⟩, ⟨v160, rejectv160⟩, ⟨v161, rejectv161⟩, ⟨v162, rejectv162⟩, ⟨v163, rejectv163⟩, ⟨v164, rejectv164⟩, ⟨v165, rejectv165⟩, ⟨v166, rejectv166⟩]
    (by decide +kernel)

private def v167 : List Sig := [w104, raw0, raw6, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv167 : search 10 0 v167 = false := by decide +kernel

private def v168 : List Sig := [w95, raw0, raw6, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

private def v169 : List Sig := [w105, raw0, raw6, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv169 : search 9 0 v169 = false := by decide +kernel

private def v170 : List Sig := [w105, w95, raw0, raw6, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv170 : search 9 0 v170 = false := by decide +kernel

private def v171 : List Sig := [w105, raw7, raw0, raw6, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv171 : search 9 0 v171 = false := by decide +kernel

private def v172 : List Sig := [w106, raw7, raw0, raw6, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv172 : search 9 0 v172 = false := by decide +kernel

private def v173 : List Sig := [w107, raw0, raw6, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv173 : search 9 0 v173 = false := by decide +kernel

private def v174 : List Sig := [w107, w95, raw0, raw6, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv174 : search 9 0 v174 = false := by decide +kernel

private def v175 : List Sig := [w107, raw8, raw0, raw6, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv175 : search 9 0 v175 = false := by decide +kernel

private def v176 : List Sig := [w108, raw8, raw0, raw6, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv176 : search 9 0 v176 = false := by decide +kernel

private def v177 : List Sig := [w88, raw5, w95, raw6, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv177 : search 9 0 v177 = false := by decide +kernel

private def v178 : List Sig := [w109, raw7, w95, raw6, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv178 : search 9 0 v178 = false := by decide +kernel

private def v179 : List Sig := [w15, raw0, w95, raw6, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv179 : search 9 0 v179 = false := by decide +kernel

private def v180 : List Sig := [w110, raw7, w95, raw0, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv180 : search 9 0 v180 = false := by decide +kernel

private def v181 : List Sig := [w111, raw8, w95, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv181 : search 9 0 v181 = false := by decide +kernel

private def v182 : List Sig := [w112, raw1, raw0, raw6, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv182 : search 9 0 v182 = false := by decide +kernel

private def v183 : List Sig := [w26, raw1, raw0, raw6, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv183 : search 9 0 v183 = false := by decide +kernel

private def v184 : List Sig := [w113, raw1, w95, raw0, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv184 : search 9 0 v184 = false := by decide +kernel

private def v185 : List Sig := [w17, raw1, w95, raw0, raw6, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv185 : search 9 0 v185 = false := by decide +kernel

private def v186 : List Sig := [w114, raw2, raw0, raw6, raw1, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv186 : search 9 0 v186 = false := by decide +kernel

private def v187 : List Sig := [w44, raw2, raw0, raw6, raw1, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv187 : search 9 0 v187 = false := by decide +kernel

private def v188 : List Sig := [w115, raw3, raw0, raw6, raw1, raw2, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv188 : search 9 0 v188 = false := by decide +kernel

private def v189 : List Sig := [w61, raw3, raw0, raw6, raw1, raw2, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv189 : search 9 0 v189 = false := by decide +kernel

private def v190 : List Sig := [w116, raw4, raw0, raw6, raw1, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv190 : search 9 0 v190 = false := by decide +kernel

private def v191 : List Sig := [w117, raw4, raw0, raw6, raw1, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv191 : search 9 0 v191 = false := by decide +kernel

private def v192 : List Sig := [w118, raw4, w95, raw0, raw1, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv192 : search 9 0 v192 = false := by decide +kernel

private def v193 : List Sig := [w119, raw5, raw0, raw6, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv193 : search 9 0 v193 = false := by decide +kernel

private def v194 : List Sig := [w90, raw5, raw0, raw6, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv194 : search 9 0 v194 = false := by decide +kernel

private def v195 : List Sig := [w120, raw5, w95, raw0, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv195 : search 9 0 v195 = false := by decide +kernel

private def v196 : List Sig := [w19, raw7, w95, raw0, raw6, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv196 : search 9 0 v196 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv168 : search 10 0 v168 = false := certifiedStep 9 0 v168
    []
    [⟨v169, rejectv169⟩, ⟨v170, rejectv170⟩, ⟨v171, rejectv171⟩, ⟨v172, rejectv172⟩, ⟨v173, rejectv173⟩, ⟨v174, rejectv174⟩, ⟨v175, rejectv175⟩, ⟨v176, rejectv176⟩, ⟨v177, rejectv177⟩, ⟨v178, rejectv178⟩, ⟨v179, rejectv179⟩, ⟨v180, rejectv180⟩, ⟨v181, rejectv181⟩, ⟨v182, rejectv182⟩, ⟨v183, rejectv183⟩, ⟨v184, rejectv184⟩, ⟨v185, rejectv185⟩, ⟨v186, rejectv186⟩, ⟨v187, rejectv187⟩, ⟨v188, rejectv188⟩, ⟨v189, rejectv189⟩, ⟨v190, rejectv190⟩, ⟨v191, rejectv191⟩, ⟨v192, rejectv192⟩, ⟨v193, rejectv193⟩, ⟨v194, rejectv194⟩, ⟨v195, rejectv195⟩, ⟨v196, rejectv196⟩]
    (by decide +kernel)

private def v197 : List Sig := [w121, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

private def v198 : List Sig := [w11, raw1, raw0, raw7, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv198 : search 9 0 v198 = false := by decide +kernel

private def v199 : List Sig := [w122, raw0, raw7, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv199 : search 9 0 v199 = false := by decide +kernel

private def v200 : List Sig := [w122, w121, raw0, raw7, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv200 : search 9 0 v200 = false := by decide +kernel

private def v201 : List Sig := [w122, raw1, raw0, raw7, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv201 : search 9 0 v201 = false := by decide +kernel

private def v202 : List Sig := [w123, raw2, raw0, raw7, raw1, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv202 : search 9 0 v202 = false := by decide +kernel

private def v203 : List Sig := [w124, raw0, raw7, raw1, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv203 : search 9 0 v203 = false := by decide +kernel

private def v204 : List Sig := [w124, w121, raw0, raw7, raw1, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv204 : search 9 0 v204 = false := by decide +kernel

private def v205 : List Sig := [w124, raw2, raw0, raw7, raw1, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv205 : search 9 0 v205 = false := by decide +kernel

private def v206 : List Sig := [w125, raw3, raw0, raw7, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv206 : search 9 0 v206 = false := by decide +kernel

private def v207 : List Sig := [w126, raw0, raw7, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv207 : search 9 0 v207 = false := by decide +kernel

private def v208 : List Sig := [w126, w121, raw0, raw7, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv208 : search 9 0 v208 = false := by decide +kernel

private def v209 : List Sig := [w126, raw3, raw0, raw7, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv209 : search 9 0 v209 = false := by decide +kernel

private def v210 : List Sig := [w83, raw4, raw0, raw7, raw1, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv210 : search 9 0 v210 = false := by decide +kernel

private def v211 : List Sig := [w127, raw0, raw7, raw1, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv211 : search 9 0 v211 = false := by decide +kernel

private def v212 : List Sig := [w127, w121, raw0, raw7, raw1, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv212 : search 9 0 v212 = false := by decide +kernel

private def v213 : List Sig := [w127, raw4, raw0, raw7, raw1, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv213 : search 9 0 v213 = false := by decide +kernel

private def v214 : List Sig := [w128, raw5, raw0, raw7, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv214 : search 9 0 v214 = false := by decide +kernel

private def v215 : List Sig := [w129, raw0, raw7, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv215 : search 9 0 v215 = false := by decide +kernel

private def v216 : List Sig := [w129, w121, raw0, raw7, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv216 : search 9 0 v216 = false := by decide +kernel

private def v217 : List Sig := [w129, raw5, raw0, raw7, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv217 : search 9 0 v217 = false := by decide +kernel

private def v218 : List Sig := [w130, raw6, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv218 : search 9 0 v218 = false := by decide +kernel

private def v219 : List Sig := [w131, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv219 : search 9 0 v219 = false := by decide +kernel

private def v220 : List Sig := [w131, w121, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv220 : search 9 0 v220 = false := by decide +kernel

private def v221 : List Sig := [w131, raw6, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv221 : search 9 0 v221 = false := by decide +kernel

private def v222 : List Sig := [w132, raw8, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv222 : search 9 0 v222 = false := by decide +kernel

private def v223 : List Sig := [w133, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv223 : search 9 0 v223 = false := by decide +kernel

private def v224 : List Sig := [w133, w121, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv224 : search 9 0 v224 = false := by decide +kernel

private def v225 : List Sig := [w133, raw8, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv225 : search 9 0 v225 = false := by decide +kernel

private def v226 : List Sig := [w15, raw0, w121, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv226 : search 9 0 v226 = false := by decide +kernel

private def v227 : List Sig := [w19, raw7, w121, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv227 : search 9 0 v227 = false := by decide +kernel

private def v228 : List Sig := [w17, raw1, w121, raw0, raw7, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv228 : search 9 0 v228 = false := by decide +kernel

private def v229 : List Sig := [w96, raw5, w121, raw0, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv229 : search 9 0 v229 = false := by decide +kernel

private def v230 : List Sig := [w134, raw6, w121, raw0, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv230 : search 9 0 v230 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv197 : search 10 0 v197 = false := certifiedStep 9 0 v197
    []
    [⟨v198, rejectv198⟩, ⟨v199, rejectv199⟩, ⟨v200, rejectv200⟩, ⟨v201, rejectv201⟩, ⟨v202, rejectv202⟩, ⟨v203, rejectv203⟩, ⟨v204, rejectv204⟩, ⟨v205, rejectv205⟩, ⟨v206, rejectv206⟩, ⟨v207, rejectv207⟩, ⟨v208, rejectv208⟩, ⟨v209, rejectv209⟩, ⟨v210, rejectv210⟩, ⟨v211, rejectv211⟩, ⟨v212, rejectv212⟩, ⟨v213, rejectv213⟩, ⟨v214, rejectv214⟩, ⟨v215, rejectv215⟩, ⟨v216, rejectv216⟩, ⟨v217, rejectv217⟩, ⟨v218, rejectv218⟩, ⟨v219, rejectv219⟩, ⟨v220, rejectv220⟩, ⟨v221, rejectv221⟩, ⟨v222, rejectv222⟩, ⟨v223, rejectv223⟩, ⟨v224, rejectv224⟩, ⟨v225, rejectv225⟩, ⟨v226, rejectv226⟩, ⟨v227, rejectv227⟩, ⟨v228, rejectv228⟩, ⟨v229, rejectv229⟩, ⟨v230, rejectv230⟩]
    (by decide +kernel)

private def v231 : List Sig := [w109, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

private def v232 : List Sig := [w135, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv232 : search 9 0 v232 = false := by decide +kernel

private def v233 : List Sig := [w135, w109, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv233 : search 9 0 v233 = false := by decide +kernel

private def v234 : List Sig := [w135, raw8, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv234 : search 9 0 v234 = false := by decide +kernel

private def v235 : List Sig := [w136, raw8, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv235 : search 9 0 v235 = false := by decide +kernel

private def v236 : List Sig := [w95, raw6, w109, raw7, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv236 : search 9 0 v236 = false := by decide +kernel

private def v237 : List Sig := [w15, raw0, w109, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv237 : search 9 0 v237 = false := by decide +kernel

private def v238 : List Sig := [w19, w109, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv238 : search 9 0 v238 = false := by decide +kernel

private def v239 : List Sig := [w19, raw7, w109, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv239 : search 9 0 v239 = false := by decide +kernel

private def v240 : List Sig := [w19, raw8, w109, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv240 : search 9 0 v240 = false := by decide +kernel

private def v241 : List Sig := [w137, raw1, raw0, raw7, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv241 : search 9 0 v241 = false := by decide +kernel

private def v242 : List Sig := [w28, raw1, raw0, raw7, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv242 : search 9 0 v242 = false := by decide +kernel

private def v243 : List Sig := [w32, raw1, w109, raw0, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv243 : search 9 0 v243 = false := by decide +kernel

private def v244 : List Sig := [w17, raw1, w109, raw0, raw7, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv244 : search 9 0 v244 = false := by decide +kernel

private def v245 : List Sig := [w138, raw2, raw0, raw7, raw1, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv245 : search 9 0 v245 = false := by decide +kernel

private def v246 : List Sig := [w46, raw2, raw0, raw7, raw1, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv246 : search 9 0 v246 = false := by decide +kernel

private def v247 : List Sig := [w139, raw3, raw0, raw7, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv247 : search 9 0 v247 = false := by decide +kernel

private def v248 : List Sig := [w63, raw3, raw0, raw7, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv248 : search 9 0 v248 = false := by decide +kernel

private def v249 : List Sig := [w140, raw4, raw0, raw7, raw1, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv249 : search 9 0 v249 = false := by decide +kernel

private def v250 : List Sig := [w141, raw4, raw0, raw7, raw1, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv250 : search 9 0 v250 = false := by decide +kernel

private def v251 : List Sig := [w142, raw5, raw0, raw7, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv251 : search 9 0 v251 = false := by decide +kernel

private def v252 : List Sig := [w92, raw5, raw0, raw7, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv252 : search 9 0 v252 = false := by decide +kernel

private def v253 : List Sig := [w143, raw6, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv253 : search 9 0 v253 = false := by decide +kernel

private def v254 : List Sig := [w106, raw6, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv254 : search 9 0 v254 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv231 : search 10 0 v231 = false := certifiedStep 9 0 v231
    []
    [⟨v232, rejectv232⟩, ⟨v233, rejectv233⟩, ⟨v234, rejectv234⟩, ⟨v235, rejectv235⟩, ⟨v236, rejectv236⟩, ⟨v237, rejectv237⟩, ⟨v238, rejectv238⟩, ⟨v239, rejectv239⟩, ⟨v240, rejectv240⟩, ⟨v241, rejectv241⟩, ⟨v242, rejectv242⟩, ⟨v243, rejectv243⟩, ⟨v244, rejectv244⟩, ⟨v245, rejectv245⟩, ⟨v246, rejectv246⟩, ⟨v247, rejectv247⟩, ⟨v248, rejectv248⟩, ⟨v249, rejectv249⟩, ⟨v250, rejectv250⟩, ⟨v251, rejectv251⟩, ⟨v252, rejectv252⟩, ⟨v253, rejectv253⟩, ⟨v254, rejectv254⟩]
    (by decide +kernel)

private def v255 : List Sig := [w15, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

private def v256 : List Sig := [w13, w15, raw1, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv256 : search 9 0 v256 = false := by decide +kernel

private def v257 : List Sig := [w144, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

private def v258 : List Sig := [w145, w144, raw3, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv258 : search 8 0 v258 = false := by decide +kernel

private def v259 : List Sig := [w146, w144, raw3, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv259 : search 8 0 v259 = false := by decide +kernel

private def v260 : List Sig := [w147, w144, raw5, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv260 : search 8 0 v260 = false := by decide +kernel

private def v261 : List Sig := [w148, w144, raw5, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv261 : search 8 0 v261 = false := by decide +kernel

private def v262 : List Sig := [w149, w144, raw6, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv262 : search 8 0 v262 = false := by decide +kernel

private def v263 : List Sig := [w150, w144, raw6, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv263 : search 8 0 v263 = false := by decide +kernel

private def v264 : List Sig := [w151, w144, raw7, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv264 : search 8 0 v264 = false := by decide +kernel

private def v265 : List Sig := [w152, w144, raw7, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv265 : search 8 0 v265 = false := by decide +kernel

private def v266 : List Sig := [w153, raw0, w144, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv266 : search 8 0 v266 = false := by decide +kernel

private def v267 : List Sig := [w20, raw0, w144, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv267 : search 8 0 v267 = false := by decide +kernel

private def v268 : List Sig := [w37, raw0, raw2, w144, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv268 : search 8 0 v268 = false := by decide +kernel

private def v269 : List Sig := [w31, raw0, raw2, w144, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv269 : search 8 0 v269 = false := by decide +kernel

private def v270 : List Sig := [w57, raw0, raw3, w144, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv270 : search 8 0 v270 = false := by decide +kernel

private def v271 : List Sig := [w49, raw0, raw3, w144, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv271 : search 8 0 v271 = false := by decide +kernel

private def v272 : List Sig := [w73, raw0, raw4, w144, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv272 : search 8 0 v272 = false := by decide +kernel

private def v273 : List Sig := [w66, raw0, raw4, w144, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv273 : search 8 0 v273 = false := by decide +kernel

private def v274 : List Sig := [w87, raw0, raw5, w144, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv274 : search 8 0 v274 = false := by decide +kernel

private def v275 : List Sig := [w88, raw0, raw5, w144, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv275 : search 8 0 v275 = false := by decide +kernel

private def v276 : List Sig := [w104, raw0, raw6, w144, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv276 : search 8 0 v276 = false := by decide +kernel

private def v277 : List Sig := [w95, raw0, raw6, w144, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv277 : search 8 0 v277 = false := by decide +kernel

private def v278 : List Sig := [w121, raw0, raw7, w144, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv278 : search 8 0 v278 = false := by decide +kernel

private def v279 : List Sig := [w109, raw0, raw7, w144, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv279 : search 8 0 v279 = false := by decide +kernel

private def v280 : List Sig := [w154, raw2, w144, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv280 : search 8 0 v280 = false := by decide +kernel

private def v281 : List Sig := [w155, raw2, w144, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv281 : search 8 0 v281 = false := by decide +kernel

private def v282 : List Sig := [w51, raw2, raw3, w144, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv282 : search 8 0 v282 = false := by decide +kernel

private def v283 : List Sig := [w156, raw2, raw3, w144, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv283 : search 8 0 v283 = false := by decide +kernel

private def v284 : List Sig := [w157, raw2, raw5, w144, raw0, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv284 : search 8 0 v284 = false := by decide +kernel

private def v285 : List Sig := [w158, raw2, raw5, w144, raw0, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv285 : search 8 0 v285 = false := by decide +kernel

private def v286 : List Sig := [w159, raw2, raw6, w144, raw0, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv286 : search 8 0 v286 = false := by decide +kernel

private def v287 : List Sig := [w160, raw2, raw6, w144, raw0, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv287 : search 8 0 v287 = false := by decide +kernel

private def v288 : List Sig := [w161, raw2, raw7, w144, raw0, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv288 : search 8 0 v288 = false := by decide +kernel

private def v289 : List Sig := [w52, raw2, raw7, w144, raw0, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv289 : search 8 0 v289 = false := by decide +kernel

private def v290 : List Sig := [w162, raw3, raw5, w144, raw0, raw2, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv290 : search 8 0 v290 = false := by decide +kernel

private def v291 : List Sig := [w163, raw3, raw5, w144, raw0, raw2, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv291 : search 8 0 v291 = false := by decide +kernel

private def v292 : List Sig := [w164, raw3, raw6, w144, raw0, raw2, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv292 : search 8 0 v292 = false := by decide +kernel

private def v293 : List Sig := [w165, raw3, raw6, w144, raw0, raw2, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv293 : search 8 0 v293 = false := by decide +kernel

private def v294 : List Sig := [w166, raw3, raw7, w144, raw0, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv294 : search 8 0 v294 = false := by decide +kernel

private def v295 : List Sig := [w67, raw3, raw7, w144, raw0, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv295 : search 8 0 v295 = false := by decide +kernel

private def v296 : List Sig := [w167, raw4, w144, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv296 : search 8 0 v296 = false := by decide +kernel

private def v297 : List Sig := [w168, raw4, w144, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv297 : search 8 0 v297 = false := by decide +kernel

private def v298 : List Sig := [w169, raw4, raw2, w144, raw0, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv298 : search 8 0 v298 = false := by decide +kernel

private def v299 : List Sig := [w56, raw4, raw2, w144, raw0, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv299 : search 8 0 v299 = false := by decide +kernel

private def v300 : List Sig := [w170, raw4, raw3, w144, raw0, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv300 : search 8 0 v300 = false := by decide +kernel

private def v301 : List Sig := [w171, raw4, raw3, w144, raw0, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv301 : search 8 0 v301 = false := by decide +kernel

private def v302 : List Sig := [w172, raw4, raw5, w144, raw0, raw2, raw3, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv302 : search 8 0 v302 = false := by decide +kernel

private def v303 : List Sig := [w173, raw4, raw5, w144, raw0, raw2, raw3, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv303 : search 8 0 v303 = false := by decide +kernel

private def v304 : List Sig := [w174, raw4, raw6, w144, raw0, raw2, raw3, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv304 : search 8 0 v304 = false := by decide +kernel

private def v305 : List Sig := [w118, raw4, raw6, w144, raw0, raw2, raw3, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv305 : search 8 0 v305 = false := by decide +kernel

private def v306 : List Sig := [w175, raw4, raw7, w144, raw0, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv306 : search 8 0 v306 = false := by decide +kernel

private def v307 : List Sig := [w176, raw4, raw7, w144, raw0, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv307 : search 8 0 v307 = false := by decide +kernel

private def v308 : List Sig := [w120, raw5, raw6, w144, raw0, raw2, raw3, raw4, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv308 : search 8 0 v308 = false := by decide +kernel

private def v309 : List Sig := [w177, raw5, raw6, w144, raw0, raw2, raw3, raw4, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv309 : search 8 0 v309 = false := by decide +kernel

private def v310 : List Sig := [w178, raw5, raw7, w144, raw0, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv310 : search 8 0 v310 = false := by decide +kernel

private def v311 : List Sig := [w96, raw5, raw7, w144, raw0, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv311 : search 8 0 v311 = false := by decide +kernel

private def v312 : List Sig := [w134, raw6, raw7, w144, raw0, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv312 : search 8 0 v312 = false := by decide +kernel

private def v313 : List Sig := [w110, raw6, raw7, w144, raw0, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv313 : search 8 0 v313 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv257 : search 9 0 v257 = false := certifiedStep 8 0 v257
    []
    [⟨v258, rejectv258⟩, ⟨v259, rejectv259⟩, ⟨v260, rejectv260⟩, ⟨v261, rejectv261⟩, ⟨v262, rejectv262⟩, ⟨v263, rejectv263⟩, ⟨v264, rejectv264⟩, ⟨v265, rejectv265⟩, ⟨v266, rejectv266⟩, ⟨v267, rejectv267⟩, ⟨v268, rejectv268⟩, ⟨v269, rejectv269⟩, ⟨v270, rejectv270⟩, ⟨v271, rejectv271⟩, ⟨v272, rejectv272⟩, ⟨v273, rejectv273⟩, ⟨v274, rejectv274⟩, ⟨v275, rejectv275⟩, ⟨v276, rejectv276⟩, ⟨v277, rejectv277⟩, ⟨v278, rejectv278⟩, ⟨v279, rejectv279⟩, ⟨v280, rejectv280⟩, ⟨v281, rejectv281⟩, ⟨v282, rejectv282⟩, ⟨v283, rejectv283⟩, ⟨v284, rejectv284⟩, ⟨v285, rejectv285⟩, ⟨v286, rejectv286⟩, ⟨v287, rejectv287⟩, ⟨v288, rejectv288⟩, ⟨v289, rejectv289⟩, ⟨v290, rejectv290⟩, ⟨v291, rejectv291⟩, ⟨v292, rejectv292⟩, ⟨v293, rejectv293⟩, ⟨v294, rejectv294⟩, ⟨v295, rejectv295⟩, ⟨v296, rejectv296⟩, ⟨v297, rejectv297⟩, ⟨v298, rejectv298⟩, ⟨v299, rejectv299⟩, ⟨v300, rejectv300⟩, ⟨v301, rejectv301⟩, ⟨v302, rejectv302⟩, ⟨v303, rejectv303⟩, ⟨v304, rejectv304⟩, ⟨v305, rejectv305⟩, ⟨v306, rejectv306⟩, ⟨v307, rejectv307⟩, ⟨v308, rejectv308⟩, ⟨v309, rejectv309⟩, ⟨v310, rejectv310⟩, ⟨v311, rejectv311⟩, ⟨v312, rejectv312⟩, ⟨v313, rejectv313⟩]
    (by decide +kernel)

private def v314 : List Sig := [w144, w15, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

private def v315 : List Sig := [w179, raw2, w144, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv315 : search 8 0 v315 = false := by decide +kernel

private def v316 : List Sig := [w180, w144, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv316 : search 8 0 v316 = false := by decide +kernel

private def v317 : List Sig := [w180, w15, w144, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv317 : search 8 0 v317 = false := by decide +kernel

private def v318 : List Sig := [w180, raw2, w144, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv318 : search 8 0 v318 = false := by decide +kernel

private def v319 : List Sig := [w181, raw3, w144, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv319 : search 8 0 v319 = false := by decide +kernel

private def v320 : List Sig := [w182, w144, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv320 : search 8 0 v320 = false := by decide +kernel

private def v321 : List Sig := [w182, w15, w144, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv321 : search 8 0 v321 = false := by decide +kernel

private def v322 : List Sig := [w182, raw3, w144, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv322 : search 8 0 v322 = false := by decide +kernel

private def v323 : List Sig := [w85, raw4, w144, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv323 : search 8 0 v323 = false := by decide +kernel

private def v324 : List Sig := [w183, w144, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv324 : search 8 0 v324 = false := by decide +kernel

private def v325 : List Sig := [w183, w15, w144, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv325 : search 8 0 v325 = false := by decide +kernel

private def v326 : List Sig := [w183, raw4, w144, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv326 : search 8 0 v326 = false := by decide +kernel

private def v327 : List Sig := [w184, raw5, w144, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv327 : search 8 0 v327 = false := by decide +kernel

private def v328 : List Sig := [w185, w144, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv328 : search 8 0 v328 = false := by decide +kernel

private def v329 : List Sig := [w185, w15, w144, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv329 : search 8 0 v329 = false := by decide +kernel

private def v330 : List Sig := [w185, raw5, w144, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv330 : search 8 0 v330 = false := by decide +kernel

private def v331 : List Sig := [w186, raw6, w144, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv331 : search 8 0 v331 = false := by decide +kernel

private def v332 : List Sig := [w187, w144, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv332 : search 8 0 v332 = false := by decide +kernel

private def v333 : List Sig := [w187, w15, w144, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv333 : search 8 0 v333 = false := by decide +kernel

private def v334 : List Sig := [w187, raw6, w144, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv334 : search 8 0 v334 = false := by decide +kernel

private def v335 : List Sig := [w132, raw7, w144, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv335 : search 8 0 v335 = false := by decide +kernel

private def v336 : List Sig := [w188, w144, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv336 : search 8 0 v336 = false := by decide +kernel

private def v337 : List Sig := [w188, w15, w144, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv337 : search 8 0 v337 = false := by decide +kernel

private def v338 : List Sig := [w188, raw7, w144, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv338 : search 8 0 v338 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv314 : search 9 0 v314 = false := certifiedStep 8 0 v314
    []
    [⟨v315, rejectv315⟩, ⟨v316, rejectv316⟩, ⟨v317, rejectv317⟩, ⟨v318, rejectv318⟩, ⟨v319, rejectv319⟩, ⟨v320, rejectv320⟩, ⟨v321, rejectv321⟩, ⟨v322, rejectv322⟩, ⟨v323, rejectv323⟩, ⟨v324, rejectv324⟩, ⟨v325, rejectv325⟩, ⟨v326, rejectv326⟩, ⟨v327, rejectv327⟩, ⟨v328, rejectv328⟩, ⟨v329, rejectv329⟩, ⟨v330, rejectv330⟩, ⟨v331, rejectv331⟩, ⟨v332, rejectv332⟩, ⟨v333, rejectv333⟩, ⟨v334, rejectv334⟩, ⟨v335, rejectv335⟩, ⟨v336, rejectv336⟩, ⟨v337, rejectv337⟩, ⟨v338, rejectv338⟩]
    (by decide +kernel)

private def v339 : List Sig := [w144, raw1, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv339 : search 9 0 v339 = false := by decide +kernel

private def v340 : List Sig := [w144, w15, raw1, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv340 : search 9 0 v340 = false := by decide +kernel

private def v341 : List Sig := [w179, w15, raw2, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv341 : search 9 0 v341 = false := by decide +kernel

private def v342 : List Sig := [w180, w15, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv342 : search 9 0 v342 = false := by decide +kernel

private def v343 : List Sig := [w180, w15, raw2, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv343 : search 9 0 v343 = false := by decide +kernel

private def v344 : List Sig := [w181, w15, raw3, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv344 : search 9 0 v344 = false := by decide +kernel

private def v345 : List Sig := [w182, w15, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv345 : search 9 0 v345 = false := by decide +kernel

private def v346 : List Sig := [w182, w15, raw3, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv346 : search 9 0 v346 = false := by decide +kernel

private def v347 : List Sig := [w85, w15, raw4, raw0, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv347 : search 9 0 v347 = false := by decide +kernel

private def v348 : List Sig := [w183, w15, raw0, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv348 : search 9 0 v348 = false := by decide +kernel

private def v349 : List Sig := [w183, w15, raw4, raw0, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv349 : search 9 0 v349 = false := by decide +kernel

private def v350 : List Sig := [w184, w15, raw5, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv350 : search 9 0 v350 = false := by decide +kernel

private def v351 : List Sig := [w185, w15, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv351 : search 9 0 v351 = false := by decide +kernel

private def v352 : List Sig := [w185, w15, raw5, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv352 : search 9 0 v352 = false := by decide +kernel

private def v353 : List Sig := [w186, w15, raw6, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv353 : search 9 0 v353 = false := by decide +kernel

private def v354 : List Sig := [w187, w15, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv354 : search 9 0 v354 = false := by decide +kernel

private def v355 : List Sig := [w187, w15, raw6, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv355 : search 9 0 v355 = false := by decide +kernel

private def v356 : List Sig := [w132, w15, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv356 : search 9 0 v356 = false := by decide +kernel

private def v357 : List Sig := [w188, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

private def v358 : List Sig := [w189, raw0, w188, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv358 : search 8 0 v358 = false := by decide +kernel

private def v359 : List Sig := [w109, raw0, w188, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv359 : search 8 0 v359 = false := by decide +kernel

private def v360 : List Sig := [w0, raw0, raw1, w188, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv360 : search 8 0 v360 = false := by decide +kernel

private def v361 : List Sig := [w20, raw0, raw1, w188, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv361 : search 8 0 v361 = false := by decide +kernel

private def v362 : List Sig := [w37, raw0, raw2, w188, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv362 : search 8 0 v362 = false := by decide +kernel

private def v363 : List Sig := [w31, raw0, raw2, w188, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv363 : search 8 0 v363 = false := by decide +kernel

private def v364 : List Sig := [w57, raw0, raw3, w188, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv364 : search 8 0 v364 = false := by decide +kernel

private def v365 : List Sig := [w49, raw0, raw3, w188, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv365 : search 8 0 v365 = false := by decide +kernel

private def v366 : List Sig := [w73, raw0, raw4, w188, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv366 : search 8 0 v366 = false := by decide +kernel

private def v367 : List Sig := [w66, raw0, raw4, w188, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv367 : search 8 0 v367 = false := by decide +kernel

private def v368 : List Sig := [w87, raw0, raw5, w188, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv368 : search 8 0 v368 = false := by decide +kernel

private def v369 : List Sig := [w88, raw0, raw5, w188, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv369 : search 8 0 v369 = false := by decide +kernel

private def v370 : List Sig := [w104, raw0, raw6, w188, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv370 : search 8 0 v370 = false := by decide +kernel

private def v371 : List Sig := [w95, raw0, raw6, w188, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv371 : search 8 0 v371 = false := by decide +kernel

private def v372 : List Sig := [w190, raw1, w188, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv372 : search 8 0 v372 = false := by decide +kernel

private def v373 : List Sig := [w152, raw1, w188, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv373 : search 8 0 v373 = false := by decide +kernel

private def v374 : List Sig := [w191, raw1, raw3, w188, raw0, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv374 : search 8 0 v374 = false := by decide +kernel

private def v375 : List Sig := [w16, raw1, raw3, w188, raw0, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv375 : search 8 0 v375 = false := by decide +kernel

private def v376 : List Sig := [w192, raw1, raw5, w188, raw0, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv376 : search 8 0 v376 = false := by decide +kernel

private def v377 : List Sig := [w99, raw1, raw5, w188, raw0, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv377 : search 8 0 v377 = false := by decide +kernel

private def v378 : List Sig := [w193, raw1, raw6, w188, raw0, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv378 : search 8 0 v378 = false := by decide +kernel

private def v379 : List Sig := [w113, raw1, raw6, w188, raw0, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv379 : search 8 0 v379 = false := by decide +kernel

private def v380 : List Sig := [w194, raw2, w188, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv380 : search 8 0 v380 = false := by decide +kernel

private def v381 : List Sig := [w195, raw2, w188, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv381 : search 8 0 v381 = false := by decide +kernel

private def v382 : List Sig := [w18, raw2, raw1, w188, raw0, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv382 : search 8 0 v382 = false := by decide +kernel

private def v383 : List Sig := [w50, raw2, raw1, w188, raw0, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv383 : search 8 0 v383 = false := by decide +kernel

private def v384 : List Sig := [w51, raw2, raw3, w188, raw0, raw1, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv384 : search 8 0 v384 = false := by decide +kernel

private def v385 : List Sig := [w156, raw2, raw3, w188, raw0, raw1, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv385 : search 8 0 v385 = false := by decide +kernel

private def v386 : List Sig := [w157, raw2, raw5, w188, raw0, raw1, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv386 : search 8 0 v386 = false := by decide +kernel

private def v387 : List Sig := [w158, raw2, raw5, w188, raw0, raw1, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv387 : search 8 0 v387 = false := by decide +kernel

private def v388 : List Sig := [w159, raw2, raw6, w188, raw0, raw1, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv388 : search 8 0 v388 = false := by decide +kernel

private def v389 : List Sig := [w160, raw2, raw6, w188, raw0, raw1, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv389 : search 8 0 v389 = false := by decide +kernel

private def v390 : List Sig := [w196, raw3, w188, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv390 : search 8 0 v390 = false := by decide +kernel

private def v391 : List Sig := [w197, raw3, w188, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv391 : search 8 0 v391 = false := by decide +kernel

private def v392 : List Sig := [w162, raw3, raw5, w188, raw0, raw1, raw2, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv392 : search 8 0 v392 = false := by decide +kernel

private def v393 : List Sig := [w163, raw3, raw5, w188, raw0, raw1, raw2, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv393 : search 8 0 v393 = false := by decide +kernel

private def v394 : List Sig := [w164, raw3, raw6, w188, raw0, raw1, raw2, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv394 : search 8 0 v394 = false := by decide +kernel

private def v395 : List Sig := [w165, raw3, raw6, w188, raw0, raw1, raw2, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv395 : search 8 0 v395 = false := by decide +kernel

private def v396 : List Sig := [w198, raw4, w188, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv396 : search 8 0 v396 = false := by decide +kernel

private def v397 : List Sig := [w199, raw4, w188, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv397 : search 8 0 v397 = false := by decide +kernel

private def v398 : List Sig := [w200, raw4, raw1, w188, raw0, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv398 : search 8 0 v398 = false := by decide +kernel

private def v399 : List Sig := [w201, raw4, raw1, w188, raw0, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv399 : search 8 0 v399 = false := by decide +kernel

private def v400 : List Sig := [w169, raw4, raw2, w188, raw0, raw1, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv400 : search 8 0 v400 = false := by decide +kernel

private def v401 : List Sig := [w56, raw4, raw2, w188, raw0, raw1, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv401 : search 8 0 v401 = false := by decide +kernel

private def v402 : List Sig := [w170, raw4, raw3, w188, raw0, raw1, raw2, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv402 : search 8 0 v402 = false := by decide +kernel

private def v403 : List Sig := [w171, raw4, raw3, w188, raw0, raw1, raw2, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv403 : search 8 0 v403 = false := by decide +kernel

private def v404 : List Sig := [w172, raw4, raw5, w188, raw0, raw1, raw2, raw3, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv404 : search 8 0 v404 = false := by decide +kernel

private def v405 : List Sig := [w173, raw4, raw5, w188, raw0, raw1, raw2, raw3, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv405 : search 8 0 v405 = false := by decide +kernel

private def v406 : List Sig := [w174, raw4, raw6, w188, raw0, raw1, raw2, raw3, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv406 : search 8 0 v406 = false := by decide +kernel

private def v407 : List Sig := [w118, raw4, raw6, w188, raw0, raw1, raw2, raw3, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv407 : search 8 0 v407 = false := by decide +kernel

private def v408 : List Sig := [w202, raw5, w188, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv408 : search 8 0 v408 = false := by decide +kernel

private def v409 : List Sig := [w203, raw5, w188, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv409 : search 8 0 v409 = false := by decide +kernel

private def v410 : List Sig := [w120, raw5, raw6, w188, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv410 : search 8 0 v410 = false := by decide +kernel

private def v411 : List Sig := [w177, raw5, raw6, w188, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv411 : search 8 0 v411 = false := by decide +kernel

private def v412 : List Sig := [w204, raw6, w188, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv412 : search 8 0 v412 = false := by decide +kernel

private def v413 : List Sig := [w205, raw6, w188, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv413 : search 8 0 v413 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv357 : search 9 0 v357 = false := certifiedStep 8 0 v357
    []
    [⟨v358, rejectv358⟩, ⟨v359, rejectv359⟩, ⟨v360, rejectv360⟩, ⟨v361, rejectv361⟩, ⟨v362, rejectv362⟩, ⟨v363, rejectv363⟩, ⟨v364, rejectv364⟩, ⟨v365, rejectv365⟩, ⟨v366, rejectv366⟩, ⟨v367, rejectv367⟩, ⟨v368, rejectv368⟩, ⟨v369, rejectv369⟩, ⟨v370, rejectv370⟩, ⟨v371, rejectv371⟩, ⟨v372, rejectv372⟩, ⟨v373, rejectv373⟩, ⟨v374, rejectv374⟩, ⟨v375, rejectv375⟩, ⟨v376, rejectv376⟩, ⟨v377, rejectv377⟩, ⟨v378, rejectv378⟩, ⟨v379, rejectv379⟩, ⟨v380, rejectv380⟩, ⟨v381, rejectv381⟩, ⟨v382, rejectv382⟩, ⟨v383, rejectv383⟩, ⟨v384, rejectv384⟩, ⟨v385, rejectv385⟩, ⟨v386, rejectv386⟩, ⟨v387, rejectv387⟩, ⟨v388, rejectv388⟩, ⟨v389, rejectv389⟩, ⟨v390, rejectv390⟩, ⟨v391, rejectv391⟩, ⟨v392, rejectv392⟩, ⟨v393, rejectv393⟩, ⟨v394, rejectv394⟩, ⟨v395, rejectv395⟩, ⟨v396, rejectv396⟩, ⟨v397, rejectv397⟩, ⟨v398, rejectv398⟩, ⟨v399, rejectv399⟩, ⟨v400, rejectv400⟩, ⟨v401, rejectv401⟩, ⟨v402, rejectv402⟩, ⟨v403, rejectv403⟩, ⟨v404, rejectv404⟩, ⟨v405, rejectv405⟩, ⟨v406, rejectv406⟩, ⟨v407, rejectv407⟩, ⟨v408, rejectv408⟩, ⟨v409, rejectv409⟩, ⟨v410, rejectv410⟩, ⟨v411, rejectv411⟩, ⟨v412, rejectv412⟩, ⟨v413, rejectv413⟩]
    (by decide +kernel)

private def v414 : List Sig := [w188, w15, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

private def v415 : List Sig := [w13, raw1, w188, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv415 : search 8 0 v415 = false := by decide +kernel

private def v416 : List Sig := [w144, w188, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv416 : search 8 0 v416 = false := by decide +kernel

private def v417 : List Sig := [w144, w15, w188, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv417 : search 8 0 v417 = false := by decide +kernel

private def v418 : List Sig := [w144, raw1, w188, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv418 : search 8 0 v418 = false := by decide +kernel

private def v419 : List Sig := [w179, raw2, w188, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv419 : search 8 0 v419 = false := by decide +kernel

private def v420 : List Sig := [w180, w188, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv420 : search 8 0 v420 = false := by decide +kernel

private def v421 : List Sig := [w180, w15, w188, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv421 : search 8 0 v421 = false := by decide +kernel

private def v422 : List Sig := [w180, raw2, w188, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv422 : search 8 0 v422 = false := by decide +kernel

private def v423 : List Sig := [w181, raw3, w188, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv423 : search 8 0 v423 = false := by decide +kernel

private def v424 : List Sig := [w182, w188, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv424 : search 8 0 v424 = false := by decide +kernel

private def v425 : List Sig := [w182, w15, w188, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv425 : search 8 0 v425 = false := by decide +kernel

private def v426 : List Sig := [w182, raw3, w188, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv426 : search 8 0 v426 = false := by decide +kernel

private def v427 : List Sig := [w85, raw4, w188, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv427 : search 8 0 v427 = false := by decide +kernel

private def v428 : List Sig := [w183, w188, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv428 : search 8 0 v428 = false := by decide +kernel

private def v429 : List Sig := [w183, w15, w188, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv429 : search 8 0 v429 = false := by decide +kernel

private def v430 : List Sig := [w183, raw4, w188, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv430 : search 8 0 v430 = false := by decide +kernel

private def v431 : List Sig := [w184, raw5, w188, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv431 : search 8 0 v431 = false := by decide +kernel

private def v432 : List Sig := [w185, w188, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv432 : search 8 0 v432 = false := by decide +kernel

private def v433 : List Sig := [w185, w15, w188, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv433 : search 8 0 v433 = false := by decide +kernel

private def v434 : List Sig := [w185, raw5, w188, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv434 : search 8 0 v434 = false := by decide +kernel

private def v435 : List Sig := [w186, raw6, w188, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv435 : search 8 0 v435 = false := by decide +kernel

private def v436 : List Sig := [w187, w188, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv436 : search 8 0 v436 = false := by decide +kernel

private def v437 : List Sig := [w187, w15, w188, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv437 : search 8 0 v437 = false := by decide +kernel

private def v438 : List Sig := [w187, raw6, w188, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv438 : search 8 0 v438 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv414 : search 9 0 v414 = false := certifiedStep 8 0 v414
    []
    [⟨v415, rejectv415⟩, ⟨v416, rejectv416⟩, ⟨v417, rejectv417⟩, ⟨v418, rejectv418⟩, ⟨v419, rejectv419⟩, ⟨v420, rejectv420⟩, ⟨v421, rejectv421⟩, ⟨v422, rejectv422⟩, ⟨v423, rejectv423⟩, ⟨v424, rejectv424⟩, ⟨v425, rejectv425⟩, ⟨v426, rejectv426⟩, ⟨v427, rejectv427⟩, ⟨v428, rejectv428⟩, ⟨v429, rejectv429⟩, ⟨v430, rejectv430⟩, ⟨v431, rejectv431⟩, ⟨v432, rejectv432⟩, ⟨v433, rejectv433⟩, ⟨v434, rejectv434⟩, ⟨v435, rejectv435⟩, ⟨v436, rejectv436⟩, ⟨v437, rejectv437⟩, ⟨v438, rejectv438⟩]
    (by decide +kernel)

private def v439 : List Sig := [w188, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv439 : search 9 0 v439 = false := by decide +kernel

private def v440 : List Sig := [w188, w15, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv440 : search 9 0 v440 = false := by decide +kernel

private def v441 : List Sig := [w0, raw0, raw1, w15, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv441 : search 9 0 v441 = false := by decide +kernel

private def v442 : List Sig := [w20, raw0, raw1, w15, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv442 : search 9 0 v442 = false := by decide +kernel

private def v443 : List Sig := [w37, raw0, raw2, w15, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv443 : search 9 0 v443 = false := by decide +kernel

private def v444 : List Sig := [w31, raw0, raw2, w15, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv444 : search 9 0 v444 = false := by decide +kernel

private def v445 : List Sig := [w57, raw0, raw3, w15, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv445 : search 9 0 v445 = false := by decide +kernel

private def v446 : List Sig := [w49, raw0, raw3, w15, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv446 : search 9 0 v446 = false := by decide +kernel

private def v447 : List Sig := [w73, raw0, raw4, w15, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv447 : search 9 0 v447 = false := by decide +kernel

private def v448 : List Sig := [w66, raw0, raw4, w15, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv448 : search 9 0 v448 = false := by decide +kernel

private def v449 : List Sig := [w87, raw0, raw5, w15, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv449 : search 9 0 v449 = false := by decide +kernel

private def v450 : List Sig := [w88, raw0, raw5, w15, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv450 : search 9 0 v450 = false := by decide +kernel

private def v451 : List Sig := [w104, raw0, raw6, w15, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv451 : search 9 0 v451 = false := by decide +kernel

private def v452 : List Sig := [w95, raw0, raw6, w15, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv452 : search 9 0 v452 = false := by decide +kernel

private def v453 : List Sig := [w121, raw0, raw7, w15, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv453 : search 9 0 v453 = false := by decide +kernel

private def v454 : List Sig := [w109, raw0, raw7, w15, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv454 : search 9 0 v454 = false := by decide +kernel

private def v455 : List Sig := [w191, raw1, raw3, w15, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv455 : search 9 0 v455 = false := by decide +kernel

private def v456 : List Sig := [w16, raw1, raw3, w15, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv456 : search 9 0 v456 = false := by decide +kernel

private def v457 : List Sig := [w192, raw1, raw5, w15, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv457 : search 9 0 v457 = false := by decide +kernel

private def v458 : List Sig := [w99, raw1, raw5, w15, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv458 : search 9 0 v458 = false := by decide +kernel

private def v459 : List Sig := [w193, raw1, raw6, w15, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv459 : search 9 0 v459 = false := by decide +kernel

private def v460 : List Sig := [w113, raw1, raw6, w15, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv460 : search 9 0 v460 = false := by decide +kernel

private def v461 : List Sig := [w206, raw1, raw7, w15, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv461 : search 9 0 v461 = false := by decide +kernel

private def v462 : List Sig := [w32, raw1, raw7, w15, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv462 : search 9 0 v462 = false := by decide +kernel

private def v463 : List Sig := [w18, raw2, raw1, w15, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv463 : search 9 0 v463 = false := by decide +kernel

private def v464 : List Sig := [w50, raw2, raw1, w15, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv464 : search 9 0 v464 = false := by decide +kernel

private def v465 : List Sig := [w51, raw2, raw3, w15, raw0, raw1, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv465 : search 9 0 v465 = false := by decide +kernel

private def v466 : List Sig := [w156, raw2, raw3, w15, raw0, raw1, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv466 : search 9 0 v466 = false := by decide +kernel

private def v467 : List Sig := [w157, raw2, raw5, w15, raw0, raw1, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv467 : search 9 0 v467 = false := by decide +kernel

private def v468 : List Sig := [w158, raw2, raw5, w15, raw0, raw1, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv468 : search 9 0 v468 = false := by decide +kernel

private def v469 : List Sig := [w159, raw2, raw6, w15, raw0, raw1, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv469 : search 9 0 v469 = false := by decide +kernel

private def v470 : List Sig := [w160, raw2, raw6, w15, raw0, raw1, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv470 : search 9 0 v470 = false := by decide +kernel

private def v471 : List Sig := [w161, raw2, raw7, w15, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv471 : search 9 0 v471 = false := by decide +kernel

private def v472 : List Sig := [w52, raw2, raw7, w15, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv472 : search 9 0 v472 = false := by decide +kernel

private def v473 : List Sig := [w162, raw3, raw5, w15, raw0, raw1, raw2, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv473 : search 9 0 v473 = false := by decide +kernel

private def v474 : List Sig := [w163, raw3, raw5, w15, raw0, raw1, raw2, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv474 : search 9 0 v474 = false := by decide +kernel

private def v475 : List Sig := [w164, raw3, raw6, w15, raw0, raw1, raw2, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv475 : search 9 0 v475 = false := by decide +kernel

private def v476 : List Sig := [w165, raw3, raw6, w15, raw0, raw1, raw2, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv476 : search 9 0 v476 = false := by decide +kernel

private def v477 : List Sig := [w166, raw3, raw7, w15, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv477 : search 9 0 v477 = false := by decide +kernel

private def v478 : List Sig := [w67, raw3, raw7, w15, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv478 : search 9 0 v478 = false := by decide +kernel

private def v479 : List Sig := [w200, raw4, raw1, w15, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv479 : search 9 0 v479 = false := by decide +kernel

private def v480 : List Sig := [w201, raw4, raw1, w15, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv480 : search 9 0 v480 = false := by decide +kernel

private def v481 : List Sig := [w169, raw4, raw2, w15, raw0, raw1, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv481 : search 9 0 v481 = false := by decide +kernel

private def v482 : List Sig := [w56, raw4, raw2, w15, raw0, raw1, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv482 : search 9 0 v482 = false := by decide +kernel

private def v483 : List Sig := [w170, raw4, raw3, w15, raw0, raw1, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv483 : search 9 0 v483 = false := by decide +kernel

private def v484 : List Sig := [w171, raw4, raw3, w15, raw0, raw1, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv484 : search 9 0 v484 = false := by decide +kernel

private def v485 : List Sig := [w172, raw4, raw5, w15, raw0, raw1, raw2, raw3, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv485 : search 9 0 v485 = false := by decide +kernel

private def v486 : List Sig := [w173, raw4, raw5, w15, raw0, raw1, raw2, raw3, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv486 : search 9 0 v486 = false := by decide +kernel

private def v487 : List Sig := [w174, raw4, raw6, w15, raw0, raw1, raw2, raw3, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv487 : search 9 0 v487 = false := by decide +kernel

private def v488 : List Sig := [w118, raw4, raw6, w15, raw0, raw1, raw2, raw3, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv488 : search 9 0 v488 = false := by decide +kernel

private def v489 : List Sig := [w175, raw4, raw7, w15, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv489 : search 9 0 v489 = false := by decide +kernel

private def v490 : List Sig := [w176, raw4, raw7, w15, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv490 : search 9 0 v490 = false := by decide +kernel

private def v491 : List Sig := [w120, raw5, raw6, w15, raw0, raw1, raw2, raw3, raw4, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv491 : search 9 0 v491 = false := by decide +kernel

private def v492 : List Sig := [w177, raw5, raw6, w15, raw0, raw1, raw2, raw3, raw4, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv492 : search 9 0 v492 = false := by decide +kernel

private def v493 : List Sig := [w178, raw5, raw7, w15, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv493 : search 9 0 v493 = false := by decide +kernel

private def v494 : List Sig := [w96, raw5, raw7, w15, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv494 : search 9 0 v494 = false := by decide +kernel

private def v495 : List Sig := [w134, raw6, raw7, w15, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv495 : search 9 0 v495 = false := by decide +kernel

private def v496 : List Sig := [w110, raw6, raw7, w15, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv496 : search 9 0 v496 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv255 : search 10 0 v255 = false := certifiedStep 9 0 v255
    []
    [⟨v256, rejectv256⟩, ⟨v257, rejectv257⟩, ⟨v314, rejectv314⟩, ⟨v339, rejectv339⟩, ⟨v340, rejectv340⟩, ⟨v341, rejectv341⟩, ⟨v342, rejectv342⟩, ⟨v343, rejectv343⟩, ⟨v344, rejectv344⟩, ⟨v345, rejectv345⟩, ⟨v346, rejectv346⟩, ⟨v347, rejectv347⟩, ⟨v348, rejectv348⟩, ⟨v349, rejectv349⟩, ⟨v350, rejectv350⟩, ⟨v351, rejectv351⟩, ⟨v352, rejectv352⟩, ⟨v353, rejectv353⟩, ⟨v354, rejectv354⟩, ⟨v355, rejectv355⟩, ⟨v356, rejectv356⟩, ⟨v357, rejectv357⟩, ⟨v414, rejectv414⟩, ⟨v439, rejectv439⟩, ⟨v440, rejectv440⟩, ⟨v441, rejectv441⟩, ⟨v442, rejectv442⟩, ⟨v443, rejectv443⟩, ⟨v444, rejectv444⟩, ⟨v445, rejectv445⟩, ⟨v446, rejectv446⟩, ⟨v447, rejectv447⟩, ⟨v448, rejectv448⟩, ⟨v449, rejectv449⟩, ⟨v450, rejectv450⟩, ⟨v451, rejectv451⟩, ⟨v452, rejectv452⟩, ⟨v453, rejectv453⟩, ⟨v454, rejectv454⟩, ⟨v455, rejectv455⟩, ⟨v456, rejectv456⟩, ⟨v457, rejectv457⟩, ⟨v458, rejectv458⟩, ⟨v459, rejectv459⟩, ⟨v460, rejectv460⟩, ⟨v461, rejectv461⟩, ⟨v462, rejectv462⟩, ⟨v463, rejectv463⟩, ⟨v464, rejectv464⟩, ⟨v465, rejectv465⟩, ⟨v466, rejectv466⟩, ⟨v467, rejectv467⟩, ⟨v468, rejectv468⟩, ⟨v469, rejectv469⟩, ⟨v470, rejectv470⟩, ⟨v471, rejectv471⟩, ⟨v472, rejectv472⟩, ⟨v473, rejectv473⟩, ⟨v474, rejectv474⟩, ⟨v475, rejectv475⟩, ⟨v476, rejectv476⟩, ⟨v477, rejectv477⟩, ⟨v478, rejectv478⟩, ⟨v479, rejectv479⟩, ⟨v480, rejectv480⟩, ⟨v481, rejectv481⟩, ⟨v482, rejectv482⟩, ⟨v483, rejectv483⟩, ⟨v484, rejectv484⟩, ⟨v485, rejectv485⟩, ⟨v486, rejectv486⟩, ⟨v487, rejectv487⟩, ⟨v488, rejectv488⟩, ⟨v489, rejectv489⟩, ⟨v490, rejectv490⟩, ⟨v491, rejectv491⟩, ⟨v492, rejectv492⟩, ⟨v493, rejectv493⟩, ⟨v494, rejectv494⟩, ⟨v495, rejectv495⟩, ⟨v496, rejectv496⟩]
    (by decide +kernel)

private def v497 : List Sig := [w15, raw0, raw8, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

private def v498 : List Sig := [w13, raw1, raw0, raw8, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv498 : search 9 0 v498 = false := by decide +kernel

private def v499 : List Sig := [w144, raw0, raw8, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv499 : search 9 0 v499 = false := by decide +kernel

private def v500 : List Sig := [w144, w15, raw0, raw8, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv500 : search 9 0 v500 = false := by decide +kernel

private def v501 : List Sig := [w144, raw1, raw0, raw8, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv501 : search 9 0 v501 = false := by decide +kernel

private def v502 : List Sig := [w179, raw2, raw0, raw8, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv502 : search 9 0 v502 = false := by decide +kernel

private def v503 : List Sig := [w180, raw0, raw8, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv503 : search 9 0 v503 = false := by decide +kernel

private def v504 : List Sig := [w180, w15, raw0, raw8, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv504 : search 9 0 v504 = false := by decide +kernel

private def v505 : List Sig := [w180, raw2, raw0, raw8, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv505 : search 9 0 v505 = false := by decide +kernel

private def v506 : List Sig := [w181, raw3, raw0, raw8, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv506 : search 9 0 v506 = false := by decide +kernel

private def v507 : List Sig := [w182, raw0, raw8, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv507 : search 9 0 v507 = false := by decide +kernel

private def v508 : List Sig := [w182, w15, raw0, raw8, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv508 : search 9 0 v508 = false := by decide +kernel

private def v509 : List Sig := [w182, raw3, raw0, raw8, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv509 : search 9 0 v509 = false := by decide +kernel

private def v510 : List Sig := [w85, raw4, raw0, raw8, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv510 : search 9 0 v510 = false := by decide +kernel

private def v511 : List Sig := [w183, raw0, raw8, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv511 : search 9 0 v511 = false := by decide +kernel

private def v512 : List Sig := [w183, w15, raw0, raw8, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv512 : search 9 0 v512 = false := by decide +kernel

private def v513 : List Sig := [w183, raw4, raw0, raw8, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv513 : search 9 0 v513 = false := by decide +kernel

private def v514 : List Sig := [w184, raw5, raw0, raw8, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv514 : search 9 0 v514 = false := by decide +kernel

private def v515 : List Sig := [w185, raw0, raw8, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv515 : search 9 0 v515 = false := by decide +kernel

private def v516 : List Sig := [w185, w15, raw0, raw8, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv516 : search 9 0 v516 = false := by decide +kernel

private def v517 : List Sig := [w185, raw5, raw0, raw8, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv517 : search 9 0 v517 = false := by decide +kernel

private def v518 : List Sig := [w186, raw6, raw0, raw8, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv518 : search 9 0 v518 = false := by decide +kernel

private def v519 : List Sig := [w187, raw0, raw8, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv519 : search 9 0 v519 = false := by decide +kernel

private def v520 : List Sig := [w187, w15, raw0, raw8, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv520 : search 9 0 v520 = false := by decide +kernel

private def v521 : List Sig := [w187, raw6, raw0, raw8, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv521 : search 9 0 v521 = false := by decide +kernel

private def v522 : List Sig := [w132, raw7, raw0, raw8, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv522 : search 9 0 v522 = false := by decide +kernel

private def v523 : List Sig := [w188, raw0, raw8, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv523 : search 9 0 v523 = false := by decide +kernel

private def v524 : List Sig := [w188, w15, raw0, raw8, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv524 : search 9 0 v524 = false := by decide +kernel

private def v525 : List Sig := [w188, raw7, raw0, raw8, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv525 : search 9 0 v525 = false := by decide +kernel

private def v526 : List Sig := [w207, raw0, w15, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv526 : search 9 0 v526 = false := by decide +kernel

private def v527 : List Sig := [w208, raw1, w15, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv527 : search 9 0 v527 = false := by decide +kernel

private def v528 : List Sig := [w17, raw1, w15, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv528 : search 9 0 v528 = false := by decide +kernel

private def v529 : List Sig := [w209, raw2, w15, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv529 : search 9 0 v529 = false := by decide +kernel

private def v530 : List Sig := [w53, raw2, w15, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv530 : search 9 0 v530 = false := by decide +kernel

private def v531 : List Sig := [w210, raw3, w15, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv531 : search 9 0 v531 = false := by decide +kernel

private def v532 : List Sig := [w68, raw3, w15, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv532 : search 9 0 v532 = false := by decide +kernel

private def v533 : List Sig := [w211, raw4, w15, raw0, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv533 : search 9 0 v533 = false := by decide +kernel

private def v534 : List Sig := [w212, raw4, w15, raw0, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv534 : search 9 0 v534 = false := by decide +kernel

private def v535 : List Sig := [w213, raw5, w15, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv535 : search 9 0 v535 = false := by decide +kernel

private def v536 : List Sig := [w97, raw5, w15, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv536 : search 9 0 v536 = false := by decide +kernel

private def v537 : List Sig := [w214, raw6, w15, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv537 : search 9 0 v537 = false := by decide +kernel

private def v538 : List Sig := [w111, raw6, w15, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv538 : search 9 0 v538 = false := by decide +kernel

private def v539 : List Sig := [w215, raw7, w15, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv539 : search 9 0 v539 = false := by decide +kernel

private def v540 : List Sig := [w19, raw7, w15, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv540 : search 9 0 v540 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv497 : search 10 0 v497 = false := certifiedStep 9 0 v497
    []
    [⟨v498, rejectv498⟩, ⟨v499, rejectv499⟩, ⟨v500, rejectv500⟩, ⟨v501, rejectv501⟩, ⟨v502, rejectv502⟩, ⟨v503, rejectv503⟩, ⟨v504, rejectv504⟩, ⟨v505, rejectv505⟩, ⟨v506, rejectv506⟩, ⟨v507, rejectv507⟩, ⟨v508, rejectv508⟩, ⟨v509, rejectv509⟩, ⟨v510, rejectv510⟩, ⟨v511, rejectv511⟩, ⟨v512, rejectv512⟩, ⟨v513, rejectv513⟩, ⟨v514, rejectv514⟩, ⟨v515, rejectv515⟩, ⟨v516, rejectv516⟩, ⟨v517, rejectv517⟩, ⟨v518, rejectv518⟩, ⟨v519, rejectv519⟩, ⟨v520, rejectv520⟩, ⟨v521, rejectv521⟩, ⟨v522, rejectv522⟩, ⟨v523, rejectv523⟩, ⟨v524, rejectv524⟩, ⟨v525, rejectv525⟩, ⟨v526, rejectv526⟩, ⟨v527, rejectv527⟩, ⟨v528, rejectv528⟩, ⟨v529, rejectv529⟩, ⟨v530, rejectv530⟩, ⟨v531, rejectv531⟩, ⟨v532, rejectv532⟩, ⟨v533, rejectv533⟩, ⟨v534, rejectv534⟩, ⟨v535, rejectv535⟩, ⟨v536, rejectv536⟩, ⟨v537, rejectv537⟩, ⟨v538, rejectv538⟩, ⟨v539, rejectv539⟩, ⟨v540, rejectv540⟩]
    (by decide +kernel)

private def v541 : List Sig := [w207, raw0, raw8, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv541 : search 10 0 v541 = false := by decide +kernel

private def v542 : List Sig := [w191, raw1, raw3, raw0, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv542 : search 10 0 v542 = false := by decide +kernel

private def v543 : List Sig := [w16, raw1, raw3, raw0, raw2, raw4, raw5, raw6, raw7, raw8]

private def v544 : List Sig := [w216, raw5, raw1, raw3, raw0, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv544 : search 9 0 v544 = false := by decide +kernel

private def v545 : List Sig := [w217, raw5, raw1, raw3, raw0, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv545 : search 9 0 v545 = false := by decide +kernel

private def v546 : List Sig := [w218, raw6, raw1, raw3, raw0, raw2, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv546 : search 9 0 v546 = false := by decide +kernel

private def v547 : List Sig := [w219, raw6, raw1, raw3, raw0, raw2, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv547 : search 9 0 v547 = false := by decide +kernel

private def v548 : List Sig := [w220, raw7, raw1, raw3, raw0, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv548 : search 9 0 v548 = false := by decide +kernel

private def v549 : List Sig := [w221, raw7, raw1, raw3, raw0, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv549 : search 9 0 v549 = false := by decide +kernel

private def v550 : List Sig := [w222, raw8, raw1, raw3, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv550 : search 9 0 v550 = false := by decide +kernel

private def v551 : List Sig := [w223, raw8, raw1, raw3, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv551 : search 9 0 v551 = false := by decide +kernel

private def v552 : List Sig := [w32, raw7, w16, raw3, raw0, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv552 : search 9 0 v552 = false := by decide +kernel

private def v553 : List Sig := [w17, w16, raw3, raw0, raw2, raw4, raw5, raw6, raw7]

private def v554 : List Sig := [w224, w17, raw3, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv554 : search 8 0 v554 = false := by decide +kernel

private def v555 : List Sig := [w163, raw5, w17, w16, raw0, raw2, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv555 : search 8 0 v555 = false := by decide +kernel

private def v556 : List Sig := [w153, raw0, w16, raw3, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv556 : search 8 0 v556 = false := by decide +kernel

private def v557 : List Sig := [w22, raw0, w17, raw3, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv557 : search 8 0 v557 = false := by decide +kernel

private def v558 : List Sig := [w49, raw0, w17, w16, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv558 : search 8 0 v558 = false := by decide +kernel

private def v559 : List Sig := [w225, w17, raw3, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv559 : search 8 0 v559 = false := by decide +kernel

private def v560 : List Sig := [w225, raw2, w17, raw3, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv560 : search 8 0 v560 = false := by decide +kernel

private def v561 : List Sig := [w225, w16, w17, raw3, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv561 : search 8 0 v561 = false := by decide +kernel

private def v562 : List Sig := [w156, raw2, w17, w16, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv562 : search 8 0 v562 = false := by decide +kernel

private def v563 : List Sig := [w170, raw4, w17, w16, raw0, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv563 : search 8 0 v563 = false := by decide +kernel

private def v564 : List Sig := [w226, raw7, w16, raw3, raw0, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv564 : search 8 0 v564 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv553 : search 9 0 v553 = false := certifiedStep 8 0 v553
    []
    [⟨v554, rejectv554⟩, ⟨v555, rejectv555⟩, ⟨v556, rejectv556⟩, ⟨v557, rejectv557⟩, ⟨v558, rejectv558⟩, ⟨v559, rejectv559⟩, ⟨v560, rejectv560⟩, ⟨v561, rejectv561⟩, ⟨v562, rejectv562⟩, ⟨v563, rejectv563⟩, ⟨v564, rejectv564⟩]
    (by decide +kernel)

private def v565 : List Sig := [w17, raw1, w16, raw3, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv565 : search 9 0 v565 = false := by decide +kernel

private def v566 : List Sig := [w17, raw8, w16, raw3, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv566 : search 9 0 v566 = false := by decide +kernel

private def v567 : List Sig := [w163, raw5, w16, raw1, raw0, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv567 : search 9 0 v567 = false := by decide +kernel

private def v568 : List Sig := [w227, raw0, raw1, raw3, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv568 : search 9 0 v568 = false := by decide +kernel

private def v569 : List Sig := [w22, raw0, raw1, raw3, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv569 : search 9 0 v569 = false := by decide +kernel

private def v570 : List Sig := [w0, raw0, w16, raw3, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv570 : search 9 0 v570 = false := by decide +kernel

private def v571 : List Sig := [w49, raw0, w16, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv571 : search 9 0 v571 = false := by decide +kernel

private def v572 : List Sig := [w15, raw0, w16, raw1, raw3, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv572 : search 9 0 v572 = false := by decide +kernel

private def v573 : List Sig := [w225, raw1, raw3, raw0, raw4, raw5, raw6, raw7, raw8]

private def v574 : List Sig := [w228, w225, raw3, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv574 : search 8 0 v574 = false := by decide +kernel

private def v575 : List Sig := [w229, w225, raw1, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv575 : search 8 0 v575 = false := by decide +kernel

private def v576 : List Sig := [w230, w225, raw1, raw3, raw0, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv576 : search 8 0 v576 = false := by decide +kernel

private def v577 : List Sig := [w231, w225, raw1, raw3, raw0, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv577 : search 8 0 v577 = false := by decide +kernel

private def v578 : List Sig := [w232, w225, raw1, raw3, raw0, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv578 : search 8 0 v578 = false := by decide +kernel

private def v579 : List Sig := [w233, w225, raw1, raw3, raw0, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv579 : search 8 0 v579 = false := by decide +kernel

private def v580 : List Sig := [w234, w225, raw1, raw3, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv580 : search 8 0 v580 = false := by decide +kernel

private def v581 : List Sig := [w32, raw7, w225, raw3, raw0, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv581 : search 8 0 v581 = false := by decide +kernel

private def v582 : List Sig := [w17, w225, raw3, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv582 : search 8 0 v582 = false := by decide +kernel

private def v583 : List Sig := [w17, raw1, w225, raw3, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv583 : search 8 0 v583 = false := by decide +kernel

private def v584 : List Sig := [w17, raw8, w225, raw3, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv584 : search 8 0 v584 = false := by decide +kernel

private def v585 : List Sig := [w163, raw5, w225, raw1, raw0, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv585 : search 8 0 v585 = false := by decide +kernel

private def v586 : List Sig := [w235, w225, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv586 : search 8 0 v586 = false := by decide +kernel

private def v587 : List Sig := [w0, raw0, w225, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv587 : search 8 0 v587 = false := by decide +kernel

private def v588 : List Sig := [w15, raw0, w225, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv588 : search 8 0 v588 = false := by decide +kernel

private def v589 : List Sig := [w170, raw4, w225, raw1, raw0, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv589 : search 8 0 v589 = false := by decide +kernel

private def v590 : List Sig := [w19, raw7, w225, raw1, raw3, raw0, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv590 : search 8 0 v590 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv573 : search 9 0 v573 = false := certifiedStep 8 0 v573
    []
    [⟨v574, rejectv574⟩, ⟨v575, rejectv575⟩, ⟨v576, rejectv576⟩, ⟨v577, rejectv577⟩, ⟨v578, rejectv578⟩, ⟨v579, rejectv579⟩, ⟨v580, rejectv580⟩, ⟨v581, rejectv581⟩, ⟨v582, rejectv582⟩, ⟨v583, rejectv583⟩, ⟨v584, rejectv584⟩, ⟨v585, rejectv585⟩, ⟨v586, rejectv586⟩, ⟨v587, rejectv587⟩, ⟨v588, rejectv588⟩, ⟨v589, rejectv589⟩, ⟨v590, rejectv590⟩]
    (by decide +kernel)

private def v591 : List Sig := [w225, raw2, raw1, raw3, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv591 : search 9 0 v591 = false := by decide +kernel

private def v592 : List Sig := [w225, w16, raw1, raw3, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv592 : search 9 0 v592 = false := by decide +kernel

private def v593 : List Sig := [w236, raw2, raw1, raw3, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv593 : search 9 0 v593 = false := by decide +kernel

private def v594 : List Sig := [w50, raw2, w16, raw3, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv594 : search 9 0 v594 = false := by decide +kernel

private def v595 : List Sig := [w156, raw2, w16, raw1, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv595 : search 9 0 v595 = false := by decide +kernel

private def v596 : List Sig := [w237, raw4, raw1, raw3, raw0, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv596 : search 9 0 v596 = false := by decide +kernel

private def v597 : List Sig := [w238, raw4, raw1, raw3, raw0, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv597 : search 9 0 v597 = false := by decide +kernel

private def v598 : List Sig := [w201, raw4, w16, raw3, raw0, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv598 : search 9 0 v598 = false := by decide +kernel

private def v599 : List Sig := [w170, raw4, w16, raw1, raw0, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv599 : search 9 0 v599 = false := by decide +kernel

private def v600 : List Sig := [w19, raw7, w16, raw1, raw3, raw0, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv600 : search 9 0 v600 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv543 : search 10 0 v543 = false := certifiedStep 9 0 v543
    []
    [⟨v544, rejectv544⟩, ⟨v545, rejectv545⟩, ⟨v546, rejectv546⟩, ⟨v547, rejectv547⟩, ⟨v548, rejectv548⟩, ⟨v549, rejectv549⟩, ⟨v550, rejectv550⟩, ⟨v551, rejectv551⟩, ⟨v552, rejectv552⟩, ⟨v553, rejectv553⟩, ⟨v565, rejectv565⟩, ⟨v566, rejectv566⟩, ⟨v567, rejectv567⟩, ⟨v568, rejectv568⟩, ⟨v569, rejectv569⟩, ⟨v570, rejectv570⟩, ⟨v571, rejectv571⟩, ⟨v572, rejectv572⟩, ⟨v573, rejectv573⟩, ⟨v591, rejectv591⟩, ⟨v592, rejectv592⟩, ⟨v593, rejectv593⟩, ⟨v594, rejectv594⟩, ⟨v595, rejectv595⟩, ⟨v596, rejectv596⟩, ⟨v597, rejectv597⟩, ⟨v598, rejectv598⟩, ⟨v599, rejectv599⟩, ⟨v600, rejectv600⟩]
    (by decide +kernel)

private def v601 : List Sig := [w192, raw1, raw5, raw0, raw2, raw3, raw4, raw6, raw7, raw8]

private def v602 : List Sig := [w239, raw3, raw1, raw5, raw0, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv602 : search 9 0 v602 = false := by decide +kernel

private def v603 : List Sig := [w240, raw1, raw5, raw0, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv603 : search 9 0 v603 = false := by decide +kernel

private def v604 : List Sig := [w240, w192, raw1, raw5, raw0, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv604 : search 9 0 v604 = false := by decide +kernel

private def v605 : List Sig := [w240, raw3, raw1, raw5, raw0, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv605 : search 9 0 v605 = false := by decide +kernel

private def v606 : List Sig := [w241, raw6, raw1, raw5, raw0, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv606 : search 9 0 v606 = false := by decide +kernel

private def v607 : List Sig := [w242, raw6, raw1, raw5, raw0, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv607 : search 9 0 v607 = false := by decide +kernel

private def v608 : List Sig := [w243, raw7, raw1, raw5, raw0, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv608 : search 9 0 v608 = false := by decide +kernel

private def v609 : List Sig := [w244, raw1, raw5, raw0, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv609 : search 9 0 v609 = false := by decide +kernel

private def v610 : List Sig := [w244, w192, raw1, raw5, raw0, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv610 : search 9 0 v610 = false := by decide +kernel

private def v611 : List Sig := [w244, raw7, raw1, raw5, raw0, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv611 : search 9 0 v611 = false := by decide +kernel

private def v612 : List Sig := [w245, raw8, raw1, raw5, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv612 : search 9 0 v612 = false := by decide +kernel

private def v613 : List Sig := [w246, raw1, raw5, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv613 : search 9 0 v613 = false := by decide +kernel

private def v614 : List Sig := [w246, w192, raw1, raw5, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv614 : search 9 0 v614 = false := by decide +kernel

private def v615 : List Sig := [w246, raw8, raw1, raw5, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv615 : search 9 0 v615 = false := by decide +kernel

private def v616 : List Sig := [w17, raw1, w192, raw5, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv616 : search 9 0 v616 = false := by decide +kernel

private def v617 : List Sig := [w7, raw0, raw1, raw5, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv617 : search 9 0 v617 = false := by decide +kernel

private def v618 : List Sig := [w247, raw0, raw1, raw5, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv618 : search 9 0 v618 = false := by decide +kernel

private def v619 : List Sig := [w15, raw0, w192, raw1, raw5, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv619 : search 9 0 v619 = false := by decide +kernel

private def v620 : List Sig := [w248, raw2, raw1, raw5, raw0, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv620 : search 9 0 v620 = false := by decide +kernel

private def v621 : List Sig := [w249, raw2, raw1, raw5, raw0, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv621 : search 9 0 v621 = false := by decide +kernel

private def v622 : List Sig := [w250, raw4, raw1, raw5, raw0, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv622 : search 9 0 v622 = false := by decide +kernel

private def v623 : List Sig := [w251, raw4, raw1, raw5, raw0, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv623 : search 9 0 v623 = false := by decide +kernel

private def v624 : List Sig := [w19, raw7, w192, raw1, raw5, raw0, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv624 : search 9 0 v624 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv601 : search 10 0 v601 = false := certifiedStep 9 0 v601
    []
    [⟨v602, rejectv602⟩, ⟨v603, rejectv603⟩, ⟨v604, rejectv604⟩, ⟨v605, rejectv605⟩, ⟨v606, rejectv606⟩, ⟨v607, rejectv607⟩, ⟨v608, rejectv608⟩, ⟨v609, rejectv609⟩, ⟨v610, rejectv610⟩, ⟨v611, rejectv611⟩, ⟨v612, rejectv612⟩, ⟨v613, rejectv613⟩, ⟨v614, rejectv614⟩, ⟨v615, rejectv615⟩, ⟨v616, rejectv616⟩, ⟨v617, rejectv617⟩, ⟨v618, rejectv618⟩, ⟨v619, rejectv619⟩, ⟨v620, rejectv620⟩, ⟨v621, rejectv621⟩, ⟨v622, rejectv622⟩, ⟨v623, rejectv623⟩, ⟨v624, rejectv624⟩]
    (by decide +kernel)

private def v625 : List Sig := [w99, raw1, raw5, raw0, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv625 : search 10 0 v625 = false := by decide +kernel

private def v626 : List Sig := [w193, raw1, raw6, raw0, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv626 : search 10 0 v626 = false := by decide +kernel

private def v627 : List Sig := [w113, raw1, raw6, raw0, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv627 : search 10 0 v627 = false := by decide +kernel

private def v628 : List Sig := [w206, raw1, raw7, raw0, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv628 : search 10 0 v628 = false := by decide +kernel

private def v629 : List Sig := [w32, raw1, raw7, raw0, raw2, raw3, raw4, raw5, raw6, raw8]

private def v630 : List Sig := [w252, raw8, raw1, raw7, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv630 : search 9 0 v630 = false := by decide +kernel

private def v631 : List Sig := [w226, raw1, raw7, raw0, raw2, raw3, raw4, raw5, raw6]

private def v632 : List Sig := [w16, raw3, w226, raw7, raw0, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv632 : search 8 0 v632 = false := by decide +kernel

private def v633 : List Sig := [w253, raw1, raw7, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv633 : search 8 0 v633 = false := by decide +kernel

private def v634 : List Sig := [w253, raw0, raw1, raw7, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv634 : search 8 0 v634 = false := by decide +kernel

private def v635 : List Sig := [w253, w226, raw1, raw7, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv635 : search 8 0 v635 = false := by decide +kernel

private def v636 : List Sig := [w20, raw0, w226, raw7, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv636 : search 8 0 v636 = false := by decide +kernel

private def v637 : List Sig := [w109, raw0, w226, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv637 : search 8 0 v637 = false := by decide +kernel

private def v638 : List Sig := [w18, raw2, w226, raw7, raw0, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv638 : search 8 0 v638 = false := by decide +kernel

private def v639 : List Sig := [w96, raw5, w226, raw1, raw0, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv639 : search 8 0 v639 = false := by decide +kernel

private def v640 : List Sig := [w134, raw6, w226, raw1, raw0, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv640 : search 8 0 v640 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv631 : search 9 0 v631 = false := certifiedStep 8 0 v631
    []
    [⟨v632, rejectv632⟩, ⟨v633, rejectv633⟩, ⟨v634, rejectv634⟩, ⟨v635, rejectv635⟩, ⟨v636, rejectv636⟩, ⟨v637, rejectv637⟩, ⟨v638, rejectv638⟩, ⟨v639, rejectv639⟩, ⟨v640, rejectv640⟩]
    (by decide +kernel)

private def v641 : List Sig := [w226, w32, raw1, raw7, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv641 : search 9 0 v641 = false := by decide +kernel

private def v642 : List Sig := [w226, raw8, raw1, raw7, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv642 : search 9 0 v642 = false := by decide +kernel

private def v643 : List Sig := [w16, raw3, w32, raw7, raw0, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv643 : search 9 0 v643 = false := by decide +kernel

private def v644 : List Sig := [w113, raw6, w32, raw7, raw0, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv644 : search 9 0 v644 = false := by decide +kernel

private def v645 : List Sig := [w17, raw1, w32, raw7, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv645 : search 9 0 v645 = false := by decide +kernel

private def v646 : List Sig := [w19, raw7, w32, raw1, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv646 : search 9 0 v646 = false := by decide +kernel

private def v647 : List Sig := [w254, raw0, raw1, raw7, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv647 : search 9 0 v647 = false := by decide +kernel

private def v648 : List Sig := [w28, raw0, raw1, raw7, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv648 : search 9 0 v648 = false := by decide +kernel

private def v649 : List Sig := [w20, raw0, w32, raw7, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv649 : search 9 0 v649 = false := by decide +kernel

private def v650 : List Sig := [w109, raw0, w32, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv650 : search 9 0 v650 = false := by decide +kernel

private def v651 : List Sig := [w15, raw0, w32, raw1, raw7, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv651 : search 9 0 v651 = false := by decide +kernel

private def v652 : List Sig := [w255, raw2, raw1, raw7, raw0, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv652 : search 9 0 v652 = false := by decide +kernel

private def v653 : List Sig := [w256, raw2, raw1, raw7, raw0, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv653 : search 9 0 v653 = false := by decide +kernel

private def v654 : List Sig := [w18, raw2, w32, raw7, raw0, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv654 : search 9 0 v654 = false := by decide +kernel

private def v655 : List Sig := [w52, raw2, w32, raw1, raw0, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv655 : search 9 0 v655 = false := by decide +kernel

private def v656 : List Sig := [w257, raw3, raw1, raw7, raw0, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv656 : search 9 0 v656 = false := by decide +kernel

private def v657 : List Sig := [w221, raw3, raw1, raw7, raw0, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv657 : search 9 0 v657 = false := by decide +kernel

private def v658 : List Sig := [w258, raw4, raw1, raw7, raw0, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv658 : search 9 0 v658 = false := by decide +kernel

private def v659 : List Sig := [w259, raw4, raw1, raw7, raw0, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv659 : search 9 0 v659 = false := by decide +kernel

private def v660 : List Sig := [w260, raw5, raw1, raw7, raw0, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv660 : search 9 0 v660 = false := by decide +kernel

private def v661 : List Sig := [w261, raw5, raw1, raw7, raw0, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv661 : search 9 0 v661 = false := by decide +kernel

private def v662 : List Sig := [w96, raw5, w32, raw1, raw0, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv662 : search 9 0 v662 = false := by decide +kernel

private def v663 : List Sig := [w262, raw6, raw1, raw7, raw0, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv663 : search 9 0 v663 = false := by decide +kernel

private def v664 : List Sig := [w263, raw6, raw1, raw7, raw0, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv664 : search 9 0 v664 = false := by decide +kernel

private def v665 : List Sig := [w134, raw6, w32, raw1, raw0, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv665 : search 9 0 v665 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv629 : search 10 0 v629 = false := certifiedStep 9 0 v629
    []
    [⟨v630, rejectv630⟩, ⟨v631, rejectv631⟩, ⟨v641, rejectv641⟩, ⟨v642, rejectv642⟩, ⟨v643, rejectv643⟩, ⟨v644, rejectv644⟩, ⟨v645, rejectv645⟩, ⟨v646, rejectv646⟩, ⟨v647, rejectv647⟩, ⟨v648, rejectv648⟩, ⟨v649, rejectv649⟩, ⟨v650, rejectv650⟩, ⟨v651, rejectv651⟩, ⟨v652, rejectv652⟩, ⟨v653, rejectv653⟩, ⟨v654, rejectv654⟩, ⟨v655, rejectv655⟩, ⟨v656, rejectv656⟩, ⟨v657, rejectv657⟩, ⟨v658, rejectv658⟩, ⟨v659, rejectv659⟩, ⟨v660, rejectv660⟩, ⟨v661, rejectv661⟩, ⟨v662, rejectv662⟩, ⟨v663, rejectv663⟩, ⟨v664, rejectv664⟩, ⟨v665, rejectv665⟩]
    (by decide +kernel)

private def v666 : List Sig := [w208, raw1, raw8, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv666 : search 10 0 v666 = false := by decide +kernel

private def v667 : List Sig := [w17, raw1, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

private def v668 : List Sig := [w191, raw1, raw3, w17, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv668 : search 9 0 v668 = false := by decide +kernel

private def v669 : List Sig := [w16, raw3, w17, raw0, raw2, raw4, raw5, raw6, raw7]

private def v670 : List Sig := [w163, raw5, w16, w17, raw0, raw2, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv670 : search 8 0 v670 = false := by decide +kernel

private def v671 : List Sig := [w22, raw0, raw3, w17, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv671 : search 8 0 v671 = false := by decide +kernel

private def v672 : List Sig := [w49, raw0, w16, w17, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv672 : search 8 0 v672 = false := by decide +kernel

private def v673 : List Sig := [w225, raw3, w17, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv673 : search 8 0 v673 = false := by decide +kernel

private def v674 : List Sig := [w225, raw2, raw3, w17, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv674 : search 8 0 v674 = false := by decide +kernel

private def v675 : List Sig := [w225, w16, raw3, w17, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv675 : search 8 0 v675 = false := by decide +kernel

private def v676 : List Sig := [w156, raw2, w16, w17, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv676 : search 8 0 v676 = false := by decide +kernel

private def v677 : List Sig := [w170, raw4, w16, w17, raw0, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv677 : search 8 0 v677 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv669 : search 9 0 v669 = false := certifiedStep 8 0 v669
    []
    [⟨v554, rejectv554⟩, ⟨v670, rejectv670⟩, ⟨v671, rejectv671⟩, ⟨v672, rejectv672⟩, ⟨v556, rejectv556⟩, ⟨v673, rejectv673⟩, ⟨v674, rejectv674⟩, ⟨v675, rejectv675⟩, ⟨v676, rejectv676⟩, ⟨v677, rejectv677⟩, ⟨v564, rejectv564⟩]
    (by decide +kernel)

private def v678 : List Sig := [w16, raw1, raw3, w17, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv678 : search 9 0 v678 = false := by decide +kernel

private def v679 : List Sig := [w192, raw1, raw5, w17, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv679 : search 9 0 v679 = false := by decide +kernel

private def v680 : List Sig := [w99, raw1, raw5, w17, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv680 : search 9 0 v680 = false := by decide +kernel

private def v681 : List Sig := [w193, raw1, raw6, w17, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv681 : search 9 0 v681 = false := by decide +kernel

private def v682 : List Sig := [w113, raw1, raw6, w17, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv682 : search 9 0 v682 = false := by decide +kernel

private def v683 : List Sig := [w206, raw1, raw7, w17, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv683 : search 9 0 v683 = false := by decide +kernel

private def v684 : List Sig := [w32, raw1, raw7, w17, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv684 : search 9 0 v684 = false := by decide +kernel

private def v685 : List Sig := [w153, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

private def v686 : List Sig := [w144, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv686 : search 8 0 v686 = false := by decide +kernel

private def v687 : List Sig := [w144, w153, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv687 : search 8 0 v687 = false := by decide +kernel

private def v688 : List Sig := [w144, raw1, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv688 : search 8 0 v688 = false := by decide +kernel

private def v689 : List Sig := [w264, w153, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv689 : search 8 0 v689 = false := by decide +kernel

private def v690 : List Sig := [w265, w153, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv690 : search 8 0 v690 = false := by decide +kernel

private def v691 : List Sig := [w266, w153, raw0, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv691 : search 8 0 v691 = false := by decide +kernel

private def v692 : List Sig := [w267, w153, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv692 : search 8 0 v692 = false := by decide +kernel

private def v693 : List Sig := [w268, w153, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv693 : search 8 0 v693 = false := by decide +kernel

private def v694 : List Sig := [w269, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv694 : search 8 0 v694 = false := by decide +kernel

private def v695 : List Sig := [w269, w153, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv695 : search 8 0 v695 = false := by decide +kernel

private def v696 : List Sig := [w269, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv696 : search 8 0 v696 = false := by decide +kernel

private def v697 : List Sig := [w95, raw6, w153, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv697 : search 8 0 v697 = false := by decide +kernel

private def v698 : List Sig := [w121, raw7, w153, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv698 : search 8 0 v698 = false := by decide +kernel

private def v699 : List Sig := [w16, raw3, w153, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv699 : search 8 0 v699 = false := by decide +kernel

private def v700 : List Sig := [w18, raw2, w153, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv700 : search 8 0 v700 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv685 : search 9 0 v685 = false := certifiedStep 8 0 v685
    []
    [⟨v686, rejectv686⟩, ⟨v687, rejectv687⟩, ⟨v688, rejectv688⟩, ⟨v689, rejectv689⟩, ⟨v690, rejectv690⟩, ⟨v691, rejectv691⟩, ⟨v692, rejectv692⟩, ⟨v693, rejectv693⟩, ⟨v694, rejectv694⟩, ⟨v695, rejectv695⟩, ⟨v696, rejectv696⟩, ⟨v697, rejectv697⟩, ⟨v698, rejectv698⟩, ⟨v699, rejectv699⟩, ⟨v700, rejectv700⟩]
    (by decide +kernel)

private def v701 : List Sig := [w153, raw0, w17, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv701 : search 9 0 v701 = false := by decide +kernel

private def v702 : List Sig := [w30, raw0, w17, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv702 : search 9 0 v702 = false := by decide +kernel

private def v703 : List Sig := [w0, raw0, raw1, w17, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv703 : search 9 0 v703 = false := by decide +kernel

private def v704 : List Sig := [w20, raw0, w17, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv704 : search 9 0 v704 = false := by decide +kernel

private def v705 : List Sig := [w20, raw0, raw1, w17, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv705 : search 9 0 v705 = false := by decide +kernel

private def v706 : List Sig := [w37, raw0, raw2, w17, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv706 : search 9 0 v706 = false := by decide +kernel

private def v707 : List Sig := [w31, raw0, raw2, w17, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv707 : search 9 0 v707 = false := by decide +kernel

private def v708 : List Sig := [w57, raw0, raw3, w17, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv708 : search 9 0 v708 = false := by decide +kernel

private def v709 : List Sig := [w49, raw0, raw3, w17, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv709 : search 9 0 v709 = false := by decide +kernel

private def v710 : List Sig := [w73, raw0, raw4, w17, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv710 : search 9 0 v710 = false := by decide +kernel

private def v711 : List Sig := [w66, raw0, raw4, w17, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv711 : search 9 0 v711 = false := by decide +kernel

private def v712 : List Sig := [w87, raw0, raw5, w17, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv712 : search 9 0 v712 = false := by decide +kernel

private def v713 : List Sig := [w88, raw0, raw5, w17, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv713 : search 9 0 v713 = false := by decide +kernel

private def v714 : List Sig := [w104, raw0, raw6, w17, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv714 : search 9 0 v714 = false := by decide +kernel

private def v715 : List Sig := [w95, raw0, raw6, w17, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv715 : search 9 0 v715 = false := by decide +kernel

private def v716 : List Sig := [w121, raw0, raw7, w17, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv716 : search 9 0 v716 = false := by decide +kernel

private def v717 : List Sig := [w109, raw0, raw7, w17, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv717 : search 9 0 v717 = false := by decide +kernel

private def v718 : List Sig := [w270, raw2, w17, raw1, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv718 : search 9 0 v718 = false := by decide +kernel

private def v719 : List Sig := [w271, raw2, w17, raw1, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv719 : search 9 0 v719 = false := by decide +kernel

private def v720 : List Sig := [w18, raw2, w17, raw0, raw3, raw4, raw5, raw6, raw7]

private def v721 : List Sig := [w229, raw2, w17, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv721 : search 8 0 v721 = false := by decide +kernel

private def v722 : List Sig := [w229, w18, raw2, w17, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv722 : search 8 0 v722 = false := by decide +kernel

private def v723 : List Sig := [w229, raw3, raw2, w17, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv723 : search 8 0 v723 = false := by decide +kernel

private def v724 : List Sig := [w272, w18, raw2, w17, raw0, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv724 : search 8 0 v724 = false := by decide +kernel

private def v725 : List Sig := [w273, w18, raw2, w17, raw0, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv725 : search 8 0 v725 = false := by decide +kernel

private def v726 : List Sig := [w274, w18, raw2, w17, raw0, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv726 : search 8 0 v726 = false := by decide +kernel

private def v727 : List Sig := [w275, w18, raw2, w17, raw0, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv727 : search 8 0 v727 = false := by decide +kernel

private def v728 : List Sig := [w51, raw3, w18, w17, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv728 : search 8 0 v728 = false := by decide +kernel

private def v729 : List Sig := [w276, raw2, w17, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv729 : search 8 0 v729 = false := by decide +kernel

private def v730 : List Sig := [w276, raw0, raw2, w17, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv730 : search 8 0 v730 = false := by decide +kernel

private def v731 : List Sig := [w276, w18, raw2, w17, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv731 : search 8 0 v731 = false := by decide +kernel

private def v732 : List Sig := [w153, raw0, w18, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv732 : search 8 0 v732 = false := by decide +kernel

private def v733 : List Sig := [w56, raw4, w18, w17, raw0, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv733 : search 8 0 v733 = false := by decide +kernel

private def v734 : List Sig := [w226, raw7, w18, raw2, raw0, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv734 : search 8 0 v734 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv720 : search 9 0 v720 = false := certifiedStep 8 0 v720
    []
    [⟨v721, rejectv721⟩, ⟨v722, rejectv722⟩, ⟨v723, rejectv723⟩, ⟨v724, rejectv724⟩, ⟨v725, rejectv725⟩, ⟨v726, rejectv726⟩, ⟨v727, rejectv727⟩, ⟨v728, rejectv728⟩, ⟨v729, rejectv729⟩, ⟨v730, rejectv730⟩, ⟨v731, rejectv731⟩, ⟨v732, rejectv732⟩, ⟨v733, rejectv733⟩, ⟨v734, rejectv734⟩]
    (by decide +kernel)

private def v735 : List Sig := [w18, raw2, raw1, w17, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv735 : search 9 0 v735 = false := by decide +kernel

private def v736 : List Sig := [w50, raw2, raw1, w17, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv736 : search 9 0 v736 = false := by decide +kernel

private def v737 : List Sig := [w51, raw2, raw3, w17, raw1, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv737 : search 9 0 v737 = false := by decide +kernel

private def v738 : List Sig := [w156, raw2, raw3, w17, raw1, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv738 : search 9 0 v738 = false := by decide +kernel

private def v739 : List Sig := [w157, raw2, raw5, w17, raw1, raw0, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv739 : search 9 0 v739 = false := by decide +kernel

private def v740 : List Sig := [w158, raw2, raw5, w17, raw1, raw0, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv740 : search 9 0 v740 = false := by decide +kernel

private def v741 : List Sig := [w159, raw2, raw6, w17, raw1, raw0, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv741 : search 9 0 v741 = false := by decide +kernel

private def v742 : List Sig := [w160, raw2, raw6, w17, raw1, raw0, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv742 : search 9 0 v742 = false := by decide +kernel

private def v743 : List Sig := [w161, raw2, raw7, w17, raw1, raw0, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv743 : search 9 0 v743 = false := by decide +kernel

private def v744 : List Sig := [w52, raw2, raw7, w17, raw1, raw0, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv744 : search 9 0 v744 = false := by decide +kernel

private def v745 : List Sig := [w277, raw3, w17, raw1, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv745 : search 9 0 v745 = false := by decide +kernel

private def v746 : List Sig := [w223, raw3, w17, raw1, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv746 : search 9 0 v746 = false := by decide +kernel

private def v747 : List Sig := [w162, raw3, raw5, w17, raw1, raw0, raw2, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv747 : search 9 0 v747 = false := by decide +kernel

private def v748 : List Sig := [w163, raw3, raw5, w17, raw1, raw0, raw2, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv748 : search 9 0 v748 = false := by decide +kernel

private def v749 : List Sig := [w164, raw3, raw6, w17, raw1, raw0, raw2, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv749 : search 9 0 v749 = false := by decide +kernel

private def v750 : List Sig := [w165, raw3, raw6, w17, raw1, raw0, raw2, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv750 : search 9 0 v750 = false := by decide +kernel

private def v751 : List Sig := [w166, raw3, raw7, w17, raw1, raw0, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv751 : search 9 0 v751 = false := by decide +kernel

private def v752 : List Sig := [w67, raw3, raw7, w17, raw1, raw0, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv752 : search 9 0 v752 = false := by decide +kernel

private def v753 : List Sig := [w278, raw4, w17, raw1, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv753 : search 9 0 v753 = false := by decide +kernel

private def v754 : List Sig := [w279, raw4, w17, raw1, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv754 : search 9 0 v754 = false := by decide +kernel

private def v755 : List Sig := [w200, raw4, raw1, w17, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv755 : search 9 0 v755 = false := by decide +kernel

private def v756 : List Sig := [w201, raw4, raw1, w17, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv756 : search 9 0 v756 = false := by decide +kernel

private def v757 : List Sig := [w169, raw4, raw2, w17, raw1, raw0, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv757 : search 9 0 v757 = false := by decide +kernel

private def v758 : List Sig := [w56, raw4, raw2, w17, raw1, raw0, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv758 : search 9 0 v758 = false := by decide +kernel

private def v759 : List Sig := [w170, raw4, raw3, w17, raw1, raw0, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv759 : search 9 0 v759 = false := by decide +kernel

private def v760 : List Sig := [w171, raw4, raw3, w17, raw1, raw0, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv760 : search 9 0 v760 = false := by decide +kernel

private def v761 : List Sig := [w172, raw4, raw5, w17, raw1, raw0, raw2, raw3, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv761 : search 9 0 v761 = false := by decide +kernel

private def v762 : List Sig := [w173, raw4, raw5, w17, raw1, raw0, raw2, raw3, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv762 : search 9 0 v762 = false := by decide +kernel

private def v763 : List Sig := [w174, raw4, raw6, w17, raw1, raw0, raw2, raw3, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv763 : search 9 0 v763 = false := by decide +kernel

private def v764 : List Sig := [w118, raw4, raw6, w17, raw1, raw0, raw2, raw3, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv764 : search 9 0 v764 = false := by decide +kernel

private def v765 : List Sig := [w175, raw4, raw7, w17, raw1, raw0, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv765 : search 9 0 v765 = false := by decide +kernel

private def v766 : List Sig := [w176, raw4, raw7, w17, raw1, raw0, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv766 : search 9 0 v766 = false := by decide +kernel

private def v767 : List Sig := [w280, raw5, w17, raw1, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv767 : search 9 0 v767 = false := by decide +kernel

private def v768 : List Sig := [w281, raw5, w17, raw1, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv768 : search 9 0 v768 = false := by decide +kernel

private def v769 : List Sig := [w120, raw5, raw6, w17, raw1, raw0, raw2, raw3, raw4, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv769 : search 9 0 v769 = false := by decide +kernel

private def v770 : List Sig := [w177, raw5, raw6, w17, raw1, raw0, raw2, raw3, raw4, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv770 : search 9 0 v770 = false := by decide +kernel

private def v771 : List Sig := [w178, raw5, raw7, w17, raw1, raw0, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv771 : search 9 0 v771 = false := by decide +kernel

private def v772 : List Sig := [w96, raw5, raw7, w17, raw1, raw0, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv772 : search 9 0 v772 = false := by decide +kernel

private def v773 : List Sig := [w282, raw6, w17, raw1, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv773 : search 9 0 v773 = false := by decide +kernel

private def v774 : List Sig := [w283, raw6, w17, raw1, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv774 : search 9 0 v774 = false := by decide +kernel

private def v775 : List Sig := [w134, raw6, raw7, w17, raw1, raw0, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv775 : search 9 0 v775 = false := by decide +kernel

private def v776 : List Sig := [w110, raw6, raw7, w17, raw1, raw0, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv776 : search 9 0 v776 = false := by decide +kernel

private def v777 : List Sig := [w284, raw7, w17, raw1, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv777 : search 9 0 v777 = false := by decide +kernel

private def v778 : List Sig := [w226, raw7, raw1, raw0, raw2, raw3, raw4, raw5, raw6]

private def v779 : List Sig := [w253, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv779 : search 8 0 v779 = false := by decide +kernel

private def v780 : List Sig := [w253, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv780 : search 8 0 v780 = false := by decide +kernel

private def v781 : List Sig := [w253, w226, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv781 : search 8 0 v781 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv778 : search 9 0 v778 = false := certifiedStep 8 0 v778
    []
    [⟨v632, rejectv632⟩, ⟨v779, rejectv779⟩, ⟨v780, rejectv780⟩, ⟨v781, rejectv781⟩, ⟨v637, rejectv637⟩, ⟨v636, rejectv636⟩, ⟨v638, rejectv638⟩, ⟨v639, rejectv639⟩, ⟨v640, rejectv640⟩]
    (by decide +kernel)

private def v782 : List Sig := [w226, raw7, w17, raw1, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv782 : search 9 0 v782 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv667 : search 10 0 v667 = false := certifiedStep 9 0 v667
    []
    [⟨v668, rejectv668⟩, ⟨v669, rejectv669⟩, ⟨v678, rejectv678⟩, ⟨v679, rejectv679⟩, ⟨v680, rejectv680⟩, ⟨v681, rejectv681⟩, ⟨v682, rejectv682⟩, ⟨v683, rejectv683⟩, ⟨v684, rejectv684⟩, ⟨v685, rejectv685⟩, ⟨v701, rejectv701⟩, ⟨v702, rejectv702⟩, ⟨v703, rejectv703⟩, ⟨v704, rejectv704⟩, ⟨v705, rejectv705⟩, ⟨v706, rejectv706⟩, ⟨v707, rejectv707⟩, ⟨v708, rejectv708⟩, ⟨v709, rejectv709⟩, ⟨v710, rejectv710⟩, ⟨v711, rejectv711⟩, ⟨v712, rejectv712⟩, ⟨v713, rejectv713⟩, ⟨v714, rejectv714⟩, ⟨v715, rejectv715⟩, ⟨v716, rejectv716⟩, ⟨v717, rejectv717⟩, ⟨v718, rejectv718⟩, ⟨v719, rejectv719⟩, ⟨v720, rejectv720⟩, ⟨v735, rejectv735⟩, ⟨v736, rejectv736⟩, ⟨v737, rejectv737⟩, ⟨v738, rejectv738⟩, ⟨v739, rejectv739⟩, ⟨v740, rejectv740⟩, ⟨v741, rejectv741⟩, ⟨v742, rejectv742⟩, ⟨v743, rejectv743⟩, ⟨v744, rejectv744⟩, ⟨v745, rejectv745⟩, ⟨v746, rejectv746⟩, ⟨v747, rejectv747⟩, ⟨v748, rejectv748⟩, ⟨v749, rejectv749⟩, ⟨v750, rejectv750⟩, ⟨v751, rejectv751⟩, ⟨v752, rejectv752⟩, ⟨v753, rejectv753⟩, ⟨v754, rejectv754⟩, ⟨v755, rejectv755⟩, ⟨v756, rejectv756⟩, ⟨v757, rejectv757⟩, ⟨v758, rejectv758⟩, ⟨v759, rejectv759⟩, ⟨v760, rejectv760⟩, ⟨v761, rejectv761⟩, ⟨v762, rejectv762⟩, ⟨v763, rejectv763⟩, ⟨v764, rejectv764⟩, ⟨v765, rejectv765⟩, ⟨v766, rejectv766⟩, ⟨v767, rejectv767⟩, ⟨v768, rejectv768⟩, ⟨v769, rejectv769⟩, ⟨v770, rejectv770⟩, ⟨v771, rejectv771⟩, ⟨v772, rejectv772⟩, ⟨v773, rejectv773⟩, ⟨v774, rejectv774⟩, ⟨v775, rejectv775⟩, ⟨v776, rejectv776⟩, ⟨v777, rejectv777⟩, ⟨v778, rejectv778⟩, ⟨v782, rejectv782⟩]
    (by decide +kernel)

private def v783 : List Sig := [w17, raw1, raw8, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

private def v784 : List Sig := [w208, raw1, w17, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv784 : search 9 0 v784 = false := by decide +kernel

private def v785 : List Sig := [w16, raw3, w17, raw8, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv785 : search 9 0 v785 = false := by decide +kernel

private def v786 : List Sig := [w153, raw0, raw1, raw8, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv786 : search 9 0 v786 = false := by decide +kernel

private def v787 : List Sig := [w30, raw0, raw1, raw8, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv787 : search 9 0 v787 = false := by decide +kernel

private def v788 : List Sig := [w20, raw0, w17, raw8, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv788 : search 9 0 v788 = false := by decide +kernel

private def v789 : List Sig := [w15, raw0, w17, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv789 : search 9 0 v789 = false := by decide +kernel

private def v790 : List Sig := [w207, raw0, w17, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv790 : search 9 0 v790 = false := by decide +kernel

private def v791 : List Sig := [w270, raw2, raw1, raw8, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv791 : search 9 0 v791 = false := by decide +kernel

private def v792 : List Sig := [w271, raw2, raw1, raw8, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv792 : search 9 0 v792 = false := by decide +kernel

private def v793 : List Sig := [w18, raw2, w17, raw8, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv793 : search 9 0 v793 = false := by decide +kernel

private def v794 : List Sig := [w209, raw2, w17, raw1, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv794 : search 9 0 v794 = false := by decide +kernel

private def v795 : List Sig := [w53, raw2, w17, raw1, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv795 : search 9 0 v795 = false := by decide +kernel

private def v796 : List Sig := [w277, raw3, raw1, raw8, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv796 : search 9 0 v796 = false := by decide +kernel

private def v797 : List Sig := [w223, raw3, raw1, raw8, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv797 : search 9 0 v797 = false := by decide +kernel

private def v798 : List Sig := [w210, raw3, w17, raw1, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv798 : search 9 0 v798 = false := by decide +kernel

private def v799 : List Sig := [w68, raw3, w17, raw1, raw0, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv799 : search 9 0 v799 = false := by decide +kernel

private def v800 : List Sig := [w278, raw4, raw1, raw8, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv800 : search 9 0 v800 = false := by decide +kernel

private def v801 : List Sig := [w279, raw4, raw1, raw8, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv801 : search 9 0 v801 = false := by decide +kernel

private def v802 : List Sig := [w211, raw4, w17, raw1, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv802 : search 9 0 v802 = false := by decide +kernel

private def v803 : List Sig := [w212, raw4, w17, raw1, raw0, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv803 : search 9 0 v803 = false := by decide +kernel

private def v804 : List Sig := [w280, raw5, raw1, raw8, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv804 : search 9 0 v804 = false := by decide +kernel

private def v805 : List Sig := [w281, raw5, raw1, raw8, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv805 : search 9 0 v805 = false := by decide +kernel

private def v806 : List Sig := [w213, raw5, w17, raw1, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv806 : search 9 0 v806 = false := by decide +kernel

private def v807 : List Sig := [w97, raw5, w17, raw1, raw0, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv807 : search 9 0 v807 = false := by decide +kernel

private def v808 : List Sig := [w282, raw6, raw1, raw8, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv808 : search 9 0 v808 = false := by decide +kernel

private def v809 : List Sig := [w283, raw6, raw1, raw8, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv809 : search 9 0 v809 = false := by decide +kernel

private def v810 : List Sig := [w214, raw6, w17, raw1, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv810 : search 9 0 v810 = false := by decide +kernel

private def v811 : List Sig := [w111, raw6, w17, raw1, raw0, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv811 : search 9 0 v811 = false := by decide +kernel

private def v812 : List Sig := [w284, raw7, raw1, raw8, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv812 : search 9 0 v812 = false := by decide +kernel

private def v813 : List Sig := [w226, raw7, raw1, raw8, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv813 : search 9 0 v813 = false := by decide +kernel

private def v814 : List Sig := [w215, raw7, w17, raw1, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv814 : search 9 0 v814 = false := by decide +kernel

private def v815 : List Sig := [w19, raw7, w17, raw1, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv815 : search 9 0 v815 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv783 : search 10 0 v783 = false := certifiedStep 9 0 v783
    []
    [⟨v784, rejectv784⟩, ⟨v785, rejectv785⟩, ⟨v786, rejectv786⟩, ⟨v787, rejectv787⟩, ⟨v788, rejectv788⟩, ⟨v789, rejectv789⟩, ⟨v790, rejectv790⟩, ⟨v791, rejectv791⟩, ⟨v792, rejectv792⟩, ⟨v793, rejectv793⟩, ⟨v794, rejectv794⟩, ⟨v795, rejectv795⟩, ⟨v796, rejectv796⟩, ⟨v797, rejectv797⟩, ⟨v798, rejectv798⟩, ⟨v799, rejectv799⟩, ⟨v800, rejectv800⟩, ⟨v801, rejectv801⟩, ⟨v802, rejectv802⟩, ⟨v803, rejectv803⟩, ⟨v804, rejectv804⟩, ⟨v805, rejectv805⟩, ⟨v806, rejectv806⟩, ⟨v807, rejectv807⟩, ⟨v808, rejectv808⟩, ⟨v809, rejectv809⟩, ⟨v810, rejectv810⟩, ⟨v811, rejectv811⟩, ⟨v812, rejectv812⟩, ⟨v813, rejectv813⟩, ⟨v814, rejectv814⟩, ⟨v815, rejectv815⟩]
    (by decide +kernel)

private def v816 : List Sig := [w18, raw2, raw1, raw0, raw3, raw4, raw5, raw6, raw7, raw8]

private def v817 : List Sig := [w285, raw3, raw2, raw1, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv817 : search 9 0 v817 = false := by decide +kernel

private def v818 : List Sig := [w229, raw2, raw1, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv818 : search 9 0 v818 = false := by decide +kernel

private def v819 : List Sig := [w229, w18, raw2, raw1, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv819 : search 9 0 v819 = false := by decide +kernel

private def v820 : List Sig := [w229, raw3, raw2, raw1, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv820 : search 9 0 v820 = false := by decide +kernel

private def v821 : List Sig := [w286, raw4, raw2, raw1, raw0, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv821 : search 9 0 v821 = false := by decide +kernel

private def v822 : List Sig := [w272, raw2, raw1, raw0, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv822 : search 9 0 v822 = false := by decide +kernel

private def v823 : List Sig := [w272, w18, raw2, raw1, raw0, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv823 : search 9 0 v823 = false := by decide +kernel

private def v824 : List Sig := [w272, raw4, raw2, raw1, raw0, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv824 : search 9 0 v824 = false := by decide +kernel

private def v825 : List Sig := [w248, raw5, raw2, raw1, raw0, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv825 : search 9 0 v825 = false := by decide +kernel

private def v826 : List Sig := [w273, raw2, raw1, raw0, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv826 : search 9 0 v826 = false := by decide +kernel

private def v827 : List Sig := [w273, w18, raw2, raw1, raw0, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv827 : search 9 0 v827 = false := by decide +kernel

private def v828 : List Sig := [w273, raw5, raw2, raw1, raw0, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv828 : search 9 0 v828 = false := by decide +kernel

private def v829 : List Sig := [w287, raw6, raw2, raw1, raw0, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv829 : search 9 0 v829 = false := by decide +kernel

private def v830 : List Sig := [w274, raw2, raw1, raw0, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv830 : search 9 0 v830 = false := by decide +kernel

private def v831 : List Sig := [w274, w18, raw2, raw1, raw0, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv831 : search 9 0 v831 = false := by decide +kernel

private def v832 : List Sig := [w274, raw6, raw2, raw1, raw0, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv832 : search 9 0 v832 = false := by decide +kernel

private def v833 : List Sig := [w288, raw7, raw2, raw1, raw0, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv833 : search 9 0 v833 = false := by decide +kernel

private def v834 : List Sig := [w275, raw2, raw1, raw0, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv834 : search 9 0 v834 = false := by decide +kernel

private def v835 : List Sig := [w275, w18, raw2, raw1, raw0, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv835 : search 9 0 v835 = false := by decide +kernel

private def v836 : List Sig := [w275, raw7, raw2, raw1, raw0, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv836 : search 9 0 v836 = false := by decide +kernel

private def v837 : List Sig := [w289, raw8, raw2, raw1, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv837 : search 9 0 v837 = false := by decide +kernel

private def v838 : List Sig := [w290, raw2, raw1, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv838 : search 9 0 v838 = false := by decide +kernel

private def v839 : List Sig := [w290, w18, raw2, raw1, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv839 : search 9 0 v839 = false := by decide +kernel

private def v840 : List Sig := [w290, raw8, raw2, raw1, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv840 : search 9 0 v840 = false := by decide +kernel

private def v841 : List Sig := [w51, raw3, w18, raw1, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv841 : search 9 0 v841 = false := by decide +kernel

private def v842 : List Sig := [w32, raw7, w18, raw2, raw0, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv842 : search 9 0 v842 = false := by decide +kernel

private def v843 : List Sig := [w17, w18, raw2, raw0, raw3, raw4, raw5, raw6, raw7]

private def v844 : List Sig := [w229, w17, raw2, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv844 : search 8 0 v844 = false := by decide +kernel

private def v845 : List Sig := [w229, w18, w17, raw2, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv845 : search 8 0 v845 = false := by decide +kernel

private def v846 : List Sig := [w229, raw3, w17, raw2, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv846 : search 8 0 v846 = false := by decide +kernel

private def v847 : List Sig := [w272, w18, w17, raw2, raw0, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv847 : search 8 0 v847 = false := by decide +kernel

private def v848 : List Sig := [w273, w18, w17, raw2, raw0, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv848 : search 8 0 v848 = false := by decide +kernel

private def v849 : List Sig := [w274, w18, w17, raw2, raw0, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv849 : search 8 0 v849 = false := by decide +kernel

private def v850 : List Sig := [w275, w18, w17, raw2, raw0, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv850 : search 8 0 v850 = false := by decide +kernel

private def v851 : List Sig := [w51, raw3, w17, w18, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv851 : search 8 0 v851 = false := by decide +kernel

private def v852 : List Sig := [w276, w17, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv852 : search 8 0 v852 = false := by decide +kernel

private def v853 : List Sig := [w276, raw0, w17, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv853 : search 8 0 v853 = false := by decide +kernel

private def v854 : List Sig := [w276, w18, w17, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv854 : search 8 0 v854 = false := by decide +kernel

private def v855 : List Sig := [w56, raw4, w17, w18, raw0, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv855 : search 8 0 v855 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv843 : search 9 0 v843 = false := certifiedStep 8 0 v843
    []
    [⟨v844, rejectv844⟩, ⟨v845, rejectv845⟩, ⟨v846, rejectv846⟩, ⟨v847, rejectv847⟩, ⟨v848, rejectv848⟩, ⟨v849, rejectv849⟩, ⟨v850, rejectv850⟩, ⟨v851, rejectv851⟩, ⟨v732, rejectv732⟩, ⟨v852, rejectv852⟩, ⟨v853, rejectv853⟩, ⟨v854, rejectv854⟩, ⟨v855, rejectv855⟩, ⟨v734, rejectv734⟩]
    (by decide +kernel)

private def v856 : List Sig := [w17, raw1, w18, raw2, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv856 : search 9 0 v856 = false := by decide +kernel

private def v857 : List Sig := [w17, raw8, w18, raw2, raw0, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv857 : search 9 0 v857 = false := by decide +kernel

private def v858 : List Sig := [w1, raw0, raw2, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv858 : search 9 0 v858 = false := by decide +kernel

private def v859 : List Sig := [w276, raw2, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv859 : search 9 0 v859 = false := by decide +kernel

private def v860 : List Sig := [w276, raw0, raw2, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv860 : search 9 0 v860 = false := by decide +kernel

private def v861 : List Sig := [w276, w18, raw2, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv861 : search 9 0 v861 = false := by decide +kernel

private def v862 : List Sig := [w0, raw0, w18, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv862 : search 9 0 v862 = false := by decide +kernel

private def v863 : List Sig := [w15, raw0, w18, raw2, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv863 : search 9 0 v863 = false := by decide +kernel

private def v864 : List Sig := [w56, raw4, w18, raw1, raw0, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv864 : search 9 0 v864 = false := by decide +kernel

private def v865 : List Sig := [w19, raw7, w18, raw2, raw1, raw0, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv865 : search 9 0 v865 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv816 : search 10 0 v816 = false := certifiedStep 9 0 v816
    []
    [⟨v817, rejectv817⟩, ⟨v818, rejectv818⟩, ⟨v819, rejectv819⟩, ⟨v820, rejectv820⟩, ⟨v821, rejectv821⟩, ⟨v822, rejectv822⟩, ⟨v823, rejectv823⟩, ⟨v824, rejectv824⟩, ⟨v825, rejectv825⟩, ⟨v826, rejectv826⟩, ⟨v827, rejectv827⟩, ⟨v828, rejectv828⟩, ⟨v829, rejectv829⟩, ⟨v830, rejectv830⟩, ⟨v831, rejectv831⟩, ⟨v832, rejectv832⟩, ⟨v833, rejectv833⟩, ⟨v834, rejectv834⟩, ⟨v835, rejectv835⟩, ⟨v836, rejectv836⟩, ⟨v837, rejectv837⟩, ⟨v838, rejectv838⟩, ⟨v839, rejectv839⟩, ⟨v840, rejectv840⟩, ⟨v841, rejectv841⟩, ⟨v842, rejectv842⟩, ⟨v843, rejectv843⟩, ⟨v856, rejectv856⟩, ⟨v857, rejectv857⟩, ⟨v858, rejectv858⟩, ⟨v859, rejectv859⟩, ⟨v860, rejectv860⟩, ⟨v861, rejectv861⟩, ⟨v862, rejectv862⟩, ⟨v863, rejectv863⟩, ⟨v864, rejectv864⟩, ⟨v865, rejectv865⟩]
    (by decide +kernel)

private def v866 : List Sig := [w50, raw2, raw1, raw0, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv866 : search 10 0 v866 = false := by decide +kernel

private def v867 : List Sig := [w51, raw2, raw3, raw0, raw1, raw4, raw5, raw6, raw7, raw8]

private def v868 : List Sig := [w285, raw1, raw2, raw3, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv868 : search 9 0 v868 = false := by decide +kernel

private def v869 : List Sig := [w228, raw2, raw3, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv869 : search 9 0 v869 = false := by decide +kernel

private def v870 : List Sig := [w228, w51, raw2, raw3, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv870 : search 9 0 v870 = false := by decide +kernel

private def v871 : List Sig := [w228, raw1, raw2, raw3, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv871 : search 9 0 v871 = false := by decide +kernel

private def v872 : List Sig := [w291, raw4, raw2, raw3, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv872 : search 9 0 v872 = false := by decide +kernel

private def v873 : List Sig := [w292, raw2, raw3, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv873 : search 9 0 v873 = false := by decide +kernel

private def v874 : List Sig := [w292, w51, raw2, raw3, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv874 : search 9 0 v874 = false := by decide +kernel

private def v875 : List Sig := [w292, raw4, raw2, raw3, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv875 : search 9 0 v875 = false := by decide +kernel

private def v876 : List Sig := [w293, raw5, raw2, raw3, raw0, raw1, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv876 : search 9 0 v876 = false := by decide +kernel

private def v877 : List Sig := [w294, raw2, raw3, raw0, raw1, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv877 : search 9 0 v877 = false := by decide +kernel

private def v878 : List Sig := [w294, w51, raw2, raw3, raw0, raw1, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv878 : search 9 0 v878 = false := by decide +kernel

private def v879 : List Sig := [w294, raw5, raw2, raw3, raw0, raw1, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv879 : search 9 0 v879 = false := by decide +kernel

private def v880 : List Sig := [w295, raw6, raw2, raw3, raw0, raw1, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv880 : search 9 0 v880 = false := by decide +kernel

private def v881 : List Sig := [w296, raw2, raw3, raw0, raw1, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv881 : search 9 0 v881 = false := by decide +kernel

private def v882 : List Sig := [w296, w51, raw2, raw3, raw0, raw1, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv882 : search 9 0 v882 = false := by decide +kernel

private def v883 : List Sig := [w296, raw6, raw2, raw3, raw0, raw1, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv883 : search 9 0 v883 = false := by decide +kernel

private def v884 : List Sig := [w297, raw7, raw2, raw3, raw0, raw1, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv884 : search 9 0 v884 = false := by decide +kernel

private def v885 : List Sig := [w298, raw2, raw3, raw0, raw1, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv885 : search 9 0 v885 = false := by decide +kernel

private def v886 : List Sig := [w298, w51, raw2, raw3, raw0, raw1, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv886 : search 9 0 v886 = false := by decide +kernel

private def v887 : List Sig := [w298, raw7, raw2, raw3, raw0, raw1, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv887 : search 9 0 v887 = false := by decide +kernel

private def v888 : List Sig := [w299, raw8, raw2, raw3, raw0, raw1, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv888 : search 9 0 v888 = false := by decide +kernel

private def v889 : List Sig := [w300, raw2, raw3, raw0, raw1, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv889 : search 9 0 v889 = false := by decide +kernel

private def v890 : List Sig := [w300, w51, raw2, raw3, raw0, raw1, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv890 : search 9 0 v890 = false := by decide +kernel

private def v891 : List Sig := [w300, raw8, raw2, raw3, raw0, raw1, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv891 : search 9 0 v891 = false := by decide +kernel

private def v892 : List Sig := [w18, raw1, w51, raw3, raw0, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv892 : search 9 0 v892 = false := by decide +kernel

private def v893 : List Sig := [w163, raw5, w51, raw2, raw0, raw1, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv893 : search 9 0 v893 = false := by decide +kernel

private def v894 : List Sig := [w301, raw0, raw2, raw3, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv894 : search 9 0 v894 = false := by decide +kernel

private def v895 : List Sig := [w302, raw2, raw3, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv895 : search 9 0 v895 = false := by decide +kernel

private def v896 : List Sig := [w302, raw0, raw2, raw3, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv896 : search 9 0 v896 = false := by decide +kernel

private def v897 : List Sig := [w302, w51, raw2, raw3, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv897 : search 9 0 v897 = false := by decide +kernel

private def v898 : List Sig := [w31, raw0, w51, raw3, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv898 : search 9 0 v898 = false := by decide +kernel

private def v899 : List Sig := [w15, raw0, w51, raw2, raw3, raw1, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv899 : search 9 0 v899 = false := by decide +kernel

private def v900 : List Sig := [w17, raw1, w51, raw2, raw3, raw0, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv900 : search 9 0 v900 = false := by decide +kernel

private def v901 : List Sig := [w170, raw4, w51, raw2, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv901 : search 9 0 v901 = false := by decide +kernel

private def v902 : List Sig := [w19, raw7, w51, raw2, raw3, raw0, raw1, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv902 : search 9 0 v902 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv867 : search 10 0 v867 = false := certifiedStep 9 0 v867
    []
    [⟨v868, rejectv868⟩, ⟨v869, rejectv869⟩, ⟨v870, rejectv870⟩, ⟨v871, rejectv871⟩, ⟨v872, rejectv872⟩, ⟨v873, rejectv873⟩, ⟨v874, rejectv874⟩, ⟨v875, rejectv875⟩, ⟨v876, rejectv876⟩, ⟨v877, rejectv877⟩, ⟨v878, rejectv878⟩, ⟨v879, rejectv879⟩, ⟨v880, rejectv880⟩, ⟨v881, rejectv881⟩, ⟨v882, rejectv882⟩, ⟨v883, rejectv883⟩, ⟨v884, rejectv884⟩, ⟨v885, rejectv885⟩, ⟨v886, rejectv886⟩, ⟨v887, rejectv887⟩, ⟨v888, rejectv888⟩, ⟨v889, rejectv889⟩, ⟨v890, rejectv890⟩, ⟨v891, rejectv891⟩, ⟨v892, rejectv892⟩, ⟨v893, rejectv893⟩, ⟨v894, rejectv894⟩, ⟨v895, rejectv895⟩, ⟨v896, rejectv896⟩, ⟨v897, rejectv897⟩, ⟨v898, rejectv898⟩, ⟨v899, rejectv899⟩, ⟨v900, rejectv900⟩, ⟨v901, rejectv901⟩, ⟨v902, rejectv902⟩]
    (by decide +kernel)

private def v903 : List Sig := [w156, raw2, raw3, raw0, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv903 : search 10 0 v903 = false := by decide +kernel

private def v904 : List Sig := [w157, raw2, raw5, raw0, raw1, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv904 : search 10 0 v904 = false := by decide +kernel

private def v905 : List Sig := [w158, raw2, raw5, raw0, raw1, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv905 : search 10 0 v905 = false := by decide +kernel

private def v906 : List Sig := [w159, raw2, raw6, raw0, raw1, raw3, raw4, raw5, raw7, raw8]

private def v907 : List Sig := [w287, raw1, raw2, raw6, raw0, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv907 : search 9 0 v907 = false := by decide +kernel

private def v908 : List Sig := [w303, raw1, raw2, raw6, raw0, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv908 : search 9 0 v908 = false := by decide +kernel

private def v909 : List Sig := [w295, raw3, raw2, raw6, raw0, raw1, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv909 : search 9 0 v909 = false := by decide +kernel

private def v910 : List Sig := [w304, raw3, raw2, raw6, raw0, raw1, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv910 : search 9 0 v910 = false := by decide +kernel

private def v911 : List Sig := [w305, raw5, raw2, raw6, raw0, raw1, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv911 : search 9 0 v911 = false := by decide +kernel

private def v912 : List Sig := [w306, raw5, raw2, raw6, raw0, raw1, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv912 : search 9 0 v912 = false := by decide +kernel

private def v913 : List Sig := [w307, raw7, raw2, raw6, raw0, raw1, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv913 : search 9 0 v913 = false := by decide +kernel

private def v914 : List Sig := [w308, raw7, raw2, raw6, raw0, raw1, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv914 : search 9 0 v914 = false := by decide +kernel

private def v915 : List Sig := [w309, raw8, raw2, raw6, raw0, raw1, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv915 : search 9 0 v915 = false := by decide +kernel

private def v916 : List Sig := [w310, raw8, raw2, raw6, raw0, raw1, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv916 : search 9 0 v916 = false := by decide +kernel

private def v917 : List Sig := [w311, raw0, raw2, raw6, raw1, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv917 : search 9 0 v917 = false := by decide +kernel

private def v918 : List Sig := [w312, raw0, raw2, raw6, raw1, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv918 : search 9 0 v918 = false := by decide +kernel

private def v919 : List Sig := [w15, raw0, w159, raw2, raw6, raw1, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv919 : search 9 0 v919 = false := by decide +kernel

private def v920 : List Sig := [w17, raw1, w159, raw2, raw6, raw0, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv920 : search 9 0 v920 = false := by decide +kernel

private def v921 : List Sig := [w313, raw4, raw2, raw6, raw0, raw1, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv921 : search 9 0 v921 = false := by decide +kernel

private def v922 : List Sig := [w314, raw2, raw6, raw0, raw1, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv922 : search 9 0 v922 = false := by decide +kernel

private def v923 : List Sig := [w314, raw4, raw2, raw6, raw0, raw1, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv923 : search 9 0 v923 = false := by decide +kernel

private def v924 : List Sig := [w314, w159, raw2, raw6, raw0, raw1, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv924 : search 9 0 v924 = false := by decide +kernel

private def v925 : List Sig := [w19, raw7, w159, raw2, raw6, raw0, raw1, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv925 : search 9 0 v925 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv906 : search 10 0 v906 = false := certifiedStep 9 0 v906
    []
    [⟨v907, rejectv907⟩, ⟨v908, rejectv908⟩, ⟨v909, rejectv909⟩, ⟨v910, rejectv910⟩, ⟨v911, rejectv911⟩, ⟨v912, rejectv912⟩, ⟨v913, rejectv913⟩, ⟨v914, rejectv914⟩, ⟨v915, rejectv915⟩, ⟨v916, rejectv916⟩, ⟨v917, rejectv917⟩, ⟨v918, rejectv918⟩, ⟨v919, rejectv919⟩, ⟨v920, rejectv920⟩, ⟨v921, rejectv921⟩, ⟨v922, rejectv922⟩, ⟨v923, rejectv923⟩, ⟨v924, rejectv924⟩, ⟨v925, rejectv925⟩]
    (by decide +kernel)

private def v926 : List Sig := [w160, raw2, raw6, raw0, raw1, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv926 : search 10 0 v926 = false := by decide +kernel

private def v927 : List Sig := [w161, raw2, raw7, raw0, raw1, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv927 : search 10 0 v927 = false := by decide +kernel

private def v928 : List Sig := [w52, raw2, raw7, raw0, raw1, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv928 : search 10 0 v928 = false := by decide +kernel

private def v929 : List Sig := [w209, raw2, raw8, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv929 : search 10 0 v929 = false := by decide +kernel

private def v930 : List Sig := [w53, raw2, raw8, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv930 : search 10 0 v930 = false := by decide +kernel

private def v931 : List Sig := [w162, raw3, raw5, raw0, raw1, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv931 : search 10 0 v931 = false := by decide +kernel

private def v932 : List Sig := [w163, raw3, raw5, raw0, raw1, raw2, raw4, raw6, raw7, raw8]

private def v933 : List Sig := [w315, raw6, raw3, raw5, raw0, raw1, raw2, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv933 : search 9 0 v933 = false := by decide +kernel

private def v934 : List Sig := [w316, raw6, raw3, raw5, raw0, raw1, raw2, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv934 : search 9 0 v934 = false := by decide +kernel

private def v935 : List Sig := [w317, raw7, raw3, raw5, raw0, raw1, raw2, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv935 : search 9 0 v935 = false := by decide +kernel

private def v936 : List Sig := [w318, raw7, raw3, raw5, raw0, raw1, raw2, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv936 : search 9 0 v936 = false := by decide +kernel

private def v937 : List Sig := [w319, raw8, raw3, raw5, raw0, raw1, raw2, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv937 : search 9 0 v937 = false := by decide +kernel

private def v938 : List Sig := [w320, raw8, raw3, raw5, raw0, raw1, raw2, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv938 : search 9 0 v938 = false := by decide +kernel

private def v939 : List Sig := [w165, raw6, w163, raw5, raw0, raw1, raw2, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv939 : search 9 0 v939 = false := by decide +kernel

private def v940 : List Sig := [w120, raw6, w163, raw3, raw0, raw1, raw2, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv940 : search 9 0 v940 = false := by decide +kernel

private def v941 : List Sig := [w96, raw7, w163, raw3, raw0, raw1, raw2, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv941 : search 9 0 v941 = false := by decide +kernel

private def v942 : List Sig := [w321, raw0, raw3, raw5, raw1, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv942 : search 9 0 v942 = false := by decide +kernel

private def v943 : List Sig := [w59, raw0, raw3, raw5, raw1, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv943 : search 9 0 v943 = false := by decide +kernel

private def v944 : List Sig := [w15, raw0, w163, raw3, raw5, raw1, raw2, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv944 : search 9 0 v944 = false := by decide +kernel

private def v945 : List Sig := [w322, raw1, raw3, raw5, raw0, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv945 : search 9 0 v945 = false := by decide +kernel

private def v946 : List Sig := [w217, raw1, raw3, raw5, raw0, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv946 : search 9 0 v946 = false := by decide +kernel

private def v947 : List Sig := [w16, raw1, w163, raw5, raw0, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv947 : search 9 0 v947 = false := by decide +kernel

private def v948 : List Sig := [w17, raw1, w163, raw3, raw5, raw0, raw2, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv948 : search 9 0 v948 = false := by decide +kernel

private def v949 : List Sig := [w323, raw2, raw3, raw5, raw0, raw1, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv949 : search 9 0 v949 = false := by decide +kernel

private def v950 : List Sig := [w324, raw2, raw3, raw5, raw0, raw1, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv950 : search 9 0 v950 = false := by decide +kernel

private def v951 : List Sig := [w51, raw2, w163, raw5, raw0, raw1, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv951 : search 9 0 v951 = false := by decide +kernel

private def v952 : List Sig := [w158, raw2, w163, raw3, raw0, raw1, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv952 : search 9 0 v952 = false := by decide +kernel

private def v953 : List Sig := [w325, raw3, raw5, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv953 : search 9 0 v953 = false := by decide +kernel

private def v954 : List Sig := [w325, raw4, raw3, raw5, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv954 : search 9 0 v954 = false := by decide +kernel

private def v955 : List Sig := [w325, w163, raw3, raw5, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv955 : search 9 0 v955 = false := by decide +kernel

private def v956 : List Sig := [w326, raw4, raw3, raw5, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv956 : search 9 0 v956 = false := by decide +kernel

private def v957 : List Sig := [w171, raw4, w163, raw5, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv957 : search 9 0 v957 = false := by decide +kernel

private def v958 : List Sig := [w173, raw4, w163, raw3, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv958 : search 9 0 v958 = false := by decide +kernel

private def v959 : List Sig := [w19, raw7, w163, raw3, raw5, raw0, raw1, raw2, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv959 : search 9 0 v959 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv932 : search 10 0 v932 = false := certifiedStep 9 0 v932
    []
    [⟨v933, rejectv933⟩, ⟨v934, rejectv934⟩, ⟨v935, rejectv935⟩, ⟨v936, rejectv936⟩, ⟨v937, rejectv937⟩, ⟨v938, rejectv938⟩, ⟨v939, rejectv939⟩, ⟨v940, rejectv940⟩, ⟨v941, rejectv941⟩, ⟨v942, rejectv942⟩, ⟨v943, rejectv943⟩, ⟨v944, rejectv944⟩, ⟨v945, rejectv945⟩, ⟨v946, rejectv946⟩, ⟨v947, rejectv947⟩, ⟨v948, rejectv948⟩, ⟨v949, rejectv949⟩, ⟨v950, rejectv950⟩, ⟨v951, rejectv951⟩, ⟨v952, rejectv952⟩, ⟨v953, rejectv953⟩, ⟨v954, rejectv954⟩, ⟨v955, rejectv955⟩, ⟨v956, rejectv956⟩, ⟨v957, rejectv957⟩, ⟨v958, rejectv958⟩, ⟨v959, rejectv959⟩]
    (by decide +kernel)

private def v960 : List Sig := [w164, raw3, raw6, raw0, raw1, raw2, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv960 : search 10 0 v960 = false := by decide +kernel

private def v961 : List Sig := [w165, raw3, raw6, raw0, raw1, raw2, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv961 : search 10 0 v961 = false := by decide +kernel

private def v962 : List Sig := [w166, raw3, raw7, raw0, raw1, raw2, raw4, raw5, raw6, raw8]

private def v963 : List Sig := [w327, raw5, raw3, raw7, raw0, raw1, raw2, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv963 : search 9 0 v963 = false := by decide +kernel

private def v964 : List Sig := [w328, raw3, raw7, raw0, raw1, raw2, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv964 : search 9 0 v964 = false := by decide +kernel

private def v965 : List Sig := [w328, w166, raw3, raw7, raw0, raw1, raw2, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv965 : search 9 0 v965 = false := by decide +kernel

private def v966 : List Sig := [w328, raw5, raw3, raw7, raw0, raw1, raw2, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv966 : search 9 0 v966 = false := by decide +kernel

private def v967 : List Sig := [w329, raw6, raw3, raw7, raw0, raw1, raw2, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv967 : search 9 0 v967 = false := by decide +kernel

private def v968 : List Sig := [w330, raw6, raw3, raw7, raw0, raw1, raw2, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv968 : search 9 0 v968 = false := by decide +kernel

private def v969 : List Sig := [w331, raw8, raw3, raw7, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv969 : search 9 0 v969 = false := by decide +kernel

private def v970 : List Sig := [w332, raw3, raw7, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv970 : search 9 0 v970 = false := by decide +kernel

private def v971 : List Sig := [w332, w166, raw3, raw7, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv971 : search 9 0 v971 = false := by decide +kernel

private def v972 : List Sig := [w332, raw8, raw3, raw7, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv972 : search 9 0 v972 = false := by decide +kernel

private def v973 : List Sig := [w19, raw7, w166, raw3, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv973 : search 9 0 v973 = false := by decide +kernel

private def v974 : List Sig := [w125, raw0, raw3, raw7, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv974 : search 9 0 v974 = false := by decide +kernel

private def v975 : List Sig := [w333, raw0, raw3, raw7, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv975 : search 9 0 v975 = false := by decide +kernel

private def v976 : List Sig := [w15, raw0, w166, raw3, raw7, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv976 : search 9 0 v976 = false := by decide +kernel

private def v977 : List Sig := [w334, raw1, raw3, raw7, raw0, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv977 : search 9 0 v977 = false := by decide +kernel

private def v978 : List Sig := [w335, raw3, raw7, raw0, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv978 : search 9 0 v978 = false := by decide +kernel

private def v979 : List Sig := [w335, raw1, raw3, raw7, raw0, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv979 : search 9 0 v979 = false := by decide +kernel

private def v980 : List Sig := [w335, w166, raw3, raw7, raw0, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv980 : search 9 0 v980 = false := by decide +kernel

private def v981 : List Sig := [w17, raw1, w166, raw3, raw7, raw0, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv981 : search 9 0 v981 = false := by decide +kernel

private def v982 : List Sig := [w297, raw2, raw3, raw7, raw0, raw1, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv982 : search 9 0 v982 = false := by decide +kernel

private def v983 : List Sig := [w336, raw2, raw3, raw7, raw0, raw1, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv983 : search 9 0 v983 = false := by decide +kernel

private def v984 : List Sig := [w337, raw4, raw3, raw7, raw0, raw1, raw2, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv984 : search 9 0 v984 = false := by decide +kernel

private def v985 : List Sig := [w338, raw4, raw3, raw7, raw0, raw1, raw2, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv985 : search 9 0 v985 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv962 : search 10 0 v962 = false := certifiedStep 9 0 v962
    []
    [⟨v963, rejectv963⟩, ⟨v964, rejectv964⟩, ⟨v965, rejectv965⟩, ⟨v966, rejectv966⟩, ⟨v967, rejectv967⟩, ⟨v968, rejectv968⟩, ⟨v969, rejectv969⟩, ⟨v970, rejectv970⟩, ⟨v971, rejectv971⟩, ⟨v972, rejectv972⟩, ⟨v973, rejectv973⟩, ⟨v974, rejectv974⟩, ⟨v975, rejectv975⟩, ⟨v976, rejectv976⟩, ⟨v977, rejectv977⟩, ⟨v978, rejectv978⟩, ⟨v979, rejectv979⟩, ⟨v980, rejectv980⟩, ⟨v981, rejectv981⟩, ⟨v982, rejectv982⟩, ⟨v983, rejectv983⟩, ⟨v984, rejectv984⟩, ⟨v985, rejectv985⟩]
    (by decide +kernel)

private def v986 : List Sig := [w67, raw3, raw7, raw0, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv986 : search 10 0 v986 = false := by decide +kernel

private def v987 : List Sig := [w210, raw3, raw8, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv987 : search 10 0 v987 = false := by decide +kernel

private def v988 : List Sig := [w68, raw3, raw8, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv988 : search 10 0 v988 = false := by decide +kernel

private def v989 : List Sig := [w200, raw4, raw1, raw0, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv989 : search 10 0 v989 = false := by decide +kernel

private def v990 : List Sig := [w201, raw4, raw1, raw0, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv990 : search 10 0 v990 = false := by decide +kernel

private def v991 : List Sig := [w169, raw4, raw2, raw0, raw1, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv991 : search 10 0 v991 = false := by decide +kernel

private def v992 : List Sig := [w56, raw4, raw2, raw0, raw1, raw3, raw5, raw6, raw7, raw8]

private def v993 : List Sig := [w339, raw1, raw4, raw2, raw0, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv993 : search 9 0 v993 = false := by decide +kernel

private def v994 : List Sig := [w340, raw1, raw4, raw2, raw0, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv994 : search 9 0 v994 = false := by decide +kernel

private def v995 : List Sig := [w341, raw4, raw2, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv995 : search 9 0 v995 = false := by decide +kernel

private def v996 : List Sig := [w341, w56, raw4, raw2, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv996 : search 9 0 v996 = false := by decide +kernel

private def v997 : List Sig := [w341, raw3, raw4, raw2, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv997 : search 9 0 v997 = false := by decide +kernel

private def v998 : List Sig := [w342, raw3, raw4, raw2, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv998 : search 9 0 v998 = false := by decide +kernel

private def v999 : List Sig := [w343, raw5, raw4, raw2, raw0, raw1, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv999 : search 9 0 v999 = false := by decide +kernel

private def v1000 : List Sig := [w344, raw5, raw4, raw2, raw0, raw1, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1000 : search 9 0 v1000 = false := by decide +kernel

private def v1001 : List Sig := [w345, raw6, raw4, raw2, raw0, raw1, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1001 : search 9 0 v1001 = false := by decide +kernel

private def v1002 : List Sig := [w346, raw6, raw4, raw2, raw0, raw1, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1002 : search 9 0 v1002 = false := by decide +kernel

private def v1003 : List Sig := [w347, raw7, raw4, raw2, raw0, raw1, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1003 : search 9 0 v1003 = false := by decide +kernel

private def v1004 : List Sig := [w348, raw7, raw4, raw2, raw0, raw1, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1004 : search 9 0 v1004 = false := by decide +kernel

private def v1005 : List Sig := [w349, raw8, raw4, raw2, raw0, raw1, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1005 : search 9 0 v1005 = false := by decide +kernel

private def v1006 : List Sig := [w350, raw8, raw4, raw2, raw0, raw1, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1006 : search 9 0 v1006 = false := by decide +kernel

private def v1007 : List Sig := [w201, raw1, w56, raw2, raw0, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1007 : search 9 0 v1007 = false := by decide +kernel

private def v1008 : List Sig := [w171, raw3, w56, raw2, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1008 : search 9 0 v1008 = false := by decide +kernel

private def v1009 : List Sig := [w172, raw5, w56, raw2, raw0, raw1, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1009 : search 9 0 v1009 = false := by decide +kernel

private def v1010 : List Sig := [w118, raw6, w56, raw2, raw0, raw1, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1010 : search 9 0 v1010 = false := by decide +kernel

private def v1011 : List Sig := [w18, raw1, w56, raw4, raw0, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1011 : search 9 0 v1011 = false := by decide +kernel

private def v1012 : List Sig := [w156, raw3, w56, raw4, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1012 : search 9 0 v1012 = false := by decide +kernel

private def v1013 : List Sig := [w158, raw5, w56, raw4, raw0, raw1, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1013 : search 9 0 v1013 = false := by decide +kernel

private def v1014 : List Sig := [w351, raw0, raw4, raw2, raw1, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1014 : search 9 0 v1014 = false := by decide +kernel

private def v1015 : List Sig := [w55, raw0, raw4, raw2, raw1, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1015 : search 9 0 v1015 = false := by decide +kernel

private def v1016 : List Sig := [w31, raw0, w56, raw4, raw1, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1016 : search 9 0 v1016 = false := by decide +kernel

private def v1017 : List Sig := [w15, raw0, w56, raw4, raw2, raw1, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1017 : search 9 0 v1017 = false := by decide +kernel

private def v1018 : List Sig := [w17, raw1, w56, raw4, raw2, raw0, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1018 : search 9 0 v1018 = false := by decide +kernel

private def v1019 : List Sig := [w19, raw7, w56, raw4, raw2, raw0, raw1, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1019 : search 9 0 v1019 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv992 : search 10 0 v992 = false := certifiedStep 9 0 v992
    []
    [⟨v993, rejectv993⟩, ⟨v994, rejectv994⟩, ⟨v995, rejectv995⟩, ⟨v996, rejectv996⟩, ⟨v997, rejectv997⟩, ⟨v998, rejectv998⟩, ⟨v999, rejectv999⟩, ⟨v1000, rejectv1000⟩, ⟨v1001, rejectv1001⟩, ⟨v1002, rejectv1002⟩, ⟨v1003, rejectv1003⟩, ⟨v1004, rejectv1004⟩, ⟨v1005, rejectv1005⟩, ⟨v1006, rejectv1006⟩, ⟨v1007, rejectv1007⟩, ⟨v1008, rejectv1008⟩, ⟨v1009, rejectv1009⟩, ⟨v1010, rejectv1010⟩, ⟨v1011, rejectv1011⟩, ⟨v1012, rejectv1012⟩, ⟨v1013, rejectv1013⟩, ⟨v1014, rejectv1014⟩, ⟨v1015, rejectv1015⟩, ⟨v1016, rejectv1016⟩, ⟨v1017, rejectv1017⟩, ⟨v1018, rejectv1018⟩, ⟨v1019, rejectv1019⟩]
    (by decide +kernel)

private def v1020 : List Sig := [w170, raw4, raw3, raw0, raw1, raw2, raw5, raw6, raw7, raw8]

private def v1021 : List Sig := [w352, raw1, raw4, raw3, raw0, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1021 : search 9 0 v1021 = false := by decide +kernel

private def v1022 : List Sig := [w353, raw4, raw3, raw0, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1022 : search 9 0 v1022 = false := by decide +kernel

private def v1023 : List Sig := [w353, w170, raw4, raw3, raw0, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1023 : search 9 0 v1023 = false := by decide +kernel

private def v1024 : List Sig := [w353, raw1, raw4, raw3, raw0, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1024 : search 9 0 v1024 = false := by decide +kernel

private def v1025 : List Sig := [w291, raw2, raw4, raw3, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1025 : search 9 0 v1025 = false := by decide +kernel

private def v1026 : List Sig := [w354, raw4, raw3, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1026 : search 9 0 v1026 = false := by decide +kernel

private def v1027 : List Sig := [w354, w170, raw4, raw3, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1027 : search 9 0 v1027 = false := by decide +kernel

private def v1028 : List Sig := [w354, raw2, raw4, raw3, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1028 : search 9 0 v1028 = false := by decide +kernel

private def v1029 : List Sig := [w355, raw5, raw4, raw3, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1029 : search 9 0 v1029 = false := by decide +kernel

private def v1030 : List Sig := [w356, raw4, raw3, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1030 : search 9 0 v1030 = false := by decide +kernel

private def v1031 : List Sig := [w356, w170, raw4, raw3, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1031 : search 9 0 v1031 = false := by decide +kernel

private def v1032 : List Sig := [w356, raw5, raw4, raw3, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1032 : search 9 0 v1032 = false := by decide +kernel

private def v1033 : List Sig := [w357, raw6, raw4, raw3, raw0, raw1, raw2, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1033 : search 9 0 v1033 = false := by decide +kernel

private def v1034 : List Sig := [w358, raw4, raw3, raw0, raw1, raw2, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1034 : search 9 0 v1034 = false := by decide +kernel

private def v1035 : List Sig := [w358, w170, raw4, raw3, raw0, raw1, raw2, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1035 : search 9 0 v1035 = false := by decide +kernel

private def v1036 : List Sig := [w358, raw6, raw4, raw3, raw0, raw1, raw2, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1036 : search 9 0 v1036 = false := by decide +kernel

private def v1037 : List Sig := [w337, raw7, raw4, raw3, raw0, raw1, raw2, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1037 : search 9 0 v1037 = false := by decide +kernel

private def v1038 : List Sig := [w359, raw4, raw3, raw0, raw1, raw2, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1038 : search 9 0 v1038 = false := by decide +kernel

private def v1039 : List Sig := [w359, w170, raw4, raw3, raw0, raw1, raw2, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1039 : search 9 0 v1039 = false := by decide +kernel

private def v1040 : List Sig := [w359, raw7, raw4, raw3, raw0, raw1, raw2, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1040 : search 9 0 v1040 = false := by decide +kernel

private def v1041 : List Sig := [w360, raw8, raw4, raw3, raw0, raw1, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1041 : search 9 0 v1041 = false := by decide +kernel

private def v1042 : List Sig := [w361, raw4, raw3, raw0, raw1, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1042 : search 9 0 v1042 = false := by decide +kernel

private def v1043 : List Sig := [w361, w170, raw4, raw3, raw0, raw1, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1043 : search 9 0 v1043 = false := by decide +kernel

private def v1044 : List Sig := [w361, raw8, raw4, raw3, raw0, raw1, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1044 : search 9 0 v1044 = false := by decide +kernel

private def v1045 : List Sig := [w172, raw5, w170, raw3, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1045 : search 9 0 v1045 = false := by decide +kernel

private def v1046 : List Sig := [w118, raw6, w170, raw3, raw0, raw1, raw2, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1046 : search 9 0 v1046 = false := by decide +kernel

private def v1047 : List Sig := [w77, raw0, raw4, raw3, raw1, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1047 : search 9 0 v1047 = false := by decide +kernel

private def v1048 : List Sig := [w362, raw4, raw3, raw1, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1048 : search 9 0 v1048 = false := by decide +kernel

private def v1049 : List Sig := [w362, raw0, raw4, raw3, raw1, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1049 : search 9 0 v1049 = false := by decide +kernel

private def v1050 : List Sig := [w362, w170, raw4, raw3, raw1, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1050 : search 9 0 v1050 = false := by decide +kernel

private def v1051 : List Sig := [w15, raw0, w170, raw4, raw3, raw1, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1051 : search 9 0 v1051 = false := by decide +kernel

private def v1052 : List Sig := [w16, raw1, w170, raw4, raw0, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1052 : search 9 0 v1052 = false := by decide +kernel

private def v1053 : List Sig := [w17, raw1, w170, raw4, raw3, raw0, raw2, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1053 : search 9 0 v1053 = false := by decide +kernel

private def v1054 : List Sig := [w51, raw2, w170, raw4, raw0, raw1, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1054 : search 9 0 v1054 = false := by decide +kernel

private def v1055 : List Sig := [w19, raw7, w170, raw4, raw3, raw0, raw1, raw2, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1055 : search 9 0 v1055 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1020 : search 10 0 v1020 = false := certifiedStep 9 0 v1020
    []
    [⟨v1021, rejectv1021⟩, ⟨v1022, rejectv1022⟩, ⟨v1023, rejectv1023⟩, ⟨v1024, rejectv1024⟩, ⟨v1025, rejectv1025⟩, ⟨v1026, rejectv1026⟩, ⟨v1027, rejectv1027⟩, ⟨v1028, rejectv1028⟩, ⟨v1029, rejectv1029⟩, ⟨v1030, rejectv1030⟩, ⟨v1031, rejectv1031⟩, ⟨v1032, rejectv1032⟩, ⟨v1033, rejectv1033⟩, ⟨v1034, rejectv1034⟩, ⟨v1035, rejectv1035⟩, ⟨v1036, rejectv1036⟩, ⟨v1037, rejectv1037⟩, ⟨v1038, rejectv1038⟩, ⟨v1039, rejectv1039⟩, ⟨v1040, rejectv1040⟩, ⟨v1041, rejectv1041⟩, ⟨v1042, rejectv1042⟩, ⟨v1043, rejectv1043⟩, ⟨v1044, rejectv1044⟩, ⟨v1045, rejectv1045⟩, ⟨v1046, rejectv1046⟩, ⟨v1047, rejectv1047⟩, ⟨v1048, rejectv1048⟩, ⟨v1049, rejectv1049⟩, ⟨v1050, rejectv1050⟩, ⟨v1051, rejectv1051⟩, ⟨v1052, rejectv1052⟩, ⟨v1053, rejectv1053⟩, ⟨v1054, rejectv1054⟩, ⟨v1055, rejectv1055⟩]
    (by decide +kernel)

private def v1056 : List Sig := [w171, raw4, raw3, raw0, raw1, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1056 : search 10 0 v1056 = false := by decide +kernel

private def v1057 : List Sig := [w172, raw4, raw5, raw0, raw1, raw2, raw3, raw6, raw7, raw8]

private def v1058 : List Sig := [w250, raw1, raw4, raw5, raw0, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1058 : search 9 0 v1058 = false := by decide +kernel

private def v1059 : List Sig := [w363, raw4, raw5, raw0, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1059 : search 9 0 v1059 = false := by decide +kernel

private def v1060 : List Sig := [w363, w172, raw4, raw5, raw0, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1060 : search 9 0 v1060 = false := by decide +kernel

private def v1061 : List Sig := [w363, raw1, raw4, raw5, raw0, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1061 : search 9 0 v1061 = false := by decide +kernel

private def v1062 : List Sig := [w364, raw2, raw4, raw5, raw0, raw1, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1062 : search 9 0 v1062 = false := by decide +kernel

private def v1063 : List Sig := [w365, raw4, raw5, raw0, raw1, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1063 : search 9 0 v1063 = false := by decide +kernel

private def v1064 : List Sig := [w365, w172, raw4, raw5, raw0, raw1, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1064 : search 9 0 v1064 = false := by decide +kernel

private def v1065 : List Sig := [w365, raw2, raw4, raw5, raw0, raw1, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1065 : search 9 0 v1065 = false := by decide +kernel

private def v1066 : List Sig := [w355, raw3, raw4, raw5, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1066 : search 9 0 v1066 = false := by decide +kernel

private def v1067 : List Sig := [w366, raw4, raw5, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1067 : search 9 0 v1067 = false := by decide +kernel

private def v1068 : List Sig := [w366, w172, raw4, raw5, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1068 : search 9 0 v1068 = false := by decide +kernel

private def v1069 : List Sig := [w366, raw3, raw4, raw5, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1069 : search 9 0 v1069 = false := by decide +kernel

private def v1070 : List Sig := [w367, raw6, raw4, raw5, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1070 : search 9 0 v1070 = false := by decide +kernel

private def v1071 : List Sig := [w368, raw4, raw5, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1071 : search 9 0 v1071 = false := by decide +kernel

private def v1072 : List Sig := [w368, w172, raw4, raw5, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1072 : search 9 0 v1072 = false := by decide +kernel

private def v1073 : List Sig := [w368, raw6, raw4, raw5, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1073 : search 9 0 v1073 = false := by decide +kernel

private def v1074 : List Sig := [w369, raw7, raw4, raw5, raw0, raw1, raw2, raw3, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1074 : search 9 0 v1074 = false := by decide +kernel

private def v1075 : List Sig := [w370, raw4, raw5, raw0, raw1, raw2, raw3, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1075 : search 9 0 v1075 = false := by decide +kernel

private def v1076 : List Sig := [w370, w172, raw4, raw5, raw0, raw1, raw2, raw3, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1076 : search 9 0 v1076 = false := by decide +kernel

private def v1077 : List Sig := [w370, raw7, raw4, raw5, raw0, raw1, raw2, raw3, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1077 : search 9 0 v1077 = false := by decide +kernel

private def v1078 : List Sig := [w371, raw8, raw4, raw5, raw0, raw1, raw2, raw3, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1078 : search 9 0 v1078 = false := by decide +kernel

private def v1079 : List Sig := [w372, raw4, raw5, raw0, raw1, raw2, raw3, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1079 : search 9 0 v1079 = false := by decide +kernel

private def v1080 : List Sig := [w372, w172, raw4, raw5, raw0, raw1, raw2, raw3, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1080 : search 9 0 v1080 = false := by decide +kernel

private def v1081 : List Sig := [w372, raw8, raw4, raw5, raw0, raw1, raw2, raw3, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1081 : search 9 0 v1081 = false := by decide +kernel

private def v1082 : List Sig := [w56, raw2, w172, raw5, raw0, raw1, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1082 : search 9 0 v1082 = false := by decide +kernel

private def v1083 : List Sig := [w170, raw3, w172, raw5, raw0, raw1, raw2, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1083 : search 9 0 v1083 = false := by decide +kernel

private def v1084 : List Sig := [w120, raw6, w172, raw4, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1084 : search 9 0 v1084 = false := by decide +kernel

private def v1085 : List Sig := [w96, raw7, w172, raw4, raw0, raw1, raw2, raw3, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1085 : search 9 0 v1085 = false := by decide +kernel

private def v1086 : List Sig := [w79, raw0, raw4, raw5, raw1, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1086 : search 9 0 v1086 = false := by decide +kernel

private def v1087 : List Sig := [w373, raw4, raw5, raw1, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1087 : search 9 0 v1087 = false := by decide +kernel

private def v1088 : List Sig := [w373, raw0, raw4, raw5, raw1, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1088 : search 9 0 v1088 = false := by decide +kernel

private def v1089 : List Sig := [w373, w172, raw4, raw5, raw1, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1089 : search 9 0 v1089 = false := by decide +kernel

private def v1090 : List Sig := [w15, raw0, w172, raw4, raw5, raw1, raw2, raw3, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1090 : search 9 0 v1090 = false := by decide +kernel

private def v1091 : List Sig := [w17, raw1, w172, raw4, raw5, raw0, raw2, raw3, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1091 : search 9 0 v1091 = false := by decide +kernel

private def v1092 : List Sig := [w19, raw7, w172, raw4, raw5, raw0, raw1, raw2, raw3, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1092 : search 9 0 v1092 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1057 : search 10 0 v1057 = false := certifiedStep 9 0 v1057
    []
    [⟨v1058, rejectv1058⟩, ⟨v1059, rejectv1059⟩, ⟨v1060, rejectv1060⟩, ⟨v1061, rejectv1061⟩, ⟨v1062, rejectv1062⟩, ⟨v1063, rejectv1063⟩, ⟨v1064, rejectv1064⟩, ⟨v1065, rejectv1065⟩, ⟨v1066, rejectv1066⟩, ⟨v1067, rejectv1067⟩, ⟨v1068, rejectv1068⟩, ⟨v1069, rejectv1069⟩, ⟨v1070, rejectv1070⟩, ⟨v1071, rejectv1071⟩, ⟨v1072, rejectv1072⟩, ⟨v1073, rejectv1073⟩, ⟨v1074, rejectv1074⟩, ⟨v1075, rejectv1075⟩, ⟨v1076, rejectv1076⟩, ⟨v1077, rejectv1077⟩, ⟨v1078, rejectv1078⟩, ⟨v1079, rejectv1079⟩, ⟨v1080, rejectv1080⟩, ⟨v1081, rejectv1081⟩, ⟨v1082, rejectv1082⟩, ⟨v1083, rejectv1083⟩, ⟨v1084, rejectv1084⟩, ⟨v1085, rejectv1085⟩, ⟨v1086, rejectv1086⟩, ⟨v1087, rejectv1087⟩, ⟨v1088, rejectv1088⟩, ⟨v1089, rejectv1089⟩, ⟨v1090, rejectv1090⟩, ⟨v1091, rejectv1091⟩, ⟨v1092, rejectv1092⟩]
    (by decide +kernel)

private def v1093 : List Sig := [w173, raw4, raw5, raw0, raw1, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1093 : search 10 0 v1093 = false := by decide +kernel

private def v1094 : List Sig := [w174, raw4, raw6, raw0, raw1, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1094 : search 10 0 v1094 = false := by decide +kernel

private def v1095 : List Sig := [w118, raw4, raw6, raw0, raw1, raw2, raw3, raw5, raw7, raw8]

private def v1096 : List Sig := [w374, raw7, raw4, raw6, raw0, raw1, raw2, raw3, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1096 : search 9 0 v1096 = false := by decide +kernel

private def v1097 : List Sig := [w375, raw7, raw4, raw6, raw0, raw1, raw2, raw3, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1097 : search 9 0 v1097 = false := by decide +kernel

private def v1098 : List Sig := [w376, raw8, raw4, raw6, raw0, raw1, raw2, raw3, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1098 : search 9 0 v1098 = false := by decide +kernel

private def v1099 : List Sig := [w377, raw8, raw4, raw6, raw0, raw1, raw2, raw3, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1099 : search 9 0 v1099 = false := by decide +kernel

private def v1100 : List Sig := [w56, raw2, w118, raw6, raw0, raw1, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1100 : search 9 0 v1100 = false := by decide +kernel

private def v1101 : List Sig := [w170, raw3, w118, raw6, raw0, raw1, raw2, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1101 : search 9 0 v1101 = false := by decide +kernel

private def v1102 : List Sig := [w173, raw5, w118, raw6, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1102 : search 9 0 v1102 = false := by decide +kernel

private def v1103 : List Sig := [w176, raw7, w118, raw6, raw0, raw1, raw2, raw3, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1103 : search 9 0 v1103 = false := by decide +kernel

private def v1104 : List Sig := [w134, raw7, w118, raw4, raw0, raw1, raw2, raw3, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1104 : search 9 0 v1104 = false := by decide +kernel

private def v1105 : List Sig := [w378, raw0, raw4, raw6, raw1, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1105 : search 9 0 v1105 = false := by decide +kernel

private def v1106 : List Sig := [w117, raw0, raw4, raw6, raw1, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1106 : search 9 0 v1106 = false := by decide +kernel

private def v1107 : List Sig := [w95, raw0, w118, raw4, raw1, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1107 : search 9 0 v1107 = false := by decide +kernel

private def v1108 : List Sig := [w15, raw0, w118, raw4, raw6, raw1, raw2, raw3, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1108 : search 9 0 v1108 = false := by decide +kernel

private def v1109 : List Sig := [w379, raw1, raw4, raw6, raw0, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1109 : search 9 0 v1109 = false := by decide +kernel

private def v1110 : List Sig := [w380, raw1, raw4, raw6, raw0, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1110 : search 9 0 v1110 = false := by decide +kernel

private def v1111 : List Sig := [w17, raw1, w118, raw4, raw6, raw0, raw2, raw3, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1111 : search 9 0 v1111 = false := by decide +kernel

private def v1112 : List Sig := [w381, raw2, raw4, raw6, raw0, raw1, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1112 : search 9 0 v1112 = false := by decide +kernel

private def v1113 : List Sig := [w346, raw2, raw4, raw6, raw0, raw1, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1113 : search 9 0 v1113 = false := by decide +kernel

private def v1114 : List Sig := [w382, raw3, raw4, raw6, raw0, raw1, raw2, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1114 : search 9 0 v1114 = false := by decide +kernel

private def v1115 : List Sig := [w383, raw3, raw4, raw6, raw0, raw1, raw2, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1115 : search 9 0 v1115 = false := by decide +kernel

private def v1116 : List Sig := [w165, raw3, w118, raw4, raw0, raw1, raw2, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1116 : search 9 0 v1116 = false := by decide +kernel

private def v1117 : List Sig := [w384, raw4, raw6, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1117 : search 9 0 v1117 = false := by decide +kernel

private def v1118 : List Sig := [w384, raw5, raw4, raw6, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1118 : search 9 0 v1118 = false := by decide +kernel

private def v1119 : List Sig := [w384, w118, raw4, raw6, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1119 : search 9 0 v1119 = false := by decide +kernel

private def v1120 : List Sig := [w385, raw5, raw4, raw6, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1120 : search 9 0 v1120 = false := by decide +kernel

private def v1121 : List Sig := [w177, raw5, w118, raw4, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1121 : search 9 0 v1121 = false := by decide +kernel

private def v1122 : List Sig := [w19, raw7, w118, raw4, raw6, raw0, raw1, raw2, raw3, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1122 : search 9 0 v1122 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1095 : search 10 0 v1095 = false := certifiedStep 9 0 v1095
    []
    [⟨v1096, rejectv1096⟩, ⟨v1097, rejectv1097⟩, ⟨v1098, rejectv1098⟩, ⟨v1099, rejectv1099⟩, ⟨v1100, rejectv1100⟩, ⟨v1101, rejectv1101⟩, ⟨v1102, rejectv1102⟩, ⟨v1103, rejectv1103⟩, ⟨v1104, rejectv1104⟩, ⟨v1105, rejectv1105⟩, ⟨v1106, rejectv1106⟩, ⟨v1107, rejectv1107⟩, ⟨v1108, rejectv1108⟩, ⟨v1109, rejectv1109⟩, ⟨v1110, rejectv1110⟩, ⟨v1111, rejectv1111⟩, ⟨v1112, rejectv1112⟩, ⟨v1113, rejectv1113⟩, ⟨v1114, rejectv1114⟩, ⟨v1115, rejectv1115⟩, ⟨v1116, rejectv1116⟩, ⟨v1117, rejectv1117⟩, ⟨v1118, rejectv1118⟩, ⟨v1119, rejectv1119⟩, ⟨v1120, rejectv1120⟩, ⟨v1121, rejectv1121⟩, ⟨v1122, rejectv1122⟩]
    (by decide +kernel)

private def v1123 : List Sig := [w175, raw4, raw7, raw0, raw1, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1123 : search 10 0 v1123 = false := by decide +kernel

private def v1124 : List Sig := [w176, raw4, raw7, raw0, raw1, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1124 : search 10 0 v1124 = false := by decide +kernel

private def v1125 : List Sig := [w211, raw4, raw8, raw0, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1125 : search 10 0 v1125 = false := by decide +kernel

private def v1126 : List Sig := [w212, raw4, raw8, raw0, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1126 : search 10 0 v1126 = false := by decide +kernel

private def v1127 : List Sig := [w120, raw5, raw6, raw0, raw1, raw2, raw3, raw4, raw7, raw8]

private def v1128 : List Sig := [w386, raw7, raw5, raw6, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1128 : search 9 0 v1128 = false := by decide +kernel

private def v1129 : List Sig := [w387, raw5, raw6, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1129 : search 9 0 v1129 = false := by decide +kernel

private def v1130 : List Sig := [w387, w120, raw5, raw6, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1130 : search 9 0 v1130 = false := by decide +kernel

private def v1131 : List Sig := [w387, raw7, raw5, raw6, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1131 : search 9 0 v1131 = false := by decide +kernel

private def v1132 : List Sig := [w388, raw8, raw5, raw6, raw0, raw1, raw2, raw3, raw4, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1132 : search 9 0 v1132 = false := by decide +kernel

private def v1133 : List Sig := [w389, raw5, raw6, raw0, raw1, raw2, raw3, raw4, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1133 : search 9 0 v1133 = false := by decide +kernel

private def v1134 : List Sig := [w389, w120, raw5, raw6, raw0, raw1, raw2, raw3, raw4, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1134 : search 9 0 v1134 = false := by decide +kernel

private def v1135 : List Sig := [w389, raw8, raw5, raw6, raw0, raw1, raw2, raw3, raw4, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1135 : search 9 0 v1135 = false := by decide +kernel

private def v1136 : List Sig := [w134, raw7, w120, raw5, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1136 : search 9 0 v1136 = false := by decide +kernel

private def v1137 : List Sig := [w390, raw0, raw5, raw6, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1137 : search 9 0 v1137 = false := by decide +kernel

private def v1138 : List Sig := [w391, raw5, raw6, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1138 : search 9 0 v1138 = false := by decide +kernel

private def v1139 : List Sig := [w391, raw0, raw5, raw6, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1139 : search 9 0 v1139 = false := by decide +kernel

private def v1140 : List Sig := [w391, w120, raw5, raw6, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1140 : search 9 0 v1140 = false := by decide +kernel

private def v1141 : List Sig := [w95, raw0, w120, raw5, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1141 : search 9 0 v1141 = false := by decide +kernel

private def v1142 : List Sig := [w15, raw0, w120, raw5, raw6, raw1, raw2, raw3, raw4, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1142 : search 9 0 v1142 = false := by decide +kernel

private def v1143 : List Sig := [w241, raw1, raw5, raw6, raw0, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1143 : search 9 0 v1143 = false := by decide +kernel

private def v1144 : List Sig := [w392, raw5, raw6, raw0, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1144 : search 9 0 v1144 = false := by decide +kernel

private def v1145 : List Sig := [w392, raw1, raw5, raw6, raw0, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1145 : search 9 0 v1145 = false := by decide +kernel

private def v1146 : List Sig := [w392, w120, raw5, raw6, raw0, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1146 : search 9 0 v1146 = false := by decide +kernel

private def v1147 : List Sig := [w17, raw1, w120, raw5, raw6, raw0, raw2, raw3, raw4, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1147 : search 9 0 v1147 = false := by decide +kernel

private def v1148 : List Sig := [w305, raw2, raw5, raw6, raw0, raw1, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1148 : search 9 0 v1148 = false := by decide +kernel

private def v1149 : List Sig := [w393, raw5, raw6, raw0, raw1, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1149 : search 9 0 v1149 = false := by decide +kernel

private def v1150 : List Sig := [w393, raw2, raw5, raw6, raw0, raw1, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1150 : search 9 0 v1150 = false := by decide +kernel

private def v1151 : List Sig := [w393, w120, raw5, raw6, raw0, raw1, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1151 : search 9 0 v1151 = false := by decide +kernel

private def v1152 : List Sig := [w394, raw3, raw5, raw6, raw0, raw1, raw2, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1152 : search 9 0 v1152 = false := by decide +kernel

private def v1153 : List Sig := [w395, raw5, raw6, raw0, raw1, raw2, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1153 : search 9 0 v1153 = false := by decide +kernel

private def v1154 : List Sig := [w395, raw3, raw5, raw6, raw0, raw1, raw2, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1154 : search 9 0 v1154 = false := by decide +kernel

private def v1155 : List Sig := [w395, w120, raw5, raw6, raw0, raw1, raw2, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1155 : search 9 0 v1155 = false := by decide +kernel

private def v1156 : List Sig := [w163, raw3, w120, raw6, raw0, raw1, raw2, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1156 : search 9 0 v1156 = false := by decide +kernel

private def v1157 : List Sig := [w367, raw4, raw5, raw6, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1157 : search 9 0 v1157 = false := by decide +kernel

private def v1158 : List Sig := [w396, raw5, raw6, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1158 : search 9 0 v1158 = false := by decide +kernel

private def v1159 : List Sig := [w396, raw4, raw5, raw6, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1159 : search 9 0 v1159 = false := by decide +kernel

private def v1160 : List Sig := [w396, w120, raw5, raw6, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1160 : search 9 0 v1160 = false := by decide +kernel

private def v1161 : List Sig := [w172, raw4, w120, raw6, raw0, raw1, raw2, raw3, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1161 : search 9 0 v1161 = false := by decide +kernel

private def v1162 : List Sig := [w19, raw7, w120, raw5, raw6, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1162 : search 9 0 v1162 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1127 : search 10 0 v1127 = false := certifiedStep 9 0 v1127
    []
    [⟨v1128, rejectv1128⟩, ⟨v1129, rejectv1129⟩, ⟨v1130, rejectv1130⟩, ⟨v1131, rejectv1131⟩, ⟨v1132, rejectv1132⟩, ⟨v1133, rejectv1133⟩, ⟨v1134, rejectv1134⟩, ⟨v1135, rejectv1135⟩, ⟨v1136, rejectv1136⟩, ⟨v1137, rejectv1137⟩, ⟨v1138, rejectv1138⟩, ⟨v1139, rejectv1139⟩, ⟨v1140, rejectv1140⟩, ⟨v1141, rejectv1141⟩, ⟨v1142, rejectv1142⟩, ⟨v1143, rejectv1143⟩, ⟨v1144, rejectv1144⟩, ⟨v1145, rejectv1145⟩, ⟨v1146, rejectv1146⟩, ⟨v1147, rejectv1147⟩, ⟨v1148, rejectv1148⟩, ⟨v1149, rejectv1149⟩, ⟨v1150, rejectv1150⟩, ⟨v1151, rejectv1151⟩, ⟨v1152, rejectv1152⟩, ⟨v1153, rejectv1153⟩, ⟨v1154, rejectv1154⟩, ⟨v1155, rejectv1155⟩, ⟨v1156, rejectv1156⟩, ⟨v1157, rejectv1157⟩, ⟨v1158, rejectv1158⟩, ⟨v1159, rejectv1159⟩, ⟨v1160, rejectv1160⟩, ⟨v1161, rejectv1161⟩, ⟨v1162, rejectv1162⟩]
    (by decide +kernel)

private def v1163 : List Sig := [w177, raw5, raw6, raw0, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1163 : search 10 0 v1163 = false := by decide +kernel

private def v1164 : List Sig := [w178, raw5, raw7, raw0, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1164 : search 10 0 v1164 = false := by decide +kernel

private def v1165 : List Sig := [w96, raw5, raw7, raw0, raw1, raw2, raw3, raw4, raw6, raw8]

private def v1166 : List Sig := [w397, raw8, raw5, raw7, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1166 : search 9 0 v1166 = false := by decide +kernel

private def v1167 : List Sig := [w398, raw8, raw5, raw7, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1167 : search 9 0 v1167 = false := by decide +kernel

private def v1168 : List Sig := [w177, raw6, w96, raw7, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1168 : search 9 0 v1168 = false := by decide +kernel

private def v1169 : List Sig := [w19, w96, raw5, raw0, raw1, raw2, raw3, raw4, raw6]

private def v1170 : List Sig := [w399, w19, raw5, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1170 : search 8 0 v1170 = false := by decide +kernel

private def v1171 : List Sig := [w177, raw6, w19, w96, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1171 : search 8 0 v1171 = false := by decide +kernel

private def v1172 : List Sig := [w189, raw0, w96, raw5, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1172 : search 8 0 v1172 = false := by decide +kernel

private def v1173 : List Sig := [w92, raw0, w19, raw5, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1173 : search 8 0 v1173 = false := by decide +kernel

private def v1174 : List Sig := [w88, raw0, w19, w96, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1174 : search 8 0 v1174 = false := by decide +kernel

private def v1175 : List Sig := [w226, raw1, w96, raw5, raw0, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1175 : search 8 0 v1175 = false := by decide +kernel

private def v1176 : List Sig := [w163, raw3, w19, w96, raw0, raw1, raw2, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1176 : search 8 0 v1176 = false := by decide +kernel

private def v1177 : List Sig := [w172, raw4, w19, w96, raw0, raw1, raw2, raw3, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1177 : search 8 0 v1177 = false := by decide +kernel

private def v1178 : List Sig := [w400, w19, raw5, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1178 : search 8 0 v1178 = false := by decide +kernel

private def v1179 : List Sig := [w400, raw6, w19, raw5, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1179 : search 8 0 v1179 = false := by decide +kernel

private def v1180 : List Sig := [w400, w96, w19, raw5, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1180 : search 8 0 v1180 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1169 : search 9 0 v1169 = false := certifiedStep 8 0 v1169
    []
    [⟨v1170, rejectv1170⟩, ⟨v1171, rejectv1171⟩, ⟨v1172, rejectv1172⟩, ⟨v1173, rejectv1173⟩, ⟨v1174, rejectv1174⟩, ⟨v1175, rejectv1175⟩, ⟨v1176, rejectv1176⟩, ⟨v1177, rejectv1177⟩, ⟨v1178, rejectv1178⟩, ⟨v1179, rejectv1179⟩, ⟨v1180, rejectv1180⟩]
    (by decide +kernel)

private def v1181 : List Sig := [w19, raw7, w96, raw5, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1181 : search 9 0 v1181 = false := by decide +kernel

private def v1182 : List Sig := [w19, raw8, w96, raw5, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1182 : search 9 0 v1182 = false := by decide +kernel

private def v1183 : List Sig := [w401, raw0, raw5, raw7, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1183 : search 9 0 v1183 = false := by decide +kernel

private def v1184 : List Sig := [w92, raw0, raw5, raw7, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1184 : search 9 0 v1184 = false := by decide +kernel

private def v1185 : List Sig := [w88, raw0, w96, raw7, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1185 : search 9 0 v1185 = false := by decide +kernel

private def v1186 : List Sig := [w121, raw0, w96, raw5, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1186 : search 9 0 v1186 = false := by decide +kernel

private def v1187 : List Sig := [w15, raw0, w96, raw5, raw7, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1187 : search 9 0 v1187 = false := by decide +kernel

private def v1188 : List Sig := [w402, raw1, raw5, raw7, raw0, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1188 : search 9 0 v1188 = false := by decide +kernel

private def v1189 : List Sig := [w261, raw1, raw5, raw7, raw0, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1189 : search 9 0 v1189 = false := by decide +kernel

private def v1190 : List Sig := [w32, raw1, w96, raw5, raw0, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1190 : search 9 0 v1190 = false := by decide +kernel

private def v1191 : List Sig := [w17, raw1, w96, raw5, raw7, raw0, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1191 : search 9 0 v1191 = false := by decide +kernel

private def v1192 : List Sig := [w403, raw2, raw5, raw7, raw0, raw1, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1192 : search 9 0 v1192 = false := by decide +kernel

private def v1193 : List Sig := [w404, raw2, raw5, raw7, raw0, raw1, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1193 : search 9 0 v1193 = false := by decide +kernel

private def v1194 : List Sig := [w405, raw3, raw5, raw7, raw0, raw1, raw2, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1194 : search 9 0 v1194 = false := by decide +kernel

private def v1195 : List Sig := [w318, raw3, raw5, raw7, raw0, raw1, raw2, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1195 : search 9 0 v1195 = false := by decide +kernel

private def v1196 : List Sig := [w163, raw3, w96, raw7, raw0, raw1, raw2, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1196 : search 9 0 v1196 = false := by decide +kernel

private def v1197 : List Sig := [w406, raw4, raw5, raw7, raw0, raw1, raw2, raw3, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1197 : search 9 0 v1197 = false := by decide +kernel

private def v1198 : List Sig := [w407, raw4, raw5, raw7, raw0, raw1, raw2, raw3, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1198 : search 9 0 v1198 = false := by decide +kernel

private def v1199 : List Sig := [w172, raw4, w96, raw7, raw0, raw1, raw2, raw3, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1199 : search 9 0 v1199 = false := by decide +kernel

private def v1200 : List Sig := [w176, raw4, w96, raw5, raw0, raw1, raw2, raw3, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1200 : search 9 0 v1200 = false := by decide +kernel

private def v1201 : List Sig := [w400, raw5, raw7, raw0, raw1, raw2, raw3, raw4, raw8]

private def v1202 : List Sig := [w387, w400, raw5, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1202 : search 8 0 v1202 = false := by decide +kernel

private def v1203 : List Sig := [w408, w400, raw5, raw7, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1203 : search 8 0 v1203 = false := by decide +kernel

private def v1204 : List Sig := [w409, w400, raw7, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1204 : search 8 0 v1204 = false := by decide +kernel

private def v1205 : List Sig := [w19, w400, raw5, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1205 : search 8 0 v1205 = false := by decide +kernel

private def v1206 : List Sig := [w19, raw7, w400, raw5, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1206 : search 8 0 v1206 = false := by decide +kernel

private def v1207 : List Sig := [w19, raw8, w400, raw5, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1207 : search 8 0 v1207 = false := by decide +kernel

private def v1208 : List Sig := [w410, w400, raw5, raw7, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1208 : search 8 0 v1208 = false := by decide +kernel

private def v1209 : List Sig := [w121, raw0, w400, raw5, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1209 : search 8 0 v1209 = false := by decide +kernel

private def v1210 : List Sig := [w15, raw0, w400, raw5, raw7, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1210 : search 8 0 v1210 = false := by decide +kernel

private def v1211 : List Sig := [w411, w400, raw5, raw7, raw0, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1211 : search 8 0 v1211 = false := by decide +kernel

private def v1212 : List Sig := [w32, raw1, w400, raw5, raw0, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1212 : search 8 0 v1212 = false := by decide +kernel

private def v1213 : List Sig := [w17, raw1, w400, raw5, raw7, raw0, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1213 : search 8 0 v1213 = false := by decide +kernel

private def v1214 : List Sig := [w412, w400, raw5, raw7, raw0, raw1, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1214 : search 8 0 v1214 = false := by decide +kernel

private def v1215 : List Sig := [w413, w400, raw5, raw7, raw0, raw1, raw2, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1215 : search 8 0 v1215 = false := by decide +kernel

private def v1216 : List Sig := [w163, raw3, w400, raw7, raw0, raw1, raw2, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1216 : search 8 0 v1216 = false := by decide +kernel

private def v1217 : List Sig := [w414, w400, raw5, raw7, raw0, raw1, raw2, raw3, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1217 : search 8 0 v1217 = false := by decide +kernel

private def v1218 : List Sig := [w172, raw4, w400, raw7, raw0, raw1, raw2, raw3, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1218 : search 8 0 v1218 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1201 : search 9 0 v1201 = false := certifiedStep 8 0 v1201
    []
    [⟨v1202, rejectv1202⟩, ⟨v1203, rejectv1203⟩, ⟨v1204, rejectv1204⟩, ⟨v1205, rejectv1205⟩, ⟨v1206, rejectv1206⟩, ⟨v1207, rejectv1207⟩, ⟨v1208, rejectv1208⟩, ⟨v1209, rejectv1209⟩, ⟨v1210, rejectv1210⟩, ⟨v1211, rejectv1211⟩, ⟨v1212, rejectv1212⟩, ⟨v1213, rejectv1213⟩, ⟨v1214, rejectv1214⟩, ⟨v1215, rejectv1215⟩, ⟨v1216, rejectv1216⟩, ⟨v1217, rejectv1217⟩, ⟨v1218, rejectv1218⟩]
    (by decide +kernel)

private def v1219 : List Sig := [w400, raw6, raw5, raw7, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1219 : search 9 0 v1219 = false := by decide +kernel

private def v1220 : List Sig := [w400, w96, raw5, raw7, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1220 : search 9 0 v1220 = false := by decide +kernel

private def v1221 : List Sig := [w415, raw6, raw5, raw7, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1221 : search 9 0 v1221 = false := by decide +kernel

private def v1222 : List Sig := [w110, raw6, w96, raw5, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1222 : search 9 0 v1222 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1165 : search 10 0 v1165 = false := certifiedStep 9 0 v1165
    []
    [⟨v1166, rejectv1166⟩, ⟨v1167, rejectv1167⟩, ⟨v1168, rejectv1168⟩, ⟨v1169, rejectv1169⟩, ⟨v1181, rejectv1181⟩, ⟨v1182, rejectv1182⟩, ⟨v1183, rejectv1183⟩, ⟨v1184, rejectv1184⟩, ⟨v1185, rejectv1185⟩, ⟨v1186, rejectv1186⟩, ⟨v1187, rejectv1187⟩, ⟨v1188, rejectv1188⟩, ⟨v1189, rejectv1189⟩, ⟨v1190, rejectv1190⟩, ⟨v1191, rejectv1191⟩, ⟨v1192, rejectv1192⟩, ⟨v1193, rejectv1193⟩, ⟨v1194, rejectv1194⟩, ⟨v1195, rejectv1195⟩, ⟨v1196, rejectv1196⟩, ⟨v1197, rejectv1197⟩, ⟨v1198, rejectv1198⟩, ⟨v1199, rejectv1199⟩, ⟨v1200, rejectv1200⟩, ⟨v1201, rejectv1201⟩, ⟨v1219, rejectv1219⟩, ⟨v1220, rejectv1220⟩, ⟨v1221, rejectv1221⟩, ⟨v1222, rejectv1222⟩]
    (by decide +kernel)

private def v1223 : List Sig := [w213, raw5, raw8, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1223 : search 10 0 v1223 = false := by decide +kernel

private def v1224 : List Sig := [w97, raw5, raw8, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1224 : search 10 0 v1224 = false := by decide +kernel

private def v1225 : List Sig := [w134, raw6, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw8]

private def v1226 : List Sig := [w416, raw8, raw6, raw7, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1226 : search 9 0 v1226 = false := by decide +kernel

private def v1227 : List Sig := [w417, raw6, raw7, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1227 : search 9 0 v1227 = false := by decide +kernel

private def v1228 : List Sig := [w417, w134, raw6, raw7, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1228 : search 9 0 v1228 = false := by decide +kernel

private def v1229 : List Sig := [w417, raw8, raw6, raw7, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1229 : search 9 0 v1229 = false := by decide +kernel

private def v1230 : List Sig := [w19, w134, raw6, raw0, raw1, raw2, raw3, raw4, raw5]

private def v1231 : List Sig := [w189, raw0, w134, raw6, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1231 : search 8 0 v1231 = false := by decide +kernel

private def v1232 : List Sig := [w418, w19, raw6, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1232 : search 8 0 v1232 = false := by decide +kernel

private def v1233 : List Sig := [w418, raw0, w19, raw6, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1233 : search 8 0 v1233 = false := by decide +kernel

private def v1234 : List Sig := [w418, w134, w19, raw6, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1234 : search 8 0 v1234 = false := by decide +kernel

private def v1235 : List Sig := [w226, raw1, w134, raw6, raw0, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1235 : search 8 0 v1235 = false := by decide +kernel

private def v1236 : List Sig := [w419, w134, w19, raw6, raw0, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1236 : search 8 0 v1236 = false := by decide +kernel

private def v1237 : List Sig := [w420, w134, w19, raw6, raw0, raw1, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1237 : search 8 0 v1237 = false := by decide +kernel

private def v1238 : List Sig := [w421, w134, w19, raw6, raw0, raw1, raw2, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1238 : search 8 0 v1238 = false := by decide +kernel

private def v1239 : List Sig := [w422, w134, w19, raw6, raw0, raw1, raw2, raw3, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1239 : search 8 0 v1239 = false := by decide +kernel

private def v1240 : List Sig := [w118, raw4, w19, w134, raw0, raw1, raw2, raw3, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1240 : search 8 0 v1240 = false := by decide +kernel

private def v1241 : List Sig := [w409, w19, raw6, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1241 : search 8 0 v1241 = false := by decide +kernel

private def v1242 : List Sig := [w409, raw5, w19, raw6, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1242 : search 8 0 v1242 = false := by decide +kernel

private def v1243 : List Sig := [w409, w134, w19, raw6, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1243 : search 8 0 v1243 = false := by decide +kernel

private def v1244 : List Sig := [w120, raw5, w19, w134, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1244 : search 8 0 v1244 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1230 : search 9 0 v1230 = false := certifiedStep 8 0 v1230
    []
    [⟨v1231, rejectv1231⟩, ⟨v1232, rejectv1232⟩, ⟨v1233, rejectv1233⟩, ⟨v1234, rejectv1234⟩, ⟨v1235, rejectv1235⟩, ⟨v1236, rejectv1236⟩, ⟨v1237, rejectv1237⟩, ⟨v1238, rejectv1238⟩, ⟨v1239, rejectv1239⟩, ⟨v1240, rejectv1240⟩, ⟨v1241, rejectv1241⟩, ⟨v1242, rejectv1242⟩, ⟨v1243, rejectv1243⟩, ⟨v1244, rejectv1244⟩]
    (by decide +kernel)

private def v1245 : List Sig := [w19, raw7, w134, raw6, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1245 : search 9 0 v1245 = false := by decide +kernel

private def v1246 : List Sig := [w19, raw8, w134, raw6, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1246 : search 9 0 v1246 = false := by decide +kernel

private def v1247 : List Sig := [w130, raw0, raw6, raw7, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1247 : search 9 0 v1247 = false := by decide +kernel

private def v1248 : List Sig := [w418, raw6, raw7, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1248 : search 9 0 v1248 = false := by decide +kernel

private def v1249 : List Sig := [w418, raw0, raw6, raw7, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1249 : search 9 0 v1249 = false := by decide +kernel

private def v1250 : List Sig := [w418, w134, raw6, raw7, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1250 : search 9 0 v1250 = false := by decide +kernel

private def v1251 : List Sig := [w121, raw0, w134, raw6, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1251 : search 9 0 v1251 = false := by decide +kernel

private def v1252 : List Sig := [w15, raw0, w134, raw6, raw7, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1252 : search 9 0 v1252 = false := by decide +kernel

private def v1253 : List Sig := [w423, raw1, raw6, raw7, raw0, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1253 : search 9 0 v1253 = false := by decide +kernel

private def v1254 : List Sig := [w419, raw6, raw7, raw0, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1254 : search 9 0 v1254 = false := by decide +kernel

private def v1255 : List Sig := [w419, raw1, raw6, raw7, raw0, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1255 : search 9 0 v1255 = false := by decide +kernel

private def v1256 : List Sig := [w419, w134, raw6, raw7, raw0, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1256 : search 9 0 v1256 = false := by decide +kernel

private def v1257 : List Sig := [w32, raw1, w134, raw6, raw0, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1257 : search 9 0 v1257 = false := by decide +kernel

private def v1258 : List Sig := [w17, raw1, w134, raw6, raw7, raw0, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1258 : search 9 0 v1258 = false := by decide +kernel

private def v1259 : List Sig := [w307, raw2, raw6, raw7, raw0, raw1, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1259 : search 9 0 v1259 = false := by decide +kernel

private def v1260 : List Sig := [w420, raw6, raw7, raw0, raw1, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1260 : search 9 0 v1260 = false := by decide +kernel

private def v1261 : List Sig := [w420, raw2, raw6, raw7, raw0, raw1, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1261 : search 9 0 v1261 = false := by decide +kernel

private def v1262 : List Sig := [w420, w134, raw6, raw7, raw0, raw1, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1262 : search 9 0 v1262 = false := by decide +kernel

private def v1263 : List Sig := [w329, raw3, raw6, raw7, raw0, raw1, raw2, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1263 : search 9 0 v1263 = false := by decide +kernel

private def v1264 : List Sig := [w421, raw6, raw7, raw0, raw1, raw2, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1264 : search 9 0 v1264 = false := by decide +kernel

private def v1265 : List Sig := [w421, raw3, raw6, raw7, raw0, raw1, raw2, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1265 : search 9 0 v1265 = false := by decide +kernel

private def v1266 : List Sig := [w421, w134, raw6, raw7, raw0, raw1, raw2, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1266 : search 9 0 v1266 = false := by decide +kernel

private def v1267 : List Sig := [w424, raw4, raw6, raw7, raw0, raw1, raw2, raw3, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1267 : search 9 0 v1267 = false := by decide +kernel

private def v1268 : List Sig := [w422, raw6, raw7, raw0, raw1, raw2, raw3, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1268 : search 9 0 v1268 = false := by decide +kernel

private def v1269 : List Sig := [w422, raw4, raw6, raw7, raw0, raw1, raw2, raw3, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1269 : search 9 0 v1269 = false := by decide +kernel

private def v1270 : List Sig := [w422, w134, raw6, raw7, raw0, raw1, raw2, raw3, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1270 : search 9 0 v1270 = false := by decide +kernel

private def v1271 : List Sig := [w118, raw4, w134, raw7, raw0, raw1, raw2, raw3, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1271 : search 9 0 v1271 = false := by decide +kernel

private def v1272 : List Sig := [w386, raw5, raw6, raw7, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1272 : search 9 0 v1272 = false := by decide +kernel

private def v1273 : List Sig := [w409, raw6, raw7, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1273 : search 9 0 v1273 = false := by decide +kernel

private def v1274 : List Sig := [w409, raw5, raw6, raw7, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1274 : search 9 0 v1274 = false := by decide +kernel

private def v1275 : List Sig := [w409, w134, raw6, raw7, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1275 : search 9 0 v1275 = false := by decide +kernel

private def v1276 : List Sig := [w120, raw5, w134, raw7, raw0, raw1, raw2, raw3, raw4, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1276 : search 9 0 v1276 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1225 : search 10 0 v1225 = false := certifiedStep 9 0 v1225
    []
    [⟨v1226, rejectv1226⟩, ⟨v1227, rejectv1227⟩, ⟨v1228, rejectv1228⟩, ⟨v1229, rejectv1229⟩, ⟨v1230, rejectv1230⟩, ⟨v1245, rejectv1245⟩, ⟨v1246, rejectv1246⟩, ⟨v1247, rejectv1247⟩, ⟨v1248, rejectv1248⟩, ⟨v1249, rejectv1249⟩, ⟨v1250, rejectv1250⟩, ⟨v1251, rejectv1251⟩, ⟨v1252, rejectv1252⟩, ⟨v1253, rejectv1253⟩, ⟨v1254, rejectv1254⟩, ⟨v1255, rejectv1255⟩, ⟨v1256, rejectv1256⟩, ⟨v1257, rejectv1257⟩, ⟨v1258, rejectv1258⟩, ⟨v1259, rejectv1259⟩, ⟨v1260, rejectv1260⟩, ⟨v1261, rejectv1261⟩, ⟨v1262, rejectv1262⟩, ⟨v1263, rejectv1263⟩, ⟨v1264, rejectv1264⟩, ⟨v1265, rejectv1265⟩, ⟨v1266, rejectv1266⟩, ⟨v1267, rejectv1267⟩, ⟨v1268, rejectv1268⟩, ⟨v1269, rejectv1269⟩, ⟨v1270, rejectv1270⟩, ⟨v1271, rejectv1271⟩, ⟨v1272, rejectv1272⟩, ⟨v1273, rejectv1273⟩, ⟨v1274, rejectv1274⟩, ⟨v1275, rejectv1275⟩, ⟨v1276, rejectv1276⟩]
    (by decide +kernel)

private def v1277 : List Sig := [w110, raw6, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1277 : search 10 0 v1277 = false := by decide +kernel

private def v1278 : List Sig := [w214, raw6, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1278 : search 10 0 v1278 = false := by decide +kernel

private def v1279 : List Sig := [w111, raw6, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1279 : search 10 0 v1279 = false := by decide +kernel

private def v1280 : List Sig := [w215, raw7, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1280 : search 10 0 v1280 = false := by decide +kernel

private def v1281 : List Sig := [w19, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

private def v1282 : List Sig := [w189, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

private def v1283 : List Sig := [w188, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1283 : search 8 0 v1283 = false := by decide +kernel

private def v1284 : List Sig := [w188, w189, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1284 : search 8 0 v1284 = false := by decide +kernel

private def v1285 : List Sig := [w188, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1285 : search 8 0 v1285 = false := by decide +kernel

private def v1286 : List Sig := [w425, raw0, raw7, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1286 : search 8 0 v1286 = false := by decide +kernel

private def v1287 : List Sig := [w425, w189, raw0, raw7, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1287 : search 8 0 v1287 = false := by decide +kernel

private def v1288 : List Sig := [w425, raw1, raw0, raw7, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1288 : search 8 0 v1288 = false := by decide +kernel

private def v1289 : List Sig := [w426, w189, raw0, raw7, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1289 : search 8 0 v1289 = false := by decide +kernel

private def v1290 : List Sig := [w427, w189, raw0, raw7, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1290 : search 8 0 v1290 = false := by decide +kernel

private def v1291 : List Sig := [w428, w189, raw0, raw7, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1291 : search 8 0 v1291 = false := by decide +kernel

private def v1292 : List Sig := [w429, w189, raw0, raw7, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1292 : search 8 0 v1292 = false := by decide +kernel

private def v1293 : List Sig := [w430, w189, raw0, raw7, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1293 : search 8 0 v1293 = false := by decide +kernel

private def v1294 : List Sig := [w0, raw1, w189, raw7, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1294 : search 8 0 v1294 = false := by decide +kernel

private def v1295 : List Sig := [w31, raw2, w189, raw7, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1295 : search 8 0 v1295 = false := by decide +kernel

private def v1296 : List Sig := [w96, raw5, w189, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1296 : search 8 0 v1296 = false := by decide +kernel

private def v1297 : List Sig := [w134, raw6, w189, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1297 : search 8 0 v1297 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1282 : search 9 0 v1282 = false := certifiedStep 8 0 v1282
    []
    [⟨v1283, rejectv1283⟩, ⟨v1284, rejectv1284⟩, ⟨v1285, rejectv1285⟩, ⟨v1286, rejectv1286⟩, ⟨v1287, rejectv1287⟩, ⟨v1288, rejectv1288⟩, ⟨v1289, rejectv1289⟩, ⟨v1290, rejectv1290⟩, ⟨v1291, rejectv1291⟩, ⟨v1292, rejectv1292⟩, ⟨v1293, rejectv1293⟩, ⟨v1294, rejectv1294⟩, ⟨v1295, rejectv1295⟩, ⟨v1296, rejectv1296⟩, ⟨v1297, rejectv1297⟩]
    (by decide +kernel)

private def v1298 : List Sig := [w189, raw0, w19, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1298 : search 9 0 v1298 = false := by decide +kernel

private def v1299 : List Sig := [w136, raw0, w19, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1299 : search 9 0 v1299 = false := by decide +kernel

private def v1300 : List Sig := [w121, raw0, raw7, w19, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1300 : search 9 0 v1300 = false := by decide +kernel

private def v1301 : List Sig := [w109, raw0, w19, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1301 : search 9 0 v1301 = false := by decide +kernel

private def v1302 : List Sig := [w109, raw0, raw7, w19, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1302 : search 9 0 v1302 = false := by decide +kernel

private def v1303 : List Sig := [w0, raw0, raw1, w19, raw7, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1303 : search 9 0 v1303 = false := by decide +kernel

private def v1304 : List Sig := [w20, raw0, raw1, w19, raw7, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1304 : search 9 0 v1304 = false := by decide +kernel

private def v1305 : List Sig := [w37, raw0, raw2, w19, raw7, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1305 : search 9 0 v1305 = false := by decide +kernel

private def v1306 : List Sig := [w31, raw0, raw2, w19, raw7, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1306 : search 9 0 v1306 = false := by decide +kernel

private def v1307 : List Sig := [w57, raw0, raw3, w19, raw7, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1307 : search 9 0 v1307 = false := by decide +kernel

private def v1308 : List Sig := [w49, raw0, raw3, w19, raw7, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1308 : search 9 0 v1308 = false := by decide +kernel

private def v1309 : List Sig := [w73, raw0, raw4, w19, raw7, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1309 : search 9 0 v1309 = false := by decide +kernel

private def v1310 : List Sig := [w66, raw0, raw4, w19, raw7, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1310 : search 9 0 v1310 = false := by decide +kernel

private def v1311 : List Sig := [w87, raw0, raw5, w19, raw7, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1311 : search 9 0 v1311 = false := by decide +kernel

private def v1312 : List Sig := [w88, raw0, raw5, w19, raw7, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1312 : search 9 0 v1312 = false := by decide +kernel

private def v1313 : List Sig := [w104, raw0, raw6, w19, raw7, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1313 : search 9 0 v1313 = false := by decide +kernel

private def v1314 : List Sig := [w95, raw0, raw6, w19, raw7, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1314 : search 9 0 v1314 = false := by decide +kernel

private def v1315 : List Sig := [w431, raw1, w19, raw7, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1315 : search 9 0 v1315 = false := by decide +kernel

private def v1316 : List Sig := [w226, raw1, w19, raw7, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1316 : search 9 0 v1316 = false := by decide +kernel

private def v1317 : List Sig := [w206, raw1, raw7, w19, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1317 : search 9 0 v1317 = false := by decide +kernel

private def v1318 : List Sig := [w32, raw1, raw7, w19, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1318 : search 9 0 v1318 = false := by decide +kernel

private def v1319 : List Sig := [w191, raw1, raw3, w19, raw7, raw0, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1319 : search 9 0 v1319 = false := by decide +kernel

private def v1320 : List Sig := [w16, raw1, raw3, w19, raw7, raw0, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1320 : search 9 0 v1320 = false := by decide +kernel

private def v1321 : List Sig := [w192, raw1, raw5, w19, raw7, raw0, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1321 : search 9 0 v1321 = false := by decide +kernel

private def v1322 : List Sig := [w99, raw1, raw5, w19, raw7, raw0, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1322 : search 9 0 v1322 = false := by decide +kernel

private def v1323 : List Sig := [w193, raw1, raw6, w19, raw7, raw0, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1323 : search 9 0 v1323 = false := by decide +kernel

private def v1324 : List Sig := [w113, raw1, raw6, w19, raw7, raw0, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1324 : search 9 0 v1324 = false := by decide +kernel

private def v1325 : List Sig := [w432, raw2, w19, raw7, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1325 : search 9 0 v1325 = false := by decide +kernel

private def v1326 : List Sig := [w433, raw2, w19, raw7, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1326 : search 9 0 v1326 = false := by decide +kernel

private def v1327 : List Sig := [w161, raw2, raw7, w19, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1327 : search 9 0 v1327 = false := by decide +kernel

private def v1328 : List Sig := [w52, raw2, raw7, w19, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1328 : search 9 0 v1328 = false := by decide +kernel

private def v1329 : List Sig := [w18, raw2, raw1, w19, raw7, raw0, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1329 : search 9 0 v1329 = false := by decide +kernel

private def v1330 : List Sig := [w50, raw2, raw1, w19, raw7, raw0, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1330 : search 9 0 v1330 = false := by decide +kernel

private def v1331 : List Sig := [w51, raw2, raw3, w19, raw7, raw0, raw1, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1331 : search 9 0 v1331 = false := by decide +kernel

private def v1332 : List Sig := [w156, raw2, raw3, w19, raw7, raw0, raw1, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1332 : search 9 0 v1332 = false := by decide +kernel

private def v1333 : List Sig := [w157, raw2, raw5, w19, raw7, raw0, raw1, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1333 : search 9 0 v1333 = false := by decide +kernel

private def v1334 : List Sig := [w158, raw2, raw5, w19, raw7, raw0, raw1, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1334 : search 9 0 v1334 = false := by decide +kernel

private def v1335 : List Sig := [w159, raw2, raw6, w19, raw7, raw0, raw1, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1335 : search 9 0 v1335 = false := by decide +kernel

private def v1336 : List Sig := [w160, raw2, raw6, w19, raw7, raw0, raw1, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1336 : search 9 0 v1336 = false := by decide +kernel

private def v1337 : List Sig := [w434, raw3, w19, raw7, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1337 : search 9 0 v1337 = false := by decide +kernel

private def v1338 : List Sig := [w435, raw3, w19, raw7, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1338 : search 9 0 v1338 = false := by decide +kernel

private def v1339 : List Sig := [w166, raw3, raw7, w19, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1339 : search 9 0 v1339 = false := by decide +kernel

private def v1340 : List Sig := [w67, raw3, raw7, w19, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1340 : search 9 0 v1340 = false := by decide +kernel

private def v1341 : List Sig := [w162, raw3, raw5, w19, raw7, raw0, raw1, raw2, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1341 : search 9 0 v1341 = false := by decide +kernel

private def v1342 : List Sig := [w163, raw3, raw5, w19, raw7, raw0, raw1, raw2, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1342 : search 9 0 v1342 = false := by decide +kernel

private def v1343 : List Sig := [w164, raw3, raw6, w19, raw7, raw0, raw1, raw2, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1343 : search 9 0 v1343 = false := by decide +kernel

private def v1344 : List Sig := [w165, raw3, raw6, w19, raw7, raw0, raw1, raw2, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1344 : search 9 0 v1344 = false := by decide +kernel

private def v1345 : List Sig := [w436, raw4, w19, raw7, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1345 : search 9 0 v1345 = false := by decide +kernel

private def v1346 : List Sig := [w437, raw4, w19, raw7, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1346 : search 9 0 v1346 = false := by decide +kernel

private def v1347 : List Sig := [w175, raw4, raw7, w19, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1347 : search 9 0 v1347 = false := by decide +kernel

private def v1348 : List Sig := [w176, raw4, raw7, w19, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1348 : search 9 0 v1348 = false := by decide +kernel

private def v1349 : List Sig := [w200, raw4, raw1, w19, raw7, raw0, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1349 : search 9 0 v1349 = false := by decide +kernel

private def v1350 : List Sig := [w201, raw4, raw1, w19, raw7, raw0, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1350 : search 9 0 v1350 = false := by decide +kernel

private def v1351 : List Sig := [w169, raw4, raw2, w19, raw7, raw0, raw1, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1351 : search 9 0 v1351 = false := by decide +kernel

private def v1352 : List Sig := [w56, raw4, raw2, w19, raw7, raw0, raw1, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1352 : search 9 0 v1352 = false := by decide +kernel

private def v1353 : List Sig := [w170, raw4, raw3, w19, raw7, raw0, raw1, raw2, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1353 : search 9 0 v1353 = false := by decide +kernel

private def v1354 : List Sig := [w171, raw4, raw3, w19, raw7, raw0, raw1, raw2, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1354 : search 9 0 v1354 = false := by decide +kernel

private def v1355 : List Sig := [w172, raw4, raw5, w19, raw7, raw0, raw1, raw2, raw3, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1355 : search 9 0 v1355 = false := by decide +kernel

private def v1356 : List Sig := [w173, raw4, raw5, w19, raw7, raw0, raw1, raw2, raw3, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1356 : search 9 0 v1356 = false := by decide +kernel

private def v1357 : List Sig := [w174, raw4, raw6, w19, raw7, raw0, raw1, raw2, raw3, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1357 : search 9 0 v1357 = false := by decide +kernel

private def v1358 : List Sig := [w118, raw4, raw6, w19, raw7, raw0, raw1, raw2, raw3, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1358 : search 9 0 v1358 = false := by decide +kernel

private def v1359 : List Sig := [w438, raw5, w19, raw7, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1359 : search 9 0 v1359 = false := by decide +kernel

private def v1360 : List Sig := [w398, raw5, w19, raw7, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1360 : search 9 0 v1360 = false := by decide +kernel

private def v1361 : List Sig := [w178, raw5, raw7, w19, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1361 : search 9 0 v1361 = false := by decide +kernel

private def v1362 : List Sig := [w96, raw5, w19, raw0, raw1, raw2, raw3, raw4, raw6]

private def v1363 : List Sig := [w177, raw6, w96, w19, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1363 : search 8 0 v1363 = false := by decide +kernel

private def v1364 : List Sig := [w92, raw0, raw5, w19, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1364 : search 8 0 v1364 = false := by decide +kernel

private def v1365 : List Sig := [w88, raw0, w96, w19, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1365 : search 8 0 v1365 = false := by decide +kernel

private def v1366 : List Sig := [w163, raw3, w96, w19, raw0, raw1, raw2, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1366 : search 8 0 v1366 = false := by decide +kernel

private def v1367 : List Sig := [w172, raw4, w96, w19, raw0, raw1, raw2, raw3, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1367 : search 8 0 v1367 = false := by decide +kernel

private def v1368 : List Sig := [w400, raw5, w19, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1368 : search 8 0 v1368 = false := by decide +kernel

private def v1369 : List Sig := [w400, raw6, raw5, w19, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1369 : search 8 0 v1369 = false := by decide +kernel

private def v1370 : List Sig := [w400, w96, raw5, w19, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1370 : search 8 0 v1370 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1362 : search 9 0 v1362 = false := certifiedStep 8 0 v1362
    []
    [⟨v1170, rejectv1170⟩, ⟨v1363, rejectv1363⟩, ⟨v1364, rejectv1364⟩, ⟨v1365, rejectv1365⟩, ⟨v1172, rejectv1172⟩, ⟨v1175, rejectv1175⟩, ⟨v1366, rejectv1366⟩, ⟨v1367, rejectv1367⟩, ⟨v1368, rejectv1368⟩, ⟨v1369, rejectv1369⟩, ⟨v1370, rejectv1370⟩]
    (by decide +kernel)

private def v1371 : List Sig := [w96, raw5, raw7, w19, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1371 : search 9 0 v1371 = false := by decide +kernel

private def v1372 : List Sig := [w120, raw5, raw6, w19, raw7, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1372 : search 9 0 v1372 = false := by decide +kernel

private def v1373 : List Sig := [w177, raw5, raw6, w19, raw7, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1373 : search 9 0 v1373 = false := by decide +kernel

private def v1374 : List Sig := [w439, raw6, w19, raw7, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1374 : search 9 0 v1374 = false := by decide +kernel

private def v1375 : List Sig := [w440, raw6, w19, raw7, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1375 : search 9 0 v1375 = false := by decide +kernel

private def v1376 : List Sig := [w134, raw6, w19, raw0, raw1, raw2, raw3, raw4, raw5]

private def v1377 : List Sig := [w418, raw6, w19, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1377 : search 8 0 v1377 = false := by decide +kernel

private def v1378 : List Sig := [w418, raw0, raw6, w19, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1378 : search 8 0 v1378 = false := by decide +kernel

private def v1379 : List Sig := [w418, w134, raw6, w19, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1379 : search 8 0 v1379 = false := by decide +kernel

private def v1380 : List Sig := [w419, w134, raw6, w19, raw0, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1380 : search 8 0 v1380 = false := by decide +kernel

private def v1381 : List Sig := [w420, w134, raw6, w19, raw0, raw1, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1381 : search 8 0 v1381 = false := by decide +kernel

private def v1382 : List Sig := [w421, w134, raw6, w19, raw0, raw1, raw2, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1382 : search 8 0 v1382 = false := by decide +kernel

private def v1383 : List Sig := [w422, w134, raw6, w19, raw0, raw1, raw2, raw3, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1383 : search 8 0 v1383 = false := by decide +kernel

private def v1384 : List Sig := [w118, raw4, w134, w19, raw0, raw1, raw2, raw3, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1384 : search 8 0 v1384 = false := by decide +kernel

private def v1385 : List Sig := [w409, raw6, w19, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1385 : search 8 0 v1385 = false := by decide +kernel

private def v1386 : List Sig := [w409, raw5, raw6, w19, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1386 : search 8 0 v1386 = false := by decide +kernel

private def v1387 : List Sig := [w409, w134, raw6, w19, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1387 : search 8 0 v1387 = false := by decide +kernel

private def v1388 : List Sig := [w120, raw5, w134, w19, raw0, raw1, raw2, raw3, raw4]

set_option maxRecDepth 10000 in
private lemma rejectv1388 : search 8 0 v1388 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1376 : search 9 0 v1376 = false := certifiedStep 8 0 v1376
    []
    [⟨v1377, rejectv1377⟩, ⟨v1378, rejectv1378⟩, ⟨v1379, rejectv1379⟩, ⟨v1231, rejectv1231⟩, ⟨v1380, rejectv1380⟩, ⟨v1235, rejectv1235⟩, ⟨v1381, rejectv1381⟩, ⟨v1382, rejectv1382⟩, ⟨v1383, rejectv1383⟩, ⟨v1384, rejectv1384⟩, ⟨v1385, rejectv1385⟩, ⟨v1386, rejectv1386⟩, ⟨v1387, rejectv1387⟩, ⟨v1388, rejectv1388⟩]
    (by decide +kernel)

private def v1389 : List Sig := [w134, raw6, raw7, w19, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1389 : search 9 0 v1389 = false := by decide +kernel

private def v1390 : List Sig := [w110, raw6, raw7, w19, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1390 : search 9 0 v1390 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1281 : search 10 0 v1281 = false := certifiedStep 9 0 v1281
    []
    [⟨v1282, rejectv1282⟩, ⟨v1298, rejectv1298⟩, ⟨v1299, rejectv1299⟩, ⟨v1300, rejectv1300⟩, ⟨v1301, rejectv1301⟩, ⟨v1302, rejectv1302⟩, ⟨v1303, rejectv1303⟩, ⟨v1304, rejectv1304⟩, ⟨v1305, rejectv1305⟩, ⟨v1306, rejectv1306⟩, ⟨v1307, rejectv1307⟩, ⟨v1308, rejectv1308⟩, ⟨v1309, rejectv1309⟩, ⟨v1310, rejectv1310⟩, ⟨v1311, rejectv1311⟩, ⟨v1312, rejectv1312⟩, ⟨v1313, rejectv1313⟩, ⟨v1314, rejectv1314⟩, ⟨v1315, rejectv1315⟩, ⟨v631, rejectv631⟩, ⟨v1316, rejectv1316⟩, ⟨v1317, rejectv1317⟩, ⟨v1318, rejectv1318⟩, ⟨v1319, rejectv1319⟩, ⟨v1320, rejectv1320⟩, ⟨v1321, rejectv1321⟩, ⟨v1322, rejectv1322⟩, ⟨v1323, rejectv1323⟩, ⟨v1324, rejectv1324⟩, ⟨v1325, rejectv1325⟩, ⟨v1326, rejectv1326⟩, ⟨v1327, rejectv1327⟩, ⟨v1328, rejectv1328⟩, ⟨v1329, rejectv1329⟩, ⟨v1330, rejectv1330⟩, ⟨v1331, rejectv1331⟩, ⟨v1332, rejectv1332⟩, ⟨v1333, rejectv1333⟩, ⟨v1334, rejectv1334⟩, ⟨v1335, rejectv1335⟩, ⟨v1336, rejectv1336⟩, ⟨v1337, rejectv1337⟩, ⟨v1338, rejectv1338⟩, ⟨v1339, rejectv1339⟩, ⟨v1340, rejectv1340⟩, ⟨v1341, rejectv1341⟩, ⟨v1342, rejectv1342⟩, ⟨v1343, rejectv1343⟩, ⟨v1344, rejectv1344⟩, ⟨v1345, rejectv1345⟩, ⟨v1346, rejectv1346⟩, ⟨v1347, rejectv1347⟩, ⟨v1348, rejectv1348⟩, ⟨v1349, rejectv1349⟩, ⟨v1350, rejectv1350⟩, ⟨v1351, rejectv1351⟩, ⟨v1352, rejectv1352⟩, ⟨v1353, rejectv1353⟩, ⟨v1354, rejectv1354⟩, ⟨v1355, rejectv1355⟩, ⟨v1356, rejectv1356⟩, ⟨v1357, rejectv1357⟩, ⟨v1358, rejectv1358⟩, ⟨v1359, rejectv1359⟩, ⟨v1360, rejectv1360⟩, ⟨v1361, rejectv1361⟩, ⟨v1362, rejectv1362⟩, ⟨v1371, rejectv1371⟩, ⟨v1372, rejectv1372⟩, ⟨v1373, rejectv1373⟩, ⟨v1374, rejectv1374⟩, ⟨v1375, rejectv1375⟩, ⟨v1376, rejectv1376⟩, ⟨v1389, rejectv1389⟩, ⟨v1390, rejectv1390⟩]
    (by decide +kernel)

private def v1391 : List Sig := [w19, raw7, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

private def v1392 : List Sig := [w215, raw7, w19, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1392 : search 9 0 v1392 = false := by decide +kernel

private def v1393 : List Sig := [w189, raw0, raw7, raw8, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1393 : search 9 0 v1393 = false := by decide +kernel

private def v1394 : List Sig := [w136, raw0, raw7, raw8, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1394 : search 9 0 v1394 = false := by decide +kernel

private def v1395 : List Sig := [w109, raw0, w19, raw8, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1395 : search 9 0 v1395 = false := by decide +kernel

private def v1396 : List Sig := [w15, raw0, w19, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1396 : search 9 0 v1396 = false := by decide +kernel

private def v1397 : List Sig := [w207, raw0, w19, raw7, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1397 : search 9 0 v1397 = false := by decide +kernel

private def v1398 : List Sig := [w431, raw1, raw7, raw8, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1398 : search 9 0 v1398 = false := by decide +kernel

private def v1399 : List Sig := [w226, raw1, raw7, raw8, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1399 : search 9 0 v1399 = false := by decide +kernel

private def v1400 : List Sig := [w208, raw1, w19, raw7, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1400 : search 9 0 v1400 = false := by decide +kernel

private def v1401 : List Sig := [w17, raw1, w19, raw7, raw0, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1401 : search 9 0 v1401 = false := by decide +kernel

private def v1402 : List Sig := [w432, raw2, raw7, raw8, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1402 : search 9 0 v1402 = false := by decide +kernel

private def v1403 : List Sig := [w433, raw2, raw7, raw8, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1403 : search 9 0 v1403 = false := by decide +kernel

private def v1404 : List Sig := [w209, raw2, w19, raw7, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1404 : search 9 0 v1404 = false := by decide +kernel

private def v1405 : List Sig := [w53, raw2, w19, raw7, raw0, raw1, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1405 : search 9 0 v1405 = false := by decide +kernel

private def v1406 : List Sig := [w434, raw3, raw7, raw8, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1406 : search 9 0 v1406 = false := by decide +kernel

private def v1407 : List Sig := [w435, raw3, raw7, raw8, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1407 : search 9 0 v1407 = false := by decide +kernel

private def v1408 : List Sig := [w210, raw3, w19, raw7, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1408 : search 9 0 v1408 = false := by decide +kernel

private def v1409 : List Sig := [w68, raw3, w19, raw7, raw0, raw1, raw2, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1409 : search 9 0 v1409 = false := by decide +kernel

private def v1410 : List Sig := [w436, raw4, raw7, raw8, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1410 : search 9 0 v1410 = false := by decide +kernel

private def v1411 : List Sig := [w437, raw4, raw7, raw8, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1411 : search 9 0 v1411 = false := by decide +kernel

private def v1412 : List Sig := [w211, raw4, w19, raw7, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1412 : search 9 0 v1412 = false := by decide +kernel

private def v1413 : List Sig := [w212, raw4, w19, raw7, raw0, raw1, raw2, raw3, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1413 : search 9 0 v1413 = false := by decide +kernel

private def v1414 : List Sig := [w438, raw5, raw7, raw8, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1414 : search 9 0 v1414 = false := by decide +kernel

private def v1415 : List Sig := [w398, raw5, raw7, raw8, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1415 : search 9 0 v1415 = false := by decide +kernel

private def v1416 : List Sig := [w96, raw5, w19, raw8, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1416 : search 9 0 v1416 = false := by decide +kernel

private def v1417 : List Sig := [w213, raw5, w19, raw7, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1417 : search 9 0 v1417 = false := by decide +kernel

private def v1418 : List Sig := [w97, raw5, w19, raw7, raw0, raw1, raw2, raw3, raw4, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1418 : search 9 0 v1418 = false := by decide +kernel

private def v1419 : List Sig := [w439, raw6, raw7, raw8, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1419 : search 9 0 v1419 = false := by decide +kernel

private def v1420 : List Sig := [w440, raw6, raw7, raw8, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1420 : search 9 0 v1420 = false := by decide +kernel

private def v1421 : List Sig := [w134, raw6, w19, raw8, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1421 : search 9 0 v1421 = false := by decide +kernel

private def v1422 : List Sig := [w214, raw6, w19, raw7, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1422 : search 9 0 v1422 = false := by decide +kernel

private def v1423 : List Sig := [w111, raw6, w19, raw7, raw0, raw1, raw2, raw3, raw4, raw5]

set_option maxRecDepth 10000 in
private lemma rejectv1423 : search 9 0 v1423 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1391 : search 10 0 v1391 = false := certifiedStep 9 0 v1391
    []
    [⟨v1392, rejectv1392⟩, ⟨v1393, rejectv1393⟩, ⟨v1394, rejectv1394⟩, ⟨v1395, rejectv1395⟩, ⟨v1396, rejectv1396⟩, ⟨v1397, rejectv1397⟩, ⟨v1398, rejectv1398⟩, ⟨v1399, rejectv1399⟩, ⟨v1400, rejectv1400⟩, ⟨v1401, rejectv1401⟩, ⟨v1402, rejectv1402⟩, ⟨v1403, rejectv1403⟩, ⟨v1404, rejectv1404⟩, ⟨v1405, rejectv1405⟩, ⟨v1406, rejectv1406⟩, ⟨v1407, rejectv1407⟩, ⟨v1408, rejectv1408⟩, ⟨v1409, rejectv1409⟩, ⟨v1410, rejectv1410⟩, ⟨v1411, rejectv1411⟩, ⟨v1412, rejectv1412⟩, ⟨v1413, rejectv1413⟩, ⟨v1414, rejectv1414⟩, ⟨v1415, rejectv1415⟩, ⟨v1416, rejectv1416⟩, ⟨v1417, rejectv1417⟩, ⟨v1418, rejectv1418⟩, ⟨v1419, rejectv1419⟩, ⟨v1420, rejectv1420⟩, ⟨v1421, rejectv1421⟩, ⟨v1422, rejectv1422⟩, ⟨v1423, rejectv1423⟩]
    (by decide +kernel)

set_option maxRecDepth 10000 in
private lemma reject4_11_0 : search 11 0 raw = false := certifiedStep 10 0 raw
    []
    [⟨v4, rejectv4⟩, ⟨v38, rejectv38⟩, ⟨v62, rejectv62⟩, ⟨v63, rejectv63⟩, ⟨v92, rejectv92⟩, ⟨v93, rejectv93⟩, ⟨v118, rejectv118⟩, ⟨v140, rejectv140⟩, ⟨v141, rejectv141⟩, ⟨v142, rejectv142⟩, ⟨v167, rejectv167⟩, ⟨v168, rejectv168⟩, ⟨v197, rejectv197⟩, ⟨v231, rejectv231⟩, ⟨v255, rejectv255⟩, ⟨v497, rejectv497⟩, ⟨v541, rejectv541⟩, ⟨v542, rejectv542⟩, ⟨v543, rejectv543⟩, ⟨v601, rejectv601⟩, ⟨v625, rejectv625⟩, ⟨v626, rejectv626⟩, ⟨v627, rejectv627⟩, ⟨v628, rejectv628⟩, ⟨v629, rejectv629⟩, ⟨v666, rejectv666⟩, ⟨v667, rejectv667⟩, ⟨v783, rejectv783⟩, ⟨v816, rejectv816⟩, ⟨v866, rejectv866⟩, ⟨v867, rejectv867⟩, ⟨v903, rejectv903⟩, ⟨v904, rejectv904⟩, ⟨v905, rejectv905⟩, ⟨v906, rejectv906⟩, ⟨v926, rejectv926⟩, ⟨v927, rejectv927⟩, ⟨v928, rejectv928⟩, ⟨v929, rejectv929⟩, ⟨v930, rejectv930⟩, ⟨v931, rejectv931⟩, ⟨v932, rejectv932⟩, ⟨v960, rejectv960⟩, ⟨v961, rejectv961⟩, ⟨v962, rejectv962⟩, ⟨v986, rejectv986⟩, ⟨v987, rejectv987⟩, ⟨v988, rejectv988⟩, ⟨v989, rejectv989⟩, ⟨v990, rejectv990⟩, ⟨v991, rejectv991⟩, ⟨v992, rejectv992⟩, ⟨v1020, rejectv1020⟩, ⟨v1056, rejectv1056⟩, ⟨v1057, rejectv1057⟩, ⟨v1093, rejectv1093⟩, ⟨v1094, rejectv1094⟩, ⟨v1095, rejectv1095⟩, ⟨v1123, rejectv1123⟩, ⟨v1124, rejectv1124⟩, ⟨v1125, rejectv1125⟩, ⟨v1126, rejectv1126⟩, ⟨v1127, rejectv1127⟩, ⟨v1163, rejectv1163⟩, ⟨v1164, rejectv1164⟩, ⟨v1165, rejectv1165⟩, ⟨v1223, rejectv1223⟩, ⟨v1224, rejectv1224⟩, ⟨v1225, rejectv1225⟩, ⟨v1277, rejectv1277⟩, ⟨v1278, rejectv1278⟩, ⟨v1279, rejectv1279⟩, ⟨v1280, rejectv1280⟩, ⟨v1281, rejectv1281⟩, ⟨v1391, rejectv1391⟩]
    (by decide +kernel)

private def v1424 : List Sig := [w441, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1424 : search 10 0 v1424 = false := by decide +kernel

private def v1425 : List Sig := [w0, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1425 : search 10 1 v1425 = false := by decide +kernel

private def v1426 : List Sig := [w20, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1426 : search 10 1 v1426 = false := by decide +kernel

private def v1427 : List Sig := [w37, raw0, raw2, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1427 : search 10 1 v1427 = false := by decide +kernel

private def v1428 : List Sig := [w31, raw0, raw2, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1428 : search 10 1 v1428 = false := by decide +kernel

private def v1429 : List Sig := [w57, raw0, raw3, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1429 : search 10 1 v1429 = false := by decide +kernel

private def v1430 : List Sig := [w49, raw0, raw3, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1430 : search 10 1 v1430 = false := by decide +kernel

private def v1431 : List Sig := [w73, raw0, raw4, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1431 : search 10 1 v1431 = false := by decide +kernel

private def v1432 : List Sig := [w66, raw0, raw4, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1432 : search 10 1 v1432 = false := by decide +kernel

private def v1433 : List Sig := [w87, raw0, raw5, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1433 : search 10 1 v1433 = false := by decide +kernel

private def v1434 : List Sig := [w88, raw0, raw5, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1434 : search 10 1 v1434 = false := by decide +kernel

private def v1435 : List Sig := [w104, raw0, raw6, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1435 : search 10 1 v1435 = false := by decide +kernel

private def v1436 : List Sig := [w95, raw0, raw6, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1436 : search 10 1 v1436 = false := by decide +kernel

private def v1437 : List Sig := [w121, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1437 : search 10 1 v1437 = false := by decide +kernel

private def v1438 : List Sig := [w109, raw0, raw7, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1438 : search 10 1 v1438 = false := by decide +kernel

private def v1439 : List Sig := [w15, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

private def v1440 : List Sig := [w442, w15, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1440 : search 9 0 v1440 = false := by decide +kernel

private def v1441 : List Sig := [w144, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1441 : search 9 1 v1441 = false := by decide +kernel

private def v1442 : List Sig := [w144, w15, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1442 : search 9 1 v1442 = false := by decide +kernel

private def v1443 : List Sig := [w144, raw1, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1443 : search 9 1 v1443 = false := by decide +kernel

private def v1444 : List Sig := [w180, w15, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1444 : search 9 1 v1444 = false := by decide +kernel

private def v1445 : List Sig := [w182, w15, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1445 : search 9 1 v1445 = false := by decide +kernel

private def v1446 : List Sig := [w183, w15, raw0, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1446 : search 9 1 v1446 = false := by decide +kernel

private def v1447 : List Sig := [w185, w15, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1447 : search 9 1 v1447 = false := by decide +kernel

private def v1448 : List Sig := [w187, w15, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1448 : search 9 1 v1448 = false := by decide +kernel

private def v1449 : List Sig := [w188, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1449 : search 9 1 v1449 = false := by decide +kernel

private def v1450 : List Sig := [w188, w15, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1450 : search 9 1 v1450 = false := by decide +kernel

private def v1451 : List Sig := [w188, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1451 : search 9 1 v1451 = false := by decide +kernel

private def v1452 : List Sig := [w441, raw0, w15, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1452 : search 9 0 v1452 = false := by decide +kernel

private def v1453 : List Sig := [w443, raw1, w15, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1453 : search 9 0 v1453 = false := by decide +kernel

private def v1454 : List Sig := [w444, raw2, w15, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1454 : search 9 0 v1454 = false := by decide +kernel

private def v1455 : List Sig := [w445, raw3, w15, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1455 : search 9 0 v1455 = false := by decide +kernel

private def v1456 : List Sig := [w446, raw4, w15, raw0, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1456 : search 9 0 v1456 = false := by decide +kernel

private def v1457 : List Sig := [w447, raw5, w15, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1457 : search 9 0 v1457 = false := by decide +kernel

private def v1458 : List Sig := [w448, raw6, w15, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1458 : search 9 0 v1458 = false := by decide +kernel

private def v1459 : List Sig := [w449, raw7, w15, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1459 : search 9 0 v1459 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1439 : search 10 1 v1439 = false := certifiedStep 9 1 v1439
    [⟨v1440, rejectv1440⟩, ⟨v1452, rejectv1452⟩, ⟨v1453, rejectv1453⟩, ⟨v1454, rejectv1454⟩, ⟨v1455, rejectv1455⟩, ⟨v1456, rejectv1456⟩, ⟨v1457, rejectv1457⟩, ⟨v1458, rejectv1458⟩, ⟨v1459, rejectv1459⟩]
    [⟨v1441, rejectv1441⟩, ⟨v1442, rejectv1442⟩, ⟨v1443, rejectv1443⟩, ⟨v1444, rejectv1444⟩, ⟨v1445, rejectv1445⟩, ⟨v1446, rejectv1446⟩, ⟨v1447, rejectv1447⟩, ⟨v1448, rejectv1448⟩, ⟨v1449, rejectv1449⟩, ⟨v1450, rejectv1450⟩, ⟨v1451, rejectv1451⟩]
    (by decide +kernel)

private def v1460 : List Sig := [w15, raw0, raw8, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1460 : search 10 1 v1460 = false := by decide +kernel

private def v1461 : List Sig := [w207, raw0, raw8, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1461 : search 10 1 v1461 = false := by decide +kernel

private def v1462 : List Sig := [w443, raw1, raw0, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1462 : search 10 0 v1462 = false := by decide +kernel

private def v1463 : List Sig := [w191, raw1, raw3, raw0, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1463 : search 10 1 v1463 = false := by decide +kernel

private def v1464 : List Sig := [w16, raw1, raw3, raw0, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1464 : search 10 1 v1464 = false := by decide +kernel

private def v1465 : List Sig := [w192, raw1, raw5, raw0, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1465 : search 10 1 v1465 = false := by decide +kernel

private def v1466 : List Sig := [w99, raw1, raw5, raw0, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1466 : search 10 1 v1466 = false := by decide +kernel

private def v1467 : List Sig := [w193, raw1, raw6, raw0, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1467 : search 10 1 v1467 = false := by decide +kernel

private def v1468 : List Sig := [w113, raw1, raw6, raw0, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1468 : search 10 1 v1468 = false := by decide +kernel

private def v1469 : List Sig := [w206, raw1, raw7, raw0, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1469 : search 10 1 v1469 = false := by decide +kernel

private def v1470 : List Sig := [w32, raw1, raw7, raw0, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1470 : search 10 1 v1470 = false := by decide +kernel

private def v1471 : List Sig := [w208, raw1, raw8, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1471 : search 10 1 v1471 = false := by decide +kernel

private def v1472 : List Sig := [w17, raw1, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1472 : search 10 1 v1472 = false := by decide +kernel

private def v1473 : List Sig := [w17, raw1, raw8, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1473 : search 10 1 v1473 = false := by decide +kernel

private def v1474 : List Sig := [w444, raw2, raw0, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1474 : search 10 0 v1474 = false := by decide +kernel

private def v1475 : List Sig := [w18, raw2, raw1, raw0, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1475 : search 10 1 v1475 = false := by decide +kernel

private def v1476 : List Sig := [w50, raw2, raw1, raw0, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1476 : search 10 1 v1476 = false := by decide +kernel

private def v1477 : List Sig := [w51, raw2, raw3, raw0, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1477 : search 10 1 v1477 = false := by decide +kernel

private def v1478 : List Sig := [w156, raw2, raw3, raw0, raw1, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1478 : search 10 1 v1478 = false := by decide +kernel

private def v1479 : List Sig := [w157, raw2, raw5, raw0, raw1, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1479 : search 10 1 v1479 = false := by decide +kernel

private def v1480 : List Sig := [w158, raw2, raw5, raw0, raw1, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1480 : search 10 1 v1480 = false := by decide +kernel

private def v1481 : List Sig := [w159, raw2, raw6, raw0, raw1, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1481 : search 10 1 v1481 = false := by decide +kernel

private def v1482 : List Sig := [w160, raw2, raw6, raw0, raw1, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1482 : search 10 1 v1482 = false := by decide +kernel

private def v1483 : List Sig := [w161, raw2, raw7, raw0, raw1, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1483 : search 10 1 v1483 = false := by decide +kernel

private def v1484 : List Sig := [w52, raw2, raw7, raw0, raw1, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1484 : search 10 1 v1484 = false := by decide +kernel

private def v1485 : List Sig := [w209, raw2, raw8, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1485 : search 10 1 v1485 = false := by decide +kernel

private def v1486 : List Sig := [w53, raw2, raw8, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1486 : search 10 1 v1486 = false := by decide +kernel

private def v1487 : List Sig := [w445, raw3, raw0, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1487 : search 10 0 v1487 = false := by decide +kernel

private def v1488 : List Sig := [w162, raw3, raw5, raw0, raw1, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1488 : search 10 1 v1488 = false := by decide +kernel

private def v1489 : List Sig := [w163, raw3, raw5, raw0, raw1, raw2, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1489 : search 10 1 v1489 = false := by decide +kernel

private def v1490 : List Sig := [w164, raw3, raw6, raw0, raw1, raw2, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1490 : search 10 1 v1490 = false := by decide +kernel

private def v1491 : List Sig := [w165, raw3, raw6, raw0, raw1, raw2, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1491 : search 10 1 v1491 = false := by decide +kernel

private def v1492 : List Sig := [w166, raw3, raw7, raw0, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1492 : search 10 1 v1492 = false := by decide +kernel

private def v1493 : List Sig := [w67, raw3, raw7, raw0, raw1, raw2, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1493 : search 10 1 v1493 = false := by decide +kernel

private def v1494 : List Sig := [w210, raw3, raw8, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1494 : search 10 1 v1494 = false := by decide +kernel

private def v1495 : List Sig := [w68, raw3, raw8, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1495 : search 10 1 v1495 = false := by decide +kernel

private def v1496 : List Sig := [w446, raw4, raw0, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1496 : search 10 0 v1496 = false := by decide +kernel

private def v1497 : List Sig := [w200, raw4, raw1, raw0, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1497 : search 10 1 v1497 = false := by decide +kernel

private def v1498 : List Sig := [w201, raw4, raw1, raw0, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1498 : search 10 1 v1498 = false := by decide +kernel

private def v1499 : List Sig := [w169, raw4, raw2, raw0, raw1, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1499 : search 10 1 v1499 = false := by decide +kernel

private def v1500 : List Sig := [w56, raw4, raw2, raw0, raw1, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1500 : search 10 1 v1500 = false := by decide +kernel

private def v1501 : List Sig := [w170, raw4, raw3, raw0, raw1, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1501 : search 10 1 v1501 = false := by decide +kernel

private def v1502 : List Sig := [w171, raw4, raw3, raw0, raw1, raw2, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1502 : search 10 1 v1502 = false := by decide +kernel

private def v1503 : List Sig := [w172, raw4, raw5, raw0, raw1, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1503 : search 10 1 v1503 = false := by decide +kernel

private def v1504 : List Sig := [w173, raw4, raw5, raw0, raw1, raw2, raw3, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1504 : search 10 1 v1504 = false := by decide +kernel

private def v1505 : List Sig := [w174, raw4, raw6, raw0, raw1, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1505 : search 10 1 v1505 = false := by decide +kernel

private def v1506 : List Sig := [w118, raw4, raw6, raw0, raw1, raw2, raw3, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1506 : search 10 1 v1506 = false := by decide +kernel

private def v1507 : List Sig := [w175, raw4, raw7, raw0, raw1, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1507 : search 10 1 v1507 = false := by decide +kernel

private def v1508 : List Sig := [w176, raw4, raw7, raw0, raw1, raw2, raw3, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1508 : search 10 1 v1508 = false := by decide +kernel

private def v1509 : List Sig := [w211, raw4, raw8, raw0, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1509 : search 10 1 v1509 = false := by decide +kernel

private def v1510 : List Sig := [w212, raw4, raw8, raw0, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1510 : search 10 1 v1510 = false := by decide +kernel

private def v1511 : List Sig := [w447, raw5, raw0, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1511 : search 10 0 v1511 = false := by decide +kernel

private def v1512 : List Sig := [w120, raw5, raw6, raw0, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1512 : search 10 1 v1512 = false := by decide +kernel

private def v1513 : List Sig := [w177, raw5, raw6, raw0, raw1, raw2, raw3, raw4, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1513 : search 10 1 v1513 = false := by decide +kernel

private def v1514 : List Sig := [w178, raw5, raw7, raw0, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1514 : search 10 1 v1514 = false := by decide +kernel

private def v1515 : List Sig := [w96, raw5, raw7, raw0, raw1, raw2, raw3, raw4, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1515 : search 10 1 v1515 = false := by decide +kernel

private def v1516 : List Sig := [w213, raw5, raw8, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1516 : search 10 1 v1516 = false := by decide +kernel

private def v1517 : List Sig := [w97, raw5, raw8, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1517 : search 10 1 v1517 = false := by decide +kernel

private def v1518 : List Sig := [w448, raw6, raw0, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1518 : search 10 0 v1518 = false := by decide +kernel

private def v1519 : List Sig := [w134, raw6, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1519 : search 10 1 v1519 = false := by decide +kernel

private def v1520 : List Sig := [w110, raw6, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1520 : search 10 1 v1520 = false := by decide +kernel

private def v1521 : List Sig := [w214, raw6, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1521 : search 10 1 v1521 = false := by decide +kernel

private def v1522 : List Sig := [w111, raw6, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1522 : search 10 1 v1522 = false := by decide +kernel

private def v1523 : List Sig := [w449, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1523 : search 10 0 v1523 = false := by decide +kernel

private def v1524 : List Sig := [w215, raw7, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1524 : search 10 1 v1524 = false := by decide +kernel

private def v1525 : List Sig := [w19, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1525 : search 10 1 v1525 = false := by decide +kernel

private def v1526 : List Sig := [w19, raw7, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1526 : search 10 1 v1526 = false := by decide +kernel

private def v1527 : List Sig := [w450, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1527 : search 10 0 v1527 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma reject1424_11_1 : search 11 1 raw = false := certifiedStep 10 1 raw
    [⟨v1424, rejectv1424⟩, ⟨v1462, rejectv1462⟩, ⟨v1474, rejectv1474⟩, ⟨v1487, rejectv1487⟩, ⟨v1496, rejectv1496⟩, ⟨v1511, rejectv1511⟩, ⟨v1518, rejectv1518⟩, ⟨v1523, rejectv1523⟩, ⟨v1527, rejectv1527⟩]
    [⟨v1425, rejectv1425⟩, ⟨v1426, rejectv1426⟩, ⟨v1427, rejectv1427⟩, ⟨v1428, rejectv1428⟩, ⟨v1429, rejectv1429⟩, ⟨v1430, rejectv1430⟩, ⟨v1431, rejectv1431⟩, ⟨v1432, rejectv1432⟩, ⟨v1433, rejectv1433⟩, ⟨v1434, rejectv1434⟩, ⟨v1435, rejectv1435⟩, ⟨v1436, rejectv1436⟩, ⟨v1437, rejectv1437⟩, ⟨v1438, rejectv1438⟩, ⟨v1439, rejectv1439⟩, ⟨v1460, rejectv1460⟩, ⟨v1461, rejectv1461⟩, ⟨v1463, rejectv1463⟩, ⟨v1464, rejectv1464⟩, ⟨v1465, rejectv1465⟩, ⟨v1466, rejectv1466⟩, ⟨v1467, rejectv1467⟩, ⟨v1468, rejectv1468⟩, ⟨v1469, rejectv1469⟩, ⟨v1470, rejectv1470⟩, ⟨v1471, rejectv1471⟩, ⟨v1472, rejectv1472⟩, ⟨v1473, rejectv1473⟩, ⟨v1475, rejectv1475⟩, ⟨v1476, rejectv1476⟩, ⟨v1477, rejectv1477⟩, ⟨v1478, rejectv1478⟩, ⟨v1479, rejectv1479⟩, ⟨v1480, rejectv1480⟩, ⟨v1481, rejectv1481⟩, ⟨v1482, rejectv1482⟩, ⟨v1483, rejectv1483⟩, ⟨v1484, rejectv1484⟩, ⟨v1485, rejectv1485⟩, ⟨v1486, rejectv1486⟩, ⟨v1488, rejectv1488⟩, ⟨v1489, rejectv1489⟩, ⟨v1490, rejectv1490⟩, ⟨v1491, rejectv1491⟩, ⟨v1492, rejectv1492⟩, ⟨v1493, rejectv1493⟩, ⟨v1494, rejectv1494⟩, ⟨v1495, rejectv1495⟩, ⟨v1497, rejectv1497⟩, ⟨v1498, rejectv1498⟩, ⟨v1499, rejectv1499⟩, ⟨v1500, rejectv1500⟩, ⟨v1501, rejectv1501⟩, ⟨v1502, rejectv1502⟩, ⟨v1503, rejectv1503⟩, ⟨v1504, rejectv1504⟩, ⟨v1505, rejectv1505⟩, ⟨v1506, rejectv1506⟩, ⟨v1507, rejectv1507⟩, ⟨v1508, rejectv1508⟩, ⟨v1509, rejectv1509⟩, ⟨v1510, rejectv1510⟩, ⟨v1512, rejectv1512⟩, ⟨v1513, rejectv1513⟩, ⟨v1514, rejectv1514⟩, ⟨v1515, rejectv1515⟩, ⟨v1516, rejectv1516⟩, ⟨v1517, rejectv1517⟩, ⟨v1519, rejectv1519⟩, ⟨v1520, rejectv1520⟩, ⟨v1521, rejectv1521⟩, ⟨v1522, rejectv1522⟩, ⟨v1524, rejectv1524⟩, ⟨v1525, rejectv1525⟩, ⟨v1526, rejectv1526⟩]
    (by decide +kernel)

private def v1528 : List Sig := [w441, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1528 : search 10 1 v1528 = false := by decide +kernel

private def v1529 : List Sig := [w441, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1529 : search 10 1 v1529 = false := by decide +kernel

private def v1530 : List Sig := [w15, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

private def v1531 : List Sig := [w442, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1531 : search 9 1 v1531 = false := by decide +kernel

private def v1532 : List Sig := [w144, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1532 : search 9 2 v1532 = false := by decide +kernel

private def v1533 : List Sig := [w188, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1533 : search 9 2 v1533 = false := by decide +kernel

private def v1534 : List Sig := [w441, w15, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1534 : search 9 1 v1534 = false := by decide +kernel

private def v1535 : List Sig := [w443, w15, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1535 : search 9 1 v1535 = false := by decide +kernel

private def v1536 : List Sig := [w444, w15, raw0, raw1, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1536 : search 9 1 v1536 = false := by decide +kernel

private def v1537 : List Sig := [w445, w15, raw0, raw1, raw2, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1537 : search 9 1 v1537 = false := by decide +kernel

private def v1538 : List Sig := [w446, w15, raw0, raw1, raw2, raw3, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1538 : search 9 1 v1538 = false := by decide +kernel

private def v1539 : List Sig := [w447, w15, raw0, raw1, raw2, raw3, raw4, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1539 : search 9 1 v1539 = false := by decide +kernel

private def v1540 : List Sig := [w448, w15, raw0, raw1, raw2, raw3, raw4, raw5, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1540 : search 9 1 v1540 = false := by decide +kernel

private def v1541 : List Sig := [w449, w15, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1541 : search 9 1 v1541 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma rejectv1530 : search 10 2 v1530 = false := certifiedStep 9 2 v1530
    [⟨v1531, rejectv1531⟩, ⟨v1534, rejectv1534⟩, ⟨v1535, rejectv1535⟩, ⟨v1536, rejectv1536⟩, ⟨v1537, rejectv1537⟩, ⟨v1538, rejectv1538⟩, ⟨v1539, rejectv1539⟩, ⟨v1540, rejectv1540⟩, ⟨v1541, rejectv1541⟩]
    [⟨v1532, rejectv1532⟩, ⟨v1533, rejectv1533⟩]
    (by decide +kernel)

private def v1542 : List Sig := [w443, raw0, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1542 : search 10 1 v1542 = false := by decide +kernel

private def v1543 : List Sig := [w443, raw1, raw0, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1543 : search 10 1 v1543 = false := by decide +kernel

private def v1544 : List Sig := [w17, raw1, raw0, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1544 : search 10 2 v1544 = false := by decide +kernel

private def v1545 : List Sig := [w444, raw0, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1545 : search 10 1 v1545 = false := by decide +kernel

private def v1546 : List Sig := [w444, raw2, raw0, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1546 : search 10 1 v1546 = false := by decide +kernel

private def v1547 : List Sig := [w445, raw0, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1547 : search 10 1 v1547 = false := by decide +kernel

private def v1548 : List Sig := [w445, raw3, raw0, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1548 : search 10 1 v1548 = false := by decide +kernel

private def v1549 : List Sig := [w446, raw0, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1549 : search 10 1 v1549 = false := by decide +kernel

private def v1550 : List Sig := [w446, raw4, raw0, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1550 : search 10 1 v1550 = false := by decide +kernel

private def v1551 : List Sig := [w447, raw0, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1551 : search 10 1 v1551 = false := by decide +kernel

private def v1552 : List Sig := [w447, raw5, raw0, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1552 : search 10 1 v1552 = false := by decide +kernel

private def v1553 : List Sig := [w448, raw0, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1553 : search 10 1 v1553 = false := by decide +kernel

private def v1554 : List Sig := [w448, raw6, raw0, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1554 : search 10 1 v1554 = false := by decide +kernel

private def v1555 : List Sig := [w449, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1555 : search 10 1 v1555 = false := by decide +kernel

private def v1556 : List Sig := [w449, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1556 : search 10 1 v1556 = false := by decide +kernel

private def v1557 : List Sig := [w19, raw7, raw0, raw1, raw2, raw3, raw4, raw5, raw6]

set_option maxRecDepth 10000 in
private lemma rejectv1557 : search 10 2 v1557 = false := by decide +kernel

private def v1558 : List Sig := [w450, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1558 : search 10 1 v1558 = false := by decide +kernel

private def v1559 : List Sig := [w450, raw8, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1559 : search 10 1 v1559 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma reject1528_11_2 : search 11 2 raw = false := certifiedStep 10 2 raw
    [⟨v1528, rejectv1528⟩, ⟨v1529, rejectv1529⟩, ⟨v1542, rejectv1542⟩, ⟨v1543, rejectv1543⟩, ⟨v1545, rejectv1545⟩, ⟨v1546, rejectv1546⟩, ⟨v1547, rejectv1547⟩, ⟨v1548, rejectv1548⟩, ⟨v1549, rejectv1549⟩, ⟨v1550, rejectv1550⟩, ⟨v1551, rejectv1551⟩, ⟨v1552, rejectv1552⟩, ⟨v1553, rejectv1553⟩, ⟨v1554, rejectv1554⟩, ⟨v1555, rejectv1555⟩, ⟨v1556, rejectv1556⟩, ⟨v1558, rejectv1558⟩, ⟨v1559, rejectv1559⟩]
    [⟨v1530, rejectv1530⟩, ⟨v1544, rejectv1544⟩, ⟨v1557, rejectv1557⟩]
    (by decide +kernel)

private def v1560 : List Sig := [w441, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1560 : search 10 2 v1560 = false := by decide +kernel

private def v1561 : List Sig := [w443, raw0, raw2, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1561 : search 10 2 v1561 = false := by decide +kernel

private def v1562 : List Sig := [w444, raw0, raw1, raw3, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1562 : search 10 2 v1562 = false := by decide +kernel

private def v1563 : List Sig := [w445, raw0, raw1, raw2, raw4, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1563 : search 10 2 v1563 = false := by decide +kernel

private def v1564 : List Sig := [w446, raw0, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1564 : search 10 2 v1564 = false := by decide +kernel

private def v1565 : List Sig := [w447, raw0, raw1, raw2, raw3, raw4, raw6, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1565 : search 10 2 v1565 = false := by decide +kernel

private def v1566 : List Sig := [w448, raw0, raw1, raw2, raw3, raw4, raw5, raw7, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1566 : search 10 2 v1566 = false := by decide +kernel

private def v1567 : List Sig := [w449, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw8]

set_option maxRecDepth 10000 in
private lemma rejectv1567 : search 10 2 v1567 = false := by decide +kernel

private def v1568 : List Sig := [w450, raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7]

set_option maxRecDepth 10000 in
private lemma rejectv1568 : search 10 2 v1568 = false := by decide +kernel

set_option maxRecDepth 10000 in
private lemma reject1560_11_3 : search 11 3 raw = false := certifiedStep 10 3 raw
    [⟨v1560, rejectv1560⟩, ⟨v1561, rejectv1561⟩, ⟨v1562, rejectv1562⟩, ⟨v1563, rejectv1563⟩, ⟨v1564, rejectv1564⟩, ⟨v1565, rejectv1565⟩, ⟨v1566, rejectv1566⟩, ⟨v1567, rejectv1567⟩, ⟨v1568, rejectv1568⟩]
    []
    (by decide +kernel)

end PEqualNP.Outside.G525

open PEqualNP.Outside.G525

theorem PEqualNP.Outside.L_meta_525 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 0 && x 7) || (x 0 && x 8)) s → 12 ≤ s := by
  intro s hs
  by_contra h
  obtain ⟨C,hg,hc,he⟩ := hs
  obtain ⟨t,ht,found⟩ := circuit_search C (by omega) hg he
  interval_cases t <;> simp_all only [reject4_11_0, reject1424_11_1, reject1528_11_2, reject1560_11_3, Bool.false_eq_true]
