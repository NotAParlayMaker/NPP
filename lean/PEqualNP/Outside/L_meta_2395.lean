import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2395

abbrev V := Fin 13

abbrev inc (dual : Bool) (p l : V) : Prop :=
  if dual then l=p ∨ l=p+1 ∨ l=p+3 ∨ l=p+9 else p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9

abbrev cap (d : Bool) (a : Finset V) : Prop :=
  ∀ l, (a.filter (fun p => inc d p l)).card  ≤  2

def ext (d : Bool) (a : Finset V) : Finset V :=
  Finset.univ.filter fun l => ∀ p ∈ a, ¬inc d p l

def blocked (d : Bool) (a : Finset V) : Finset V :=
  a ∪ Finset.univ.filter (fun p => ¬cap d (insert p a))

set_option maxRecDepth 10000 in
theorem lineSize : ∀ (d : Bool) (l : V), (Finset.univ.filter (fun p => inc d p l)).card = 4 := by decide +kernel

set_option maxRecDepth 10000 in
theorem uniqueJoin : ∀ (d : Bool) (p q : V), p ≠ q → ∃ l, inc d p l ∧ inc d q l ∧
    ∀ k, inc d p k → inc d q k → k=l := by intro d; cases d <;> decide +kernel

theorem shortCap (d : Bool) (a : Finset V) (h : a.card  ≤  2) : cap d a := by
  intro k; exact (Finset.card_le_card (Finset.filter_subset _ _)).trans h

theorem smallBlocked (d : Bool) (k : Fin 3) (a : Finset V)
    (mem : a ∈ (Finset.univ : Finset V).powersetCard k.val) : (blocked d a).card  ≤  4 := by
  have card := (Finset.mem_powersetCard.mp mem).2
  by_cases small : a.card  ≤  1
  · have eq : blocked d a = a := by
      apply Finset.Subset.antisymm _ (Finset.subset_union_left)
      intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · exact h
      · have valid := shortCap d (insert p a) ((Finset.card_insert_le _ _).trans (by omega))
        exact False.elim ((Finset.mem_filter.mp h).2 valid)
    rw [eq]; omega
  obtain ⟨p,q,ne,rfl⟩ := Finset.card_eq_two.mp (show a.card=2 by omega)
  obtain ⟨l,pa,qa,uniq⟩ := uniqueJoin d p q ne
  let on := Finset.univ.filter (fun r => inc d r l)
  have sub : blocked d {p,q} ⊆ on := by
    intro r hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hr with h|h
    · simp only [Finset.mem_insert,Finset.mem_singleton] at h; rcases h with rfl|rfl <;> assumption
    · by_contra out
      apply (Finset.mem_filter.mp h).2
      intro w
      by_cases rp : inc d r w <;> by_cases pp : inc d p w <;> by_cases qp : inc d q w
      all_goals first | exact False.elim (out ((uniq _ pp qp) ▸ rp)) |
        (simp [Finset.filter_insert,Finset.filter_singleton,rp,pp,qp] <;> first | exact Finset.card_le_two | omega)
  exact (Finset.card_le_card sub).trans (le_of_eq (lineSize d l))

theorem swap_inc (d : Bool) (p l : V) : inc (!d) l p ↔ inc d p l := by cases d <;> rfl

theorem reverse {d : Bool} {a b : Finset V} (compatible : b ⊆ ext d a) :
    a ⊆ ext (!d) b := by
  intro p hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro l hl h
  exact (Finset.mem_filter.mp (compatible hl)).2 p hp ((swap_inc d p l).mp h)

theorem grow {d : Bool} {a b : Finset V} (small : a.card < 3) (other : b.card  ≤  2)
    (compatible : b ⊆ ext d a) : ∃ p ∉ a, cap d (insert p a) ∧ b ⊆ ext d (insert p a) := by
  let on := fun l => Finset.univ.filter (fun p => inc d p l)
  have lim : (b.biUnion on).card  ≤  8 := calc
    _  ≤  ∑ l ∈ b, (on l).card := Finset.card_biUnion_le
    _ = b.card * 4 := by simp [on,lineSize]
    _  ≤  8 := by omega
  have blockedSize := smallBlocked d ⟨a.card,small⟩ a
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ a,rfl⟩)
  have bound := Finset.card_union_le (blocked d a) (b.biUnion on)
  have short : ((blocked d a) ∪ b.biUnion on).card < (Finset.univ : Finset V).card := by
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  obtain ⟨p,_,available⟩ := Finset.exists_mem_notMem_of_card_lt_card short
  have ok : p ∉ blocked d a := fun h => available (Finset.mem_union_left _ h)
  have away : p ∉ b.biUnion on := fun h => available (Finset.mem_union_right _ h)
  refine ⟨p,fun h => ok (Finset.mem_union_left _ h),?_,?_⟩
  · by_contra bad
    exact ok (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bad⟩))
  · intro l hl
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    intro q hq h
    rcases Finset.mem_insert.mp hq with rfl|hq
    · exact away (Finset.mem_biUnion.mpr ⟨l,hl,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩)
    · exact (Finset.mem_filter.mp (compatible hl)).2 q hq h

theorem toThree {d : Bool} {a b : Finset V} (small : a.card  ≤  3) (other : b.card  ≤  2)
    (ca : cap d a) (ab : b ⊆ ext d a) :
    ∃ t : Finset V, t.card=3 ∧ cap d t ∧ a ⊆ t ∧ b ⊆ ext d t := by
  by_cases done : a.card=3
  · exact ⟨a,done,ca,Finset.Subset.rfl,ab⟩
  obtain ⟨p,hp,cap',ext'⟩ := grow (by omega) other ab
  have more := Finset.card_insert_of_notMem hp
  obtain ⟨t,sz,ct,sub,last⟩ := toThree (a := insert p a) (b := b) (by omega) other cap' ext'
  exact ⟨t,sz,ct,(Finset.subset_insert _ _).trans sub,last⟩
termination_by 3-a.card



abbrev Triple := V × V × V × V
def triples (d : Bool) : List Triple :=
  if d then [(0,0,4,10),(0,0,4,12),(0,0,10,12),(0,4,10,12),(1,0,1,5),(1,0,1,11),(1,0,5,11),(1,1,5,11),(2,1,2,6),(2,1,2,12),(2,1,6,12),(2,2,6,12),(3,0,2,3),(3,0,2,7),(3,0,3,7),(3,2,3,7),(4,1,3,4),(4,1,3,8),(4,1,4,8),(4,3,4,8),(5,2,4,5),(5,2,4,9),(5,2,5,9),(5,4,5,9),(6,3,5,6),(6,3,5,10),(6,3,6,10),(6,5,6,10),(7,4,6,7),(7,4,6,11),(7,4,7,11),(7,6,7,11),(8,5,7,8),(8,5,7,12),(8,5,8,12),(8,7,8,12),(9,0,6,8),(9,0,6,9),(9,0,8,9),(9,6,8,9),(10,1,7,9),(10,1,7,10),(10,1,9,10),(10,7,9,10),(11,2,8,10),(11,2,8,11),(11,2,10,11),(11,8,10,11),(12,3,9,11),(12,3,9,12),(12,3,11,12),(12,9,11,12)]
  else [(0,0,1,3),(0,0,1,9),(0,0,3,9),(0,1,3,9),(1,1,2,4),(1,1,2,10),(1,1,4,10),(1,2,4,10),(2,2,3,5),(2,2,3,11),(2,2,5,11),(2,3,5,11),(3,3,4,6),(3,3,4,12),(3,3,6,12),(3,4,6,12),(4,0,4,5),(4,0,4,7),(4,0,5,7),(4,4,5,7),(5,1,5,6),(5,1,5,8),(5,1,6,8),(5,5,6,8),(6,2,6,7),(6,2,6,9),(6,2,7,9),(6,6,7,9),(7,3,7,8),(7,3,7,10),(7,3,8,10),(7,7,8,10),(8,4,8,9),(8,4,8,11),(8,4,9,11),(8,8,9,11),(9,5,9,10),(9,5,9,12),(9,5,10,12),(9,9,10,12),(10,0,6,10),(10,0,6,11),(10,0,10,11),(10,6,10,11),(11,1,7,11),(11,1,7,12),(11,1,11,12),(11,7,11,12),(12,0,2,8),(12,0,2,12),(12,0,8,12),(12,2,8,12)]
def validTriple (d : Bool) (t : Triple) :=
  t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧ t.2.2.1 ≠ t.2.2.2 ∧
  inc d t.2.1 t.1 ∧ inc d t.2.2.1 t.1 ∧ inc d t.2.2.2 t.1
theorem tripleData : ∀ d : Bool, ∀ t ∈ triples d, validTriple d t := by
  unfold validTriple; decide +kernel

def bad (d : Bool) (a : List V) := (triples d).any fun t =>
  decide (t.2.1∈a ∧ t.2.2.1∈a ∧ t.2.2.2∈a)
def offLines (d : Bool) (a : List V) :=
  (List.finRange 13).filter fun l => decide (¬inc d 0 l ∧ ∀ q ∈ a, ¬inc d q l)
def ruled (d : Bool) : ℕ → List V → Bool
  | 0,a => bad d a
  | k+1,a =>
    if bad d a then true else
    match (offLines d a).head? with
    | none => false
    | some l => (List.finRange 13).all fun q => !decide (inc d q l) || ruled d k (q::a)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem checkedCover : ∀ d : Bool, ruled d 5 [] = true := by decide +kernel

theorem shift (d : Bool) (p i l : V) : inc d (p+i) (p+l) ↔ inc d i l := by
  cases d <;> simp [inc,add_assoc]

theorem noBad (d : Bool) (p : V) (s : Finset V) (ok : cap d s) (a : List V)
    (sub : ∀ i ∈ a, p+i ∈ s) : bad d a = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  obtain ⟨t,ht,held⟩ := List.any_eq_true.mp yes
  obtain ⟨i,j,k⟩ := of_decide_eq_true held
  obtain ⟨ij,ik,jk,il,jl,kl⟩ := tripleData d t ht
  let group : Finset V := {p+t.2.1,p+t.2.2.1,p+t.2.2.2}
  have included : group ⊆ s.filter (fun q => inc d q (p+t.1)) := by
    intro x hx
    simp only [group,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · exact Finset.mem_filter.mpr ⟨sub _ i,(shift _ _ _ _).mpr il⟩
    · exact Finset.mem_filter.mpr ⟨sub _ j,(shift _ _ _ _).mpr jl⟩
    · exact Finset.mem_filter.mpr ⟨sub _ k,(shift _ _ _ _).mpr kl⟩
  have size : group.card=3 := by simp [group,ij,ik,jk]
  have bound := (Finset.card_le_card included).trans (ok (p+t.1))
  omega

theorem coverSound (d : Bool) (p : V) (s : Finset V) (ok : cap d s)
    (hits : ∀ l : V, ¬inc d p l → ∃ q ∈ s, inc d q l) (k : ℕ) :
    ∀ a : List V, (∀ i ∈ a,p+i∈s) → ruled d k a = false := by
  induction k with
  | zero => exact fun a sub => noBad d p s ok a sub
  | succ k ih =>
    intro a sub
    simp only [ruled,noBad d p s ok a sub,Bool.false_eq_true,ite_false]
    cases e : (offLines d a).head? with
    | none => rfl
    | some l =>
      have mem := List.mem_of_mem_head? (show l ∈ (offLines d a).head? by simp [e])
      have lo := of_decide_eq_true (List.mem_filter.mp mem).2
      have out : ¬inc d p (p+l) := by simpa using mt (shift d p 0 l).mp lo.1
      obtain ⟨q,hq,hits⟩ := hits (p+l) out
      have restore : p+(q-p)=q := by abel
      have near : inc d (q-p) l := (shift _ _ _ _).mp (restore ▸ hits)
      have fail := ih ((q-p)::a) (by intro i hi; rcases List.mem_cons.mp hi with rfl|h; simpa only [restore] using hq; exact sub i h)
      apply Bool.eq_false_iff.mpr
      intro good
      have h := List.all_eq_true.mp good (q-p) (by simp)
      simp [near,fail] at h

theorem missing (d : Bool) (s : Finset V) (ok : cap d s) (p : V) :
    ∃ l ∈ ext d s, ¬inc d p l := by
  classical
  by_contra! impossible
  have hits (l : V) (out : ¬inc d p l) : ∃ q ∈ s, inc d q l := by
    by_contra! all
    exact out (impossible l (Finset.mem_filter.mpr ⟨Finset.mem_univ _,all⟩))
  have bad := coverSound d p s ok hits 5 [] (by simp)
  rw [checkedCover] at bad
  contradiction

theorem noLine (s : Finset V) (d : Bool) (ok : cap d s) (many : 3 ≤ s.card) :
    ¬∃ l, ∀ p ∈ s, inc d p l := by
  rintro ⟨l,all⟩
  have lim := ok l
  rw [Finset.filter_eq_self.mpr all] at lim
  omega

abbrev generic (u : Finset V) :=
  (∀ p ∉ u, ∃ l : V, (∀ q ∈ u, ¬inc false q l) ∧ inc false p l) ∧
  (¬∃ l : V, ∀ p ∈ u, inc false p l) ∧
  ¬∃ p : V, ∀ l : V, (∀ q ∈ u, ¬inc false q l) → inc false p l

theorem anti (d : Bool) {s t : Finset V} (sub : s⊆t) : ext d t ⊆ ext d s := by
  intro l hl
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun q hq => (Finset.mem_filter.mp hl).2 q (sub hq)⟩

theorem closure (d : Bool) (s : Finset V) : ext d (ext (!d) (ext d s)) = ext d s := by
  apply Finset.Subset.antisymm
  · exact anti d (reverse (d:=d) (b:=ext d s) Finset.Subset.rfl)
  · simpa only [Bool.not_not] using reverse (d:=!d) (b:=ext (!d) (ext d s)) Finset.Subset.rfl

set_option maxHeartbeats 1200000 in
theorem finish (a b : Finset V) (away : b⊆ext false a)
    (pt : ¬∃ l, ∀ p ∈ a, inc false p l)
    (ln : ¬∃ p, ∀ l ∈ ext false a, inc false p l) :
    ∃ u : Finset V, a⊆u ∧ b⊆ext false u ∧ generic u := by
  let u := ext true (ext false a)
  have au : a ⊆ u := reverse (d:=false) (a:=a) (b:=ext false a) Finset.Subset.rfl
  have clos : ext false u = ext false a := closure false a
  have bu : b ⊆ ext false u := by rw [clos];exact away
  have original (l : V) (hl : l ∈ ext false a) : ∀ q ∈ u, ¬inc false q l := by
    have h : l ∈ ext false u := by rw [clos]; exact hl
    exact (Finset.mem_filter.mp h).2
  refine ⟨u,au,bu,?_,?_,?_⟩
  · intro p out
    by_contra! all
    apply out
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun l hl => all l (original l hl)⟩
  · rintro ⟨l,all⟩; exact pt ⟨l,fun p hp => all p (au hp)⟩
  · rintro ⟨p,all⟩
    exact ln ⟨p,fun l hl => all l (original l hl)⟩

set_option maxHeartbeats 1200000 in
theorem completion (a b : Finset V) (ca : cap false a) (cb : cap true b) (away : b ⊆ ext false a) :
    ∃ u : Finset V, a⊆u ∧ b⊆ext false u ∧ generic u := by
  have primal (s : Finset V) (ok : cap false s) (many : 3 ≤ s.card) (hs : a⊆s) (hb : b⊆ext false s) :
      ∃ u : Finset V, a⊆u ∧ b⊆ext false u ∧ generic u := by
    obtain ⟨u,su,last⟩ := finish s b hb (noLine s false ok many) (by
      rintro ⟨p,all⟩; obtain ⟨l,hl,no⟩ := missing false s ok p; exact no (all l hl))
    exact ⟨u,hs.trans su,last⟩
  by_cases big : 3 ≤ a.card
  · exact primal a ca big Finset.Subset.rfl away
  by_cases dualBig : 3 ≤ b.card
  · let s := ext true b
    have inside : a ⊆ s := reverse (d:=false) (a:=a) (b:=b) away
    have extB : b ⊆ ext false s := reverse (d:=true) (a:=b) (b:=ext true b) Finset.Subset.rfl
    obtain ⟨u,hu,hb,gu⟩ := finish s b extB (by
      rintro ⟨l,all⟩; obtain ⟨p,hp,no⟩ := missing true b cb l; exact no (all p hp)) (by
      rintro ⟨p,all⟩; exact noLine b true cb dualBig ⟨p,fun l hl => all l (extB hl)⟩)
    exact ⟨u,inside.trans hu,hb,gu⟩
  obtain ⟨s,sz,ok,ha,hb⟩ := toThree (d:=false) (a:=a) (b:=b) (by omega) (by omega) ca away
  exact primal s ok (by omega) ha hb

end PEqualNP.Outside.L_meta_2395

open PEqualNP.Outside.L_meta_2395 in
theorem PEqualNP.Outside.L_meta_2395 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, ¬x1 x4 x6) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x2 | x1 x6 x5}.card  ≤  (2 : ℕ)) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x1 x6 x7}.card  ≤  (2 : ℕ)) → ∃ (x7 : Finset (Fin (13 : ℕ))), x2 ⊆ x7 ∧ (∀ x8 ∈ x3, ∀ x10 ∈ x7, ¬x1 x10 x8) ∧ (∀ x8 ∉ x7, ∃ (x10 : Fin (13 : ℕ)), (∀ x11 ∈ x7, ¬x1 x11 x10) ∧ x1 x8 x10) ∧ (¬∃ (x8 : Fin (13 : ℕ)), ∀ x9 ∈ x7, x1 x9 x8) ∧ ¬∃ (x8 : Fin (13 : ℕ)), ∀ (x9 : Fin (13 : ℕ)), (∀ x10 ∈ x7, ¬x1 x10 x9) → x1 x8 x9 := by
  dsimp only
  intro a b away ca cb
  have compatible : b⊆ext false a := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp => away p hp l hl⟩
  obtain ⟨u,hu,hb,maximal,noncollinear,nonconcurrent⟩ := completion a b ca cb compatible
  exact ⟨u,hu,fun l hl => (Finset.mem_filter.mp (hb hl)).2,maximal,noncollinear,nonconcurrent⟩
