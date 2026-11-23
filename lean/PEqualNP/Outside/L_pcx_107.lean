import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.SplitIfs

namespace PEqualNP.Outside.L_pcx_107
namespace CoverTree
abbrev State (n : ℕ) := Fin n → Option Bool

def Conflict {n} (A : Fin n → Fin n → Prop) (r : State n) :=
  ∃ u v, A u v ∧ r u=some false ∧ r v=some false
def trueSet {n} (r : State n) := Finset.univ.filter (fun u => r u=some true)
def Forced {n} (A : Fin n → Fin n → Prop) (r : State n) :=
  ∃ u v, A u v ∧ r u=some false ∧ r v=none
def Done {n} (A : Fin n → Fin n → Prop) (t : ℕ) (r : State n) :=
  Conflict A r ∨ t≤(trueSet r).card
def Legal {n} (A : Fin n → Fin n → Prop) (t : ℕ) (N : State n → ℕ) :=
  ∀ r, (Done A t r ∧ 1 ≤ N r) ∨ ∃ y, r y=none ∧
    N (Function.update r y (some false))+N (Function.update r y (some true)) ≤ N r
def Tree (n : ℕ) (A : Fin n → Fin n → Prop) (t k : ℕ) :=
  ∃ N : State n → ℕ, N (fun _ => none)≤k ∧ Legal A t N

theorem enough_true {n t} (r : State n) : t≤(trueSet r).card ↔
    ∃ S : Finset (Fin n), S.card=t ∧ ∀ x∈S, r x=some true := by
  constructor
  · intro h
    obtain ⟨S,sub,size⟩ := Finset.exists_subset_card_eq h
    exact ⟨S,size,fun x hx => (Finset.mem_filter.mp (sub hx)).2⟩
  · rintro ⟨S,h,all⟩
    rw [←h]
    exact Finset.card_le_card (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _,all x hx⟩)

theorem tree_iff (n : ℕ) (A : Fin n → Fin n → Prop) (t k : ℕ) : Tree n A t k ↔
    ∃ N : State n → ℕ, N (fun _ => none)≤k ∧ ∀ r : State n,
      (((∃ u v, A u v ∧ r u=some false ∧ r v=some false) ∨
        ∃ S : Finset (Fin n), S.card=t ∧ ∀ x∈S, r x=some true) ∧ 1≤N r) ∨
      ∃ y, r y=none ∧ N (Function.update r y (some false))+N (Function.update r y (some true)) ≤ N r := by
  simp only [Tree,Legal,Done,Conflict,enough_true]

theorem true_update {n} (r : State n) (v : Fin n) (h : r v=none) :
    trueSet (Function.update r v (some true)) = insert v (trueSet r) ∧
    trueSet (Function.update r v (some false)) = trueSet r := by
  constructor <;> ext x <;> by_cases e : x=v <;> simp [trueSet,Function.update,e,h]

noncomputable def cost {n} (A : Fin n → Fin n → Prop) (t : ℕ) (r : State n) : ℕ := by
  classical
  exact if Done A t r then 1 else if Forced A r then 2^(t-(trueSet r).card) else 2^(t-(trueSet r).card+1)-1

theorem cost_le {n} (A : Fin n → Fin n → Prop) (t : ℕ) (r : State n) :
    cost A t r ≤ 2^(t-(trueSet r).card+1)-1 := by
  classical
  have pos := Nat.two_pow_pos (t-(trueSet r).card)
  unfold cost
  rw [pow_succ]
  split
  · omega
  · split <;> omega

theorem cost_legal {n t} (G : SimpleGraph (Fin n))
    (minimum : ∀ R : Finset (Fin n), (∀ u v, G.Adj u v → u∈R ∨ v∈R) → t ≤ R.card) :
    Legal G.Adj t (cost G.Adj t) := by
  classical
  intro r
  by_cases finished : Done G.Adj t r
  · exact Or.inl ⟨finished,by simp [cost,finished]⟩
  have lt : (trueSet r).card<t := Nat.lt_of_not_ge fun h => finished (Or.inr h)
  have progress (v) (unknown : r v=none) :
      cost G.Adj t (Function.update r v (some true)) ≤ 2^(t-(trueSet r).card)-1 := by
    have hi := cost_le G.Adj t (Function.update r v (some true))
    have notmem : v∉trueSet r := by simp [trueSet,unknown]
    rw [(true_update r v unknown).1,Finset.card_insert_of_notMem notmem,show t-((trueSet r).card+1)+1=t-(trueSet r).card by omega] at hi
    exact hi
  by_cases force : Forced G.Adj r
  · obtain ⟨u,v,edge,fu,empty⟩ := force
    have ne := G.ne_of_adj edge
    have bad : Done G.Adj t (Function.update r v (some false)) := Or.inl
      ⟨u,v,edge,by simp [Function.update_of_ne ne,fu],by simp⟩
    refine Or.inr ⟨v,empty,?_⟩
    have step := progress v empty
    have pos := Nat.two_pow_pos (t-(trueSet r).card)
    have forced : Forced G.Adj r := ⟨u,v,edge,fu,empty⟩
    simpa only [cost,ite_eq_left bad,ite_eq_right finished,ite_eq_left forced] using
      (by omega : 1+cost G.Adj t (Function.update r v (some true)) ≤ 2^(t-(trueSet r).card))
  · obtain ⟨u,v,edge,hu,hv⟩ : ∃ u v, G.Adj u v ∧ u∉trueSet r ∧ v∉trueSet r := by
      by_contra! h
      exact (Nat.not_le_of_lt lt) (minimum _ (fun u v e => or_iff_not_imp_left.mpr (h u v e)))
    have undef (a b : Fin n) (adj : G.Adj a b) (na : a∉trueSet r) (nb : b∉trueSet r) : r a=none := by
      cases ea : r a with
      | none => rfl
      | some x =>
        cases x with
        | true => exact False.elim (na (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ea⟩))
        | false =>
          cases eb : r b with
          | none => exact False.elim (force ⟨a,b,adj,ea,eb⟩)
          | some y =>
            cases y with
            | true => exact False.elim (nb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eb⟩))
            | false => exact False.elim (finished (Or.inl ⟨a,b,adj,ea,eb⟩))
    have unknown := undef u v edge hu hv
    have other := undef v u edge.symm hv hu
    have forces : Forced G.Adj (Function.update r u (some false)) :=
      ⟨u,v,edge,by simp,by simpa [Function.update_of_ne (G.ne_of_adj edge).symm] using other⟩
    have step := progress u unknown
    have falseCost : cost G.Adj t (Function.update r u (some false)) ≤ 2^(t-(trueSet r).card) := by
      unfold cost
      rw [ite_eq_left forces,(true_update r u unknown).2]
      split
      · exact Nat.two_pow_pos _
      · rfl
    refine Or.inr ⟨u,unknown,?_⟩
    have here : cost G.Adj t r = 2^(t-(trueSet r).card+1)-1 := by simp [cost,finished,force]
    rw [here,pow_succ]
    have pos := Nat.two_pow_pos (t-(trueSet r).card)
    omega


theorem all_graphs_upper {n t} (G : SimpleGraph (Fin n))
    (minimum : ∀ R : Finset (Fin n), (∀ u v, G.Adj u v → u∈R ∨ v∈R) → t ≤ R.card) :
    Tree n G.Adj t (2^(t+1)-1) := by
  refine ⟨cost G.Adj t,?_,cost_legal G minimum⟩
  simpa [trueSet] using cost_le G.Adj t (fun _ => none)

end CoverTree

namespace MatchingState
open CoverTree

def adr {k} (i : Fin k) (b : Bool) : Fin (2*k) := ⟨2*i.val+b.toNat,by cases b <;> simp <;> omega⟩
def index {k} (v : Fin (2*k)) : Fin k := ⟨v.val/2,by omega⟩
def side {k} (v : Fin (2*k)) := decide (v.val % 2=1)

@[local simp] theorem idxAdr {k} (i : Fin k) (b) : index (adr i b)=i := by
  apply Fin.ext
  cases b <;> simp [index,adr] <;> omega
@[local simp] theorem sideAdr {k} (i : Fin k) (b) : side (adr i b)=b := by cases b <;> simp [side,adr]
@[local simp] theorem adrIdx {k} (v : Fin (2*k)) : adr (index v) (side v)=v := by
  apply Fin.ext
  by_cases e : v.val % 2=1 <;> simp [adr,side,index,e] <;> omega
@[local simp] theorem adr_eq {k} (i j : Fin k) (a b) : adr i a=adr j b ↔ i=j ∧ a=b := by
  constructor
  · intro e; exact ⟨by simpa using congrArg index e,by simpa using congrArg side e⟩
  · rintro ⟨rfl,rfl⟩;rfl

def free {k} (r : State (2*k)) := Finset.univ.filter (fun i : Fin k => ∀ b, r (adr i b)=none)
def unresolved {k} (r : State (2*k)) := Finset.univ.filter (fun i : Fin k => ∀ b, r (adr i b) ≠ some true)
def clean {k} (r : State (2*k)) := ∀ (i : Fin k) (b t : Bool), ¬(r (adr i b)=some t ∧ r (adr i (!b))=some t)
def relation (k) (u v : Fin (2*k)) := u≠v ∧ u.val/2=v.val/2

theorem preserve {k} (r : State (2*k)) (c : clean r) (i : Fin k) (b t : Bool)
    (other : r (adr i (!b)) ≠ some t) : clean (Function.update r (adr i b) (some t)) := by
  intro j a x
  by_cases e : j=i
  · subst j
    cases a <;> cases b <;> cases t <;> cases x <;> simp_all [Function.update]
  · simpa [Function.update,e] using c j a x

theorem update_free {k} (r : State (2*k)) (i : Fin k) (b t : Bool) :
    free (Function.update r (adr i b) (some t)) = (free r).erase i := by
  ext j
  by_cases e : j=i
  · subst j; cases b <;> simp [free,Function.update]
  · simp [free,Function.update,e]

theorem update_yes {k} (r : State (2*k)) (i : Fin k) (b : Bool) :
    unresolved (Function.update r (adr i b) (some true)) = (unresolved r).erase i := by
  ext j
  by_cases e : j=i
  · subst j; cases b <;> simp [unresolved,Function.update]
  · simp [unresolved,Function.update,e]

theorem update_no {k} (r : State (2*k)) (i : Fin k) (b : Bool) (h : r (adr i b)=none) :
    unresolved (Function.update r (adr i b) (some false)) = unresolved r := by
  ext j
  by_cases e : j=i
  · subst j; cases b <;> simp [unresolved,Function.update] at h ⊢ <;> simp [h]
  · simp [unresolved,Function.update,e]

theorem sub {k} (r : State (2*k)) : free r ⊆ unresolved r := by
  intro i hi
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,fun b => by simp [(Finset.mem_filter.mp hi).2 b]⟩

theorem no_conflict {k} (r : State (2*k)) (c : clean r) : ¬Conflict (relation k) r := by
  rintro ⟨u,v,⟨diff,eq⟩,hu,hv⟩
  have ix : index u=index v := Fin.ext eq
  have opp : side v = !side u := by
    have neq : side u≠side v := fun e => diff (by rw [←adrIdx u,←adrIdx v,ix,e])
    cases a : side u <;> cases b : side v <;> simp_all
  apply c (index u) (side u) false
  exact ⟨by simpa using hu,by simpa only [ix,←opp,adrIdx] using hv⟩

theorem count_resolved {k} (r : State (2*k)) (c : clean r) :
    (trueSet r).card + (unresolved r).card = k := by
  classical
  have inj : Set.InjOn index (↑(trueSet r) : Set (Fin (2*k))) := by
    intro u hu v hv e
    by_cases eq : side u=side v
    · rw [←adrIdx u,←adrIdx v,e,eq]
    · exfalso
      have opp : side v = !side u := by cases a : side u <;> cases b : side v <;> simp_all
      apply c (index u) (side u) true
      exact ⟨by simpa using (Finset.mem_filter.mp hu).2,
        by simpa only [e,←opp,adrIdx] using (Finset.mem_filter.mp hv).2⟩
  have image_eq : (trueSet r).image index = (unresolved r)ᶜ := by
    ext i
    constructor
    · intro hi
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
      apply Finset.mem_compl.mpr
      intro h
      have bad := (Finset.mem_filter.mp h).2 (side v)
      exact bad (by simpa using (Finset.mem_filter.mp hv).2)
    · intro hi
      have h : ¬ ∀ b, r (adr i b)≠some true := by simpa [unresolved] using hi
      push Not at h
      obtain ⟨b,h⟩ := h
      exact Finset.mem_image.mpr ⟨adr i b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,idxAdr _ _⟩
  rw [← Finset.card_image_of_injOn inj,image_eq,Finset.card_compl]
  have h := Finset.card_le_univ (unresolved r)
  simp only [Fintype.card_fin] at *
  omega

open CoverTree

private theorem other_side (s b : Bool) (h : s≠b) : s = !b := by cases s <;> cases b <;> simp_all

def unasked {n} (r : State n) := Finset.univ.filter (fun i => r i=none)

theorem fewer {n} (r : State n) (y : Fin n) (empty : r y=none) (v : Bool) :
    (unasked (Function.update r y (some v))).card < (unasked r).card := by
  have eq : unasked (Function.update r y (some v))=(unasked r).erase y := by
    ext z; by_cases h : z=y <;> simp [unasked,Function.update,h]
  rw [eq]
  exact Finset.card_erase_lt_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,empty⟩)

theorem positive {n t} {A : Fin n → Fin n → Prop} (N : State n → ℕ) (cert : Legal A t N) (r : State n) :
    1 ≤ N r := by
  induction h : (unasked r).card using Nat.strong_induction_on generalizing r with
  | ind d ih =>
    rcases cert r with done|⟨v,hv,step⟩
    · exact done.2
    · have b := ih _ (h ▸ fewer r v hv false) _ rfl
      omega

def value {k} (r : State (2*k)) := (2^((free r).card+1)-1) + ((unresolved r).card-(free r).card)

theorem bound {k} (N : State (2*k) → ℕ) (cert : Legal (relation k) k N) (r : State (2*k))
    (valid : clean r) : value r ≤ N r := by
  classical
  induction h : (unasked r).card using Nat.strong_induction_on generalizing r with
  | ind d ih =>
    rcases cert r with ⟨done,pos⟩|⟨v,unknown,split⟩
    · have cover := done.resolve_left (no_conflict r valid)
      have counts := count_resolved r valid
      have subset := Finset.card_le_card (sub r)
      have z : (unresolved r).card=0 := by omega
      have zz : (free r).card=0 := by omega
      simpa [value,z,zz] using pos
    · let i := index v
      let b := side v
      have eq : adr i b=v := adrIdx v
      rw [←eq] at unknown split
      let no := Function.update r (adr i b) (some false)
      let yes := Function.update r (adr i b) (some true)
      change N no + N yes ≤ N r at split
      have recurse (t : Bool) (notClash : r (adr i (!b)) ≠ some t) :
          value (Function.update r (adr i b) (some t)) ≤ N (Function.update r (adr i b) (some t)) :=
        ih _ (h ▸ fewer r _ unknown t) _ (preserve r valid i b t notClash) rfl
      have ff : free no = (free r).erase i := update_free r i b false
      have ft : free yes = (free r).erase i := update_free r i b true
      have uf : unresolved no = unresolved r := update_no r i b unknown
      have ut : unresolved yes = (unresolved r).erase i := update_yes r i b
      have subset := Finset.card_le_card (sub r)
      cases other : r (adr i (!b)) with
      | none =>
        have fm : i∈free r := Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun s => by
          by_cases e : s=b
          · simpa [e] using unknown
          · have e' : s= !b := other_side s b e
            simpa [e'] using other⟩
        have um := sub r fm
        have h1 : value no ≤ N no := recurse false (by simp [other])
        have h2 : value yes ≤ N yes := recurse true (by simp [other])
        unfold value at *
        rw [ff,uf,Finset.card_erase_of_mem fm] at h1
        rw [ft,ut,Finset.card_erase_of_mem fm,Finset.card_erase_of_mem um] at h2
        have fpos := Finset.card_pos.mpr ⟨i,fm⟩
        have ux := Finset.card_pos.mpr ⟨i,um⟩
        have powpos := Nat.two_pow_pos (free r).card
        have ex : (free r).card-1+1=(free r).card := by omega
        rw [ex] at h1 h2
        rw [pow_succ]
        omega
      | some bv =>
        have nf : i∉free r := fun hx => by have := (Finset.mem_filter.mp hx).2 (!b); simp [other] at this
        cases bv with
        | false =>
          have um : i∈unresolved r := Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun s => by
            by_cases e : s=b
            · simp [e,unknown]
            · have e' : s= !b := other_side s b e
              simp [e',other]⟩
          have h1 := positive N cert no
          have h2 : value yes ≤ N yes := recurse true (by simp [other])
          have strict : (free r).card < (unresolved r).card := Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨sub r,fun e => nf (e ▸ um)⟩)
          unfold value at h2 ⊢
          rw [ft,ut,Finset.erase_eq_of_notMem nf,Finset.card_erase_of_mem um] at h2
          omega
        | true =>
          have h1 : value no ≤ N no := recurse false (by simp [other])
          unfold value at h1 ⊢
          rw [ff,uf,Finset.erase_eq_of_notMem nf] at h1
          omega

def graph (k) : SimpleGraph (Fin (2*k)) where
  Adj := relation k
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem minimum (k : ℕ) (R : Finset (Fin (2*k)))
    (cover : ∀ u v, (graph k).Adj u v → u∈R ∨ v∈R) : k≤R.card := by
  classical
  have hit (i : Fin k) : ∃ b, adr i b∈R := by
    have edge : (graph k).Adj (adr i false) (adr i true) := ⟨by simp,congrArg Fin.val ((idxAdr i false).trans (idxAdr i true).symm)⟩
    exact (cover _ _ edge).elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
  choose b hb using hit
  let f (i : Fin k) := adr i (b i)
  have inj : Function.Injective f := fun _ _ h => ((adr_eq _ _ _ _).mp h).1
  have sub : Finset.univ.image f ⊆ R := by rintro _ h; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h; exact hb i
  simpa [Finset.card_image_of_injective _ inj] using Finset.card_le_card sub

theorem exact_matching (k : ℕ) :
    Tree (2*k) (relation k) k (2^(k+1)-1) ∧
      ∀ m, Tree (2*k) (relation k) k m → 2^(k+1)-1 ≤ m := by
  refine ⟨all_graphs_upper (graph k) (minimum k),?_⟩
  rintro m ⟨N,root,cert⟩
  let start : State (2*k) := fun _ => none
  have ok : clean start := by simp [clean,start]
  have lower := bound N cert start ok
  simpa [value,free,unresolved,start] using lower.trans root

end MatchingState

namespace TreeGlue
open CoverTree
def Bounded {n} (A : Fin n → Fin n → Prop) (t : ℕ) (r : State n) (K : ℕ) :=
  ∃ N, Legal A t N ∧ N r≤K

theorem tighten {n t} {A : Fin n → Fin n → Prop} {P N : State n → ℕ} (bound : ∀ x,P x≤N x)
    (r : State n) (equal : P r=N r) (step : Legal A t N) :
    (Done A t r ∧ 1≤P r) ∨ ∃ v, r v=none ∧ P (Function.update r v (some false))+
      P (Function.update r v (some true))≤P r := by
  rw [equal]
  rcases step r with leaf|⟨v,hv,split⟩
  · exact Or.inl leaf
  · exact Or.inr ⟨v,hv,(Nat.add_le_add (bound _) (bound _)).trans split⟩

theorem minimum_legal {n t} {A : Fin n → Fin n → Prop} (N M : State n → ℕ)
    (hn : Legal A t N) (hm : Legal A t M) : Legal A t (fun r => min (N r) (M r)) := by
  intro r
  rcases le_total (N r) (M r) with h|h
  · exact tighten (fun u => min_le_left _ _) r (min_eq_left h) hn
  · exact tighten (fun u => min_le_right _ _) r (min_eq_right h) hm

theorem leaf {n t} {A : Fin n → Fin n → Prop} {r : State n} (sol : ∃ N, Legal A t N)
    (finish : Done A t r) : Bounded A t r 1 := by
  classical
  obtain ⟨N,hn⟩ := sol
  let P (x : State n) := if x=r then min 1 (N r) else N x
  have le (x) : P x≤N x := by by_cases h : x=r <;> simp [P,h]
  refine ⟨P,?_,by simp [P]⟩
  intro x
  by_cases e : x=r
  · subst x
    rcases le_total (N r) 1 with h|h
    · exact tighten le r (by simp [P,min_eq_right h]) hn
    · exact Or.inl ⟨finish,by simp [P,h]⟩
  · exact tighten le x (by simp [P,e]) hn

theorem branch {n t a b} {A : Fin n → Fin n → Prop} {r : State n} (v : Fin n) (empty : r v=none)
    (left : Bounded A t (Function.update r v (some false)) a)
    (right : Bounded A t (Function.update r v (some true)) b) : Bounded A t r (a+b) := by
  classical
  obtain ⟨N,hn,costA⟩ := left
  obtain ⟨M,hm,costB⟩ := right
  let C (x : State n) := min (N x) (M x)
  let P (x : State n) := if x=r then min (C x) (a+b) else C x
  have base := minimum_legal N M hn hm
  have le (x) : P x≤C x := by by_cases h : x=r <;> simp [P,h]
  refine ⟨P,?_,by simp [P]⟩
  intro x
  by_cases eq : x=r
  · subst x
    rcases le_total (C r) (a+b) with h|h
    · exact tighten le r (by simp [P,min_eq_left h]) base
    · refine Or.inr ⟨v,empty,?_⟩
      have L := (le (Function.update r v (some false))).trans ((min_le_left _ _).trans costA)
      have R := (le (Function.update r v (some true))).trans ((min_le_right _ _).trans costB)
      simpa [P,min_eq_right h] using Nat.add_le_add L R
  · exact tighten le x (by simp [P,eq]) base

theorem widen {n t a b} {A : Fin n → Fin n → Prop} {r : State n} (h : Bounded A t r a)
    (le : a≤b) : Bounded A t r b := by
  obtain ⟨N,leg,cost⟩ := h
  exact ⟨N,leg,cost.trans le⟩

theorem true_count {n} (r : State n) (v : Fin n) (h : r v=none) :
    (trueSet (Function.update r v (some true))).card=(trueSet r).card+1 := by
  rw [(true_update r v h).1,Finset.card_insert_of_notMem (by simp [trueSet,h])]

end TreeGlue

namespace FibonacciBudget
def F (r : ℕ) := Nat.fib (r+4)-2
def phi (r u : ℕ) := min r u + F (r-u)

theorem F_zero : F 0 = 1 := by decide
theorem F_one : F 1 = 3 := by decide

theorem fib_two (r : ℕ) : 2≤Nat.fib (r+4) :=
  (by decide : 2≤Nat.fib 4).trans (Nat.fib_mono (by omega))

theorem F_add (r : ℕ) : F (r+2) = F (r+1)+F r+2 := by
  have known (x : ℕ) : F x+2=Nat.fib (x+4) := Nat.sub_add_cancel (fib_two x)
  have total : F (r+2)+2 = (F r+2)+(F (r+1)+2) :=
    (known (r+2)).trans ((@Nat.fib_add_two (r+4)).trans (congrArg₂ Nat.add (known r).symm (known (r+1)).symm))
  omega

theorem F_step (r : ℕ) : F r+1 ≤ F (r+1) := by
  cases r with
  | zero => decide
  | succ r => rw [show r+1+1=r+2 by omega,F_add]; omega

theorem phi_zero (u : ℕ) : phi 0 u=1 := by simp [phi,F_zero]

theorem decrease (r u : ℕ) : phi r (u+1) ≤ phi r u := by
  by_cases h : r≤u
  · simp [phi,min_eq_left h,min_eq_left (show r≤u+1 by omega),Nat.sub_eq_zero_of_le h,Nat.sub_eq_zero_of_le (show r≤u+1 by omega)]
  · have e : r-u = (r-(u+1))+1 := by omega
    simp only [phi,min_eq_right (show u+1≤r by omega),min_eq_right (show u≤r by omega),e]
    have := F_step (r-(u+1))
    omega

theorem anti (r : ℕ) {u v : ℕ} (h : u≤v) : phi r v ≤ phi r u := by
  induction h with
  | refl => rfl
  | step h ih => exact (decrease r _).trans ih

theorem forced (r u : ℕ) (hr : 0<r) (hu : 0<u) : phi r u = 1+phi (r-1) (u-1) := by
  cases r <;> cases u <;> simp_all [phi,Nat.succ_min_succ,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

theorem branch (r u : ℕ) (hr : 0<r) : phi r u ≤ phi (r-1) u + phi r (u+2) := by
  by_cases rich : u+2≤r
  · have e : r-u = r-(u+2)+2 := by omega
    have e' : r-1-u = r-(u+2)+1 := by omega
    simp only [phi,min_eq_right rich,min_eq_right (show u≤r by omega),min_eq_right (show u≤r-1 by omega),e,e',F_add]
    omega
  · by_cases ample : r≤u
    · simp [phi,min_eq_left ample,min_eq_left (show r-1≤u by omega),min_eq_left (show r≤u+2 by omega),
        Nat.sub_eq_zero_of_le ample,Nat.sub_eq_zero_of_le (show r-1≤u by omega),Nat.sub_eq_zero_of_le (show r≤u+2 by omega),F_zero]
    · have eq : r=u+1 := by omega
      subst r
      simp [phi,min_eq_right (show u≤u+1 by omega),min_eq_left (show u+1≤u+2 by omega),F_zero,F_one]
      omega

end FibonacciBudget

namespace DegreeTwo
open CoverTree FibonacciBudget MatchingState

noncomputable def neighbors {n} (G : SimpleGraph (Fin n)) (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun u => G.Adj v u)

noncomputable def forcedSet {n} (G : SimpleGraph (Fin n)) (r : State n) := by
  classical
  exact Finset.univ.filter (fun v => r v=none ∧ ∃ w, G.Adj w v ∧ r w=some false)

theorem forced_yes {n} (G : SimpleGraph (Fin n)) (r : State n) (v : Fin n) (hv : r v=none) :
    forcedSet G (Function.update r v (some true)) = (forcedSet G r).erase v := by
  classical
  ext u
  by_cases eq : u=v
  · simp [eq,forcedSet]
  · have old (w) : Function.update r v (some true) w = some false ↔ r w=some false := by
      by_cases ew : w=v <;> simp [Function.update,ew,hv]
    simp [forcedSet,eq,Function.update_of_ne,old]

theorem forced_no {n} (G : SimpleGraph (Fin n)) (r : State n) (v : Fin n) :
    forcedSet G (Function.update r v (some false)) ⊆ (forcedSet G r) ∪ neighbors G v := by
  classical
  intro u hu
  obtain ⟨empty,w,edge,h⟩ := (Finset.mem_filter.mp hu).2
  by_cases wv : w=v
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,wv ▸ edge⟩)
  · have uv : u≠v := by rintro rfl; simp at empty
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [Function.update_of_ne uv] using empty,
      w,edge,by simpa [Function.update_of_ne wv] using h⟩

theorem safe_yes {n} (G : SimpleGraph (Fin n)) (r : State n) (v : Fin n) (safe : ¬Conflict G.Adj r) :
    ¬Conflict G.Adj (Function.update r v (some true)) := by
  rintro ⟨a,b,e,ra,rb⟩
  have old (s) (h : Function.update r v (some true) s=some false) : r s=some false := by
    by_cases eq : s=v <;> simp_all [Function.update]
  exact safe ⟨a,b,e,old a ra,old b rb⟩

theorem safe_no {n} (G : SimpleGraph (Fin n)) (r : State n) (v : Fin n) (empty : r v=none)
    (safe : ¬Conflict G.Adj r) (unforced : v∉forcedSet G r) : ¬Conflict G.Adj (Function.update r v (some false)) := by
  classical
  rintro ⟨a,b,edge,ra,rb⟩
  by_cases av : a=v
  · subst a
    have bv := (G.ne_of_adj edge).symm
    exact unforced (Finset.mem_filter.mpr ⟨Finset.mem_univ _,empty,b,edge.symm,by simpa [Function.update_of_ne bv] using rb⟩)
  by_cases bv : b=v
  · subst b
    exact unforced (Finset.mem_filter.mpr ⟨Finset.mem_univ _,empty,a,edge,by simpa [Function.update_of_ne av] using ra⟩)
  exact safe ⟨a,b,edge,by simpa [Function.update_of_ne av] using ra,by simpa [Function.update_of_ne bv] using rb⟩

theorem lower_at {n t} (G : SimpleGraph (Fin n))
    (degree : ∀ v, (neighbors G v).card ≤ 2)
    (N : State n → ℕ) (legal : Legal G.Adj t N) (r : State n) (clean : ¬Conflict G.Adj r) :
    phi (t-(trueSet r).card) (forcedSet G r).card ≤ N r := by
  classical
  induction h : (unasked r).card using Nat.strong_induction_on generalizing r with
  | ind d ih =>
    by_cases full : t≤(trueSet r).card
    · simpa [Nat.sub_eq_zero_of_le full,phi_zero] using positive N legal r
    have lt : (trueSet r).card<t := by omega
    have notDone : ¬Done G.Adj t r := fun done => (done.resolve_left clean).not_gt lt
    obtain ⟨v,empty,budget⟩ := (legal r).resolve_left (fun h => notDone h.1)
    let no := Function.update r v (some false)
    let yes := Function.update r v (some true)
    change N no + N yes ≤ N r at budget
    let a := t-(trueSet r).card
    let u := (forcedSet G r).card
    have pos : 0<a := by dsimp [a]; omega
    have dec : t-(trueSet yes).card=a-1 := by
      rw [(true_update r v empty).1,Finset.card_insert_of_notMem (by simp [trueSet,empty])]
      dsimp [a]; omega
    have trueBound := ih _ (h ▸ fewer r v empty true) yes (safe_yes G r v clean) rfl
    rw [dec,forced_yes G r v empty] at trueBound
    change phi a u ≤ _
    by_cases unit : v∈forcedSet G r
    · rw [Finset.card_erase_of_mem unit] at trueBound
      rw [forced a u pos (Finset.card_pos.mpr ⟨v,unit⟩)]
      exact (Nat.add_le_add (positive N legal no) trueBound).trans budget
    · rw [Finset.erase_eq_of_notMem unit] at trueBound
      have falseBound := ih _ (h ▸ fewer r v empty false) no (safe_no G r v empty clean unit) rfl
      rw [(true_update r v empty).2] at falseBound
      have delta := (Finset.card_le_card (forced_no G r v)).trans (Finset.card_union_le _ _)
      have two := degree v
      have room : (forcedSet G no).card≤u+2 := delta.trans (Nat.add_le_add_left two _)
      have h0 := (anti a room).trans falseBound
      exact (branch a u pos).trans ((Nat.add_le_add trueBound h0).trans (by omega))

theorem lower {n t k} (G : SimpleGraph (Fin n))
    (degree : ∀ v, (neighbors G v).card ≤ 2)
    (tree : Tree n G.Adj t k) : F t ≤ k := by
  obtain ⟨N,root,h⟩ := tree
  have z := lower_at G degree N h (fun _ => none) (by simp [Conflict])
  simpa [phi,forcedSet,trueSet] using z.trans root

end DegreeTwo

namespace PathUpper
open CoverTree TreeGlue FibonacciBudget

theorem forced_step {n t K} {A : Fin n → Fin n → Prop} (sol : ∃ N, Legal A t N)
    (r : State n) (z v : Fin n) (edge : A z v ∨ A v z) (diff : z≠v)
    (zero : r z=some false) (empty : r v=none) (next : Bounded A t (Function.update r v (some true)) K) :
    Bounded A t r (1+K) := by
  apply TreeGlue.branch v empty _ next
  apply leaf sol
  left
  have cz : Function.update r v (some false) z=some false := by simpa [Function.update_of_ne diff] using zero
  rcases edge with e|e
  · exact ⟨z,v,e,cz,by simp⟩
  · exact ⟨v,z,e,by simp,cz⟩

def FreshPath {n} (A : Fin n → Fin n → Prop) (r : State n) (v : ℕ → Fin n) (l : ℕ) :=
  (∀ i, i<l → r (v i)=none) ∧
  (∀ i j, i<l → j<l → v i=v j → i=j) ∧
  (∀ i, i+1<l → A (v i) (v (i+1)))

theorem step_tail {n} {A : Fin n → Fin n → Prop} {r : State n} {v : ℕ → Fin n} {l : ℕ}
    (old : FreshPath A r v l) (start K : ℕ) (ends : start+K≤l)
    (s : State n) (same : ∀ i, i<K → s (v (start+i))=r (v (start+i))) :
    FreshPath A s (fun i => v (start+i)) K := by
  refine ⟨fun i hi => (same i hi).trans (old.1 _ (by omega)),?_,?_⟩
  · intro i j hi hj e
    have := old.2.1 (start+i) (start+j) (by omega) (by omega) e
    omega
  · intro i hi
    exact old.2.2 (start+i) (by omega)

theorem path_upper_at {n t} (A : Fin n → Fin n → Prop) (sol : ∃ N, Legal A t N)
    (k : ℕ) (r : State n) (v : ℕ → Fin n) (path : FreshPath A r v (2*k))
    (enough : t≤(trueSet r).card+k) : Bounded A t r (F k) := by
  induction k using Nat.strong_induction_on generalizing r v with
  | ind k ih =>
    cases k with
    | zero => exact leaf sol (Or.inr (by omega))
    | succ k =>
      cases k with
      | zero =>
        have a := path.1 0 (by decide)
        have b := path.1 1 (by decide)
        have ne : v 1 ≠ v 0 := fun e => (by decide : (1:ℕ)≠0) (path.2.1 _ _ (by decide) (by decide) e)
        let no := Function.update r (v 0) (some false)
        have free : no (v 1)=none := by simpa [no,Function.update_of_ne ne] using b
        have count : (trueSet no).card=(trueSet r).card := congrArg Finset.card (true_update r (v 0) a).2
        have L : Bounded A t no (1+1) := forced_step sol no (v 0) (v 1) (Or.inl (path.2.2 0 (by decide)))
          ne.symm (by simp [no]) free (leaf sol (Or.inr (by rw [true_count _ _ free,count]; omega)))
        have R := leaf sol (r:=Function.update r (v 0) (some true)) (Or.inr (by rw [true_count _ _ a]; omega))
        exact TreeGlue.branch (v 0) a L R
      | succ k =>
        have a := path.1 0 (by omega)
        have b := path.1 1 (by omega)
        have c := path.1 2 (by omega)
        have distinct (i j : ℕ) (hi : i<2*(k+2)) (hj : j<2*(k+2)) (ne : i≠j) : v i≠v j := fun e => ne (path.2.1 i j hi hj e)
        let no := Function.update r (v 1) (some false)
        let yes := Function.update r (v 1) (some true)
        let leftOn := Function.update no (v 0) (some true)
        let both := Function.update leftOn (v 2) (some true)
        have c0 : no (v 0)=none := by simpa [no,Function.update_of_ne (distinct 0 1 (by omega) (by omega) (by decide))] using a
        have c2 : leftOn (v 2)=none := by
          simpa [leftOn,no,Function.update_of_ne (distinct 2 0 (by omega) (by omega) (by decide)),
            Function.update_of_ne (distinct 2 1 (by omega) (by omega) (by decide))] using c
        have onyes : (trueSet yes).card=(trueSet r).card+1 := true_count r _ b
        have onno : (trueSet no).card=(trueSet r).card := congrArg Finset.card (true_update r _ b).2
        have one : (trueSet leftOn).card=(trueSet no).card+1 := true_count no _ c0
        have two : (trueSet both).card=(trueSet leftOn).card+1 := true_count leftOn _ c2
        have sy : FreshPath A yes (fun i => v (2+i)) (2*(k+1)) := by
          apply step_tail path 2 _ (by omega) yes
          intro i hi
          simp [yes,Function.update_of_ne (distinct (2+i) 1 (by omega) (by omega) (by omega))]
        have sb : FreshPath A both (fun i => v (3+i)) (2*k) := by
          apply step_tail path 3 _ (by omega) both
          intro i hi
          simp [both,leftOn,no,Function.update_of_ne (distinct (3+i) 0 (by omega) (by omega) (by omega)),
            Function.update_of_ne (distinct (3+i) 1 (by omega) (by omega) (by omega)),
            Function.update_of_ne (distinct (3+i) 2 (by omega) (by omega) (by omega))]
        have R := ih (k+1) (by omega) yes _ sy (by omega)
        have tail := ih k (by omega) both _ sb (by omega)
        have mid : leftOn (v 1)=some false := by simp [leftOn,no,Function.update_of_ne (distinct 1 0 (by omega) (by omega) (by decide))]
        have L2 := forced_step sol leftOn (v 1) (v 2) (Or.inl (path.2.2 1 (by omega)))
          (distinct 1 2 (by omega) (by omega) (by decide)) mid c2 tail
        have L1 := forced_step sol no (v 1) (v 0) (Or.inr (path.2.2 0 (by omega)))
          (distinct 1 0 (by omega) (by omega) (by decide)) (by simp [no]) c0 L2
        apply widen (TreeGlue.branch (v 1) b L1 R)
        rw [F_add]
        omega

end PathUpper

namespace RingUpper
open CoverTree TreeGlue PathUpper FibonacciBudget

theorem cycle_upper_at {n t} (A : Fin n → Fin n → Prop) (sol : ∃ N, Legal A t N)
    (k : ℕ) (r : State n) (v : ℕ → Fin n) (path : FreshPath A r v n)
    (room : 2*k+3 ≤ n) (enough : t ≤ (trueSet r).card+k+2)
    (wrap : A (v (n-1)) (v 0)) : Bounded A t r (F (k+2)) := by
  have diff (i j : ℕ) (hi : i<n) (hj : j<n) (h : i≠j) : v i≠v j := fun e => h (path.2.1 i j hi hj e)
  let z := v (n-1)
  let p := v 0
  let q := v (n-2)
  have zp : z≠p := diff (n-1) 0 (by omega) (by omega) (by omega)
  have zq : z≠q := diff (n-1) (n-2) (by omega) (by omega) (by omega)
  have qp : q≠p := diff (n-2) 0 (by omega) (by omega) (by omega)
  have edge : A q z := by
    have e := path.2.2 (n-2) (by omega)
    simpa only [q,z,show n-2+1=n-1 by omega] using e
  let no := Function.update r z (some false)
  let yes := Function.update r z (some true)
  let onp := Function.update no p (some true)
  let both := Function.update onp q (some true)
  have ez : r z=none := path.1 (n-1) (by omega)
  have ep : no p=none := by simpa [no, Function.update_of_ne zp.symm] using path.1 0 (by omega)
  have eqn : onp q=none := by
    simpa [onp,no,Function.update_of_ne qp, Function.update_of_ne zq.symm] using path.1 (n-2) (by omega)
  have fy : FreshPath A yes (fun i => v (0+i)) (2*(k+1)) := by
    apply step_tail path 0 _ (by omega) yes
    intro i hi
    exact Function.update_of_ne (diff (0+i) (n-1) (by omega) (by omega) (by omega)) _ _
  have fb : FreshPath A both (fun i => v (1+i)) (2*k) := by
    apply step_tail path 1 _ (by omega) both
    intro i hi
    have np : v (1+i)≠p := diff (1+i) 0 (by omega) (by omega) (by omega)
    have nq : v (1+i)≠q := diff (1+i) (n-2) (by omega) (by omega) (by omega)
    have nz : v (1+i)≠z := diff (1+i) (n-1) (by omega) (by omega) (by omega)
    simp [both,onp,no,Function.update_of_ne np,Function.update_of_ne nq,Function.update_of_ne nz]
  have countY : (trueSet yes).card=(trueSet r).card+1 := true_count r z ez
  have countN : (trueSet no).card=(trueSet r).card := congrArg Finset.card (true_update r z ez).2
  have countP : (trueSet onp).card=(trueSet no).card+1 := true_count no p ep
  have countB : (trueSet both).card=(trueSet onp).card+1 := true_count onp q eqn
  have R := path_upper_at A sol (k+1) yes _ fy (by omega)
  have B := path_upper_at A sol k both _ fb (by omega)
  have P := forced_step sol onp z q (Or.inr edge) zq (by simp [onp,no,Function.update_of_ne zp]) eqn B
  have L := forced_step sol no z p (Or.inl wrap) zp (by simp [no]) ep P
  apply widen (TreeGlue.branch z ez L R)
  rw [F_add]
  omega

def idx (n : ℕ) (pos : 0<n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ pos⟩

theorem interval {n} (pos : 0<n) (A : Fin n → Fin n → Prop)
    (step : ∀ u v : Fin n, u.val+1=v.val → A u v) (len : ℕ) (bound : len≤n) :
    FreshPath A (fun _ => none) (idx n pos) len := by
  refine ⟨fun _ _ => rfl,?_,?_⟩
  · intro i j hi hj h
    simpa [idx,Nat.mod_eq_of_lt (by omega : i<n),Nat.mod_eq_of_lt (by omega : j<n)] using congrArg Fin.val h
  · intro i hi
    apply step
    simp [idx,Nat.mod_eq_of_lt (by omega : i<n),Nat.mod_eq_of_lt (by omega : i+1<n)]

theorem path_bound {n} (hn : 2≤n) (G : SimpleGraph (Fin n))
    (step : ∀ u v : Fin n, u.val+1=v.val → G.Adj u v)
    (minimum : ∀ R : Finset (Fin n), (∀ u v, G.Adj u v → u∈R ∨ v∈R) → n/2 ≤ R.card) :
    Tree n G.Adj (n/2) (F (n/2)) := by
  have b := path_upper_at G.Adj ⟨_,cost_legal G minimum⟩ (n/2) (fun _ => none) _
    (interval (by omega) G.Adj step (2*(n/2)) (by omega)) (by simp [trueSet])
  obtain ⟨N,leg,top⟩ := b
  exact ⟨N,top,leg⟩

theorem cycle_bound {n} (hn : 4≤n) (G : SimpleGraph (Fin n))
    (step : ∀ u v : Fin n, u.val+1=v.val → G.Adj u v)
    (wrap : G.Adj (idx n (by omega) (n-1)) (idx n (by omega) 0))
    (minimum : ∀ R : Finset (Fin n), (∀ u v, G.Adj u v → u∈R ∨ v∈R) → (n+1)/2 ≤ R.card) :
    Tree n G.Adj ((n+1)/2) (F ((n+1)/2)) := by
  let k := (n+1)/2-2
  have e : (n+1)/2=k+2 := by dsimp [k]; omega
  have b := cycle_upper_at G.Adj ⟨_,cost_legal G minimum⟩ k (fun _ => none) _
    (interval (by omega) G.Adj step n (by omega)) (by omega) (by simp [trueSet,e]) wrap
  obtain ⟨N,leg,top⟩ := b
  exact ⟨N,e ▸ top,leg⟩

end RingUpper

namespace SpiderTree
abbrev Pin := Option Bool
abbrev Totals := ℕ × ℕ × ℕ × ℕ × ℕ

-- Counts of untouched arms, arms with one false vertex and one unknown vertex,
-- false inner vertices, true outer vertices with unknown inner vertex, and equal assigned pairs.
def record : Pin → Pin → Totals
  | none, none => (1,0,0,0,0)
  | none, some false => (0,1,0,0,0)
  | none, some true => (0,0,0,1,0)
  | some false, none => (0,1,1,0,0)
  | some false, some false => (0,0,1,0,1)
  | some false, some true => (0,0,1,0,0)
  | some true, none => (0,0,0,0,0)
  | some true, some false => (0,0,0,0,0)
  | some true, some true => (0,0,0,0,1)

def weight (hub : Pin) (a : Totals) : ℕ :=
  let ⟨f,p,b,r,c⟩ := a
  if 0<c then 1 else
  match hub with
  | none => 2^f+p + (if 0<b then 0 else if 0<r then min 1 f else f)
  | some false => if 0<b then 1 else if 0<r then min 2 (f+p+1) else f+p+1
  | some true => max 1 (2^f-1+p)

theorem split_hub (a : Totals) :
    weight none a ≤ weight (some false) a + weight (some true) a := by
  obtain ⟨f,p,b,r,c⟩ := a
  have := Nat.two_pow_pos f
  simp only [weight]
  split_ifs <;> omega

private theorem armInner (h m : Pin) (a : Totals) :
    weight h (record none m+a) ≤ weight h (record (some false) m+a) + weight h (record (some true) m+a) := by
  obtain ⟨f,p,b,r,c⟩ := a
  have hp := Nat.two_pow_pos f
  rcases h with _ | (_ | _) <;> rcases m with _ | (_ | _) <;>
    simp only [record,weight,Nat.zero_add,Nat.one_add,pow_succ] <;>
    split_ifs <;> omega

private theorem armOuter (h m : Pin) (a : Totals) :
    weight h (record m none+a) ≤ weight h (record m (some false)+a) + weight h (record m (some true)+a) := by
  obtain ⟨f,p,b,r,c⟩ := a
  have hp := Nat.two_pow_pos f
  rcases h with _ | (_ | _) <;> rcases m with _ | (_ | _) <;>
    simp only [record,weight,Nat.zero_add,Nat.one_add,pow_succ] <;>
    split_ifs <;> omega

def assign (m : Bool → Pin) (side v : Bool) := Function.update m side (some v)
theorem split_arm (h : Pin) (m : Bool → Pin) (side : Bool) (unknown : m side=none) (a : Totals) :
    weight h (record (m false) (m true)+a) ≤
      weight h (record (assign m side false false) (assign m side false true)+a) +
      weight h (record (assign m side true false) (assign m side true true)+a) := by
  cases side <;> simp_all [assign,Function.update,armInner,armOuter]

open CoverTree

abbrev V (k : ℕ) := Fin (2*k+1)
def hub (k : ℕ) : V k := ⟨0,by omega⟩
def arm {k : ℕ} (i : Fin k) (outer : Bool) : V k :=
  ⟨1+i.val + if outer then k else 0,by cases outer <;> simp <;> omega⟩

theorem arm_ne_hub {k} (i : Fin k) (b : Bool) : arm i b ≠ hub k := by
  intro eq
  have := congrArg Fin.val eq
  cases b <;> simp [arm,hub] at this
@[local simp] theorem arm_eq {k} (i j : Fin k) (a b : Bool) : arm i a=arm j b ↔ i=j ∧ a=b := by
  constructor
  · intro h
    have e := congrArg Fin.val h
    cases a <;> cases b <;> simp [arm] at e ⊢ <;> omega
  · rintro ⟨rfl,rfl⟩;rfl

theorem vertices {k} (v : V k) : v=hub k ∨ ∃ i b, v=arm i b := by
  by_cases e : v.val=0
  · exact Or.inl (Fin.ext e)
  right
  by_cases mid : v.val≤k
  · exact ⟨⟨v.val-1,by omega⟩,false,Fin.ext (by simp [arm];omega)⟩
  · exact ⟨⟨v.val-k-1,by have := v.isLt;omega⟩,true,Fin.ext (by simp [arm];omega)⟩

def relation (k : ℕ) (a b : V k) : Prop :=
  (a.val=0 ∧ 1≤b.val ∧ b.val≤k) ∨ (b.val=0 ∧ 1≤a.val ∧ a.val≤k) ∨
  (1≤a.val ∧ a.val≤k ∧ b.val=a.val+k) ∨ (1≤b.val ∧ b.val≤k ∧ a.val=b.val+k)

theorem edges {k : ℕ} {u v : V k} : relation k u v ↔
    (∃ i, u=hub k ∧ v=arm i false) ∨ (∃ i, v=hub k ∧ u=arm i false) ∨
    (∃ i, u=arm i false ∧ v=arm i true) ∨ (∃ i, v=arm i false ∧ u=arm i true) := by
  constructor
  · rintro (⟨hu,hv,b⟩ | ⟨hv,hu,b⟩ | ⟨ha,hb,hv⟩ | ⟨ha,hb,hu⟩)
    · exact Or.inl ⟨⟨v.val-1,by omega⟩,Fin.ext hu,Fin.ext (by simp [arm];omega)⟩
    · exact Or.inr (Or.inl ⟨⟨u.val-1,by omega⟩,Fin.ext hv,Fin.ext (by simp [arm];omega)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨⟨u.val-1,by omega⟩,Fin.ext (by simp [arm];omega),
        Fin.ext (by simp [arm];omega)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨⟨v.val-1,by omega⟩,Fin.ext (by simp [arm];omega),
        Fin.ext (by simp [arm];omega)⟩))
  · rintro (⟨i,rfl,rfl⟩ | ⟨i,rfl,rfl⟩ | ⟨i,rfl,rfl⟩ | ⟨i,rfl,rfl⟩) <;>
      simp [relation,hub,arm] <;> omega

def graph (k : ℕ) : SimpleGraph (V k) where
  Adj := relation k
  symm := ⟨by intro a b h;rcases h with h|h|h|h <;> simp_all [relation]⟩
  loopless := ⟨by intro a h;rcases h with h|h|h|h <;> omega⟩

def encode {k} : Option (Fin k × Bool) → V k
  | none => hub k
  | some (i,b) => arm i b
theorem encode_bijective {k} : Function.Bijective (encode (k:=k)) := by
  constructor
  · rintro (_ | ⟨i,a⟩) (_ | ⟨j,b⟩) h
    · rfl
    · exact False.elim ((arm_ne_hub _ _) h.symm)
    · exact False.elim ((arm_ne_hub _ _) h)
    · obtain ⟨rfl,rfl⟩ := (arm_eq i j a b).mp h
      rfl
  · intro v
    rcases vertices v with rfl | ⟨i,b,rfl⟩
    · exact ⟨none,rfl⟩
    · exact ⟨some (i,b),rfl⟩

theorem minimum {k} (R : Finset (V k)) (covers : ∀ u v, (graph k).Adj u v → u∈R ∨ v∈R) : k≤R.card := by
  classical
  have hit (i : Fin k) : ∃ b, arm i b ∈ R := by
    have edge : (graph k).Adj (arm i false) (arm i true) := edges.mpr (Or.inr (Or.inr (Or.inl ⟨i,rfl,rfl⟩)))
    exact (covers _ _ edge).elim (fun a=>⟨false,a⟩) (fun b=>⟨true,b⟩)
  choose b hb using hit
  have injective : Function.Injective (fun i=>arm i (b i)) := fun i j e => ((arm_eq i j ..).mp e).1
  have sub : Finset.univ.image (fun i=>arm i (b i)) ⊆ R := by
    rintro _ h;obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h;exact hb i
  simpa [Finset.card_image_of_injective _ injective] using Finset.card_le_card sub

open CoverTree

def selected (p : Pin) : ℕ := if p=some true then 1 else 0
def entry {k} (r : State (2*k+1)) (i : Fin k) := record (r (arm i false)) (r (arm i true))
def total {k} (r : State (2*k+1)) := ∑ i, entry r i
def score {k} (r : State (2*k+1)) := weight (r (hub k)) (total r)
def rest {k} (r : State (2*k+1)) (i : Fin k) := ∑ j∈Finset.univ.erase i, entry r j

theorem total_eq {k} (r : State (2*k+1)) (i : Fin k) : total r=entry r i+rest r i := by
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

private theorem record_count (a b : Pin) : selected a + selected b +
    (record a b).1 + (record a b).2.1 ≤ 1+(record a b).2.2.2.2 := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> decide

private theorem sum_count {k} (r : State (2*k+1)) (s : Finset (Fin k)) :
    (∑ i∈s, (selected (r (arm i false)) + selected (r (arm i true)))) +
      (∑ i∈s, entry r i).1 + (∑ i∈s, entry r i).2.1 ≤ s.card + (∑ i∈s, entry r i).2.2.2.2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s h ih =>
    have localCount := record_count (r (arm j false)) (r (arm j true))
    change _ + (entry r j).1 + (entry r j).2.1 ≤ 1+(entry r j).2.2.2.2 at localCount
    simp only [Finset.sum_insert h,Prod.fst_add,Prod.snd_add,Finset.card_insert_of_notMem h]
    omega

private theorem true_count {k} (r : State (2*k+1)) : (trueSet r).card = selected (r (hub k)) +
    ∑ i : Fin k, (selected (r (arm i false)) + selected (r (arm i true))) := by
  classical
  let e : Option (Fin k × Bool) ≃ V k := Equiv.ofBijective encode encode_bijective
  have transfer := Fintype.sum_equiv e (fun x => selected (r (encode x))) (fun v=>selected (r v)) (fun _=>rfl)
  have card : (trueSet r).card = ∑ v : V k, selected (r v) := by simp [trueSet,selected]
  rw [card,←transfer,Fintype.sum_option,Fintype.sum_prod_type]
  simp [encode,add_comm]

theorem done_weight {k} (r : State (2*k+1)) (h : Done (relation k) k r) : score r ≤ 1 := by
  rcases h with conflict | enough
  · obtain ⟨u,v,edge,hu,hv⟩ := conflict
    rcases edges.mp edge with ⟨i,rfl,rfl⟩ | ⟨i,rfl,rfl⟩ | ⟨i,rfl,rfl⟩ | ⟨i,rfl,rfl⟩
    all_goals
      unfold score
      rw [total_eq r i]
      unfold entry
      simp only [hu,hv]
      rcases rest r i with ⟨f,p,b,risk,c⟩
      rcases r (arm i true) with _ | (_ | _) <;> simp [record,weight]
  · have count := sum_count r Finset.univ
    simp only [Finset.card_univ,Fintype.card_fin] at count
    change _ + (total r).1 + (total r).2.1 ≤ k+(total r).2.2.2.2 at count
    rw [true_count] at enough
    unfold score
    rcases htot : total r with ⟨f,p,b,risk,c⟩
    rw [htot] at count
    simp [selected] at count
    by_cases clash : 0<c
    · simp [weight,clash]
    · rcases hh : r (hub k) with _ | (_ | _) <;> simp [hh,selected] at enough <;>
        first
        | have z : f=0 ∧ p=0 := by omega
          simp [weight,clash,z.1,z.2]
        | have few : f=0 ∨ f=1 := by omega
          rcases few with z|z <;> simp [weight,clash,z] <;> omega

open CoverTree

private theorem hub_total {k} (r : State (2*k+1)) (v : Bool) :
    total (Function.update r (hub k) (some v))=total r := by
  unfold total
  apply Finset.sum_congr rfl
  intro i _
  simp [entry,Function.update_of_ne (arm_ne_hub _ _)]

private theorem away {k} (r : State (2*k+1)) (i : Fin k) (side bit : Bool) :
    rest (Function.update r (arm i side) (some bit)) i = rest r i := by
  unfold rest
  apply Finset.sum_congr rfl
  intro j hj
  simp [entry,Function.update,(Finset.mem_erase.mp hj).1]

private theorem at_arm {k} (r : State (2*k+1)) (i : Fin k) (side bit : Bool) :
    entry (Function.update r (arm i side) (some bit)) i =
      record (assign (fun b=>r (arm i b)) side bit false) (assign (fun b=>r (arm i b)) side bit true) := by
  cases side <;> simp [entry,assign,Function.update]

theorem split_score {k} (r : State (2*k+1)) (v : V k) (unknown : r v=none) :
    score r ≤ score (Function.update r v (some false)) + score (Function.update r v (some true)) := by
  rcases vertices v with rfl | ⟨i,s,rfl⟩
  · simpa [score,unknown,hub_total] using split_hub (total r)
  · unfold score
    rw [Function.update_of_ne (arm_ne_hub _ _).symm,Function.update_of_ne (arm_ne_hub _ _).symm]
    rw [total_eq r i,total_eq _ i,total_eq _ i]
    simp only [away,at_arm]
    exact split_arm _ (fun b=>r (arm i b)) s unknown _

theorem bound {k} (N : State (2*k+1) → ℕ) (legal : Legal (relation k) k N) (r : State (2*k+1)) :
    score r ≤ N r := by
  induction h : (MatchingState.unasked r).card using Nat.strong_induction_on generalizing r with
  | ind d ih =>
    rcases legal r with ⟨done,pos⟩ | ⟨v,unknown,split⟩
    · exact (done_weight r done).trans pos
    · have l := ih _ (h ▸ MatchingState.fewer r v unknown false) _ rfl
      have u := ih _ (h ▸ MatchingState.fewer r v unknown true) _ rfl
      exact (split_score r v unknown).trans ((Nat.add_le_add l u).trans split)

theorem lower (k m : ℕ) (tree : Tree (2*k+1) (relation k) k m) : 2^k+k ≤ m := by
  obtain ⟨N,h,legal⟩ := tree
  let empty : State (2*k+1) := fun _=>none
  have val := (bound N legal empty).trans h
  simpa [score,total,entry,record,weight,empty] using val

open CoverTree TreeGlue

private theorem inner_edge {k} (i : Fin k) : relation k (hub k) (arm i false) :=
  edges.mpr (Or.inl ⟨i,rfl,rfl⟩)

private theorem false_hub {k} (r : State (2*k+1)) (hh : r (hub k)=some false) :
    Bounded (relation k) k r (k-(trueSet r).card+1) := by
  classical
  let N := cost (graph k).Adj k
  have legal : Legal (relation k) k N := cost_legal (graph k) minimum
  have valid : ∃ C, Legal (relation k) k C := ⟨N,legal⟩
  induction h : k-(trueSet r).card using Nat.strong_induction_on generalizing r with
  | ind n ih =>
    by_cases finish : Done (relation k) k r
    · exact widen (leaf valid finish) (by omega)
    have demand : (trueSet r).card<k := by unfold Done at finish;omega
    obtain ⟨i,notChosen⟩ : ∃ i : Fin k, r (arm i false)≠some true := by
      by_contra! all
      have inj : Function.Injective (fun j : Fin k=>arm j false) := fun i j e=>((arm_eq i j ..).mp e).1
      have sub : Finset.univ.image (fun j : Fin k=>arm j false) ⊆ trueSet r := by
        rintro _ hi;obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi;simp [trueSet,all]
      have count := Finset.card_le_card sub
      simp [Finset.card_image_of_injective _ inj] at count
      omega
    have unknown : r (arm i false)=none := by
      cases hv : r (arm i false) with
      | none => rfl
      | some b =>
        cases b with
        | true => contradiction
        | false => exact False.elim (finish (Or.inl ⟨_,_,inner_edge i,hh,hv⟩))
    have bad : Done (relation k) k (Function.update r (arm i false) (some false)) :=
      Or.inl ⟨_,_,inner_edge i,by simpa [Function.update_of_ne (arm_ne_hub _ _).symm] using hh,by simp⟩
    have more := TreeGlue.true_count r _ unknown
    let yes := Function.update r (arm i false) (some true)
    have small : k-(trueSet yes).card<n := by dsimp [yes];omega
    have yesHub : yes (hub k)=some false := by simpa [yes,Function.update_of_ne (arm_ne_hub _ _).symm] using hh
    exact widen (branch _ unknown (leaf valid bad) (ih _ small yes yesHub rfl)) (by dsimp [yes];omega)

theorem upper (k : ℕ) (pos : 1 ≤ k) : Tree (2*k+1) (relation k) k (2^k+k) := by
  let start : State (2*k+1) := fun _=>none
  let left := Function.update start (hub k) (some false)
  let right := Function.update start (hub k) (some true)
  have base : (trueSet start).card=0 := by simp [trueSet,start]
  have low : (trueSet left).card=0 := by rw [show trueSet left=trueSet start from (true_update start (hub k) rfl).2,base]
  have hi : (trueSet right).card=1 := (TreeGlue.true_count start (hub k) rfl).trans (by rw [base])
  have a : Bounded (relation k) k left (k+1) := by
    have := false_hub left (by simp [left]);simpa only [low,Nat.sub_zero] using this
  have b : Bounded (relation k) k right (2^k-1) := by
    refine ⟨cost (graph k).Adj k,cost_legal (graph k) minimum,?_⟩
    have := cost_le (graph k).Adj k right
    rwa [hi,show k-1+1=k by omega] at this
  obtain ⟨N,legal,c⟩ := branch (hub k) (r:=start) rfl a b
  have pow := Nat.two_pow_pos k
  exact ⟨N,by change N start ≤ _;omega,legal⟩

theorem exact_spider (k : ℕ) (pos : 1 ≤ k) : Tree (2*k+1) (relation k) k (2^k+k) ∧
    ∀ m, Tree (2*k+1) (relation k) k m → 2^k+k ≤ m := ⟨upper k pos,lower k⟩

end SpiderTree

namespace LeafGraphs
def pathRel (n : ℕ) (a b : Fin n) : Prop := a.val+1=b.val ∨ b.val+1=a.val
def cycleRel (n : ℕ) (a b : Fin n) : Prop := (a.val+1) % n=b.val ∨ (b.val+1) % n=a.val

def pathGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj := pathRel n
  symm := ⟨fun _ _ h=>h.symm⟩
  loopless := ⟨by intro x; unfold pathRel; omega⟩
def next {n : ℕ} (x : Fin n) : Fin n := ⟨(x.val+1) % n,Nat.mod_lt _ (by have := x.isLt;omega)⟩
def prev {n : ℕ} (x : Fin n) : Fin n := ⟨if x.val=0 then n-1 else x.val-1,by split_ifs <;> omega⟩

private theorem wrap {n : ℕ} (x : Fin n) : (x.val+1) % n=if x.val+1=n then 0 else x.val+1 := by
  by_cases atEnd : x.val+1=n
  · simp [atEnd]
  · simp [atEnd,Nat.mod_eq_of_lt (by omega : x.val+1<n)]

@[local simp] theorem prev_next {n : ℕ} (x : Fin n) : prev (next x)=x := by
  apply Fin.ext
  change (if (x.val+1) % n=0 then n-1 else (x.val+1) % n-1)=x.val
  by_cases last : x.val+1=n <;> simp [wrap,last]
  omega
@[local simp] theorem next_prev {n : ℕ} (x : Fin n) : next (prev x)=x := by
  apply Fin.ext
  change ((if x.val=0 then n-1 else x.val-1)+1) % n=x.val
  by_cases z : x.val=0
  · rw [ite_eq_left z,show n-1+1=n by omega,Nat.mod_self,z]
  · rw [ite_eq_right z,show x.val-1+1=x.val by omega,Nat.mod_eq_of_lt x.isLt]
theorem next_injective {n : ℕ} : Function.Injective (next (n:=n)) :=
  Function.LeftInverse.injective prev_next

theorem cycle_neighbours {n : ℕ} (a b : Fin n) : cycleRel n a b ↔ b=next a ∨ b=prev a := by
  constructor
  · rintro (h|h)
    · exact Or.inl (Fin.ext h.symm)
    · have eq : next b=a := Fin.ext h
      exact Or.inr (eq ▸ (prev_next b).symm)
  · rintro (rfl|rfl)
    · exact Or.inl rfl
    · exact Or.inr (congrArg Fin.val (next_prev _))

def cycleGraph (n : ℕ) (hn : 2 ≤ n) : SimpleGraph (Fin n) where
  Adj := cycleRel n
  symm := ⟨fun _ _ h=>h.symm⟩
  loopless := ⟨by intro x h;rcases h with h|h <;> rw [wrap] at h <;> split_ifs at h <;> omega⟩
private def paired {n} (i : Fin (n/2)) (b : Bool) : Fin n :=
  ⟨2*i.val+b.toNat,by cases b <;> simp <;> omega⟩

theorem path_minimum (n : ℕ) (R : Finset (Fin n))
    (cover : ∀ a b, (pathGraph n).Adj a b → a∈R ∨ b∈R) : n/2 ≤ R.card := by
  have hit (i : Fin (n/2)) : ∃ b, paired i b∈R := by
    have h : (pathGraph n).Adj (paired i false) (paired i true) := Or.inl rfl
    exact (cover _ _ h).elim (fun l=>⟨false,l⟩) (fun r=>⟨true,r⟩)
  choose b hb using hit
  have inj : Function.Injective (fun i=>paired i (b i)) := by
    intro i j eq
    apply Fin.ext
    have e := congrArg Fin.val eq
    dsimp [paired] at e
    have left : (b i).toNat≤1 := by cases b i <;> decide
    have right : (b j).toNat≤1 := by cases b j <;> decide
    omega
  have sub : Finset.univ.image (fun i=>paired i (b i)) ⊆ R := by
    rintro _ h;obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h;exact hb i
  simpa [Finset.card_image_of_injective _ inj] using Finset.card_le_card sub

theorem cycle_minimum (n : ℕ) (hn : 2 ≤ n) (R : Finset (Fin n))
    (cover : ∀ a b, (cycleGraph n hn).Adj a b → a∈R ∨ b∈R) : (n+1)/2 ≤ R.card := by
  have contained : Rᶜ.image next ⊆ R := by
    rintro _ h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    exact (cover a (next a) (Or.inl rfl)).resolve_left (Finset.mem_compl.mp ha)
  have count := Finset.card_le_card contained
  rw [Finset.card_image_of_injective _ next_injective,Finset.card_compl,Fintype.card_fin] at count
  omega

theorem path_degree (n : ℕ) (v : Fin n) : (DegreeTwo.neighbors (pathGraph n) v).card ≤ 2 := by
  classical
  have sub : (DegreeTwo.neighbors (pathGraph n) v).image Fin.val ⊆ {v.val-1,v.val+1} := by
    rintro _ h
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
    obtain h | h := (Finset.mem_filter.mp hx).2
    · simp [h]
    · exact Finset.mem_insert.mpr (Or.inl (by omega))
  have card := (Finset.card_le_card sub).trans Finset.card_le_two
  simpa only [Finset.card_image_of_injective _ Fin.val_injective] using card

theorem cycle_degree (n : ℕ) (hn : 2 ≤ n) (v : Fin n) : (DegreeTwo.neighbors (cycleGraph n hn) v).card ≤ 2 := by
  classical
  have sub : DegreeTwo.neighbors (cycleGraph n hn) v ⊆ {next v,prev v} := by
    intro u hu
    simpa only [Finset.mem_insert,Finset.mem_singleton] using
      (cycle_neighbours v u).mp (Finset.mem_filter.mp hu).2
  exact (Finset.card_le_card sub).trans Finset.card_le_two

end LeafGraphs

end PEqualNP.Outside.L_pcx_107

open PEqualNP.Outside.L_pcx_107

theorem PEqualNP.Outside.L_pcx_107 : ∀ Tr : (n0 : ℕ) → (Fin n0 → Fin n0 → Prop) → ℕ → ℕ → Prop, (∀ (n1 : ℕ) (A1 : Fin n1 → Fin n1 → Prop) (t1 k1 : ℕ), Tr n1 A1 t1 k1 ↔ ∃ N1 : (Fin n1 → Option Bool) → ℕ, N1 (fun w1 : Fin n1 => none) ≤ k1 ∧ ∀ ρ1 : Fin n1 → Option Bool, ((((∃ u1 v1 : Fin n1, A1 u1 v1 ∧ ρ1 u1 = some false ∧ ρ1 v1 = some false) ∨ ∃ S1 : Finset (Fin n1), S1.card = t1 ∧ ∀ x1 ∈ S1, ρ1 x1 = some true) ∧ 1 ≤ N1 ρ1) ∨ ∃ y1 : Fin n1, ρ1 y1 = none ∧ N1 (Function.update ρ1 y1 (some false)) + N1 (Function.update ρ1 y1 (some true)) ≤ N1 ρ1)) → (∀ n2 : ℕ, 4 ≤ n2 → ∃ L2 : ℕ, L2 + 2 = Nat.fib ((n2 + 1) / 2 + 4) ∧ (Tr n2 (fun a2 b2 : Fin n2 => (a2.val + 1) % n2 = b2.val ∨ (b2.val + 1) % n2 = a2.val) ((n2 + 1) / 2) (L2) ∧ ∀ m2 : ℕ, Tr n2 (fun a2 b2 : Fin n2 => (a2.val + 1) % n2 = b2.val ∨ (b2.val + 1) % n2 = a2.val) ((n2 + 1) / 2) m2 → L2 ≤ m2)) ∧ (∀ n3 : ℕ, 2 ≤ n3 → ∃ L3 : ℕ, L3 + 2 = Nat.fib (n3 / 2 + 4) ∧ (Tr n3 (fun a3 b3 : Fin n3 => a3.val + 1 = b3.val ∨ b3.val + 1 = a3.val) (n3 / 2) (L3) ∧ ∀ m3 : ℕ, Tr n3 (fun a3 b3 : Fin n3 => a3.val + 1 = b3.val ∨ b3.val + 1 = a3.val) (n3 / 2) m3 → L3 ≤ m3)) ∧ (∀ k4 : ℕ, 1 ≤ k4 → (Tr (2 * k4 + 1) (fun a4 b4 : Fin (2 * k4 + 1) => (a4.val = 0 ∧ 1 ≤ b4.val ∧ b4.val ≤ k4) ∨ (b4.val = 0 ∧ 1 ≤ a4.val ∧ a4.val ≤ k4) ∨ (1 ≤ a4.val ∧ a4.val ≤ k4 ∧ b4.val = a4.val + k4) ∨ (1 ≤ b4.val ∧ b4.val ≤ k4 ∧ a4.val = b4.val + k4)) k4 (2 ^ k4 + k4) ∧ ∀ m4 : ℕ, Tr (2 * k4 + 1) (fun a4 b4 : Fin (2 * k4 + 1) => (a4.val = 0 ∧ 1 ≤ b4.val ∧ b4.val ≤ k4) ∨ (b4.val = 0 ∧ 1 ≤ a4.val ∧ a4.val ≤ k4) ∨ (1 ≤ a4.val ∧ a4.val ≤ k4 ∧ b4.val = a4.val + k4) ∨ (1 ≤ b4.val ∧ b4.val ≤ k4 ∧ a4.val = b4.val + k4)) k4 m4 → 2 ^ k4 + k4 ≤ m4)) ∧ (∀ (n5 : ℕ) (G5 : SimpleGraph (Fin n5)) (t5 : ℕ), (∃ u5 v5 : Fin n5, G5.Adj u5 v5) → (∃ T5 : Finset (Fin n5), T5.card = t5 ∧ ∀ p5 q5 : Fin n5, G5.Adj p5 q5 → p5 ∈ T5 ∨ q5 ∈ T5) → (∀ R5 : Finset (Fin n5), (∀ p6 q6 : Fin n5, G5.Adj p6 q6 → p6 ∈ R5 ∨ q6 ∈ R5) → t5 ≤ R5.card) → ∃ k5 : ℕ, k5 + 1 ≤ 2 ^ (t5 + 1) ∧ Tr n5 G5.Adj t5 k5) ∧ (∀ t6 : ℕ, 1 ≤ t6 → ∃ L6 : ℕ, L6 + 1 = 2 ^ (t6 + 1) ∧ (Tr (2 * t6) (fun a6 b6 : Fin (2 * t6) => a6 ≠ b6 ∧ a6.val / 2 = b6.val / 2) t6 (L6) ∧ ∀ m6 : ℕ, Tr (2 * t6) (fun a6 b6 : Fin (2 * t6) => a6 ≠ b6 ∧ a6.val / 2 = b6.val / 2) t6 m6 → L6 ≤ m6)) := by
  intro Tr spec
  have tr (n : ℕ) (A : Fin n → Fin n → Prop) (t k : ℕ) : Tr n A t k ↔ CoverTree.Tree n A t k :=
    (spec n A t k).trans (CoverTree.tree_iff n A t k).symm
  have formula (r : ℕ) : FibonacciBudget.F r+2=Nat.fib (r+4) :=
    Nat.sub_add_cancel (FibonacciBudget.fib_two r)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro n hn
    let G := LeafGraphs.cycleGraph n (by omega)
    have step (u v : Fin n) (e : u.val+1=v.val) : G.Adj u v :=
      Or.inl (by rw [e,Nat.mod_eq_of_lt v.isLt])
    have wrap : G.Adj (RingUpper.idx n (by omega) (n-1)) (RingUpper.idx n (by omega) 0) := by
      apply Or.inl
      simp only [RingUpper.idx,Nat.zero_mod]
      rw [Nat.mod_eq_of_lt (by omega : n-1<n),show n-1+1=n by omega,Nat.mod_self]
    refine ⟨_,formula _,(tr n G.Adj _ _).mpr (RingUpper.cycle_bound hn G step wrap (LeafGraphs.cycle_minimum n (by omega))),?_⟩
    intro m h
    exact DegreeTwo.lower G (LeafGraphs.cycle_degree n (by omega)) ((tr n G.Adj _ m).mp h)
  · intro n hn
    let G := LeafGraphs.pathGraph n
    refine ⟨_,formula _,(tr n G.Adj _ _).mpr (RingUpper.path_bound hn G (fun _ _ e => Or.inl e) (LeafGraphs.path_minimum n)),?_⟩
    intro m h
    exact DegreeTwo.lower G (LeafGraphs.path_degree n) ((tr n G.Adj _ m).mp h)
  · intro k hk
    obtain ⟨upper,lower⟩ := SpiderTree.exact_spider k hk
    exact ⟨(tr _ _ _ _).mpr upper, fun m h => lower m ((tr _ _ _ _).mp h)⟩
  · intro n G t _ _ minimum
    refine ⟨2^(t+1)-1,?_,(tr _ _ _ _).mpr (CoverTree.all_graphs_upper G minimum)⟩
    have := Nat.two_pow_pos (t+1)
    omega
  · intro t _
    obtain ⟨upper,lower⟩ := MatchingState.exact_matching t
    refine ⟨2^(t+1)-1,?_,(tr _ _ _ _).mpr upper,fun m h => lower m ((tr _ _ _ _).mp h)⟩
    exact Nat.sub_add_cancel (Nat.two_pow_pos _)
