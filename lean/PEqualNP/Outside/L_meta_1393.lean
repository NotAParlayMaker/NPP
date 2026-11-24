import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1393
open Finset (mem_filter mem_sdiff mem_biUnion mem_univ mem_union_left mem_union_right mem_union card_le_card mem_singleton_self singleton_injective mem_insert mem_insert_self mem_insert_of_mem mem_inter mem_Ico mem_product mem_image card_biUnion_le_card_mul card_union_le card_image_le card_image_of_injective card_filter_le one_lt_card card_pos notMem_empty empty_subset filter_subset inter_subset_left inter_subset_right inter_eq_right card_sdiff_add_card_inter length_toList mem_toList card_univ card_product univ Ico card_insert_le exists_subset_card_eq disjoint_left mem_range card_le_one card_eq_one sum_le_sum mem_singleton mem_powersetCard card_powersetCard card_eq_two filter_eq_self not_nonempty_iff_eq_empty card_union_of_disjoint union_subset card_empty card_singleton)
open List (ofFn replicate length_append getD_append getD_eq_default getD_append_right length_cons length_singleton getD_eq_getElem foldl_cons foldl_append length_pos_of_mem mem_iff_getElem mem_toFinset getElem?_eq_getElem)
open Nat (strong_induction_on succ_le_succ add_sub_cancel_left)
open Relation (ReflTransGen)
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (Monotone2)
private abbrev _0 (N:ℕ):=Fin N→ Fin N→ Prop
private abbrev _1:=@Relation.ReflTransGen
private abbrev _2 (N:ℕ):=Finset (Fin N× Fin N)
private abbrev _3 (N:ℕ):=Finset (Fin N)
private abbrev _4:=@DecidableRel
private abbrev _5:=@DecidableEq
private abbrev _6:=@Fintype
private abbrev _7:=@Fin.castAdd
private abbrev _8:=@Fin.natAdd
private abbrev _9:=@congrArg
private abbrev _a:=Circuit
private abbrev _b:=Monotone2
private abbrev _c:=@List.length_append
private abbrev _d:=@List.length_singleton
private abbrev _e:=@List.length_cons
private abbrev _f:=@List.length_replicate
private abbrev _g:=@List.getD_append_right
private abbrev _i:=@List.getD_append
private abbrev _j:=@List.getD_eq_default
private abbrev _k:=@List.getD_eq_getElem
private abbrev _l:=@Finset.card_image_of_injective
private abbrev _m:=@Finset.card_product
private abbrev _n:=@Nat.succ_le_succ
private abbrev _o:=@of_decide_eq_true
private abbrev _r:=@Bool.or_eq_true
private abbrev _s:=@Bool.and_eq_true
private abbrev _t:=@Finset.card_filter_add_card_filter_not
private abbrev _u:=@List.toFinset_card_le
private abbrev _v:=@List.mem_toFinset
private abbrev _w:=@Finset.not_nonempty_iff_eq_empty
private abbrev _x:=@Finset.card_eq_one
private abbrev _y:=@Finset.card_le_one
private abbrev _z:=@Finset.card_sdiff_add_card_inter
private lemma _A {α:Type*} {p:α→ Prop} [DecidablePred p] {s:Finset α} {a:α}:a∈s.filter p→ a∈s∧p a:=Finset.mem_filter.mp
private lemma _B {α:Type*} {p:α→ Prop} [DecidablePred p] {s:Finset α} {a:α}:a∈s∧p a→ a∈s.filter p:=Finset.mem_filter.mpr
private lemma _C {α:Type*} {s t:Finset α}:s⊆t→ s.card≤ t.card:=Finset.card_le_card
private lemma _D {α:Type*} [DecidableEq α] {s:Finset α} (t:Finset α) {a:α}:a∈s→ a∈s∪t:=Finset.mem_union_left t
private lemma _E {α β:Type*} [DecidableEq β] (s:Finset α) (f:α→ Finset β) (k:ℕ):(∀ a∈s,(f a).card≤ k)→(s.biUnion f).card≤ s.card*k:=Finset.card_biUnion_le_card_mul s f k
private lemma _F {α β:Type*} [DecidableEq β] {s:Finset α} {t:α→ Finset β} {b:β}:(∃ a∈s,b∈t a)→ b∈s.biUnion t:=Finset.mem_biUnion.mpr
private lemma _G {α:Type*} [DecidableEq α] (s:Finset α) {t:Finset α} {a:α}:a∈t→ a∈s∪t:=Finset.mem_union_right s
private lemma _H {α:Type*} [Fintype α] (a:α):a∈(Finset.univ:Finset α):=Finset.mem_univ a
private lemma _I {α:Type*} [DecidableEq α] (a:α):a∈({a}:Finset α):=Finset.mem_singleton_self a
private lemma _J {α:Type*} [DecidableEq α] (s t:Finset α):(s∪t).card≤ s.card+t.card:=Finset.card_union_le s t
private lemma _K {α:Type*} [DecidableEq α] (a:α) (s:Finset α):(insert a s).card≤ s.card+1:=Finset.card_insert_le a s
private lemma _L {α:Type*} [DecidableEq α] {a b:α} {s:Finset α}:a∈s→ a∈insert b s:=Finset.mem_insert_of_mem
private lemma _M {α:Type*} [DecidableEq α] {a:α} {s t:Finset α}:a∈s\t→ a∈s∧a∉t:=Finset.mem_sdiff.mp
private lemma _N {α:Type*} {s:Finset α} {n:ℕ}:n≤ s.card→∃ t⊆s,t.card=n:=Finset.exists_subset_card_eq
private lemma _O {P:Prop} {Rg:Decidable P} {α:Sort*} {a b:α} (h:P):(@ite α P Rg a b)=a:=ite_eq_left h
private lemma _P {α:Type*} [DecidableEq α] {a:α} {s t:Finset α}:a∈s∩t→ a∈s∧a∈t:=Finset.mem_inter.mp
private lemma _Q {P:Prop} {Rg:Decidable P} {α:Sort*} {a:P→ α} {b:¬P→ α} (h:P):(@dite α P Rg a b)=a h:=dite_eq_left h
private lemma _R {α β:Type*} {p:α× β} {s:Finset α} {t:Finset β}:p.1∈s∧p.2∈t→ p∈s×ˢ t:=Finset.mem_product.mpr
private lemma _S {α:Type*} [DecidableEq α] (a:α) (s:Finset α):a∈insert a s:=Finset.mem_insert_self a s
private lemma _T {α β:Type*} [DecidableEq β] {s:Finset α} {f:α→ β}:(s.image f).card≤ s.card:=Finset.card_image_le
private lemma _U {α:Type*} {a b:α}:a∈({b}:Finset α)→ a=b:=Finset.mem_singleton.mp
private lemma _V {α:Type*} [DecidableEq α] {a:α} {s t:Finset α}:a∈s∧a∉t→ a∈s\t:=Finset.mem_sdiff.mpr
private lemma _W {α β:Type*} [DecidableEq β] {s:Finset α} {f:α→ β} {b:β}:(∃ a∈s,f a=b)→ b∈s.image f:=Finset.mem_image.mpr
private lemma _X {α:Type*} [DecidableEq α] {a:α} {s t:Finset α}:a∈s∧a∈t→ a∈s∩t:=Finset.mem_inter.mpr
private lemma _Y {α β:Type*} {p:α× β} {s:Finset α} {t:Finset β}:p∈s×ˢ t→ p.1∈s∧p.2∈t:=Finset.mem_product.mp
private lemma _Z {α:Type*} {s:Finset α}:1 < s.card→∃ a∈s,∃ b∈s,a≠b:=Finset.one_lt_card.mp
namespace Mb
lemma jB {α β:Type*} [_5 α] [_5 β] (P:Finset α) (Q:Finset β) (R:α→ β→ Prop) [_4 R] (k:ℕ) (h:∀ p∈P,(Q.filter (R p)).card≤ k):((P.product Q).filter (λ e=>R e.1 e.2)).card≤ P.card*k:=by
 classical
 let rows:α→ Finset (α× β):=λ p=>(Q.filter (R p)).image (λ q=>(p,q));have vR:(P.product Q).filter (λ e=>R e.1 e.2)⊆P.biUnion rows:=by
  intro e he;obtain⟨he,hR⟩:=_A he;obtain⟨hp,hq⟩:=_Y he;apply _F
  refine⟨e.1,hp,?_⟩
  exact _W ⟨e.2,_B ⟨hq,hR⟩,rfl⟩
 calc ((P.product Q).filter (λ e=>R e.1 e.2)).card≤(P.biUnion rows).card:=_C vR
  _≤ ∑ p∈P,(rows p).card:=Finset.card_biUnion_le
  _≤ ∑ _p∈P,k:=by
   apply sum_le_sum
   intro p hp;exact _T.trans (h p hp)
  _=P.card*k:=by simp
lemma kq {α β:Type*} [_5 α] [_5 β] (P:Finset α) (Q:Finset β) (R:α→ β→ Prop) [_4 R] (k:ℕ) (h:∀ q∈Q,(P.filter (λ p=>R p q)).card≤ k):((P.product Q).filter (λ e=>R e.1 e.2)).card≤ Q.card*k:=by
 classical
 let Qs:β→ Finset (α× β):=λ q=>(P.filter (λ p=>R p q)).image (λ p=>(p,q));have vR:(P.product Q).filter (λ e=>R e.1 e.2)⊆Q.biUnion Qs:=by
  intro e he;obtain⟨he,hR⟩:=_A he;obtain⟨hp,hq⟩:=_Y he;apply _F
  refine⟨e.2,hq,?_⟩
  exact _W ⟨e.1,_B ⟨hp,hR⟩,rfl⟩
 calc ((P.product Q).filter (λ e=>R e.1 e.2)).card≤(Q.biUnion Qs).card:=_C vR
  _≤ ∑ q∈Q,(Qs q).card:=Finset.card_biUnion_le
  _≤ ∑ _q∈Q,k:=by
   apply sum_le_sum
   intro q hq;exact _T.trans (h q hq)
  _=Q.card*k:=by simp
lemma kd {α β:Type*} [_5 α] [_5 β] (P:Finset α) (Q:Finset β) (B₁ B₂:α→ β→ Prop) [_4 B₁] [_4 B₂] (h₁:∀ p∈P,(Q.filter (B₁ p)).card≤2) (h₂:∀ q∈Q,(P.filter (λ p=>B₂ p q)).card≤2) (XO:∀ p∈P,∀ q∈Q,B₁ p q∨B₂ p q):P.card*Q.card≤2*P.card+2*Q.card:=by
 classical
 have vR:P.product Q⊆((P.product Q).filter (λ e=>B₁ e.1 e.2))∪((P.product Q).filter (λ e=>B₂ e.1 e.2)):=by
  intro e he;obtain⟨hp,hq⟩:=_Y he;rcases XO e.1 hp e.2 hq with h | h
  · exact _D _ (_B ⟨he,h⟩)
  · exact _G _ (_B ⟨he,h⟩)
 have xV:=_C vR;have hu:=_J
  ((P.product Q).filter (λ e=>B₁ e.1 e.2))
  ((P.product Q).filter (λ e=>B₂ e.1 e.2))
 have hr:=jB P Q B₁ 2 h₁;have hc:=kq P Q B₂ 2 h₂;simp only[Finset.product_eq_sprod,_m] at xV hr hc hu;omega
lemma nw {α β:Type*} [_5 α] [_5 β] (P:Finset α) (Q:Finset β) (B₁ B₂:α→ β→ Prop) [_4 B₁] [_4 B₂] (hP:5≤ P.card) (hQ:5≤ Q.card) (h₁:∀ p∈P,(Q.filter (B₁ p)).card≤2) (h₂:∀ q∈Q,(P.filter (λ p=>B₂ p q)).card≤2):∃ p∈P,∃ q∈Q,¬ B₁ p q∧¬ B₂ p q:=by
 classical
 by_contra hn;have hb:∀ p∈P,∀ q∈Q,B₁ p q∨B₂ p q:=by intro p hp q hq;by_contra h;push Not at h;exact hn ⟨p,hp,q,hq,h⟩
 have xV:=kd P Q B₁ B₂ h₁ h₂ hb;have hP':(5:ℤ)≤ P.card:=by exact_mod_cast hP
 have hQ':(5:ℤ)≤ Q.card:=by exact_mod_cast hQ
 have xV':(P.card:ℤ)*Q.card≤2*P.card+2*Q.card:=by exact_mod_cast xV
 have zA:(0:ℤ)≤((P.card:ℤ)-5)*((Q.card:ℤ)-5):=mul_nonneg (by omega) (by omega);nlinarith
lemma u4 {α β:Type*} [_5 α] [_5 β] (P:Finset α) (Q:Finset β) (gM:α→ Finset β) (gT:β→ Finset α) (hP:5≤ P.card) (hQ:5≤ Q.card) (h₁:∀ p∈P,(gM p).card≤2) (h₂:∀ q∈Q,(gT q).card≤2):∃ p∈P,∃ q∈Q,q∉gM p∧p∉gT q:=by
 apply nw P Q (λ p q=>q∈gM p) (λ p q=>p∈gT q) hP hQ
 · intro p hp;apply le_trans (_C ?_) (h₁ p hp)
   intro q hq;exact (_A hq).2
 · intro q hq;apply le_trans (_C ?_) (h₂ q hq)
   intro p hp;exact (_A hp).2
lemma wY {α β:Type*} [_5 α] [_5 β] (P:Finset α) (Q:Finset β) (gM:α→ Finset β) (gT:β→ Finset α) (h₁:∀ p∈P,(gM p).card≤2) (h₂:∀ q∈Q,(gT q).card≤2) (XO:∀ p∈P,∀ q∈Q,q∈gM p∨p∈gT q):P.card≤4∨Q.card≤4:=by
 classical
 by_contra hn;push Not at hn;obtain⟨p,hp,q,hq,h₁',h₂'⟩:=u4 P Q gM gT (by omega) (by omega) h₁ h₂;exact (XO p hp q hq).elim h₁' h₂'
end Mb
namespace Ma
variable {P L : Type*} [_5 L]
def zT (A:P→ Finset L):Prop:=∀ p q,p≠q→(A p∩A q).card≤1
lemma gR (A:P→ Finset L) (Q:Finset L) (a b p:P) (hQ:Q⊆A a∪A b):Q∩A p⊆(A a∩A p)∪(A b∩A p):=by
 intro l hl;obtain⟨Ja,P3⟩:=_P hl;rcases mem_union.mp (hQ Ja) with nF | pv
 · exact _D _ (_X ⟨nF,P3⟩)
 · exact _G _ (_X ⟨pv,P3⟩)
lemma cR (A:P→ Finset L) (hA:zT A) (Q:Finset L) (a b p:P) (hQ:Q⊆A a∪A b) (hp:3≤(Q∩A p).card):p=a∨p=b:=by
 classical
 by_contra h;push Not at h;have ha:=hA a p (Ne.symm h.1);have hb:=hA b p (Ne.symm h.2);have vR:=_C (gR A Q a b p hQ);have xA:=_J (A a∩A p) (A b∩A p);omega
lemma m5 [_6 P] [_5 P] (A:P→ Finset L) (hA:zT A) (Q:Finset L) (a b:P) (hQ:Q⊆A a∪A b):univ.filter (λ p=>3≤(Q∩A p).card)⊆({a,b}:Finset P):=by
 classical
 intro p hp;have zD:=cR A hA Q a b p hQ (_A hp).2;simpa only[mem_insert,mem_singleton] using zD
lemma fQ [_6 P] (A:P→ Finset L) (hA:zT A) (Q:Finset L) (hQ:∃ a b,Q⊆A a∪A b):(univ.filter (λ p=>3≤(Q∩A p).card)).card≤2:=by
 classical
 obtain⟨a,b,hQ⟩:=hQ;have vR:=_C (m5 A hA Q a b hQ);have fF:({a,b}:Finset P).card≤2:=by exact le_trans (_K a {b}) (by simp)
 omega
lemma q0 (A:P→ Finset L) (Q:Finset L) (p q:P) (hQ:Q⊆A p∪A q):Q.card≤(Q∩A p).card+(Q∩A q).card:=by
 have vR:Q⊆(Q∩A p)∪(Q∩A q):=by
  intro l hl;rcases mem_union.mp (hQ hl) with hp | hq
  · exact _D _ (_X ⟨hl,hp⟩)
  · exact _G _ (_X ⟨hl,hq⟩)
 exact le_trans (_C vR) (_J _ _)
lemma fH (A:P→ Finset L) (Q:Finset L) (p q:P) (yP:5≤ Q.card) (hp:(Q∩A p).card≤2) (hQ:Q⊆A p∪A q):3≤(Q∩A q).card:=by have xV:=q0 A Q p q hQ;omega
noncomputable def xx [_6 P] (A:P→ Finset L) (Q:Finset L):Finset P:=by
 classical
 exact if ∃ a b,Q⊆A a∪A b then univ.filter (λ p=>3≤(Q∩A p).card) else ∅
lemma qS [_6 P] (A:P→ Finset L) (hA:zT A) (Q:Finset L):(xx A Q).card≤2:=by
 classical
 unfold xx;split_ifs with hQ
 · exact fQ A hA Q hQ
 · simp
lemma kk [_6 P] (A:P→ Finset L) (Q:Finset L) (p:P):p∈xx A Q↔(∃ a b,Q⊆A a∪A b)∧3≤(Q∩A p).card:=by
 classical
 unfold xx;split_ifs <;> simp_all
lemma xQ [_6 P] (A:P→ Finset L) (Q:Finset L) (p q:P) (yP:5≤ Q.card) (hp:p∉xx A Q) (hq:q∉xx A Q):∃ l∈Q,l∉A p∧l∉A q:=by
 classical
 by_contra h;push Not at h;have hQ:Q⊆A p∪A q:=by
  intro l hl;rw[mem_union];by_cases P3:l∈A p
  · exact Or.inl P3
  · exact Or.inr (h l hl P3)
 have zs:∃ a b,Q⊆A a∪A b:=⟨p,q,hQ⟩;have Xk:(Q∩A p).card≤2:=by by_contra Xk;exact hp ((kk A Q p).mpr ⟨zs,by omega⟩)
 have Jb:=fH A Q p q yP Xk hQ;exact hq ((kk A Q q).mpr ⟨zs,Jb⟩)
lemma pr [_6 L] (I:P→ L→ Prop) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)):zT (λ p=>univ.filter (I p)):=by
 intro p q W0;rw[_y];intro l hl u hu;by_contra XA;have hl':I p l∧I q l:=by simpa only[mem_inter,mem_filter,_H,true_and] using hl
 have hu':I p u∧I q u:=by simpa only[mem_inter,mem_filter,_H,true_and] using hu
 exact hI p q l u W0 XA ⟨hl'.1,hu'.1,hl'.2,hu'.2⟩
end Ma
namespace Kc
open Finset
variable {P L G : Type*} [_6 P] [_6 L] [_5 P] [_5 L] [_5 G]
def WS (I:P→ L→ Prop) [_4 I] (S:Finset P) (E:Finset (P× L)) (l:L):Finset P:=S.filter λ p=>I p l∧(p,l)∉E
def wg (I:P→ L→ Prop) [_4 I] (gs:Finset G) (S:G→ Finset P) (A:G→ Finset L) (E:Finset (P× L)):Finset (P× L):=univ.filter λ e=>e∉E∧I e.1 e.2∧∃ g∈gs,e.1∈S g∧e.2∈A g∧(A g).card≤4
def pencil (I:P→ L→ Prop) [_4 I] (p:P):Finset L:=univ.filter (I p)
def z8 (I:P→ L→ Prop) [_4 I] (A:Finset L):Prop:=∃ T:Finset P,T.card≤2∧A⊆T.biUnion (pencil I)
def yW (I:P→ L→ Prop) [_4 I] (A:Finset L) (p:P):Prop:=5≤ A.card∧¬(z8 I A∧3≤(A.filter (I p)).card)
noncomputable def xk (I:P→ L→ Prop) [_4 I] (gs:Finset G) (A:G→ Finset L):Finset (P× L):=by
 classical
 exact univ.filter λ e=>I e.1 e.2∧∃ g∈gs,e.2∈A g∧z8 I (A g)∧3≤((A g).filter (I e.1)).card
lemma pU (I:P→ L→ Prop) [_4 I] (gs:Finset G) (S:G→ Finset P) (A:G→ Finset L) (E:Finset (P× L)) (p:P) (l:L) (g:G) (hg:g∈gs) (hp:p∈S g) (hl:l∈A g) (hI:I p l) (hE:(p,l)∉E) (xz:(p,l)∉wg I gs S A E) (bX:(p,l)∉xk I gs A):yW I (A g) p:=by
 classical
 constructor
 · by_contra! hc;apply xz
   exact _B ⟨_H _,hE,hI,g,hg,hp,hl,by omega⟩
 · rintro⟨zs,kp⟩;apply bX
   exact _B ⟨_H _,hI,g,hg,hl,zs,kp⟩
section Network
variable (I : P → L → Prop) [_4 I] (wW vw : Finset ℕ) (vU : ℕ → Finset ℕ) (vu : ℕ → ℕ) (vH yT : ℕ → Finset P) (vk : ℕ → Finset L) (v9 : ℕ → P → Finset L) (yV : ∀ i ∈ wW, ∀ c ∈ vU i, c < i) (yz : ∀ i ∈ vw, vu i < i) (qn : ∀ i ∈ wW, ∀ p, p ∈ yT i ↔ ∃ c ∈ vU i, p ∈ yT c) (uL : ∀ i ∈ vw, ∀ p, p ∈ yT i ↔ p ∈ vH i ∧ (p ∈ yT (vu i) ∨ yW I (vk (vu i)) p)) (mq : ∀ i, i ∉ wW → i ∉ vw → yT i = ∅) (gF : ∀ i ∈ wW, ∀ p l, l ∈ v9 i p ↔ ∃ c ∈ vU i, l ∈ v9 c p) (wB : ∀ i ∈ vw, ∀ p l, l ∈ v9 i p ↔ p ∈ vH i ∧ l ∈ v9 (vu i) p) (mW : ∀ i, i ∉ wW → i ∉ vw → ∀ p, v9 i p = vk i) (cD : ∀ i ∈ wW, ∀ l, l ∈ vk i ↔ ∃ c ∈ vU i, l ∈ vk c) (zm : ∀ i p, vk i ⊆ v9 i p)
include yV yz gF wB mW cD zm in
theorem pH (i:ℕ) (p:P) (l:L) (hl:l∈v9 i p):l∈vk i∨∃ g∈vw,p∈vH g∧l∈vk (vu g)∧vk (vu g)⊆v9 i p:=by
 induction i using strong_induction_on with
 | ind i ih=>
  by_cases wv:i∈wW
  · obtain⟨c,hc,cI⟩:=(gF i wv p l).mp hl;rcases ih c (yV i wv c hc) cI with yi | ⟨g,hg,z1,YW,vR⟩
    · exact Or.inl ((cD i wv l).mpr ⟨c,hc,yi⟩)
    · refine Or.inr ⟨g,hg,z1,YW,?_⟩
      intro u hu;exact (gF i wv p u).mpr ⟨c,hc,vR hu⟩
  · by_cases zJ:i∈vw
    · obtain⟨z1,cI⟩:=(wB i zJ p l).mp hl;rcases ih (vu i) (yz i zJ) cI with yi | ⟨g,hg,V4,YW,vR⟩
      · refine Or.inr ⟨i,zJ,z1,yi,?_⟩
        intro u hu;exact (wB i zJ p u).mpr ⟨z1,zm (vu i) p hu⟩
      · refine Or.inr ⟨g,hg,V4,YW,?_⟩
        intro u hu;exact (wB i zJ p u).mpr ⟨z1,vR hu⟩
    · exact Or.inl (by simpa only[mW i wv zJ p] using hl)
include yV yz qn uL mq gF wB zm in
theorem k3 (i:ℕ) (p:P) (hp:p∈yT i):∃ g∈vw,p∈vH g∧yW I (vk (vu g)) p∧vk (vu g)⊆v9 i p:=by
 induction i using strong_induction_on with
 | ind i ih=>
  by_cases wv:i∈wW
  · obtain⟨c,hc,gn⟩:=(qn i wv p).mp hp;obtain⟨g,hg,z1,xS,vR⟩:=ih c (yV i wv c hc) gn;refine⟨g,hg,z1,xS,?_⟩
    intro l hl;exact (gF i wv p l).mpr ⟨c,hc,vR hl⟩
  · by_cases zJ:i∈vw
    · obtain⟨z1,UF | xS⟩:=(uL i zJ p).mp hp
      · obtain⟨g,hg,V4,xS,vR⟩:=ih (vu i) (yz i zJ) UF;refine⟨g,hg,V4,xS,?_⟩
        intro l hl;exact (wB i zJ p l).mpr ⟨z1,vR hl⟩
      · refine⟨i,zJ,z1,xS,?_⟩
        intro l hl;exact (wB i zJ p l).mpr ⟨z1,zm (vu i) p hl⟩
    · rw[mq i wv zJ] at hp;exact (notMem_empty _ hp).elim
include yV yz qn uL gF wB mW cD in
theorem xB (E:Finset (P× L)) (p:P) (l:L) (hI:I p l) (hE:(p,l)∉E) (xz:(p,l)∉wg I vw vH (λ g=>vk (vu g)) E) (bX:(p,l)∉xk I vw (λ g=>vk (vu g))):∀ i,l∈v9 i p→ l∉vk i→ p∈yT i:=by
 intro i;induction i using strong_induction_on with
 | ind i ih=>
  intro hl yi;by_cases wv:i∈wW
  · obtain⟨c,hc,cI⟩:=(gF i wv p l).mp hl;have WP:l∉vk c:=λ h=>yi ((cD i wv l).mpr ⟨c,hc,h⟩);exact (qn i wv p).mpr ⟨c,hc,ih c (yV i wv c hc) cI WP⟩
  · by_cases zJ:i∈vw
    · obtain⟨z1,cI⟩:=(wB i zJ p l).mp hl;apply (uL i zJ p).mpr
      refine⟨z1,?_⟩
      by_cases WP:l∈vk (vu i)
      · exact Or.inr (pU I vw vH (λ g=>vk (vu g)) E p l i zJ z1 WP hI hE xz bX)
      · exact Or.inl (ih (vu i) (yz i zJ) cI WP)
    · rw[mW i wv zJ p] at hl;exact (yi hl).elim
end Network
end Kc
namespace M6
open Ma
open Mb
variable {Point Line : Type*} [_6 Point] [_5 Line]
def p6 (A:Point→ Finset Line) (l:Line) (P:Finset Point):Finset Point:=P.filter (λ p=>l∉A p)
def pm (A:Point→ Finset Line) (v9:Point→ Finset Line) (p:Point):Prop:=∃ S:Finset Line,5≤ S.card∧p∉xx A S∧S⊆v9 p
lemma u5 (A:Point→ Finset Line) (hA:zT A) (l:Line) (P Q:Finset Point) (gW gC nb p9:Point→ Finset Line) (hP:∀ p∈P,5≤(nb p).card∧p∉xx A (nb p)∧nb p⊆gW p) (hQ:∀ q∈Q,5≤(p9 q).card∧q∉xx A (p9 q)∧p9 q⊆gC q) (vM:∀ p∈P,l∉A p→∀ q∈Q,l∉A q→∀ u∈gW p,∀ v∈gC q,u∉A p→ u∉A q→ v∉A p→ v∉A q→ False):(p6 A l P).card≤4∨(p6 A l Q).card≤4:=by
 classical
 apply wY (p6 A l P) (p6 A l Q) (λ p=>xx A (nb p)) (λ q=>xx A (p9 q))
 · intro p _;exact qS A hA (nb p)
 · intro q _;exact qS A hA (p9 q)
 · intro p hp q hq;obtain⟨U1,bd⟩:=_A hp;obtain⟨SX,ny⟩:=_A hq;obtain⟨TT,Pz,Om⟩:=hP p U1;obtain⟨Tt,Ok,QV⟩:=hQ q SX;by_contra hn;push Not at hn;obtain⟨u,hu,Tz,Lo⟩:=xQ A (nb p) p q TT Pz hn.1;obtain⟨v,hv,NP,Ny⟩:=xQ A (p9 q) q p Tt Ok hn.2;exact vM p U1 bd q SX ny u (Om hu) v (QV hv) Tz Lo Ny NP
lemma nY (A:Point→ Finset Line) (hA:zT A) (l:Line) (P Q:Finset Point) (gW gC:Point→ Finset Line) (hP:∀ p∈P,pm A gW p) (hQ:∀ q∈Q,pm A gC q) (vM:∀ p∈P,l∉A p→∀ q∈Q,l∉A q→∀ u∈gW p,∀ v∈gC q,u∉A p→ u∉A q→ v∉A p→ v∉A q→ False):(p6 A l P).card≤4∨(p6 A l Q).card≤4:=by
 classical
 let nb:Point→ Finset Line:=λ p=>if hp:p∈P then Classical.choose (hP p hp) else ∅;let p9:Point→ Finset Line:=λ q=>if hq:q∈Q then Classical.choose (hQ q hq) else ∅;apply u5 A hA l P Q gW gC nb p9
 · intro p hp;simpa only[nb,_Q hp] using Classical.choose_spec (hP p hp)
 · intro q hq;simpa only[p9,_Q hq] using Classical.choose_spec (hQ q hq)
 · exact vM
lemma ct (A:Point→ Finset Line) (l:Line) (P:Finset Point) (v9:Point→ Finset Line) (hP:∀ p∈P,pm A v9 p) (vM:∀ p∈P,l∉A p→∀ u∈v9 p,u∉A p→ False):∀ p∈P,l∈A p:=by intro p hp;by_contra bd;obtain⟨S,hS,Rb,qk⟩:=hP p hp;obtain⟨u,hu,Tz,_⟩:=xQ A S p p hS Rb Rb;exact vM p hp bd u (qk hu) Tz
open Kc
open Ma
variable {Point Line Gate : Type*} [_6 Point] [_6 Line] [_5 Point] [_5 Line]
omit [_6 Point] in
lemma jS (I:Point→ Line→ Prop) [_4 I] (S:Finset Line) (a b:Point) (h:S⊆pencil I a∪pencil I b):z8 I S:=by
 refine⟨{a,b},?_,?_⟩
 · exact (_K a {b}).trans (by simp)
 · intro l hl;rcases mem_union.mp (h hl) with ha | hb
   · exact _F ⟨a,by simp,ha⟩
   · exact _F ⟨b,by simp,hb⟩
lemma nu (I:Point→ Line→ Prop) [_4 I] (S:Finset Line) (p:Point) (h:yW I S p):p∉xx (pencil I) S:=by
 intro hp;obtain⟨⟨a,b,zs⟩,kp⟩:=(kk (pencil I) S p).mp hp;have zD:S∩pencil I p=S.filter (I p):=by ext l;simp[pencil]
 rw[zD] at kp;exact h.2 ⟨jS I S a b zs,kp⟩
lemma pz (I:Point→ Line→ Prop) [_4 I] (v9:Point→ Finset Line) (p:Point) (S:Finset Line) (h:yW I S p) (vR:S⊆v9 p):pm (pencil I) v9 p:=⟨S,h.1,nu I S p h,vR⟩
lemma zK (I:Point→ Line→ Prop) [_4 I] (vw:Finset Gate) (vH:Gate→ Finset Point) (vX:Gate→ Finset Line) (v9:Point→ Finset Line) (p:Point) (h:∃ g∈vw,p∈vH g∧yW I (vX g) p∧vX g⊆v9 p):pm (pencil I) v9 p:=by obtain⟨g,_,_,xS,vR⟩:=h;exact pz I v9 p (vX g) xS vR
lemma x2 (I:Point→ Line→ Prop) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (l:Line) (P Q:Finset Point) (gW gC:Point→ Finset Line) (vw:Finset Gate) (vH:Gate→ Finset Point) (vX:Gate→ Finset Line) (hP:∀ p∈P,∃ g∈vw,p∈vH g∧yW I (vX g) p∧vX g⊆gW p) (hQ:∀ q∈Q,∃ g∈vw,q∈vH g∧yW I (vX g) q∧vX g⊆gC q) (vM:∀ p∈P,¬ I p l→∀ q∈Q,¬ I q l→∀ u∈gW p,∀ v∈gC q,¬ I p u→¬ I q u→¬ I p v→¬ I q v→ False):(P.filter (λ p=>¬ I p l)).card≤4∨(Q.filter (λ q=>¬ I q l)).card≤4:=by
 have xH:=nY (pencil I) (pr I hI)
  l P Q gW gC
  (λ p hp=>zK I vw vH vX gW p (hP p hp))
  (λ q hq=>zK I vw vH vX gC q (hQ q hq))
  (by
   intro p hp bd q hq ny u hu v hv Tz Lo Ny NP;exact vM p hp (by simpa[pencil] using bd) q hq (by simpa[pencil] using ny) u hu v hv (by simpa[pencil] using Tz) (by simpa[pencil] using Lo) (by simpa[pencil] using Ny) (by simpa[pencil] using NP))
 simpa only[p6,pencil,mem_filter,_H,true_and] using xH
lemma wZ (I:Point→ Line→ Prop) [_4 I] (l:Line) (P:Finset Point) (v9:Point→ Finset Line) (vw:Finset Gate) (vH:Gate→ Finset Point) (vX:Gate→ Finset Line) (hP:∀ p∈P,∃ g∈vw,p∈vH g∧yW I (vX g) p∧vX g⊆v9 p) (vM:∀ p∈P,¬ I p l→∀ u∈v9 p,¬ I p u→ False):∀ p∈P,I p l:=by
 have bE:=ct (pencil I) l P v9
  (λ p hp=>zK I vw vH vX v9 p (hP p hp))
  (by
   intro p hp bd u hu Tz;exact vM p hp (by simpa[pencil] using bd) u hu (by simpa[pencil] using Tz))
 simpa only[pencil,mem_filter,_H,true_and] using bE
variable {Point Line Gate : Type*} [_5 Point] [_5 Line]
def z7 (f:Finset Point→ Finset Line→ Bool):Prop:=∀ X X' Y Y',X⊆X'→ Y⊆Y'→ f X Y=true→ f X' Y'=true
def wq (I:Point→ Line→ Prop) (l:Line) (f g:Finset Point→ Finset Line→ Bool):Prop:=∀ X Y,l∈Y→ f X Y=true→ g X Y=true→∃ p∈X,∃ u∈Y,I p u
lemma u9 (I:Point→ Line→ Prop) (l:Line) (f g:Finset Point→ Finset Line→ Bool) (g5:z7 f) (nX:z7 g) (vM:wq I l f g) (p q:Point) (u v:Line) (hf:f {p} {u}=true) (hg:g {q} {v}=true) (bd:¬ I p l) (ny:¬ I q l) (f4:¬ I p u) (b8:¬ I q u) (SF:¬ I p v) (Na:¬ I q v):False:=by
 have hf':f {p,q} {l,u,v}=true:=g5 {p} {p,q} {u} {l,u,v} (by simp) (by simp) hf;have hg':g {p,q} {l,u,v}=true:=nX {q} {p,q} {v} {l,u,v} (by simp) (by simp) hg;obtain⟨r,hr,s,hs,hI⟩:=vM {p,q} {l,u,v} (by simp) hf' hg';simp only[mem_insert,mem_singleton] at hr hs;rcases hr with rfl | rfl
 · rcases hs with rfl | rfl | rfl
   · exact bd hI
   · exact f4 hI
   · exact SF hI
 · rcases hs with rfl | rfl | rfl
   · exact ny hI
   · exact b8 hI
   · exact Na hI
lemma qf (I:Point→ Line→ Prop) (l:Line) (f g:Finset Point→ Finset Line→ Bool) (g5:z7 f) (nX:z7 g) (vM:wq I l f g) (yi:g ∅ {l}=true) (p:Point) (u:Line) (hf:f {p} {u}=true) (bd:¬ I p l) (f4:¬ I p u):False:=by have hg:g {p} {l}=true:=nX ∅ {p} {l} {l} (by simp) (by simp) yi;exact u9 I l f g g5 nX vM p p u l hf hg bd bd f4 f4 bd bd
lemma x0 [_6 Point] [_6 Line] (I:Point→ Line→ Prop) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (l:Line) (P Q:Finset Point) (gW gC:Point→ Finset Line) (vw:Finset Gate) (vH:Gate→ Finset Point) (vX:Gate→ Finset Line) (hP:∀ p∈P,∃ a∈vw,p∈vH a∧Kc.yW I (vX a) p∧vX a⊆gW p) (hQ:∀ q∈Q,∃ a∈vw,q∈vH a∧Kc.yW I (vX a) q∧vX a⊆gC q) (f g:Finset Point→ Finset Line→ Bool) (g5:z7 f) (nX:z7 g) (vM:wq I l f g) (Ot:∀ p u,u∈gW p→ f {p} {u}=true) (PA:∀ q v,v∈gC q→ g {q} {v}=true):(P.filter (λ p=>¬ I p l)).card≤4∨(Q.filter (λ q=>¬ I q l)).card≤4:=by
 apply x2 I hI l P Q gW gC vw vH vX hP hQ
 intro p _ bd q _ ny u hu v hv f4 b8 SF Na;exact u9 I l f g g5 nX vM p q u v (Ot p u hu) (PA q v hv) bd ny f4 b8 SF Na
lemma zS [_6 Point] [_6 Line] (I:Point→ Line→ Prop) [_4 I] (l:Line) (P:Finset Point) (v9:Point→ Finset Line) (vw:Finset Gate) (vH:Gate→ Finset Point) (vX:Gate→ Finset Line) (hP:∀ p∈P,∃ a∈vw,p∈vH a∧Kc.yW I (vX a) p∧vX a⊆v9 p) (f g:Finset Point→ Finset Line→ Bool) (g5:z7 f) (nX:z7 g) (vM:wq I l f g) (yi:g ∅ {l}=true) (qk:∀ p u,u∈v9 p→ f {p} {u}=true):∀ p∈P,I p l:=by
 apply wZ I l P v9 vw vH vX hP
 intro p _ bd u hu f4;exact qf I l f g g5 nX vM yi p u (qk p u hu) bd f4
end M6
namespace M8
variable {N : ℕ}
def pencil (I:_0 N) [_4 I] (p:Fin N):_3 N:=univ.filter (I p)
lemma pY (I:_0 N) [_4 I] (p l:Fin N):l∈pencil I p↔I p l:=by simp[pencil]
lemma Ze (P A B C:_3 N) (hs:∀ a∈A,∀ b∈B,∀ c∈C,a∈P∨b∈P∨c∈P):A⊆P∨B⊆P∨C⊆P:=by
 classical
 by_contra hn;have OB:=(not_or.mp hn).1;have PJ:=(not_or.mp (not_or.mp hn).2).1;have Ov:=(not_or.mp (not_or.mp hn).2).2;obtain⟨a,ha,S2⟩:=Finset.not_subset.mp OB;obtain⟨b,hb,Nv⟩:=Finset.not_subset.mp PJ;obtain⟨c,hc,RF⟩:=Finset.not_subset.mp Ov;rcases hs a ha b hb c hc with h | h | h
 · exact S2 h
 · exact Nv h
 · exact RF h
lemma k2 (I:_0 N) [_4 I] (p:Fin N) (A:_3 N) (hA:A⊆pencil I p):A.card≤4∨(5≤ A.card∧3≤(A.filter (I p)).card∧∃ T:_3 N,T.card≤2∧∀ l∈A,∃ q∈T,I q l):=by
 classical
 by_cases hs:A.card≤4
 · exact Or.inl hs
 · right
   have ZW:A.filter (I p)=A:=by
    apply filter_eq_self.mpr
    intro l hl;exact (pY I p l).mp (hA hl)
   refine⟨by omega,?_,{p},by simp,?_⟩
   · rw[ZW];omega
   · intro l hl;exact⟨p,_I p,(pY I p l).mp (hA hl)⟩
lemma mz (P A:_3 N) (l:Fin N) (hl:l∈A) (hA:A⊆P):(2≤ A.card∧A⊆P∧l∈A)∨A={l}:=by
 classical
 by_cases YV:2≤ A.card
 · exact Or.inl ⟨YV,hA,hl⟩
 · right
   apply Finset.Subset.antisymm
   · intro a ha;exact mem_singleton.mpr ((_y.mp (by omega:A.card≤1)) a ha l hl)
   · exact Finset.singleton_subset_iff.mpr hl
lemma wL (I:_0 N) [_4 I] (labels:Finset ℕ) (vH vX vk:ℕ→_3 N) (v9:ℕ→ Fin N→_3 N) (yi:∀ r p,vk r⊆v9 r p) (x5:∀ r p l,l∈v9 r p→ l∈vk r∨∃ g∈labels,p∈vH g∧l∈vX g∧vX g⊆v9 r p) (r:ℕ) (p l:Fin N) (hl:l∈v9 r p) (hh:v9 r p⊆pencil I p):(∃ g∈labels,p∈vH g∧l∈vX g∧((vX g).card≤4∨(5≤(vX g).card∧3≤((vX g).filter (I p)).card∧∃ T:_3 N,T.card≤2∧∀ u∈vX g,∃ q∈T,I q u)))∨(2≤(vk r).card∧vk r⊆pencil I p∧l∈vk r)∨vk r={l}:=by
 classical
 rcases x5 r p l hl with hb | ⟨g,hg,hp,hq,vR⟩
 · exact Or.inr (mz (pencil I p) (vk r) l hb (Finset.Subset.trans (yi r p) hh))
 · exact Or.inl ⟨g,hg,hp,hq,k2 I p (vX g) (Finset.Subset.trans vR hh)⟩
lemma jP (I:_0 N) [_4 I] (labels:Finset ℕ) (vH vX vk:ℕ→_3 N) (v9:ℕ→ Fin N→_3 N) (yi:∀ r p,vk r⊆v9 r p) (x5:∀ r p l,l∈v9 r p→ l∈vk r∨∃ g∈labels,p∈vH g∧l∈vX g∧vX g⊆v9 r p) (a b c:ℕ) (p l:Fin N) (ha:l∈v9 a p) (hb:l∈v9 b p) (hc:l∈v9 c p) (hs:∀ u∈v9 a p,∀ v∈v9 b p,∀ w∈v9 c p,I p u∨I p v∨I p w):∃ r∈({a,b,c}:Finset ℕ),(∃ g∈labels,p∈vH g∧l∈vX g∧((vX g).card≤4∨(5≤(vX g).card∧3≤((vX g).filter (I p)).card∧∃ T:_3 N,T.card≤2∧∀ u∈vX g,∃ q∈T,I q u)))∨(2≤(vk r).card∧vk r⊆pencil I p∧l∈vk r)∨vk r={l}:=by
 classical
 have hh:=Ze (pencil I p) (v9 a p) (v9 b p) (v9 c p) (by
  intro u hu v hv w hw;simpa only[pY] using hs u hu v hv w hw)
 rcases hh with hh | hh | hh
 · exact⟨a,by simp,wL I labels vH vX vk v9 yi x5 a p l ha hh⟩
 · exact⟨b,by simp,wL I labels vH vX vk v9 yi x5 b p l hb hh⟩
 · exact⟨c,by simp,wL I labels vH vX vk v9 yi x5 c p l hc hh⟩
lemma pA {K:ℕ} (vk:ℕ→_3 N) (ye:Fin K→ Fin 3→ ℕ):((univ:Finset ((Fin K× Fin 3)× Fin N)).filter (λ x=>vk (ye x.1.1 x.1.2)={x.2})).card≤3*K:=by
 classical
 let k5:=(univ:Finset ((Fin K× Fin 3)× Fin N)).filter
  (λ x=>vk (ye x.1.1 x.1.2)={x.2})
 have xV:k5.card≤(univ:Finset (Fin K× Fin 3)).card:=by
  apply Finset.card_le_card_of_injOn (λ x=>x.1)
  · intro x hx;exact _H _
  · intro x hx y hy XB;change x.1=y.1 at XB;have hx':=(_A hx).2;have hy':=(_A hy).2
    have fY:({x.2}:_3 N)={y.2}:=by rw[← hx',← hy',XB]
    exact Prod.ext XB (singleton_injective fY)
 simpa[k5,Nat.mul_comm] using xV
end M8
namespace K8
open M6
theorem qi {Point Line Gate:Type*} [_6 Point] [_6 Line] [_5 Point] [_5 Line] (I:Point→ Line→ Prop) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (S:ℕ→ Finset Point) (v9:ℕ→ Point→ Finset Line) (vk:ℕ→ Finset Line) (vw:Finset Gate) (vH:Gate→ Finset Point) (vX:Gate→ Finset Line) (x5:∀ r p,p∈S r→∃ g∈vw,p∈vH g∧Kc.yW I (vX g) p∧vX g⊆v9 r p) (F:ℕ→ Finset Point→ Finset Line→ Bool) (xT:∀ r,z7 (F r)) (qk:∀ r p u,u∈v9 r p→ F r {p} {u}=true) (yi:∀ r l,l∈vk r↔F r ∅ {l}=true) (a b:ℕ) (l:Line) (vM:wq I l (F a) (F b)) (E:Finset Point) (VO:l∉vk a→ E⊆S a) (VE:l∉vk b→ E⊆S b):∃ r∈({a,b}:Finset ℕ),((S r).filter (λ p=>¬ I p l)).card≤4∧E⊆S r:=by
 classical
 have TC:¬(l∈vk a∧l∈vk b):=by rintro⟨ha,hb⟩;obtain⟨p,hp,u,hu,f4⟩:=vM ∅ {l} (by simp) ((yi a l).mp ha) ((yi b l).mp hb);exact notMem_empty p hp
 have cT (r:ℕ) (bE:∀ p∈S r,I p l):((S r).filter (λ p=>¬ I p l)).card≤4:=by
  have gV:(S r).filter (λ p=>¬ I p l)=∅:=by
   apply Finset.eq_empty_iff_forall_notMem.mpr
   intro p hp;exact (_A hp).2 (bE p (_A hp).1)
  simp[gV]
 by_cases ha:l∈vk a
 · have bE:∀ p∈S b,I p l:=zS I l (S b) (v9 b) vw vH vX
    (λ p hp=>x5 b p hp) (F b) (F a) (xT b) (xT a)
    (λ X Y hl hb ha'=>vM X Y hl ha' hb)
    ((yi a l).mp ha) (qk b)
   exact⟨b,by simp,cT b bE,VE (λ hb=>TC ⟨ha,hb⟩)⟩
 by_cases hb:l∈vk b
 · have bE:∀ p∈S a,I p l:=zS I l (S a) (v9 a) vw vH vX
    (λ p hp=>x5 a p hp) (F a) (F b) (xT a) (xT b)
    vM ((yi b l).mp hb) (qk a)
   exact⟨a,by simp,cT a bE,VO ha⟩
 have xH:=x0 I hI l (S a) (S b)
  (v9 a) (v9 b) vw vH vX
  (λ p hp=>x5 a p hp) (λ p hp=>x5 b p hp)
  (F a) (F b) (xT a) (xT b) vM (qk a) (qk b)
 rcases xH with h | h
 · exact⟨a,by simp,h,VO ha⟩
 · exact⟨b,by simp,h,VE hb⟩
open M6
def bK (i:Fin 3):Fin 3:=if i=0 then 1 else 0
def b2 (i:Fin 3):Fin 3:=if i=2 then 1 else 2
theorem YT {Point Line:Type*} [_5 Point] [_5 Line] {K:ℕ} (I:Point→ Line→ Prop) (ye:Fin K→ Fin 3→ ℕ) (F:ℕ→ Finset Point→ Finset Line→ Bool) (xT:∀ r,z7 (F r)) (vM:∀ j X Y,(∀ i:Fin 3,F (ye j i) X Y=true)→∃ p∈X,∃ l∈Y,I p l) (v9:ℕ→ Point→ Finset Line) (qk:∀ r p l,l∈v9 r p→ F r {p} {l}=true) (j:Fin K) (p:Point) (u v w:Line) (hu:u∈v9 (ye j 0) p) (hv:v∈v9 (ye j 1) p) (hw:w∈v9 (ye j 2) p):I p u∨I p v∨I p w:=by
 have h0:F (ye j 0) {p} {u,v,w}=true:=xT (ye j 0) {p} {p} {u} {u,v,w} (by simp) (by simp)
  (qk (ye j 0) p u hu)
 have h1:F (ye j 1) {p} {u,v,w}=true:=xT (ye j 1) {p} {p} {v} {u,v,w} (by simp) (by simp)
  (qk (ye j 1) p v hv)
 have h2:F (ye j 2) {p} {u,v,w}=true:=xT (ye j 2) {p} {p} {w} {u,v,w} (by simp) (by simp)
  (qk (ye j 2) p w hw)
 have cn:∀ i:Fin 3,F (ye j i) {p} {u,v,w}=true:=by
  intro i;fin_cases i
  · exact h0
  · exact h1
  · exact h2
 obtain⟨q,hq,l,hl,hI⟩:=vM j {p} {u,v,w} cn;have LC:q=p:=_U hq;subst q;simp only[mem_insert,mem_singleton] at hl;rcases hl with rfl | rfl | rfl
 · exact Or.inl hI
 · exact Or.inr (Or.inl hI)
 · exact Or.inr (Or.inr hI)
theorem ju {Point Line:Type*} [_5 Point] [_5 Line] {K:ℕ} (I:Point→ Line→ Prop) (ye:Fin K→ Fin 3→ ℕ) (F:ℕ→ Finset Point→ Finset Line→ Bool) (xT:∀ r,z7 (F r)) (vM:∀ j X Y,(∀ i:Fin 3,F (ye j i) X Y=true)→∃ p∈X,∃ l∈Y,I p l) (vk:ℕ→ Finset Line) (yi:∀ r l,l∈vk r↔F r ∅ {l}=true) (j:Fin K) (i:Fin 3) (l:Line) (hl:l∈vk (ye j i)):wq I l (F (ye j (bK i))) (F (ye j (b2 i))):=by
 intro X Y Ko ha hb;have hm:F (ye j i) X Y=true:=xT (ye j i) ∅ X {l} Y (by simp)
  (Finset.singleton_subset_iff.mpr Ko) ((yi (ye j i) l).mp hl)
 apply vM j X Y
 intro t;fin_cases i <;> fin_cases t <;> simp_all [bK,b2]
theorem me {Point Line:Type*} [_5 Point] [_5 Line] {K:ℕ} (I:Point→ Line→ Prop) (ye:Fin K→ Fin 3→ ℕ) (F:ℕ→ Finset Point→ Finset Line→ Bool) (xT:∀ r,z7 (F r)) (vM:∀ j X Y,(∀ i:Fin 3,F (ye j i) X Y=true)→∃ p∈X,∃ l∈Y,I p l) (vk:ℕ→ Finset Line) (yi:∀ r l,l∈vk r↔F r ∅ {l}=true) (j:Fin K) (i:Fin 3) (l:Line) (Vr:vk (ye j i)={l}):wq I l (F (ye j (bK i))) (F (ye j (b2 i))):=by
 apply ju I ye F xT vM vk yi j i l
 simp[Vr]
theorem nn {N K:ℕ} (I:_0 N) [_4 I] (labels:Finset ℕ) (vH vX vk:ℕ→_3 N) (v9:ℕ→ Fin N→_3 N) (ye:Fin K→ Fin 3→ ℕ) (F B:_2 N) (yi:∀ r p,vk r⊆v9 r p) (x5:∀ r p l,l∈v9 r p→ l∈vk r∨∃ g∈labels,p∈vH g∧l∈vX g∧vX g⊆v9 r p) (yP:∀ r p l,2≤(vk r).card→(∀ u∈vk r,I p u)→ l∈vk r→(p,l)∈B) (vM:∀ j p,∀ u∈v9 (ye j 0) p,∀ v∈v9 (ye j 1) p,∀ w∈v9 (ye j 2) p,I p u∨I p v∨I p w) (p l:Fin N) (hI:I p l) (hc:∃ j,∀ i,l∈v9 (ye j i) p) (hF:(p,l)∉F) (xz:(p,l)∉Kc.wg I labels vH vX F) (bX:(p,l)∉Kc.xk I labels vX) (hB:(p,l)∉B):∃ j i,vk (ye j i)={l}∧∀ t,l∈v9 (ye j t) p:=by
 classical
 obtain⟨j,hj⟩:=hc;obtain⟨r,hr,hs | hb | fY⟩:=M8.jP I labels vH vX vk v9 yi x5 (ye j 0) (ye j 1) (ye j 2) p l (hj 0) (hj 1) (hj 2) (vM j p)
 · obtain⟨g,hg,hp,hl,xV | ⟨_,kp,T,hT,zs⟩⟩:=hs
   · exact (xz (_B ⟨_H _,hF,hI,g,hg,hp,hl,xV⟩)).elim
   · apply (bX _).elim
     apply _B
     refine⟨_H _,hI,g,hg,hl,?_,kp⟩
     refine⟨T,hT,?_⟩
     intro u hu;obtain⟨q,hq,b8⟩:=zs u hu;exact _F ⟨q,hq,by simpa[Kc.pencil] using b8⟩
 · exact (hB (yP r p l hb.1 (λ u hu=>(M8.pY I p u).mp (hb.2.1 hu)) hb.2.2)).elim
 · simp only[mem_insert,mem_singleton] at hr;rcases hr with rfl | rfl | rfl
   · exact⟨j,0,fY,hj⟩
   · exact⟨j,1,fY,hj⟩
   · exact⟨j,2,fY,hj⟩
end K8
namespace M2
abbrev vg:=List ℕ ⊕ (ℕ× ℕ)
def step (labels:ℕ→ Bool) (w:List Bool):vg→ Bool
 | Sum.inl rs=>(rs.map λ r=>w.getD r false).any id
 | Sum.inr (a,r)=>labels a && w.getD r false
def run (gs:List vg) (labels:ℕ→ Bool) (y:List Bool):List Bool:=gs.foldl (λ w g=>w ++ [step labels w g]) y
lemma xU (g:vg) (gs:List vg) (labels:ℕ→ Bool) (y:List Bool):run (g :: gs) labels y=run gs labels (y ++ [step labels y g]):=rfl
lemma na (gs hs:List vg) (labels:ℕ→ Bool) (y:List Bool):run (gs ++ hs) labels y=run hs labels (run gs labels y):=by simp[run,foldl_append]
lemma bJ (gs:List vg) (labels:ℕ→ Bool):∀ y:List Bool,∃ t,run gs labels y=y ++ t∧t.length=gs.length:=by
 induction gs with
 | nil=>intro y;exact⟨[],by simp[run],rfl⟩
 | cons g gs ih=>
  intro y;obtain⟨t,ht,hl⟩:=ih (y ++ [step labels y g]);refine⟨step labels y g :: t,?_,by simp[hl]⟩
  rw[xU,ht];simp
lemma zv (gs:List vg) (labels:ℕ→ Bool) (y:List Bool):(run gs labels y).length=y.length+gs.length:=by obtain⟨t,ht,hl⟩:=bJ gs labels y;simp[ht,hl]
lemma zr (gs:List vg) (labels:ℕ→ Bool) (y:List Bool) (w:ℕ) (hw:w < y.length):(run gs labels y).getD w false=y.getD w false:=by obtain⟨t,ht,_⟩:=bJ gs labels y;rw[ht,_i _ _ _ _ hw]
lemma c8 (gs:List vg) (g:vg) (labels:ℕ→ Bool) (y:List Bool):run (gs ++ [g]) labels y=run gs labels y ++ [step labels (run gs labels y) g]:=by simp[run,foldl_append]
lemma kL (gs:List vg) (g:vg) (labels:ℕ→ Bool) (y:List Bool) (w:ℕ) (hw:w < y.length+gs.length):(run (gs ++ [g]) labels y).getD w false=(run gs labels y).getD w false:=by rw[c8,_i _ _ _ _ (by simpa only[zv] using hw)]
lemma wN (gs:List vg) (g:vg) (labels:ℕ→ Bool) (y:List Bool):(run (gs ++ [g]) labels y).getD (y.length+gs.length) false=step labels (run gs labels y) g:=by rw[c8,_g _ _ _ _ (by simp[zv])];simp[zv]
def ut {n:ℕ} (labels:ℕ→ Bool) (w:List (Finset (Fin n))):vg→ Finset (Fin n)
 | Sum.inl rs=>rs.toFinset.biUnion λ r=>w.getD r ∅
 | Sum.inr (a,r)=>if labels a then w.getD r ∅ else ∅
def yU {n:ℕ} (gs:List vg) (labels:ℕ→ Bool) (w:List (Finset (Fin n))):List (Finset (Fin n)):=gs.foldl (λ w g=>w ++ [ut labels w g]) w
noncomputable def pD {n:ℕ} (y:Fin n→ Bool) (S:Finset (Fin n)):Bool:=S.toList.any y
lemma pc {n:ℕ} (y:Fin n→ Bool) (S:Finset (Fin n)):pD y S=true↔∃ l∈S,y l=true:=by simp[pD]
@[local simp] lemma hits_empty {n : ℕ} (y : Fin n → Bool) : pD y ∅ = false := by simp [pD]
@[local simp] lemma bb {n : ℕ} (y : Fin n → Bool) (l : Fin n) : pD y {l} = y l := by
 apply Bool.eq_iff_iff.mpr
 simp[pc]
lemma kK {n:ℕ} (y:Fin n→ Bool) (w:List (Finset (Fin n))) (r:ℕ):(w.map (pD y)).getD r false=pD y (w.getD r ∅):=by
 induction w generalizing r with
 | nil=>simp
 | cons S w ih=>
  cases r with
  | zero=>rfl
  | succ r=>exact ih r
lemma b4 {n:ℕ} (labels:ℕ→ Bool) (y:Fin n→ Bool) (w:List (Finset (Fin n))) (g:vg):pD y (ut labels w g)=step labels (w.map (pD y)) g:=by
 apply Bool.eq_iff_iff.mpr
 cases g with
 | inl rs=>
  simp only[ut,step,pc,mem_biUnion,_v,List.any_eq_true,List.mem_map,id_eq];constructor
  · rintro⟨l,⟨r,hr,hl⟩,hy⟩;refine⟨(w.map (pD y)).getD r false,⟨r,hr,rfl⟩,?_⟩
    rw[kK];exact (pc y _).mpr ⟨l,hl,hy⟩
  · rintro⟨b,⟨r,hr,rfl⟩,hb⟩;rw[kK] at hb;obtain⟨l,hl,hy⟩:=(pc y _).mp hb;exact⟨l,⟨r,hr,hl⟩,hy⟩
 | inr ar=>
  rcases ar with ⟨a,r⟩
  cases ha:labels a with
  | false=>simp[ut,step,ha]
  | true=>
   change pD y (if labels a then w.getD r ∅ else ∅)=true↔(labels a && (w.map (pD y)).getD r false)=true;rw[ha];simp only[Bool.true_and,ite_true];rw[kK]
lemma YR {n:ℕ} (gs:List vg) (labels:ℕ→ Bool) (y:Fin n→ Bool) (w:List (Finset (Fin n))):run gs labels (w.map (pD y))=(yU gs labels w).map (pD y):=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih=>
  change run gs labels (w.map (pD y) ++ [step labels (w.map (pD y)) g])=(yU gs labels (w ++ [ut labels w g])).map (pD y);rw[← b4];simpa only[List.map_append,List.map_singleton] using ih (w ++ [ut labels w g])
def uV {n:ℕ} (gs:List vg) (labels:ℕ→ Bool):List (Finset (Fin n)):=yU gs labels (ofFn λ l:Fin n=>{l})
lemma fD {n:ℕ} (gs:List vg) (labels:ℕ→ Bool) (y:Fin n→ Bool):run gs labels (ofFn y)=(uV gs labels).map (pD y):=by have h:=YR gs labels y (ofFn λ l:Fin n=>{l});simpa only[uV,List.map_ofFn,Function.comp_def,bb] using h
lemma Wr {n:ℕ} (gs:List vg) (labels:ℕ→ Bool) (y:Fin n→ Bool) (w:ℕ):(run gs labels (ofFn y)).getD w false=pD y ((uV gs labels).getD w ∅):=by rw[fD,kK]
lemma xY {n:ℕ} (gs:List vg) (labels:ℕ→ Bool) (y:Fin n→ Bool) (w:ℕ):(run gs labels (ofFn y)).getD w false=true↔∃ l∈(uV gs labels).getD w ∅,y l=true:=by rw[Wr,pc]
lemma y4 {n:ℕ} (gs:List vg) (labels:ℕ→ Bool) (l:Fin n) (w:ℕ):(run gs labels (ofFn λ t=>decide (t=l))).getD w false=true↔l∈(uV gs labels).getD w ∅:=by rw[xY];simp
lemma uj {u v:List Bool} (h:List.Forall₂ (λ a b=>a=true→ b=true) u v) (r:ℕ):u.getD r false=true→ v.getD r false=true:=by
 induction h generalizing r with
 | nil=>simp
 | cons fP ZD ih=>
  cases r with
  | zero=>exact fP
  | succ r=>exact ih r
lemma gY (L L':ℕ→ Bool) (hL:∀ a,L a=true→ L' a=true) {u v:List Bool} (ZD:List.Forall₂ (λ a b=>a=true→ b=true) u v) (g:vg):step L u g=true→ step L' v g=true:=by
 cases g with
 | inl rs=>
  simp only[step,List.any_eq_true,List.mem_map,id_eq];rintro⟨b,⟨r,hr,rfl⟩,hb⟩;exact⟨_,⟨r,hr,rfl⟩,uj ZD r hb⟩
 | inr ar=>
  rcases ar with ⟨a,r⟩
  simp only[step,_s];exact λ h=>⟨hL a h.1,uj ZD r h.2⟩
lemma dv (gs:List vg) (L L':ℕ→ Bool) (hL:∀ a,L a=true→ L' a=true) {u v:List Bool} (ZD:List.Forall₂ (λ a b=>a=true→ b=true) u v):List.Forall₂ (λ a b=>a=true→ b=true) (run gs L u) (run gs L' v):=by
 induction gs generalizing u v with
 | nil=>exact ZD
 | cons g gs ih=>
  change List.Forall₂ (λ a b=>a=true→ b=true) (run gs L (u ++ [step L u g])) (run gs L' (v ++ [step L' v g]));exact ih (List.rel_append ZD (.cons (gY L L' hL ZD g) .nil))
lemma ze {n:ℕ} (gs:List vg) (L L':ℕ→ Bool) (hL:∀ a,L a=true→ L' a=true) (y y':Fin n→ Bool) (hy:∀ l,y l=true→ y' l=true) (r:ℕ):(run gs L (ofFn y)).getD r false=true→(run gs L' (ofFn y')).getD r false=true:=by
 apply uj (dv gs L L' hL ?_) r
 apply List.forall₂_iff_get.mpr
 refine⟨by simp,?_⟩
 intro i hi hi';simpa using hy ⟨i,by simpa using hi⟩
noncomputable def vB {n:ℕ} (I:Fin n→ Fin n→ Prop) (S:Finset (Fin n)) (p:Fin n):Bool:=by
 classical
 exact decide (∀ l∈S,¬ I p l)
def xZ {n:ℕ} (L:ℕ→(Fin n→ Bool)→ Bool):Prop:=∀ a x x',(∀ p,x p=true→ x' p=true)→ L a x=true→ L a x'=true
def qz {n:ℕ} (I:Fin n→ Fin n→ Prop) (gs:List vg) (L:ℕ→(Fin n→ Bool)→ Bool) (r0 r1 r2:ℕ):Prop:=∀ x y:Fin n→ Bool,(run gs (λ a=>L a x) (ofFn y)).getD r0 false=true→(run gs (λ a=>L a x) (ofFn y)).getD r1 false=true→(run gs (λ a=>L a x) (ofFn y)).getD r2 false=true→∃ p l,I p l∧x p=true∧y l=true
end M2
namespace Kd
open M2
open Kc
def vX {N:ℕ} (gs:List vg) (labels:ℕ→ Bool) (w:ℕ):_3 N:=(uV gs labels).getD w ∅
def gateAt (gs:List vg) (N w:ℕ):vg:=gs.getD (w-N) (Sum.inl [])
def mO {N:ℕ} (labels:ℕ→ Bool) (u1:ℕ→_3 N):vg→_3 N
 | .inl rs=>rs.toFinset.biUnion u1
 | .inr (a,r)=>if labels a then u1 r else ∅
lemma qI {N:ℕ} (g:vg) (gs:List vg) (labels:ℕ→ Bool) (w:List (_3 N)):yU (g :: gs) labels w=yU gs labels (w ++ [ut labels w g]):=rfl
lemma k9 {N:ℕ} (gs:List vg) (labels:ℕ→ Bool) (w:List (_3 N)):(yU gs labels w).length=w.length+gs.length:=by
 induction gs generalizing w with
 | nil=>simp[yU]
 | cons g gs ih=>rw[qI,ih];simp;omega
lemma kE {N:ℕ} (gs:List vg) (labels:ℕ→ Bool) (w:List (_3 N)) (r:ℕ) (hr:r < w.length):(yU gs labels w).getD r ∅=w.getD r ∅:=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih=>
  rw[qI,ih _ (by simp;omega),_i _ _ _ _ hr]
lemma bq {N:ℕ} (gs:List vg) (labels:ℕ→ Bool) (w:List (_3 N)) (j:ℕ):yU gs labels w=yU (gs.drop j) labels (yU (gs.take j) labels w):=by simpa only[yU,foldl_append] using _9 (λ hs:List vg=>yU hs labels w) (List.take_append_drop j gs).symm
lemma kU {N:ℕ} (gs:List vg) (labels:ℕ→ Bool) (p:Fin N):vX gs labels p={p}:=by unfold vX uV;rw[kE _ _ _ _ (by simp),_k _ _ (by simp)];simp
lemma wV {N:ℕ} (gs:List vg) (labels:ℕ→ Bool) (w:ℕ) (hw:N+gs.length≤ w):vX (N:=N) gs labels w=∅:=by unfold vX uV;exact _j _ _ (by simpa[k9] using hw)
lemma g1 {N:ℕ} (gs:List vg) (labels:ℕ→ Bool) (w:ℕ) (hn:N≤ w) (hw:w < N+gs.length):vX gs labels w=mO labels (λ r=>if r < w then vX (N:=N) gs labels r else ∅) (gateAt gs N w):=by
 let j:=w-N;have hj:j < gs.length:=by dsimp[j];omega
 let g:=gs[j];let vC:List (_3 N):=ofFn λ l:Fin N=>{l};let earlier:=yU (gs.take j) labels vC;have g4:earlier.length=w:=by simp[earlier,vC,k9,Nat.min_eq_left hj.le,j];omega
 have split:yU gs labels vC=yU (g :: gs.drop (j+1)) labels earlier:=by rw[bq gs labels vC j,List.drop_eq_getElem_cons hj]
 have u1 (r:ℕ):earlier.getD r ∅=if r < w then vX (N:=N) gs labels r else ∅:=by
  by_cases hr:r < w
  · rw[_O hr];change earlier.getD r ∅=(yU gs labels vC).getD r ∅;rw[split];exact (kE _ labels earlier r (by simpa only[g4] using hr)).symm
  · rw[ite_eq_right hr];exact _j _ _ (by omega)
 have hg:gateAt gs N w=g:=_k _ _ hj;rw[hg];change (yU gs labels vC).getD w ∅=_;rw[split,qI,kE _ _ _ _ (by simp[g4]),_g _ _ _ _ (by omega)];simp only[g4,Nat.sub_self,List.getD_cons_zero];cases g <;> simp only[ut,mO,u1]
lemma pK (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (N:ℕ):gateAt gs N N=Sum.inl []:=by
 cases gs with
 | nil=>simp at vK
 | cons g gs=>
  have hg:g=Sum.inl []:=by simpa using vK
  simp[gateAt,hg]
lemma qQ (gs:List vg) (vK:gs.head?=some (Sum.inl [])):0 < gs.length:=by cases gs <;> simp_all
lemma q1 {N:ℕ} (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (labels:ℕ→ Bool):vX (N:=N) gs labels N=∅:=by
 rw[g1 gs labels N (by omega) (by have:=qQ gs vK;omega),pK gs vK N]
 simp[mO]
def Yi (α:ℕ→ Bool):vg→ Prop
 | .inl _=>True
 | .inr (a,_)=>α a=true
def wE (α:ℕ→ Bool):vg→ Prop
 | .inl _=>False
 | .inr (a,_)=>α a=false
noncomputable def wW (gs:List vg) (N:ℕ) (α:ℕ→ Bool):Finset ℕ:=by
 classical
 exact (Ico N (N+gs.length)).filter λ w=>Yi α (gateAt gs N w)
noncomputable def vw (gs:List vg) (N:ℕ) (α:ℕ→ Bool):Finset ℕ:=by
 classical
 exact (Ico N (N+gs.length)).filter λ w=>wE α (gateAt gs N w)
def j2 (N w r:ℕ):ℕ:=if r < w then r else N
def vu (gs:List vg) (N w:ℕ):ℕ:=match gateAt gs N w with
 | .inl _=>N
 | .inr (_,r)=>j2 N w r
def yk (gs:List vg) (N w:ℕ):ℕ:=match gateAt gs N w with
 | .inl _=>0
 | .inr (a,_)=>a
def vU (gs:List vg) (N w:ℕ):Finset ℕ:=match gateAt gs N w with
 | .inl rs=>rs.toFinset.filter (· < w)
 | .inr (_,r)=>{j2 N w r}
lemma jR (gs:List vg) (N w:ℕ) (hn:N≤ w) (hw:w < N+gs.length):gateAt gs N w∈gs:=by
 have hj:w-N < gs.length:=by omega
 rw[gateAt,_k _ _ hj];exact List.getElem_mem _
lemma qA (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (N w a r:ℕ) (hn:N≤ w) (v7:gateAt gs N w=Sum.inr (a,r)):N < w:=by
 by_contra h;have zD:w=N:=by omega
 rw[zD,pK gs vK N] at v7;contradiction
lemma dT (N w r:ℕ) (h:N < w):j2 N w r < w:=by unfold j2;split_ifs <;> omega
lemma dU {N:ℕ} (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (labels:ℕ→ Bool) (w r:ℕ):vX (N:=N) gs labels (j2 N w r)=if r < w then vX gs labels r else ∅:=by
 unfold j2;split_ifs
 · rfl
 · exact q1 gs vK labels
lemma yV (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (N:ℕ) (α:ℕ→ Bool):∀ w∈wW gs N α,∀ c∈vU gs N w,c < w:=by
 classical
 intro w hw c hc;obtain⟨Z9,_⟩:=_A hw;have g7:=(mem_Ico.mp Z9).1;cases v7:gateAt gs N w with
 | inl rs=>
  have hc':c∈rs.toFinset.filter (· < w):=by simpa only[vU,v7] using hc
  exact (_A hc').2
 | inr ar=>
  rcases ar with ⟨a,r⟩
  have Xc:c=j2 N w r:=by simpa only[vU,v7,mem_singleton] using hc
  rw[Xc];exact dT N w r (qA gs vK N w a r g7 v7)
lemma yz (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (N:ℕ) (α:ℕ→ Bool):∀ w∈vw gs N α,vu gs N w < w:=by
 classical
 intro w hw;obtain⟨Z9,mI⟩:=_A hw;have g7:=(mem_Ico.mp Z9).1;cases v7:gateAt gs N w with
 | inl rs=>simp[wE,v7] at mI
 | inr ar=>
  rcases ar with ⟨a,r⟩
  simp only[vu,v7];exact dT N w r (qA gs vK N w a r g7 v7)
lemma wl (gs:List vg) (N:ℕ) (α:ℕ→ Bool):Disjoint (wW gs N α) (vw gs N α):=by
 classical
 apply disjoint_left.mpr
 intro w ho hl;have ho':=(_A ho).2;have hl':=(_A hl).2;cases v7:gateAt gs N w with
 | inl rs=>simp[wE,v7] at hl'
 | inr ar=>
  rcases ar with ⟨a,r⟩
  simp only[Yi,v7] at ho';simp only[wE,v7] at hl';rw[ho'] at hl';contradiction
lemma uG (gs:List vg) (N:ℕ) (α:ℕ→ Bool) (w:ℕ) (hw:w∈Ico N (N+gs.length)):w∈wW gs N α∨w∈vw gs N α:=by
 classical
 cases v7:gateAt gs N w with
 | inl rs=>exact Or.inl (_B ⟨hw,by simp[Yi,v7]⟩)
 | inr ar=>
  rcases ar with ⟨a,r⟩
  cases ha:α a
  · exact Or.inr (_B ⟨hw,by simp[wE,v7,ha]⟩)
  · exact Or.inl (_B ⟨hw,by simp[Yi,v7,ha]⟩)
lemma dt (gs:List vg) (N:ℕ) (α:ℕ→ Bool) (RC:∀ rs,Sum.inl rs∈gs→ rs.length≤2):∀ w∈wW gs N α,(vU gs N w).card≤2:=by
 classical
 intro w hw;obtain⟨Z9,_⟩:=_A hw;obtain⟨g7,kJ⟩:=mem_Ico.mp Z9;cases v7:gateAt gs N w with
 | inl rs=>
  have y5:=RC rs (by simpa only[v7] using jR gs N w g7 kJ);simp only[vU,v7];exact (card_filter_le _ _).trans ((_u _).trans y5)
 | inr ar=>simp[vU,v7]
lemma dX {N:ℕ} (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α β:ℕ→ Bool) (hαβ:∀ a,α a=true→ β a=true) (w:ℕ) (hw:w∈wW gs N α):vX gs β w=(vU gs N w).biUnion (vX (N:=N) gs β):=by
 classical
 obtain⟨Z9,mI⟩:=_A hw;obtain⟨g7,kJ⟩:=mem_Ico.mp Z9;rw[g1 gs β w g7 kJ];cases v7:gateAt gs N w with
 | inl rs=>
  simp only[mO,vU,v7];ext l;simp only[mem_biUnion,mem_filter];constructor
  · rintro⟨r,hr,hl⟩;by_cases b7:r < w
    · exact⟨r,⟨hr,b7⟩,by simpa only[_O b7] using hl⟩
    · simp[b7] at hl
  · rintro⟨r,⟨hr,b7⟩,hl⟩;exact⟨r,hr,by simpa only[_O b7] using hl⟩
 | inr ar=>
  rcases ar with ⟨a,r⟩
  have ha:α a=true:=by simpa only[Yi,v7] using mI
  have hb:=hαβ a ha;simp only[mO,hb,ite_true,vU,v7,Finset.singleton_biUnion];exact (dU gs vK β w r).symm
lemma mj {N:ℕ} (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α β:ℕ→ Bool) (w:ℕ) (hw:w∈vw gs N α):vX (N:=N) gs β w=if β (yk gs N w) then vX gs β (vu gs N w) else ∅:=by
 classical
 obtain⟨Z9,mI⟩:=_A hw;obtain⟨g7,kJ⟩:=mem_Ico.mp Z9;rw[g1 gs β w g7 kJ];cases v7:gateAt gs N w with
 | inl rs=>simp[wE,v7] at mI
 | inr ar=>
  rcases ar with ⟨a,r⟩
  simp only[mO,yk,vu,v7];rw[dU gs vK β w r]
lemma bz {N:ℕ} (gs:List vg) (α β γ:ℕ→ Bool) (w:ℕ) (wv:w∉wW gs N α) (x1:w∉vw gs N α):vX (N:=N) gs β w=vX gs γ w:=by
 by_cases g7:w < N
 · exact (kU gs β ⟨w,g7⟩).trans (kU gs γ ⟨w,g7⟩).symm
 · have kJ:N+gs.length≤ w:=by
    by_contra h;rcases uG gs N α w (mem_Ico.mpr ⟨by omega,by omega⟩) with ho | hl
    · exact wv ho
    · exact x1 hl
   rw[wV gs β w kJ,wV gs γ w kJ]
lemma XD {N:ℕ} (gs:List vg) (α β:ℕ→ Bool) (h:∀ a,α a=true→ β a=true) (w:ℕ):vX (N:=N) gs α w⊆vX gs β w:=by
 intro l hl;have hv:=(y4 gs α l w).mpr hl;have hm:=ze gs α β h (λ t=>decide (t=l))
  (λ t=>decide (t=l)) (λ _=>id) w hv
 exact (y4 gs β l w).mp hm
def vk {N:ℕ} (gs:List vg) (α:ℕ→ Bool):ℕ→_3 N:=vX gs α
def v9 {N:ℕ} (gs:List vg) (L:ℕ→(Fin N→ Bool)→ Bool) (w:ℕ) (p:Fin N):_3 N:=vX gs (λ a=>L a (λ q=>decide (q=p))) w
def vH {N:ℕ} (gs:List vg) (L:ℕ→(Fin N→ Bool)→ Bool) (w:ℕ):_3 N:=univ.filter λ p=>L (yk gs N w) (λ q=>decide (q=p))=true
lemma xg {N:ℕ} (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (w:ℕ) (hw:w∈wW gs N α) (l:Fin N):l∈vk gs α w↔∃ c∈vU gs N w,l∈vk gs α c:=by change l∈vX gs α w↔_;rw[dX gs vK α α (λ _=>id) w hw];exact mem_biUnion
lemma jK {N:ℕ} (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (hα:∀ a x,α a=true→ L a x=true) (w:ℕ) (hw:w∈wW gs N α) (p l:Fin N):l∈v9 gs L w p↔∃ c∈vU gs N w,l∈v9 gs L c p:=by change l∈vX gs (λ a=>L a (λ q=>decide (q=p))) w↔_;rw[dX gs vK α _ (λ a=>hα a _) w hw];exact mem_biUnion
lemma xW {N:ℕ} (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (w:ℕ) (hw:w∈vw gs N α) (p l:Fin N):l∈v9 gs L w p↔p∈vH gs L w∧l∈v9 gs L (vu gs N w) p:=by
 change l∈vX gs (λ a=>L a (λ q=>decide (q=p))) w↔_;rw[mj gs vK α _ w hw];by_cases h:L (yk gs N w) (λ q=>decide (q=p))=true
 · simp[h,vH,v9]
 · simp[h,vH,v9]
lemma qN {N:ℕ} (gs:List vg) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (w:ℕ) (wv:w∉wW gs N α) (x1:w∉vw gs N α) (p:Fin N):v9 gs L w p=vk gs α w:=bz gs α _ α w wv x1
lemma zm {N:ℕ} (gs:List vg) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (hα:∀ a x,α a=true→ L a x=true) (w:ℕ) (p:Fin N):vk gs α w⊆v9 gs L w p:=XD gs α _ (λ a=>hα a _) w
lemma wD {N:ℕ} (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (w:ℕ) (hw:w∈vw gs N α):vk (N:=N) gs α w=∅:=by
 classical
 have hk:=(_A hw).2;have hf:α (yk gs N w)=false:=by
  cases he:gateAt gs N w with
  | inl rs=>simp[wE,he] at hk
  | inr ar=>simpa[wE,yk,he] using hk
 exact (mj gs vK α α w hw).trans (by simp[hf])
open Classical
noncomputable def yT {N:ℕ} (I:_0 N) [_4 I] (gs:List vg) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (w:ℕ):_3 N:=by
 classical
 exact Nat.strongRecOn w λ i QY=>if i∈wW gs N α then (vU gs N i).biUnion λ c=>if h:c < i then QY c h else ∅ else if i∈vw gs N α then (vH gs L i).filter λ p=>(if h:vu gs N i < i then p∈QY (vu gs N i) h else False)∨yW I (vk gs α (vu gs N i)) p else ∅
lemma mA {N:ℕ} (I:_0 N) [_4 I] (gs:List vg) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (w:ℕ):yT I gs α L w=if w∈wW gs N α then (vU gs N w).biUnion λ c=>if c < w then yT I gs α L c else ∅ else if w∈vw gs N α then (vH gs L w).filter λ p=>(if vu gs N w < w then p∈yT I gs α L (vu gs N w) else False)∨yW I (vk gs α (vu gs N w)) p else ∅:=by
 classical
 unfold yT;rw[Nat.strongRecOn_eq];rfl
lemma jl {N:ℕ} (I:_0 N) [_4 I] (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (w:ℕ) (hw:w∈wW gs N α) (p:Fin N):p∈yT I gs α L w↔∃ c∈vU gs N w,p∈yT I gs α L c:=by
 classical
 rw[mA,_O hw];simp only[mem_biUnion];constructor
 · rintro⟨c,hc,hp⟩;exact⟨c,hc,by simpa[yV gs vK N α w hw c hc] using hp⟩
 · rintro⟨c,hc,hp⟩;exact⟨c,hc,by simpa[yV gs vK N α w hw c hc] using hp⟩
lemma uf {N:ℕ} (I:_0 N) [_4 I] (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (w:ℕ) (hw:w∈vw gs N α) (p:Fin N):p∈yT I gs α L w↔p∈vH gs L w∧(p∈yT I gs α L (vu gs N w)∨yW I (vk gs α (vu gs N w)) p):=by
 classical
 have hn:w∉wW gs N α:=λ ho=>disjoint_left.mp (wl gs N α) ho hw;rw[mA,ite_eq_right hn,_O hw];simp only[mem_filter,_O (yz gs vK N α w hw)]
lemma j9 {N:ℕ} (I:_0 N) [_4 I] (gs:List vg) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (w:ℕ) (wv:w∉wW gs N α) (x1:w∉vw gs N α):yT I gs α L w=∅:=by
 classical
 rw[mA,ite_eq_right wv,ite_eq_right x1]
lemma pH {N:ℕ} (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (hα:∀ a x,α a=true→ L a x=true) (i:ℕ) (p l:Fin N) (hl:l∈v9 gs L i p):l∈vk gs α i∨∃ g∈vw gs N α,p∈vH gs L g∧l∈vk gs α (vu gs N g)∧vk gs α (vu gs N g)⊆v9 gs L i p:=by exact Kc.pH (wW gs N α) (vw gs N α) (vU gs N) (vu gs N) (vH gs L) (vk gs α) (v9 gs L) (yV gs vK N α) (yz gs vK N α) (jK gs vK α L hα) (xW gs vK α L) (qN gs α L) (xg gs vK α) (zm gs α L hα) i p l hl
lemma k3 {N:ℕ} (I:_0 N) [_4 I] (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (hα:∀ a x,α a=true→ L a x=true) (i:ℕ) (p:Fin N) (hp:p∈yT I gs α L i):∃ g∈vw gs N α,p∈vH gs L g∧yW I (vk gs α (vu gs N g)) p∧vk gs α (vu gs N g)⊆v9 gs L i p:=by exact Kc.k3 I (wW gs N α) (vw gs N α) (vU gs N) (vu gs N) (vH gs L) (yT I gs α L) (vk gs α) (v9 gs L) (yV gs vK N α) (yz gs vK N α) (jl I gs vK α L) (uf I gs vK α L) (j9 I gs α L) (jK gs vK α L hα) (xW gs vK α L) (zm gs α L hα) i p hp
lemma xB {N:ℕ} (I:_0 N) [_4 I] (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (hα:∀ a x,α a=true→ L a x=true) (E:_2 N) (p l:Fin N) (hI:I p l) (hE:(p,l)∉E) (xz:(p,l)∉wg I (vw gs N α) (vH gs L) (λ g=>vk gs α (vu gs N g)) E) (bX:(p,l)∉xk I (vw gs N α) (λ g=>vk gs α (vu gs N g))) (i:ℕ) (hl:l∈v9 gs L i p) (yi:l∉vk gs α i):p∈yT I gs α L i:=by
 exact Kc.xB I (wW gs N α) (vw gs N α) (vU gs N) (vu gs N) (vH gs L) (yT I gs α L) (vk gs α) (v9 gs L) (yV gs vK N α) (yz gs vK N α) (jl I gs vK α L) (uf I gs vK α L) (jK gs vK α L hα) (xW gs vK α L) (qN gs α L) (xg gs vK α) E p l hI hE xz bX i hl yi
end Kd
namespace Ke
def run (gs:List Gate) (x:List Bool):List Bool:=gs.foldl (λ w g=>w ++ [g.op.eval (g.inputs.map λ i=>w.getD i false)]) x
lemma xU (g:Gate) (gs:List Gate) (x:List Bool):run (g :: gs) x=run gs (x ++ [g.op.eval (g.inputs.map λ i=>x.getD i false)]):=
 rfl
lemma zv (gs:List Gate) (x:List Bool):(run gs x).length=x.length+gs.length:=by
 induction gs generalizing x with
 | nil=>simp[run]
 | cons g gs ih=>rw[xU,ih];simp;omega
lemma jN (gs:List Gate) (x:List Bool) (w:ℕ) (hw:w < x.length):(run gs x).getD w false=x.getD w false:=by
 induction gs generalizing x with
 | nil=>rfl
 | cons g gs ih=>
  rw[xU,ih _ (by simp;omega),_i _ _ _ _ hw]
lemma ds (gs:List Gate) (x:List Bool) (j:ℕ):run gs x=run (gs.drop j) (run (gs.take j) x):=by simpa only[run,foldl_append] using _9 (λ l:List Gate=>run l x) (List.take_append_drop j gs).symm
def value {n:ℕ} (C:_a) (x:Fin n→ Bool) (w:ℕ):Bool:=(C.wires (ofFn x)).getD w false
lemma xF {n:ℕ} (C:_a) (x:Fin n→ Bool) (p:Fin n):value C x p=x p:=by
 change (run C.gates (ofFn x)).getD p false=x p;have hp:(p:ℕ) < (ofFn x).length:=by simp
 rw[jN _ _ _ hp,_k _ _ hp];simp
lemma wR {n:ℕ} (C:_a) (x:Fin n→ Bool) (w:ℕ) (hw:n+C.size≤ w):value C x w=false:=by change (run C.gates (ofFn x)).getD w false=false;exact _j _ _ (by simpa[zv,Circuit.size] using hw)
lemma ud {n:ℕ} (C:_a) (x:Fin n→ Bool) (w:ℕ) (hn:n≤ w) (hw:w < n+C.size):
 let g:=C.gates[w-n]'(by unfold Circuit.size at hw;omega)
 value C x w=g.op.eval (g.inputs.map λ r=>if r < w then value C x r else false):=by
 let j:=w-n;have hj:j < C.gates.length:=by unfold j Circuit.size at *;omega
 let g:=C.gates[j];let earlier:=run (C.gates.take j) (ofFn x);have g4:earlier.length=w:=by simp[earlier,zv,Nat.min_eq_left hj.le,j];omega
 have split:run C.gates (ofFn x)=run (g :: C.gates.drop (j+1)) earlier:=by rw[ds C.gates (ofFn x) j,List.drop_eq_getElem_cons hj]
 have u1 (r:ℕ):earlier.getD r false=if r < w then value C x r else false:=by
  by_cases hr:r < w
  · rw[_O hr];change earlier.getD r false=(run C.gates (ofFn x)).getD r false;rw[split];exact (jN _ earlier r (by simpa only[g4] using hr)).symm
  · rw[ite_eq_right hr];exact _j _ _ (by omega)
 change (run C.gates (ofFn x)).getD w false=g.op.eval (g.inputs.map λ r=>if r < w then value C x r else false);rw (occs:=[1]) [split]
 rw (occs:=[1]) [xU]
 rw[jN _ _ _ (by simp[g4]),_g _ _ _ _ (by omega)];simp only[g4,Nat.sub_self,List.getD_cons_zero,u1]
lemma xh {n:ℕ} (C:_a) (hG:∀ g∈C.gates,(g.op=GateOp.and∨g.op=GateOp.or)∧g.inputs.length≤2) (w:ℕ) (hn:n≤ w) (hw:w < n+C.size):∃ P:Finset ℕ,P.card≤2∧(∀ r∈P,r < w)∧∀(x y:Fin n→ Bool),(∀ r∈P,value C x r=true→ value C y r=true)→ value C x w=true→ value C y w=true:=by
 let g:=C.gates[w-n]'(by unfold Circuit.size at hw;omega)
 obtain⟨kf,y5⟩:=hG g (List.getElem_mem _);let P:=g.inputs.toFinset.filter (· < w);refine⟨P,(card_filter_le _ _).trans ((_u g.inputs).trans y5),?_,?_⟩
 · exact λ r hr=>(_A hr).2
 · intro x y XB hx
   have step (r) (hr:r∈g.inputs):(if r < w then value C x r else false)=true→(if r < w then value C y r else false)=true:=by
    by_cases h:r < w
    · simpa[h] using XB r (_B ⟨_v.mpr hr,h⟩)
    · simp[h]
   have form (z:Fin n→ Bool):value C z w=g.op.eval (g.inputs.map λ r=>if r < w then value C z r else false):=ud C z w hn hw;rw[form x] at hx;rw[form y];rcases kf with kf|kf
   · simp only[kf,GateOp.eval,List.all_eq_true,List.mem_map,id_eq] at hx ⊢;intro b hb;obtain⟨r,hr,rfl⟩:=hb;exact step r hr (hx _ ⟨r,hr,rfl⟩)
   · simp only[kf,GateOp.eval,List.any_eq_true,List.mem_map,id_eq] at hx ⊢;obtain⟨b,⟨r,hr,rfl⟩,hv⟩:=hx;exact⟨_,⟨r,hr,rfl⟩,step r hr hv⟩
lemma p8 {n:ℕ} (C:_a) (hG:∀ g∈C.gates,(g.op=GateOp.and∨g.op=GateOp.or)∧g.inputs.length≤2) (x y:Fin n→ Bool) (XB:∀ p,x p=true→ y p=true) (w:ℕ):value C x w=true→ value C y w=true:=by
 induction w using strong_induction_on with
 | ind w ih=>
  by_cases hn:w < n
  · let p:Fin n:=⟨w,hn⟩;change value C x p=true→ value C y p=true;simpa only[xF] using XB p
  by_cases hw:w < n+C.size
  · obtain⟨P,_,hP,zl⟩:=xh C hG w (by omega) hw;exact zl x y λ r hr=>ih r (hP r hr)
  · simp[wR C x w (by omega)]
def support {n:ℕ} (C:_a) (w:ℕ):Finset (Fin n):=univ.filter (λ p=>value C (λ q=>decide (q=p)) w=true)
lemma yF {n:ℕ} (C:_a) (w:ℕ) (p:Fin n):p∈support C w↔value C (λ q=>decide (q=p)) w=true:=by simp[support]
lemma jt {n:ℕ} (C:_a) (w:ℕ) (h:2≤(support (n:=n) C w).card):n≤ w∧w < n+C.size:=by
 constructor
 · by_contra! hw;let p:Fin n:=⟨w,hw⟩
   have hs:support C w⊆{p}:=by intro q hq;have hv:=(yF C w q).mp hq;change value C (λ r=>decide (r=q)) p=true at hv;simpa[xF,eq_comm] using hv
   have hb:=_C hs;simp at hb
   omega
 · by_contra! hw
   have hs:support (n:=n) C w=∅:=by ext q;simp[yF,wR C _ w hw]
   simp[hs] at h
abbrev good (C:_a):=∀ g∈C.gates,(g.op=GateOp.and∨g.op=GateOp.or)∧g.inputs.length≤2
def bit {n:ℕ} (A:Finset (Fin n)) (v:Fin n):Bool:=decide (v∈A)
def vT {n:ℕ} (C:_a) (P:Finset (Fin n)) (w:ℕ):=support C w∩P
noncomputable def vU {n:ℕ} (C:_a) (hg:good C) (w:ℕ):Finset ℕ:=if h:n≤ w∧w < n+C.size then (xh (n:=n) C hg w h.1 h.2).choose else ∅
lemma wy {n:ℕ} (C:_a) (hg:good C) (w:ℕ):(vU (n:=n) C hg w).card≤2∧(∀ c∈vU (n:=n) C hg w,c < w)∧(n≤ w→ w < n+C.size→∀ x y:Fin n→ Bool,(∀ c∈vU (n:=n) C hg w,value C x c=true→ value C y c=true)→ value C x w=true→ value C y w=true):=by
 unfold vU;split_ifs with h
 · have hs:=(xh (n:=n) C hg w h.1 h.2).choose_spec;exact⟨hs.1,hs.2.1,λ _ _=>hs.2.2⟩
 · exact⟨by simp,by simp,λ hn hw=>(h ⟨hn,hw⟩).elim⟩
lemma jh {n:ℕ} (C:_a) (hg:good C) (w:ℕ) (hn:n≤ w) (hw:w < n+C.size) (x y:Fin n→ Bool) (hx:value C x w=true) (hy:value C y w=false):∃ c∈vU (n:=n) C hg w,value C x c=true∧value C y c=false:=by
 by_contra! h;have ht:=(wy (n:=n) C hg w).2.2 hn hw x y (by
  intro c hc N0;exact Bool.eq_true_of_not_eq_false (h c hc N0)) hx
 simp[hy] at ht
def yl {n m:ℕ} (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (S:Finset (Fin m)):Fin n→ Bool:=bit (P\S.biUnion T)
def dead {n m:ℕ} (C:_a) (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (d w:ℕ):Prop:=∃ S:Finset (Fin m),S.card≤ d∧value C (yl P T S) w=false
lemma qR {n m:ℕ} (C:_a) (hg:good C) (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (S:Finset (Fin m)) (w:ℕ) (hw:value C (yl P T S) w=false):vT C P w⊆S.biUnion T:=by
 intro p hp;by_contra x9;have qX:=(yF C w p).mp (_P hp).1;have hm:=p8 C hg (λ q=>decide (q=p)) (yl P T S) (by
  intro q hq;have eq:q=p:=_o hq;subst q;simp[yl,bit,(_P hp).2,x9]) w qX
 simp[hw] at hm
lemma n5 {n m:ℕ} (C:_a) (hg:good C) (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (hT:∀ i j,i≠j→(T i∩T j).card≤1) (d w:ℕ) (hw:dead C P T d w):(univ.filter λ l=>d+1≤(vT C P w∩T l).card).card≤ d:=by
 classical
 obtain⟨S,hS,zj⟩:=hw;refine (_C (t:=S) ?_).trans hS
 intro l hl;have yP:=(_A hl).2;by_contra x9;have vR:vT C P w∩T l⊆S.biUnion (λ s=>T s∩T l):=by intro p hp;obtain⟨s,hs,Sb⟩:=mem_biUnion.mp (qR C hg P T S w zj (_P hp).1);exact _F ⟨s,hs,_X ⟨Sb,(_P hp).2⟩⟩
 have hb:=_E S (λ s=>T s∩T l) 1 (by
  intro s hs;exact hT s l (λ h=>x9 (h▸hs)))
 have hc:=_C vR;simp only[mul_one] at hb;omega
lemma yB {n:ℕ} (C:_a) (P:Finset (Fin n)) (w:ℕ) (h:2≤(vT C P w).card):n≤ w∧w < n+C.size:=jt C w (h.trans (_C inter_subset_left))
lemma XJ {n m:ℕ} (C:_a) (hg:good C) (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (d:ℕ) (hd:1≤ d) (G:Finset ℕ) (fN:∀ g∈G,∀ c∈vU (n:=n) C hg g,n≤ c→ c∈G) (p:Fin n) (l:Fin m) (S:Finset (Fin m)):∀ w,w∈G→ p∈vT C P w→ value C (yl P T S) w=false→ d+1≤(vT C P w∩T l).card→∃ g∈G,value C (yl P T S) g=false∧d+1≤(vT C P g∩T l).card∧∃ c∈vU (n:=n) C hg g,p∈vT C P c∧(vT C P c∩T l).card≤ d:=by
 intro w;induction w using strong_induction_on with
 | ind w ih=>
  intro hw hp zj yP;have v7:=yB C P w (by
   have cX:=_C (inter_subset_left (s₁:=vT C P w) (s₂:=T l));omega)
  obtain⟨c,hc,UV,Yb⟩:=jh C hg w v7.1 v7.2 (λ q=>decide (q=p)) (yl P T S) ((yF C w p).mp (_P hp).1) zj;have gn:p∈vT C P c:=_X ⟨(yF C c p).mpr UV,(_P hp).2⟩;by_cases hclarge:d+1≤(vT C P c∩T l).card
  · have Wf:=yB C P c (by
     have cX:=_C (inter_subset_left (s₁:=vT C P c) (s₂:=T l));omega)
    exact ih c ((wy C hg w).2.1 c hc) (fN w hw c hc Wf.1) gn Yb hclarge
  · exact⟨w,hw,zj,yP,c,hc,gn,by omega⟩
noncomputable def counted {n m:ℕ} (C:_a) (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (G:Finset ℕ) (d:ℕ):Finset (Fin n× Fin m):=by
 classical
 exact univ.filter λ e=>e.1∈T e.2∧∃ w∈G,dead C P T d w∧e.1∈vT C P w∧d+1≤(vT C P w∩T e.2).card
theorem km {n m:ℕ} (C:_a) (hg:good C) (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (hT:∀ i j,i≠j→(T i∩T j).card≤1) (d:ℕ) (hd:1≤ d) (G:Finset ℕ) (fN:∀ g∈G,∀ c∈vU (n:=n) C hg g,n≤ c→ c∈G):(counted C P T G d).card≤(2*d*d)*G.card:=by
 classical
 let Lg:ℕ→ Finset (Fin m):=λ g=>univ.filter λ l=>d+1≤(vT C P g∩T l).card∧dead C P T d g;let Tc:Fin m→ ℕ→ Finset (Fin n× Fin m):=λ l c=>if (vT C P c∩T l).card≤ d then
  (vT C P c∩T l).image (λ p=>(p,l)) else ∅
 have NB:∀ g,(Lg g).card≤ d:=by
  intro g;by_cases v4:dead C P T d g
  · have zD:Lg g=univ.filter (λ l=>d+1≤(vT C P g∩T l).card):=by
     ext l;simp[Lg,v4]
    rw[zD];exact n5 C hg P T hT d g v4
  · simp[Lg,v4]
 have QZ:∀ l c,(Tc l c).card≤ d:=by
  intro l c;simp only[Tc];split_ifs with h
  · exact _T.trans h
  · simp
 have vR:counted C P T G d⊆G.biUnion (λ g=>(Lg g).biUnion (λ l=>(vU (n:=n) C hg g).biUnion (λ c=>Tc l c))):=by
  intro e he;obtain⟨_,NS,w,hw,⟨S,hS,zj⟩,hp,yP⟩:=_A he;obtain⟨g,MW,YD,Ye,c,hc,gn,fG⟩:=XJ C hg P T d hd G fN e.1 e.2 S w hw hp zj yP;refine _F ⟨g,MW,_F ⟨e.2,?_,_F ⟨c,hc,?_⟩⟩⟩
  · exact _B ⟨_H _,Ye,S,hS,YD⟩
  · simp only[Tc,_O fG,mem_image];exact⟨e.1,_X ⟨gn,NS⟩,rfl⟩
 refine (_C vR).trans ?_
 refine (_E G _ (2*d*d) ?_).trans (by rw[Nat.mul_comm])
 intro g _;refine (_E (Lg g) _ (2*d) ?_).trans ?_
 · intro l _;refine (_E (vU (n:=n) C hg g) _ d (λ c _=>QZ l c)).trans ?_
   exact Nat.mul_le_mul_right d (wy (n:=n) C hg g).1
 · have hb:=Nat.mul_le_mul_right (2*d) (NB g);nlinarith
end Ke
namespace Kc
end Kc
namespace K9
open PEqualNP.CircuitLowerBounds M2
def j1 (labels:ℕ→ Bool):vg→ Gate
 | Sum.inl rs=>⟨GateOp.or,rs⟩
 | Sum.inr (a,r)=>⟨GateOp.or,if labels a then [r] else []⟩
def xG (gs:List vg) (labels:ℕ→ Bool):_a:=⟨gs.map (j1 labels),0⟩
@[local simp] lemma bareGate_op (labels : ℕ → Bool) (g : vg) : (j1 labels g).op = GateOp.or := by cases g <;> rfl
lemma Zl (labels:ℕ→ Bool) (w:List Bool) (g:vg):(j1 labels g).op.eval ((j1 labels g).inputs.map λ r=>w.getD r false)=step labels w g:=by
 cases g with
 | inl rs=>rfl
 | inr ar=>
  rcases ar with ⟨a,r⟩
  cases ha:labels a <;> simp[j1,step,GateOp.eval,ha]
lemma mn (gs:List vg) (labels:ℕ→ Bool) (y:List Bool):(xG gs labels).wires y=run gs labels y:=by
 induction gs generalizing y with
 | nil=>rfl
 | cons g gs ih=>
  change (xG gs labels).wires (y ++ [(j1 labels g).op.eval ((j1 labels g).inputs.map λ r=>y.getD r false)])=run gs labels (y ++ [step labels y g]);rw[Zl];exact ih _
@[local simp] lemma size_eq (gs : List vg) (labels : ℕ → Bool) : (xG gs labels).size = gs.length := by simp [xG, Circuit.size]
lemma xY {n:ℕ} (gs:List vg) (labels:ℕ→ Bool) (y:Fin n→ Bool) (w:ℕ):((xG gs labels).wires (ofFn y)).getD w false=true↔∃ l∈(uV gs labels).getD w ∅,y l=true:=by rw[mn,M2.xY]
lemma br {n:ℕ} (gs:List vg) (labels:ℕ→ Bool) (p:Fin n) (w:ℕ):((xG gs labels).wires (ofFn (λ q:Fin n=>decide (q=p)))).getD w false=true↔p∈(uV gs labels).getD w ∅:=by rw[xY];simp
end K9
namespace Kc
end Kc
namespace K6
def run (gs:List Gate) (x:List Bool):List Bool:=gs.foldl (λ w g=>w ++ [g.op.eval (g.inputs.map λ i=>w.getD i false)]) x
lemma xU (g:Gate) (gs:List Gate) (x:List Bool):run (g :: gs) x=run gs (x ++ [g.op.eval (g.inputs.map λ i=>x.getD i false)]):=
 rfl
lemma zv (gs:List Gate) (x:List Bool):(run gs x).length=x.length+gs.length:=by
 induction gs generalizing x with
 | nil=>simp[run]
 | cons g gs ih=>rw[xU,ih];simp;omega
lemma jN (gs:List Gate) (x:List Bool) (w:ℕ) (hw:w < x.length):(run gs x).getD w false=x.getD w false:=by
 induction gs generalizing x with
 | nil=>rfl
 | cons g gs ih=>
  rw[xU,ih _ (by simp;omega),_i _ _ _ _ hw]
lemma ds (gs:List Gate) (x:List Bool) (j:ℕ):run gs x=run (gs.drop j) (run (gs.take j) x):=by simpa only[run,foldl_append] using _9 (λ l:List Gate=>run l x) (List.take_append_drop j gs).symm
def value {n:ℕ} (C:_a) (x:Fin n→ Bool) (w:ℕ):Bool:=(C.wires (ofFn x)).getD w false
lemma xF {n:ℕ} (C:_a) (x:Fin n→ Bool) (p:Fin n):value C x p=x p:=by
 change (run C.gates (ofFn x)).getD p false=x p;have hp:(p:ℕ) < (ofFn x).length:=by simp
 rw[jN _ _ _ hp,_k _ _ hp];simp
lemma wR {n:ℕ} (C:_a) (x:Fin n→ Bool) (w:ℕ) (hw:n+C.size≤ w):value C x w=false:=by change (run C.gates (ofFn x)).getD w false=false;exact _j _ _ (by simpa[zv,Circuit.size] using hw)
lemma ud {n:ℕ} (C:_a) (x:Fin n→ Bool) (w:ℕ) (hn:n≤ w) (hw:w < n+C.size):
 let g:=C.gates[w-n]'(by unfold Circuit.size at hw;omega)
 value C x w=g.op.eval (g.inputs.map λ r=>if r < w then value C x r else false):=by
 let j:=w-n;have hj:j < C.gates.length:=by unfold j Circuit.size at *;omega
 let g:=C.gates[j];let earlier:=run (C.gates.take j) (ofFn x);have g4:earlier.length=w:=by simp[earlier,zv,Nat.min_eq_left hj.le,j];omega
 have split:run C.gates (ofFn x)=run (g :: C.gates.drop (j+1)) earlier:=by rw[ds C.gates (ofFn x) j,List.drop_eq_getElem_cons hj]
 have u1 (r:ℕ):earlier.getD r false=if r < w then value C x r else false:=by
  by_cases hr:r < w
  · rw[_O hr];change earlier.getD r false=(run C.gates (ofFn x)).getD r false;rw[split];exact (jN _ earlier r (by simpa only[g4] using hr)).symm
  · rw[ite_eq_right hr];exact _j _ _ (by omega)
 change (run C.gates (ofFn x)).getD w false=g.op.eval (g.inputs.map λ r=>if r < w then value C x r else false);rw (occs:=[1]) [split]
 rw (occs:=[1]) [xU]
 rw[jN _ _ _ (by simp[g4]),_g _ _ _ _ (by omega)];simp only[g4,Nat.sub_self,List.getD_cons_zero,u1]
lemma xh {n:ℕ} (C:_a) (hG:∀ g∈C.gates,(g.op=GateOp.and∨g.op=GateOp.or)∧g.inputs.length≤2) (w:ℕ) (hn:n≤ w) (hw:w < n+C.size):∃ P:Finset ℕ,P.card≤2∧(∀ r∈P,r∈(C.gates[w-n]'(by unfold Circuit.size at hw;omega)).inputs)∧(∀ r∈P,r < w)∧∀(x y:Fin n→ Bool),(∀ r∈P,value C x r=true→ value C y r=true)→ value C x w=true→ value C y w=true:=by
 let g:=C.gates[w-n]'(by unfold Circuit.size at hw;omega)
 obtain⟨kf,y5⟩:=hG g (List.getElem_mem _);let P:=g.inputs.toFinset.filter (· < w);refine⟨P,(card_filter_le _ _).trans ((_u g.inputs).trans y5),?_,?_,?_⟩
 · exact λ r hr=>_v.mp (_A hr).1
 · exact λ r hr=>(_A hr).2
 · intro x y XB hx
   have step (r) (hr:r∈g.inputs):(if r < w then value C x r else false)=true→(if r < w then value C y r else false)=true:=by
    by_cases h:r < w
    · simpa[h] using XB r (_B ⟨_v.mpr hr,h⟩)
    · simp[h]
   have form (z:Fin n→ Bool):value C z w=g.op.eval (g.inputs.map λ r=>if r < w then value C z r else false):=ud C z w hn hw;rw[form x] at hx;rw[form y];rcases kf with kf|kf
   · simp only[kf,GateOp.eval,List.all_eq_true,List.mem_map,id_eq] at hx ⊢;intro b hb;obtain⟨r,hr,rfl⟩:=hb;exact step r hr (hx _ ⟨r,hr,rfl⟩)
   · simp only[kf,GateOp.eval,List.any_eq_true,List.mem_map,id_eq] at hx ⊢;obtain⟨b,⟨r,hr,rfl⟩,hv⟩:=hx;exact⟨_,⟨r,hr,rfl⟩,step r hr hv⟩
lemma p8 {n:ℕ} (C:_a) (hG:∀ g∈C.gates,(g.op=GateOp.and∨g.op=GateOp.or)∧g.inputs.length≤2) (x y:Fin n→ Bool) (XB:∀ p,x p=true→ y p=true) (w:ℕ):value C x w=true→ value C y w=true:=by
 induction w using strong_induction_on with
 | ind w ih=>
  by_cases hn:w < n
  · let p:Fin n:=⟨w,hn⟩;change value C x p=true→ value C y p=true;simpa only[xF] using XB p
  by_cases hw:w < n+C.size
  · obtain⟨P,_,_,hP,zl⟩:=xh C hG w (by omega) hw;exact zl x y λ r hr=>ih r (hP r hr)
  · simp[wR C x w (by omega)]
def support {n:ℕ} (C:_a) (w:ℕ):Finset (Fin n):=univ.filter (λ p=>value C (λ q=>decide (q=p)) w=true)
lemma yF {n:ℕ} (C:_a) (w:ℕ) (p:Fin n):p∈support C w↔value C (λ q=>decide (q=p)) w=true:=by simp[support]
lemma jt {n:ℕ} (C:_a) (w:ℕ) (h:2≤(support (n:=n) C w).card):n≤ w∧w < n+C.size:=by
 constructor
 · by_contra! hw;let p:Fin n:=⟨w,hw⟩
   have hs:support C w⊆{p}:=by intro q hq;have hv:=(yF C w q).mp hq;change value C (λ r=>decide (r=q)) p=true at hv;simpa[xF,eq_comm] using hv
   have hb:=_C hs;simp at hb
   omega
 · by_contra! hw
   have hs:support (n:=n) C w=∅:=by ext q;simp[yF,wR C _ w hw]
   simp[hs] at h
abbrev good (C:_a):=∀ g∈C.gates,(g.op=GateOp.and∨g.op=GateOp.or)∧g.inputs.length≤2
def bit {n:ℕ} (A:Finset (Fin n)) (v:Fin n):Bool:=decide (v∈A)
def vT {n:ℕ} (C:_a) (P:Finset (Fin n)) (w:ℕ):=support C w∩P
noncomputable def vU {n:ℕ} (C:_a) (hg:good C) (w:ℕ):Finset ℕ:=if h:n≤ w∧w < n+C.size then (xh (n:=n) C hg w h.1 h.2).choose else ∅
lemma wy {n:ℕ} (C:_a) (hg:good C) (w:ℕ):(vU (n:=n) C hg w).card≤2∧(∀ c∈vU (n:=n) C hg w,c < w)∧(n≤ w→ w < n+C.size→∀ x y:Fin n→ Bool,(∀ c∈vU (n:=n) C hg w,value C x c=true→ value C y c=true)→ value C x w=true→ value C y w=true):=by
 unfold vU;split_ifs with h
 · have hs:=(xh (n:=n) C hg w h.1 h.2).choose_spec;exact⟨hs.1,hs.2.2.1,λ _ _=>hs.2.2.2⟩
 · exact⟨by simp,by simp,λ hn hw=>(h ⟨hn,hw⟩).elim⟩
lemma jh {n:ℕ} (C:_a) (hg:good C) (w:ℕ) (hn:n≤ w) (hw:w < n+C.size) (x y:Fin n→ Bool) (hx:value C x w=true) (hy:value C y w=false):∃ c∈vU (n:=n) C hg w,value C x c=true∧value C y c=false:=by
 by_contra! h;have ht:=(wy (n:=n) C hg w).2.2 hn hw x y (by
  intro c hc N0;exact Bool.eq_true_of_not_eq_false (h c hc N0)) hx
 simp[hy] at ht
def yl {n m:ℕ} (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (S:Finset (Fin m)):Fin n→ Bool:=bit (P\S.biUnion T)
def dead {n m:ℕ} (C:_a) (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (d w:ℕ):Prop:=∃ S:Finset (Fin m),S.card≤ d∧value C (yl P T S) w=false
lemma qR {n m:ℕ} (C:_a) (hg:good C) (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (S:Finset (Fin m)) (w:ℕ) (hw:value C (yl P T S) w=false):vT C P w⊆S.biUnion T:=by
 intro p hp;by_contra x9;have qX:=(yF C w p).mp (_P hp).1;have hm:=p8 C hg (λ q=>decide (q=p)) (yl P T S) (by
  intro q hq;have eq:q=p:=_o hq;subst q;simp[yl,bit,(_P hp).2,x9]) w qX
 simp[hw] at hm
lemma n5 {n m:ℕ} (C:_a) (hg:good C) (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (hT:∀ i j,i≠j→(T i∩T j).card≤1) (d w:ℕ) (hw:dead C P T d w):(univ.filter λ l=>d+1≤(vT C P w∩T l).card).card≤ d:=by
 classical
 obtain⟨S,hS,zj⟩:=hw;refine (_C (t:=S) ?_).trans hS
 intro l hl;have yP:=(_A hl).2;by_contra x9;have vR:vT C P w∩T l⊆S.biUnion (λ s=>T s∩T l):=by intro p hp;obtain⟨s,hs,Sb⟩:=mem_biUnion.mp (qR C hg P T S w zj (_P hp).1);exact _F ⟨s,hs,_X ⟨Sb,(_P hp).2⟩⟩
 have hb:=_E S (λ s=>T s∩T l) 1 (by
  intro s hs;exact hT s l (λ h=>x9 (h▸hs)))
 have hc:=_C vR;simp only[mul_one] at hb;omega
lemma yB {n:ℕ} (C:_a) (P:Finset (Fin n)) (w:ℕ) (h:2≤(vT C P w).card):n≤ w∧w < n+C.size:=jt C w (h.trans (_C inter_subset_left))
lemma XJ {n m:ℕ} (C:_a) (hg:good C) (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (d:ℕ) (hd:1≤ d) (G:Finset ℕ) (fN:∀ g∈G,∀ c∈vU (n:=n) C hg g,n≤ c→ c∈G) (p:Fin n) (l:Fin m) (S:Finset (Fin m)):∀ w,w∈G→ p∈vT C P w→ value C (yl P T S) w=false→ d+1≤(vT C P w∩T l).card→∃ g∈G,value C (yl P T S) g=false∧d+1≤(vT C P g∩T l).card∧∃ c∈vU (n:=n) C hg g,p∈vT C P c∧(vT C P c∩T l).card≤ d:=by
 intro w;induction w using strong_induction_on with
 | ind w ih=>
  intro hw hp zj yP;have v7:=yB C P w (by
   have cX:=_C (inter_subset_left (s₁:=vT C P w) (s₂:=T l));omega)
  obtain⟨c,hc,UV,Yb⟩:=jh C hg w v7.1 v7.2 (λ q=>decide (q=p)) (yl P T S) ((yF C w p).mp (_P hp).1) zj;have gn:p∈vT C P c:=_X ⟨(yF C c p).mpr UV,(_P hp).2⟩;by_cases hclarge:d+1≤(vT C P c∩T l).card
  · have Wf:=yB C P c (by
     have cX:=_C (inter_subset_left (s₁:=vT C P c) (s₂:=T l));omega)
    exact ih c ((wy C hg w).2.1 c hc) (fN w hw c hc Wf.1) gn Yb hclarge
  · exact⟨w,hw,zj,yP,c,hc,gn,by omega⟩
noncomputable def counted {n m:ℕ} (C:_a) (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (G:Finset ℕ) (d:ℕ):Finset (Fin n× Fin m):=by
 classical
 exact univ.filter λ e=>e.1∈T e.2∧∃ w∈G,dead C P T d w∧e.1∈vT C P w∧d+1≤(vT C P w∩T e.2).card
theorem km {n m:ℕ} (C:_a) (hg:good C) (P:Finset (Fin n)) (T:Fin m→ Finset (Fin n)) (hT:∀ i j,i≠j→(T i∩T j).card≤1) (d:ℕ) (hd:1≤ d) (G:Finset ℕ) (fN:∀ g∈G,∀ c∈vU (n:=n) C hg g,n≤ c→ c∈G):(counted C P T G d).card≤(2*d*d)*G.card:=by
 classical
 let Lg:ℕ→ Finset (Fin m):=λ g=>univ.filter λ l=>d+1≤(vT C P g∩T l).card∧dead C P T d g;let Tc:Fin m→ ℕ→ Finset (Fin n× Fin m):=λ l c=>if (vT C P c∩T l).card≤ d then
  (vT C P c∩T l).image (λ p=>(p,l)) else ∅
 have NB:∀ g,(Lg g).card≤ d:=by
  intro g;by_cases v4:dead C P T d g
  · have zD:Lg g=univ.filter (λ l=>d+1≤(vT C P g∩T l).card):=by
     ext l;simp[Lg,v4]
    rw[zD];exact n5 C hg P T hT d g v4
  · simp[Lg,v4]
 have QZ:∀ l c,(Tc l c).card≤ d:=by
  intro l c;simp only[Tc];split_ifs with h
  · exact _T.trans h
  · simp
 have vR:counted C P T G d⊆G.biUnion (λ g=>(Lg g).biUnion (λ l=>(vU (n:=n) C hg g).biUnion (λ c=>Tc l c))):=by
  intro e he;obtain⟨_,NS,w,hw,⟨S,hS,zj⟩,hp,yP⟩:=_A he;obtain⟨g,MW,YD,Ye,c,hc,gn,fG⟩:=XJ C hg P T d hd G fN e.1 e.2 S w hw hp zj yP;refine _F ⟨g,MW,_F ⟨e.2,?_,_F ⟨c,hc,?_⟩⟩⟩
  · exact _B ⟨_H _,Ye,S,hS,YD⟩
  · simp only[Tc,_O fG,mem_image];exact⟨e.1,_X ⟨gn,NS⟩,rfl⟩
 refine (_C vR).trans ?_
 refine (_E G _ (2*d*d) ?_).trans (by rw[Nat.mul_comm])
 intro g _;refine (_E (Lg g) _ (2*d) ?_).trans ?_
 · intro l _;refine (_E (vU (n:=n) C hg g) _ d (λ c _=>QZ l c)).trans ?_
   exact Nat.mul_le_mul_right d (wy (n:=n) C hg g).1
 · have hb:=Nat.mul_le_mul_right (2*d) (NB g);nlinarith
lemma YZ {n:ℕ} (C:_a) (hg:good C) (w:ℕ) (hn:n≤ w) (hw:w < n+C.size) (c:ℕ) (hc:c∈vU (n:=n) C hg w):c∈(C.gates[w-n]'(by unfold Circuit.size at hw;omega)).inputs:=by
 have hh:n≤ w∧w < n+C.size:=⟨hn,hw⟩;have hs:=(xh (n:=n) C hg w hn hw).choose_spec;have hc':c∈(xh (n:=n) C hg w hn hw).choose:=by simpa only[vU,_Q hh] using hc
 exact hs.2.1 c hc'
def gK (gs:List Gate) (d:List ℕ):List ℕ:=gs.foldl (λ d g=>d ++ [g.lineDegree d]) d
lemma dD (g:Gate) (gs:List Gate) (d:List ℕ):gK (g :: gs) d=gK gs (d ++ [g.lineDegree d]):=rfl
lemma Xj (gs:List Gate) (d:List ℕ):(gK gs d).length=d.length+gs.length:=by
 induction gs generalizing d with
 | nil=>simp[gK]
 | cons g gs ih=>rw[dD,ih];simp;omega
lemma Zr (gs:List Gate) (d:List ℕ) (w:ℕ) (hw:w < d.length):(gK gs d).getD w 0=d.getD w 0:=by
 induction gs generalizing d with
 | nil=>rfl
 | cons g gs ih=>
  rw[dD,ih _ (by simp;omega),_i _ _ _ _ hw]
lemma Wh (gs:List Gate) (d:List ℕ) (j:ℕ):gK gs d=gK (gs.drop j) (gK (gs.take j) d):=by simpa only[gK,foldl_append] using _9 (λ l:List Gate=>gK l d) (List.take_append_drop j gs).symm
lemma Ym {l:List ℕ} {a:ℕ} (h:a∈l):a≤ l.foldr max 0:=by
 induction l with
 | nil=>simp at h
 | cons b l ih=>
  simp only[List.foldr_cons];rcases List.mem_cons.1 h with h | h
  · subst h;exact le_max_left _ _
  · exact le_trans (ih h) (le_max_right _ _)
lemma m2 (g:Gate) (d:List ℕ) (c:ℕ) (hc:c∈g.inputs):d.getD c 0≤ g.lineDegree d:=by
 have hm:d.getD c 0∈g.inputs.map (λ i=>d.getD i 0):=List.mem_map.mpr ⟨c,hc,rfl⟩;unfold Gate.lineDegree;split_ifs
 · exact List.le_sum_of_mem hm
 · exact Ym hm
lemma pJ (C:_a) (n:ℕ) (marked:Finset ℕ) (w:ℕ) (hn:n≤ w) (hw:w < n+C.size) (c:ℕ) (hc:c∈(C.gates[w-n]'(by unfold Circuit.size at hw;omega)).inputs) (Xc:c < w):(C.lineDegrees n marked).getD c 0≤(C.lineDegrees n marked).getD w 0:=by
 let j:=w-n;have hj:j < C.gates.length:=by unfold j Circuit.size at *;omega
 let g:=C.gates[j];let vC:=(List.range n).map λ i=>if i∈marked then 1 else 0;let earlier:=gK (C.gates.take j) vC;have g4:earlier.length=w:=by simp[earlier,vC,Xj,Nat.min_eq_left hj.le,j];omega
 have split:gK C.gates vC=gK (g :: C.gates.drop (j+1)) earlier:=by rw[Wh C.gates vC j,List.drop_eq_getElem_cons hj]
 have QT:(C.lineDegrees n marked).getD c 0=earlier.getD c 0:=by change (gK C.gates vC).getD c 0=_;rw[split];exact Zr _ earlier c (by simpa only[g4] using Xc)
 have Q3:(C.lineDegrees n marked).getD w 0=g.lineDegree earlier:=by change (gK C.gates vC).getD w 0=_;rw[split,dD];rw[Zr _ _ _ (by simp[g4]),_g _ _ _ _ (by omega)];simp only[g4,Nat.sub_self,List.getD_cons_zero]
 rw[QT,Q3];exact m2 g earlier c hc
end K6
namespace K7
open K6
def wX (C:_a) (n:ℕ) (marked:Finset ℕ) (k:ℕ):Finset ℕ:=(Ico n (n+C.size)).filter λ w=>(C.lineDegrees n marked).getD w 0≤ k
lemma Zk {n:ℕ} (C:_a) (hg:good C) (marked:Finset ℕ) (k:ℕ):∀ w∈wX C n marked k,∀ c∈vU (n:=n) C hg w,n≤ c→ c∈wX C n marked k:=by
 intro w hw c hc Tx;obtain⟨Z9,Kr⟩:=_A hw;obtain⟨g7,kJ⟩:=mem_Ico.mp Z9;have Xc:=(wy (n:=n) C hg w).2.1 c hc;have MJ:=pJ C n marked w g7 kJ c
  (YZ C hg w g7 kJ c hc) Xc
 exact _B ⟨mem_Ico.mpr ⟨Tx,lt_trans Xc kJ⟩,MJ.trans Kr⟩
def zf (N:ℕ):Fin N ↪ Fin (N+N):=⟨_7 N,λ _ _ h=>Fin.ext (by simpa using _9 Fin.val h)⟩
def jH {N:ℕ} (S:_3 N):Finset (Fin (N+N)):=S.map (zf N)
def yt (N:ℕ):Finset (Fin (N+N)):=jH univ
def zV {N:ℕ} (I:_0 N) [_4 I] (l:Fin N):Finset (Fin (N+N)):=jH (univ.filter λ p=>I p l)
lemma zp {N:ℕ} (S:_3 N) (p:Fin N):_7 N p∈jH S↔p∈S:=by
 constructor
 · intro hp;obtain⟨q,hq,zD⟩:=Finset.mem_map.mp hp;have LC:q=p:=(zf N).injective zD;simpa only[LC] using hq
 · intro hp;exact Finset.mem_map.mpr ⟨p,hp,rfl⟩
lemma px {N:ℕ} (S:_3 N) (l:Fin N):_8 N l∉jH S:=by intro hl;obtain⟨p,_,zD⟩:=Finset.mem_map.mp hl;have hv:=_9 Fin.val zD;change p.val=N+l.val at hv;have:=p.isLt;omega
def vS {N:ℕ} (C:_a) (w:ℕ):_3 N:=univ.filter λ p=>value C (λ v=>decide (v=_7 N p)) w=true
lemma jU {N:ℕ} (x:Fin N→ Bool):ofFn (Fin.addCases x (λ _:Fin N=>false))=ofFn x ++ replicate N false:=by change ofFn (Fin.append x (λ _:Fin N=>false))=_;rw[List.ofFn_fin_append];simp
lemma gd {N:ℕ} (p:Fin N):Fin.addCases (λ q=>decide (q=p)) (λ _:Fin N=>false)=λ v=>decide (v=_7 N p):=by
 funext v
 by_cases hv:v.val < N
 · let q:Fin N:=⟨v.val,hv⟩;have zD:v=_7 N q:=Fin.ext rfl;rw[zD,Fin.addCases_left];congr 1
   exact propext ⟨λ h=>_9 (_7 N) h,λ h=>Fin.ext (_9 (λ z:Fin (N+N)=>z.val) h)⟩
 · let l:Fin N:=⟨v.val-N,by have:=v.isLt;omega⟩
   have zD:v=_8 N l:=Fin.ext (by dsimp[l];omega)
   rw[zD,Fin.addCases_right];have xR:_8 N l≠_7 N p:=by intro zD;have hv:=_9 Fin.val zD;change N+l.val=p.val at hv;have:=p.isLt;omega
   simp only[xR,decide_false]
lemma gh {N:ℕ} (C:_a) (w:ℕ) (p:Fin N):p∈vS C w↔(C.wires (ofFn (λ q:Fin N=>decide (q=p)) ++ replicate N false)).getD w false=true:=by change p∈(univ.filter λ q=>value C (λ v=>decide (v=_7 N q)) w=true)↔_;rw[mem_filter];simp only[_H,true_and];change (C.wires (ofFn (λ v=>decide (v=_7 N p)))).getD w false=true↔_;rw[← gd,jU]
lemma w2 {N:ℕ} (C:_a) (w:ℕ):jH (vS C w)=vT C (yt N) w:=by
 ext v;constructor
 · intro hv;obtain⟨p,hp,rfl⟩:=Finset.mem_map.mp hv;apply _X
   refine⟨(yF C w _).mpr (_A hp).2,?_⟩
   exact Finset.mem_map.mpr ⟨p,_H _,rfl⟩
 · intro hv;obtain⟨hs,hp⟩:=_P hv;obtain⟨p,_,rfl⟩:=Finset.mem_map.mp hp;exact Finset.mem_map.mpr ⟨p,_B ⟨_H _,(yF C w _).mp hs⟩,rfl⟩
lemma n4 {N:ℕ} (C:_a) (w:ℕ) (I:_0 N) [_4 I] (l:Fin N):((vS C w).filter λ p=>I p l).card=(vT C (yt N) w∩zV I l).card:=by
 rw[← w2];change _=((vS C w).map (zf N)∩(univ.filter λ p=>I p l).map (zf N)).card;rw[← Finset.map_inter,Finset.card_map];congr 1
 ext p;simp
lemma f8 {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)):∀ l u,l≠u→(zV I l∩zV I u).card≤1:=by
 intro l u XA;unfold zV jH;rw[← Finset.map_inter,Finset.card_map,_y];intro p hp q hq;by_contra W0;have hp':I p l∧I p u:=by simpa using hp
 have hq':I q l∧I q u:=by simpa using hq
 exact hI p q l u W0 XA ⟨hp'.1,hp'.2,hq'.1,hq'.2⟩
def kF {N:ℕ} (I:_0 N) [_4 I] (S:_3 N):Fin (N+N)→ Bool:=Fin.addCases (λ p=>decide (∀ l∈S,¬ I p l)) (λ _=>false)
lemma qU {N:ℕ} (I:_0 N) [_4 I] (C:_a) (w:ℕ) (S:_3 N):value C (kF I S) w=(C.wires (ofFn (λ p=>decide (∀ l∈S,¬ I p l)) ++ replicate N false)).getD w false:=by change (C.wires (ofFn (Fin.addCases (λ p=>decide (∀ l∈S,¬ I p l)) (λ _:Fin N=>false)))).getD w false=_;rw[jU]
lemma du {N:ℕ} (I:_0 N) [_4 I] (S:_3 N):kF I S=yl (yt N) (zV I) S:=by
 funext v
 refine Fin.addCases ?_ ?_ v
 · intro p;simp only[kF,Fin.addCases_left,yl,bit,mem_sdiff,yt,zp,_H,true_and];congr 1
   simp only[mem_biUnion,zV,zp,mem_filter,_H,true_and,not_exists,not_and]
 · intro l;simp only[kF,Fin.addCases_right,yl,bit,mem_sdiff,yt,px,false_and,decide_false]
end K7
namespace Kb
open M2
open K6
open K7
def Z {N:ℕ} (C:_a) (a:ℕ) (x:Fin N→ Bool):Bool:=(C.wires (ofFn x ++ replicate N false)).getD a false
lemma X1 {N:ℕ} (C:_a) (a:ℕ) (x:Fin N→ Bool):Z C a x=value C (Fin.addCases x (λ _:Fin N=>false)) a:=by simp only[Z,value,jU]
lemma wm {N:ℕ} (C:_a) (hm:_b C):xZ (Z (N:=N) C):=by
 have hg:good C:=by intro g hg;obtain⟨kf,y5⟩:=hm g hg;exact⟨by simpa only[Set.mem_insert_iff,Set.mem_singleton_iff] using kf,y5⟩
 intro a x x' hxx' hx;rw[X1] at hx ⊢;apply p8 C hg _ _ ?_ a hx
 intro v;refine Fin.addCases ?_ ?_ v
 · intro p;simpa only[Fin.addCases_left] using hxx' p
 · intro l;simp only[Fin.addCases_right,Bool.false_eq_true,IsEmpty.forall_iff]
end Kb
namespace K3
open PEqualNP.CircuitLowerBounds M2
open Kc
lemma jX {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)):∀ p q,p≠q→(pencil I p∩pencil I q).card≤1:=by
 intro p q W0;rw[_y];intro l hl u hu;by_contra XA;have hl':I p l∧I q l:=by simpa[pencil] using hl
 have hu':I p u∧I q u:=by simpa[pencil] using hu
 exact hI p q l u W0 XA ⟨hl'.1,hu'.1,hl'.2,hu'.2⟩
end K3
namespace M1
open M2
abbrev State:=List vg×(List ℕ× List ℕ)
def net (s:State):List vg:=s.1
def u3 (s:State):List ℕ:=s.2.1
def degrees (s:State):List ℕ:=s.2.2
def vC (N:ℕ):State:=([Sum.inl []],(replicate N N ++ List.range N,replicate N 0 ++ replicate N 1))
def zq (vW:ℕ) (s:State) (r:ℕ):ℕ:=if r < (u3 s).length then r else vW
def yx (N vW:ℕ) (s:State) (g:Gate):List vg:=
 let d:=g.lineDegree (degrees s);let a:=λ r=>(u3 s).getD r N;let z:=zq vW s;if d=1∨d=2 then match g.op,g.inputs with
  | .or,rs=>[Sum.inl (rs.map a)]
  | .and,[r]=>[Sum.inl [a r]]
  | .and,[r,t]=>
   if (degrees s).getD r 0=1∧(degrees s).getD t 0=1 then [Sum.inr (z r,a t),Sum.inr (z t,a r),Sum.inl [N+(net s).length,N+(net s).length+1]]
   else if (degrees s).getD r 0=0 then [Sum.inr (z r,a t)]
   else if (degrees s).getD t 0=0 then [Sum.inr (z t,a r)]
   else []
  | _,_=>[]
 else []
def YJ (N vW:ℕ) (s:State) (g:Gate):ℕ:=
 let ps:=yx N vW s g;if ps=[] then N else N+(net s).length+ps.length-1
def ya (N vW:ℕ) (s:State) (g:Gate):State:=(net s ++ yx N vW s g,(u3 s ++ [YJ N vW s g],degrees s ++ [g.lineDegree (degrees s)]))
def yp (N vW:ℕ) (gs:List Gate):State:=gs.foldl (ya N vW) (vC N)
def yZ (N:ℕ) (C:_a):State:=yp N (N+N+C.size) C.gates
def ky (s:State) (g:Gate):ℕ:=
 let d:=g.lineDegree (degrees s);if d=1 then 1 else if d=2 then match g.op,g.inputs with
  | .and,[r,t]=>
   if (degrees s).getD r 0=1∧(degrees s).getD t 0=1 then 3 else 1
  | _,_=>1
 else 0
lemma zG (N z:ℕ) (s:State) (g:Gate):net (ya N z s g)=net s ++ yx N z s g:=rfl
lemma xd (N z:ℕ) (s:State) (g:Gate):u3 (ya N z s g)=u3 s ++ [YJ N z s g]:=rfl
lemma yC (N z:ℕ) (s:State) (g:Gate):degrees (ya N z s g)=degrees s ++ [g.lineDegree (degrees s)]:=rfl
lemma qL (N z:ℕ) (s:State) (g:Gate):(yx N z s g).length≤ ky s g:=by
 unfold yx ky;dsimp only;split_ifs
 all_goals try split
 all_goals try split_ifs
 all_goals simp_all [Gate.lineDegree]
lemma dj (N z:ℕ) (gs:List Gate):(u3 (yp N z gs)).length=N+N+gs.length:=by
 have SQ:∀(s:State),(u3 (gs.foldl (ya N z) s)).length=(u3 s).length+gs.length:=by
  induction gs with
  | nil=>intro s;simp
  | cons g gs ih=>
   intro s;rw[foldl_cons,ih,xd];simp
   omega
 simpa[yp,vC,u3,_f,List.length_range,Nat.add_assoc] using SQ (vC N)
lemma kP (N z:ℕ) (gs:List Gate):(degrees (yp N z gs)).length=N+N+gs.length:=by
 have SQ:∀(s:State),(degrees (gs.foldl (ya N z) s)).length=(degrees s).length+gs.length:=by
  induction gs with
  | nil=>intro s;simp
  | cons g gs ih=>
   intro s;rw[foldl_cons,ih,yC];simp
   omega
 simpa[yp,vC,degrees,_f,Nat.add_assoc] using SQ (vC N)
def yr (g:Gate) (Z P:ℕ→ Bool):Bool:=match g.op,g.inputs with
 | .or,rs=>(rs.map P).any id
 | .and,[]=>false
 | .and,[r]=>P r
 | .and,[r,t]=>(Z r && P t) || (P r && Z t)
 | _,_=>false
lemma uQ (g:Gate) (Z P Z' P':ℕ→ Bool) (hZ:∀ r∈g.inputs,Z r=Z' r) (hP:∀ r∈g.inputs,P r=P' r):yr g Z P=yr g Z' P':=by
 rcases g with ⟨op,rs⟩
 cases op with
 | or=>
  simp only[yr];congr 1
  apply List.map_congr_left
  intro r hr;exact hP r hr
 | and=>
  cases rs with
  | nil=>rfl
  | cons r rs=>
   cases rs with
   | nil=>exact hP r (by simp)
   | cons t rs=>
    cases rs with
    | nil=>
     simp only[yr];rw[hZ r (by simp),hZ t (by simp),hP r (by simp),hP t (by simp)]
    | cons u rs=>rfl
 | not=>rfl
 | mod n=>rfl
 | maj=>rfl
lemma k8 (g:Gate) (Z P:ℕ→ Bool) (hP:∀ r∈g.inputs,P r=false):yr g Z P=false:=by
 have zD:=uQ g Z P Z (λ _=>false)
  (λ _ _=>rfl) hP
 rw[zD];rcases g with ⟨op,rs⟩
 cases op with
 | or=>simp[yr]
 | and=>
  cases rs with
  | nil=>rfl
  | cons r rs=>
   cases rs with
   | nil=>rfl
   | cons t rs=>cases rs <;> simp[yr]
 | not=>rfl
 | mod n=>rfl
 | maj=>rfl
lemma uI (g:vg) (labels:ℕ→ Bool) (v:List Bool):(run [g] labels v).getD v.length false=step labels v g:=by simpa[run] using wN [] g labels v
lemma fq (labels:ℕ→ Bool) (v:List Bool) (a b c d:ℕ) (hb:b < v.length) (hd:d < v.length):(run [Sum.inr (a,b),Sum.inr (c,d),Sum.inl [v.length,v.length+1]] labels v).getD (v.length+2) false=((labels a && v.getD b false) || (labels c && v.getD d false)):=by
 have UQ:=wN [Sum.inr (a,b),Sum.inr (c,d)]
  (Sum.inl [v.length,v.length+1]) labels v
 have XZ:=kL [Sum.inr (a,b)] (Sum.inr (c,d)) labels v
  v.length (by simp)
 have Yz:=wN [Sum.inr (a,b)] (Sum.inr (c,d)) labels v;have Sd:=uI (Sum.inr (a,b)) labels v;have hold:=zr [Sum.inr (a,b)] labels v d hd;simp only[_e,List.length_nil,Nat.add_zero,Nat.zero_add,List.cons_append,List.nil_append] at UQ XZ Yz;change (run [Sum.inr (a,b),Sum.inr (c,d),Sum.inl [v.length,v.length+1]] labels v).getD (v.length+2) false=_ at UQ;rw[UQ];simp only[step,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false] at XZ Yz Sd ⊢;rw[XZ,Sd,Yz,hold]
lemma Zj (N vW:ℕ) (s:State) (g:Gate) (labels:ℕ→ Bool) (v:List Bool) (y5:v.length=N+(net s).length) (zj:v.getD N false=false) (hN:N < v.length) (Zm:∀ r,(u3 s).getD r N < v.length) (bH:∀ r,(degrees s).getD r 0=0→ v.getD ((u3 s).getD r N) false=false) (xT:g.op=GateOp.and∨g.op=GateOp.or) (x8:g.inputs.length≤2):(run (yx N vW s g) labels v).getD (YJ N vW s g) false=if g.lineDegree (degrees s)=1∨g.lineDegree (degrees s)=2 then yr g (λ r=>labels (zq vW s r)) (λ r=>v.getD ((u3 s).getD r N) false) else false:=by
 classical
 by_cases hdeg:g.lineDegree (degrees s)=1∨g.lineDegree (degrees s)=2
 · rw[_O hdeg];rcases g with ⟨op,rs⟩
   rcases xT with kf | kf <;> dsimp only at kf x8 <;> subst op
   · cases rs with
     | nil=>simp[Gate.lineDegree] at hdeg
     | cons r rs=>
      cases rs with
      | nil=>
       have hp:yx N vW s ⟨.and,[r]⟩=[Sum.inl [(u3 s).getD r N]]:=by simp only[yx,hdeg,↓reduceIte]
       rw[show YJ N vW s ⟨.and,[r]⟩=v.length by simp only[YJ,hp,List.cons_ne_nil,↓reduceIte,_e,List.length_nil];omega]
       rw[hp,uI];simp only[step,yr,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false]
      | cons t rs=>
       cases rs with
       | cons u rs=>simp at x8
       | nil=>
        have hd:(degrees s).getD r 0+(degrees s).getD t 0=1∨(degrees s).getD r 0+(degrees s).getD t 0=2:=by simpa[Gate.lineDegree] using hdeg
        by_cases hf:(degrees s).getD r 0=1∧(degrees s).getD t 0=1
        · have hp:yx N vW s ⟨.and,[r,t]⟩=[Sum.inr (zq vW s r,(u3 s).getD t N),Sum.inr (zq vW s t,(u3 s).getD r N),Sum.inl [v.length,v.length+1]]:=by
           simp only[yx,hdeg,↓reduceIte,hf,y5] <;> simp
          rw[show YJ N vW s ⟨.and,[r,t]⟩=v.length+2 by simp only[YJ,hp,List.cons_ne_nil,↓reduceIte,_e,List.length_nil];omega]
          rw[hp,fq labels v _ _ _ _ (Zm t) (Zm r)];simp[yr,Bool.and_comm]
        · have hz:(degrees s).getD r 0=0∨(degrees s).getD t 0=0:=by omega
          rcases hz with hz | hz
          · have hp:yx N vW s ⟨.and,[r,t]⟩=[Sum.inr (zq vW s r,(u3 s).getD t N)]:=by
             simp only[yx,hdeg,↓reduceIte,hf,hz] <;> simp
            rw[show YJ N vW s ⟨.and,[r,t]⟩=v.length by simp only[YJ,hp,List.cons_ne_nil,↓reduceIte,_e,List.length_nil];omega]
            rw[hp,uI];simp only[step,yr];rw[bH r hz];simp
          · have hr:(degrees s).getD r 0≠0:=by omega
            have hp:yx N vW s ⟨.and,[r,t]⟩=[Sum.inr (zq vW s t,(u3 s).getD r N)]:=by simp only[yx,hdeg,↓reduceIte,hf,hr,hz] <;> simp
            rw[show YJ N vW s ⟨.and,[r,t]⟩=v.length by simp only[YJ,hp,List.cons_ne_nil,↓reduceIte,_e,List.length_nil];omega]
            rw[hp,uI];simp only[step,yr];rw[bH t hz];simp[Bool.and_comm]
   · have hp:yx N vW s ⟨.or,rs⟩=[Sum.inl (rs.map λ r=>(u3 s).getD r N)]:=by
      simp only[yx,hdeg,↓reduceIte]
     rw[show YJ N vW s ⟨.or,rs⟩=v.length by simp only[YJ,hp,List.cons_ne_nil,↓reduceIte,_e,List.length_nil];omega]
     rw[hp,uI];simp[step,yr,List.map_map,Function.comp_def]
 · simpa only[yx,YJ,hdeg,↓reduceIte,run,List.foldl_nil] using zj
lemma cj (N vW:ℕ) (s:State) (g:Gate) (labels:ℕ→ Bool) (v P:List Bool) (y5:v.length=N+(net s).length) (PH:(degrees s).length=(u3 s).length) (Sk:P.length=(u3 s).length) (zj:v.getD N false=false) (hN:N < v.length) (Zm:∀ r,(u3 s).getD r N < v.length) (bH:∀ r,(degrees s).getD r 0=0→ v.getD ((u3 s).getD r N) false=false) (hold:∀ r,(degrees s).getD r 0≤2→ v.getD ((u3 s).getD r N) false=P.getD r false) (cZ:∀ r∈g.inputs,(degrees s).getD r 0≤ g.lineDegree (degrees s)) (xT:g.op=GateOp.and∨g.op=GateOp.or) (x8:g.inputs.length≤2):∀ r,(degrees (ya N vW s g)).getD r 0≤2→(run (yx N vW s g) labels v).getD ((u3 (ya N vW s g)).getD r N) false=(P ++ [yr g (λ t=>labels (zq vW s t)) (λ t=>P.getD t false)]).getD r false:=by
 intro r hr;by_cases z5:r < (u3 s).length
 · have hd:(degrees (ya N vW s g)).getD r 0=(degrees s).getD r 0:=by
    rw[yC,_i _ _ _ _ (by omega)]
   rw[hd] at hr;rw[xd,_i _ _ _ _ z5,zr _ _ _ _ (Zm r),_i _ _ _ _ (by omega)];exact hold r hr
 · by_cases zD:r=(u3 s).length
   · subst r
     have hd:(degrees (ya N vW s g)).getD (u3 s).length 0=g.lineDegree (degrees s):=by rw[yC,_g _ _ _ _ (by omega)];simp only[PH,Nat.sub_self,List.getD_cons_zero]
     rw[hd] at hr;rw[xd,_g _ _ _ _ (by omega)];simp only[Nat.sub_self,List.getD_cons_zero];rw[_g _ _ _ _ (by omega)];simp only[Sk,Nat.sub_self,List.getD_cons_zero];rw[Zj N vW s g labels v y5 zj hN Zm bH xT x8];by_cases hz:g.lineDegree (degrees s)=0
     · have hc:yr g (λ t=>labels (zq vW s t)) (λ t=>P.getD t false)=false:=by
        apply k8
        intro t ht;have Kh:(degrees s).getD t 0=0:=by have:=cZ t ht;omega
        rw[← hold t (by omega),bH t Kh]
       rw[hz,hc];simp
     · have hp:g.lineDegree (degrees s)=1∨g.lineDegree (degrees s)=2:=by omega
       rw[_O hp];apply uQ
       · intro t ht;rfl
       · intro t ht;exact hold t ((cZ t ht).trans hr)
   · have RN:(u3 s).length+1≤ r:=by omega
     have hm:(u3 (ya N vW s g)).getD r N=N:=by
      apply _j
      simp only[xd,_c,_d];exact RN
     have hp:(P ++ [yr g (λ t=>labels (zq vW s t)) (λ t=>P.getD t false)]).getD r false=false:=by
      apply _j
      simp only[_c,_d,Sk];exact RN
     rw[hm,hp,zr _ _ _ _ hN,zj]
open M2
lemma fu (N z:ℕ) (gs:List Gate) (s:State):degrees (gs.foldl (ya N z) s)=gs.foldl (λ d g=>d ++ [g.lineDegree d]) (degrees s):=by
 induction gs generalizing s with
 | nil=>rfl
 | cons g gs ih=>
  rw[foldl_cons,ih,yC];rfl
lemma uc (N:ℕ):degrees (vC N)=(List.range (N+N)).map (λ i=>if i∈Ico N (N+N) then 1 else 0):=by
 change replicate N 0 ++ replicate N 1=_;rw[List.range_add,List.map_append,List.map_map];have Ui:(List.range N).map (λ i=>if i∈Ico N (N+N) then 1 else 0)=replicate N 0:=by
  have h:(List.range N).map (λ i=>if i∈Ico N (N+N) then 1 else 0)=(List.range N).map (λ _=>0):=by
   apply List.map_congr_left
   intro i hi;have hi':=List.mem_range.mp hi;simp only[mem_Ico];split_ifs <;> omega
  simpa using h
 have Qy:(List.range N).map ((λ i=>if i∈Ico N (N+N) then 1 else 0) ∘ (λ i=>N+i))=replicate N 1:=by
  have h:(List.range N).map ((λ i=>if i∈Ico N (N+N) then 1 else 0) ∘ (λ i=>N+i))=(List.range N).map (λ _=>1):=by
   apply List.map_congr_left
   intro i hi;have hi':=List.mem_range.mp hi;simp only[Function.comp_apply,mem_Ico];split_ifs <;> omega
  simpa using h
 rw[Ui,Qy]
lemma wt (N:ℕ) (C:_a):degrees (yZ N C)=C.lineDegrees (N+N) (Ico N (N+N)):=by rw[yZ,yp,fu,uc];rfl
lemma ce (N z:ℕ) (gs:List Gate) (s:State):∃ t,net (gs.foldl (ya N z) s)=net s ++ t:=by
 induction gs generalizing s with
 | nil=>exact⟨[],by simp⟩
 | cons g gs ih=>
  obtain⟨t,ht⟩:=ih (ya N z s g);refine⟨yx N z s g ++ t,?_⟩
  rw[foldl_cons,ht,zG,List.append_assoc]
lemma hM (N z:ℕ) (gs:List Gate) (s:State):∃ t,degrees (gs.foldl (ya N z) s)=degrees s ++ t∧t.length=gs.length:=by
 induction gs generalizing s with
 | nil=>exact⟨[],by simp,rfl⟩
 | cons g gs ih=>
  obtain⟨t,ht,hl⟩:=ih (ya N z s g);refine⟨g.lineDegree (degrees s) :: t,?_,by simp[hl]⟩
  rw[foldl_cons,ht,yC];simp only[List.append_assoc,List.singleton_append]
lemma nm (N z:ℕ) (gs:List Gate) (s:State) (r d:ℕ) (hr:r < (degrees s).length):(degrees (gs.foldl (ya N z) s)).getD r d=(degrees s).getD r d:=by obtain⟨t,ht,_⟩:=hM N z gs s;rw[ht,_i _ _ _ _ hr]
lemma Yr (N z:ℕ) (gs hs:List Gate):yp N z (gs ++ hs)=hs.foldl (ya N z) (yp N z gs):=by simp only[yp,foldl_append]
lemma qh (N z:ℕ) (gs hs:List Gate) (r d:ℕ) (hr:r < N+N+gs.length):(degrees (yp N z (gs ++ hs))).getD r d=(degrees (yp N z gs)).getD r d:=by
 rw[Yr];apply nm
 simpa only[kP] using hr
lemma xM (N z:ℕ) (gs:List Gate):∃ t,net (yp N z gs)=Sum.inl [] :: t:=by obtain⟨t,ht⟩:=ce N z gs (vC N);exact⟨t,by simpa only[yp,vC,net,List.singleton_append] using ht⟩
lemma Zh (N z:ℕ) (gs:List Gate):0 < (net (yp N z gs)).length:=by obtain⟨t,ht⟩:=xM N z gs;simp[ht]
def j8 (N:ℕ) (s:State):Prop:=∀ r∈u3 s,r < N+(net s).length
lemma qt (N:ℕ):j8 N (vC N):=by
 intro r hr;change r∈replicate N N ++ List.range N at hr;change r < N+1;rcases List.mem_append.mp hr with h | h
 · have Sl:=List.eq_of_mem_replicate h;omega
 · have Sl:=List.mem_range.mp h;omega
lemma Vj (N z:ℕ) (s:State) (g:Gate) (hs:0 < (net s).length):YJ N z s g < N+(net (ya N z s g)).length:=by
 rw[zG,_c];unfold YJ;dsimp only;split_ifs with h
 · simp only[h,List.length_nil];omega
 · have hp:0 < (yx N z s g).length:=List.length_pos_iff.mpr h;omega
lemma ql (N z:ℕ) (s:State) (g:Gate) (hs:0 < (net s).length) (hb:j8 N s):j8 N (ya N z s g):=by
 intro r hr;rw[xd,List.mem_append,List.mem_singleton] at hr;rcases hr with hr | rfl
 · have h:=hb r hr;rw[zG,_c];omega
 · exact Vj N z s g hs
lemma bR (N z:ℕ) (gs:List Gate) (s:State) (hs:0 < (net s).length) (hb:j8 N s):j8 N (gs.foldl (ya N z) s):=by
 induction gs generalizing s with
 | nil=>exact hb
 | cons g gs ih=>
  rw[foldl_cons];apply ih
  · rw[zG,_c];omega
  · exact ql N z s g hs hb
lemma cl (N z:ℕ) (gs:List Gate):j8 N (yp N z gs):=bR N z gs (vC N) (by simp[vC,net]) (qt N)
lemma uR (xs:List ℕ) (d b:ℕ) (hm:∀ r∈xs,r < b) (hd:d < b) (r:ℕ):xs.getD r d < b:=by
 induction xs generalizing r with
 | nil=>simpa using hd
 | cons a xs ih=>
  cases r with
  | zero=>exact hm a (by simp)
  | succ r=>
   exact ih (λ t ht=>hm t (by simp[ht])) r
lemma nQ (N z:ℕ) (gs:List Gate) (r:ℕ):(u3 (yp N z gs)).getD r N < N+(net (yp N z gs)).length:=by
 apply uR
 · exact cl N z gs
 · have h:=Zh N z gs;omega
lemma wO (N:ℕ) (C:_a) (r:ℕ):(u3 (yZ N C)).getD r N < N+(net (yZ N C)).length:=nQ N (N+N+C.size) C.gates r
lemma fh (N p:ℕ) (hp:p < N):(u3 (vC N)).getD p N=N:=by change (replicate N N ++ List.range N).getD p N=N;rw[_i _ _ _ _ (by simpa using hp)];exact List.getD_replicate N hp
lemma dE (N l:ℕ) (hl:l < N):(u3 (vC N)).getD (N+l) N=l:=by change (replicate N N ++ List.range N).getD (N+l) N=l;rw[_g _ _ _ _ (by simp)];simp only[_f,add_sub_cancel_left];rw[_k _ _ (by simpa using hl)];exact List.getElem_range _
lemma nd (z:ℕ) (s:State) (r:ℕ) (hr:r < (u3 s).length):zq z s r=r:=by simp[zq,hr]
lemma ng (z:ℕ) (s:State) (r:ℕ) (hr:(u3 s).length≤ r):zq z s r=z:=by simp[zq,Nat.not_lt.mpr hr]
def cF (N:ℕ) (s:State):Prop:=∀ r,(degrees s).getD r 0=0→(u3 s).getD r N=N
lemma dL (N:ℕ):cF N (vC N):=by
 intro r hd;change (replicate N 0 ++ replicate N 1).getD r 0=0 at hd;change (replicate N N ++ List.range N).getD r N=N;by_cases hr:r < N
 · rw[_i _ _ _ _ (by simpa using hr)];exact List.getD_replicate N hr
 · have MB:N≤ r:=by omega
   by_cases WA:r < N+N
   · rw[_g _ _ _ _ (by simpa using MB)] at hd;simp only[_f] at hd;rw[List.getD_replicate 1 (by omega:r-N < N)] at hd;omega
   · apply _j
     simp only[_c,_f,List.length_range];omega
lemma gL (N z:ℕ) (s:State) (g:Gate) (hd:g.lineDegree (degrees s)=0):YJ N z s g=N:=by
 have hp:yx N z s g=[]:=by simp[yx,hd]
 simp[YJ,hp]
lemma wi {α:Type*} (xs:List α) (a d:α):(xs ++ [a]).getD xs.length d=a:=by rw[_g _ _ _ _ (Nat.le_refl _)];simp
lemma f5 (N z:ℕ) (s:State) (g:Gate) (y5:(u3 s).length=(degrees s).length) (hz:cF N s):cF N (ya N z s g):=by
 intro r hd;by_cases hr:r < (u3 s).length
 · rw[xd,_i _ _ _ _ hr];rw[yC,_i _ _ _ _ (by omega)] at hd;exact hz r hd
 · by_cases he:r=(u3 s).length
   · subst r;rw[xd,wi];rw[yC,y5,wi] at hd;exact gL N z s g hd
   · apply _j
     rw[xd,_c,_d];omega
lemma q3 (N z:ℕ) (gs:List Gate) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=N):(run (net (yp N z gs)) labels y).getD N false=false:=by obtain⟨t,ht⟩:=xM N z gs;rw[ht,xU];change (run t labels (y ++ [false])).getD N false=false;rw[zr _ _ _ _ (by simp[hy])];rw[_g _ _ _ _ (by omega)];simp[hy]
lemma fz (N:ℕ) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=N):∀ r,(run (net (vC N)) labels y).getD ((u3 (vC N)).getD r N) false=(replicate N false ++ y).getD r false:=by
 intro r;have zj:(run (net (vC N)) labels y).getD N false=false:=by simpa only[yp,List.foldl_nil] using q3 N 0 [] labels y hy
 by_cases hr:r < N
 · rw[fh N r hr,zj,_i _ _ _ _ (by simpa using hr),List.getD_replicate false hr]
 · have MB:N≤ r:=by omega
   by_cases WA:r < N+N
   · have hl:r-N < N:=by omega
     have he:N+(r-N)=r:=by omega
     have hm:=dE N (r-N) hl;rw[he] at hm;rw[hm,zr _ _ _ _ (by omega),_g _ _ _ _ (by simpa using MB)];simp only[_f]
   · have hm:(u3 (vC N)).getD r N=N:=by
      apply _j
      simp only[vC,u3,_c,_f,List.length_range];omega
     rw[hm,zj];symm;apply _j
     simp only[_c,_f,hy];omega
def kg (d:List ℕ) (g:Gate):Bool:=if g.lineDegree d=2 then match g.op,g.inputs with
 | .and,[r,t]=>decide (d.getD r 0=1∧d.getD t 0=1)
 | _,_=>false
 else false
def vQ (k:ℕ):List ℕ→ List Gate→ ℕ
 | _,[]=>0
 | d,g :: gs=>(if g.lineDegree d=k then 1 else 0)+vQ k (d ++ [g.lineDegree d]) gs
def zB:List ℕ→ List Gate→ ℕ
 | _,[]=>0
 | d,g :: gs=>(if kg d g then 1 else 0)+zB (d ++ [g.lineDegree d]) gs
def vA (N k:ℕ) (gs:List Gate):ℕ:=vQ k (degrees (vC N)) gs
def ks (N:ℕ) (gs:List Gate):ℕ:=zB (degrees (vC N)) gs
lemma jA (s:State) (g:Gate):ky s g=(if g.lineDegree (degrees s)=1 then 1 else 0)+(if g.lineDegree (degrees s)=2 then 1 else 0)+2*(if kg (degrees s) g then 1 else 0):=by
 unfold ky kg;dsimp only;split_ifs
 all_goals try split
 all_goals try split_ifs
 all_goals simp_all
lemma p0 (d:List ℕ) (g:Gate) (hf:kg d g=true):g.lineDegree d=2:=by
 unfold kg at hf;split_ifs at hf with hd
 exact hd
lemma Ws (d:List ℕ) (g:Gate):kg d g=true↔∃ r t,g.op=GateOp.and∧g.inputs=[r,t]∧d.getD r 0=1∧d.getD t 0=1:=by
 classical
 constructor
 · intro hf;unfold kg at hf;split_ifs at hf
   split at hf
   · rename_i r t kf pE
     exact⟨r,t,kf,pE,by simpa using hf⟩
   · contradiction
 · rintro⟨r,t,kf,pE,hr,ht⟩
   have hd:g.lineDegree d=2:=by unfold Gate.lineDegree;rw[kf,pE];simp only[ite_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero];rw[hr,ht]
   rw[kg,_O hd,kf,pE];exact decide_eq_true ⟨hr,ht⟩
lemma qd (N z:ℕ) (gs:List Gate) (s:State):(net (gs.foldl (ya N z) s)).length≤(net s).length+vQ 1 (degrees s) gs+vQ 2 (degrees s) gs+2*zB (degrees s) gs:=by
 induction gs generalizing s with
 | nil=>simp[vQ,zB]
 | cons g gs ih=>
  have h:=ih (ya N z s g);rw[zG,_c,yC] at h;have hp:=qL N z s g;rw[jA] at hp;simp only[foldl_cons,vQ,zB];omega
lemma x7 (N z:ℕ) (gs:List Gate):(net (yp N z gs)).length≤1+vA N 1 gs+vA N 2 gs+2*ks N gs:=by simpa only[yp,vA,ks,vC,net,_d] using qd N z gs (vC N)
lemma jE (d:List ℕ) (gs:List Gate):zB d gs≤ vQ 2 d gs:=by
 induction gs generalizing d with
 | nil=>rfl
 | cons g gs ih=>
  have h:=ih (d ++ [g.lineDegree d]);have zl:(if kg d g then 1 else 0)≤(if g.lineDegree d=2 then 1 else 0):=by
   by_cases hf:kg d g=true
   · simp[hf,p0 d g hf]
   · simp[hf]
  simp only[zB,vQ];omega
lemma q5 (N:ℕ) (gs:List Gate):ks N gs≤ vA N 2 gs:=jE _ _
lemma pf (d:List ℕ) (gs:List Gate):vQ 0 d gs+vQ 1 d gs+vQ 2 d gs≤ gs.length:=by
 induction gs generalizing d with
 | nil=>rfl
 | cons g gs ih=>
  have h:=ih (d ++ [g.lineDegree d]);simp only[vQ,_e];split_ifs <;> omega
lemma ue (N:ℕ) (gs:List Gate):vA N 0 gs+vA N 1 gs+vA N 2 gs≤ gs.length:=pf _ _
end M1
namespace M4
def value (g:Gate) (w:List Bool):Bool:=g.op.eval (g.inputs.map λ i=>w.getD i false)
def un (g:Gate) (z p:List Bool):Bool:=match g.op,g.inputs with
 | .or,np=>(np.map λ i=>p.getD i false).any id
 | .and,[]=>false
 | .and,[a]=>p.getD a false
 | .and,[a,b]=>
  (z.getD a false && p.getD b false) || (p.getD a false && z.getD b false)
 | _,_=>false
def At (z p w:Bool) (d:ℕ):Prop:=(z=true→ w=true)∧(p=true→ w=true)∧(d=0→ p=false)∧(d≤1→ w=(z || p))
lemma cN:At false false false 0:=by simp[At]
lemma RS {za pa wa zb pb wb:Bool} {da db:ℕ} (ha:At za pa wa da) (hb:At zb pb wb db):At (za && zb) ((za && pb) || (pa && zb)) (wa && wb) (da+db):=by
 obtain⟨d3,z1,W3,YH⟩:=ha;obtain⟨YI,jn,T8,Za⟩:=hb;refine⟨?_,?_,?_,?_⟩
 · intro h;rw[_s] at h;obtain⟨ha,hb⟩:=h;simpa only[_s] using And.intro (d3 ha) (YI hb)
 · intro h;rw[_r] at h;rcases h with h | h
   · rw[_s] at h;obtain⟨ha,hb⟩:=h;simpa only[_s] using And.intro (d3 ha) (jn hb)
   · rw[_s] at h;obtain⟨ha,hb⟩:=h;simpa only[_s] using And.intro (z1 ha) (YI hb)
 · intro h;have YL:da=0:=by omega
   have Vs:db=0:=by omega
   simp[W3 YL,T8 Vs]
 · intro h;have ha':da≤1:=by omega
   have hb':db≤1:=by omega
   rw[YH ha',Za hb'];have hz:da=0∨db=0:=by omega
   rcases hz with hz | hz
   · rw[W3 hz];cases za <;> cases zb <;> cases pb <;> rfl
   · rw[T8 hz];cases za <;> cases zb <;> cases pa <;> rfl
lemma Po {za pa wa zb pb wb:Bool} {da db:ℕ} (ha:At za pa wa da) (hb:At zb pb wb db):At (za || zb) (pa || pb) (wa || wb) (max da db):=by
 obtain⟨d3,z1,W3,YH⟩:=ha;obtain⟨YI,jn,T8,Za⟩:=hb;refine⟨?_,?_,?_,?_⟩
 · intro h;rw[_r] at h;rcases h with h | h
   · simpa only[_r] using Or.inl (b:=wb=true) (d3 h)
   · simpa only[_r] using Or.inr (a:=wa=true) (YI h)
 · intro h;rw[_r] at h;rcases h with h | h
   · simpa only[_r] using Or.inl (b:=wb=true) (z1 h)
   · simpa only[_r] using Or.inr (a:=wa=true) (jn h)
 · intro h;have YL:da=0:=by omega
   have Vs:db=0:=by omega
   simp[W3 YL,T8 Vs]
 · intro h;have ha':da≤1:=le_trans (le_max_left _ _) h;have hb':db≤1:=le_trans (le_max_right _ _) h;rw[YH ha',Za hb'];cases za <;> cases zb <;> cases pa <;> cases pb <;> rfl
def mi (z p w:List Bool) (d:List ℕ):Prop:=∀ i,At (z.getD i false) (p.getD i false) (w.getD i false) (d.getD i 0)
lemma TH (g:Gate) (z p w:List Bool) (d:List ℕ) (hm:g.op=.and∨g.op=.or) (hl:g.inputs.length≤2) (h:mi z p w d):At (value g z) (un g z p) (value g w) (g.lineDegree d):=by
 rcases g with ⟨op,np⟩
 change op=.and∨op=.or at hm;change np.length≤2 at hl;rcases hm with rfl | rfl
 · cases np with
   | nil=>simp[At,value,un,GateOp.eval,Gate.lineDegree]
   | cons a as=>
    cases as with
    | nil=>simpa[value,un,GateOp.eval,Gate.lineDegree] using h a
    | cons b bs=>
     cases bs with
     | nil=>simpa[value,un,GateOp.eval,Gate.lineDegree] using RS (h a) (h b)
     | cons c cs=>simp only[_e] at hl;omega
 · cases np with
   | nil=>simp[At,value,un,GateOp.eval,Gate.lineDegree]
   | cons a as=>
    cases as with
    | nil=>simpa[value,un,GateOp.eval,Gate.lineDegree] using h a
    | cons b bs=>
     cases bs with
     | nil=>simpa[value,un,GateOp.eval,Gate.lineDegree] using Po (h a) (h b)
     | cons c cs=>simp only[_e] at hl;omega
lemma ni (g:Gate) (d:List ℕ) (r:ℕ) (hm:g.op=.and∨g.op=.or) (hl:g.inputs.length≤2) (hr:r∈g.inputs):d.getD r 0≤ g.lineDegree d:=by
 rcases g with ⟨op,np⟩
 change op=.and∨op=.or at hm;change np.length≤2 at hl;change r∈np at hr;rcases hm with rfl | rfl
 · cases np with
   | nil=>simp at hr
   | cons a as=>
    cases as with
    | nil=>
     simp only[List.mem_singleton] at hr;subst r;simp[Gate.lineDegree]
    | cons b bs=>
     cases bs with
     | nil=>
      simp only[List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl | rfl <;> simp[Gate.lineDegree]
     | cons c cs=>simp only[_e] at hl;omega
 · cases np with
   | nil=>simp at hr
   | cons a as=>
    cases as with
    | nil=>
     simp only[List.mem_singleton] at hr;subst r;simp[Gate.lineDegree]
    | cons b bs=>
     cases bs with
     | nil=>
      simp only[List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl | rfl <;> simp[Gate.lineDegree]
     | cons c cs=>simp only[_e] at hl;omega
lemma Yg (z p w:List Bool) (d:List ℕ) (Ph:z.length=p.length) (Mq:z.length=w.length) (NZ:z.length=d.length) (h:mi z p w d) (zn pn wn:Bool) (dn:ℕ) (hn:At zn pn wn dn):mi (z ++ [zn]) (p ++ [pn]) (w ++ [wn]) (d ++ [dn]):=by
 intro i;by_cases hi:i < z.length
 · have Jl:i < p.length:=by omega
   have Jh:i < w.length:=by omega
   have KQ:i < d.length:=by omega
   rw[_i z [zn] false i hi,_i p [pn] false i Jl,_i w [wn] false i Jh,_i d [dn] 0 i KQ];exact h i
 · by_cases he:i=z.length
   · have hp:p.length≤ i:=by omega
     have hw:w.length≤ i:=by omega
     have hd:d.length≤ i:=by omega
     rw[_g z [zn] false i (by omega),_g p [pn] false i hp,_g w [wn] false i hw,_g d [dn] 0 i hd];have ez:i-z.length=0:=by omega
     have ep:i-p.length=0:=by omega
     have ew:i-w.length=0:=by omega
     have ed:i-d.length=0:=by omega
     simpa only[ez,ep,ew,ed,List.getD_cons_zero] using hn
   · have hz:(z ++ [zn]).length≤ i:=by simp only[_c,_d];omega
     have hp:(p ++ [pn]).length≤ i:=by simp only[_c,_d];omega
     have hw:(w ++ [wn]).length≤ i:=by simp only[_c,_d];omega
     have hd:(d ++ [dn]).length≤ i:=by simp only[_c,_d];omega
     rw[_j _ _ hz,_j _ _ hp,_j _ _ hw,_j _ _ hd];exact cN
abbrev State:=List Bool× List Bool× List Bool× List ℕ
def step (s:State) (g:Gate):State:=(s.1 ++ [value g s.1],s.2.1 ++ [un g s.1 s.2.1],s.2.2.1 ++ [value g s.2.2.1],s.2.2.2 ++ [g.lineDegree s.2.2.2])
def x6 (s:State):Prop:=s.1.length=s.2.1.length∧s.1.length=s.2.2.1.length∧s.1.length=s.2.2.2.length∧mi s.1 s.2.1 s.2.2.1 s.2.2.2
lemma nc (s:State) (g:Gate) (hs:x6 s) (hm:g.op=.and∨g.op=.or) (hl:g.inputs.length≤2):x6 (step s g):=by
 rcases s with ⟨z,p,w,d⟩
 rcases hs with ⟨Ph,Mq,NZ,h⟩
 refine⟨?_,?_,?_,?_⟩
 · simpa only[step,_c,_d] using _9 (λ n=>n+1) Ph
 · simpa only[step,_c,_d] using _9 (λ n=>n+1) Mq
 · simpa only[step,_c,_d] using _9 (λ n=>n+1) NZ
 · exact Yg z p w d Ph Mq NZ h _ _ _ _ (TH g z p w d hm hl h)
lemma Wi (gs:List Gate) (s:State) (hs:x6 s) (hm:∀ g∈gs,(g.op=.and∨g.op=.or)∧g.inputs.length≤2):x6 (gs.foldl step s):=by
 induction gs generalizing s with
 | nil=>exact hs
 | cons g gs ih=>
  have hg:=hm g List.mem_cons_self;exact ih (step s g) (nc s g hs hg.1 hg.2) (λ h hh=>hm h (List.mem_cons_of_mem g hh))
lemma jx (gs:List Gate) (s:State):(gs.foldl step s).1.length=s.1.length+gs.length∧(gs.foldl step s).2.1.length=s.2.1.length+gs.length∧(gs.foldl step s).2.2.1.length=s.2.2.1.length+gs.length∧(gs.foldl step s).2.2.2.length=s.2.2.2.length+gs.length:=by
 induction gs generalizing s with
 | nil=>simp
 | cons g gs ih=>
  simpa only[foldl_cons,_e,step,_c,_d,List.length_nil,Nat.zero_add,Nat.add_assoc,Nat.add_comm 1] using ih (step s g)
lemma Xw (gs:List Gate) (s:State) (i:ℕ) (hi:i < s.2.1.length):(gs.foldl step s).2.1.getD i false=s.2.1.getD i false:=by
 induction gs generalizing s with
 | nil=>rfl
 | cons g gs ih=>
  have hi':i < (step s g).2.1.length:=by simp only[step,_c,_d];omega
  change (gs.foldl step (step s g)).2.1.getD i false=s.2.1.getD i false;rw[ih (step s g) hi'];exact _i _ _ _ _ hi
lemma Y7 (gs:List Gate) (s:State) (i:ℕ) (hi:i < s.1.length):(gs.foldl step s).1.getD i false=s.1.getD i false:=by
 induction gs generalizing s with
 | nil=>rfl
 | cons g gs ih=>
  have hi':i < (step s g).1.length:=by simp only[step,_c,_d];omega
  change (gs.foldl step (step s g)).1.getD i false=s.1.getD i false;rw[ih (step s g) hi'];exact _i _ _ _ _ hi
lemma fE (gs:List Gate) (s:State):(gs.foldl step s).1=gs.foldl (λ z g=>z ++ [value g z]) s.1:=by
 induction gs generalizing s with
 | nil=>rfl
 | cons g gs ih=>simpa only[foldl_cons,step] using ih (step s g)
lemma fg (gs:List Gate) (s:State):(gs.foldl step s).2.2.1=gs.foldl (λ w g=>w ++ [value g w]) s.2.2.1:=by
 induction gs generalizing s with
 | nil=>rfl
 | cons g gs ih=>simpa only[foldl_cons,step] using ih (step s g)
lemma n2 (gs:List Gate) (s:State):(gs.foldl step s).2.2.2=gs.foldl (λ d g=>d ++ [g.lineDegree d]) s.2.2.2:=by
 induction gs generalizing s with
 | nil=>rfl
 | cons g gs ih=>simpa only[foldl_cons,step] using ih (step s g)
lemma V5 (b:Bool):At b false b 0:=by cases b <;> simp[At]
lemma TY (b:Bool):At false b b 1:=by cases b <;> simp[At]
def vC (x y:List Bool):State:=(x ++ replicate y.length false,replicate x.length false ++ y,x ++ y,replicate x.length 0 ++ replicate y.length 1)
lemma Zo (x y:List Bool):mi (x ++ replicate y.length false) (replicate x.length false ++ y) (x ++ y) (replicate x.length 0 ++ replicate y.length 1):=by
 intro i;by_cases hi:i < x.length
 · rw[_i x _ false i hi,_i (replicate x.length false) y false i (by simpa using hi),_i x y false i hi,_i (replicate x.length 0) _ 0 i (by simpa using hi),List.getD_replicate false hi,List.getD_replicate 0 hi];exact V5 (x.getD i false)
 · by_cases hj:i-x.length < y.length
   · rw[_g x _ false i (by omega),_g (replicate x.length false) y false i (by simpa using Nat.le_of_not_gt hi),_g x y false i (by omega),_g (replicate x.length 0) _ 0 i (by simpa using Nat.le_of_not_gt hi)];simp only[_f];rw[List.getD_replicate false hj,List.getD_replicate 1 hj];exact TY (y.getD (i-x.length) false)
   · have XB:x.length+y.length≤ i:=by omega
     have hz:(x ++ replicate y.length false).length≤ i:=by simpa using XB
     have hp:(replicate x.length false ++ y).length≤ i:=by simpa using XB
     have hw:(x ++ y).length≤ i:=by simpa using XB
     have hd:(replicate x.length 0 ++ replicate y.length 1).length≤ i:=by simpa using XB
     rw[_j _ _ hz,_j _ _ hp,_j _ _ hw,_j _ _ hd];exact cN
lemma kC (x y:List Bool):x6 (vC x y):=by
 refine⟨by simp[vC],by simp[vC],by simp[vC],?_⟩
 exact Zo x y
lemma w7 (C:_a) (hm:_b C) (x y:List Bool):x6 (C.gates.foldl step (vC x y)):=by
 apply Wi C.gates (vC x y) (kC x y)
 intro g hg;obtain⟨kf,y5⟩:=hm g hg;exact⟨by simpa only[Set.mem_insert_iff,Set.mem_singleton_iff] using kf,y5⟩
lemma fI {z p w:Bool} {d:ℕ} (h:At z p w d) (hd:d≤1) (hw:w=true) (hz:z=false):p=true:=by have zD:=h.2.2.2 hd;simpa[hw,hz] using zD.symm
lemma go {z p w:Bool} {d:ℕ} (h:At z p w d) (hd:d=0):w=z:=by have zD:=h.2.2.2 (by omega:d≤1);simpa[h.2.2.1 hd] using zD
end M4
namespace M1
open M2
abbrev gD:=M4.State
abbrev yX:=M4.step
abbrev bF:=M4.x6
lemma mZ (g:Gate) (Z P:List Bool):yr g (λ r=>Z.getD r false) (λ r=>P.getD r false)=M4.un g Z P:=by
 rcases g with ⟨op,rs⟩
 cases op with
 | or=>rfl
 | and=>
  cases rs with
  | nil=>rfl
  | cons r rs=>
   cases rs with
   | nil=>rfl
   | cons t rs=>cases rs <;> rfl
 | not=>rfl
 | mod n=>rfl
 | maj=>rfl
lemma gg (z:ℕ) (gs:List Gate) (s:State) (c:gD) (labels:ℕ→ Bool) (hz:c.1.length+gs.length≤ z) (y5:(u3 s).length=c.1.length) (hl:∀ r,labels r=(gs.foldl yX c).1.getD r false) (r:ℕ):labels (zq z s r)=c.1.getD r false:=by
 by_cases hr:r < (u3 s).length
 · rw[nd z s r hr,hl];exact M4.Y7 gs c r (by omega)
 · rw[ng z s r (by omega),hl]
   have hz':(gs.foldl yX c).1.length≤ z:=by rw[(M4.jx gs c).1];exact hz
   rw[_j _ _ hz',_j _ _ (by omega:c.1.length≤ r)]
lemma dB (N z:ℕ) (gs:List Gate) (s:State) (c:gD) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=N) (hc:bF c) (hd:degrees s=c.2.2.2) (y5:(u3 s).length=c.1.length) (hn:0 < (net s).length) (hb:j8 N s) (O5:cF N s) (hz:c.1.length+gs.length≤ z) (hl:∀ r,labels r=(gs.foldl yX c).1.getD r false) (hf:(run (net s) labels y).getD N false=false) (Zm:∀ r,(degrees s).getD r 0≤2→(run (net s) labels y).getD ((u3 s).getD r N) false=c.2.1.getD r false) (hm:∀ g∈gs,(g.op=.and∨g.op=.or)∧g.inputs.length≤2):∀ r,(degrees (gs.foldl (ya N z) s)).getD r 0≤2→(run (net (gs.foldl (ya N z) s)) labels y).getD ((u3 (gs.foldl (ya N z) s)).getD r N) false=(gs.foldl yX c).2.1.getD r false:=by
 induction gs generalizing s c with
 | nil=>exact Zm
 | cons g gs ih=>
  have hg:=hm g List.mem_cons_self;have hc':bF (yX c g):=M4.nc c g hc hg.1 hg.2;have hd':degrees (ya N z s g)=(yX c g).2.2.2:=by simp only[yC,yX,M4.step,hd]
  have y5':(u3 (ya N z s g)).length=(yX c g).1.length:=by simp only[xd,yX,M4.step,_c,_d,y5]
  have hn':0 < (net (ya N z s g)).length:=by rw[zG,_c];omega
  have hb':=ql N z s g hn hb;have O5':=f5 N z s g (by rw[hd];exact y5.trans hc.2.2.1) O5
  have hz':(yX c g).1.length+gs.length≤ z:=by
   have OH:(yX c g).1.length=c.1.length+1:=by simp[yX,M4.step]
   rw[OH];simp only[_e] at hz;omega
  have hl':∀ r,labels r=(gs.foldl yX (yX c g)).1.getD r false:=hl;have VW:(run (net s) labels y).length=N+(net s).length:=by rw[zv,hy]
  have hN:N < (run (net s) labels y).length:=by rw[VW];omega
  have Pc:∀ r,(u3 s).getD r N < (run (net s) labels y).length:=by intro r;rw[VW];exact uR (u3 s) N (N+(net s).length) hb (by omega) r
  have hf':(run (net (ya N z s g)) labels y).getD N false=false:=by rw[zG,na,zr _ _ _ _ hN,hf]
  have Rl:=cj N z s g labels (run (net s) labels y) c.2.1
   VW (by rw[hd];exact hc.2.2.1.symm.trans y5.symm)
   (hc.1.symm.trans y5.symm) hf hN Pc
   (λ r hr=>by rw[O5 r hr];exact hf) Zm
   (λ r hr=>M4.ni g (degrees s) r hg.1 hg.2 hr) hg.1 hg.2
  have LX:yr g (λ r=>labels (zq z s r)) (λ r=>c.2.1.getD r false)=M4.un g c.1 c.2.1:=by
   rw[← mZ];apply uQ
   · intro r hr;exact gg z (g :: gs) s c labels hz y5 hl r
   · intro r hr;rfl
  have Zm':∀ r,(degrees (ya N z s g)).getD r 0≤2→(run (net (ya N z s g)) labels y).getD ((u3 (ya N z s g)).getD r N) false=(yX c g).2.1.getD r false:=by intro r hr;rw[zG,na];simpa only[yX,M4.step,LX] using Rl r hr
  exact ih (ya N z s g) (yX c g) hc' hd' y5' hn' hb' O5' hz' hl' hf' Zm' (λ h hh=>hm h (List.mem_cons_of_mem g hh))
def vy (N:ℕ) (C:_a) (x:List Bool):ℕ→ Bool:=λ r=>(C.wires (x ++ replicate N false)).getD r false
def yn (C:_a) (x y:List Bool):gD:=C.gates.foldl yX (M4.vC x y)
lemma ka (N:ℕ) (C:_a) (x y:List Bool) (hy:y.length=N):(yn C x y).1=C.wires (x ++ replicate N false):=by unfold yn;rw[M4.fE];simp only[M4.vC,hy];rfl
lemma u8 (C:_a) (x y:List Bool):(yn C x y).2.2.1=C.wires (x ++ y):=by unfold yn;rw[M4.fg];rfl
lemma qO (N:ℕ) (C:_a) (x y:List Bool) (hx:x.length=N) (hy:y.length=N):(yn C x y).2.2.2=C.lineDegrees (N+N) (Ico N (N+N)):=by unfold yn;rw[M4.n2];change C.gates.foldl (λ d g=>d ++ [g.lineDegree d]) (replicate x.length 0 ++ replicate y.length 1)=_;rw[hx,hy];change C.gates.foldl (λ d g=>d ++ [g.lineDegree d]) (degrees (vC N))=_;rw[uc N];rfl
lemma u0 (N:ℕ) (C:_a) (hm:_b C) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (r:ℕ) (hr:(C.lineDegrees (N+N) (Ico N (N+N))).getD r 0≤2):(run (net (yZ N C)) (vy N C x) y).getD ((u3 (yZ N C)).getD r N) false=(yn C x y).2.1.getD r false:=by
 have h:=dB N (N+N+C.size) C.gates (vC N)
  (M4.vC x y)
  (vy N C x) y hy
  (M4.kC x y)
  (by simp[vC,degrees,M4.vC,hx,hy])
  (by simp[vC,u3,M4.vC,hx,hy])
  (by simp[vC,net]) (qt N) (dL N)
  (by simp[M4.vC,hx,hy,Circuit.size])
  (by
   intro i;change (C.wires (x ++ replicate N false)).getD i false=(yn C x y).1.getD i false;rw[ka N C x y hy])
  (by
   simpa only[yp,List.foldl_nil] using q3 N (N+N+C.size) [] (vy N C x) y hy)
  (by
   intro i hi;simpa only[M4.vC,hx] using fz N (vy N C x) y hy i)
  (by
   intro g hg;obtain⟨kf,x8⟩:=hm g hg;exact⟨by simpa only[Set.mem_insert_iff,Set.mem_singleton_iff] using kf,x8⟩)
  r
 apply h
 change (degrees (yZ N C)).getD r 0≤2;rw[wt];exact hr
lemma k7 (N:ℕ) (C:_a) (hm:_b C) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (r:ℕ) (hr:(C.lineDegrees (N+N) (Ico N (N+N))).getD r 0≤2) (hv:(run (net (yZ N C)) (vy N C x) y).getD ((u3 (yZ N C)).getD r N) false=true):(C.wires (x ++ y)).getD r false=true:=by rw[u0 N C hm x y hx hy r hr] at hv;have ha:=(M4.w7 C hm x y).2.2.2 r;have hw:=ha.2.1 hv;change (yn C x y).2.2.1.getD r false=true at hw;rw[u8] at hw;exact hw
lemma zE (N:ℕ) (C:_a) (hm:_b C) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (r:ℕ) (hr:(C.lineDegrees (N+N) (Ico N (N+N))).getD r 0≤1) (hw:(C.wires (x ++ y)).getD r false=true) (hz:(C.wires (x ++ replicate N false)).getD r false=false):(run (net (yZ N C)) (vy N C x) y).getD ((u3 (yZ N C)).getD r N) false=true:=by
 rw[u0 N C hm x y hx hy r (by omega)];have ha:=(M4.w7 C hm x y).2.2.2 r;apply M4.fI ha
 · change (yn C x y).2.2.2.getD r 0≤1;rw[qO N C x y hx hy];exact hr
 · change (yn C x y).2.2.1.getD r false=true;rw[u8];exact hw
 · change (yn C x y).1.getD r false=false;rw[ka N C x y hy];exact hz
open M2
def wz {N:ℕ} (z:Fin (N+N)→ Bool):List Bool:=ofFn (λ p:Fin N=>z (_7 N p))
def uW {N:ℕ} (z:Fin (N+N)→ Bool):List Bool:=ofFn (λ l:Fin N=>z (_8 N l))
lemma cQ {N:ℕ} (z:Fin (N+N)→ Bool):ofFn z=wz z ++ uW z:=by exact List.ofFn_add (f:=z)
def yd {N:ℕ} (p l:Fin N):Fin (N+N)→ Bool:=λ v=>if v=_7 N p then true else if v=_8 N l then true else false
def yG {N:ℕ} (p:Fin N):Fin (N+N)→ Bool:=λ v=>decide (v=_7 N p)
lemma uU {N:ℕ} (p l:Fin N):_7 N p≠_8 N l:=by intro h;have hv:=_9 Fin.val h;simp only[Fin.val_castAdd,Fin.val_natAdd] at hv;omega
lemma ck {N:ℕ} (p l q:Fin N):yd p l (_7 N q)=decide (q=p):=by simp only[yd,uU,↓reduceIte,Fin.castAdd_inj];split <;> simp_all
lemma c6 {N:ℕ} (p l u:Fin N):yd p l (_8 N u)=decide (u=l):=by have hn:_8 N u≠_7 N p:=(uU p u).symm;simp only[yd,hn,↓reduceIte,Fin.natAdd_inj];split <;> simp_all
lemma dc {N:ℕ} (p q:Fin N):yG p (_7 N q)=decide (q=p):=by simp[yG]
lemma cc {N:ℕ} (p u:Fin N):yG p (_8 N u)=false:=by have hn:_8 N u≠_7 N p:=(uU p u).symm;simp only[yG,hn,decide_false]
lemma uZ {N:ℕ} (p l:Fin N):wz (yd p l)=ofFn (λ q:Fin N=>decide (q=p)):=by simp only[wz,ck]
lemma kI {N:ℕ} (p l:Fin N):uW (yd p l)=ofFn (λ u:Fin N=>decide (u=l)):=by simp only[uW,c6]
lemma nj {N:ℕ} (p:Fin N):ofFn (yG p)=ofFn (λ q:Fin N=>decide (q=p)) ++ replicate N false:=by rw[cQ];simp only[wz,uW,dc,cc,List.ofFn_const]
lemma nV {N:ℕ} (p l:Fin N):ofFn (yd p l)=ofFn (λ q:Fin N=>decide (q=p)) ++ ofFn (λ u:Fin N=>decide (u=l)):=by rw[cQ,uZ,kI]
end M1
namespace Ka
open M2
def xy (n:ℕ) (gs:List vg) (r:ℕ):List ℕ→ List vg× ℕ
 | []=>(gs,r)
 | s :: rs=>xy n (gs ++ [Sum.inl [r,s]]) (n+gs.length) rs
def yA (n:ℕ) (gs:List vg):List ℕ→ List vg× ℕ
 | []=>(gs,n)
 | r :: rs=>xy n gs r rs
@[local simp] lemma aggregate_nil (n : ℕ) (gs : List vg) : yA n gs [] = (gs, n) := rfl
@[local simp] lemma aggregate_singleton (n : ℕ) (gs : List vg) (r : ℕ) : yA n gs [r] = (gs, r) := rfl
lemma hY (n:ℕ) (gs:List vg) (r:ℕ) (rs:List ℕ):∃ hs:List vg,(xy n gs r rs).1=gs ++ hs∧hs.length=rs.length∧∀ g∈hs,∃ us,g=Sum.inl us∧us.length=2:=by
 induction rs generalizing gs r with
 | nil=>exact⟨[],by simp[xy],rfl,by simp⟩
 | cons s rs ih=>
  obtain⟨hs,zD,y5,wv⟩:=ih (gs ++ [Sum.inl [r,s]]) (n+gs.length);refine⟨Sum.inl [r,s] :: hs,?_,by simp[y5],?_⟩
  · simpa only[xy,List.append_assoc,List.singleton_append] using zD
  · intro g hg;rcases List.mem_cons.mp hg with rfl | hg
    · exact⟨[r,s],rfl,rfl⟩
    · exact wv g hg
lemma zO (n:ℕ) (gs:List vg) (rs:List ℕ):∃ hs:List vg,(yA n gs rs).1=gs ++ hs∧hs.length=rs.length-1∧∀ g∈hs,∃ us,g=Sum.inl us∧us.length=2:=by
 cases rs with
 | nil=>exact⟨[],by simp,rfl,by simp⟩
 | cons r rs=>simpa only[yA,_e,Nat.add_sub_cancel] using hY n gs r rs
lemma pd (n:ℕ) (gs:List vg) (rs:List ℕ):(yA n gs rs).1.length=gs.length+(rs.length-1):=by obtain⟨hs,zD,y5,_⟩:=zO n gs rs;simp[zD,y5]
lemma g2 (n:ℕ) (gs:List vg) (r:ℕ) (rs:List ℕ) (hr:r < n+gs.length):(xy n gs r rs).2 < n+(xy n gs r rs).1.length:=by
 induction rs generalizing gs r with
 | nil=>exact hr
 | cons s rs ih=>
  apply ih
  simp
lemma ug (n:ℕ) (gs:List vg) (rs:List ℕ) (hz:gs.head?=some (Sum.inl [])) (pE:∀ r∈rs,r < n+gs.length):(yA n gs rs).2 < n+(yA n gs rs).1.length:=by
 cases rs with
 | nil=>
  have qX:0 < gs.length:=by
   cases gs with
   | nil=>simp at hz
   | cons g gs=>simp
  simpa only[yA] using (show n < n+gs.length by omega)
 | cons r rs=>exact g2 n gs r rs (pE r (by simp))
lemma Wp (n:ℕ) (gs:List vg) (hz:gs.head?=some (Sum.inl [])) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n):(run gs labels y).getD n false=false:=by
 cases gs with
 | nil=>simp at hz
 | cons g gs=>
  have hg:g=Sum.inl []:=Option.some.inj hz;subst g;rw[xU];simp only[step,List.map_nil,List.any_nil];rw[zr gs labels (y ++ [false]) n (by simp[hy])];rw[_g _ _ _ _ (by omega)];simp[hy]
lemma bt (n:ℕ) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n) (gs:List vg) (r:ℕ) (rs:List ℕ) (hr:r < n+gs.length) (pE:∀ s∈rs,s < n+gs.length):(run (xy n gs r rs).1 labels y).getD (xy n gs r rs).2 false=true↔(run gs labels y).getD r false=true∨∃ s∈rs,(run gs labels y).getD s false=true:=by
 induction rs generalizing gs r with
 | nil=>simp[xy]
 | cons s rs ih=>
  have hs:s < n+gs.length:=pE s (by simp);have Oq:∀ t∈rs,t < n+(gs ++ [Sum.inl [r,s]]).length:=by intro t ht;have h:=pE t (by simp[ht]);simpa only[_c,_d] using (show t < n+(gs.length+1) by omega)
  have S0:n+gs.length < n+(gs ++ [Sum.inl [r,s]]).length:=by simp
  rw[xy,ih _ _ S0 Oq];have TE:(run (gs ++ [Sum.inl [r,s]]) labels y).getD (n+gs.length) false=((run gs labels y).getD r false || (run gs labels y).getD s false):=by simpa[hy,step] using wN gs (Sum.inl [r,s]) labels y
  rw[TE,_r];have hold (t:ℕ) (ht:t∈rs):(run (gs ++ [Sum.inl [r,s]]) labels y).getD t false=(run gs labels y).getD t false:=by
   apply kL
   have h:=pE t (by simp[ht]);simpa only[hy] using h
  constructor
  · rintro ((hr | hs) | ⟨t,ht,hv⟩)
    · exact Or.inl hr
    · exact Or.inr ⟨s,by simp,hs⟩
    · exact Or.inr ⟨t,by simp[ht],(hold t ht)▸hv⟩
  · rintro (hr | ⟨t,ht,htval⟩)
    · exact Or.inl (Or.inl hr)
    · rcases List.mem_cons.mp ht with hts | ht
      · subst t;exact Or.inl (Or.inr htval)
      · exact Or.inr ⟨t,ht,(hold t ht).symm▸htval⟩
lemma cV (n:ℕ) (gs:List vg) (rs:List ℕ) (hz:gs.head?=some (Sum.inl [])) (pE:∀ r∈rs,r < n+gs.length) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n):(run (yA n gs rs).1 labels y).getD (yA n gs rs).2 false=true↔∃ r∈rs,(run gs labels y).getD r false=true:=by
 cases rs with
 | nil=>
  change (run gs labels y).getD n false=true↔∃ r∈([]:List ℕ),(run gs labels y).getD r false=true;rw[Wp n gs hz labels y hy];simp
 | cons r rs=>
  rw[yA,bt n labels y hy gs r rs (pE r (by simp)) (λ s hs=>pE s (by simp[hs]))];simp
lemma cp (n:ℕ) (gs:List vg) (rs:List ℕ) (x8:∀ us,Sum.inl us∈gs→ us.length≤2):∀ us,Sum.inl us∈(yA n gs rs).1→ us.length≤2:=by
 obtain⟨hs,zD,_,wv⟩:=zO n gs rs;intro us hu;rw[zD] at hu;rcases List.mem_append.mp hu with hu | hu
 · exact x8 us hu
 · obtain⟨vs,he,hv⟩:=wv (Sum.inl us) hu;have NJ:us=vs:=Sum.inl.inj he;simp[NJ,hv]
lemma cP (n:ℕ) (gs:List vg) (rs:List ℕ) (hz:gs.head?=some (Sum.inl [])):(yA n gs rs).1.head?=some (Sum.inl []):=by
 obtain⟨hs,zD,_,_⟩:=zO n gs rs;rw[zD];cases gs with
 | nil=>simp at hz
 | cons g gs=>simpa using hz
end Ka
namespace M0
open M2 Ka
abbrev State:=List vg×((ℕ→ ℕ)×(ℕ→ ℕ))
def net (s:State):List vg:=s.1
def yR (s:State):ℕ→ ℕ:=s.2.1
def yj (s:State):ℕ→ ℕ:=s.2.2
def vC (n:ℕ) (gs:List vg):State:=(gs,(λ _=>n,λ _=>n))
def zP (vn vm:List (ℕ× ℕ)) (pj:ℕ→ ℕ) (v:ℕ):List ℕ:=((vn.filter λ e=>decide (e.1=v)).map Prod.snd) ++ ((vm.filter λ e=>decide (e.2=v)).map λ e=>pj e.1)
def y1 (vn vm:List (ℕ× ℕ)) (v:ℕ):ℕ:=(vn.filter λ e=>decide (e.1=v)).length+(vm.filter λ e=>decide (e.2=v)).length
lemma cw (vn vm:List (ℕ× ℕ)) (pj:ℕ→ ℕ) (v:ℕ):(zP vn vm pj v).length=y1 vn vm v:=by simp[zP,y1]
lemma jD (vn vm:List (ℕ× ℕ)) (pj:ℕ→ ℕ) (v r:ℕ):r∈zP vn vm pj v↔(∃ e∈vn,e.1=v∧e.2=r)∨(∃ e∈vm,e.2=v∧pj e.1=r):=by simp[zP,and_assoc]
def step (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State):State:=
 let a:=yA n (net s) (zP vn vm (yj s) v);match vo v with
 | none=>(a.1,(Function.update (yR s) v a.2,Function.update (yj s) v a.2))
 | some z=>(a.1 ++ [Sum.inr (z,a.2)],(Function.update (yR s) v a.2,Function.update (yj s) v (n+a.1.length)))
def yp (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ):ℕ→ State→ State
 | 0,s=>s
 | k+1,s=>yp n vn vm vo k (step n vn vm vo k s)
def gp (n:ℕ) (s:State):Prop:=(net s).head?=some (Sum.inl [])∧(∀ v,yR s v < n+(net s).length)∧(∀ v,yj s v < n+(net s).length)
lemma kC (n:ℕ) (gs:List vg) (h:gs.head?=some (Sum.inl [])):gp n (vC n gs):=by
 have hp:0 < gs.length:=by
  cases gs with
  | nil=>simp at h
  | cons g gs=>simp
 exact⟨h,λ _=>by simpa[vC,yR,net] using (show n < n+gs.length by omega),λ _=>by simpa[vC,yj,net] using (show n < n+gs.length by omega)⟩
lemma j0 (n:ℕ) (vn vm:List (ℕ× ℕ)) (v:ℕ) (s:State) (hs:gp n s) (ke:∀ e∈vn,e.2 < n+(net s).length):∀ r∈zP vn vm (yj s) v,r < n+(net s).length:=by
 intro r hr;rcases (jD vn vm (yj s) v r).mp hr with h | h
 · obtain⟨e,he,_,rfl⟩:=h;exact ke e he
 · obtain⟨e,_,_,rfl⟩:=h;exact hs.2.2 e.1
lemma mx (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State):∃ hs,net (step n vn vm vo v s)=net s ++ hs:=by
 obtain⟨hs,h,_,_⟩:=zO n (net s) (zP vn vm (yj s) v);cases hw:vo v with
 | none=>exact⟨hs,by simpa[step,net,hw] using h⟩
 | some z=>
  refine⟨hs ++ [Sum.inr (z,(yA n (net s) (zP vn vm (yj s) v)).2)],?_⟩
  simp only[step,hw,net];simp only[net] at h;rw[h,List.append_assoc]
lemma d1 (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State):(net (step n vn vm vo v s)).length=(net s).length+(y1 vn vm v-1)+(if (vo v).isSome then 1 else 0):=by
 cases hw:vo v <;>
  simp[step,net,hw,pd,cw]
lemma cO (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State):(net s).length≤(net (step n vn vm vo v s)).length:=by rw[d1];omega
lemma qT (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n) (r:ℕ) (hr:r < n+(net s).length):(run (net (step n vn vm vo v s)) labels y).getD r false=(run (net s) labels y).getD r false:=by obtain⟨hs,he⟩:=mx n vn vm vo v s;rw[he,na];exact zr hs labels _ r (by simpa only[zv,hy] using hr)
lemma ch (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State):yR (step n vn vm vo v s) v=(yA n (net s) (zP vn vm (yj s) v)).2:=by cases hw:vo v <;> simp[step,yR,hw]
lemma ci (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State) (u:ℕ) (hu:u≠v):yR (step n vn vm vo v s) u=yR s u:=by cases hw:vo v <;> simp[step,yR,hw,hu]
lemma cg (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State) (u:ℕ) (hu:u≠v):yj (step n vn vm vo v s) u=yj s u:=by cases hw:vo v <;> simp[step,yj,hw,hu]
lemma nc (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State) (hs:gp n s) (ke:∀ e∈vn,e.2 < n+(net s).length):gp n (step n vn vm vo v s):=by
 let a:=yA n (net s) (zP vn vm (yj s) v);have ha:a.2 < n+a.1.length:=ug n (net s) _ hs.1 (j0 n vn vm v s hs ke);have hh:a.1.head?=some (Sum.inl []):=cP n (net s) _ hs.1;have hl:(net s).length≤ a.1.length:=by dsimp[a];rw[pd];omega
 cases hw:vo v with
 | none=>
  change (net (step n vn vm vo v s)).head?=_∧_;refine⟨by simpa only[step,net,hw,a] using hh,?_,?_⟩
  · intro u;simp only[yR,step,hw,net];change Function.update (yR s) v a.2 u < n+a.1.length;by_cases hu:u=v
    · simpa[hu] using ha
    · simpa[hu] using (show yR s u < n+a.1.length by have:=hs.2.1 u;omega)
  · intro u;simp only[yj,step,hw,net];change Function.update (yj s) v a.2 u < n+a.1.length;by_cases hu:u=v
    · simpa[hu] using ha
    · simpa[hu] using (show yj s u < n+a.1.length by have:=hs.2.2 u;omega)
 | some z=>
  have vK:(a.1 ++ [Sum.inr (z,a.2)]).head?=some (Sum.inl []):=by
   cases he:a.1 with
   | nil=>simp[he] at hh
   | cons g gs=>simpa[he] using hh
  refine⟨by simpa only[step,net,hw,a] using vK,?_,?_⟩
  · intro u;simp only[yR,step,hw,net];change Function.update (yR s) v a.2 u < n+(a.1 ++ [Sum.inr (z,a.2)]).length;simp only[_c,_d];by_cases hu:u=v
    · simpa[hu] using (show a.2 < n+(a.1.length+1) by omega)
    · simpa[hu] using (show yR s u < n+(a.1.length+1) by have:=hs.2.1 u;omega)
  · intro u;simp only[yj,step,hw,net];change Function.update (yj s) v (n+a.1.length) u < n+(a.1 ++ [Sum.inr (z,a.2)]).length;simp only[_c,_d];by_cases hu:u=v
    · simp[hu]
    · simpa[hu] using (show yj s u < n+(a.1.length+1) by have:=hs.2.2 u;omega)
def yo (labels:ℕ→ Bool) (vo:ℕ→ Option ℕ) (v:ℕ):Bool:=(vo v).elim true labels
lemma fy (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State) (hs:gp n s) (ke:∀ e∈vn,e.2 < n+(net s).length) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n):(run (net (step n vn vm vo v s)) labels y).getD (yR (step n vn vm vo v s) v) false=true↔∃ r∈zP vn vm (yj s) v,(run (net s) labels y).getD r false=true:=by
 let rs:=zP vn vm (yj s) v;have pE:=j0 n vn vm v s hs ke;have ht:=cV n (net s) rs hs.1 pE labels y hy;have hr:=ug n (net s) rs hs.1 pE;rw[ch];cases hw:vo v with
 | none=>simpa only[step,net,hw,rs] using ht
 | some z=>
  change (run (net (step n vn vm vo v s)) labels y).getD (yA n (net s) rs).2 false=true↔_;have hn:net (step n vn vm vo v s)=(yA n (net s) rs).1 ++ [Sum.inr (z,(yA n (net s) rs).2)]:=by simp only[step,net,hw,rs]
  rw[hn,kL _ _ labels y _ (by simpa only[hy] using hr)];exact ht
lemma fS (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State) (hs:gp n s) (ke:∀ e∈vn,e.2 < n+(net s).length) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n):(run (net (step n vn vm vo v s)) labels y).getD (yj (step n vn vm vo v s) v) false=true↔yo labels vo v=true∧(run (net (step n vn vm vo v s)) labels y).getD (yR (step n vn vm vo v s) v) false=true:=by
 let a:=yA n (net s) (zP vn vm (yj s) v);have ha:a.2 < n+a.1.length:=ug n (net s) _ hs.1 (j0 n vn vm v s hs ke);cases hw:vo v with
 | none=>simp[step,net,yR,yj,hw,yo]
 | some z=>
  simp only[step,net,yR,yj,hw,Function.update_self,yo,Option.elim_some];change (run (a.1 ++ [Sum.inr (z,a.2)]) labels y).getD (n+a.1.length) false=true↔labels z=true∧(run (a.1 ++ [Sum.inr (z,a.2)]) labels y).getD a.2 false=true;have hn:=wN a.1 (Sum.inr (z,a.2)) labels y;rw[hy] at hn;rw[hn,kL _ _ labels y _ (by simpa only[hy] using ha)];simp[M2.step]
lemma nO (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State) (hs:gp n s) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n) (u:ℕ) (hu:u≠v):(run (net (step n vn vm vo v s)) labels y).getD (yR (step n vn vm vo v s) u) false=(run (net s) labels y).getD (yR s u) false:=by rw[ci _ _ _ _ _ _ _ hu];exact qT n vn vm vo v s labels y hy _ (hs.2.1 u)
lemma mu (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State) (hs:gp n s) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n) (u:ℕ) (hu:u≠v):(run (net (step n vn vm vo v s)) labels y).getD (yj (step n vn vm vo v s) u) false=(run (net s) labels y).getD (yj s u) false:=by rw[cg _ _ _ _ _ _ _ hu];exact qT n vn vm vo v s labels y hy _ (hs.2.2 u)
end M0
namespace K4
def pT {σ:Type*} (step:ℕ→ σ→ σ):ℕ→ σ→ σ
 | 0,s=>s
 | k+1,s=>pT step k (step k s)
def YA {σ:Type*} (V:ℕ) (Xp fj:σ→ ℕ→ Bool) (vo v8:ℕ→ Bool) (k:ℕ) (s:σ):Prop:=∀ u,k≤ u→ u < V→ Xp s u=v8 u∧fj s u=(vo u && v8 u)
lemma fe {σ:Type*} (V:ℕ) (step:ℕ→ σ→ σ) (Xp fj:σ→ ℕ→ Bool) (vo v8:ℕ→ Bool) (x6:σ→ Prop) (XG:∀ v,v < V→∀ s,x6 s→ x6 (step v s)) (gX:∀ v,v < V→∀ s,x6 s→∀ u,u≠v→ Xp (step v s) u=Xp s u∧fj (step v s) u=fj s u) (S0:∀ v,v < V→∀ s,x6 s→(∀ u,v < u→ u < V→ fj s u=(vo u && v8 u))→ Xp (step v s) v=v8 v∧fj (step v s) v=(vo v && v8 v)):∀ k,k≤ V→∀ s,x6 s→ YA V Xp fj vo v8 k s→ x6 (pT step k s)∧YA V Xp fj vo v8 0 (pT step k s):=by
 intro k;induction k with
 | zero=>
  intro _ s hs hc;exact⟨hs,hc⟩
 | succ k ih=>
  intro hk s hs hc;have Ln:k < V:=by omega
  have hn:=S0 k Ln s hs (by
   intro u Kp hu;exact (hc u (by omega) hu).2)
  have QU:YA V Xp fj vo v8 k (step k s):=by
   intro u Kp hu;by_cases huk:u=k
   · subst u;exact hn
   · obtain⟨Rt,Uv⟩:=gX k Ln s hs u huk;obtain⟨KX,L2⟩:=hc u (by omega) hu;exact⟨Rt.trans KX,Uv.trans L2⟩
  exact ih (by omega) (step k s) (XG k Ln s hs) QU
def zC (vm:List (ℕ× ℕ)) (v:ℕ) (fj:ℕ→ Bool):Bool:=vm.any λ e=>decide (e.2=v) && fj e.1
lemma b5 (V:ℕ) (vm:List (ℕ× ℕ)) (nE:∀ e∈vm,e.2 < e.1∧e.1 < V) (v:ℕ) (fj fj':ℕ→ Bool) (Uv:∀ u,v < u→ u < V→ fj u=fj' u):zC vm v fj=zC vm v fj':=by
 have Vv:∀ e∈vm,(decide (e.2=v) && fj e.1)=(decide (e.2=v) && fj' e.1):=by
  intro e he;by_cases Vp:e.2=v
  · obtain⟨z5,hb⟩:=nE e he;have hp:v < e.1:=by omega
    simp[Vp,Uv e.1 hp hb]
  · simp[Vp]
 apply Bool.eq_iff_iff.mpr
 simp only[zC,List.any_eq_true];constructor
 · rintro⟨e,he,hv⟩;exact⟨e,he,(Vv e he)▸hv⟩
 · rintro⟨e,he,hv⟩;exact⟨e,he,(Vv e he).symm▸hv⟩
theorem g3 {σ:Type*} (V:ℕ) (step:ℕ→ σ→ σ) (Xp fj:σ→ ℕ→ Bool) (vo v8 OG:ℕ→ Bool) (vm:List (ℕ× ℕ)) (x6:σ→ Prop) (nE:∀ e∈vm,e.2 < e.1∧e.1 < V) (XG:∀ v,v < V→∀ s,x6 s→ x6 (step v s)) (gX:∀ v,v < V→∀ s,x6 s→∀ u,u≠v→ Xp (step v s) u=Xp s u∧fj (step v s) u=fj s u) (Rt:∀ v,v < V→∀ s,x6 s→ Xp (step v s) v=(OG v || zC vm v (fj s))) (Uv:∀ v,v < V→∀ s,x6 s→ fj (step v s) v=(vo v && Xp (step v s) v)) (YE:∀ v,v < V→ v8 v=(OG v || zC vm v (λ u=>vo u && v8 u))) (vC:σ) (cU:x6 vC):x6 (pT step V vC)∧∀ u,u < V→ Xp (pT step V vC) u=v8 u∧fj (pT step V vC) u=(vo u && v8 u):=by
 have hn:∀ v,v < V→∀ s,x6 s→(∀ u,v < u→ u < V→ fj s u=(vo u && v8 u))→ Xp (step v s) v=v8 v∧fj (step v s) v=(vo v && v8 v):=by
  intro v hv s hs Um;have hc:Xp (step v s) v=v8 v:=by rw[Rt v hv s hs,b5 V vm nE v (fj s) (λ u=>vo u && v8 u) Um];exact (YE v hv).symm
  exact⟨hc,by rw[Uv v hv s hs,hc]⟩
 obtain⟨hf,hc⟩:=fe V step Xp fj vo v8 x6 XG gX hn V le_rfl vC cU (by
  intro u XA huu;omega)
 exact⟨hf,λ u hu=>hc u (Nat.zero_le _) hu⟩
end K4
namespace K2
open M2 M0
abbrev u1 (labels:ℕ→ Bool) (y:List Bool) (s:State) (w:ℕ):Bool:=(run (net s) labels y).getD w false
abbrev pZ (labels:ℕ→ Bool) (y:List Bool) (s:State) (v:ℕ):Bool:=u1 labels y s (yR s v)
abbrev mL (labels:ℕ→ Bool) (y:List Bool) (s:State) (v:ℕ):Bool:=u1 labels y s (yj s v)
def q9 (vn:List (ℕ× ℕ)) (yg:ℕ→ Bool) (v:ℕ):Bool:=vn.any λ e=>decide (e.1=v) && yg e.2
lemma bD (vn:List (ℕ× ℕ)) (yg:ℕ→ Bool) (v:ℕ):q9 vn yg v=true↔∃ e∈vn,e.1=v∧yg e.2=true:=by simp[q9]
lemma gO (vm:List (ℕ× ℕ)) (values:ℕ→ Bool) (v:ℕ):K4.zC vm v values=true↔∃ e∈vm,e.2=v∧values e.1=true:=by simp[K4.zC]
def qM (n:ℕ) (vn:List (ℕ× ℕ)) (labels:ℕ→ Bool) (y:List Bool) (yg:ℕ→ Bool) (s:State):Prop:=gp n s∧∀ e∈vn,e.2 < n+(net s).length∧u1 labels y s e.2=yg e.2
lemma YN (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n) (yg:ℕ→ Bool) (v:ℕ) (s:State) (hs:qM n vn labels y yg s):qM n vn labels y yg (M0.step n vn vm vo v s):=by
 refine⟨nc n vn vm vo v s hs.1 (λ e he=>(hs.2 e he).1),?_⟩
 intro e he;obtain⟨Vp,JA⟩:=hs.2 e he;have y5:=cO n vn vm vo v s;refine⟨by omega,?_⟩
 exact (qT n vn vm vo v s labels y hy e.2 Vp).trans JA
lemma Yl (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n) (yg:ℕ→ Bool) (v:ℕ) (s:State) (hs:qM n vn labels y yg s):pZ labels y (M0.step n vn vm vo v s) v=(q9 vn yg v || K4.zC vm v (mL labels y s)):=by
 apply Bool.eq_iff_iff.mpr
 rw[fy n vn vm vo v s hs.1 (λ e he=>(hs.2 e he).1) labels y hy];rw[_r,bD,gO];constructor
 · rintro⟨r,hr,hv⟩;rcases (jD vn vm (yj s) v r).mp hr with hh | hh
   · obtain⟨e,he,Vp,rfl⟩:=hh;exact Or.inl ⟨e,he,Vp,(hs.2 e he).2▸hv⟩
   · obtain⟨e,he,Vp,rfl⟩:=hh;exact Or.inr ⟨e,he,Vp,hv⟩
 · rintro (⟨e,he,Vp,hv⟩ | ⟨e,he,Vp,hv⟩)
   · refine⟨e.2,(jD vn vm (yj s) v e.2).mpr (Or.inl ⟨e,he,Vp,rfl⟩),?_⟩
     change u1 labels y s e.2=true;rw[(hs.2 e he).2];exact hv
   · exact⟨yj s e.1,(jD vn vm (yj s) v _).mpr (Or.inr ⟨e,he,Vp,rfl⟩),hv⟩
lemma Ys (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n) (yg:ℕ→ Bool) (v:ℕ) (s:State) (hs:qM n vn labels y yg s):mL labels y (M0.step n vn vm vo v s) v=(yo labels vo v && pZ labels y (M0.step n vn vm vo v s) v):=by
 apply Bool.eq_iff_iff.mpr
 rw[_s];exact fS n vn vm vo v s hs.1 (λ e he=>(hs.2 e he).1) labels y hy
lemma dd (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (k:ℕ) (s:State):yp n vn vm vo k s=K4.pT (M0.step n vn vm vo) k s:=by
 induction k generalizing s with
 | zero=>rfl
 | succ k ih=>exact ih _
theorem Zi (n V:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n) (yg v8:ℕ→ Bool) (nE:∀ e∈vm,e.2 < e.1∧e.1 < V) (YE:∀ v,v < V→ v8 v=(q9 vn yg v || K4.zC vm v (λ u=>yo labels vo u && v8 u))) (vC:State) (cU:qM n vn labels y yg vC):qM n vn labels y yg (yp n vn vm vo V vC)∧∀ u,u < V→ pZ labels y (yp n vn vm vo V vC) u=v8 u∧mL labels y (yp n vn vm vo V vC) u=(yo labels vo u && v8 u):=by
 have h:=K4.g3 V
  (M0.step n vn vm vo) (pZ labels y) (mL labels y)
  (yo labels vo) v8 (q9 vn yg) vm
  (qM n vn labels y yg) nE
  (λ v _ s hs=>YN n vn vm vo labels y hy yg v s hs)
  (λ v _ s hs u hu=>⟨ nO n vn vm vo v s hs.1 labels y hy u hu,mu n vn vm vo v s hs.1 labels y hy u hu⟩)
  (λ v _ s hs=>Yl n vn vm vo labels y hy yg v s hs)
  (λ v _ s hs=>Ys n vn vm vo labels y hy yg v s hs)
  YE vC cU
 simpa only[dd] using h
lemma bw (n:ℕ) (gs:List vg) (vn:List (ℕ× ℕ)) (hz:gs.head?=some (Sum.inl [])) (ke:∀ e∈vn,e.2 < n+gs.length) (labels:ℕ→ Bool) (y:List Bool):qM n vn labels y (λ r=>(run gs labels y).getD r false) (vC n gs):=by
 refine⟨kC n gs hz,?_⟩
 intro e he;exact⟨ke e he,rfl⟩
end K2
namespace Kf
def bf (vm:List (ℕ× ℕ)) (v5:ℕ→ Bool) (u v:ℕ):Prop:=(u,v)∈vm∧v5 u=true
def xj (vm:List (ℕ× ℕ)) (v5:ℕ→ Bool) (vn:List (ℕ× ℕ)) (yD:ℕ→ Bool) (v:ℕ):Prop:=∃ s∈vn,yD s.2=true∧_1 (bf vm v5) s.1 v
noncomputable def v8 (vm:List (ℕ× ℕ)) (v5:ℕ→ Bool) (vn:List (ℕ× ℕ)) (yD:ℕ→ Bool) (v:ℕ):Bool:=by
 classical
 exact decide (xj vm v5 vn yD v)
@[local simp] lemma wo (vm : List (ℕ × ℕ)) (v5 : ℕ → Bool) (vn : List (ℕ × ℕ)) (yD : ℕ → Bool) (v : ℕ) : v8 vm v5 vn yD v = true ↔ xj vm v5 vn yD v := by
 classical
 simp[v8]
theorem qC (vm:List (ℕ× ℕ)) (v5:ℕ→ Bool) (vn:List (ℕ× ℕ)) (yD:ℕ→ Bool) (v:ℕ):v8 vm v5 vn yD v=true↔(∃ s∈vn,s.1=v∧yD s.2=true)∨∃ e∈vm,e.2=v∧v5 e.1=true∧v8 vm v5 vn yD e.1=true:=by
 constructor
 · intro ht;obtain⟨s,hs,hb,hp⟩:=(wo vm v5 vn yD v).mp ht;rcases hp.cases_tail with h | ⟨u,MU,ZD⟩
   · exact Or.inl ⟨s,hs,h.symm,hb⟩
   · refine Or.inr ⟨(u,v),ZD.1,rfl,ZD.2,?_⟩
     exact (wo vm v5 vn yD u).mpr ⟨s,hs,hb,MU⟩
 · rintro (⟨s,hs,hv,hb⟩ | ⟨e,he,hv,hw,hu⟩)
   · apply (wo vm v5 vn yD v).mpr
     refine⟨s,hs,hb,?_⟩
     simpa only[hv] using (ReflTransGen.refl:_1 (bf vm v5) s.1 s.1)
   · obtain⟨s,hs,hb,MU⟩:=(wo vm v5 vn yD e.1).mp hu;apply (wo vm v5 vn yD v).mpr
     refine⟨s,hs,hb,MU.tail ?_⟩
     exact⟨by simpa only[← hv] using he,hw⟩
theorem md (vm:List (ℕ× ℕ)) (v5:ℕ→ Bool) (vn:List (ℕ× ℕ)) (yD:ℕ→ Bool) (v:ℕ):v8 vm v5 vn yD v=((vn.any λ s=>decide (s.1=v) && yD s.2) || (vm.any λ e=>decide (e.2=v) && (v5 e.1 && v8 vm v5 vn yD e.1))):=by
 apply Bool.eq_iff_iff.mpr
 rw[qC];simp only[_r,List.any_eq_true,_s,decide_eq_true_eq]
@[local simp] lemma target_empty_seeds (vm : List (ℕ × ℕ)) (v5 : ℕ → Bool) (yD : ℕ → Bool) (v : ℕ) : v8 vm v5 [] yD v = false := by
 classical
 simp[v8,xj]
end Kf
namespace K0
open M2 M0 K2
 theorem bx (n V:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n) (yg:ℕ→ Bool) (nE:∀ e∈vm,e.2 < e.1∧e.1 < V) (s:State) (hs:qM n vn labels y yg s):qM n vn labels y yg (yp n vn vm vo V s)∧∀ u,u < V→ pZ labels y (yp n vn vm vo V s) u=Kf.v8 vm (yo labels vo) vn yg u∧mL labels y (yp n vn vm vo V s) u=(yo labels vo u && Kf.v8 vm (yo labels vo) vn yg u):=by
  apply Zi n V vn vm vo labels y hy yg (Kf.v8 vm (yo labels vo) vn yg) nE (λ v _=>?_) s hs
  exact Kf.md vm (yo labels vo) vn yg v
 theorem b9 (n V:ℕ) (gs:List vg) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n) (hz:gs.head?=some (Sum.inl [])) (ke:∀ e∈vn,e.2 < n+gs.length) (nE:∀ e∈vm,e.2 < e.1∧e.1 < V):gp n (yp n vn vm vo V (vC n gs))∧∀ u,u < V→ pZ labels y (yp n vn vm vo V (vC n gs)) u=Kf.v8 vm (yo labels vo) vn (λ r=>(run gs labels y).getD r false) u∧mL labels y (yp n vn vm vo V (vC n gs)) u=(yo labels vo u && Kf.v8 vm (yo labels vo) vn (λ r=>(run gs labels y).getD r false) u):=by
  have h:=bx n V vn vm vo labels y hy
   (λ r=>(run gs labels y).getD r false) nE (vC n gs)
   (bw n gs vn hz ke labels y)
  exact⟨h.1.1,h.2⟩
 theorem dF (n V:ℕ) (gs:List vg) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n) (hz:gs.head?=some (Sum.inl [])) (ke:∀ e∈vn,e.2 < n+gs.length) (nE:∀ e∈vm,e.2 < e.1∧e.1 < V) (v:ℕ) (hv:v < V):pZ labels y (yp n vn vm vo V (vC n gs)) v=true↔Kf.xj vm (yo labels vo) vn (λ r=>(run gs labels y).getD r false) v:=by rw[((b9 n V gs vn vm vo labels y hy hz ke nE).2 v hv).1];exact Kf.wo vm (yo labels vo) vn (λ r=>(run gs labels y).getD r false) v
end K0
namespace M7
lemma ns {α:Type*} [_5 α] (V F:Finset α) (n:α→ ℕ) (hF:F⊆V) (hn:∀ v∈F,1≤ n v):(∑ v∈V,(n v-1))+F.card≤ ∑ v∈V,n v:=by
 classical
 have Z8:(∑ v∈V,if v∈F then (1:ℕ) else 0)=F.card:=by
  have ZW:V.filter (λ v=>v∈F)=F:=by ext v;simp only[mem_filter];exact⟨λ h=>h.2,λ h=>⟨hF h,h⟩⟩
  rw[← Finset.sum_filter];simp[ZW]
 rw[← Z8,← Finset.sum_add_distrib];apply sum_le_sum
 intro v hv;by_cases hf:v∈F
 · simp only[hf,↓reduceIte];have:=hn v hf;omega
 · simp[hf]
def wd {α:Type*} (v8:α→ ℕ) (xs:List α) (v:ℕ):ℕ:=(xs.filter λ x=>decide (v8 x=v)).length
lemma cr {α:Type*} (v8:α→ ℕ) (a:α) (xs:List α) (v:ℕ):wd v8 (a :: xs) v=(if v8 a=v then 1 else 0)+wd v8 xs v:=by by_cases h:v8 a=v <;> simp[wd,h,Nat.add_comm]
lemma b3 {α:Type*} (v8:α→ ℕ) (xs:List α) (B:ℕ):(∑ v∈Finset.range B,wd v8 xs v)=(xs.filter λ x=>decide (v8 x < B)).length:=by
 induction xs with
 | nil=>simp[wd]
 | cons a xs ih=>
  simp_rw [cr]
  rw[Finset.sum_add_distrib,ih];have R1:(∑ v∈Finset.range B,if v8 a=v then (1:ℕ) else 0)=if v8 a < B then 1 else 0:=by simp[eq_comm]
  rw[R1];by_cases h:v8 a < B <;> simp[h,Nat.add_comm]
theorem qu {α:Type*} (v8:α→ ℕ) (xs:List α) (B:ℕ):(∑ v∈Finset.range B,wd v8 xs v)≤ xs.length:=by rw[b3];exact List.length_filter_le _ _
def xf (vn vm:List (ℕ× ℕ)) (v:ℕ):ℕ:=wd Prod.fst vn v+wd Prod.snd vm v
theorem hW (vn vm:List (ℕ× ℕ)) (B:ℕ):(∑ v∈Finset.range B,xf vn vm v)≤ vn.length+vm.length:=by simp only[xf,Finset.sum_add_distrib];exact Nat.add_le_add (qu Prod.fst vn B) (qu Prod.snd vm B)
theorem pe (vn vm:List (ℕ× ℕ)) (B:ℕ) (yh:Finset ℕ) (hF:yh⊆Finset.range B) (q4:∀ v∈yh,1≤ xf vn vm v):(∑ v∈Finset.range B,(xf vn vm v-1))+yh.card≤ vn.length+vm.length:=by exact (ns (Finset.range B) yh (xf vn vm) hF q4).trans (hW vn vm B)
theorem fx (vn vm:List (ℕ× ℕ)) (B:ℕ) (yh:Finset ℕ) (hF:yh⊆Finset.range B) (q4:∀ v∈yh,1≤ xf vn vm v) (vC final weighted:ℕ) (Y3:final≤ vC+(∑ v∈Finset.range B,(xf vn vm v-1))+weighted):final+yh.card≤ vC+vn.length+vm.length+weighted:=by have:=pe vn vm B yh hF q4;omega
lemma c4 (cost:ℕ→ ℕ) (B:ℕ):((List.range B).map cost).sum=∑ v∈Finset.range B,cost v:=by
 induction B with
 | zero=>simp
 | succ B ih=>simp[List.range_succ,Finset.sum_range_succ,ih]
end M7
namespace K5
open M2 Ka M0
lemma jf (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (k:ℕ) (s:State):∃ hs,net (yp n vn vm vo k s)=net s ++ hs:=by
 induction k generalizing s with
 | zero=>exact⟨[],by simp[yp]⟩
 | succ k ih=>
  obtain⟨hs,he⟩:=mx n vn vm vo k s;obtain⟨ts,ht⟩:=ih (step n vn vm vo k s);exact⟨hs ++ ts,by simpa only[yp,he,List.append_assoc] using ht⟩
lemma bB (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (k:ℕ) (s:State) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=n) (r:ℕ) (hr:r < n+(net s).length):(run (net (yp n vn vm vo k s)) labels y).getD r false=(run (net s) labels y).getD r false:=by obtain⟨hs,he⟩:=jf n vn vm vo k s;rw[he,na];exact zr hs labels _ r (by simpa only[zv,hy] using hr)
lemma X2 (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State) (x8:∀ us,Sum.inl us∈net s→ us.length≤2):∀ us,Sum.inl us∈net (step n vn vm vo v s)→ us.length≤2:=by
 have ha:=cp n (net s) (zP vn vm (yj s) v) x8;cases hw:vo v with
 | none=>simpa only[M0.step,net,hw] using ha
 | some z=>
  intro us hu;simp only[M0.step,hw,net,List.mem_append,List.mem_singleton,reduceCtorEq,or_false] at hu;exact ha us hu
lemma Xh (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (k:ℕ) (s:State) (x8:∀ us,Sum.inl us∈net s→ us.length≤2):∀ us,Sum.inl us∈net (yp n vn vm vo k s)→ us.length≤2:=by
 induction k generalizing s with
 | zero=>exact x8
 | succ k ih=>
  exact ih (step n vn vm vo k s) (X2 n vn vm vo k s x8)
lemma Yj (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (k:ℕ) (s:State):(net (yp n vn vm vo k s)).length=(net s).length+∑ v∈Finset.range k,((y1 vn vm v-1)+(if (vo v).isSome then 1 else 0)):=by
 induction k generalizing s with
 | zero=>simp[yp]
 | succ k ih=>
  rw[yp,ih,d1,Finset.sum_range_succ];omega
def kx (vo:ℕ→ Option ℕ) (k:ℕ):ℕ:=∑ v∈Finset.range k,if (vo v).isSome then 1 else 0
def yh (vn vm:List (ℕ× ℕ)) (vI:Finset ℕ):Finset ℕ:=vI.filter λ v=>0 < y1 vn vm v
lemma xI (vn vm:List (ℕ× ℕ)) (v:ℕ):y1 vn vm v=M7.xf vn vm v:=rfl
lemma fm (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (k:ℕ) (s:State) (F:Finset ℕ) (hF:F⊆Finset.range k) (q4:∀ v∈F,0 < y1 vn vm v):(net (yp n vn vm vo k s)).length+F.card≤(net s).length+vn.length+vm.length+kx vo k:=by
 apply M7.fx vn vm k F hF
 · intro v hv;simpa only[← xI] using (Nat.succ_le_iff.mpr (q4 v hv))
 · rw[Yj,Finset.sum_add_distrib];simp only[kx,xI];omega
lemma Yu (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (k:ℕ) (s:State) (vI:Finset ℕ) (hF:vI⊆Finset.range k):(net (yp n vn vm vo k s)).length+(yh vn vm vI).card≤(net s).length+vn.length+vm.length+kx vo k:=by
 apply fm n vn vm vo k s (yh vn vm vI)
 · exact λ _ hv=>hF (_A hv).1
 · exact λ _ hv=>(_A hv).2
end K5
namespace M3
def kM {α β:Type*} (f:List α→ β→ α) (gs:List β) (w:List α):List α:=gs.foldl (λ w g=>w ++ [f w g]) w
theorem dV {α β:Type*} (f:List α→ β→ α) (gs hs:List β) (w:List α):kM f (gs ++ hs) w=kM f hs (kM f gs w):=by simp[kM,foldl_append]
theorem mm {α β:Type*} (f:List α→ β→ α) (gs:List β):∀ w:List α,∃ t:List α,kM f gs w=w ++ t∧t.length=gs.length:=by
 induction gs with
 | nil=>intro w;exact⟨[],by simp[kM],rfl⟩
 | cons g gs ih=>
  intro w;obtain⟨t,ht,hl⟩:=ih (w ++ [f w g]);refine⟨f w g :: t,?_,by simp[hl]⟩
  change kM f gs (w ++ [f w g])=w ++ f w g :: t;rw[ht];simp
theorem qB {α β:Type*} (f:List α→ β→ α) (gs:List β) (w:List α):(kM f gs w).length=w.length+gs.length:=by obtain⟨t,ht,hl⟩:=mm f gs w;rw[ht];simp[hl]
theorem f1 {α β:Type*} (f:List α→ β→ α) (gs:List β) (w:List α) (i:ℕ) (d:α) (h:i < w.length):(kM f gs w).getD i d=w.getD i d:=by obtain⟨t,ht,_⟩:=mm f gs w;rw[ht,_i _ _ _ _ h]
theorem ZE {α β:Type*} (f:List α→ β→ α) (gs:List β) (w:List α) (d:α) (j:ℕ) (hj:j < gs.length):(kM f gs w).getD (w.length+j) d=f (kM f (gs.take j) w) gs[j]:=by
 have p5:gs=gs.take j ++ gs[j] :: gs.drop (j+1):=by simp
 set A:=kM f (gs.take j) w with hA;have LI:A.length=w.length+j:=by
  rw[hA,qB];simp
  omega
 have hw:kM f gs w=kM f (gs.drop (j+1)) (A ++ [f A gs[j]]):=by
  conv_lhs=>rw[p5]
  rw[dV];rfl
 rw[hw,f1 _ _ _ _ _ (by simp[LI]),_g _ _ _ _ (by omega)];simp[LI]
def dH (w:List Bool) (g:Gate):Bool:=g.op.eval (g.inputs.map λ i=>w.getD i false)
def y0 (n:ℕ) (marked:Finset ℕ):List ℕ:=(List.range n).map λ i=>if i∈marked then 1 else 0
theorem Zp (C:_a) (x:List Bool):C.wires x=kM dH C.gates x:=rfl
theorem wI (C:_a) (n:ℕ) (marked:Finset ℕ):C.lineDegrees n marked=kM (λ d g=>g.lineDegree d) C.gates (y0 n marked):=rfl
@[local simp] theorem yY (n : ℕ) (marked : Finset ℕ) : (y0 n marked).length = n := by simp [y0]
theorem Z1 (C:_a) (x:List Bool):(C.wires x).length=x.length+C.size:=by rw[Zp,qB];rfl
theorem gQ (C:_a) (n:ℕ) (marked:Finset ℕ):(C.lineDegrees n marked).length=n+C.size:=by rw[wI,qB,yY];rfl
theorem fK (C:_a) (x:List Bool) (j:ℕ) (hj:j < C.gates.length):(C.wires x).getD (x.length+j) false=dH (kM dH (C.gates.take j) x) C.gates[j]:=ZE _ _ _ _ _ hj
theorem pg (C:_a) (n:ℕ) (marked:Finset ℕ) (j:ℕ) (hj:j < C.gates.length):(C.lineDegrees n marked).getD (n+j) 0=C.gates[j].lineDegree (kM (λ d g=>g.lineDegree d) (C.gates.take j) (y0 n marked)):=by rw[wI];simpa only[yY] using ZE (λ d g=>g.lineDegree d) C.gates (y0 n marked) 0 j hj
end M3
namespace M9
open M4
def xu (N:ℕ) (C:_a):ℕ:=N+N+C.size
def degrees (N:ℕ) (C:_a):List ℕ:=C.lineDegrees (N+N) (Ico N (N+N))
def yf (N:ℕ) (C:_a) (r:ℕ):ℕ:=(degrees N C).getD r 0
def yq (N:ℕ) (C:_a) (w r:ℕ):ℕ:=if r < w then yf N C r else 0
def gateAt (N:ℕ) (C:_a) (w:ℕ):Option Gate:=if N+N≤ w then C.gates[w-(N+N)]? else none
def v6 (N:ℕ) (C:_a) (w:ℕ):List ℕ:=match gateAt N C w with
 | none=>[]
 | some g=>if yf N C w=2 then g.inputs.filter (λ r=>decide (r < w∧yf N C r=2)) else []
def vm (N:ℕ) (C:_a):List (ℕ× ℕ):=(List.range (xu N C)).flatMap (λ w=>(v6 N C w).map (λ r=>(w,r)))
def vo (N:ℕ) (C:_a) (w:ℕ):Option ℕ:=match gateAt N C w with
 | none=>none
 | some g=>if yf N C w=2 then match g.op with
  | .and=>(g.inputs.find? (λ r=>decide (yq N C w r=0))).map (λ r=>if r < w then r else xu N C)
  | _=>none
  else none
def y3 (N:ℕ) (C:_a) (w a b:ℕ):Prop:=∃ g,gateAt N C w=some g∧g.op=.and∧g.inputs=[a,b]∧yq N C w a=1∧yq N C w b=1
def nM (N:ℕ) (C:_a) (w:ℕ):Prop:=∃ a b,y3 N C w a b
def yL (g:Gate) (d:List ℕ):Option ℕ:=match g.op with
 | .and=>g.inputs.find? (λ r=>decide (d.getD r 0=0))
 | _=>none
def xK (z:List Bool) (v:Option ℕ):Bool:=v.elim true (λ r=>z.getD r false)
lemma xC (a b:ℕ) (w:List Bool):value ⟨.and,[a,b]⟩ w=(w.getD a false && w.getD b false):=by simp only[value,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true]
lemma w3 (a b:ℕ) (d:List ℕ):yL ⟨.and,[a,b]⟩ d=if d.getD a 0=0 then some a else if d.getD b 0=0 then some b else none:=by
 by_cases ha:d.getD a 0=0 <;> by_cases hb:d.getD b 0=0 <;>
  simp only[yL,List.find?_cons,List.find?_nil,ha,hb,
   decide_true,decide_false,ite_true,ite_false]
lemma fO (a:ℕ) (d:List ℕ):yL ⟨.and,[a]⟩ d=if d.getD a 0=0 then some a else none:=by
 by_cases ha:d.getD a 0=0 <;>
  simp only[yL,List.find?_cons,List.find?_nil,ha,
   decide_true,decide_false,ite_true,ite_false]
lemma TA (g:Gate) (z p w:List Bool) (d:List ℕ) (hm:g.op=.and∨g.op=.or) (hl:g.inputs.length≤2) (h:mi z p w d) (hd:g.lineDegree d=2) (r:ℕ) (hr:r∈g.inputs) (QB:d.getD r 0=2) (b7:w.getD r false=true) (hz:xK z (yL g d)=true):value g w=true:=by
 rcases g with ⟨op,np⟩
 change op=.and∨op=.or at hm;change np.length≤2 at hl;change r∈np at hr;rcases hm with rfl | rfl
 · cases np with
   | nil=>simp at hr
   | cons a as=>
    cases as with
    | nil=>
     simp only[List.mem_singleton] at hr;subst r;simpa[value,GateOp.eval] using b7
    | cons b bs=>
     cases bs with
     | nil=>
      have fP:d.getD a 0+d.getD b 0=2:=by simpa[Gate.lineDegree] using hd
      simp only[List.mem_cons,List.not_mem_nil,or_false] at hr;rcases hr with rfl | rfl
      · have Vs:d.getD b 0=0:=by omega
        have YI:z.getD b false=true:=by rw[w3,QB,Vs] at hz;exact hz
        have kJ:=(h b).1 YI;rw[xC,b7,kJ];rfl
      · have YL:d.getD a 0=0:=by omega
        have d3:z.getD a false=true:=by rw[w3,YL] at hz;exact hz
        have m7:=(h a).1 d3;rw[xC,m7,b7];rfl
     | cons c cs=>simp only[_e] at hl;omega
 · have yH:true∈np.map (λ i=>w.getD i false):=List.mem_map.mpr ⟨r,hr,b7⟩;simpa[value,GateOp.eval,List.any_eq_true] using yH
lemma cd {za pa wa zb pb wb:Bool} (ha:At za pa wa 1) (hb:At zb pb wb 1) (hw:(wa && wb)=true) (hz:(za && zb)=false) (hp:((za && pb) || (pa && zb))=false):pa=true∧pb=true:=by have hea:=ha.2.2.2 (by omega);have heb:=hb.2.2.2 (by omega);rw[_s] at hw;obtain⟨rfl,rfl⟩:=hw;clear ha hb;cases za <;> cases zb <;> cases pa <;> cases pb <;> first | contradiction | exact⟨rfl,rfl⟩
lemma W5 (g:Gate) (z p w:List Bool) (d:List ℕ) (hm:g.op=.and∨g.op=.or) (hl:g.inputs.length≤2) (h:mi z p w d) (hd:g.lineDegree d=2) (hw:value g w=true) (hz:value g z=false) (hp:un g z p=false):(∃ a b,g.op=.and∧g.inputs=[a,b]∧d.getD a 0=1∧d.getD b 0=1∧p.getD a false=true∧p.getD b false=true)∨∃ r∈g.inputs,d.getD r 0=2∧w.getD r false=true∧z.getD r false=false∧p.getD r false=false∧xK z (yL g d)=true:=by
 rcases g with ⟨op,np⟩
 change op=.and∨op=.or at hm;change np.length≤2 at hl;rcases hm with rfl | rfl
 · cases np with
   | nil=>simp[Gate.lineDegree] at hd
   | cons a as=>
    cases as with
    | nil=>
     have W4:d.getD a 0=2:=by simpa[Gate.lineDegree] using hd
     right
     refine⟨a,by simp,W4,?_,?_,?_,?_⟩
     · simpa[value,GateOp.eval] using hw
     · simpa[value,GateOp.eval] using hz
     · simpa[un] using hp
     · rw[fO,W4];rfl
    | cons b bs=>
     cases bs with
     | nil=>
      have fP:d.getD a 0+d.getD b 0=2:=by simpa[Gate.lineDegree] using hd
      have VP:w.getD a false=true∧w.getD b false=true:=by simpa only[xC,_s] using hw
      have m7:=VP.1;have kJ:=VP.2;by_cases YL:d.getD a 0=0
      · have UT:d.getD b 0=2:=by omega
        have d3:z.getD a false=true:=(go (h a) YL).symm.trans m7;have z1:p.getD a false=false:=(h a).2.2.1 YL;right
        refine⟨b,by simp,UT,kJ,?_,?_,?_⟩
        · rw[xC,d3] at hz;exact hz
        · change ((z.getD a false && p.getD b false) || (p.getD a false && z.getD b false))=false at hp;rw[d3,z1] at hp;simpa only[Bool.true_and,Bool.false_and,Bool.or_false] using hp
        · rw[w3,YL];exact d3
      · by_cases Vs:d.getD b 0=0
        · have W4:d.getD a 0=2:=by omega
          have YI:z.getD b false=true:=(go (h b) Vs).symm.trans kJ;have jn:p.getD b false=false:=(h b).2.2.1 Vs;right
          refine⟨a,by simp,W4,m7,?_,?_,?_⟩
          · rw[xC,YI] at hz;simpa only[Bool.and_true] using hz
          · change ((z.getD a false && p.getD b false) || (p.getD a false && z.getD b false))=false at hp;rw[YI,jn] at hp;simpa only[Bool.and_false,Bool.and_true,Bool.false_or] using hp
          · rw[w3,W4,Vs];exact YI
        · have YH:d.getD a 0=1:=by omega
          have Za:d.getD b 0=1:=by omega
          left
          refine⟨a,b,rfl,rfl,YH,Za,?_⟩
          apply cd (by simpa only[YH] using h a) (by simpa only[Za] using h b)
          · simpa[value,GateOp.eval] using hw
          · simpa[value,GateOp.eval] using hz
          · exact hp
     | cons c cs=>simp only[_e] at hl;omega
 · have Ud:∃ r∈np,w.getD r false=true:=by simpa[value,GateOp.eval,List.any_eq_true] using hw
   obtain⟨r,hr,b7⟩:=Ud;have OV:z.getD r false=false:=by
    have cn:∀ r∈np,z.getD r false=false:=by simpa[value,GateOp.eval,List.any_eq_false] using hz
    exact cn r hr
   have OS:p.getD r false=false:=by
    have cn:∀ r∈np,p.getD r false=false:=by simpa[un,List.any_eq_false] using hp
    exact cn r hr
   have P6:d.getD r 0≤2:=by have he:=ni ⟨.or,np⟩ d r (Or.inr rfl) hl hr;omega
   have WA:d.getD r 0=2:=by
    by_contra hh;have cX:d.getD r 0≤1:=by omega
    have he:=(h r).2.2.2 cX;rw[b7,OV,OS] at he;contradiction
   exact Or.inr ⟨r,hr,WA,b7,OV,OS,by simp[xK,yL]⟩
lemma yu {α:Type*} (xs:List α) (n i:ℕ) (d:α):(xs.take n).getD i d=if i < n then xs.getD i d else d:=by
 by_cases hi:i < n
 · rw[_O hi];change ((xs.take n)[i]?).getD d=(xs[i]?).getD d;rw[List.getElem?_take_of_lt hi]
 · rw[ite_eq_right hi];apply _j
   have hn:(xs.take n).length≤ n:=by simp
   omega
lemma c2 (z p w:List Bool) (d:List ℕ) (n:ℕ) (h:mi z p w d):mi (z.take n) (p.take n) (w.take n) (d.take n):=by
 intro i;simp only[yu];by_cases hi:i < n
 · simpa only[_O hi] using h i
 · simpa only[ite_eq_right hi] using cN
lemma ba (gs:List Gate) (s:State):∃ t,(gs.foldl step s).2.1=s.2.1 ++ t∧t.length=gs.length:=by
 induction gs generalizing s with
 | nil=>exact⟨[],by simp,rfl⟩
 | cons g gs ih=>
  obtain⟨t,ht,y5⟩:=ih (step s g);refine⟨un g s.1 s.2.1 :: t,?_,by simp[y5]⟩
  change (gs.foldl step (step s g)).2.1=_;rw[ht];simp[step,List.append_assoc]
lemma bm (gs:List Gate) (s:State):∃ t,(gs.foldl step s).1=s.1 ++ t∧t.length=gs.length:=by
 induction gs generalizing s with
 | nil=>exact⟨[],by simp,rfl⟩
 | cons g gs ih=>
  obtain⟨t,ht,y5⟩:=ih (step s g);refine⟨value g s.1 :: t,?_,by simp[y5]⟩
  change (gs.foldl step (step s g)).1=_;rw[ht];simp[step,List.append_assoc]
lemma Xg (gs:List Gate) (s:State) (j:ℕ) (hj:j≤ gs.length):((gs.take j).foldl step s).2.1=(gs.foldl step s).2.1.take (s.2.1.length+j):=by
 have y5:((gs.take j).foldl step s).2.1.length=s.2.1.length+j:=by simpa only[List.length_take,Nat.min_eq_left hj] using (jx (gs.take j) s).2.1
 obtain⟨t,ht,_⟩:=ba (gs.drop j) ((gs.take j).foldl step s);have zD:(gs.foldl step s).2.1=((gs.take j).foldl step s).2.1 ++ t:=by
  conv_lhs=>rw[← List.take_append_drop j gs,foldl_append]
  exact ht
 rw[zD,← y5];simp
lemma Xq (gs:List Gate) (s:State) (j:ℕ) (hj:j≤ gs.length):((gs.take j).foldl step s).1=(gs.foldl step s).1.take (s.1.length+j):=by
 have y5:((gs.take j).foldl step s).1.length=s.1.length+j:=by simpa only[List.length_take,Nat.min_eq_left hj] using (jx (gs.take j) s).1
 obtain⟨t,ht,_⟩:=bm (gs.drop j) ((gs.take j).foldl step s);have zD:(gs.foldl step s).1=((gs.take j).foldl step s).1 ++ t:=by
  conv_lhs=>rw[← List.take_append_drop j gs,foldl_append]
  exact ht
 rw[zD,← y5];simp
lemma YO (gs:List Gate) (s:State) (j:ℕ) (hj:j < gs.length):(gs.foldl step s).2.1.getD (s.2.1.length+j) false=un gs[j] ((gs.take j).foldl step s).1 ((gs.take j).foldl step s).2.1:=by
 let Zg:=(gs.take j).foldl step s;have y5:Zg.2.1.length=s.2.1.length+j:=by simpa only[Zg,List.length_take,Nat.min_eq_left (Nat.le_of_lt hj)] using (jx (gs.take j) s).2.1
 have p5:gs=gs.take j ++ gs[j] :: gs.drop (j+1):=by simp
 have UY:gs.foldl step s=(gs.drop (j+1)).foldl step (step Zg gs[j]):=by
  conv_lhs=>rw[p5,foldl_append]
  rfl
 rw[UY,Xw _ _ _ (by simp only[step,_c,_d];omega)]
 change (Zg.2.1 ++ [un gs[j] Zg.1 Zg.2.1]).getD (s.2.1.length+j) false=_;rw[_g _ _ _ _ (by omega)];simp[y5,Zg]
lemma di (gs:List Gate) (s:State) (j:ℕ) (hj:j < gs.length) (y5:s.1.length=s.2.1.length):(gs.foldl step s).2.1.getD (s.2.1.length+j) false=un gs[j] ((gs.foldl step s).1.take (s.2.1.length+j)) ((gs.foldl step s).2.1.take (s.2.1.length+j)):=by rw[YO gs s j hj,Xq gs s j (Nat.le_of_lt hj),Xg gs s j (Nat.le_of_lt hj),y5]
lemma p7 {α β:Type*} (f:List α→ β→ α) (gs:List β) (xs:List α) (j:ℕ) (hj:j≤ gs.length):M3.kM f (gs.take j) xs=(M3.kM f gs xs).take (xs.length+j):=by
 obtain⟨t,ht,_⟩:=M3.mm f (gs.drop j) (M3.kM f (gs.take j) xs);have y5:(M3.kM f (gs.take j) xs).length=xs.length+j:=by simp only[M3.qB,List.length_take,Nat.min_eq_left hj]
 have zD:M3.kM f gs xs=M3.kM f (gs.take j) xs ++ t:=by
  conv_lhs=>rw[← List.take_append_drop j gs,M3.dV]
  exact ht
 rw[zD,← y5];simp
lemma nh (C:_a) (xs:List Bool) (j:ℕ) (hj:j < C.gates.length):(C.wires xs).getD (xs.length+j) false=value C.gates[j] ((C.wires xs).take (xs.length+j)):=by rw[M3.fK C xs j hj,p7 _ _ _ _ (Nat.le_of_lt hj)];rfl
lemma fZ (N:ℕ) (C:_a) (j:ℕ) (hj:j < C.gates.length):yf N C (N+N+j)=C.gates[j].lineDegree ((degrees N C).take (N+N+j)):=by unfold yf degrees;rw[M3.pg C (N+N) _ j hj,p7 _ _ _ _ (Nat.le_of_lt hj),M3.yY];rfl
lemma d8 (N:ℕ):M3.y0 (N+N) (Ico N (N+N))=replicate N 0 ++ replicate N 1:=by
 unfold M3.y0;rw[List.range_add,List.map_append,List.map_map];have h0:(List.range N).map (λ i=>if i∈Ico N (N+N) then 1 else 0)=replicate N 0:=by
  calc
   _=(List.range N).map (λ _=>0):=by
    apply List.map_congr_left
    intro i hi;have hi':=List.mem_range.mp hi;have hn:i∉Ico N (N+N):=by simp only[mem_Ico];omega
    simp only[ite_eq_right hn]
   _=_:=by simp
 have h1:(List.range N).map (λ i=>if N+i∈Ico N (N+N) then 1 else 0)=replicate N 1:=by
  calc
   _=(List.range N).map (λ _=>1):=by
    apply List.map_congr_left
    intro i hi;have hi':=List.mem_range.mp hi;have hn:N+i∈Ico N (N+N):=by simp only[mem_Ico];omega
    simp only[_O hn]
   _=_:=by simp
 exact congrArg₂ List.append h0 h1
def xX (C:_a) (x y:List Bool):State:=C.gates.foldl step (vC x y)
def zM (N:ℕ) (C:_a) (x:List Bool):List Bool:=C.wires (x ++ replicate N false)
def v1 (C:_a) (x y:List Bool):List Bool:=(xX C x y).2.1
def zL (C:_a) (x y:List Bool):List Bool:=C.wires (x ++ y)
lemma mh (N:ℕ) (C:_a) (x y:List Bool) (hy:y.length=N):(xX C x y).1=zM N C x:=by rw[xX,fE];simp only[vC,hy];rfl
lemma bC (C:_a) (x y:List Bool):(xX C x y).2.2.1=zL C x y:=fg C.gates (vC x y)
lemma fi (N:ℕ) (C:_a) (x y:List Bool) (hx:x.length=N) (hy:y.length=N):(xX C x y).2.2.2=degrees N C:=by rw[xX,n2];simp only[vC,hx,hy];rw[← d8 N];rfl
lemma pN (N:ℕ) (C:_a) (hm:_b C) (x y:List Bool) (hx:x.length=N) (hy:y.length=N):mi (zM N C x) (v1 C x y) (zL C x y) (degrees N C):=by have h:=(w7 C hm x y).2.2.2;change mi (xX C x y).1 (v1 C x y) (xX C x y).2.2.1 (xX C x y).2.2.2 at h;rwa[mh N C x y hy,bC C x y,fi N C x y hx hy] at h
lemma gG (N:ℕ) (C:_a) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (j:ℕ) (hj:j < C.gates.length):(v1 C x y).getD (N+N+j) false=un C.gates[j] ((zM N C x).take (N+N+j)) ((v1 C x y).take (N+N+j)):=by have zD:=di C.gates (vC x y) j hj (by simp[vC]);change (v1 C x y).getD _ false=un _ ((xX C x y).1.take _) ((v1 C x y).take _) at zD;rw[mh N C x y hy] at zD;simpa only[vC,_c,_f,hx,hy] using zD
lemma gU (N:ℕ) (C:_a) (j r:ℕ) (hj:j≤ C.gates.length):(M3.kM (λ d g=>g.lineDegree d) (C.gates.take j) (M3.y0 (N+N) (Ico N (N+N)))).getD r 0=yq N C (N+N+j) r:=by rw[p7 _ _ _ _ hj,M3.yY,yu];rfl
lemma yE (N:ℕ) (C:_a) (w r:ℕ):((degrees N C).take w).getD r 0=yq N C w r:=yu (degrees N C) w r 0
lemma pW (N:ℕ) (C:_a) (j:ℕ) (hj:j < C.gates.length):gateAt N C (N+N+j)=some C.gates[j]:=by simp[gateAt,hj]
lemma uu (N:ℕ) (C:_a) (w:ℕ) (g:Gate) (hg:gateAt N C w=some g):∃ j:ℕ,∃ hj:j < C.gates.length,w=N+N+j∧C.gates[j]=g:=by
 unfold gateAt at hg;split_ifs at hg with hw
 · obtain⟨hj,zD⟩:=List.getElem?_eq_some_iff.mp hg;exact⟨w-(N+N),hj,by omega,zD⟩
lemma qG (N:ℕ) (C:_a) (w:ℕ) (g:Gate) (hg:gateAt N C w=some g):yf N C w=g.lineDegree ((degrees N C).take w):=by obtain⟨j,hj,rfl,rfl⟩:=uu N C w g hg;exact fZ N C j hj
lemma dO (N:ℕ) (C:_a) (hm:_b C) (w:ℕ) (g:Gate) (hg:gateAt N C w=some g):(g.op=.and∨g.op=.or)∧g.inputs.length≤2:=by obtain⟨j,hj,_,rfl⟩:=uu N C w g hg;obtain⟨kf,y5⟩:=hm C.gates[j] (List.getElem_mem hj);exact⟨by simpa only[Set.mem_insert_iff,Set.mem_singleton_iff] using kf,y5⟩
lemma dZ (N:ℕ) (C:_a) (w:ℕ) (hf:nM N C w):yf N C w=2:=by
 obtain⟨a,b,g,hg,kf,cM,ha,hb⟩:=hf;rw[qG N C w g hg];rcases g with ⟨op,np⟩
 change op=.and at kf;change np=[a,b] at cM;subst op;subst np;simp only[Gate.lineDegree,ite_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,yE,ha,hb];rfl
lemma w6 (N:ℕ) (C:_a) (w r:ℕ) (g:Gate) (hg:gateAt N C w=some g) (hd:yf N C w=2):r∈v6 N C w↔r∈g.inputs∧r < w∧yf N C r=2:=by simp[v6,hg,hd]
lemma wA (N:ℕ) (C:_a) (w r:ℕ):(w,r)∈vm N C↔w < xu N C∧r∈v6 N C w:=by simp[vm]
lemma nT (N:ℕ) (C:_a):(degrees N C).length=xu N C:=M3.gQ C (N+N) _
lemma qD (N:ℕ) (C:_a) (x:List Bool) (hx:x.length=N):(zM N C x).length=xu N C:=by simp only[zM,M3.Z1,_c,_f,hx,xu]
lemma hD (N:ℕ) (C:_a) (r:ℕ) (hr:r < N+N):yf N C r≤1:=by unfold yf degrees;rw[M3.wI,M3.f1 _ _ _ _ _ (by simpa only[M3.yY] using hr)];rw[_k _ _ (by simpa only[M3.yY] using hr)];simp only[M3.y0,List.getElem_map,List.getElem_range];split_ifs <;> omega
lemma x4 (N:ℕ) (C:_a) (w:ℕ) (hd:yf N C w=2):N+N≤ w∧w < xu N C:=by
 constructor
 · by_contra h;have he:=hD N C w (by omega);omega
 · by_contra h;have he:yf N C w=0:=_j (degrees N C) 0 (by rw[nT];omega)
   omega
lemma fB (N:ℕ) (C:_a) (w:ℕ) (hd:yf N C w=2):∃ g,gateAt N C w=some g:=by
 obtain⟨PB,ON⟩:=x4 N C w hd;have hj:w-(N+N) < C.gates.length:=by unfold xu Circuit.size at ON;omega
 refine⟨C.gates[w-(N+N)],?_⟩
 have zD:w=N+N+(w-(N+N)):=by omega
 conv_lhs=>rw[zD]
 exact pW N C (w-(N+N)) hj
lemma gk (N:ℕ) (C:_a) (w r:ℕ) (hr:r∈v6 N C w):∃ g,gateAt N C w=some g∧yf N C w=2∧r∈g.inputs∧r < w∧yf N C r=2:=by
 cases hg:gateAt N C w with
 | none=>simp[v6,hg] at hr
 | some g=>
  by_cases hd:yf N C w=2
  · exact⟨g,rfl,hd,(w6 N C w r g hg hd).mp hr⟩
  · simp[v6,hg,hd] at hr
lemma n7 (N:ℕ) (C:_a) (w r:ℕ) (he:(w,r)∈vm N C):r < w∧w < xu N C∧yf N C w=2∧yf N C r=2:=by obtain⟨hw,hr⟩:=(wA N C w r).mp he;obtain⟨g,_,hd,_,z5,WA⟩:=gk N C w r hr;exact⟨z5,hw,hd,WA⟩
lemma xi (N:ℕ) (C:_a) (w a b:ℕ) (hf:y3 N C w a b):a < w∧b < w∧w < xu N C∧yf N C a=1∧yf N C b=1:=by
 have m7:=x4 N C w (dZ N C w ⟨a,b,hf⟩);obtain⟨g,hg,_,_,ha,hb⟩:=hf;have QD:a < w:=by unfold yq at ha;split_ifs at ha;omega
 have Vr:b < w:=by unfold yq at hb;split_ifs at hb;omega
 exact⟨QD,Vr,m7.2,by simpa only[yq,_O QD] using ha,by simpa only[yq,_O Vr] using hb⟩
lemma gi (N:ℕ) (C:_a) (w:ℕ) (g:Gate) (hg:gateAt N C w=some g) (hd:yf N C w=2):vo N C w=(yL g ((degrees N C).take w)).map (λ r=>if r < w then r else xu N C):=by
 have ME:(λ r=>decide (yq N C w r=0))=(λ r=>decide (((degrees N C).take w).getD r 0=0)):=by
  funext r
  rw[yE]
 unfold vo;simp only[hg,hd,ite_true];cases kf:g.op <;> simp only[kf,yL,ME,Option.map_none]
lemma gw (N:ℕ) (C:_a) (w:ℕ) (g:Gate) (z:List Bool) (hz:z.length=xu N C) (hg:gateAt N C w=some g) (hd:yf N C w=2):xK z (vo N C w)=xK (z.take w) (yL g ((degrees N C).take w)):=by
 rw[gi N C w g hg hd];cases hv:yL g ((degrees N C).take w) with
 | none=>rfl
 | some r=>
  simp only[Option.map_some,xK,Option.elim_some,yu];by_cases hr:r < w
  · simp only[_O hr]
  · simp only[ite_eq_right hr];exact _j z false (by omega)
lemma my (N:ℕ) (C:_a) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (w:ℕ) (g:Gate) (hg:gateAt N C w=some g):(zL C x y).getD w false=value g ((zL C x y).take w):=by obtain⟨j,hj,rfl,rfl⟩:=uu N C w g hg;simpa only[zL,_c,hx,hy] using nh C (x ++ y) j hj
lemma Y6 (N:ℕ) (C:_a) (x:List Bool) (hx:x.length=N) (w:ℕ) (g:Gate) (hg:gateAt N C w=some g):(zM N C x).getD w false=value g ((zM N C x).take w):=by obtain⟨j,hj,rfl,rfl⟩:=uu N C w g hg;simpa only[zM,_c,_f,hx] using nh C (x ++ replicate N false) j hj
lemma cf (N:ℕ) (C:_a) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (w:ℕ) (g:Gate) (hg:gateAt N C w=some g):(v1 C x y).getD w false=un g ((zM N C x).take w) ((v1 C x y).take w):=by obtain⟨j,hj,rfl,rfl⟩:=uu N C w g hg;exact gG N C x y hx hy j hj
lemma T5 (N:ℕ) (C:_a) (hm:_b C) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (w r:ℕ) (he:(w,r)∈vm N C) (hz:xK (zM N C x) (vo N C w)=true) (hr:(zL C x y).getD r false=true):(zL C x y).getD w false=true:=by
 obtain⟨_,hc⟩:=(wA N C w r).mp he;obtain⟨g,hg,hd,Nh,z5,WA⟩:=gk N C w r hc;obtain⟨Mw,Tu⟩:=dO N C hm w g hg;have NI:=c2 _ _ _ _ w (pN N C hm x y hx hy);have cu:g.lineDegree ((degrees N C).take w)=2:=by rwa[← qG N C w g hg]
 have QB:((degrees N C).take w).getD r 0=2:=by rw[yE,yq,_O z5];exact WA
 have b7:((zL C x y).take w).getD r false=true:=by rw[yu,_O z5];exact hr
 rw[gw N C w g _ (qD N C x hx) hg hd] at hz;rw[my N C x y hx hy w g hg];exact TA g _ _ _ _ Mw Tu NI cu r Nh QB b7 hz
lemma dI (N:ℕ) (C:_a) (hm:_b C) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (w a b:ℕ) (hf:y3 N C w a b) (ha:(v1 C x y).getD a false=true) (hb:(v1 C x y).getD b false=true):(zL C x y).getD w false=true:=by
 have hc:=xi N C w a b hf;have hi:=pN N C hm x y hx hy;have m7:=(hi a).2.1 ha;have kJ:=(hi b).2.1 hb;obtain⟨g,hg,kf,cM,_,_⟩:=hf;rw[my N C x y hx hy w g hg];rcases g with ⟨op,np⟩
 change op=.and at kf;change np=[a,b] at cM;subst op;subst np;rw[xC,yu,yu,_O hc.1,_O hc.2.1,m7,kJ];rfl
def c7 (N:ℕ) (C:_a) (x y:List Bool) (w:ℕ):Prop:=yf N C w=2∧(zL C x y).getD w false=true∧(zM N C x).getD w false=false∧(v1 C x y).getD w false=false
def vl (N:ℕ) (C:_a) (x:List Bool) (w r:ℕ):Prop:=(w,r)∈vm N C∧xK (zM N C x) (vo N C w)=true
lemma Vg (N:ℕ) (C:_a) (hm:_b C) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (w:ℕ) (hw:c7 N C x y w):(∃ a b,y3 N C w a b∧(v1 C x y).getD a false=true∧(v1 C x y).getD b false=true)∨∃ r,vl N C x w r∧c7 N C x y r:=by
 obtain⟨hd,hw,hz,hp⟩:=hw;obtain⟨g,hg⟩:=fB N C w hd;obtain⟨Mw,Tu⟩:=dO N C hm w g hg;have NI:=c2 _ _ _ _ w (pN N C hm x y hx hy);have cu:g.lineDegree ((degrees N C).take w)=2:=by rwa[← qG N C w g hg]
 rw[my N C x y hx hy w g hg] at hw;rw[Y6 N C x hx w g hg] at hz;rw[cf N C x y hx hy w g hg] at hp;rcases W5 g _ _ _ _ Mw Tu NI cu hw hz hp with hf | he
 · obtain⟨a,b,kf,cM,YH,Za,z1,jn⟩:=hf;have QD:a < w:=by rw[yE] at YH;unfold yq at YH;split_ifs at YH;omega
   have Vr:b < w:=by rw[yE] at Za;unfold yq at Za;split_ifs at Za;omega
   left
   refine⟨a,b,⟨g,hg,kf,cM,?_,?_⟩,?_,?_⟩
   · rwa[yE] at YH
   · rwa[yE] at Za
   · simpa only[yu,_O QD] using z1
   · simpa only[yu,_O Vr] using jn
 · obtain⟨r,Nh,WA,b7,OV,OS,hweight⟩:=he;have Vo:r < w:=by rw[yE] at WA;unfold yq at WA;split_ifs at WA;omega
   have QB:yf N C r=2:=by simpa only[yE,yq,_O Vo] using WA
   right
   refine⟨r,⟨?_,?_⟩,QB,?_,?_,?_⟩
   · apply (wA N C w r).mpr
     exact⟨(x4 N C w hd).2,(w6 N C w r g hg hd).mpr ⟨Nh,Vo,QB⟩⟩
   · rwa[gw N C w g _ (qD N C x hx) hg hd]
   · simpa only[yu,_O Vo] using b7
   · simpa only[yu,_O Vo] using OV
   · simpa only[yu,_O Vo] using OS
lemma pB (N:ℕ) (C:_a) (hm:_b C) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (w:ℕ) (hw:c7 N C x y w):∃ v a b,_1 (vl N C x) w v∧y3 N C v a b∧(v1 C x y).getD a false=true∧(v1 C x y).getD b false=true:=by
 induction w using strong_induction_on with
 | ind w ih=>
  rcases Vg N C hm x y hx hy w hw with hf | he
  · obtain⟨a,b,hf,ha,hb⟩:=hf;exact⟨w,a,b,.refl,hf,ha,hb⟩
  · obtain⟨r,he,hr⟩:=he;obtain⟨v,a,b,wP,hf,ha,hb⟩:=ih r (n7 N C w r he.1).1 hr;exact⟨v,a,b,ReflTransGen.head he wP,hf,ha,hb⟩
lemma ZQ (N:ℕ) (C:_a) (hm:_b C) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (w v:ℕ) (hp:_1 (vl N C x) w v) (hv:(zL C x y).getD v false=true):(zL C x y).getD w false=true:=by
 induction hp using ReflTransGen.head_induction_on with
 | refl=>exact hv
 | head he _ ih=>exact T5 N C hm x y hx hy _ _ he.1 he.2 ih
lemma nL (g:Gate) (d:List ℕ) (r:ℕ) (hr:yL g d=some r):d.getD r 0=0:=by
 cases kf:g.op with
 | and=>
  simp only[yL,kf] at hr;exact _o (List.find?_eq_some_iff_append.mp hr).1
 | or=>simp[yL,kf] at hr
 | not=>simp[yL,kf] at hr
 | mod m=>simp[yL,kf] at hr
 | maj=>simp[yL,kf] at hr
lemma zZ (N:ℕ) (C:_a) (w a:ℕ) (hw:vo N C w=some a):yf N C a=0:=by
 cases hg:gateAt N C w with
 | none=>simp[vo,hg] at hw
 | some g=>
  by_cases hd:yf N C w=2
  · rw[gi N C w g hg hd] at hw;obtain⟨r,hr,zD⟩:=Option.map_eq_some_iff.mp hw;have L3:=nL g ((degrees N C).take w) r hr;by_cases Vo:r < w
    · simp only[_O Vo] at zD;subst a;simpa only[yE,yq,_O Vo] using L3
    · simp only[ite_eq_right Vo] at zD;subst a;exact _j (degrees N C) 0 (by rw[nT])
  · simp[vo,hg,hd] at hw
end M9
namespace K1
open PEqualNP.CircuitLowerBounds M2
abbrev F:=M1.yZ
abbrev vh (N:ℕ) (C:_a):=M1.net (F N C)
abbrev vr (N:ℕ) (C:_a) (r:ℕ):=(M1.u3 (F N C)).getD r N
abbrev uJ:=M9.xu
abbrev k6:=M9.vm
abbrev jC:=M9.vo
abbrev WG:=M9.nM
abbrev f9:=M9.y3
abbrev yS:=M9.yf
def vn {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ):List (ℕ× ℕ):=ofFn λ j=>(fa j,vr N C (fb j))
def U0 {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ):M0.State:=M0.yp N (vn N C fa fb) (k6 N C) (jC N C) (uJ N C) (M0.vC N (vh N C))
def net {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ):List vg:=M0.net (U0 N C fa fb)
def yR {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (w:ℕ):ℕ:=M0.yR (U0 N C fa fb) w
noncomputable def vI (N:ℕ) (C:_a):Finset ℕ:=by
 classical
 exact (Finset.range (uJ N C)).filter (WG N C)
noncomputable def yh {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ):Finset ℕ:=K5.yh (vn N C fa fb) (k6 N C) (vI N C)
def ku (N:ℕ) (C:_a) (w:ℕ):List ℕ:=((M9.gateAt N C w).map Gate.inputs).getD []
def vD (N:ℕ) (C:_a) (w:ℕ):ℕ:=(ku N C w).getD 0 (uJ N C)
def vz (N:ℕ) (C:_a) (w:ℕ):ℕ:=(ku N C w).getD 1 (uJ N C)
abbrev nR:=ℕ× ℕ× ℕ
def cJ {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (j:Fin J):nR:=(vr N C (fa j),vr N C (fb j),vr N C (fb j))
def cx {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (w:ℕ):nR:=(vr N C (vD N C w),vr N C (vz N C w),yR N C fa fb w)
noncomputable def k5 {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ):List nR:=ofFn (cJ N C fa fb) ++ (yh N C fa fb).toList.map (cx N C fa fb)
lemma Yd {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ):(vn N C fa fb).length=J:=by simp[vn]
lemma dy {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (e:ℕ× ℕ):e∈vn N C fa fb↔∃ j,e=(fa j,vr N C (fb j)):=by simp[vn,eq_comm]
lemma Y5 {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ):∀ e∈vn N C fa fb,e.2 < N+(vh N C).length:=by intro e he;obtain⟨j,rfl⟩:=(dy N C fa fb e).mp he;exact M1.wO N C (fb j)
lemma z9 (N:ℕ) (C:_a):(vh N C).head?=some (Sum.inl []):=by obtain⟨t,ht⟩:=M1.xM N (N+N+C.size) C.gates;change (M1.net (M1.yp N (N+N+C.size) C.gates)).head?=_;rw[ht];rfl
lemma j7 {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=N) (r:ℕ):(run (net N C fa fb) labels y).getD (vr N C r) false=(run (vh N C) labels y).getD (vr N C r) false:=by exact K5.bB N (vn N C fa fb) (k6 N C) (jC N C) (uJ N C) (M0.vC N (vh N C)) labels y hy (vr N C r) (M1.wO N C r)
lemma YK {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ):(k5 N C fa fb).length=J+(yh N C fa fb).card:=by simp[k5]
lemma bU {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (t:nR):t∈k5 N C fa fb↔(∃ j,t=cJ N C fa fb j)∨∃ w∈yh N C fa fb,t=cx N C fa fb w:=by simp[k5,eq_comm]
lemma WW (N:ℕ) (C:_a) (w:ℕ):w∈vI N C↔w < uJ N C∧WG N C w:=by
 classical
 simp[vI]
lemma gx {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (w:ℕ):w∈yh N C fa fb↔w < uJ N C∧WG N C w∧0 < M0.y1 (vn N C fa fb) (k6 N C) w:=by
 classical
 simp[yh,K5.yh,WW,and_assoc]
lemma jI (N:ℕ) (C:_a) (w:ℕ) (hf:WG N C w):f9 N C w (vD N C w) (vz N C w):=by
 obtain⟨a,b,g,hg,ho,hi,ha,hb⟩:=hf;have hl:vD N C w=a:=by simp[vD,ku,hg,hi]
 have hr:vz N C w=b:=by simp[vz,ku,hg,hi]
 exact hl▸hr▸⟨g,hg,ho,hi,ha,hb⟩
lemma n7 (N:ℕ) (C:_a):∀ e∈k6 N C,e.2 < e.1∧e.1 < uJ N C:=by
 rintro⟨w,r⟩ he;obtain⟨hw,hr⟩:=(M9.wA N C w r).mp he;refine⟨?_,hw⟩
 cases hg:M9.gateAt N C w with
 | none=>simp[M9.v6,hg] at hr
 | some g=>
  by_cases hd:yS N C w=2
  · exact ((M9.w6 N C w r g hg hd).mp hr).2.1
  · simp[M9.v6,hg,hd] at hr
lemma qE {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (labels:ℕ→ Bool) (y:List Bool) (hy:y.length=N) (w:ℕ) (hw:w < uJ N C):(run (net N C fa fb) labels y).getD (yR N C fa fb w) false=true↔Kf.xj (k6 N C) (M0.yo labels (jC N C)) (vn N C fa fb) (λ r=>(run (vh N C) labels y).getD r false) w:=by exact K0.dF N (uJ N C) (vh N C) (vn N C fa fb) (k6 N C) (jC N C) labels y hy (z9 N C) (Y5 N C fa fb) (n7 N C) w hw
lemma jq (vm vn:List (ℕ× ℕ)) (v5 yD:ℕ→ Bool) (w:ℕ) (hr:Kf.xj vm v5 vn yD w):0 < M0.y1 vn vm w:=by
 have ht:=(Kf.wo vm v5 vn yD w).mpr hr;have hd:=(Kf.qC vm v5 vn yD w).mp ht;by_contra hp;have hz:M0.y1 vn vm w=0:=by omega
 simp only[M0.y1,Nat.add_eq_zero,List.length_eq_zero_iff] at hz;rcases hd with ⟨s,hs,Vt,_⟩ | ⟨e,he,OX,_,_⟩
 · have hm:s∈vn.filter (λ e=>decide (e.1=w)):=by simp[hs,Vt]
   rw[hz.1] at hm;simp at hm
 · have hm:e∈vm.filter (λ e=>decide (e.2=w)):=by simp[he,OX]
   rw[hz.2] at hm;simp at hm
def d2 (u1:ℕ→ Bool) (t:nR):Prop:=u1 t.1=true∧u1 t.2.1=true∧u1 t.2.2=true
lemma yv (N:ℕ) (C:_a) (hm:_b C) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (r:ℕ) (hr:yS N C r≤2):(run (vh N C) (M1.vy N C x) y).getD (vr N C r) false=(M9.v1 C x y).getD r false:=M1.u0 N C hm x y hx hy r hr
lemma pL (N:ℕ) (C:_a) (w a b:ℕ) (hf:f9 N C w a b):vD N C w=a:=by obtain⟨g,hg,_,hi,_,_⟩:=hf;simp[vD,ku,hg,hi]
lemma qP (N:ℕ) (C:_a) (w a b:ℕ) (hf:f9 N C w a b):vz N C w=b:=by obtain⟨g,hg,_,hi,_,_⟩:=hf;simp[vz,ku,hg,hi]
open PEqualNP.CircuitLowerBounds M2
def dN (t:nR):Fin 3→ ℕ:=![t.1,t.2.1,t.2.2]
noncomputable def ye {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (j:Fin (k5 N C fa fb).length):Fin 3→ ℕ:=dN (k5 N C fa fb)[j]
lemma fC (t:nR) (u1:ℕ→ Bool):(∀ i,u1 (dN t i)=true)↔d2 u1 t:=by
 constructor
 · intro h;exact⟨h 0,h 1,h 2⟩
 · rintro⟨ha,hb,hc⟩ i;fin_cases i
   · exact ha
   · exact hb
   · exact hc
lemma mo {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (j:Fin (k5 N C fa fb).length) (u1:ℕ→ Bool):(∀ i,u1 (ye N C fa fb j i)=true)↔d2 u1 (k5 N C fa fb)[j]:=fC _ _
lemma dz {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (u1:ℕ→ Bool):(∃ j,∀ i,u1 (ye N C fa fb j i)=true)↔∃ t∈k5 N C fa fb,d2 u1 t:=by
 constructor
 · rintro⟨j,hj⟩;exact⟨(k5 N C fa fb)[j],List.get_mem _ j,(mo N C fa fb j u1).mp hj⟩
 · rintro⟨t,ht,hf⟩;obtain⟨j,hj,SR⟩:=mem_iff_getElem.mp ht;refine⟨⟨j,hj⟩,(mo N C fa fb ⟨j,hj⟩ u1).mpr ?_⟩
   change d2 u1 (k5 N C fa fb)[j];rw[SR];exact hf
end K1
namespace M1
open M2
lemma df (N z:ℕ) (s:State) (g:Gate) (x8:g.inputs.length≤2) (rs:List ℕ) (yH:Sum.inl rs∈yx N z s g):rs.length≤2:=by
 unfold yx at yH;dsimp only at yH;split_ifs at yH
 all_goals try split at yH
 all_goals try split_ifs at yH
 all_goals simp_all
lemma mr (N z:ℕ) (s:State) (g:Gate) (a r:ℕ) (yH:Sum.inr (a,r)∈yx N z s g):∃ i,a=zq z s i∧(degrees s).getD i 0≤1:=by
 unfold yx at yH;dsimp only at yH;split_ifs at yH
 all_goals try split at yH
 all_goals try split_ifs at yH
 all_goals simp_all
 all_goals aesop
lemma gf (N z:ℕ) (gs:List Gate) (s:State) (np:vg) (yH:np∈net (gs.foldl (ya N z) s)):np∈net s∨∃ Zg g post,gs=Zg ++ g :: post∧np∈yx N z (Zg.foldl (ya N z) s) g:=by
 induction gs generalizing s with
 | nil=>exact Or.inl yH
 | cons g gs ih=>
  rw[foldl_cons] at yH;rcases ih (ya N z s g) yH with h | ⟨Zg,g',post,Te,hp⟩
  · rw[zG,List.mem_append] at h;rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨[],g,gs,rfl,h⟩
  · refine Or.inr ⟨g :: Zg,g',post,?_,?_⟩
    · simp only[List.cons_append,Te]
    · simpa only[foldl_cons] using hp
lemma kX (N z:ℕ) (gs:List Gate) (np:vg) (yH:np∈net (yp N z gs)):np=Sum.inl []∨∃ Zg g post,gs=Zg ++ g :: post∧np∈yx N z (yp N z Zg) g:=by
 rcases gf N z gs (vC N) np yH with h | h
 · exact Or.inl (by simpa only[vC,net,List.mem_singleton] using h)
 · exact Or.inr h
lemma w8 (N:ℕ) (C:_a) (hC:_b C) (rs:List ℕ) (yH:Sum.inl rs∈net (yZ N C)):rs.length≤2:=by
 rcases kX N (N+N+C.size) C.gates (Sum.inl rs) yH with h | ⟨Zg,g,post,Te,hp⟩
 · have pE:rs=[]:=Sum.inl.inj h;simp[pE]
 · have hg:g∈C.gates:=by rw[Te];simp
   exact df N (N+N+C.size) (yp N (N+N+C.size) Zg) g (hC g hg).2 rs hp
lemma zH (N:ℕ) (C:_a) (a r:ℕ) (yH:Sum.inr (a,r)∈net (yZ N C)):(C.lineDegrees (N+N) (Ico N (N+N))).getD a 0≤1:=by
 rcases kX N (N+N+C.size) C.gates (Sum.inr (a,r)) yH with h | ⟨Zg,g,post,Te,hp⟩
 · contradiction
 · obtain⟨i,ha,hi⟩:=mr N (N+N+C.size) (yp N (N+N+C.size) Zg) g a r hp;rw[← wt];by_cases QX:i < (u3 (yp N (N+N+C.size) Zg)).length
   · rw[ha,nd _ _ _ QX]
     have T0:(degrees (yZ N C)).getD i 0=(degrees (yp N (N+N+C.size) Zg)).getD i 0:=by
      change (degrees (yp N (N+N+C.size) C.gates)).getD i 0=_;rw[Te];apply qh
      simpa only[dj] using QX
     rw[T0];exact hi
   · rw[ha,ng _ _ _ (Nat.le_of_not_gt QX)]
     have bH:(degrees (yZ N C)).getD (N+N+C.size) 0=0:=by
      apply _j
      simp only[yZ,kP,Circuit.size];omega
     rw[bH];omega
def xa:List ℕ→ List Gate→ List ℕ
 | _,[]=>[]
 | d,g :: gs=>g.lineDegree d :: xa (d ++ [g.lineDegree d]) gs
lemma gE (d:List ℕ) (gs:List Gate):(xa d gs).length=gs.length:=by
 induction gs generalizing d with
 | nil=>rfl
 | cons g gs ih=>simp only[xa,_e,ih]
lemma jW (d:List ℕ) (gs:List Gate):gs.foldl (λ d g=>d ++ [g.lineDegree d]) d=d ++ xa d gs:=by
 induction gs generalizing d with
 | nil=>simp[xa]
 | cons g gs ih=>
  rw[foldl_cons,ih];simp only[xa,List.append_assoc,List.singleton_append]
lemma kl (k:ℕ) (d:List ℕ) (gs:List Gate):vQ k d gs=(xa d gs).count k:=by
 induction gs generalizing d with
 | nil=>rfl
 | cons g gs ih=>
  simp only[vQ,xa,List.count_cons,beq_iff_eq,ih];omega
lemma qV (xs:List ℕ) (k:ℕ):xs.count k=((Finset.range xs.length).filter (λ i=>xs.getD i 0=k)).card:=by
 rw[Finset.card_filter];induction xs with
 | nil=>simp
 | cons a xs ih=>
  simp only[List.count_cons,_e,Finset.sum_range_succ',List.getD_cons_succ,List.getD_cons_zero,beq_iff_eq,ih]
lemma kT (d xs:List ℕ) (k:ℕ):xs.count k=((Ico d.length (d.length+xs.length)).filter (λ w=>(d ++ xs).getD w 0=k)).card:=by
 rw[qV];apply Finset.card_bij (λ i _=>d.length+i)
 · intro i hi;obtain⟨QX,Ks⟩:=_A hi;have hi':=mem_range.mp QX;apply _B
   constructor
   · exact mem_Ico.mpr ⟨by omega,by omega⟩
   · rw[_g _ _ _ _ (by omega),add_sub_cancel_left];exact Ks
 · intro i _ j _ LW;omega
 · intro w hw;obtain⟨QI,Xz⟩:=_A hw;obtain⟨PB,ON⟩:=mem_Ico.mp QI
   have yH:w-d.length∈(Finset.range xs.length).filter (λ i=>xs.getD i 0=k):=by
    apply _B
    constructor
    · exact mem_range.mpr (by omega)
    · rw[_g _ _ _ _ PB] at Xz;exact Xz
   exact⟨w-d.length,yH,by omega⟩
lemma xE (N:ℕ) (C:_a):C.lineDegrees (N+N) (Ico N (N+N))=degrees (vC N) ++ xa (degrees (vC N)) C.gates:=by rw[← wt,yZ,yp,fu,jW]
lemma zX (N k:ℕ) (C:_a):vA N k C.gates=((Ico (N+N) (N+N+C.size)).filter (λ w=>(C.lineDegrees (N+N) (Ico N (N+N))).getD w 0=k)).card:=by rw[vA,kl,kT];rw[← xE N C];simp only[vC,degrees,_c,_f,gE,Circuit.size]
lemma uP (N:ℕ) (C:_a):vA N 0 C.gates+vA N 1 C.gates=((Ico (N+N) (N+N+C.size)).filter (λ w=>(C.lineDegrees (N+N) (Ico N (N+N))).getD w 0≤1)).card:=by
 let D:=C.lineDegrees (N+N) (Ico N (N+N));let S:=Ico (N+N) (N+N+C.size);have zD:S.filter (λ w=>D.getD w 0≤1)=S.filter (λ w=>D.getD w 0=0)∪S.filter (λ w=>D.getD w 0=1):=by
  ext w;simp only[mem_filter,mem_union];constructor
  · rintro⟨hw,hd⟩;have Qu:D.getD w 0=0∨D.getD w 0=1:=by omega
    exact Qu.elim (λ h=>Or.inl ⟨hw,h⟩) (λ h=>Or.inr ⟨hw,h⟩)
  · rintro (⟨hw,hd⟩ | ⟨hw,hd⟩) <;> exact⟨hw,by omega⟩
 have hd:Disjoint (S.filter (λ w=>D.getD w 0=0)) (S.filter (λ w=>D.getD w 0=1)):=by
  apply disjoint_left.mpr
  intro w h0 h1;have h0':=(_A h0).2;have h1':=(_A h1).2;omega
 change vA N 0 C.gates+vA N 1 C.gates=(S.filter (λ w=>D.getD w 0≤1)).card;rw[zD,card_union_of_disjoint hd,zX,zX]
lemma jg (N:ℕ) (C:_a) (w:ℕ) (hw:w < N+N):(C.lineDegrees (N+N) (Ico N (N+N))).getD w 0≤1:=by
 rw[xE,_i _ _ _ _ (by simpa[vC,degrees] using hw)];have hm:∀ r∈degrees (vC N),r < 2:=by
  intro r hr;change r∈replicate N 0 ++ replicate N 1 at hr;rcases List.mem_append.mp hr with h | h
  · have:=List.eq_of_mem_replicate h;omega
  · have:=List.eq_of_mem_replicate h;omega
 have h:=uR (degrees (vC N)) 0 2 hm (by omega) w;omega
lemma zF (N:ℕ) (C:_a):vA N 2 C.gates=((Finset.range (N+N+C.size)).filter (λ w=>(C.lineDegrees (N+N) (Ico N (N+N))).getD w 0=2)).card:=by
 rw[zX];congr 1
 ext w;simp only[mem_filter,mem_Ico,mem_range];constructor
 · exact λ h=>⟨h.1.2,h.2⟩
 · rintro⟨hw,hd⟩
   have PB:N+N≤ w:=by by_contra hn;have hi:=jg N C w (by omega);omega
   exact⟨⟨PB,hw⟩,hd⟩
def kt:List ℕ→ List Gate→ List Bool
 | _,[]=>[]
 | d,g :: gs=>kg d g :: kt (d ++ [g.lineDegree d]) gs
lemma dK (d:List ℕ) (gs:List Gate):(kt d gs).length=gs.length:=by
 induction gs generalizing d with
 | nil=>rfl
 | cons g gs ih=>simp only[kt,_e,ih]
lemma ji (d:List ℕ) (gs:List Gate):zB d gs=(kt d gs).count true:=by
 induction gs generalizing d with
 | nil=>rfl
 | cons g gs ih=>
  simp only[zB,kt,List.count_cons,beq_iff_eq,ih];omega
lemma ui (xs:List Bool):xs.count true=((Finset.range xs.length).filter (λ i=>xs.getD i false=true)).card:=by
 rw[Finset.card_filter];induction xs with
 | nil=>simp
 | cons a xs ih=>
  simp only[List.count_cons,_e,Finset.sum_range_succ',List.getD_cons_succ,List.getD_cons_zero,beq_iff_eq,ih]
lemma n0 (d:List ℕ) (gs:List Gate) (j:ℕ) (hj:j < gs.length):(kt d gs).getD j false=kg ((gs.take j).foldl (λ d g=>d ++ [g.lineDegree d]) d) gs[j]:=by
 induction gs generalizing d j with
 | nil=>simp at hj
 | cons g gs ih=>
  cases j with
  | zero=>rfl
  | succ j=>
   have hj':j < gs.length:=by simpa only[_e,Nat.succ_lt_succ_iff] using hj
   simpa only[kt,List.getD_cons_succ,List.take_succ_cons,foldl_cons,List.getElem_cons_succ] using ih (d ++ [g.lineDegree d]) j hj'
lemma zt (N:ℕ) (C:_a) (j r:ℕ) (hj:j≤ C.gates.length):((C.gates.take j).foldl (λ d g=>d ++ [g.lineDegree d]) (degrees (vC N))).getD r 0=M9.yq N C (N+N+j) r:=by simpa only[M3.kM,M3.y0,← uc N] using M9.gU N C j r hj
lemma wT (N:ℕ) (C:_a) (j:ℕ) (hj:j < C.gates.length):kg ((C.gates.take j).foldl (λ d g=>d ++ [g.lineDegree d]) (degrees (vC N))) C.gates[j]=true↔M9.nM N C (N+N+j):=by
 rw[Ws];constructor
 · rintro⟨a,b,kf,cM,ha,hb⟩;refine⟨a,b,C.gates[j],M9.pW N C j hj,kf,cM,?_,?_⟩
   · rwa[← zt N C j a hj.le]
   · rwa[← zt N C j b hj.le]
 · rintro⟨a,b,g,hg,kf,cM,ha,hb⟩;rw[M9.pW N C j hj] at hg;have zD:C.gates[j]=g:=Option.some.inj hg;subst g;refine⟨a,b,kf,cM,?_,?_⟩
   · rwa[zt N C j a hj.le]
   · rwa[zt N C j b hj.le]
open Classical in
lemma jj (N:ℕ) (C:_a):ks N C.gates=((Finset.range C.gates.length).filter (λ j=>M9.nM N C (N+N+j))).card:=by
 classical
 rw[ks,ji,ui];congr 1
 rw[dK];ext j;simp only[mem_filter,mem_range];constructor
 · rintro⟨hj,hf⟩;refine⟨hj,?_⟩
   rw[n0 _ _ _ hj] at hf;exact (wT N C j hj).mp hf
 · rintro⟨hj,hf⟩;refine⟨hj,?_⟩
   rw[n0 _ _ _ hj];exact (wT N C j hj).mpr hf
open Classical in
lemma kS (N:ℕ) (C:_a):ks N C.gates=((Finset.range (M9.xu N C)).filter (M9.nM N C)).card:=by
 classical
 rw[jj];apply Finset.card_bij (λ j _=>N+N+j)
 · intro j hj;obtain⟨KG,KM⟩:=_A hj;have hj':=mem_range.mp KG;apply _B
   refine⟨mem_range.mpr ?_,KM⟩
   simp only[M9.xu,Circuit.size];omega
 · intro i _ j _ LW;omega
 · intro w hw;obtain⟨QI,RQ⟩:=_A hw
   have PB:N+N≤ w:=by obtain⟨a,b,g,hg,_⟩:=RQ;obtain⟨j,_,hweq,_⟩:=M9.uu N C w g hg;omega
   have ON:=mem_range.mp QI;have hj:w-(N+N) < C.gates.length:=by simp only[M9.xu,Circuit.size] at ON;omega
   have zD:N+N+(w-(N+N))=w:=by omega
   have yH:w-(N+N)∈(Finset.range C.gates.length).filter (λ j=>M9.nM N C (N+N+j)):=by exact _B ⟨mem_range.mpr hj,by rwa[zD]⟩
   exact⟨w-(N+N),yH,zD⟩
end M1
namespace Mc
open Classical
open M9
lemma nz (rs:List ℕ) (d:ℕ→ ℕ) (hl:rs.length≤2):(rs.filter λ r=>decide (d r=2)).length+(if (rs.find? λ r=>decide (d r=0)).isSome then 1 else 0)≤2:=by
 cases rs with
 | nil=>simp
 | cons a rs=>
  cases rs with
  | nil=>
   by_cases YL:d a=0 <;> by_cases W4:d a=2 <;>
    simp_all
  | cons b rs=>
   cases rs with
   | nil=>
    by_cases YL:d a=0 <;> by_cases W4:d a=2 <;>
     by_cases Vs:d b=0 <;> by_cases UT:d b=2 <;>
     simp_all
   | cons c cs=>simp only[_e] at hl;omega
lemma ja (N:ℕ) (C:_a) (w r:ℕ):yq N C w r=2↔r < w∧yf N C r=2:=by unfold yq;split_ifs with hr <;> simp_all
lemma jR (N:ℕ) (C:_a) (w:ℕ) (g:Gate) (hg:gateAt N C w=some g):g∈C.gates:=by
 unfold gateAt at hg;split_ifs at hg
 exact List.mem_of_getElem? hg
lemma uM (N:ℕ) (C:_a) (w:ℕ) (x8:∀ g∈C.gates,g.inputs.length≤2):(v6 N C w).length+(if (vo N C w).isSome then 1 else 0)≤2:=by
 cases hg:gateAt N C w with
 | none=>simp[v6,vo,hg]
 | some g=>
  have hl:=x8 g (jR N C w g hg);by_cases hd:yf N C w=2
  · have he:(g.inputs.filter λ r=>decide (r < w∧yf N C r=2))=(g.inputs.filter λ r=>decide (yq N C w r=2)):=by
     apply List.filter_congr
     intro r hr;simp only[ja]
    cases kf:g.op with
    | and=>
     simp only[v6,vo,hg,hd,ite_true,kf];rw[he];simpa using nz g.inputs (yq N C w) hl
    | or | not | mod _ | maj=>
     simpa[v6,vo,hg,hd,kf] using (List.length_filter_le (λ r=>decide (r < w∧yf N C r=2)) g.inputs).trans hl
  · simp[v6,vo,hg,hd]
lemma yJ (N:ℕ) (C:_a) (w:ℕ) (hf:nM N C w):(v6 N C w).length+(if (vo N C w).isSome then 1 else 0)=0:=by
 obtain⟨a,b,g,hg,kf,cM,ha,hb⟩:=hf;have W4:¬(a < w∧yf N C a=2):=by rw[← ja];omega
 have UT:¬(b < w∧yf N C b=2):=by rw[← ja];omega
 by_cases hd:yf N C w=2 <;>
  simp[v6,vo,hg,hd,kf,cM,ha,hb,W4,UT]
lemma zY (N:ℕ) (C:_a) (w:ℕ) (hd:yf N C w≠2):(v6 N C w).length+(if (vo N C w).isSome then 1 else 0)=0:=by cases hg:gateAt N C w <;> simp[v6,vo,hg,hd]
lemma dx (N:ℕ) (C:_a) (w:ℕ) (x8:∀ g∈C.gates,g.inputs.length≤2):(v6 N C w).length+(if (vo N C w).isSome then 1 else 0)≤ if yf N C w=2∧¬ nM N C w then 2 else 0:=by
 classical
 by_cases hd:yf N C w=2
 · by_cases hf:nM N C w
   · rw[yJ N C w hf];simp[hf]
   · simpa[hd,hf] using uM N C w x8
 · rw[zY N C w hd];simp[hd]
noncomputable def vP (N:ℕ) (C:_a):Finset ℕ:=(Finset.range (xu N C)).filter λ w=>yf N C w=2
noncomputable def vI (N:ℕ) (C:_a):Finset ℕ:=by
 classical
 exact (Finset.range (xu N C)).filter λ w=>nM N C w
def zW (N:ℕ) (C:_a):Finset ℕ:=(Finset.range (xu N C)).filter λ w=>(vo N C w).isSome
lemma gN (N:ℕ) (C:_a):vI N C⊆Finset.range (xu N C):=by
 classical
 exact filter_subset _ _
lemma YB (N:ℕ) (C:_a):(vm N C).length=∑ w∈Finset.range (xu N C),(v6 N C w).length:=by simp only[vm,List.length_flatMap,List.length_map];exact M7.c4 _ _
lemma gu (N:ℕ) (C:_a):(zW N C).card=∑ w∈Finset.range (xu N C),if (vo N C w).isSome then 1 else 0:=by simp[zW,Finset.sum_boole]
lemma dG (N:ℕ) (C:_a) (x8:∀ g∈C.gates,g.inputs.length≤2):(vm N C).length+(zW N C).card≤2*(vP N C\vI N C).card:=by
 classical
 rw[YB,gu,← Finset.sum_add_distrib];have hc:vP N C\vI N C=(Finset.range (xu N C)).filter λ w=>yf N C w=2∧¬ nM N C w:=by ext w;simp only[vP,vI,mem_sdiff,mem_filter];tauto
 rw[hc,Finset.card_filter];rw[Finset.mul_sum];apply sum_le_sum
 intro w hw;have hh:=dx N C w x8;split_ifs at hh ⊢ <;> omega
lemma nI (N:ℕ) (C:_a) (x8:∀ g∈C.gates,g.inputs.length≤2) (Q1:vI N C⊆vP N C):(vm N C).length+(zW N C).card≤2*((vP N C).card-(vI N C).card):=by simpa only[Finset.card_sdiff_of_subset Q1] using dG N C x8
lemma yO (N:ℕ) (C:_a):vI N C⊆vP N C:=by intro w hw;obtain⟨hr,hf⟩:=_A hw;exact _B ⟨hr,dZ N C w hf⟩
lemma bg (N:ℕ) (C:_a) (x8:∀ g∈C.gates,g.inputs.length≤2):(vm N C).length+(zW N C).card≤2*((vP N C).card-(vI N C).card):=nI N C x8 (yO N C)
end Mc
namespace M5
open M9
open Mc
lemma de (N:ℕ) (C:_a):K5.kx (vo N C) (xu N C)=(zW N C).card:=by exact (gu N C).symm
lemma bi (N:ℕ) (C:_a) (vn:List (ℕ× ℕ)) (s:M0.State) (x8:∀ g∈C.gates,g.inputs.length≤2):(M0.net (M0.yp N vn (vm N C) (vo N C) (xu N C) s)).length+(K5.yh vn (vm N C) (vI N C)).card≤(M0.net s).length+vn.length+2*((vP N C).card-(vI N C).card):=by
 have h:=K5.Yu N vn (vm N C) (vo N C)
  (xu N C) s (vI N C) (gN N C)
 rw[de] at h;have hc:=bg N C x8;omega
end M5
namespace K5
open M2 Ka M0
lemma uX (n:ℕ) (gs:List vg) (rs:List ℕ) (a r:ℕ) (h:Sum.inr (a,r)∈(yA n gs rs).1):Sum.inr (a,r)∈gs:=by
 obtain⟨hs,zD,_,wv⟩:=zO n gs rs;rw[zD] at h;rcases List.mem_append.mp h with h | h
 · exact h
 · obtain⟨us,he,_⟩:=wv (Sum.inr (a,r)) h;cases he
lemma fv (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (v:ℕ) (s:State) (a r:ℕ) (h:Sum.inr (a,r)∈net (M0.step n vn vm vo v s)):Sum.inr (a,r)∈net s∨vo v=some a:=by
 cases hw:vo v with
 | none=>
  left
  apply uX n (net s) (zP vn vm (yj s) v) a r
  simpa only[M0.step,hw,net] using h
 | some z=>
  simp only[M0.step,hw,net,List.mem_append,List.mem_singleton] at h;rcases h with h | h
  · exact Or.inl (uX n (net s) (zP vn vm (yj s) v) a r h)
  · have he:a=z:=_9 Prod.fst (Sum.inr.inj h);exact Or.inr (by simp only[he])
lemma gI (n:ℕ) (vn vm:List (ℕ× ℕ)) (vo:ℕ→ Option ℕ) (k:ℕ) (s:State) (a r:ℕ) (h:Sum.inr (a,r)∈net (yp n vn vm vo k s)):Sum.inr (a,r)∈net s∨∃ v < k,vo v=some a:=by
 induction k generalizing s with
 | zero=>exact Or.inl h
 | succ k ih=>
  change Sum.inr (a,r)∈net (yp n vn vm vo k (M0.step n vn vm vo k s)) at h;rcases ih (M0.step n vn vm vo k s) h with h | h
  · rcases fv n vn vm vo k s a r h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨k,by omega,h⟩
  · obtain⟨v,hv,he⟩:=h;exact Or.inr ⟨v,by omega,he⟩
end K5
namespace K1
open PEqualNP.CircuitLowerBounds M2
lemma VA {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ):(net N C fa fb).head?=some (Sum.inl []):=by
 obtain⟨hs,he⟩:=K5.jf N (vn N C fa fb) (k6 N C) (jC N C) (uJ N C) (M0.vC N (vh N C));change (M0.net _).head?=_;unfold U0;rw[he];change (vh N C ++ hs).head?=_;have hh:=z9 N C;cases hg:vh N C with
 | nil=>simp[hg] at hh
 | cons g gs=>simpa only[hg,List.cons_append,List.head?_cons] using hh
lemma ZS {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (rs:List ℕ) (hr:Sum.inl rs∈net N C fa fb):rs.length≤2:=by exact K5.Xh N (vn N C fa fb) (k6 N C) (jC N C) (uJ N C) (M0.vC N (vh N C)) (M1.w8 N C hm) rs hr
lemma uz {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (a r:ℕ) (hr:Sum.inr (a,r)∈net N C fa fb):yS N C a≤1:=by
 rcases K5.gI N (vn N C fa fb) (k6 N C) (jC N C) (uJ N C) (M0.vC N (vh N C)) a r hr with hf | hw
 · exact M1.zH N C a r hf
 · obtain⟨w,_,hw⟩:=hw;have hd:=M9.zZ N C w a hw;exact Nat.le_trans (Nat.le_of_eq hd) (by omega)
lemma xD (N:ℕ) (C:_a):(Mc.vP N C).card=M1.vA N 2 C.gates:=by exact (M1.zF N C).symm
lemma wH (N:ℕ) (C:_a):(Mc.vI N C).card=M1.ks N C.gates:=by exact (M1.kS N C).symm
end K1
section NearStarThresh
lemma dp {n m K:ℕ} (zo:ℕ) (T:Fin m→ Finset (Fin n)) (hT:∀ i j,i≠j→(T i∩T j).card≤1) (S:ℕ→ Finset (Fin n)) (G:Finset ℕ) (vU:ℕ→ Finset ℕ) (fs:∀ g∈G,(vU g).card≤2) (z5:∀ g∈G,∀ c∈vU g,c < g) (xA:∀ g∈G,S g=(vU g).biUnion S) (yP:∀ g,2*zo+2≤(S g).card→ g∈G) (root:Fin K→ ℕ) (line:Fin K→ Fin m) (xH:∀ j,(S (root j)\T (line j)).card≤ zo):((univ:Finset (Fin K)).biUnion λ j=>(S (root j)).image λ p=>(p,line j)).card≤2*(2*zo+1)*(G.filter λ g=>2≤(vU g).card).card+(2*zo+1)*K:=by
 classical
 let G₂:=G.filter λ g=>2≤(vU g).card;let zQ:=2*zo+1;let L:ℕ→ Finset (Fin m):=λ g=>if zQ+1≤(S g).card then
  univ.filter λ l=>(S g\T l).card≤ zo
  else ∅
 have hL:∀ g,(L g).card≤1:=by
  intro g;dsimp only[L];split_ifs with hg
  · rw[_y];intro l₁ hl₁ l₂ hl₂;by_contra xR;have h1:=(_A hl₁).2;have h2:=(_A hl₂).2;have p4:=hT l₁ l₂ xR
    have vR:S g⊆(S g\T l₁)∪(S g\T l₂)∪(T l₁∩T l₂):=by
     intro p hp;by_cases Xo:p∈T l₁
     · by_cases Xk:p∈T l₂
       · exact _G _ (_X ⟨Xo,Xk⟩)
       · exact _D _ (_G _ (_V ⟨hp,Xk⟩))
     · exact _D _ (_D _ (_V ⟨hp,Xo⟩))
    have hc:=_C vR;have Xt:=_J ((S g\T l₁)∪(S g\T l₂)) (T l₁∩T l₂);have Y9:=_J (S g\T l₁) (S g\T l₂);omega
  · simp
 let small:ℕ→ Finset (Fin n):=λ c=>if (S c).card≤ zQ then S c else ∅;have xz:∀ c,(small c).card≤ zQ:=by
  intro c;dsimp only[small];split_ifs with hc
  · exact hc
  · simp
 let C:ℕ→ ℕ→ Finset (Fin n× Fin m):=λ g c=>(L g).biUnion λ l=>(small c).image λ p=>(p,l);have hC:∀ g c,(C g c).card≤ zQ:=by
  intro g c;have hb:=_E (L g)
   (λ l=>(small c).image λ p=>(p,l)) zQ
   (λ _ _=>_T.trans (xz c))
  have LR:=hL g;dsimp only[C];exact hb.trans (by nlinarith)
 let OY:Finset (Fin n× Fin m):=G₂.biUnion λ g=>(vU g).biUnion (C g);have Nu:OY.card≤2*zQ*G₂.card:=by
  have hb:=_E G₂
   (λ g=>(vU g).biUnion (C g)) (2*zQ) (by
    intro g hg;have hc:=_E (vU g) (C g) zQ (λ c _=>hC g c);have hk:=fs g (_A hg).1;exact hc.trans (Nat.mul_le_mul_right zQ hk))
  dsimp only[OY];exact hb.trans (by ring_nf;omega)
 let WH:Finset (Fin n× Fin m):=(univ:Finset (Fin K)).biUnion λ j=>if (S (root j)).card≤ zQ then (S (root j)).image λ p=>(p,line j) else ∅;have R3:WH.card≤ zQ*K:=by
  have hs:=_E (univ:Finset (Fin K))
   (λ j=>if (S (root j)).card≤ zQ then (S (root j)).image λ p=>(p,line j) else ∅) zQ (by
    intro j _;split_ifs with hj
    · exact _T.trans hj
    · simp)
  simpa only[WH,card_univ,Fintype.card_fin,Nat.mul_comm] using hs
 have UU:∀ w p,p∈S w→ zQ+1≤(S w).card→∃ g∈G₂,zQ+1≤(S g).card∧S g⊆S w∧∃ c∈vU g,p∈S c∧(S c).card≤ zQ:=by
  intro w;induction w using strong_induction_on with
  | ind w ih=>
   intro p hp hw;have QO:w∈G:=yP w (by omega);have hp':p∈(vU w).biUnion S:=by rwa[← xA w QO]
   obtain⟨c,hc,gn⟩:=mem_biUnion.mp hp';by_cases h2:2≤(vU w).card
   · have N9:w∈G₂:=_B ⟨QO,h2⟩;by_cases Si:(S c).card≤ zQ
     · exact⟨w,N9,hw,Finset.Subset.refl _,c,hc,gn,Si⟩
     · obtain⟨g,hg,Tu,vR,c',hc',gn',Si'⟩:=ih c (z5 w QO c hc) p gn (by omega)
       have Xc:S c⊆S w:=by intro q hq;rw[xA w QO];exact _F ⟨c,hc,hq⟩
       exact⟨g,hg,Tu,vR.trans Xc,c',hc',gn',Si'⟩
   · have Mk:(vU w).card=1:=by
      have xR:(vU w).Nonempty:=⟨c,hc⟩;have:=Finset.one_le_card.mpr xR;omega
     obtain⟨c0,T7⟩:=_x.mp Mk;have Kz:c=c0:=by simpa[T7] using hc
     subst Kz;have LM:S w=S c:=by rw[xA w QO,T7,Finset.singleton_biUnion]
     have Xc:S c⊆S w:=by rw[LM]
     obtain⟨g,hg,Tu,vR,c',hc',gn',Si'⟩:=ih c (z5 w QO c hc) p gn (by rw[← LM];exact hw)
     exact⟨g,hg,Tu,vR.trans Xc,c',hc',gn',Si'⟩
 have vR:((univ:Finset (Fin K)).biUnion λ j=>(S (root j)).image λ p=>(p,line j))⊆WH∪OY:=by
  intro e he;obtain⟨j,_,KL⟩:=mem_biUnion.mp he;obtain⟨p,hp,rfl⟩:=mem_image.mp KL;by_cases hj:(S (root j)).card≤ zQ
  · apply _D
    exact _F ⟨j,_H _,by simp only[_O hj];exact _W ⟨p,hp,rfl⟩⟩
  · obtain⟨g,hg,Tu,Te,c,hc,gn,fG⟩:=UU (root j) p hp (by omega)
    have Zd:(S g\T (line j)).card≤ zo:=by
     refine (_C ?_).trans (xH j)
     intro q hq;obtain⟨Lh,Jd⟩:=_M hq;exact _V ⟨Te Lh,Jd⟩
    apply _G
    refine _F ⟨g,hg,_F ⟨c,hc,?_⟩⟩
    refine _F ⟨line j,?_,?_⟩
    · dsimp only[L];rw[_O Tu];exact _B ⟨_H _,Zd⟩
    · apply _W
      refine⟨p,?_,rfl⟩
      simpa only[small,_O fG] using gn
 have hb:=_C vR;have hu:=_J WH OY;exact hb.trans (hu.trans ((Nat.add_le_add R3 Nu).trans (by
  dsimp only[zQ];rw[Nat.add_comm])))
lemma up {n m K:ℕ} (zo:ℕ) (T:Fin m→ Finset (Fin n)) (hT:∀ i j,i≠j→(T i∩T j).card≤1) (S:ℕ→ Finset (Fin n)) (G:Finset ℕ) (vU:ℕ→ Finset ℕ) (fs:∀ g∈G,(vU g).card≤2) (z5:∀ g∈G,∀ c∈vU g,c < g) (xA:∀ g∈G,S g=(vU g).biUnion S) (yP:∀ g,2*zo+2≤(S g).card→ g∈G) (root:Fin K→ ℕ) (line:Fin K→ Fin m) (xH:∀ j,(S (root j)\T (line j)).card≤ zo) (E:Finset (Fin n× Fin m)) (zs:∀ e∈E,∃ j,e.2=line j∧e.1∈S (root j)):E.card≤2*(2*zo+1)*(G.filter λ g=>2≤(vU g).card).card+(2*zo+1)*K:=by
 classical
 refine (_C ?_).trans (dp zo T hT S G vU fs z5 xA yP root line xH)
 intro e he;obtain⟨j,hj,hp⟩:=zs e he;refine _F ⟨j,_H _,?_⟩
 exact _W ⟨e.1,hp,by cases e;simp_all⟩
end NearStarThresh
section FirstQueryK
open Ma
open Kc
variable {P L : Type*} [_6 P] [_6 L] [_5 P] [_5 L]
def vx (A:P→ Finset L) (k:ℕ) (Q:Finset L):Prop:=∃ T:Finset P,T.card≤ k∧Q⊆T.biUnion A
def jO (I:P→ L→ Prop) [_4 I] (k zo:ℕ) (A:Finset L) (p:P):Prop:=zo+1≤ A.card∧¬(vx (pencil I) k A∧k+1≤(A.filter (I p)).card)
def zU (I:P→ L→ Prop) [_4 I] {G:Type*} [_5 G] (zo:ℕ) (gs:Finset G) (S:G→ Finset P) (A:G→ Finset L) (E:Finset (P× L)):Finset (P× L):=univ.filter λ e=>e∉E∧I e.1 e.2∧∃ g∈gs,e.1∈S g∧e.2∈A g∧(A g).card≤ zo
noncomputable def zg (I:P→ L→ Prop) [_4 I] {G:Type*} [_5 G] (k:ℕ) (gs:Finset G) (A:G→ Finset L):Finset (P× L):=by
 classical
 exact univ.filter λ e=>I e.1 e.2∧∃ g∈gs,e.2∈A g∧vx (pencil I) k (A g)∧k+1≤((A g).filter (I e.1)).card
lemma q2 (I:P→ L→ Prop) [_4 I] {G:Type*} [_5 G] (k zo:ℕ) (gs:Finset G) (S:G→ Finset P) (A:G→ Finset L) (E:Finset (P× L)) (p:P) (l:L) (g:G) (hg:g∈gs) (hp:p∈S g) (hl:l∈A g) (hI:I p l) (hE:(p,l)∉E) (xz:(p,l)∉zU I zo gs S A E) (bX:(p,l)∉zg I k gs A):jO I k zo (A g) p:=by
 classical
 constructor
 · by_contra! hc;exact xz (_B ⟨_H _,hE,hI,g,hg,hp,hl,by omega⟩)
 · rintro⟨zs,kp⟩;exact bX (_B ⟨_H _,hI,g,hg,hl,zs,kp⟩)
end FirstQueryK
section E1E2FmapBound
open PEqualNP.CircuitLowerBounds M2 K1
lemma cm {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (qZ:∀ j,yS N C (fa j)≤2) (gP:∀ j,yS N C (fb j)≤2) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (j:Fin J) (hf:d2 (λ r=>(run (net N C fa fb) (M1.vy N C x) y).getD r false) (cJ N C fa fb j)):(C.wires (x ++ y)).getD (fa j) false=true∧(C.wires (x ++ y)).getD (fb j) false=true:=by
 rcases hf with ⟨ha,hb,_⟩
 change (run (net N C fa fb) _ y).getD (vr N C (fa j)) false=true at ha;change (run (net N C fa fb) _ y).getD (vr N C (fb j)) false=true at hb;rw[j7 N C fa fb _ y hy] at ha hb;exact⟨M1.k7 N C hm x y hx hy (fa j) (qZ j) ha,M1.k7 N C hm x y hx hy (fb j) (gP j) hb⟩
lemma d7 {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (gP:∀ j,yS N C (fb j)≤2) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (w:ℕ) (hw:w∈yh N C fa fb) (hf:d2 (λ r=>(run (net N C fa fb) (M1.vy N C x) y).getD r false) (cx N C fa fb w)):∃ j,(C.wires (x ++ y)).getD (fa j) false=true∧(C.wires (x ++ y)).getD (fb j) false=true:=by
 obtain⟨Mt,SY,_⟩:=(gx N C fa fb w).mp hw;have wj:=jI N C w SY;have hc:=M9.xi N C w _ _ wj;rcases hf with ⟨ha,hb,hk⟩
 change (run (net N C fa fb) _ y).getD (vr N C (vD N C w)) false=true at ha;change (run (net N C fa fb) _ y).getD (vr N C (vz N C w)) false=true at hb;change (run (net N C fa fb) _ y).getD (yR N C fa fb w) false=true at hk;rw[j7 N C fa fb _ y hy,yv N C hm x y hx hy _ (Nat.le_trans (Nat.le_of_eq hc.2.2.2.1) (by omega))] at ha;rw[j7 N C fa fb _ y hy,yv N C hm x y hx hy _ (Nat.le_trans (Nat.le_of_eq hc.2.2.2.2) (by omega))] at hb;have Qh:=M9.dI
  N C hm x y hx hy w _ _ wj ha hb
 obtain⟨e,he,OA,wP⟩:=(qE N C fa fb _ y hy w Mt).mp hk;obtain⟨j,rfl⟩:=(dy N C fa fb e).mp he;have UY:=M9.ZQ
  N C hm x y hx hy (fa j) w wP Qh
 refine⟨j,UY,?_⟩
 exact M1.k7 N C hm x y hx hy (fb j) (gP j) OA
lemma d9 {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (qZ:∀ j,yS N C (fa j)≤2) (gP:∀ j,yS N C (fb j)≤2) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (t:nR) (ht:t∈k5 N C fa fb) (hf:d2 (λ r=>(run (net N C fa fb) (M1.vy N C x) y).getD r false) t):∃ j,(C.wires (x ++ y)).getD (fa j) false=true∧(C.wires (x ++ y)).getD (fb j) false=true:=by
 rcases (bU N C fa fb t).mp ht with ⟨j,rfl⟩ | ⟨w,hw,rfl⟩
 · exact⟨j,cm N C fa fb hm qZ gP x y hx hy j hf⟩
 · exact d7 N C fa fb hm gP x y hx hy w hw hf
lemma g0 {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (qZ:∀ j,yS N C (fa j)≤2) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (j:Fin J) (ha:(C.wires (x ++ y)).getD (fa j) false=true) (d3:(C.wires (x ++ replicate N false)).getD (fa j) false=false) (jn:(run (vh N C) (M1.vy N C x) y).getD (vr N C (fb j)) false=true):∃ t∈k5 N C fa fb,d2 (λ r=>(run (net N C fa fb) (M1.vy N C x) y).getD r false) t:=by
 have jn':(run (net N C fa fb) (M1.vy N C x) y).getD (vr N C (fb j)) false=true:=by rw[j7 N C fa fb _ y hy];exact jn
 by_cases z1:(run (vh N C) (M1.vy N C x) y).getD (vr N C (fa j)) false=true
 · refine⟨cJ N C fa fb j,(bU N C fa fb _).mpr (Or.inl ⟨j,rfl⟩),?_⟩
   refine⟨?_,jn',jn'⟩
   change (run (net N C fa fb) _ y).getD (vr N C (fa j)) false=true;rw[j7 N C fa fb _ y hy];exact z1
 · have W3:(run (vh N C) (M1.vy N C x) y).getD (vr N C (fa j)) false=false:=Bool.eq_false_iff.mpr z1
   have Qw:yS N C (fa j)=2:=by
    by_contra hn;have cX:yS N C (fa j)≤1:=by have:=qZ j;omega
    exact z1 (M1.zE N C hm x y hx hy (fa j) cX ha d3)
   have Ra:(M9.v1 C x y).getD (fa j) false=false:=by rw[← yv N C hm x y hx hy (fa j) (qZ j)];exact W3
   obtain⟨w,a,b,wP,hf,z1,Lx⟩:=M9.pB N C hm x y hx hy (fa j) ⟨Qw,ha,d3,Ra⟩;have hc:=M9.xi N C w a b hf;have hr:Kf.xj (k6 N C) (M0.yo (M1.vy N C x) (jC N C)) (vn N C fa fb) (λ r=>(run (vh N C) (M1.vy N C x) y).getD r false) w:=⟨(fa j,vr N C (fb j)),(dy N C fa fb _).mpr ⟨j,rfl⟩,jn,wP⟩;have hw:w∈yh N C fa fb:=(gx N C fa fb w).mpr
    ⟨hc.2.2.1,⟨a,b,hf⟩,jq _ _ _ _ w hr⟩
   refine⟨cx N C fa fb w,(bU N C fa fb _).mpr (Or.inr ⟨w,hw,rfl⟩),?_⟩
   refine⟨?_,?_,(qE N C fa fb _ y hy w hc.2.2.1).mpr hr⟩
   · change (run (net N C fa fb) _ y).getD (vr N C (vD N C w)) false=true;rw[pL N C w a b hf,j7 N C fa fb _ y hy,yv N C hm x y hx hy a (Nat.le_trans (Nat.le_of_eq hc.2.2.2.1) (by omega))];exact z1
   · change (run (net N C fa fb) _ y).getD (vr N C (vz N C w)) false=true;rw[qP N C w a b hf,j7 N C fa fb _ y hy,yv N C hm x y hx hy b (Nat.le_trans (Nat.le_of_eq hc.2.2.2.2) (by omega))];exact Lx
lemma dA {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (qZ:∀ j,yS N C (fa j)≤2) (gP:∀ j,yS N C (fb j)≤2) (x y:List Bool) (hx:x.length=N) (hy:y.length=N) (j:Fin (k5 N C fa fb).length) (hf:∀ i,(run (net N C fa fb) (M1.vy N C x) y).getD (ye N C fa fb j i) false=true):∃ k,(C.wires (x ++ y)).getD (fa k) false=true∧(C.wires (x ++ y)).getD (fb k) false=true:=d9 N C fa fb hm qZ gP x y hx hy _ (List.get_mem _ j) ((mo N C fa fb j _).mp hf)
lemma j4 {J:ℕ} (N:ℕ) (I:_0 N) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (qZ:∀ j,yS N C (fa j)≤2) (gP:∀ j,yS N C (fb j)≤2) (vM:∀ j (z:Fin (N+N)→ Bool),(C.wires (ofFn z)).getD (fa j) false=true→(C.wires (ofFn z)).getD (fb j) false=true→∃ p l,I p l∧z (_7 N p)=true∧z (_8 N l)=true) (x y:Fin N→ Bool) (j:Fin (k5 N C fa fb).length) (hf:∀ i,(run (net N C fa fb) (M1.vy N C (ofFn x)) (ofFn y)).getD (ye N C fa fb j i) false=true):∃ p l,I p l∧x p=true∧y l=true:=by obtain⟨k,ha,hb⟩:=dA N C fa fb hm qZ gP (ofFn x) (ofFn y) (by simp) (by simp) j hf;rw[← List.ofFn_fin_append] at ha hb;obtain⟨p,l,hi,hp,hl⟩:=vM k (Fin.append x y) ha hb;exact⟨p,l,hi,by simpa only[Fin.append_left] using hp,by simpa only[Fin.append_right] using hl⟩
lemma qJ {J:ℕ} (N:ℕ) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (qZ:∀ j,yS N C (fa j)≤2) (p l:Fin N) (j:Fin J) (ha:(C.wires (ofFn (M1.yd p l))).getD (fa j) false=true) (d3:(C.wires (ofFn (M1.yG p))).getD (fa j) false=false) (jn:(run (vh N C) (M1.vy N C (ofFn (λ q=>decide (q=p)))) (ofFn (λ u=>decide (u=l)))).getD (vr N C (fb j)) false=true):∃ k,∀ i,(run (net N C fa fb) (M1.vy N C (ofFn (λ q=>decide (q=p)))) (ofFn (λ u=>decide (u=l)))).getD (ye N C fa fb k i) false=true:=by
 apply (dz N C fa fb (λ r=>(run (net N C fa fb) (M1.vy N C (ofFn (λ q=>decide (q=p)))) (ofFn (λ u=>decide (u=l)))).getD r false)).mpr
 rw[M1.nV] at ha;rw[M1.nj] at d3;exact g0 N C fa fb hm qZ _ _ (by simp) (by simp) j ha d3 jn
end E1E2FmapBound
section BaseFnetAndSubtraction
open PEqualNP.CircuitLowerBounds M2 Kd
open K1 Kb
open K7 Kc
lemma nU {N:ℕ} (gs hs:List vg) (labels:ℕ→ Bool) (w:List (_3 N)):yU (gs ++ hs) labels w=yU hs labels (yU gs labels w):=by simpa only[yU,foldl_append]
lemma g8 {N:ℕ} (gs hs:List vg) (labels:ℕ→ Bool) (w:ℕ) (hw:w < N+gs.length):vX (N:=N) (gs ++ hs) labels w=vX (N:=N) gs labels w:=by
 unfold vX uV;rw[nU];apply kE
 rw[k9];simpa using hw
lemma gl (gs hs:List vg) (N w:ℕ) (g7:N≤ w) (hw:w < N+gs.length):gateAt (gs ++ hs) N w=gateAt gs N w:=by unfold gateAt;exact _i gs hs (Sum.inl []) (w-N) (by omega)
lemma bN (gs hs:List vg) (N g:ℕ) (Zd:N≤ g) (hg:g < N+gs.length):yk (gs ++ hs) N g=yk gs N g:=by simp only[yk,gl gs hs N g Zd hg]
lemma Yf (gs hs:List vg) (N g:ℕ) (Zd:N≤ g) (hg:g < N+gs.length):vu (gs ++ hs) N g=vu gs N g:=by simp only[vu,gl gs hs N g Zd hg]
lemma Yx {N:ℕ} (gs hs:List vg) (L:ℕ→(Fin N→ Bool)→ Bool) (g:ℕ) (Zd:N≤ g) (hg:g < N+gs.length):vH (gs ++ hs) L g=vH gs L g:=by simp only[vH,bN gs hs N g Zd hg]
lemma fX {N:ℕ} (gs hs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (g:ℕ) (hg:g∈vw gs N α):vk (N:=N) (gs ++ hs) α (vu (gs ++ hs) N g)=vk (N:=N) gs α (vu gs N g):=by
 classical
 have UD:=(_A hg).1;obtain⟨Zd,Vf⟩:=mem_Ico.mp UD;rw[Yf gs hs N g Zd Vf];have z5:=yz gs vK N α g hg;exact g8 gs hs α (vu gs N g) (by omega)
noncomputable def cv {N:ℕ} (I:_0 N) [_4 I] (gs:List vg) (α:ℕ→ Bool):_2 N:=by
 classical
 exact univ.filter λ e:Fin N× Fin N=>∃ r∈Ico N (N+gs.length),2≤(vk (N:=N) gs α r).card∧(∀ u∈vk (N:=N) gs α r,I e.1 u)∧e.2∈vk (N:=N) gs α r
noncomputable def gm {N:ℕ} (I:_0 N) [_4 I] (gs:List vg) (α:ℕ→ Bool) (r:ℕ):_2 N:=by
 classical
 exact univ.filter λ e:Fin N× Fin N=>2≤(vk (N:=N) gs α r).card∧(∀ u∈vk (N:=N) gs α r,I e.1 u)∧e.2∈vk (N:=N) gs α r∧∀ c∈vU gs N r,¬(2≤(vk (N:=N) gs α c).card∧e.2∈vk (N:=N) gs α c)
lemma zR {N:ℕ} (gs:List vg) (α:ℕ→ Bool) (r:ℕ) (hr:r < N):(vk (N:=N) gs α r).card≤1:=by have h:vk (N:=N) gs α r={⟨r,hr⟩}:=kU gs α ⟨r,hr⟩;rw[h];simp
lemma qm {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p p' l l':Fin N,p≠p'→ l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l')) (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (x8:∀ rs,Sum.inl rs∈gs→ rs.length≤2) (α:ℕ→ Bool) (r:ℕ) (hr:r∈Ico N (N+gs.length)):(gm I gs α r).card≤2:=by
 classical
 by_cases xR:(gm I gs α r).Nonempty
 · obtain⟨e0,Td⟩:=xR;have h0:=(_A Td).2;have YV:2≤(vk (N:=N) gs α r).card:=h0.1;obtain⟨u₁,hu₁,u₂,hu₂,RG⟩:=_Z (by omega:1 < (vk (N:=N) gs α r).card)
   have TL:∀ e∈gm I gs α r,e.1=e0.1:=by intro e he;have h:=(_A he).2;by_contra PW;exact hI e.1 e0.1 u₁ u₂ PW RG ⟨h.2.1 u₁ hu₁,h.2.1 u₂ hu₂,h0.2.1 u₁ hu₁,h0.2.1 u₂ hu₂⟩
   by_cases wv:r∈wW gs N α
   · let bu:=(vU gs N r).filter λ c=>(vk (N:=N) gs α c).card≤1
     have vR:gm I gs α r⊆bu.biUnion λ c=>(vk (N:=N) gs α c).image λ l=>(e0.1,l):=by
      intro e he;have h:=(_A he).2;have hb:e.2∈vk (N:=N) gs α r:=h.2.2.1;rw[xg gs vK α r wv] at hb;obtain⟨c,hc,WP⟩:=hb;have Si:(vk (N:=N) gs α c).card≤1:=by by_contra! Ml;exact h.2.2.2 c hc ⟨Ml,WP⟩
      refine _F ⟨c,_B ⟨hc,Si⟩,?_⟩
      refine _W ⟨e.2,WP,?_⟩
      exact Prod.ext (TL e he).symm rfl
     have hk2:bu.card≤2:=(card_filter_le _ _).trans (dt gs N α x8 r wv);have hb:=_E bu
      (λ c=>(vk (N:=N) gs α c).image λ l=>(e0.1,l)) 1 (λ c hc=>_T.trans (_A hc).2)
     exact (_C vR).trans (hb.trans (by omega))
   · have x1:r∈vw gs N α:=by
      rcases uG gs N α r hr with h | h
      · exact (wv h).elim
      · exact h
     have gV:=wD gs vK α r x1;rw[gV] at YV;simp at YV
 · rw[_w.mp xR];simp
lemma Yv {N:ℕ} (I:_0 N) [_4 I] (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool):∀ r,r∈Ico N (N+gs.length)→∀ e:Fin N× Fin N,2≤(vk (N:=N) gs α r).card→(∀ u∈vk (N:=N) gs α r,I e.1 u)→ e.2∈vk (N:=N) gs α r→∃ r'∈Ico N (N+gs.length),r'≤ r∧e∈gm I gs α r':=by
 intro r;induction r using strong_induction_on with
 | ind r ih=>
  intro hr e h2 hI OK;by_cases hmin:∀ c∈vU gs N r,¬(2≤(vk (N:=N) gs α c).card∧e.2∈vk (N:=N) gs α c)
  · exact⟨r,hr,le_rfl,_B ⟨_H _,h2,hI,OK,hmin⟩⟩
  · push Not at hmin
    obtain⟨c,hc,Sn,Rq⟩:=hmin
    have wv:r∈wW gs N α:=by
     rcases uG gs N α r hr with h | h
     · exact h
     · rw[wD gs vK α r h] at h2;simp at h2
    have ZY:=yV gs vK N α r wv c hc;have Tx:N≤ c:=by by_contra! z5;have:=zR gs α c z5;omega
    have Pt:c∈Ico N (N+gs.length):=mem_Ico.mpr ⟨Tx,lt_trans ZY (mem_Ico.mp hr).2⟩;have vR:vk (N:=N) gs α c⊆vk (N:=N) gs α r:=by intro u hu;exact (xg gs vK α r wv u).mpr ⟨c,hc,hu⟩
    obtain⟨r',hr',P6,Wy⟩:=ih c ZY Pt e Sn (λ u hu=>hI u (vR hu)) Rq;exact⟨r',hr',le_trans P6 ZY.le,Wy⟩
lemma gB {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p p' l l':Fin N,p≠p'→ l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l')) (gs hs:List vg) (vK:gs.head?=some (Sum.inl [])) (x8:∀ rs,Sum.inl rs∈(gs ++ hs)→ rs.length≤2) (α:ℕ→ Bool):(cv I (gs ++ hs) α \ cv I gs α).card≤2*hs.length:=by
 classical
 have vK':(gs ++ hs).head?=some (Sum.inl []):=by
  cases gs with
  | nil=>simp at vK
  | cons g _=>simpa using vK
 have vR:cv I (gs ++ hs) α \ cv I gs α⊆(Ico (N+gs.length) (N+(gs ++ hs).length)).biUnion (gm I (gs ++ hs) α):=by
  intro e he;obtain⟨Sp,Td⟩:=_M he;obtain⟨_,r,hr,h2,OJ,OK⟩:=_A Sp;obtain⟨r',hr',_,Wy⟩:=Yv I (gs ++ hs) vK' α r hr e h2 OJ OK;have SL:N+gs.length≤ r':=by
   by_contra! z5;have Wy':=(_A Wy).2;have VK:vk (N:=N) (gs ++ hs) α r'=vk (N:=N) gs α r':=g8 gs hs α r' z5;apply Td
   refine _B ⟨_H _,r',mem_Ico.mpr ⟨(mem_Ico.mp hr').1,z5⟩,?_,?_,?_⟩
   · simpa only[VK] using Wy'.1
   · intro u hu;exact Wy'.2.1 u (by simpa only[VK] using hu)
   · simpa only[VK] using Wy'.2.2.1
  exact _F ⟨r',mem_Ico.mpr ⟨SL,(mem_Ico.mp hr').2⟩,Wy⟩
 have hb:=_E
  (Ico (N+gs.length) (N+(gs ++ hs).length))
  (gm I (gs ++ hs) α) 2 (λ r hr=>qm I hI (gs ++ hs) vK' x8 α r (mem_Ico.mpr ⟨by have:=(mem_Ico.mp hr).1;omega,(mem_Ico.mp hr).2⟩))
 refine (_C vR).trans (hb.trans ?_)
 simp[Nat.mul_comm];omega
lemma uw (gs:List vg) (N:ℕ) (α:ℕ→ Bool) (g:ℕ) (hg:g∈vw gs N α):Sum.inr (yk gs N g,vu gs N g)∈gs∨∃ r,Sum.inr (yk gs N g,r)∈gs:=by
 classical
 obtain⟨UD,mI⟩:=_A hg;obtain⟨Zd,Vf⟩:=mem_Ico.mp UD;have yH:=jR gs N g Zd Vf;cases v7:gateAt gs N g with
 | inl rs=>simp[wE,v7] at mI
 | inr ar=>
  rcases ar with ⟨a,r⟩
  right
  refine⟨r,?_⟩
  simpa only[yk,v7] using yH
lemma we {N:ℕ} (C:_a) (α:ℕ→ Bool) (g:ℕ) (hg:g∈vw (vh N C) N α):(C.lineDegrees (N+N) (Ico N (N+N))).getD (yk (vh N C) N g) 0≤1:=by
 rcases uw (vh N C) N α g hg with h | ⟨r,hr⟩
 · exact M1.zH N C _ _ h
 · exact M1.zH N C _ r hr
lemma wG {J N:ℕ} (C:_a) (fa fb:Fin J→ ℕ) (α:ℕ→ Bool) (g:ℕ) (hg:g∈vw (net N C fa fb) N α):(C.lineDegrees (N+N) (Ico N (N+N))).getD (yk (net N C fa fb) N g) 0≤1:=by
 rcases uw (net N C fa fb) N α g hg with h | ⟨r,hr⟩
 · exact uz N C fa fb _ _ h
 · exact uz N C fa fb _ r hr
lemma ul (N:ℕ) (C:_a):(vh N C).head?=some (Sum.inl []):=z9 N C
lemma bh (N:ℕ) (C:_a) (hm:_b C):∀ rs,Sum.inl rs∈vh N C→ rs.length≤2:=M1.w8 N C hm
lemma jw (gs:List vg) (N:ℕ) (α:ℕ→ Bool) (g:ℕ) (hg:g∈vw gs N α):α (yk gs N g)=false:=by
 classical
 have mI:=(_A hg).2;cases v7:gateAt gs N g with
 | inl rs=>simp[wE,v7] at mI
 | inr ar=>
  rcases ar with ⟨a,r⟩
  simp only[wE,v7] at mI;simpa only[yk,v7] using mI
lemma q8 {N:ℕ} (C:_a) (x:Fin N→ Bool) (a:ℕ):Z C a x=M1.vy N C (ofFn x) a:=rfl
lemma yQ {N:ℕ} (C:_a) (a:ℕ) (p:Fin N):p∈vS C a↔Z C a (λ q=>decide (q=p))=true:=gh C a p
noncomputable def zk {n:ℕ} (I:Fin n→ Fin n→ Prop) (L:ℕ→(Fin n→ Bool)→ Bool) (a:ℕ):Prop:=∃ S:Finset (Fin n),S.card≤4∧L a (vB I S)=false
noncomputable def vO {n:ℕ} (I:Fin n→ Fin n→ Prop) (L:ℕ→(Fin n→ Bool)→ Bool) (a:ℕ) (x:Fin n→ Bool):Bool:=by
 classical
 exact if zk I L a then L a x else true
noncomputable def vi {N:ℕ} (I:_0 N) (C:_a):ℕ→(Fin N→ Bool)→ Bool:=vO I (Z C)
noncomputable def vc {N:ℕ} (I:_0 N) (C:_a) (a:ℕ):Bool:=vi I C a (λ _=>false)
lemma w4 {N:ℕ} (C:_a) (hm:_b C):xZ (Z (N:=N) C):=λ a x x' hxx' hx=>wm C hm a x x' hxx' hx
lemma xr {n:ℕ} (I:Fin n→ Fin n→ Prop) (L:ℕ→(Fin n→ Bool)→ Bool) (hL:xZ L):xZ (vO I L):=by
 classical
 intro a x x' hxx';by_cases ha:zk I L a
 · simpa[vO,ha] using hL a x x' hxx'
 · simp[vO,ha]
lemma uO {n:ℕ} (I:Fin n→ Fin n→ Prop) (L:ℕ→(Fin n→ Bool)→ Bool) (a:ℕ) (x:Fin n→ Bool):L a x=true→ vO I L a x=true:=by
 classical
 by_cases ha:zk I L a <;> simp[vO,ha]
lemma wF {n:ℕ} (I:Fin n→ Fin n→ Prop) (L:ℕ→(Fin n→ Bool)→ Bool) (a:ℕ) (x:Fin n→ Bool) (hf:vO I L a x=false):zk I L a:=by
 classical
 by_contra hn;simp[vO,hn] at hf
lemma n6 {n:ℕ} (I:Fin n→ Fin n→ Prop) (L:ℕ→(Fin n→ Bool)→ Bool) (a:ℕ) (x₀:Fin n→ Bool) (hf:vO I L a x₀=false) (x:Fin n→ Bool):vO I L a x=L a x:=by
 classical
 simp only[vO,_O (wF I L a x₀ hf)]
lemma w9 {n:ℕ} (I:Fin n→ Fin n→ Prop) (L:ℕ→(Fin n→ Bool)→ Bool) (S:Finset (Fin n)) (hS:S.card≤4) (a:ℕ):vO I L a (vB I S)=L a (vB I S):=by
 classical
 by_cases ha:zk I L a
 · simp[vO,ha]
 · have ht:L a (vB I S)=true:=Bool.eq_true_of_not_eq_false (λ hf=>ha ⟨S,hS,hf⟩);simp[vO,ha,ht]
lemma jp {N:ℕ} (I:_0 N) [_4 I] (C:_a) (a:ℕ) (v4:zk I (Z C) a):K6.dead C (yt N) (zV I) 4 a:=by
 classical
 obtain⟨S,hS,hf⟩:=v4;refine⟨S,hS,?_⟩
 rw[← du I S,qU];have zD:vB I S=(λ p=>decide (∀ l∈S,¬ I p l)):=by
  funext p
  by_cases hp:∀ l∈S,¬ I p l <;> simp[vB,hp]
 change (C.wires (ofFn (vB I S) ++ replicate N false)).getD a false=false at hf;rw[zD] at hf;exact hf
theorem nq {n:ℕ} (I:Fin n→ Fin n→ Prop) (gs:List vg) (L:ℕ→(Fin n→ Bool)→ Bool) (hL:xZ L) (r0 r1 r2:ℕ) (vM:qz I gs L r0 r1 r2):qz I gs (vO I L) r0 r1 r2:=by
 classical
 intro x y h0 h1 h2;by_contra c3;obtain⟨l0,Je,hy0⟩:=(xY gs (λ a=>vO I L a x) y r0).mp h0;obtain⟨l1,LQ,hy1⟩:=(xY gs (λ a=>vO I L a x) y r1).mp h1;obtain⟨l2,LH,hy2⟩:=(xY gs (λ a=>vO I L a x) y r2).mp h2;let S:Finset (Fin n):={l0,l1,l2};have hS:S.card≤4:=by
  have h3:S.card≤3:=(_K _ _).trans
   ((Nat.add_le_add_right (_K _ _) 1).trans (by simp))
  omega
 let ys:Fin n→ Bool:=λ l=>decide (l∈S);let xs:=vB I S;have KY:∀ l∈S,y l=true:=by intro l hl;simp only[S,mem_insert,mem_singleton] at hl;rcases hl with rfl | rfl | rfl <;> assumption
 have hx:∀ p,x p=true→ xs p=true:=by intro p hp;simp only[xs,vB,decide_eq_true_eq];intro l hl hI;exact c3 ⟨p,l,hI,hp,KY l hl⟩
 have UE:(run gs (λ a=>vO I L a x) (ofFn ys)).getD r0 false=true:=(xY gs _ ys r0).mpr ⟨l0,Je,by simp[ys,S]⟩
 have TX:(run gs (λ a=>vO I L a x) (ofFn ys)).getD r1 false=true:=(xY gs _ ys r1).mpr ⟨l1,LQ,by simp[ys,S]⟩
 have Jo:(run gs (λ a=>vO I L a x) (ofFn ys)).getD r2 false=true:=(xY gs _ ys r2).mpr ⟨l2,LH,by simp[ys,S]⟩
 have Uo:(λ a=>vO I L a xs)=(λ a=>L a xs):=by
  funext a
  exact w9 I L S hS a
 have lift (r:ℕ) (ht:(run gs (λ a=>vO I L a x) (ofFn ys)).getD r false=true):(run gs (λ a=>L a xs) (ofFn ys)).getD r false=true:=by
  have hm:=ze gs _ _
   (λ a=>xr I L hL a x xs hx) ys ys (λ _=>id) r ht
  simpa only[Uo] using hm
 obtain⟨p,l,hI,hp,hl⟩:=vM xs ys (lift r0 UE) (lift r1 TX) (lift r2 Jo);exact (_o hp) l (_o hl) hI
noncomputable def v2 {N:ℕ} (I:_0 N) [_4 I] (C:_a):_2 N:=by
 classical
 exact univ.filter λ e=>I e.1 e.2∧∃ w∈wX C (N+N) (Ico N (N+N)) 1,K6.dead C (yt N) (zV I) 4 w∧e.1∈vS C w∧5≤((vS C w).filter λ p=>I p e.2).card
theorem fW {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p p' l l':Fin N,p≠p'→ l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l')) (C:_a) (hg:K6.good C):(v2 I C).card≤32*(wX C (N+N) (Ico N (N+N)) 1).card:=by
 classical
 let f:Fin N× Fin N→ Fin (N+N)× Fin N:=λ e=>(_7 N e.1,e.2);have Yc:Function.Injective f:=by intro a b h;have hp:a.1=b.1:=(zf N).injective (_9 Prod.fst h);have hl:a.2=b.2:=_9 (λ z:Fin (N+N)× Fin N=>z.2) h;exact Prod.ext hp hl
 have vR:(v2 I C).image f⊆K6.counted C (yt N) (zV I) (wX C (N+N) (Ico N (N+N)) 1) 4:=by
  intro e he;obtain⟨a,ha,rfl⟩:=mem_image.mp he;obtain⟨_,NT,w,hw,v4,z1,yP⟩:=_A ha;have yP':4+1≤(K6.vT C (yt N) w∩zV I a.2).card:=by simpa only[n4] using yP
  apply _B
  refine⟨_H _,?_,w,hw,v4,?_,yP'⟩
  · change _7 N a.1∈zV I a.2;exact (zp _ _).mpr (_B ⟨_H _,NT⟩)
  · change _7 N a.1∈K6.vT C (yt N) w;rw[← w2];exact (zp _ _).mpr z1
 have xV:=_C vR;rw[_l _ Yc] at xV;have OL:=K6.km C hg (yt N) (zV I)
  (f8 I hI) 4 (by omega)
  (wX C (N+N) (Ico N (N+N)) 1)
  (K7.Zk C hg (Ico N (N+N)) 1)
 exact xV.trans (by simpa using OL)
lemma zi {N:ℕ} (I:_0 N) [_4 I] (C:_a) (a:ℕ) (ha:(C.lineDegrees (N+N) (Ico N (N+N))).getD a 0≤1) (hα:vi I C a (λ _=>false)=false) (p l:Fin N) (wK:I p l) (hp:vi I C a (λ q=>decide (q=p))=true) (yP:5≤((univ.filter λ q:Fin N=>vi I C a (λ r=>decide (r=q))=true).filter (λ q=>I q l)).card):(p,l)∈v2 I C:=by
 classical
 have Rh:zk I (Z C) a:=wF I (Z C) a _ hα;have v4:K6.dead C (yt N) (zV I) 4 a:=jp I C a Rh;have zD:∀ x,vi I C a x=Z C a x:=n6 I (Z C) a _ hα;have Jv:Z C a (λ q=>decide (q=p))=true:=by simpa only[zD] using hp
 have z1:p∈vS (N:=N) C a:=(yQ C a p).mpr Jv;have vR:((univ.filter λ q:Fin N=>vi I C a (λ r=>decide (r=q))=true).filter λ q=>I q l)⊆(vS (N:=N) C a).filter λ q=>I q l:=by
  intro q hq;obtain⟨KV,ny⟩:=_A hq;have Ku:Z C a (λ r=>decide (r=q))=true:=by simpa only[zD] using (_A KV).2
  exact _B ⟨(yQ C a q).mpr Ku,ny⟩
 have Uq:5≤((vS (N:=N) C a).filter λ q=>I q l).card:=yP.trans (_C vR);have h2:2≤(K6.vT C (yt N) a).card:=by
  have h1:=(card_filter_le (vS (N:=N) C a) (λ q=>I q l)).trans' Uq;have h2':(vS (N:=N) C a).card≤(K6.vT C (yt N) a).card:=by
   have Yc:Function.Injective (zf N):=(zf N).injective;rw[← _l (vS (N:=N) C a) Yc];apply _C
   intro x hx;obtain⟨q,hq,rfl⟩:=mem_image.mp hx;rw[← w2];exact (zp _ _).mpr hq
  omega
 have v7:=K6.yB C (yt N) a h2;exact _B ⟨_H _,wK,a,_B ⟨mem_Ico.mpr v7,ha⟩,v4,z1,Uq⟩
noncomputable def kQ {N:ℕ} (I:_0 N) (C:_a) (gs:List vg) (r:ℕ) (X Y:_3 N):Bool:=by
 classical
 exact (run gs (λ a=>vi I C a (λ p=>decide (p∈X))) (ofFn (λ l=>decide (l∈Y)))).getD r false
lemma gr (N:ℕ) (I:_0 N) (C:_a) (hm:_b C) (gs:List vg) (r:ℕ):M6.z7 (kQ (N:=N) I C gs r):=by
 classical
 intro X X' Y Y' KD' Jk' hr;apply ze gs (λ a=>vi I C a (λ p=>decide (p∈X))) (λ a=>vi I C a (λ p=>decide (p∈X'))) (λ a ha=>xr I (Z C) (w4 C hm) a _ _ (λ p hp=>decide_eq_true (KD' (_o hp))) ha) (λ l=>decide (l∈Y)) (λ l=>decide (l∈Y')) (λ l hl=>decide_eq_true (Jk' (_o hl))) r hr
lemma fT {N:ℕ} (I:_0 N) (C:_a) (gs:List vg) (r:ℕ) (p u:Fin N) (hu:u∈v9 gs (vi I C) r p):kQ (N:=N) I C gs r {p} {u}=true:=by
 classical
 have zD:(λ q:Fin N=>decide (q∈({p}:_3 N)))=(λ q=>decide (q=p)):=by funext q;simp
 have SM:(λ l:Fin N=>decide (l∈({u}:_3 N)))=(λ l=>decide (l=u)):=by funext l;simp
 unfold kQ;rw[zD,SM];exact (y4 gs _ u r).mpr hu
lemma Zf {N:ℕ} (I:_0 N) (C:_a) (gs:List vg) (r:ℕ) (l:Fin N):l∈vk (N:=N) gs (vc I C) r↔kQ (N:=N) I C gs r ∅ {l}=true:=by
 classical
 have zD:(λ q:Fin N=>decide (q∈(∅:_3 N)))=(λ _=>false):=by funext q;simp
 have SM:(λ u:Fin N=>decide (u∈({l}:_3 N)))=(λ u=>decide (u=l)):=by funext u;simp
 unfold kQ vk vc;rw[zD,SM];exact (y4 gs _ l r).symm
lemma jZ {N:ℕ} (I:_0 N) [_4 I] {G:Type*} [_5 G] (zo:ℕ) (gs:Finset G) (S:G→_3 N) (A:G→_3 N) (E:_2 N) (kp:∀ g∈gs,∀ l p,p∈S g→ I p l→5≤((S g).filter λ q=>I q l).card→(p,l)∈E):(zU I zo gs S A E).card≤(4*zo)*gs.card:=by
 classical
 let B:G→_2 N:=λ g=>if (A g).card≤ zo then
  (A g).biUnion λ l=>(Kc.WS I (S g) E l).image λ p=>(p,l)
  else ∅
 have hB:∀ g∈gs,(B g).card≤4*zo:=by
  intro g hg;dsimp only[B];split_ifs with xz
  · have xV:=_E (A g)
     (λ l=>(Kc.WS I (S g) E l).image λ p=>(p,l)) 4 (by
      intro l _;refine _T.trans ?_
      by_contra! h5;have vR:Kc.WS I (S g) E l⊆(S g).filter λ q=>I q l:=by intro q hq;obtain⟨Lh,Kx,_⟩:=_A hq;exact _B ⟨Lh,Kx⟩
      have h5':5≤((S g).filter λ q=>I q l).card:=Nat.succ_le_of_lt (lt_of_lt_of_le h5 (_C vR));obtain⟨p,hp⟩:=card_pos.mp (by omega:0 < (Kc.WS I (S g) E l).card);have Mf:=_A hp;exact Mf.2.2 (kp g hg l p Mf.1 Mf.2.1 h5'))
    exact xV.trans (Nat.mul_le_mul_right 4 xz |>.trans (by omega))
  · simp
 have vR:zU I zo gs S A E⊆gs.biUnion B:=by
  intro e he;obtain⟨_,RW,OZ,g,hg,hp,hl,xz⟩:=_A he;apply _F
  refine⟨g,hg,?_⟩
  simp only[B,_O xz,mem_biUnion];refine⟨e.2,hl,_W ⟨e.1,?_,by simp⟩⟩
  exact _B ⟨hp,OZ,RW⟩
 exact (_C vR).trans ((_E gs B (4*zo) hB).trans (by rw[Nat.mul_comm]))
def y2 {n:ℕ} (zo:ℕ) (S:ℕ→ Finset (Fin n)) (G:Finset ℕ) (vU:ℕ→ Finset ℕ) (w:ℕ):Finset (Fin n):=if w∈G then (vU w).biUnion λ c=>if _h:c < w then y2 zo S G vU c else ∅ else if (S w).card≤4+zo then S w else ∅
termination_by w
lemma kw {n:ℕ} (zo:ℕ) (S:ℕ→ Finset (Fin n)) (G:Finset ℕ) (vU:ℕ→ Finset ℕ) (w:ℕ) (hw:w∈G) (z5:∀ c∈vU w,c < w):y2 zo S G vU w=(vU w).biUnion (y2 zo S G vU):=by
 rw[y2,_O hw];apply Finset.biUnion_congr rfl
 intro c hc;exact _Q (z5 c hc)
lemma uk {n:ℕ} (zo:ℕ) (S:ℕ→ Finset (Fin n)) (G:Finset ℕ) (vU:ℕ→ Finset ℕ) (w:ℕ) (hw:w∉G):y2 zo S G vU w=if (S w).card≤4+zo then S w else ∅:=by rw[y2,if_neg hw]
lemma nP {n:ℕ} (zo:ℕ) (S:ℕ→ Finset (Fin n)) (G:Finset ℕ) (vU:ℕ→ Finset ℕ) (z5:∀ g∈G,∀ c∈vU g,c < g) (xA:∀ g∈G,S g=(vU g).biUnion S):∀ w,y2 zo S G vU w⊆S w:=by
 intro w;induction w using strong_induction_on with
 | ind w ih=>
  by_cases hw:w∈G
  · rw[kw zo S G vU w hw (z5 w hw)];intro p hp;obtain⟨c,hc,gn⟩:=mem_biUnion.mp hp;rw[xA w hw];exact _F ⟨c,hc,ih c (z5 w hw c hc) gn⟩
  · rw[uk zo S G vU w hw];split_ifs
    · exact Finset.Subset.refl _
    · exact empty_subset _
lemma hJ {n:ℕ} (zo:ℕ) (Ow:3≤ zo) (S:ℕ→ Finset (Fin n)) (G:Finset ℕ) (vU:ℕ→ Finset ℕ) (w:ℕ) (hw:2*zo+2≤(y2 zo S G vU w).card):w∈G:=by
 by_contra hn;rw[uk zo S G vU w hn] at hw;split_ifs at hw with h
 · omega
 · simp at hw
lemma gz {n m:ℕ} (zo:ℕ) (S:ℕ→ Finset (Fin n)) (G:Finset ℕ) (vU:ℕ→ Finset ℕ) (z5:∀ g∈G,∀ c∈vU g,c < g) (xA:∀ g∈G,S g=(vU g).biUnion S) (T:Fin m→ Finset (Fin n)) (w:ℕ) (l:Fin m) (xH:(S w\T l).card≤ zo):(y2 zo S G vU w\T l).card≤ zo:=by
 refine (_C ?_).trans xH
 intro p hp;obtain⟨Sb,Mn⟩:=_M hp;exact _V ⟨nP zo S G vU z5 xA w Sb,Mn⟩
lemma dq {n m:ℕ} (zo:ℕ) (S:ℕ→ Finset (Fin n)) (G L:Finset ℕ) (vU:ℕ→ Finset ℕ) (A:ℕ→ Finset (Fin n)) (z5:∀ g∈G,∀ c∈vU g,c < g) (xA:∀ g∈G,S g=(vU g).biUnion S) (zJ:∀ g,g∉G→(S g).Nonempty→ g∈L∧S g⊆A g) (T:Fin m→ Finset (Fin n)) (r:ℕ) (l:Fin m) (p:Fin n) (xH:(S r\T l).card≤ zo) (Y4:∀ g∈L,p∈A g→(A g∩T l).card≤4):∀ w,S w⊆S r→ p∈S w→ p∈y2 zo S G vU w:=by
 intro w;induction w using strong_induction_on with
 | ind w ih=>
  intro QI hp;by_cases hw:w∈G
  · have hp':p∈(vU w).biUnion S:=by rwa[← xA w hw]
    obtain⟨c,hc,gn⟩:=mem_biUnion.mp hp';have Xc:S c⊆S w:=by intro q hq;rw[xA w hw];exact _F ⟨c,hc,hq⟩
    rw[kw zo S G vU w hw (z5 w hw)];exact _F ⟨c,hc,ih c (z5 w hw c hc) (Xc.trans QI) gn⟩
  · obtain⟨O4,m7⟩:=zJ w hw ⟨p,hp⟩
    have hinside:(S w∩T l).card≤4:=by
     refine (_C ?_).trans (Y4 w O4 (m7 hp))
     intro q hq;obtain⟨Ta,QJ⟩:=_P hq;exact _X ⟨m7 Ta,QJ⟩
    have houtside:(S w\T l).card≤ zo:=by
     refine (_C ?_).trans xH
     intro q hq;obtain⟨Ta,QJ⟩:=_M hq;exact _V ⟨QI Ta,QJ⟩
    have zs:S w⊆(S w∩T l)∪(S w\T l):=by
     intro q hq;by_cases QJ:q∈T l
     · exact _D _ (_X ⟨hq,QJ⟩)
     · exact _G _ (_V ⟨hq,QJ⟩)
    have hc:=_C zs;have hu:=_J (S w∩T l) (S w\T l);have hs:(S w).card≤4+zo:=by omega
    simpa only[uk zo S G vU w hw,_O hs] using hp
theorem wp {n m K:ℕ} (zo:ℕ) (Ow:3≤ zo) (T:Fin m→ Finset (Fin n)) (hT:∀ i j,i≠j→(T i∩T j).card≤1) (S:ℕ→ Finset (Fin n)) (G L:Finset ℕ) (vU:ℕ→ Finset ℕ) (A:ℕ→ Finset (Fin n)) (fs:∀ g∈G,(vU g).card≤2) (z5:∀ g∈G,∀ c∈vU g,c < g) (xA:∀ g∈G,S g=(vU g).biUnion S) (zJ:∀ g,g∉G→(S g).Nonempty→ g∈L∧S g⊆A g) (root:Fin K→ ℕ) (line:Fin K→ Fin m) (xH:∀ j,(S (root j)\T (line j)).card≤ zo) (E:Finset (Fin n× Fin m)) (zs:∀ e∈E,∃ j,e.2=line j∧e.1∈S (root j)) (Y4:∀ e∈E,∀ g∈L,e.1∈A g→(A g∩T e.2).card≤4):E.card≤2*(2*zo+1)*(G.filter λ g=>2≤(vU g).card).card+(2*zo+1)*K:=by
 apply up zo T hT (y2 zo S G vU) G vU fs z5 (λ g hg=>kw zo S G vU g hg (z5 g hg)) (hJ zo Ow S G vU) root line (λ j=>gz zo S G vU z5 xA T (root j) (line j) (xH j)) E
 intro e he;obtain⟨j,hj,hp⟩:=zs e he;refine⟨j,hj,?_⟩
 exact dq zo S G L vU A z5 xA zJ T (root j) (line j) e.1 (xH j) (λ g hg Kg=>by simpa only[← hj] using Y4 e he g hg Kg) (root j) (Finset.Subset.refl _) hp
theorem m3 {N K:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (hT:∀ l u,l≠u→((univ.filter λ p=>I p l)∩(univ.filter λ p=>I p u)).card≤1) (S:ℕ→_3 N) (wW vw:Finset ℕ) (vU:ℕ→ Finset ℕ) (vH vX vk:ℕ→_3 N) (v9:ℕ→ Fin N→_3 N) (fs:∀ g∈wW,(vU g).card≤2) (z5:∀ g∈wW,∀ c∈vU g,c < g) (xA:∀ g∈wW,S g=(vU g).biUnion S) (zJ:∀ g,g∉wW→(S g).Nonempty→ g∈vw∧S g⊆vH g) (x5:∀ r p,p∈S r→∃ g∈vw,p∈vH g∧Kc.yW I (vX g) p∧vX g⊆v9 r p) (F:ℕ→_3 N→_3 N→ Bool) (xT:∀ r,M6.z7 (F r)) (qk:∀ r p u,u∈v9 r p→ F r {p} {u}=true) (yi:∀ r l,l∈vk r↔F r ∅ {l}=true) (ye:Fin K→ Fin 3→ ℕ) (vM:∀ j X Y,(∀ i,F (ye j i) X Y=true)→
 ∃ p∈X,∃ l∈Y,I p l)
 (E:_2 N)
 (zs:∀ e∈E,∃ j i,vk (ye j i)={e.2}∧∀ t,e.2∈v9 (ye j t) e.1)
 (Sr:∀ e∈E,∀ r,e.2∈v9 r e.1→ e.2∉vk r→ e.1∈S r)
 (Y4:∀ e∈E,∀ g∈vw,e.1∈vH g→((vH g).filter λ p=>I p e.2).card≤4):
 E.card≤18*(wW.filter λ g=>2≤(vU g).card).card+27*K:=by
 classical
 let k5:=(univ:Finset ((Fin K× Fin 3)× Fin N)).filter
  (λ x=>vk (ye x.1.1 x.1.2)={x.2})
 let Tr:={j // j∈k5};let points (j:Tr):_3 N:=univ.filter λ p=>(p,j.val.2)∈E∧∀ t,j.val.2∈v9 (ye j.val.1.1 t) p;have WI (j:Tr):∃ r∈({ye j.val.1.1 (K8.bK j.val.1.2),ye j.val.1.1 (K8.b2 j.val.1.2)}:Finset ℕ),((S r).filter (λ p=>¬ I p j.val.2)).card≤4∧points j⊆S r:=by
  have hj:vk (ye j.val.1.1 j.val.1.2)={j.val.2}:=(_A j.property).2;apply K8.qi I hI S v9 vk vw vH vX x5 F xT qk yi (ye j.val.1.1 (K8.bK j.val.1.2)) (ye j.val.1.1 (K8.b2 j.val.1.2)) j.val.2 (K8.me I ye F xT vM vk yi j.val.1.1 j.val.1.2 j.val.2 hj) (points j)
  · intro hb p hp;obtain⟨he,hr⟩:=(_A hp).2;exact Sr (p,j.val.2) he _ (hr _) hb
  · intro hb p hp;obtain⟨he,hr⟩:=(_A hp).2;exact Sr (p,j.val.2) he _ (hr _) hb
 let mE:Tr→ ℕ:=λ j=>Classical.choose (WI j);have Zq (j:Tr):((S (mE j)).filter (λ p=>¬ I p j.val.2)).card≤4∧points j⊆S (mE j):=(Classical.choose_spec (WI j)).2;let dW:=Fintype.equivFin Tr;have Z8:E.card≤18*(wW.filter λ g=>2≤(vU g).card).card+9*Fintype.card Tr:=by
  have h4:=wp 4 (by omega)
   (λ l=>univ.filter λ p=>I p l) hT S wW vw vU vH
   fs z5 xA zJ
   (λ k=>mE (dW.symm k)) (λ k=>(dW.symm k).val.2)
   (λ k=>by
    have zD:S (mE (dW.symm k))\(univ.filter λ p=>I p (dW.symm k).val.2)=(S (mE (dW.symm k))).filter λ p=>¬ I p (dW.symm k).val.2:=by ext p;simp
    rw[zD];exact (Zq (dW.symm k)).1)
   E
   (λ e he=>by
    obtain⟨j,i,hs,hr⟩:=zs e he;let d:Tr:=⟨((j,i),e.2),_B ⟨_H _,hs⟩⟩;refine⟨dW d,?_,?_⟩
    · simp[d]
    · simpa[d] using (Zq d).2 (_B ⟨_H _,he,hr⟩))
   (λ e he g hg hp=>by
    have zD:vH g∩(univ.filter λ p=>I p e.2)=(vH g).filter λ p=>I p e.2:=by ext p;simp
    rw[zD];exact Y4 e he g hg hp)
  omega
 have Pq:Fintype.card Tr≤3*K:=by simpa only[Tr,Fintype.card_coe,k5] using M8.pA vk ye
 omega
end BaseFnetAndSubtraction
section OrInlTightAndBase37
open PEqualNP.CircuitLowerBounds M2 Kd
open K1 Kb
open K7 Kc
noncomputable def vV (gs:List vg) (N:ℕ):Finset ℕ:=by
 classical
 exact (Ico N (N+gs.length)).filter λ w=>∃ rs,gateAt gs N w=Sum.inl rs
lemma jQ (gs:List vg) (N:ℕ) (α:ℕ→ Bool):vV gs N⊆wW gs N α:=by
 classical
 intro w hw;obtain⟨Z9,rs,pE⟩:=_A hw;exact _B ⟨Z9,by simp[Yi,pE]⟩
lemma jL (gs:List vg) (N:ℕ) (α:ℕ→ Bool):((wW gs N α).filter λ g=>2≤(vU gs N g).card)⊆vV gs N:=by
 classical
 intro w hw;obtain⟨L0,hw2⟩:=_A hw;have Z9:=(_A L0).1;cases v7:gateAt gs N w with
 | inl rs=>exact _B ⟨Z9,rs,v7⟩
 | inr ar=>
  rcases ar with ⟨a,r⟩
  have hkc:(vU gs N w).card=1:=by simp[vU,v7]
  omega
lemma gq (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (N:ℕ):N∈vV gs N:=by
 classical
 have qX:=qQ gs vK;exact _B ⟨mem_Ico.mpr ⟨le_rfl,by omega⟩,[],pK gs vK N⟩
lemma fJ (N z:ℕ) (s:M1.State) (g:Gate):(M1.yx N z s g).countP Sum.isLeft≤ if g.lineDegree (M1.degrees s)=1∨g.lineDegree (M1.degrees s)=2 then 1 else 0:=by
 unfold M1.yx;dsimp only;split_ifs
 all_goals try split
 all_goals try split_ifs
 all_goals simp[Sum.isLeft]
lemma gH (N z:ℕ) (gs:List Gate) (s:M1.State):(M1.net (gs.foldl (M1.ya N z) s)).countP Sum.isLeft≤(M1.net s).countP Sum.isLeft+M1.vQ 1 (M1.degrees s) gs+M1.vQ 2 (M1.degrees s) gs:=by
 induction gs generalizing s with
 | nil=>simp[M1.vQ]
 | cons g gs ih=>
  rw[foldl_cons];refine (ih (M1.ya N z s g)).trans ?_
  rw[M1.zG,M1.yC,List.countP_append];have hp:=fJ N z s g;simp only[M1.vQ];split_ifs at hp ⊢ <;> omega
lemma xO (gs:List vg) (N:ℕ):(vV gs N).card=gs.countP Sum.isLeft:=by
 classical
 have MX:(vV gs N).card=((Finset.range gs.length).filter (λ j=>(gs[j]?).elim false Sum.isLeft)).card:=by
  apply Finset.card_bij (λ w _=>w-N)
  · intro w hw;obtain⟨Z9,rs,pE⟩:=_A hw;obtain⟨g7,kJ⟩:=mem_Ico.mp Z9;have z5:w-N < gs.length:=by omega
    refine _B ⟨mem_range.mpr z5,?_⟩
    rw[getElem?_eq_getElem z5];have RN:gs[w-N]=Sum.inl rs:=by rw[← _k gs (Sum.inl []) z5];exact pE
    simp[RN]
  · intro a ha b hb zD;have YH:=(mem_Ico.mp (_A ha).1).1;have Za:=(mem_Ico.mp (_A hb).1).1;omega
  · intro j hj;obtain⟨Kv,LL⟩:=_A hj;have z5:=mem_range.mp Kv;rw[getElem?_eq_getElem z5] at LL;cases hg:gs[j] with
    | inl rs=>
     refine⟨N+j,_B ⟨mem_Ico.mpr ⟨by omega,by omega⟩,rs,?_⟩,by omega⟩
     change gs.getD (N+j-N) (Sum.inl [])=Sum.inl rs;rw[add_sub_cancel_left,_k gs (Sum.inl []) z5,hg]
    | inr _=>simp[hg] at LL
 have Z8:∀ ls:List vg,(∑ i∈Finset.range ls.length,if (ls[i]?).elim false Sum.isLeft=true then 1 else 0)=ls.countP Sum.isLeft:=by
  intro ls;induction ls with
  | nil=>simp
  | cons y ys ih=>
   rw[_e,Finset.sum_range_succ',List.countP_cons];simp only[List.getElem?_cons_zero,List.getElem?_cons_succ,Option.elim_some];rw[ih];cases y with
   | inl rs=>simp[Sum.isLeft]
   | inr ar=>simp[Sum.isLeft]
 rw[MX,Finset.card_filter,Z8 gs]
theorem nH (N:ℕ) (C:_a):(vV (vh N C) N).card≤1+M1.vA N 1 C.gates+M1.vA N 2 C.gates:=by
 have h1:=xO (vh N C) N;have h2:=gH N (N+N+C.size) C.gates
  (M1.vC N)
 have OQ:(M1.net (C.gates.foldl (M1.ya N (N+N+C.size)) (M1.vC N))).countP Sum.isLeft=(vh N C).countP Sum.isLeft:=rfl;have PR:(M1.net (M1.vC N)).countP Sum.isLeft=1:=by simp[M1.vC,M1.net]
 have hd1:M1.vA N 1 C.gates=M1.vQ 1 (M1.degrees (M1.vC N)) C.gates:=rfl;have hd2:M1.vA N 2 C.gates=M1.vQ 2 (M1.degrees (M1.vC N)) C.gates:=rfl;omega
lemma dM {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p p' l l':Fin N,p≠p'→ l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l')) (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (x8:∀ rs,Sum.inl rs∈gs→ rs.length≤2) (α:ℕ→ Bool):(cv I gs α).card≤2*(vV gs N).card:=by
 classical
 have vR:cv I gs α⊆(vV gs N).biUnion (gm I gs α):=by
  intro e he;obtain⟨_,r,hr,h2,OJ,OK⟩:=_A he;have OI:∀ w,w∈Ico N (N+gs.length)→2≤(vk (N:=N) gs α w).card→(∀ u∈vk (N:=N) gs α w,I e.1 u)→ e.2∈vk (N:=N) gs α w→∃ r'∈vV gs N,e∈gm I gs α r':=by
   intro w;induction w using strong_induction_on with
   | ind w ih=>
    intro hw Pb MD OX;cases v7:gateAt gs N w with
    | inl rs=>
     by_cases hmin:∀ c∈vU gs N w,¬(2≤(vk (N:=N) gs α c).card∧e.2∈vk (N:=N) gs α c)
     · exact⟨w,_B ⟨hw,rs,v7⟩,_B ⟨_H _,Pb,MD,OX,hmin⟩⟩
     · push Not at hmin
       obtain⟨c,hc,Sn,Rq⟩:=hmin
       have wv:w∈wW gs N α:=_B ⟨hw,by simp[Yi,v7]⟩
       have ZY:=yV gs vK N α w wv c hc;have Tx:N≤ c:=by by_contra! z5;have:=zR gs α c z5;omega
       have Pt:c∈Ico N (N+gs.length):=mem_Ico.mpr ⟨Tx,lt_trans ZY (mem_Ico.mp hw).2⟩;have Pf:vk (N:=N) gs α c⊆vk (N:=N) gs α w:=λ u hu=>(xg gs vK α w wv u).mpr ⟨c,hc,hu⟩;exact ih c ZY Pt Sn (λ u hu=>MD u (Pf hu)) Rq
    | inr ar=>
     rcases ar with ⟨a,c⟩
     by_cases ha:α a=true
     · have wv:w∈wW gs N α:=_B ⟨hw,by simp[Yi,v7,ha]⟩
       have Xc:j2 N w c∈vU gs N w:=by simp[vU,v7]
       have ZY:=yV gs vK N α w wv (j2 N w c) Xc;have Tx:N≤ j2 N w c:=by
        by_contra! z5;have Za:=zR gs α (j2 N w c) z5;have zD:vk (N:=N) gs α w=vk (N:=N) gs α (j2 N w c):=by ext u;rw[xg gs vK α w wv];simp[vU,v7]
        rw[zD] at Pb;omega
       have Pt:j2 N w c∈Ico N (N+gs.length):=mem_Ico.mpr ⟨Tx,lt_trans ZY (mem_Ico.mp hw).2⟩;have zD:vk (N:=N) gs α w=vk (N:=N) gs α (j2 N w c):=by ext u;rw[xg gs vK α w wv];simp[vU,v7]
       exact ih (j2 N w c) ZY Pt (by rw[← zD];exact Pb) (λ u hu=>MD u (by rw[zD];exact hu)) (by rw[← zD];exact OX)
     · have x1:w∈vw gs N α:=_B
        ⟨hw,by simp[wE,v7,Bool.eq_false_iff.mpr ha]⟩
       rw[wD gs vK α w x1] at Pb;simp at Pb
  obtain⟨r',hr',Wy⟩:=OI r hr h2 OJ OK;exact _F ⟨r',hr',Wy⟩
 have hb:=_E (vV gs N) (gm I gs α) 2
  (λ r hr=>qm I hI gs vK x8 α r (_A hr).1)
 exact (_C vR).trans (hb.trans (by omega))
def yK (gs:List vg) (N:ℕ) (α:ℕ→ Bool) (w:ℕ):ℕ:=if w < N then w else if w < N+gs.length then match gateAt gs N w with
 | .inl _=>w
 | .inr (a,r)=>if α a∧r < w then yK gs N α r else N
 else N
termination_by w
lemma Wn (gs:List vg) (N:ℕ) (α:ℕ→ Bool) (w:ℕ) (hw:w < N+gs.length):yK gs N α w≤ w:=by
 induction w using strong_induction_on with
 | ind w ih=>
  rw[yK];split_ifs with h1
  · exact le_rfl
  · cases v7:gateAt gs N w with
    | inl rs=>exact le_rfl
    | inr ar=>
     rcases ar with ⟨a,r⟩
     dsimp only;split_ifs with h3
     · exact (ih r h3.2 (by omega)).trans h3.2.le
     · omega
lemma ZV (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (N:ℕ) (α:ℕ→ Bool) (w:ℕ):yK gs N α w < N∨yK gs N α w∈vV gs N:=by
 classical
 induction w using strong_induction_on with
 | ind w ih=>
  by_cases h1:w < N
  · rw[yK,_O h1];exact Or.inl h1
  · by_cases h2:w < N+gs.length
    · cases v7:gateAt gs N w with
      | inl rs=>
       have hr:yK gs N α w=w:=by rw[yK,if_neg h1,_O h2,v7]
       rw[hr];exact Or.inr (_B ⟨mem_Ico.mpr ⟨by omega,h2⟩,rs,v7⟩)
      | inr ar=>
       rcases ar with ⟨a,r⟩
       have hr:yK gs N α w=if α a∧r < w then yK gs N α r else N:=by rw[yK,if_neg h1,_O h2,v7]
       rw[hr];split_ifs with h3
       · exact ih r h3.2
       · exact Or.inr (gq gs vK N)
    · rw[yK,if_neg h1,if_neg h2];exact Or.inr (gq gs vK N)
def wx (gs:List vg) (j:ℕ):ℕ:=(gs.take j).countP Sum.isLeft
lemma n8 (gs:List vg) (i j:ℕ) (hi:i < j) (hj:j < gs.length) (Nd:(gs[i]'(by omega)).isLeft=true):
 wx gs i < wx gs j:=by
 induction gs generalizing i j with
 | nil=>simp at hj
 | cons g rest ih=>
  cases i with
  | zero=>
   cases j with
   | zero=>omega
   | succ j'=>
    simp only[List.getElem_cons_zero] at Nd;cases g with
    | inl rs=>
     simp only[wx,List.take_zero,List.countP_nil,List.take_succ_cons,List.countP_cons,Sum.isLeft_inl,ite_true];omega
    | inr _=>simp at Nd
  | succ i'=>
   cases j with
   | zero=>omega
   | succ j'=>
    simp only[wx,List.take_succ_cons,List.countP_cons];have Lv:=ih i' j' (by omega) (by simpa using hj) (by simpa using Nd);simp only[wx] at Lv;split_ifs <;> omega
def xp (gs:List vg) (N:ℕ) (α:ℕ→ Bool) (r:ℕ):ℕ:=
 let r':=yK gs N α r;if r' < N then r' else N+wx gs (r'-N)
def v3 (full:List vg) (N:ℕ) (α:ℕ→ Bool) (off:ℕ):List vg→ List Gate
 | []=>[]
 | .inl rs :: rest=>
  ⟨GateOp.or,rs.map λ r=>if r < N+off then xp full N α r else N⟩ :: v3 full N α (off+1) rest
 | .inr _ :: rest=>v3 full N α (off+1) rest
def y9 (gs:List vg) (N:ℕ) (α:ℕ→ Bool):_a:=⟨v3 gs N α 0 gs,0⟩
lemma jo (full:List vg) (N:ℕ) (α:ℕ→ Bool) (off:ℕ) (gs:List vg):(v3 full N α off gs).length=gs.countP Sum.isLeft:=by
 induction gs generalizing off with
 | nil=>simp[v3]
 | cons g rest ih=>
  cases g with
  | inl rs=>simp only[v3,_e,List.countP_cons,Sum.isLeft_inl,ite_true,ih,Nat.add_comm]
  | inr ar=>simp only[v3,_e,List.countP_cons,Sum.isLeft_inr,Bool.false_eq_true,ite_false,Nat.add_zero,ih]
lemma q6 (gs:List vg) (N:ℕ) (α:ℕ→ Bool):(y9 gs N α).size=(vV gs N).card:=by unfold Circuit.size y9;rw[jo,xO]
lemma fd (full:List vg) (N:ℕ) (α:ℕ→ Bool) (off:ℕ) (gs:List vg) (vR:∀ rs,Sum.inl rs∈gs→ rs.length≤2):Ke.good ⟨v3 full N α off gs,0⟩:=by
 intro g hg;induction gs generalizing off with
 | nil=>simp[v3] at hg
 | cons x rest ih=>
  cases x with
  | inl rs=>
   simp only[v3,List.mem_cons] at hg;rcases hg with rfl | hg
   · exact⟨Or.inr rfl,by simpa using vR rs (by simp)⟩
   · exact ih (off+1) (λ rs' pE'=>vR rs' (List.mem_cons_of_mem _ pE')) hg
  | inr ar=>
   exact ih (off+1) (λ rs' pE'=>vR rs' (List.mem_cons_of_mem _ pE')) hg
lemma gJ (full:List vg) (N:ℕ) (α:ℕ→ Bool) (off:ℕ) (gs:List vg) (g:Gate) (hg:g∈v3 full N α off gs):g.op=GateOp.or:=by
 induction gs generalizing off with
 | nil=>simp[v3] at hg
 | cons x rest ih=>
  cases x with
  | inl rs=>
   simp only[v3,List.mem_cons] at hg;rcases hg with rfl | hg
   · rfl
   · exact ih (off+1) hg
  | inr ar=>exact ih (off+1) hg
lemma mG (full:List vg) (N:ℕ) (α:ℕ→ Bool):∀(gs:List vg) (off j:ℕ) (hj:j < gs.length) (rs:List ℕ) (pE:gs[j]=Sum.inl rs),∃ bA:(gs.take j).countP Sum.isLeft < (v3 full N α off gs).length,(v3 full N α off gs)[(gs.take j).countP Sum.isLeft]'bA=⟨GateOp.or,rs.map λ r=>if r < N+(off+j) then xp full N α r else N⟩:=by
 intro gs;induction gs with
 | nil=>intro off j hj;simp at hj
 | cons g rest ih=>
  intro off j hj rs pE;cases j with
  | zero=>
   simp only[List.getElem_cons_zero] at pE;subst pE;refine⟨by simp[v3],?_⟩
   simp[v3]
  | succ j'=>
   cases g with
   | inl rs0=>
    obtain⟨bA,zD⟩:=ih (off+1) j' (by simpa using hj) rs (by simpa using pE);refine⟨by
     simp only[List.take_succ_cons,List.countP_cons,Sum.isLeft_inl,ite_true,v3,_e];exact Nat.succ_lt_succ bA,?_⟩
    simp only[List.take_succ_cons,List.countP_cons,Sum.isLeft_inl,ite_true,v3,List.getElem_cons_succ];simpa[Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using zD
   | inr ar=>
    obtain⟨bA,zD⟩:=ih (off+1) j' (by simpa using hj) rs (by simpa using pE);refine⟨by simpa[v3] using bA,?_⟩
    simp only[List.take_succ_cons,List.countP_cons,Sum.isLeft_inr,Bool.false_eq_true,ite_false,Nat.add_zero,v3];simpa[Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using zD
lemma fL {N:ℕ} (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (x:Fin N→ Bool):∀ w,w < N+gs.length→ Ke.value (y9 gs N α) x (xp gs N α w)=((K9.xG gs α).wires (ofFn x)).getD w false:=by
 classical
 intro w;induction w using strong_induction_on with
 | ind w ih=>
  intro hw;have qX:=qQ gs vK;have Xd:Ke.value (y9 gs N α) x N=false:=by
   have MT:N < N+(y9 gs N α).size:=by
    rw[q6,xO];cases gs with
    | nil=>simp at vK
    | cons g rest=>
     have:g=Sum.inl []:=by simpa using vK
     subst this;simp
   have Vi:=Ke.ud (y9 gs N α) x N le_rfl MT;have Ql:(y9 gs N α).gates[0]'(by
    change 0 < (v3 gs N α 0 gs).length;rw[jo];cases gs with
    | nil=>simp at vK
    | cons g rest=>
     have:g=Sum.inl []:=by simpa using vK
     subst this;simp)=⟨GateOp.or,[]⟩:=by
    cases gs with
    | nil=>simp at vK
    | cons g rest=>
     have:g=Sum.inl []:=by simpa using vK
     subst this;simp[y9,v3]
   simp only[Nat.sub_self,Ql,GateOp.eval] at Vi;exact Vi
  by_cases g7:w < N
  · have f3:yK gs N α w=w:=by rw[yK,_O g7]
    have S3:xp gs N α w=w:=by simp[xp,f3,g7]
    rw[S3,Ke.xF (y9 gs N α) x ⟨w,g7⟩,K9.mn];change _=(run gs α (ofFn x)).getD w false;rw[M2.zr gs α (ofFn x) w (by simp[g7]),_k _ _ (by simp[g7])];simp
  · have RN:N≤ w:=Nat.le_of_not_gt g7
    have UW:((K9.xG gs α).wires (ofFn x)).getD w false=(run gs α (ofFn x)).getD w false:=by rw[K9.mn]
    rw[UW];have cK:(run gs α (ofFn x)).getD w false=match gateAt gs N w with
     | .inl rs=>rs.any (λ r=>if r < w then (run gs α (ofFn x)).getD r false else false)
     | .inr (a,r)=>if α a∧r < w then (run gs α (ofFn x)).getD r false else false:=by
     let j:=w-N;have hj:j < gs.length:=by dsimp[j];omega
     have hg:gateAt gs N w=gs[j]:=_k _ _ hj;rw[hg];have YS:gs=(gs.take j ++ [gs[j]]) ++ gs.drop (j+1):=by rw[List.append_assoc,List.singleton_append,← List.drop_eq_getElem_cons hj,List.take_append_drop]
     have p5:run gs α (ofFn x)=run (gs.drop (j+1)) α (run (gs.take j ++ [gs[j]]) α (ofFn x)):=by simpa only[run,foldl_append] using _9 (λ hs=>run hs α (ofFn x)) YS
     have y5:(run (gs.take j) α (ofFn x)).length=w:=by simp[zv,Nat.min_eq_left hj.le,j];omega
     have UM:=c8 (gs.take j) gs[j] α (ofFn x);have Uc:w < (run (gs.take j ++ [gs[j]]) α (ofFn x)).length:=by rw[UM,_c,y5];simp
     have SR:(run gs α (ofFn x)).getD w false=step α (run (gs.take j) α (ofFn x)) gs[j]:=by rw[p5,zr (gs.drop (j+1)) α _ w Uc,UM,_g _ _ _ _ (by omega)];simp[y5]
     rw[SR];have So:∀ r,(run (gs.take j) α (ofFn x)).getD r false=if r < w then (run gs α (ofFn x)).getD r false else false:=by
      intro r;by_cases hr:r < w
      · have cA:run gs α (ofFn x)=run (gs[j] :: gs.drop (j+1)) α (run (gs.take j) α (ofFn x)):=by
         rw[p5,UM,← xU]
        rw[_O hr,cA];exact (M2.zr _ _ _ r (by simpa only[y5] using hr)).symm
      · rw[if_neg hr];exact _j _ _ (by omega)
     cases gs[j] with
     | inl rs=>
      simp only[step,List.any_map,So];rfl
     | inr ar=>
      rcases ar with ⟨a,r⟩
      cases ha:α a <;> by_cases hr:r < w <;>
       simp only[step,ha,hr,Bool.true_and,Bool.false_and,Bool.false_eq_true,↓reduceIte,false_and,true_and,and_false,So]
    rw[cK];cases v7:gateAt gs N w with
    | inl rs=>
     have f3:yK gs N α w=w:=by rw[yK,if_neg g7,_O hw,v7]
     have S3:xp gs N α w=N+wx gs (w-N):=by simp[xp,f3,g7]
     have hj:w-N < gs.length:=by omega
     have Jx:gs[w-N]=Sum.inl rs:=by have:=_k gs (Sum.inl []) hj;change gateAt gs N w=_ at this;rw[v7] at this;exact this.symm
     obtain⟨bA,XF⟩:=mG gs N α gs 0 (w-N) hj rs Jx;have hidx_len:wx gs (w-N) < (y9 gs N α).size:=by change wx gs (w-N) < (v3 gs N α 0 gs).length;exact bA
     have Vi:=Ke.ud (y9 gs N α) x
      (N+wx gs (w-N)) (Nat.le_add_right _ _) (by omega)
     simp only[add_sub_cancel_left] at Vi;have TU:∀ z5,(y9 gs N α).gates[wx gs (w-N)]'z5=⟨GateOp.or,rs.map λ r=>if r < N+(0+(w-N)) then xp gs N α r else N⟩:=λ _=>XF;rw[TU _] at Vi;simp only[GateOp.eval,List.any_map,Nat.zero_add,(show N+(w-N)=w by omega)] at Vi
     rw[S3,Vi];congr 1
     funext r
     simp only[Function.comp_apply,id_eq];by_cases b7:r < w
     · have Qm:xp gs N α r < N+wx gs (w-N):=by
        unfold xp;dsimp only;split_ifs with Sl
        · exact lt_of_lt_of_le Sl (Nat.le_add_right _ _)
        · have hrlt:yK gs N α r < w:=lt_of_le_of_lt (Wn gs N α r (by omega)) b7;have wj:=ZV gs vK N α r;rcases wj with Sl' | wv
          · exact (Sl Sl').elim
          · obtain⟨Jc,rs',pE'⟩:=_A wv
            have Vo:yK gs N α r-N < gs.length:=by have:=(mem_Ico.mp Jc).2;omega
            have Ui:(gs[yK gs N α r-N]'Vo).isLeft=true:=by have:=_k gs (Sum.inl []) Vo;change gateAt gs N (yK gs N α r)=_ at this;rw[pE'] at this;rw[← this];rfl
            have hlt_idx:=n8 gs (yK gs N α r-N) (w-N)
             (by omega) hj Ui
            omega
       simp only[b7,↓reduceIte,Qm];rw[← K9.mn];exact ih r b7 (by omega)
     · simp only[b7,↓reduceIte,Xd,ite_self]
    | inr ar=>
     rcases ar with ⟨a,r⟩
     have f3:yK gs N α w=if α a∧r < w then yK gs N α r else N:=by rw[yK,if_neg g7,_O hw,v7]
     by_cases h3:α a=true∧r < w
     · have f3':yK gs N α w=yK gs N α r:=by
        rw[f3,_O h3]
       have S3:xp gs N α w=xp gs N α r:=by simp only[xp,f3']
       rw[S3];simp only[h3.1,h3.2,and_self,↓reduceIte];rw[← K9.mn];exact ih r h3.2 (by omega)
     · have f3':yK gs N α w=N:=by
        rw[f3,if_neg h3]
       have S3:xp gs N α w=N:=by simp[xp,f3',wx]
       rw[S3];simp only[h3,↓reduceIte];exact Xd
theorem kb {N:ℕ} {G:Type*} [_5 G] (I:_0 N) [_4 I] (k:ℕ) (hk:1≤ k) (hI:∀ p q,p≠q→(pencil I p∩pencil I q).card≤1) (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (x8:∀ rs,Sum.inl rs∈gs→ rs.length≤2) (α:ℕ→ Bool) (gs':Finset G) (A:G→_3 N) (wire:G→ ℕ) (hA:∀ g∈gs',A g=vk (N:=N) gs α (wire g)) (Pr:∀ g∈gs',wire g < N+gs.length):(zg I k gs' A).card≤(2*k*k)*(vV gs N).card:=by
 classical
 let B:=y9 gs N α;have hB:Ke.good B:=fd gs N α 0 gs x8;let E:=Ke.counted B univ (pencil I)
  (Ico N (N+B.size)) k
 have fN:∀ u∈Ico N (N+B.size),∀ c∈Ke.vU (n:=N) B hB u,N≤ c→ c∈Ico N (N+B.size):=by intro u hu c hc Tx;have z5:=(Ke.wy B hB u).2.1 c hc;exact mem_Ico.mpr ⟨Tx,lt_trans z5 (mem_Ico.mp hu).2⟩
 have vR:(zg I k gs' A).image Prod.swap⊆E:=by
  intro e he;obtain⟨a,ha,rfl⟩:=mem_image.mp he;obtain⟨_,NT,g,hg,YW,⟨T,QZ,zs⟩,kp⟩:=_A ha;let w':=xp gs N α (wire g);have c1:Ke.support B w'=A g:=by ext l;rw[Ke.yF,hA g hg];change Ke.value B (λ q=>decide (q=l)) w'=true↔l∈vk (N:=N) gs α (wire g);rw[fL gs vK α _ (wire g) (Pr g hg)];unfold vk vX;rw[← K9.br gs α l (wire g)]
  have Sf:Ke.vT B univ w'=A g:=by simp only[Ke.vT,Finset.inter_univ,c1]
  have xV:2≤(Ke.support (n:=N) B w').card:=by have h1:k+1≤((A g).filter (I a.1)).card:=kp;have h2:=card_filter_le (A g) (I a.1);rw[c1];omega
  have cK':=Ke.jt B w' xV;have zj:Ke.value B (Ke.yl univ (pencil I) T) w'=false:=by
   apply Bool.eq_false_iff.mpr
   intro hv;have YU:∀ l:Fin N,Ke.yl univ (pencil I) T l=true→ l∉T.biUnion (pencil I):=by intro l hl;simp only[Ke.yl,Ke.bit,mem_sdiff,decide_eq_true_eq] at hl;exact hl.2
   have TN:∃ l∈A g,Ke.yl univ (pencil I) T l=true:=by
    have TG:∀ u,u < N+B.size→ Ke.value B (Ke.yl univ (pencil I) T) u=true→∃ l:Fin N,l∈Ke.support B u∧Ke.yl univ (pencil I) T l=true:=by
     intro u;induction u using strong_induction_on with
     | ind u iha=>
      intro hu N7;by_cases QL:u < N
      · rw[Ke.xF B _ ⟨u,QL⟩] at N7;refine⟨⟨u,QL⟩,?_,N7⟩
        rw[Ke.yF];simpa using Ke.xF B (λ q:Fin N=>decide (q=⟨u,QL⟩)) ⟨u,QL⟩
      · have Vi:=Ke.ud B
         (Ke.yl univ (pencil I) T) u (by omega) hu
        rw[N7] at Vi;have RL:B.gates[u-N]'(by unfold Circuit.size at hu;omega)∈B.gates:=List.getElem_mem _
        have kf:(B.gates[u-N]'(by unfold Circuit.size at hu;omega)).op=GateOp.or:=gJ gs N α 0 gs _ RL
        simp only[kf,GateOp.eval,List.any_map] at Vi;obtain⟨c,Oe,Z4⟩:=List.any_eq_true.mp Vi.symm;simp only[Function.comp_apply,id_eq] at Z4;split_ifs at Z4 with hcu
        obtain⟨l,g9,Uu⟩:=iha c hcu (by omega) Z4;refine⟨l,?_,Uu⟩
        rw[Ke.yF] at g9 ⊢;have Mv:=Ke.ud B (λ q=>decide (q=l)) u
         (by omega) hu
        rw[Mv];simp only[kf,GateOp.eval,List.any_map,Function.comp_apply,id_eq,List.any_eq_true];exact⟨c,Oe,by simp[hcu,g9]⟩
    obtain⟨l,g9,Uu⟩:=TG w' cK'.2 hv;rw[c1] at g9;exact⟨l,g9,Uu⟩
   obtain⟨l,KO,LU⟩:=TN;exact YU l LU (zs KO)
  have p4:(A g∩pencil I a.1)=(A g).filter (I a.1):=by ext l;simp[pencil]
  apply _B
  refine⟨_H _,?_,w',mem_Ico.mpr cK',⟨T,QZ,zj⟩,?_,?_⟩
  · simpa[pencil] using NT
  · change a.2∈Ke.vT B univ w';rw[Sf];exact YW
  · change k+1≤(Ke.vT B univ w'∩pencil I a.1).card;rw[Sf,p4];exact kp
 have Yc:Function.Injective (Prod.swap:Fin N× Fin N→ Fin N× Fin N):=by intro a b h;simpa using _9 Prod.swap h
 have xV:=_C vR;rw[_l _ Yc] at xV;refine xV.trans ?_
 have OL:=Ke.km B hB univ (pencil I)
  hI k hk (Ico N (N+B.size)) fN
 have Rn:B.size=(vV gs N).card:=q6 gs N α;simp only[Nat.card_Ico,add_sub_cancel_left] at OL;simpa[E,B,Rn] using OL
noncomputable def kv {N:ℕ} (I:_0 N) [_4 I] (k zo:ℕ) (C:_a):_2 N:=by
 classical
 let gs₀:=vh N C;let L:=vi I C;let α:=vc I C;let F₄:=v2 I C;let A₀:=zU I zo (vw gs₀ N α) (vH gs₀ L) (λ g=>vk (N:=N) gs₀ α (vu gs₀ N g)) F₄;let H₀:=zg I k (vw gs₀ N α) (λ g=>vk (N:=N) gs₀ α (vu gs₀ N g));let B₀:=cv I gs₀ α;exact F₄∪A₀∪H₀∪B₀
noncomputable abbrev v0 {N:ℕ} (I:_0 N) [_4 I] (C:_a):_2 N:=kv I 3 7 C
theorem fR {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p p' l l':Fin N,p≠p'→ l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l')) (k zo:ℕ) (hk:1≤ k) (C:_a) (hm:_b C):(kv I k zo C).card≤32*(wX C (N+N) (Ico N (N+N)) 1).card+(4*zo)*(vw (vh N C) N (vc I C)).card+(2*k*k+2)*(vV (vh N C) N).card:=by
 classical
 let gs₀:=vh N C;let L:=vi I C;let α:=vc I C;let F₄:=v2 I C;let A₀:=zU I zo (vw gs₀ N α) (vH gs₀ L) (λ g=>vk (N:=N) gs₀ α (vu gs₀ N g)) F₄;let H₀:=zg I k (vw gs₀ N α) (λ g=>vk (N:=N) gs₀ α (vu gs₀ N g));let B₀:=cv I gs₀ α;have hF:F₄.card≤32*(wX C (N+N) (Ico N (N+N)) 1).card:=fW I hI C (by
  intro g hg;obtain⟨kf,y5⟩:=hm g hg;exact⟨by simpa only[Set.mem_insert_iff,Set.mem_singleton_iff] using kf,y5⟩)
 have hA:A₀.card≤(4*zo)*(vw gs₀ N α).card:=by
  apply jZ I zo (vw gs₀ N α) (vH gs₀ L) (λ g=>vk (N:=N) gs₀ α (vu gs₀ N g)) F₄
  intro g hg l p hp wK yP;have hα:vi I C (yk gs₀ N g) (λ _=>false)=false:=jw gs₀ N α g hg;have SH:vi I C (yk gs₀ N g) (λ q=>decide (q=p))=true:=by simpa only[L,vH,mem_filter,_H,true_and] using hp
  have yP':5≤((univ.filter λ q:Fin N=>vi I C (yk gs₀ N g) (λ r=>decide (r=q))=true).filter (λ q=>I q l)).card:=by
   have cX:((vH gs₀ L g).filter (λ q=>I q l)).card≤((univ.filter λ q:Fin N=>vi I C (yk gs₀ N g) (λ r=>decide (r=q))=true).filter (λ q=>I q l)).card:=by
    apply _C
    intro q hq;obtain⟨Vu,ny⟩:=_A hq;exact _B ⟨_B ⟨_H _,by simpa only[L,vH,mem_filter,_H,true_and] using Vu⟩,ny⟩
   omega
  exact zi I C (yk gs₀ N g) (we C α g hg) hα p l wK SH yP'
 have hH:H₀.card≤(2*k*k)*(vV gs₀ N).card:=by
  apply kb I k hk (K3.jX I hI) gs₀ (ul N C) (bh N C hm) α (vw gs₀ N α) (λ g=>vk (N:=N) gs₀ α (vu gs₀ N g)) (vu gs₀ N) (λ _ _=>rfl) (λ g hg=>by have z5:=yz gs₀ (ul N C) N α g hg;have Vf:=(mem_Ico.mp (_A hg).1).2;omega)
 have hB:B₀.card≤2*(vV gs₀ N).card:=dM I hI gs₀ (ul N C) (bh N C hm) α;have h0:(kv I k zo C).card≤(F₄∪A₀∪H₀∪B₀).card:=le_rfl;have h1:=_J (F₄∪A₀∪H₀) B₀;have h2:=_J (F₄∪A₀) H₀;have h3:=_J F₄ A₀;nlinarith
theorem gZ {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p p' l l':Fin N,p≠p'→ l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l')) (C:_a) (hm:_b C):(v0 I C).card≤32*(wX C (N+N) (Ico N (N+N)) 1).card+28*(vw (vh N C) N (vc I C)).card+20*(vV (vh N C) N).card:=by simpa using fR I hI 3 7 (by omega) C hm
private def uF:vg→ Bool
 | Sum.inl _=>true
 | Sum.inr _=>false
private lemma uh (gs hs:List vg) (N w:ℕ) (hn:N≤ w) (hw:w < N+gs.length):gateAt (gs ++ hs) N w=gateAt gs N w:=by
 unfold gateAt;have hj:w-N < gs.length:=by omega
 have KN:w-N < (gs ++ hs).length:=by simp;omega
 rw[_k _ _ KN,_k _ _ hj,List.getElem_append_left hj]
private lemma pG (gs:List vg) (N:ℕ):(vV gs N).card≤ gs.countP uF:=by
 classical
 induction gs using List.reverseRecOn with
 | nil=>simp[vV]
 | append_singleton gs x ih=>
  have vR:vV (gs ++ [x]) N⊆vV gs N∪(if uF x then {N+gs.length} else ∅):=by
   intro w hw;obtain⟨Z9,rs,v7⟩:=_A hw;obtain⟨g7,kJ⟩:=mem_Ico.mp Z9;simp only[_c,_d] at kJ;by_cases z5:w < N+gs.length
   · apply _D
     rw[uh gs [x] N w g7 z5] at v7;exact _B ⟨mem_Ico.mpr ⟨g7,z5⟩,rs,v7⟩
   · have zD:w=N+gs.length:=by omega
     subst zD;have KP:gateAt (gs ++ [x]) N (N+gs.length)=x:=by
      unfold gateAt;have bA:N+gs.length-N=gs.length:=by omega
      rw[bA,_k _ _ (by simp),List.getElem_append_right (le_refl _)];simp
     rw[KP] at v7;have hx:uF x=true:=by simp[v7,uF]
     apply _G
     simp[hx]
  have Vh:=_C vR;have Sn:=_J (vV gs N) (if uF x then {N+gs.length} else ∅);have KA:(if uF x then ({N+gs.length}:Finset ℕ) else ∅).card=if uF x then 1 else 0:=by split_ifs <;> simp
  have hcnt:(gs ++ [x]).countP uF=gs.countP uF+if uF x then 1 else 0:=by rw[List.countP_append];cases x <;> simp[uF,List.countP_cons]
  omega
private lemma mD (N:ℕ) (C:_a):(vh N C).countP uF≤1+M1.vA N 1 C.gates+M1.vA N 2 C.gates:=by
 have UO:∀(s:M1.State) (g:Gate),(M1.yx N (N+N+C.size) s g).countP uF≤(if g.lineDegree (M1.degrees s)=1 then 1 else 0)+(if g.lineDegree (M1.degrees s)=2 then 1 else 0):=by
  intro s g;unfold M1.yx;dsimp only;split_ifs
  all_goals try split
  all_goals try split_ifs
  all_goals simp_all [uF,Gate.lineDegree,List.countP_cons,List.countP_nil]
 have Op:∀(gs:List Gate) (s:M1.State),(M1.net (gs.foldl (M1.ya N (N+N+C.size)) s)).countP uF≤(M1.net s).countP uF+M1.vQ 1 (M1.degrees s) gs+M1.vQ 2 (M1.degrees s) gs:=by
  intro gs;induction gs with
  | nil=>intro s;simp[M1.vQ]
  | cons g gs ih=>
   intro s;have h:=ih (M1.ya N (N+N+C.size) s g);rw[M1.zG,List.countP_append,M1.yC] at h;have hp:=UO s g;simp only[foldl_cons,M1.vQ];omega
 have f3:=Op C.gates (M1.vC N);change (vh N C).countP uF≤([Sum.inl []]:List vg).countP uF+M1.vA N 1 C.gates+M1.vA N 2 C.gates at f3;have PR:([Sum.inl []]:List vg).countP uF=1:=rfl;omega
theorem kN (N Jn:ℕ) (I:_0 N) [_4 I] (Ckt:_a) (fa fb:Fin Jn→ ℕ) (hI:∀ p p' l l':Fin N,p≠p'→ l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l')) (hm:_b Ckt) (qZ:∀ jd,(Ckt.lineDegrees (N+N) (Ico N (N+N))).getD (fa jd) 0≤2) (gP:∀ jd,(Ckt.lineDegrees (N+N) (Ico N (N+N))).getD (fb jd) 0≤2) (vM:∀(jb:Fin Jn) (zz:Fin (N+N)→ Bool),(Ckt.wires (ofFn zz)).getD (fa jb) false=true→(Ckt.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (E:_2 N) (hE:∀ e∈E,I e.1 e.2∧∃ j:Fin Jn,(Ckt.wires (ofFn (M1.yd e.1 e.2))).getD (fa j) false=true∧(Ckt.wires (ofFn (M1.yG e.1))).getD (fa j) false=false∧(run (vh N Ckt)
 (M1.vy N Ckt (ofFn (λ q=>decide (q=e.1))))
 (ofFn (λ u=>decide (u=e.2)))).getD (vr N Ckt (fb j)) false=true):
 (E\v0 I Ckt).card≤26*(vV (vh N Ckt) N).card+56*(M1.vA N 2 Ckt.gates-(vI N Ckt).card)+55*Jn:=by
 classical
 have qZ':∀ j,yS N Ckt (fa j)≤2:=λ j=>qZ j;have gP':∀ j,yS N Ckt (fb j)≤2:=λ j=>gP j;let gs₀:=vh N Ckt;let gs₁:=net N Ckt fa fb;obtain⟨hs,hgs₁⟩:=K5.jf N (vn N Ckt fa fb) (k6 N Ckt) (jC N Ckt) (uJ N Ckt) (M0.vC N gs₀);change gs₁=gs₀ ++ hs at hgs₁;let L:=vi I Ckt;let α:=vc I Ckt;let F₄:=v2 I Ckt;let A₀:=zU I 7 (vw gs₀ N α) (vH gs₀ L) (λ g=>vk (N:=N) gs₀ α (vu gs₀ N g)) F₄;let B₀:=cv I gs₀ α;let kh:=wg I (vw gs₁ N α \ vw gs₀ N α)
  (vH gs₁ L) (λ g=>vk (N:=N) gs₁ α (vu gs₁ N g)) F₄
 let H₁:=zg I 2 (vw gs₁ N α) (λ g=>vk (N:=N) gs₁ α (vu gs₁ N g));let qH:=cv I gs₁ α \ B₀;let R:=(E\v0 I Ckt)\(kh∪H₁∪qH);have hhead₁:gs₁.head?=some (Sum.inl []):=VA N Ckt fa fb;have hfan₁:∀ rs,Sum.inl rs∈gs₁→ rs.length≤2:=ZS N Ckt fa fb hm;have hAdiff:kh.card≤16*(vw gs₁ N α \ vw gs₀ N α).card:=by
  have zD:kh=zU I 4 (vw gs₁ N α \ vw gs₀ N α) (vH gs₁ L) (λ g=>vk (N:=N) gs₁ α (vu gs₁ N g)) F₄:=by ext e;simp only[kh,wg,zU,mem_filter,_H,true_and]
  rw[zD];apply jZ I 4 (vw gs₁ N α \ vw gs₀ N α) (vH gs₁ L) (λ g=>vk (N:=N) gs₁ α (vu gs₁ N g)) F₄
  intro g hg l p hp wK yP;have hα:vi I Ckt (yk gs₁ N g) (λ _=>false)=false:=jw gs₁ N α g (_M hg).1;have SH:vi I Ckt (yk gs₁ N g) (λ q=>decide (q=p))=true:=by simpa only[L,vH,mem_filter,_H,true_and] using hp
  have yP':5≤((univ.filter λ q:Fin N=>vi I Ckt (yk gs₁ N g) (λ r=>decide (r=q))=true).filter (λ q=>I q l)).card:=by
   have cX:((vH gs₁ L g).filter (λ q=>I q l)).card≤((univ.filter λ q:Fin N=>vi I Ckt (yk gs₁ N g) (λ r=>decide (r=q))=true).filter (λ q=>I q l)).card:=by
    apply _C
    intro q hq;obtain⟨Vu,ny⟩:=_A hq;exact _B ⟨_B ⟨_H _,by simpa only[L,vH,mem_filter,_H,true_and] using Vu⟩,ny⟩
   omega
  exact zi I Ckt (yk gs₁ N g) (wG Ckt fa fb α g (_M hg).1) hα p l wK SH yP'
 have hH₁:H₁.card≤8*(vV gs₁ N).card:=by
  simpa using kb I 2 (by omega) (K3.jX I hI) gs₁ hhead₁ hfan₁ α (vw gs₁ N α) (λ g=>vk (N:=N) gs₁ α (vu gs₁ N g)) (vu gs₁ N) (λ _ _=>rfl) (λ g hg=>by have z5:=yz gs₁ hhead₁ N α g hg;have Vf:=(mem_Ico.mp (_A hg).1).2;omega)
 have hBdiff:qH.card≤2*hs.length:=by simpa only[qH,B₀,hgs₁] using gB I hI gs₀ hs (ul N Ckt) (by simpa only[← hgs₁] using hfan₁) α
 have hαL:∀ a x,α a=true→ L a x=true:=by intro a x ha;exact xr I (Z Ckt) (w4 Ckt hm) a (λ _=>false) x (λ _ h=>by cases h) ha
 have hA₀_sub:wg I (vw gs₁ N α) (vH gs₁ L) (λ g=>vk (N:=N) gs₁ α (vu gs₁ N g)) F₄⊆A₀∪kh:=by
  intro e he;obtain⟨_,QH,OZ,g,hg,hp,hl,xz⟩:=_A he;by_cases hg₀:g∈vw gs₀ N α
  · apply _D
    have UD:=(_A hg₀).1;obtain⟨Zd,Vf⟩:=mem_Ico.mp UD;have QD:vH gs₁ L g=vH gs₀ L g:=by simpa only[← hgs₁] using Yx gs₀ hs L g Zd Vf
    have Zc:vk (N:=N) gs₁ α (vu gs₁ N g)=vk (N:=N) gs₀ α (vu gs₀ N g):=by simpa only[← hgs₁] using fX gs₀ hs (ul N Ckt) α g hg₀
    refine _B ⟨_H _,QH,OZ,g,hg₀,?_,?_,?_⟩
    · simpa only[QD] using hp
    · simpa only[Zc] using hl
    · change (vk (N:=N) gs₀ α (vu gs₀ N g)).card≤7;rw[← Zc];exact xz.trans (by omega)
  · apply _G
    exact _B ⟨_H _,QH,OZ,g,_V ⟨hg,hg₀⟩,hp,hl,xz⟩
 have hH₁_eq:H₁=xk I (vw gs₁ N α) (λ g=>vk (N:=N) gs₁ α (vu gs₁ N g)):=by ext e;simp only[H₁,zg,xk,vx,z8];rfl
 have hr:∀ e∈R,e∈E∧e∉F₄∧e∉wg I (vw gs₁ N α) (vH gs₁ L) (λ g=>vk (N:=N) gs₁ α (vu gs₁ N g)) F₄∧e∉xk I (vw gs₁ N α) (λ g=>vk (N:=N) gs₁ α (vu gs₁ N g))∧e∉cv I gs₁ α:=by
  intro e he;have Sp:=_M he;have O7:=_M Sp.1;have bo:=O7.2;have hF:e∉F₄:=λ h=>bo (_D _ (_D _ (_D _ h)));have KC:e∉A₀:=λ h=>bo (_D _ (_D _ (_G _ h)));have Kw:e∉B₀:=λ h=>bo (_G _ h);have b1:=Sp.2;have Kk:e∉kh:=λ h=>b1 (_D _ (_D _ h));have hH:e∉H₁:=λ h=>b1 (_D _ (_G _ h));have L6:e∉qH:=λ h=>b1 (_G _ h);refine⟨O7.1,hF,?_,by rwa[← hH₁_eq],?_⟩
  · intro h;rcases mem_union.mp (hA₀_sub h) with YL | had
    · exact KC YL
    · exact Kk had
  · intro hb;exact L6 (_V ⟨hb,Kw⟩)
 have YX:∀ j X Y,(∀ i,kQ I Ckt gs₁ (ye N Ckt fa fb j i) X Y=true)→∃ p∈X,∃ l∈Y,I p l:=by
  intro j X Y hf;have NY:=nq I gs₁ (Z Ckt) (w4 Ckt hm)
   (ye N Ckt fa fb j 0) (ye N Ckt fa fb j 1) (ye N Ckt fa fb j 2)
   (λ x y h0 h1 h2=>by
    have OQ:(λ a=>Z Ckt a x)=M1.vy N Ckt (ofFn x):=funext λ a=>q8 Ckt x a;rw[OQ] at h0 h1 h2;exact j4 N I Ckt fa fb hm qZ' gP' vM x y j (λ i=>by
     fin_cases i
     · exact h0
     · exact h1
     · exact h2))
  obtain⟨p,l,bd,hp,hl⟩:=NY (λ p=>decide (p∈X)) (λ l=>decide (l∈Y)) (hf 0) (hf 1) (hf 2);exact⟨p,_o hp,l,_o hl,bd⟩
 have hR:R.card≤18*((wW gs₁ N α).filter λ g=>2≤(vU gs₁ N g).card).card+27*(k5 N Ckt fa fb).length:=by
  have Qo:∀ l u:Fin N,l≠u→(univ.filter (λ p=>I p l)∩univ.filter (λ p=>I p u)).card≤1:=by intro l u XA;by_contra! hgt;obtain⟨p₁,hp₁,p₂,hp₂,xR⟩:=_Z hgt;simp only[mem_inter,mem_filter,_H,true_and] at hp₁ hp₂;exact hI p₁ p₂ l u xR XA ⟨hp₁.1,hp₁.2,hp₂.1,hp₂.2⟩
  apply m3 I hI Qo (yT I gs₁ α L) (wW gs₁ N α) (vw gs₁ N α) (vU gs₁ N) (vH gs₁ L) (λ g=>vk (N:=N) gs₁ α (vu gs₁ N g)) (vk (N:=N) gs₁ α) (v9 gs₁ L) (dt gs₁ N α hfan₁) (yV gs₁ hhead₁ N α) (λ g hg=>by
   ext p;simpa[mem_biUnion] using jl I gs₁ hhead₁ α L g hg p)
   (by
    intro g hg xR;by_contra x9;have wv:g∉wW gs₁ N α:=hg;have x1:g∉vw gs₁ N α:=by intro hl;exact x9 ⟨hl,λ p hp=>((uf I gs₁ hhead₁ α L g hl p).mp hp).1⟩
    rw[j9 I gs₁ α L g wv x1] at xR;exact Finset.not_nonempty_empty xR)
   (λ r p hp=>k3 I gs₁ hhead₁ α L hαL r p hp)
   (kQ I Ckt gs₁) (gr N I Ckt hm gs₁)
   (fT I Ckt gs₁) (Zf I Ckt gs₁)
   (ye N Ckt fa fb) YX R
  · intro e he;obtain⟨RW,QH,N8,MV,L4⟩:=hr e he;obtain⟨OJ,j,ha,d3,jn⟩:=hE e RW
    have zu:∃ k,∀ i,e.2∈v9 gs₁ L (ye N Ckt fa fb k i) e.1:=by
     obtain⟨k,hk⟩:=qJ N Ckt fa fb hm qZ' e.1 e.2 j ha d3 jn;refine⟨k,λ i=>?_⟩
     have KB:=hk i;have OQ:∀ a,M1.vy N Ckt (ofFn λ q=>decide (q=e.1)) a=true→ L a (λ q=>decide (q=e.1))=true:=by
      intro a ha;apply uO
      rwa[q8]
     have qk':(run gs₁ (λ a=>L a λ q=>decide (q=e.1)) (ofFn λ t=>decide (t=e.2))).getD (ye N Ckt fa fb k i) false=true:=ze gs₁ _ _ OQ _ _ (λ _ h=>h) (ye N Ckt fa fb k i) KB;exact (y4 gs₁ _ e.2 (ye N Ckt fa fb k i)).mp qk'
    refine K8.nn I (vw gs₁ N α) (vH gs₁ L) (λ g=>vk (N:=N) gs₁ α (vu gs₁ N g)) (vk (N:=N) gs₁ α) (v9 gs₁ L) (ye N Ckt fa fb) F₄ (cv I gs₁ α) (zm gs₁ α L hαL) (pH gs₁ hhead₁ α L hαL) (λ r p l h2 wK hl=>by
     by_cases Sl:r < N
     · have:=zR gs₁ α r Sl;omega
     · by_cases hrb:r < N+gs₁.length
       · exact _B ⟨_H _,r,mem_Ico.mpr ⟨by omega,hrb⟩,h2,wK,hl⟩
       · have:=wV (N:=N) gs₁ α r (by omega);change vk (N:=N) gs₁ α r=∅ at this;rw[this] at h2;simp at h2)
     (λ j p u hu v hv w hw=>K8.YT I (ye N Ckt fa fb) (kQ I Ckt gs₁) (gr N I Ckt hm gs₁) YX (v9 gs₁ L) (fT I Ckt gs₁) j p u v w hu hv hw)
     e.1 e.2 OJ zu QH N8 MV L4
  · intro e he r Px Ru;obtain⟨RW,_,N8,MV,_⟩:=hr e he;exact xB I gs₁ hhead₁ α L hαL F₄ e.1 e.2 (hE e RW).1 (hr e he).2.1 N8 MV r Px Ru
  · intro e he g hg hp;obtain⟨RW,QH,_,_,_⟩:=hr e he;by_contra! hc;have hα:vi I Ckt (yk gs₁ N g) (λ _=>false)=false:=jw gs₁ N α g hg
    have h5:5≤((univ.filter λ q:Fin N=>vi I Ckt (yk gs₁ N g) (λ r=>decide (r=q))=true).filter (λ q=>I q e.2)).card:=by
     have cX:((vH gs₁ L g).filter (λ q=>I q e.2)).card≤((univ.filter λ q:Fin N=>vi I Ckt (yk gs₁ N g) (λ r=>decide (r=q))=true).filter (λ q=>I q e.2)).card:=by
      apply _C
      intro q hq;obtain⟨Vu,ny⟩:=_A hq;exact _B ⟨_B ⟨_H _,by simpa only[L,vH,mem_filter,_H,true_and] using Vu⟩,ny⟩
     omega
    have SH:vi I Ckt (yk gs₁ N g) (λ q=>decide (q=e.1))=true:=by simpa only[L,vH,mem_filter,_H,true_and] using hp
    exact QH (zi I Ckt (yk gs₁ N g) (wG Ckt fa fb α g hg) hα e.1 e.2 (hE e RW).1 SH h5)
 have VS:E\v0 I Ckt⊆kh∪H₁∪qH∪R:=by
  intro e he;by_cases yH:e∈kh∪H₁∪qH
  · exact _D _ yH
  · exact _G _ (_V ⟨he,yH⟩)
 have T7:=_C VS;have Xt:=_J (kh∪H₁∪qH) R;have Y9:=_J (kh∪H₁) qH;have LF:=_J kh H₁;have hor_two:((wW gs₁ N α).filter λ g=>2≤(vU gs₁ N g).card).card≤(vV gs₁ N).card:=_C (jL gs₁ N α);have X8:Disjoint (vw gs₁ N α \ vw gs₀ N α) (vV gs₁ N\vV gs₀ N):=by
  apply disjoint_left.mpr
  intro g PG OD;exact disjoint_left.mp (wl gs₁ N α) (jQ gs₁ N α (_M OD).1) (_M PG).1
 have W6:(vw gs₁ N α \ vw gs₀ N α)∪(vV gs₁ N\vV gs₀ N)⊆Ico (N+gs₀.length) (N+gs₁.length):=by
  intro g hg;rcases mem_union.mp hg with PG | OD
  · obtain⟨Ly,QR⟩:=_M PG;obtain⟨UD,x1⟩:=_A Ly;obtain⟨Zd,Vf⟩:=mem_Ico.mp UD;refine mem_Ico.mpr ⟨?_,Vf⟩
    by_contra! z5;apply QR
    have x1':wE α (gateAt gs₀ N g):=by rw[hgs₁,uh gs₀ hs N g Zd z5] at x1;exact x1
    exact _B ⟨mem_Ico.mpr ⟨Zd,z5⟩,x1'⟩
  · obtain⟨Ly,QR⟩:=_M OD;obtain⟨UD,rs,pE⟩:=_A Ly;obtain⟨Zd,Vf⟩:=mem_Ico.mp UD;refine mem_Ico.mpr ⟨?_,Vf⟩
    by_contra! z5;apply QR
    rw[hgs₁,uh gs₀ hs N g Zd z5] at pE;exact _B ⟨mem_Ico.mpr ⟨Zd,z5⟩,rs,pE⟩
 have hpart1:(vw gs₁ N α \ vw gs₀ N α).card+(vV gs₁ N\vV gs₀ N).card≤ hs.length:=by
  rw[← card_union_of_disjoint X8];have xV:=_C W6;have y5:gs₁.length=gs₀.length+hs.length:=by simp[hgs₁]
  simp only[Nat.card_Ico] at xV;omega
 have hor1_split:(vV gs₁ N).card≤(vV gs₀ N).card+(vV gs₁ N\vV gs₀ N).card:=by
  have vR:vV gs₁ N⊆vV gs₀ N∪(vV gs₁ N\vV gs₀ N):=by
   intro g hg;by_cases QR:g∈vV gs₀ N
   · exact _D _ QR
   · exact _G _ (_V ⟨hg,QR⟩)
  exact (_C vR).trans (_J _ _)
 have hrev:gs₁.length+(yh N Ckt fa fb).card≤ gs₀.length+Jn+2*(M1.vA N 2 Ckt.gates-(vI N Ckt).card):=by
  have hr:=M5.bi N Ckt (vn N Ckt fa fb)
   (M0.vC N (vh N Ckt)) (λ g hg=>(hm g hg).2)
  change gs₁.length+(yh N Ckt fa fb).card≤ gs₀.length+(vn N Ckt fa fb).length+2*((Mc.vP N Ckt).card-(vI N Ckt).card) at hr;rwa[xD N Ckt,Yd] at hr
 have Pq:(k5 N Ckt fa fb).length=Jn+(yh N Ckt fa fb).card:=YK N Ckt fa fb;have hgs0_eq:(vV gs₀ N).card=(vV (vh N Ckt) N).card:=rfl;have h1:(E\v0 I Ckt).card≤ kh.card+H₁.card+qH.card+R.card:=by omega
 have h2:kh.card+H₁.card+qH.card+R.card≤16*(vw gs₁ N α \ vw gs₀ N α).card+26*(vV gs₁ N).card+2*hs.length+27*(k5 N Ckt fa fb).length:=by omega
 have h3:16*(vw gs₁ N α \ vw gs₀ N α).card+26*(vV gs₁ N).card+2*hs.length≤26*(vV (vh N Ckt) N).card+28*hs.length:=by omega
 have h4:28*hs.length+27*(k5 N Ckt fa fb).length≤56*(M1.vA N 2 Ckt.gates-(vI N Ckt).card)+55*Jn:=by
  have y5:gs₁.length=gs₀.length+hs.length:=by simp[hgs₁]
  omega
 omega
theorem nB (N Jn:ℕ) (I:_0 N) [_4 I] (Ckt:_a) (fa fb:Fin Jn→ ℕ) (hI:∀ p p' l l':Fin N,p≠p'→ l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l')) (hm:_b Ckt) (qZ:∀ jd,(Ckt.lineDegrees (N+N) (Ico N (N+N))).getD (fa jd) 0≤2) (gP:∀ jd,(Ckt.lineDegrees (N+N) (Ico N (N+N))).getD (fb jd) 0≤2) (vM:∀(jb:Fin Jn) (zz:Fin (N+N)→ Bool),(Ckt.wires (ofFn zz)).getD (fa jb) false=true→(Ckt.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (E:_2 N) (hE:∀ e∈E,I e.1 e.2∧∃ j:Fin Jn,(Ckt.wires (ofFn (M1.yd e.1 e.2))).getD (fb j) false=true∧(Ckt.wires (ofFn (M1.yG e.1))).getD (fb j) false=false∧(run (vh N Ckt)
 (M1.vy N Ckt (ofFn (λ q=>decide (q=e.1))))
 (ofFn (λ u=>decide (u=e.2)))).getD (vr N Ckt (fa j)) false=true):
 (E\v0 I Ckt).card≤26*(vV (vh N Ckt) N).card+56*(M1.vA N 2 Ckt.gates-(vI N Ckt).card)+55*Jn:=kN N Jn I Ckt fb fa hI hm gP qZ
 (λ jb zz hb ha=>vM jb zz ha hb) E hE
theorem qK (N Jn:ℕ) (I:_0 N) [_4 I] (Ckt:_a) (fa fb:Fin Jn→ ℕ) (hI:∀ p p' l l':Fin N,p≠p'→ l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l')) (hm:_b Ckt) (qZ:∀ jd,(Ckt.lineDegrees (N+N) (Ico N (N+N))).getD (fa jd) 0≤2) (gP:∀ jd,(Ckt.lineDegrees (N+N) (Ico N (N+N))).getD (fb jd) 0≤2) (vM:∀(jb:Fin Jn) (zz:Fin (N+N)→ Bool),(Ckt.wires (ofFn zz)).getD (fa jb) false=true→(Ckt.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (E₁ E₂:_2 N) (hE₁:∀ e∈E₁,I e.1 e.2∧∃ j:Fin Jn,(Ckt.wires (ofFn (M1.yd e.1 e.2))).getD (fa j) false=true∧(Ckt.wires (ofFn (M1.yG e.1))).getD (fa j) false=false∧(run (vh N Ckt)
 (M1.vy N Ckt (ofFn (λ q=>decide (q=e.1))))
 (ofFn (λ u=>decide (u=e.2)))).getD (vr N Ckt (fb j)) false=true)
 (hE₂:∀ e∈E₂,I e.1 e.2∧∃ j:Fin Jn,(Ckt.wires (ofFn (M1.yd e.1 e.2))).getD (fb j) false=true∧(Ckt.wires (ofFn (M1.yG e.1))).getD (fb j) false=false∧(run (vh N Ckt) (M1.vy N Ckt (ofFn (λ q=>decide (q=e.1)))) (ofFn (λ u=>decide (u=e.2)))).getD (vr N Ckt (fa j)) false=true):
 (v0 I Ckt∪E₁∪E₂).card≤32*M1.vA N 0 Ckt.gates+104*M1.vA N 1 Ckt.gates+128*(vI N Ckt).card+184*(M1.vA N 2 Ckt.gates-(vI N Ckt).card)+110*Jn+72:=by
 classical
 have zu:v0 I Ckt∪E₁∪E₂⊆v0 I Ckt∪(E₁ \ v0 I Ckt)∪(E₂ \ v0 I Ckt):=by
  intro e he;rcases mem_union.mp he with Sp | O7
  · rcases mem_union.mp Sp with hB | Sp'
    · exact _D _ (_D _ hB)
    · by_cases hB:e∈v0 I Ckt
      · exact _D _ (_D _ hB)
      · exact _D _ (_G _ (_V ⟨Sp',hB⟩))
  · by_cases hB:e∈v0 I Ckt
    · exact _D _ (_D _ hB)
    · exact _G _ (_V ⟨O7,hB⟩)
 have hc:=_C zu;have Xt:=_J
  (v0 I Ckt∪(E₁ \ v0 I Ckt)) (E₂ \ v0 I Ckt)
 have Y9:=_J (v0 I Ckt) (E₁ \ v0 I Ckt);have hB:=gZ I hI Ckt hm;have h1:=kN N Jn I Ckt fa fb hI hm qZ gP vM E₁ hE₁;have h2:=nB N Jn I Ckt fa fb hI hm qZ gP vM E₂ hE₂;have Oh:(wX Ckt (N+N) (Ico N (N+N)) 1).card=M1.vA N 0 Ckt.gates+M1.vA N 1 Ckt.gates:=by rw[M1.uP];rfl
 have fl:Disjoint (vw (vh N Ckt) N (vc I Ckt)) (vV (vh N Ckt) N):=by
  apply disjoint_left.mpr
  intro g PG OD;exact disjoint_left.mp (wl (vh N Ckt) N (vc I Ckt)) (jQ (vh N Ckt) N (vc I Ckt) OD) PG
 have bZ:vw (vh N Ckt) N (vc I Ckt)∪vV (vh N Ckt) N⊆Ico N (N+(vh N Ckt).length):=by
  intro g hg;rcases mem_union.mp hg with hL | hO
  · exact (_A hL).1
  · exact (_A hO).1
 have Xb:(vw (vh N Ckt) N (vc I Ckt)).card+(vV (vh N Ckt) N).card≤(vh N Ckt).length:=by rw[← card_union_of_disjoint fl];exact (_C bZ).trans (by simp)
 have Se:(vh N Ckt).length≤1+M1.vA N 1 Ckt.gates+M1.vA N 2 Ckt.gates+2*(vI N Ckt).card:=by have Vr:=M1.x7 N (N+N+Ckt.size) Ckt.gates;rw[← wH N Ckt] at Vr;exact Vr
 have hor_inl_le:(vV (vh N Ckt) N).card≤1+M1.vA N 1 Ckt.gates+M1.vA N 2 Ckt.gates:=(pG (vh N Ckt) N).trans (mD N Ckt);have hfk:(vI N Ckt).card≤ M1.vA N 2 Ckt.gates:=by have Md:=M1.q5 N Ckt.gates;rwa[← wH N Ckt] at Md
 have Yy:(v0 I Ckt∪E₁∪E₂).card≤(v0 I Ckt).card+(E₁ \ v0 I Ckt).card+(E₂ \ v0 I Ckt).card:=by omega
 have hL0:28*(vw (vh N Ckt) N (vc I Ckt)).card+28*(vV (vh N Ckt) N).card≤28*(vh N Ckt).length:=by omega
 have hlen0:28*(vh N Ckt).length≤28+28*M1.vA N 1 Ckt.gates+28*M1.vA N 2 Ckt.gates+56*(vI N Ckt).card:=by omega
 have hor44:44*(vV (vh N Ckt) N).card≤44+44*M1.vA N 1 Ckt.gates+44*M1.vA N 2 Ckt.gates:=by omega
 omega
end OrInlTightAndBase37
section E3RetainedAndWeapons
open Ma
open M2 Kd
open M1 Kb
open Kc K7
open K1
open Classical in
noncomputable def zw {N:ℕ} (I:_0 N) [_4 I] (k zo:ℕ) (gs:List vg) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool):ℕ→_3 N
 | w=>
  if _hw:w∈wW gs N α then (vU gs N w).biUnion λ c=>if _hc:c < w then zw I k zo gs α L c else ∅
  else if _hl:w∈vw gs N α then if _hc:vu gs N w < w then (vH gs L w).filter λ p=>p∈zw I k zo gs α L (vu gs N w)∨jO I k zo (vk (N:=N) gs α (vu gs N w)) p else ∅
  else ∅
termination_by w=>w
lemma ko {N:ℕ} (I:_0 N) [_4 I] (k zo:ℕ) (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (w:ℕ) (hw:w∈wW gs N α) (p:Fin N):p∈zw I k zo gs α L w↔∃ c∈vU gs N w,p∈zw I k zo gs α L c:=by
 classical
 rw[zw,_Q hw,mem_biUnion];constructor
 · rintro⟨c,hc,gn⟩;rw[_Q (yV gs vK N α w hw c hc)] at gn;exact⟨c,hc,gn⟩
 · rintro⟨c,hc,gn⟩;refine⟨c,hc,?_⟩
   rw[_Q (yV gs vK N α w hw c hc)];exact gn
lemma cq {N:ℕ} (I:_0 N) [_4 I] (k zo:ℕ) (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (w:ℕ) (hw:w∈wW gs N α):zw I k zo gs α L w=(vU gs N w).biUnion (zw I k zo gs α L):=by ext p;rw[ko I k zo gs vK α L w hw p,mem_biUnion]
lemma wJ {N:ℕ} (I:_0 N) [_4 I] (k zo:ℕ) (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (w:ℕ) (hw:w∈vw gs N α) (p:Fin N):p∈zw I k zo gs α L w↔p∈vH gs L w∧(p∈zw I k zo gs α L (vu gs N w)∨jO I k zo (vk (N:=N) gs α (vu gs N w)) p):=by
 classical
 have wv:w∉wW gs N α:=λ ho=>disjoint_left.mp (wl gs N α) ho hw;have z5:vu gs N w < w:=yz gs vK N α w hw;rw[zw,dif_neg wv,_Q hw,_Q z5,mem_filter]
lemma jm {N:ℕ} (I:_0 N) [_4 I] (k zo:ℕ) (gs:List vg) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (w:ℕ) (wv:w∉wW gs N α) (x1:w∉vw gs N α):zw I k zo gs α L w=∅:=by rw[zw,dif_neg wv,dif_neg x1]
theorem dC {N:ℕ} (I:_0 N) [_4 I] (k zo:ℕ) (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (hα:∀ a x,α a=true→ L a x=true) (i:ℕ) (p:Fin N) (hp:p∈zw I k zo gs α L i):∃ g∈vw gs N α,p∈vH gs L g∧jO I k zo (vk (N:=N) gs α (vu gs N g)) p∧vk (N:=N) gs α (vu gs N g)⊆v9 gs L i p:=by
 induction i using strong_induction_on with
 | ind i ih=>
  by_cases wv:i∈wW gs N α
  · obtain⟨c,hc,gn⟩:=(ko I k zo gs vK α L i wv p).mp hp;obtain⟨g,hg,z1,xS,vR⟩:=ih c (yV gs vK N α i wv c hc) gn;refine⟨g,hg,z1,xS,?_⟩
    intro l hl;exact (jK gs vK α L hα i wv p l).mpr ⟨c,hc,vR hl⟩
  · by_cases x1:i∈vw gs N α
    · obtain⟨z1,UF | xS⟩:=(wJ I k zo gs vK α L i x1 p).mp hp
      · obtain⟨g,hg,V4,xS,vR⟩:=ih (vu gs N i) (yz gs vK N α i x1) UF;refine⟨g,hg,V4,xS,?_⟩
        intro l hl;exact (xW gs vK α L i x1 p l).mpr ⟨z1,vR hl⟩
      · refine⟨i,x1,z1,xS,?_⟩
        intro l hl;exact (xW gs vK α L i x1 p l).mpr ⟨z1,zm gs α L hα (vu gs N i) p hl⟩
    · rw[jm I k zo gs α L i wv x1] at hp;exact (notMem_empty _ hp).elim
theorem m4 {N:ℕ} (I:_0 N) [_4 I] (k zo:ℕ) (gs:List vg) (vK:gs.head?=some (Sum.inl [])) (α:ℕ→ Bool) (L:ℕ→(Fin N→ Bool)→ Bool) (hα:∀ a x,α a=true→ L a x=true) (E:_2 N) (p l:Fin N) (hI:I p l) (hE:(p,l)∉E) (xz:(p,l)∉zU I zo (vw gs N α) (vH gs L) (λ g=>vk (N:=N) gs α (vu gs N g)) E) (bX:(p,l)∉zg I k (vw gs N α) (λ g=>vk (N:=N) gs α (vu gs N g))) (i:ℕ) (hl:l∈v9 gs L i p) (yi:l∉vk (N:=N) gs α i):p∈zw I k zo gs α L i:=by
 induction i using strong_induction_on with
 | ind i ih=>
  by_cases wv:i∈wW gs N α
  · obtain⟨c,hc,cI⟩:=(jK gs vK α L hα i wv p l).mp hl;have WP:l∉vk (N:=N) gs α c:=λ h=>yi ((xg gs vK α i wv l).mpr ⟨c,hc,h⟩);exact (ko I k zo gs vK α L i wv p).mpr ⟨c,hc,ih c (yV gs vK N α i wv c hc) cI WP⟩
  · by_cases x1:i∈vw gs N α
    · obtain⟨z1,cI⟩:=(xW gs vK α L i x1 p l).mp hl;refine (wJ I k zo gs vK α L i x1 p).mpr ⟨z1,?_⟩
      by_cases WP:l∈vk (N:=N) gs α (vu gs N i)
      · right
        exact q2 I k zo (vw gs N α) (vH gs L) (λ g=>vk (N:=N) gs α (vu gs N g)) E p l i x1 z1 WP hI hE xz bX
      · left
        exact ih (vu gs N i) (yz gs vK N α i x1) cI WP
    · rw[qN gs α L i wv x1 p] at hl;exact (yi hl).elim
noncomputable def kD {N:ℕ} (I:_0 N) [_4 I] (C:_a):ℕ→_3 N:=zw I 3 7 (vh N C) (vc I C) (vi I C)
lemma j6 {N:ℕ} (I:_0 N) (C:_a) (hm:_b C):xZ (vi I C):=xr I (Z C) (w4 C hm)
lemma xN {N:ℕ} (I:_0 N) (C:_a) (hm:_b C) (a:ℕ) (x:Fin N→ Bool) (ha:vc I C a=true):vi I C a x=true:=j6 I C hm a (λ _=>false) x (λ _ h=>by cases h) ha
lemma mC {N:ℕ} (I:_0 N) [_4 I] (C:_a) (hm:_b C) (i:ℕ) (p:Fin N) (hp:p∈kD I C i):∃ g∈vw (vh N C) N (vc I C),p∈vH (vh N C) (vi I C) g∧jO I 3 7 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)) p∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) i p:=dC I 3 7 (vh N C) (ul N C) (vc I C) (vi I C) (xN I C hm) i p hp
lemma kR {N:ℕ} (I:_0 N) [_4 I] (C:_a) (hm:_b C) (p l:Fin N) (hI:I p l) (Y8:(p,l)∉v0 I C) (i:ℕ) (hl:l∈v9 (vh N C) (vi I C) i p) (yi:l∉vk (N:=N) (vh N C) (vc I C) i):p∈kD I C i:=by
 have hF:(p,l)∉v2 I C:=λ h=>Y8 (by
  simp only[v0,kv];exact _D _ (_D _ (_D _ h)))
 have hA:(p,l)∉zU I 7 (vw (vh N C) N (vc I C)) (vH (vh N C) (vi I C)) (λ g=>vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))
  (v2 I C):=λ h=>Y8 (by
  simp only[v0,kv];exact _D _ (_D _ (_G _ h)))
 have hH:(p,l)∉zg I 3 (vw (vh N C) N (vc I C)) (λ g=>vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)):=λ h=>Y8 (by
  simp only[v0,kv];exact _D _ (_G _ h))
 exact m4 I 3 7 (vh N C) (ul N C) (vc I C) (vi I C) (xN I C hm) (v2 I C) p l hI hF hA hH i hl yi
theorem mJ {N K:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (hm:_b C) (root:Fin K→ ℕ) (line:Fin K→ Fin N) (xH:∀ j:Fin K,((kD I C (root j)).filter λ q=>¬ I q (line j)).card≤12) (qj:_2 N) (vR:∀ e∈qj,I e.1 e.2∧e∉v0 I C) (zs:∀ e∈qj,∃ j:Fin K,e.2=line j∧e.1∈kD I C (root j)):qj.card≤50*(vV (vh N C) N).card+25*K:=by
 classical
 let gs₀:=vh N C;let L:=vi I C;let α:=vc I C;have hT:∀ l u:Fin N,l≠u→((univ.filter λ p=>I p l)∩(univ.filter λ p=>I p u)).card≤1:=by intro l u XA;rw[_y];intro p hp q hq;by_contra W0;have Xo:=(_A (_P hp).1).2;have Xk:=(_A (_P hp).2).2;have U2:=(_A (_P hq).1).2;have Vq:=(_A (_P hq).2).2;exact hI p q l u W0 XA ⟨Xo,Xk,U2,Vq⟩
 have x8:=bh N C hm;have vK:=ul N C;have h4:=wp (n:=N) (m:=N) (K:=K) 12 (by omega)
  (λ l=>univ.filter λ p=>I p l) hT
  (kD I C) (wW gs₀ N α) (vw gs₀ N α) (vU gs₀ N) (vH gs₀ L)
  (λ g hg=>by
   have UD:=(_A hg).1;obtain⟨Zd,Vf⟩:=mem_Ico.mp UD;cases v7:gateAt gs₀ N g with
   | inl rs=>
    have yH:Sum.inl rs∈gs₀:=by simpa only[v7] using jR gs₀ N g Zd Vf
    have y5:=x8 rs yH;have vR:vU gs₀ N g⊆rs.toFinset:=by simp only[vU,v7];exact filter_subset _ _
    exact (_C vR).trans ((_u rs).trans y5)
   | inr ar=>
    rcases ar with ⟨a,r⟩
    simp[vU,v7])
  (λ g hg c hc=>yV gs₀ vK N α g hg c hc)
  (λ g hg=>cq I 3 7 gs₀ vK α L g hg)
  (λ g x9 ⟨p,hp⟩=>by
   by_cases x1:g∈vw gs₀ N α
   · refine⟨x1,λ q hq=>?_⟩
     exact ((wJ I 3 7 gs₀ vK α L g x1 q).mp hq).1
   · unfold kD at hp;rw[jm I 3 7 gs₀ α L g x9 x1] at hp;exact (notMem_empty _ hp).elim)
  root line
  (λ j=>by
   have zD:kD I C (root j)\(univ.filter λ p=>I p (line j))=(kD I C (root j)).filter λ q=>¬ I q (line j):=by ext q;simp
   rw[zD];exact xH j)
  qj zs
  (λ e he g hg hp=>by
   have Y8:=(vR e he).2;have NX:=(vR e he).1;have Mp:e∉v2 I C:=λ h=>Y8 (by
    simp only[v0,kv];exact _D _ (_D _ (_D _ h)))
   have zD:vH gs₀ L g∩(univ.filter λ p=>I p e.2)=(vH gs₀ L g).filter λ p=>I p e.2:=by ext q;simp
   rw[zD];by_contra! hfive;apply Mp
   have hα:L (yk gs₀ N g) (λ _=>false)=false:=jw gs₀ N α g hg;have SH:L (yk gs₀ N g) (λ q=>decide (q=e.1))=true:=by simpa only[L,vH,mem_filter,_H,true_and] using hp
   have yP':5≤((univ.filter λ q:Fin N=>L (yk gs₀ N g) (λ r=>decide (r=q))=true).filter (λ q=>I q e.2)).card:=by
    have cX:((vH gs₀ L g).filter (λ q=>I q e.2)).card≤((univ.filter λ q:Fin N=>L (yk gs₀ N g) (λ r=>decide (r=q))=true).filter (λ q=>I q e.2)).card:=by
     apply _C
     intro q hq;obtain⟨Vu,ny⟩:=_A hq;exact _B ⟨_B ⟨_H _,by simpa only[L,vH,mem_filter,_H,true_and] using Vu⟩,ny⟩
    omega
   exact zi I C (yk gs₀ N g) (we C α g hg) hα e.1 e.2 NX SH yP')
 have Ps:((wW gs₀ N α).filter λ g=>2≤(vU gs₀ N g).card)⊆vV gs₀ N:=jL gs₀ N α;have hc:=_C Ps;refine h4.trans ?_
 calc 2*(2*12+1)*((wW gs₀ N α).filter λ g=>2≤(vU gs₀ N g).card).card+(2*12+1)*K≤2*(2*12+1)*(vV gs₀ N).card+(2*12+1)*K:=by gcongr
  _=50*(vV gs₀ N).card+25*K:=by ring
end E3RetainedAndWeapons
section PointF4
open M2 K6 K7 Kb M1
open Classical
lemma xv {n:ℕ} (I:Fin n→ Fin n→ Prop) (L:ℕ→(Fin n→ Bool)→ Bool) (a:ℕ) (S2:¬ zk I L a) (S:Finset (Fin n)) (hS:S.card≤4):L a (vB I S)=true:=by by_contra zj;exact S2 ⟨S,hS,Bool.eq_false_iff.mpr zj⟩
lemma y7 {N:ℕ} (I:_0 N) [_4 I] (C:_a) (a:ℕ) (YL:(C.lineDegrees (N+N) (Ico N (N+N))).getD a 0≤1) (v4:zk I (Z C) a) (p l:Fin N) (hI:I p l) (z1:p∈vS C a) (x9:(p,l)∉v2 I C):((vS C a).filter λ q=>I q l).card≤4:=by
 by_contra! hfive;apply x9
 have h2:2≤(vT C (yt N) a).card:=by
  have h1:=(card_filter_le (vS (N:=N) C a) (λ q=>I q l)).trans' hfive;have h2':(vS (N:=N) C a).card≤(vT C (yt N) a).card:=by
   have Yc:Function.Injective (zf N):=(zf N).injective;rw[← _l (vS (N:=N) C a) Yc];apply _C
   intro x hx;obtain⟨q,hq,rfl⟩:=mem_image.mp hx;rw[← w2];exact (zp _ _).mpr hq
  omega
 have v7:=yB C (yt N) a h2;exact _B ⟨_H _,hI,a,_B ⟨mem_Ico.mpr v7,YL⟩,jp I C a v4,z1,hfive⟩
end PointF4
section PathActiveEval
open M2 Kd M1 K1 Kb Kc
def vZ {N:ℕ} (I:_0 N) (C:_a) (w:ℕ):Prop:=∃ a:ℕ,M9.vo N C w=some a∧zk I (Z C) a
def vj {N:ℕ} (I:_0 N) (C:_a) (w r:ℕ):Prop:=(w,r)∈M9.vm N C∧¬ vZ I C w
lemma je {N:ℕ} (C:_a) (hm:_b C) (x₁ x₂:Fin N→ Bool) (hx:∀ p,x₁ p=true→ x₂ p=true) (w r:ℕ):M9.vl N C (ofFn x₁) w r→ M9.vl N C (ofFn x₂) w r:=by
 rintro⟨he,xo⟩;refine⟨he,?_⟩
 cases hw:M9.vo N C w with
 | none=>
  simp only[M9.xK,hw,Option.elim_none]
 | some a=>
  simp only[M9.xK,hw,Option.elim_some] at xo ⊢;change Z C a x₁=true at xo;exact wm C hm a x₁ x₂ hx xo
lemma y8 {N:ℕ} (C:_a) (hm:_b C) (x₁ x₂:Fin N→ Bool) (hx:∀ p,x₁ p=true→ x₂ p=true) (u v:ℕ):_1 (M9.vl N C (ofFn x₁)) u v→_1 (M9.vl N C (ofFn x₂)) u v:=by
 intro hp;induction hp using ReflTransGen.head_induction_on with
 | refl=>exact .refl
 | head he _ ih=>exact .head (je C hm x₁ x₂ hx _ _ he) ih
lemma uK {N:ℕ} (I:_0 N) (C:_a) (hm:_b C) (S:_3 N) (hS:S.card≤4) (x:Fin N→ Bool) (hx:∀ q,vB I S q=true→ x q=true) (w r:ℕ) (zl:vj I C w r):M9.vl N C (ofFn x) w r:=by
 refine⟨zl.1,?_⟩
 cases hw:M9.vo N C w with
 | none=>simp only[M9.xK,hw,Option.elim_none]
 | some a=>
  simp only[M9.xK,hw,Option.elim_some];have S2:¬ zk I (Z C) a:=λ h=>zl.2 ⟨a,hw,h⟩;exact wm C hm a (vB I S) x hx (xv I (Z C) a S2 S hS)
lemma yN {N:ℕ} (I:_0 N) (C:_a) (hm:_b C) (S:_3 N) (hS:S.card≤4) (x:Fin N→ Bool) (hx:∀ q,vB I S q=true→ x q=true) (u v:ℕ):_1 (vj I C) u v→_1 (M9.vl N C (ofFn x)) u v:=by
 intro hp;induction hp using ReflTransGen.head_induction_on with
 | refl=>exact .refl
 | head he _ ih=>exact .head (uK I C hm S hS x hx _ _ he) ih
lemma nf {N:ℕ} (I:_0 N) (C:_a) (x:List Bool) (u v:ℕ) (hp:_1 (M9.vl N C x) u v):_1 (vj I C) u v∨∃ g c,_1 (M9.vl N C x) u g∧M9.vl N C x g c∧vZ I C g∧_1 (vj I C) c v:=by
 induction hp using ReflTransGen.head_induction_on with
 | refl=>exact Or.inl .refl
 | head he hrest ih=>
  rename_i a b
  rcases ih with nJ | ⟨g,c,Wy,hgc,v4,hcv⟩
  · by_cases qZ:vZ I C a
    · exact Or.inr ⟨a,b,.refl,he,qZ,nJ⟩
    · exact Or.inl (.head ⟨he.1,qZ⟩ nJ)
  · exact Or.inr ⟨g,c,.head he Wy,hgc,v4,hcv⟩
lemma ww {N:ℕ} (I:_0 N) (C:_a) (x:List Bool) (u v:ℕ) (hp:_1 (M9.vl N C x) u v):_1 (vj I C) u v∨∃ g c,_1 (vj I C) u g∧M9.vl N C x g c∧vZ I C g∧_1 (M9.vl N C x) c v:=by
 induction hp using ReflTransGen.head_induction_on with
 | refl=>exact Or.inl .refl
 | head he hrest ih=>
  rename_i a b
  by_cases qZ:vZ I C a
  · exact Or.inr ⟨a,b,.refl,he,qZ,hrest⟩
  · rcases ih with nJ | ⟨g,c,Wy,hgc,v4,hcv⟩
    · exact Or.inl (.head ⟨he.1,qZ⟩ nJ)
    · exact Or.inr ⟨g,c,.head ⟨he.1,qZ⟩ Wy,hgc,v4,hcv⟩
lemma vL {N:ℕ} (I:_0 N) (C:_a) (hm:_b C) (S:_3 N) (hS:S.card≤4) (x y:Fin N→ Bool) (hx:∀ q,vB I S q=true→ x q=true) (r:ℕ) (l:Fin N) (hl:l∈vk (vh N C) (vc I C) r) (YG:y l=true):(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD r false=true:=by
 have h1:(run (vh N C) (vc I C) (ofFn (λ u=>decide (u=l)))).getD r false=true:=(y4 (vh N C) (vc I C) l r).mpr hl;refine ze (vh N C) (vc I C) (vy N C (ofFn x)) (λ a ha=>?_) (λ u=>decide (u=l)) y (λ u hu=>by have eq:u=l:=_o hu;subst u;exact YG) r h1
 have Ju:¬ zk I (Z C) a:=by
  intro v4;have ⟨S',_,hfs'⟩:=v4;have MH:Z (N:=N) C a (λ _=>false)=false:=by
   by_contra ht;have Pu:Z (N:=N) C a (λ _=>false)=true:=Bool.eq_true_of_not_eq_false ht;have L5:=wm C hm a (λ _=>false) (vB I S')
    (λ (_:Fin N) (h:false=true)=>False.elim (Bool.noConfusion h)) Pu
   rw[L5] at hfs';exact Bool.noConfusion hfs'
  have hf:vc I C a=false:=by
   unfold vc vi vO;classical
   rw[_O v4,MH]
  rw[hf] at ha;exact Bool.noConfusion ha
 change Z C a x=true;exact wm C hm a (vB I S) x hx (xv I (Z C) a Ju S hS)
lemma yI {N:ℕ} (I:_0 N) (C:_a) (hm:_b C) (S:_3 N) (hS:S.card≤4) (x y:Fin N→ Bool) (hx:∀ q,vB I S q=true→ x q=true) (r:ℕ) (p u:Fin N) (hu:u∈v9 (vh N C) (vi I C) r p) (PO:x p=true) (Nt:y u=true):(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD r false=true:=by
 have h1:(run (vh N C) (λ a=>vi I C a (λ q=>decide (q=p))) (ofFn (λ v=>decide (v=u)))).getD r false=true:=(y4 (vh N C) (λ a=>vi I C a (λ q=>decide (q=p))) u r).mpr hu;refine ze (vh N C) (λ a=>vi I C a (λ q=>decide (q=p))) (vy N C (ofFn x)) (λ a ha=>?_) (λ v=>decide (v=u)) y (λ v hv=>by have eq:v=u:=_o hv;subst v;exact Nt) r h1
 change Z C a x=true;by_cases v4:zk I (Z C) a
 · have Ph:Z C a (λ q=>decide (q=p))=true:=by
    simpa only[vi,vO,_O v4] using ha
   exact wm C hm a (λ q=>decide (q=p)) x (λ q hq=>by have eq:q=p:=_o hq;subst q;exact PO) Ph
 · exact wm C hm a (vB I S) x hx (xv I (Z C) a v4 S hS)
lemma zc {J N:ℕ} (I:_0 N) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (fa jb) false=true→(C.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (j:Fin J) (wa ua va wb xb yb:ℕ) (Su:M9.y3 N C wa ua va) (Sm:M9.y3 N C wb xb yb) (x y:Fin N→ Bool) (z1:_1 (M9.vl N C (ofFn x)) (fa j) wa) (jn:_1 (M9.vl N C (ofFn x)) (fb j) wb) (gy:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C ua) false=true) (WT:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C va) false=true)
 (ZR:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C xb) false=true)
 (Z3:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C yb) false=true):
 ∃(pa lb:Fin N),I pa lb∧x pa=true∧y lb=true:=by
 have cz:=M9.xi N C wa ua va Su;have U8:=M9.xi N C wb xb yb Sm;have mH:(ofFn x).length=N:=by simp
 have nC:(ofFn y).length=N:=by simp
 have Nz:yS N C ua≤2:=by change M9.yf N C ua≤2;have:=cz.2.2.2.1;omega
 have Mu:yS N C va≤2:=by change M9.yf N C va≤2;have:=cz.2.2.2.2;omega
 have Nl:yS N C xb≤2:=by change M9.yf N C xb≤2;have:=U8.2.2.2.1;omega
 have Nw:yS N C yb≤2:=by change M9.yf N C yb≤2;have:=U8.2.2.2.2;omega
 rw[yv N C hm _ _ mH nC ua Nz] at gy;rw[yv N C hm _ _ mH nC va Mu] at WT;rw[yv N C hm _ _ mH nC xb Nl] at ZR;rw[yv N C hm _ _ mH nC yb Nw] at Z3;have V9:=M9.dI N C hm _ _ mH nC wa ua va Su gy WT;have Uk:=M9.dI N C hm _ _ mH nC wb xb yb Sm ZR Z3;have b6:=M9.ZQ N C hm _ _ mH nC (fa j) wa z1 V9;have bp:=M9.ZQ N C hm _ _ mH nC (fb j) wb jn Uk;change (C.wires (ofFn x ++ ofFn y)).getD (fa j) false=true at b6;change (C.wires (ofFn x ++ ofFn y)).getD (fb j) false=true at bp;rw[← List.ofFn_fin_append x y] at b6 bp;obtain⟨pa,lb,hI,hp,hl⟩:=vM j (Fin.append x y) b6 bp
 exact⟨pa,lb,hI,by simpa only[Fin.append_left] using hp,by simpa only[Fin.append_right] using hl⟩
lemma kZ {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (Q:_3 N) (q:Fin N) (xS:8≤ Q.card∧¬(z8 I Q∧4≤(Q.filter (I q)).card)):∀ p₁ p₂:Fin N,p₁≠p₂→(∃ u∈Q,¬ I q u∧¬ I p₁ u)∨(∃ u∈Q,¬ I q u∧¬ I p₂ u):=by
 classical
 let Q':=Q.filter λ u=>¬ I q u;by_cases gV:∃ u₀∈Q',∀ p:Fin N,¬ I p u₀
 · obtain⟨u₀,hu₀,RI⟩:=gV;obtain⟨hu₀Q,hu₀q⟩:=_A hu₀;intro p₁ _ _;exact Or.inl ⟨u₀,hu₀Q,hu₀q,RI p₁⟩
 · push Not at gV
   have hQ'2:2≤ Q'.card:=by
    by_cases zu:z8 I Q
    · have cX:(Q.filter (I q)).card≤3:=by
       by_contra! h4;exact xS.2 ⟨zu,h4⟩
      have p5:Q.card=(Q.filter (I q)).card+Q'.card:=by simpa[Q'] using (_t (s:=Q) (p:=I q)).symm
      omega
    · by_contra! h1;by_cases h0:Q'.card=0
      · have vR:Q⊆pencil I q:=by
         intro u hu;by_contra hnq;have yH:u∈Q':=_B ⟨hu,by simpa[pencil] using hnq⟩
         rw[Finset.card_eq_zero.mp h0] at yH;simp at yH
        exact zu ⟨{q},by simp,λ u hu=>_F ⟨q,by simp,vR hu⟩⟩
      · have Ro:Q'.card=1:=by omega
        obtain⟨u₀,hu₀⟩:=_x.mp Ro;have hu₀Q':u₀∈Q':=by rw[hu₀];exact _I u₀
        obtain⟨p,hp⟩:=gV u₀ hu₀Q';exact zu ⟨{q,p},Finset.card_le_two,λ u hu=>by
         by_cases b8:I q u
         · exact _F ⟨q,by simp,_B ⟨_H _,b8⟩⟩
         · have yH:u∈Q':=_B ⟨hu,b8⟩;rw[hu₀,mem_singleton] at yH;subst u;exact _F ⟨p,by simp,_B ⟨_H _,hp⟩⟩⟩
   obtain⟨u₁,hu₁,u₂,hu₂,xR⟩:=_Z (by omega:1 < Q'.card);have U2:u₁∈Q:=(_A hu₁).1;have Oy:¬ I q u₁:=(_A hu₁).2;have Vq:u₂∈Q:=(_A hu₂).1;have Os:¬ I q u₂:=(_A hu₂).2;intro p₁ p₂ hpne;by_contra! uq;exact hI p₁ p₂ u₁ u₂ hpne xR ⟨uq.1 u₁ U2 Oy,uq.1 u₂ Vq Os,uq.2 u₁ U2 Oy,uq.2 u₂ Vq Os⟩
lemma jv {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (R:_3 N) (hR5:5≤ R.card) (pu:Fin N→_3 N) (Yn:∀ q∈R,8≤(pu q).card∧¬(z8 I (pu q)∧4≤((pu q).filter (I q)).card)):∃ fV:Fin N,∀ p:Fin N,p≠fV→∀(pC py:Option (Fin N)),∃ q∈R,(∀ qx,pC=some qx→ q≠qx)∧(∀ qy,py=some qy→ q≠qy)∧∃ u∈pu q,¬ I q u∧¬ I p u:=by
 classical
 have Pj:0 < N:=by obtain⟨q₀,_⟩:=card_pos.mp (by omega:0 < R.card);exact Fin.pos q₀
 let z0:Fin N:=⟨0,Pj⟩;have nk:∀ q∈R,∃ OP:Fin N,∀ p,p≠OP→∃ u∈pu q,¬ I q u∧¬ I p u:=by
  intro q hq;by_cases wr:∃ p,¬ ∃ u∈pu q,¬ I q u∧¬ I p u
  · obtain⟨OP,NM⟩:=wr;refine⟨OP,λ p hp=>?_⟩
    rcases kZ I hI (pu q) q (Yn q hq) p OP hp with h | h
    · exact h
    · exact (NM h).elim
  · push Not at wr;exact⟨z0,λ p _=>wr p⟩
 let kY:Fin N→ Fin N:=λ q=>if hq:q∈R then (nk q hq).choose else z0;have ZJ:∀ q∈R,∀ p,p≠kY q→∃ u∈pu q,¬ I q u∧¬ I p u:=by intro q hq p hp;simp only[kY,_Q hq] at hp;exact (nk q hq).choose_spec p hp
 by_cases YV:∃ p:Fin N,3≤(R.filter λ q=>kY q=p).card
 · obtain⟨fV,UR⟩:=YV;refine⟨fV,λ p hp pC py=>?_⟩
   have fl:Disjoint (R.filter λ q=>kY q=p) (R.filter λ q=>kY q=fV):=by
    apply disjoint_left.mpr
    intro q h1 h2;have U2:=(_A h1).2;have Vq:=(_A h2).2;exact hp (U2.symm.trans Vq)
   have Yy:(R.filter λ q=>kY q=p).card+(R.filter λ q=>kY q=fV).card≤ R.card:=by rw[← card_union_of_disjoint fl];exact _C (union_subset (filter_subset _ _) (filter_subset _ _))
   let mg:_3 N:=pC.elim ∅ (λ x=>({x}:_3 N));let nN:_3 N:=py.elim ∅ (λ x=>({x}:_3 N));let PS:=(R\(R.filter λ q=>kY q=p))\(mg∪nN);have Wc:PS.Nonempty:=by
    rw[Finset.nonempty_iff_ne_empty];intro Sh;have vR:R⊆(R.filter λ q=>kY q=p)∪(mg∪nN):=by
     intro q hq;by_cases h1:q∈R.filter λ q=>kY q=p
     · exact _D _ h1
     · by_cases h2:q∈mg∪nN
       · exact _G _ h2
       · have:q∈PS:=_V ⟨_V ⟨hq,h1⟩,h2⟩;rw[Sh] at this;simp at this
    have hc:=_C vR;have hu:=_J (R.filter λ q=>kY q=p) (mg∪nN);have hub:=_J mg nN;have Kq:mg.card≤1:=by cases pC <;> simp[mg]
    have Kj:nN.card≤1:=by cases py <;> simp[nN]
    omega
   obtain⟨q,VB⟩:=Wc;obtain⟨U2,Vq⟩:=_M VB;obtain⟨Xl,Wl⟩:=_M U2;have Yh:p≠kY q:=λ h=>Wl (_B ⟨Xl,h.symm⟩);refine⟨q,Xl,?_,?_,ZJ q Xl p Yh⟩
   · intro qx NN;intro zD;subst q;exact Vq (_D _ (by simp[mg,NN]))
   · intro qy NE;intro zD;subst q;exact Vq (_G _ (by simp[nN,NE]))
 · push Not at YV;refine⟨z0,λ p _ pC py=>?_⟩
   let mg:_3 N:=pC.elim ∅ (λ x=>({x}:_3 N));let nN:_3 N:=py.elim ∅ (λ x=>({x}:_3 N));let PS:=(R\(R.filter λ q=>kY q=p))\(mg∪nN);have Wc:PS.Nonempty:=by
    rw[Finset.nonempty_iff_ne_empty];intro Sh;have vR:R⊆(R.filter λ q=>kY q=p)∪(mg∪nN):=by
     intro q hq;by_cases h1:q∈R.filter λ q=>kY q=p
     · exact _D _ h1
     · by_cases h2:q∈mg∪nN
       · exact _G _ h2
       · have:q∈PS:=_V ⟨_V ⟨hq,h1⟩,h2⟩;rw[Sh] at this;simp at this
    have hc:=_C vR;have hu:=_J (R.filter λ q=>kY q=p) (mg∪nN);have hub:=_J mg nN;have Kq:mg.card≤1:=by cases pC <;> simp[mg]
    have Kj:nN.card≤1:=by cases py <;> simp[nN]
    have Tm:=YV p;omega
   obtain⟨q,VB⟩:=Wc;obtain⟨U2,Vq⟩:=_M VB;obtain⟨Xl,Wl⟩:=_M U2;have Yh:p≠kY q:=λ h=>Wl (_B ⟨Xl,h.symm⟩);refine⟨q,Xl,?_,?_,ZJ q Xl p Yh⟩
   · intro qx NN zD;subst q;exact Vq (_D _ (by simp[mg,NN]))
   · intro qy NE zD;subst q;exact Vq (_G _ (by simp[nN,NE]))
lemma xm {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (U:_3 N) (hU:2≤ U.card):∃ qStar:Option (Fin N),∀ q:Fin N,(∀ qs,qStar=some qs→ q≠qs)→∃ u∈U,¬ I q u:=by
 classical
 by_cases wr:∃ q:Fin N,∀ u∈U,I q u
 · obtain⟨qs,Ta⟩:=wr;refine⟨some qs,λ q xR=>?_⟩
   by_contra! cn;obtain⟨u₁,hu₁,u₂,hu₂,hune⟩:=_Z (by omega:1 < U.card);exact hI q qs u₁ u₂ (xR qs rfl) hune ⟨cn u₁ hu₁,cn u₂ hu₂,Ta u₁ hu₁,Ta u₂ hu₂⟩
 · push Not at wr;exact⟨none,λ q _=>wr q⟩
end PathActiveEval
section L1aTripleAvoidance
open Kc Ma
lemma ym {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (Q:_3 N) (q₁:Fin N) (xS:8≤ Q.card∧¬(vx (pencil I) 3 Q∧4≤(Q.filter (I q₁)).card)):(¬ vx (pencil I) 3 Q→∀ q₂ q₃:Fin N,∃ u∈Q,¬ I q₁ u∧¬ I q₂ u∧¬ I q₃ u)∧(vx (pencil I) 3 Q→∃ B:_3 N,B.card≤2∧∀ q₂ q₃:Fin N,q₂∉B→ q₃∉B→∃ u∈Q,¬ I q₁ u∧¬ I q₂ u∧¬ I q₃ u):=by
 classical
 constructor
 · intro Xu q₂ q₃;by_contra! cn;apply Xu
   refine⟨{q₁,q₂,q₃},?_,?_⟩
   · exact (_K _ _).trans (_n (Finset.card_le_two))
   · intro u hu;by_cases h1:I q₁ u
     · exact _F ⟨q₁,by simp,_B ⟨_H _,h1⟩⟩
     · by_cases h2:I q₂ u
       · exact _F ⟨q₂,by simp,_B ⟨_H _,h2⟩⟩
       · have h3:=cn u hu h1 h2;exact _F ⟨q₃,by simp,_B ⟨_H _,h3⟩⟩
 · intro zu
   have Np:(Q.filter (I q₁)).card≤3:=by by_contra! h4;exact xS.2 ⟨zu,h4⟩
   let Q₀:=Q.filter λ u=>¬ I q₁ u;have p5:Q.card=(Q.filter (I q₁)).card+Q₀.card:=by simpa[Q₀] using (_t (s:=Q) (p:=I q₁)).symm
   have hQ₀5:5≤ Q₀.card:=by omega
   have Ll:zT (pencil I):=by intro a b fP;by_contra! hgt;obtain⟨l₁,hl₁,l₂,hl₂,xR⟩:=_Z hgt;exact hI a b l₁ l₂ fP xR ⟨(_A (_P hl₁).1).2,(_A (_P hl₂).1).2,(_A (_P hl₁).2).2,(_A (_P hl₂).2).2⟩
   refine⟨xx (pencil I) Q₀,qS (pencil I) Ll Q₀,?_⟩
   intro q₂ q₃ hq₂ hq₃;obtain⟨u,huQ₀,hnu₂,hnu₃⟩:=xQ (pencil I) Q₀ q₂ q₃ hQ₀5 hq₂ hq₃;obtain⟨Ky,hnu₁⟩:=_A huQ₀;exact⟨u,Ky,hnu₁,by simpa[pencil] using hnu₂,by simpa[pencil] using hnu₃⟩
lemma u6 {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (A B C:_3 N) (hA:13≤ A.card) (hB:13≤ B.card) (hC:13≤ C.card) (XH Wg Wd:Fin N→_3 N) (SS:∀ q∈A,8≤(XH q).card∧¬(vx (pencil I) 3 (XH q)∧4≤((XH q).filter (I q)).card)) (Qq:∀ q∈B,8≤(Wg q).card∧¬(vx (pencil I) 3 (Wg q)∧4≤((Wg q).filter (I q)).card)) (Qx:∀ q∈C,8≤(Wd q).card∧¬(vx (pencil I) 3 (Wd q)∧4≤((Wd q).filter (I q)).card)):∃ q₁∈A,∃ q₂∈B,∃ q₃∈C,(∃ u₁∈XH q₁,¬ I q₁ u₁∧¬ I q₂ u₁∧¬ I q₃ u₁)∧(∃ u₂∈Wg q₂,¬ I q₂ u₂∧¬ I q₁ u₂∧¬ I q₃ u₂)∧(∃ u₃∈Wd q₃,¬ I q₃ u₃∧¬ I q₁ u₃∧¬ I q₂ u₃):=by
 classical
 obtain⟨A',SZ,cy⟩:=_N hA;obtain⟨B',SN,cG⟩:=_N hB;obtain⟨C',Rr,cB⟩:=_N hC;let z4:(Fin N→_3 N)→ Fin N→_3 N:=λ Q q=>if zu:vx (pencil I) 3 (Q q) then
  if hg:8≤(Q q).card∧¬(vx (pencil I) 3 (Q q)∧4≤((Q q).filter (I q)).card) then ((ym I hI (Q q) q hg).2 zu).choose
  else ∅
  else ∅
 have jJ:∀ Q q,(z4 Q q).card≤2:=by
  intro Q q;dsimp only[z4];split_ifs with zu hg
  · exact ((ym I hI (Q q) q hg).2 zu).choose_spec.1
  · simp
  · simp
 have dJ:∀ Q q,8≤(Q q).card∧¬(vx (pencil I) 3 (Q q)∧4≤((Q q).filter (I q)).card)→∀ p₁ p₂,p₁∉z4 Q q→ p₂∉z4 Q q→∃ u∈Q q,¬ I q u∧¬ I p₁ u∧¬ I p₂ u:=by
  intro Q q hq p₁ p₂ hp₁ hp₂;by_cases zu:vx (pencil I) 3 (Q q)
  · have hp₁':p₁∉((ym I hI (Q q) q hq).2 zu).choose:=by
     simpa only[z4,_Q zu,_Q hq] using hp₁
    have hp₂':p₂∉((ym I hI (Q q) q hq).2 zu).choose:=by simpa only[z4,_Q zu,_Q hq] using hp₂
    exact ((ym I hI (Q q) q hq).2 zu).choose_spec.2 p₁ p₂ hp₁' hp₂'
  · exact (ym I hI (Q q) q hq).1 zu p₁ p₂
 let All:=A'×ˢ (B'×ˢ C');let c5:=All.filter λ t=>t.2.1∈z4 XH t.1∨t.2.2∈z4 XH t.1;let bM:=All.filter λ t=>t.1∈z4 Wg t.2.1∨t.2.2∈z4 Wg t.2.1;let UI:=All.filter λ t=>t.1∈z4 Wd t.2.2∨t.2.1∈z4 Wd t.2.2;have Oc:c5.card≤4*169:=by
  have vR:c5⊆A'.biUnion λ q₁=>((B'∩z4 XH q₁)×ˢ C')∪(B'×ˢ (C'∩z4 XH q₁)) |>.image (λ bc=>(q₁,bc)):=by
   intro⟨q₁,q₂,q₃⟩ ht;obtain⟨zI,wv⟩:=_A ht;simp only[All,mem_product] at zI;refine _F ⟨q₁,zI.1,_W ⟨(q₂,q₃),?_,rfl⟩⟩
   rcases wv with h2 | h3
   · exact _D _ (_R ⟨_X ⟨zI.2.1,h2⟩,zI.2.2⟩)
   · exact _G _ (_R ⟨zI.2.1,_X ⟨zI.2.2,h3⟩⟩)
  refine (_C vR).trans ((_E A' _ (4*13) ?_).trans ?_)
  · intro q₁ _;refine _T.trans ((_J _ _).trans ?_)
    rw[_m,_m,cG,cB];have h1:(B'∩z4 XH q₁).card≤2:=(_C inter_subset_right).trans (jJ XH q₁);have h2:(C'∩z4 XH q₁).card≤2:=(_C inter_subset_right).trans (jJ XH q₁);nlinarith
  · rw[cy]
 have Ol:bM.card≤4*169:=by
  have vR:bM⊆B'.biUnion λ q₂=>((A'∩z4 Wg q₂)×ˢ C')∪(A'×ˢ (C'∩z4 Wg q₂)) |>.image (λ ac=>(ac.1,q₂,ac.2)):=by
   intro⟨q₁,q₂,q₃⟩ ht;obtain⟨zI,wv⟩:=_A ht;simp only[All,mem_product] at zI;refine _F ⟨q₂,zI.2.1,_W ⟨(q₁,q₃),?_,rfl⟩⟩
   rcases wv with h1 | h3
   · exact _D _ (_R ⟨_X ⟨zI.1,h1⟩,zI.2.2⟩)
   · exact _G _ (_R ⟨zI.1,_X ⟨zI.2.2,h3⟩⟩)
  refine (_C vR).trans ((_E B' _ (4*13) ?_).trans ?_)
  · intro q₂ _;refine _T.trans ((_J _ _).trans ?_)
    rw[_m,_m,cy,cB];have h1:(A'∩z4 Wg q₂).card≤2:=(_C inter_subset_right).trans (jJ Wg q₂);have h2:(C'∩z4 Wg q₂).card≤2:=(_C inter_subset_right).trans (jJ Wg q₂);nlinarith
  · rw[cG]
 have hBadC:UI.card≤4*169:=by
  have vR:UI⊆C'.biUnion λ q₃=>((A'∩z4 Wd q₃)×ˢ B')∪(A'×ˢ (B'∩z4 Wd q₃)) |>.image (λ ab=>(ab.1,ab.2,q₃)):=by
   intro⟨q₁,q₂,q₃⟩ ht;obtain⟨zI,wv⟩:=_A ht;simp only[All,mem_product] at zI;refine _F ⟨q₃,zI.2.2,_W ⟨(q₁,q₂),?_,rfl⟩⟩
   rcases wv with h1 | h2
   · exact _D _ (_R ⟨_X ⟨zI.1,h1⟩,zI.2.1⟩)
   · exact _G _ (_R ⟨zI.1,_X ⟨zI.2.1,h2⟩⟩)
  refine (_C vR).trans ((_E C' _ (4*13) ?_).trans ?_)
  · intro q₃ _;refine _T.trans ((_J _ _).trans ?_)
    rw[_m,_m,cy,cG];have h1:(A'∩z4 Wd q₃).card≤2:=(_C inter_subset_right).trans (jJ Wd q₃);have h2:(B'∩z4 Wd q₃).card≤2:=(_C inter_subset_right).trans (jJ Wd q₃);nlinarith
  · rw[cB]
 have hAll_card:All.card=2197:=by simp only[All,_m,cy,cG,cB]
 have cW:(All\(c5∪bM∪UI)).Nonempty:=by rw[Finset.nonempty_iff_ne_empty];intro Sh;have vR:All⊆c5∪bM∪UI:=Finset.sdiff_eq_empty_iff_subset.mp Sh;have hc:=_C vR;have Xt:=_J (c5∪bM) UI;have Y9:=_J c5 bM;omega
 obtain⟨⟨q₁,q₂,q₃⟩,ht⟩:=cW;obtain⟨zI,UK⟩:=_M ht;simp only[All,mem_product] at zI;have hq₁A:q₁∈A:=SZ zI.1;have hq₂B:q₂∈B:=SN zI.2.1;have hq₃C:q₃∈C:=Rr zI.2.2;have OB:¬(q₂∈z4 XH q₁∨q₃∈z4 XH q₁):=λ h=>UK (_D _ (_D _
  (_B ⟨_R ⟨zI.1,_R ⟨zI.2.1,zI.2.2⟩⟩,h⟩)))
 have PJ:¬(q₁∈z4 Wg q₂∨q₃∈z4 Wg q₂):=λ h=>UK (_D _ (_G _
  (_B ⟨_R ⟨zI.1,_R ⟨zI.2.1,zI.2.2⟩⟩,h⟩)))
 have Ov:¬(q₁∈z4 Wd q₃∨q₂∈z4 Wd q₃):=λ h=>UK (_G _
  (_B ⟨_R ⟨zI.1,_R ⟨zI.2.1,zI.2.2⟩⟩,h⟩))
 push Not at OB PJ Ov;refine⟨q₁,hq₁A,q₂,hq₂B,q₃,hq₃C,dJ XH q₁ (SS q₁ hq₁A) q₂ q₃ OB.1 OB.2,dJ Wg q₂ (Qq q₂ hq₂B) q₁ q₃ PJ.1 PJ.2,dJ Wd q₃ (Qx q₃ hq₃C) q₁ q₂ Ov.1 Ov.2⟩
end L1aTripleAvoidance
section DagEdgeCrossing
open K1
lemma xP {N:ℕ} (C:_a) (hm:_b C):(M9.vm N C).toFinset.card≤2*(Mc.vP N C\Mc.vI N C).card:=by have hc:=Mc.bg N C (λ g hg=>(hm g hg).2);have he:(M9.vm N C).toFinset.card≤(M9.vm N C).length:=_u _;rw[Finset.card_sdiff_of_subset (Mc.yO N C)];omega
lemma dk {N:ℕ} (C:_a):(Mc.vP N C\Mc.vI N C).card=M1.vA N 2 C.gates-(Mc.vI N C).card:=by
 rw[Finset.card_sdiff_of_subset (Mc.yO N C)];congr 1
 exact xD N C
lemma zd {N:ℕ} (C:_a) (w a:ℕ) (hw:M9.vo N C w=some a):w∈Mc.vP N C\Mc.vI N C:=by
 classical
 have hd:M9.yf N C w=2:=by
  cases hg:M9.gateAt N C w with
  | none=>simp[M9.vo,hg] at hw
  | some g=>
   by_cases h2:M9.yf N C w=2
   · exact h2
   · simp[M9.vo,hg,h2] at hw
 have z5:w < M9.xu N C:=(M9.x4 N C w hd).2;have Pe:¬ M9.nM N C w:=by intro hf;have hz:=Mc.yJ N C w hf;simp[hw] at hz
 exact _V ⟨_B ⟨mem_range.mpr z5,hd⟩,λ hm=>Pe (_A hm).2⟩
lemma pk {N:ℕ} {I:_0 N} (C:_a) (hm:_b C) (mY:ℕ→_3 N) (j3:ℕ→_3 N) (xT:∀ w r,vj I C w r→ mY r⊆mY w) (ZP:∀ w r p,vj I C w r→ p∈j3 w→ p∈j3 r) (XV:∀ w,2≤(mY w).card→(j3 w).card≤3) (qq:_2 N) (zs:∀ e∈qq,∃ u v,_1 (vj I C) u v∧e.1∈j3 u∧2≤(mY u).card∧(mY v).card=1∧e.2∈mY v):qq.card≤6*(Mc.vP N C\Mc.vI N C).card:=by
 let Edges:=(M9.vm N C).toFinset;have vR:qq⊆Edges.biUnion λ edge=>if (mY edge.2).card=1∧2≤(mY edge.1).card then (j3 edge.1).biUnion λ p=>(mY edge.2).image λ l=>(p,l) else ∅:=by
  intro⟨p,l⟩ he;obtain⟨u,v,ZD,f4,U3,LS,MG⟩:=zs (p,l) he;have wr:∃ a b,vj I C a b∧p∈j3 a∧2≤(mY a).card∧(mY b).card=1∧l∈mY b:=by
   clear he zs qq;induction ZD using ReflTransGen.head_induction_on with
   | refl=>omega
   | head zl hrest ih=>
    rename_i a b
    have jn:p∈j3 b:=ZP a b p zl f4;by_cases WE:2≤(mY b).card
    · exact ih jn WE
    · have bQ:mY v⊆mY b:=by
       clear WE ih jn f4 U3 zl;induction hrest using ReflTransGen.head_induction_on with
       | refl=>exact Finset.Subset.refl _
       | head hs _ ih2=>exact ih2.trans (xT _ _ hs)
      have Wx:(mY b).card=1:=by have cX:=_C bQ;omega
      exact⟨a,b,zl,f4,U3,Wx,bQ MG⟩
  obtain⟨a,b,fP,z1,N2,Wx,pv⟩:=wr;refine _F ⟨(a,b),_v.mpr fP.1,?_⟩
  rw[_O ⟨Wx,N2⟩];exact _F ⟨p,z1,_W ⟨l,pv,rfl⟩⟩
 refine (_C vR).trans ?_
 refine (_E Edges _ 3 ?_).trans ?_
 · intro edge _;split_ifs with h
   · refine (_E (j3 edge.1) _ 1 ?_).trans ?_
     · intro p _;exact _T.trans (by omega)
     · have h3:=XV edge.1 h.2;omega
   · simp
 · have Uf:=xP (N:=N) C hm;nlinarith
lemma nv {N:ℕ} {I:_0 N} (C:_a) (hm:_b C) (hV:ℕ→_3 N) (qe:ℕ→_3 N) (xT:∀ w r,vj I C w r→ hV w⊆hV r) (ZP:∀ w r p,vj I C w r→ p∈qe r→ p∈qe w) (XN:∀ w,2≤(hV w).card→(qe w).card≤3) (qq:_2 N) (zs:∀ e∈qq,∃ u v,_1 (vj I C) u v∧e.1∈qe v∧(hV u).card=1∧e.2∈hV u∧2≤(hV v).card):qq.card≤6*(Mc.vP N C\Mc.vI N C).card:=by
 let Edges:=(M9.vm N C).toFinset;have vR:qq⊆Edges.biUnion λ edge=>if (hV edge.1).card=1∧2≤(hV edge.2).card then (qe edge.2).biUnion λ p=>(hV edge.1).image λ l=>(p,l) else ∅:=by
  intro⟨p,l⟩ he;obtain⟨u,v,ZD,SF,O1,XA,LO⟩:=zs (p,l) he;have wr:∃ a b,vj I C a b∧p∈qe b∧(hV a).card=1∧l∈hV a∧2≤(hV b).card:=by
   clear he zs qq;induction ZD using ReflTransGen.head_induction_on with
   | refl=>omega
   | head zl hrest ih=>
    rename_i a b
    by_cases WE:2≤(hV b).card
    · have jn:p∈qe b:=by
       clear WE ih O1 XA zl;induction hrest using ReflTransGen.head_induction_on with
       | refl=>exact SF
       | head hs _ ih2=>exact ZP _ _ _ hs ih2
      exact⟨a,b,zl,jn,O1,XA,WE⟩
    · have bQ:hV a⊆hV b:=xT a b zl
      have Wx:(hV b).card=1:=by have cX:=_C bQ;omega
      exact ih Wx (bQ XA)
  obtain⟨a,b,fP,jn,Ou,nF,WE⟩:=wr;refine _F ⟨(a,b),_v.mpr fP.1,?_⟩
  rw[_O ⟨Ou,WE⟩];exact _F ⟨p,jn,_W ⟨l,nF,rfl⟩⟩
 refine (_C vR).trans ?_
 refine (_E Edges _ 3 ?_).trans ?_
 · intro edge _;split_ifs with h
   · refine (_E (qe edge.2) _ 1 ?_).trans ?_
     · intro p _;exact _T.trans (by omega)
     · have h3:=XN edge.2 h.2;omega
   · simp
 · have Uf:=xP (N:=N) C hm;nlinarith
end DagEdgeCrossing
section E3OneSide
open M2 Kd M1 K1 Kb Kc
def gS {J N:ℕ} (I:_0 N) (C:_a) (fa fb:Fin J→ ℕ) (p l:Fin N):Prop:=I p l∧∃ j:Fin J,(C.wires (ofFn (yd p l))).getD (fa j) false=true∧(C.wires (ofFn (yd p l))).getD (fb j) false=true∧(C.wires (ofFn (yG p))).getD (fa j) false=false∧(C.wires (ofFn (yG p))).getD (fb j) false=false∧(run (vh N C) (vy N C (wz (yd p l))) (uW (yd p l))).getD (vr N C (fa j)) false=false∧(run (vh N C) (vy N C (wz (yd p l))) (uW (yd p l))).getD (vr N C (fb j)) false=false
lemma n9 {J N:ℕ} (I:_0 N) [_4 I] (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (qZ:∀ jd,(C.lineDegrees (N+N) (Ico N (N+N))).getD (fa jd) 0≤2) (gP:∀ jd,(C.lineDegrees (N+N) (Ico N (N+N))).getD (fb jd) 0≤2) (p l:Fin N) (j:Fin J) (ha:(C.wires (ofFn (yd p l))).getD (fa j) false=true) (hb:(C.wires (ofFn (yd p l))).getD (fb j) false=true) (d3:(C.wires (ofFn (yG p))).getD (fa j) false=false) (YI:(C.wires (ofFn (yG p))).getD (fb j) false=false) (Ve:(run (vh N C) (vy N C (wz (yd p l))) (uW (yd p l))).getD (vr N C (fa j)) false=false) (WX:(run (vh N C) (vy N C (wz (yd p l))) (uW (yd p l))).getD (vr N C (fb j)) false=false):(∃ wa ua va,_1 (M9.vl N C
 (ofFn (λ q=>decide (q=p)))) (fa j) wa∧M9.y3 N C wa ua va∧wa∈Mc.vI N C∧l∈v9 (vh N C) (λ a x=>Z C a x) (vr N C ua) p∧l∈v9 (vh N C) (λ a x=>Z C a x) (vr N C va) p)∧(∃ wb xb yb,_1 (M9.vl N C
 (ofFn (λ q=>decide (q=p)))) (fb j) wb∧M9.y3 N C wb xb yb∧wb∈Mc.vI N C∧l∈v9 (vh N C) (λ a x=>Z C a x) (vr N C xb) p∧l∈v9 (vh N C) (λ a x=>Z C a x) (vr N C yb) p):=by
 have qZ':yS N C (fa j)≤2:=qZ j;have gP':yS N C (fb j)≤2:=gP j;have Qt:wz (yd p l)=ofFn (λ q:Fin N=>decide (q=p)):=uZ p l;have SD:uW (yd p l)=ofFn (λ u:Fin N=>decide (u=l)):=kI p l;rw[Qt,SD] at Ve WX;rw[nV] at ha hb;rw[nj] at d3 YI;have Qw:yS N C (fa j)=2:=by
  by_contra hn;have cX:(C.lineDegrees (N+N) (Ico N (N+N))).getD (fa j) 0≤1:=by have:=qZ j;change (C.lineDegrees (N+N) (Ico N (N+N))).getD (fa j) 0≠2 at hn;omega
  have RF:=zE N C hm _ _ (by simp) (by simp) (fa j) cX ha d3;change (run (vh N C) (vy N C (ofFn (λ q:Fin N=>decide (q=p)))) (ofFn (λ u:Fin N=>decide (u=l)))).getD (vr N C (fa j)) false=true at RF;rw[RF] at Ve;exact Bool.noConfusion Ve
 have La:yS N C (fb j)=2:=by
  by_contra hn;have cX:(C.lineDegrees (N+N) (Ico N (N+N))).getD (fb j) 0≤1:=by have:=gP j;change (C.lineDegrees (N+N) (Ico N (N+N))).getD (fb j) 0≠2 at hn;omega
  have RF:=zE N C hm _ _ (by simp) (by simp) (fb j) cX hb YI;change (run (vh N C) (vy N C (ofFn (λ q:Fin N=>decide (q=p)))) (ofFn (λ u:Fin N=>decide (u=l)))).getD (vr N C (fb j)) false=true at RF;rw[RF] at WX;exact Bool.noConfusion WX
 have Lm:(M9.v1 C (ofFn (λ q:Fin N=>decide (q=p))) (ofFn (λ u:Fin N=>decide (u=l)))).getD (fa j) false=false:=by rw[← yv N C hm _ _ (by simp) (by simp) (fa j) qZ'];exact Ve
 have Nn:(M9.v1 C (ofFn (λ q:Fin N=>decide (q=p))) (ofFn (λ u:Fin N=>decide (u=l)))).getD (fb j) false=false:=by rw[← yv N C hm _ _ (by simp) (by simp) (fb j) gP'];exact WX
 obtain⟨wa,ua,va,z1,m6,RH,ML⟩:=M9.pB N C hm _ _ (by simp) (by simp) (fa j) ⟨Qw,ha,d3,Lm⟩;obtain⟨wb,xb,yb,jn,m9,LB,Lq⟩:=M9.pB N C hm _ _ (by simp) (by simp) (fb j) ⟨La,hb,YI,Nn⟩;have cz:=M9.xi N C wa ua va m6;have U8:=M9.xi N C wb xb yb m9;have Vz:wa∈Mc.vI N C:=by
  classical
  exact _B ⟨mem_range.mpr cz.2.2.1,ua,va,m6⟩
 have VG:wb∈Mc.vI N C:=by
  classical
  exact _B ⟨mem_range.mpr U8.2.2.1,xb,yb,m9⟩
 have WC:∀ r,yS N C r≤2→(M9.v1 C (ofFn (λ q:Fin N=>decide (q=p))) (ofFn (λ u:Fin N=>decide (u=l)))).getD r false=true→ l∈v9 (vh N C) (λ a x=>Z C a x) (vr N C r) p:=by intro r hr qX;rw[← yv N C hm _ _ (by simp) (by simp) r hr] at qX;exact (y4 (vh N C) (λ a=>Z C a (λ q=>decide (q=p))) l (vr N C r)).mp qX
 exact⟨⟨wa,ua,va,z1,m6,Vz,WC ua (by change M9.yf N C ua≤2;have:=cz.2.2.2.1;omega) RH,WC va (by change M9.yf N C va≤2;have:=cz.2.2.2.2;omega) ML⟩,⟨wb,xb,yb,jn,m9,VG,WC xb (by change M9.yf N C xb≤2;have:=U8.2.2.2.1;omega) LB,WC yb (by change M9.yf N C yb≤2;have:=U8.2.2.2.2;omega) Lq⟩⟩
noncomputable def vd (N:ℕ) (C:_a) (w:ℕ) (i:Fin 2):ℕ:=if i=0 then vD N C w else vz N C w
lemma zh (N:ℕ) (C:_a) (w ua va:ℕ) (hf:M9.y3 N C w ua va):vd N C w 0=ua∧vd N C w 1=va:=by simp only[vd,↓reduceIte,Fin.isValue,Fin.one_eq_zero_iff,Nat.reduceEqDiff];exact⟨pL N C w ua va hf,qP N C w ua va hf⟩
lemma x3 {N:ℕ} (I:_0 N) (C:_a) (r:ℕ) (p l:Fin N) (hl:l∈v9 (vh N C) (λ a x=>Z C a x) r p):l∈v9 (vh N C) (vi I C) r p:=by have h1:(run (vh N C) (λ a=>Z C a (λ q=>decide (q=p))) (ofFn (λ u=>decide (u=l)))).getD r false=true:=(y4 (vh N C) (λ a=>Z C a (λ q=>decide (q=p))) l r).mpr hl;exact (y4 (vh N C) (λ a=>vi I C a (λ q=>decide (q=p))) l r).mp (ze (vh N C) (λ a=>Z C a (λ q=>decide (q=p))) (λ a=>vi I C a (λ q=>decide (q=p))) (λ a ha=>uO I (Z C) a _ ha) _ _ (λ _ h=>h) r h1)
lemma xe {J N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (fa jb) false=true→(C.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆
 v9 (vh N C) (vi I C) r q)
 (wa:ℕ) (m7:wa∈Mc.vI N C) (i:Fin 2) (l:Fin N)
 (zN:vk (vh N C) (vc I C) (vr N C (vd N C wa i))={l})
 (V0:l∈vk (vh N C) (vc I C) (vr N C (vd N C wa (1-i)))∨5≤(ve (vr N C (vd N C wa (1-i)))\univ.filter λ q=>I q l).card):
 ∃ fV:Fin N,∀ p':Fin N,p'≠fV→∀(j:Fin J) (wb:ℕ) (kJ:wb∈Mc.vI N C) (Ux Uy:_3 N),(∃ u,_1 (M9.vl N C (ofFn (λ q=>decide (q=p')))) (fa j) u∧_1 (vj I C) u wa)→(∃ v,_1 (vj I C) (fb j) v∧_1 (M9.vl N C (ofFn (λ q=>decide (q=p')))) v wb)→((l∈vk (vh N C) (vc I C) (vr N C (vD N C wb))∧Ux={l})∨((2≤ Ux.card∨∃ u₀:Fin N,Ux={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Ux,¬ I p' u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C wb)) p'))→((l∈vk (vh N C) (vc I C) (vr N C (vz N C wb))∧Uy={l})∨((2≤ Uy.card∨∃ u₀:Fin N,Uy={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Uy,¬ I p' u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C wb)) p'))→ I p' l:=by
 have fk:M9.y3 N C wa (vD N C wa) (vz N C wa):=by
  classical
  exact jI N C wa (_A m7).2
 have mM:∀(p':Fin N) (w:ℕ) (U:_3 N) (S:_3 N) (hS:S.card≤4) (x:Fin N→ Bool) (y:Fin N→ Bool),(∀ q,vB I S q=true→ x q=true)→ x p'=true→((l∈vk (vh N C) (vc I C) (vr N C w)∧U={l})∨((2≤ U.card∨∃ u₀:Fin N,U={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈U,¬ I p' u∧u∈v9 (vh N C) (vi I C) (vr N C w) p'))→ y l=true→(∀ u∈U,y u=true→(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C w) false=true):=by
  intro p' w U S hS x y Xe PO hU YG u hu Nt;rcases hU with ⟨pv,_⟩ | ⟨_,hU⟩
  · exact vL I C hm S hS x y Xe (vr N C w) l pv YG
  · exact yI I C hm S hS x y Xe (vr N C w) p' u (hU u hu).2 PO Nt
 rcases V0 with hpbare | hpr5
 · refine⟨⟨0,Fin.pos l⟩,λ p' _ j wb kJ Ux Uy ⟨u,Zz,hu_wa⟩ ⟨v,hfb_v,Xv⟩ Wu Wk=>?_⟩
   by_contra hnI;have mv:M9.y3 N C wb (vD N C wb) (vz N C wb):=by
    classical
    exact jI N C wb (_A kJ).2
   have MA:∀(U:_3 N),((l∈vk (vh N C) (vc I C) (vr N C (vD N C wb))∧U={l})∨((2≤ U.card∨∃ u₀:Fin N,U={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈U,¬ I p' u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C wb)) p'))→∃ u∈U,¬ I p' u:=by
    intro U hU;rcases hU with ⟨_,rfl⟩ | ⟨h2 | ⟨u₀,rfl,_⟩,wj⟩
    · exact⟨l,_I l,hnI⟩
    · obtain⟨u,hu⟩:=card_pos.mp (by omega:0 < U.card);exact⟨u,hu,(wj u hu).1⟩
    · exact⟨u₀,_I u₀,(wj u₀ (_I u₀)).1⟩
   have Ox:∀(U:_3 N),((l∈vk (vh N C) (vc I C) (vr N C (vz N C wb))∧U={l})∨((2≤ U.card∨∃ u₀:Fin N,U={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈U,¬ I p' u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C wb)) p'))→∃ u∈U,¬ I p' u:=by
    intro U hU;rcases hU with ⟨_,rfl⟩ | ⟨h2 | ⟨u₀,rfl,_⟩,wj⟩
    · exact⟨l,_I l,hnI⟩
    · obtain⟨u,hu⟩:=card_pos.mp (by omega:0 < U.card);exact⟨u,hu,(wj u hu).1⟩
    · exact⟨u₀,_I u₀,(wj u₀ (_I u₀)).1⟩
   obtain⟨ux,Yo,Rp⟩:=MA Ux Wu;obtain⟨uy,YC,Qk⟩:=Ox Uy Wk;let S:_3 N:={l,ux,uy};have wh:S.card≤4:=by
    refine (_K _ _).trans ?_
    have:=_K ux ({uy}:_3 N);simp only[card_singleton] at this;omega
   let x:Fin N→ Bool:=λ q=>decide (q=p') || vB I S q;let y:Fin N→ Bool:=λ w=>decide (w∈S);have UB:x p'=true:=by simp[x]
   have fw:∀ q,decide (q=p')=true→ x q=true:=by intro q hq;simp[x,hq]
   have xc:∀ q,vB I S q=true→ x q=true:=by intro q hq;simp[x,hq]
   have bO:_1 (M9.vl N C (ofFn x)) (fa j) wa:=(y8 C hm _ x fw _ _ Zz).trans
    (yN I C hm S wh x xc _ _ hu_wa)
   have bS:_1 (M9.vl N C (ofFn x)) (fb j) wb:=(yN I C hm S wh x xc _ _ hfb_v).trans
    (y8 C hm _ x fw _ _ Xv)
   have YG:y l=true:=by simp[y,S]
   have SU:y ux=true:=by simp[y,S]
   have S6:y uy=true:=by simp[y,S]
   have gy:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C (vD N C wa)) false=true:=by
    have hi:i=0∨i=1:=by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · have To:vd N C wa 0=vD N C wa:=rfl;rw[To] at zN;exact vL I C hm S wh x y xc _ l (by rw[zN];simp) YG
    · have To:vd N C wa (1-1)=vD N C wa:=rfl;rw[To] at hpbare;exact vL I C hm S wh x y xc _ l hpbare YG
   have WT:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C (vz N C wa)) false=true:=by
    have hi:i=0∨i=1:=by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · have TI:vd N C wa (1-0)=vz N C wa:=rfl;rw[TI] at hpbare;exact vL I C hm S wh x y xc _ l hpbare YG
    · have TI:vd N C wa 1=vz N C wa:=rfl;rw[TI] at zN;exact vL I C hm S wh x y xc _ l (by rw[zN];simp) YG
   have ZR:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C (vD N C wb)) false=true:=mM p' (vD N C wb) Ux S wh x y xc UB Wu YG ux Yo SU;have Z3:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C (vz N C wb)) false=true:=mM p' (vz N C wb) Uy S wh x y xc UB Wk YG uy YC S6;obtain⟨pa,lb,jz,z1,pv⟩:=zc I C fa fb hm vM j wa _ _ wb _ _ fk mv x y bO bS gy WT ZR Z3;have f7:lb∈S:=_o pv;simp only[x,_r,decide_eq_true_eq] at z1;rcases z1 with rfl | hm_pa
   · simp only[S,mem_insert,mem_singleton] at f7;rcases f7 with rfl | rfl | rfl
     · exact hnI jz
     · exact Rp jz
     · exact Qk jz
   · have qY:∀ u∈S,¬ I pa u:=by
      simpa only[vB,decide_eq_true_eq] using hm_pa
     exact qY lb f7 jz
 · let R:=ve (vr N C (vd N C wa (1-i)))\univ.filter λ q=>I q l
   let pu:Fin N→_3 N:=λ q=>if hq:q∈R then
    vk (vh N C) (vc I C) (vu (vh N C) N (vf _ q (_M hq).1).choose)
    else ∅
   have Yn:∀ q∈R,8≤(pu q).card∧¬(z8 I (pu q)∧4≤((pu q).filter (I q)).card):=by
    intro q hq;have wj:=(vf _ q (_M hq).1).choose_spec;simp only[pu,_Q hq];refine⟨by have:=wj.2.2.1;omega,?_⟩
    rintro⟨⟨T,hT2,PN⟩,h4⟩;apply wj.2.2.2.1
    refine⟨⟨T,by omega,PN⟩,h4⟩
   obtain⟨fV,UR⟩:=jv I hI R hpr5 pu Yn;refine⟨fV,λ p' hp' j wb kJ Ux Uy ⟨u,Zz,hu_wa⟩ ⟨v,hfb_v,Xv⟩ Wu Wk=>?_⟩
   by_contra hnI;have mv:M9.y3 N C wb (vD N C wb) (vz N C wb):=by
    classical
    exact jI N C wb (_A kJ).2
   have PX:∀(U:_3 N),((l∈vk (vh N C) (vc I C) (vr N C (vD N C wb))∧U={l})∨(((2≤ U.card∨∃ u₀:Fin N,U={u₀}∧∀ q:Fin N,¬ I q u₀))∧∀ u∈U,¬ I p' u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C wb)) p'))→∃ qStar:Option (Fin N),∀ q,¬ I q l→(∀ qs,qStar=some qs→ q≠qs)→∃ u∈U,¬ I q u∧¬ I p' u:=by
    intro U hU;rcases hU with ⟨_,rfl⟩ | ⟨h2 | ⟨u₀,rfl,RI⟩,wj⟩
    · exact⟨none,λ q ny _=>⟨l,_I l,ny,hnI⟩⟩
    · obtain⟨qs,Ta⟩:=xm I hI U h2
      exact⟨qs,λ q _ Qv=>by obtain⟨u,hu,Vd⟩:=Ta q Qv;exact⟨u,hu,Vd,(wj u hu).1⟩⟩
    · exact⟨none,λ q _ _=>⟨u₀,_I u₀,RI q,(wj u₀ (_I u₀)).1⟩⟩
   have PL:∀(U:_3 N),((l∈vk (vh N C) (vc I C) (vr N C (vz N C wb))∧U={l})∨(((2≤ U.card∨∃ u₀:Fin N,U={u₀}∧∀ q:Fin N,¬ I q u₀))∧∀ u∈U,¬ I p' u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C wb)) p'))→∃ qStar:Option (Fin N),∀ q,¬ I q l→(∀ qs,qStar=some qs→ q≠qs)→∃ u∈U,¬ I q u∧¬ I p' u:=by
    intro U hU;rcases hU with ⟨_,rfl⟩ | ⟨h2 | ⟨u₀,rfl,RI⟩,wj⟩
    · exact⟨none,λ q ny _=>⟨l,_I l,ny,hnI⟩⟩
    · obtain⟨qs,Ta⟩:=xm I hI U h2
      exact⟨qs,λ q _ Qv=>by obtain⟨u,hu,Vd⟩:=Ta q Qv;exact⟨u,hu,Vd,(wj u hu).1⟩⟩
    · exact⟨none,λ q _ _=>⟨u₀,_I u₀,RI q,(wj u₀ (_I u₀)).1⟩⟩
   obtain⟨pC,KS⟩:=PX Ux Wu;obtain⟨py,Kl⟩:=PL Uy Wk;obtain⟨qv,Qe,Qg,Rj,uv,Of,UL,Ty⟩:=UR p' hp' pC py;have T9:qv∈ve (vr N C (vd N C wa (1-i))):=(_M Qe).1;have X3:¬ I qv l:=by intro ny;exact (_M Qe).2 (_B ⟨_H _,ny⟩)
   obtain⟨ux,Yo,UN,TR⟩:=KS qv X3 Qg;obtain⟨uy,YC,V1,T3⟩:=Kl qv X3 Rj;let S:_3 N:={l,uv,ux,uy};have wh:S.card≤4:=by
    refine (_K _ _).trans ?_
    refine _n ((_K _ _).trans ?_)
    have:=_K ux ({uy}:_3 N);simp only[card_singleton] at this;omega
   let x:Fin N→ Bool:=λ q=>decide (q=p') || vB I S q;let y:Fin N→ Bool:=λ w=>decide (w∈S);have UB:x p'=true:=by simp[x]
   have St:x qv=true:=by
    simp only[x,_r,vB,decide_eq_true_eq];right
    intro w hw;simp only[S,mem_insert,mem_singleton] at hw;rcases hw with rfl | rfl | rfl | rfl
    · exact X3
    · exact UL
    · exact UN
    · exact V1
   have fw:∀ q,decide (q=p')=true→ x q=true:=by intro q hq;simp[x,hq]
   have xc:∀ q,vB I S q=true→ x q=true:=by intro q hq;simp[x,hq]
   have bO:_1 (M9.vl N C (ofFn x)) (fa j) wa:=(y8 C hm _ x fw _ _ Zz).trans
    (yN I C hm S wh x xc _ _ hu_wa)
   have bS:_1 (M9.vl N C (ofFn x)) (fb j) wb:=(yN I C hm S wh x xc _ _ hfb_v).trans
    (y8 C hm _ x fw _ _ Xv)
   have YG:y l=true:=by simp[y,S]
   have OE:y uv=true:=by simp[y,S]
   have SU:y ux=true:=by simp[y,S]
   have S6:y uy=true:=by simp[y,S]
   have cH:uv∈v9 (vh N C) (vi I C) (vr N C (vd N C wa (1-i))) qv:=by have wj:=(vf _ qv T9).choose_spec;simp only[pu,_Q Qe] at Of;exact wj.2.2.2.2 Of
   have gy:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C (vD N C wa)) false=true:=by
    have hi:i=0∨i=1:=by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · have To:vd N C wa 0=vD N C wa:=rfl;rw[To] at zN;exact vL I C hm S wh x y xc _ l (by rw[zN];simp) YG
    · have To:vd N C wa (1-1)=vD N C wa:=rfl;rw[To] at cH;exact yI I C hm S wh x y xc _ qv uv cH St OE
   have WT:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C (vz N C wa)) false=true:=by
    have hi:i=0∨i=1:=by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · have TI:vd N C wa (1-0)=vz N C wa:=rfl;rw[TI] at cH;exact yI I C hm S wh x y xc _ qv uv cH St OE
    · have TI:vd N C wa 1=vz N C wa:=rfl;rw[TI] at zN;exact vL I C hm S wh x y xc _ l (by rw[zN];simp) YG
   have ZR:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C (vD N C wb)) false=true:=mM p' (vD N C wb) Ux S wh x y xc UB Wu YG ux Yo SU;have Z3:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C (vz N C wb)) false=true:=mM p' (vz N C wb) Uy S wh x y xc UB Wk YG uy YC S6;obtain⟨pa,lb,jz,z1,pv⟩:=zc I C fa fb hm vM j wa _ _ wb _ _ fk mv x y bO bS gy WT ZR Z3;have f7:lb∈S:=_o pv;simp only[x,_r,decide_eq_true_eq] at z1;rcases z1 with rfl | hm_pa
   · simp only[S,mem_insert,mem_singleton] at f7;rcases f7 with rfl | rfl | rfl | rfl
     · exact hnI jz
     · exact Ty jz
     · exact TR jz
     · exact T3 jz
   · have qY:∀ u∈S,¬ I pa u:=by
      simpa only[vB,decide_eq_true_eq] using hm_pa
     exact qY lb f7 jz
lemma wM {J N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (fa jb) false=true→(C.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q)
 (j:Fin J) (wa wb:ℕ)
 (m7:wa∈Mc.vI N C) (kJ:wb∈Mc.vI N C)
 (i:Fin 2) (l:Fin N)
 (zN:vk (vh N C) (vc I C) (vr N C (vd N C wa i))={l})
 (cz:_1 (vj I C) (fa j) wa)
 (U8:_1 (vj I C) (fb j) wb)
 (z1:l∈vk (vh N C) (vc I C) (vr N C (vd N C wa (1-i)))∨13≤(ve (vr N C (vd N C wa (1-i)))\univ.filter λ q=>I q l).card)
 (ZR:l∈vk (vh N C) (vc I C) (vr N C (vD N C wb))∨13≤(ve (vr N C (vD N C wb))\univ.filter λ q=>I q l).card)
 (Z3:l∈vk (vh N C) (vc I C) (vr N C (vz N C wb))∨13≤(ve (vr N C (vz N C wb))\univ.filter λ q=>I q l).card):
 False:=by
 have fk:M9.y3 N C wa (vD N C wa) (vz N C wa):=by
  classical
  exact jI N C wa (_A m7).2
 have mv:M9.y3 N C wb (vD N C wb) (vz N C wb):=by
  classical
  exact jI N C wb (_A kJ).2
 let r₀:=vr N C (vd N C wa (1-i));let r₁:=vr N C (vD N C wb);let r₂:=vr N C (vz N C wb);let Vn:_3 N:=univ.filter λ q=>I q l;have Yw:∀ w,∃ pu:Fin N→_3 N,∀ q∈ve w\Vn,8≤(pu q).card∧¬(vx (pencil I) 3 (pu q)∧4≤((pu q).filter (I q)).card)∧pu q⊆v9 (vh N C) (vi I C) w q:=by
  intro w;refine⟨λ q=>if hq:q∈ve w\Vn then vk (vh N C) (vc I C) (vu (vh N C) N (vf w q (_M hq).1).choose) else ∅,λ q hq=>?_⟩
  have hs:=(vf w q (_M hq).1).choose_spec;simp only[_Q hq];exact⟨hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2⟩
 obtain⟨Q₀,hQ₀⟩:=Yw r₀;obtain⟨Q₁,hQ₁⟩:=Yw r₁;obtain⟨Q₂,hQ₂⟩:=Yw r₂;have Nm:∃ S:_3 N,S.card≤4∧l∈S∧((run (vh N C) (vy N C (ofFn (vB I S))) (ofFn (λ w=>decide (w∈S)))).getD r₀ false=true∧(run (vh N C) (vy N C (ofFn (vB I S))) (ofFn (λ w=>decide (w∈S)))).getD r₁ false=true∧(run (vh N C) (vy N C (ofFn (vB I S))) (ofFn (λ w=>decide (w∈S)))).getD r₂ false=true):=by
  have X4:∀(a b c:ℕ) (Qa Qb Qc:Fin N→_3 N),(∀ q∈ve a\Vn,8≤(Qa q).card∧¬(vx (pencil I) 3 (Qa q)∧4≤((Qa q).filter (I q)).card)∧Qa q⊆v9 (vh N C) (vi I C) a q)→(∀ q∈ve b\Vn,8≤(Qb q).card∧¬(vx (pencil I) 3 (Qb q)∧4≤((Qb q).filter (I q)).card)∧Qb q⊆v9 (vh N C) (vi I C) b q)→(∀ q∈ve c\Vn,8≤(Qc q).card∧¬(vx (pencil I) 3 (Qc q)∧4≤((Qc q).filter (I q)).card)∧Qc q⊆v9 (vh N C) (vi I C) c q)→13≤(ve a\Vn).card→13≤(ve b\Vn).card→13≤(ve c\Vn).card→∃ q₁ q₂ q₃ u₁ u₂ u₃,¬ I q₁ l∧¬ I q₂ l∧¬ I q₃ l∧¬ I q₁ u₁∧¬ I q₂ u₁∧¬ I q₃ u₁∧¬ I q₁ u₂∧¬ I q₂ u₂∧¬ I q₃ u₂∧¬ I q₁ u₃∧¬ I q₂ u₃∧¬ I q₃ u₃∧u₁∈v9 (vh N C) (vi I C) a q₁∧u₂∈v9 (vh N C) (vi I C) b q₂∧u₃∈v9 (vh N C) (vi I C) c q₃:=by
   intro a b c Qa Qb Qc N6 NA Ni ha hb hc;obtain⟨q₁,hq₁,q₂,hq₂,q₃,hq₃,⟨u₁,hu₁,O0,W8,fp⟩,⟨u₂,hu₂,OT,MC,Jg⟩,⟨u₃,hu₃,Jw,O3,L8⟩⟩:=u6 I hI (ve a\Vn) (ve b\Vn) (ve c\Vn) ha hb hc Qa Qb Qc (λ q hq=>⟨(N6 q hq).1,(N6 q hq).2.1⟩) (λ q hq=>⟨(NA q hq).1,(NA q hq).2.1⟩) (λ q hq=>⟨(Ni q hq).1,(Ni q hq).2.1⟩);have nl:∀ q w,q∈ve w\Vn→¬ I q l:=λ q w LV MM=>(_M LV).2 (_B ⟨_H _,MM⟩);exact⟨q₁,q₂,q₃,u₁,u₂,u₃,nl _ _ hq₁,nl _ _ hq₂,nl _ _ hq₃,O0,W8,fp,MC,OT,Jg,O3,L8,Jw,(N6 q₁ hq₁).2.2 hu₁,(NA q₂ hq₂).2.2 hu₂,(Ni q₃ hq₃).2.2 hu₃⟩
  have w5:∀ S:_3 N,S.card≤4→∀ r q u,(∀ w∈S,¬ I q w)→ u∈S→ u∈v9 (vh N C) (vi I C) r q→(run (vh N C) (vy N C (ofFn (vB I S))) (ofFn (λ w=>decide (w∈S)))).getD r false=true:=by
   intro S hS r q u Km Vb PQ;refine yI I C hm S hS _ _ (λ _ h=>h) r q u PQ ?_ (decide_eq_true Vb)
   simp only[vB,decide_eq_true_eq];exact Km
  rcases z1 with OU | QC <;> rcases ZR with Wx | RV <;> rcases Z3 with WE | Sy
  · refine⟨{l},by simp,by simp,?_,?_,?_⟩
    · exact vL I C hm {l} (by simp) _ _ (λ _ h=>h) r₀ l OU (by simp)
    · exact vL I C hm {l} (by simp) _ _ (λ _ h=>h) r₁ l Wx (by simp)
    · exact vL I C hm {l} (by simp) _ _ (λ _ h=>h) r₂ l WE (by simp)
  · obtain⟨_,_,q,_,_,u,_,_,TD,_,_,_,_,_,_,_,_,Vd,_,_,hu⟩:=X4 r₂ r₂ r₂ Q₂ Q₂ Q₂ hQ₂ hQ₂ hQ₂ Sy Sy Sy;let S:_3 N:={l,u};have wh:S.card≤4:=(_K _ _).trans (by simp);refine⟨S,wh,by simp[S],?_,?_,?_⟩
    · exact vL I C hm S wh _ _ (λ _ h=>h) r₀ l OU (by simp[S])
    · exact vL I C hm S wh _ _ (λ _ h=>h) r₁ l Wx (by simp[S])
    · exact w5 S wh r₂ q u (λ w hw=>by rcases mem_insert.mp hw with rfl | h;exact TD;rw[_U h];exact Vd) (by simp[S]) hu
  · obtain⟨_,q,_,_,u,_,_,TD,_,_,_,_,_,Vd,_,_,_,_,_,hu,_⟩:=X4 r₁ r₁ r₁ Q₁ Q₁ Q₁ hQ₁ hQ₁ hQ₁ RV RV RV;let S:_3 N:={l,u};have wh:S.card≤4:=(_K _ _).trans (by simp);refine⟨S,wh,by simp[S],?_,?_,?_⟩
    · exact vL I C hm S wh _ _ (λ _ h=>h) r₀ l OU (by simp[S])
    · exact w5 S wh r₁ q u (λ w hw=>by rcases mem_insert.mp hw with rfl | h;exact TD;rw[_U h];exact Vd) (by simp[S]) hu
    · exact vL I C hm S wh _ _ (λ _ h=>h) r₂ l WE (by simp[S])
  · obtain⟨q₁,q₂,_,u₁,u₂,_,TF,hnl2,_,O0,W8,_,MC,OT,_,_,_,_,hu₁,hu₂,_⟩:=X4 r₁ r₂ r₂ Q₁ Q₂ Q₂ hQ₁ hQ₂ hQ₂ RV Sy Sy;let S:_3 N:={l,u₁,u₂};have wh:S.card≤4:=(_K _ _).trans (_n ((_K _ _).trans (by simp)));refine⟨S,wh,by simp[S],?_,?_,?_⟩
    · exact vL I C hm S wh _ _ (λ _ h=>h) r₀ l OU (by simp[S])
    · exact w5 S wh r₁ q₁ u₁ (λ w hw=>by simp only[S,mem_insert,mem_singleton] at hw;rcases hw with rfl | rfl | rfl <;> assumption) (by simp[S]) hu₁
    · exact w5 S wh r₂ q₂ u₂ (λ w hw=>by simp only[S,mem_insert,mem_singleton] at hw;rcases hw with rfl | rfl | rfl <;> assumption) (by simp[S]) hu₂
  · obtain⟨q,_,_,u,_,_,TD,_,_,Vd,_,_,_,_,_,_,_,_,hu,_,_⟩:=X4 r₀ r₀ r₀ Q₀ Q₀ Q₀ hQ₀ hQ₀ hQ₀ QC QC QC;let S:_3 N:={l,u};have wh:S.card≤4:=(_K _ _).trans (by simp);refine⟨S,wh,by simp[S],?_,?_,?_⟩
    · exact w5 S wh r₀ q u (λ w hw=>by rcases mem_insert.mp hw with rfl | h;exact TD;rw[_U h];exact Vd) (by simp[S]) hu
    · exact vL I C hm S wh _ _ (λ _ h=>h) r₁ l Wx (by simp[S])
    · exact vL I C hm S wh _ _ (λ _ h=>h) r₂ l WE (by simp[S])
  · obtain⟨q₀,_,q₂,u₀,_,u₂,hnl0,_,hnl2,LK,_,L9,_,_,_,KZ,_,OT,hu₀,_,hu₂⟩:=X4 r₀ r₂ r₂ Q₀ Q₂ Q₂ hQ₀ hQ₂ hQ₂ QC Sy Sy;let S:_3 N:={l,u₀,u₂};have wh:S.card≤4:=(_K _ _).trans (_n ((_K _ _).trans (by simp)));refine⟨S,wh,by simp[S],?_,?_,?_⟩
    · exact w5 S wh r₀ q₀ u₀ (λ w hw=>by simp only[S,mem_insert,mem_singleton] at hw;rcases hw with rfl | rfl | rfl <;> assumption) (by simp[S]) hu₀
    · exact vL I C hm S wh _ _ (λ _ h=>h) r₁ l Wx (by simp[S])
    · exact w5 S wh r₂ q₂ u₂ (λ w hw=>by simp only[S,mem_insert,mem_singleton] at hw;rcases hw with rfl | rfl | rfl <;> assumption) (by simp[S]) hu₂
  · obtain⟨q₀,q₁,_,u₀,u₁,_,hnl0,TF,_,LK,QK,_,KJ,O0,_,_,_,_,hu₀,hu₁,_⟩:=X4 r₀ r₁ r₁ Q₀ Q₁ Q₁ hQ₀ hQ₁ hQ₁ QC RV RV;let S:_3 N:={l,u₀,u₁};have wh:S.card≤4:=(_K _ _).trans (_n ((_K _ _).trans (by simp)));refine⟨S,wh,by simp[S],?_,?_,?_⟩
    · exact w5 S wh r₀ q₀ u₀ (λ w hw=>by simp only[S,mem_insert,mem_singleton] at hw;rcases hw with rfl | rfl | rfl <;> assumption) (by simp[S]) hu₀
    · exact w5 S wh r₁ q₁ u₁ (λ w hw=>by simp only[S,mem_insert,mem_singleton] at hw;rcases hw with rfl | rfl | rfl <;> assumption) (by simp[S]) hu₁
    · exact vL I C hm S wh _ _ (λ _ h=>h) r₂ l WE (by simp[S])
  · obtain⟨q₀,q₁,q₂,u₀,u₁,u₂,hnl0,TF,hnl2,LK,QK,L9,KJ,O0,W8,KZ,MC,OT,hu₀,hu₁,hu₂⟩:=X4 r₀ r₁ r₂ Q₀ Q₁ Q₂ hQ₀ hQ₁ hQ₂ QC RV Sy;let S:_3 N:={l,u₀,u₁,u₂};have wh:S.card≤4:=(_K _ _).trans (_n ((_K _ _).trans (_n ((_K _ _).trans (by simp)))));refine⟨S,wh,by simp[S],?_,?_,?_⟩
    · exact w5 S wh r₀ q₀ u₀ (λ w hw=>by simp only[S,mem_insert,mem_singleton] at hw;rcases hw with rfl | rfl | rfl | rfl <;> assumption) (by simp[S]) hu₀
    · exact w5 S wh r₁ q₁ u₁ (λ w hw=>by simp only[S,mem_insert,mem_singleton] at hw;rcases hw with rfl | rfl | rfl | rfl <;> assumption) (by simp[S]) hu₁
    · exact w5 S wh r₂ q₂ u₂ (λ w hw=>by simp only[S,mem_insert,mem_singleton] at hw;rcases hw with rfl | rfl | rfl | rfl <;> assumption) (by simp[S]) hu₂
 obtain⟨S,wh,XY,hr₀,hr₁,hr₂⟩:=Nm;let x:=vB I S;let y:Fin N→ Bool:=λ w=>decide (w∈S);have bO:_1 (M9.vl N C (ofFn x)) (fa j) wa:=yN I C hm S wh x (λ _ h=>h) (fa j) wa cz;have bS:_1 (M9.vl N C (ofFn x)) (fb j) wb:=yN I C hm S wh x (λ _ h=>h) (fb j) wb U8;have YG:y l=true:=decide_eq_true XY;have gy:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C (vD N C wa)) false=true:=by
  have hi:i=0∨i=1:=by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · have To:vd N C wa 0=vD N C wa:=rfl;rw[To] at zN;exact vL I C hm S wh x y (λ _ h=>h) _ l (by rw[zN];simp) YG
  · simpa only[r₀,show vd N C wa (1-1)=vD N C wa from rfl] using hr₀
 have WT:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C (vz N C wa)) false=true:=by
  have hi:i=0∨i=1:=by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · simpa only[r₀,show vd N C wa (1-0)=vz N C wa from rfl] using hr₀
  · have TI:vd N C wa 1=vz N C wa:=rfl;rw[TI] at zN;exact vL I C hm S wh x y (λ _ h=>h) _ l (by rw[zN];simp) YG
 obtain⟨pa,lb,jz,z1,pv⟩:=zc I C fa fb hm vM j wa _ _ wb _ _ fk mv x y bO bS gy WT hr₁ hr₂;have z1':∀ u∈S,¬ I pa u:=by simpa only[x,vB,decide_eq_true_eq] using z1
 exact z1' lb (_o pv) jz
noncomputable def vN {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (u:ℕ):_3 N:=by
 classical
 exact univ.filter λ l=>∃ w∈Mc.vI N C,∃ i:Fin 2,vk (vh N C) (vc I C) (vr N C (vd N C w i))={l}∧(l∈vk (vh N C) (vc I C) (vr N C (vd N C w (1-i)))∨13≤(ve (vr N C (vd N C w (1-i)))\univ.filter λ q=>I q l).card)∧_1 (vj I C) u w
noncomputable def vF {J N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (fa fb:Fin J→ ℕ) (u:ℕ):_3 N:=by
 classical
 exact univ.filter λ l=>∃ j:Fin J,vN I C ve (fa j)={l}∧_1 (vj I C) (fb j) u
lemma mw {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (w r:ℕ) (zl:vj I C w r):vN I C ve r⊆vN I C ve w:=by intro l hl;unfold vN at hl ⊢;simp only[mem_filter,_H,true_and] at hl ⊢;obtain⟨wf,RQ,i,yi,hp,wP⟩:=hl;exact⟨wf,RQ,i,yi,hp,.head zl wP⟩
lemma bY {J N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (fa fb:Fin J→ ℕ) (w r:ℕ) (zl:vj I C w r):vF I C ve fa fb w⊆vF I C ve fa fb r:=by intro l hl;unfold vF at hl ⊢;simp only[mem_filter,_H,true_and] at hl ⊢;obtain⟨j,Lr,wP⟩:=hl;exact⟨j,Lr,ReflTransGen.tail wP zl⟩
lemma uD {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (w:ℕ) (hw:w∈Mc.vI N C):vN I C ve w=univ.filter λ l=>∃ i:Fin 2,vk (vh N C) (vc I C) (vr N C (vd N C w i))={l}∧(l∈vk (vh N C) (vc I C) (vr N C (vd N C w (1-i)))∨13≤(ve (vr N C (vd N C w (1-i)))\univ.filter λ q=>I q l).card):=by
 ext l;simp only[vN,mem_filter,_H,true_and];constructor
 · rintro⟨w',_,i,yi,hp,wP⟩;cases wP using ReflTransGen.head_induction_on with
   | refl=>exact⟨i,yi,hp⟩
   | head zl _=>
    exfalso;have hf:M9.nM N C w:=by
     classical
     exact (_A hw).2
    have h0:=Mc.yJ N C w hf;have R0:(w,_)∈M9.vm N C:=zl.1;obtain⟨_,hc⟩:=(M9.wA N C w _).mp R0;have qX:0 < (M9.v6 N C w).length:=length_pos_of_mem hc;omega
 · rintro⟨i,yi,hp⟩;exact⟨w,hw,i,yi,hp,.refl⟩
lemma pX {J N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (fa jb) false=true→(C.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q)
 (E₀:_2 N)
 (z6:∀ e∈E₀,(e.1,e.2)∉v2 I C)
 (hE:∀ e∈E₀,I e.1 e.2∧∃(j:Fin J) (wa wb:ℕ),wa∈Mc.vI N C∧wb∈Mc.vI N C∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fa j) wa∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fb j) wb∧(∃ i:Fin 2,vk (vh N C) (vc I C) (vr N C (vd N C wa i))={e.2}∧(e.2∈vk (vh N C) (vc I C) (vr N C (vd N C wa (1-i)))∨13≤(ve (vr N C (vd N C wa (1-i)))\univ.filter λ q=>I q e.2).card))∧(∃ Ux:_3 N,(2≤ Ux.card∨∃ u₀:Fin N,Ux={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Ux,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C wb)) e.1)∧(∃ Uy:_3 N,(2≤ Uy.card∨∃ u₀:Fin N,Uy={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Uy,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C wb)) e.1)∧
  (vF I C ve fa fb wb={e.2}→(e.2∈vk (vh N C) (vc I C) (vr N C (vD N C wb))∨13≤(ve (vr N C (vD N C wb))\univ.filter λ q=>I q e.2).card)∧(e.2∈vk (vh N C) (vc I C) (vr N C (vz N C wb))∨13≤(ve (vr N C (vz N C wb))\univ.filter λ q=>I q e.2).card))):
 E₀.card≤6*(Mc.vI N C).card+24*(Mc.vP N C\Mc.vI N C).card+3*J:=by
 classical
 by_cases hN:N=0
 · subst hN;have Lw:E₀=∅:=Finset.eq_empty_of_forall_notMem λ e=>Fin.elim0 e.1;simp[Lw]
 haveI:NeZero N:=⟨hN⟩;have ff:∀ u v,_1 (vj I C) u v→ vN I C ve v⊆vN I C ve u:=by
  intro u v ZD;induction ZD using ReflTransGen.head_induction_on with
  | refl=>exact Finset.Subset.refl _
  | head hs _ ih=>exact ih.trans (mw I C ve _ _ hs)
 let ws (w:ℕ) (k:Fin 2) (l:Fin N):Prop:=w∈Mc.vI N C∧vk (vh N C) (vc I C) (vr N C (vd N C w k))={l}∧(l∈vk (vh N C) (vc I C) (vr N C (vd N C w (1-k)))∨13≤(ve (vr N C (vd N C w (1-k)))\univ.filter λ q=>I q l).card);let qw:ℕ→ Fin 2→ Fin N→ Fin N:=λ w k l=>if h:ws w k l then
  (xe I hI C fa fb hm vM ve vf w h.1 k l h.2.1 (by
   rcases h.2.2 with h1 | fp
   · exact Or.inl h1
   · exact Or.inr (by omega))).choose
  else 0
 have wU:∀ w k l (h:ws w k l) (p':Fin N),p'≠qw w k l→∀(j:Fin J) (wb:ℕ) (kJ:wb∈Mc.vI N C) (Ux Uy:_3 N),(∃ u,_1 (M9.vl N C (ofFn (λ q=>decide (q=p')))) (fa j) u∧_1 (vj I C) u w)→(∃ v,_1 (vj I C) (fb j) v∧_1 (M9.vl N C (ofFn (λ q=>decide (q=p')))) v wb)→((2≤ Ux.card∨∃ u₀:Fin N,Ux={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Ux,¬ I p' u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C wb)) p')→((2≤ Uy.card∨∃ u₀:Fin N,Uy={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Uy,¬ I p' u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C wb)) p')→ I p' l:=by
  intro w k l h p' xR j wb kJ Ux Uy QP QM Wu Wk;have wj:=(xe I hI C fa fb hm vM ve vf
   w h.1 k l h.2.1 (by rcases h.2.2 with h1 | fp;exact Or.inl h1;exact Or.inr (by omega))).choose_spec
  dsimp only[qw] at xR;rw[_Q h] at xR;exact wj p' xR j wb kJ Ux Uy QP QM (Or.inr Wu) (Or.inr Wk)
 let wC (u:ℕ):Finset (ℕ× Fin 2):=(Mc.vI N C×ˢ (univ:Finset (Fin 2))).filter λ wk=>∃ l:Fin N,ws wk.1 wk.2 l∧_1 (vj I C) u wk.1;let fU (wk:ℕ× Fin 2):Fin N:=if h:∃ l:Fin N,ws wk.1 wk.2 l then h.choose else 0;have jF:∀ wk l,ws wk.1 wk.2 l→ fU wk=l:=by intro wk l h;have wr:∃ l':Fin N,ws wk.1 wk.2 l':=⟨l,h⟩;simp only[fU,_Q wr];have Za:vk (vh N C) (vc I C) (vr N C (vd N C wk.1 wk.2))={wr.choose}:=wr.choose_spec.2.1;have UT:vk (vh N C) (vc I C) (vr N C (vd N C wk.1 wk.2))={l}:=h.2.1;rw[Za] at UT;exact singleton_injective UT
 let j3:ℕ→_3 N:=λ u=>univ.filter λ p=>∀ wk∈wC u,I p (fU wk)∨p=qw wk.1 wk.2 (fU wk);have XR:∀ w r p,vj I C w r→ p∈j3 w→ p∈j3 r:=by
  intro w r p zl hp;simp only[j3,mem_filter,_H,true_and] at hp ⊢;intro wk Xz;apply hp wk
  simp only[wC,mem_filter] at Xz ⊢;exact⟨Xz.1,let ⟨l,hl,Yk⟩:=Xz.2;⟨l,hl,.head zl Yk⟩⟩
 have d5:∀ w,2≤(vN I C ve w).card→(j3 w).card≤3:=by
  intro w h2;obtain⟨l₁,hl₁,l₂,hl₂,xR⟩:=_Z h2;simp only[vN,mem_filter,_H,true_and] at hl₁ hl₂;obtain⟨w₁,hw₁,i₁,hb₁,hp₁,hpath₁⟩:=hl₁;obtain⟨w₂,hw₂,i₂,hb₂,hp₂,hpath₂⟩:=hl₂;have hg₁:ws w₁ i₁ l₁:=⟨hw₁,hb₁,hp₁⟩;have hg₂:ws w₂ i₂ l₂:=⟨hw₂,hb₂,hp₂⟩;have hm₁:(w₁,i₁)∈wC w:=_B ⟨_R ⟨hw₁,_H _⟩,l₁,hg₁,hpath₁⟩;have hm₂:(w₂,i₂)∈wC w:=_B ⟨_R ⟨hw₂,_H _⟩,l₂,hg₂,hpath₂⟩;let p₁:=qw w₁ i₁ l₁;let p₂:=qw w₂ i₂ l₂;have vR:j3 w⊆({p₁,p₂}:_3 N)∪univ.filter (λ p=>I p l₁∧I p l₂):=by
   intro p hp;simp only[j3,mem_filter,_H,true_and] at hp;have hc₁:=hp (w₁,i₁) hm₁;have hc₂:=hp (w₂,i₂) hm₂;rw[jF (w₁,i₁) l₁ hg₁] at hc₁;rw[jF (w₂,i₂) l₂ hg₂] at hc₂;rcases hc₁ with hI₁ | rfl
   · rcases hc₂ with hI₂ | rfl
     · exact _G _ (_B ⟨_H _,hI₁,hI₂⟩)
     · exact _D _ (_L (_I _))
   · exact _D _ (_S _ _)
  have TJ:(univ.filter (λ p=>I p l₁∧I p l₂)).card≤1:=by by_contra! hgt;obtain⟨q₁,hq₁,q₂,hq₂,Wl⟩:=_Z hgt;exact hI q₁ q₂ l₁ l₂ Wl xR ⟨(_A hq₁).2.1,(_A hq₁).2.2,(_A hq₂).2.1,(_A hq₂).2.2⟩
  have XS:({p₁,p₂}:_3 N).card≤2:=(_K _ _).trans (by simp);exact (_C vR).trans ((_J _ _).trans (by omega))
 let Zv (j:Fin J) (l:Fin N):Prop:=vN I C ve (fa j)={l};let f2 (j:Fin J):Fin N:=if h:∃ l:Fin N,Zv j l then h.choose else 0;let gj (j:Fin J):ℕ× Fin 2:=if h:∃ l:Fin N,Zv j l∧∃ w∈Mc.vI N C,∃ k:Fin 2,ws w k l∧_1 (vj I C) (fa j) w then
  let w:=h.choose_spec.2.choose;let k:=h.choose_spec.2.choose_spec.2.choose;(w,k)
  else (0,0)
 have nD:∀ j l,Zv j l→
  let wk:=gj j;ws wk.1 wk.2 l∧_1 (vj I C) (fa j) wk.1∧f2 j=l:=by
  intro j l hj;have VD:l∈vN I C ve (fa j):=by rw[hj];exact _I l
  simp only[vN,mem_filter,_H,true_and] at VD;obtain⟨w,hw,k,yi,hp,wP⟩:=VD;have wr:∃ l':Fin N,Zv j l'∧∃ w'∈Mc.vI N C,∃ k':Fin 2,ws w' k' l'∧_1 (vj I C) (fa j) w':=⟨l,hj,w,hw,k,⟨hw,yi,hp⟩,wP⟩;have Sc:wr.choose=l:=by have h1:vN I C ve (fa j)={wr.choose}:=wr.choose_spec.1;rw[hj] at h1;exact (singleton_injective h1).symm
  have bW:f2 j=l:=by have RK:∃ l':Fin N,Zv j l':=⟨l,hj⟩;dsimp only[f2];rw[_Q RK];have h1:vN I C ve (fa j)={RK.choose}:=RK.choose_spec;rw[hj] at h1;exact (singleton_injective h1).symm
  dsimp only[gj];rw[_Q wr];obtain⟨NV,MZ,NR⟩:=wr.choose_spec.2.choose_spec.2.choose_spec.1;have Yk:=wr.choose_spec.2.choose_spec.2.choose_spec.2;refine⟨⟨NV,?_,?_⟩,Yk,bW⟩
  · rw[← Sc];exact MZ
  · rw[← Sc];exact NR
 let qe:ℕ→_3 N:=λ v=>univ.filter λ p=>∀ j:Fin J,(∃ l,Zv j l)→_1 (vj I C) (fb j) v→ I p (f2 j)∨p=qw (gj j).1 (gj j).2 (f2 j);have Wj:∀ w r p,vj I C w r→ p∈qe r→ p∈qe w:=by intro w r p zl hp;simp only[qe,mem_filter,_H,true_and] at hp ⊢;intro j hj wP;exact hp j hj (ReflTransGen.tail wP zl)
 have dQ:∀ v,2≤(vF I C ve fa fb v).card→(qe v).card≤3:=by
  intro v h2;obtain⟨l₁,hl₁,l₂,hl₂,xR⟩:=_Z h2;simp only[vF,mem_filter,_H,true_and] at hl₁ hl₂;obtain⟨j₁,hj₁,hpath₁⟩:=hl₁;obtain⟨j₂,hj₂,hpath₂⟩:=hl₂;have hs₁:=nD j₁ l₁ hj₁;have hs₂:=nD j₂ l₂ hj₂;let p₁:=qw (gj j₁).1 (gj j₁).2 l₁;let p₂:=qw (gj j₂).1 (gj j₂).2 l₂;have vR:qe v⊆({p₁,p₂}:_3 N)∪univ.filter (λ p=>I p l₁∧I p l₂):=by
   intro p hp;simp only[qe,mem_filter,_H,true_and] at hp;have hc₁:=hp j₁ ⟨l₁,hj₁⟩ hpath₁;have hc₂:=hp j₂ ⟨l₂,hj₂⟩ hpath₂;rw[hs₁.2.2] at hc₁;rw[hs₂.2.2] at hc₂;rcases hc₁ with hI₁ | rfl
   · rcases hc₂ with hI₂ | rfl
     · exact _G _ (_B ⟨_H _,hI₁,hI₂⟩)
     · exact _D _ (_L (_I _))
   · exact _D _ (_S _ _)
  have TJ:(univ.filter (λ p=>I p l₁∧I p l₂)).card≤1:=by by_contra! hgt;obtain⟨q₁,hq₁,q₂,hq₂,Wl⟩:=_Z hgt;exact hI q₁ q₂ l₁ l₂ Wl xR ⟨(_A hq₁).2.1,(_A hq₁).2.2,(_A hq₂).2.1,(_A hq₂).2.2⟩
  have XS:({p₁,p₂}:_3 N).card≤2:=(_K _ _).trans (by simp);exact (_C vR).trans ((_J _ _).trans (by omega))
 let dP:=E₀.filter λ e=>∃(j:Fin J) (wa wb:ℕ),wa∈Mc.vI N C∧wb∈Mc.vI N C∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fa j) wa∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fb j) wb∧e.2∈vN I C ve wa∧2≤(vN I C ve wa).card∧(∃ Ux:_3 N,(2≤ Ux.card∨∃ u₀:Fin N,Ux={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Ux,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C wb)) e.1)∧(∃ Uy:_3 N,(2≤ Uy.card∨∃ u₀:Fin N,Uy={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Uy,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C wb)) e.1);let uo:=E₀.filter λ e=>∃(va ca:ℕ),(va,ca)∈M9.vm N C∧vZ I C va∧M9.vl N C (ofFn (λ q=>decide (q=e.1))) va ca∧vN I C ve ca={e.2}
 let kj:=E₀.filter λ e=>∃ u v:ℕ,_1 (vj I C) u v∧e.1∈j3 u∧2≤(vN I C ve u).card∧(vN I C ve v).card=1∧e.2∈vN I C ve v;let jG:=E₀.filter λ e=>∃(vb:ℕ),vZ I C vb∧(∃ c,M9.vl N C (ofFn (λ q=>decide (q=e.1))) vb c)∧vF I C ve fa fb vb={e.2};let bv:=E₀.filter λ e=>∃ j:Fin J,vN I C ve (fa j)={e.2}∧2≤(vF I C ve fa fb (fb j)).card∧e.1∈qe (fb j);let mV:=E₀.filter λ e=>∃ u v:ℕ,_1 (vj I C) u v∧e.1∈qe v∧(vF I C ve fa fb u).card=1∧e.2∈vF I C ve fa fb u∧2≤(vF I C ve fa fb v).card;have Z2:E₀⊆dP∪uo∪kj∪jG∪bv∪mV:=by
  intro⟨p,l⟩ he;obtain⟨wK,j,wa,wb,m7,kJ,z1,jn,⟨i,zN,Xb⟩,XL,Wo,R8⟩:=hE (p,l) he;obtain⟨Ux,Wu⟩:=XL;obtain⟨Uy,Wk⟩:=Wo;have dY:l∈vN I C ve wa:=by rw[uD I C ve wa m7];exact _B ⟨_H _,i,zN,Xb⟩
  have hwa_card_le2:(vN I C ve wa).card≤2:=by
   rw[uD I C ve wa m7];have Uj:univ.filter (λ l':Fin N=>∃ k:Fin 2,vk (vh N C) (vc I C) (vr N C (vd N C wa k))={l'}∧(l'∈vk (vh N C) (vc I C) (vr N C (vd N C wa (1-k)))∨13≤(ve (vr N C (vd N C wa (1-k)))\univ.filter λ q=>I q l').card))⊆((univ:Finset (Fin 2)).filter λ k=>(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C wa k))).card=1).biUnion
    λ k=>vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C wa k)):=by
    intro l' hl';obtain⟨k,P8,_⟩:=(_A hl').2;exact _F ⟨k,_B ⟨_H _,by rw[P8];simp⟩,by rw[P8];exact _I _⟩
   refine (_C Uj).trans ((_E _ _ 1 ?_).trans ?_)
   · intro k hk;exact le_of_eq (_A hk).2
   · have Tm:((univ:Finset (Fin 2)).filter λ k=>(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C wa k))).card=1).card≤2:=(card_filter_le _ _).trans (by simp);omega
  have gv':∀ u,_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (fa j) u→ p∈j3 u:=by
   intro u Zz;simp only[j3,mem_filter,_H,true_and];intro wk Xz;simp only[wC,mem_filter] at Xz;obtain⟨l',hl',Yk⟩:=Xz.2;rw[jF wk l' hl'];by_contra! uq;rcases ww I C (ofFn (λ q=>decide (q=p))) (fb j) wb jn with uS | ⟨vb,cb,hfb_vb,mT,_,hcb_wb⟩
   · exact uq.1 (wU wk.1 wk.2 l' hl' p uq.2 j wb kJ Ux Uy ⟨u,Zz,Yk⟩ ⟨wb,uS,.refl⟩ Wu Wk)
   · exact uq.1 (wU wk.1 wk.2 l' hl' p uq.2 j wb kJ Ux Uy ⟨u,Zz,Yk⟩ ⟨vb,hfb_vb,.head mT hcb_wb⟩ Wu Wk)
  have kG:∀ v,_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) v wb→ p∈qe v:=by intro v Xv;simp only[qe,mem_filter,_H,true_and];intro j' ⟨l',hj'⟩ RE;have hs:=nD j' l' hj';rw[hs.2.2];by_contra! uq;exact uq.1 (wU (gj j').1 (gj j').2 l' hs.1 p uq.2 j' wb kJ Ux Uy ⟨fa j',.refl,hs.2.1⟩ ⟨v,RE,Xv⟩ Wu Wk)
  by_cases Ul:2≤(vN I C ve wa).card
  · exact _D _ (_D _ (_D _ (_D _ (_D _ (_B ⟨he,j,wa,wb,m7,kJ,z1,jn,dY,Ul,⟨Ux,Wu⟩,⟨Uy,Wk⟩⟩)))))
  · have PV:(vN I C ve wa).card=1:=by
     have qX:0 < (vN I C ve wa).card:=card_pos.mpr ⟨l,dY⟩;omega
    rcases nf I C (ofFn (λ q=>decide (q=p))) (fa j) wa z1 with nS | ⟨va,ca,hfa_va,Z6,UA,hca_wa⟩
    ·
     have VU:l∈vN I C ve (fa j):=ff (fa j) wa nS dY;by_cases Mg:2≤(vN I C ve (fa j)).card
     ·
      exact _D _ (_D _ (_D _ (_G _ (_B ⟨he,fa j,wa,nS,gv' (fa j) .refl,Mg,PV,dY⟩))))
     · have Zn:vN I C ve (fa j)={l}:=by
        have qX:0 < (vN I C ve (fa j)).card:=card_pos.mpr ⟨l,VU⟩;obtain⟨x,hx⟩:=_x.mp (by omega:(vN I C ve (fa j)).card=1);rw[hx] at VU;rw[hx,_U VU]
       rcases ww I C (ofFn (λ q=>decide (q=p))) (fb j) wb jn with uS | ⟨vb,cb,hfb_vb,mT,Ub,hcb_wb⟩
       ·
        have Ur:l∈vF I C ve fa fb wb:=_B ⟨_H _,j,Zn,uS⟩;by_cases Lu:2≤(vF I C ve fa fb wb).card
        · by_cases UP:2≤(vF I C ve fa fb (fb j)).card
          · exact _D _ (_G _ (_B ⟨he,j,Zn,UP,kG (fb j) jn⟩))
          · have RP:(vF I C ve fa fb (fb j)).card=1:=by
             have ZH:l∈vF I C ve fa fb (fb j):=_B ⟨_H _,j,Zn,.refl⟩;have qX:0 < (vF I C ve fa fb (fb j)).card:=card_pos.mpr ⟨l,ZH⟩;omega
            have ZH:l∈vF I C ve fa fb (fb j):=_B ⟨_H _,j,Zn,.refl⟩;exact _G _ (_B ⟨he,fb j,wb,uS,kG wb .refl,RP,ZH,Lu⟩)
        · exfalso
          have N1:vF I C ve fa fb wb={l}:=by have qX:0 < (vF I C ve fa fb wb).card:=card_pos.mpr ⟨l,Ur⟩;obtain⟨x,hx⟩:=_x.mp (by omega:(vF I C ve fa fb wb).card=1);rw[hx] at Ur;rw[hx,_U Ur]
          obtain⟨ZR,Z3⟩:=R8 N1;exact wM I hI C fa fb hm vM ve vf j wa wb m7 kJ i l zN nS uS Xb ZR Z3
       ·
        have VY:l∈vF I C ve fa fb vb:=_B ⟨_H _,j,Zn,hfb_vb⟩;by_cases NO:2≤(vF I C ve fa fb vb).card
        · by_cases UP:2≤(vF I C ve fa fb (fb j)).card
          · exact _D _ (_G _ (_B ⟨he,j,Zn,UP,kG (fb j) jn⟩))
          · have ZH:l∈vF I C ve fa fb (fb j):=_B ⟨_H _,j,Zn,.refl⟩
            have RP:(vF I C ve fa fb (fb j)).card=1:=by have qX:=card_pos.mpr ⟨l,ZH⟩;omega
            exact _G _ (_B ⟨he,fb j,vb,hfb_vb,kG vb (.head mT hcb_wb),RP,ZH,NO⟩)
        · have VC:vF I C ve fa fb vb={l}:=by
           have qX:=card_pos.mpr ⟨l,VY⟩;obtain⟨x,hx⟩:=_x.mp (by omega:(vF I C ve fa fb vb).card=1);rw[hx] at VY;rw[hx,_U VY]
          exact _D _ (_D _ (_G _ (_B ⟨he,vb,Ub,⟨cb,mT⟩,VC⟩)))
    ·
     have VT:l∈vN I C ve ca:=ff ca wa hca_wa dY;by_cases ND:2≤(vN I C ve ca).card
     · exact _D _ (_D _ (_D _ (_G _ (_B ⟨he,ca,wa,hca_wa,gv' ca (ReflTransGen.tail hfa_va Z6),ND,PV,dY⟩))))
     · have Uw:vN I C ve ca={l}:=by
        have qX:=card_pos.mpr ⟨l,VT⟩;obtain⟨x,hx⟩:=_x.mp (by omega:(vN I C ve ca).card=1);rw[hx] at VT;rw[hx,_U VT]
       exact _D _ (_D _ (_D _ (_D _ (_G _ (_B ⟨he,va,ca,Z6.1,UA,Z6,Uw⟩)))))
 have h1:dP.card≤6*(Mc.vI N C).card:=by
  let F:=Mc.vI N C;have vR:dP⊆F.biUnion λ wa=>if 2≤(vN I C ve wa).card then (j3 wa).biUnion λ p=>(vN I C ve wa).image λ l=>(p,l) else ∅:=by
   intro⟨p,l⟩ he;obtain⟨Td,j,wa,wb,m7,kJ,z1,jn,dY,Ul,XL,Wo⟩:=_A he;obtain⟨Ux,Wu⟩:=XL;obtain⟨Uy,Wk⟩:=Wo;have NH:p∈j3 wa:=by
    simp only[j3,mem_filter,_H,true_and];intro wk Xz;simp only[wC,mem_filter] at Xz;obtain⟨l',hl',Yk⟩:=Xz.2;rw[jF wk l' hl'];by_contra! uq;rcases ww I C (ofFn (λ q=>decide (q=p))) (fb j) wb jn with uS | ⟨vb,cb,hfb_vb,mT,_,hcb_wb⟩
    · exact uq.1 (wU wk.1 wk.2 l' hl' p uq.2 j wb kJ Ux Uy ⟨wa,z1,Yk⟩ ⟨wb,uS,.refl⟩ Wu Wk)
    · exact uq.1 (wU wk.1 wk.2 l' hl' p uq.2 j wb kJ Ux Uy ⟨wa,z1,Yk⟩ ⟨vb,hfb_vb,.head mT hcb_wb⟩ Wu Wk)
   refine _F ⟨wa,m7,?_⟩
   rw[_O Ul];exact _F ⟨p,NH,_W ⟨l,dY,rfl⟩⟩
  refine (_C vR).trans ((_E F _ 6 ?_).trans (by rw[Nat.mul_comm]))
  intro wa m7;split_ifs with Ul
  · have Ns:(vN I C ve wa).card≤2:=by
     rw[uD I C ve wa m7];have Uj:univ.filter (λ l':Fin N=>∃ k:Fin 2,vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C wa k))={l'}∧(l'∈vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C wa (1-k)))∨13≤(ve (vr N C (vd N C wa (1-k)))\univ.filter λ q=>I q l').card))⊆((univ:Finset (Fin 2)).filter λ k=>(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C wa k))).card=1).biUnion
      λ k=>vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C wa k)):=by
      intro l' hl';obtain⟨k,P8,_⟩:=(_A hl').2;exact _F ⟨k,_B ⟨_H _,by rw[P8];simp⟩,by rw[P8];exact _I _⟩
     refine (_C Uj).trans ((_E _ _ 1 ?_).trans ?_)
     · intro k hk;exact le_of_eq (_A hk).2
     · have Tm:((univ:Finset (Fin 2)).filter λ k=>(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C wa k))).card=1).card≤2:=(card_filter_le _ _).trans (by simp);omega
    have h3:=d5 wa Ul;refine (_E (j3 wa) _ 2 ?_).trans (by nlinarith)
    intro p _;exact _T.trans Ns
  · simp
 have h2:uo.card≤8*(Mc.vP N C\Mc.vI N C).card:=by
  let Edges:=(M9.vm N C).toFinset;have vR:uo⊆Edges.biUnion λ edge=>if h:vZ I C edge.1∧(vN I C ve edge.2).card=1 then ((univ:_3 N).filter λ p=>p∈K7.vS C (h.1.choose)∧∀ l∈vN I C ve edge.2,I p l∧(p,l)∉v2 I C).biUnion λ p=>(vN I C ve edge.2).image λ l=>(p,l) else ∅:=by
   intro⟨p,l⟩ he;have Td:=(_A he).1;obtain⟨_,va,ca,R0,v4,xo,Uw⟩:=_A he;have zy:vZ I C va∧(vN I C ve ca).card=1:=⟨v4,by rw[Uw];simp⟩
   refine _F ⟨(va,ca),_v.mpr R0,?_⟩
   rw[_Q zy];have ZO:=zy.1.choose_spec;have z1:p∈K7.vS C zy.1.choose:=by rw[yQ];have xo':=xo.2;rw[M9.xK,ZO.1] at xo';simp only[Option.elim_some] at xo';change (C.wires (ofFn (λ q=>decide (q=p)) ++ replicate N false)).getD zy.1.choose false=true at xo';exact xo'
   refine _F ⟨p,_B ⟨_H _,z1,?_⟩,?_⟩
   · intro l' hl';rw[Uw] at hl';obtain rfl:=_U hl';exact⟨(hE (p,l') Td).1,z6 (p,l') Td⟩
   · exact _W ⟨l,by rw[Uw];exact _I _,rfl⟩
  refine (_C vR).trans ?_
  refine (_E Edges _ 4 ?_).trans ?_
  · intro edge _;split_ifs with h
    · have MO:((univ:_3 N).filter λ p=>p∈K7.vS C h.1.choose∧∀ l∈vN I C ve edge.2,I p l∧(p,l)∉v2 I C).card≤4:=by
       obtain⟨l₀,hl₀⟩:=_x.mp h.2;by_cases xR:((univ:_3 N).filter λ p=>p∈K7.vS C h.1.choose∧∀ l∈vN I C ve edge.2,I p l∧(p,l)∉v2 I C).Nonempty
       · obtain⟨p₀,hp₀⟩:=xR;have hp₀':=(_A hp₀).2;have hl₀_mem:l₀∈vN I C ve edge.2:=by rw[hl₀];exact _I _
         have bI:(C.lineDegrees (N+N) (Ico N (N+N))).getD h.1.choose 0≤1:=by have hz:=M9.zZ N C edge.1 h.1.choose h.1.choose_spec.1;change (C.lineDegrees (N+N) (Ico N (N+N))).getD h.1.choose 0=0 at hz;omega
         have h4:=y7 I C h.1.choose bI h.1.choose_spec.2 p₀ l₀
          (hp₀'.2 l₀ hl₀_mem).1 hp₀'.1 (hp₀'.2 l₀ hl₀_mem).2
         refine (_C ?_).trans h4
         intro q hq;have hq':=(_A hq).2;exact _B ⟨hq'.1,(hq'.2 l₀ hl₀_mem).1⟩
       · rw[_w.mp xR];simp
      refine (_E _ _ 1 ?_).trans (by omega)
      intro p _;exact _T.trans (by omega)
    · simp
  · have Uf:=xP (N:=N) C hm;nlinarith
 have h3:kj.card≤6*(Mc.vP N C\Mc.vI N C).card:=by
  refine pk C hm (vN I C ve) j3 (mw I C ve) XR d5 kj ?_
  intro e he;obtain⟨_,u,v,ZD,f4,U3,LS,MG⟩:=_A he;exact⟨u,v,ZD,f4,U3,LS,MG⟩
 have h4:jG.card≤4*(Mc.vP N C\Mc.vI N C).card:=by
  let NF:=Mc.vP N C\Mc.vI N C;have vR:jG⊆NF.biUnion λ vb=>if h:vZ I C vb∧(vF I C ve fa fb vb).card=1 then ((univ:_3 N).filter λ p=>p∈K7.vS C h.1.choose∧∀ l∈vF I C ve fa fb vb,I p l∧(p,l)∉v2 I C).biUnion λ p=>(vF I C ve fa fb vb).image λ l=>(p,l) else ∅:=by
   intro⟨p,l⟩ he;have Td:=(_A he).1;obtain⟨_,vb,v4,⟨cb,xo⟩,VC⟩:=_A he;have ZO:=v4.choose_spec;have SE:vb∈NF:=zd C vb v4.choose ZO.1;have zy:vZ I C vb∧(vF I C ve fa fb vb).card=1:=⟨v4,by rw[VC];simp⟩
   refine _F ⟨vb,SE,?_⟩
   rw[_Q zy];have z1:p∈K7.vS C zy.1.choose:=by rw[yQ];have xo':=xo.2;rw[M9.xK,zy.1.choose_spec.1] at xo';simp only[Option.elim_some] at xo';exact xo'
   refine _F ⟨p,_B ⟨_H _,z1,?_⟩,?_⟩
   · intro l' hl';rw[VC] at hl';obtain rfl:=_U hl';exact⟨(hE (p,l') Td).1,z6 (p,l') Td⟩
   · exact _W ⟨l,by rw[VC];exact _I _,rfl⟩
  refine (_C vR).trans ?_
  refine (_E NF _ 4 ?_).trans (by rw[Nat.mul_comm])
  intro vb _;split_ifs with h
  · have MO:((univ:_3 N).filter λ p=>p∈K7.vS C h.1.choose∧∀ l∈vF I C ve fa fb vb,I p l∧(p,l)∉v2 I C).card≤4:=by
     obtain⟨l₀,hl₀⟩:=_x.mp h.2;by_cases xR:((univ:_3 N).filter λ p=>p∈K7.vS C h.1.choose∧∀ l∈vF I C ve fa fb vb,I p l∧(p,l)∉v2 I C).Nonempty
     · obtain⟨p₀,hp₀⟩:=xR;have hp₀':=(_A hp₀).2;have hl₀_mem:l₀∈vF I C ve fa fb vb:=by rw[hl₀];exact _I _
       have bI:(C.lineDegrees (N+N) (Ico N (N+N))).getD h.1.choose 0≤1:=by have hz:=M9.zZ N C vb h.1.choose h.1.choose_spec.1;change (C.lineDegrees (N+N) (Ico N (N+N))).getD h.1.choose 0=0 at hz;omega
       have h4:=y7 I C h.1.choose bI h.1.choose_spec.2 p₀ l₀
        (hp₀'.2 l₀ hl₀_mem).1 hp₀'.1 (hp₀'.2 l₀ hl₀_mem).2
       refine (_C ?_).trans h4
       intro q hq;have hq':=(_A hq).2;exact _B ⟨hq'.1,(hq'.2 l₀ hl₀_mem).1⟩
     · rw[_w.mp xR];simp
    refine (_E _ _ 1 ?_).trans (by omega)
    intro p _;exact _T.trans (by omega)
  · simp
 have h5:bv.card≤3*J:=by
  have vR:bv⊆(univ:Finset (Fin J)).biUnion λ j=>if (vN I C ve (fa j)).card=1∧2≤(vF I C ve fa fb (fb j)).card then (qe (fb j)).biUnion λ p=>(vN I C ve (fa j)).image λ l=>(p,l) else ∅:=by
   intro⟨p,l⟩ he;obtain⟨_,j,Zn,UP,No⟩:=_A he;refine _F ⟨j,_H _,?_⟩
   rw[_O ⟨by rw[Zn];simp,UP⟩]
   exact _F ⟨p,No,_W ⟨l,by rw[Zn];exact _I _,rfl⟩⟩
  refine (_C vR).trans ?_
  refine (_E (univ:Finset (Fin J)) _ 3 ?_).trans ?_
  · intro j _;split_ifs with zy
    · have h3:=dQ (fb j) zy.2;refine (_E (qe (fb j)) _ 1 ?_).trans (by nlinarith)
      intro p _;exact _T.trans (by omega)
    · simp
  · simp[Nat.mul_comm]
 have h6:mV.card≤6*(Mc.vP N C\Mc.vI N C).card:=by
  refine nv C hm (vF I C ve fa fb) qe (bY I C ve fa fb) Wj dQ mV ?_
  intro e he;obtain⟨_,u,v,ZD,SF,O1,XA,LO⟩:=_A he;exact⟨u,v,ZD,SF,O1,XA,LO⟩
 have Xt:=_C Z2;have Y9:=_J (dP∪uo∪kj∪jG∪bv) mV;have LF:=_J (dP∪uo∪kj∪jG) bv;have hu4:=_J (dP∪uo∪kj) jG;have hu5:=_J (dP∪uo) kj;have QN:=_J dP uo;omega
private lemma hX {α:Type*} [_5 α] (s:Finset α) (p:α→ Prop) [DecidablePred p]:(s.filter p).card+(s.filter λ x=>¬ p x).card=s.card:=by rw[← card_union_of_disjoint (Finset.disjoint_filter.mpr λ _ _ hx Jy=>Jy hx)];congr 1;ext x;by_cases h:p x <;> simp[h]
lemma mc {J N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (fa jb) false=true→(C.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q)
 (Yp:_2 N)
 (z6:∀ e∈Yp,(e.1,e.2)∉v2 I C)
 (hE:∀ e∈Yp,I e.1 e.2∧∃(j:Fin J) (wa wb:ℕ),wa∈Mc.vI N C∧wb∈Mc.vI N C∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fa j) wa∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fb j) wb∧(∃ i:Fin 2,vk (vh N C) (vc I C) (vr N C (vd N C wa i))={e.2}∧(e.2∈vk (vh N C) (vc I C) (vr N C (vd N C wa (1-i)))∨13≤(ve (vr N C (vd N C wa (1-i)))\univ.filter λ q=>I q e.2).card))∧(∃ Ux:_3 N,(2≤ Ux.card∨∃ u₀:Fin N,Ux={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Ux,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C wb)) e.1)∧(∃ Uy:_3 N,(2≤ Uy.card∨∃ u₀:Fin N,Uy={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Uy,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C wb)) e.1)∧
  (vF I C ve fa fb wb={e.2}→(e.2∈vk (vh N C) (vc I C) (vr N C (vD N C wb))∨13≤(ve (vr N C (vD N C wb))\univ.filter λ q=>I q e.2).card)∧(e.2∈vk (vh N C) (vc I C) (vr N C (vz N C wb))∨13≤(ve (vr N C (vz N C wb))\univ.filter λ q=>I q e.2).card))):
 Yp.card≤6*(Mc.vI N C).card+24*(Mc.vP N C\Mc.vI N C).card+3*J:=by
 classical
 refine pX I hI C fa fb hm vM ve vf Yp z6 ?_
 intro e he;obtain⟨wK,j,wa,wb,m7,kJ,z1,jn,hi,U4,MQ,R8⟩:=hE e he;refine⟨wK,j,wa,wb,m7,kJ,z1,jn,hi,U4,MQ,R8⟩
end E3OneSide
section E3Final
open Ma
open M2 Kd
open M1 Kb
open Kc K7
open K1
private lemma uC {N:ℕ} (I:_0 N) [_4 I] (C:_a) (hm:_b C) (p l:Fin N) (r:ℕ) (qc:r∈Ico N (N+(vh N C).length)→2≤(vk (N:=N) (vh N C) (vc I C) r).card→ l∈vk (N:=N) (vh N C) (vc I C) r→¬ ∀ u∈vk (N:=N) (vh N C) (vc I C) r,I p u) (hl:l∈vk (N:=N) (vh N C) (vc I C) r) (xR:vk (N:=N) (vh N C) (vc I C) r≠{l}):∃ u:Fin N,¬ I p u∧u∈v9 (vh N C) (vi I C) r p:=by
 have h2:2≤(vk (N:=N) (vh N C) (vc I C) r).card:=by
  have qX:0 < (vk (N:=N) (vh N C) (vc I C) r).card:=card_pos.mpr ⟨l,hl⟩;by_contra! Pl;have h1:(vk (N:=N) (vh N C) (vc I C) r).card=1:=by omega
  obtain⟨u,hu⟩:=_x.mp h1;rw[hu,mem_singleton] at hl;exact xR (by rw[hu,hl])
 have Qr:r∈Ico N (N+(vh N C).length):=by
  by_contra hr_not;rw[mem_Ico,not_and,not_lt] at hr_not;by_cases z5:r < N
  · have hq:vk (N:=N) (vh N C) (vc I C) r={⟨r,z5⟩}:=by
     change vX (vh N C) (vc I C) r=_;exact kU (vh N C) (vc I C) ⟨r,z5⟩
    rw[hq] at h2;simp at h2
  · have cX:N+(vh N C).length≤ r:=hr_not (by omega)
    have hq:vk (N:=N) (vh N C) (vc I C) r=∅:=by change vX (vh N C) (vc I C) r=∅;exact wV (vh N C) (vc I C) r cX
    rw[hq] at h2;simp at h2
 have Xs:=qc Qr h2 hl;push Not at Xs;obtain⟨u,TP,Vd⟩:=Xs;refine⟨u,Vd,zm (vh N C) (vc I C) (vi I C) ?_ r p TP⟩
 intro a x ha;classical
 by_cases v4:zk I (Z C) a
 · have MH:Z (N:=N) C a (λ _=>false)=true:=by
    have Zc:vc I C a=Z (N:=N) C a (λ _=>false):=by unfold vc vi vO;rw[_O v4]
    rw[Zc] at ha;exact ha
   exact uO I (Z C) a x (wm C hm a (λ _=>false) x (λ _ h=>False.elim (Bool.noConfusion h)) MH)
 · unfold vi vO;rw[if_neg v4]
private lemma u7 {N:ℕ} (I:_0 N) [_4 I] (C:_a) (hm:_b C) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (p l:Fin N) (wK:I p l) (yM:∀ r,l∈v9 (vh N C) (vi I C) r p→ l∉vk (N:=N) (vh N C) (vc I C) r→ p∈ve r) (qc:∀ r,r∈Ico N (N+(vh N C).length)→2≤(vk (N:=N) (vh N C) (vc I C) r).card→ l∈vk (N:=N) (vh N C) (vc I C) r→
 ¬ ∀ u∈vk (N:=N) (vh N C) (vc I C) r,I p u)
 (r:ℕ)
 (Js:l∈v9 (vh N C) (vi I C) r p):
 vk (N:=N) (vh N C) (vc I C) r={l}∨∃ u:Fin N,¬ I p u∧u∈v9 (vh N C) (vi I C) r p:=by
 by_cases WR:vk (N:=N) (vh N C) (vc I C) r={l}
 · exact Or.inl WR
 · right
   by_cases yi:l∈vk (N:=N) (vh N C) (vc I C) r
   · exact uC I C hm p l r (qc r) yi WR
   · have XT:p∈ve r:=yM r Js yi;obtain⟨g,_,_,h8,x9,vR⟩:=vf r p XT;let B:=vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)
     have wr:∃ u∈B,¬ I p u:=by
      by_contra hnone;push Not at hnone;apply x9
      refine⟨⟨{p},by simp,λ u hu=>_F ⟨p,_I _,_B ⟨_H _,hnone u hu⟩⟩⟩,?_⟩
      rw[filter_eq_self.mpr λ u hu=>hnone u hu];dsimp only[B];omega
     obtain⟨u,Zu,Vd⟩:=wr;exact⟨u,Vd,vR Zu⟩
private lemma uH {J N:ℕ} (I:_0 N) [_4 I] (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (fa jb) false=true→(C.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (p l:Fin N) (wK:I p l)
 (yM:∀ r,l∈v9 (vh N C) (vi I C) r p→ l∉vk (N:=N) (vh N C) (vc I C) r→ p∈ve r)
 (qc:∀ r,r∈Ico N (N+(vh N C).length)→2≤(vk (N:=N) (vh N C) (vc I C) r).card→ l∈vk (N:=N) (vh N C) (vc I C) r→¬ ∀ u∈vk (N:=N) (vh N C) (vc I C) r,I p u)
 (j:Fin J) (wa ua va wb xb yb:ℕ)
 (z1:_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (fa j) wa)
 (jn:_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (fb j) wb)
 (m6:M9.y3 N C wa ua va)
 (m9:M9.y3 N C wb xb yb)
 (ZZ:l∈v9 (vh N C) (vi I C) (vr N C ua) p)
 (YF:l∈v9 (vh N C) (vi I C) (vr N C va) p)
 (Z5:l∈v9 (vh N C) (vi I C) (vr N C xb) p)
 (ZU:l∈v9 (vh N C) (vi I C) (vr N C yb) p):
 vk (N:=N) (vh N C) (vc I C) (vr N C ua)={l}∨vk (N:=N) (vh N C) (vc I C) (vr N C va)={l}∨vk (N:=N) (vh N C) (vc I C) (vr N C xb)={l}∨vk (N:=N) (vh N C) (vc I C) (vr N C yb)={l}:=by
 classical
 by_contra hnone;push Not at hnone;obtain⟨h1,h2,h3,h4⟩:=hnone;have OW:=u7 I C hm ve vf
  p l wK yM qc
 obtain⟨u₁,S8,hr1⟩:=(OW (vr N C ua) ZZ).resolve_left h1;obtain⟨u₂,R7,WA⟩:=(OW (vr N C va) YF).resolve_left h2;obtain⟨u₃,hn3,hr3⟩:=(OW (vr N C xb) Z5).resolve_left h3;obtain⟨u₄,hn4,hr4⟩:=(OW (vr N C yb) ZU).resolve_left h4;let S:_3 N:={u₁,u₂,u₃,u₄};have wh:S.card≤4:=by refine (_K _ _).trans (_n ((_K _ _).trans (_n ((_K _ _).trans (by simp)))))
 let x:Fin N→ Bool:=λ q=>decide (q=p) || vB I S q;let y:Fin N→ Bool:=λ w=>decide (w∈S);have PO:x p=true:=by simp[x]
 have Xe:∀ q,vB I S q=true→ x q=true:=by intro q hq;simp[x,hq]
 have QQ:∀ q,decide (q=p)=true→ x q=true:=by intro q hq;simp[x,hq]
 have TZ:=y8 C hm _ x QQ _ _ z1;have TS:=y8 C hm _ x QQ _ _ jn;have ZK:=λ r u hr Vb=>yI I C hm S wh x y Xe r p u hr PO (decide_eq_true Vb);have gy:=ZK (vr N C ua) u₁ hr1 (_S _ _);have WT:=ZK (vr N C va) u₂ WA (_L (_S _ _));have ZR:=ZK (vr N C xb) u₃ hr3
  (_L (_L (_S _ _)))
 have Z3:=ZK (vr N C yb) u₄ hr4
  (_L (_L (_L (_I _))))
 obtain⟨pa,lb,jz,dS,Y2⟩:=zc I C fa fb hm vM j wa ua va wb xb yb m6 m9 x y TZ TS gy WT ZR Z3;have f7:lb∈S:=_o Y2;simp only[x,_r,decide_eq_true_eq] at dS;rcases dS with rfl | hm_pa
 · simp only[S,mem_insert,mem_singleton] at f7;rcases f7 with rfl | rfl | rfl | rfl
   · exact S8 jz
   · exact R7 jz
   · exact hn3 jz
   · exact hn4 jz
 · have qY:∀ u∈S,¬ I pa u:=by
    simpa only[vB,decide_eq_true_eq] using hm_pa
   exact qY lb f7 jz
private lemma mK {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (p l:Fin N) (yM:∀ r,l∈v9 (vh N C) (vi I C) r p→ l∉vk (N:=N) (vh N C) (vc I C) r→ p∈ve r) (w:ℕ) (QE:l∈v9 (vh N C) (vi I C) (vr N C w) p):l∈vk (N:=N) (vh N C) (vc I C) (vr N C w)∨∃ U:_3 N,(2≤ U.card∨∃ u₀:Fin N,U={u₀}∧∀ q:Fin N,¬ I q u₀)∧
 ∀ u∈U,¬ I p u∧u∈v9 (vh N C) (vi I C) (vr N C w) p:=by
 by_cases yi:l∈vk (N:=N) (vh N C) (vc I C) (vr N C w)
 · exact Or.inl yi
 · right
   have XT:p∈ve (vr N C w):=yM (vr N C w) QE yi;obtain⟨g,_,_,h8,x9,vR⟩:=vf (vr N C w) p XT;let B:=vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g);let U:=B.filter λ u=>¬ I p u;by_cases h2:2≤ U.card
   · exact⟨U,Or.inl h2,λ u hu=>⟨(_A hu).2,vR (_A hu).1⟩⟩
   · have xR:U.Nonempty:=by
      by_contra Sh;rw[_w] at Sh;apply x9
      have Sv:B⊆pencil I p:=by
       intro u hu;refine _B ⟨_H _,?_⟩
       by_contra hn;have:u∈U:=_B ⟨hu,hn⟩;rw[Sh] at this;exact notMem_empty _ this
      refine⟨⟨{p},by simp,λ u hu=>_F ⟨p,_I _,Sv hu⟩⟩,?_⟩
      have NQ:B.filter (I p)=B:=filter_eq_self.mpr λ u hu=>(_A (Sv hu)).2;rw[NQ];dsimp only[B];omega
     obtain⟨u₀,hu₀⟩:=xR;have hu₀':=_A hu₀;have RI:∀ q:Fin N,¬ I q u₀:=by
      intro q b8;apply x9
      have Qj:U.card=1:=by have:0 < U.card:=card_pos.mpr ⟨u₀,hu₀⟩;omega
      have Lb:U={u₀}:=_x.mp Qj |>.elim λ x hx=>by rw[hx,mem_singleton] at hu₀;rw[hx,hu₀]
      refine⟨⟨{p,q},(_K _ _).trans (by simp),λ u hu=>?_⟩,?_⟩
      · by_cases f4:I p u
        · exact _F ⟨p,_S _ _,_B ⟨_H _,f4⟩⟩
        · have Th:u∈U:=_B ⟨hu,f4⟩;rw[Lb,mem_singleton] at Th;subst Th;exact _F ⟨q,_L (_I _),_B ⟨_H _,b8⟩⟩
      · have:(B.filter (I p)).card+U.card=B.card:=by
         dsimp only[U];exact hX B (I p)
        dsimp only[B] at this;omega
     exact⟨{u₀},Or.inr ⟨u₀,rfl,RI⟩,λ u hu=>by rw[_U hu];exact⟨hu₀'.2,vR hu₀'.1⟩⟩
lemma Uh {J N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (qZ:∀ jd,(C.lineDegrees (N+N) (Ico N (N+N))).getD (fa jd) 0≤2) (gP:∀ jd,(C.lineDegrees (N+N) (Ico N (N+N))).getD (fb jd) 0≤2) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (fa jb) false=true→(C.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧
 4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q)
 (E₃:_2 N)
 (z6:∀ e∈E₃,(e.1,e.2)∉v2 I C)
 (yM:∀ p l r,(p,l)∈E₃→ I p l→ l∈v9 (vh N C) (vi I C) r p→ l∉vk (N:=N) (vh N C) (vc I C) r→ p∈ve r)
 (qc:∀ p l r,(p,l)∈E₃→ r∈Ico N (N+(vh N C).length)→2≤(vk (N:=N) (vh N C) (vc I C) r).card→ l∈vk (N:=N) (vh N C) (vc I C) r→¬ ∀ u∈vk (N:=N) (vh N C) (vc I C) r,I p u)
 (WZ:∀(K:ℕ) (root:Fin K→ ℕ) (line:Fin K→ Fin N),(∀ j:Fin K,((ve (root j)).filter λ q=>¬ I q (line j)).card≤12)→∀ qj:_2 N,qj⊆E₃→(∀ e∈qj,∃ j:Fin K,e.2=line j∧e.1∈ve (root j))→ qj.card≤50*(1+M1.vA N 1 C.gates+M1.vA N 2 C.gates)+25*K)
 (hE₃:∀ e∈E₃,gS (N:=N) I C fa fb e.1 e.2)
 (XK:∀ k4:_2 N,k4⊆E₃→(∀ e∈k4,¬(I e.1 e.2∧∃(j:Fin J) (wa wb:ℕ),wa∈Mc.vI N C∧wb∈Mc.vI N C∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fa j) wa∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fb j) wb∧(∃ i:Fin 2,vk (vh N C) (vc I C) (vr N C (vd N C wa i))={e.2}∧(e.2∈vk (vh N C) (vc I C) (vr N C (vd N C wa (1-i)))∨13≤(ve (vr N C (vd N C wa (1-i)))\univ.filter λ q=>I q e.2).card))∧(∃ Ux:_3 N,(2≤ Ux.card∨∃ u₀:Fin N,Ux={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Ux,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C wb)) e.1)∧(∃ Uy:_3 N,(2≤ Uy.card∨∃ u₀:Fin N,Uy={u₀}∧∀ q:Fin N,¬ I q u₀)∧
  ∀ u∈Uy,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C wb)) e.1)∧(vF I C ve fa fb wb={e.2}→(e.2∈vk (vh N C) (vc I C) (vr N C (vD N C wb))∨13≤(ve (vr N C (vD N C wb))\univ.filter λ q=>I q e.2).card)∧(e.2∈vk (vh N C) (vc I C) (vr N C (vz N C wb))∨13≤(ve (vr N C (vz N C wb))\univ.filter λ q=>I q e.2).card))))→(∀ e∈k4,¬(I e.1 e.2∧∃(j:Fin J) (wb wa:ℕ),wb∈Mc.vI N C∧wa∈Mc.vI N C∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fb j) wb∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fa j) wa∧(∃ i:Fin 2,vk (vh N C) (vc I C) (vr N C (vd N C wb i))={e.2}∧(e.2∈vk (vh N C) (vc I C) (vr N C (vd N C wb (1-i)))∨
   13≤(ve (vr N C (vd N C wb (1-i)))\univ.filter λ q=>I q e.2).card))∧(∃ Ux:_3 N,(2≤ Ux.card∨∃ u₀:Fin N,Ux={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Ux,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C wa)) e.1)∧(∃ Uy:_3 N,(2≤ Uy.card∨∃ u₀:Fin N,Uy={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Uy,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C wa)) e.1)∧(vF I C ve fb fa wa={e.2}→(e.2∈vk (vh N C) (vc I C) (vr N C (vD N C wa))∨13≤(ve (vr N C (vD N C wa))\univ.filter λ q=>I q e.2).card)∧(e.2∈vk (vh N C) (vc I C) (vr N C (vz N C wa))∨13≤(ve (vr N C (vz N C wa))\univ.filter λ q=>I q e.2).card))))→(∀ e∈k4,I e.1 e.2→∀ w∈Mc.vI N C,∀ i:Fin 2,e.2∈vk (vh N C) (vc I C) (vr N C (vd N C w i))→
  (vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C w i))).card≤3→ e.2∈v9 (vh N C) (vi I C) (vr N C (vd N C w (1-i))) e.1→ e.2∈vk (vh N C) (vc I C) (vr N C (vd N C w (1-i)))∨13≤(ve (vr N C (vd N C w (1-i)))\univ.filter λ q=>I q e.2).card)→(∀ e∈k4,I e.1 e.2→∀(t:Fin 3),t=1∨t=2→∀(ga gb:Fin J→ ℕ),(t=1→ ga=fa∧gb=fb)→(t=2→ ga=fb∧gb=fa)→∀ wb∈Mc.vI N C,e.2∈v9 (vh N C) (vi I C) (vr N C (vD N C wb)) e.1→ e.2∈v9 (vh N C) (vi I C) (vr N C (vz N C wb)) e.1→ vF I C ve ga gb wb={e.2}→(e.2∈vk (vh N C) (vc I C) (vr N C (vD N C wb))∨13≤(ve (vr N C (vD N C wb))\univ.filter λ q=>I q e.2).card)∧(e.2∈vk (vh N C) (vc I C) (vr N C (vz N C wb))∨
   13≤(ve (vr N C (vz N C wb))\univ.filter λ q=>I q e.2).card))→ k4.card≤6*M1.vA N 1 C.gates+42*(Mc.vI N C).card+106*(Mc.vP N C\Mc.vI N C).card+90*J):
 E₃.card≤56*M1.vA N 1 C.gates+224*(Mc.vI N C).card+204*(Mc.vP N C\Mc.vI N C).card+96*J+50:=by
 classical
 let F:=Mc.vI N C;let u2:=F×ˢ (univ:Finset (Fin 2));let pS:ℕ× Fin 2→ ℕ:=λ wc=>vr N C (vd N C wc.1 wc.2);let kA:ℕ× Fin 2→ ℕ:=λ wc=>vr N C (vd N C wc.1 (1-wc.2));let XQ:ℕ× Fin 2→_3 N:=λ wc=>(if (vk (N:=N) (vh N C) (vc I C) (kA wc)).card≤3 then
  vk (N:=N) (vh N C) (vc I C) (kA wc) else ∅)∪(if (vF I C ve fa fb wc.1).card=1 then vF I C ve fa fb wc.1 else ∅)∪(if (vF I C ve fb fa wc.1).card=1 then vF I C ve fb fa wc.1 else ∅)
 have Tg:∀ wc,(XQ wc).card≤5:=by
  intro wc;have h1:(if (vk (N:=N) (vh N C) (vc I C) (kA wc)).card≤3 then
   vk (N:=N) (vh N C) (vc I C) (kA wc) else ∅).card≤3:=by
   split_ifs with h <;> simp[h]
  have h2:(if (vF I C ve fa fb wc.1).card=1 then vF I C ve fa fb wc.1 else ∅).card≤1:=by split_ifs with h <;> simp[h]
  have h3:(if (vF I C ve fb fa wc.1).card=1 then vF I C ve fb fa wc.1 else ∅).card≤1:=by split_ifs with h <;> simp[h]
  have Xt:=_J
   ((if (vk (N:=N) (vh N C) (vc I C) (kA wc)).card≤3 then vk (N:=N) (vh N C) (vc I C) (kA wc) else ∅)∪(if (vF I C ve fa fb wc.1).card=1 then vF I C ve fa fb wc.1 else ∅))
   (if (vF I C ve fb fa wc.1).card=1 then vF I C ve fb fa wc.1 else ∅)
  have Y9:=_J
   (if (vk (N:=N) (vh N C) (vc I C) (kA wc)).card≤3 then vk (N:=N) (vh N C) (vc I C) (kA wc) else ∅)
   (if (vF I C ve fa fb wc.1).card=1 then vF I C ve fa fb wc.1 else ∅)
  dsimp only[XQ];omega
 let mB:=u2.filter λ wc=>26≤(ve (pS wc)).card∧∃ l:Fin N,((ve (pS wc)).filter λ q=>¬ I q l).card≤12;let K:=mB.card;let fo:=mB.toList;have y5:fo.length=K:=length_toList mB;let root:Fin K→ ℕ:=λ k=>pS (fo[k.1]'(by rw[y5];exact k.2))
 let Xn:∀ k:Fin K,∃ l:Fin N,((ve (root k)).filter λ q=>¬ I q l).card≤12:=by
  intro k;have yH:fo[k.1]'(by rw[y5];exact k.2)∈mB:=mem_toList.mp (List.getElem_mem (by rw[y5];exact k.2))
  exact (_A yH).2.2
 let line:Fin K→ Fin N:=λ k=>(Xn k).choose;have xH:∀ k:Fin K,((ve (root k)).filter λ q=>¬ I q (line k)).card≤12:=λ k=>(Xn k).choose_spec;let f0:=E₃.filter λ e=>∃ k:Fin K,e.2=line k∧e.1∈ve (root k);have hK_le:K≤2*F.card:=by
  have h1:K≤ u2.card:=card_filter_le u2 _;have hU:u2.card=F.card*2:=by simp[u2,_m]
  omega
 have hns_big_bound:f0.card≤50*(1+M1.vA N 1 C.gates+M1.vA N 2 C.gates)+25*K:=WZ K root line xH f0 (filter_subset _ _)
  (λ _ he=>(_A he).2)
 let pP:=E₃.filter λ e=>∃ wc∈u2,(ve (pS wc)).card≤25∧e.1∈ve (pS wc)∧e.2∈XQ wc;have W1:∀ P L:_3 N,P.card≤25→ L.card≤5→((P×ˢ L).filter λ e=>I e.1 e.2).card≤35:=by
  intro P L hP25 hL5;let S:=(P×ˢ L).filter λ e=>I e.1 e.2;let Zx:=S.filter λ e=>∀ l₀∈L,I e.1 l₀→ e.2≤ l₀;let ZN:=S.filter λ e=>∃ l₀∈L,l₀ < e.2∧I e.1 l₀;have Ue:S⊆Zx∪ZN:=by
   intro⟨p,l⟩ he;by_cases hm:∀ l₀∈L,I p l₀→ l≤ l₀
   · exact _D _ (_B ⟨he,hm⟩)
   · push Not at hm;obtain⟨l₀,hl₀L,hpl₀,z5⟩:=hm;exact _G _ (_B ⟨he,l₀,hl₀L,z5,hpl₀⟩)
  have hmin_le:Zx.card≤ P.card:=by
   have vR:Zx⊆P.biUnion λ p=>if h:∃ l∈L,(p,l)∈Zx then {(p,h.choose)} else ∅:=by
    intro⟨p,l⟩ he;have RJ:=(_A he).1;have U1:=(_Y (_A RJ).1).1;have OO:=(_Y (_A RJ).1).2;have wr:∃ l'∈L,(p,l')∈Zx:=⟨l,OO,he⟩;have nk:l=wr.choose:=by
     have h1:=(_A he).2 wr.choose wr.choose_spec.1
      (_A (_A wr.choose_spec.2).1).2
     have h2:=(_A wr.choose_spec.2).2 l OO
      (_A RJ).2
     exact le_antisymm h1 h2
    refine _F ⟨p,U1,?_⟩
    rw[_Q wr,mem_singleton,nk]
   refine (_C vR).trans ((_E P _ 1 ?_).trans (by omega))
   intro p _;split_ifs <;> simp
  let LP:=(L×ˢ L).filter λ ab=>ab.1 < ab.2;have hLP_le:LP.card≤10:=by
   let cC:=LP.image Prod.swap;let Rk:=L.image λ a=>(a,a);have X8:Disjoint LP cC:=disjoint_left.mpr λ ⟨a,b⟩ h1 h2=>by
    have Li:=(_A h1).2;obtain⟨⟨c,d⟩,W9,Vt⟩:=mem_image.mp h2;have My:=(_A W9).2;simp only[Prod.swap,Prod.mk.injEq] at Vt;rcases Vt with ⟨rfl,rfl⟩
    exact lt_asymm Li My
   have R4:Disjoint (LP∪cC) Rk:=disjoint_left.mpr λ ⟨a,b⟩ h1 h2=>by
    obtain⟨c,_,hc⟩:=mem_image.mp h2;simp only[Prod.mk.injEq] at hc;rcases mem_union.mp h1 with Ou | Wx
    · have z5:=(_A Ou).2;rw[← hc.1,← hc.2] at z5;exact lt_irrefl _ z5
    · obtain⟨⟨c',d'⟩,W9,Vt⟩:=mem_image.mp Wx;have z5:=(_A W9).2;simp only[Prod.swap,Prod.mk.injEq] at Vt;rw[Vt.1,Vt.2,← hc.1,← hc.2] at z5;exact lt_irrefl _ z5
   have vR:LP∪cC∪Rk⊆L×ˢ L:=by
    intro⟨a,b⟩ h;rcases mem_union.mp h with W8 | h3
    · rcases mem_union.mp W8 with h1 | h2
      · exact (_A h1).1
      · obtain⟨⟨c,d⟩,W9,Vt⟩:=mem_image.mp h2;have yH:=_Y (_A W9).1;simp only[Prod.swap,Prod.mk.injEq] at Vt;exact _R ⟨by rw[← Vt.1];exact yH.2,by rw[← Vt.2];exact yH.1⟩
    · obtain⟨c,hc,Lj⟩:=mem_image.mp h3;simp only[Prod.mk.injEq] at Lj;exact _R ⟨by rw[← Lj.1];exact hc,by rw[← Lj.2];exact hc⟩
   have bT:=_C vR;rw[card_union_of_disjoint R4,card_union_of_disjoint X8,_m] at bT;have P7:cC.card=LP.card:=_l LP Prod.swap_injective;have Tf:Rk.card=L.card:=_l L λ _ _ h=>(Prod.mk.inj h).1;rw[P7,Tf] at bT;by_cases h5:L.card=5
   · rw[h5] at bT;omega
   · have h4:L.card≤4:=by omega
     have Jj:L.card*L.card≤16:=by nlinarith
     omega
  have hrest_le:ZN.card≤ LP.card:=by
   have vR:ZN⊆LP.biUnion λ ab=>if h:∃ p∈P,I p ab.1∧I p ab.2 then {(h.choose,ab.2)} else ∅:=by
    intro⟨p,l⟩ he;obtain⟨RJ,l₀,hl₀L,z5,hpl₀⟩:=_A he;have U1:=(_Y (_A RJ).1).1;have OO:=(_Y (_A RJ).1).2;have bd:=(_A RJ).2;have MI:(l₀,l)∈LP:=_B ⟨_R ⟨hl₀L,OO⟩,z5⟩;have wr:∃ p'∈P,I p' l₀∧I p' l:=⟨p,U1,hpl₀,bd⟩;have nk:p=wr.choose:=by by_contra xR;exact hI p wr.choose l₀ l xR (ne_of_lt z5) ⟨hpl₀,bd,wr.choose_spec.2.1,wr.choose_spec.2.2⟩
    refine _F ⟨(l₀,l),MI,?_⟩
    rw[_Q wr,mem_singleton,nk]
   refine (_C vR).trans ((_E LP _ 1 ?_).trans (by omega))
   intro ab _;split_ifs <;> simp
  have SC:=_C Ue;have QL:=_J Zx ZN;dsimp only[S] at SC;omega
 have hns_small_bound:pP.card≤70*F.card:=by
  have vR:pP⊆u2.biUnion λ wc=>if (ve (pS wc)).card≤25 then ((ve (pS wc)×ˢ XQ wc).filter λ e=>I e.1 e.2) else ∅:=by
   intro⟨p,l⟩ he;have Le:=(_A he).1;obtain⟨wc,Jp,VM,cY,Y1⟩:=(_A he).2;refine _F ⟨wc,Jp,?_⟩
   rw[_O VM];exact _B ⟨_R ⟨cY,Y1⟩,(hE₃ (p,l) Le).1⟩
  refine (_C vR).trans ((_E u2 _ 35 ?_).trans ?_)
  · intro wc _;split_ifs with VM
    · exact W1 _ _ VM (Tg wc)
    · simp
  · have P0:u2.card=F.card*2:=by simp[u2,_m]
    rw[P0];omega
 let qj:=f0∪pP;have hns_bound:qj.card≤50*(1+M1.vA N 1 C.gates+M1.vA N 2 C.gates)+25*K+70*F.card:=by have QL:=_J f0 pP;dsimp only[qj];omega
 have WD:∀(p l:Fin N) (dm:(p,l)∈E₃) (w:ℕ) (hw:w∈F) (c:Fin 2) (cY:p∈ve (pS (w,c))) (Y1:l∈XQ (w,c)) (W8:((ve (pS (w,c))).filter λ q=>¬ I q l).card≤12),(p,l)∈qj:=by
  intro p l dm w hw c cY Y1 W8;have WB:(w,c)∈u2:=_R ⟨hw,_H _⟩;by_cases L1:26≤(ve (pS (w,c))).card
  · refine _D _ (_B ⟨dm,?_⟩)
    have bA:(w,c)∈mB:=_B ⟨WB,L1,l,W8⟩;obtain⟨PD,Pg,VV⟩:=mem_iff_getElem.mp (mem_toList.mpr bA);let k:Fin K:=⟨PD,by rw[← y5];exact Pg⟩
    have VV':fo[k.1]'(by rw[y5];exact k.2)=(w,c):=VV
    have YY:root k=pS (w,c):=by dsimp only[root];rw[VV']
    have hk12:((ve (pS (w,c))).filter λ q=>¬ I q (line k)).card≤12:=by simpa only[← YY] using xH k
    have bW:l=line k:=by
     by_contra xR;let S:=ve (pS (w,c));have Ue:S⊆(S.filter λ q=>¬ I q l)∪(S.filter λ q=>¬ I q (line k))∪(S.filter λ q=>I q l∧I q (line k)):=by
      intro q hq;by_cases ny:I q l
      · by_cases hqk:I q (line k)
        · exact _G _ (_B ⟨hq,ny,hqk⟩)
        · exact _D _ (_G _ (_B ⟨hq,hqk⟩))
      · exact _D _ (_D _ (_B ⟨hq,ny⟩))
     have p4:(S.filter λ q=>I q l∧I q (line k)).card≤1:=by by_contra! hgt;obtain⟨q₁,hq₁,q₂,hq₂,VJ⟩:=_Z hgt;obtain⟨_,Lp,Ms⟩:=_A hq₁;obtain⟨_,Nf,Nk⟩:=_A hq₂;exact hI q₁ q₂ l (line k) VJ xR ⟨Lp,Ms,Nf,Nk⟩
     have hc:=_C Ue;have Xt:=_J
      ((S.filter λ q=>¬ I q l)∪(S.filter λ q=>¬ I q (line k)))
      (S.filter λ q=>I q l∧I q (line k))
     have Y9:=_J
      (S.filter λ q=>¬ I q l) (S.filter λ q=>¬ I q (line k))
     dsimp only[S] at hc Xt Y9 p4;omega
    refine⟨k,bW,?_⟩
    rw[YY];exact cY
  · refine _G _ (_B ⟨dm,(w,c),WB,by omega,cY,Y1⟩)
 let uE:=E₃ \ qj;have wu:∀(p l:Fin N) (pV:(p,l)∉qj) (dm:(p,l)∈E₃) (wK:I p l) (w:ℕ) (hw:w∈F) (i:Fin 2) (Vk:l∈vk (vh N C) (vc I C) (vr N C (vd N C w i))) (ZX:(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C w i))).card≤3)
  (jV:l∈v9 (vh N C) (vi I C) (vr N C (vd N C w (1-i))) p),l∈vk (vh N C) (vc I C) (vr N C (vd N C w (1-i)))∨13≤(ve (vr N C (vd N C w (1-i)))\univ.filter λ q=>I q l).card:=by
  intro p l pV dm wK w hw i Vk ZX jV;by_cases hbo:l∈vk (vh N C) (vc I C) (vr N C (vd N C w (1-i)))
  · exact Or.inl hbo
  · right
    have XT:p∈ve (vr N C (vd N C w (1-i))):=yM p l _ dm wK jV hbo;by_contra! W8;apply pV
    have ZL:((ve (pS (w,1-i))).filter λ q=>¬ I q l).card≤12:=by
     have zD:(ve (pS (w,1-i))).filter (λ q=>¬ I q l)=ve (vr N C (vd N C w (1-i)))\univ.filter λ q=>I q l:=by ext q;simp[pS]
     rw[zD];omega
    have ZG:kA (w,1-i)=vr N C (vd N C w i):=by
     dsimp only[kA];have hi:(1-(1-i):Fin 2)=i:=by fin_cases i <;> decide
     rw[hi]
    have Y1:l∈XQ (w,1-i):=by
     refine _D _ (_D _ ?_)
     rw[_O (by rw[ZG];exact ZX),ZG]
     exact Vk
    exact WD p l dm w hw (1-i) XT Y1 ZL
 have hwa_cond:∀(p l:Fin N) (pV:(p,l)∉qj) (dm:(p,l)∈E₃) (wK:I p l) (w:ℕ) (hw:w∈F) (i:Fin 2) (yi:vk (vh N C) (vc I C) (vr N C (vd N C w i))={l}) (jV:l∈v9 (vh N C) (vi I C) (vr N C (vd N C w (1-i))) p),l∈vk (vh N C) (vc I C) (vr N C (vd N C w (1-i)))∨13≤(ve (vr N C (vd N C w (1-i)))\univ.filter λ q=>I q l).card:=by intro p l pV dm wK w hw i yi jV;exact wu p l pV dm wK w hw i (by rw[yi];exact _I _) (by rw[yi];simp) jV
 have pM:∀(t:Fin 3) (ht:t=1∨t=2) (ga gb:Fin J→ ℕ),(t=1→ ga=fa∧gb=fb)→(t=2→ ga=fb∧gb=fa)→∀(p l:Fin N),(p,l)∉qj→(p,l)∈E₃→ I p l→∀ wb∈F,l∈v9 (vh N C) (vi I C) (vr N C (vD N C wb)) p→ l∈v9 (vh N C) (vi I C) (vr N C (vz N C wb)) p→ vF I C ve ga gb wb={l}→(l∈vk (vh N C) (vc I C) (vr N C (vD N C wb))∨13≤(ve (vr N C (vD N C wb))\univ.filter λ q=>I q l).card)∧(l∈vk (vh N C) (vc I C) (vr N C (vz N C wb))∨13≤(ve (vr N C (vz N C wb))\univ.filter λ q=>I q l).card):=by
  intro t ht ga gb h1 h2 p l pV dm wK wb kJ QS PE Qz;have cZ:∀ Un:Fin 2,l∈v9 (vh N C) (vi I C) (vr N C (vd N C wb Un)) p→ l∈vk (vh N C) (vc I C) (vr N C (vd N C wb Un))∨13≤(ve (vr N C (vd N C wb Un))\univ.filter λ q=>I q l).card:=by
   intro Un qk;by_cases yi:l∈vk (vh N C) (vc I C) (vr N C (vd N C wb Un))
   · exact Or.inl yi
   · right
     have XT:p∈ve (vr N C (vd N C wb Un)):=yM p l _ dm wK qk yi;by_contra! W8;apply pV
     have ZL:((ve (pS (wb,Un))).filter λ q=>¬ I q l).card≤12:=by
      have zD:(ve (pS (wb,Un))).filter (λ q=>¬ I q l)=ve (vr N C (vd N C wb Un))\univ.filter λ q=>I q l:=by ext q;simp[pS]
      rw[zD];omega
     have Y1:l∈XQ (wb,Un):=by
      rcases ht with rfl | rfl
      · obtain⟨rfl,rfl⟩:=h1 rfl;refine _D _ (_G _ ?_)
        rw[_O (by rw[Qz];simp),Qz]
        exact _I _
      · obtain⟨rfl,rfl⟩:=h2 rfl;refine _G _ ?_
        rw[_O (by rw[Qz];simp),Qz]
        exact _I _
     exact WD p l dm wb kJ Un XT Y1 ZL
  exact⟨by simpa[vd] using cZ 0 (by simpa[vd] using QS),by simpa[vd] using cZ 1 (by simpa[vd] using PE)⟩
 let kH:=uE.filter λ e=>I e.1 e.2∧∃(j:Fin J) (wa wb:ℕ),wa∈Mc.vI N C∧wb∈Mc.vI N C∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fa j) wa∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fb j) wb∧(∃ i:Fin 2,vk (vh N C) (vc I C) (vr N C (vd N C wa i))={e.2}∧(e.2∈vk (vh N C) (vc I C) (vr N C (vd N C wa (1-i)))∨13≤(ve (vr N C (vd N C wa (1-i)))\univ.filter λ q=>I q e.2).card))∧(∃ Ux:_3 N,(2≤ Ux.card∨∃ u₀:Fin N,Ux={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Ux,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C wb)) e.1)∧(∃ Uy:_3 N,(2≤ Uy.card∨∃ u₀:Fin N,Uy={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Uy,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C wb)) e.1)∧
  (vF I C ve fa fb wb={e.2}→(e.2∈vk (vh N C) (vc I C) (vr N C (vD N C wb))∨13≤(ve (vr N C (vD N C wb))\univ.filter λ q=>I q e.2).card)∧(e.2∈vk (vh N C) (vc I C) (vr N C (vz N C wb))∨13≤(ve (vr N C (vz N C wb))\univ.filter λ q=>I q e.2).card))
 let kB:=uE.filter λ e=>I e.1 e.2∧∃(j:Fin J) (wb wa:ℕ),wb∈Mc.vI N C∧wa∈Mc.vI N C∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fb j) wb∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fa j) wa∧(∃ i:Fin 2,vk (vh N C) (vc I C) (vr N C (vd N C wb i))={e.2}∧(e.2∈vk (vh N C) (vc I C) (vr N C (vd N C wb (1-i)))∨13≤(ve (vr N C (vd N C wb (1-i)))\univ.filter λ q=>I q e.2).card))∧(∃ Ux:_3 N,(2≤ Ux.card∨∃ u₀:Fin N,Ux={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Ux,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C wa)) e.1)∧(∃ Uy:_3 N,(2≤ Uy.card∨∃ u₀:Fin N,Uy={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Uy,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C wa)) e.1)∧
  (vF I C ve fb fa wa={e.2}→(e.2∈vk (vh N C) (vc I C) (vr N C (vD N C wa))∨13≤(ve (vr N C (vD N C wa))\univ.filter λ q=>I q e.2).card)∧(e.2∈vk (vh N C) (vc I C) (vr N C (vz N C wa))∨13≤(ve (vr N C (vz N C wa))\univ.filter λ q=>I q e.2).card))
 let k4:=uE\(kH∪kB);have X6:uE⊆kH∪kB∪k4:=by
  intro e he;by_cases LE:e∈kH∪kB
  · exact _D _ LE
  · exact _G _ (_V ⟨he,LE⟩)
 have hsb_bound:k4.card≤6*M1.vA N 1 C.gates+42*F.card+106*(Mc.vP N C\F).card+90*J:=by
  refine XK k4 (λ e he=>(_M (_M he).1).1) (λ e he hA=>(_M he).2 (_D _ (_B ⟨(_M he).1,hA⟩))) (λ e he hB=>(_M he).2 (_G _ (_B ⟨(_M he).1,hB⟩))) (λ e he wK w hw i Vk ZX jV=>by
   have pw:=(_M he).1;exact wu e.1 e.2 (_M pw).2 (_M pw).1 wK w hw i Vk ZX jV)
   (λ e he wK t ht ga gb h1 h2 wb kJ LZ Pm Qz=>by have pw:=(_M he).1;exact pM t ht ga gb h1 h2 e.1 e.2 (_M pw).2 (_M pw).1 wK wb kJ LZ Pm Qz)
 have hsideA_bound:kH.card≤6*F.card+24*(Mc.vP N C\F).card+3*J:=mc I hI C fa fb hm vM ve vf kH
  (λ e he=>z6 e (_M (_A he).1).1)
  (λ e he=>(_A he).2)
 have X0:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (fb jb) false=true→(C.wires (ofFn zz)).getD (fa jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true:=λ jb zz hb ha=>vM jb zz ha hb;have hsideB_bound:kB.card≤6*F.card+24*(Mc.vP N C\F).card+3*J:=mc I hI C fb fa hm X0 ve vf kB
  (λ e he=>z6 e (_M (_A he).1).1)
  (λ e he=>(_A he).2)
 have Tv:E₃⊆qj∪(kH∪kB∪k4):=by
  intro e he;by_cases hns:e∈qj
  · exact _D _ hns
  · exact _G _ (X6 (_V ⟨he,hns⟩))
 have hcard_E3:E₃.card≤ qj.card+kH.card+kB.card+k4.card:=by have h1:=_C Tv;have h2:=_J qj (kH∪kB∪k4);have h3:=_J (kH∪kB) k4;have h4:=_J kH kB;omega
 have SA:M1.vA N 2 C.gates=(Mc.vP N C).card:=by rw[M1.zF N C];rfl
 have XU:F⊆Mc.vP N C:=Mc.yO N C;have cA:(Mc.vP N C).card=F.card+(Mc.vP N C\F).card:=by have h:=_z (Mc.vP N C) F;have hi:Mc.vP N C∩F=F:=inter_eq_right.mpr XU;rw[hi] at h;omega
 dsimp only[F] at *;omega
end E3Final
section RemHelper09
lemma jT {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (P L:_3 N) (bP bL pI:ℕ) (hP:P.card≤ bP) (hL:L.card≤ bL) (TQ:bP*(bL*(bL-1)+(pI+1)) < (pI+1) ^ 2):((P×ˢ L).filter λ e=>I e.1 e.2).card≤ pI:=by
 classical
 let d:Fin N→ ℕ:=λ p=>(L.filter λ l=>I p l).card;have Yy:((P×ˢ L).filter λ e=>I e.1 e.2).card=∑ p∈P,d p:=by
  have zD:(P×ˢ L).filter (λ e=>I e.1 e.2)=P.biUnion λ p=>(L.filter λ l=>I p l).image λ l=>(p,l):=by
   ext ⟨p,l⟩;simp only[mem_filter,mem_product,mem_biUnion,mem_image];constructor
   · rintro⟨⟨hp,hl⟩,wK⟩;exact⟨p,hp,l,⟨hl,wK⟩,rfl⟩
   · rintro⟨p',hp',l',⟨hl',wK'⟩,zA⟩;obtain⟨rfl,rfl⟩:=Prod.mk.inj zA;exact⟨⟨hp',hl'⟩,wK'⟩
  rw[zD,Finset.card_biUnion]
  · refine Finset.sum_congr rfl λ p _=>?_
    exact _l _ (λ a b h=>_9 Prod.snd h)
  · intro p₁ _ p₂ _ xR;dsimp only[Function.onFun];rw[disjoint_left];intro⟨a,b⟩ h1 h2;obtain⟨_,_,Xo⟩:=mem_image.mp h1;obtain⟨_,_,Xk⟩:=mem_image.mp h2;exact xR (_9 Prod.fst (Xo.trans Xk.symm))
 have Va:(P:Set (Fin N)).PairwiseDisjoint (λ p=>(L.filter λ l=>I p l).offDiag):=by intro p₁ _ p₂ _ xR;dsimp only[Function.onFun];rw[disjoint_left];intro⟨l₁,l₂⟩ h1 h2;obtain⟨Nj,Mo,Up⟩:=Finset.mem_offDiag.mp h1;obtain⟨Lf,MY,_⟩:=Finset.mem_offDiag.mp h2;exact hI p₁ p₂ l₁ l₂ xR Up ⟨(_A Nj).2,(_A Mo).2,(_A Lf).2,(_A MY).2⟩
 have UZ:P.biUnion (λ p=>(L.filter λ l=>I p l).offDiag)⊆L.offDiag:=by intro⟨l₁,l₂⟩ yH;obtain⟨p,_,hl⟩:=mem_biUnion.mp yH;obtain⟨Pm,MR,xR⟩:=Finset.mem_offDiag.mp hl;exact Finset.mem_offDiag.mpr ⟨(_A Pm).1,(_A MR).1,xR⟩
 have hoff_sum:∑ p∈P,d p*(d p-1)≤ bL*(bL-1):=by
  have ZA:∀ s:_3 N,s.offDiag.card=s.card*(s.card-1):=by
   intro s;rw[Finset.offDiag_card];cases s.card with
   | zero=>simp
   | succ k=>rw[Nat.mul_succ,Nat.add_sub_cancel];rfl
  have h1:=_C UZ;rw[Finset.card_biUnion Va,ZA L] at h1;have h2:∑ p∈P,(L.filter λ l=>I p l).offDiag.card=∑ p∈P,d p*(d p-1):=Finset.sum_congr rfl λ p _=>ZA _;have hLmul:L.card*(L.card-1)≤ bL*(bL-1):=Nat.mul_le_mul hL (Nat.sub_le_sub_right hL 1);omega
 have Jj:(∑ p∈P,d p) ^ 2≤ P.card * ∑ p∈P,(d p) ^ 2:=by
  have h2:2*(∑ p∈P,d p) ^ 2≤2*(P.card * ∑ p∈P,(d p) ^ 2):=by
   have Mx:2*(∑ p∈P,d p) ^ 2=∑ p∈P,∑ q∈P,(2*(d p*d q)):=by
    rw[sq,Finset.sum_mul_sum,Finset.mul_sum];refine Finset.sum_congr rfl λ p _=>?_
    rw[Finset.mul_sum]
   have Lc:2*(P.card * ∑ p∈P,(d p) ^ 2)=∑ p∈P,∑ q∈P,((d p) ^ 2+(d q) ^ 2):=by simp only[Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,← Finset.mul_sum];ring
   rw[Mx,Lc];refine sum_le_sum λ p _=>sum_le_sum λ q _=>?_
   zify
   nlinarith [sq_nonneg ((d p:ℤ)-(d q:ℤ))]
  omega
 have Q5:∑ p∈P,(d p) ^ 2≤ bL*(bL-1)+∑ p∈P,d p:=by
  have Mn:∀ p∈P,(d p) ^ 2=d p*(d p-1)+d p:=by
   intro p _;cases hdp:d p with
   | zero=>simp
   | succ k=>simp;ring
  rw[Finset.sum_congr rfl Mn,Finset.sum_add_distrib];omega
 have Mh:(∑ p∈P,d p) ^ 2≤ bP*(bL*(bL-1)+∑ p∈P,d p):=by have cX:P.card * ∑ p∈P,(d p) ^ 2≤ bP*(bL*(bL-1)+∑ p∈P,d p):=Nat.mul_le_mul hP Q5;omega
 rw[Yy];by_contra! hgt;let S:=∑ p∈P,d p;let K:=bL*(bL-1);have hS:pI+1≤ S:=hgt;have hbp_lt:bP < pI+1:=by
  by_contra! RN;have LQ:(pI+1)*(pI+1)≤ bP*(pI+1):=Nat.mul_le_mul_right (pI+1) RN;have LH:bP*(pI+1)≤ bP*(K+(pI+1)):=Nat.mul_le_mul_left bP (Nat.le_add_left _ _);have TQ':bP*(K+(pI+1)) < (pI+1)*(pI+1):=by simpa only[sq] using TQ
  omega
 let t:=S-(pI+1);have hS_eq:S=(pI+1)+t:=by omega
 have hsq_fin:S*S≤ bP*(K+S):=by simpa only[sq] using Mh
 have TQ':bP*(K+(pI+1)) < (pI+1)*(pI+1):=by simpa only[sq] using TQ
 nlinarith
lemma xL {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (P L:_3 N) (hP:P.card≤9) (hL:L.card≤6):((P×ˢ L).filter λ e=>I e.1 e.2).card≤21:=jT I hI P L 9 6 21 hP hL (by decide)
lemma pp {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (P L:_3 N) (hP:P.card≤12) (hL:L.card≤6):((P×ˢ L).filter λ e=>I e.1 e.2).card≤25:=jT I hI P L 12 6 25 hP hL (by decide)
lemma uY {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (L7:_3 N) (QF:L7.card=7) (yc:Fin N→_3 N) (fc:∀ la∈L7,(yc la).card≤3) (P:_3 N) (k0 Sq ZT:ℕ) (hk_sum:k0+Sq≤4) (RU:0 < k0) (hb_mul:21 < k0*(ZT+1)) (Rm:∀ p∈P,(L7.filter λ la=>¬ I p la∧p∉yc la).card≤ Sq):P.card≤ ZT+2:=by
 classical
 let kc:=P.filter λ p=>k0≤(L7.filter λ la=>p∈yc la).card;let ZI:=P.filter λ p=>(L7.filter λ la=>p∈yc la).card≤ k0-1;have hP_star:kc.card≤ ZT:=by
  let Tl:=(kc×ˢ L7).filter λ pl=>pl.1∈yc pl.2;have Oh:k0*kc.card≤ Tl.card:=by
   have vR:kc.biUnion (λ p=>(L7.filter λ la=>p∈yc la).image λ la=>(p,la))⊆Tl:=by intro⟨p,la⟩ yH;obtain⟨p',hp',yH'⟩:=mem_biUnion.mp yH;obtain⟨la',nF',zA⟩:=mem_image.mp yH';obtain⟨rfl,rfl⟩:=Prod.mk.inj zA;exact _B ⟨_R ⟨hp',(_A nF').1⟩,(_A nF').2⟩
   have fl:(kc:Set (Fin N)).PairwiseDisjoint (λ p=>(L7.filter λ la=>p∈yc la).image λ la=>(p,la)):=by intro p₁ _ p₂ _ xR;dsimp only[Function.onFun];rw[disjoint_left];intro⟨a,b⟩ h1 h2;obtain⟨_,_,Xo⟩:=mem_image.mp h1;obtain⟨_,_,Xk⟩:=mem_image.mp h2;exact xR (_9 Prod.fst (Xo.trans Xk.symm))
   have xV:=_C vR;rw[Finset.card_biUnion fl] at xV;have hsumk:k0*kc.card≤ ∑ p∈kc,((L7.filter λ la=>p∈yc la).image λ la=>(p,la)).card:=by
    calc k0*kc.card=∑ _p∈kc,k0:=by simp[Nat.mul_comm]
     _≤ ∑ p∈kc,((L7.filter λ la=>p∈yc la).image λ la=>(p,la)).card:=by
      refine sum_le_sum λ p hp=>?_
      rw[_l _ (λ a b h=>_9 Prod.snd h)];exact (_A hp).2
   omega
  have Og:Tl.card≤21:=by
   have vR:Tl⊆L7.biUnion λ la=>(yc la).image λ p=>(p,la):=by intro⟨p,la⟩ yH;obtain⟨zA,KI⟩:=_A yH;exact _F ⟨la,(_Y zA).2,_W ⟨p,KI,rfl⟩⟩
   refine (_C vR).trans ?_
   refine (_E L7 _ 3 ?_).trans (by rw[QF])
   intro la nF;exact _T.trans (fc la nF)
  have Q9:k0*kc.card < k0*(ZT+1):=by omega
  exact Nat.lt_succ_iff.mp ((Nat.mul_lt_mul_left RU).mp Q9)
 have hP_inc:ZI.card≤2:=by
  by_contra! h3;obtain⟨p1,Xo⟩:=card_pos.mp (by omega:0 < ZI.card);have h2:1 < (ZI.erase p1).card:=by rw[Finset.card_erase_of_mem Xo];omega
  obtain⟨p2,Oz,p3,Pw,PP⟩:=_Z h2;have Up:p1≠p2:=(Finset.ne_of_mem_erase Oz).symm;have P2:p1≠p3:=(Finset.ne_of_mem_erase Pw).symm;have Xk:=Finset.mem_of_mem_erase Oz;have KR:=Finset.mem_of_mem_erase Pw;have Vw:∀ p∈ZI,4≤(L7.filter λ la=>I p la).card:=by
   intro p hp;obtain⟨U1,Rb⟩:=_A hp;have h1:=Rm p U1;have vR:L7⊆(L7.filter λ la=>p∈yc la)∪(L7.filter λ la=>¬ I p la∧p∉yc la)∪(L7.filter λ la=>I p la):=by
    intro la nF;by_cases hs:p∈yc la
    · exact _D _ (_D _ (_B ⟨nF,hs⟩))
    · by_cases hi:I p la
      · exact _G _ (_B ⟨nF,hi⟩)
      · exact _D _ (_G _ (_B ⟨nF,hi,hs⟩))
   have hc:=_C vR;have Xt:=_J
    ((L7.filter λ la=>p∈yc la)∪(L7.filter λ la=>¬ I p la∧p∉yc la))
    (L7.filter λ la=>I p la)
   have Y9:=_J
    (L7.filter λ la=>p∈yc la) (L7.filter λ la=>¬ I p la∧p∉yc la)
   omega
  have Yt:∀ p q,p≠q→((L7.filter λ la=>I p la)∩(L7.filter λ la=>I q la)).card≤1:=by
   intro p q xR;apply _y.mpr
   intro l1 Pm l2 MR;by_contra OF;obtain⟨Ou,Wx⟩:=_P Pm;obtain⟨N2,WE⟩:=_P MR;exact hI p q l1 l2 xR OF ⟨(_A Ou).2,(_A N2).2,(_A Wx).2,(_A WE).2⟩
  let A1:=L7.filter λ la=>I p1 la;let A2:=L7.filter λ la=>I p2 la;let A3:=L7.filter λ la=>I p3 la;have Vh:=Vw p1 Xo;have Sn:=Vw p2 Xk;have KA:=Vw p3 KR;have hi12:=Yt p1 p2 Up;have hi13:=Yt p1 p3 P2;have hi23:=Yt p2 p3 PP;have RG:=Finset.card_inter_add_card_union A1 A2;have Pa:((A1∪A2)∩A3).card≤(A1∩A3).card+(A2∩A3).card:=by
   have vR:(A1∪A2)∩A3⊆(A1∩A3)∪(A2∩A3):=by
    intro la nF;obtain⟨W8,LN⟩:=_P nF;rcases mem_union.mp W8 with KK | KE
    · exact _D _ (_X ⟨KK,LN⟩)
    · exact _G _ (_X ⟨KE,LN⟩)
   exact (_C vR).trans (_J _ _)
  have P1:=Finset.card_inter_add_card_union (A1∪A2) A3;have Od:(A1∪A2)∪A3⊆L7:=union_subset (union_subset (filter_subset _ _) (filter_subset _ _))
   (filter_subset _ _)
  have N4:=(_C Od).trans_eq QF;dsimp only[A1,A2,A3] at RG Pa P1 N4;omega
 have Qf:P⊆kc∪ZI:=by
  intro p hp;by_cases hk:k0≤(L7.filter λ la=>p∈yc la).card
  · exact _D _ (_B ⟨hp,hk⟩)
  · exact _G _ (_B ⟨hp,by omega⟩)
 have hc:=_C Qf;have hu:=_J kc ZI;omega
lemma uB {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (L7:_3 N) (QF:L7.card=7) (yc:Fin N→_3 N) (fc:∀ la∈L7,(yc la).card≤3) (pt:Fin N→_3 N) (ki:∀ la∈L7,(pt la).card≤1) (P:_3 N) (hP:∀ p∈P,∃(G3:_3 N) (pF:Fin N→_3 N),G3.card=3∧(∀ lb∈G3,¬ I p lb)∧(∀ lb∈G3,(pF lb).card≤1)∧∀ la∈L7,∀ lb∈G3,¬ I p la→ p∉yc la→ lb∉pt la→ la∉pF lb→ False):P.card≤9:=by
 classical
 have Pl:∀ p∈P,(L7.filter λ la=>¬ I p la∧p∉yc la).card≤1:=by
  intro p hp;by_contra! hgt1;obtain⟨Kn,Oa,Jf,Q0,S9⟩:=_Z hgt1;obtain⟨G3,pF,Jt,_,Ng,Pp⟩:=hP p hp;let LA:_3 N:={Kn,Jf};have N5:LA.card=2:=Finset.card_pair S9;have Tk:LA⊆L7:=by
   intro la nF;rcases mem_insert.mp nF with rfl | nF'
   · exact (_A Oa).1
   · rw[_U nF'];exact (_A Q0).1
  let c5:=(LA×ˢ G3).filter λ ab=>ab.2∈pt ab.1;let bM:=(LA×ˢ G3).filter λ ab=>ab.1∈pF ab.2;have Oc:c5.card≤2:=by
   have vR:c5⊆LA.biUnion λ la=>(G3.filter λ lb=>lb∈pt la).image λ lb=>(la,lb):=by intro⟨la,lb⟩ fP;obtain⟨zA,yH⟩:=_A fP;obtain⟨nF,pv⟩:=_Y zA;exact _F ⟨la,nF,_W ⟨lb,_B ⟨pv,yH⟩,rfl⟩⟩
   refine (_C vR).trans ?_
   refine (_E LA _ 1 ?_).trans (by omega)
   intro la nF;refine _T.trans ((_C ?_).trans (ki la (Tk nF)))
   intro lb pv;exact (_A pv).2
  have Ol:bM.card≤3:=by
   have vR:bM⊆G3.biUnion λ lb=>(LA.filter λ la=>la∈pF lb).image λ la=>(la,lb):=by intro⟨la,lb⟩ fP;obtain⟨zA,yH⟩:=_A fP;obtain⟨nF,pv⟩:=_Y zA;exact _F ⟨lb,pv,_W ⟨la,_B ⟨nF,yH⟩,rfl⟩⟩
   refine (_C vR).trans ?_
   refine (_E G3 _ 1 ?_).trans (by omega)
   intro lb pv;refine _T.trans ((_C ?_).trans (Ng lb pv))
   intro la nF;exact (_A nF).2
  have hprod6:(LA×ˢ G3).card=6:=by rw[_m,N5,Jt]
  have z5:(c5∪bM).card < (LA×ˢ G3).card:=by have hu:=_J c5 bM;omega
  obtain⟨⟨la,lb⟩,dr,Y0⟩:=Finset.exists_mem_notMem_of_card_lt_card z5;obtain⟨XI,RD⟩:=_Y dr;have XI':la∈LA:=XI;have Ob:la∈L7.filter (λ la=>¬ I p la∧p∉yc la):=by
   rcases mem_insert.mp XI' with rfl | nF'
   · exact Oa
   · rw[_U nF'];exact Q0
  obtain⟨S1,VL,Ti⟩:=_A Ob;exact Pp la S1 lb RD VL Ti (λ h=>Y0 (_D _ (_B ⟨dr,h⟩))) (λ h=>Y0 (_G _ (_B ⟨dr,h⟩)))
 exact uY I hI L7 QF yc fc P 3 1 7 (by omega) (by omega) (by decide) Pl
lemma uA {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (L7:_3 N) (QF:L7.card=7) (yc:Fin N→_3 N) (fc:∀ la∈L7,(yc la).card≤3) (P:_3 N) (hP:∀ p∈P,(L7.filter λ la=>¬ I p la∧p∉yc la).card≤2):P.card≤12:=uY I hI L7 QF yc fc P 2 2 10 (by omega) (by omega) (by decide) hP
end RemHelper09
section QueryWBBadBigFull
open M2 Kd M1
open K1 Kc Kb
open Ma
private lemma pQ (N:ℕ) (C:_a) (α:ℕ→ Bool):((wW (vh N C) N α).filter (λ o=>o≠N)).card≤ vA N 1 C.gates+vA N 2 C.gates+2*(Mc.vI N C).card:=by
 classical
 let gs:=vh N C;have fl:Disjoint (vw gs N α) (wW gs N α):=(wl gs N α).symm;have bZ:vw gs N α∪wW gs N α⊆Ico N (N+gs.length):=by
  intro g hg;rcases mem_union.mp hg with hL | hO
  · exact (_A hL).1
  · exact (_A hO).1
 have Xb:(vw gs N α).card+(wW gs N α).card≤ gs.length:=by rw[← card_union_of_disjoint fl];exact (_C bZ).trans (by simp)
 have Q8:N∈wW gs N α:=by
  have vK:gs.head?=some (Sum.inl []):=z9 N C;cases Te:gs with
  | nil=>simp[Te] at vK
  | cons x xs=>
   rw[Te] at vK;have hx:x=Sum.inl []:=by simpa using vK
   subst x;refine _B ⟨mem_Ico.mpr ⟨le_rfl,by simp⟩,?_⟩
   simp[Yi,gateAt]
 have TW:insert N ((wW gs N α).filter (λ o=>o≠N))⊆wW gs N α:=by
  intro o ho;rcases mem_insert.mp ho with rfl | ho'
  · exact Q8
  · exact (_A ho').1
 have RZ:((wW gs N α).filter (λ o=>o≠N)).card+1≤(wW gs N α).card:=by have hc:=_C TW;rwa[Finset.card_insert_of_notMem (by simp)] at hc
 have Se:gs.length≤1+vA N 1 C.gates+vA N 2 C.gates+2*(Mc.vI N C).card:=by have Vr:=x7 N (N+N+C.size) C.gates;rw[← wH N C] at Vr;exact Vr
 dsimp only[gs] at Xb RZ Se;omega
noncomputable def zx {N:ℕ} (I:_0 N) [_4 I] (C:_a) (α:ℕ→ Bool):_2 N:=by
 classical
 let gs:=vh N C;exact univ.filter λ e=>I e.1 e.2∧∃ w∈Mc.vI N C,∃ k:Fin 2,
  let r:=vr N C (if k=0 then vD N C w else vz N C w);e.2∈vk (N:=N) gs α r∧4≤(vk (N:=N) gs α r).card∧(vk (N:=N) gs α r\pencil I e.1).card≤1
lemma jM {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (α:ℕ→ Bool) (hm:_b C) (pO:∀{n m K:ℕ} (zo:ℕ) (T:Fin m→ Finset (Fin n)) (_hT:∀ i j,i≠j→(T i∩T j).card≤1) (S:ℕ→ Finset (Fin n)) (G:Finset ℕ) (vU:ℕ→ Finset ℕ) (_hkids:∀ g∈G,(vU g).card≤2) (_hlt:∀ g∈G,∀ c∈vU g,c < g) (_hunion:∀ g∈G,S g=(vU g).biUnion S) (_hlarge:∀ g,2*zo+2≤(S g).card→ g∈G) (root:Fin K→ ℕ) (line:Fin K→ Fin m) (_hnear:∀ j,(S (root j)\T (line j)).card≤ zo) (E:Finset (Fin n× Fin m)) (_hcover:∀ e∈E,∃ j,e.2=line j∧e.1∈S (root j)),E.card≤2*(2*zo+1)*G.card+(2*zo+1)*K):(zx I C α).card≤6*vA N 1 C.gates+6*vA N 2 C.gates+18*(Mc.vI N C).card:=by
 classical
 let gs:=vh N C;let S:ℕ→_3 N:=vk gs α;let T:Fin N→_3 N:=pencil I;have hT:∀ p q,p≠q→(T p∩T q).card≤1:=by intro p q W0;by_contra! hgt;obtain⟨l₁,hl₁,l₂,hl₂,xR⟩:=_Z hgt;exact hI p q l₁ l₂ W0 xR ⟨(_A (_P hl₁).1).2,(_A (_P hl₂).1).2,(_A (_P hl₁).2).2,(_A (_P hl₂).2).2⟩
 let pairs:=(Mc.vI N C×ˢ (univ:Finset (Fin 2))).filter λ wk=>
  let r:=vr N C (if wk.2=0 then vD N C wk.1 else vz N C wk.1);4≤(S r).card∧∃ p,(S r\T p).card≤1
 let O8':=(wW gs N α).filter (λ o=>o≠N);have hGB'_card:O8'.card≤ vA N 1 C.gates+vA N 2 C.gates+2*(Mc.vI N C).card:=pQ N C α;let K:=pairs.card;let V6:=pairs.toList;have y5:V6.length=K:=length_toList pairs;let root:Fin K→ ℕ:=λ j=>
  let wk:=V6[j]'(by rw[y5];exact j.2)
  vr N C (if wk.2=0 then vD N C wk.1 else vz N C wk.1)
 have cS:∀ j:Fin K,∃ p:Fin N,(S (root j)\T p).card≤1:=by
  intro j;have On:V6[j]'(by rw[y5];exact j.2)∈pairs:=mem_toList.mp (List.getElem_mem _)
  exact (_A On).2.2
 let line:Fin K→ Fin N:=λ j=>(cS j).choose;let RT:_2 N:=(zx I C α).image Prod.swap;have PC:RT.card≤2*(2*1+1)*O8'.card+(2*1+1)*K:=by
  apply pO 1 T hT S O8' (vU gs N)
  · intro o ho;exact dt gs N α (λ rs pE=>w8 N C hm rs pE) o (_A ho).1
  · intro o ho c hc;exact yV gs (z9 N C) N α o (_A ho).1 c hc
  · intro o ho;ext l;simpa[S,mem_biUnion] using xg gs (z9 N C) α o (_A ho).1 l
  · intro o ho;by_cases hon:o < N
    · have hq:S o={⟨o,hon⟩}:=kU gs α ⟨o,hon⟩;rw[hq] at ho;simp at ho
    · by_cases hob:N+gs.length≤ o
      · have pv:S o=∅:=wV gs α o hob;rw[pv] at ho;simp at ho
      · have Ji:o∈Ico N (N+gs.length):=mem_Ico.mpr ⟨by omega,by omega⟩
        rcases uG gs N α o Ji with wv | x1
        · refine _B ⟨wv,?_⟩
          intro zD;subst o;have zj:S N=∅:=q1 gs (z9 N C) α;rw[zj] at ho;simp at ho
        · have zj:S o=∅:=wD gs (z9 N C) α o x1;rw[zj] at ho;simp at ho
  · intro j;exact (cS j).choose_spec
  · intro e he;obtain⟨e',he',rfl⟩:=mem_image.mp he;unfold zx at he';obtain⟨_,_,w,hw,k,yH,h4,xH⟩:=_A he';have Xz:(w,k)∈pairs:=_B ⟨_R ⟨hw,_H k⟩,h4,e'.1,xH⟩;obtain⟨Jr,Ts,TB⟩:=mem_iff_getElem.mp (mem_toList.mpr Xz);let j:Fin K:=⟨Jr,by rw[← y5];exact Ts⟩
    have XE:root j=vr N C (if k=0 then vD N C w else vz N C w):=_9 (λ wk:ℕ× Fin 2=>vr N C (if wk.2=0 then vD N C wk.1 else vz N C wk.1)) TB;have Ls:e'.1=line j:=by
     by_contra xR;have h1:(S (root j)\T e'.1).card≤1:=by simpa[XE] using xH
     have h2:(S (root j)\T (line j)).card≤1:=(cS j).choose_spec;have vR:S (root j)⊆(S (root j)\T e'.1)∪(S (root j)\T (line j))∪(T e'.1∩T (line j)):=by
      intro u hu;by_cases Xt:u∈T e'.1
      · by_cases Y9:u∈T (line j)
        · exact _G _ (_X ⟨Xt,Y9⟩)
        · exact _D _ (_G _ (_V ⟨hu,Y9⟩))
      · exact _D _ (_D _ (_V ⟨hu,Xt⟩))
     have xV:=_C vR;have Xt:=_J ((S (root j)\T e'.1)∪(S (root j)\T (line j)))
      (T e'.1∩T (line j))
     have Y9:=_J (S (root j)\T e'.1) (S (root j)\T (line j));have p4:=hT e'.1 (line j) xR;have h4':4≤(S (root j)).card:=by simpa[XE] using h4
     omega
    refine⟨j,Ls,?_⟩
    change e'.2∈S (root j);rwa[XE]
 have Yc:Function.Injective (Prod.swap:Fin N× Fin N→ Fin N× Fin N):=by intro a b h;simpa using _9 Prod.swap h
 have hE:(zx I C α).card≤6*O8'.card+3*K:=by rw[← _l (zx I C α) Yc];exact PC.trans (by omega)
 have hK:K≤2*(Mc.vI N C).card:=by
  have hf:=card_filter_le (Mc.vI N C×ˢ (univ:Finset (Fin 2)))
   (λ wk=>let r:=vr N C (if wk.2=0 then vD N C wk.1 else vz N C wk.1)
    4≤(S r).card∧∃ p,(S r\T p).card≤1)
  rw[_m,card_univ,Fintype.card_fin] at hf;change K≤(Mc.vI N C).card*2 at hf;omega
 dsimp only[K] at hE;omega
end QueryWBBadBigFull
section SbHelp01
open M2 Kd
open M1 Kb
open Kc K7
open K1
private noncomputable def vG {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (r:ℕ) (q:Fin N):_3 N:=by
 classical
 exact if hq:q∈ve r then vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N (vf r q hq).choose)
 else ∅
private lemma xw {N:ℕ} (I:_0 N) [_4 I] (B:_3 N) (q:Fin N) (h8:8≤ B.card) (x9:¬(vx (pencil I) 3 B∧4≤(B.filter (I q)).card)) (zu:vx (pencil I) 3 B):5≤(B.filter λ u=>¬ I q u).card:=by
 have Np:(B.filter (I q)).card≤3:=by by_contra! h4;exact x9 ⟨zu,h4⟩
 have Yy:=_t (s:=B) (p:=I q);omega
private noncomputable def y6 {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (r:ℕ) (q:Fin N):_3 N:=by
 classical
 exact if hq:q∈ve r then
  let B:=vG I C ve vf r q;if zu:vx (pencil I) 3 B then (_N (xw I B q (by simpa[B,vG,_Q hq] using (vf r q hq).choose_spec.2.2.1) (by simpa[B,vG,_Q hq] using (vf r q hq).choose_spec.2.2.2.1) zu)).choose
  else ∅
 else ∅
private noncomputable def yw {N:ℕ} (I:_0 N) [_4 I] (ve:ℕ→_3 N) (r:ℕ) (l:Fin N):_3 N:=by
 classical
 exact if fp:13≤(ve r\univ.filter λ q=>I q l).card then (_N fp).choose
 else ∅
private noncomputable def vY {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (w:ℕ) (m:Fin 2) (l:Fin N):_3 N:=by
 classical
 let r:=vr N C (vd N C w (1-m));exact if l∈vk (vh N C) (vc I C) r then ∅
 else if 13≤(ve r\univ.filter λ q=>I q l).card then
  let g6:=yw I ve r l;univ.filter λ p:Fin N=>4≤(g6.filter λ q=>vx (pencil I) 3 (vG I C ve vf r q)∧4≤((y6 I C ve vf r q).filter λ u=>I p u).card).card
 else ∅
private lemma xl {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (w:ℕ) (m:Fin 2) (l:Fin N):(vY I C ve vf w m l).card≤3:=by
 classical
 dsimp only[vY];split_ifs with hb fp
 · simp
 · let r:=vr N C (vd N C w (1-m));let g6:=yw I ve r l
   have dl:g6.card=13:=by dsimp only[g6,yw];rw[_Q fp];exact (_N fp).choose_spec.2
   have nW:g6⊆ve r\univ.filter λ q=>I q l:=by dsimp only[g6,yw];rw[_Q fp];exact (_N fp).choose_spec.1
   let P:=univ.filter λ p:Fin N=>4≤(g6.filter λ q=>vx (pencil I) 3 (vG I C ve vf r q)∧4≤((y6 I C ve vf r q).filter λ u=>I p u).card).card;let E:=(P×ˢ g6).filter λ pq=>vx (pencil I) 3 (vG I C ve vf r pq.2)∧4≤((y6 I C ve vf r pq.2).filter λ u=>I pq.1 u).card;have Oh:4*P.card≤ E.card:=by
    let QG:Fin N→_2 N:=λ p=>(g6.filter λ q=>vx (pencil I) 3 (vG I C ve vf r q)∧4≤((y6 I C ve vf r q).filter λ u=>I p u).card).image λ q=>(p,q);have vR:P.biUnion QG⊆E:=by intro pq W0;obtain⟨p,U1,hq⟩:=mem_biUnion.mp W0;obtain⟨q,KW,rfl⟩:=mem_image.mp hq;obtain⟨Xl,c3⟩:=_A KW;exact _B ⟨_R ⟨U1,Xl⟩,c3⟩
    have fl:(P:Set (Fin N)).PairwiseDisjoint QG:=by intro p₁ _ p₂ _ xR;dsimp only[Function.onFun,QG];rw[disjoint_left];intro pq h1 h2;obtain⟨_,_,Xo⟩:=mem_image.mp h1;obtain⟨_,_,Xk⟩:=mem_image.mp h2;exact xR (_9 Prod.fst (Xo.trans Xk.symm))
    have Yy:=Finset.card_biUnion fl;have h4:4*P.card≤ ∑ p∈P,(QG p).card:=by
     calc 4*P.card=∑ _p∈P,4:=by simp[Nat.mul_comm]
      _≤ ∑ p∈P,(QG p).card:=by
       refine sum_le_sum λ p hp=>?_
       dsimp only[QG];rw[_l _ (λ a b h=>_9 Prod.snd h)];exact (_A hp).2
    exact h4.trans (Yy▸_C vR)
   have Og:E.card≤ g6.card:=by
    have vR:E⊆g6.biUnion λ q=>if h:∃ p:Fin N,vx (pencil I) 3 (vG I C ve vf r q)∧4≤((y6 I C ve vf r q).filter λ u=>I p u).card then {(h.choose,q)} else ∅:=by
     intro⟨p,q⟩ W0;obtain⟨zA,c3⟩:=_A W0;have Xl:=(_Y zA).2;have wr:∃ p':Fin N,vx (pencil I) 3 (vG I C ve vf r q)∧4≤((y6 I C ve vf r q).filter λ u=>I p' u).card:=⟨p,c3⟩;have nk:p=wr.choose:=by
      by_contra xR;have xn:q∈ve r:=(_M (nW Xl)).1;let U5:=y6 I C ve vf r q;have hU5_card:U5.card=5:=by
       have WN:=(vf r q xn).choose_spec;have h5:5≤(vG I C ve vf r q |>.filter λ u=>¬ I q u).card:=xw I _ q (by simpa[vG,_Q xn] using WN.2.2.1)
        (by simpa[vG,_Q xn] using WN.2.2.2.1) c3.1
       dsimp only[U5,y6];rw[_Q xn,_Q c3.1];exact (_N h5).choose_spec.2
      have p4:2≤((U5.filter λ u=>I p u)∩(U5.filter λ u=>I wr.choose u)).card:=by
       have hu:(U5.filter λ u=>I p u)∪(U5.filter λ u=>I wr.choose u)⊆U5:=union_subset (filter_subset _ _) (filter_subset _ _);have LT:=_C hu;have hs:=Finset.card_inter_add_card_union (U5.filter λ u=>I p u)
        (U5.filter λ u=>I wr.choose u)
       have h4p:4≤(U5.filter λ u=>I p u).card:=c3.2;have h4c:4≤(U5.filter λ u=>I wr.choose u).card:=wr.choose_spec.2;omega
      obtain⟨u₁,hu₁,u₂,hu₂,Vx⟩:=_Z p4;have Xo:=(_A (_P hu₁).1).2;have Xk:=(_A (_P hu₂).1).2;have Vh:=(_A (_P hu₁).2).2;have Sn:=(_A (_P hu₂).2).2;exact hI p wr.choose u₁ u₂ xR Vx ⟨Xo,Xk,Vh,Sn⟩
     refine _F ⟨q,Xl,?_⟩
     rw[_Q wr,mem_singleton,nk]
    refine (_C vR).trans ?_
    refine (_E g6 _ 1 ?_).trans (by omega)
    intro q _;split_ifs <;> simp
   have KU:P.card≤3:=by omega
   exact KU
 · simp
private def vE {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (w:ℕ) (m:Fin 2) (l:Fin N):Prop:=w∈Mc.vI N C∧l∈vk (vh N C) (vc I C) (vr N C (vd N C w m))∧(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C w m))).card≤3∧(l∈vk (vh N C) (vc I C) (vr N C (vd N C w (1-m)))∨13≤(ve (vr N C (vd N C w (1-m)))\univ.filter λ q=>I q l).card)
private lemma z3 {N:ℕ} (I:_0 N) [_4 I] (C:_a) (hm:_b C) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (w:ℕ) (m:Fin 2) (l:Fin N) (ht:vE I C ve w m l) (S:_3 N) (wh:S.card≤4) (XY:l∈S) (x y:Fin N→ Bool) (Xe:∀ q,vB I S q=true→ x q=true) (TM:∀ u∈S,y u=true) (gX:l∈vk (vh N C) (vc I C) (vr N C (vd N C w (1-m)))∨
 ∃ q∈ve (vr N C (vd N C w (1-m))),∃ u∈S,u∈vG I C ve vf (vr N C (vd N C w (1-m))) q∧∀ s∈S,¬ I q s):
 ∃ ua va,M9.y3 N C w ua va∧(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C ua) false=true∧(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C va) false=true:=by
 classical
 have RQ:M9.nM N C w:=(_A ht.1).2;obtain⟨ua,va,hf⟩:=RQ;have QK:vd N C w 0=ua∧vd N C w 1=va:=zh N C w ua va hf;have WU:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C (vd N C w m)) false=true:=vL I C hm S wh x y Xe _ l ht.2.1 (TM l XY);have d4:(run (vh N C) (vy N C (ofFn x)) (ofFn y)).getD (vr N C (vd N C w (1-m))) false=true:=by
  rcases gX with yi | ⟨q,xn,u,Vb,Zu,hnq⟩
  · exact vL I C hm S wh x y Xe _ l yi (TM l XY)
  · have Ki:x q=true:=Xe q (by
     simp only[vB,decide_eq_true_eq];exact hnq)
    have Ry:u∈v9 (vh N C) (vi I C) (vr N C (vd N C w (1-m))) q:=by dsimp only[vG] at Zu;rw[_Q xn] at Zu;exact (vf _ q xn).choose_spec.2.2.2.2 Zu
    exact yI I C hm S wh x y Xe _ q u Ry Ki (TM u Vb)
 refine⟨ua,va,hf,?_,?_⟩
 · fin_cases m
   · simpa[QK.1] using WU
   · simpa[QK.1] using d4
 · fin_cases m
   · simpa[QK.2] using d4
   · simpa[QK.2] using WU
lemma z2 {J N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (g₀ g₁:Fin J→ ℕ) (hm:_b C) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (g₀ jb) false=true→(C.wires (ofFn zz)).getD (g₁ jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q)
 (j:Fin J) (p:Fin N) (wa wb:ℕ) (ma mb:Fin 2) (l:Fin N)
 (Sg:vE I C ve wa ma l)
 (U9:vE I C ve wb mb l)
 (Ti:¬ I p l)
 (mF:p∉vY I C ve vf wa ma l)
 (nK:p∉vY I C ve vf wb mb l)
 (mP:_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₀ j) wa)
 (mQ:_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₁ j) wb):
 False:=by
 classical
 let ra:=vr N C (vd N C wa (1-ma));let rb:=vr N C (vd N C wb (1-mb));let B:=vG I C ve vf
 let U5:=y6 I C ve vf
 have Wv:∀ w m (ht:vE I C ve w m l) (YM:p∉vY I C ve vf w m l) (hb:l∉vk (vh N C) (vc I C) (vr N C (vd N C w (1-m)))) (fp:13≤(ve (vr N C (vd N C w (1-m)))\univ.filter λ q=>I q l).card),
  let r:=vr N C (vd N C w (1-m));let Q:=(yw I ve r l).filter λ q=>¬(vx (pencil I) 3 (B r q)∧4≤((U5 r q).filter λ u=>I p u).card);10≤ Q.card∧∀ q∈Q,q∈ve r∧¬ I q l:=by
  intro w m _ YM hb fp r Q;have dl:(yw I ve r l).card=13:=by dsimp only[yw];rw[_Q fp];exact (_N fp).choose_spec.2
  have nW:yw I ve r l⊆ve r\univ.filter λ q=>I q l:=by dsimp only[yw];rw[_Q fp];exact (_N fp).choose_spec.1
  have hbad3:((yw I ve r l).filter λ q=>vx (pencil I) 3 (B r q)∧4≤((U5 r q).filter λ u=>I p u).card).card≤3:=by
   by_contra! h4;apply YM
   dsimp only[vY];rw[if_neg hb,_O fp];exact _B ⟨_H _,h4⟩
  have Yy:=_t
   (s:=yw I ve r l)
   (p:=λ q=>vx (pencil I) 3 (B r q)∧4≤((U5 r q).filter λ u=>I p u).card)
  refine⟨by dsimp only[Q];omega,λ q hq=>?_⟩
  have yH:=_M (nW (_A hq).1);exact⟨yH.1,λ h=>yH.2 (_B ⟨_H _,h⟩)⟩
 have ml:∀ w m (ht:vE I C ve w m l) (YM:p∉vY I C ve vf w m l),l∈vk (vh N C) (vc I C) (vr N C (vd N C w (1-m)))∨∃ q∈ve (vr N C (vd N C w (1-m))),¬ I q l∧∃ u∈B (vr N C (vd N C w (1-m))) q,¬ I q u∧¬ I p u:=by
  intro w m ht YM;rcases ht.2.2.2 with yi | fp
  · exact Or.inl yi
  · by_cases hb:l∈vk (vh N C) (vc I C) (vr N C (vd N C w (1-m)))
    · exact Or.inl hb
    · right
      obtain⟨MK,RY⟩:=Wv w m ht YM hb fp;obtain⟨q,SX⟩:=card_pos.mp (Nat.lt_of_lt_of_le (by omega) MK);obtain⟨xn,ny⟩:=RY q SX;have WN:=(vf _ q xn).choose_spec;by_cases zu:vx (pencil I) 3 (B (vr N C (vd N C w (1-m))) q)
      · have bj:5≤(vG I C ve vf (vr N C (vd N C w (1-m))) q |>.filter λ u=>¬ I q u).card:=xw I _ q
         (by dsimp only[B,vG];rw[_Q xn];exact WN.2.2.1)
         (by dsimp only[B,vG];rw[_Q xn];exact WN.2.2.2.1) zu
        have h5:5≤(U5 (vr N C (vd N C w (1-m))) q).card:=by dsimp only[U5,y6];rw[_Q xn,_Q zu];exact le_of_eq (_N bj).choose_spec.2.symm
        have cE:U5 (vr N C (vd N C w (1-m))) q⊆(B (vr N C (vd N C w (1-m))) q).filter λ u=>¬ I q u:=by dsimp only[U5,y6];rw[_Q xn,_Q zu];exact (_N bj).choose_spec.1
        have VN:((U5 (vr N C (vd N C w (1-m))) q).filter λ u=>I p u).card≤3:=by by_contra! h4;exact (_A SX).2 ⟨zu,h4⟩
        have Yy:=_t
         (s:=U5 (vr N C (vd N C w (1-m))) q) (p:=λ u=>I p u)
        obtain⟨u,hu⟩:=card_pos.mp (by omega:0 < ((U5 (vr N C (vd N C w (1-m))) q).filter λ u=>¬ I p u).card);obtain⟨Th,f4⟩:=_A hu;have Zu:=_A (cE Th);exact⟨q,xn,ny,u,Zu.1,Zu.2,f4⟩
      · have wr:∃ u∈B (vr N C (vd N C w (1-m))) q,¬ I q u∧¬ I p u:=by
         by_contra hnone;push Not at hnone;apply zu
         refine⟨{q,p},(_K _ _).trans (by simp),λ u hu=>?_⟩
         by_cases b8:I q u
         · exact _F ⟨q,_S _ _,_B ⟨_H _,b8⟩⟩
         · exact _F ⟨p,_L (_I _),_B ⟨_H _,hnone u hu b8⟩⟩
        obtain⟨u,Zu,b8,f4⟩:=wr;exact⟨q,xn,ny,u,Zu,b8,f4⟩
 have Wb:∃ S:_3 N,S.card≤3∧l∈S∧(∀ u∈S,¬ I p u)∧(l∈vk (vh N C) (vc I C) ra∨∃ qa∈ve ra,∃ ua∈S,ua∈B ra qa∧∀ s∈S,¬ I qa s)∧(l∈vk (vh N C) (vc I C) rb∨∃ qb∈ve rb,∃ ub∈S,ub∈B rb qb∧∀ s∈S,¬ I qb s):=by
  by_cases Zc:l∈vk (vh N C) (vc I C) ra
  · rcases ml wb mb U9 nK with hbb | ⟨qb,XX,Oi,ub,Zu,hqub,hpub⟩
    · refine⟨{l},by simp,_I _,λ u hu=>by rw[_U hu];exact Ti,Or.inl Zc,Or.inl hbb⟩
    · refine⟨{l,ub},(_K _ _).trans (by simp),_S _ _,λ u hu=>?_,Or.inl Zc,Or.inr ⟨qb,XX,ub,_L (_I _),Zu,λ s hs=>?_⟩⟩
      · rcases mem_insert.mp hu with rfl | hu'
        · exact Ti
        · rw[_U hu'];exact hpub
      · rcases mem_insert.mp hs with rfl | hs'
        · exact Oi
        · rw[_U hs'];exact hqub
  · by_cases hbb:l∈vk (vh N C) (vc I C) rb
    · obtain⟨qa,XP,Pn,ua,Zu,NK,RH⟩:=(ml wa ma Sg mF).resolve_left Zc;refine⟨{l,ua},(_K _ _).trans (by simp),_S _ _,λ u hu=>?_,Or.inr ⟨qa,XP,ua,_L (_I _),Zu,λ s hs=>?_⟩,Or.inl hbb⟩
      · rcases mem_insert.mp hu with rfl | hu'
        · exact Ti
        · rw[_U hu'];exact RH
      · rcases mem_insert.mp hs with rfl | hs'
        · exact Pn
        · rw[_U hs'];exact NK
    · have Ua:13≤(ve ra\univ.filter λ q=>I q l).card:=Sg.2.2.2.resolve_left Zc;have S5:13≤(ve rb\univ.filter λ q=>I q l).card:=U9.2.2.2.resolve_left hbb;obtain⟨PU,Wm⟩:=Wv wa ma Sg mF Zc Ua;obtain⟨Q4,We⟩:=Wv wb mb U9 nK hbb S5;let Qa:=(yw I ve ra l).filter λ q=>¬(vx (pencil I) 3 (B ra q)∧4≤((U5 ra q).filter λ u=>I p u).card);let Qb:=(yw I ve rb l).filter λ q=>¬(vx (pencil I) 3 (B rb q)∧4≤((U5 rb q).filter λ u=>I p u).card);let bad₁:=(Qa×ˢ Qb).filter λ qp=>¬ ∃ ua∈B ra qp.1,¬ I qp.1 ua∧¬ I qp.2 ua∧¬ I p ua;let bad₂:=(Qa×ˢ Qb).filter λ qp=>¬ ∃ ub∈B rb qp.2,¬ I qp.2 ub∧¬ I qp.1 ub∧¬ I p ub
      have ZF:∀(r:ℕ) (qr:Fin N) (QA:qr∈ve r) (Pk:¬(vx (pencil I) 3 (B r qr)∧4≤((U5 r qr).filter λ u=>I p u).card)) (WJ:_3 N),(WJ.filter λ qo=>¬ ∃ u∈B r qr,¬ I qr u∧¬ I qo u∧¬ I p u).card≤1:=by
       intro r qr QA Pk WJ;rw[_y];intro q₁ hq₁ q₂ hq₂;have h1:=(_A hq₁).2;have h2:=(_A hq₂).2;by_contra xR;by_cases zu:vx (pencil I) 3 (B r qr)
       · have WN:=(vf r qr QA).choose_spec
         have bj:5≤(vG I C ve vf r qr |>.filter λ u=>¬ I qr u).card:=xw I _ qr
          (by dsimp only[B,vG];rw[_Q QA];exact WN.2.2.1)
          (by dsimp only[B,vG];rw[_Q QA];exact WN.2.2.2.1) zu
         have h5:5≤(U5 r qr).card:=by dsimp only[U5,y6];rw[_Q QA,_Q zu];exact le_of_eq (_N bj).choose_spec.2.symm
         have cE:U5 r qr⊆(B r qr).filter λ u=>¬ I qr u:=by dsimp only[U5,y6];rw[_Q QA,_Q zu];exact (_N bj).choose_spec.1
         have VN:((U5 r qr).filter λ u=>I p u).card≤3:=by by_contra! h4;exact Pk ⟨zu,h4⟩
         have Yy:=_t (s:=U5 r qr) (p:=λ u=>I p u);have NW:2≤((U5 r qr).filter λ u=>¬ I p u).card:=by omega
         obtain⟨u₁,hu₁,u₂,hu₂,Vx⟩:=_Z NW;have Xt':=_A hu₁;have Y9':=_A hu₂;have Tj:=_A (cE Xt'.1);have TV:=_A (cE Y9'.1);have SJ:I q₁ u₁:=by by_contra hn;exact h1 ⟨u₁,Tj.1,Tj.2,hn,Xt'.2⟩
         have Rx:I q₁ u₂:=by by_contra hn;exact h1 ⟨u₂,TV.1,TV.2,hn,Y9'.2⟩
         have ST:I q₂ u₁:=by by_contra hn;exact h2 ⟨u₁,Tj.1,Tj.2,hn,Xt'.2⟩
         have RX:I q₂ u₂:=by by_contra hn;exact h2 ⟨u₂,TV.1,TV.2,hn,Y9'.2⟩
         exact hI q₁ q₂ u₁ u₂ xR Vx ⟨SJ,Rx,ST,RX⟩
       · apply zu
         refine⟨{qr,q₁,p},(_K _ _).trans (_n ((_K _ _).trans (by simp))),λ u hu=>?_⟩
         by_cases hqr_u:I qr u
         · exact _F ⟨qr,_S _ _,_B ⟨_H _,hqr_u⟩⟩
         · by_cases hq1_u:I q₁ u
           · exact _F ⟨q₁,_L (_S _ _),_B ⟨_H _,hq1_u⟩⟩
           · have f4:I p u:=by
              by_contra hn;exact h1 ⟨u,hu,hqr_u,hq1_u,hn⟩
             exact _F ⟨p,_L (_L (_I _)),_B ⟨_H _,f4⟩⟩
      have hbad₁:bad₁.card≤ Qa.card:=by
       have vR:bad₁⊆Qa.biUnion λ q₁=>(Qb.filter λ q₂=>¬ ∃ ua∈B ra q₁,¬ I q₁ ua∧¬ I q₂ ua∧¬ I p ua).image λ q₂=>(q₁,q₂):=by intro⟨q₁,q₂⟩ hm_b;obtain⟨zA,dw⟩:=_A hm_b;obtain⟨hq₁,hq₂⟩:=_Y zA;exact _F ⟨q₁,hq₁,_W ⟨q₂,_B ⟨hq₂,dw⟩,rfl⟩⟩
       refine (_C vR).trans ?_
       refine (_E Qa _ 1 ?_).trans (by omega)
       intro q₁ hq₁;refine _T.trans ?_
       exact ZF ra q₁ (Wm q₁ hq₁).1 (_A hq₁).2 Qb
      have hbad₂:bad₂.card≤ Qb.card:=by
       have vR:bad₂⊆Qb.biUnion λ q₂=>(Qa.filter λ q₁=>¬ ∃ ub∈B rb q₂,¬ I q₂ ub∧¬ I q₁ ub∧¬ I p ub).image λ q₁=>(q₁,q₂):=by intro⟨q₁,q₂⟩ hm_b;obtain⟨zA,dw⟩:=_A hm_b;obtain⟨hq₁,hq₂⟩:=_Y zA;exact _F ⟨q₂,hq₂,_W ⟨q₁,_B ⟨hq₁,dw⟩,rfl⟩⟩
       refine (_C vR).trans ?_
       refine (_E Qb _ 1 ?_).trans (by omega)
       intro q₂ hq₂;refine _T.trans ?_
       exact ZF rb q₂ (We q₂ hq₂).1 (_A hq₂).2 Qa
      have z5:(bad₁∪bad₂).card < (Qa×ˢ Qb).card:=by have hQa_le:10≤ Qa.card:=PU;have hQb_le:10≤ Qb.card:=Q4;have hu:=_J bad₁ bad₂;rw[_m];nlinarith
      have xR:((Qa×ˢ Qb)\(bad₁∪bad₂)).Nonempty:=by rw[← card_pos];have hs:=_z (Qa×ˢ Qb) (bad₁∪bad₂);have hi:=_C (inter_subset_right:(Qa×ˢ Qb)∩(bad₁∪bad₂)⊆bad₁∪bad₂);omega
      obtain⟨⟨qa,qb⟩,hq⟩:=xR;obtain⟨zA,x9⟩:=_M hq;obtain⟨Vu,O6⟩:=_Y zA;have S8:¬(qa,qb)∈bad₁:=λ h=>x9 (_D _ h);have R7:¬(qa,qb)∈bad₂:=λ h=>x9 (_G _ h);simp only[bad₁,mem_filter,zA,true_and,not_not] at S8;simp only[bad₂,mem_filter,zA,true_and,not_not] at R7;obtain⟨ua,Qn,Pv,PM,Rs⟩:=S8;obtain⟨ub,SI,Py,Oo,QW⟩:=R7;have Pn:=(Wm qa Vu).2;have Oi:=(We qb O6).2
      refine⟨{l,ua,ub},(_K _ _).trans (_n ((_K _ _).trans (by simp))),_S _ _,λ u hu=>?_,Or.inr ⟨qa,(Wm qa Vu).1,ua,_L (_S _ _),Qn,λ s hs=>?_⟩,Or.inr ⟨qb,(We qb O6).1,ub,_L (_L (_I _)),SI,λ s hs=>?_⟩⟩
      · simp only[mem_insert,mem_singleton] at hu;rcases hu with rfl | rfl | rfl <;> assumption
      · simp only[mem_insert,mem_singleton] at hs;rcases hs with rfl | rfl | rfl <;> assumption
      · simp only[mem_insert,mem_singleton] at hs;rcases hs with rfl | rfl | rfl <;> assumption
 obtain⟨S,hS3,XY,Rb,RB,SK⟩:=Wb;have wh:S.card≤4:=by omega
 let x:Fin N→ Bool:=λ q=>decide (q=p) || vB I S q;let y:Fin N→ Bool:=λ w=>decide (w∈S);have Xe:∀ q,vB I S q=true→ x q=true:=λ q hq=>by simp[x,hq]
 have QQ:∀ q,decide (q=p)=true→ x q=true:=λ q hq=>by simp[x,hq]
 have TM:∀ u∈S,y u=true:=λ u hu=>decide_eq_true hu;obtain⟨ua,va,m6,gy,WT⟩:=z3 I C hm ve vf wa ma l Sg S wh XY x y Xe TM RB;obtain⟨xb,yb,m9,ZR,Z3⟩:=z3 I C hm ve vf wb mb l U9 S wh XY x y Xe TM SK;have Ss:∀{u v},_1 (λ a b=>M9.vl N C (ofFn (λ q=>decide (q=p))) a b∨vj I C a b) u v→_1 (M9.vl N C (ofFn x)) u v:=by
  intro u v hp;induction hp using ReflTransGen.head_induction_on with
  | refl=>exact .refl
  | head hs _ ih=>
   rcases hs with ha | hc
   · exact .head (je C hm _ x QQ _ _ ha) ih
   · exact .head (uK I C hm S wh x Xe _ _ hc) ih
 obtain⟨pa,lb',jz,dS,Y2⟩:=zc I C g₀ g₁ hm vM j wa ua va wb xb yb m6 m9 x y (Ss mP) (Ss mQ) gy WT ZR Z3;have YQ:lb'∈S:=_o Y2;simp only[x,_r,decide_eq_true_eq] at dS;rcases dS with rfl | hm_pa
 · exact Rb lb' YQ jz
 · exact (by simpa only[vB,decide_eq_true_eq] using hm_pa:∀ u∈S,¬ I pa u) lb' YQ jz
private noncomputable def vt {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (u:ℕ):_3 N:=by
 classical
 exact univ.filter λ l=>∃ w∈Mc.vI N C,∃ m:Fin 2,_1 (vj I C) u w∧l∈vk (vh N C) (vc I C) (vr N C (vd N C w m))∧(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C w m))).card≤3∧vE I C ve w m l
private lemma n3 {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (u v:ℕ) (h:vj I C u v):vt I C ve v⊆vt I C ve u:=by
 classical
 intro l hl;obtain⟨w,hw,m,hp,yH,h3,ht⟩:=(_A hl).2;exact _B ⟨_H _,w,hw,m,.head h hp,yH,h3,ht⟩
private lemma qW {N:ℕ} (I:_0 N) (C:_a) (w v:ℕ) (hw:w∈Mc.vI N C):¬ vj I C w v:=by
 classical
 intro zl;have RQ:M9.nM N C w:=(_A hw).2;have R0:=(M9.wA N C w v).mp zl.1;have qX:0 < (M9.v6 N C w).length:=length_pos_of_mem R0.2;have h0:=Mc.yJ N C w RQ;omega
private lemma m8 {N:ℕ} (I:_0 N) (C:_a) (w v:ℕ) (hw:w∈Mc.vI N C) (hp:_1 (vj I C) w v):v=w:=by
 cases hp using ReflTransGen.head_induction_on with
 | refl=>rfl
 | head zl _=>exact (qW I C w _ hw zl).elim
private lemma jY {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (w:ℕ) (hw:w∈Mc.vI N C):(vt I C ve w).card≤6:=by
 classical
 have vR:vt I C ve w⊆((univ:Finset (Fin 2)).filter λ m=>(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C w m))).card≤3).biUnion
  λ m=>vk (vh N C) (vc I C) (vr N C (vd N C w m)):=by
  intro l hl;obtain⟨w',_,m,hp,yH,h3,_⟩:=(_A hl).2;obtain rfl:=m8 I C w w' hw hp;exact _F ⟨m,_B ⟨_H _,h3⟩,yH⟩
 refine (_C vR).trans ((_E _ _ 3 ?_).trans ?_)
 · intro m hm;exact (_A hm).2
 · have h2:((univ:Finset (Fin 2)).filter λ m=>(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C w m))).card≤3).card≤2:=(card_filter_le _ _).trans (by simp);omega
private lemma qF {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (dh:_2 N) (KH:∀ e∈dh,∃ w∈Mc.vI N C,∃ m:Fin 2,e.2∈vk (vh N C) (vc I C) (vr N C (vd N C w m))∧(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C w m))).card≤3∧e.1∈vY I C ve vf w m e.2):
 dh.card≤18*(Mc.vI N C).card:=by
 classical
 let WK:=Mc.vI N C×ˢ (univ:Finset (Fin 2));have vR:dh⊆WK.biUnion λ wk=>
  let r:=vr N C (vd N C wk.1 wk.2);if (vk (N:=N) (vh N C) (vc I C) r).card≤3 then (vk (vh N C) (vc I C) r).biUnion λ l=>(vY I C ve vf wk.1 wk.2 l).image λ p=>(p,l)
  else ∅:=by
  intro⟨p,l⟩ he;obtain⟨w,hw,m,Vk,h3,hp⟩:=KH (p,l) he;refine _F ⟨(w,m),_R ⟨hw,_H _⟩,?_⟩
  dsimp only;rw[_O h3];exact _F ⟨l,Vk,_W ⟨p,hp,rfl⟩⟩
 refine (_C vR).trans ?_
 refine (_E WK _ 9 ?_).trans ?_
 · intro wk _;dsimp only;split_ifs with h3
   · refine (_E _ _ 3 ?_).trans (by nlinarith)
     intro l _;exact _T.trans (xl I hI C ve vf wk.1 wk.2 l)
   · simp
 · have Xz:WK.card=(Mc.vI N C).card*2:=by simp[WK,_m]
   rw[Xz];omega
private lemma kW {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (c w:ℕ) (wP:_1 (vj I C) c w) (h7:7≤(vt I C ve c).card) (h6:(vt I C ve w).card≤6):∃ a b:ℕ,vj I C a b∧_1 (vj I C) c a∧_1 (vj I C) b w∧7≤(vt I C ve a).card∧(vt I C ve b).card≤6:=by
 induction wP using ReflTransGen.head_induction_on with
 | refl=>omega
 | head zl hrest ih=>
  rename_i x y
  by_cases hy6:(vt I C ve y).card≤6
  · exact⟨x,y,zl,.refl,hrest,h7,hy6⟩
  · obtain⟨a,b,fP,cz,V8,Vm,Vl⟩:=ih (by omega);exact⟨a,b,fP,.head zl cz,V8,Vm,Vl⟩
private noncomputable def vJ {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (c:ℕ) (p:Fin N):_3 N:=by
 classical
 exact (vt I C ve c).filter λ u=>¬ I p u∧∃ w∈Mc.vI N C,∃ m:Fin 2,_1 (vj I C) c w∧vE I C ve w m u∧p∉vY I C ve vf w m u
private lemma h9 {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (c a:ℕ) (p:Fin N) (cz:_1 (vj I C) c a):vJ I C ve vf a p⊆vJ I C ve vf c p:=by
 classical
 intro u hu;obtain⟨Vb,Ti,w,hw,m,NC,Kt,Xo⟩:=_A hu;have Vb':u∈vt I C ve c:=by
  induction cz using ReflTransGen.head_induction_on with
  | refl=>exact Vb
  | head hs _ ih=>exact n3 I C ve _ _ hs ih
 exact _B ⟨Vb',Ti,w,hw,m,cz.trans NC,Kt,Xo⟩
private lemma nr {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (v:ℕ) (v4:vZ I C v):vt I C ve v=∅:=by
 classical
 rw[Finset.eq_empty_iff_forall_notMem];intro l hl;obtain⟨w,hw,_,wP,_⟩:=(_A hl).2;cases wP using ReflTransGen.head_induction_on with
 | refl=>
  exact (_M (zd C v v4.choose v4.choose_spec.1)).2 hw
 | head zl _=>
  exact zl.2 v4
private noncomputable def vv {J N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (fa fb:Fin J→ ℕ) (u:ℕ):_3 N:=by
 classical
 exact univ.filter λ l=>∃ j:Fin J,(_1 (vj I C) (fb j) u∧(vt I C ve (fa j)).card≤6∧l∈vt I C ve (fa j))∨(_1 (vj I C) (fa j) u∧(vt I C ve (fb j)).card≤6∧l∈vt I C ve (fb j))
private lemma uT {J N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (F4:_2 N) (z6:∀ e∈F4,(e.1,e.2)∉v2 I C) (qq:_2 N) (Ya:qq⊆F4) (zu:∀ e∈qq,I e.1 e.2∧((∃ v c:ℕ,(v,c)∈M9.vm N C∧vZ I C v∧
 M9.vl N C (ofFn (λ q=>decide (q=e.1))) v c∧(vt I C ve c).card≤6∧e.2∈vt I C ve c)∨(∃ a b:ℕ,vj I C a b∧7≤(vt I C ve a).card∧(vt I C ve b).card≤6∧e.2∈vt I C ve b∧(vJ I C ve vf a e.1).card≤2)∨(∃ u yy:ℕ,vj I C u yy∧vZ I C yy∧(∃ c_top:ℕ,(yy,c_top)∈M9.vm N C∧M9.vl N C (ofFn (λ q=>decide (q=e.1))) yy c_top)∧(vv I C ve fa fb u).card≤6∧e.2∈vv I C ve fa fb u)∨(∃ yy:ℕ,vZ I C yy∧(∃ c_top:ℕ,(yy,c_top)∈M9.vm N C∧M9.vl N C (ofFn (λ q=>decide (q=e.1))) yy c_top)∧(vv I C ve fa fb yy).card≤6∧e.2∈vv I C ve fa fb yy))):
 qq.card≤50*(Mc.vP N C\Mc.vI N C).card:=by
 classical
 let NF:=Mc.vP N C\Mc.vI N C;have mS:∀ x y,vj I C x y→ x∈NF∧y∈M9.v6 N C x:=by
  intro x y UJ;obtain⟨z5,hc⟩:=(M9.wA N C x y).mp UJ.1;have qX:0 < (M9.v6 N C x).length:=length_pos_of_mem hc;have hd:M9.yf N C x=2:=by by_contra xR;have h0:=Mc.zY N C x xR;omega
  have Pe:¬ M9.nM N C x:=λ hf=>by have h0:=Mc.yJ N C x hf;omega
  exact⟨_V ⟨_B ⟨mem_range.mpr z5,hd⟩,λ hm'=>Pe (_A hm').2⟩,hc⟩
 let q7:(ℕ× ℕ)→_2 N:=λ edge=>if h:vZ I C edge.1∧(vt I C ve edge.2).card≤6 then
  (vt I C ve edge.2).biUnion λ l=>((univ:_3 N).filter λ p=>p∈K7.vS C h.1.choose∧(p,l)∈F4∧I p l).image λ p=>(p,l)
  else ∅
 let j5:ℕ→_2 N:=λ v=>if h:vZ I C v∧(vv I C ve fa fb v).card≤6 then
  (vv I C ve fa fb v).biUnion λ l=>((univ:_3 N).filter λ p=>p∈K7.vS C h.1.choose∧(p,l)∈F4∧I p l).image λ p=>(p,l)
  else ∅
 let ph:(ℕ× ℕ)→_2 N:=λ edge=>if h:vj I C edge.1 edge.2∧7≤(vt I C ve edge.1).card∧(vt I C ve edge.2).card≤6 then
  let P:=(univ:_3 N).filter λ p=>(vJ I C ve vf edge.1 p).card≤2;((P×ˢ vt I C ve edge.2).filter λ e=>I e.1 e.2)
  else ∅
 let xt:(ℕ× ℕ)→_2 N:=λ edge=>if h:vj I C edge.1 edge.2∧vZ I C edge.2∧(vv I C ve fa fb edge.1).card≤6 then
  (vv I C ve fa fb edge.1).biUnion λ l=>((univ:_3 N).filter λ p=>p∈K7.vS C h.2.1.choose∧(p,l)∈F4∧I p l).image λ p=>(p,l)
  else ∅
 have vR:qq⊆NF.biUnion λ v=>if vZ I C v then ((M9.v6 N C v).toFinset.biUnion λ c=>q7 (v,c))∪j5 v else (M9.v6 N C v).toFinset.biUnion λ c=>ph (v,c)∪xt (v,c):=by
  intro⟨p,l⟩ he;obtain⟨wK,Xx⟩:=zu (p,l) he;rcases Xx with ⟨v,c,R0,v4,xo,hk,XY⟩ | ⟨a,b,UJ,Vm,Vl,XY,xS⟩ | ⟨u,yy,UJ,v4,⟨c_top,hed_top,bV⟩,VH,UC⟩ | ⟨yy,v4,⟨c_top,hed_top,bV⟩,VH,UC⟩
  · have R9:v∈NF:=zd C v v4.choose v4.choose_spec.1;have hc:=((M9.wA N C v c).mp R0).2;refine _F ⟨v,R9,?_⟩
    rw[_O v4];refine _D _ (_F ⟨c,_v.mpr hc,?_⟩)
    have zy:vZ I C v∧(vt I C ve c).card≤6:=⟨v4,hk⟩;dsimp only[q7];rw[_Q zy];have z1:p∈K7.vS C zy.1.choose:=by rw[yQ];have xo':=xo.2;rw[M9.xK,zy.1.choose_spec.1] at xo';simp only[Option.elim_some] at xo';exact xo'
    exact _F ⟨l,XY,_W ⟨p,_B ⟨_H _,z1,Ya he,wK⟩,rfl⟩⟩
  · obtain⟨Mz,WP⟩:=mS a b UJ;refine _F ⟨a,Mz,?_⟩
    rw[if_neg UJ.2];refine _F ⟨b,_v.mpr WP,_D _ ?_⟩
    have zy:vj I C a b∧7≤(vt I C ve a).card∧(vt I C ve b).card≤6:=⟨UJ,Vm,Vl⟩;dsimp only[ph];rw[_Q zy];exact _B ⟨_R ⟨_B ⟨_H _,xS⟩,XY⟩,wK⟩
  · obtain⟨Qi,RR⟩:=mS u yy UJ;refine _F ⟨u,Qi,?_⟩
    rw[if_neg UJ.2];refine _F ⟨yy,_v.mpr RR,_G _ ?_⟩
    have zy:vj I C u yy∧vZ I C yy∧(vv I C ve fa fb u).card≤6:=⟨UJ,v4,VH⟩;dsimp only[xt];rw[_Q zy];have z1:p∈K7.vS C zy.2.1.choose:=by rw[yQ];have xo':=bV.2;rw[M9.xK,zy.2.1.choose_spec.1] at xo';simp only[Option.elim_some] at xo';exact xo'
    exact _F ⟨l,UC,_W ⟨p,_B ⟨_H _,z1,Ya he,wK⟩,rfl⟩⟩
  · have R9:yy∈NF:=zd C yy v4.choose v4.choose_spec.1;refine _F ⟨yy,R9,?_⟩
    rw[_O v4];refine _G _ ?_
    have zy:vZ I C yy∧(vv I C ve fa fb yy).card≤6:=⟨v4,VH⟩;dsimp only[j5];rw[_Q zy];have z1:p∈K7.vS C zy.1.choose:=by rw[yQ];have xo':=bV.2;rw[M9.xK,zy.1.choose_spec.1] at xo';simp only[Option.elim_some] at xo';exact xo'
    exact _F ⟨l,UC,_W ⟨p,_B ⟨_H _,z1,Ya he,wK⟩,rfl⟩⟩
 have kr:∀ v (v4:vZ I C v) (l:Fin N),((univ:_3 N).filter λ p=>p∈K7.vS C v4.choose∧(p,l)∈F4∧I p l).card≤4:=by
  intro v v4 l;by_cases xR:((univ:_3 N).filter λ p=>p∈K7.vS C v4.choose∧(p,l)∈F4∧I p l).Nonempty
  · obtain⟨p₀,hp₀⟩:=xR;have hp₀':=(_A hp₀).2
    have bI:(C.lineDegrees (N+N) (Ico N (N+N))).getD v4.choose 0≤1:=by have hz:=M9.zZ N C v v4.choose v4.choose_spec.1;change (C.lineDegrees (N+N) (Ico N (N+N))).getD v4.choose 0=0 at hz;omega
    have h4:=y7 I C v4.choose bI v4.choose_spec.2 p₀ l
     hp₀'.2.2 hp₀'.1 (z6 (p₀,l) hp₀'.2.1)
    refine (_C ?_).trans h4
    intro q hq;have hq':=(_A hq).2;exact _B ⟨hq'.1,hq'.2.2⟩
  · rw[_w.mp xR];simp
 refine (_C vR).trans ?_
 refine (_E NF _ 50 ?_).trans (by dsimp only[NF];omega)
 intro v _;have Y3:=Mc.uM N C v (λ g hg=>(hm g hg).2);split_ifs with v4
 · have Ud:(M9.vo N C v).isSome=true:=by rw[v4.choose_spec.1];rfl
   have Uc:(M9.v6 N C v).length≤1:=by rw[_O Ud] at Y3;omega
   have hch1:(M9.v6 N C v).toFinset.card≤1:=(_u _).trans Uc;have Oj:∀ c,(q7 (v,c)).card≤24:=by
    intro c;dsimp only[q7];split_ifs with h
    · refine (_E _ _ 4 ?_).trans (by nlinarith [h.2])
      intro l _;exact _T.trans (kr v h.1 l)
    · simp
   have htv_v:(j5 v).card≤24:=by
    dsimp only[j5];split_ifs with h
    · refine (_E _ _ 4 ?_).trans (by nlinarith [h.2])
      intro l _;exact _T.trans (kr v h.1 l)
    · simp
   have h1:((M9.v6 N C v).toFinset.biUnion λ c=>q7 (v,c)).card≤24:=(_E _ _ 24 (λ c _=>Oj c)).trans (by nlinarith);have hu:=_J ((M9.v6 N C v).toFinset.biUnion λ c=>q7 (v,c))
    (j5 v)
   omega
 · have V7:(M9.v6 N C v).length≤2:=by
    split_ifs at Y3 <;> omega
   have hch2:(M9.v6 N C v).toFinset.card≤2:=(_u _).trans V7;refine (_E _ _ 25 ?_).trans (by nlinarith)
   intro c _;by_cases VZ:vZ I C c
   · have U8:ph (v,c)=∅:=by
      dsimp only[ph];split_ifs with h
      · rw[nr I C ve c VZ];simp
      · rfl
     rw[U8,Finset.empty_union];dsimp only[xt];split_ifs with h
     · refine (_E _ _ 4 ?_).trans (by nlinarith [h.2.2])
       intro l _;exact _T.trans (kr c h.2.1 l)
     · simp
   · have U9:xt (v,c)=∅:=by
      dsimp only[xt];rw[dif_neg (λ h=>VZ h.2.1)]
     rw[U9,Finset.union_empty];dsimp only[ph];split_ifs with h
     · obtain⟨U7,Qd,T2⟩:=_N h.2.1;let Lk:Fin N→ ℕ:=λ u=>if hu:u∈vt I C ve v then (_A hu).2.choose else 0;let Mj:Fin N→ Fin 2:=λ u=>if hu:u∈vt I C ve v then (_A hu).2.choose_spec.2.choose else 0;let P:=(univ:_3 N).filter λ p=>(vJ I C ve vf v p).card≤2
       have MP:P.card≤12:=by
        refine uA I hI U7 T2 (λ u=>vY I C ve vf (Lk u) (Mj u) u) (λ u _=>xl I hI C ve vf (Lk u) (Mj u) u) P ?_
        intro p hp;have Tm:=(_A hp).2;refine (_C ?_).trans Tm
        intro u hu;obtain⟨Th,R6,Sb⟩:=_A hu;have Vb:=Qd Th;have wr:=(_A Vb).2;have hw:=wr.choose_spec.1;have WN:=wr.choose_spec.2.choose_spec;simp only[Lk,Mj,_Q Vb] at Sb;exact _B ⟨Vb,R6,wr.choose,hw,wr.choose_spec.2.choose,WN.1,WN.2.2.2,Sb⟩
       exact pp I hI P (vt I C ve c) MP h.2.2
     · simp
private lemma qg {J N:ℕ} (I:_0 N) [_4 I] (C:_a) (fa fb:Fin J→ ℕ) (ve:ℕ→_3 N) (F4:_2 N) (z6:∀ e∈F4,(e.1,e.2)∉v2 I C) (kn:_2 N) (Xm:kn⊆F4) (PZ:∀ e∈kn,I e.1 e.2∧∃ j:Fin J,((vZ I C (fa j)∧(∃ c:ℕ,(fa j,c)∈M9.vm N C∧M9.vl N C (ofFn (λ q=>decide (q=e.1))) (fa j) c)∧(vt I C ve (fb j)).card≤6∧e.2∈vt I C ve (fb j))∨(vZ I C (fb j)∧(∃ c:ℕ,(fb j,c)∈M9.vm N C∧M9.vl N C (ofFn (λ q=>decide (q=e.1))) (fb j) c)∧(vt I C ve (fa j)).card≤6∧e.2∈vt I C ve (fa j)))):kn.card≤48*J:=by
 classical
 have kr:∀ v (v4:vZ I C v) (l:Fin N),((univ:_3 N).filter λ p=>p∈K7.vS C v4.choose∧(p,l)∈F4∧I p l).card≤4:=by
  intro v v4 l;by_cases xR:((univ:_3 N).filter λ p=>p∈K7.vS C v4.choose∧(p,l)∈F4∧I p l).Nonempty
  · obtain⟨p₀,hp₀⟩:=xR;have hp₀':=(_A hp₀).2
    have bI:(C.lineDegrees (N+N) (Ico N (N+N))).getD v4.choose 0≤1:=by have hz:=M9.zZ N C v v4.choose v4.choose_spec.1;change (C.lineDegrees (N+N) (Ico N (N+N))).getD v4.choose 0=0 at hz;omega
    have h4:=y7 I C v4.choose bI v4.choose_spec.2 p₀ l
     hp₀'.2.2 hp₀'.1 (z6 (p₀,l) hp₀'.2.1)
    refine (_C ?_).trans h4
    intro q hq;have hq':=(_A hq).2;exact _B ⟨hq'.1,hq'.2.2⟩
  · rw[_w.mp xR];simp
 let JS:=(univ:Finset (Fin J))×ˢ (univ:Finset (Fin 2));have vR:kn⊆JS.biUnion λ js=>
  let v:=if js.2=0 then fa js.1 else fb js.1;let u:=if js.2=0 then fb js.1 else fa js.1;if h:vZ I C v∧(vt I C ve u).card≤6 then (vt I C ve u).biUnion λ l=>((univ:_3 N).filter λ p=>p∈K7.vS C h.1.choose∧(p,l)∈F4∧I p l).image λ p=>(p,l)
  else ∅:=by
  intro⟨p,l⟩ he;obtain⟨wK,j,Xx⟩:=PZ (p,l) he;rcases Xx with ⟨v4,⟨c,_,xo⟩,h6,XY⟩ | ⟨v4,⟨c,_,xo⟩,h6,XY⟩
  · refine _F ⟨(j,0),_R ⟨_H _,_H _⟩,?_⟩
    dsimp only;rw[_O rfl,_O rfl];have zy:vZ I C (fa j)∧(vt I C ve (fb j)).card≤6:=⟨v4,h6⟩;rw[_Q zy];have z1:p∈K7.vS C zy.1.choose:=by rw[yQ];have xo':=xo.2;rw[M9.xK,zy.1.choose_spec.1] at xo';simp only[Option.elim_some] at xo';exact xo'
    exact _F ⟨l,XY,_W ⟨p,_B ⟨_H _,z1,Xm he,wK⟩,rfl⟩⟩
  · refine _F ⟨(j,1),_R ⟨_H _,_H _⟩,?_⟩
    dsimp only;rw[if_neg (by decide),if_neg (by decide)];have zy:vZ I C (fb j)∧(vt I C ve (fa j)).card≤6:=⟨v4,h6⟩;rw[_Q zy];have z1:p∈K7.vS C zy.1.choose:=by rw[yQ];have xo':=xo.2;rw[M9.xK,zy.1.choose_spec.1] at xo';simp only[Option.elim_some] at xo';exact xo'
    exact _F ⟨l,XY,_W ⟨p,_B ⟨_H _,z1,Xm he,wK⟩,rfl⟩⟩
 refine (_C vR).trans ?_
 refine (_E JS _ 24 ?_).trans ?_
 · intro js _;dsimp only;by_cases hjs0:js.2=0
   · simp only[hjs0,ite_true];split_ifs with h
     · refine (_E _ _ 4 ?_).trans (by nlinarith [h.2])
       intro l _;exact _T.trans (kr _ h.1 l)
     · simp
   · simp only[hjs0,ite_false];split_ifs with h
     · refine (_E _ _ 4 ?_).trans (by nlinarith [h.2])
       intro l _;exact _T.trans (kr _ h.1 l)
     · simp
 · have MS:JS.card=J*2:=by simp[JS]
   rw[MS];omega
private lemma wQ {J N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (g₀ g₁:Fin J→ ℕ) (hm:_b C) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (g₀ jb) false=true→(C.wires (ofFn zz)).getD (g₁ jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆
 v9 (vh N C) (vi I C) r q)
 (uN:ℕ→ Fin 2→ Fin N→_3 N)
 (ki:∀ w m l,(uN w m l).card≤1)
 (jy:∀(j:Fin J) (p:Fin N) (wa wb:ℕ) (ma mb:Fin 2) (la lb:Fin N),vE I C ve wa ma la→ vE I C ve wb mb lb→¬ I p la→¬ I p lb→ p∉vY I C ve vf wa ma la→ p∉vY I C ve vf wb mb lb→ lb∉uN wa ma la→ la∉uN wb mb lb→(_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₀ j) wa)→(_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₁ j) wb)→ False)
 (j:Fin J) (p:Fin N) (c₀ c₁:ℕ)
 (hc₀:_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (g₀ j) c₀)
 (hc₁:_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (g₁ j) c₁):
 (vJ I C ve vf c₀ p).card≤2∨(vJ I C ve vf c₁ p).card≤2:=by
 classical
 by_contra! uq;obtain⟨U₀,hU₀sub,hU₀card⟩:=_N uq.1;obtain⟨U₁,hU₁sub,hU₁card⟩:=_N uq.2;let w0:Fin N→ ℕ:=λ u=>if h:u∈vJ I C ve vf c₀ p then (_A h).2.2.choose else 0;let m0:Fin N→ Fin 2:=λ u=>if h:u∈vJ I C ve vf c₀ p then
  (_A h).2.2.choose_spec.2.choose else 0
 let w1:Fin N→ ℕ:=λ u=>if h:u∈vJ I C ve vf c₁ p then (_A h).2.2.choose else 0;let m1:Fin N→ Fin 2:=λ u=>if h:u∈vJ I C ve vf c₁ p then
  (_A h).2.2.choose_spec.2.choose else 0
 let bad₀:=(U₀×ˢ U₁).filter λ ab=>ab.2∈uN (w0 ab.1) (m0 ab.1) ab.1;let bad₁:=(U₀×ˢ U₁).filter λ ab=>ab.1∈uN (w1 ab.2) (m1 ab.2) ab.2;have hbad₀:bad₀.card≤ U₀.card:=by
  have vR:bad₀⊆U₀.biUnion λ a=>(U₁.filter λ b=>b∈uN (w0 a) (m0 a) a).image λ b=>(a,b):=by intro⟨a,b⟩ fP;obtain⟨zA,yH⟩:=_A fP;obtain⟨ha,hb⟩:=_Y zA;exact _F ⟨a,ha,_W ⟨b,_B ⟨hb,yH⟩,rfl⟩⟩
  refine (_C vR).trans ((_E U₀ _ 1 ?_).trans (by omega))
  intro a _;refine _T.trans ?_
  exact (_C λ x hx=>(_A hx).2).trans (ki (w0 a) (m0 a) a)
 have hbad₁:bad₁.card≤ U₁.card:=by
  have vR:bad₁⊆U₁.biUnion λ b=>(U₀.filter λ a=>a∈uN (w1 b) (m1 b) b).image λ a=>(a,b):=by intro⟨a,b⟩ fP;obtain⟨zA,yH⟩:=_A fP;obtain⟨ha,hb⟩:=_Y zA;exact _F ⟨b,hb,_W ⟨a,_B ⟨ha,yH⟩,rfl⟩⟩
  refine (_C vR).trans ((_E U₁ _ 1 ?_).trans (by omega))
  intro b _;refine _T.trans ?_
  exact (_C λ x hx=>(_A hx).2).trans (ki (w1 b) (m1 b) b)
 have z5:(bad₀∪bad₁).card < (U₀×ˢ U₁).card:=by have hu:=_J bad₀ bad₁;rw[_m,hU₀card,hU₁card];omega
 have xR:((U₀×ˢ U₁)\(bad₀∪bad₁)).Nonempty:=by rw[← card_pos];have hs:=_z (U₀×ˢ U₁) (bad₀∪bad₁);have hi:=_C (inter_subset_right:(U₀×ˢ U₁)∩(bad₀∪bad₁)⊆bad₀∪bad₁);omega
 obtain⟨⟨la,lb⟩,yH⟩:=xR;obtain⟨zA,x9⟩:=_M yH;obtain⟨Lt,Mi⟩:=_Y zA;have WL:lb∉uN (w0 la) (m0 la) la:=λ h=>x9 (_D _ (_B ⟨zA,h⟩));have WF:la∉uN (w1 lb) (m1 lb) lb:=λ h=>x9 (_G _ (_B ⟨zA,h⟩));have Rw:=hU₀sub Lt;have Qp:=hU₁sub Mi;have QP:=(_A Rw).2;have QM:=(_A Qp).2;let wa:=QP.2.choose;let ma:=QP.2.choose_spec.2.choose;let wb:=QM.2.choose;let mb:=QM.2.choose_spec.2.choose;have Rs:¬ I p la:=QP.1;have QW:¬ I p lb:=QM.1;have Xf:=QP.2.choose_spec.2.choose_spec;have YP:=QM.2.choose_spec.2.choose_spec;have Rd:w0 la=wa:=by dsimp only[w0];rw[_Q Rw]
 have RM:m0 la=ma:=by dsimp only[m0];rw[_Q Rw]
 have R2:w1 lb=wb:=by dsimp only[w1];rw[_Q Qp]
 have SB:m1 lb=mb:=by dsimp only[m1];rw[_Q Qp]
 rw[Rd,RM] at WL;rw[R2,SB] at WF;have mP:_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₀ j) wa:=ReflTransGen.trans
  (ReflTransGen.mono (λ _ _ h=>Or.inl h) _ _ hc₀)
  (ReflTransGen.mono (λ _ _ h=>Or.inr h) _ _ Xf.1)
 have mQ:_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₁ j) wb:=ReflTransGen.trans
  (ReflTransGen.mono (λ _ _ h=>Or.inl h) _ _ hc₁)
  (ReflTransGen.mono (λ _ _ h=>Or.inr h) _ _ YP.1)
 by_cases zD:la=lb
 · subst zD;exact z2 I hI C g₀ g₁ hm vM ve vf j p wa wb ma mb la Xf.2.1 YP.2.1 Rs Xf.2.2 YP.2.2 mP mQ
 · exact jy j p wa wb ma mb la lb Xf.2.1 YP.2.1 Rs QW Xf.2.2 YP.2.2 WL WF mP mQ
private lemma kO {J N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (fa fb:Fin J→ ℕ) (r v:ℕ) (wP:_1 (vj I C) r v) (hv7:7≤(vv I C ve fa fb v).card):(7≤(vv I C ve fa fb r).card)∨∃ u x₀:ℕ,vj I C u x₀∧_1 (vj I C) r u∧_1 (vj I C) x₀ v∧(vv I C ve fa fb u).card≤6∧7≤(vv I C ve fa fb x₀).card:=by
 by_cases hr7:7≤(vv I C ve fa fb r).card
 · exact Or.inl hr7
 · right
   have Lz:∀ r0,_1 (vj I C) r0 v→(vv I C ve fa fb r0).card≤6→∃ u x₀:ℕ,vj I C u x₀∧_1 (vj I C) r0 u∧_1 (vj I C) x₀ v∧(vv I C ve fa fb u).card≤6∧7≤(vv I C ve fa fb x₀).card:=by
    intro r0 hp h6;induction hp using ReflTransGen.head_induction_on with
    | refl=>omega
    | head zl hrest ih=>
     rename_i a b
     by_cases hb7:7≤(vv I C ve fa fb b).card
     · exact⟨a,b,zl,.refl,hrest,h6,hb7⟩
     · obtain⟨u,x₀,U4,hbu,Pd,QN,hx7⟩:=ih (by omega);exact⟨u,x₀,U4,.head zl hbu,Pd,QN,hx7⟩
   exact Lz r wP (by omega)
private lemma xq {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (u v:ℕ) (hp:_1 (vj I C) u v):vt I C ve v⊆vt I C ve u:=by
 induction hp using ReflTransGen.head_induction_on with
 | refl=>exact Finset.Subset.refl _
 | head h _ ih=>exact ih.trans (n3 I C ve _ _ h)
private lemma wS {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (u v:ℕ) (p:Fin N) (hp:_1 (vj I C) u v):vJ I C ve vf v p⊆vJ I C ve vf u p:=h9 I C ve vf u v p hp
private lemma po {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (p l:Fin N) (g w:ℕ) (m:Fin 2) (hp:_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) g w) (ht:vE I C ve w m l):((∃ v c:ℕ,(v,c)∈M9.vm N C∧vZ I C v∧M9.vl N C (ofFn (λ q=>decide (q=p))) v c∧
 (vt I C ve c).card≤6∧l∈vt I C ve c)∨(∃ a b:ℕ,vj I C a b∧7≤(vt I C ve a).card∧(vt I C ve b).card≤6∧l∈vt I C ve b∧(vJ I C ve vf a p).card≤2))∨(∃ c:ℕ,_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) g c∧3≤(vJ I C ve vf c p).card∧∃ a b:ℕ,vj I C a b∧_1 (vj I C) c a∧_1 (vj I C) b w∧7≤(vt I C ve a).card∧(vt I C ve b).card≤6∧l∈vt I C ve b∧3≤(vJ I C ve vf a p).card)∨(_1 (vj I C) g w∧(vt I C ve g).card≤6∧l∈vt I C ve g):=by
 classical
 have QE:l∈vt I C ve w:=_B ⟨_H _,w,ht.1,m,.refl,ht.2.1,ht.2.2.1,ht⟩;have PF:(vt I C ve w).card≤6:=jY I C ve w ht.1;rcases nf I C (ofFn (λ q=>decide (q=p))) g w hp with nJ | ⟨v,c,Vi,RR,v4,Xc⟩
 · have LR:l∈vt I C ve g:=xq I C ve g w nJ QE;by_cases hg6:(vt I C ve g).card≤6
   · exact Or.inr (Or.inr ⟨nJ,hg6,LR⟩)
   · obtain⟨a,b,fP,LG,V8,Vm,Vl⟩:=kW I C ve g w nJ (by omega) PF;have pv:l∈vt I C ve b:=xq I C ve b w V8 QE;by_cases Wt:(vJ I C ve vf a p).card≤2
     · exact Or.inl (Or.inr ⟨a,b,fP,Vm,Vl,pv,Wt⟩)
     · have T4:3≤(vJ I C ve vf g p).card:=by
        have hs:=_C (wS I C ve vf g a p LG);omega
       exact Or.inr (Or.inl ⟨g,.refl,T4,a,b,fP,LG,V8,Vm,Vl,pv,by omega⟩)
 · have cI:l∈vt I C ve c:=xq I C ve c w Xc QE;by_cases Rc:(vt I C ve c).card≤6
   · exact Or.inl (Or.inl ⟨v,c,RR.1,v4,RR,Rc,cI⟩)
   · obtain⟨a,b,fP,cz,V8,Vm,Vl⟩:=kW I C ve c w Xc (by omega) PF;have pv:l∈vt I C ve b:=xq I C ve b w V8 QE;by_cases Wt:(vJ I C ve vf a p).card≤2
     · exact Or.inl (Or.inr ⟨a,b,fP,Vm,Vl,pv,Wt⟩)
     · have Tw:3≤(vJ I C ve vf c p).card:=by
        have hs:=_C (wS I C ve vf c a p cz);omega
       exact Or.inr (Or.inl ⟨c,Vi.trans (.single RR),Tw,a,b,fP,cz,V8,Vm,Vl,pv,by omega⟩)
private def xJ {J N:ℕ} (I:_0 N) [_4 I] (C:_a) (fa fb:Fin J→ ℕ) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (p l:Fin N) (j:Fin J) (Xy d0:Fin J→ ℕ) (WY XC:ℕ) (Tb U6:Fin 2):Prop:=vE I C ve WY Tb l∧vE I C ve XC U6 l∧p∉vY I C ve vf WY Tb l∧p∉vY I C ve vf XC U6 l∧_1 (vj I C) (Xy j) WY∧(vt I C ve (Xy j)).card≤6∧
 l∈vt I C ve (Xy j)∧_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (d0 j) XC∧∃ Wq a b x₀ yy c_top:ℕ,_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (d0 j) Wq∧vj I C a b∧_1 (vj I C) Wq a∧_1 (vj I C) b XC∧7≤(vt I C ve a).card∧(vt I C ve b).card≤6∧l∈vt I C ve b∧3≤(vJ I C ve vf a p).card∧_1 (vj I C) (d0 j) x₀∧_1 (vj I C) x₀ yy∧M9.vl N C (ofFn (λ q=>decide (q=p))) yy c_top∧vZ I C yy∧_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) yy Wq∧7≤(vv I C ve fa fb x₀).card∧(x₀=d0 j∨∃ u:ℕ,vj I C u x₀∧_1 (vj I C) (d0 j) u∧
  (vv I C ve fa fb u).card≤6)
private def fA {J N:ℕ} (I:_0 N) [_4 I] (C:_a) (fa fb:Fin J→ ℕ) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (e:Fin N× Fin N):Prop:=I e.1 e.2∧(e.1,e.2)∉v2 I C∧∃(j:Fin J) (g₀ g₁:Fin J→ ℕ),((g₀=fa∧g₁=fb)∨(g₀=fb∧g₁=fa))∧∃(w₀ w₁:ℕ) (m₀ m₁:Fin 2),vk (vh N C) (vc I C) (vr N C (vd N C w₀ m₀))={e.2}∧(xJ I C fa fb ve vf e.1 e.2 j g₀ g₁ w₀ w₁ m₀ m₁∨
 xJ I C fa fb ve vf e.1 e.2 j g₁ g₀ w₁ w₀ m₁ m₀)
private lemma pR {J N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (fa jb) false=true→(C.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆
 v9 (vh N C) (vi I C) r q)
 (uN:ℕ→ Fin 2→ Fin N→_3 N)
 (ki:∀ w m l,(uN w m l).card≤1)
 (jy:∀(g₀ g₁:Fin J→ ℕ),((g₀=fa∧g₁=fb)∨(g₀=fb∧g₁=fa))→∀(j:Fin J) (p:Fin N) (wa wb:ℕ) (ma mb:Fin 2) (la lb:Fin N),vE I C ve wa ma la→ vE I C ve wb mb lb→¬ I p la→¬ I p lb→ p∉vY I C ve vf wa ma la→ p∉vY I C ve vf wb mb lb→ lb∉uN wa ma la→ la∉uN wb mb lb→(_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₀ j) wa)→(_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₁ j) wb)→ False)
 (F4:_2 N)
 (z6:∀ e∈F4,(e.1,e.2)∉v2 I C)
 (E':_2 N)
 (bG:E'⊆F4)
 (mf:∀ e∈E',I e.1 e.2∧∃(j:Fin J) (g₀ g₁:Fin J→ ℕ),((g₀=fa∧g₁=fb)∨(g₀=fb∧g₁=fa))∧∃(w₀ w₁:ℕ) (m₀ m₁:Fin 2),_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (g₀ j) w₀∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (g₁ j) w₁∧vk (vh N C) (vc I C) (vr N C (vd N C w₀ m₀))={e.2}∧vE I C ve w₀ m₀ e.2∧vE I C ve w₁ m₁ e.2):
 ∃ uE⊆E',E'.card≤18*(Mc.vI N C).card+50*(Mc.vP N C\Mc.vI N C).card+48*J+uE.card∧∀ e∈uE,fA I C fa fb ve vf e:=by
 classical
 let V3:Fin N× Fin N→ Prop:=λ e=>I e.1 e.2∧((∃ v c:ℕ,(v,c)∈M9.vm N C∧vZ I C v∧M9.vl N C (ofFn (λ q=>decide (q=e.1))) v c∧(vt I C ve c).card≤6∧e.2∈vt I C ve c)∨(∃ a b:ℕ,vj I C a b∧7≤(vt I C ve a).card∧(vt I C ve b).card≤6∧e.2∈vt I C ve b∧(vJ I C ve vf a e.1).card≤2)∨(∃ u yy:ℕ,vj I C u yy∧vZ I C yy∧(∃ c_top:ℕ,(yy,c_top)∈M9.vm N C∧M9.vl N C (ofFn (λ q=>decide (q=e.1))) yy c_top)∧(vv I C ve fa fb u).card≤6∧e.2∈vv I C ve fa fb u)∨(∃ yy:ℕ,vZ I C yy∧(∃ c_top:ℕ,(yy,c_top)∈M9.vm N C∧M9.vl N C (ofFn (λ q=>decide (q=e.1))) yy c_top)∧(vv I C ve fa fb yy).card≤6∧
  e.2∈vv I C ve fa fb yy))
 let Q6:Fin N× Fin N→ Prop:=λ e=>∃ w∈Mc.vI N C,∃ m:Fin 2,e.2∈vk (vh N C) (vc I C) (vr N C (vd N C w m))∧(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C w m))).card≤3∧e.1∈vY I C ve vf w m e.2;let X7:Fin N× Fin N→ Prop:=λ e=>I e.1 e.2∧∃ j:Fin J,((vZ I C (fa j)∧(∃ c:ℕ,(fa j,c)∈M9.vm N C∧M9.vl N C (ofFn (λ q=>decide (q=e.1))) (fa j) c)∧(vt I C ve (fb j)).card≤6∧e.2∈vt I C ve (fb j))∨(vZ I C (fb j)∧(∃ c:ℕ,(fb j,c)∈M9.vm N C∧M9.vl N C (ofFn (λ q=>decide (q=e.1))) (fb j) c)∧(vt I C ve (fa j)).card≤6∧e.2∈vt I C ve (fa j)));let dh:=E'.filter Q6;let fM:=E'.filter V3;let kn:=E'.filter X7;let uE:=((E'\dh)\fM)\kn
 have hE_mp:dh.card≤18*(Mc.vI N C).card:=qF I hI C ve vf dh λ e he=>(_A he).2;have hE_dlc:fM.card≤50*(Mc.vP N C\Mc.vI N C).card:=uT I hI C fa fb hm ve vf F4 z6 fM
  ((filter_subset _ _).trans bG) λ e he=>(_A he).2
 have hE_root:kn.card≤48*J:=qg I C fa fb ve F4 z6 kn
  ((filter_subset _ _).trans bG) λ e he=>(_A he).2
 have Xi:uE⊆E':=Finset.sdiff_subset.trans (Finset.sdiff_subset.trans Finset.sdiff_subset);have xV:E'.card≤ dh.card+fM.card+kn.card+uE.card:=by
  have zu:E'⊆dh∪fM∪kn∪uE:=by
   intro e he;by_cases h1:e∈dh
   · exact _D _ (_D _ (_D _ h1))
   · by_cases h2:e∈fM
     · exact _D _ (_D _ (_G _ h2))
     · by_cases h3:e∈kn
       · exact _D _ (_G _ h3)
       · exact _G _ (_V ⟨_V ⟨_V ⟨he,h1⟩,h2⟩,h3⟩)
  have Vh:=_C zu;have Xt:=_J (dh∪fM∪kn) uE;have Y9:=_J (dh∪fM) kn;have LF:=_J dh fM;omega
 refine⟨uE,Xi,by omega,?_⟩
 intro⟨p,l⟩ pw;have UG':(p,l)∈E':=Xi pw;have Zy:¬ X7 (p,l):=by intro h;exact (_M pw).2 (_B ⟨UG',h⟩)
 have Sx:=(_M pw).1;have bk:¬ V3 (p,l):=by intro h;exact (_M Sx).2 (_B ⟨UG',h⟩)
 dsimp only[X7] at Zy;dsimp only[V3] at bk;have P9:=(_M Sx).1;have Tq:¬ Q6 (p,l):=λ h=>(_M P9).2 (_B ⟨UG',h⟩);obtain⟨wK,j,g₀,g₁,fF,w₀,w₁,m₀,m₁,hp₀,hp₁,hb₀,ht₀,ht₁⟩:=mf (p,l) UG';have V2:∀ w m,vE I C ve w m l→ p∉vY I C ve vf w m l:=by
  intro w m ht PI
  exact Tq ⟨w,ht.1,m,ht.2.1,ht.2.2.1,PI⟩
 have hnp₀:=V2 w₀ m₀ ht₀;have hnp₁:=V2 w₁ m₁ ht₁;have jr:∀{g w m},_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) g w→ vE I C ve w m l→(∃ c:ℕ,_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) g c∧3≤(vJ I C ve vf c p).card∧∃ a b:ℕ,vj I C a b∧_1 (vj I C) c a∧_1 (vj I C) b w∧7≤(vt I C ve a).card∧(vt I C ve b).card≤6∧l∈vt I C ve b∧3≤(vJ I C ve vf a p).card)∨(_1 (vj I C) g w∧(vt I C ve g).card≤6∧l∈vt I C ve g):=by
  intro g w m hp ht;rcases po I C ve vf p l g w m hp ht with hdlc | f3
  · exfalso;apply bk
    refine⟨wK,?_⟩
    rcases hdlc with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact f3
 have Tn:∀{c₀ c₁},_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (g₀ j) c₀→_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (g₁ j) c₁→3≤(vJ I C ve vf c₀ p).card→3≤(vJ I C ve vf c₁ p).card→ False:=by
  intro c₀ c₁ hc₀ hc₁ LD O3;have cX:(vJ I C ve vf c₀ p).card≤2∨(vJ I C ve vf c₁ p).card≤2:=by
   rcases fF with ⟨hg₀,hg₁⟩ | ⟨hg₀,hg₁⟩
   · have hc₀':_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (fa j) c₀:=by
      simpa[hg₀] using hc₀
     have hc₁':_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (fb j) c₁:=by simpa[hg₁] using hc₁
     exact wQ I hI C fa fb hm vM ve vf uN ki (jy fa fb (Or.inl ⟨rfl,rfl⟩)) j p c₀ c₁ hc₀' hc₁'
   · have hc₁':_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (fa j) c₁:=by
      simpa[hg₁] using hc₁
     have hc₀':_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (fb j) c₀:=by simpa[hg₀] using hc₀
     exact (wQ I hI C fa fb hm vM ve vf uN ki (jy fa fb (Or.inl ⟨rfl,rfl⟩)) j p c₁ c₀ hc₁' hc₀').symm
  omega
 have n1:_1 (vj I C) (g₀ j) w₀→_1 (vj I C) (g₁ j) w₁→ False:=by
  intro T7 Vh;have ZR:l∈vk (vh N C) (vc I C) (vr N C (vD N C w₁))∨13≤(ve (vr N C (vD N C w₁))\univ.filter λ q=>I q l).card:=by
   fin_cases m₁
   · exact Or.inl (by simpa[vd] using ht₁.2.1)
   · simpa[vd] using ht₁.2.2.2
  have Z3:l∈vk (vh N C) (vc I C) (vr N C (vz N C w₁))∨13≤(ve (vr N C (vz N C w₁))\univ.filter λ q=>I q l).card:=by
   fin_cases m₁
   · simpa[vd] using ht₁.2.2.2
   · exact Or.inl (by simpa[vd] using ht₁.2.1)
  rcases fF with ⟨hg₀,hg₁⟩ | ⟨hg₀,hg₁⟩
  · exact wM I hI C fa fb hm vM ve vf j w₀ w₁ ht₀.1 ht₁.1 m₀ l hb₀ (by simpa[hg₀] using T7) (by simpa[hg₁] using Vh) ht₀.2.2.2 ZR Z3
  · exact wM I hI C fb fa hm (λ jb zz h1 h0=>vM jb zz h0 h1) ve vf j w₀ w₁ ht₀.1 ht₁.1 m₀ l hb₀ (by simpa[hg₀] using T7) (by simpa[hg₁] using Vh) ht₀.2.2.2 ZR Z3
 have ZC:∀(Xy d0:Fin J→ ℕ) (WY XC:ℕ) (Tb U6:Fin 2),((Xy=fa∧d0=fb)∨(Xy=fb∧d0=fa))→(_1 (vj I C) (Xy j) WY→_1 (vj I C) (d0 j) XC→ False)→ vE I C ve WY Tb l→ vE I C ve XC U6 l→ p∉vY I C ve vf WY Tb l→ p∉vY I C ve vf XC U6 l→_1 (vj I C) (Xy j) WY→(vt I C ve (Xy j)).card≤6→ l∈vt I C ve (Xy j)→_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (d0 j) XC→(∃ c:ℕ,_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (d0 j) c∧3≤(vJ I C ve vf c p).card∧∃ a b:ℕ,vj I C a b∧_1 (vj I C) c a∧_1 (vj I C) b XC∧
  7≤(vt I C ve a).card∧(vt I C ve b).card≤6∧l∈vt I C ve b∧3≤(vJ I C ve vf a p).card)∨(_1 (vj I C) (d0 j) XC∧(vt I C ve (d0 j)).card≤6∧l∈vt I C ve (d0 j))→ xJ I C fa fb ve vf p l j Xy d0 WY XC Tb U6:=by
  intro Xy d0 WY XC Tb U6 W9 Uz LY KF NU Nb cL Rc cI KT gX;refine⟨LY,KF,NU,Nb,cL,Rc,cI,KT,?_⟩
  rcases gX with ⟨Wq,hgc_d,_,a,b,fP,cz,V8,Vm,Vl,pv,OR⟩ | ⟨VI,_,_⟩
  · rcases ww I C (ofFn (λ q=>decide (q=p))) (d0 j) Wq hgc_d with ZM | ⟨yy,c_top,hgd_vt,hvt_ct,ms,hct_cd⟩
    · exact False.elim (Uz cL (ZM.trans (cz.trans (.head fP V8))))
    · have Z7:_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) yy Wq:=.head hvt_ct hct_cd
      have Re:∀ u,_1 (vj I C) (d0 j) u→ l∈vv I C ve fa fb u:=by
       intro u Pi;refine _B ⟨_H _,j,?_⟩
       rcases W9 with ⟨hgc,cu⟩ | ⟨hgc,cu⟩
       · exact Or.inl ⟨by simpa[cu] using Pi,by simpa[hgc] using Rc,by simpa[hgc] using cI⟩
       · exact Or.inr ⟨by simpa[cu] using Pi,by simpa[hgc] using Rc,by simpa[hgc] using cI⟩
      have hvt_ne:yy≠d0 j:=by
       intro zD;subst zD;apply Zy
       refine⟨wK,j,?_⟩
       rcases W9 with ⟨hgc,cu⟩ | ⟨hgc,cu⟩
       · exact Or.inr ⟨by simpa[cu] using ms,⟨c_top,by simpa[cu] using hvt_ct.1,by simpa[cu] using hvt_ct⟩,by simpa[hgc] using Rc,by simpa[hgc] using cI⟩
       · exact Or.inl ⟨by simpa[cu] using ms,⟨c_top,by simpa[cu] using hvt_ct.1,by simpa[cu] using hvt_ct⟩,by simpa[hgc] using Rc,by simpa[hgc] using cI⟩
      have NL:7≤(vv I C ve fa fb yy).card:=by by_contra h6;exact bk ⟨wK,Or.inr (Or.inr (Or.inr ⟨yy,ms,⟨c_top,hvt_ct.1,hvt_ct⟩,by omega,Re yy hgd_vt⟩))⟩
      refine⟨Wq,a,b,?_⟩
      rcases kO I C ve fa fb (d0 j) yy hgd_vt NL with hgd7 | ⟨u,x₀,U4,hgdu,hxvt,QN,hx7⟩
      · exact⟨d0 j,yy,c_top,hgc_d,fP,cz,V8,Vm,Vl,pv,OR,.refl,hgd_vt,hvt_ct,ms,Z7,hgd7,Or.inl rfl⟩
      · exact⟨x₀,yy,c_top,hgc_d,fP,cz,V8,Vm,Vl,pv,OR,hgdu.trans (.single U4),hxvt,hvt_ct,ms,Z7,hx7,Or.inr ⟨u,U4,hgdu,QN⟩⟩
  · exact False.elim (Uz cL VI)
 refine⟨wK,(z6 (p,l) (bG UG')),j,g₀,g₁,fF,w₀,w₁,m₀,m₁,hb₀,?_⟩
 rcases jr hp₀ ht₀ with ⟨c₀,hgc₀,LD,_,_,_,_,_,_,_,_,_⟩ | ⟨hclean₀,hc6₀,hlc₀⟩
 · rcases jr hp₁ ht₁ with ⟨c₁,hgc₁,O3,_,_,_,_,_,_,_,_,_⟩ | ⟨hclean₁,hc6₁,hlc₁⟩
   · exact False.elim (Tn hgc₀ hgc₁ LD O3)
   · have bn:(g₁=fa∧g₀=fb)∨(g₁=fb∧g₀=fa):=by
      rcases fF with ⟨hg₀,hg₁⟩ | ⟨hg₀,hg₁⟩
      · exact Or.inr ⟨hg₁,hg₀⟩
      · exact Or.inl ⟨hg₁,hg₀⟩
     exact Or.inr (ZC g₁ g₀ w₁ w₀ m₁ m₀ bn (λ h1 h0=>n1 h0 h1) ht₁ ht₀ hnp₁ hnp₀ hclean₁ hc6₁ hlc₁ hp₀ (jr hp₀ ht₀))
 · exact Or.inl (ZC g₀ g₁ w₀ w₁ m₀ m₁ fF n1 ht₀ ht₁ hnp₀ hnp₁ hclean₀ hc6₀ hlc₀ hp₁ (jr hp₁ ht₁))
private lemma co {J N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (fa jb) false=true→(C.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q)
 (uN:ℕ→ Fin 2→ Fin N→_3 N)
 (ki:∀ w m l,(uN w m l).card≤1)
 (jy:∀(g₀ g₁:Fin J→ ℕ),((g₀=fa∧g₁=fb)∨(g₀=fb∧g₁=fa))→∀(j:Fin J) (p:Fin N) (wa wb:ℕ) (ma mb:Fin 2) (la lb:Fin N),vE I C ve wa ma la→ vE I C ve wb mb lb→¬ I p la→¬ I p lb→ p∉vY I C ve vf wa ma la→ p∉vY I C ve vf wb mb lb→ lb∉uN wa ma la→ la∉uN wb mb lb→_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₀ j) wa→_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₁ j) wb→ False)
 (uE:_2 N)
 (Wc:∀ e∈uE,fA I C fa fb ve vf e):
 uE.card≤42*(Mc.vP N C\Mc.vI N C).card+42*J:=by
 classical
 let NF:=Mc.vP N C\Mc.vI N C;have mS:∀ x y,vj I C x y→ x∈NF∧y∈M9.v6 N C x:=by
  intro x y UJ;obtain⟨z5,hc⟩:=(M9.wA N C x y).mp UJ.1;have qX:0 < (M9.v6 N C x).length:=length_pos_of_mem hc;have hd:M9.yf N C x=2:=by by_contra xR;have h0:=Mc.zY N C x xR;omega
  have Pe:¬ M9.nM N C x:=λ hf=>by have h0:=Mc.yJ N C x hf;omega
  exact⟨_V ⟨_B ⟨mem_range.mpr z5,hd⟩,λ hm'=>Pe (_A hm').2⟩,hc⟩
 have Sa:∀ v∈NF,(M9.v6 N C v).toFinset.card≤2:=by
  intro v _;have Y3:=Mc.uM N C v (λ g hg=>(hm g hg).2);have V7:(M9.v6 N C v).length≤2:=by split_ifs at Y3 <;> omega
  exact (_u _).trans V7
 let dR:ℕ→_3 N:=λ x₀=>(univ:_3 N).filter λ p=>∃ a yy Wq:ℕ,_1 (vj I C) x₀ yy∧_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) yy Wq∧_1 (vj I C) Wq a∧3≤(vJ I C ve vf a p).card;have Yq:∀ x₀,7≤(vv I C ve fa fb x₀).card→(dR x₀).card≤9:=by
  intro x₀ hx₀7;obtain⟨L7,Rf,T1⟩:=_N hx₀7;have Z0:∀ la∈L7,∃ t:(Fin J→ ℕ)×(Fin J→ ℕ)× Fin J× ℕ× Fin 2,((t.1=fa∧t.2.1=fb)∨(t.1=fb∧t.2.1=fa))∧_1 (vj I C) (t.2.1 t.2.2.1) x₀∧_1 (vj I C) (t.1 t.2.2.1) t.2.2.2.1∧vE I C ve t.2.2.2.1 t.2.2.2.2 la:=by
   intro la nF;obtain⟨j',Xx⟩:=(_A (Rf nF)).2;rcases Xx with ⟨uS,_,hla_a⟩ | ⟨nS,_,hla_b⟩
   · obtain⟨SO,_,S7,Ug,_,_,Q2⟩:=(_A hla_a).2;exact⟨(fa,fb,j',SO,S7),Or.inl ⟨rfl,rfl⟩,uS,Ug,Q2⟩
   · obtain⟨SO,_,S7,Ug,_,_,Q2⟩:=(_A hla_b).2;exact⟨(fb,fa,j',SO,S7),Or.inr ⟨rfl,rfl⟩,nS,Ug,Q2⟩
  let dg:Fin N→ ℕ:=λ la=>if h:la∈L7 then (Z0 la h).choose.2.2.2.1 else 0;let d6:Fin N→ Fin 2:=λ la=>if h:la∈L7 then (Z0 la h).choose.2.2.2.2 else 0;let yc:Fin N→_3 N:=λ la=>vY I C ve vf (dg la) (d6 la) la;let pt:Fin N→_3 N:=λ la=>uN (dg la) (d6 la) la;refine uB I hI L7 T1 yc (λ la _=>xl I hI C ve vf (dg la) (d6 la) la) pt (λ la _=>ki (dg la) (d6 la) la) (dR x₀) ?_
  intro p hp;obtain⟨a,yy,Wq,Pd,RR,cz,h3⟩:=(_A hp).2;obtain⟨G3,R5,TO⟩:=_N h3;have b0:∀ lb∈G3,∃ wb:ℕ× Fin 2,¬ I p lb∧_1 (vj I C) a wb.1∧vE I C ve wb.1 wb.2 lb∧p∉vY I C ve vf wb.1 wb.2 lb:=by intro lb pv;obtain⟨_,Ti,wb,_,mb,NC,Q2,VR⟩:=_A (R5 pv);exact⟨(wb,mb),Ti,NC,Q2,VR⟩
  let pF:Fin N→_3 N:=λ lb=>if h:lb∈G3 then uN (b0 lb h).choose.1 (b0 lb h).choose.2 lb else ∅;refine⟨G3,pF,TO,λ lb pv=>(b0 lb pv).choose_spec.1,λ lb pv=>by dsimp only[pF];rw[_Q pv];exact ki _ _ _,?_⟩
  intro la nF lb pv VL Xa X9 bl;have nA:=(Z0 la nF).choose_spec;let t:=(Z0 la nF).choose;have O4:dg la=t.2.2.2.1:=by dsimp only[dg];rw[_Q nF]
  have Jm:d6 la=t.2.2.2.2:=by dsimp only[d6];rw[_Q nF]
  have VQ:vE I C ve (dg la) (d6 la) la:=by rw[O4,Jm];exact nA.2.2.2
  have kV:=(b0 lb pv).choose_spec;let wb:=(b0 lb pv).choose;have X9':lb∉uN (dg la) (d6 la) la:=X9;have bl':la∉uN wb.1 wb.2 lb:=by dsimp only[pF] at bl;rw[_Q pv] at bl;exact bl
  have Rv:_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (t.1 t.2.2.1) (dg la):=by rw[O4];exact ReflTransGen.mono (λ _ _ h=>Or.inr h) _ _ nA.2.2.1
  have S4:_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (t.2.1 t.2.2.1) wb.1:=by have h1:_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (t.2.1 t.2.2.1) yy:=ReflTransGen.mono (λ _ _ h=>Or.inr h) _ _ (nA.2.1.trans Pd);have h2:_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) yy Wq:=ReflTransGen.mono (λ _ _ h=>Or.inl h) _ _ RR;have Jq:_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) Wq wb.1:=ReflTransGen.mono (λ _ _ h=>Or.inr h) _ _ (cz.trans kV.2.1);exact ReflTransGen.trans (ReflTransGen.trans h1 h2) Jq
  have Xa':p∉vY I C ve vf (dg la) (d6 la) la:=Xa;by_cases zD:la=lb
  · subst zD;rcases nA.1 with ⟨hg₀,hg₁⟩ | ⟨hg₀,hg₁⟩
    · exact z2 I hI C fa fb hm vM ve vf t.2.2.1 p (dg la) wb.1 (d6 la) wb.2 la VQ kV.2.2.1 VL Xa' kV.2.2.2 (by simpa[t,hg₀] using Rv) (by simpa[t,hg₁] using S4)
    · exact z2 I hI C fb fa hm (λ jb zz h1 h0=>vM jb zz h0 h1) ve vf t.2.2.1 p (dg la) wb.1 (d6 la) wb.2 la VQ kV.2.2.1 VL Xa' kV.2.2.2 (by simpa[t,hg₀] using Rv) (by simpa[t,hg₁] using S4)
  · exact jy t.1 t.2.1 nA.1 t.2.2.1 p (dg la) wb.1 (d6 la) wb.2 la lb VQ kV.2.2.1 VL kV.1 Xa' kV.2.2.2 X9' bl' Rv S4
 let mN:_2 N:=NF.biUnion λ u=>(M9.v6 N C u).toFinset.biUnion λ x₀=>if 7≤(vv I C ve fa fb x₀).card∧(vv I C ve fa fb u).card≤6 then
  (dR x₀×ˢ vv I C ve fa fb u).filter λ e=>I e.1 e.2
  else ∅
 let mR:_2 N:=(univ:Finset (Fin J× Fin 2)).biUnion λ js=>
  let x₀:=if js.2=0 then fb js.1 else fa js.1;let gc:=if js.2=0 then fa js.1 else fb js.1;if 7≤(vv I C ve fa fb x₀).card∧(vt I C ve gc).card≤6 then (dR x₀×ˢ vt I C ve gc).filter λ e=>I e.1 e.2
  else ∅
 have Vy:uE⊆mN∪mR:=by
  intro⟨p,l⟩ he;obtain⟨wK,_,j,g₀,g₁,fF,w₀,w₁,m₀,m₁,_,hsc⟩:=Wc (p,l) he;have Ut:∀(Xy d0:Fin J→ ℕ) (WY XC:ℕ) (Tb U6:Fin 2),((Xy=fa∧d0=fb)∨(Xy=fb∧d0=fa))→ xJ I C fa fb ve vf p l j Xy d0 WY XC Tb U6→(p,l)∈mN∪mR:=by
   intro Xy d0 WY XC Tb U6 W9 ⟨_,_,_,_,_,O9,cI,_,Wq,a,b,x₀,yy,c_top,_,_,cz,_,_,_,_,OR,_,Pd,_,_,Z7,hx7,hx_case⟩;have Wa:p∈dR x₀:=_B ⟨_H _,a,yy,Wq,Pd,Z7,cz,OR⟩;rcases hx_case with hx_eq | ⟨u,U4,Pi,QN⟩
   · refine _G _ ?_
     rcases W9 with ⟨hgc,cu⟩ | ⟨hgc,cu⟩
     · refine _F ⟨(j,0),_H _,?_⟩
       dsimp only;simp only[show ((0:Fin 2)=0)↔True from by decide,ite_true]
       have zy:7≤(vv I C ve fa fb (fb j)).card∧(vt I C ve (fa j)).card≤6:=⟨by simpa[cu,hx_eq] using hx7,by simpa[hgc] using O9⟩
       rw[_O zy];exact _B ⟨_R ⟨by simpa[cu,hx_eq] using Wa,by simpa[hgc] using cI⟩,wK⟩
     · refine _F ⟨(j,1),_H _,?_⟩
       dsimp only;simp only[show ((1:Fin 2)=0)↔False from by decide,ite_false]
       have zy:7≤(vv I C ve fa fb (fa j)).card∧(vt I C ve (fb j)).card≤6:=⟨by simpa[cu,hx_eq] using hx7,by simpa[hgc] using O9⟩
       rw[_O zy];exact _B ⟨_R ⟨by simpa[cu,hx_eq] using Wa,by simpa[hgc] using cI⟩,wK⟩
   · refine _D _ ?_
     obtain⟨Qi,RA⟩:=mS u x₀ U4;have Nr:l∈vv I C ve fa fb u:=by
      refine _B ⟨_H _,j,?_⟩
      rcases W9 with ⟨hgc,cu⟩ | ⟨hgc,cu⟩
      · exact Or.inl ⟨by simpa[cu] using Pi,by simpa[hgc] using O9,by simpa[hgc] using cI⟩
      · exact Or.inr ⟨by simpa[cu] using Pi,by simpa[hgc] using O9,by simpa[hgc] using cI⟩
     refine _F ⟨u,Qi,_F ⟨x₀,_v.mpr RA,?_⟩⟩
     rw[_O ⟨hx7,QN⟩];exact _B ⟨_R ⟨Wa,Nr⟩,wK⟩
  rcases hsc with hsc0 | hsc1
  · exact Ut g₀ g₁ w₀ w₁ m₀ m₁ fF hsc0
  · have bn:(g₁=fa∧g₀=fb)∨(g₁=fb∧g₀=fa):=by
     rcases fF with ⟨hg₀,hg₁⟩ | ⟨hg₀,hg₁⟩
     · exact Or.inr ⟨hg₁,hg₀⟩
     · exact Or.inl ⟨hg₁,hg₀⟩
    exact Ut g₁ g₀ w₁ w₀ m₁ m₀ bn hsc1
 have PT:mN.card≤42*NF.card:=by
  refine (_E NF _ 42 ?_).trans (by omega)
  intro u hu;refine (_E _ _ 21 ?_).trans (by nlinarith [Sa u hu])
  intro x₀ _;split_ifs with h
  · exact xL I hI (dR x₀) (vv I C ve fa fb u) (Yq x₀ h.1) h.2
  · simp
 have hRoot:mR.card≤42*J:=by
  refine (_E _ _ 21 ?_).trans ?_
  · intro js _;dsimp only;by_cases hjs0:js.2=0
    · simp only[hjs0,ite_true];split_ifs with h
      · exact xL I hI (dR (fb js.1)) (vt I C ve (fa js.1)) (Yq _ h.1) h.2
      · simp
    · simp only[hjs0,ite_false];split_ifs with h
      · exact xL I hI (dR (fa js.1)) (vt I C ve (fb js.1)) (Yq _ h.1) h.2
      · simp
  · have MS:(univ:Finset (Fin J× Fin 2)).card=J*2:=by simp
    rw[MS];omega
 have Vh:=_C Vy;have Sn:=_J mN mR;dsimp only[NF] at PT;omega
lemma nZ {J N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (fa jb) false=true→(C.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q)
 (uN:ℕ→ Fin 2→ Fin N→_3 N)
 (ki:∀ w m l,(uN w m l).card≤1)
 (jy:∀(g₀ g₁:Fin J→ ℕ),((g₀=fa∧g₁=fb)∨(g₀=fb∧g₁=fa))→∀(j:Fin J) (p:Fin N) (wa wb:ℕ) (ma mb:Fin 2) (la lb:Fin N),vE I C ve wa ma la→ vE I C ve wb mb lb→¬ I p la→¬ I p lb→ p∉vY I C ve vf wa ma la→ p∉vY I C ve vf wb mb lb→ lb∉uN wa ma la→ la∉uN wb mb lb→_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₀ j) wa→_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₁ j) wb→ False)
 (F4:_2 N)
 (z6:∀ e∈F4,(e.1,e.2)∉v2 I C)
 (E':_2 N)
 (bG:E'⊆F4)
 (mf:∀ e∈E',I e.1 e.2∧∃(j:Fin J) (g₀ g₁:Fin J→ ℕ),((g₀=fa∧g₁=fb)∨(g₀=fb∧g₁=fa))∧∃(w₀ w₁:ℕ) (m₀ m₁:Fin 2),_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (g₀ j) w₀∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (g₁ j) w₁∧vk (vh N C) (vc I C) (vr N C (vd N C w₀ m₀))={e.2}∧vE I C ve w₀ m₀ e.2∧vE I C ve w₁ m₁ e.2):
 E'.card≤18*(Mc.vI N C).card+92*(Mc.vP N C\Mc.vI N C).card+90*J:=by
 obtain⟨uE,_,p5,Wc⟩:=pR I hI C fa fb hm vM ve vf uN ki jy F4 z6 E' bG mf;have hrem_le:=co I hI C fa fb hm vM ve vf uN ki jy
  uE Wc
 omega
end SbHelp01
section SmallBareAndBridge06
open Ma
open M2 Kd
open M1 Kb
open Kc K7
open K1
private noncomputable def um {N:ℕ} (I:_0 N) [_4 I] (C:_a) (ve:ℕ→_3 N) (w:ℕ) (m:Fin 2) (l:Fin N):_3 N:=by
 classical
 let r:=vr N C (vd N C w (1-m));exact if l∈vk (vh N C) (vc I C) r then ∅
 else if 13≤(ve r\univ.filter λ q=>I q l).card then
  let g6:=yw I ve r l;univ.filter λ v:Fin N=>(g6.filter λ q=>¬ I q v).card < 6
 else ∅
private lemma nx {N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (ve:ℕ→_3 N) (C:_a) (w:ℕ) (m:Fin 2) (l:Fin N):(um I C ve w m l).card≤1:=by
 classical
 dsimp only[um];split_ifs with hb fp
 · simp
 · rw[_y];intro v₁ hv₁ v₂ hv₂;by_contra xR;let r:=vr N C (vd N C w (1-m));let g6:=yw I ve r l
   have dl:g6.card=13:=by dsimp only[g6,yw];rw[_Q fp];exact (_N fp).choose_spec.2
   have hv1:(g6.filter λ q=>¬ I q v₁).card < 6:=(_A hv₁).2;have hv2:(g6.filter λ q=>¬ I q v₂).card < 6:=(_A hv₂).2;have h8a:8≤(g6.filter λ q=>I q v₁).card:=by have:=_t (s:=g6) (p:=λ q=>I q v₁);omega
   have h8b:8≤(g6.filter λ q=>I q v₂).card:=by have:=_t (s:=g6) (p:=λ q=>I q v₂);omega
   have p4:2≤((g6.filter λ q=>I q v₁)∩(g6.filter λ q=>I q v₂)).card:=by have hu:(g6.filter λ q=>I q v₁)∪(g6.filter λ q=>I q v₂)⊆g6:=union_subset (filter_subset _ _) (filter_subset _ _);have LT:=_C hu;have hs:=Finset.card_inter_add_card_union (g6.filter λ q=>I q v₁) (g6.filter λ q=>I q v₂);omega
   obtain⟨q₁,hq₁,q₂,hq₂,VJ⟩:=_Z p4;exact hI q₁ q₂ v₁ v₂ VJ xR ⟨(_A (_P hq₁).1).2,(_A (_P hq₁).2).2,(_A (_P hq₂).1).2,(_A (_P hq₂).2).2⟩
 · simp
open Classical in
private lemma k1 {N:ℕ} (I:_0 N) [_4 I] (_hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q) (w:ℕ) (m:Fin 2) (l kz p:Fin N) (hb:l∉vk (vh N C) (vc I C) (vr N C (vd N C w (1-m)))) (fp:13≤(ve (vr N C (vd N C w (1-m)))\univ.filter λ q=>I q l).card) (hp:p∉vY I C ve vf w m l)
 (Mr:kz∉um I C ve w m l):
 let r:=vr N C (vd N C w (1-m));let Q:=(yw I ve r l).filter λ q=>¬ I q kz∧¬(vx (pencil I) 3 (vG I C ve vf r q)∧4≤((y6 I C ve vf r q).filter λ u=>I p u).card);3≤ Q.card∧∀ q∈Q,q∈ve r∧¬ I q l∧¬ I q kz∧8≤(vG I C ve vf r q).card∧¬(vx (pencil I) 3 (vG I C ve vf r q)∧4≤((vG I C ve vf r q).filter (I q)).card)∧(vx (pencil I) 3 (vG I C ve vf r q)→2≤((y6 I C ve vf r q).filter λ u=>¬ I p u).card∧∀ u∈y6 I C ve vf r q,u∈vG I C ve vf r q∧¬ I q u):=by
 classical
 intro r Q;have nW:yw I ve r l⊆ve r\univ.filter λ q=>I q l:=by dsimp only[yw];rw[_Q fp];exact (_N fp).choose_spec.1
 have dl:(yw I ve r l).card=13:=by dsimp only[yw];rw[_Q fp];exact (_N fp).choose_spec.2
 have hv_ge6:6≤((yw I ve r l).filter λ q=>¬ I q kz).card:=by
  by_contra! z5;apply Mr
  dsimp only[um];rw[ite_eq_right hb,_O fp];exact _B ⟨_H _,z5⟩
 have VN:((yw I ve r l).filter λ q=>vx (pencil I) 3 (vG I C ve vf r q)∧4≤((y6 I C ve vf r q).filter λ u=>I p u).card).card≤3:=by
  by_contra! hgt;apply hp
  dsimp only[vY];rw[ite_eq_right hb,_O fp];exact _B ⟨_H _,hgt⟩
 have N3:3≤ Q.card:=by
  have vR:(yw I ve r l).filter (λ q=>¬ I q kz)⊆Q∪(yw I ve r l).filter λ q=>vx (pencil I) 3 (vG I C ve vf r q)∧4≤((y6 I C ve vf r q).filter λ u=>I p u).card:=by
   intro q hq;obtain⟨Xl,TD⟩:=_A hq;by_cases c3:vx (pencil I) 3 (vG I C ve vf r q)∧4≤((y6 I C ve vf r q).filter λ u=>I p u).card
   · exact _G _ (_B ⟨Xl,c3⟩)
   · exact _D _ (_B ⟨Xl,TD,c3⟩)
  have hc:=(_C vR).trans (_J _ _);omega
 refine⟨N3,λ q hq=>?_⟩
 obtain⟨Xl,TD,PK⟩:=_A hq;obtain⟨xn,ny⟩:=_M (nW Xl);have TF:¬ I q l:=λ h=>ny (_B ⟨_H _,h⟩);have WN:=(vf r q xn).choose_spec;have h8:8≤(vG I C ve vf r q).card:=by simpa[vG,_Q xn] using WN.2.2.1
 have x9:¬(vx (pencil I) 3 (vG I C ve vf r q)∧4≤((vG I C ve vf r q).filter (I q)).card):=by simpa[vG,_Q xn] using WN.2.2.2.1
 refine⟨xn,TF,TD,h8,x9,λ zu=>?_⟩
 have SV:y6 I C ve vf r q⊆(vG I C ve vf r q).filter (λ u=>¬ I q u)∧(y6 I C ve vf r q).card=5:=by have h5:5≤((vG I C ve vf r q).filter λ u=>¬ I q u).card:=xw I _ q h8 x9 zu;dsimp only[y6];rw[_Q xn,_Q zu];exact (_N h5).choose_spec
 have hlt4:((y6 I C ve vf r q).filter λ u=>I p u).card≤3:=by by_contra! h4;exact PK ⟨zu,h4⟩
 have hadd:=_t
  (s:=y6 I C ve vf r q) (p:=λ u=>I p u)
 refine⟨by omega,λ u hu=>?_⟩
 have LJ:=_A (SV.1 hu);exact⟨LJ.1,LJ.2⟩
private lemma f6 {J N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (g₀ g₁:Fin J→ ℕ) (hm:_b C) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (g₀ jb) false=true→(C.wires (ofFn zz)).getD (g₁ jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q)
 (j:Fin J) (p:Fin N)
 (wa wb:ℕ) (ma mb:Fin 2) (la lb:Fin N)
 (Sg:vE I C ve wa ma la)
 (U9:vE I C ve wb mb lb)
 (S2:¬ I p la) (Nv:¬ I p lb)
 (mF:p∉vY I C ve vf wa ma la)
 (nK:p∉vY I C ve vf wb mb lb)
 (Wz:lb∉um I C ve wa ma la)
 (WM:la∉um I C ve wb mb lb)
 (mP:_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₀ j) wa)
 (mQ:_1 (λ u v=>M9.vl N C (ofFn (λ q=>decide (q=p))) u v∨vj I C u v) (g₁ j) wb):
 False:=by
 classical
 let ra:=vr N C (vd N C wa (1-ma));let rb:=vr N C (vd N C wb (1-mb));let B:=vG I C ve vf
 let U5:=y6 I C ve vf
 have Xr:∀ w m l kz (ht:vE I C ve w m l) (YM:p∉vY I C ve vf w m l) (OC:kz∉um I C ve w m l),l∈vk (vh N C) (vc I C) (vr N C (vd N C w (1-m)))∨∃ q∈ve (vr N C (vd N C w (1-m))),¬ I q l∧¬ I q kz∧∃ u∈B (vr N C (vd N C w (1-m))) q,¬ I q u∧¬ I p u:=by
  intro w m l kz ht YM OC;rcases ht.2.2.2 with Zc | Ua
  · exact Or.inl Zc
  · by_cases Zc:l∈vk (vh N C) (vc I C) (vr N C (vd N C w (1-m)))
    · exact Or.inl Zc
    · right
      obtain⟨N3,RY⟩:=k1 I hI C ve vf w m l kz p Zc Ua YM OC;obtain⟨q,SX⟩:=card_pos.mp (Nat.lt_of_lt_of_le (by decide) N3);obtain⟨xn,ny,P5,h8,x9,ft⟩:=RY q SX;by_cases zu:vx (pencil I) 3 (B (vr N C (vd N C w (1-m))) q)
      · obtain⟨U3,ur⟩:=ft zu;obtain⟨u,hu⟩:=card_pos.mp (Nat.lt_of_lt_of_le (by decide) U3);obtain⟨Th,R6⟩:=_A hu;exact⟨q,xn,ny,P5,u,(ur u Th).1,(ur u Th).2,R6⟩
      · have wr:∃ u∈B (vr N C (vd N C w (1-m))) q,¬ I q u∧¬ I p u:=by
         by_contra hnone;push Not at hnone;apply zu
         refine⟨{q,p},(_K _ _).trans (by simp),λ u hu=>?_⟩
         by_cases b8:I q u
         · exact _F ⟨q,_S _ _,_B ⟨_H _,b8⟩⟩
         · exact _F ⟨p,_L (_I _),_B ⟨_H _,hnone u hu b8⟩⟩
        obtain⟨u,Zu,b8,f4⟩:=wr;exact⟨q,xn,ny,P5,u,Zu,b8,f4⟩
 have Wb:∃ S:_3 N,S.card≤4∧la∈S∧lb∈S∧(∀ u∈S,¬ I p u)∧(la∈vk (vh N C) (vc I C) ra∨∃ qa∈ve ra,∃ ua∈S,ua∈B ra qa∧∀ s∈S,¬ I qa s)∧(lb∈vk (vh N C) (vc I C) rb∨∃ qb∈ve rb,∃ ub∈S,ub∈B rb qb∧∀ s∈S,¬ I qb s):=by
  by_cases Zc:la∈vk (vh N C) (vc I C) ra
  · rcases Xr wb mb lb la U9 nK WM with hbb | ⟨qb,xn,ny,Nq,ub,Zu,b8,f4⟩
    · refine⟨{la,lb},(_K _ _).trans (by simp),_S _ _,_L (_I _),λ u hu=>?_,Or.inl Zc,Or.inl hbb⟩
      rcases mem_insert.mp hu with rfl | hu'
      · exact S2
      · rw[_U hu'];exact Nv
    · refine⟨{la,lb,ub},(_K _ _).trans (_n ((_K _ _).trans (by simp))),_S _ _,_L (_S _ _),λ u hu=>?_,Or.inl Zc,Or.inr ⟨qb,xn,ub,_L (_L (_I _)),Zu,λ s hs=>?_⟩⟩
      · simp only[mem_insert,mem_singleton] at hu;rcases hu with rfl | rfl | rfl <;> assumption
      · simp only[mem_insert,mem_singleton] at hs;rcases hs with rfl | rfl | rfl <;> assumption
  · by_cases hbb:lb∈vk (vh N C) (vc I C) rb
    · obtain⟨qa,xn,ny,Nq,ua,Zu,b8,f4⟩:=(Xr wa ma la lb Sg mF Wz).resolve_left Zc;refine⟨{la,lb,ua},(_K _ _).trans (_n ((_K _ _).trans (by simp))),_S _ _,_L (_S _ _),λ u hu=>?_,Or.inr ⟨qa,xn,ua,_L (_L (_I _)),Zu,λ s hs=>?_⟩,Or.inl hbb⟩
      · simp only[mem_insert,mem_singleton] at hu;rcases hu with rfl | rfl | rfl <;> assumption
      · simp only[mem_insert,mem_singleton] at hs;rcases hs with rfl | rfl | rfl <;> assumption
    · have Ua:=Sg.2.2.2.resolve_left Zc;have S5:=U9.2.2.2.resolve_left hbb;obtain⟨Mm,Sw⟩:=k1 I hI C ve vf wa ma la lb p Zc Ua mF Wz;obtain⟨MF,Sz⟩:=k1 I hI C ve vf wb mb lb la p hbb S5 nK WM;let Qa:=(yw I ve ra la).filter λ q=>¬ I q lb∧¬(vx (pencil I) 3 (B ra q)∧4≤((U5 ra q).filter λ u=>I p u).card);let Qb:=(yw I ve rb lb).filter λ q=>¬ I q la∧¬(vx (pencil I) 3 (B rb q)∧4≤((U5 rb q).filter λ u=>I p u).card);let bad₁:=(Qa×ˢ Qb).filter λ qp=>¬ ∃ ua∈B ra qp.1,¬ I qp.1 ua∧¬ I qp.2 ua∧¬ I p ua;let bad₂:=(Qa×ˢ Qb).filter λ qp=>¬ ∃ ub∈B rb qp.2,¬ I qp.1 ub∧¬ I qp.2 ub∧¬ I p ub
      have hbad₁:bad₁.card≤ Qa.card:=by
       have vR:bad₁⊆Qa.biUnion λ q₁=>if h:∃ q₂∈Qb,¬ ∃ ua∈B ra q₁,¬ I q₁ ua∧¬ I q₂ ua∧¬ I p ua then {(q₁,h.choose)} else ∅:=by
        intro⟨q₁,q₂⟩ yH;obtain⟨zA,dw⟩:=_A yH;obtain⟨hq₁,hq₂⟩:=_Y zA;have wr:∃ q'∈Qb,¬ ∃ ua∈B ra q₁,¬ I q₁ ua∧¬ I q' ua∧¬ I p ua:=⟨q₂,hq₂,dw⟩;obtain⟨_,_,_,h8,x9,ft⟩:=Sw q₁ hq₁;have zu:vx (pencil I) 3 (B ra q₁):=by
         by_contra Xu;apply dw
         by_contra hnone;push Not at hnone;apply Xu
         refine⟨{q₁,q₂,p},(_K _ _).trans (_n ((_K _ _).trans (by simp))),λ u hu=>?_⟩
         by_cases h1:I q₁ u
         · exact _F ⟨q₁,_S _ _,_B ⟨_H _,h1⟩⟩
         · by_cases h2:I q₂ u
           · exact _F ⟨q₂,_L (_S _ _),_B ⟨_H _,h2⟩⟩
           · exact _F ⟨p,_L (_L (_I _)),_B ⟨_H _,hnone u hu h1 h2⟩⟩
        obtain⟨U3,ur⟩:=ft zu;obtain⟨ua,gy,ub,hub,X5⟩:=_Z U3;have gy':=_A gy;have hub':=_A hub;have nk:q₂=wr.choose:=by
         by_contra NG;have YH:I q₂ ua:=by by_contra hn;exact dw ⟨ua,(ur ua gy'.1).1,(ur ua gy'.1).2,hn,gy'.2⟩
         have Za:I q₂ ub:=by by_contra hn;exact dw ⟨ub,(ur ub hub'.1).1,(ur ub hub'.1).2,hn,hub'.2⟩
         have W4:I wr.choose ua:=by by_contra hn;exact wr.choose_spec.2 ⟨ua,(ur ua gy'.1).1,(ur ua gy'.1).2,hn,gy'.2⟩
         have UT:I wr.choose ub:=by by_contra hn;exact wr.choose_spec.2 ⟨ub,(ur ub hub'.1).1,(ur ub hub'.1).2,hn,hub'.2⟩
         exact hI q₂ wr.choose ua ub NG X5 ⟨YH,Za,W4,UT⟩
        refine _F ⟨q₁,hq₁,?_⟩
        rw[_Q wr,mem_singleton,nk]
       refine (_C vR).trans ?_
       refine (_E Qa _ 1 ?_).trans (by omega)
       intro q₁ _;split_ifs <;> simp
      have hbad₂:bad₂.card≤ Qb.card:=by
       have vR:bad₂⊆Qb.biUnion λ q₂=>if h:∃ q₁∈Qa,¬ ∃ ub∈B rb q₂,¬ I q₁ ub∧¬ I q₂ ub∧¬ I p ub then {(h.choose,q₂)} else ∅:=by
        intro⟨q₁,q₂⟩ yH;obtain⟨zA,dw⟩:=_A yH;obtain⟨hq₁,hq₂⟩:=_Y zA;have wr:∃ q'∈Qa,¬ ∃ ub∈B rb q₂,¬ I q' ub∧¬ I q₂ ub∧¬ I p ub:=⟨q₁,hq₁,dw⟩;obtain⟨_,_,_,h8,x9,ft⟩:=Sz q₂ hq₂;have zu:vx (pencil I) 3 (B rb q₂):=by
         by_contra Xu;apply dw
         by_contra hnone;push Not at hnone;apply Xu
         refine⟨{q₁,q₂,p},(_K _ _).trans (_n ((_K _ _).trans (by simp))),λ u hu=>?_⟩
         by_cases h1:I q₁ u
         · exact _F ⟨q₁,_S _ _,_B ⟨_H _,h1⟩⟩
         · by_cases h2:I q₂ u
           · exact _F ⟨q₂,_L (_S _ _),_B ⟨_H _,h2⟩⟩
           · exact _F ⟨p,_L (_L (_I _)),_B ⟨_H _,hnone u hu h1 h2⟩⟩
        obtain⟨U3,ur⟩:=ft zu;obtain⟨ua,gy,ub,hub,X5⟩:=_Z U3;have gy':=_A gy;have hub':=_A hub;have nk:q₁=wr.choose:=by
         by_contra Nc;have YH:I q₁ ua:=by by_contra hn;exact dw ⟨ua,(ur ua gy'.1).1,hn,(ur ua gy'.1).2,gy'.2⟩
         have Za:I q₁ ub:=by by_contra hn;exact dw ⟨ub,(ur ub hub'.1).1,hn,(ur ub hub'.1).2,hub'.2⟩
         have W4:I wr.choose ua:=by by_contra hn;exact wr.choose_spec.2 ⟨ua,(ur ua gy'.1).1,hn,(ur ua gy'.1).2,gy'.2⟩
         have UT:I wr.choose ub:=by by_contra hn;exact wr.choose_spec.2 ⟨ub,(ur ub hub'.1).1,hn,(ur ub hub'.1).2,hub'.2⟩
         exact hI q₁ wr.choose ua ub Nc X5 ⟨YH,Za,W4,UT⟩
        refine _F ⟨q₂,hq₂,?_⟩
        rw[_Q wr,mem_singleton,nk]
       refine (_C vR).trans ?_
       refine (_E Qb _ 1 ?_).trans (by omega)
       intro q₂ _;split_ifs <;> simp
      have z5:(bad₁∪bad₂).card < (Qa×ˢ Qb).card:=by have hu:=_J bad₁ bad₂;rw[_m];change 3≤ Qa.card at Mm;change 3≤ Qb.card at MF;nlinarith
      have xR:((Qa×ˢ Qb)\(bad₁∪bad₂)).Nonempty:=by rw[← card_pos];have hs:=_z (Qa×ˢ Qb) (bad₁∪bad₂);have hi:=_C (inter_subset_right:(Qa×ˢ Qb)∩(bad₁∪bad₂)⊆bad₁∪bad₂);omega
      obtain⟨⟨qa,qb⟩,hq⟩:=xR;obtain⟨zA,x9⟩:=_M hq;obtain⟨Vu,O6⟩:=_Y zA;have S8:¬(qa,qb)∈bad₁:=λ h=>x9 (_D _ h);have R7:¬(qa,qb)∈bad₂:=λ h=>x9 (_G _ h);simp only[bad₁,mem_filter,zA,true_and,not_not] at S8;simp only[bad₂,mem_filter,zA,true_and,not_not] at R7;obtain⟨ua,Qn,Pv,PM,hnpa1⟩:=S8;obtain⟨ub,SI,Oo,Py,hnpb2⟩:=R7;obtain⟨XP,hqal1,hqalb,_,_,_⟩:=Sw qa Vu;obtain⟨XX,hqbl2,hqbla,_,_,_⟩:=Sz qb O6
      refine⟨{la,lb,ua,ub},(_K _ _).trans (_n ((_K _ _).trans (_n ((_K _ _).trans (by simp))))),_S _ _,_L (_S _ _),λ u hu=>?_,Or.inr ⟨qa,XP,ua,_L (_L (_S _ _)),Qn,λ s hs=>?_⟩,Or.inr ⟨qb,XX,ub,_L (_L (_L (_I _))),SI,λ s hs=>?_⟩⟩
      · simp only[mem_insert,mem_singleton] at hu;rcases hu with rfl | rfl | rfl | rfl <;> assumption
      · simp only[mem_insert,mem_singleton] at hs;rcases hs with rfl | rfl | rfl | rfl <;> assumption
      · simp only[mem_insert,mem_singleton] at hs;rcases hs with rfl | rfl | rfl | rfl <;> assumption
 obtain⟨S,wh,Nx,f7,Rb,RB,SK⟩:=Wb;let x:Fin N→ Bool:=λ q=>decide (q=p) || vB I S q;let y:Fin N→ Bool:=λ w=>decide (w∈S);have Xe:∀ q,vB I S q=true→ x q=true:=λ q hq=>by simp[x,hq]
 have QQ:∀ q,decide (q=p)=true→ x q=true:=λ q hq=>by simp[x,hq]
 have TM:∀ u∈S,y u=true:=λ u hu=>decide_eq_true hu;obtain⟨ua,va,m6,gy,WT⟩:=z3 I C hm ve vf wa ma la Sg S wh Nx x y Xe TM RB;obtain⟨xb,yb,m9,ZR,Z3⟩:=z3 I C hm ve vf wb mb lb U9 S wh f7 x y Xe TM SK;have be:∀ u v,_1 (λ a b=>M9.vl N C (ofFn (λ q=>decide (q=p))) a b∨vj I C a b) u v→_1 (M9.vl N C (ofFn x)) u v:=by
  intro u v hp;induction hp with
  | refl=>exact .refl
  | tail _ zl ih=>
   rcases zl with ha | hc
   · exact .tail ih (je C hm _ x QQ _ _ ha)
   · exact .tail ih (uK I C hm S wh x Xe _ _ hc)
 obtain⟨pa,lb',jz,dS,Y2⟩:=zc I C g₀ g₁ hm vM j wa ua va wb xb yb m6 m9 x y (be _ _ mP) (be _ _ mQ) gy WT ZR Z3;have YQ:lb'∈S:=_o Y2;simp only[x,_r,decide_eq_true_eq] at dS;rcases dS with rfl | hm_pa
 · exact Rb lb' YQ jz
 · exact (by simpa only[vB,decide_eq_true_eq] using hm_pa:∀ u∈S,¬ I pa u) lb' YQ jz
private lemma nt {J N:ℕ} (I:_0 N) [_4 I] (hI:∀ p q l u,p≠q→ l≠u→¬(I p l∧I p u∧I q l∧I q u)) (C:_a) (fa fb:Fin J→ ℕ) (hm:_b C) (qZ:∀ jd,(C.lineDegrees (N+N) (Ico N (N+N))).getD (fa jd) 0≤2) (gP:∀ jd,(C.lineDegrees (N+N) (Ico N (N+N))).getD (fb jd) 0≤2) (vM:∀(jb:Fin J) (zz:Fin (N+N)→ Bool),(C.wires (ofFn zz)).getD (fa jb) false=true→(C.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true) (ve:ℕ→_3 N) (vf:∀ r q,q∈ve r→∃ g∈vw (vh N C) N (vc I C),q∈vH (vh N C) (vi I C) g∧8≤(vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).card∧¬(vx (pencil I) 3 (vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g))∧
 4≤((vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)).filter (I q)).card)∧vk (N:=N) (vh N C) (vc I C) (vu (vh N C) N g)⊆v9 (vh N C) (vi I C) r q)
 (E₃:_2 N)
 (z6:∀ e∈E₃,(e.1,e.2)∉v2 I C)
 (yM:∀ p l r,(p,l)∈E₃→ I p l→ l∈v9 (vh N C) (vi I C) r p→ l∉vk (N:=N) (vh N C) (vc I C) r→ p∈ve r)
 (qc:∀ p l r,(p,l)∈E₃→ r∈Ico N (N+(vh N C).length)→2≤(vk (N:=N) (vh N C) (vc I C) r).card→ l∈vk (N:=N) (vh N C) (vc I C) r→¬ ∀ u∈vk (N:=N) (vh N C) (vc I C) r,I p u)
 (hE₃:∀ e∈E₃,gS (N:=N) I C fa fb e.1 e.2)
 (k4:_2 N)
 (c9:k4⊆E₃)
 (ZB:∀ e∈k4,¬(I e.1 e.2∧∃(j:Fin J) (wa wb:ℕ),wa∈Mc.vI N C∧wb∈Mc.vI N C∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fa j) wa∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fb j) wb∧(∃ i:Fin 2,vk (vh N C) (vc I C) (vr N C (vd N C wa i))={e.2}∧(e.2∈vk (vh N C) (vc I C) (vr N C (vd N C wa (1-i)))∨13≤(ve (vr N C (vd N C wa (1-i)))\univ.filter λ q=>I q e.2).card))∧(∃ Ux:_3 N,(2≤ Ux.card∨∃ u₀:Fin N,Ux={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Ux,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C wb)) e.1)∧(∃ Uy:_3 N,(2≤ Uy.card∨∃ u₀:Fin N,Uy={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Uy,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C wb)) e.1)∧
  (vF I C ve fa fb wb={e.2}→(e.2∈vk (vh N C) (vc I C) (vr N C (vD N C wb))∨13≤(ve (vr N C (vD N C wb))\univ.filter λ q=>I q e.2).card)∧(e.2∈vk (vh N C) (vc I C) (vr N C (vz N C wb))∨13≤(ve (vr N C (vz N C wb))\univ.filter λ q=>I q e.2).card))))
 (Zw:∀ e∈k4,¬(I e.1 e.2∧∃(j:Fin J) (wb wa:ℕ),wb∈Mc.vI N C∧wa∈Mc.vI N C∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fb j) wb∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (fa j) wa∧(∃ i:Fin 2,vk (vh N C) (vc I C) (vr N C (vd N C wb i))={e.2}∧(e.2∈vk (vh N C) (vc I C) (vr N C (vd N C wb (1-i)))∨13≤(ve (vr N C (vd N C wb (1-i)))\univ.filter λ q=>I q e.2).card))∧(∃ Ux:_3 N,(2≤ Ux.card∨∃ u₀:Fin N,Ux={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Ux,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C wa)) e.1)∧(∃ Uy:_3 N,(2≤ Uy.card∨∃ u₀:Fin N,Uy={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Uy,¬ I e.1 u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C wa)) e.1)∧
  (vF I C ve fb fa wa={e.2}→(e.2∈vk (vh N C) (vc I C) (vr N C (vD N C wa))∨13≤(ve (vr N C (vD N C wa))\univ.filter λ q=>I q e.2).card)∧(e.2∈vk (vh N C) (vc I C) (vr N C (vz N C wa))∨13≤(ve (vr N C (vz N C wa))\univ.filter λ q=>I q e.2).card))))
 (wu:∀ e∈k4,I e.1 e.2→∀ w∈Mc.vI N C,∀ i:Fin 2,e.2∈vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C w i))→(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C w i))).card≤3→ e.2∈v9 (vh N C) (vi I C) (vr N C (vd N C w (1-i))) e.1→ e.2∈vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C w (1-i)))∨13≤(ve (vr N C (vd N C w (1-i)))\univ.filter λ q=>I q e.2).card)
 (pM:∀ e∈k4,I e.1 e.2→∀(t:Fin 3),t=1∨t=2→∀(ga gb:Fin J→ ℕ),(t=1→ ga=fa∧gb=fb)→(t=2→ ga=fb∧gb=fa)→∀ wb∈Mc.vI N C,e.2∈v9 (vh N C) (vi I C) (vr N C (vD N C wb)) e.1→ e.2∈v9 (vh N C) (vi I C) (vr N C (vz N C wb)) e.1→ vF I C ve ga gb wb={e.2}→(e.2∈vk (vh N C) (vc I C) (vr N C (vD N C wb))∨13≤(ve (vr N C (vD N C wb))\univ.filter λ q=>I q e.2).card)∧(e.2∈vk (vh N C) (vc I C) (vr N C (vz N C wb))∨13≤(ve (vr N C (vz N C wb))\univ.filter λ q=>I q e.2).card)):
 k4.card≤6*M1.vA N 1 C.gates+42*(Mc.vI N C).card+106*(Mc.vP N C\Mc.vI N C).card+90*J:=by
 classical
 let F:=Mc.vI N C;let NF:=Mc.vP N C\Mc.vI N C;let pi:=zx I C (vc I C);have pO:∀{n m K:ℕ} (zo:ℕ) (T:Fin m→ Finset (Fin n)) (_hT:∀ i j,i≠j→(T i∩T j).card≤1) (S:ℕ→ Finset (Fin n)) (G:Finset ℕ) (vU:ℕ→ Finset ℕ) (_hkids:∀ g∈G,(vU g).card≤2) (_hlt:∀ g∈G,∀ c∈vU g,c < g) (_hunion:∀ g∈G,S g=(vU g).biUnion S) (_hlarge:∀ g,2*zo+2≤(S g).card→ g∈G) (root:Fin K→ ℕ) (line:Fin K→ Fin m) (_hnear:∀ j,(S (root j)\T (line j)).card≤ zo) (E:Finset (Fin n× Fin m)) (_hcover:∀ e∈E,∃ j,e.2=line j∧e.1∈S (root j)),E.card≤2*(2*zo+1)*G.card+(2*zo+1)*K:=by
  intro n m K zo T hT S G vU fs z5 xA yP root line xH E zu;have Si:=up zo T hT S G vU fs z5 xA yP root line xH E zu;have hf:=card_filter_le G (λ g=>2≤(vU g).card);nlinarith
 have XM:pi.card≤6*M1.vA N 1 C.gates+24*F.card+6*NF.card:=by
  have h1:=jM I hI C (vc I C) hm pO;have SA:M1.vA N 2 C.gates=(Mc.vP N C).card:=by rw[M1.zF N C];rfl
  have cA:(Mc.vP N C).card=F.card+NF.card:=by have h:=_z (Mc.vP N C) F;have hi:Mc.vP N C∩F=F:=inter_eq_right.mpr (Mc.yO N C);rw[hi] at h;dsimp only[F,NF] at h ⊢;omega
  dsimp only[pi,F,NF] at h1 cA ⊢;rw[SA] at h1;omega
 let E':=k4\pi;have mf:∀ e∈E',I e.1 e.2∧∃(j:Fin J) (g₀ g₁:Fin J→ ℕ),((g₀=fa∧g₁=fb)∨(g₀=fb∧g₁=fa))∧∃(w₀ w₁:ℕ) (m₀ m₁:Fin 2),_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (g₀ j) w₀∧_1 (M9.vl N C (ofFn (λ q=>decide (q=e.1)))) (g₁ j) w₁∧vk (vh N C) (vc I C) (vr N C (vd N C w₀ m₀))={e.2}∧vE I C ve w₀ m₀ e.2∧vE I C ve w₁ m₁ e.2:=by
  intro⟨p,l⟩ he;have nG:=(_M he).1;have VX:=(_M he).2;have Le:=hE₃ (p,l) (c9 nG);obtain⟨wK,j,YH,Za,YL,Vs,Ve,WX⟩:=Le;obtain⟨⟨wa,ua,va,z1,m6,m7,ZZ,YF⟩,⟨wb,xb,yb,jn,m9,kJ,Z5,ZU⟩⟩:=n9 I C fa fb hm qZ gP p l j YH Za YL Vs Ve WX;have ZZ':=x3 I C (vr N C ua) p l ZZ;have YF':=x3 I C (vr N C va) p l YF;have Z5':=x3 I C (vr N C xb) p l Z5;have ZU':=x3 I C (vr N C yb) p l ZU;have WR:=uH I C fa fb hm vM ve vf
   p l wK (λ r=>yM p l r (c9 nG) wK)
   (λ r=>qc p l r (c9 nG)) j wa ua va wb xb yb z1 jn m6 m9
   ZZ' YF' Z5' ZU'
  let UX (g₀ g₁:Fin J→ ℕ):Prop:=¬(I p l∧∃(j':Fin J) (w' w'':ℕ),w'∈F∧w''∈F∧_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (g₀ j') w'∧_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (g₁ j') w''∧(∃ i:Fin 2,vk (vh N C) (vc I C) (vr N C (vd N C w' i))={l}∧(l∈vk (vh N C) (vc I C) (vr N C (vd N C w' (1-i)))∨13≤(ve (vr N C (vd N C w' (1-i)))\univ.filter λ q=>I q l).card))∧(∃ Ux:_3 N,(2≤ Ux.card∨∃ u₀:Fin N,Ux={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Ux,¬ I p u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C w'')) p)∧(∃ Uy:_3 N,(2≤ Uy.card∨∃ u₀:Fin N,Uy={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Uy,¬ I p u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C w'')) p)∧(vF I C ve g₀ g₁ w''={l}→
   (l∈vk (vh N C) (vc I C) (vr N C (vD N C w''))∨13≤(ve (vr N C (vD N C w''))\univ.filter λ q=>I q l).card)∧(l∈vk (vh N C) (vc I C) (vr N C (vz N C w''))∨13≤(ve (vr N C (vz N C w''))\univ.filter λ q=>I q l).card)))
  have mX:∀(g₀ g₁:Fin J→ ℕ) (t:Fin 3) (ht:t=1∨t=2) (h1:t=1→ g₀=fa∧g₁=fb) (h2:t=2→ g₀=fb∧g₁=fa) (w₀ c₀₀ c₀₁ w₁ c₁₀ c₁₁:ℕ) (hw₀:w₀∈F) (hw₁:w₁∈F) (hfw₀:M9.y3 N C w₀ c₀₀ c₀₁) (hfw₁:M9.y3 N C w₁ c₁₀ c₁₁) (hp₀:_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (g₀ j) w₀) (hp₁:_1 (M9.vl N C (ofFn (λ q=>decide (q=p)))) (g₁ j) w₁) (hr₀₀:l∈v9 (vh N C) (vi I C) (vr N C c₀₀) p) (hr₀₁:l∈v9 (vh N C) (vi I C) (vr N C c₀₁) p) (hr₁₀:l∈v9 (vh N C) (vi I C) (vr N C c₁₀) p) (hr₁₁:l∈v9 (vh N C) (vi I C) (vr N C c₁₁) p) (Zt:UX g₀ g₁) (m₀:Fin 2) (mU:vk (vh N C) (vc I C) (vr N C (vd N C w₀ m₀))={l}),∃ m₁:Fin 2,vE I C ve w₀ m₀ l∧vE I C ve w₁ m₁ l:=by
   intro g₀ g₁ t ht h1 h2 w₀ c₀₀ c₀₁ w₁ c₁₀ c₁₁ hw₀ hw₁ hfw₀ hfw₁ hp₀ hp₁ hr₀₀ hr₀₁ hr₁₀ hr₁₁ Zt m₀ mU;have T7:=zh N C w₀ c₀₀ c₀₁ hfw₀;have Vh:=zh N C w₁ c₁₀ c₁₁ hfw₁;have W2:l∈v9 (vh N C) (vi I C) (vr N C (vd N C w₀ (1-m₀))) p:=by
    have UH:m₀=0∨m₀=1:=by fin_cases m₀ <;> simp
    rcases UH with rfl | rfl
    · simpa[T7.2] using hr₀₁
    · simpa[T7.1] using hr₀₀
   have WQ:=wu (p,l) nG wK w₀ hw₀ m₀
    (by rw[mU];exact _I _) (by rw[mU];simp) W2
   have UE:vE I C ve w₀ m₀ l:=⟨hw₀,by rw[mU];exact _I _,by rw[mU];simp,WQ⟩
   have Me':l∈v9 (vh N C) (vi I C) (vr N C (vD N C w₁)) p:=by rwa[pL N C w₁ c₁₀ c₁₁ hfw₁]
   have MN':l∈v9 (vh N C) (vi I C) (vr N C (vz N C w₁)) p:=by rwa[qP N C w₁ c₁₀ c₁₁ hfw₁]
   have SP:¬((∃ Ux:_3 N,(2≤ Ux.card∨∃ u₀:Fin N,Ux={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Ux,¬ I p u∧u∈v9 (vh N C) (vi I C) (vr N C (vD N C w₁)) p)∧(∃ Uy:_3 N,(2≤ Uy.card∨∃ u₀:Fin N,Uy={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈Uy,¬ I p u∧u∈v9 (vh N C) (vi I C) (vr N C (vz N C w₁)) p)):=by rintro⟨U4,MQ⟩;exact Zt ⟨wK,j,w₀,w₁,hw₀,hw₁,hp₀,hp₁,⟨m₀,mU,WQ⟩,U4,MQ,pM (p,l) nG wK t ht g₀ g₁ h1 h2 w₁ hw₁ Me' MN'⟩
   have Zb:∀ m:Fin 2,(¬ ∃ U:_3 N,(2≤ U.card∨∃ u₀:Fin N,U={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈U,¬ I p u∧u∈v9 (vh N C) (vi I C) (vr N C (vd N C w₁ m)) p)→ l∈vk (vh N C) (vc I C) (vr N C (vd N C w₁ m)):=by
    intro m O2;have RO:l∈v9 (vh N C) (vi I C) (vr N C (vd N C w₁ m)) p:=by
     have UH:m=0∨m=1:=by fin_cases m <;> simp
     rcases UH with rfl | rfl
     · simpa[Vh.1] using hr₁₀
     · simpa[Vh.2] using hr₁₁
    exact (mK I C ve vf p l (λ r=>yM p l r (c9 nG) wK) (vd N C w₁ m) RO).resolve_right O2
   have WV:∀ m:Fin 2,l∈vk (vh N C) (vc I C) (vr N C (vd N C w₁ m))→4≤(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C w₁ m))).card→∃ U:_3 N,(2≤ U.card∨∃ u₀:Fin N,U={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈U,¬ I p u∧u∈v9 (vh N C) (vi I C) (vr N C (vd N C w₁ m)) p:=by
    intro m OM h4;let r:=vr N C (vd N C w₁ m);have SG:2≤(vk (vh N C) (vc I C) r\pencil I p).card:=by
     by_contra! h1;apply VX
     refine _B ⟨_H _,wK,w₁,hw₁,m,?_⟩
     have P4:vr N C (if m=0 then vD N C w₁ else vz N C w₁)=r:=by fin_cases m <;> rfl
     rw[P4];exact⟨OM,h4,by dsimp only;omega⟩
    refine⟨vk (vh N C) (vc I C) r\pencil I p,Or.inl SG,λ u hu=>?_⟩
    obtain⟨hub,Tz⟩:=_M hu;refine⟨λ Ld=>Tz (_B ⟨_H _,Ld⟩),zm (vh N C) (vc I C) (vi I C) (xN I C hm) r p hub⟩
   have Ri:∃ m₁:Fin 2,l∈vk (vh N C) (vc I C) (vr N C (vd N C w₁ m₁))∧(vk (N:=N) (vh N C) (vc I C) (vr N C (vd N C w₁ m₁))).card≤3:=by
    by_contra hnone;push Not at hnone;have Sj:∀ m:Fin 2,∃ U:_3 N,(2≤ U.card∨∃ u₀:Fin N,U={u₀}∧∀ q:Fin N,¬ I q u₀)∧∀ u∈U,¬ I p u∧u∈v9 (vh N C) (vi I C) (vr N C (vd N C w₁ m)) p:=by intro m;by_contra O2;have OM:=Zb m O2;exact O2 (WV m OM (hnone m OM))
    exact SP ⟨by simpa[vd] using Sj 0,by simpa[vd] using Sj 1⟩
   obtain⟨m₁,hbm1,Q7⟩:=Ri;have Vc:l∈v9 (vh N C) (vi I C) (vr N C (vd N C w₁ (1-m₁))) p:=by
    have UH:m₁=0∨m₁=1:=by fin_cases m₁ <;> simp
    rcases UH with rfl | rfl
    · simpa[Vh.2] using hr₁₁
    · simpa[Vh.1] using hr₁₀
   exact⟨m₁,UE,hw₁,hbm1,Q7,wu (p,l) nG wK w₁ hw₁ m₁ hbm1 Q7 Vc⟩
  have Tp:=zh N C wa ua va m6;have T6:=zh N C wb xb yb m9;rcases WR with hua_s | hva_s | hxb_s | hyb_s
  · obtain⟨m₁,UE,TX⟩:=mX fa fb 1 (Or.inl rfl) (λ _=>⟨rfl,rfl⟩) (λ h=>by cases h) wa ua va wb xb yb m7 kJ m6 m9 z1 jn ZZ' YF' Z5' ZU' (ZB (p,l) nG) 0 (by simpa[Tp.1] using hua_s)
    exact⟨wK,j,fa,fb,Or.inl ⟨rfl,rfl⟩,wa,wb,0,m₁,z1,jn,by simpa[Tp.1] using hua_s,UE,TX⟩
  · obtain⟨m₁,UE,TX⟩:=mX fa fb 1 (Or.inl rfl) (λ _=>⟨rfl,rfl⟩) (λ h=>by cases h) wa ua va wb xb yb m7 kJ m6 m9 z1 jn ZZ' YF' Z5' ZU' (ZB (p,l) nG) 1 (by simpa[Tp.2] using hva_s)
    exact⟨wK,j,fa,fb,Or.inl ⟨rfl,rfl⟩,wa,wb,1,m₁,z1,jn,by simpa[Tp.2] using hva_s,UE,TX⟩
  · obtain⟨m₁,UE,TX⟩:=mX fb fa 2 (Or.inr rfl) (λ h=>by cases h) (λ _=>⟨rfl,rfl⟩) wb xb yb wa ua va kJ m7 m9 m6 jn z1 Z5' ZU' ZZ' YF' (Zw (p,l) nG) 0 (by simpa[T6.1] using hxb_s)
    exact⟨wK,j,fb,fa,Or.inr ⟨rfl,rfl⟩,wb,wa,0,m₁,jn,z1,by simpa[T6.1] using hxb_s,UE,TX⟩
  · obtain⟨m₁,UE,TX⟩:=mX fb fa 2 (Or.inr rfl) (λ h=>by cases h) (λ _=>⟨rfl,rfl⟩) wb xb yb wa ua va kJ m7 m9 m6 jn z1 Z5' ZU' ZZ' YF' (Zw (p,l) nG) 1 (by simpa[T6.2] using hyb_s)
    exact⟨wK,j,fb,fa,Or.inr ⟨rfl,rfl⟩,wb,wa,1,m₁,jn,z1,by simpa[T6.2] using hyb_s,UE,TX⟩
 have hE'_le:=nZ I hI C fa fb hm vM ve vf
  (um I C ve) (λ w m l=>nx I hI ve C w m l)
  (λ g₀ g₁ W9=>f6 I hI C g₀ g₁ hm (by rcases W9 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩;exact vM;exact λ jb zz h1 h0=>vM jb zz h0 h1) ve vf)
  E₃ z6 E' (Finset.sdiff_subset.trans c9) mf
 have TK:k4⊆pi∪E':=λ e he=>by
  by_cases hb:e∈pi
  · exact _D _ hb
  · exact _G _ (_V ⟨he,hb⟩)
 have hcard_sb:=(_C TK).trans (_J pi E');dsimp only[F,NF] at XM;omega
theorem gA:∀(N Jn:ℕ) (I:_0 N) [_4 I] (Ckt:_a) (fa fb:Fin Jn→ ℕ) (fr:ℕ),(∀ p p' l l':Fin N,p≠p'→ l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l'))→_b Ckt→(∀ jd:Fin Jn,(Ckt.lineDegrees (N+N) (Ico N (N+N))).getD (fa jd) 0≤2∧(Ckt.lineDegrees (N+N) (Ico N (N+N))).getD (fb jd) 0≤2)→(∀(jb:Fin Jn) (zz:Fin (N+N)→ Bool),(Ckt.wires (ofFn zz)).getD (fa jb) false=true→(Ckt.wires (ofFn zz)).getD (fb jb) false=true→∃(pa lb:Fin N),I pa lb∧zz (_7 N pa)=true∧zz (_8 N lb)=true)→(univ.filter (λ e2:Fin N× Fin N=>I e2.1 e2.2∧(Ckt.wires (ofFn (λ vq:Fin (N+N)=>if vq=_7 N e2.1 then true else if vq=_8 N e2.2 then true else false))).getD fr false=false∧(∃ jc:Fin Jn,(Ckt.wires (ofFn (λ vq:Fin (N+N)=>
 if vq=_7 N e2.1 then true
 else if vq=_8 N e2.2 then true else false))).getD (fa jc) false=true∧(Ckt.wires (ofFn (λ vq:Fin (N+N)=>if vq=_7 N e2.1 then true
 else if vq=_8 N e2.2 then true else false))).getD (fb jc) false=true)∧∀ jk:Fin Jn,(Ckt.wires (ofFn (λ vq:Fin (N+N)=>if vq=_7 N e2.1 then true
 else if vq=_8 N e2.2 then true else false))).getD (fa jk) false=true→(Ckt.wires (ofFn (λ vq:Fin (N+N)=>if vq=_7 N e2.1 then true
 else if vq=_8 N e2.2 then true else false))).getD (fb jk) false=true→(Ckt.wires (ofFn (λ vp:Fin (N+N)=>decide (vp=_7 N e2.1)))).getD (fa jk) false=false∧(Ckt.wires (ofFn (λ vp:Fin (N+N)=>decide (vp=_7 N e2.1)))).getD (fb jk) false=false)).card≤400*(Ckt.size+Jn)+16*N:=by
 intro N Jn I _ Ckt fa fb fr hI hm hdeg vM;classical
 let E:=univ.filter (λ e2:Fin N× Fin N=>I e2.1 e2.2∧(Ckt.wires (ofFn (λ vq:Fin (N+N)=>if vq=_7 N e2.1 then true
  else if vq=_8 N e2.2 then true else false))).getD fr false=false∧(∃ jc:Fin Jn,(Ckt.wires (ofFn (λ vq:Fin (N+N)=>if vq=_7 N e2.1 then true else if vq=_8 N e2.2 then true else false))).getD (fa jc) false=true∧(Ckt.wires (ofFn (λ vq:Fin (N+N)=>if vq=_7 N e2.1 then true else if vq=_8 N e2.2 then true else false))).getD (fb jc) false=true)∧∀ jk:Fin Jn,(Ckt.wires (ofFn (λ vq:Fin (N+N)=>if vq=_7 N e2.1 then true else if vq=_8 N e2.2 then true else false))).getD (fa jk) false=true→(Ckt.wires (ofFn (λ vq:Fin (N+N)=>if vq=_7 N e2.1 then true else if vq=_8 N e2.2 then true else false))).getD (fb jk) false=true→(Ckt.wires (ofFn (λ vp:Fin (N+N)=>decide (vp=_7 N e2.1)))).getD (fa jk) false=false∧
  (Ckt.wires (ofFn (λ vp:Fin (N+N)=>decide (vp=_7 N e2.1)))).getD (fb jk) false=false)
 change E.card≤400*(Ckt.size+Jn)+16*N;by_cases Jz:Jn=0
 · have Lw:E=∅:=by
    rw[Finset.eq_empty_iff_forall_notMem];intro e he;obtain⟨_,_,⟨jc,_⟩,_⟩:=(_A he).2;exact (Jz▸jc).elim0
   rw[Lw];simp
 by_cases hN7:N≤7
 · have cX:E.card≤ N*N:=by
    simpa[card_univ,Fintype.card_prod,Fintype.card_fin] using _C (Finset.subset_univ E)
   have hnn:N*N≤16*N:=Nat.mul_le_mul_right N (by omega);omega
 · have qZ:∀ jd,(Ckt.lineDegrees (N+N) (Ico N (N+N))).getD (fa jd) 0≤2:=λ jd=>(hdeg jd).1;have gP:∀ jd,(Ckt.lineDegrees (N+N) (Ico N (N+N))).getD (fb jd) 0≤2:=λ jd=>(hdeg jd).2
   have VF:∀ p l:Fin N,(λ vq:Fin (N+N)=>if vq=_7 N p then true else if vq=_8 N l then true else false)=yd p l:=by
    intro p l;funext vq
    by_cases h1:vq=_7 N p <;> by_cases h2:vq=_8 N l <;>
     simp[yd,h1,h2]
   have SW:∀ p:Fin N,(λ vp:Fin (N+N)=>decide (vp=_7 N p))=yG p:=by intro p;funext vp;simp[yG]
   let E₁:=E.filter λ e=>I e.1 e.2∧∃ j:Fin Jn,(Ckt.wires (ofFn (yd e.1 e.2))).getD (fa j) false=true∧(Ckt.wires (ofFn (yG e.1))).getD (fa j) false=false∧(run (vh N Ckt) (vy N Ckt (ofFn (λ q=>decide (q=e.1))))
    (ofFn (λ u=>decide (u=e.2)))).getD (vr N Ckt (fb j)) false=true
   let E₂:=E.filter λ e=>I e.1 e.2∧∃ j:Fin Jn,(Ckt.wires (ofFn (yd e.1 e.2))).getD (fb j) false=true∧(Ckt.wires (ofFn (yG e.1))).getD (fb j) false=false∧(run (vh N Ckt) (vy N Ckt (ofFn (λ q=>decide (q=e.1))))
    (ofFn (λ u=>decide (u=e.2)))).getD (vr N Ckt (fa j)) false=true
   let E₃:=E.filter λ e=>e∉v0 I Ckt∧gS (N:=N) I Ckt fa fb e.1 e.2;have zu:E⊆(v0 I Ckt∪E₁∪E₂)∪E₃:=by
    intro⟨p,l⟩ he;have he':=(_A he).2;have wK:I p l:=he'.1;obtain⟨j,Ww,WO⟩:=he'.2.2.1;obtain⟨d3,YI⟩:=he'.2.2.2 j Ww WO;rw[VF p l] at Ww WO;rw[SW p] at d3 YI;by_cases hb:(p,l)∈v0 I Ckt
    · exact _D _ (_D _ (_D _ hb))
    · by_cases hfb1:(run (vh N Ckt) (vy N Ckt (ofFn (λ q=>decide (q=p)))) (ofFn (λ u=>decide (u=l)))).getD (vr N Ckt (fb j)) false=true
      · exact _D _ (_D _ (_G _ (_B ⟨he,wK,j,Ww,d3,hfb1⟩)))
      · by_cases hfa1:(run (vh N Ckt) (vy N Ckt (ofFn (λ q=>decide (q=p)))) (ofFn (λ u=>decide (u=l)))).getD (vr N Ckt (fa j)) false=true
        · exact _D _ (_G _ (_B ⟨he,wK,j,WO,YI,hfa1⟩))
        · refine _G _ (_B ⟨he,hb,wK,j,Ww,WO,d3,YI,?_,?_⟩)
          · rw[uZ,kI];exact Bool.eq_false_iff.mpr hfa1
          · rw[uZ,kI];exact Bool.eq_false_iff.mpr hfb1
   have W8:=qK N Jn I Ckt fa fb hI hm qZ gP vM E₁ E₂
    (λ _ he=>(_A he).2) (λ _ he=>(_A he).2)
   have z6:∀ e∈E₃,(e.1,e.2)∉v2 I Ckt:=by intro e he Mp;exact (_A he).2.1 (_D _ (_D _ (_D _ Mp)))
   have qc:∀ p l r,(p,l)∈E₃→ r∈Ico N (N+(vh N Ckt).length)→2≤(vk (N:=N) (vh N Ckt) (vc I Ckt) r).card→ l∈vk (N:=N) (vh N Ckt) (vc I Ckt) r→¬ ∀ u∈vk (N:=N) (vh N Ckt) (vc I Ckt) r,I p u:=by
    intro p l r he hr h2 hl cn;apply (_A he).2.1
    refine _G _ (_B ⟨_H _,r,hr,h2,cn,hl⟩)
   have h3:=Uh I hI Ckt fa fb hm qZ gP vM (kD I Ckt)
    (λ r q hq=>by obtain⟨g,hg,ha,xS,vR⟩:=mC I Ckt hm r q hq;exact⟨g,hg,ha,xS.1,xS.2,vR⟩) E₃ z6
    (λ p l r he wK qk XW=>kR I Ckt hm p l wK (_A he).2.1 r qk XW)
    qc
    (λ K root line xH qj Zs PY=>(mJ I hI Ckt hm root line xH qj (λ e he=>⟨(_A (_A (Zs he)).1).2.1,(_A (Zs he)).2.1⟩) PY).trans (by
     have h_inl:=nH N Ckt;omega))
    (λ _ he=>(_A he).2.2)
    (λ k4 c9 hA hB m7 kJ=>nt I hI Ckt fa fb hm qZ gP vM (kD I Ckt) (λ r q hq=>by
     obtain⟨g,hg,ha,xS,vR⟩:=mC I Ckt hm r q hq;exact⟨g,hg,ha,xS.1,xS.2,vR⟩) E₃ z6
     (λ p l r he wK qk XW=>kR I Ckt hm p l wK (_A he).2.1 r qk XW)
     qc (λ _ he=>(_A he).2.2) k4 c9 hA hB m7 kJ)
   have hcard_cov:E.card≤(v0 I Ckt∪E₁∪E₂).card+E₃.card:=(_C zu).trans (_J _ _);have Us:(Mc.vP N Ckt\Mc.vI N Ckt).card=M1.vA N 2 Ckt.gates-(Mc.vI N Ckt).card:=dk Ckt;have W7:(Mc.vI N Ckt).card≤ M1.vA N 2 Ckt.gates:=by rw[← xD N Ckt];exact _C (Mc.yO N Ckt)
   have US:=M1.ue N Ckt.gates;change _≤ Ckt.size at US;have Rz:(Mc.vI N Ckt).card=(vI N Ckt).card:=rfl;rw[Rz] at h3 Us W7;omega
end SmallBareAndBridge06
end PEqualNP.Outside.L_meta_1393
theorem PEqualNP.Outside.L_meta_1393 :
 ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (fr : ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2 ∧ (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fb jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD fr false = false ∧ (∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jc) false = true) ∧ ∀ jk : Fin Jn, (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jk) false = true → (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fb jk) false = true → (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fa jk) false = false ∧ (Ckt.wires (List.ofFn (fun vp : Fin (N + N) => decide (vp = Fin.castAdd N e2.1)))).getD (fb jk) false = false)).card ≤ 400 * (Ckt.size + Jn) + 16 * N := by
 exact PEqualNP.Outside.L_meta_1393.gA
