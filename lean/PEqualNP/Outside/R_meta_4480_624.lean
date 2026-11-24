import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4480_624
    (pendant : ∀ (n : ℕ) (H : (Fin n → Bool) → Bool) (c : Fin n) (S K : Finset (Fin n)),
      S.Nonempty → Disjoint S K → c∉S → c∉K →
      (∀ x v b, v=c ∨ v∈S → H (Function.update x v b)=H x) →
      H (fun _ => false)=false → (∀ i : Fin n,H (fun j => decide (j=i))=false) →
      (∃ x,H x=true) → ∀ C : Circuit, IsAO2 n C →
      (∀ x, circuitFun n C x = (H x || (x c && (decide (∃ i∈S,x i=true) || decide (∃ i∈K,x i=true))))) →
      ∃ D : Circuit, IsAO2 n D ∧ (∀ x,circuitFun n D x=H x) ∧
           D.size+S.card+1+(if K.Nonempty then 1 else 0)≤C.size)
    (merge : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (a b : Fin C.size),
      let val := fun k (x : Fin n → Bool) => (C.wires (List.ofFn (Function.update x v false))).getD k false
      let cheap := fun j : Fin C.size => (∃ c : Bool,∀ x,val (n+j.val) x=c) ∨
        ∃ k<n+j.val,∀ x,val (n+j.val) x=val k x
      IsAO2 n C → a≠b → cheap a → cheap b → (∃ x y,val C.output x≠val C.output y) →
      ∃ D : Circuit, IsAO2 n D ∧ (∀ x,circuitFun n D x=val C.output x) ∧ D.size+2≤C.size)
    (branching : ∀ (p q : ℕ) (E : Finset (Fin p × Fin q)) (C : Circuit),
      let L := fun e : Fin p × Fin q => Fin.castAdd q e.1
      let R := fun e : Fin p × Fin q => Fin.natAdd p e.2
      let F := fun c => E.filter (fun e => L e=c ∨ R e=c)
      let P := fun c => (F c).filter (fun e => (F (if L e=c then R e else L e)).card=1)
      let ok := fun (A : Finset (Fin p × Fin q)) (B : Circuit) =>
        IsAO2 (p+q) B ∧ ∀ x,circuitFun (p+q) B x=decide (∃ e∈A,x (L e)=true ∧ x (R e)=true)
      let cheap := fun (v : Fin (p+q)) (j : Fin C.size) =>
      let val := fun k (x : Fin (p+q) → Bool) => (C.wires (List.ofFn (Function.update x v false))).getD k false
      ∃ k<p+q+j.val,∀ x,val (p+q+j.val) x=val k x
      (∀ a b u v,a≠b → u≠v → ¬ ((a,u)∈E ∧ (a,v)∈E ∧ (b,u)∈E ∧ (b,v)∈E)) →
      ok E C → (∃ c,(F c).card=1) →
      (∀ v,(F v).card=1 → ∀ a b,cheap v a → cheap v b → a=b) →
      (∀ c,(P c).Nonempty → (P c).card+2≤(F c).card) →
      ∃ t D,(F t).Nonempty ∧ ok (E \ F t) D ∧ D.size+(F t).card+1≤C.size) : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ ∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ x9 ∈ x6, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true);   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) →     x6 x3 x4 →       (∃ (x9 : Fin (x1 + x2)), (Finset.filter (x5 x9) x3).card = (1 : ℕ)) →         ∃ (x10 : Fin (x1 + x2)),           have x11 : Finset (Fin x1 × Fin x2) := {x11 ∈ x3 | ¬x5 x10 x11};           x11.card < x3.card ∧ (x11 = ∅ ∨ ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), x6 x11 x12 ∧ x12.size + (x3.card - x11.card) + (1 : ℕ) ≤ x4.size) := by

  classical
  intro p q E C
  let L := fun e : Fin p × Fin q => Fin.castAdd q e.1
  let R := fun e : Fin p × Fin q => Fin.natAdd p e.2
  let touch := fun (c : Fin (p+q)) (e : Fin p × Fin q) => L e=c ∨ R e=c
  let F := fun c => E.filter (touch c)
  let mate := fun c e => if L e=c then R e else L e
  let P := fun c => (F c).filter (fun e => (F (mate c e)).card=1)
  let ok := fun (A : Finset (Fin p × Fin q)) (B : Circuit) =>
    IsAO2 (p+q) B ∧ ∀ x,circuitFun (p+q) B x=decide (∃ e∈A,x (L e)=true ∧ x (R e)=true)
  dsimp only
  intro sq good leaf
  change ok E C at good
  change ∃ c,(F c).card=1 at leaf
  let cheap := fun (v : Fin (p+q)) (j : Fin C.size) =>
      let val := fun k (x : Fin (p+q) → Bool) => (C.wires (List.ofFn (Function.update x v false))).getD k false
      (∃ b : Bool,∀ x,val (p+q+j.val) x=b) ∨ ∃ k<p+q+j.val,∀ x,val (p+q+j.val) x=val k x
  by_cases many : ∃ v,(F v).card=1 ∧ ∃ a b,cheap v a ∧ cheap v b ∧ a≠b
  · obtain ⟨v,hv,a,b,ha,hb,neq⟩ := many
    let A := E.filter (fun e => ¬touch v e)
    have parts : (F v).card+A.card=E.card := Finset.card_filter_add_card_filter_not ..
    refine ⟨v,show A.card<E.card by omega,?_⟩
    by_cases emp : A=∅
    · exact Or.inl emp
    right
    let f := fun x : Fin (p+q) → Bool => circuitFun (p+q) C (Function.update x v false)
    have sem (x : Fin (p+q) → Bool) : f x=decide (∃ e∈A,x (L e)=true ∧ x (R e)=true) := by
      rw [show f x=circuitFun (p+q) C (Function.update x v false) from rfl,good.2]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_iff]
      constructor
      · rintro ⟨e,he,h1,h2⟩
        have nl : L e≠v := fun eq => by simp [eq] at h1
        have nr : R e≠v := fun eq => by simp [eq] at h2
        exact ⟨e,Finset.mem_filter.mpr ⟨he,not_or.mpr ⟨nl,nr⟩⟩,by simpa [Function.update_of_ne nl] using h1,by simpa [Function.update_of_ne nr] using h2⟩
      · rintro ⟨e,he,h1,h2⟩
        obtain ⟨he,h⟩ := Finset.mem_filter.mp he
        obtain ⟨nl,nr⟩ := not_or.mp (show ¬(L e=v ∨ R e=v) from h)
        exact ⟨e,he,by simpa [Function.update_of_ne nl] using h1,by simpa [Function.update_of_ne nr] using h2⟩
    have nc : ∃ x y,f x≠f y := by
      obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr emp
      have no : f (fun _ => false)=false := by simp [sem]
      have yes : f (fun _ => true)=true := (sem _).trans (decide_eq_true ⟨e,he,rfl,rfl⟩)
      exact ⟨fun _ => false,fun _ => true,by rw [no,yes];decide⟩
    obtain ⟨D,ao,ev,size⟩ := merge (p+q) C v a b good.1 neq ha hb nc
    exact ⟨D,⟨ao,fun x => (ev x).trans (sem x)⟩,by change D.size+(E.card-A.card)+1≤C.size;omega⟩
  have lonely (v) (h : (F v).card=1) (a b) (ha : cheap v a) (hb : cheap v b) : a=b := by
    by_contra neq;exact many ⟨v,h,a,b,ha,hb,neq⟩
  by_cases hard : ∀ c,(P c).Nonempty → (P c).card+2≤(F c).card
  · obtain ⟨t,D,non,dok,save⟩ := branching p q E C sq good leaf
      (fun v hv a b ha hb => lonely v hv a b (Or.inr ha) (Or.inr hb)) hard
    let A := E.filter (fun e => ¬touch t e)
    have same : E \ F t=A := by
      ext e; simp only [F,A,Finset.mem_sdiff,Finset.mem_filter];tauto
    have part : (F t).card+A.card=E.card := Finset.card_filter_add_card_filter_not ..
    have pos : 0<(F t).card := Finset.card_pos.mpr non
    change D.size+(F t).card+1≤C.size at save
    rw [same] at dok
    exact ⟨t,show A.card<E.card by omega,Or.inr ⟨D,dok,by change D.size+(E.card-A.card)+1≤C.size;omega⟩⟩
  push_neg at hard
  obtain ⟨c,non,small⟩ := hard
  let I := F c
  let A := E.filter (fun e => ¬touch c e)
  let S := (P c).image (mate c)
  let K := (I \ P c).image (mate c)
  have part : I.card+A.card=E.card := Finset.card_filter_add_card_filter_not ..
  have psub : P c ⊆ I := Finset.filter_subset .. 
  have ipos := Finset.card_pos.mpr (non.mono psub)
  refine ⟨c,show A.card<E.card by omega,?_⟩
  by_cases empty : A=∅
  · exact Or.inl empty
  right
  have lr (e f : Fin p × Fin q) : L e≠R f := by
    intro h;have hv := congrArg Fin.val h
    change e.1.val=p+f.2.val at hv
    have := e.1.isLt; omega
  have touchI {e} (he : e∈I) : touch c e := (Finset.mem_filter.mp he).2
  have ends {e} (he : e∈I) : (L e=c ∧ R e=mate c e) ∨ (R e=c ∧ L e=mate c e) := by
    rcases touchI he with l|r
    · exact Or.inl ⟨l,by simp [mate,l]⟩
    · have l : L e≠c := fun h => lr e e (h.trans r.symm)
      exact Or.inr ⟨r,by simp [mate,l]⟩
  have inject : Set.InjOn (mate c) (↑I : Set _) := by
    intro e he f hf eq
    rcases ends he with ⟨l,r⟩|⟨r,l⟩ <;> rcases ends hf with ⟨l',r'⟩|⟨r',l'⟩
    · exact Prod.ext (Fin.castAdd_inj.mp (l.trans l'.symm)) (Fin.natAdd_injective q p (r.trans (eq.trans r'.symm)))
    · exact (lr e f (l.trans r'.symm)).elim
    · exact (lr f e (l'.trans r.symm)).elim
    · exact Prod.ext (Fin.castAdd_inj.mp (l.trans (eq.trans l'.symm))) (Fin.natAdd_injective q p (r.trans r'.symm))
  have csafe {e} (he : e∈I) : mate c e≠c := by
    rcases ends he with ⟨l,r⟩|⟨r,l⟩
    · exact fun eq => lr e e (l.trans (r.trans eq).symm)
    · exact fun eq => lr e e ((l.trans eq).trans r.symm)
  have Spos : S.Nonempty := non.image _
  have Sc : c∉S := by
    intro h;obtain ⟨e,he,eq⟩ := Finset.mem_image.mp h
    exact csafe (psub he) eq
  have Kc : c∉K := by
    intro h;obtain ⟨e,he,eq⟩ := Finset.mem_image.mp h
    exact csafe (Finset.mem_sdiff.mp he).1 eq
  have dis : Disjoint S K := by
    apply Finset.disjoint_left.mpr
    intro t h k
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨f,hf,eq⟩ := Finset.mem_image.mp k
    have fe := inject (Finset.mem_sdiff.mp hf).1 (psub he) eq
    exact (Finset.mem_sdiff.mp hf).2 (fe ▸ he)
  have sct : S.card=(P c).card := Finset.card_image_of_injOn (inject.mono psub)
  have kp : K.Nonempty ↔ (P c).card<I.card := by
    rw [show K=(I \ P c).image (mate c) from rfl,Finset.image_nonempty,←Finset.card_pos,Finset.card_sdiff_of_subset psub]
    omega
  have raw {v} (hv : v=c ∨ v∈S) {e} (he : e∈A) : ¬touch v e := by
    rcases hv with rfl|hv
    · exact (Finset.mem_filter.mp he).2
    · obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hv
      have sel := Finset.mem_filter.mp hf
      have snd : touch (mate c f) f := (ends sel.1).elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
      intro ue
      have fm : f∈F (mate c f) := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp sel.1).1,snd⟩
      have em : e∈F (mate c f) := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,ue⟩
      have eq := Finset.card_le_one.mp sel.2.le f fm e em
      exact (Finset.mem_filter.mp he).2 (eq ▸ touchI sel.1)
  let H := fun x : Fin (p+q) → Bool => decide (∃ e∈A,x (L e)=true ∧ x (R e)=true)
  have quiet (x : Fin (p+q) → Bool) (v) (b) (hv : v=c ∨ v∈S) : H (Function.update x v b)=H x := by
    apply Bool.eq_iff_iff.mpr
    simp only [H,decide_eq_true_iff]
    constructor <;> rintro ⟨e,he,hl,hr⟩ <;> refine ⟨e,he,?_⟩
    all_goals
      have nl : L e≠v := fun h => raw hv he (Or.inl h)
      have nr : R e≠v := fun h => raw hv he (Or.inr h)
      simpa only [Function.update_of_ne nl,Function.update_of_ne nr] using And.intro hl hr
  have single (i : Fin (p+q)) : H (fun j => decide (j=i))=false := by
    simp only [H,decide_eq_true_iff,decide_eq_false_iff_not]
    rintro ⟨e,_,h,k⟩;exact lr e e (h.trans k.symm)
  have full : ∃ x,H x=true := by
    obtain ⟨e,h⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    exact ⟨fun _ => true,decide_eq_true ⟨e,h,rfl,rfl⟩⟩
  have edg (x) : circuitFun (p+q) C x=(H x || (x c && (decide (∃ i∈S,x i=true) || decide (∃ i∈K,x i=true)))) := by
    rw [good.2]
    apply Bool.eq_iff_iff.mpr
    simp only [H,decide_eq_true_iff,Bool.or_eq_true,Bool.and_eq_true]
    constructor
    · rintro ⟨e,he,l,r⟩
      by_cases inc : touch c e
      · have mem : e∈I := Finset.mem_filter.mpr ⟨he,inc⟩
        have output : x c=true ∧ x (mate c e)=true := by
          rcases ends mem with ⟨hl,hr⟩|⟨hr,hl⟩
          · exact ⟨hl ▸ l,hr ▸ r⟩
          · exact ⟨hr ▸ r,hl ▸ l⟩
        refine Or.inr ⟨output.1,?_⟩
        by_cases le : e∈P c
        · exact Or.inl ⟨_,Finset.mem_image_of_mem _ le,output.2⟩
        · exact Or.inr ⟨_,Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨mem,le⟩),output.2⟩
      · exact Or.inl ⟨e,Finset.mem_filter.mpr ⟨he,inc⟩,l,r⟩
    · rintro (⟨e,h,l,r⟩|⟨hc,side⟩)
      · exact ⟨e,(Finset.mem_filter.mp h).1,l,r⟩
      · have add (e) (he : e∈I) (hm : x (mate c e)=true) : ∃ f∈E,x (L f)=true ∧ x (R f)=true := by
          refine ⟨e,(Finset.mem_filter.mp he).1,?_⟩
          rcases ends he with ⟨l,r⟩|⟨r,l⟩
          · exact ⟨l.symm ▸ hc,r.symm ▸ hm⟩
          · exact ⟨l.symm ▸ hm,r.symm ▸ hc⟩
        rcases side with ⟨v,h,hv⟩|⟨v,h,hv⟩ <;> obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp h
        · exact add e (psub he) hv
        · exact add e (Finset.mem_sdiff.mp he).1 hv
  obtain ⟨D,ao,ev,sz⟩ := pendant (p+q) H c S K Spos dis Sc Kc quiet (by simp [H]) single full C good.1 edg
  refine ⟨D,⟨ao,ev⟩,?_⟩
  change D.size+(E.card-A.card)+1≤C.size
  change (P c).card+2>I.card at small
  rw [sct] at sz
  by_cases pos : K.Nonempty
  · simp only [if_pos pos] at sz;omega
  · have lim := mt kp.mpr pos
    simp only [if_neg pos] at sz;omega
