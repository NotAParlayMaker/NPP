import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2161

-- Encode the live nonconstant signals in a suffix with separate binary and negation budgets.
abbrev Word := BitVec 512

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def top : Word := BitVec.allOnes 512
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proper (a : Word) : Prop := a ≠ 0 ∧ a ≠ top
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
instance (a : Word) : Decidable (proper a) := by unfold proper; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def combine (disj : Bool) (a b : Word) : Word := if disj then a ||| b else a &&& b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma laws (a : Word) :
    combine true a 0 = a ∧ combine false a 0 = 0 ∧
    combine true a top = top ∧ combine false a top = a ∧
    combine true a a = a ∧ combine false a a = a := by
  exact ⟨by simp [combine], by simp [combine], BitVec.or_allOnes, BitVec.and_allOnes,
    BitVec.or_self, BitVec.and_self⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma comm (d : Bool) (a b : Word) : combine d a b = combine d b a := by
  cases d <;> simp [combine, BitVec.and_comm, BitVec.or_comm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
inductive Live (target : Word) : ℕ → ℕ → Finset Word → Prop
  | done : Live target 0 0 {target}
  | unary {b t U a} (ha : proper a) (fresh : ~~~a ∉ insert a U)
      (tail : Live target b t (insert (~~~a) U)) : Live target b (t+1) (insert a U)
  | binary {b t U a c d} (ha : proper a) (hc : proper c) (ne : a ≠ c)
      (fresh : combine d a c ∉ insert a (insert c U))
      (tail : Live target b t (insert (combine d a c) U)) :
      Live target (b+1) t (insert a (insert c U))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma Live.good {target : Word} (valid : proper target) {b t S} (h : Live target b t S) :
    ∀ a ∈ S, proper a := by
  induction h with
  | done => simpa using valid
  | unary ha hf ht ih =>
    intro a h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact ha
    · exact ih _ (Finset.mem_insert_of_mem h)
  | binary ha hc _ _ ht ih =>
    intro a h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact ha
    rcases Finset.mem_insert.mp h with rfl | h
    · exact hc
    · exact ih _ (Finset.mem_insert_of_mem h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Feasible (target : Word) (b t : ℕ) (S : Finset Word) : Prop :=
  ∃ i ≤ b, ∃ j ≤ t, ∃ T ⊆ S, Live target i j T

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma weaken {x b t S b' t' S'} (h : Feasible x b t S)
    (hb : b ≤ b') (ht : t ≤ t') (hs : S ⊆ S') : Feasible x b' t' S' := by
  obtain ⟨i,hi,j,hj,T,hT,hL⟩ := h
  exact ⟨i,hi.trans hb,j,hj.trans ht,T,hT.trans hs,hL⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma ignore {x z b t S} (hx : proper x) (h : Feasible x b t (insert z S))
    (hz : z ∈ S ∨ ¬ proper z) : Feasible x b t S := by
  obtain ⟨i,hi,j,hj,T,hT,hL⟩ := h
  refine ⟨i,hi,j,hj,T,?_,hL⟩
  intro a ha
  rcases Finset.mem_insert.mp (hT ha) with rfl | h
  · exact hz.resolve_right fun hnot => hnot (hL.good hx _ ha)
  · exact h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unary_pull {x a b t S} (hx : proper x) (ha : a ∈ S)
    (h : Feasible x b t (insert (~~~a) S)) : Feasible x b (t+1) S := by
  by_cases bad : ~~~a ∈ S ∨ ¬ proper (~~~a)
  · exact weaken (ignore hx h bad) le_rfl (by omega) (by rfl)
  obtain ⟨i,hi,j,hj,T,hT,hL⟩ := h
  by_cases hm : ~~~a ∈ T
  · let U := T.erase (~~~a)
    have inS : U ⊆ S := by
      intro y hy; obtain ⟨hne,hyT⟩ := Finset.mem_erase.mp hy
      exact (Finset.mem_insert.mp (hT hyT)).resolve_left hne
    have p : proper a := by
      by_contra nh
      unfold proper at nh
      push Not at nh
      by_cases za : a = 0
      · subst a; exact bad (Or.inr (by simp [proper,top]))
      · have zt := nh za
        subst a; exact bad (Or.inr (by simp [proper,top]))
    refine ⟨i,hi,j+1,by omega,insert a U,Finset.insert_subset ha inS,Live.unary p ?_ ?_⟩
    · intro h'
      exact bad (Or.inl ((Finset.insert_subset ha inS) h'))
    · simpa [U, Finset.insert_erase hm] using hL
  · exact ⟨i,hi,j,by omega,T,fun y hy => (Finset.mem_insert.mp (hT hy)).resolve_left (by
      rintro rfl; exact hm hy), hL⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma binary_pull {x a c b t S} (hx : proper x) (d : Bool) (ha : a ∈ S) (hc : c ∈ S)
    (h : Feasible x b t (insert (combine d a c) S)) : Feasible x (b+1) t S := by
  let z := combine d a c
  by_cases redundant : z ∈ S ∨ ¬ proper z
  · exact weaken (ignore hx h redundant) (by omega) le_rfl (by rfl)
  have simple {a c : Word} (haS : a ∈ S) (hcS : c ∈ S) (hz : ¬ (combine d a c ∈ S ∨ ¬ proper (combine d a c))) :
      proper a := by
    constructor
    · rintro rfl
      rw [comm] at hz
      cases d
      · rw [(laws c).2.1] at hz
        exact hz (Or.inr fun h => h.1 rfl)
      · rw [(laws c).1] at hz
        exact hz (Or.inl hcS)
    · rintro rfl
      rw [comm] at hz
      cases d
      · rw [(laws c).2.2.2.1] at hz
        exact hz (Or.inl hcS)
      · rw [(laws c).2.2.1] at hz
        exact hz (Or.inr fun h => h.2 rfl)
  have pa := simple ha hc redundant
  have pc := simple hc ha (by rwa [comm])
  have unequal : a ≠ c := by
    rintro rfl; apply redundant; left; cases d <;> simpa [z,combine] using ha
  obtain ⟨i,hi,j,hj,T,hT,hL⟩ := h
  by_cases hm : z ∈ T
  · let U := T.erase z
    have inS : U ⊆ S := by
      intro y hy; obtain ⟨hne,hyT⟩ := Finset.mem_erase.mp hy
      exact (Finset.mem_insert.mp (hT hyT)).resolve_left hne
    have subset := Finset.insert_subset ha (Finset.insert_subset hc inS)
    refine ⟨i+1,by omega,j,hj,insert a (insert c U),subset,Live.binary (d := d) pa pc unequal ?_ ?_⟩
    · intro hz
      exact redundant (Or.inl (subset hz))
    · simpa [U,z, Finset.insert_erase hm] using hL
  · exact ⟨i,by omega,j,hj,T,fun y hy => (Finset.mem_insert.mp (hT hy)).resolve_left (by
      rintro rfl; exact hm hy), hL⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Projection where
  q : Word → Word
  neg (a) : q (~~~a) = ~~~(q a)
  bin (d a c) : q (combine d a c) = combine d (q a) (q c)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def constants (P : Projection) (S : Finset Word) : ℕ :=
  (S.filter fun w => ¬ proper (P.q w)).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def charge (P : Projection) (w : Word) : ℕ := if proper (P.q w) then 0 else 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c_insert {P : Projection} (w : Word) (S : Finset Word) :
    constants P (insert w S) ≤ constants P S + charge P w := by
  by_cases h : proper (P.q w)
  · simp [constants, charge, Finset.filter_insert, h]
  · simpa [constants, charge, Finset.filter_insert, h] using
      Finset.card_insert_le w (S.filter fun v => ¬proper (P.q v))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c_fresh {P : Projection} (w : Word) (S : Finset Word) (hw : w ∉ S) :
    constants P (insert w S) = constants P S + charge P w := by
  by_cases h : proper (P.q w)
  · simp [constants, charge, Finset.filter_insert, h]
  · simp [constants, charge, Finset.filter_insert, h,
      Finset.card_insert_of_notMem (by simp [Finset.mem_filter,hw] :
        w ∉ S.filter fun v => ¬proper (P.q v))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma neg_proper_iff (w : Word) : proper (~~~w) ↔ proper w := by
  have aux (z : Word) : proper (~~~z) → proper z := by
    rintro h
    constructor <;> rintro rfl <;> simp [proper, top] at h
  exact ⟨aux _, fun h => aux (~~~w) (by simpa only [BitVec.not_not] using h)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma const_cases {w : Word} (h : ¬proper w) : w = 0 ∨ w = top := by
  by_cases z : w = 0
  · exact Or.inl z
  · exact Or.inr <| by by_contra ho; exact h ⟨z,ho⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma idle_of_const {a c : Word} (d : Bool) (h : ¬proper a ∨ ¬proper c) :
    combine d a c = a ∨ combine d a c = c ∨ ¬proper (combine d a c) := by
  have aux (a c : Word) (h : ¬proper c) :
      combine d a c = a ∨ ¬proper (combine d a c) := by
    rcases const_cases h with rfl | rfl <;> cases d
    · exact Or.inr fun h => h.1 (laws a).2.1
    · exact Or.inl (laws a).1
    · exact Or.inl (laws a).2.2.2.1
    · exact Or.inr fun h => h.2 (laws a).2.2.1
  rcases h with h | h
  · rw [comm]; exact Or.inr (aux c a h)
  · exact (aux a c h).imp_right Or.inr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma const_bin {a c : Word} (d : Bool) (ha : ¬proper a) (hc : ¬proper c) :
    ¬proper (combine d a c) := by
  rcases idle_of_const d (Or.inl ha : ¬proper a ∨ ¬proper c) with e|e|h
  · rwa [e]
  · rwa [e]
  · exact h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem project_live (P : Projection) {x : Word} (hx : proper (P.q x)) {b t S}
    (h : Live x b t S) :
    ∃ n, n + constants P S ≤ b ∧ Feasible (P.q x) n t (S.image P.q) := by
  induction h with
  | done =>
    refine ⟨0, by simp [constants,hx], 0, le_rfl,0,le_rfl,{P.q x}, by simp, .done⟩
  | @unary b t U a _ fresh tail ih =>
    obtain ⟨n,hn,h⟩ := ih
    have f : ~~~a ∉ U := fun he => fresh (Finset.mem_insert_of_mem he)
    have eq := c_fresh (P := P) (~~~a) U f
    have le := c_insert (P := P) a U
    have ng : charge P (~~~a) = charge P a := by simp [charge,P.neg,neg_proper_iff]
    refine ⟨n, by omega, ?_⟩
    rw [Finset.image_insert]
    rw [Finset.image_insert,P.neg] at h
    apply unary_pull hx (Finset.mem_insert_self ..)
    apply weaken h le_rfl le_rfl
    exact Finset.insert_subset_insert _ (Finset.subset_insert ..)
  | @binary b t U a c d _ _ _ fresh tail ih =>
    let z := combine d a c
    let A := insert (P.q a) (insert (P.q c) (U.image P.q))
    obtain ⟨n,hn,h⟩ := ih
    have f : z ∉ U := fun he => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem he))
    have ez := c_fresh (P := P) z U f
    have ec := c_insert (P := P) c U
    have ea := c_insert (P := P) a (insert c U)
    change n + constants P (insert z U) ≤ b at hn
    have hq : P.q z = combine d (P.q a) (P.q c) := P.bin ..
    have htail : Feasible (P.q x) n t (insert (P.q z) A) := by
      rw [Finset.image_insert] at h
      apply weaken h le_rfl le_rfl
      exact Finset.insert_subset_insert _ ((Finset.subset_insert ..).trans (Finset.subset_insert ..))
    rw [Finset.image_insert,Finset.image_insert]
    change ∃ n, _ ∧ Feasible _ n t A
    have ma : P.q a ∈ A := Finset.mem_insert_self ..
    have mc : P.q c ∈ A := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    by_cases pc : proper (P.q c) <;> by_cases pa : proper (P.q a)
    · have aa : charge P a = 0 := by simp [charge,pa]
      have ac : charge P c = 0 := by simp [charge,pc]
      refine ⟨n+1, by omega, binary_pull hx d ma mc ?_⟩
      rwa [←hq]
    all_goals
      have idle : P.q z ∈ A ∨ ¬proper (P.q z) := by
        rw [hq]
        rcases idle_of_const d (by tauto : ¬proper (P.q a) ∨ ¬proper (P.q c)) with ha|hc|hn
        · exact Or.inl (by rwa [ha])
        · exact Or.inl (by rwa [hc])
        · exact Or.inr hn
      refine ⟨n, ?_, ignore hx htail idle⟩
    · have aa : charge P a = 1 := by simp [charge,pa]
      have ac : charge P c = 0 := by simp [charge,pc]
      omega
    · have aa : charge P a = 0 := by simp [charge,pa]
      have ac : charge P c = 1 := by simp [charge,pc]
      omega
    · have aa : charge P a = 1 := by simp [charge,pa]
      have ac : charge P c = 1 := by simp [charge,pc]
      have az : charge P z = 1 := by simp [charge,hq,const_bin d pa pc]
      omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def bit (a : Word) (i : Fin 512) : Bool := a[i.val]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def tab (f : Fin 512 → Bool) : Word :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tab_bit (f : Fin 512 → Bool) (i : Fin 512) : bit (tab f) i = f i := by
  unfold bit tab
  rw [← BitVec.getLsbD_eq_getElem]
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt), List.getElem_ofFn]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def faceQ (f : Fin 512 → Fin 512) : Projection where
  q a := tab (fun i => bit a (f i))
  neg a := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    change bit (tab _) ⟨i, hi⟩ = (~~~(tab _))[i]
    rw [tab_bit,BitVec.getElem_not]
    change bit (~~~a) _ = !bit (tab _) ⟨i,hi⟩
    rw [tab_bit]; exact BitVec.getElem_not _
  bin d a c := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    cases d <;> change bit (tab _) ⟨i,hi⟩ = _ <;> rw [tab_bit]
    · change _ = (tab _ &&& tab _)[i]
      rw [BitVec.getElem_and]
      change _ = (bit (tab _) ⟨i,hi⟩ && bit (tab _) ⟨i,hi⟩)
      rw [tab_bit,tab_bit]; exact BitVec.getElem_and _
    · change _ = (tab _ ||| tab _)[i]
      rw [BitVec.getElem_or]
      change _ = (bit (tab _) ⟨i,hi⟩ || bit (tab _) ⟨i,hi⟩)
      rw [tab_bit,tab_bit]; exact BitVec.getElem_or _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q_bit (f : Fin 512 → Fin 512) (w : Word) (i : Fin 512) :
    bit ((faceQ f).q w) i = bit w (f i) := tab_bit _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def available (P : Projection) (S R : Finset Word) : Finset Word := S.image P.q ∪ R

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Guard (P : Projection) (x : Word) (S R : Finset Word) (t lo spent : ℕ) : Prop :=
  proper (P.q x) ∧ ∀ b, Feasible (P.q x) b t (available P S R) → lo ≤ b + spent

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma guard_bound {P x b t S R lo spent} (g : Guard P x S R t lo spent)
    (h : Live x b t S) : lo + constants P S ≤ b + spent := by
  obtain ⟨n,hn,hf⟩ := project_live P g.1 h
  have hb := g.2 n <| weaken hf le_rfl le_rfl Finset.subset_union_left
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma avail_child {P : Projection} {S T R : Finset Word} {z : Word}
    (h : T ⊆ insert z S) : available P T R ⊆ insert (P.q z) (available P S R) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hi|hr
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
    rcases Finset.mem_insert.mp (h ha) with rfl|hs
    · exact Finset.mem_insert_self ..
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs))
  · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hr)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cost (P : Projection) (S R : Finset Word) (z : Word) : ℕ :=
  if P.q z ∈ available P S R ∨ ¬ proper (P.q z) then 0 else 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma guard_binary {P x S T R t lo spent a c d} (g : Guard P x S R t lo spent)
    (ha : a ∈ S) (hc : c ∈ S) (hT : T ⊆ insert (combine d a c) S) :
    Guard P x T R t lo (spent + cost P S R (combine d a c)) := by
  refine ⟨g.1,?_⟩
  intro b h
  let z := combine d a c
  let A := available P S R
  have h' := weaken h le_rfl le_rfl (avail_child hT)
  change Feasible _ _ _ (insert (P.q z) A) at h'
  change lo ≤ b+(spent+cost P S R z)
  unfold cost
  split_ifs with free
  · simpa using g.2 b (ignore g.1 h' free)
  · have ma : P.q a ∈ A := Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
    have mc : P.q c ∈ A := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc)
    have hq : P.q z = combine d (P.q a) (P.q c) := P.bin ..
    rw [hq] at h'
    have hB := g.2 _ (binary_pull g.1 d ma mc h')
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma guard_unary {P x S T R t lo spent a} (g : Guard P x S R (t+1) lo spent)
    (ha : a ∈ S) (hT : T ⊆ insert (~~~a) S) :
    Guard P x T R t lo spent := by
  refine ⟨g.1,?_⟩
  intro b h
  have h' := weaken h le_rfl le_rfl (avail_child hT)
  rw [P.neg] at h'
  exact g.2 b (unary_pull g.1 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)) h')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma count_live {x b t S} (h : Live x b t S) : S.card ≤ b+1 := by
  induction h with
  | done => simp
  | @unary b t U a _ fresh tail ih =>
    have hn : ~~~a ∉ U := fun he => fresh (Finset.mem_insert_of_mem he)
    rw [Finset.card_insert_of_notMem hn] at ih
    exact (Finset.card_insert_le ..).trans ih
  | @binary b t U a c d _ _ _ fresh tail ih =>
    have hn : combine d a c ∉ U := fun he => fresh
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem he))
    rw [Finset.card_insert_of_notMem hn] at ih
    have hc := Finset.card_insert_le c U
    have ha := Finset.card_insert_le a (insert c U)
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def distinguishes (t : ℕ) (w : Word) (i j : Fin 512) : Prop :=
  if t = 0 then bit w i = true ∧ bit w j = false else bit w i ≠ bit w j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma distinguish_bit {a c : Word} {d : Bool} {t : ℕ} {i j : Fin 512}
    (h : distinguishes t (combine d a c) i j) :
    distinguishes t a i j ∨ distinguishes t c i j := by
  have eq (k : Fin 512) : bit (combine d a c) k =
      if d then (bit a k || bit c k) else (bit a k && bit c k) := by
    cases d <;> simp [bit,combine]
  cases d <;> by_cases ht : t=0 <;>
    simp only [distinguishes,ht,eq,ite_true,ite_false,Bool.false_eq_true] at h ⊢ <;>
    cases e1 : bit a i <;> cases e2 : bit a j <;> cases e3 : bit c i <;> cases e4 : bit c j <;> simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma distinguish_old {a : Word} {t : ℕ} {i j : Fin 512} (h : distinguishes t a i j) :
    distinguishes (t+1) a i j := by
  simp only [distinguishes,Nat.succ_ne_zero,ite_false]
  by_cases ht : t=0
  · simp only [distinguishes,ht,ite_true] at h
    simp [h.1,h.2]
  · simpa [distinguishes,ht] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma distinguishes_live {x b t S} (h : Live x b t S) {i j : Fin 512}
    (hi : bit x i = true) (hj : bit x j = false) : ∃ a ∈ S, distinguishes t a i j := by
  induction h with
  | done => exact ⟨x,by simp,by simp [distinguishes,hi,hj]⟩
  | unary _ _ tail ih =>
    obtain ⟨a,ha,hm⟩ := ih
    rcases Finset.mem_insert.mp ha with rfl | hw
    · refine ⟨_,Finset.mem_insert_self ..,?_⟩
      have h := distinguish_old hm
      simpa [distinguishes,bit] using h
    · exact ⟨_,Finset.mem_insert_of_mem hw,distinguish_old hm⟩
  | binary _ _ _ _ tail ih =>
    obtain ⟨a,ha,hm⟩ := ih
    rcases Finset.mem_insert.mp ha with rfl | hw
    · rcases distinguish_bit hm with hl|hr
      · exact ⟨_,Finset.mem_insert_self ..,hl⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self ..),hr⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw),hm⟩

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gv (w : List Word) (g : Gate) : Word :=
  let xs := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => xs.foldr (combine false) top
  | .or => xs.foldr (combine true) 0
  | .not => ~~~(xs.headD 0)
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def execute (gs : List Gate) (w : List Word) : List Word :=
  gs.foldl (fun l g => l ++ [gv l g]) w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pool (w : List Word) : Finset Word := insert 0 (insert top w.toFinset)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma read_mem (w : List Word) (i : Nat) : w.getD i 0 ∈ pool w := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : w[i]? with
  | none => exact Finset.mem_insert_self ..
  | some a =>
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (List.mem_toFinset.mpr (List.mem_of_getElem? hi)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def negative (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma gate_pull {x b t w} (hx : proper x) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : Feasible x b t (insert (gv w g) (pool w))) :
    Feasible x (b + (if negative g then 0 else 1))
      (t + (if negative g then 1 else 0)) (pool w) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  obtain ⟨ops,hi⟩ := hg
  have zero' : 0 ∈ pool w := Finset.mem_insert_self ..
  have top' : top ∈ pool w := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
  have idle (z : Word) (hz : z ∈ pool w) (h : Feasible x b t (insert z (pool w))) :
      Feasible x (b+1) t (pool w) := by
    exact weaken (ignore hx h (Or.inl hz)) (by omega) le_rfl (by rfl)
  cases ins with
  | nil =>
    rcases ops with rfl | rfl | rfl
    · exact idle top top' h
    · exact idle 0 zero' h
    · exact unary_pull hx zero' h
  | cons a ins =>
    cases ins with
    | nil =>
      rcases ops with rfl | rfl | rfl
      · exact idle _ (read_mem _ a) (by simpa only [gv,List.map_cons,List.map_nil,
          List.foldr_cons,List.foldr_nil,(laws _).2.2.2.1] using h)
      · exact idle _ (read_mem _ a) (by simpa only [gv,List.map_cons,List.map_nil,
          List.foldr_cons,List.foldr_nil,(laws _).1] using h)
      · exact unary_pull hx (read_mem _ a) h
    | cons c is =>
      cases is with
      | cons i ss => simp at hi
      | nil =>
        rcases ops with rfl | rfl | rfl
        · exact binary_pull (t := t) hx false (read_mem _ a) (read_mem _ c) (by
            simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
              (laws _).2.2.2.1] using h)
        · exact binary_pull (t := t) hx true (read_mem _ a) (read_mem _ c) (by
            simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
              (laws _).1] using h)
        · exact unary_pull hx (read_mem _ a) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma extract {x} (hx : proper x) (gs : List Gate) (w : List Word)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hout : x ∈ execute gs w) :
    Feasible x (gs.filter (fun g => !negative g)).length (gs.filter negative).length (pool w) := by
  induction gs generalizing w with
  | nil =>
    exact ⟨0,le_rfl,0,le_rfl,{x},Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (List.mem_toFinset.mpr hout))),.done⟩
  | cons g gs ih =>
    have h := ih (w ++ [gv w g]) (fun a ha => legal a (by simp [ha])) hout
    have e : pool (w ++ [gv w g]) = insert (gv w g) (pool w) := by
      ext a; simp [pool]; tauto
    rw [e] at h
    have m := gate_pull hx g (legal g (by simp)) h
    cases n : negative g <;> simpa [List.filter_cons,n] using m

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma bit_zero (i) : bit 0 i = false := by simp [bit]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma bit_top (i) : bit top i = true := by
  change (BitVec.allOnes 512)[i.val] = true
  exact BitVec.getElem_allOnes ..
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma bit_not (w : Word) (i) : bit (~~~w) i = !bit w i := BitVec.getElem_not _
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma bit_bin (d : Bool) (a b : Word) (i) : bit (combine d a b) i =
    if d then bit a i || bit b i else bit a i && bit b i := by
  cases d <;> simp [bit,combine]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma read_bit (w : List Word) (j : Nat) (i : Fin 512) :
    (w.map (fun a => bit a i)).getD j false = bit (w.getD j 0) i := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma run_bit (g : Gate) (w : List Word) (i : Fin 512)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit (gv w g) i = g.op.eval (g.inputs.map fun j => (w.map (fun a => bit a i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [read_bit]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_top _
    | cons a l ih =>
      change bit (combine false _ _) i = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit (w.getD a 0) i && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit (combine true _ _) i = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit (w.getD a 0) i || x) ih
  · cases l with
    | nil => exact (bit_not (0 : Word) i).trans (by rw [bit_zero]; rfl)
    | cons a l => exact bit_not _ _
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma execute_bits (gs : List Gate) (w : List Word) (i : Fin 512)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (fun a => bit a i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
      (w.map (fun a => bit a i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit g w i (hg g (by simp))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma foldl_append_getD {α : Type} (f : List α → Gate → α) (gs : List Gate)
    (l : List α) (i : Nat) (hi : i < l.length) (d : α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) l).getD i d = l.getD i d := by
  induction gs generalizing l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (l ++ [f l g]).length := by simp; omega
    rw [ih (l ++ [f l g]) hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def raw : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def target : Word := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def testRow (i : Fin 512) (j : Fin 9) := i.val.testBit j.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawRow (i : Fin 512) : raw.map (fun a => bit a i) = List.ofFn (testRow i) := by
  have ok : ∀ r : Fin 512, raw.map (fun a => bit a r) = List.ofFn (testRow r) := by decide +kernel
  exact ok i
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma targetRow (i : Fin 512) : bit target i = edgeF (testRow i) := by
  have ok : ∀ r : Fin 512, bit target r = edgeF (testRow r) := by decide +kernel
  exact ok i
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma targetProper : proper target := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma target_mem (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = edgeF y) :
    target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have e : w.getD C.output 0 = target := by
    apply BitVec.eq_of_getElem_eq
    intro r hr
    change bit (w.getD C.output 0) ⟨r,hr⟩ = bit target ⟨r,hr⟩
    rw [targetRow, ←read_bit]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ (fun g hg => (hf g hg).1),rawRow]
    exact he _
  have h := read_mem w C.output
  rw [e] at h
  simpa only [pool,Finset.mem_insert,List.mem_toFinset, targetProper.1,targetProper.2,
    false_or] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def extra : Word := combine true (raw.getD 0 0) (raw.getD 2 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def start : List Word := raw ++ [extra]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma extraRow (r : Fin 512) : bit extra r = (testRow r 0 || testRow r 2) := by
  have ok : ∀ i : Fin 512, bit extra i = (testRow i 0 || testRow i 2) := by decide +kernel
  exact ok r
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma first_value {g : Gate} {gs : List Gate}
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (first : ∀ y : Fin 9 → Bool,
      ((Circuit.mk (g :: gs) 0).wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) :
    gv raw g = extra := by
  apply BitVec.eq_of_getElem_eq
  intro r hr
  let i : Fin 512 := ⟨r,hr⟩
  change bit (gv raw g) i = bit extra i
  rw [extraRow, run_bit g raw i hg,rawRow]
  have h := first (testRow i)
  simp only [Circuit.wires,List.foldl_cons] at h
  rw [foldl_append_getD _ gs _ 9 (by simp) false] at h
  simpa [List.getD_eq_getElem?_getD] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma uniqueNegCount (gs : List Gate)
    (h : ∃! i : Fin gs.length, negative (gs.get i) = true) :
    (gs.filter negative).length = 1 := by
  induction gs with
  | nil => obtain ⟨i, _⟩ := h; exact Fin.elim0 i
  | cons g gs ih =>
    obtain ⟨i, hi, only⟩ := h
    by_cases hg : negative g = true
    · have hone : (0 : Fin (g :: gs).length) = i := only 0 hg
      have nil : gs.filter negative = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro a ha hn
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp ha
        have hs : negative ((g :: gs).get j.succ) = true := by
          change negative (gs.get j) = true
          rwa [hj]
        have eq := (only j.succ hs).trans hone.symm
        exact (Fin.succ_ne_zero j) eq
      simp [hg,nil]
    · have htail : ∃! j : Fin gs.length, negative (gs.get j) = true := by
        cases i using Fin.cases with
        | zero => exact (hg hi).elim
        | succ j =>
          refine ⟨j, hi, ?_⟩
          intro k hk
          exact Fin.succ_injective _ (only k.succ hk)
      simpa [hg] using ih htail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma first_nonneg {g : Gate} {gs : List Gate}
    (hfirst : ∀ y : Fin 9 → Bool,
      ((Circuit.mk (g :: gs) 0).wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) :
    negative g = false := by
  cases hop : g.op <;> simp only [negative,hop]
  let x : Fin 9 → Bool := fun _ => false
  have z (j : ℕ) : (List.ofFn x).getD j false = false := by
    by_cases hj : j < 9
    · have hh : j < (List.ofFn x).length := by simpa only [List.length_ofFn] using hj
      rw [List.getD_eq_getElem _ _ hh,List.getElem_ofFn]
    · have hn : (List.ofFn x).length ≤ j := by simpa using Nat.le_of_not_gt hj
      exact List.getD_eq_default _ _ hn
  have h := hfirst x
  simp only [Circuit.wires, List.foldl_cons] at h
  have hl : 9 < (List.ofFn x ++ [g.op.eval (g.inputs.map fun j =>
      (List.ofFn x).getD j false)]).length := by simp
  rw [foldl_append_getD _ gs _ 9 hl false] at h
  have heq : (List.ofFn x ++ [g.op.eval (g.inputs.map fun j =>
      (List.ofFn x).getD j false)]).getD 9 false =
      g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false) := by
    simp [List.getD_eq_getElem?_getD]
  rw [heq,hop] at h
  cases he : g.inputs with
  | nil => simp [he,GateOp.eval,x] at h
  | cons a as =>
    simp only [he, List.map_cons, GateOp.eval, List.headD_cons, z] at h
    exact Bool.noConfusion h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma neg_iff (g : Gate) : negative g = true ↔ g.op = GateOp.not := by
  cases g with
  | mk op xs => cases op <;> simp [negative]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma starts {C : Circuit} (hsize : C.size ≤ 15) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hn : ∃! i : Fin C.gates.length, (C.gates.get i).op = GateOp.not)
    (hw9 : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2))
    (he : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = edgeF y) :
    Feasible target 13 1 start.toFinset := by
  obtain ⟨i,hi,only⟩ := hn
  have hn1 := uniqueNegCount C.gates ⟨i,(neg_iff _).2 hi,fun j hj => only j ((neg_iff _).1 hj)⟩
  cases hgs : C.gates with
  | nil => simp [hgs] at hn1
  | cons g gs =>
    have hlen : gs.length ≤ 14 := by
      change C.gates.length ≤ 15 at hsize; rw [hgs] at hsize; simp at hsize; omega
    have hh : ∀ y : Fin 9 → Bool,
        ((Circuit.mk (g :: gs) 0).wires (List.ofFn y)).getD 9 false = (y 0 || y 2) := by
      intro y; simpa only [Circuit.wires,hgs] using hw9 y
    have hneg := first_nonneg hh
    rw [hgs] at hn1
    simp only [List.filter_cons, hneg, Bool.false_eq_true, ↓reduceIte] at hn1
    have counts := List.length_eq_length_filter_add (l:=gs) negative
    change gs.length = (gs.filter negative).length + (gs.filter (fun g => !negative g)).length at counts
    have hv := first_value (hf g (by rw [hgs]; simp)).1 hh
    have hm := target_mem C hf he
    rw [hgs] at hm
    change target ∈ execute gs (raw ++ [gv raw g]) at hm
    rw [hv] at hm
    have h := extract targetProper gs start (fun a ha => hf a (by rw [hgs]; simp [ha])) hm
    have h' := weaken h (show (gs.filter (fun g => !negative g)).length ≤ 13 by omega)
      (show (gs.filter negative).length ≤ 1 by omega) (by rfl)
    exact ignore targetProper (ignore targetProper h' (Or.inr fun q => q.1 rfl))
      (Or.inr fun q => q.2 rfl)

-- Prune live suffixes with paired truth-table rows and induced graph lower bounds.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Charts (x : Word) where
  p : Fin 512 → Fin 512
  n : Fin 512 → Fin 512
  hp : ∀ i, bit x (p i) = true
  hn : ∀ i, bit x (n i) = false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Wire {x : Word} (c : Charts x) where
  w : Word
  p : Word
  n : Word
  hp : ∀ i, bit p i = bit w (c.p i)
  hn : ∀ i, bit n i = bit w (c.n i)

namespace Wire
variable {x : Word} {c : Charts x}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def binary (d : Bool) (a b : Wire c) : Wire c :=
  ⟨combine d a.w b.w,combine d a.p b.p,combine d a.n b.n,
    fun i => by simp only [bit_bin,a.hp,b.hp],
    fun i => by simp only [bit_bin,a.hn,b.hn]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def flip (a : Wire c) : Wire c :=
  ⟨~~~a.w,~~~a.p,~~~a.n,fun i => by simp only [bit_not,a.hp],
    fun i => by simp only [bit_not,a.hn]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sep (t : ℕ) (a : Wire c) : Word :=
  if t = 0 then a.p &&& ~~~a.n else a.p ^^^ a.n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sep_bit {t : ℕ} (a : Wire c) (i : Fin 512) :
    bit (a.sep t) i = true ↔ distinguishes t a.w (c.p i) (c.n i) := by
  have p := a.hp i
  have n := a.hn i
  by_cases ht : t = 0
  · simpa only [sep,distinguishes,ht,ite_true,bit,BitVec.getElem_and,BitVec.getElem_not,
      Bool.and_eq_true,Bool.not_eq_true'] using (and_congr (congrArg (· = true) p).to_iff
      (congrArg (· = false) n).to_iff)
  · simp only [sep,distinguishes,ht,ite_false,bit,BitVec.getElem_xor]
    change (bit a.p i ^^ bit a.n i) = true ↔ bit a.w (c.p i) ≠ bit a.w (c.n i)
    rw [p,n]
    cases bit a.w (c.p i) <;> cases bit a.w (c.n i) <;> decide
end Wire

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def wires {x : Word} {c : Charts x} (v : List (Wire c)) : Finset Word :=
  (v.map Wire.w).toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cover {x : Word} {c : Charts x} (t : ℕ) : List (Wire c) → Word
  | [] => 0
  | w :: v => w.sep t ||| cover t v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cover_bit {x : Word} {c : Charts x} (t : ℕ) (v : List (Wire c)) (i : Fin 512) :
    bit (cover t v) i = true ↔ ∃ w ∈ v, distinguishes t w.w (c.p i) (c.n i) := by
  induction v with
  | nil => simp only [cover,bit_zero,Bool.false_eq_true,List.not_mem_nil,false_and]; tauto
  | cons a v ih =>
    change bit (combine true _ _) i = true ↔ _
    simp only [bit_bin,ite_true,Bool.or_eq_true,Wire.sep_bit,ih,List.mem_cons,
      exists_eq_or_imp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma distinguish_more {a : Word} {i j : Fin 512} {u t : ℕ}
    (h : distinguishes u a i j) (hu : u ≤ t) : distinguishes t a i j := by
  cases t with
  | zero => simpa [show u=0 by omega] using h
  | succ t =>
    have hp := distinguish_old h
    simpa only [distinguishes,Nat.succ_ne_zero,ite_false] using hp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cover_live {x : Word} (c : Charts x) {b j t} (v : List (Wire c))
    (h : Live x b j (wires v)) (ht : j ≤ t) : cover t v = top := by
  apply BitVec.eq_of_getElem_eq; intro k hk
  let i : Fin 512 := ⟨k,hk⟩
  change bit (cover t v) i = bit top i
  rw [bit_top,cover_bit]
  obtain ⟨a,ha,hd⟩ := distinguishes_live h (c.hp i) (c.hn i)
  obtain ⟨w, hw, hwa⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact ⟨w,hw,hwa ▸ distinguish_more hd ht⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Exact (x : Word) (b t : ℕ) (S : Finset Word) : Prop :=
  ∃ n ≤ b, ∃ j ≤ t, Live x n j S

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma exact_size {x b t S} (h : Exact x b t S) : S.card ≤ b+1 := by
  obtain ⟨n,hn,j,_,h⟩ := h
  exact (count_live h).trans (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma exact_cover {x : Word} (c : Charts x) {b t} (v : List (Wire c))
    (h : Exact x b t (wires v)) : cover t v = top := by
  obtain ⟨n,_,j,hj,h⟩ := h
  exact cover_live c v h hj

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
inductive Step {x : Word} (c : Charts x) where
  | flip (a : Wire c) (keep : Bool)
  | binary (d : Bool) (a b : Wire c) (keepA keepB : Bool)

namespace Step
variable {x : Word} {c : Charts x}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def out : Step c → Wire c
  | .flip a _ => a.flip
  | .binary d a b _ _ => a.binary d b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rest (s : Step c) (v : List (Wire c)) : List (Wire c) :=
  match s with
  | .flip a ka => v.filter (fun y => ka || y.w != a.w)
  | .binary _ a b ka kb =>
    v.filter (fun y => (ka || y.w != a.w) && (kb || y.w != b.w))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def after (s : Step c) (v : List (Wire c)) := s.out :: s.rest v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def budget (s : Step c) (b t : ℕ) :=
  match s with
  | .flip .. => (b,t-1)
  | .binary .. => (b-1,t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def all (b t : ℕ) (v : List (Wire c)) : List (Step c) :=
  v.flatMap fun a =>
    (if t=0 then [] else [Step.flip a false,Step.flip a true]) ++
    (if b=0 then [] else v.flatMap fun w =>
      if a.w.toNat < w.w.toNat then
        [false,true].flatMap fun d => [false,true].flatMap fun ka =>
          [false,true].map (fun kb => Step.binary d a w ka kb)
      else [])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mem_flip {a : Wire c} {b t : ℕ} {v : List (Wire c)} (ht : 0<t) (ha : a ∈ v)
    (ka : Bool) : Step.flip a ka ∈ all b t v := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_append_left _ ?_⟩
  cases ka <;> simp [show t≠0 by omega]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mem_binary {a w : Wire c} {b t : ℕ} {v : List (Wire c)} (hb : 0<b)
    (ha : a ∈ v) (hw : w ∈ v) (hlt : a.w.toNat < w.w.toNat) (d ka kb : Bool) :
    Step.binary d a w ka kb ∈ all b t v := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_append_right _ ?_⟩
  simp only [show b≠0 by omega,ite_false]
  apply List.mem_flatMap.mpr
  refine ⟨w,hw,?_⟩
  simp only [hlt,ite_true]
  apply List.mem_flatMap.mpr
  refine ⟨d,by cases d <;> simp,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨ka,by cases ka <;> simp,List.mem_map.mpr ⟨kb,by cases kb <;> simp,rfl⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mem_wires {v : List (Wire c)} {w : Word} : w ∈ wires v ↔ ∃ a ∈ v, a.w = w := by
  simp [wires]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma next_flip {a : Wire c} {v : List (Wire c)} {U : Finset Word}
    (hs : wires v = insert a.w U) :
    wires ((Step.flip a (decide (a.w ∈ U))).after v) = insert (~~~a.w) U := by
  ext z
  simp only [after,wires,List.map_cons,List.toFinset_cons,Finset.mem_insert]
  apply or_congr_right
  change z ∈ wires (v.filter _) ↔ z ∈ U
  rw [mem_wires]
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨hv,cond⟩ := List.mem_filter.mp hq
    have eq : q.w ∈ insert a.w U := hs ▸ (mem_wires.mpr ⟨q,hv,rfl⟩)
    rcases Finset.mem_insert.mp eq with he|h
    · simpa [he] using cond
    · exact h
  · intro hz
    have hv : z ∈ wires v := hs ▸ Finset.mem_insert_of_mem hz
    obtain ⟨q,hq,eq⟩ := mem_wires.mp hv
    refine ⟨q,List.mem_filter.mpr ⟨hq,?_⟩,eq⟩
    by_cases h : z=a.w
    · simp [←h,eq,hz]
    · simp [eq,h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma next_bin {a w : Wire c} {v : List (Wire c)} {U : Finset Word}
    (hs : wires v = insert a.w (insert w.w U)) :
    wires ((Step.binary d a w (decide (a.w ∈ U)) (decide (w.w ∈ U))).after v) =
      insert (combine d a.w w.w) U := by
  ext z
  simp only [after,wires,List.map_cons,List.toFinset_cons,Finset.mem_insert]
  apply or_congr_right
  change z ∈ wires (v.filter _) ↔ z ∈ U
  rw [mem_wires]
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨hv,cond⟩ := List.mem_filter.mp hq
    have eq : q.w ∈ insert a.w (insert w.w U) := hs ▸ (mem_wires.mpr ⟨q,hv,rfl⟩)
    obtain ⟨c1,c2⟩ := Bool.and_eq_true_iff.mp cond
    rcases Finset.mem_insert.mp eq with he|h
    · simpa [he] using c1
    rcases Finset.mem_insert.mp h with he|h
    · simpa [he] using c2
    · exact h
  · intro hz
    have hv : z ∈ wires v := hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
    obtain ⟨q,hq,eq⟩ := mem_wires.mp hv
    refine ⟨q,List.mem_filter.mpr ⟨hq,?_⟩,eq⟩
    apply Bool.and_eq_true_iff.mpr
    constructor
    · by_cases h : z=a.w
      · simp [←h,eq,hz]
      · simp [eq,h]
    · by_cases h : z=w.w
      · simp [←h,eq,hz]
      · simp [eq,h]
end Step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def eligible {x : Word} {c : Charts x} (v : List (Wire c)) (s : Step c) : Prop :=
  proper s.out.w ∧ s.out.w ∉ wires v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma descend {x : Word} (c : Charts x) (hx : proper x) {b t : ℕ} {v : List (Wire c)}
    (h : Exact x b t (wires v)) :
    x ∈ wires v ∨ ∃ s ∈ Step.all b t v, eligible v s ∧
      Exact x (s.budget b t).1 (s.budget b t).2 (wires (s.after v)) := by
  obtain ⟨n,hn,j,hj,h⟩ := h
  generalize hs : wires v = S at h
  cases h with
  | done =>
    left; simp
  | @unary nb nt U a pa fresh tail =>
    right
    have hv : a ∈ wires v := hs ▸ Finset.mem_insert_self ..
    obtain ⟨aw,hw,eq⟩ := Step.mem_wires.mp hv
    subst a
    let s := Step.flip aw (decide (aw.w ∈ U))
    refine ⟨s,Step.mem_flip (by omega) hw _,⟨tail.good hx _ (Finset.mem_insert_self ..),?_⟩,
      n,hn,nt,by change nt ≤ t-1; omega,?_⟩
    · change ~~~aw.w ∉ wires v
      rwa [hs]
    · change Live x n nt (wires ((Step.flip aw _).after _))
      rwa [Step.next_flip hs]
  | @binary nb nt U a w d pa pw ne fresh tail =>
    right
    have ha : a ∈ wires v := hs ▸ Finset.mem_insert_self ..
    have hw : w ∈ wires v := hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    obtain ⟨aw,ah,a_eq⟩ := Step.mem_wires.mp ha
    obtain ⟨ww,wh,w_eq⟩ := Step.mem_wires.mp hw
    subst a; subst w
    have ord : aw.w.toNat ≠ ww.w.toNat := fun e => ne (BitVec.eq_of_toNat_eq e)
    have mk (y z : Wire c) (hy : y ∈ v) (hz : z ∈ v) (hlt : y.w.toNat < z.w.toNat)
        (heads : wires v = insert y.w (insert z.w U))
        (fresh' : combine d y.w z.w ∉ wires v)
        (tail' : Live x nb j (insert (combine d y.w z.w) U)) :
        ∃ s ∈ Step.all b t v, eligible v s ∧
          Exact x (s.budget b t).1 (s.budget b t).2 (wires (s.after v)) := by
      let s := Step.binary d y z (decide (y.w ∈ U)) (decide (z.w ∈ U))
      refine ⟨s,Step.mem_binary (by omega) hy hz hlt ..,
        ⟨tail'.good hx _ (Finset.mem_insert_self ..), fresh'⟩,
        nb,by change nb ≤ b-1; omega,j,hj,?_⟩
      change Live x nb j (wires ((Step.binary d y z _ _).after _))
      rwa [Step.next_bin heads]
    rcases lt_or_gt_of_ne ord with hlt|hlt
    · exact mk aw ww ah wh hlt hs (hs ▸ fresh) tail
    · apply mk ww aw wh ah hlt
      · rwa [Finset.insert_comm]
      · rwa [comm,hs]
      · rwa [comm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Basis (x : Word) where
  mask : Word
  raw : List Word
  lo : ℕ
  proj : Projection
  zero : proj.q 0 = 0
  one : proj.q top = top
  refl (a b : Word) : a &&& mask = b &&& mask → proj.q a = proj.q b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Price (x : Word) where
  basis : Basis x
  spent : ℕ

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Basis.base {x : Word} (f : Basis x) := (f.raw.map f.proj.q).toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Price.Valid {x : Word} (f : Price x) (t : ℕ) (S : Finset Word) :=
  Guard f.basis.proj x S f.basis.base t f.basis.lo f.spent

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def maskedConst (m a : Word) : Bool := (a &&& m) == 0 || (a &&& m) == m

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def freeAt {x : Word} {c : Charts x} (f : Basis x) (v : List (Wire c)) (w : Word) : Bool :=
  maskedConst f.mask w || v.any (fun a => (w &&& f.mask) == (a.w &&& f.mask)) ||
    f.raw.any (fun a => (w &&& f.mask) == (a &&& f.mask))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma maskedConst_sound {x : Word} {f : Basis x} {a : Word}
    (h : maskedConst f.mask a = true) : ¬proper (f.proj.q a) := by
  rcases Bool.or_eq_true_iff.mp h with h|h
  · have eq := f.refl a 0 (by simpa using beq_iff_eq.mp h)
    rw [f.zero] at eq; exact fun hp => hp.1 eq
  · have eq := f.refl a top (by simpa only [top,BitVec.allOnes_and] using beq_iff_eq.mp h)
    rw [f.one] at eq; exact fun hp => hp.2 eq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma freeAt_sound {x : Word} {c : Charts x} {f : Basis x} {v : List (Wire c)} {w : Word}
    (h : freeAt f v w = true) :
    f.proj.q w ∈ available f.proj (wires v) f.base ∨ ¬proper (f.proj.q w) := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · exact Or.inr (maskedConst_sound h)
    · obtain ⟨a,ha,e⟩ := List.any_eq_true.mp h
      rw [f.refl w a.w (beq_iff_eq.mp e)]
      exact Or.inl (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Step.mem_wires.mpr ⟨a,ha,rfl⟩)))
  · obtain ⟨a,ha,e⟩ := List.any_eq_true.mp h
    rw [f.refl w a (beq_iff_eq.mp e)]
    exact Or.inl (Finset.mem_union_right _
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Price.advance {x : Word} {c : Charts x} (f : Price x) (v : List (Wire c)) (s : Step c) :
    Price x := match s with
  | .flip .. => f
  | .binary .. => ⟨f.basis,f.spent + (if freeAt f.basis v s.out.w then 0 else 1)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma Step.child_subset {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) :
    wires (s.after v) ⊆ insert s.out.w (wires v) := by
  intro a ha
  obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp ha
  rcases List.mem_cons.mp hw with rfl|hw
  · exact Finset.mem_insert_self ..
  · have h : w ∈ v := by cases s <;> exact List.mem_of_mem_filter hw
    exact Finset.mem_insert_of_mem (Step.mem_wires.mpr ⟨w,h,rfl⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma advance_flip {x : Word} {c : Charts x} {p : Price x} {a : Wire c}
    {v : List (Wire c)} {t : ℕ} (hv : p.Valid (t+1) (wires v)) (ha : a ∈ v) (ka : Bool) :
    (p.advance v (.flip a ka)).Valid t (wires ((Step.flip a ka).after v)) :=
  guard_unary hv (Step.mem_wires.mpr ⟨a,ha,rfl⟩) ((Step.flip a ka).child_subset v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma advance_bin {x : Word} {c : Charts x} {p : Price x} {a b : Wire c}
    {v : List (Wire c)} {t : ℕ} (hv : p.Valid t (wires v)) (ha : a ∈ v) (hb : b ∈ v)
    (d ka kb : Bool) :
    (p.advance v (.binary d a b ka kb)).Valid t (wires ((Step.binary d a b ka kb).after v)) := by
  let s := Step.binary d a b ka kb
  have hnext := guard_binary hv (Step.mem_wires.mpr ⟨a,ha,rfl⟩)
    (Step.mem_wires.mpr ⟨b,hb,rfl⟩) (s.child_subset v)
  have cost_le : cost p.basis.proj (wires v) p.basis.base s.out.w ≤
      (if freeAt p.basis v s.out.w then 0 else 1) := by
    cases h : freeAt p.basis v s.out.w
    · change cost _ _ _ _ ≤ 1
      unfold cost; split <;> omega
    · simp [cost,freeAt_sound h]
  refine ⟨hnext.1,fun k hk => ?_⟩
  exact (hnext.2 k hk).trans (Nat.add_le_add_left (Nat.add_le_add_left cost_le _) _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Step.Legal {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) (b t : ℕ) : Prop :=
  match s with
  | .flip a _ => a ∈ v ∧ 0<t
  | .binary _ a w _ _ => a ∈ v ∧ w ∈ v ∧ 0<b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma Step.all_legal {x : Word} {c : Charts x} {s : Step c} {v : List (Wire c)} {b t : ℕ}
    (h : s ∈ Step.all b t v) : s.Legal v b t := by
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hm with hu|hb
  · split at hu
    · contradiction
    rename_i ht
    rcases List.mem_cons.mp hu with rfl|hu
    · exact ⟨ha,by omega⟩
    · obtain rfl := List.mem_singleton.mp hu
      exact ⟨ha,by omega⟩
  · split at hb
    · contradiction
    rename_i hpos
    obtain ⟨w,hw,hm⟩ := List.mem_flatMap.mp hb
    split at hm
    · obtain ⟨d,_,h⟩ := List.mem_flatMap.mp hm
      obtain ⟨ka,_,h⟩ := List.mem_flatMap.mp h
      obtain ⟨kb,_,rfl⟩ := List.mem_map.mp h
      exact ⟨ha,hw,by omega⟩
    · contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma advance_valid {x : Word} {c : Charts x} {p : Price x} {s : Step c}
    {v : List (Wire c)} {b t : ℕ} (hv : p.Valid t (wires v)) (h : s.Legal v b t) :
    (p.advance v s).Valid (s.budget b t).2 (wires (s.after v)) := by
  cases s with
  | flip a ka =>
    obtain ⟨hw,ht⟩ := h
    cases t with
    | zero => omega
    | succ t => exact advance_flip hv hw ka
  | binary d a w ka kb => exact advance_bin hv h.1 h.2.1 d ka kb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def loss {x : Word} {c : Charts x} (f : Basis x) (v : List (Wire c)) :=
  ((v.map Wire.w).filter (maskedConst f.mask)).length

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma loss_le {x : Word} {c : Charts x} (f : Basis x) (v : List (Wire c))
    (nd : (v.map Wire.w).Nodup) : loss f v ≤ constants f.proj (wires v) := by
  rw [loss,←List.toFinset_card_of_nodup (nd.filter _)]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨hm,hc⟩ := List.mem_filter.mp (List.mem_toFinset.mp ha)
  exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm,maskedConst_sound hc⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Price.cuts {x : Word} {c : Charts x} (p : Price x) (b : ℕ) (v : List (Wire c)) : Bool :=
  decide (b+p.spent < p.basis.lo+loss p.basis v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cut_sound {x : Word} {c : Charts x} {p : Price x} {b t : ℕ} {v : List (Wire c)}
    (nd : (v.map Wire.w).Nodup) (valid : p.Valid t (wires v)) (cut : p.cuts b v = true) :
    ¬ Exact x b t (wires v) := by
  rintro ⟨n,hn,j,hj,h⟩
  have g : Guard p.basis.proj x (wires v) p.basis.base j p.basis.lo p.spent :=
    ⟨valid.1,fun k hk => valid.2 k (weaken hk le_rfl hj (by rfl))⟩
  have e := guard_bound g h
  have l := loss_le p.basis v nd
  have q := of_decide_eq_true cut
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma Step.child_nd {x : Word} {c : Charts x} {v : List (Wire c)} (s : Step c)
    (nd : (v.map Wire.w).Nodup) (hf : s.out.w ∉ wires v) :
    ((s.after v).map Wire.w).Nodup := by
  simp only [Step.after,List.map_cons,List.nodup_cons]
  have sub : List.Sublist (s.rest v) v := by cases s <;> exact List.filter_sublist
  exact ⟨fun hm => hf (List.mem_toFinset.mpr ((sub.map Wire.w).subset hm)),
    nd.sublist (sub.map Wire.w)⟩

abbrev Key := List ℕ

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
inductive Cache where
  | empty
  | bin (hash : ℕ) (bucket : List Key) (left right : Cache)

namespace Cache
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
instance : EmptyCollection Cache := ⟨empty⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hashKey (k : Key) := k.foldl (fun h n => Nat.mod (h*101+n) 65521) 7919
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def find (h : ℕ) : Cache → List Key
  | .empty => []
  | .bin n keys l r => if h=n then keys else if h<n then find h l else find h r
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def put (h : ℕ) (k : Key) : Cache → Cache
  | .empty => .bin h [k] .empty .empty
  | .bin n keys l r => if h=n then .bin n (k::keys) l r
      else if h<n then .bin n keys (put h k l) r else .bin n keys l (put h k r)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def contains (db : Cache) (k : Key) := (find (hashKey k) db).contains k
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def insert (db : Cache) (k : Key) := put (hashKey k) k db
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Has (k : Key) : Cache → Prop
  | .empty => False
  | .bin _ keys l r => k ∈ keys ∨ Has k l ∨ Has k r
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
instance : Membership Key Cache where mem db k := Has k db
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma find_mem {k : Key} (h : ℕ) (db : Cache) (m : k ∈ find h db) : k ∈ db := by
  induction db with
  | empty => contradiction
  | bin n keys l r il ir =>
    change k ∈ keys ∨ _ ∨ _
    simp only [find] at m
    split at m
    · exact Or.inl m
    split at m
    · exact Or.inr (Or.inl (il m))
    · exact Or.inr (Or.inr (ir m))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma contains_mem {k : Key} {db : Cache} (h : db.contains k) : k ∈ db :=
  find_mem _ _ (List.contains_iff_mem.mp h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mem_put {k v : Key} (h : ℕ) (db : Cache) (m : v ∈ put h k db) : v=k ∨ v ∈ db := by
  induction db with
  | empty =>
    change v ∈ [k] ∨ False ∨ False at m
    exact Or.inl (by simpa using m)
  | bin n keys l r il ir =>
    simp only [put] at m
    split at m
    · change v ∈ k::keys ∨ Has v l ∨ Has v r at m
      change v=k ∨ v∈keys ∨ Has v l ∨ Has v r
      simp only [List.mem_cons] at m
      tauto
    split at m
    · change v ∈ keys ∨ Has v (put h k l) ∨ Has v r at m
      change v=k ∨ v∈keys ∨ Has v l ∨ Has v r
      rcases m with a|m|a
      · tauto
      · rcases il m with e|e <;> tauto
      · tauto
    · change v ∈ keys ∨ Has v l ∨ Has v (put h k r) at m
      change v=k ∨ v∈keys ∨ Has v l ∨ Has v r
      rcases m with a|a|m
      · tauto
      · tauto
      · rcases ir m with e|e <;> tauto
end Cache

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sortNats : List ℕ → List ℕ
  | [] => []
  | a::xs => ordered a (sortNats xs)
where ordered (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b::ys => if a≤b then a::b::ys else b::ordered a ys

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sort_perm (x : List ℕ) : (sortNats x).Perm x := by
  have helper (a : ℕ) (xs : List ℕ) : (sortNats.ordered a xs).Perm (a::xs) := by
    induction xs with
    | nil => exact .refl _
    | cons b ys ih =>
      simp only [sortNats.ordered]
      split
      · exact .refl _
      · exact (List.Perm.cons b ih).trans (List.Perm.swap ..)
  induction x with
  | nil => exact .refl _
  | cons a xs ih => exact (helper a _).trans (List.Perm.cons a ih)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sorted {x : Word} {c : Charts x} (v : List (Wire c)) : List ℕ :=
  sortNats (v.map fun a => a.w.toNat)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def key {x : Word} {c : Charts x} (b t : ℕ) (v : List (Wire c)) : Key :=
  b :: t :: sorted v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Safe (x : Word) (db : Cache) :=
  ∀ b t ws, b::t::ws ∈ db → ¬ Exact x b t (ws.map (BitVec.ofNat 512)).toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma key_set {x : Word} {c : Charts x} (v : List (Wire c)) :
    ((sorted v).map (BitVec.ofNat 512)).toFinset = wires v := by
  have perm := (sort_perm (v.map (fun a => a.w.toNat))).map
    (BitVec.ofNat 512)
  ext a
  rw [List.mem_toFinset]
  unfold sorted
  rw [perm.mem_iff]
  simp [wires,Function.comp_def]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma safe_insert {x : Word} {c : Charts x} {b t : ℕ} {v : List (Wire c)} {db : Cache}
    (hd : Safe x db) (h : ¬Exact x b t (wires v)) : Safe x (db.insert (key b t v)) := by
  intro b' t' ws hk
  rcases Cache.mem_put _ _ hk with e|hm
  · have eq : key b t v = b'::t'::ws := e.symm
    obtain ⟨rfl,rfl,rfl⟩ := (by simpa only [key,List.cons.injEq] using eq :
      b=b' ∧ t=t' ∧ sorted v=ws)
    rw [key_set]; exact h
  · exact hd _ _ _ hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def batch {α : Type} (run : α → Cache → Option Cache) : List α → Cache → Option Cache
  | [], db => some db
  | a::xs, db => (run a db).bind (batch run xs)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma batch_sound {α : Type} {x : Word} {Q : α → Prop} {run : α → Cache → Option Cache}
    (xs : List α) {db out : Cache} (legal : ∀ a ∈ xs, ∀ d e, Safe x d → run a d = some e →
      Safe x e ∧ Q a) (sd : Safe x db) (done : batch run xs db = some out) :
      Safe x out ∧ ∀ a ∈ xs, Q a := by
  induction xs generalizing db with
  | nil => exact ⟨(Option.some.inj done) ▸ sd,by simp⟩
  | cons a xs ih =>
    simp only [batch] at done
    cases ha : run a db with
    | none => simp [ha] at done
    | some e =>
      have hh := legal a (by simp) db e sd ha
      have hr := ih (fun z hz => legal z (by simp [hz])) hh.1 (by simpa [ha] using done)
      exact ⟨hr.1,fun z hz => (List.mem_cons.mp hz).elim (fun eq => eq ▸ hh.2) (hr.2 z)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def isEligible {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) : Bool :=
  s.out.w != 0 && s.out.w != top && !(v.any fun a => a.w == s.out.w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma eligible_iff {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) :
    isEligible s v = true ↔ eligible v s := by
  simp only [isEligible,eligible,proper,Bool.and_eq_true,bne_iff_ne,Bool.not_eq_true',
    List.any_eq_false,beq_iff_eq,Step.mem_wires,not_exists,not_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def immediate {x : Word} {c : Charts x} (b t : ℕ) (v : List (Wire c)) (ps : List (Price x)) :
    Bool := decide (b+1 < v.length) || cover t v != top || ps.any (fun p => p.cuts b v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma immediate_sound {x : Word} {c : Charts x} {b t} {v : List (Wire c)} {ps}
    (nd : (v.map Wire.w).Nodup) (valid : ∀ p ∈ ps, p.Valid t (wires v))
    (h : immediate b t v ps = true) : ¬Exact x b t (wires v) := by
  intro he
  rcases Bool.or_eq_true_iff.mp h with h|h
  · rcases Bool.or_eq_true_iff.mp h with hs|hc
    · have hsz := exact_size he
      have ec := List.toFinset_card_of_nodup nd
      rw [List.length_map] at ec
      change (v.map Wire.w).toFinset.card ≤ b+1 at hsz
      have hh := of_decide_eq_true hs
      omega
    · simp [exact_cover c v he] at hc
  · obtain ⟨p,hp,cut⟩ := List.any_eq_true.mp h
    exact cut_sound nd (valid p hp) cut he

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def close {x : Word} (c : Charts x) : ℕ → ℕ → ℕ → List (Wire c) → List (Price x) →
    Cache → Option Cache
  | 0,_,_,_,_,_ => none
  | fuel+1,b,t,v,ps,db =>
    if immediate b t v ps then some db
    else
      let k := key b t v
      if db.contains k then some db
      else if v.any (fun a => a.w == x) then none
      else
        let act := fun s e =>
          if isEligible s v then
            close c fuel (s.budget b t).1 (s.budget b t).2 (s.after v)
              (ps.map (fun p => p.advance v s)) e
          else some e
        (batch act (Step.all b t v) db).map (fun e => e.insert k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma close_sound {x : Word} (c : Charts x) (hx : proper x) (fuel : ℕ) {b t}
    {v : List (Wire c)} {ps} {db out : Cache}
    (nd : (v.map Wire.w).Nodup) (valid : ∀ p ∈ ps, p.Valid t (wires v)) (safe : Safe x db)
    (done : close c fuel b t v ps db = some out) : Safe x out ∧ ¬Exact x b t (wires v) := by
  induction fuel generalizing b t v ps db out with
  | zero => contradiction
  | succ fuel ih =>
    simp only [close] at done
    split at done
    · rename_i h
      obtain rfl := Option.some.inj done
      exact ⟨safe, immediate_sound nd valid h⟩
    split at done
    · rename_i h
      obtain rfl := Option.some.inj done
      have e := safe b t (sorted v) (Cache.contains_mem h)
      rw [key_set] at e; exact ⟨safe,e⟩
    split at done
    · contradiction
    rename_i nx
    have nox : x ∉ wires v := by
      rintro hm
      obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      exact nx (List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩)
    let act := fun (s : Step c) (e : Cache) =>
      if isEligible s v then
        close c fuel (s.budget b t).1 (s.budget b t).2 (s.after v)
          (ps.map (fun p => p.advance v s)) e
      else some e
    change (batch act (Step.all b t v) db).map (fun e => e.insert (key b t v)) = some out at done
    cases hb : batch act (Step.all b t v) db with
    | none => simp [hb] at done
    | some e =>
      have outEq : e.insert (key b t v) = out := by simpa only [hb,Option.map_some,
        Option.some.injEq] using done
      obtain ⟨se,branches⟩ := batch_sound (Q:=fun s => eligible v s →
        ¬Exact x (s.budget b t).1 (s.budget b t).2 (wires (s.after v)))
        (Step.all b t v) (run:=act) (db:=db) (out:=e) (by
          intro s hs d o sd sol
          by_cases he : isEligible s v = true
          · have h := (eligible_iff s v).1 he
            have sol' : close c fuel (s.budget b t).1 (s.budget b t).2 (s.after v) (ps.map (fun p => p.advance v s)) d = some o := by simpa [act,he] using sol
            have h' := ih (s.child_nd nd h.2) (by
              intro p hp
              obtain ⟨orig,hm,rfl⟩ := List.mem_map.mp hp
              exact advance_valid (valid _ hm) (Step.all_legal hs)) sd sol'
            exact ⟨h'.1,fun _ => h'.2⟩
          · have outEq : d=o := by simpa [act,he] using sol
            exact ⟨outEq ▸ sd,fun el => False.elim (he ((eligible_iff s v).2 el))⟩) safe hb
      have impossible : ¬Exact x b t (wires v) := by
        intro hypothetical
        rcases (descend c hx hypothetical).resolve_left nox with ⟨s,hs,el,h⟩
        exact branches s hs el h
      exact ⟨outEq ▸ safe_insert se impossible,impossible⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma price_subset {x : Word} {p : Price x} {t : ℕ} {S T : Finset Word}
    (h : p.Valid t S) (sub : T ⊆ S) : p.Valid t T := by
  refine ⟨h.1, fun b hb => h.2 b (weaken hb le_rfl le_rfl ?_)⟩
  exact Finset.union_subset_union_left (Finset.image_subset_image sub)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def validate {x : Word} (c : Charts x) (b t : ℕ) (v : List (Wire c)) (ps : List (Price x)) :=
  (batch (fun u db => close c (b+t+2) b t u ps db) v.sublists ∅).isSome

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verified {x : Word} (c : Charts x) (hx : proper x) {b t} {v : List (Wire c)} {ps}
    (nd : (v.map Wire.w).Nodup) (valid : ∀ p ∈ ps, p.Valid t (wires v))
    (check : validate c b t v ps = true) : ¬Feasible x b t (wires v) := by
  obtain ⟨out,done⟩ := Option.isSome_iff_exists.mp check
  have sf : Safe x ∅ := by intro b' t' ws h; exact False.elim h
  obtain ⟨_,no⟩ := batch_sound (Q:=fun u => ¬Exact x b t (wires u)) v.sublists
    (run:=fun u db => close c (b+t+2) b t u ps db) (db:=∅) (out:=out) (by
      intro u hu d e sd hh
      have sub := List.mem_sublists.mp hu
      have incl : wires u ⊆ wires v := by
        intro a ha; exact List.mem_toFinset.mpr ((sub.map Wire.w).subset (List.mem_toFinset.mp ha))
      exact close_sound c hx _ (nd.sublist (sub.map Wire.w))
        (fun p hp => price_subset (valid p hp) incl) sd hh) sf done
  rintro ⟨i,hi,j,hj,T,sub,hL⟩
  let u := v.filter (fun a => decide (a.w ∈ T))
  have eq : wires u = T := by
    ext a; rw [Step.mem_wires]
    constructor
    · rintro ⟨w,hw,rfl⟩; exact of_decide_eq_true (List.mem_filter.mp hw).2
    · intro ha
      obtain ⟨w,hw,e⟩ := Step.mem_wires.mp (sub ha)
      exact ⟨w,List.mem_filter.mpr ⟨hw,by simpa [e] using ha⟩,e⟩
  apply no u (List.mem_sublists.mpr List.filter_sublist)
  rw [eq]; exact ⟨i,hi,j,hj,hL⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def unpack (code : ℕ) (i : Fin 512) : Fin 512 := Fin.ofNat 512 (code >>> (9*i.val))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def basisFor (x : Word) (m : Word) (raw : List Word) (lo : ℕ) (row : Fin 512 → Fin 512)
    (good : ∀ i, bit m (row i) = true) : Basis x where
  mask := m
  raw := raw
  lo := lo
  proj := faceQ row
  zero := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    change bit ((faceQ row).q 0) ⟨r,hr⟩ = bit 0 ⟨r,hr⟩
    rw [q_bit,bit_zero,bit_zero]
  one := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    change bit ((faceQ row).q top) ⟨r,hr⟩ = bit top ⟨r,hr⟩
    rw [q_bit,bit_top,bit_top]
  refl a b e := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    let i : Fin 512 := ⟨r,hr⟩
    change bit ((faceQ row).q a) i = bit ((faceQ row).q b) i
    rw [q_bit,q_bit]
    have he := congrArg (fun w => bit w (row i)) e
    change bit (combine false a m) (row i) = bit (combine false b m) (row i) at he
    simpa only [bit_bin,Bool.false_eq_true,ite_false,good,Bool.and_true] using he

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initial_price {x y : Word} {f : Basis x} {S child : Finset Word}
    (hy : proper y) (forbidden : ¬Feasible y (f.lo-1) 1 child) (ex : f.proj.q x = y)
    (inc : available f.proj S f.base ⊆ insert 0 child) :
    (Price.mk f 0).Valid 1 S := by
  refine ⟨ex ▸ hy, ?_⟩
  intro b h
  by_contra fail
  have bl : b ≤ f.lo-1 := by change ¬f.lo ≤ b+0 at fail; omega
  rw [ex] at h
  apply forbidden
  exact ignore hy (weaken h bl le_rfl inc) (Or.inr fun hp => hp.1 rfl)

-- Replay short gate sequences and certify the search in bounded-depth pieces.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def vanished (keep : Bool) (a : Word) : Finset Word := if keep then ∅ else {a}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def debit (keep : Bool) := if keep then 0 else 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma vanishes (keep : Bool) (a : Word) : (vanished keep a).card = debit keep := by
  cases keep <;> simp [vanished,debit]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Step.discard {x : Word} {c : Charts x} : Step c → Finset Word
  | .flip a ka => vanished ka a.w
  | .binary _ a w ka kb => vanished ka a.w ∪ vanished kb w.w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Step.drops {x : Word} {c : Charts x} : Step c → ℕ
  | .flip _ ka => debit ka
  | .binary _ _ _ ka kb => debit ka + debit kb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma discard_le {x : Word} {c : Charts x} (s : Step c) : s.discard.card ≤ s.drops := by
  cases s with
  | flip a ka => exact (vanishes ka a.w).le
  | binary d a b ka kb =>
    exact (Finset.card_union_le ..).trans (by simp only [Step.drops,vanishes,le_refl])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rest_inclusion {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) :
    wires v ⊆ wires (s.rest v) ∪ s.discard := by
  intro a ha
  obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp ha
  by_cases keepW : w ∈ s.rest v
  · exact Finset.mem_union_left _ (Step.mem_wires.mpr ⟨w,keepW,rfl⟩)
  · apply Finset.mem_union_right
    cases s with
    | flip a ka =>
      cases ka <;> simp_all [Step.discard,Step.rest,vanished,List.mem_filter]
    | binary d a b ka kb =>
      cases ka <;> cases kb <;> simp_all [Step.discard,Step.rest,vanished,List.mem_filter]
      all_goals tauto

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fits_step {x : Word} {c : Charts x} {b t} (v : List (Wire c)) (s : Step c)
    (nd : (v.map Wire.w).Nodup) (el : eligible v s) (h : Exact x (s.budget b t).1
      (s.budget b t).2 (wires (s.after v))) :
    v.length+1 ≤ (s.budget b t).1+1+s.drops := by
  have le₁ := Finset.card_le_card (rest_inclusion s v)
  have le₂ := Finset.card_union_le (wires (s.rest v)) s.discard
  have le₃ := discard_le s
  have le₄ := exact_size h
  have eq : (wires v).card = v.length := by simpa [wires] using List.toFinset_card_of_nodup nd
  have fresh : s.out.w ∉ wires (s.rest v) := by
    intro hm
    obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
    have mem : w ∈ v := by cases s <;> exact List.mem_of_mem_filter hw
    exact el.2 (Step.mem_wires.mpr ⟨w,mem,e⟩)
  have ee : (wires (s.after v)).card = (wires (s.rest v)).card + 1 := by
    simpa only [wires,Step.after,List.map_cons,List.toFinset_cons] using
      Finset.card_insert_of_notMem fresh
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Step.anyBad {x : Word} {c : Charts x} (b t : ℕ) (v : List (Wire c)) (test : Step c → Bool) :=
  v.all (fun a =>
    ((t==0) || (test (.flip a false) && test (.flip a true))) &&
    ((b==0) || v.all (fun w =>
      !(decide (a.w.toNat < w.w.toNat)) ||
      [false,true].all (fun d => [false,true].all (fun ka =>
        test (.binary d a w ka false) && test (.binary d a w ka true))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma checked_steps {x : Word} {c : Charts x} {b t} {v : List (Wire c)} {test : Step c → Bool}
    (h : Step.anyBad b t v test=true) {s} (hs : s ∈ Step.all b t v) : test s=true := by
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hs
  have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)
  rcases List.mem_append.mp hm with hu|hb
  · split at hu
    · contradiction
    rename_i ht
    have q := Bool.and_eq_true_iff.mp ((Bool.or_eq_true_iff.mp hh.1).resolve_left
      (by simpa only [beq_iff_eq] using ht))
    rcases List.mem_cons.mp hu with rfl|hu
    · exact q.1
    · obtain rfl := List.mem_singleton.mp hu; exact q.2
  · split at hb
    · contradiction
    rename_i hbPos
    have q := (Bool.or_eq_true_iff.mp hh.2).resolve_left (by simpa only [beq_iff_eq] using hbPos)
    obtain ⟨w,hw,hm⟩ := List.mem_flatMap.mp hb
    split at hm
    · rename_i lt
      have gate := (Bool.or_eq_true_iff.mp (List.all_eq_true.mp q w hw)).resolve_left (by simp [lt])
      obtain ⟨d,hd,h⟩ := List.mem_flatMap.mp hm
      obtain ⟨ka,hka,h⟩ := List.mem_flatMap.mp h
      obtain ⟨kb,hkb,rfl⟩ := List.mem_map.mp h
      have both := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp gate d hd) ka hka)
      cases kb
      · exact both.1
      · exact both.2
    · contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Frame {x : Word} (c : Charts x) where
  b : ℕ
  t : ℕ
  v : List (Wire c)
  ps : List (Price x)

namespace Frame
variable {x : Word} {c : Charts x}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Valid (f : Frame c) := (f.v.map Wire.w).Nodup ∧ ∀ p ∈ f.ps, p.Valid f.t (wires f.v)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def No (f : Frame c) := ¬Exact x f.b f.t (wires f.v)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def code (f : Frame c) := key f.b f.t f.v
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def child (f : Frame c) (s : Step c) : Frame c :=
  ⟨(s.budget f.b f.t).1,(s.budget f.b f.t).2,s.after f.v,f.ps.map (fun p => p.advance f.v s)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma child_valid {f : Frame c} (h : f.Valid) {s} (ok : eligible f.v s)
    (legal : s.Legal f.v f.b f.t) : (f.child s).Valid := by
  refine ⟨s.child_nd h.1 ok.2,?_⟩
  intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact advance_valid (h.2 q hq) legal

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma transfer {f g : Frame c} (eq : f.code = g.code) (h : f.No) : g.No := by
  obtain ⟨b,t,s⟩ := (by simpa only [code,key,List.cons.injEq] using eq :
    f.b=g.b ∧ f.t=g.t ∧ sorted f.v=sorted g.v)
  have e : wires f.v=wires g.v := by rw [←key_set f.v,←key_set g.v,s]
  unfold No at *
  rwa [←b,←t,←e]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def decoded (f : Frame c) (j : ℕ) : Option (Step c) :=
  if j < 32 then
    if f.t = 0 then none else
      (f.v[j/2]?).map (fun a => .flip a (Nat.mod j 2 == 1))
  else if f.b = 0 then none else
    let i := j-32
    (f.v[i/128]?).bind fun a =>
      (f.v[Nat.mod (i/8) 16]?).map fun w => .binary (Nat.mod (i/4) 2 == 1) a w
        (Nat.mod (i/2) 2 == 1) (Nat.mod i 2 == 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma decode_legal {f : Frame c} {j : ℕ} {s : Step c} (h : f.decoded j = some s) :
    s.Legal f.v f.b f.t := by
  unfold decoded at h
  split at h
  · split at h
    · contradiction
    rename_i ht
    cases e : f.v[j/2]? with
    | none => simp [e] at h
    | some a =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst s; exact ⟨List.mem_of_getElem? e,by omega⟩
  · split at h
    · contradiction
    rename_i hb
    let i := j-32
    change ((f.v[i/128]?).bind _)=some s at h
    cases e : f.v[i/128]? with
    | none => simp [e] at h
    | some a =>
      simp only [e,Option.bind_some] at h
      cases ew : f.v[Nat.mod (i/8) 16]? with
      | none => simp [i] at ew; simp [ew] at h
      | some w =>
        change Option.map _ (f.v[Nat.mod (i/8) 16]?) = some s at h
        simp only [ew,Option.map_some,Option.some.injEq] at h
        subst s; exact ⟨List.mem_of_getElem? e,List.mem_of_getElem? ew,by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def jump (f : Frame c) (j : ℕ) : Option (Frame c) :=
  (f.decoded j).bind (fun s => if isEligible s f.v then some (f.child s) else none)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma jump_valid {f g : Frame c} {j : ℕ} (h : f.Valid) (eq : f.jump j=some g) : g.Valid := by
  unfold jump at eq
  cases e : f.decoded j with
  | none => simp [e] at eq
  | some s =>
    simp only [e,Option.bind_some] at eq
    split at eq
    · rename_i eligibleS
      obtain rfl := Option.some.inj eq
      exact child_valid h ((eligible_iff ..).1 eligibleS) (decode_legal e)
    · contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def replay (f : Frame c) : ℕ → ℕ → Option (Frame c)
  | 0,_ => some f
  | d+1,tape => (f.replay d (tape / 4096)).bind fun g => g.jump (Nat.mod tape 4096-1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma replay_valid {f g : Frame c} {d tape : ℕ} (h : f.Valid)
    (eq : f.replay d tape = some g) : g.Valid := by
  induction d generalizing tape g with
  | zero => exact (Option.some.inj eq) ▸ h
  | succ d ih =>
    unfold replay at eq
    cases e : f.replay d (tape/4096) with
    | none => simp [e] at eq
    | some g' =>
      exact jump_valid (ih e) (by simpa only [e,Option.bind_some] using eq)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def check (known : Frame c → Bool) : ℕ → Frame c → Bool
  | 0,f => immediate f.b f.t f.v f.ps || known f
  | d+1,f =>
    immediate f.b f.t f.v f.ps ||
      (!(f.v.any (fun a => a.w == x)) &&
        Step.anyBad f.b f.t f.v (fun s =>
          decide ((s.budget f.b f.t).1+1+s.drops < f.v.length+1) || !(isEligible s f.v) || check known d (f.child s)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma check_sound (known : Frame c → Bool) (good : ∀ f, known f = true → f.No)
    (hx : proper x) (d : ℕ) {f : Frame c} (v : f.Valid) (h : check known d f=true) : f.No := by
  induction d generalizing f with
  | zero =>
    rcases Bool.or_eq_true_iff.mp h with hi|hk
    · exact immediate_sound v.1 v.2 hi
    · exact good f hk
  | succ d ih =>
    rcases Bool.or_eq_true_iff.mp h with hi|hs
    · exact immediate_sound v.1 v.2 hi
    obtain ⟨no,all⟩ := Bool.and_eq_true_iff.mp hs
    intro hex
    rcases descend c hx hex with hm | ⟨s,hs,el,ht⟩
    · obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      have yes : f.v.any (fun a => a.w == x) = true := List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩
      simp [yes] at no
    · have chk := checked_steps all hs
      have fits := fits_step f.v s v.1 el ht
      simp only [show ¬ ((s.budget f.b f.t).1+1+s.drops < f.v.length+1) by omega,
        decide_false,Bool.false_or,(eligible_iff ..).2 el,Bool.not_true] at chk
      exact ih (child_valid v el (Step.all_legal hs)) chk ht
end Frame

abbrev Table := Array ℕ

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lowerIndex (a : Table) (h : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,l,_ => l
  | fuel+1,l,r =>
    if l<r then
      let m := (l+r)/2
      if Nat.mod a[m]! 65521 < h then lowerIndex a h fuel (m+1) r
        else lowerIndex a h fuel l m
    else l

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def TableSound {x : Word} {c : Charts x} (root : Frame c) (depth : ℕ) (a : Table) :=
  ∀ (j w : ℕ), a[j]?=some w → ∀ f, root.replay depth (w/65521) = some f → f.No

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hitRow {x : Word} {c : Charts x} (root : Frame c) (depth h : ℕ) (k : Key) : Option ℕ → Bool
  | none => false
  | some w =>
    Nat.mod w 65521 == h && (root.replay depth (w/65521)).any (fun g => g.code == k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lookup {x : Word} {c : Charts x} (root : Frame c) (depth : ℕ) (a : Table) (f : Frame c) :=
  let k := f.code
  let h := Cache.hashKey k
  let j := lowerIndex a h 20 0 a.size
  [0,1,2,3,4,5].any (fun n => hitRow root depth h k (a[j+n]?))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma lookup_sound {x : Word} {c : Charts x} {root : Frame c} {depth} {a : Table}
    (sound : TableSound root depth a) (f : Frame c) (ok : lookup root depth a f = true) :
    f.No := by
  let k := f.code
  let h := Cache.hashKey k
  let j := lowerIndex a h 20 0 a.size
  obtain ⟨n,_,eh⟩ := List.any_eq_true.mp ok
  change hitRow root depth h k (a[j+n]?) = true at eh
  cases e : a[j+n]? with
  | none => simp [e,hitRow] at eh
  | some w =>
    have pair := Bool.and_eq_true_iff.mp (by simpa only [e,hitRow] using eh :
      Nat.mod w 65521 == h && (root.replay depth (w/65521)).any (fun g => g.code == k))
    cases eq : root.replay depth (w/65521) with
    | none => simp [eq] at pair
    | some g =>
      have hkey : g.code=k := by simpa [eq] using pair.2
      exact Frame.transfer hkey (sound (j+n) w e g eq)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def tableRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (a : Table)
    (known : Frame c → Bool) (hops j : ℕ) :=
  (a[j]?).all (fun w => (root.replay d (w/65521)).all (Frame.check known hops))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Span (p : ℕ → Bool) (lo hi : ℕ) := ∀ j, lo ≤ j → j < hi → p j=true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sampleSpan (p : ℕ → Bool) (lo n : ℕ) := (List.range n).all (fun i => p (lo+i))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma checked_span {p : ℕ → Bool} {lo n : ℕ} (h : sampleSpan p lo n = true) : Span p lo (lo+n) := by
  intro j hj htop
  have q := List.all_eq_true.mp h (j-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le hj] using q
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma join_span {p : ℕ → Bool} {lo mid hi : ℕ} (h : Span p lo mid) (k : Span p mid hi) :
    Span p lo hi := by
  intro j hj ht
  by_cases e : j < mid
  · exact h j hj e
  · exact k j (by omega) ht
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma certified_table {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    (d : ℕ) (a : Table) {known : Frame c → Bool} (sk : ∀ f, known f=true → f.No)
    (hops : ℕ) (h : Span (tableRow root d a known hops) 0 a.size) : TableSound root d a := by
  intro j w ew f ef
  have hj := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
  have e : Frame.check known hops f=true := by simpa only [tableRow,ew,Option.all_some,ef] using hj
  exact Frame.check_sound known sk hx hops (Frame.replay_valid vr ef) e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def checkSubsets {x : Word} {c : Charts x} (root : Frame c) (known : Frame c → Bool) (hops : ℕ) :=
  root.v.sublists.all (fun u => Frame.check known hops {root with v:=u})

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma checked_root {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    {known : Frame c → Bool} (sk : ∀ f, known f=true → f.No)
    (hops : ℕ) (ok : checkSubsets root known hops=true) :
    ¬Feasible x root.b root.t (wires root.v) := by
  rintro ⟨i,hi,j,hj,T,sub,hL⟩
  let u := root.v.filter (fun a => decide (a.w ∈ T))
  have eq : wires u=T := by
    ext a; rw [Step.mem_wires]
    constructor
    · rintro ⟨w,hw,rfl⟩; exact of_decide_eq_true (List.mem_filter.mp hw).2
    · intro ha; obtain ⟨w,hw,e⟩ := Step.mem_wires.mp (sub ha)
      exact ⟨w,List.mem_filter.mpr ⟨hw,by simpa [e] using ha⟩,e⟩
  have hchk := List.all_eq_true.mp ok u (List.mem_sublists.mpr List.filter_sublist)
  have q : ({root with v:=u} : Frame c).Valid := ⟨vr.1.sublist (List.filter_sublist.map _), fun p hp =>
    price_subset (vr.2 p hp) (eq ▸ sub)⟩
  have no := Frame.check_sound known sk hx hops q hchk
  apply no
  change Exact x root.b root.t (wires u); rw [eq]
  exact ⟨i,hi,j,hj,hL⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma check_block {p : ℕ → Bool} {lo hi : ℕ} (h : sampleSpan p lo (hi-lo)=true) :
    Span p lo hi := by
  intro j hj htop
  exact checked_span h j hj (by omega)

-- Share positive and negative sample masks between related gate choices.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def keepList {α : Type} (k : Bool) (a : α) := if k then [a] else []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def addSep (k : Bool) (a r : Word) := if k then a ||| r else r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cover_keep {x : Word} {c : Charts x} (t : ℕ) (a : Wire c) (k : Bool)
    (tail : List (Wire c)) :
    cover t (keepList k a ++ tail)=addSep k (a.sep t) (cover t tail) := by
  cases k <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma preserve_cover {x : Word} {c : Charts x} {b t} {S : Finset Word} (v : List (Wire c))
    (h : Exact x b t S) (sub : S ⊆ wires v) : cover t v=top := by
  obtain ⟨n,_,j,hj,h⟩ := h
  apply BitVec.eq_of_getElem_eq; intro k hk
  let i : Fin 512 := ⟨k,hk⟩
  change bit (cover t v) i=bit top i
  rw [bit_top,cover_bit]
  obtain ⟨a,ha,hd⟩ := distinguishes_live h (c.hp i) (c.hn i)
  obtain ⟨w,hw,e⟩ := Step.mem_wires.mp (sub ha)
  exact ⟨w,hw,e ▸ distinguish_more hd hj⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def alone {x : Word} {c : Charts x} (a : Wire c) (v : List (Wire c)) :=
  v.filter (fun w => w.w != a.w)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def aside {x : Word} {c : Charts x} (a b : Wire c) (v : List (Wire c)) :=
  v.filter (fun w => w.w != a.w && w.w != b.w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cover_unary {x : Word} {c : Charts x} {n t} {a : Wire c} {v : List (Wire c)} (k : Bool)
    (h : Exact x n t (wires ((Step.flip a k).after v))) :
    a.flip.sep t ||| addSep k (a.sep t) (cover t (alone a v))=top := by
  let v' := a.flip :: (keepList k a ++ alone a v)
  have hv : cover t v'=top := preserve_cover v' h (by
    intro z hz; obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp hz
    rcases List.mem_cons.mp hw with rfl|hw
    · exact Step.mem_wires.mpr ⟨_,List.mem_cons_self,rfl⟩
    obtain ⟨wm,ok⟩ := List.mem_filter.mp hw
    by_cases e : w.w=a.w
    · cases k
      · simp [e] at ok
      · exact Step.mem_wires.mpr ⟨a,by simp [v',keepList],e.symm⟩
    · exact Step.mem_wires.mpr ⟨w,List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_filter.mpr ⟨wm,by simp [e]⟩)),rfl⟩)
  simpa only [v',cover,cover_keep] using hv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cover_binary {x : Word} {c : Charts x} {n t} {a b : Wire c} {v : List (Wire c)}
    (d ka kb : Bool) (h : Exact x n t (wires ((Step.binary d a b ka kb).after v))) :
    (a.binary d b).sep t ||| addSep ka (a.sep t) (addSep kb (b.sep t) (cover t (aside a b v)))=top := by
  let v' := a.binary d b :: (keepList ka a ++ (keepList kb b ++ aside a b v))
  have hv : cover t v'=top := preserve_cover v' h (by
    intro z hz; obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp hz
    rcases List.mem_cons.mp hw with rfl|hw
    · exact Step.mem_wires.mpr ⟨_,List.mem_cons_self,rfl⟩
    obtain ⟨wm,ok⟩ := List.mem_filter.mp hw
    obtain ⟨okA,okB⟩ := Bool.and_eq_true_iff.mp ok
    by_cases ea : w.w=a.w
    · cases ka
      · simp [ea] at okA
      · exact Step.mem_wires.mpr ⟨a,by simp [v',keepList],ea.symm⟩
    by_cases eb : w.w=b.w
    · cases kb
      · simp [eb] at okB
      · exact Step.mem_wires.mpr ⟨b,by simp [v',keepList],eb.symm⟩
    exact Step.mem_wires.mpr ⟨w,List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_filter.mpr ⟨wm,by simp [ea,eb]⟩))),rfl⟩)
  simpa only [v',cover,cover_keep] using hv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def scan {x : Word} {c : Charts x} (f : Frame c) (next : Frame c → Bool) :=
  let len := f.v.length
  let test := fun (s : Step c) (budget : ℕ) (bits : Word) =>
    decide (budget+1+s.drops < len+1) || bits != top || !isEligible s f.v || next (f.child s)
  f.v.all (fun a =>
    ((f.t==0) ||
      (let t := f.t-1
       let r := cover t (alone a f.v)
       let g := a.flip.sep t
       test (.flip a false) f.b (g ||| r) && test (.flip a true) f.b (g ||| (a.sep t ||| r)))) &&
    ((f.b==0) || f.v.all (fun w => !(decide (a.w.toNat < w.w.toNat)) ||
      (let r := cover f.t (aside a w f.v)
       let wa := a.sep f.t
       let wb := w.sep f.t
       [false,true].all (fun d =>
         let g := (a.binary d w).sep f.t
         [false,true].all (fun ka => [false,true].all (fun kb =>
           test (.binary d a w ka kb) (f.b-1) (g ||| addSep ka wa (addSep kb wb r)))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Fast {x : Word} {c : Charts x} (known : Frame c → Bool) : ℕ → Frame c → Bool
  | 0,f => immediate f.b f.t f.v f.ps || known f
  | k+1,f => immediate f.b f.t f.v f.ps ||
      (!(f.v.any (fun a => a.w == x)) && scan f (Fast known k))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma scan_sound {x : Word} {c : Charts x} {f : Frame c} {s : Step c} {next : Frame c → Bool}
    (h : scan f next = true) (nd : (f.v.map Wire.w).Nodup)
    (hs : s ∈ Step.all f.b f.t f.v) (el : eligible f.v s)
    (ht : Exact x (s.budget f.b f.t).1 (s.budget f.b f.t).2 (wires (s.after f.v))) :
    next (f.child s)=true := by
  have fit := fits_step f.v s nd el ht
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hs
  have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)
  rcases List.mem_append.mp hm with hu|hb
  · split at hu
    · contradiction
    rename_i tpos
    have q := Bool.and_eq_true_iff.mp ((Bool.or_eq_true_iff.mp hh.1).resolve_left
      (by simpa only [beq_iff_eq] using tpos))
    rcases List.mem_cons.mp hu with rfl|hu
    · have eq := cover_unary false ht
      change f.v.length+1 ≤ f.b+1+_ at fit
      simp only [Step.budget,addSep,Bool.false_eq_true,ite_false] at eq
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using q.1
    · obtain rfl := List.mem_singleton.mp hu
      have eq := cover_unary true ht
      change f.v.length+1 ≤ f.b+1+_ at fit
      simp only [Step.budget,addSep,ite_true] at eq
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using q.2
  · split at hb
    · contradiction
    rename_i bpos
    have q := (Bool.or_eq_true_iff.mp hh.2).resolve_left (by simpa only [beq_iff_eq] using bpos)
    obtain ⟨w,hw,hm⟩ := List.mem_flatMap.mp hb
    split at hm
    · rename_i lt
      have gate := (Bool.or_eq_true_iff.mp (List.all_eq_true.mp q w hw)).resolve_left (by simp [lt])
      obtain ⟨d,hd,h⟩ := List.mem_flatMap.mp hm
      obtain ⟨ka,hka,h⟩ := List.mem_flatMap.mp h
      obtain ⟨kb,hkb,rfl⟩ := List.mem_map.mp h
      have val := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp gate d hd) ka hka) kb hkb
      have eq := cover_binary d ka kb ht
      simp only [Step.budget] at eq
      change f.v.length+1 ≤ f.b-1+1+_ at fit
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using val
    · contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_sound {x : Word} {c : Charts x} (known : Frame c → Bool) (good : ∀ f, known f=true → f.No)
    (hx : proper x) (d : ℕ) {f : Frame c} (valid : f.Valid) (ok : Fast known d f = true) : f.No := by
  induction d generalizing f with
  | zero =>
    rcases Bool.or_eq_true_iff.mp ok with h|h
    · exact immediate_sound valid.1 valid.2 h
    · exact good _ h
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp ok with h|q
    · exact immediate_sound valid.1 valid.2 h
    obtain ⟨no,rows⟩ := Bool.and_eq_true_iff.mp q
    intro hex
    rcases descend c hx hex with hm | ⟨s,hs,el,ht⟩
    · obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      have yes : f.v.any (fun a => a.w == x) = true := List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩
      simp [yes] at no
    · exact ih (Frame.child_valid valid el (Step.all_legal hs)) (scan_sound rows valid.1 hs el ht) ht

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def fastRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (a : Table)
    (known : Frame c → Bool) (hops j : ℕ) :=
  (a[j]?).all (fun w => (root.replay d (w/65521)).all (Fast known hops))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_table {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    (d : ℕ) (a : Table) {known : Frame c → Bool} (sk : ∀ f, known f=true → f.No)
    (hops : ℕ) (h : Span (fastRow root d a known hops) 0 a.size) : TableSound root d a := by
  intro j w ew f ef
  have hj := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
  have e : Fast known hops f=true := by simpa only [fastRow,ew,Option.all_some,ef] using hj
  exact fast_sound known sk hx hops (Frame.replay_valid vr ef) e

-- Relabel truth-table rows along graph automorphisms.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Automorphism (x : Word) where
  p : Projection
  zero : p.q 0=0
  one : p.q top=top
  inj : Function.Injective p.q
  fix : p.q x=x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def autoFor (x : Word) (f g : Fin 512 → Fin 512) (rightInv : ∀ i, f (g i)=i)
    (fixed : (faceQ f).q x=x) : Automorphism x where
  p := faceQ f
  zero := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    change bit ((faceQ f).q 0) ⟨r,hr⟩ = bit 0 ⟨r,hr⟩; rw [q_bit,bit_zero,bit_zero]
  one := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    change bit ((faceQ f).q top) ⟨r,hr⟩ = bit top ⟨r,hr⟩; rw [q_bit,bit_top,bit_top]
  inj := by
    intro a b h
    apply BitVec.eq_of_getElem_eq; intro r hr
    let i : Fin 512 := ⟨r,hr⟩
    have e := congrArg (fun w => bit w (g i)) h
    change bit a i=bit b i
    simpa only [q_bit,rightInv] using e
  fix := fixed

namespace Automorphism
variable {x : Word}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma maps_proper (R : Automorphism x) {a} (h : proper a) : proper (R.p.q a) := by
  constructor
  · exact fun e => h.1 (R.inj (e.trans R.zero.symm))
  · exact fun e => h.2 (R.inj (e.trans R.one.symm))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma map_live (R : Automorphism x) {b t S} (h : Live x b t S) :
    Live x b t (S.image R.p.q) := by
  induction h with
  | done => simpa only [Finset.image_singleton,R.fix] using (Live.done (target:=x))
  | @unary b t U a pa fresh tail ih =>
    rw [Finset.image_insert]
    rw [Finset.image_insert,R.p.neg] at ih
    apply Live.unary (R.maps_proper pa) _ ih
    rw [←R.p.neg,←Finset.image_insert]
    intro hm
    obtain ⟨y,hy,e⟩ := Finset.mem_image.mp hm
    exact fresh ((R.inj e) ▸ hy)
  | @binary b t U a w d pa pw ne fresh tail ih =>
    rw [Finset.image_insert,Finset.image_insert]
    rw [Finset.image_insert,R.p.bin] at ih
    apply Live.binary (d:=d) (R.maps_proper pa) (R.maps_proper pw) (fun e => ne (R.inj e)) _ ih
    rw [←R.p.bin,←Finset.image_insert,←Finset.image_insert]
    intro hm
    obtain ⟨y,hy,e⟩ := Finset.mem_image.mp hm
    exact fresh ((R.inj e) ▸ hy)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma map_exact (R : Automorphism x) {b t S} (h : Exact x b t S) :
    Exact x b t (S.image R.p.q) := by
  obtain ⟨n,hn,j,hj,hl⟩ := h
  exact ⟨n,hn,j,hj,R.map_live hl⟩
end Automorphism

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def bareStep (v : List Word) (j : ℕ) : List Word :=
  if j < 32 then
    let a := v.getD (j/2) 0
    ~~~a :: v.filter (fun u => (Nat.mod j 2 == 1) || u != a)
  else
    let i := j-32
    let a := v.getD (i/128) 0
    let b := v.getD (Nat.mod (i/8) 16) 0
    combine (Nat.mod (i/4) 2 == 1) a b :: v.filter (fun u =>
      ((Nat.mod (i/2) 2 == 1) || u != a) && ((Nat.mod i 2 == 1) || u != b))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def bareReplay (v : List Word) : ℕ → ℕ → List Word
  | 0,_ => v
  | d+1,tape => bareStep (bareReplay v d (tape/4096)) (Nat.mod tape 4096-1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma filt_map {α β : Type} (f : α→β) (p : α→Bool) (q : β→Bool) (ok : ∀ a, q (f a)=p a)
    (v : List α) : (v.map f).filter q = (v.filter p).map f := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [List.map_cons,List.filter_cons,ok]
    cases p a <;> simp [ih]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mapped_get {α β : Type} (f : α→β) (a : α) (v : List α) (i : ℕ) :
    (v.map f).getD i (f a)=f (v.getD i a) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases v[i]? <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma project_step {x : Word} (R : Automorphism x) (v : List Word) (j : ℕ) :
    bareStep (v.map R.p.q) j=(bareStep v j).map R.p.q := by
  have bne (a b : Word) : (R.p.q a != R.p.q b) = (a != b) := by
    apply Bool.eq_iff_iff.mpr; simp only [bne_iff_ne]; exact not_congr R.inj.eq_iff
  have get (i : ℕ) : (v.map R.p.q).getD i 0 = R.p.q (v.getD i 0) := by
    simpa only [R.zero] using mapped_get R.p.q 0 v i
  by_cases small : j < 32
  · simp only [bareStep,small,ite_true,get,List.map_cons,R.p.neg]
    congr 1; exact filt_map _ _ _ (fun u => by simp only [bne]) _
  · simp only [bareStep,small,ite_false,get,List.map_cons,R.p.bin]
    congr 1; exact filt_map _ _ _ (fun u => by simp only [bne]) _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma project_tape {x : Word} (R : Automorphism x) (v : List Word) (d tape : ℕ) :
    bareReplay (v.map R.p.q) d tape=(bareReplay v d tape).map R.p.q := by
  induction d generalizing tape with
  | zero => rfl
  | succ d ih => simp only [bareReplay,ih,project_step]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma decode_words {x : Word} {c : Charts x} {f : Frame c} {j : ℕ} {s : Step c}
    (eq : f.decoded j=some s) :
    (s.after f.v).map Wire.w=bareStep (f.v.map Wire.w) j := by
  unfold Frame.decoded at eq
  unfold bareStep
  split at eq
  · rename_i small
    simp only [small,ite_true]
    split at eq
    · contradiction
    cases e : f.v[j/2]? with
    | none => simp [e] at eq
    | some a =>
      simp only [e,Option.map_some,Option.some.injEq] at eq
      subst s
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map,e,Option.map_some,Option.getD_some,
        Step.after,Step.out,Step.rest,Wire.flip,List.map_cons,List.cons.injEq,true_and]
      exact (filt_map Wire.w _ (fun u => (Nat.mod j 2 == 1) || u != a.w) (fun _ => rfl) f.v).symm
  · rename_i large
    simp only [large,ite_false]
    split at eq
    · contradiction
    let i := j-32
    change ((f.v[i/128]?).bind _)=some s at eq
    cases e : f.v[i/128]? with
    | none => simp [e] at eq
    | some a =>
      simp only [e,Option.bind_some] at eq
      cases z : f.v[Nat.mod (i/8) 16]? with
      | none => simp [i] at z; simp [z] at eq
      | some b =>
        change Option.map _ (f.v[Nat.mod (i/8) 16]?) = some s at eq
        simp only [z,Option.map_some,Option.some.injEq] at eq
        subst s
        simp only [i] at e z
        simp only [List.getD_eq_getElem?_getD,List.getElem?_map,e,z,Option.map_some,Option.getD_some,
          Step.after,Step.out,Step.rest,Wire.binary,List.map_cons,List.cons.injEq,true_and]
        exact (filt_map Wire.w _ (fun u => ((Nat.mod (i/2) 2 == 1) || u != a.w) && ((Nat.mod i 2 == 1) || u != b.w)) (fun _ => rfl) f.v).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma jump_words {x : Word} {c : Charts x} {f g : Frame c} {j : ℕ} (h : f.jump j=some g) :
    g.v.map Wire.w=bareStep (f.v.map Wire.w) j := by
  unfold Frame.jump at h
  cases e : f.decoded j with
  | none => simp [e] at h
  | some s =>
    simp only [e,Option.bind_some] at h
    split at h
    · obtain rfl := Option.some.inj h; exact decode_words e
    · contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma replay_words {x : Word} {c : Charts x} {f g : Frame c} {d tape} (h : f.replay d tape=some g) :
    g.v.map Wire.w=bareReplay (f.v.map Wire.w) d tape := by
  induction d generalizing tape g with
  | zero => obtain rfl := Option.some.inj h; rfl
  | succ d ih =>
    unfold Frame.replay at h
    cases e : f.replay d (tape/4096) with
    | none => simp [e] at h
    | some q =>
      obtain hq := jump_words (by simpa only [e,Option.bind_some] using h :
        q.jump (Nat.mod tape 4096-1)=some g)
      rw [hq,ih e]; rfl

-- Transfer an infeasibility proof within each orbit and certify representatives.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gather (v : ℕ) : List ℕ → ℕ
  | [] => 0
  | j::xs => (if v.testBit j then 1 else 0) + 2*gather v xs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def assignRows (order : List ℕ) (i : Fin 512) : Fin 512 := Fin.ofNat 512 (gather i.val order)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Rotation {x : Word} {c : Charts x} (root : Frame c) where
  R : Automorphism x
  base : List Word
  eq : base=(root.v.map Wire.w).map R.p.q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def refCode (links : Array ℕ) (j : ℕ) := (links[j]?).getD 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def linked {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (rows links : Array ℕ)
    (rot : Array (Rotation root)) (tag tape : ℕ) (f : Frame c) : Bool :=
  let k := tag/16-1
  refCode links k == 0 &&
    (rot[Nat.mod tag 16]?).any (fun A =>
      (rows[k]?).any (fun w => (root.replay d (w/65521)).any (fun g =>
        f.b==g.b && f.t==g.t && (bareReplay A.base d tape).isPerm (g.v.map Wire.w))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def symRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (rows links : Array ℕ)
    (rot : Array (Rotation root)) (known : Frame c → Bool) (hops j : ℕ) :=
  let tag := refCode links j
  if tag=0 then fastRow root d rows known hops j else
    (rows[j]?).all (fun w => (root.replay d (w/65521)).all (linked root d rows links rot tag (w/65521)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma linked_sound {x : Word} {c : Charts x} {root : Frame c} {d : ℕ} {rows links : Array ℕ}
    {rot : Array (Rotation root)} {tag tape : ℕ} {f : Frame c}
    (reps : ∀ (j w : ℕ), refCode links j=0 → rows[j]?=some w →
      ∀ g, root.replay d (w/65521)=some g → g.No)
    (he : root.replay d tape=some f) (h : linked root d rows links rot tag tape f=true) : f.No := by
  let k := tag/16-1
  obtain ⟨tagZero,rotHit⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨A,_,rowHit⟩ := (Option.any_eq_true ..).1 rotHit
  obtain ⟨word,ew,frameHit⟩ := (Option.any_eq_true ..).1 rowHit
  obtain ⟨g,eg,hit⟩ := (Option.any_eq_true ..).1 frameHit
  obtain ⟨bud,perm⟩ := Bool.and_eq_true_iff.mp hit
  obtain ⟨eb,et⟩ := Bool.and_eq_true_iff.mp bud
  have eb := beq_iff_eq.mp eb
  have et := beq_iff_eq.mp et
  have ng := reps k word (beq_iff_eq.mp tagZero) ew g eg
  have listEq : bareReplay A.base d tape=(f.v.map Wire.w).map A.R.p.q := by
    rw [A.eq,project_tape,←replay_words he]
  have eq : (wires f.v).image A.R.p.q = wires g.v := by
    ext a
    have p := (List.isPerm_iff.mp perm).mem_iff (a:=a)
    rw [listEq] at p
    simpa only [wires,List.mem_toFinset,List.mem_map,Finset.mem_image] using p
  intro hf
  have mapped := A.R.map_exact hf
  rw [eb,et,eq] at mapped
  exact ng mapped

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sym_table {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    (d : ℕ) (rows links : Table) (rot : Array (Rotation root)) {known : Frame c → Bool}
    (sk : ∀ f, known f=true → f.No) (hops : ℕ)
    (h : Span (symRow root d rows links rot known hops) 0 rows.size) : TableSound root d rows := by
  have reps (j w : ℕ) (zero : refCode links j=0) (ew : rows[j]?=some w)
      (f : Frame c) (ef : root.replay d (w/65521)=some f) : f.No := by
    have hh := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
    have ck : Fast known hops f=true := by
      simpa only [symRow,zero,ite_true,fastRow,ew,Option.all_some,ef] using hh
    exact fast_sound known sk hx hops (Frame.replay_valid vr ef) ck
  intro j w ew f ef
  by_cases z : refCode links j=0
  · exact reps j w z ew f ef
  · have hh := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
    apply linked_sound reps ef (rot:=rot) (tag:=refCode links j)
    simpa only [symRow,z,ite_false,ew,Option.all_some,ef] using hh

-- A read-once monotone suffix cannot realize the six-row AND and OR requirements on a single pair of leaves.
abbrev Tiny := BitVec 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure TracePoint where
  row : Fin 6 → Fin 512

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def TracePoint.sig (p : TracePoint) (w : Word) : Tiny :=
  BitVec.ofBoolListBE [bit w (p.row 5),bit w (p.row 4),bit w (p.row 3),
    bit w (p.row 2),bit w (p.row 1),bit w (p.row 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sig_bit (p : TracePoint) (w : Word) (i : Fin 6) : (p.sig w)[i.val] = bit w (p.row i) := by
  let rows := [bit w (p.row 5),bit w (p.row 4),bit w (p.row 3),bit w (p.row 2),bit w (p.row 1),bit w (p.row 0)]
  have q := BitVec.getElem_ofBoolListBE (bs:=rows) (i:=i.val) (show i.val<rows.length from i.isLt)
  exact q.trans (by fin_cases i <;> rfl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sig_combine (p : TracePoint) (d : Bool) (a b : Word) :
    p.sig (combine d a b) = if d then p.sig a ||| p.sig b else p.sig a &&& p.sig b := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let i : Fin 6 := ⟨j,hj⟩
  rw [sig_bit p (combine d a b) i,bit_bin]
  cases d <;> simp only [Bool.false_eq_true,ite_false,ite_true,BitVec.getElem_and,BitVec.getElem_or] <;> rw [←sig_bit p a i,←sig_bit p b i]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def allowed (a b : Bool) (s : Tiny) : Bool :=
  (if a then (if b then 0xfffffffffdffffff else 0xdddddddd0000dddd)
    else (if b then 0xf5f5f5f500f500f5 else 0xd5d5d5d5000000d5) : ℕ).testBit s.toNat

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma allowed_join : ∀ (a b c d : Bool) (s t : Tiny) (op : Bool),
    (a && c)=false → (b && d)=false → allowed a b s=true → allowed c d t=true →
    allowed (a||c) (b||d) (if op then s ||| t else s &&& t)=true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mergeMark (a b z w : Word) := if w=a ∨ w=b then z else w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rof_live {x : Word} (p : TracePoint) {n t S} (live : Live x n t S) (zero : t=0)
    (full : S.card=n+1) (A B : Word) (memA : A∈S) (memB : B∈S)
    (ok : ∀ w∈S, allowed (w==A) (w==B) (p.sig w)=true) :
    allowed true true (p.sig x)=true := by
  induction live generalizing A B with
  | done =>
    obtain rfl := Finset.mem_singleton.mp memA
    obtain rfl := Finset.mem_singleton.mp memB
    simpa using ok _ (Finset.mem_singleton_self _)
  | unary _ _ _ ih => omega
  | @binary n t U a b d pa pb ab fresh tail ih =>
    let z := combine d a b
    have zU : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have cap := count_live tail
    rw [Finset.card_insert_of_notMem zU] at cap
    have hbU : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at full
      have bind := Finset.card_insert_le a U
      omega
    have hbcard := Finset.card_insert_of_notMem hbU
    have haB : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at full
      omega
    rw [Finset.card_insert_of_notMem haB,hbcard] at full
    have member (w : Word) (pw : w∈insert a (insert b U)) :
        mergeMark a b z w ∈ insert z U := by
      by_cases eq : w=a ∨ w=b
      · simp [mergeMark,eq]
      · have hu : w∈U := ((Finset.mem_insert.mp ((Finset.mem_insert.mp pw).resolve_left (not_or.mp eq).1)).resolve_left (not_or.mp eq).2)
        simp [mergeMark,eq,hu]
    have mz (w : Word) (pw : w∈insert a (insert b U)) :
        (z==mergeMark a b z w) = ((a==w) || (b==w)) := by
      have zw : z≠w := fun e => fresh (show z∈insert a (insert b U) by rwa [e])
      by_cases e1 : w=a
      · simp [mergeMark,e1]
      by_cases e2 : w=b
      · simp [mergeMark,e2]
      simp only [mergeMark,e1,e2,or_self,ite_false]
      rw [beq_eq_false_iff_ne.mpr zw,beq_eq_false_iff_ne.mpr (Ne.symm e1),beq_eq_false_iff_ne.mpr (Ne.symm e2)]
      rfl
    have normal (u w : Word) (uU : u∈U) :
        (u==mergeMark a b z w)=(u==w) := by
      have ua : u≠a := by rintro rfl; exact haB (Finset.mem_insert_of_mem uU)
      have ub : u≠b := by rintro rfl; exact hbU uU
      have uz : u≠z := by rintro rfl; exact zU uU
      by_cases e1 : w=a <;> by_cases e2 : w=b <;> simp_all [mergeMark]
    apply ih zero (by rw [Finset.card_insert_of_notMem zU]; omega)
      (mergeMark a b z A) (mergeMark a b z B) (member A memA) (member B memB)
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|hw
    · change allowed (z==_) (z==_) (p.sig (combine d a b))=true
      rw [mz A memA,mz B memB,sig_combine]
      apply allowed_join
      · by_cases h : a=A
        · have nb : b≠A := by rintro e; exact ab (h.trans e.symm)
          simp [h,nb]
        · simp [h]
      · by_cases h : a=B
        · have nb : b≠B := by rintro e; exact ab (h.trans e.symm)
          simp [h,nb]
        · simp [h]
      · exact ok a (Finset.mem_insert_self ..)
      · exact ok b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    · rw [normal w A hw,normal w B hw]
      exact ok w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))

-- Test six-row witnesses in parallel on the packed positive and negative samples.
abbrev Patch := BitVec 36
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lane (v : Word) (n : ℕ) : Patch := v.extractLsb' n 36

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def patchPoint {x : Word} (c : Charts x) (k : Fin 36) : TracePoint :=
  ⟨![c.p ⟨k.val, by omega⟩,c.n ⟨k.val,by omega⟩,c.n ⟨36+k.val,by omega⟩,
     c.p ⟨36+k.val,by omega⟩,c.p ⟨72+k.val,by omega⟩,c.n ⟨72+k.val,by omega⟩]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pGrey {x : Word} {c : Charts x} (w : Wire c) : Patch :=
  (~~~(lane w.p 0) ||| (lane w.n 0 &&& lane w.n 36)) &&&
  (~~~(lane w.p 36 ||| lane w.p 72) ||| lane w.n 72)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pLeft {x : Word} {c : Charts x} (w : Wire c) : Patch := lane w.n 0 &&& ~~~(lane w.p 72)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pRight {x : Word} {c : Charts x} (w : Wire c) : Patch := lane w.n 36 &&& ~~~(lane w.p 36)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def wordGrey (s : Tiny) := (!s[0] || (s[1] && s[2])) && (!(s[3] || s[4]) || s[5])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def wordLeft (s : Tiny) := s[1] && !s[4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def wordRight (s : Tiny) := s[2] && !s[3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma legal_grey : ∀ s, wordGrey s=true → allowed false false s=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma legal_left : ∀ s, wordLeft s=true → allowed true false s=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma legal_right : ∀ s, wordRight s=true → allowed false true s=true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma lane_bit (v : Word) (n : ℕ) (k : Fin 36) (h : n+k.val < 512) :
   (lane v n)[k.val] = bit v ⟨n+k.val,h⟩ := by
  exact (BitVec.getElem_extractLsb' (x:=v) (start:=n) k.isLt).trans (BitVec.getLsbD_eq_getElem h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma patch_extract {x : Word} {c : Charts x} (w : Wire c) (k : Fin 36) :
    (pGrey w)[k.val] = wordGrey ((patchPoint c k).sig w.w) ∧
    (pLeft w)[k.val] = wordLeft ((patchPoint c k).sig w.w) ∧
    (pRight w)[k.val] = wordRight ((patchPoint c k).sig w.w) := by
  have point (j : ℕ) (h : j<6) : ((patchPoint c k).sig w.w)[j]=bit w.w ((patchPoint c k).row ⟨j,h⟩) := sig_bit (patchPoint c k) w.w ⟨j,h⟩
  simp only [wordGrey,wordLeft,wordRight,pGrey,pLeft,pRight,BitVec.getElem_and,BitVec.getElem_or,
    BitVec.getElem_not,lane_bit _ 0 k (by omega),lane_bit _ 36 k (by omega),lane_bit _ 72 k (by omega)]
  rw [point 0 (by decide),point 1 (by decide),point 2 (by decide),point 3 (by decide),point 4 (by decide),point 5 (by decide)]
  simp only [w.hp,w.hn,Nat.zero_add]
  exact ⟨rfl,rfl,rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma patch_target {x : Word} (c : Charts x) (k : Fin 36) : (patchPoint c k).sig x=25 := by
  have q (i : Fin 6) : bit x ((patchPoint c k).row i) = (25 : Tiny)[i.val] := by
    fin_cases i <;> first | exact c.hp _ | exact c.hn _
  apply BitVec.eq_of_getElem_eq
  intro j hj
  exact (sig_bit (patchPoint c k) x ⟨j,hj⟩).trans (q ⟨j,hj⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def greyRest {x : Word} {c : Charts x} (a b : Word) : List (Wire c) → Patch
  | [] => BitVec.allOnes 36
  | w::v => if w.w==a || w.w==b then greyRest a b v else pGrey w &&& greyRest a b v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def findConflict {x : Word} {c : Charts x} (v : List (Wire c)) :=
  v.any (fun a => v.any (fun b => a.w != b.w &&
    (pLeft a &&& pRight b &&& greyRest a.w b.w v) != 0))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma uncovered {u : Patch} (neq : u≠0) : ∃ k : Fin 36, u[k.val]=true := by
  by_contra! no
  apply neq
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have q := no ⟨j,hj⟩
  cases h : u[j] <;> simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rest_grey {x : Word} {c : Charts x} {a b : Word} {v : List (Wire c)} {k : Fin 36}
    (ok : (greyRest a b v)[k.val]=true) (w : Wire c) (inV : w∈v)
    (wa : w.w≠a) (wb : w.w≠b) : (pGrey w)[k.val]=true := by
  induction v with
  | nil => contradiction
  | cons h l ih =>
    cases e : (h.w==a || h.w==b)
    · rw [greyRest,e] at ok
      have val : (pGrey h &&& greyRest a b l)[k.val]=true := ok
      rw [BitVec.getElem_and] at val
      have two := Bool.and_eq_true_iff.mp val
      rcases List.mem_cons.mp inV with rfl|hw
      · exact two.1
      · exact ih two.2 hw
    · rw [greyRest,e] at ok
      apply ih ok
      apply (List.mem_cons.mp inV).resolve_left
      rintro rfl
      simp [beq_eq_false_iff_ne.mpr wa,beq_eq_false_iff_ne.mpr wb] at e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma no_readOnce {x : Word} {c : Charts x} {v : List (Wire c)} {b : ℕ}
    (nd : (v.map Wire.w).Nodup) (width : b+1=v.length) (hit : findConflict v=true) :
    ¬Exact x b 0 (wires v) := by
  rintro ⟨n,hn,t,ht,h⟩
  have card : (wires v).card=v.length := by
    change (v.map Wire.w).toFinset.card=v.length
    rw [List.toFinset_card_of_nodup nd,List.length_map]
  have cap := count_live h
  have eq : (wires v).card=n+1 := by omega
  obtain ⟨a,ha,yy⟩ := List.any_eq_true.mp hit
  obtain ⟨d,hd,yy⟩ := List.any_eq_true.mp yy
  obtain ⟨ad,mask⟩ := Bool.and_eq_true_iff.mp yy
  obtain ⟨k,hk⟩ := uncovered (bne_iff_ne.mp mask)
  rw [BitVec.getElem_and,BitVec.getElem_and] at hk
  obtain ⟨both,rest⟩ := Bool.and_eq_true_iff.mp hk
  obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp both
  have valid := rof_live (patchPoint c k) h (by omega) eq a.w d.w
    (Step.mem_wires.mpr ⟨a,ha,rfl⟩) (Step.mem_wires.mpr ⟨d,hd,rfl⟩)
  have bad := valid (by
    intro y hy; obtain ⟨u,hu,rfl⟩ := Step.mem_wires.mp hy
    by_cases ea : u.w=a.w
    · rw [ea,beq_self_eq_true,beq_eq_false_iff_ne.mpr (bne_iff_ne.mp ad)]
      exact legal_left _ ((patch_extract a k).2.1 ▸ left)
    by_cases eb : u.w=d.w
    · rw [eb,beq_self_eq_true,beq_eq_false_iff_ne.mpr (Ne.symm (bne_iff_ne.mp ad))]
      exact legal_right _ ((patch_extract d k).2.2 ▸ right)
    rw [beq_eq_false_iff_ne.mpr ea,beq_eq_false_iff_ne.mpr eb]
    apply legal_grey
    rw [←(patch_extract u k).1]
    exact rest_grey rest u hu ea eb)
  rw [patch_target] at bad
  exact (by decide : allowed true true 25 ≠ true) bad

-- Assign the two distinguished inputs and verify the remaining inputs by a four-state scan.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Flags where
  grey : Patch
  a : Patch
  b : Patch
  ab : Patch

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def flagFold {x : Word} {c : Charts x} : List (Wire c) → Flags
  | [] => ⟨BitVec.allOnes 36,0,0,0⟩
  | w::v =>
    let f := flagFold v
    let g := pGrey w
    let a := pLeft w
    let b := pRight w
    ⟨g &&& f.grey,(g &&& f.a) ||| (a &&& f.grey),(g &&& f.b) ||| (b &&& f.grey),
      (g &&& f.ab) ||| (a &&& f.b) ||| (b &&& f.a)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def AllGrey {x : Word} {c : Charts x} (k : Fin 36) (v : List (Wire c)) :=
  ∀ w∈v, (pGrey w)[k.val]=true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def OneSlot {x : Word} {c : Charts x} (mark : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∃ a∈v, (mark a)[k.val]=true ∧ ∀ w∈v, w.w≠a.w → (pGrey w)[k.val]=true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def TwoSlots {x : Word} {c : Charts x} (ma mb : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∃ a∈v, ∃ b∈v, a.w≠b.w ∧ (ma a)[k.val]=true ∧ (mb b)[k.val]=true ∧
    ∀ w∈v, w.w≠a.w → w.w≠b.w → (pGrey w)[k.val]=true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma next_grey {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c}
    (h : (pGrey w)[k.val]=true) (hg : AllGrey k v) : AllGrey k (w::v) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma one_grey {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c} {mark}
    (h : (pGrey w)[k.val]=true) (hg : OneSlot mark k v) : OneSlot mark k (w::v) := by
  obtain ⟨a,ha,hm,hg⟩ := hg
  refine ⟨a,List.mem_cons_of_mem _ ha,hm,?_⟩
  intro q hq nq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq nq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma one_pick {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c} {mark : Wire c→Patch}
    (h : (mark w)[k.val]=true) (hg : AllGrey k v) : OneSlot mark k (w::v) := by
  refine ⟨w,List.mem_cons_self,h,?_⟩
  intro q hq nq
  exact hg q ((List.mem_cons.mp hq).resolve_left (by rintro rfl; exact nq rfl))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma two_grey {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c} {ma mb}
    (h : (pGrey w)[k.val]=true) (hg : TwoSlots ma mb k v) : TwoSlots ma mb k (w::v) := by
  obtain ⟨a,ha,b,hb,ne,pa,pb,hg⟩ := hg
  refine ⟨a,List.mem_cons_of_mem _ ha,b,List.mem_cons_of_mem _ hb,ne,pa,pb,?_⟩
  intro q hq qa qb
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq qa qb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma two_pick {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c} {ma mb : Wire c→Patch}
    (nw : w.w∉wires v) (h : (ma w)[k.val]=true) (hg : OneSlot mb k v) : TwoSlots ma mb k (w::v) := by
  obtain ⟨a,ha,pa,hg⟩ := hg
  have ne : w.w≠a.w := fun eq => nw (Step.mem_wires.mpr ⟨a,ha,eq.symm⟩)
  refine ⟨w,List.mem_cons_self,a,List.mem_cons_of_mem _ ha,ne,h,pa,?_⟩
  intro q hq qw qa
  exact hg q ((List.mem_cons.mp hq).resolve_left (by rintro rfl; exact qw rfl)) qa

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma two_swap {x : Word} {c : Charts x} {k} {v : List (Wire c)} {ma mb}
    (h : TwoSlots ma mb k v) : TwoSlots mb ma k v := by
  obtain ⟨a,ha,b,hb,n,pa,pb,hh⟩ := h
  exact ⟨b,hb,a,ha,n.symm,pb,pa,fun q hq qb qa => hh q hq qa qb⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma flags_sound {x : Word} {c : Charts x} (k : Fin 36) (v : List (Wire c)) (nd : (v.map Wire.w).Nodup) :
    ((flagFold v).grey[k.val]=true → AllGrey k v) ∧
    ((flagFold v).a[k.val]=true → OneSlot pLeft k v) ∧
    ((flagFold v).b[k.val]=true → OneSlot pRight k v) ∧
    ((flagFold v).ab[k.val]=true → TwoSlots pLeft pRight k v) := by
  induction v with
  | nil => simp [AllGrey,flagFold]
  | cons w l ih =>
    obtain ⟨nw,nl⟩ := List.nodup_cons.mp nd
    have nm : w.w∉wires l := fun hh => nw (List.mem_toFinset.mp hh)
    obtain ⟨ig,ia,ib,iab⟩ := ih nl
    simp only [flagFold,BitVec.getElem_and,BitVec.getElem_or,Bool.and_eq_true,Bool.or_eq_true]
    refine ⟨fun ⟨wG,g⟩ => next_grey wG (ig g),?_,?_,?_⟩
    · rintro (⟨wg,a⟩|⟨wa,g⟩)
      · exact one_grey wg (ia a)
      · exact one_pick wa (ig g)
    · rintro (⟨wg,b⟩|⟨wb,g⟩)
      · exact one_grey wg (ib b)
      · exact one_pick wb (ig g)
    · rintro ((⟨wg,ab⟩|⟨wa,b⟩)|⟨wb,a⟩)
      · exact two_grey wg (iab ab)
      · exact two_pick nm wa (ib b)
      · exact two_swap (two_pick nm wb (ia a))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma grey_rest_of {x : Word} {c : Charts x} {a b : Word} {v : List (Wire c)} {k : Fin 36}
    (h : ∀ w∈v, w.w≠a → w.w≠b → (pGrey w)[k.val]=true) : (greyRest a b v)[k.val]=true := by
  induction v with
  | nil => exact BitVec.getElem_allOnes k.val k.isLt
  | cons w l ih =>
    have tl := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    by_cases ea : w.w=a
    · simp [greyRest,ea,tl]
    by_cases eb : w.w=b
    · simp [greyRest,eb,tl]
    have ww := h w List.mem_cons_self ea eb
    simp only [greyRest,beq_eq_false_iff_ne.mpr ea,beq_eq_false_iff_ne.mpr eb,Bool.false_or,
      Bool.false_eq_true,ite_false,BitVec.getElem_and,ww,tl,Bool.true_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma certified_flags {x : Word} {c : Charts x} {v : List (Wire c)} {b : ℕ}
    (nd : (v.map Wire.w).Nodup) (width : b+1=v.length) (hit : (flagFold v).ab != 0) :
    ¬Exact x b 0 (wires v) := by
  obtain ⟨k,hk⟩ := uncovered (bne_iff_ne.mp hit)
  obtain ⟨a,ha,z,hz,nz,pa,pz,gy⟩ := (flags_sound k v nd).2.2.2 hk
  apply no_readOnce nd width
  apply List.any_eq_true.mpr
  refine ⟨a,ha,List.any_eq_true.mpr ⟨z,hz,Bool.and_eq_true_iff.mpr ⟨bne_iff_ne.mpr nz,?_⟩⟩⟩
  apply bne_iff_ne.mpr
  intro eq
  have h := congrArg (fun u : Patch => u[k.val]) eq
  simp only [BitVec.getElem_and,pa,pz,grey_rest_of gy,Bool.true_and] at h
  exact Bool.noConfusion (h.trans (BitVec.getElem_zero k.isLt))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def tightConflict {x : Word} {c : Charts x} (f : Frame c) :=
  (f.t==0 && f.b+1==f.v.length) && (flagFold f.v).ab != 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tight_sound {x : Word} {c : Charts x} {f : Frame c} (valid : f.Valid)
    (ok : tightConflict f=true) : f.No := by
  obtain ⟨small,hit⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨t,width⟩ := Bool.and_eq_true_iff.mp small
  have h := certified_flags valid.1 (beq_iff_eq.mp width) hit
  change ¬ Exact x f.b f.t (wires f.v)
  rwa [beq_iff_eq.mp t]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def readCut {x : Word} {c : Charts x} (f : Frame c) :=
  immediate f.b f.t f.v f.ps || tightConflict f

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma read_cut {x : Word} {c : Charts x} {f : Frame c} (v : f.Valid) (h : readCut f=true) : f.No := by
  rcases Bool.or_eq_true_iff.mp h with hi|hc
  · exact immediate_sound v.1 v.2 hi
  · exact tight_sound v hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ReadSearch {x : Word} {c : Charts x} (known : Frame c → Bool) : ℕ → Frame c → Bool
  | 0,f => readCut f || known f
  | k+1,f => readCut f ||
      (!(f.v.any (fun a => a.w == x)) && scan f (ReadSearch known k))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma read_sound {x : Word} {c : Charts x} (known : Frame c → Bool) (good : ∀ f, known f=true → f.No)
    (hx : proper x) (d : ℕ) {f : Frame c} (valid : f.Valid) (ok : ReadSearch known d f = true) : f.No := by
  induction d generalizing f with
  | zero =>
    rcases Bool.or_eq_true_iff.mp ok with h|h
    · exact read_cut valid h
    · exact good _ h
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp ok with h|q
    · exact read_cut valid h
    obtain ⟨no,rows⟩ := Bool.and_eq_true_iff.mp q
    intro hex
    rcases descend c hx hex with hm | ⟨s,hs,el,ht⟩
    · obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      have yes : f.v.any (fun a => a.w == x) = true := List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩
      simp [yes] at no
    · exact ih (Frame.child_valid valid el (Step.all_legal hs)) (scan_sound rows valid.1 hs el ht) ht

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def readRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (a : Table)
    (known : Frame c → Bool) (hops j : ℕ) :=
  (a[j]?).all (fun w => (root.replay d (w/65521)).all (ReadSearch known hops))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rSymRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (rows links : Array ℕ)
    (rot : Array (Rotation root)) (known : Frame c → Bool) (hops j : ℕ) :=
  let tag := refCode links j
  if tag=0 then readRow root d rows known hops j else
    (rows[j]?).all (fun w => (root.replay d (w/65521)).all (linked root d rows links rot tag (w/65521)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rSym_table {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    (d : ℕ) (rows links : Table) (rot : Array (Rotation root)) {known : Frame c → Bool}
    (sk : ∀ f, known f=true → f.No) (hops : ℕ)
    (h : Span (rSymRow root d rows links rot known hops) 0 rows.size) : TableSound root d rows := by
  have reps (j w : ℕ) (zero : refCode links j=0) (ew : rows[j]?=some w)
      (f : Frame c) (ef : root.replay d (w/65521)=some f) : f.No := by
    have hh := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
    have ck : ReadSearch known hops f=true := by
      simpa only [rSymRow,zero,ite_true,readRow,ew,Option.all_some,ef] using hh
    exact read_sound known sk hx hops (Frame.replay_valid vr ef) ck
  intro j w ew f ef
  by_cases z : refCode links j=0
  · exact reps j w z ew f ef
  · have hh := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
    apply linked_sound reps ef (rot:=rot) (tag:=refCode links j)
    simpa only [rSymRow,z,ite_false,ew,Option.all_some,ef] using hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Positive (x : Word) (S : Finset Word) : Prop :=
  ∀ a∈S, ∃ i j : Fin 512, bit x i=true ∧ bit x j=false ∧ bit a i=true ∧ bit a j=false ∧
    ∀ w∈S, w≠a → bit w i=bit w j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma exact_difference {x b t S} (h : Live x b t S) {i j : Fin 512}
    (xi : bit x i=true) (xj : bit x j=false) : ∃ a∈S, bit a i≠bit a j := by
  obtain ⟨a,ha,d⟩ := distinguishes_live h xi xj
  refine ⟨a,ha,?_⟩
  by_cases z : t=0
  · obtain ⟨u,v⟩ := (by simpa [distinguishes,z] using d : bit a i=true ∧ bit a j=false)
    simp [u,v]
  · simpa [distinguishes,z] using d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tight_parts {x : Word} {n t U a b d} (ab : a≠b)
    (fresh : combine d a b∉insert a (insert b U)) (tail : Live x n t (insert (combine d a b) U))
    (width : (insert a (insert b U)).card=n+1+1) :
    a∉U ∧ b∉U ∧ (insert (combine d a b) U).card=n+1 := by
  have zu : combine d a b∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have cnt := count_live tail
  rw [Finset.card_insert_of_notMem zu] at cnt ⊢
  have notB : b∉U := by
    intro h
    rw [Finset.insert_eq_of_mem h] at width
    have lim := Finset.card_insert_le a U
    omega
  have bcard := Finset.card_insert_of_notMem notB
  have notA : a∉insert b U := by
    intro h
    rw [Finset.insert_eq_of_mem h] at width
    omega
  rw [Finset.card_insert_of_notMem notA,bcard] at width
  exact ⟨fun h => notA (Finset.mem_insert_of_mem h),notB,by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tight_positive {x : Word} {n t S} (live : Live x n t S) (one : t≤1)
    (width : S.card=n+1) (positive : Positive x S) : t=0 := by
  induction live with
  | done => rfl
  | @unary n t U a ha fresh tail ih =>
    have zero : t=0 := by omega
    have zu : ~~~a ∉ U := fun h => fresh (Finset.mem_insert_of_mem h)
    have cnt := count_live tail
    rw [Finset.card_insert_of_notMem zu] at cnt
    have au : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at width
      -- A unary operation keeps the same budget, so retaining its input violates the tight width.
      omega
    obtain ⟨i,j,xi,xj,ai,aj,q⟩ := positive a (Finset.mem_insert_self ..)
    obtain ⟨w,hw,dist⟩ := distinguishes_live tail xi xj
    have dl : bit w i=true ∧ bit w j=false := by simpa [distinguishes,zero] using dist
    rcases Finset.mem_insert.mp hw with rfl|wu
    · simp [bit_not,ai] at dl
    · have wa : w≠a := by rintro rfl; exact au wu
      have e := q w (Finset.mem_insert_of_mem wu) wa
      simp [dl.1,dl.2] at e
  | @binary n t U a b d pa pb ab fresh tail ih =>
    obtain ⟨au,bu,tw⟩ := tight_parts ab fresh tail width
    apply ih one tw
    intro w hw
    have am : a∈insert a (insert b U) := Finset.mem_insert_self ..
    have bm : b∈insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    rcases Finset.mem_insert.mp hw with rfl|wu
    · obtain ⟨i,j,xi,xj,ai,aj,other⟩ := positive a am
      have beq := other b bm ab.symm
      obtain ⟨w,hw,diff⟩ := exact_difference tail xi xj
      have wz : w=combine d a b := (Finset.mem_insert.mp hw).resolve_right (by
        intro hu
        apply diff
        exact other w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) (by rintro rfl; exact au hu))
      subst w
      have pos : bit (combine d a b) i=true ∧ bit (combine d a b) j=false := by
        cases d <;> cases h : bit b j <;> simp_all only [bit_bin,Bool.false_eq_true,ite_false,ite_true,
          Bool.true_and,Bool.false_and,Bool.true_or,Bool.false_or] <;> decide
      refine ⟨i,j,xi,xj,pos.1,pos.2,?_⟩
      intro w hw wz
      have hu := (Finset.mem_insert.mp hw).resolve_left wz
      exact other w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) (by rintro rfl; exact au hu)
    · obtain ⟨i,j,xi,xj,wi,wj,other⟩ := positive w
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem wu))
      refine ⟨i,j,xi,xj,wi,wj,?_⟩
      intro q hq qw
      rcases Finset.mem_insert.mp hq with rfl|qu
      · have ae := other a am (by rintro rfl; exact au wu)
        have be := other b bm (by rintro rfl; exact bu wu)
        simp only [bit_bin,ae,be]
      · exact other q (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem qu)) qw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def diffWords {x : Word} {c : Charts x} : List (Wire c) → Word × Word
  | [] => (0,0)
  | w::v =>
    let r := diffWords v
    let d := w.p ^^^ w.n
    (d ||| r.1,(d &&& r.1) ||| r.2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma df_bit {x : Word} {c : Charts x} (v : List (Wire c)) (i : Fin 512) :
    (∀ w ∈ v, bit (w.p ^^^ w.n) i=true → bit (diffWords v).1 i=true) ∧
    (∀ w ∈ v, ∀ u ∈ v, w.w≠u.w → bit (w.p ^^^ w.n) i=true → bit (u.p ^^^ u.n) i=true →
      bit (diffWords v).2 i=true) := by
  induction v with
  | nil => simp
  | cons h l ih =>
    obtain ⟨one,two⟩ := ih
    have bor (u z : Word) : bit (u ||| z) i = (bit u i || bit z i) := BitVec.getElem_or _
    have band (u z : Word) : bit (u &&& z) i = (bit u i && bit z i) := BitVec.getElem_and _
    simp only [diffWords,bor,band,Bool.or_eq_true,Bool.and_eq_true]
    constructor
    · intro w hw eq
      rcases List.mem_cons.mp hw with rfl|hw
      · exact Or.inl eq
      · exact Or.inr (one w hw eq)
    · intro w hw u hu ne pw pu
      rcases List.mem_cons.mp hw with rfl|hw
      · have ut := (List.mem_cons.mp hu).resolve_left (by rintro rfl; exact ne rfl)
        exact Or.inl ⟨pw,one u ut pu⟩
      rcases List.mem_cons.mp hu with rfl|hu
      · have tl : w∈l := (List.mem_cons.mp hw).resolve_left (by rintro rfl; exact ne rfl)
        exact Or.inl ⟨pu,one w tl pw⟩
      · exact Or.inr (two w hw u hu ne pw pu)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def allPositive {x : Word} {c : Charts x} (v : List (Wire c)) :=
  let single := ~~~(diffWords v).2
  v.all (fun w => (w.p &&& ~~~w.n &&& single) != 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma marked_word {q : Word} (n : q≠0) : ∃ i : Fin 512, bit q i=true := by
  by_contra! no
  apply n
  apply BitVec.eq_of_getElem_eq
  intro j h
  have z := no ⟨j,h⟩
  change bit q ⟨j,h⟩=bit 0 ⟨j,h⟩
  rw [bit_zero]
  cases eq : bit q ⟨j,h⟩ <;> simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma positive_checked {x : Word} {c : Charts x} {v : List (Wire c)}
    (ok : allPositive v=true) : Positive x (wires v) := by
  intro a ha
  obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp ha
  have nz := List.all_eq_true.mp ok w hw
  obtain ⟨i,e⟩ := marked_word (bne_iff_ne.mp nz)
  have cast : bit (w.p &&& ~~~w.n &&& ~~~(diffWords v).2) i =
      ((bit w.p i && !bit w.n i) && !bit (diffWords v).2 i) := by
    simp only [bit,BitVec.getElem_and,BitVec.getElem_not]
  rw [cast] at e
  have ⟨a,e0⟩ := Bool.and_eq_true_iff.mp e
  have ⟨p,n⟩ := Bool.and_eq_true_iff.mp a
  have wn : bit w.n i=false := by simpa using n
  have wt : bit (w.p ^^^ w.n) i=true := by
    rw [show bit (w.p ^^^ w.n) i=(bit w.p i ^^ bit w.n i) from BitVec.getElem_xor _]
    simp [p,wn]
  refine ⟨c.p i,c.n i,c.hp i,c.hn i,(w.hp i) ▸ p,(w.hn i) ▸ wn,?_⟩
  intro u hu ne
  obtain ⟨z,hz,rfl⟩ := Step.mem_wires.mp hu
  rw [←z.hp i,←z.hn i]
  by_contra bad
  have dz : bit (z.p ^^^ z.n) i=true := by
    rw [show bit (z.p ^^^ z.n) i=(bit z.p i ^^ bit z.n i) from BitVec.getElem_xor _]
    cases e1 : bit z.p i <;> cases e2 : bit z.n i <;> simp_all
  have h2 := (df_bit v i).2 w hw z hz ne.symm wt dz
  simp [h2] at e0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def positiveConflict {x : Word} {c : Charts x} (f : Frame c) :=
  (f.b+1==f.v.length) && ((f.t==0 || (f.t==1 && allPositive f.v)) && (flagFold f.v).ab != 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma positive_conflict {x : Word} {c : Charts x} {f : Frame c} (valid : f.Valid)
    (ok : positiveConflict f=true) : f.No := by
  obtain ⟨width,rest⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨tst,mask⟩ := Bool.and_eq_true_iff.mp rest
  have width := beq_iff_eq.mp width
  have no := certified_flags valid.1 width mask
  rcases Bool.or_eq_true_iff.mp tst with t|p
  · change ¬Exact x f.b f.t (wires f.v)
    rwa [beq_iff_eq.mp t]
  obtain ⟨one,positive⟩ := Bool.and_eq_true_iff.mp p
  have one := beq_iff_eq.mp one
  rintro ⟨b,hb,t,ht,h⟩
  have card : (wires f.v).card=f.v.length := by
    change (f.v.map Wire.w).toFinset.card=f.v.length
    rw [List.toFinset_card_of_nodup valid.1,List.length_map]
  have cap := count_live h
  have zero := tight_positive h (by omega) (by omega) (positive_checked positive)
  exact no ⟨b,hb,t,by omega,h⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full_raw {x b t S} (sens : Positive x S) (h : ¬Exact x b t S) :
    ¬Feasible x b t S := by
  rintro ⟨n,hn,j,hj,T,sub,live⟩
  have need : S⊆T := by
    intro a ha
    obtain ⟨i,k,pi,ni,_,_,only⟩ := sens a ha
    obtain ⟨w,hw,diff⟩ := exact_difference live pi ni
    by_contra miss
    have ne : w≠a := by rintro rfl; exact miss hw
    exact diff (only w (sub hw) ne)
  have eq := Finset.Subset.antisymm sub need
  exact h ⟨n,hn,j,hj,eq ▸ live⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def countConst {x : Word} {c : Charts x} (m : Word) : List (Wire c) → ℕ
  | [] => 0
  | a::l => if maskedConst m a.w then (countConst m l)+1 else countConst m l

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma count_const {x : Word} {c : Charts x} (f : Basis x) (v : List (Wire c)) :
    countConst f.mask v=loss f v := by
  induction v with
  | nil => rfl
  | cons a l ih =>
    cases e : maskedConst f.mask a.w <;> simp_all [countConst,loss,List.filter_cons]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cheapCut {x : Word} {c : Charts x} (b : ℕ) (v : List (Wire c)) (p : Price x) :=
  let need := p.basis.lo+countConst p.basis.mask v
  decide (b<need) && decide (b+p.spent<need)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cheap_sound_cut {x : Word} {c : Charts x} {b} {v : List (Wire c)} {p : Price x}
    (ok : cheapCut b v p=true) : p.cuts b v=true := by
  have q := (Bool.and_eq_true_iff.mp ok).2
  simpa only [Price.cuts,count_const] using q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Cheap {x : Word} {c : Charts x} (known : Frame c → Bool) : ℕ → Frame c → Bool
  | 0,f => f.ps.any (cheapCut f.b f.v) || known f
  | k+1,f => f.ps.any (cheapCut f.b f.v) ||
      (!(f.v.any (fun a => a.w == x)) && scan f (Cheap known k))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cheap_cut {x : Word} {c : Charts x} {f : Frame c} (v : f.Valid)
    (h : f.ps.any (cheapCut f.b f.v)=true) : f.No := by
  obtain ⟨p,hp,hc⟩ := List.any_eq_true.mp h
  exact cut_sound v.1 (v.2 _ hp) (cheap_sound_cut hc)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cheap_sound {x : Word} {c : Charts x} (known : Frame c → Bool) (good : ∀ f, known f=true → f.No)
    (hx : proper x) (d : ℕ) {f : Frame c} (valid : f.Valid) (ok : Cheap known d f = true) : f.No := by
  induction d generalizing f with
  | zero =>
    rcases Bool.or_eq_true_iff.mp ok with h|h
    · exact cheap_cut valid h
    · exact good _ h
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp ok with h|q
    · exact cheap_cut valid h
    obtain ⟨no,rows⟩ := Bool.and_eq_true_iff.mp q
    intro hex
    rcases descend c hx hex with hm | ⟨s,hs,el,ht⟩
    · obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      have yes : f.v.any (fun a => a.w == x) = true := List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩
      simp [yes] at no
    · exact ih (Frame.child_valid valid el (Step.all_legal hs)) (scan_sound rows valid.1 hs el ht) ht

-- The three coverage counters follow the construction in the Petersen parent proof.
abbrev Cov := Word × Word × Word

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def addCov (z : Word) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def takeOne (c : Cov) (a : Word) : Word := c.1 &&& ~~~(c.2.1 &&& a)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def takeTwo (c : Cov) (a b : Word) : Word :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cov_one (c : Cov) (a : Word) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cov_two (c : Cov) (a b : Word) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma add_swap (c : Cov) (a b : Word) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def accumCov {x : Word} {c : Charts x} (t : ℕ) : List (Wire c) → Cov
  | [] => (0,0,0)
  | a::rest => addCov (a.sep t) (accumCov t rest)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cov_permute {x : Word} {c : Charts x} (t : ℕ) {u v : List (Wire c)} (p : u.Perm v) : accumCov t u=accumCov t v := by
  induction p with
  | nil => rfl
  | cons a _ h => exact congrArg (addCov (a.sep t)) h
  | swap a b t => exact add_swap ..
  | trans _ _ a b => exact a.trans b
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cov_first {x : Word} {c : Charts x} (t : ℕ) (v : List (Wire c)) : (accumCov t v).1=cover t v := by
  induction v with
  | nil => rfl
  | cons a v ih => change a.sep t ||| (accumCov t v).1= _; rw [ih]; rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma wire_injective {x : Word} {c : Charts x} : Function.Injective (Wire.w (c:=c)) := by
  intro a b e
  have pe:a.p=b.p := by
    apply BitVec.eq_of_getElem_eq; intro j hj
    change bit a.p ⟨j,hj⟩=bit b.p ⟨j,hj⟩; rw [a.hp,b.hp,e]
  have ne:a.n=b.n := by
    apply BitVec.eq_of_getElem_eq; intro j hj
    change bit a.n ⟨j,hj⟩=bit b.n ⟨j,hj⟩; rw [a.hn,b.hn,e]
  cases a; cases b; simp_all
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_single {x : Word} {c : Charts x} {a : Wire c} {v : List (Wire c)} (nd : v.Nodup) (ha : a∈v) : v.Perm (a::alone a v) := by
  classical
  have p:=List.perm_cons_erase ha
  rw [nd.erase_eq_filter] at p
  have filt : v.filter (fun w=>w != a)=alone a v := by
    apply List.filter_congr; intro w _
    by_cases e:w=a
    · simp [e]
    · have h : w.w≠a.w := fun z=>e (wire_injective z)
      simp [bne_iff_ne.mpr e,bne_iff_ne.mpr h]
  rwa [filt] at p
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cov_alone {x : Word} {c : Charts x} {a : Wire c} {v : List (Wire c)} (t : ℕ)
    (nd : (v.map Wire.w).Nodup) (ha : a∈v) : takeOne (accumCov t v) (a.sep t)=cover t (alone a v) := by
  rw [cov_permute t (split_single (List.Nodup.of_map _ nd) ha)]
  exact (cov_one ..).trans (cov_first ..)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cov_aside {x : Word} {c : Charts x} {a b : Wire c} {v : List (Wire c)} (t : ℕ)
    (nd : (v.map Wire.w).Nodup) (ha : a∈v) (hb : b∈v) (ab : a.w.toNat<b.w.toNat) :
    takeTwo (accumCov t v) (a.sep t) (b.sep t)=cover t (aside a b v) := by
  have vnd:=List.Nodup.of_map _ nd
  have neq : b.w≠a.w := by intro eq; simp [eq] at ab
  have bm : b∈alone a v := List.mem_filter.mpr ⟨hb,bne_iff_ne.mpr neq⟩
  have perm := (split_single vnd ha).trans ((split_single (vnd.filter _) bm).cons a)
  have eq : alone b (alone a v)=aside a b v := by
    simp only [alone,aside,List.filter_filter]; apply List.filter_congr; intro w _; exact Bool.and_comm ..
  rw [cov_permute t perm,←eq]
  exact (cov_two ..).trans (cov_first ..)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def coveredScan {x : Word} {c : Charts x} (f : Frame c) (next : Frame c → Bool) :=
  let len := f.v.length
  let test := fun (s : Step c) (budget : ℕ) (bits : Word) =>
    decide (budget+1+s.drops < len+1) || bits != top || !isEligible s f.v || next (f.child s)
  f.v.all (fun a =>
    ((f.t==0) ||
      (let t := f.t-1
       let r := takeOne (accumCov t f.v) (a.sep t)
       let g := a.flip.sep t
       test (.flip a false) f.b (g ||| r) && test (.flip a true) f.b (g ||| (a.sep t ||| r)))) &&
    ((f.b==0) || f.v.all (fun w => !(decide (a.w.toNat < w.w.toNat)) ||
      (let r := takeTwo (accumCov f.t f.v) (a.sep f.t) (w.sep f.t)
       let wa := a.sep f.t
       let wb := w.sep f.t
       [false,true].all (fun d =>
         let g := (a.binary d w).sep f.t
         [false,true].all (fun ka => [false,true].all (fun kb =>
           test (.binary d a w ka kb) (f.b-1) (g ||| addSep ka wa (addSep kb wb r)))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma covered_sound {x : Word} {c : Charts x} {f : Frame c} {s : Step c} {next : Frame c → Bool}
    (h : coveredScan f next = true) (nd : (f.v.map Wire.w).Nodup)
    (hs : s ∈ Step.all f.b f.t f.v) (el : eligible f.v s)
    (ht : Exact x (s.budget f.b f.t).1 (s.budget f.b f.t).2 (wires (s.after f.v))) :
    next (f.child s)=true := by
  have fit := fits_step f.v s nd el ht
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hs
  have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)
  rcases List.mem_append.mp hm with hu|hb
  · split at hu
    · contradiction
    rename_i tpos
    have q := Bool.and_eq_true_iff.mp ((Bool.or_eq_true_iff.mp hh.1).resolve_left
      (by simpa only [beq_iff_eq] using tpos))
    rw [cov_alone _ nd ha] at q
    rcases List.mem_cons.mp hu with rfl|hu
    · have eq := cover_unary false ht
      change f.v.length+1 ≤ f.b+1+_ at fit
      simp only [Step.budget,addSep,Bool.false_eq_true,ite_false] at eq
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using q.1
    · obtain rfl := List.mem_singleton.mp hu
      have eq := cover_unary true ht
      change f.v.length+1 ≤ f.b+1+_ at fit
      simp only [Step.budget,addSep,ite_true] at eq
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using q.2
  · split at hb
    · contradiction
    rename_i bpos
    have q := (Bool.or_eq_true_iff.mp hh.2).resolve_left (by simpa only [beq_iff_eq] using bpos)
    obtain ⟨w,hw,hm⟩ := List.mem_flatMap.mp hb
    split at hm
    · rename_i lt
      have gate := (Bool.or_eq_true_iff.mp (List.all_eq_true.mp q w hw)).resolve_left (by simp [lt])
      rw [cov_aside _ nd ha hw lt] at gate
      obtain ⟨d,hd,h⟩ := List.mem_flatMap.mp hm
      obtain ⟨ka,hka,h⟩ := List.mem_flatMap.mp h
      obtain ⟨kb,hkb,rfl⟩ := List.mem_map.mp h
      have val := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp gate d hd) ka hka) kb hkb
      have eq := cover_binary d ka kb ht
      simp only [Step.budget] at eq
      change f.v.length+1 ≤ f.b-1+1+_ at fit
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using val
    · contradiction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
inductive ReadTree
  | atom (w : Word) (inv : Bool)
  | gate (d : Bool) (a b : ReadTree)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def signedWord (w : Word) (inv : Bool) := if inv then ~~~w else w
namespace ReadTree
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def value : ReadTree → Word
  | atom w i => signedWord w i
  | gate d a b => combine d a.value b.value

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hits (w : Word) : ReadTree → ℕ
  | atom a _ => if a=w then 1 else 0
  | gate _ a b => a.hits w + b.hits w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def has (w : Word) (i : Bool) : ReadTree → Prop
  | atom a j => a=w ∧ j=i
  | gate _ a b => a.has w i ∨ b.has w i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma has_hit {t : ReadTree} {w i} (h : t.has w i) : 0<t.hits w := by
  induction t with
  | atom a j => obtain ⟨rfl,_⟩ := h; simp [hits]
  | gate d a b ia ib => rcases h with h|h <;> simp only [hits] <;> first | have := ia h; omega | have := ib h; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma one_sign (t : ReadTree) {w i j} (n : t.hits w ≤ 1) (p : t.has w i) (q : t.has w j) : i=j := by
  induction t with
  | atom a k => exact p.2.symm.trans q.2
  | gate d a b ai bi =>
    change a.hits w+b.hits w≤1 at n
    rcases p with p|p <;> rcases q with q|q
    · exact ai (by omega) p q
    · have := has_hit p; have := has_hit q; omega
    · have := has_hit p; have := has_hit q; omega
    · exact bi (by omega) p q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def splice (u : Word) (f : Bool → ReadTree) : ReadTree → ReadTree
  | atom a i => if a=u then f i else atom a i
  | gate d a b => gate d (a.splice u f) (b.splice u f)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma splice_value (t : ReadTree) (u : Word) (f : Bool → ReadTree)
    (ok : ∀ i, (f i).value=signedWord u i) : (t.splice u f).value=t.value := by
  induction t with
  | atom a i => by_cases e:a=u <;> simp [splice,value,e,ok]
  | gate d a b ia ib => simp only [splice,value,ia,ib]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma splice_hits (t : ReadTree) (u w : Word) (f : Bool → ReadTree) (m : ℕ)
    (ok : ∀ i, (f i).hits w=m) : (t.splice u f).hits w =
      (if w=u then 0 else t.hits w) + t.hits u*m := by
  induction t with
  | atom a i => cases i <;> by_cases e : a=u <;> by_cases q : w=u <;> simp_all [splice,hits,eq_comm] <;> omega
  | gate d a b ia ib =>
    simp only [splice,hits,ia,ib,Nat.add_mul]
    split <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma separating (t : ReadTree) (i j : Fin 512) (p : bit t.value i=true) (q : bit t.value j=false) :
    ∃ w s, t.has w s ∧ bit (signedWord w s) i=true ∧ bit (signedWord w s) j=false := by
  induction t with
  | atom w s => exact ⟨w,s,⟨rfl,rfl⟩,p,q⟩
  | gate d a b ia ib =>
    simp only [value,bit_bin] at p q
    have aux : (bit a.value i=true ∧ bit a.value j=false) ∨ (bit b.value i=true ∧ bit b.value j=false) := by
      cases d <;> cases h : bit a.value i <;> cases h' : bit a.value j <;> simp_all
    rcases aux with h|h
    · obtain ⟨w,s,z,e₁,e₂⟩ := ia h.1 h.2; exact ⟨w,s,Or.inl z,e₁,e₂⟩
    · obtain ⟨w,s,z,e₁,e₂⟩ := ib h.1 h.2; exact ⟨w,s,Or.inr z,e₁,e₂⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma marks (t : ReadTree) (p : TracePoint) (A B : Word) (ca : t.hits A≤1) (cb : t.hits B≤1)
    (ok : ∀ w s, t.has w s → allowed (w==A) (w==B) (p.sig (signedWord w s))=true) :
    allowed (decide (0<t.hits A)) (decide (0<t.hits B)) (p.sig t.value)=true := by
  induction t with
  | atom w s =>
    have eq (X : Word) : decide (0 < (ReadTree.atom w s).hits X) = (w==X) := by
      by_cases e : w=X
      · simp [hits,e]
      · simp [hits,e,beq_eq_false_iff_ne.mpr e]
    rw [eq,eq]; exact ok w s ⟨rfl,rfl⟩
  | gate d a b ia ib =>
    change a.hits A+b.hits A≤1 at ca; change a.hits B+b.hits B≤1 at cb
    have la := ia (by omega) (by omega) (fun w s h=>ok w s (Or.inl h))
    have lb := ib (by omega) (by omega) (fun w s h=>ok w s (Or.inr h))
    have one (j k : ℕ) (e : j+k≤1) : (decide (0<j) && decide (0<k))=false := by simp; omega
    have pos (j k : ℕ) : decide (0<j+k)=(decide (0<j)||decide (0<k)) := by
      by_cases hj : 0<j <;> by_cases hk : 0<k <;> simp_all <;> omega
    change allowed (decide (0<a.hits A+b.hits A)) (decide (0<a.hits B+b.hits B)) (p.sig (combine d a.value b.value))=true
    rw [pos,pos,sig_combine]
    exact allowed_join _ _ _ _ _ _ d (one _ _ ca) (one _ _ cb) la lb
end ReadTree

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def deMorgan (d i : Bool) (a b : Word) :=
  ReadTree.gate (d ^^ i) (.atom a i) (.atom b i)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma deMorgan_value (d i : Bool) (a b : Word) : (deMorgan d i a b).value=signedWord (combine d a b) i := by
  cases d <;> cases i <;> simp [deMorgan,ReadTree.value,signedWord,combine]
  all_goals apply BitVec.eq_of_getElem_eq; intro j hj; simp [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Once (x : Word) (S : Finset Word) := ∃ t : ReadTree, t.value=x ∧ ∀ w, t.hits w=if w∈S then 1 else 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma once_of_tight {x n k S} (h : Live x n k S) (width : S.card=n+1) : Once x S := by
  induction h with
  | done => exact ⟨.atom x false,rfl,by intro w; by_cases e:x=w <;> simp_all [ReadTree.hits,eq_comm]⟩
  | @unary n k U a ha fresh tail ih =>
    have zu : ~~~a∉U := fun h=>fresh (Finset.mem_insert_of_mem h)
    have cnt:=count_live tail
    rw [Finset.card_insert_of_notMem zu] at cnt
    have au : a∉U := by rintro eh; rw [Finset.insert_eq_of_mem eh] at width; omega
    obtain ⟨t,eq,ht⟩ := ih (by rw [Finset.card_insert_of_notMem au] at width; rw [Finset.card_insert_of_notMem zu]; omega)
    let f := fun i => ReadTree.atom a (!i)
    refine ⟨t.splice (~~~a) f,(t.splice_value _ f (fun i=>by cases i <;> simp [f,ReadTree.value,signedWord])).trans eq,?_⟩
    intro w
    rw [t.splice_hits (~~~a) w f (if a=w then 1 else 0) (by intro i; rfl),ht,ht]
    have az : ~~~a≠a := fun e=>fresh (Finset.mem_insert.mpr (Or.inl e))
    by_cases e : w=a <;> by_cases z : w = ~~~a <;> simp_all [eq_comm]
  | @binary n k U a b d ha hb ab fresh tail ih =>
    let z:=combine d a b
    have zu : z∉U := fun h=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    obtain ⟨au,bu,tw⟩ := tight_parts ab fresh tail width
    obtain ⟨t,eq,ht⟩ := ih tw
    let f:=fun i=>deMorgan d i a b
    refine ⟨t.splice z f,(t.splice_value z f (fun i=>deMorgan_value ..)).trans eq,?_⟩
    intro w
    rw [t.splice_hits z w f ((if a=w then 1 else 0)+(if b=w then 1 else 0)) (by intro i; rfl),ht,ht]
    have za : z≠a := fun e=>fresh (Finset.mem_insert.mpr (Or.inl e))
    have zb : z≠b := fun e=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e)))
    change _ + (if z∈insert z U then _ else _)*_=_
    by_cases e : w=a <;> by_cases g : w=b <;> by_cases q : w=z <;> simp_all [eq_comm,z]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def maskFold {x : Word} {c : Charts x} (gray left right : Wire c→Patch) : List (Wire c) → Flags
  | [] => ⟨BitVec.allOnes 36,0,0,0⟩
  | w::v =>
    let f := maskFold gray left right v
    let g := gray w
    let a := left w
    let b := right w
    ⟨g &&& f.grey,(g &&& f.a) ||| (a &&& f.grey),(g &&& f.b) ||| (b &&& f.grey),
      (g &&& f.ab) ||| (a &&& f.b) ||| (b &&& f.a)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def MaskGrey {x : Word} {c : Charts x} (gray : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∀ w∈v, (gray w)[k.val]=true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def MaskOne {x : Word} {c : Charts x} (gray : Wire c→Patch) (mark : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∃ a∈v, (mark a)[k.val]=true ∧ ∀ w∈v, w.w≠a.w → (gray w)[k.val]=true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def MaskTwo {x : Word} {c : Charts x} (gray : Wire c→Patch) (ma mb : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∃ a∈v, ∃ b∈v, a.w≠b.w ∧ (ma a)[k.val]=true ∧ (mb b)[k.val]=true ∧
    ∀ w∈v, w.w≠a.w → w.w≠b.w → (gray w)[k.val]=true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_next {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c}
    (h : (gray w)[k.val]=true) (hg : MaskGrey gray k v) : MaskGrey gray k (w::v) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_onegrey {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c} {mark}
    (h : (gray w)[k.val]=true) (hg : MaskOne gray mark k v) : MaskOne gray mark k (w::v) := by
  obtain ⟨a,ha,hm,hg⟩ := hg
  refine ⟨a,List.mem_cons_of_mem _ ha,hm,?_⟩
  intro q hq nq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq nq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_onepick {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c} {mark : Wire c→Patch}
    (h : (mark w)[k.val]=true) (hg : MaskGrey gray k v) : MaskOne gray mark k (w::v) := by
  refine ⟨w,List.mem_cons_self,h,?_⟩
  intro q hq nq
  exact hg q ((List.mem_cons.mp hq).resolve_left (by rintro rfl; exact nq rfl))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_twogrey {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c} {ma mb}
    (h : (gray w)[k.val]=true) (hg : MaskTwo gray ma mb k v) : MaskTwo gray ma mb k (w::v) := by
  obtain ⟨a,ha,b,hb,ne,pa,pb,hg⟩ := hg
  refine ⟨a,List.mem_cons_of_mem _ ha,b,List.mem_cons_of_mem _ hb,ne,pa,pb,?_⟩
  intro q hq qa qb
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq qa qb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_twopick {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c} {ma mb : Wire c→Patch}
    (nw : w.w∉wires v) (h : (ma w)[k.val]=true) (hg : MaskOne gray mb k v) : MaskTwo gray ma mb k (w::v) := by
  obtain ⟨a,ha,pa,hg⟩ := hg
  have ne : w.w≠a.w := fun eq => nw (Step.mem_wires.mpr ⟨a,ha,eq.symm⟩)
  refine ⟨w,List.mem_cons_self,a,List.mem_cons_of_mem _ ha,ne,h,pa,?_⟩
  intro q hq qw qa
  exact hg q ((List.mem_cons.mp hq).resolve_left (by rintro rfl; exact qw rfl)) qa

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_swap {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {ma mb}
    (h : MaskTwo gray ma mb k v) : MaskTwo gray mb ma k v := by
  obtain ⟨a,ha,b,hb,n,pa,pb,hh⟩ := h
  exact ⟨b,hb,a,ha,n.symm,pb,pa,fun q hq qb qa => hh q hq qa qb⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mask_sound {x : Word} {c : Charts x} (gray left right : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) (nd : (v.map Wire.w).Nodup) :
    ((maskFold gray left right v).grey[k.val]=true → MaskGrey gray k v) ∧
    ((maskFold gray left right v).a[k.val]=true → MaskOne gray left k v) ∧
    ((maskFold gray left right v).b[k.val]=true → MaskOne gray right k v) ∧
    ((maskFold gray left right v).ab[k.val]=true → MaskTwo gray left right k v) := by
  induction v with
  | nil => simp [MaskGrey,maskFold]
  | cons w l ih =>
    obtain ⟨nw,nl⟩ := List.nodup_cons.mp nd
    have nm : w.w∉wires l := fun hh => nw (List.mem_toFinset.mp hh)
    obtain ⟨ig,ia,ib,iab⟩ := ih nl
    simp only [maskFold,BitVec.getElem_and,BitVec.getElem_or,Bool.and_eq_true,Bool.or_eq_true]
    refine ⟨fun ⟨wG,g⟩ => mask_next wG (ig g),?_,?_,?_⟩
    · rintro (⟨wg,a⟩|⟨wa,g⟩)
      · exact mask_onegrey wg (ia a)
      · exact mask_onepick wa (ig g)
    · rintro (⟨wg,b⟩|⟨wb,g⟩)
      · exact mask_onegrey wg (ib b)
      · exact mask_onepick wb (ig g)
    · rintro ((⟨wg,ab⟩|⟨wa,b⟩)|⟨wb,a⟩)
      · exact mask_twogrey wg (iab ab)
      · exact mask_twopick nm wa (ib b)
      · exact mask_swap (mask_twopick nm wb (ia a))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def turned {x : Word} {c : Charts x} (w : Wire c) (s : Bool) : Wire c := if s then w.flip else w
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma turned_word {x : Word} {c : Charts x} (w : Wire c) (s : Bool) : (turned w s).w=signedWord w.w s := by cases s <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def adverse {x : Word} {c : Charts x} (single : Word) (w : Wire c) (s : Bool) :=
  let a:=turned w s
  (a.n &&& ~~~a.p &&& single) != 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pairedMask {x : Word} {c : Charts x} (single : Word) (m : Wire c→Patch) (w : Wire c) :=
  (if adverse single w false then BitVec.allOnes 36 else m w) &&&
  (if adverse single w true then BitVec.allOnes 36 else m w.flip)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma paired_bit {x : Word} {c : Charts x} {w : Wire c} {single : Word} {k : Fin 36}
    {m : Wire c→Patch} {s : Bool} (h : (pairedMask single m w)[k.val]=true)
    (go : adverse single w s=false) : (m (turned w s))[k.val]=true := by
  rw [pairedMask,BitVec.getElem_and,Bool.and_eq_true] at h
  cases s
  · simpa only [go,Bool.false_eq_true,ite_false,turned] using h.1
  · simpa only [go,Bool.false_eq_true,ite_false,turned,ite_true] using h.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma turns_diff {x : Word} {c : Charts x} {w : Wire c} {s : Bool} {i : Fin 512}
    (dif : bit (signedWord w.w s) (c.p i) ≠ bit (signedWord w.w s) (c.n i)) :
    bit (w.p ^^^ w.n) i=true := by
  rw [show bit (w.p ^^^ w.n) i=(bit w.p i ^^ bit w.n i) from BitVec.getElem_xor _,w.hp,w.hn]
  cases s <;> cases a : bit w.w (c.p i) <;> cases b : bit w.w (c.n i) <;>
    simp_all [signedWord,bit_not]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sign_used {x : Word} {c : Charts x} {v : List (Wire c)} {t : ReadTree} (val : t.value=x)
    (hits : ∀ w, t.hits w=if w∈wires v then 1 else 0) {w : Wire c} (hw : w∈v) {s : Bool}
    (used : t.has w.w s) : adverse (~~~(diffWords v).2) w s=false := by
  by_contra! fail
  have neq : ((turned w s).n &&& ~~~(turned w s).p &&& ~~~(diffWords v).2)≠0 := bne_iff_ne.mp (Bool.eq_true_of_not_eq_false fail)
  obtain ⟨i,fi⟩ := marked_word neq
  have detail : (bit (turned w s).n i && !bit (turned w s).p i && !bit (diffWords v).2 i)=true := by simpa only [bit,BitVec.getElem_and,BitVec.getElem_not] using fi
  obtain ⟨first,unique⟩ := Bool.and_eq_true_iff.mp detail
  obtain ⟨down,nup⟩ := Bool.and_eq_true_iff.mp first
  have up : bit (signedWord w.w s) (c.p i)=false := by simpa only [←turned_word,(turned w s).hp,Bool.not_eq_true'] using nup
  have dn : bit (signedWord w.w s) (c.n i)=true := by simpa only [←turned_word,(turned w s).hn] using down
  obtain ⟨a,j,here,pa,na⟩ := t.separating (c.p i) (c.n i) (val ▸ c.hp i) (val ▸ c.hn i)
  by_cases eq : a=w.w
  · subst a
    have jm := t.one_sign (by rw [hits]; split <;> omega) here used
    simp [jm,up] at pa
  · have present : a∈wires v := by
      have q:=ReadTree.has_hit here; by_contra hm; simp [hits,hm] at q
    obtain ⟨u,hu,rfl⟩ := Step.mem_wires.mp present
    have d1:=turns_diff (w:=u) (s:=j) (i:=i) (by simp [pa,na])
    have d2:=turns_diff (w:=w) (s:=s) (i:=i) (by simp [up,dn])
    have two := (df_bit v i).2 u hu w hw eq d1 d2
    simp [two] at unique

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def signCut {x : Word} {c : Charts x} (f : Frame c) :=
  f.b+1==f.v.length &&
    (let single:= ~~~(diffWords f.v).2
     let m:=pairedMask single
     (maskFold (m pGrey) (m pLeft) (m pRight) f.v).ab != 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sign_cut {x : Word} {c : Charts x} {f : Frame c} (valid : f.Valid) (cut : signCut f=true) : f.No := by
  obtain ⟨width,hit⟩ := Bool.and_eq_true_iff.mp cut
  have width:=beq_iff_eq.mp width
  rintro ⟨n,hn,j,hj,live⟩
  have len : (wires f.v).card=f.v.length := by
    change (f.v.map Wire.w).toFinset.card=f.v.length
    rw [List.toFinset_card_of_nodup valid.1,List.length_map]
  have cap:=count_live live
  obtain ⟨t,val,hits⟩ := once_of_tight live (by omega)
  let single:= ~~~(diffWords f.v).2
  let m:=pairedMask (c:=c) single
  obtain ⟨k,hk⟩ := uncovered (bne_iff_ne.mp hit)
  obtain ⟨a,ha,z,hz,nz,pa,pz,gy⟩ := (mask_sound (m pGrey) (m pLeft) (m pRight) k f.v valid.1).2.2.2 hk
  have ah : t.hits a.w=1 := by rw [hits,if_pos (Step.mem_wires.mpr ⟨a,ha,rfl⟩)]
  have zh : t.hits z.w=1 := by rw [hits,if_pos (Step.mem_wires.mpr ⟨z,hz,rfl⟩)]
  have allok := t.marks (patchPoint c k) a.w z.w ah.le zh.le (by
    intro w s hs
    have present : w∈wires f.v := by
      have q:=ReadTree.has_hit hs; by_contra h; simp [hits,h] at q
    obtain ⟨u,hu,rfl⟩ := Step.mem_wires.mp present
    have ok := sign_used val hits hu hs
    by_cases ua : u.w=a.w
    · rw [ua,beq_self_eq_true,beq_eq_false_iff_ne.mpr nz]
      have useA : t.has a.w s := ua ▸ hs
      have v := paired_bit pa (sign_used val hits ha useA)
      rw [←turned_word]
      exact legal_left _ ((patch_extract (turned a s) k).2.1 ▸ v)
    by_cases uz : u.w=z.w
    · rw [uz,beq_eq_false_iff_ne.mpr nz.symm,beq_self_eq_true]
      have useZ : t.has z.w s := uz ▸ hs
      have v := paired_bit pz (sign_used val hits hz useZ)
      rw [←turned_word]
      exact legal_right _ ((patch_extract (turned z s) k).2.2 ▸ v)
    · rw [beq_eq_false_iff_ne.mpr ua,beq_eq_false_iff_ne.mpr uz,←turned_word]
      have v := paired_bit (gy u hu ua uz) ok
      exact legal_grey _ ((patch_extract (turned u s) k).1 ▸ v))
  rw [val,patch_target,ah,zh] at allok
  exact (by decide : allowed true true 25 ≠ true) allok

noncomputable def permEquiv {x : Word} (a : Automorphism x) : Word ≃ Word :=
  Equiv.ofBijective a.p.q ⟨a.inj,Finite.surjective_of_injective a.inj⟩

noncomputable def Automorphism.back {x : Word} (a : Automorphism x) : Automorphism x := by
  let f := permEquiv a
  have inv (w : Word) : a.p.q (f.symm w)=w := f.apply_symm_apply w
  refine ⟨⟨f.symm,?_,?_⟩,?_,?_,f.symm.injective,?_⟩
  · intro w; apply a.inj; rw [inv,a.p.neg,inv]
  · intro d u v; apply a.inj; rw [inv,a.p.bin,inv,inv]
  · apply a.inj; rw [inv,a.zero]
  · apply a.inj; rw [inv,a.one]
  · apply a.inj; rw [inv,a.fix]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma Automorphism.back_q {x : Word} (a : Automorphism x) (w : Word) : a.back.p.q (a.p.q w)=w := by
  change (permEquiv a).symm (permEquiv a w)=w
  exact Equiv.symm_apply_apply ..
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma Automorphism.reflect {x : Word} (a : Automorphism x) {b t S} (h : Exact x b t (S.image a.p.q)) : Exact x b t S := by
  have r:=a.back.map_exact h
  have eq : (S.image a.p.q).image a.back.p.q=S := by ext w; simp [Finset.mem_image,a.back_q]
  rwa [eq] at r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def fromOrbit {x : Word} {c : Charts x} (root : Frame c) (depth tape : ℕ) (a : Rotation root) (f : Frame c) :=
  (root.replay depth tape).any (fun g=>f.b==g.b && f.t==g.t && (bareReplay a.base depth tape).isPerm (f.v.map Wire.w))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma orbit_hit {x : Word} {c : Charts x} {root f : Frame c} {depth tape} {a : Rotation root}
    (good : ∀ g, root.replay depth tape=some g → g.No) (hit : fromOrbit root depth tape a f=true) : f.No := by
  obtain ⟨g,eg,h⟩ := (Option.any_eq_true ..).1 hit
  obtain ⟨⟨b,t⟩,pm⟩ := (Bool.and_eq_true_iff.mp h).imp_left Bool.and_eq_true_iff.mp
  have eq : (wires g.v).image a.R.p.q=wires f.v := by
    have words : bareReplay a.base depth tape=(g.v.map Wire.w).map a.R.p.q := by
      rw [a.eq,project_tape,←replay_words eg]
    ext z
    have p := (List.isPerm_iff.mp pm).mem_iff (a:=z)
    rw [words] at p
    simpa only [wires,List.mem_toFinset,List.mem_map,Finset.mem_image] using p
  intro he
  apply good g eg
  apply a.R.reflect
  rw [eq,←beq_iff_eq.mp b,←beq_iff_eq.mp t]
  exact he

abbrev Rows := Array (Array ℕ)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def fetchRow (r : Rows) (i : ℕ) := ((r[i/24]?).getD #[])[Nat.mod i 24]?.getD 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def tapeAt (r : Rows) (d i : ℕ) := Nat.mod (fetchRow r i) (2^(12*d))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Region {x : Word} {c : Charts x} (root : Frame c) (d num : ℕ) (r : Rows) :=
  ∀ j<num, ∀ g, root.replay d (tapeAt r d j)=some g → g.No

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def glimpse {x : Word} {c : Charts x} (f : Frame c) :=
  Nat.mod (f.v.foldl (fun acc w=>acc+w.w.toNat) (f.b+17*f.t)) 4093

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def linkBits {x : Word} {c : Charts x} (root : Frame c) (next : Rows) (rot : Array (Rotation root))
    (d num key : ℕ) (f : Frame c) : ℕ→ℕ→Bool
  | 0,_ => false
  | cnt+1,blob =>
    if blob=0 then false else
      (let h:=blob &&& 0xfffffff
       let idx:=h >>> 16
       h &&& 4095 == key && decide (idx<num) &&
         (rot[(h >>> 12) &&& 15]?).any (fun a=>fromOrbit root d (tapeAt next d idx) a f)) ||
      linkBits root next rot d num key f cnt (blob >>> 28)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma links_valid {x : Word} {c : Charts x} {root f : Frame c} {r : Rows} {rot} {d num key blob cnt}
    (good : Region root d num r) (hit : linkBits root r rot d num key f cnt blob=true) : f.No := by
  induction cnt generalizing blob with
  | zero => contradiction
  | succ n ih =>
    simp only [linkBits] at hit
    split at hit
    · contradiction
    rcases Bool.or_eq_true_iff.mp hit with use|go
    · obtain ⟨⟨_,idx⟩,q⟩ := (Bool.and_eq_true_iff.mp use).imp_left Bool.and_eq_true_iff.mp
      obtain ⟨a,_,h⟩ := (Option.any_eq_true ..).1 q
      exact orbit_hit (good _ (of_decide_eq_true idx)) h
    · exact ih go

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selectPrices {x : Word} (ps : List (Price x)) : ℕ→ℕ→List (Price x)
  | 0,_ => []
  | n+1,blob => if blob=0 then [] else
      (ps[(blob &&& 15)-1]?).toList ++ selectPrices ps n (blob >>> 4)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prices_mem {x : Word} {ps : List (Price x)} {n blob p} (h : p∈selectPrices ps n blob) : p∈ps := by
  induction n generalizing blob with
  | zero => contradiction
  | succ n ih =>
    simp only [selectPrices] at h
    split at h
    · contradiction
    rcases List.mem_append.mp h with a|b
    · exact List.mem_of_getElem? (Option.mem_toList.mp a)
    · exact ih b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shapeCut {x : Word} {c : Charts x} (f : Frame c) :=
  if f.t=0 then tightConflict f else signCut f
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_sound {x : Word} {c : Charts x} {f : Frame c} (v : f.Valid) (h : shapeCut f=true) : f.No := by
  unfold shapeCut at h; split at h
  · exact tight_sound v h
  · exact sign_cut v h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def localClose {x : Word} {c : Charts x} (root : Frame c) (next : Rows) (rot : Array (Rotation root))
    (d num links : ℕ) (f : Frame c) :=
  f.ps.any (cheapCut f.b f.v) || shapeCut f ||
    (links != 0 && linkBits root next rot d num (glimpse f) f 100 links)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma local_close {x : Word} {c : Charts x} {root f : Frame c} {next : Rows} {rot d num links}
    (v : f.Valid) (gn : Region root d num next) (h : localClose root next rot d num links f=true) : f.No := by
  rcases Bool.or_eq_true_iff.mp h with h|h
  · rcases Bool.or_eq_true_iff.mp h with h|h
    · exact cheap_cut v h
    · exact shape_sound v h
  · exact links_valid gn (Bool.and_eq_true_iff.mp h).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def atlasRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (rows next : Rows)
    (num : ℕ) (rot : Array (Rotation root)) (i : ℕ) :=
  let pack:=fetchRow rows i >>> (12*d)
  (root.replay d (tapeAt rows d i)).all (fun f =>
    let g:Frame c:={f with ps:=selectPrices f.ps 10 (pack &&& 0xffffffffff)}
    !(g.v.any (fun w=>w.w==x)) && coveredScan g (localClose root next rot (d+1) num (pack >>> 40)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma atlas_sound {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (v : root.Valid)
    (d n num : ℕ) (rows next : Rows) (rot : Array (Rotation root))
    (gn : Region root (d+1) num next) (h : Span (atlasRow root d rows next num rot) 0 n) : Region root d n rows := by
  intro i hi f ef
  have good:=Frame.replay_valid v ef
  let pack:=fetchRow rows i >>> (12*d)
  let g:Frame c:={f with ps:=selectPrices f.ps 10 (pack &&& 0xffffffffff)}
  have gv : g.Valid:=⟨good.1,fun p hp=>good.2 p (prices_mem hp)⟩
  have ck:=h i (Nat.zero_le _) hi
  simp only [atlasRow,ef,Option.all_some] at ck
  obtain ⟨none,run⟩ := Bool.and_eq_true_iff.mp ck
  intro he
  rcases descend c hx he with hm|⟨s,hs,el,nxt⟩
  · obtain ⟨w,hw,eq⟩:=Step.mem_wires.mp hm
    have found : f.v.any (fun z=>z.w==x)=true:=List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr eq⟩
    simp [found] at none
  · have ok:=covered_sound (f:=g) run gv.1 hs el nxt
    exact local_close (Frame.child_valid gv el (Step.all_legal hs)) gn ok nxt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma whole {x : Word} {c : Charts x} {root : Frame c} {r : Rows}
    (h : Region root 0 1 r) : root.No := by
  exact h 0 (by decide) root rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root_choices {x : Word} {c : Charts x} (root : Frame c) (pivot : Word) (raw : List (Wire c))
    (rv : wires root.v=insert pivot (wires raw))
    (force : ∀ a∈wires raw, ∃ i j : Fin 512, bit x i=true ∧ bit x j=false ∧
      ∀ w∈wires root.v, w≠a → bit w i=bit w j)
    (wholeNo : root.No) (rawNo : ¬Feasible x root.b root.t (wires raw)) : ¬Feasible x root.b root.t (wires root.v) := by
  rintro ⟨n,hn,j,hj,T,sub,h⟩
  have allRaw : wires raw ⊆ T := by
    intro a ha
    obtain ⟨u,v,xu,xv,only⟩:=force a ha
    obtain ⟨z,hz,d⟩:=exact_difference h xu xv
    by_contra miss
    exact d (only z (sub hz) (by rintro rfl; exact miss hz))
  by_cases use:pivot∈T
  · have eq : wires root.v=T := Finset.Subset.antisymm (rv ▸ Finset.insert_subset use allRaw) sub
    exact wholeNo ⟨n,hn,j,hj,eq ▸ h⟩
  · apply rawNo
    refine ⟨n,hn,j,hj,T,?_,h⟩
    intro w hw
    have ins : w ∈ insert pivot (wires raw) := rv ▸ sub hw
    exact (Finset.mem_insert.mp ins).resolve_left (fun e=>use (e ▸ hw))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def forcedExcept {x : Word} {c : Charts x} (v raw : List (Wire c)) :=
  let single:= ~~~(diffWords v).2
  raw.all (fun w=>(w.p &&& ~~~w.n &&& single) != 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma forced_except {x : Word} {c : Charts x} {v raw : List (Wire c)} (inc : ∀ w∈raw, w∈v)
    (ck : forcedExcept v raw=true) (a) (ha : a∈wires raw) :
    ∃ i j : Fin 512, bit x i=true ∧ bit x j=false ∧ ∀ w∈wires v, w≠a → bit w i=bit w j := by
  obtain ⟨w,hw,rfl⟩:=Step.mem_wires.mp ha
  obtain ⟨i,hi⟩:=marked_word (bne_iff_ne.mp (List.all_eq_true.mp ck w hw))
  have e : (bit w.p i && !bit w.n i && !bit (diffWords v).2 i)=true := by
    simpa only [bit,BitVec.getElem_and,BitVec.getElem_not] using hi
  obtain ⟨⟨pi,nn⟩,unique⟩:=(Bool.and_eq_true_iff.mp e).imp_left Bool.and_eq_true_iff.mp
  have wn : bit w.n i=false := by simpa using nn
  have dif : bit (w.p ^^^ w.n) i=true := by simp only [bit,BitVec.getElem_xor] at *; simp [pi,wn]
  refine ⟨c.p i,c.n i,c.hp i,c.hn i,?_⟩
  intro z hz ne
  obtain ⟨q,hq,rfl⟩ := Step.mem_wires.mp hz
  rw [←q.hp i,←q.hn i]
  by_contra bad
  have dd : bit (q.p ^^^ q.n) i=true := by
    rw [show bit (q.p ^^^ q.n) i=(bit q.p i ^^ bit q.n i) from BitVec.getElem_xor _]
    cases h : bit q.p i <;> cases k : bit q.n i <;> simp_all
  have since := (df_bit v i).2 q hq w (inc w hw) ne dd dif
  simp [since] at unique

-- Prove induced graph bounds in order, using previously proved smaller restrictions.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g0X : Word := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g0C : Charts g0X := ⟨unpack 0x180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c0603,unpack 0x8040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040401,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g0W0 : Wire g0C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g0W1 : Wire g0C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,2,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g0V := [g0W0,g0W1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g0proper : proper g0X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g0nd : (g0V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g0bound : ¬Feasible g0X 0 1 (wires g0V) := by
  apply full_raw (positive_checked (v:=g0V) (by decide +kernel))
  intro h
  have total := exact_size h
  have count : (wires g0V).card=2 := by decide +kernel
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g1X : Word := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g1C : Charts g1X := ⟨unpack 0x28140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a050281c0c06030140a05,unpack 0x80402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080c0803010100601,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g1W0 : Wire g1C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd3,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g1W1 : Wire g1C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x78,0x5a,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g1W2 : Wire g1C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x24,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g1V := [g1W0,g1W1,g1W2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g1proper : proper g1X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g1nd : (g1V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g1bound : ¬Feasible g1X 1 1 (wires g1V) := by
  apply full_raw (positive_checked (v:=g1V) (by decide +kernel))
  intro h
  have total := exact_size h
  have count : (wires g1V).card=3 := by decide +kernel
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2X : Word := 0xfca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0fca0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2C : Charts g2X := ⟨unpack 0x28140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a0e06830180c06030160b05028140a0501c0e05028140a05,unpack 0x80402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402060482410060200c1203048200c03010180609030100601,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2W0 : Wire g2C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe8307f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec7933,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2W1 : Wire g2C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x103fe0,0x1153ea,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2W2 : Wire g2C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc07f,0x11824c,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2W3 : Wire g2C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x1fff80,0xe2c10,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2V := [g2W0,g2W1,g2W2,g2W3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2proper : proper g2X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2nd : (g2V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2f0 : Basis g2X := basisFor g2X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g2V.map Wire.w) 2 (assignRows [9,0,1,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2f0valid : (Price.mk g2f0 0).Valid 1 (wires g2V) :=
  initial_price g1proper g1bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2f1 : Basis g2X := basisFor g2X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g2V.map Wire.w) 2 (assignRows [0,9,2,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2f1valid : (Price.mk g2f1 0).Valid 1 (wires g2V) :=
  initial_price g1proper g1bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2f2 : Basis g2X := basisFor g2X 0x5050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505 (g2V.map Wire.w) 1 (assignRows [9,0,9,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2f2valid : (Price.mk g2f2 0).Valid 1 (wires g2V) :=
  initial_price g0proper g0bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2f3 : Basis g2X := basisFor g2X 0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033 (g2V.map Wire.w) 1 (assignRows [0,9,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2f3valid : (Price.mk g2f3 0).Valid 1 (wires g2V) :=
  initial_price g0proper g0bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g2prices : List (Price g2X) := [⟨g2f0,0⟩,⟨g2f1,0⟩,⟨g2f2,0⟩,⟨g2f3,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g2valid : ∀ p ∈ g2prices, p.Valid 1 (wires g2V) := by
  intro p hp
  simp only [g2prices,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact g2f0valid
  · exact g2f1valid
  · exact g2f2valid
  · exact g2f3valid
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g2bound : ¬Feasible g2X 3 1 (wires g2V) := by
  apply verified g2C g2proper g2nd g2valid
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g4X : Word := 0xf888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888f888
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g4C : Charts g4X := ⟨unpack 0x180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c0603070381a0d06030180c06030160b0381c06030180c0603,unpack 0x8040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201050181205050241006028101409030141409030140401,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g4W0 : Wire g4C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff303ff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff34955,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g4W1 : Wire g4C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03ff,0xc92aa,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g4W2 : Wire g4C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffcc0,0x51ccc,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g4W3 : Wire g4C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xfff00,0xae330,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g4V := [g4W0,g4W1,g4W2,g4W3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g4proper : proper g4X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g4nd : (g4V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g4bound : ¬Feasible g4X 2 1 (wires g4V) := by
  apply full_raw (positive_checked (v:=g4V) (by decide +kernel))
  intro h
  have total := exact_size h
  have count : (wires g4V).card=4 := by decide +kernel
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g6X : Word := 0xfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g6C : Charts g6X := ⟨unpack 0x4824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120904824120f07034180c0602c140a050241209,unpack 0x80402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402070301410070200c1007010200e01,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g6W0 : Wire g6C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff447,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff553,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g6W1 : Wire g6C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x1878,0x195a,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g6W2 : Wire g6C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1f80,0x1d92,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g6W3 : Wire g6C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x224,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g6V := [g6W0,g6W1,g6W2,g6W3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g6proper : proper g6X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g6nd : (g6V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6bound : ¬Feasible g6X 2 1 (wires g6V) := by
  apply full_raw (positive_checked (v:=g6V) (by decide +kernel))
  intro h
  have total := exact_size h
  have count : (wires g6V).card=4 := by decide +kernel
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3X : Word := 0xfff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8fff8eca8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3C : Charts g3X := ⟨unpack 0x180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c381a0c86430180c06030180c0582c150a05028140a0502813098381c0d0682c140a05028140a0501c0a05028140a050280c06030180c0603,unpack 0x8040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008041812088242411080301208030480c1109044200c048180812088300c0c048242411060241006010182411060240c0400848220c048180401,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3W0 : Wire g3C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc01019c07fff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcd21488d414a9,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3W1 : Wire g3C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd00601e7fc07f,0x120e85221e246,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3W2 : Wire g3C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x2007fe7807f80,0x204a167094b14,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3W3 : Wire g3C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x3ff8007ff8000,0x2470185ce0c18,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3W4 : Wire g3C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x3fffff8000000,0x1b85e18303060,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3V := [g3W0,g3W1,g3W2,g3W3,g3W4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3proper : proper g3X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3nd : (g3V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f0 : Basis g3X := basisFor g3X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g3V.map Wire.w) 4 (assignRows [9,0,1,2,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f0valid : (Price.mk g3f0 0).Valid 1 (wires g3V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f1 : Basis g3X := basisFor g3X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g3V.map Wire.w) 4 (assignRows [0,9,2,1,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f1valid : (Price.mk g3f1 0).Valid 1 (wires g3V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f2 : Basis g3X := basisFor g3X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g3V.map Wire.w) 4 (assignRows [0,2,9,3,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f2valid : (Price.mk g3f2 0).Valid 1 (wires g3V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f3 : Basis g3X := basisFor g3X 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff (g3V.map Wire.w) 4 (assignRows [2,0,3,9,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f3valid : (Price.mk g3f3 0).Valid 1 (wires g3V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f4 : Basis g3X := basisFor g3X 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff (g3V.map Wire.w) 4 (assignRows [2,3,0,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f4valid : (Price.mk g3f4 0).Valid 1 (wires g3V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3prices : List (Price g3X) := [⟨g3f0,0⟩,⟨g3f1,0⟩,⟨g3f2,0⟩,⟨g3f3,0⟩,⟨g3f4,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3valid : ∀ p ∈ g3prices, p.Valid 1 (wires g3V) := by
  intro p hp
  simp only [g3prices,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  · exact g3f0valid
  · exact g3f1valid
  · exact g3f2valid
  · exact g3f3valid
  · exact g3f4valid
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g3bound : ¬Feasible g3X 6 1 (wires g3V) := by
  apply verified g3C g3proper g3nd g3valid
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g5X : Word := 0xfff0eca0fff0eca0fff0eca0fff0eca0fff0eca0fff0eca0fff0eca0fff0eca0fff0eca0fff0eca0fff0eca0fff0eca0fff0eca0fff0eca0fff0eca0fff0eca0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g5C : Charts g5X := ⟨unpack 0x28140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a05028140a1c0d86832190c06030180c0602e160b05428140a0502814070381a0d0582c140a05028140a0381c0a05028140a05,unpack 0x804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020c098482209098401809040182612030442610060240c040601818090480c260c048200c020300c260c048180801,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g5W0 : Wire g5C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb02403c0ff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb92641e869,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g5W1 : Wire g5C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xc0380cffc0,0xc87a2463e4,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g5W2 : Wire g5C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff003fff00ff,0x10248be1296,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g5W3 : Wire g5C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x1ffc00fff00,0x11380cb9c18,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g5W4 : Wire g5C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x1fffff00000,0xec37002020,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g5V := [g5W0,g5W1,g5W2,g5W3,g5W4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g5proper : proper g5X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g5nd : (g5V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g5f0 : Basis g5X := basisFor g5X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g5V.map Wire.w) 4 (assignRows [9,0,1,2,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g5f0valid : (Price.mk g5f0 0).Valid 1 (wires g5V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5bound : ¬Feasible g5X 4 1 (wires g5V) := by
  apply full_raw (positive_checked (v:=g5V) (by decide +kernel))
  exact cut_sound g5nd g5f0valid (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g7X : Word := 0xfffcaa00fffcaa00fffcaa00fffcaa00fffcaa00fffcaa00fffcaa00fffcaa00fffcaa00fffcaa00fffcaa00fffcaa00fffcaa00fffcaa00fffcaa00fffcaa00
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g7C : Charts g7X := ⟨unpack 0x482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090f07034190c06030180c05c2c150a85028140a05026130904824120903c1e0d0682c1609048241209,unpack 0x8040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201070301411088401c080381c0c1102844200e038102203088401c07010380e0c028280611070200e01,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g7W0 : Wire g7C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1058307ff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff18dcb92b3,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g7W1 : Wire g7C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xa0603fe60,0xa2e193e6a,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g7W2 : Wire g7C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc07fc0780,0xc2e9c378a,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g7W3 : Wire g7C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80007ff,0xe3010254c,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g7W4 : Wire g7C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffff800,0x1c162c010,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g7V := [g7W0,g7W1,g7W2,g7W3,g7W4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g7proper : proper g7X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g7nd : (g7V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g7f1 : Basis g7X := basisFor g7X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g7V.map Wire.w) 4 (assignRows [0,9,1,2,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g7f1valid : (Price.mk g7f1 0).Valid 1 (wires g7V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g7bound : ¬Feasible g7X 4 1 (wires g7V) := by
  apply full_raw (positive_checked (v:=g7V) (by decide +kernel))
  exact cut_sound g7nd g7f1valid (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8X : Word := 0xffffffeafcf0ccc0ffffffeafcf0ccc0ffffffeafcf0ccc0ffffffeafcf0ccc0ffffffeafcf0ccc0ffffffeafcf0ccc0ffffffeafcf0ccc0ffffffeafcf0ccc0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8C : Charts g8X := ⟨unpack 0x30180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c060301872381a0cc6432188c06030180c06030168b0582a148a05028140a05028130984a251188c4221108844221108743a1c0e06c361a0d05c2c150a85028140a050281407838160b05028140a050281407038180c06030180c06,unpack 0x100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100832181204c44120889044200c84c200d0689018220489044200c84c1a081208848051100c482210064260d008641a180606426180904c2411028904419098401a04068301203120883213068200405018904419098340802,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8W0 : Wire g8C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x24808803ffe6580b0180,0x248d88e147e659ab399c,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8W1 : Wire g8C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc700100cc007e00fffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7241244d202e28152a9,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8W2 : Wire g8C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc800e00f00787ffc01ff,0x841e42b21280c3c8946,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8W3 : Wire g8C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x3000fff0007f800ffe00,0x3009a8b0057d012e2c14,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8W4 : Wire g8C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x3fff0000007ffff00000,0x358e00c00657f1c03018,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8W5 : Wire g8C := ⟨0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x3fffffffff8000000000,0xa70570eb8000600c060,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8V := [g8W0,g8W1,g8W2,g8W3,g8W4,g8W5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g8proper : proper g8X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g8nd : (g8V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g8f0 : Basis g8X := basisFor g8X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g8V.map Wire.w) 7 (assignRows [9,0,1,2,3,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g8f0valid : (Price.mk g8f0 0).Valid 1 (wires g8V) :=
  initial_price g3proper g3bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g8bound : ¬Feasible g8X 7 1 (wires g8V) := by
  apply full_raw (positive_checked (v:=g8V) (by decide +kernel))
  exact cut_sound g8nd g8f0valid (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9X : Word := 0xfffffff0eeccaa00fffffff0eeccaa00fffffff0eeccaa00fffffff0eeccaa00fffffff0eeccaa00fffffff0eeccaa00fffffff0eeccaa00fffffff0eeccaa00
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9C : Charts g9X := ⟨unpack 0x48241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048f070351a0cc6431188c06030180c06030170b0562a150a45028140a050281409c4e26130944a24120904824120903c1e0e874341a0c8642e170b058261309048241209048240f078341a0b058241209048241209,unpack 0x80402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010080402010087030150a08c44210888c401c0a8401c070703046220508446200e0541c080388c0e22030840a23100702a0e03810380e0e054300a0c0442a070a0182203118702a100701c040e038300a0a0188c3815070200e01,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9W0 : Wire g9C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff95802406600cf301fff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff95c9264e728473a4ad3,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9W1 : Wire g9C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x600b80780333fff980,0x643ba2f9191158f9ca,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9W2 : Wire g9C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x5800c007fffc3c01e00,0x581bc0eaa7fc3c6de3a,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9W3 : Wire g9C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000fff8003fc001fff,0x6012c8b0053b804952c,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9W4 : Wire g9C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x7fff0000003ffffe000,0x789c00c0062eea70030,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9W5 : Wire g9C := ⟨0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x7fffffffffc00000000,0x760370558000080040,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9V := [g9W0,g9W1,g9W2,g9W3,g9W4,g9W5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9proper : proper g9X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9nd : (g9V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9f0 : Basis g9X := basisFor g9X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g9V.map Wire.w) 5 (assignRows [9,0,1,2,3,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9f0valid : (Price.mk g9f0 0).Valid 1 (wires g9V) :=
  initial_price g7proper g7bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9f1 : Basis g9X := basisFor g9X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g9V.map Wire.w) 5 (assignRows [0,9,1,3,2,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9f1valid : (Price.mk g9f1 0).Valid 1 (wires g9V) :=
  initial_price g7proper g7bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9f2 : Basis g9X := basisFor g9X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g9V.map Wire.w) 5 (assignRows [0,1,9,2,3,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9f2valid : (Price.mk g9f2 0).Valid 1 (wires g9V) :=
  initial_price g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9f3 : Basis g9X := basisFor g9X 0x550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055 (g9V.map Wire.w) 4 (assignRows [9,0,1,9,2,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9f3valid : (Price.mk g9f3 0).Valid 1 (wires g9V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9f4 : Basis g9X := basisFor g9X 0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333 (g9V.map Wire.w) 4 (assignRows [0,9,1,2,9,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9f4valid : (Price.mk g9f4 0).Valid 1 (wires g9V) :=
  initial_price g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9f5 : Basis g9X := basisFor g9X 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f (g9V.map Wire.w) 3 (assignRows [0,2,9,1,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9f5valid : (Price.mk g9f5 0).Valid 1 (wires g9V) :=
  initial_price g4proper g4bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9prices : List (Price g9X) := [⟨g9f0,0⟩,⟨g9f1,0⟩,⟨g9f2,0⟩,⟨g9f3,0⟩,⟨g9f4,0⟩,⟨g9f5,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9valid : ∀ p ∈ g9prices, p.Valid 1 (wires g9V) := by
  intro p hp
  simp only [g9prices,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl
  · exact g9f0valid
  · exact g9f1valid
  · exact g9f2valid
  · exact g9f3valid
  · exact g9f4valid
  · exact g9f5valid
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g9bound : ¬Feasible g9X 6 1 (wires g9V) := by
  apply verified g9C g9proper g9nd g9valid
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g10X : Word := 0xfffffff0eeee0000fffffff0eeee0000fffffff0eeee0000fffffff0eeee0000fffffff0eeee0000fffffff0eeee0000fffffff0eeee0000fffffff0eeee0000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g10C : Charts g10X := ⟨unpack 0x88442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088442211088f07034198c86230180c06030178b85a2c158ac542a148a45028140a05027138984c25128904824120903e1e0f0743a1b0d06832190b8582c150a84c2412090482411088442211,unpack 0x804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100870301411888422310070200f078381a0c1182c440a1082446200e03c1023038880c210288c401c078101e1c070701a0b0c0283009038500c140280c461c0803c04230e0401e01,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g10W0 : Wire g10C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8a0acc1982739c1f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8b1ace59ca318e53,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g10W1 : Wire g10C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xc0cf01e039ce7e0,0xd1cf25e4a94a672,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g10W2 : Wire g10C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x500f001fffe0f800,0x505f00ca9fe0f94a,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g10W3 : Wire g10C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x600fffe003ff0000,0x605f54e01bff014a,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g10W4 : Wire g10C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000003ffffff,0x70600080114a518c,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g10W5 : Wire g10C := ⟨0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x7ffffffffc000000,0xf80ab1560000210,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g10V := [g10W0,g10W1,g10W2,g10W3,g10W4,g10W5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g10proper : proper g10X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g10nd : (g10V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g10f0 : Basis g10X := basisFor g10X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g10V.map Wire.w) 5 (assignRows [9,0,1,2,3,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g10f0valid : (Price.mk g10f0 0).Valid 1 (wires g10V) :=
  initial_price g7proper g7bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g10bound : ¬Feasible g10X 5 1 (wires g10V) := by
  apply full_raw (positive_checked (v:=g10V) (by decide +kernel))
  exact cut_sound g10nd g10f0valid (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12X : Word := 0xffffffa8fcf8eca8ffffffa8fcf8eca8ffffffa8fcf8eca8ffffffa8fcf8eca8ffffffa8fcf8eca8ffffffa8fcf8eca8ffffffa8fcf8eca8ffffffa8fcf8eca8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12C : Charts g12X := ⟨unpack 0x180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c72381b0d06432188c46030180c06030180b8582c150a45228140a05028140a04e251288c461d0e070361a0d0582c150a05028140a0502813098381c0d0682c140a05028140a0501c0a05028140a050280c06030180c0603,unpack 0x8040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008043218130904412108444c2110064241006098480c110841226108803212060204c241088842190c0303218090480c11130843212080300812088300c0c048244c210c8481808010184c210c8481804008984219090300401,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12W0 : Wire g12C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0c00603f21019c07fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0d406a0b21608d818b1,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12W1 : Wire g12C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcb00480263e01e7fc07f,0xb22491240e91224e44a,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12W2 : Wire g12C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc0070039c7fe7807f80,0xc20f10b042867226344,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12W3 : Wire g12C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x30007ffc1f8007ff8000,0x3004922c1f0245cb0a14,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12W4 : Wire g12C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x3fff80001ffff8000000,0x314700301bd3980c0c18,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12W5 : Wire g12C := ⟨0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x3fffffffe00000000000,0xeb86dc3e00c00303060,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12V := [g12W0,g12W1,g12W2,g12W3,g12W4,g12W5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12proper : proper g12X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12nd : (g12V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12f0 : Basis g12X := basisFor g12X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g12V.map Wire.w) 5 (assignRows [9,0,1,2,3,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12f0valid : (Price.mk g12f0 0).Valid 1 (wires g12V) :=
  initial_price g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12f1 : Basis g12X := basisFor g12X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g12V.map Wire.w) 5 (assignRows [0,9,2,1,4,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12f1valid : (Price.mk g12f1 0).Valid 1 (wires g12V) :=
  initial_price g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12f2 : Basis g12X := basisFor g12X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g12V.map Wire.w) 5 (assignRows [0,2,9,4,1,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12f2valid : (Price.mk g12f2 0).Valid 1 (wires g12V) :=
  initial_price g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12f3 : Basis g12X := basisFor g12X 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff (g12V.map Wire.w) 5 (assignRows [2,0,4,9,3,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12f3valid : (Price.mk g12f3 0).Valid 1 (wires g12V) :=
  initial_price g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12f4 : Basis g12X := basisFor g12X 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff (g12V.map Wire.w) 5 (assignRows [2,4,0,3,9,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12f4valid : (Price.mk g12f4 0).Valid 1 (wires g12V) :=
  initial_price g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12f5 : Basis g12X := basisFor g12X 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff (g12V.map Wire.w) 5 (assignRows [4,2,3,0,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12f5valid : (Price.mk g12f5 0).Valid 1 (wires g12V) :=
  initial_price g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12prices : List (Price g12X) := [⟨g12f0,0⟩,⟨g12f1,0⟩,⟨g12f2,0⟩,⟨g12f3,0⟩,⟨g12f4,0⟩,⟨g12f5,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12valid : ∀ p ∈ g12prices, p.Valid 1 (wires g12V) := by
  intro p hp
  simp only [g12prices,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl
  · exact g12f0valid
  · exact g12f1valid
  · exact g12f2valid
  · exact g12f3valid
  · exact g12f4valid
  · exact g12f5valid
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g12bound : ¬Feasible g12X 7 1 (wires g12V) := by
  apply verified g12C g12proper g12nd g12valid
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g14X : Word := 0xfffff888f888f888fffff888f888f888fffff888f888f888fffff888f888f888fffff888f888f888fffff888f888f888fffff888f888f888fffff888f888f888
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g14C : Charts g14X := ⟨unpack 0x180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c743a1c8e470381b0d86a351a0d06432188c46030180c06030180c06030170b85a2d160b0562b1389c46230f0783a1d0e070361b0b85c2613070381a0d06030180c06030180c06030160b0381c06030180c06030180c0603,unpack 0x804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804541a148645018130584a1512050441210844542913094401a0c8582a101509852251409054291309444210d05832150c05034190b0542411050181205150a44c250d0642c150401014090301454291309434190b0540401,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g14W0 : Wire g14C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc30c0033f33f3003fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc30d4a3153153551555,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g14W1 : Wire g14C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0c3000c3fc3fc003fff,0x30c3294c2ac2acaa2aaa,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g14W2 : Wire g14C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfc000fccfccfffcc00,0xfc0c654c54c5334ccc,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g14W3 : Wire g14C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x3f00000ff0ff0ffff000,0x3f00318ab0ab0accb330,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g14W4 : Wire g14C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x3ffffff000fff0000000,0x155541f000fff00f003c,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g14W5 : Wire g14C := ⟨0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x3fffffffff0000000000,0x2aaabe0fff0000f003c0,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g14V := [g14W0,g14W1,g14W2,g14W3,g14W4,g14W5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g14proper : proper g14X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g14nd : (g14V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g14bound : ¬Feasible g14X 4 1 (wires g14V) := by
  apply full_raw (positive_checked (v:=g14V) (by decide +kernel))
  intro h
  have total := exact_size h
  have count : (wires g14V).card=6 := by decide +kernel
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11X : Word := 0xfffffffffffffcccfffaffaaf0f0f000fffffffffffffcccfffaffaaf0f0f000fffffffffffffcccfffaffaaf0f0f000fffffffffffffcccfffaffaaf0f0f000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11C : Charts g11X := ⟨unpack 0x6030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030e470349a0cc6532190c46130180c06030180c0602d968b2592c160aa5429948a25128140a05028140a05026934984c2592c944a2391c8c462190c844221108844221108763a1d0e470381b0d86834198cc6231170b0562a150a45028140a05028140a04e271289446231088442211088442210f8783a1c0b85c2c160a85428140a05028140a0501e0f070381a0d06030180c06030180c,unpack 0x20100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020106430249204c452209044412491480321308036070d8689219240608a440984882112491480321306c20072491490442482c900a2281c88062080c9245200c84c1b0380836320d06460181909860241904c601113090162205024924519098401b0401c4c071201444032491464261006c0e010d86832180981c24060881492451909836100381016070501812052491464260d8200e04,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W0 : Wire g11C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x9100b2b00cccc0240f2403fffacc03300,0x91c3b2bc5cccf1a40527155c7acf2b3ca,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W1 : Wire g11C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x22200c0c000fffff8ccb803300cf003c00,0x2221bc0c1d05547f8ccb8d7336cf0ebc3a,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W2 : Wire g11C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc3c0003000f0f0000f0c003c00ffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc3c490304950f128050c147c520554d553,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W3 : Wire g11C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc000fc000ff0003f00fffc000f0003fff,0xc082fc084af0212d002e18084f0222a8c,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W4 : Wire g11C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x30000fffff000003fff0000000ffffc000,0x30012d4d16000053faf0090024fa8b0028,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W5 : Wire g11C := ⟨0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x3ffff00000000003ffffffffff00000000,0x3261c000180000612fad0e2a38000c0030,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11W6 : Wire g11C := ⟨0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x3ffffffffffffffc000000000000000000,0xd9e02b2e0faab8000003000c0003000c0,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11V := [g11W0,g11W1,g11W2,g11W3,g11W4,g11W5,g11W6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g11proper : proper g11X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g11nd : (g11V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g11f0 : Basis g11X := basisFor g11X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g11V.map Wire.w) 8 (assignRows [9,0,1,2,3,4,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g11f0valid : (Price.mk g11f0 0).Valid 1 (wires g11V) :=
  initial_price g8proper g8bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g11bound : ¬Feasible g11X 8 1 (wires g11V) := by
  apply full_raw (positive_checked (v:=g11V) (by decide +kernel))
  exact cut_sound g11nd g11f0valid (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13X : Word := 0xfffffffeffffffccfffffafaf888f888fffffffeffffffccfffffafaf888f888fffffffeffffffccfffffafaf888f888fffffffeffffffccfffffafaf888f888
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13C : Charts g13X := ⟨unpack 0x180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c0603019c0d46834194c86431188c2612d164b0562a954a85429144a25028140a05028140a050269309449249209048241209048241208e462310c844221108844221108843a1d0e470381b0d46832190c46030180c06030180c0602e160ac5229130984a24120904824120904824118844221108844221108843c1e0e874381c0d86c2e170984c1c0e06834180c06030180c06030180b0581c0e030180c06030180c06032110884422110884551d188a032280c0a25024108c44921084924221098420b19140906824120484230984c26130984c20301884060c03830180c0183042033083006211800ca03001830c8241200c0e610180c06030180c06461481c8426210909248211200646018908403280a4602110920180c061084203,unpack 0x804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100980546014114c04430088c0410d064301622854881409104226022900541a0c8582a10229101441049808a401506832160a8208a4403104c045200a834190b054042a0d06450180b054282209044c0451508034190b054202a140a85009110180a60228a8401a0c8582a04111808a2a1006832160a80434160c85430140d0642c1509044140604814c0451506832160a820080a048180a60228a834190b054040130180c06030180c0150d1802a1a0a8682a1504818c00930024126011018821a0d054c060300240c60010080402010080445150188022200808241209000444110808002200a04009141001008041004002008040201008040206048140c06030181208010200206008100405080242020008240804020080201,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13W0 : Wire g13C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8434c6009802400444007200ffccfcc01fff010216300ffe8bb487fec229583,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8414c68a9a2a51444514128a22cc54d28a95012b96244010380100fec2294c3,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13W1 : Wire g13C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa0c908002003fff898014c008030ff001ffffed069d8101a892486ff78bb005,0x2049083420d086b898a94c549530ab0d146a009440d82fed029001013c92004,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13W2 : Wire g13C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x701f000c0038000e0018fff003f33ffe600010000402001f4407a015414038,0x501f086c21b90c0e10c068721953151a68c012b40442014010000017c15038,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13W3 : Wire g13C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x380e0000fffc001f0001f000003fc3fff80000809213c001744040008340478,0x280e003828e4071f00b1f058162ac28e58700094961840080005b8008340440,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13W4 : Wire g13C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x400fffff0000001ffffe0000003ffc00000001bf000c0000000b00000000a00,0xf5a1f007803cdec3e001e07bffc07803c01bf001c0000000000000000a00,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13W5 : Wire g13C := ⟨0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x7ff000000000001fffffffffffc00000000000d424692fe4029939009404782,0x7ae001200480241212c1e960d80000280140fe402983900940c682000000100,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13W6 : Wire g13C := ⟨0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x7fffffffffffffe000000000000000000000ff6bfb87dfe0008221012bd2844,0x57b0a5c0d703780003000180600000300180fe4029239012bd2844000000000,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13V := [g13W0,g13W1,g13W2,g13W3,g13W4,g13W5,g13W6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13proper : proper g13X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13nd : (g13V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13f0 : Basis g13X := basisFor g13X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g13V.map Wire.w) 8 (assignRows [9,0,1,3,4,2,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f0valid : (Price.mk g13f0 0).Valid 1 (wires g13V) :=
  initial_price g8proper g8bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13f1 : Basis g13X := basisFor g13X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g13V.map Wire.w) 8 (assignRows [0,9,3,1,4,5,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f1valid : (Price.mk g13f1 0).Valid 1 (wires g13V) :=
  initial_price g8proper g8bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13f2 : Basis g13X := basisFor g13X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g13V.map Wire.w) 8 (assignRows [1,3,9,0,4,2,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f2valid : (Price.mk g13f2 0).Valid 1 (wires g13V) :=
  initial_price g8proper g8bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13f3 : Basis g13X := basisFor g13X 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff (g13V.map Wire.w) 8 (assignRows [3,1,0,9,4,5,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f3valid : (Price.mk g13f3 0).Valid 1 (wires g13V) :=
  initial_price g8proper g8bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13f4 : Basis g13X := basisFor g13X 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff (g13V.map Wire.w) 8 (assignRows [0,1,4,5,9,2,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f4valid : (Price.mk g13f4 0).Valid 1 (wires g13V) :=
  initial_price g12proper g12bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13f5 : Basis g13X := basisFor g13X 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff (g13V.map Wire.w) 7 (assignRows [0,3,1,4,2,9,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f5valid : (Price.mk g13f5 0).Valid 1 (wires g13V) :=
  initial_price g9proper g9bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13f6 : Basis g13X := basisFor g13X 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff (g13V.map Wire.w) 7 (assignRows [3,0,4,1,2,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f6valid : (Price.mk g13f6 0).Valid 1 (wires g13V) :=
  initial_price g9proper g9bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13prices : List (Price g13X) := [⟨g13f0,0⟩,⟨g13f1,0⟩,⟨g13f2,0⟩,⟨g13f3,0⟩,⟨g13f4,0⟩,⟨g13f5,0⟩,⟨g13f6,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13valid : ∀ p ∈ g13prices, p.Valid 1 (wires g13V) := by
  intro p hp
  simp only [g13prices,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact g13f0valid
  · exact g13f1valid
  · exact g13f2valid
  · exact g13f3valid
  · exact g13f4valid
  · exact g13f5valid
  · exact g13f6valid
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13frame : Frame g13C := ⟨10,1,g13V,g13prices⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13vframe : g13frame.Valid := ⟨g13nd,g13valid⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13auto0 := autoFor g13X (assignRows [0, 1, 2, 3, 4, 5, 6, 7, 8]) (assignRows [0, 1, 2, 3, 4, 5, 6, 7, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rot0 : Rotation g13frame := ⟨g13auto0,[g13W0.w,g13W1.w,g13W2.w,g13W3.w,g13W4.w,g13W5.w,g13W6.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13auto1 := autoFor g13X (assignRows [1, 0, 3, 2, 4, 6, 5, 7, 8]) (assignRows [1, 0, 3, 2, 4, 6, 5, 7, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rot1 : Rotation g13frame := ⟨g13auto1,[g13W1.w,g13W0.w,g13W3.w,g13W2.w,g13W4.w,g13W6.w,g13W5.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13auto2 := autoFor g13X (assignRows [2, 3, 0, 1, 4, 5, 6, 7, 8]) (assignRows [2, 3, 0, 1, 4, 5, 6, 7, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rot2 : Rotation g13frame := ⟨g13auto2,[g13W2.w,g13W3.w,g13W0.w,g13W1.w,g13W4.w,g13W5.w,g13W6.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13auto3 := autoFor g13X (assignRows [3, 2, 1, 0, 4, 6, 5, 7, 8]) (assignRows [3, 2, 1, 0, 4, 6, 5, 7, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rot3 : Rotation g13frame := ⟨g13auto3,[g13W3.w,g13W2.w,g13W1.w,g13W0.w,g13W4.w,g13W6.w,g13W5.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rot := #[g13rot0,g13rot1,g13rot2,g13rot3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rows0 : Rows := #[
 #[0x2141400900eb004018e002015000a195d00a0f4b0030d6900534840080e6b001243b0060fc3008171c0052ddb001387100b02a90061149005180500825600010fbf0070c1400018940062b160083d520050e3e0011f8a000096d00718ec00b2afc006353e0000054321]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rows1 : Rows := #[
 #[0x1a0993061066a01a36cf00602eb01b0bb005a264202406c8005095905d0e1305a1eba024309801b30120053ba9048118c0623fb804824d90620f2f02b06c800117ff05c027f0000032514040,0xe1fe50661d210293a9a0110db002f3b9705009af06c19ae0412e7a02b1b550363d1a07826ef004344a06720ca03d24c00700ff3030111204f151f00b027a00a131c02d374106927ff05e3c2a00000432150c8,0x320e4a06806bf0440cad01f21e60260bcd066319d052047e0160b3d00e25d306d000b01f056702622c20661d2101c097601a15f60522ab40162ba000e0cec01a36cf04a064e06d285e04d0eed028079a0171a2700c073503815bb01804c803833760182070000054321600c,0x6f0a660530b090573dff06b07e906b109a05727590790c24057118306b2edb0650592006121206b36d005707bc00602eb065126a079247a0070eb500714a6000004321500a,0x7a07ed0530b0901928780123d6301937ad0122ee60190d2701218b60191b3801202de07b0a5e00000000762d4,0x1f1e640162ba005923b004f0a7805707bc0750ed403c28be0502e8b04824d90352a1605b316f0720cf904204a902e2b990272258071190004006670090c7e0210569078371b031307d023105901335bf01e07ff00d1dab0000053241050,0x463cc00123d6303705350582b2300f02f402129b3030244902e33dd003113802f3b97024146c03e392a0352a160362b6203334c404506d40470c3600816200000053214008,0x4a1c3a060091101c09760221774065059203104700150e57040260403d109a05a3a2d033296f0312344015209f00523d3040066703d37b30050959077011505a1eba0330d640421a8c010095f0001c8701d0a280110db002a07ff0430fd500000315240c0,0x521e9103a24b80260bcd05403dd00a30af06b07e9004167e07131ab05f14ec0092b41039319602c271500f1bc605b228504b0fdd0150e570001c87003359606a17d203c28be01b0bb004824d903e0fbb0232a750021bcd06427ff03b2d7e00000532141d0,0x3211110320e4a063026e063159807400bc051011804e041a06f0a6603a24b80232a750463cc003a302d0233d480462e4303a0baa06009110611591023003c046181303a1663061066a06015e90231059046023b06e07ff0140b0100065432172d8,0x681f7106315980440cad0591fe100a30af0582b23054127c029093a04f20050371ca60593365022177400a131c058067605438b2029205604f0a78037309e07400bc025166903f07ff0560c9e0000043215250,0x6d12cf06d000b0790c2405f14ec05f0f1d07216c00412e7a05a3a2d04529d10720cf90413e4503409b705a264204533f90093235049184b0092b410490203070250307327ff02009430000042153140]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rows2 : Rows := #[
 #[0x6d058d06d2b200440ed5000000000003805e,0x230b8002,0x1d377b0000000003158323,0x80be103a364a0000000013058008,0x98369e00000000051481de,0x21040147,0xa61c20000000000504000c,0xa707c60970bfa08a302e08634a008a16230861f8f000000005700a05a,0x8129620732cfb02519f9009087d03b0ba203109a80763ac4000000003700605a,0xf0f690000000000030056,0x172aa9053336c000000000004805e,0x3721dc03e34c606138c406436ba034097000000000250c805a,0x5b0ceb05b28720521e5a000054321600c04e,0x3312610572c100700162054299806a012b04b2bf500000543120d8001,0x582d0f00403b7000000005104800e,0x300b7807419e7000000003415800a,0x9a12700591dcc091007a09125bc09517ce066045b07c128b00000000240c005a,0xa8097f0790e3700000000000c004e,0x1600235c,0x69174000000000001d8323,0x8402560a405c50ac0b2e07219af072055907238980722e5300067543212d8001,0x11370100000000020c0256,0x6315000e,0x99019b08800bb08827ad0a900d904e05cf032220a02e39cd02920c203208fa02e1c1002909a2000000000600e052],
 #[0x38113f0420abd000002154600c03e,0x10ec000000000002d4127,0x160fde02f1d8c0000000001040010,0x1040256,0x6b078a05615c600000000420c000e,0x1311c200000000240c0052,0x16050002,0x5c3fc600a197800000000000d800e,0x633da1024036806327590241c74093017e0050ea4005186a0000005213140001,0x731c0509d3f830000000002050006,0x382e0,0x601d8c05e24080781bae00000000000d005e,0xb2f770000000013040008,0x2708ab0000000005258323,0x6e247700000000641d000e,0x150260,0x4330bc0431367000000000600c05c,0x31482d6,0x240c0002,0x920522000000000004004e,0x6f1cf006e0a2c07e064801c0d6009b174a00818a20460ff808916ba0070a250980bb4011180900000000210d00a1,0x75273507f2e1d000000000514805a,0x1e01d600000000310021d8,0x20200800000000010021d0],
 #[0x4a22fb0000000052048006,0x591dcc00000000020c025e,0x8b017c000000006700c360,0x2d1be70000000041002148,0x301c8,0x28190a00000000020041d8,0x481e5a00000000520041d0,0x9e300500000000540082e0,0x4d0d81000002154700e03e,0x5009330000000000058122,0xd1aec00000000020d035e,0x8c2f9a0392eb503f3365010179d01f1c9c082021c051122e0a03f6900000543120d0001,0x8916ba00000000000d01d8,0x38250,0x7286503502060000000041002258,0x56250002,0x50148,0x30250,0xa107410000000000038056,0x26154a096025400e06130ab044f06808ce00028740000fef00000053120c0001,0x6525000e,0x19266f000000000403000a,0x15156a08103900621d830000000001002360,0x300b78014069603d22880411a1f08f2f3b05f0eba000000004700805a],
 #[0x9c328f07a35e500000000000b8056,0x2b1d2103c19e70000000003140052,0x401c4007b1de5000000003103800e,0x9b174a00000000000d0258,0x94027f00000000001d80a8,0x7110be0713301000054321600c05e,0x8b144008b017c0152fef01531750150b42015156a00000000052d82a1,0x611720000000000048056,0xc81d8,0xa50b2e00000000002d82a2,0x6f26340881969038113f09001d105d0687000000000015800e,0x5600a35c,0x1d02e0,0xd0250,0x830f1a067154a0210378080029f02125b808024340000043215250001,0x122fd0000000001505000c,0x23262100000000020042d8,0x1502e0,0xa303af000000000003003e,0x1c0d6000000000000d0260,0x181e4a01b0bf80182dc101b3f4504c1fb600c0c5f00c3a170000005321040001,0x40140,0x771d580473de6003229801a3b6d0020f2107d0d7c06c3bd10000004213148001,0x41401de],
 #[0x9a127000000000000c0360,0x40360,0x4522f90363cb80000000001040052,0x525835f,0x501f6908d20df00000000260d0002,0x85130b00000000250c000c,0x5b3e2b0491f0905514810000000001048010,0x4314824f,0x991baa08710a105a09f8000000000025800e,0x451c8002,0xd1aec0460ff800000000000d01e0,0x7e209304f160700000000451d000c,0x4104824f,0x8e0f620222480000000000414000e,0xa50b2e0ad082c00000000672d8002,0xa707c60a71af00650614000000000500a360,0x2c2bf4000000000103004e,0x205815f,0x501c8,0x12030002,0xaa0b2e000000000025005e,0x41050260,0x58158,0x38148],
 #[0xa2182f00000000051c825e,0x2a0a5b000000000514000c,0x9f03fd00000000002d42a7,0x75432162d4001]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rows3 : Rows := #[
 #[0xc000102e,0x2d4127001,0x148001046,0x48001056,0x4800e029,0x140001036,0xc805e001,0xd00a1006,0x1058121006,0x605a04e,0x50010029,0x21400a1,0x4000103e,0x582583e5,0x270c6a00000000000c0001056,0x153f680000000000030056001,0x5800103e,0x380de121,0x15000c029,0x3805a001,0x2341b000000000000805a056,0x4360321,0x4001002d,0x14805e221],
 #[0xb8001056,0x41c80a1,0xc800105a,0x4000105a,0xd00a11d8,0xd005a001,0x21d80a1,0x58001046,0x48008029,0x250001046,0x3000e029,0x82d80a1,0x14000105a,0x805205e,0x38001056,0x258323001,0x22600a1,0xe05202e,0x14000c029,0x14005a0a5,0x14004e001,0x2038006029,0xc05a02d,0xb800e029],
 #[0x415800a061,0x605a036,0xe052036,0x5000105e,0x1d081b028233d00f16270081a2500000000000c805a001,0x22580a1,0x60f52000000000004005a001,0x1c805a125,0x1a2a8f01619cc00000000001d001004d,0xa19430173d3100000000001d000105a,0x42580a1,0x605a046,0x1110f0000000000014005a001,0x405a04e,0x148052125,0x15800104e,0xc001002d,0x6052046,0x16034801210d1000000000000c03e05a,0xe05403d,0xd107900d360c000000000003805e001,0xb8052045,0xd00a1158,0xc8001052],
 #[0x52d7700000000000022500a1,0xc800e02d,0x414800a029,0x1d800103e,0xb800104e,0x1e15c80003bfa000000000000e03e052,0xe05204e,0x15800c029,0x15293200000000000580021a9,0x58001036,0xb092100b2681000000000000e04e052,0x18308600000000001c8056001,0x1d8001036,0x20c800e029,0x110b20000000000038010029,0x1619cc010083d00000000001d8001052,0x14800e02d,0x380521d5,0x25800e029,0x41c800e055,0x132ee4000000000015001002d,0x160348000000000015800e029,0x1d005e1a1,0x2202d8000000000000805a02e],
 #[0x5005e2a1,0x148052225,0x43600a1,0x30001056,0x14805205d,0xa3600a1,0x71d6900000000000c005a04d,0x24335202415530000000000258001052,0xc000104e,0x15005a001,0xd800103e,0x2007c900000000000c000e02d,0xc8001046,0x3805e221,0xd00a100c,0x1a1846000000000005812100c,0xd800104e,0x300e0561a1,0x2d800103e,0x205a15f,0x62580a1,0x4805a1a5,0x4052046,0x1c8001056],
 #[0x9064b0033bca000000000005005e001,0x2603cd00000000000c004e001,0x2121d300000000000b805e001,0xc0010029,0x250fe501f072901902f70192e480000000000038052001,0xc322f0000000000148001036,0x20d00a100a,0x1b21ff000000000004805a001,0x25000103e,0x205a35f,0xd000102f,0x25000105e,0x2d800104f,0x3800c029,0xe1146000000000000a052036,0x41cd90043d8e000000000025001002d,0x1d0010059,0x581211d8,0xa05202e,0xc360321,0x1d000105e,0x31d0002045,0x14000e02d,0x405a046],
 #[0x231c220140881000000000015800e02d,0xc005a1a5,0x4004e001,0x14000104e,0x1d80a81a1,0x3805205d,0xc000105a,0xa05a056,0xc8156121,0x250010059,0x70879000000000003805235e,0x58121158,0xb805e221,0x62600a1,0x22d80a1,0x2d42a7001,0x158001045,0x38056001,0x1480521d5,0x3003e001,0x2d800104e,0x290b2d00000000002d8002329,0xb800c029,0x500a05a35f],
 #[0xc004e059,0x2a0408000000000000c05a056,0x290b2d000000000025005e001,0x1c083d00000000000c0001052,0x2d800104d,0x52d8002055]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rows4 : Rows := #[
 #[0xc03605a0a5,0xc000e02904d,0x205205e2a1,0x1d005e00103d,0x25800e02d221,0xc8008029045,0x4005a001039,0x3805204d2d6,0x48052001031,0x5005e00104d,0x158001052045,0xe04e052225,0xc800103e041,0xc005600103d,0xa05a02e031,0x48052001041,0x1d8001052035,0x140052001031,0xe046052125,0x5001002d1a1,0x15800e02d121,0x14005e001045,0x15000105a03d,0x58001052045],
 #[0x4805e001035,0x38052001041,0xd00a100e035,0x14805a001029,0xc000105205d,0xc805a001051,0xc04605a0a5,0x38052001049,0xc000e02d059,0x4005e001035,0x805a02e031,0x1d001002d1a1,0x25000105a02d,0x38052001059,0xc004e00105d,0xc00010562a1,0x1c805a001031,0x25005e00104d,0xc05a0562a1]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rows5 : Rows := #[]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13audit4 := atlasRow g13frame 4 g13rows4 g13rows5 0 g13rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check4x0 : Span g13audit4 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check4x8 : Span g13audit4 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check4x16 : Span g13audit4 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check4x24 : Span g13audit4 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check4x32 : Span g13audit4 32 40 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check4x40 : Span g13audit4 40 43 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13done4 : Region g13frame 4 43 g13rows4 :=
  atlas_sound g13proper g13frame g13vframe 4 43 0 g13rows4 g13rows5 g13rot (by intro j hj; omega) (join_span (join_span g13check4x0 (join_span g13check4x8 g13check4x16)) (join_span g13check4x24 (join_span g13check4x32 g13check4x40)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13audit3 := atlasRow g13frame 3 g13rows3 g13rows4 43 g13rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x0 : Span g13audit3 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x8 : Span g13audit3 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x16 : Span g13audit3 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x24 : Span g13audit3 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x32 : Span g13audit3 32 40 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x40 : Span g13audit3 40 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x48 : Span g13audit3 48 56 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x56 : Span g13audit3 56 64 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x64 : Span g13audit3 64 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x72 : Span g13audit3 72 80 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x80 : Span g13audit3 80 88 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x88 : Span g13audit3 88 96 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x96 : Span g13audit3 96 104 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x104 : Span g13audit3 104 112 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x112 : Span g13audit3 112 120 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x120 : Span g13audit3 120 128 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x128 : Span g13audit3 128 136 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x136 : Span g13audit3 136 144 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x144 : Span g13audit3 144 152 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x152 : Span g13audit3 152 160 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x160 : Span g13audit3 160 168 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x168 : Span g13audit3 168 174 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13done3 : Region g13frame 3 174 g13rows3 :=
  atlas_sound g13proper g13frame g13vframe 3 174 43 g13rows3 g13rows4 g13rot g13done4 (join_span (join_span (join_span (join_span g13check3x0 g13check3x8) (join_span g13check3x16 (join_span g13check3x24 g13check3x32))) (join_span (join_span g13check3x40 (join_span g13check3x48 g13check3x56)) (join_span g13check3x64 (join_span g13check3x72 g13check3x80)))) (join_span (join_span (join_span g13check3x88 g13check3x96) (join_span g13check3x104 (join_span g13check3x112 g13check3x120))) (join_span (join_span g13check3x128 (join_span g13check3x136 g13check3x144)) (join_span g13check3x152 (join_span g13check3x160 g13check3x168)))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13audit2 := atlasRow g13frame 2 g13rows2 g13rows3 174 g13rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x0 : Span g13audit2 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x8 : Span g13audit2 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x16 : Span g13audit2 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x24 : Span g13audit2 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x32 : Span g13audit2 32 40 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x40 : Span g13audit2 40 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x48 : Span g13audit2 48 56 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x56 : Span g13audit2 56 64 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x64 : Span g13audit2 64 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x72 : Span g13audit2 72 80 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x80 : Span g13audit2 80 88 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x88 : Span g13audit2 88 96 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x96 : Span g13audit2 96 104 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x104 : Span g13audit2 104 112 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x112 : Span g13audit2 112 120 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x120 : Span g13audit2 120 124 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13done2 : Region g13frame 2 124 g13rows2 :=
  atlas_sound g13proper g13frame g13vframe 2 124 174 g13rows2 g13rows3 g13rot g13done3 (join_span (join_span (join_span (join_span g13check2x0 g13check2x8) (join_span g13check2x16 g13check2x24)) (join_span (join_span g13check2x32 g13check2x40) (join_span g13check2x48 g13check2x56))) (join_span (join_span (join_span g13check2x64 g13check2x72) (join_span g13check2x80 g13check2x88)) (join_span (join_span g13check2x96 g13check2x104) (join_span g13check2x112 g13check2x120))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13audit1 := atlasRow g13frame 1 g13rows1 g13rows2 124 g13rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check1x0 : Span g13audit1 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check1x8 : Span g13audit1 8 12 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13done1 : Region g13frame 1 12 g13rows1 :=
  atlas_sound g13proper g13frame g13vframe 1 12 124 g13rows1 g13rows2 g13rot g13done2 (join_span g13check1x0 g13check1x8)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13audit0 := atlasRow g13frame 0 g13rows0 g13rows1 12 g13rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check0x0 : Span g13audit0 0 1 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13done0 : Region g13frame 0 1 g13rows0 :=
  atlas_sound g13proper g13frame g13vframe 0 1 12 g13rows0 g13rows1 g13rot g13done1 g13check0x0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g13bound : ¬Feasible g13X 10 1 (wires g13V) := by
  apply full_raw (positive_checked (v:=g13V) (by decide +kernel))
  exact whole g13done0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g15X : Word := 0xffffffffffffff00fefcfaf0eeccaa00ffffffffffffff00fefcfaf0eeccaa00ffffffffffffff00fefcfaf0eeccaa00ffffffffffffff00fefcfaf0eeccaa00
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g15C : Charts g15X := ⟨unpack 0x48241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241209048241278389c0d46833998ca643198cc46230984c06030180c06030180c0602e160ae562a954a85429948a25128140a05028140a050281409e4e27134984c25928944924120904824120904824120783c1d0e872391a8d46834198cc6432170b8582c158ac52291389c4c261289448241209048241209048240f0783a1d0d06832190b85c2c160984c24120904824120904824120783c1a0d0582c1209048241209048241209,unpack 0x8040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040238188c05428239188a442188c8422208848e401c0c45423100702a0e0e0608e462285488142190882112390070311508c3815080388e4607114880c2190814412390070311508c381507020701c1c0a870311885460141888c602215038500c1508c50211181c4406108148e38188a846200e0541c040e03838150c02830110a81c28060880c8e38188a8461c0a8401c020701c18050500c8e38188a8461c0a8381001,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g15W0 : Wire g15C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe8acc002cb002490003cc0fcc0033cc00ffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe8ace522cb952499501cc05cea411cea856a9,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g15W1 : Wire g15C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x2cf00030c0038e000c0fccf000ccffffcc00,0x2cf23130c8c78e8c8405ccf262445663ce64,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g15W2 : Wire g15C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0000bf0003f00030f0f0fffff0f000f000,0xf0207bf0837f083905050560ff0f21af21c,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g15W3 : Wire g15C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff300000c00003ffffff00ff0000ff0000ffff,0x13000a5c002a4922afe00fa014aee0152a956,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g15W4 : Wire g15C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x1c00000fffffc00003fff000000ffffff0000,0x1c000c6c5133800333bfa00018cbba99c0198,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g15W5 : Wire g15C := ⟨0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x1ffffff00000000003fffffffff0000000000,0x1f054f80003c0003c2fafafa9f00001e001e0,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g15W6 : Wire g15C := ⟨0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x1ffffffffffffffffc0000000000000000000,0xfab003aec036dc000000002000002000200,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g15V := [g15W0,g15W1,g15W2,g15W3,g15W4,g15W5,g15W6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g15proper : proper g15X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g15nd : (g15V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g15f0 : Basis g15X := basisFor g15X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g15V.map Wire.w) 7 (assignRows [9,0,1,2,3,4,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g15f0valid : (Price.mk g15f0 0).Valid 1 (wires g15V) :=
  initial_price g9proper g9bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g15bound : ¬Feasible g15X 7 1 (wires g15V) := by
  apply full_raw (positive_checked (v:=g15V) (by decide +kernel))
  exact cut_sound g15nd g15f0valid (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16X : Word := 0xfffffffffffffffcfffffffffffff0f0ffffffffffccffccffeaeaeaffc0c0c0fffffffffffffffcfffffffffffff0f0ffffffffffccffccffeaeaeaffc0c0c0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16C : Charts g16X := ⟨unpack 0x30180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c0603385c0d56a345a2d06832d94c964b2190c562b1188c361b0984b4592c158ab552a952a85429146a25128540a05028140a05028140a05026d34994c255289349a49249148a41209048241209048241209047a391a8d462310e8642a150884422110884422110884421d4e874391c4e070361a8d06532190c46130180c06030180c06030180c05d2e164b0572b14ca652291349a4c2612c944924920904824120904824120904823918864321108844221108844221108843c1e0e874381c0d86c351a8cc6631188b85c2d168ac5629148984c251288c4621108844221108844221108843a1d0e070361b0d06832190c06030180c06030180c06030170b8582c0f078381c07038180c06030180c06030180c06,unpack 0x100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020130580552a304a2c02822d14c144b0110c122b0088c141b010434190c0588b450a9128814091068211205828b401546832160a8401306a2d148944054288309a08248108b0516802a8d0642c1504c200d45a29120d44031068240815828b401546832160a8260d02154a83419144a030160a8504522090444160a2caa401a0c8582a1004c1a552a144a0552a1442650091141a440602c144104b051655200d0642c1504c1a0822910820360a2caa401a0c8582a098340434160c85430140d064340a8c82630088b0542c068a816280489044240288806c1459546832160a84013068042a0d0a030260b09028220960a2caa34190b0541308034101509850240d05830140501b0516551a0c8582a098340802,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W0 : Wire g16C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x565998122400559800b2c0044110015665800b00001f9f9ffff3300199800,0x565998122741d59e85b2f434411e075665f06be0c00a8a8bc1f33e1599f0c,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W1 : Wire g16C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80601e9c380061e000c300008420001f86000fffe66666660003c001fffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80600a9c391561e22cc31160842454028622c145a62626269503c4b0aaa59,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W2 : Wire g16C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9801e1204000060000ffffff09c0019878000c0018787878003c0001fffff,0x1800a12040688600d114469f09c2a39878152c2a5858585868bc0345551a6,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W3 : Wire g16C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x7e003f8000780000fc00000e0001e07ffff0001f807f80003ffffe1e000,0x6a003f810cf80219fc10d00e0432002ea1b0434a807f808c9554661e234,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W4 : Wire g16C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x1f8001c000007fffff000007f00001ff800000001fff8000003fffffe0000,0x1a8001c0007106a8e6000727f002c5ff8016402c957f8000712aa399e01c8,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W5 : Wire g16C := ⟨0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x600001ffffff800000000007fffffe00000000001fffffffffc0000000000,0x1e4c83e0000780003c19e60f8000007800f1ff575743e0001e0000f0,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W6 : Wire g16C := ⟨0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x7ffffe000000000000000007ffffffffffffffffe00000000000000000000,0x7f95f4000240000480002406619b01fd51580eb00000000140000a0000500,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16W7 : Wire g16C := ⟨0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x7ffffffffffffffffffffff80000000000000000000000000000000000000,0x657f5e1b3780795700ebb800000c0000006000c00000000180000c0000600,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16V := [g16W0,g16W1,g16W2,g16W3,g16W4,g16W5,g16W6,g16W7]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g16proper : proper g16X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g16nd : (g16V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g16f0 : Basis g16X := basisFor g16X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g16V.map Wire.w) 11 (assignRows [9,0,1,2,3,4,5,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g16f0valid : (Price.mk g16f0 0).Valid 1 (wires g16V) :=
  initial_price g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g16bound : ¬Feasible g16X 11 1 (wires g16V) := by
  apply full_raw (positive_checked (v:=g16V) (by decide +kernel))
  exact cut_sound g16nd g16f0valid (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17X : Word := 0xfffffffffffffffcfffffffafffffff0ffffffffffeeffccfefefafaeeee0000fffffffffffffffcfffffffafffffff0ffffffffffeeffccfefefafaeeee0000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17C : Charts g17X := ⟨unpack 0x28944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128944a25128945c4e170381a8d16834192c862b1588c461b0d84c25c2c960b0552a950a85329146a350a8538984a24d249148241209048241209048241208f47235188b45a29148944a21108844221108844221108843a1d0c8642a150884422110884422110884421e0e870381a8d06532188c26030180c06030180c06030180b85c2c160ac552a948a251279389a4d26130964a2492490482412090482412090482411c8e462310c864221108844221108844221108783c1d0e872341a0c86431178b85c2d160b0562b148a44e261309448241209048241209048241208c4621108844221108844221108843e1e0f0743a1b0d06832190b8582c150a84c241209048241209048241209044221108844221108844221130109202130240c04848108c084090902242288d120a81a044229012220484844048b0321a2a090324228448c244108241210a2022515404588214204490242421084a108890b0241908424210889024211238108e02404884c20892042d058285a0e048085108438340241110b10e07058044841110a108451,unpack 0x2090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090482412090544c160280a8c16014182c060915804460a0d80821c2894030510a940285128144835020438180a20d048160a8906802a114702a0e0401e0f07034188305a08148104b054483401508a38150701e084181d04064081582a241a00a8451c0a8380f020e0a850180a850452208882c15120ca845200e054200e03ca81c28060a85422940a041078388a0d22030160a2082582a2419508a401c0a8380f041140e440310406c15120ca845200e0541c07808701c1c0a870300a0c04430078a81c0d14030540b140240e220301582a2419508a3815080380f0208806c15120ca8451c0a8401c078041e1c070701a0b0c0283009038500c140280d82a2419508a3815070200f0130544832a114702a0e0401e016020c608350300601850208a045150508a8322850a0280e11482a02a0a0381c1508830a20a0a030221030100a02004080c00810040c018280a0c02808100801814020101030060505004080101020080500a28088c00c08904822082102505020580a040204504428300048120910a030180040481008100441,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W0 : Wire g17C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffffd12cc003c500159800cc000120001bb2c00660002193e4007ffe739c007ff10028600040b54185900a441859,0xffffffffffffffffffffffffffffffffffffffffd12cc00145a4359d22ce9101350409b2ea167508009166a1350e318ea154350138600000000000000a441859,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W1 : Wire g17C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x2000f4cb060019e000f00004400024c30007fffcc6e3380060039ce7ff8004049000511700020a2070002022,0x200054cb066139e30af185044c2400c31852ac2c42e339896c4a94a589b125049000d1000000000070002022,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W2 : Wire g17C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x20f000c28001e0000ffffa1800338fc0007800318fc3fff8003e0f800000001448a08a00294504a00010404,0x2050000280cbe00665433a1830f38fc0637831908b42c63831be0f8650ca0016ccb08000000000a00010404,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W3 : Wire g17C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x3008f030001fffff0000460003c0fffff80003e0ffc0000003ff00000000100105a6084828200084020000,0x8503003bea81f000f46006d40d740f8007be0ffc01b00dbff001d03a0108187a6000000000084020000,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W4 : Wire g17C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffffffffffc3c00f003fffe000000000780003ff0000000003ff0000000003fffffffff248aef079033440aaa049a8f3d1,0x2400900380ac00054002a78024bf60004a00253bd00005202914a50560ac232468b2a048a8f351881008380,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W5 : Wire g17C := ⟨0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0x3c000fffc00000000000007ffffc000000000003fffffffffffc0000000009a2458a1d6089115d5d02d48b88,0x24000ffe8043000218010c4e4870000010c00862f74a911c48e00001182302a88114d5902c48a88440920180,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W6 : Wire g17C := ⟨0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffff000000000000000007ffffffffffffffffc000000000000000000000cb618012214122a2005b530c723,0xffffffffffffffffffffffffffffffffffffffffdbffa000008c000460023031b382bf28a70553800000026013000002604c08432a68004b538452330921ce01,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17W7 : Wire g17C := ⟨0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x3fffffffffffffffffffff800000000000000000000000000000000000000249031484d84a85000711fb4484,0x3dbaf6afc7f0015780abc0001c00000038001c00000003801c00000380700dcc101010711530484532fc5010,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17V := [g17W0,g17W1,g17W2,g17W3,g17W4,g17W5,g17W6,g17W7]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17proper : proper g17X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17nd : (g17V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f0 : Basis g17X := basisFor g17X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g17V.map Wire.w) 11 (assignRows [9,0,3,4,1,2,5,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f0valid : (Price.mk g17f0 0).Valid 1 (wires g17V) :=
  initial_price g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f1 : Basis g17X := basisFor g17X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g17V.map Wire.w) 11 (assignRows [0,9,4,3,1,5,2,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f1valid : (Price.mk g17f1 0).Valid 1 (wires g17V) :=
  initial_price g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f2 : Basis g17X := basisFor g17X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g17V.map Wire.w) 11 (assignRows [0,4,9,3,5,1,6,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f2valid : (Price.mk g17f2 0).Valid 1 (wires g17V) :=
  initial_price g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f3 : Basis g17X := basisFor g17X 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff (g17V.map Wire.w) 11 (assignRows [4,0,3,9,5,6,1,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f3valid : (Price.mk g17f3 0).Valid 1 (wires g17V) :=
  initial_price g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f4 : Basis g17X := basisFor g17X 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff (g17V.map Wire.w) 9 (assignRows [0,1,3,4,9,5,6,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f4valid : (Price.mk g17f4 0).Valid 1 (wires g17V) :=
  initial_price g11proper g11bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f5 : Basis g17X := basisFor g17X 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff (g17V.map Wire.w) 9 (assignRows [0,3,1,4,5,9,2,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f5valid : (Price.mk g17f5 0).Valid 1 (wires g17V) :=
  initial_price g11proper g11bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f6 : Basis g17X := basisFor g17X 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff (g17V.map Wire.w) 9 (assignRows [3,0,4,1,5,2,9,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f6valid : (Price.mk g17f6 0).Valid 1 (wires g17V) :=
  initial_price g11proper g11bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f7 : Basis g17X := basisFor g17X 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff (g17V.map Wire.w) 9 (assignRows [3,4,0,1,2,5,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f7valid : (Price.mk g17f7 0).Valid 1 (wires g17V) :=
  initial_price g11proper g11bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17prices : List (Price g17X) := [⟨g17f0,0⟩,⟨g17f1,0⟩,⟨g17f2,0⟩,⟨g17f3,0⟩,⟨g17f4,0⟩,⟨g17f5,0⟩,⟨g17f6,0⟩,⟨g17f7,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17valid : ∀ p ∈ g17prices, p.Valid 1 (wires g17V) := by
  intro p hp
  simp only [g17prices,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact g17f0valid
  · exact g17f1valid
  · exact g17f2valid
  · exact g17f3valid
  · exact g17f4valid
  · exact g17f5valid
  · exact g17f6valid
  · exact g17f7valid
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17frame : Frame g17C := ⟨12,1,g17V,g17prices⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17vframe : g17frame.Valid := ⟨g17nd,g17valid⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto0 := autoFor g17X (assignRows [0, 1, 2, 3, 4, 5, 6, 7, 8]) (assignRows [0, 1, 2, 3, 4, 5, 6, 7, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot0 : Rotation g17frame := ⟨g17auto0,[g17W0.w,g17W1.w,g17W2.w,g17W3.w,g17W4.w,g17W5.w,g17W6.w,g17W7.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto1 := autoFor g17X (assignRows [0, 2, 1, 3, 5, 4, 7, 6, 8]) (assignRows [0, 2, 1, 3, 5, 4, 7, 6, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot1 : Rotation g17frame := ⟨g17auto1,[g17W0.w,g17W2.w,g17W1.w,g17W3.w,g17W5.w,g17W4.w,g17W7.w,g17W6.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto2 := autoFor g17X (assignRows [1, 0, 3, 2, 4, 6, 5, 7, 8]) (assignRows [1, 0, 3, 2, 4, 6, 5, 7, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot2 : Rotation g17frame := ⟨g17auto2,[g17W1.w,g17W0.w,g17W3.w,g17W2.w,g17W4.w,g17W6.w,g17W5.w,g17W7.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto3 := autoFor g17X (assignRows [1, 3, 0, 2, 6, 4, 7, 5, 8]) (assignRows [2, 0, 3, 1, 5, 7, 4, 6, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot3 : Rotation g17frame := ⟨g17auto3,[g17W1.w,g17W3.w,g17W0.w,g17W2.w,g17W6.w,g17W4.w,g17W7.w,g17W5.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto4 := autoFor g17X (assignRows [2, 0, 3, 1, 5, 7, 4, 6, 8]) (assignRows [1, 3, 0, 2, 6, 4, 7, 5, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot4 : Rotation g17frame := ⟨g17auto4,[g17W2.w,g17W0.w,g17W3.w,g17W1.w,g17W5.w,g17W7.w,g17W4.w,g17W6.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto5 := autoFor g17X (assignRows [2, 3, 0, 1, 7, 5, 6, 4, 8]) (assignRows [2, 3, 0, 1, 7, 5, 6, 4, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot5 : Rotation g17frame := ⟨g17auto5,[g17W2.w,g17W3.w,g17W0.w,g17W1.w,g17W7.w,g17W5.w,g17W6.w,g17W4.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto6 := autoFor g17X (assignRows [3, 1, 2, 0, 6, 7, 4, 5, 8]) (assignRows [3, 1, 2, 0, 6, 7, 4, 5, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot6 : Rotation g17frame := ⟨g17auto6,[g17W3.w,g17W1.w,g17W2.w,g17W0.w,g17W6.w,g17W7.w,g17W4.w,g17W5.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17auto7 := autoFor g17X (assignRows [3, 2, 1, 0, 7, 6, 5, 4, 8]) (assignRows [3, 2, 1, 0, 7, 6, 5, 4, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot7 : Rotation g17frame := ⟨g17auto7,[g17W3.w,g17W2.w,g17W1.w,g17W0.w,g17W7.w,g17W6.w,g17W5.w,g17W4.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rot := #[g17rot0,g17rot1,g17rot2,g17rot3,g17rot4,g17rot5,g17rot6,g17rot7]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows0 : Rows := #[
 #[0x4802004325000162ed00021e700417a000140610030ebb0021f5e0000f200031b4e002009700407300012ad00042d1e00107a60001b3c0000004321]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows1 : Rows := #[
 #[0x13faf00c304f01465020180c1d02118b00150df6001649200c68320143a8001f2dc000a5e4f01710df00e1cc001d256d00417fa01f750800a03d0017465d000006432100c,0xc2de7008683501e08d200c47cc025678e0022337002475d0263fe9000064321524c,0x1520bd0221d910230e340150df601674fa0165fc90162e4e016015c00b2c7e019389200b05070191e5401306fb000084321525c,0x2154ff0002f4a0182ee1000049d0180c1d01b084b0221d91000742d0005a1b0200b8a00f4e8c007597f01c4c8102108390205a7800f1d7a0070dcb01c10d001a05d201018d400007643212d8,0x10d7100627bf01203d3014175600d2d0f00825d0000742d00503ff00f4e8c02446820115112001649200010c0006129001247f901470ae005627000f0cfd0245f2f01149bf00905d200310620000753412258]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows2 : Rows := #[
 #[0x5a18de092094a00258de0884d7905e18de0987eb304f0cec00000006312d8368,0x5b4a14003535304954d002c475308c5e3a050334100d7e9d0070c4300b05f101d1c110150f2d0191c4702f757302e100306f2570004548e01c3f1b0007583412258012,0x4776e004068ad0770e550060ab40672dfe02765d106856f10000347251254066,0x85008100945d104f0cec04f697f064056107609010856b4f0480c420703dff05f55cc012778904860b2070226f05f480701219c407c1b2004e0cdd00006843212e0001,0x8a1da30720e4603616180363c060532b680530af608e1b3c000054321800a062,0x34672e0354d2e0900e710000000012258328,0x3235be092094a01e09af0326dd8031550603105060880fb4065150608530530856b4f0000003142250368,0x8657fd03f0eb900f07e400003be00000000212d8064,0x405d8c04036480a0082c0773f670763b9d069600500000000172503e4,0x3d527500c0bb10354d2e0336fb103d469b0355b9f033086100e5dd10805cec00e45240804e7b06148c10892a0e0000573412258002,0x76ea8093358c0967ca700a350807372df0140149000042315600c04c,0x24152d0782b510251bf409912690233bb607b0d2c0521d8103e35d10660289000053182425c056,0x300a6a04776e0067338f0105fb102d02d006000040008743215254012,0x373f10036dd303235be0322cdc03b1f0b0031b0f0325f30032488803b049c003072b0a30ed8055209200c26610643b0000c313206420a200000032412503e8,0x194aa1087748b0196ff1039170f03847b208754b7000084321500a066,0x5033410170d2308b09fa0a30ed807e26920491a5f050667b04b15d10463a900000003142258066,0x983cd009812230a2093e06e09e104c05d109861b309847a108f19110442e7c03c3df009b035e08f391d0440e8803c10ab09b26160000584321260001,0x81738501a0d670316c7005a338e0055b4002c16bf0840da30655c7007d0e9f05e338e0831a4c0000043216360323,0x5b4a1403209b203b3be108c11350325f3003b049c01f392105b1d4e01f6e010453e01045692107d189103d527503d075500005831422583e6,0x2913f8091049b0412d9602829aa041061f0280f6c000084321525c001,0x1e40a201713be0815611003535305b629105015f901a3a7e0562a4d036634e00006412382e0012,0x79725c01b3d2b0792bb001b6ebb02439e009c05f409912690233bb60382b9607216d00a13160000684321525c00e,0x7901820510e5606a4ef901b6ebb02057b209e414f03a753504a5690037530f000004328525c0a5,0xb592b015726a02d7b2802b261805677e8082612f07a79cd095071e0574aa0000054321700a05a],
 #[0x502bee00149e302b4dd902b135a0507adc0011e2f000074321600c360,0x9c416d06d474507100e005d0b3a00006432172d42a5,0x2a45a300f539802a149100f07e404344e20225d6904310960220e7b00006742312d8002,0x8b09fa08b481c0a2093e08b170a0a30ed8021182b02104be09a0b2d0a212640000064321260360,0x15a3c002609e05c0f95054115d002357e05e057e0010d7605e509e06b039500000432172603a3,0x9607610965c410742ae107473d9000031426700e054,0x5838ba05822b404d0ef206201180626a8a000000000524c3e4,0xd68f20185b7a0167ca001d5e7001068f80971b33000084213700e066,0x3f5eb902a45a302645ff00000000212d82a8,0x17480a039170f08a1da3016314b0161e1e09442fd09f55ff0085d7306300e507553e704906f80540a4b000765421300a360,0x7844b9051679e051485605137a00511fd606e09e1078183007b1dd802901c1000000000626035c,0x2509ff06a329a06a5ce406a1d6906a7d9c06a6bee06a0ce606a4ef906a251f02536320251bf40590457091049b0255d760911707000000000525c35c,0x1f3921034524e013042e0335527045692109d3c4d06c367b00000000043602a4,0x4271f007f7c2b0303a2e0a0082c05822b404260d007f6132030564a08d230f000007432835c0a5,0x694ca0062404301134dd0112a0300008431262dc001]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows3 : Rows := #[
 #[0xce5f9700000000002d8064001,0x5700a2e8423,0x250360321,0x400a2d8470,0x7e392a000000000400a3e80a2,0x7f61cc0000000000258323066,0xf29ed0534cd70000000005254066323,0x8258012063,0x2d801202b,0xa66aa200000001562500012d8,0x3d2f970ce5f970000000008010054066,0x9956ba08903c10000387142258012061,0x931fed00000000002580023f0,0x6e2af5000000005300a056368,0x706ca302065d00000000485360002056,0x5417e300000000082d80020ea,0x32c2f000000035700a0563e4,0x90250a0196ee6000871432535c00104a,0x4c115a0250cf606e63a102813260000043126258001052,0x86072000000000043602a4225,0x8133050966a20000004213600c04c045,0x9979460c70cfd0324b8509f3b6005718f9000000002625801205a,0x166ed90254ed9000000002626000e056,0xce38ff0000000042258066010],
 #[0x5b450106e63a1000031742600e04e052,0x5f471d03f771d00000000372e001005e,0x1b2dc9000000006700e3e83a3,0x3b132804839bc08478cd08a6e0c00000763212d4225010,0x8c1c080d14e010804e7a03f282f06e63a10000654312250010029,0x924e610071bd500000003172e0010056,0xbf2bb5000000000625000e3ee,0x2502de322,0x107fc70771138000000000225c1a5058,0x26036002a,0xb43e7a0b41e7a0881bfb0883bd30804e7a00000000052d8002052,0xa403ba0a24a4e00007432162d4066011,0x60004308f06d70384db40ad1ff600000000002d42a7012,0x9a1e6209a393400c07b900c2ac409e11fd09e37bf0154066000000000025c35c325,0x9142000944200066cd2006336a00000000072603a8001,0x5254056002,0x6b3409000685432125c001051,0x9d5a7e09d07070510029000004321626035c001,0xb505d0000000042726000242f,0xb45fa300e7e960802fa3000000000600a0522e8,0x9c11000c21bb404435f3000000000500c3e8323,0x356c2600a3e980b87f000437877000000000525401205a,0xc6258a00000421372e001002d,0x300a3680a6],
 #[0x3790a0356c260580e78005092900000754212541a5010,0x250062367,0x25836846e,0xb31733086585f07d0c9d07a086000000000082580020ea,0x2580640ed,0x2065d00406ae1000000042536000232f,0x6d2d680801d68000000003700c05a368,0x6675240465d9807b1dfd0174783000008542125c1a5002,0x3b02c00563d8f03b5c140566f1f0a416580601c1a000000007525c01005e,0x423408000000000626000e066,0x9824f80654106000000000025c225058,0x105fa00000000032502de3e6,0xab18d2013462501365fd00000000002d800104c,0xb34c130706ca302e21b700000000782583e6002,0x62d4066002,0x2d80640ed,0x5254056366,0x9d1c6909b1648000854321625c001052,0xb7078c04f448e000000000024c225058,0xb525d0000000000626000205e,0x2f7db702f23380d205b100d0e6f0008543216260001056,0xb353dc000000000125005c325,0x87568403041fa07a4cec07a6fb0054439702c2a77068732402c0b71068541e000000432125005e001,0x600a364327],
 #[0xa36fed069293000000000002e0001060,0x3654710ae1433000000004300a36006e,0x74581f02625f70526a150980fc70086ba107134f6000000000325c1a504c,0xb515d002055d002075d0076611f076438e00000000432d8066002,0x582600012e8,0xd52899000000000024c3e40a5,0x673d6c0a622bf02149da021566d0ac224f0c115ef067283d0a7363108b195f0a72d0908b792f00000862142e000103d,0x9071002149da00000000872d8368001,0x227a8e000000002125005e010,0x4b786f000000000025c0a52d8,0xc01e5206259e906275d60346c7903443a40c038900c5001b00000000062d42a7062,0x6d6fa30802fa30b25ef50491199000052841300a062056,0x114b9d000000000800a36006a,0xa9279a00000000002583680a1,0x891a4c0374d6801a06800801d68000000004636001205a,0xe1dfc01a467109f0c5f0b836e702a446d04d323402342bc0613797050513d000007184300e062035,0x632a4605c12df00000000002543641a5,0xa103ed0a12a5b0a142420a167ef0d40337000000006525c35c0a5,0x2d657c00000000002580622e7,0x8600c36846f,0x9717f600000000002603a3327,0xcc00f1078033300007643212d42a5002,0x8e121000000000002580622a7,0xa33a6f0af70b30cb4595000000000025000105c],
 #[0xca339b000432175825401202d,0x78436000204f,0x5c3af7000000045724c0013e4,0xa3600a2,0xac224f0642e230a548e70000000002258368001,0xbf44a60cf51cf000000000025005a2a7,0xc33e4b01409d3000084321525c056001,0xa01f801c3d6605967a0000000000024c066010,0xa06ed40275b96000084321735c2a7001,0x905ffb0903e0600025a6000000005424c0013e8,0x2014c0c40c1b0024dab00c64e409a5aa60a1424205e734d000000000025c35c1a5,0x3e3d4800085432172603a3001,0x7e013702257ca0000000024258324001,0xb1135000000000025c05d328,0xb115ac04b189104b394904b489304b60cc0bb17540b14923000000000626000135c,0x25001202b,0x9442008340020640414085696f000784321536000104e,0x9e37bf09523560950f400bc15e60bc3d0e09e11fd079198500000000002d42a505c,0xa21a110246cf60244dae0486cf804845310c9076708f5d88000000000600a06235c,0xaa597c022297c000000000700e06405e,0x3a76b802206b8000000004600c05c06e,0x801d6802550c70257e380c81fcd06c0c0b00007621432d8012029,0xa8125a0c115ef02902490000000005254368001,0x1d49360000000003254056066],
 #[0xb12fa5000000000525c05e35f,0x566f1f0240a59091717504e43b5000008543225c0a500e,0x374d6805718f9033140f0801d68000076243101005205e,0xd61a5f000000000025c05605e,0x694b500af4a6b06952a30af5bfa0000057431258001037,0x44581d04547ff00007643212e03a3065,0x82310800000000002500663a3,0x6a083004a568707c15d90b7078c03169f305a70bb000000000424c225054,0x372ceb06d1ceb01f2e990800ceb0000000054360002052,0xbf44a60b63d40000000005700a2d8062,0x32275f0b41e7a05708ec0be2ebe0804e7a000065432100e04a056,0x412bc600087421353602a3001,0xb643e701b2dc902d53f009c072100428e60000006431360323125,0x830aa20673d6c00000004672e00013e8,0x2d82a406e,0x5f00ac0122f67073392703f40ac000021843601004e052,0xb927d700000000312502e80a5,0x933b3202e59d202e357e0401d3a07d2a7a0400c1107d41c10000564321250002035,0xb23a5f000000000726000e062,0x258066360,0x99013c0992466044581d000000000000a36846f,0x6f3c2f072686f06f2505072064400000864312dc125002,0x804e7a0bd4c6f0801d680bd10be000000432100c05a056,0xab48d200000000002d8001068],
 #[0x835e7002f6e7008d289402b098e0000000026258328001,0x15406605e234b05e040305e734d05e5b8301513dd000743215625c00135c,0x2503603ee,0x3d2f9708108af0ce5f9703d0f97081235000000000060100540e2,0x3126001002e,0x8903c10c70cfd0804e7a01e710008947e70800ceb01e19ad000000341200a05a04e,0x3a597c022297c0aa597c0961a10000000000600e0540ea,0x1600c70920f27094778a039383e02550c7000021843601005e323,0x2f6e700000000265258360001,0x600a35c327,0xd00c5e0000000000260360029,0x3f312e0ba278103f6df103c276b03c723d000004321726000105a,0x180bf40b00d3e000085432125c05d00e,0x25832406e,0x106e0e04766f000000000002d412505c,0x754dce00000432182d801202d,0x5d3b840a8257f00000000002503e4125,0x55174900043217682d401202d,0xd205b10d315390000000000260001360,0xcd08b3000000432125005e066]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows4 : Rows := #[
 #[0x32540013680a1,0x2502de3663e5,0x25c2252d41a5,0x400a05e3641a5,0x2e03a30a5002,0x2541a501002a,0x2d82a8001035,0x25801205e029,0x2d41a505c2a5,0x12d8068001065,0x364a7000000000024c066010069,0x2d40652a8001,0x25c1252d42a5,0xd0ae300d5b41000000000026000105605a,0x260012062045,0x24c0663a30a5,0x25c12504c0d5,0x26032301002d,0x1004e05a1a5,0x26000105c045,0x25c05600105a,0x85432125c05e35b001,0x1e5e8800000000002d80120663a1,0x2d40a500204a],
 #[0x25c05d00e02e,0x424c00105a066,0xc4610000000000036001205a04d,0x700c368423125,0x400a3640660a5,0x2092800000000002503e40a5001,0x1b3107000000000600c0620563a3,0x32e0002052045,0x12500020660e5,0x25000102d260,0xc05c06e0a1,0x10052045044,0x25c0a500e052,0xa05e32305e,0x25c225054125,0x1263f70000000000254066001052,0x2e000104a03d,0x40669000000000025436800102d,0x3010052045060,0x2258328001035,0x244594000000000025005e00102f,0x2583232252d6,0x103973000000000025036600204d,0x1258068001065],
 #[0x618e0003ba30000000000258066001052,0x35c0a5224055,0x4500c04a05e3e6,0xe04a066323,0x25c05e323125,0x1592500000000002541a500c062,0x2125005e01202d,0x100c04a066367,0x25c05e00e02d,0x1e64bf000000000000e04e062125,0xe04c0da055,0x25c22500e056,0x260001052045,0x162bca00000000000100540e205d,0x2d82a3001062,0x25800e02905e,0x2177ed00000000022500020350de,0x2e02a300105a,0x2d8012056029,0xa05a3640a5,0x25005a2a5010,0x250062325002,0x84a3b000000000025c0a500205a,0x25c12504c001],
 #[0x25c12500e052,0x175761023187f000000000000c05a04e062,0x2dc125054225,0x25c2252d8001,0x2e000104a05e,0xa05a02d060,0xe29d000000000002d412501002a,0x2541a5060001,0x978dc01a076501f48ad00b33f5019425b000000000400e04a04505c,0x626035c001029,0x2d41a505c225,0x435c3272a3001,0x25806600105e,0x25c01002d052,0xa06635c2a5,0x32e001005202d,0x2541a501002e,0xa3e43a70a1,0xa1581000008743235c0a52a4001,0x101005e2a3056,0x22541a52dc001,0x2541a52e00a1,0x152b73000007642125c00135c225,0x250012056059],
 #[0x62d42a7012055,0xa05a02d050,0x2d40662a3125,0x24c22535c125,0x12503e800102d,0x2d41a5060001,0x125c125002056,0x22583e800104d,0x2d806600103d,0x3600010470d6,0x24c225054225,0x2d4001061050,0x2d801202904a,0x100e0520663e7,0x400a05e0623a7,0x35c0a500204e,0x250002066365,0xf250500000763212d422505c001,0x2dc12500204a,0xe0560622a7,0x25c0a504c125,0x26000e02d3a3,0x31250066002035,0x2d4125060001],
 #[0x2d42a5002062,0x85432125c055054001,0x2580020ea0a5,0x2d412500204e,0x24c22505c125,0x104b6f0147c9b000000000025800203d0e2,0x25800e02a051,0x258062327001,0x4200a05a04e066,0x162bca0225f80000000000001005404d0da,0x2d80662a3001,0x12e000105e3e6,0xa35c1250a6,0x7222a000000000025000105e062,0x142182000000000036000232b225,0x2d806600104e,0x26000205a04d,0x500a05a04e3e6,0x25c0a500c02a,0x25800103505c,0x225001202905e,0x1250060001035,0x2d8062327001,0x2d42a7012051],
 #[0x258364001051,0x825c22500c02e,0x12500120663a1,0x25836800204d,0xa05605a066,0x2d42a505c225,0x1004c0e2045,0x2d80622a7001,0x25c1a504c0d5,0xa05a36846d,0x25c05635a2a5,0x52d400104a066,0xa3e83a31a5,0x26035c001051,0x25c055054065,0x125001006a03d,0x24c05e001066,0x25c2252d40a5,0x25c05600d05a,0x2e000104c0d5,0x2d4066011056,0x5024000000000002500013e80a1,0x4360001045360,0x360001045048],
 #[0x4133c00000000002580013641a5,0x2503e80a1001,0xe04c05e0d9,0x2600010540dd,0x12503e800104d,0x525c056010029,0x25806600e029,0x3600010470d2,0x25c05d00e02a,0x25c05635e001,0x212d801205202d,0x1029bf00000000002e000242b06d,0x126000205a055,0x1258066002065,0xc3683232a5,0x24c2250540dd,0x130c00032882000000000000a05a02d2dc,0x20734302029d800000000002582e80a5001,0x26000105205e,0x25c36000102d,0x25c055054225,0xa06204e3a3,0x11718c000000000500c04a05e062,0x25806201042d],
 #[0x25c05605a2a5,0x4133c00000000002580010352dc,0xa3e83a30a5,0x2d406600104e,0x25c1a52d41a5,0x43212d42a7062001,0x1d2a36000000000000c3e80a52a3,0xa05a04e368,0x260010029056,0x600a06235c0a5,0x1c495e000000000024c01002d062,0x225800106403d,0x2d42a5002066,0x13336101311250130fde0132eac000000000025005e066001,0xa0540660a1,0x2e03a3066001,0x260360029001,0x181438006360d0000000000258012029052,0x26000105605e,0x260360001029,0x432125c35c0a5001,0x2543640a5001,0x26035c02d001]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows5 : Rows := #[
 #[0x25005e00106202d,0xc04a03d35c125,0x2503e40a500102d,0xa05203535c325,0x2541a52e000102d,0x2500013e80a102d,0x250010029062035,0x258001056062125,0x2d412500206205d,0xc06202d044035,0x35c0a5224001051,0xa05203505404d,0xc04a03d2e00a1,0x26000105605a1a5,0x2d40a501002a03d,0x2d41a505c001049,0x2e03e7002055129,0xe0620562a3225,0x25405600106202d,0x25005e066001035,0x2e00020452ab225,0x25c00135c2a50a1,0x100540660e1045,0xc05a0662a31a5],
 #[0x250010029062055,0x1005a03d04c04d,0xe04a04505c1a5,0xe06205e2a31a5,0x25401202d052225,0x2e001002d2a3225,0xa05e3231252d6,0x1005a03d04c1a5,0x2502e80a500102d,0x36000204d32f0a1,0xa05403d0da035,0xa06205605a065,0x2580660010370c5]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows6 : Rows := #[]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit5 := atlasRow g17frame 5 g17rows5 g17rows6 0 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check5x0 : Span g17audit5 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check5x8 : Span g17audit5 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check5x16 : Span g17audit5 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check5x24 : Span g17audit5 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check5x32 : Span g17audit5 32 37 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done5 : Region g17frame 5 37 g17rows5 :=
  atlas_sound g17proper g17frame g17vframe 5 37 0 g17rows5 g17rows6 g17rot (by intro j hj; omega) (join_span (join_span g17check5x0 g17check5x8) (join_span g17check5x16 (join_span g17check5x24 g17check5x32)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit4 := atlasRow g17frame 4 g17rows4 g17rows5 37 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x0 : Span g17audit4 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x8 : Span g17audit4 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x16 : Span g17audit4 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x24 : Span g17audit4 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x32 : Span g17audit4 32 40 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x40 : Span g17audit4 40 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x48 : Span g17audit4 48 56 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x56 : Span g17audit4 56 64 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x64 : Span g17audit4 64 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x72 : Span g17audit4 72 80 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x80 : Span g17audit4 80 88 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x88 : Span g17audit4 88 96 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x96 : Span g17audit4 96 104 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x104 : Span g17audit4 104 112 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x112 : Span g17audit4 112 120 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x120 : Span g17audit4 120 128 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x128 : Span g17audit4 128 136 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x136 : Span g17audit4 136 144 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x144 : Span g17audit4 144 152 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x152 : Span g17audit4 152 160 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x160 : Span g17audit4 160 168 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x168 : Span g17audit4 168 176 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x176 : Span g17audit4 176 184 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x184 : Span g17audit4 184 192 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x192 : Span g17audit4 192 200 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x200 : Span g17audit4 200 208 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x208 : Span g17audit4 208 215 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done4 : Region g17frame 4 215 g17rows4 :=
  atlas_sound g17proper g17frame g17vframe 4 215 37 g17rows4 g17rows5 g17rot g17done5 (join_span (join_span (join_span (join_span g17check4x0 (join_span g17check4x8 g17check4x16)) (join_span g17check4x24 (join_span g17check4x32 g17check4x40))) (join_span (join_span g17check4x48 (join_span g17check4x56 g17check4x64)) (join_span (join_span g17check4x72 g17check4x80) (join_span g17check4x88 g17check4x96)))) (join_span (join_span (join_span g17check4x104 (join_span g17check4x112 g17check4x120)) (join_span (join_span g17check4x128 g17check4x136) (join_span g17check4x144 g17check4x152))) (join_span (join_span g17check4x160 (join_span g17check4x168 g17check4x176)) (join_span (join_span g17check4x184 g17check4x192) (join_span g17check4x200 g17check4x208)))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit3 := atlasRow g17frame 3 g17rows3 g17rows4 215 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x0 : Span g17audit3 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x8 : Span g17audit3 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x16 : Span g17audit3 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x24 : Span g17audit3 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x32 : Span g17audit3 32 40 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x40 : Span g17audit3 40 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x48 : Span g17audit3 48 56 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x56 : Span g17audit3 56 64 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x64 : Span g17audit3 64 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x72 : Span g17audit3 72 80 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x80 : Span g17audit3 80 88 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x88 : Span g17audit3 88 96 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x96 : Span g17audit3 96 104 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x104 : Span g17audit3 104 112 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x112 : Span g17audit3 112 120 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x120 : Span g17audit3 120 128 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x128 : Span g17audit3 128 136 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x136 : Span g17audit3 136 144 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x144 : Span g17audit3 144 152 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x152 : Span g17audit3 152 160 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x160 : Span g17audit3 160 164 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done3 : Region g17frame 3 164 g17rows3 :=
  atlas_sound g17proper g17frame g17vframe 3 164 215 g17rows3 g17rows4 g17rot g17done4 (join_span (join_span (join_span (join_span g17check3x0 g17check3x8) (join_span g17check3x16 (join_span g17check3x24 g17check3x32))) (join_span (join_span g17check3x40 g17check3x48) (join_span g17check3x56 (join_span g17check3x64 g17check3x72)))) (join_span (join_span (join_span g17check3x80 g17check3x88) (join_span g17check3x96 (join_span g17check3x104 g17check3x112))) (join_span (join_span g17check3x120 (join_span g17check3x128 g17check3x136)) (join_span g17check3x144 (join_span g17check3x152 g17check3x160)))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit2 := atlasRow g17frame 2 g17rows2 g17rows3 164 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x0 : Span g17audit2 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x8 : Span g17audit2 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x16 : Span g17audit2 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x24 : Span g17audit2 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x32 : Span g17audit2 32 39 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done2 : Region g17frame 2 39 g17rows2 :=
  atlas_sound g17proper g17frame g17vframe 2 39 164 g17rows2 g17rows3 g17rot g17done3 (join_span (join_span g17check2x0 g17check2x8) (join_span g17check2x16 (join_span g17check2x24 g17check2x32)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit1 := atlasRow g17frame 1 g17rows1 g17rows2 39 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check1x0 : Span g17audit1 0 5 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done1 : Region g17frame 1 5 g17rows1 :=
  atlas_sound g17proper g17frame g17vframe 1 5 39 g17rows1 g17rows2 g17rot g17done2 g17check1x0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit0 := atlasRow g17frame 0 g17rows0 g17rows1 5 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check0x0 : Span g17audit0 0 1 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done0 : Region g17frame 0 1 g17rows0 :=
  atlas_sound g17proper g17frame g17vframe 0 1 5 g17rows0 g17rows1 g17rot g17done1 g17check0x0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g17bound : ¬Feasible g17X 12 1 (wires g17V) := by
  apply full_raw (positive_checked (v:=g17V) (by decide +kernel))
  exact whole g17done0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19X : Word := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19C : Charts g19X := ⟨unpack 0x10887a5d0e872791c2e0f0781c0d96c345a1d066b3196ca6532791c8e2b1589c4e231186c2e170984c1e0ee970b4592c154aa54aa150a4d228b45a25128541a0d028140a05028140a05028140a050281349a4ca6530984aa512592492452290c82412090482412090482412090482411c8d4622d168ac56271188c36190a8542613088442211088442211088442211088441e0d0681c0de8f0783a5d0e872385c0e06cb61b0d46a349a4d168b3598cb653298ac56231186c2612d164b2582c154aa54aa150a45128942a05028140a05028140a05028140a05026934994c2612c944a24d229147235188b45a190a854221108844221108844221108844221106833e1e0f0763a9c8e471361b0d46a349a4cc6532988c46130970b2582c158aa5529148a25126934984c2592894472310c84422110884422110884422110884421e0e874381c0d86c35198c45c2c160ac5229130984a2511884422110884422110884422110884421c0d06832180c06030180c06030180c06030180c0582c150a84c2211088442211088442211088442211070341a0c06030180c06030180c06030180c0602c1607030180c06030180c06030180c060301806030180c06030180c06030180c06039048241209048241209048084060c42031249206240a29006a81080d426114190420314092482112008844221108844221108844a2211321017118881818061601a068501a13080308908060308c45081110884422110884422110886060306030222110832108485030840d08830184210d002242108841821,unpack 0x8072590683259182c0b0700c0c96430581c064b2192c84532590c0e09158144e011182c0c170104c1604e87034190c1142a44a2050249220a4582112050120e4b031482c01a0c9451d0d045200c855141a4486510180a8510582092042280e4b031482c01a0c9451d0d045190a841148944229128a416251080c160902054041392c0c520b0068325147434114642a04416090281404e8d038325906832305806064b4190d02a34124d060b2590c96422982456011182c0410d12432480c1142a44a205024410890392c0c520ad064a29007434114642a1024914894822124900a249208145225108a44a090205c960629056832514803a1a08a321501104813a1c0d0743a1c0647034190d02a34124c86422980446020950925024150a84528048a0412491490442492014452210725818a415a0c9451d0d045200c854021a0c85430140d06434190c05428120a850091208848051164b031482b41928a3a1a08a32150800214090281392c0c520ad064a28e868228c854100405024140284b25818a415a0c9451d0d045190a82001050240b92c0c520ad064a28e868228c85408020281205c9606290568325147434114642a0200b25818a415a0c9451d0d045190a804018a45229148a45229148a450a8241960415148a0484822120ca03810560703018a02815018a453031412090482412090482412092040a0502424241202a0482810288009090241240124002440120901224008040201008040201008060209124100301008101004050900405008100802809000202808040801,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W0 : Wire g19C := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc4c10398cc00b1800001080000fc60004c4481d3200820001075b0003090d9a33c9400001c73fffe20001ffff600070003fff000000500fff3839bdfff3818ad,0xc4c10098c400b1a910010a91004c6a44444480d320082a841014b542100048a11c95510000112a222a88095116a8835441511000403712000401602fff3818ad,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W1 : Wire g19C := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0x210a52610c040200006430000b2180007c00061c3b30c0006249c00031632604c0fffff66a4c8000c0006400080007fffffff003014800000a5697000300a110,0x210a52610804024086643408c9219023180002040b30d04362494821a0210200402208762a44c118d0462608c90464823608e000a54860003a7c82000000a110,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W2 : Wire g19C := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1c01f2583c000181c00013c6000072081863c4010000038e7fffc98c38470f180008738f0001000078000ffff9fffc000001180008000c7d602000c55602,0x40052583c185181c18512c6061462080801440106140080130a498438470518c508508b18a1062858c50262893148c50fff1a808dffc18008d000c55602,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W3 : Wire g19C := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0x600607e0080c000000600001c07ffff8070e07c003e00007c0f80000e0fc0780fe0000f83f00001ffff80000ffffe0000000000e45e62000228000000c6d602,0x600002a0080c001a206001a4000a0698070a07c003e00c9340f8064820bc0280ae01a228370034860d2801a4c0d3606901a4000200860001c45602001028000,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W4 : Wire g19C := ⟨0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0x380c7f80031f000001f800001ff800000380ff8007c000007ff000000ff0007ff000000ffc000001fffffffff000000000000000a44820ffe18008d000200820,0x380c7f00031f005245f805249fb0149203805f0007c015124be00a890df00056e002a44d7c005491952576a4a15240a922a48ffe9c408d000200820000000000,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W5 : Wire g19C := ⟨0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xc00f800003e0000001ffffffe000000003ff000007ffffff800000000fffff800000000ffffffffe000000000000000000000ffc1b808d001808000ffc18008d,0x3e0000066ae5006e000001b029900000553401b8000000d8fffb7000000066fffee80dc00360006c0036001b006c00183c000ffc18008d000804000,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W6 : Wire g19C := ⟨0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0x3ff0000003fffffffe0000000000000003fffffff8000000000000000ffffffffffffff000000000000000000000000000000002002110002000040000002150,0xe50000003e9d48378000037000000dc03fffdfbf000019c000000ce0fdefdffbfdc3780000006e001b80037001b800dc0370002000000000002110000000040,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W7 : Wire g19C := ⟨0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0x3ffffffffc000000000000000000000003fffffffffffffffffffffff00000000000000000000000000000000000000000000000010000000401602000010000,0x3ffffbffac00006380000638000018e00166f7febaacb9e07f7fecf030000000000338000000670019c00338019c00ce03380000401602000010000000000000,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19W8 : Wire g19C := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0x3ffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000ffc5ab7df000182204002028040,0x31afffd5fc162b7c0151afc01fff5f007c00000000001e0000000f00000000000003c000000078001e0003c001e000f003c00ffc58379f002028040002500088,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19V := [g19W0,g19W1,g19W2,g19W3,g19W4,g19W5,g19W6,g19W7,g19W8]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19proper : proper g19X := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19nd : (g19V.map Wire.w).Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f0 : Basis g19X := basisFor g19X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g19V.map Wire.w) 12 (assignRows [9,1,6,5,0,4,2,3,7]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f0valid : (Price.mk g19f0 0).Valid 1 (wires g19V) :=
  initial_price g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f1 : Basis g19X := basisFor g19X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g19V.map Wire.w) 12 (assignRows [4,9,1,6,3,7,0,2,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f1valid : (Price.mk g19f1 0).Valid 1 (wires g19V) :=
  initial_price g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f2 : Basis g19X := basisFor g19X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g19V.map Wire.w) 12 (assignRows [6,1,9,4,3,5,2,0,7]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f2valid : (Price.mk g19f2 0).Valid 1 (wires g19V) :=
  initial_price g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f3 : Basis g19X := basisFor g19X 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff (g19V.map Wire.w) 12 (assignRows [5,6,1,9,0,7,3,2,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f3valid : (Price.mk g19f3 0).Valid 1 (wires g19V) :=
  initial_price g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f4 : Basis g19X := basisFor g19X 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff (g19V.map Wire.w) 13 (assignRows [0,4,7,3,9,5,1,2,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f4valid : (Price.mk g19f4 0).Valid 1 (wires g19V) :=
  initial_price g17proper g17bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f5 : Basis g19X := basisFor g19X 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff (g19V.map Wire.w) 12 (assignRows [1,6,5,7,2,9,3,0,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f5valid : (Price.mk g19f5 0).Valid 1 (wires g19V) :=
  initial_price g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f6 : Basis g19X := basisFor g19X 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff (g19V.map Wire.w) 13 (assignRows [4,0,5,6,1,7,9,2,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f6valid : (Price.mk g19f6 0).Valid 1 (wires g19V) :=
  initial_price g17proper g17bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f7 : Basis g19X := basisFor g19X 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff (g19V.map Wire.w) 13 (assignRows [6,5,0,4,1,3,2,9,7]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f7valid : (Price.mk g19f7 0).Valid 1 (wires g19V) :=
  initial_price g17proper g17bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f8 : Basis g19X := basisFor g19X 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff (g19V.map Wire.w) 12 (assignRows [7,5,6,1,2,4,0,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f8valid : (Price.mk g19f8 0).Valid 1 (wires g19V) :=
  initial_price g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19prices : List (Price g19X) := [⟨g19f0,0⟩,⟨g19f1,0⟩,⟨g19f2,0⟩,⟨g19f3,0⟩,⟨g19f4,0⟩,⟨g19f5,0⟩,⟨g19f6,0⟩,⟨g19f7,0⟩,⟨g19f8,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19valid : ∀ p ∈ g19prices, p.Valid 1 (wires g19V) := by
  intro p hp
  simp only [g19prices,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact g19f0valid
  · exact g19f1valid
  · exact g19f2valid
  · exact g19f3valid
  · exact g19f4valid
  · exact g19f5valid
  · exact g19f6valid
  · exact g19f7valid
  · exact g19f8valid
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rootStep := Step.binary true g19W0 g19W2 true true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rootV := rootStep.after g19V
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rootPrices := g19prices.map (fun p => p.advance g19V rootStep)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootValid : ∀ p ∈ rootPrices, p.Valid 1 (wires rootV) := by
  intro p hp
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
  exact advance_bin (g19valid r hr) (by simp [g19V] : g19W0 ∈ g19V) (by simp [g19V] : g19W2 ∈ g19V) true true true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19frame : Frame g19C := ⟨13,1,rootV,rootPrices⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19vframe : g19frame.Valid := ⟨by decide +kernel,rootValid⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19auto0 := autoFor g19X (assignRows [0, 1, 2, 3, 4, 5, 6, 7, 8]) (assignRows [0, 1, 2, 3, 4, 5, 6, 7, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rot0 : Rotation g19frame := ⟨g19auto0,[extra,g19W0.w,g19W1.w,g19W2.w,g19W3.w,g19W4.w,g19W5.w,g19W6.w,g19W7.w,g19W8.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19auto1 := autoFor g19X (assignRows [2, 1, 0, 5, 7, 3, 6, 4, 8]) (assignRows [2, 1, 0, 5, 7, 3, 6, 4, 8]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rot1 : Rotation g19frame := ⟨g19auto1,[extra,g19W2.w,g19W1.w,g19W0.w,g19W5.w,g19W7.w,g19W3.w,g19W6.w,g19W4.w,g19W8.w],by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rot := #[g19rot0,g19rot1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows0 : Rows := #[
 #[0x100ad300d18cb005092700d05b40000645005179d0041efb00600170010d3700113ee00a09b400f001600c0b1400202f00040e8200a101400b059300800940090c8100707820091e1a007191b00e0ad800305d90296431785]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows1 : Rows := #[
 #[0x2d055300a0c9800a17f704c02cb0a80a9403904340810a93088059409c0edf020046107b0d6d04c10c80391a910280b110a3064e0900bcd053014f07200bb05b063a06b0bb9079055806000590210dac063032e0540fd607805580293645817258,0x360c450a7072607a05d4020046105f090f04119bd04e0898062072502c049f00b1ff4001049c044120606c17430a2124403a1a8d0400f380751bac01d1a390740ec00640b3404709c10820c4a066074b0330fed0561e7a06a1fd60840e630496572381158,0x591ff30590cdc07b0d6d02f162602f05ad0380cbb05207bc02b03ac0490eaa02b15450491046096031b0070e190964317852006,0x3212df0320fc506000590a40a28066074b0661dff06f0533089060f0190fee03b00cd0191fdf03b10be068029607d03720964238751001,0xc1d9009b1b880800be404c10c803c01bb07c12d400b1ff40410e6e0260c7101212d305c095206213d202f05ad08e185004213510251f3e0a00d9501f14950871f6e07e0d1400296478530c6,0x24031609d0d7605f1150095071602e0d750a108760800be40981d7300212f50930df301c0b7c091167d03015c005100c1094213785600e,0x8b02cd0561e7a09d0d760a80a94056044409d1bec07c034d02c049f02c1b5307c12d400804de0670fdc03d1bd103d0d6a094077008c06c10270271023096806e08b909704690170f270a40a280090fd60140b860496827351170,0xd06900731171057020c053014f091035a03d1bd10a2124403a0fa808a1af601d1a390490eaa015076d01106b004d0ad70130a1a0429631578056,0x77107f01106b00930df30280b11077011001117410931c6904203ca0670fdc044120604408ba09a0c3d027027105207bc04213510050ad7086010b064293187506e,0x990b8f0a3064e01c185906c174308d1a7003f0bd00400f3802b03ac0251f3e06d00d0055115004f09d702a0b9400006950691baf05e1fd60431f190249361578058,0x2208c200f06ba095071600403a30390434098058c00114f30260c71076138208d1a7006d1c0901608c707104710291bcc062072507f0ff401a191f009641758213f,0x691baf00212f50690c40002016b08e08c900804de076138204b04e209407700380cbb08e185007609df055115005502e903704a600e0fa40920fd6070060a0326498751070,0x4a0a22065181a0a10876065050308805940a116ec08306c0027027101e0e8801d1a3901e154201d00f30a60ad701b06880964321875127,0x350d1b063032e024031600a17f709b08ea0a7072600403a3065050305604440590cdc00f1a0007311710690c40050013101117410060a350101f23034053605804c70320fc505d1fd601805e90296874153270,0x5817de05804c707905580a01e0e0170f270820c4a082130101608c70610f2603e0a270a00d950161f2403704a600e0fa402a0b94000069502a1d2d000182e08f0a3205a0b0e04504f00a505cc04514e10a515bd031079509e08710964213785002,0x30f2102e0d750810a9302e1beb012034c01212d304b04e203f0bd003f1d690610f2603e0a2709407700400f3804015f20850fd60460b870964327851128,0x2d055300c0e090360c4503612fc02208c20030f2104a0a2200c1d900221f1f0990b8f00d06900991d2800d1829048007e09f0b7c0642317859014]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows2 : Rows := #[
 #[0xc900621f1115700e194c15606cb17209fa0680ad60f1017a004042e1e915c300421957680020de,0xe213aa1a700741e0012213e1ffa20d1ea50941625159129906001260cd13af05f119f166173b00000875630b6156,0x1100a9b15713f5000000001407000c,0x1b10fca1a9025b0000000009128016,0xe803d8000000002113f270,0x1d610f61d6018706a0e0d0ee0a220050cb406a1d941be052d0fb0ad60810b690811c620de152d1690ad60a005e20de052d1691ad6093164287506e002,0x5c04491c0016600000000012700a3,0x461b1f04608080dc08990990a7919c031405106cd0391f65051185a03900f50964318752006029,0x5d09301040eef00000000210701f7,0x2040f9e193023309c042b0fe05e6208087b15502600000000792170002,0xab171b10e06ac00000000192583f6,0x1fe0e8910a01a700b17080e10bf01541cf40e7077a12f10e71ae1ae5000002641714825e,0xc301d909818cb10c063308c00c905012580ef13b400f0eb2101116300642751891d6014,0xdd005d203115202f19470e0025809f119b0631427589056014,0x1e915c31e9065408802dd1040eef021018408812641cc09fa0fb0ad610d1a9810d0a890260d3d00642187590020f6,0x14f10c1000000002113f370,0x1b31fe910215c300000000003700a2,0x17e009e150128810703a903a1dd80240ad60540aea096423158705606e,0xd0071920c06090e61ebd000000218612825e,0x8904090f21e691c802430ca035718c0fee019087f011051903d0bee11a08880bd07b117c044b0942631875056001,0x5e1ebc05e0e430a807430a818dc07501690b101960d203d10d21f9103703fe11f092a07a042b0730de0053030f0860e0d0964317852170001,0xd40a051d90ba70000000098056070,0xcd04060200b8408f18fd04903bb07103ac003189a0ad09760f0063809643758120021c7,0x1040eef02101841ba037c1760fd61e2087b194026000000729130021f8],
 #[0xb0091f0e803d8144053814f0a350b301a614c0f1d067044115a098e1aa145a1151f58083177610302421461d400963217854270001,0x20109f00a917f809d002712b0ad305b0d870f907150342965871001058,0xbf004d05f119f08a10d506404f7121024307911911c31ce713a1fd309641875320b6002,0x19e138e19e00771e401081a2040415c04301181de50d81e1111808b80d808e40964321875127001,0xf613161510f8a0000000536048010,0x2f00010cc1e5210713c61740f6006c1ad609e10aa0432196875046127,0xda09fc1630bb00000000068127058,0x19b013a0ae0e9f1711b9100000968711d6070,0x12f10e72170bc612f0ee11b6092d1740f6016f0bc01360e72185073a000000041714805e,0x1f803d30000000000258078,0xe204010500b7f10c06331620e6a1bd1f59006417582913f014,0x5d09301ba037c140023300000000121700a3,0x15004a31df02981881aad1c40c6a0000000436270010,0x11c00b9000000145604825e,0x500b7f03519d307b1eb41e01f730200b841c60b0300b09e219006eb07e17c40b712440bf1bdc00000785420c613f,0x10703a91ca0fd010713c61ca1e461080ad620e0f29096421385706e127,0x15817971470a5c1b6092d158059401c0b8817e009e01401381cf0a24000000002706e258,0x8a10d509b195400000024530b6048,0x1120fd500000013860020e0,0x251ed516512400000086312058008,0x2170bc60e40125141046714909a9023112921e0d4114a0eb000000081631581f6,0xc301d90c31fd30dd005d1330ac71eb05fc0400e160000006497258016,0x183150f21018770000000036128010,0x4107f012908e31371a791e505d808b1c5713916d700976845320c6006],
 #[0xf4090512403be183051e18e0a1b1100a9b0f6018c0f70746033126f13b1aa1000962785400a02a,0x3189a1dd09fa0030ef70000000312002040,0x1d10d3f10e120b0471e551811ab90a20d5e0f9136d06e0e36028044918a115513f0c1e06f02310196428753001270,0x1d703090000000000158078,0x1df029819706a807f06901190c5e0bb15101950ad60420c6409216875342700a1,0x970c9d00000000002703a8,0x9818cb10c06330e213aa203115202f19470b908cf0781cee05819650000000029158016,0x1920fd500000001390020f8,0x21807e71fd0a750000009312070008,0x7b1eb412207461d80347000000041213f258,0x1c802431740f60072170a20a136c0000000008056148,0x1811ab915e14e51480acc0c2151c15b08f319902ed08e08d4045120a02817f10429635871001056,0x8c00c91e30d4b077060a10a1c7a10a01a720c060900b170808503d300b09e212908e3082068706900ce0d90caf0d911201f4072f1c9104d1c90bdc00009654870c61d6,0x149106f10713c602c10690f20cd00a818dc0000007325046170,0x2120a5d164051b164150c1dd09fa1110ad6021018400e194c00e000600196487520021af,0xa60e68126074400000008620581af,0xe194c1f00c6000000000180581a7,0x980d7c17d1bd010a01a70e415d61e01f730aa133d00709400af0c681e8044107d0d811341d0012f0ee11280a5900000872530c6147,0x15817970061f9f01803150aa0e890e10bf021f05e21370af2082068706a0e0d1d40deb000097518606e1d6,0x11c00b90b21b6f0a61ccf02711cf013124f070193d1ec145f0300bfd0630e8300d0cb61961f4c2000d7f04d02930ac0f4c0610d7f0319627854048001,0xe10bf01411b1b0aa133d03e19311b6092d10713c61821bb61e11c7b000000013506e148,0x15f117617209fa0000000361002060,0xe61ebd0e60e4413d0056126074412618dd1cd092f16a131316a0de30151b5a1ef0b860150b5a1ef1b860319647852128001,0xb908cf20203b020605991e8164702311291540c7e06001260a416630c015bd11302c0123134901d104c1da0c1401a09171b80ad602207d909463857121580a1],
 #[0xef13b41620e6a1b10fca0ef033b16214ca12c0c3812c1dd11ce00771a60bac1ab054a1ab1a7c1910ff6000642785901402a,0x16e087703a1dd80160dfb0ce0d3e0319647582056006,0x2f194702f00010e301ab2160d590321648759127014,0x207055913d005600000000920701af,0xc301d90ab047d092171a0d007191b004e30091b6512f10e704119f31e30d4b07b0717158179710b0d3e03402c001f083f09601de14b1cec0950c5c00000541871d6257,0x17904a407405991cb1d8e0d40a050ba00ae1d2193c04c05d61421e3c0680ad600019451f61e3c0b50ad61bf05080120e3c0ff0ad60631942758056002,0x13e1ffa09a052210f09c40000000001158226,0x70193d0700c6f00000065840480de,0x100016621b044900000000052700a6,0x1881aad0c5151013c08e705a18a903b1e9c0c419040a71ef71840fa9065059f094231758600e029,0x3a1dd803a0e691370af21371a791050f421800576031964875206e006,0xdd005d1740f6016e087717e009e0fc0ad621c004e0642931758046056,0x950c5c0951a590c60ae011e054d0a30fcb1ad013e0000004627258002,0x13124f1b5136000000019540480f6,0xe7077a10713c603817400471e5502a07570000007651148076,0x17904a41dc010b0000000548056228,0x1e9065405c044908719481ed173000000000130022f8,0x3a0e691190c5e046080803c174900000003120062f8,0x870cf008719480ed0e4408f18fd2120a5d1e2087b0ed1dcb08f0f5a1920fd50fb0ad615606cb15618640326418579002076,0x3402c0130059103410bd11e054d0b40b5a221006200000000002580a2,0x52026406217c500000024530c6128,0x1001dbb1b31fe91750cf00f5069f0000000069370002,0xfd1f0c1121fd508d1fd50a11fd50000000054048002,0x17d059505912fd1a700741611e190cc0611206059913c12420c11c13000000001415800c],
 #[0x10e06ac10e120b1360e721e7008f1250def20109f0145054d1480acc1870b601af06bd1f30c3c1d10d3f0642937518001258,0x1fa0fd500000001320021b0,0x10c063305912fd00b09e20f006380db191e000076528113f056,0x17e009e20f09521d10d3f044086d0000000001258076,0xaf17ba09a052215912990be0c6013114331a011bf1380a8a010194c00000023811580a2,0x10713c604a07ff19e007714405380000000000127270,0x1360e7214a0eb016c078115b12300a917f820b0a4708e08d402e044d090069c06b1529047088e0429365871001158,0xa0d3e1470a5c00a1bb4018031514104671411b1b018129c0ee0a222040f9e000085713206e16f,0x14d09fb16d02cc05b0d8705b1d7821902a00a917f80a907f50396487512001038,0x1e906540ec0f580000000051048076,0x16600de1280a5910f1fba03604f20d70cdb0be15a90d60dd00bc10e20000000241148002,0x1330ac701f083f19a000b21400080a50b101b902e401f163c1350e1f17805d100c00dc0ea0ad621505e102934875162580a1,0x20d0f0b14303d91f1081a00000000120481cf,0x20d1ea50b20368000000683205813e,0x21e0d4109c042b1d301a41f5018400000007211700a2,0xf907150f9136d21902a009d002709d101816d02cc0364298571001070,0x18619401d003f9207055918608c71d01a561b501c71b51360001169c0010795116006000806091c50115116106000816090316427859070001,0x127030a000000792113f070,0x10b0d3e0eb001210b1b3b1200acc11705db0800ae000000000172580a3,0x17e009e0e50c4508915870b310280000000015046370,0x71b46094162514313cd09108d40c717bf12a154b06d0e161c70cd800000000211580a3,0xd70cdb03f08d100000000051480a6,0x1d01a56000000093207013e,0x1d601871ee0428000000005406e228],
 #[0x1d8034721104a71d819a41cf0a2401e0d7104f04241f70eef1bc0a4c132054d0cb00621e60bbc17006bd0932167854258001,0x9601de0961fd80c900621200acc1c10fcb1ea013e00000001370022e0,0x19f0d3300000000001582a8,0x4119f304107f016e08771b902e40dc08991fb076600000031720062e0,0x92171a0e7077a0e401251fe0e89077060a018031505e1ebc000000768117025e,0xa210780a20d5e1250def0310ad70d3003a17b037c17a159208e08d417a058f08e18d10964218573001036,0x14b0f571c9104d1341d001c60b0305202641d411e3198018901718590e90e5a0c80fb707c0ee004e004016704af09627184530c6002,0x1141784000000042113f048,0x17d1bd003519d3059013400600b30f4187d02d18ad00972845360c600e,0xd007190d0151600000000021282e0,0x7d18d00f006380cd13af1f1115700e194c09108d40291dd30b61a2800000006130021e0,0x1d502340b8037b0000000079127070,0x1ae01231e1033220a0bb905612251de0f741521f1002b116216b0c600321b651090db41b408b50941673852158001,0x1a80fd51fa0fd51a81fd50000000002128002,0x1c0b8803e027d03e19310661bf11a5019d0660cea1a51296189066a0930c13064293187506e001,0x5501141b20bb700000468711d6228,0x1740f601ff0cf31e4010821104a70000000051127258,0x14e074c02817f11e7008f14e13a4028044916c078116c1e3504802d717b037c064293857100106e,0x1cb02af0cf13000000000025046128,0xd105e600000000001703a8,0x1930233213037c00000000071700a6,0x2711cf000000453204813e,0x8802dd1861940000000019607025e,0x1cc09fa0000007139002078],
 #[0xc60ae00840acc00000005282580a6,0x1611e190cc0611150128804319be19d0901063192758405600a,0x1920fd518d0fd518d1fd50000000009070002,0x15004a300a0d3e1ca0fd000600b321d09bb1ac0fec091432875606e00e,0x21018417f042b00000007210701a7,0x1a7125503519d318e13af12d150b1bb1064009417582613f00e,0x1e516511e505d821807e70251ed502500711f908130f314670f305f4000964785200602a,0x10601cb10610410d51d510d504972090ad618f0d3106491875321700a1,0x5912fd12403be12e07a9009675182413f00a,0x12c0c381fc069a0000000089058016,0x50cb401b08f8000000007206e128,0xab047d0df03ac0e7077a0b0091f00000000161d6270,0x91b65009096218b064100000000002581a8,0xa0d3e1ca0fd010601cb0c5151015307b90000007326170010,0x20ba71760fd60ad09761fa0fd51110ad60021b2e0ad1fd30260d3d004042e00415c71e2087b0291dd30290dd0096437851200203e,0x1eb05fc00f0eb20781cee07803a500f1e391f20b7522006ad168051311b004b1681a4511b157d1b70fbf1770af70642318759014029,0x961fd806900ce07d0d810200b840f012e508812640ed1dcb076188915f0f6104b00400021b2e096218375400214e,0x1ca0fd00cc1e521a117c71730378032194875612700e,0x20308151610669149106f0741ac303604f20000813752046147,0xc900620f8054d000000051804805e,0x47088e0471e5514a0eb014a15670c2151c0c2050d14d09fb0310ad721902a01c207cc17b037c0fa0c8221a01b12050d5e0642398517001170,0x1c10fcb04b125204903bb164051b0291dd307618890711a1810d1a981120fd50680ad60f113220870cf0032491587600205e,0x1d502340da09fc0da10b61a4087f11d126311d0d331a30aaa1600ad615d0aaa1110ad61a31aaa1601ad60321964875127002,0xdf03ac20203b019706a800000000011582f8],
 #[0x92171a2170bc609205171470a5c19a000b00000072191702e0]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows3 : Rows := #[
 #[0x740ad5000000005604600205e,0x2a021800f12180ee0cae000000009407000104e,0xa9030c1c41a59000000003100203e25e,0x10020401c5,0x17912e01f5100a000000000800203e0de,0x1e50ad5000000007206e0021af,0x3406e0c600e,0x70a4500000000000c6147123,0x1b9121a02218c60681a5500f03220000000958070001045,0x11405e810700c400000000000c62561a8,0x3206e16f010,0xbd114400000000010c613f056,0x1bf0fe71d4052b0f108041f406e900008654312580a105d,0x7d1fec1170b8615a1aa51531c050f91105168118512718730002965784048001055,0xdb0bdf00000000050020ce1a7,0x1b8028205a19740b901720e51eab00000009181d6014031,0xdb0bdf00000008741480a2001,0x1ae0f050710a22121096802f1d3f1d70ad817710f30042976531056001065,0xda093b0fe0e3b1320e3b0000000001056002037,0x304b81680ee400000000690580010f6,0x1de0dbb1de1bb81c8059c0700063000000000006e258029,0x270b590000000001128001037,0x8205600602a,0x1ce1f841550b4100000000131d600204e],
 #[0x1c906e202600ed1030e51000000001806e16f25e,0x431e5308c16ed05612b00096432175056001067,0x38188100000000001580a1046,0x1bb08f71340ffb0a318f70a308f7000000000206e128001,0x1a70b7b01c06be000000000006e001258,0x2118d319307270911cfb00c1d0400007425131480a1065,0x1840ac91d809590000000000258001076,0x1a102c210b125700000004811d6257121,0x11d1e861c60e2c0a91c33000000003100214e1c7,0x1a6023301d0d5d00000000070020f61a7,0x1d1103c11310be09643821751580a1001,0x19c045c1ef1ba6054153500000053211480a116e,0xb80ad50ff029c0c11ad50091ad51631ad5000000000805606e002,0x5048008031,0x2070f9e1a602330e308431c50919000000000000203e0f6,0xf908070360a4f17d0d0703f1a4f00000000010580011c7,0x183086506a1653000621857300104606e,0x791ed51c4085317902ec20519ac000000000300203e04e,0x4819e91cf02d411e1b340000000000148076001,0x14800102e,0x13b0cc205e02ae00000000000561700a1,0x61d600a02a,0x11580a3,0x1ec1eae0000000059046127014],
 #[0x17f08830ae088309e110a000000004604800105e,0x180103c1800039000000319700103616e,0x14800102b,0x5600e02a04e,0x2000d4000000000001d6257122,0x8e0cf70d00eba00000000060b61d600a,0x42046147002,0x1bd0a0b000000000017000102f,0xbc100500000000001580760a1,0x13005241ad01350000968752006029046,0x13d16cb000000005204606e006,0x97162909301920820f84000062875400a02906e,0xb04480d903eb00000000000063f80a1,0x8c16ed0000000004056001048,0x920f6203219c9000000000006e001158,0xb21f0d08908d012218d010518d000000000001480a6001,0x1470bbd0f3090a0000000000258016029,0x4a047615601e900000000030c60062de,0x14d133b14807f209632875412700a1001,0x504600e02a,0x4c05fc0bb09220000000000258076001,0x79001046070,0x13005240d919950000000000006029270,0x6a00a91da0e960000000007001158076],
 #[0x700106e128,0x100205e1c7,0x151099900000000001272700a1,0x1cd13761c60e2c1c40853066050c1090a4e000000003500204e14d,0x981fa012a0098069088d0fc18d51d01504000042957805600206d,0x1c1139803304f803619f503f09f50ac1398000000004204800103e,0x212831a5102c059058d1af16561551b4100000003850c6002045,0x1e20687042044e000000000725800103e,0x1491e8100000000000c613f014,0x8006029058,0xc00507059058d1b11d1200000000030c60021af,0x1720218000000000017000102a,0x7e16e703e12b001719371ab0ad9096432187505606e001,0x1f30d9b000000000015825d2a8,0x12407a10a00b6b0000000001148001076,0xc63700a3,0x1602311a21ee508716f80000000000148016029,0x30b604600e,0xa029070,0x620010380de,0x46144800000000000022f8121,0x701f7121,0x1cc045300000000030c6170001,0xe70ede20412c305504b5000000023813f00224e],
 #[0x7c1da91e41d1f1f10aab19b037900000561230b6156121,0x1510b81991b6e03f09f50000000584048001035,0x861df200d10f51440f960b10f9600000000011d61a8001,0x9a0e821450e820000000004048001057,0x20b6002076,0x8215310bf0edb000094875600e029036,0x406e001048,0x12f022420118ce000000000027000103e,0x17912e0000000000800205e0dd,0x1250c5e1cd050f1cd1376000000003100214e25e,0x571e0c03517ef04d1e0c09407ef000000000606e00225e,0x250eea195154500963187520011480a1,0x12919d51ba0ad505f0ad50851ad50fb0ad50000000008056127002,0x1580a304e,0x70012700a6,0xc2168004f0c4d00632187540012700a1,0x127076e09e02a300000005640480de001,0x791ed51c60e2c000000003100204e1c7,0x780fa900000000000461580a1,0x1c703f018d0ce9000000000017000102b,0x12a0098171059807a02e018c159817912e000000000020560021df,0x1bd0a0b1c703f00000000000170001067,0x1cd13761091c51000000003100204e25e,0x176019d16f0b7e00000000000c617025e],
 #[0x5a0e251a01ed30621569018035e08716f80000000000148016031,0x90091d000000000113f00205e,0x1aa1eac1aa002b000964875217000102d,0x20b61d6257,0xec018600000000010c6002047,0x11d1e861c40853000000000100214e1cf,0x1b179a00000000080b61d60a2,0x1541b0800000000002700a1127,0x1b706bc00000000072580a3001,0xc11ad503517ef09407ef000000000606e00205e,0x1dc021a000000000006e0c61d6,0x840245000000000037000102b,0x4412601361acb04400171360acb1970acb00000000002580a6001,0x1330f6300000000000c61d61a8,0x1fa04730c90d16152179115203710096428751170001029,0x1f818cc000000000700205e076,0x571e0c066171e00000000060020f625e,0x1ae0f051cb0aea1500fcd0000000000056001270,0x90091d02816e7000000000113f0020de,0x8600625e0a2,0x14b0c590b9017200000000070c61d6014,0x805800203d,0x2060ad3180103c06a00a90004953871001036056,0x7200207613e],
 #[0x20011580a2,0x10508d315e11d31a91f5c00000001620021e0121,0x176019d00000000000c61702de,0x920f6209215fc064198753206e001036,0x70a450810fc9000000000213f1c6123,0x6006df0b60c5100000007621d6257002,0x1250c5e1091c51000000007300225e2df,0x2700a23af,0x1491e8105a0e2500000000020c6147014,0x6029070,0x1580a222d,0x15f18ab06e0bab16a0a4f0ef0a4f000000000113f058001,0x1e80a380e6042a0000000002170002129,0x7960010580f6,0xb012f613a170e04706601980a720964321875056127001,0xd30a361010c4c0000628759046014029,0x5c08431e50ad50e30843000000000206e00203e,0x805800204d,0x6a16530d11dbc0000000000001036270,0xb60c510b61a4e07f0ba70000000002258002035,0x4158b00000000001480a106e,0x58068800000000002580a1127,0x15309670331baf00000000620580011af,0x19182f0bf18270971629000029578400a029056],
 #[0x1ed0d501aa1eac0370f450000000008056170001,0x400103804e,0x20205b302600ed16c11a5000000001806e15825d,0x1d62572ee,0x1450e820d80f4b0000000001048001037,0xa91c330791ed5000000371800203e1c5,0x11d607022f,0xe80d6d00000000000c6147122,0x11d6270001,0x1cc14cc1cc04531ed0d501ed1ee9203053917a02bf0000649852170001065,0x15a0e6419903671c100af0ac00af000000000205800113e,0xc701ba111069d0000000008056270001,0x1060a6d00000000002580a2065,0x17105980000000008056002045,0x11610e102d10e10f410e100000000000021d00a1,0x1fd0da900000000620b61d60a1,0x1600a7e061037a1b0037a061137a0000000009127070001,0x3101ce0210f57087014e00000001921580a1014,0xb80ad50000000089056002076,0xd71aef00000000003700a1046,0x991a270aa1a270f40a270000000000158002031,0x5612b00000000002056001038,0x1b20c5f03b055f02b02eb0000000132158002129,0xe71e2218e13e600000000010b600225e],
 #[0x1e401cf0290b4a05d10d10cb0ee500000000321480a105f,0x1a8182003c045b17e01ac0cd039418110bd0000000000148010029,0x180003906a1653010156b0000000079001046170,0x14b0c591b8028200000000471d6257014,0x800a029058,0x9301920820f8418f1c49000000007217000c031,0x1b706bc000000005825800212d,0x15e0ce000000000011480a3065,0x10d11fd01f02f01df0e870121fa31701da60c0050701a148600000138540c6002055,0x20c0c3b00000000580020ce05e,0x431e530000000009056001070,0x25800102b,0x17b0715000000008405612700a,0x11d1e860791ed500000000430021c724e,0x8b144c0240f620000948752056006029,0xba171d189181d039181d146081d0000000082056128001,0x2c019c000000000012825e2df,0x1703a8121,0x1aa1eac0800bd3000000000017000105e,0x79001036070,0xb80ad51d0150400000000890560020f6,0x6c0d0100000000001700a1046,0x1180ed511b185309b0db420519ac0000000002148002035,0x6d08b7000000000514800212d],
 #[0x17507c218a0cb60096875321127001046,0xdf084200000000050c61d60a3,0x1ba0ad500000000681270020de,0x807340901d120451db41b11d1209b0db400000000030b6046002,0x1ad01351b30e150000000000006029258,0x1fc0b860000000589046056014,0x49052c0c5052c000000000106e002037,0x230036000000000015825d2f0,0x805601402a,0x1030e5120205b30760eec000000000006e14825e,0x1491e81000000000013f1c6014,0x12701402a,0xe084c02600ed1ef0dac00000000181581f625d,0x12e155300000000000463700a1,0xf8086609c0e43075086600000000030c6130001,0x6114807625e,0x113f270001,0xec018600000000140c6002057,0x2090ff600000000072580a1002,0x2580a31a7,0x511b1d1ff1f5713e0f5716d1f570000000000048076001,0x571e0c000000007100207625e,0xcf0a2105c08430cf1a210e30843000000000206e0021f7,0x630e6900000000030c6014032],
 #[0x310021c705e,0x1670d53000000000800204e0de,0x1211c061d304f90d5022512b115f0000000007046001170,0x5200602a04e,0x11d600a032,0x67069e1fb182d1d9169e178169e0000000000370002031,0x805800c031,0x400a02a076,0x1bc1cde1bc0a950d2054c0d2154c18b054c000000000004805e001,0x7001058076,0xd3100000000090011700a3,0x571e0c0e308430570d9300000000070020760f5,0xbe126a0740ad50be00210741ad50dd0ad50dd1ad50000000058046056002,0x8058002075,0x20b05ae1b608401e80a38000000002717000206d,0x18c15980000000008056002035,0x1941d3f000000000527000212d,0x5740c601402a,0xe0023000000000002700a2001,0x10e05c8000000000027000102a,0x2070f9e0e3084300000000920020f61f7,0x206e00602a,0x18f069000000000261700a100e,0xb51def000000008705606e127],
 #[0x60ad51d201dc0b70ad51e50ad50b71ad5000000000706e127002,0x115800102a,0x18807771a40b6700000000000c6147256,0x8f07c100000000071d6257123,0x113f056014,0x66050c1201665000000000000204e0f6,0x40012583f6,0x9b17c100000000131580022ad,0x107000c031,0x1a60233000000000700203e1ad,0x100205e0df,0x3101ce0e20cac06511a41411e950540a2508816e900046518321580a105d,0x14f00af1ac1b8f11000af00000000020b6058001,0x12f12410c71353000294875637000102d,0x1db005f0000000001070001047,0x19f0fec00000000172580a3065,0x4127001048,0xd9199500000000020062f8121,0x8a0a5f1cb0aea0293187654056001046,0x9603a30620b0a01812540000428759014029056,0x17f088307d1fec01510b80ae0883000000000104800125e,0x1ba1ad5000000000412700204e,0x18b054c1060a6d0000000000258002129,0x17000102e],
 #[0x1970acb19f0fec00000000000022e0121,0x18e13e6204001b00000000120b600205e,0x2113f2580a3,0x1f11dc40a1074205d10d11391add00000000321480a1067,0x113f00a032,0x2060ad304b09cd0000000000001036258,0x189181d00000008260581af001,0x140818165030906b121a005121a000000000113f070001,0xe10b5e11b185300000000040c6147002,0x4a04760950a0d0951ce700000000640c600625e,0x810fc91a908d800000000011480a306d,0x640010480de,0xa807690000000008058016031,0x20b600a02a,0x213f00a02a,0x1a40b67102064300000000000c6147056,0x2580a21a7,0xca06fc03b19b800000000001480a2065,0x1e206871840ac9000298765425800102d,0x1bf0fe70f3090a00000000092580a1014,0x770b4301204dd0a60bb51a50d11000000006315825d002,0x1f2037900000000002580a106e,0x2060ad31e00a50000000000000114805e,0x9606e00625e],
 #[0x1580a204e,0x951ce7000007856200625e0a1,0x5504b502816e718e0656000000058213f00203d,0x600e02a03e,0x190ee30bf0edb18110bd0000000000148010031,0x1bb08f700000000290701af001,0x313f1c61a6,0x12700a2,0xf50e0c00000000001700a3001,0x1c30b8e02600ed000000083106e1581f5,0x501bd90fe1ca20ad1ca2000000000104600204f,0x10481cf121,0x12f022411c09c50000000000127270001,0x12580a6,0x9f1e0b04e1b26164015f1591dc80096428751370001029,0x1c906e21c30b8e000000000006e16f2e0,0x2060ad318308650002953871001046056,0x13b0cc200000000020561571ee,0x180103c00000000960011581f6,0x7b1bdd1ce03ec10d11fd002128300000000410c60022de,0xc701ba0ea0417000000000027000105e,0xd3100000000790010381f6,0x700106e328,0x20b6270001],
 #[0x19119da000000005604606e00e,0x6048010029,0x114800102f,0x8317da18f06900000000000170010029,0x1881904091030900000000010c6158121,0xf6025f0ed01690b3025f1e6025f0000000007170002031,0x18702a700000000780020760de,0x6070010029,0x1dc021a1de1bb8000000000006e0c6256,0xe80d6d0ca06fc000000000313f1c6122,0x27000102f,0x2060ad318504d10000000004001056148,0x1751af617507c2006487532112700106e,0x15c0aa915c1aa9000000000112700203f,0x1046058,0x10020501d5,0x1127002045,0x204614700e,0xdc099b000000000113f014032,0x200aaf0731baf0331baf1b51baf0000000006127058001,0x12800f7000000000000205e1af,0x2048008029,0xe10b5e1180ed5000000002113f1c6002,0xa617b11b11d121af165600000000310c600203e],
 #[0xf200440000000000014029058,0xcf0a2104d0d9309407ef000000000806e002045,0xf80866075086618902ff000000002412800104e,0x720f1d12417be09d148e000948765215800102d,0x6a00a90c41d89000000007600106e158,0x7920010380f6,0x14c02680000000582046056006,0x10218461660328102064306f035d12d05d8000000004714805e0a1,0x1f90e261dd039e0096428751258001029,0xce049b0b41c8105302180a7121800000000030c6070001,0x6002060165,0x1580b951191d0b000094875612700e029,0xe402380000000058046056127,0x1f818cc0000000000370002035,0x2070f9e1a60233000000072900203e1f6,0x181254018035e0000648759014029036,0x10b125710b00542090ff600000000002580a105f,0x981fa00741ad500000005480560022af,0x4001036048,0x6a00a906a1653000648537100103606e,0x1d31bb00d5124208a0a5f0941876532056001036,0x8e0cf71a80899000000000115825d00c,0xc600fd000000008504605606e,0x1eb0b2e135042a135142a0e6042a00000000000701a7001],
 #[0x1e308d51e313c8000064875206e006029,0x18308650fa0c0d0000000000001046370,0x115122816c11a50d61c79000000000006e158029,0x12800c031,0xe029038,0x64073701306b4000000000014805e001,0x2a021802218c600f1218000000000307000114e,0x12580a3,0x9716291080e5b000000000000a029370,0x206e001038,0x13700a3,0x10712c710700c420d0ddb00000000002581a8121,0x1cb0aea0d51242004287563105600106e,0x107000204d,0x30b600a032,0xa40af70a4153e09643875211700a1001,0x18609ed00000000020c613f02b,0x201402a03e,0x10020760f7,0x1b608400f50e0c000000000717000212d,0x11f025f11f125f1e6025f00000000290021f80a1,0x2700a1002,0x9a1d7d0d812800000000001058001037,0x1582f8121],
 #[0x40c6002076,0x1056128,0x1d4052b00000000001702e0121,0x1000dc1000000000015825d070,0x1301de51300524000064875200602906e,0x1b41ba10111412000092875405600a029,0x17507c21421f630000000000127001270,0x1582a8121,0x2b15b000000000001480a206d,0x12700a02a,0x9127001070,0x15c0aa91ca0aa90000000001127002047,0x60ad50000000009127002076,0x1a70b7b0920f62042531987606e001056,0x631ee20dc099b1400afb0630e690dc1ff80a807690a81902000026485901402a065,0x8e0cf700000000000b615600a,0x112800204d,0x2128016029,0x37000102e,0x601402a05e,0xf71e460f01f0c000042875606e00e029,0xab013d0ab113d00a013d0000000000258002031,0x720f1d00000000430c6158001,0x12580a2],
 #[0x1330f6300000000001d61a82df,0x1400afb0000000000128016031,0x8d127215b1bb60a2088319e188300000000011d6228001,0x16d1f570000000000270002129,0x5b15e501e1eee0096428751158001029,0xee1ba600000008960580f6001,0x20205b31c30b8e0d40a4a000000000006e14805e,0x14a0af00000000000014029038,0xcb13d5139016100001276531580a1002,0x1b30e150f1080400000000020062e0121,0x1c2037b00000000920021f8121,0xd00eba00000084520b600a029,0x25800102e,0x20b601402a,0x49152c049052c000000000106e002077,0x7a02e00851ad517912e0000000008205600203e,0x1941d3f00000000002700a3001,0x1091c511090a4e07f0ba7000000000000204e05e,0x70011700a6,0x313f00203f,0xe904cf1081e4c0000000000270010029,0x126121a1b0037a12608771b908771b9121a000000009207000103e,0x771e051701da61af165600000000010c60021c7,0x6d18b400000007531580a3001],
 #[0x2f1d3f08a0a5f13c0e920000000000056001148,0x7b076f01f1cd81550b4100000000030c61d6002,0x19a1ce5000000007606e12700e,0x6911e50850ad500000000250460021af,0x900207817d,0x1bb08f70000000029128001076,0x1402a067,0x1840ac916b060c000000000006e258001,0x126121a06803f81b9121a00000000010700011c7,0x18308651ee0b8b0000000000001258076,0x501bd90da1bd903a0bd90000000005046002057,0x1700a205e,0x1a0ee7000000003606e1d6002,0x60ad51a6023300000000791270020f6,0xc10ad5000000005406e0022af,0x158078121,0x113f258001,0x16e036d0ee1ba60341ba610a0ba60000000089056070001,0x40089a19b037913f0513131029f00000000121580a1048,0x2700a205e,0xc8089c09e110a1381653112110a0a5010a0000000084056228001,0x2002040235,0x9d148e1c0119a000000003515800104e,0x1081e4c00000000062700a100e],
 #[0x149003008e0cf700712ab0e81f1c07c1da911d003518614bb01b179a1fd0da90e71e220e113c10770b4300000007580b61561d5,0x12417be1be1225000000000006e158001,0xe308431370457000000000700203e076,0x14b0c59176019d02c019c1330f6311405e81a40b6704a04761dc021a08f07c12000d401a102c21250c5e0df08420df1cb007b1bdd07b076f06006df00000095870c61d6255,0x18a0cb614e0b000000000000127001258,0x30c6006032,0x25800102a,0x18308650fd0ed8000000000700106e258,0x18807771ef1ba607c05460a107420290b4a00000002530c6147121,0xe0023000000000050020ce076,0x174013d174113d00a013d00000000000022e00a1,0x1b802821b8107f192012d09603a30f3090a0000000000258016031,0x304b80000000069058001076,0x3d069e157069e178169e00000000000023f80a1,0x314270521fea11a14270c31427000000000406e228001,0x9c0e430751f960000000852128001045,0x10c0b5f1431c5f0011c5f1b20c5f00000000000581a7001,0x17902ec00000000420020ce1cf,0xe51eab0e50e320f200440f2157614a0af0000064285901402905f,0x1f70bc21e907ea00932187540012580a1,0x16f0b7e1960b781ea069200000068740c61d60a1,0x1d0d5d00000000791700a2001,0x3a0bd90ad1ca21321ca20000000001046002037,0x25800102f],
 #[0x258078121,0x200602a076,0x100203e1ae,0x15613ec15601e91d5029f1e100021b30e1500000000000062e00a1,0x6058016029,0x2070008029,0x1030e5119c045c00e084c00000000001481f625e,0x18204a500000000001272580a1,0xac139817d11ce0ae08830000000854048001045,0x104805e,0x2300360e20cac1690a3800000000001580a1270,0x2046147014,0x20b05ae000000009206e16f002,0xaf098b0af199900643187590011700a1,0x1411e951931c2118100cc00000002411580a100a,0x1b0037a00000000920700011af,0x13704570000000072170002035,0x291700a1002,0x9d148e19d1ddc0000000005046158001,0x11580a6,0x2c019c00000000000c613025e,0x20481c724d,0x1fe0ea5173062f16104a2161160f096432187506e127001,0x1a3084600000000002580760a1],
 #[0x412800c029,0x1e2068715d04d10000000000127258001,0x1f6063900000000070020761af,0x17c037b0eb0a7f10f037b1c2037b00000000071700a6001,0x2580a1128,0x162087d1d6037209632854172580a1001,0x411d4104102020000648759127014029,0xe084c1c30b8e1660328000000000914805e1f6,0x70008031,0x79001038076,0x790011700a2,0x2e04480cc100e1040448046144800000000002700a6001,0x12306011e7117a12c17df1e70f2e12c05962080f1f0964321875046056001,0x306e00e02a,0x1581f6122,0x6e1d61a8,0x30081e192012d030115a1a0081f1a01ed30de012b006423158901402905d,0x20c0c3b00000000072580a2001]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows4 : Rows := #[
 #[0x10381f6121,0x10481a7001045,0x116d400000000001d600203d257,0x10580010760f5,0x1580a106e001,0x20b6070001035,0x106e127002075,0xc613f1c51a3,0x30b6046002055,0x104606e002035,0x580022e00a102d,0x63f80a102d,0x33079c00000000001580a104d002,0xc612800104d,0xd081403f0fab000000000014805e1f625d,0x1070001045056,0x90010561700a1,0x4600e029036,0x1c3f000000000015825d00206d,0x14805e001029,0x113f070001065,0x58001045146,0x3148016029035,0x4606e001056],
 #[0x14801603102d,0x214801003104d,0x606e1d600206d,0x50c613f02a1c5,0x6e0012580a1,0x90020f61a70a1,0x8148001029056,0x30e8000000000000c6002055256,0x12705800106d,0x1580a104d012,0x700010351d6,0x1580a11d5268,0x5056006029046,0x70011480a106e,0xd0814000000001806e1581f525d,0x1280010370c5,0xb60020450c6,0x2a0c4f0361b5100000000000c6147121057,0x7000104e14d,0x158002129055,0xc613025e2dd,0x10021e00a1045,0x12700a6001075,0x4600104d150],
 #[0x1402905d328,0x21580a105d012,0x6e0011480a1,0x104800103e1ad,0x1046070001035,0x6e00204e14d,0x5800103e1c5,0x260b460000000000056170001029,0x1480a1056001,0x1046128001035,0x10460020370d5,0x158002129065,0x14801002906d,0x10023f80a1045,0x4606e00104d,0x2048001035036,0x310ffc00000000001580a104825d,0x127014029046,0x25800103e029,0x4600104f0ee,0x2580a6001055,0x13f05600203d,0x70023f81210a5,0x56127001065],
 #[0x158076001065,0x6e0020370f5,0x3d0e6c00000000000c600625e2dd,0x10362580a1,0x25807600102d,0x6e002045146,0x27000102905d,0x12700a1036,0x105600205f0ed,0x5807600106d,0x6e32800106d,0xc6070001045,0x1c066200000008311580a105d166,0x1f1958000000000013f00203d1c6,0x460010380d5,0x20760f514e,0x2580a1127001,0xc60020451af,0xc6147014039,0x14800102906e,0x6e00203e1f5,0x3608cb01103aa00000000001580a104f0dd,0x561700a1001,0x1056127002045],
 #[0x1706d400000000000c61d6255002,0x1127070001045,0x215801603105d,0x30c6014032065,0x14805e00102d,0x1480a105d328,0x204e0f614d,0x1370002031075,0x7000103513f,0x181469000000000005600206d1af,0x700103605606e,0xb6070001045,0x1700a1046001,0x14800212d0a1,0x13f058001045,0x1b0ac2000000000014805e0a105d,0x706e258029001,0x56001065228,0x40c6158001035,0x1127048001035,0x104600205e0dd,0x30c613000102d,0x410801000000000006e1480291d6,0x1c3f02401be00000000000b61561d5002],
 #[0x461580a1001,0x1a01be000000000000203e05e13d,0x5600203e1dd,0x3186b00116d400000000000c61d60022dd,0x3c0003002075e030184702a0c4f00000875210c613f1c51a1,0x305800106d14e,0x4606e00104f,0xf00ca000000000000204e05e0a1,0x191e95000000000017000105e0a1,0x13f1c6123065,0x717000c03102d,0x17000c02902d,0x37000102b065,0x104600203e1ad,0x30c6128001055,0x705c700b02fe00000000211580a1014029,0x350e1d00000000001480a105d002,0x11480a600104d,0x56001036046,0x4600602906e,0x4600104f0d6,0x30c6058001055,0xb61561d500a,0x70c61d62551a3],
 #[0x13f00205e0dd,0x2815f400000000000c615812104d,0x6e001036056,0x217000c031075,0x606e002045056,0xc60060291d6,0x25801603102d,0x527001003102d,0xa1e1a00000000080460020550d6,0x114800203104d,0x10480010470d5,0x30b6046002035,0xc6130001045,0x805614800102d,0x104605800104d,0x27000102905f,0x1480010760a1,0x3018470361b5100000000000c614712105f,0x1d622800103d,0x106e128001035,0x1700a1001056,0x1056228001035,0x2401be000000000015825d00204d,0x11d6070001035],
 #[0x8058016031065,0x1a01be000000000000203e13d1d6,0x114800203103d,0x125800203105d,0x2058001035036,0x560020470dd,0x1048001045056,0x11700a1056,0x4612700106e,0x11d61a8001035,0x1580a600106d,0x117000203103d,0x1d607000105d,0x2112e502909c6000000000004606e127001,0x1706d400000000001d625700203d,0x106e127002045,0x10560020760f5,0x3a0d0200000000000c61d6014039,0x5046128001055,0x160a710000000000258076001029,0x1480760a1001,0xb60461d60a1,0x85046056002055,0x3514801003102d],
 #[0x30c60020551af,0x504606e00204d,0x13700a1046,0x106e328001045,0x106e148029,0x6e0020370c5,0x131351013049e000000000004605606e001,0x805627000102d,0x805622800106d,0x17000102905d,0x13f1c612205d,0x871480a10020e5,0x3700a600106d,0x14801002902d,0x30c6070001055,0x6e0020451ef,0xb61d600a031,0x10363700a1,0x104805e001045,0x46014029056,0x2206d00420cab000000000006e14805e029,0x704600103606e,0x806e148029001,0x2700a1056001],
 #[0x480010370c5,0x60293700a1,0x10560020370ed,0x20ce1a70a1,0x113f014032065,0x1046056002045,0x1402905d128,0x50c61d60a3255,0x20ce0760a1,0x1e095800000000000c613f1c5002,0x1580a105d268,0x200203e0760f5,0x2f108802f00130000000000046056127001,0xc601403105f,0x701a700102d,0x1f195800000000000c613f00224d,0xc613f1c51a2,0x27001002902d,0x1d1174000000000027000105e0a1,0x71700a6001065,0xc60020470d5,0x7170002031065,0x504607000104d,0x113f058001035],
 #[0x706e00a029036,0x62e0121065,0x140290580e5,0x402eb00000000002580a1014029,0x80021e00a102d,0x3b0d15000000000017000212d0a1,0x1170002031075,0x806e00a029056,0xc613000104d,0x105800106d1c7,0x10463700a1,0x1056127002035,0x5046002055226,0x106e258029,0x560020370dd,0x805606e00206d,0x40052600000000001580a11d5068,0x46014029036,0x1002c900000000000c6147056121,0xd0814000000000006e1481f525e,0x12700a600104d,0x21e01210a5,0x258002129065,0x430d4700000000000c62561a81a1],
 #[0xa0293700a1,0x3706d4000000000000204e05e14d,0x1056070001035,0x120cd700000000000c6256121057,0x581a700106d,0x3186b00000000001d600206d2df,0x27000102a065,0x71700a600103d,0x20b6058001035,0x56270001029,0x1046058001035,0x871480a1001056,0x430d4700000000000c61d6255228,0x410801000000005306e148029065,0x10021e00a1035,0x1048001055226,0x1e0958000000000013f1c600203d,0x812700a029056,0x106e328001035,0x1e11be000000000015800203525d,0x127270001029,0x1a01be000000000000213e1de25d,0xc17950000000000158076001029,0x10021f80a1045],
 #[0x341ed8000000000000205e0f60a1,0x7056001065168,0x11580a600103d,0x4605600106e,0x6e14800102d,0x3706d4000000000000214e25e2dd,0x7000103e13d,0x50480de00106d,0x205e1af029,0x5046127002055,0x205600206d1df,0x141f7c00000000090560011700a1,0x4605600104d,0x714805e0a1001,0x562700a1001,0x12727000102d,0x500602904606e,0x1580a10480d5,0x560020370c5,0xc61d61a82dd,0x6e128001065,0x10701a7001045,0x12580a600104d,0x200203e0760a1],
 #[0x504605800106d,0x751580a10020d5,0x4612700104f,0x561571ee121,0x61b4000000000000560011480a1,0x5606e006029,0x1048076001035,0x1580a10480e5,0x128016031065,0x1480a105d00e,0x1270013700a1,0x10481a7001035,0x1d61a800103d,0x10480010370d5,0x1056128001035,0x8525801602902d,0x2700a1001036,0xb61561d5012,0x140290380e5,0x3a0d0200000000070c61d6255012,0x46056006029,0x3700a1001046,0x3e086500000000001270012580a1,0xb6058001045],
 #[0x2b187700000000000560012700a1,0x1272700a1001,0x170001029046,0x5800106d1af,0x3700a1127001,0x116d400000000000c61d6002035,0x3d0e6c00000000000c60062de0a1,0x10023f80a1035,0x12700e02906e,0x270001029036,0x205800106d13e,0xc605800104d,0x12700203f0c5,0x127258001029,0x21d0121065,0x20b6048001055,0x127070001065,0x6e127001056,0x72580a100106e,0x104606e002045,0x370001029046,0x13f070001045,0x3f0fab01b0ac2000000000014805e0a116e,0x204e0de0a1],
 #[0x5800106d0ee,0x1580a104d268,0x13f05800103d,0x6e258001029,0x38089a000000000006e0c6147031,0x5807600102d,0x805607000106d,0xc617025e121,0x1c3f00000000000b61d600206d,0x560020451d7,0x17000102a065,0x6e12700105d,0x10022e00a1045,0x12700104606e,0xc617025e2dd,0x4600104d068,0x50022f80a102d,0x200203e04e0cd,0x1700010650a2,0x5612700a029,0x11700a6001075,0x5800103513f,0x3148010029035,0x4800105e25d],
 #[0x900103604616e,0xe14ff005149d00000000211580a100a029,0x1272580a1001,0x700104605606e,0x6e25800102d,0x1056148029,0xc613f02b1c5,0x20760de029,0xc61471211ce,0x104612800104d,0x127001046056,0x4805e00102d,0x460020451c7,0x717000102b065,0x1f195800000000000c613f002035,0x21700a100e029,0x3c0003000000000013f1c61210e8,0x5606e00a029,0x258016031065,0x31480a106500e,0x321b25000000000037000212d0a1,0x11580a1046,0xc61d60a1128,0x22e01210a5],
 #[0x56127001046,0x5800104513e,0x6e12700a029,0x310ffc00000000000b6156121040,0x1480a116e1d6,0x56148001029,0x30c6058001035,0x22e0121065,0x158016031065,0x120cd700000000000c61d62551a1,0x2815801602902d,0x2580760a1001,0x1002c900000000000c6147056255,0x2401be000000000015825d002045,0x7900203e0f61a5,0x6e001046056,0x15825d00c031,0x21d012106d,0x504617000102d,0x5606e001036,0x13f048001045,0x58006029046056,0x56001065268,0x2401be00000000000b61d6002035],
 #[0x107000103e1ad,0x13f056002045,0x581a700102d,0x230be800000000000060292580a1,0x4600e02906e,0x1127048001045,0x2c041c000000000017000206d12d,0x25800212d0a1,0x3a0d0200000000001d6257014039,0x2070001035036,0x105612700205d,0x106e128001075,0x4805e001055,0x17000102f0e5,0x6e148001029,0x2580a105d012,0x14800105e0a1,0x5800103e13d,0x70021f81210a5,0xd08140420cab000000000006e14805e1f5,0x1a1958000000000000203e04e14d,0x90b7a00808de00810de000000009200203e0f60a1,0x1a1958000000000000204e14d1c7,0x17000102b0e5],
 #[0x6e25802905d,0xd0814000000000006e16f25e2df,0x1270020370c5,0x5600104606e,0x30c6170001065,0x3706d4000000000000205e14e25d,0x106d400000000000c600205e2dd,0x14807600102d,0x2e140f00000000000460020550ee,0x871480a100106e,0x706e127002065,0x7904600103616e,0x1702e0121065,0x62e00a1065,0x72580a1001036,0x56001065128,0x2580010760a1,0x127000203104d,0x11580760a1,0x700010370c5,0x2d083e000000000006e0c61d6255,0x258001029036,0x2d083e000000000006e1d6257031,0x10c6002055226],
 #[0x114805e0a1,0x62e00a102d,0x712725800102d,0x806e006029056,0x2a0c4f01111d6000000000213f1c6121057,0x706e00203e1ad,0x70021f80a102d,0x3906c2000000000004605600104f,0x217000206d129,0x12580a1036,0xc61d60a1127,0x701a7001065,0x56127014029,0x8056170001065,0x12580760a1,0x1580a116e1d5,0x2075e000000000013f1c61210d0,0x30073101103aa00000000010b6156121047,0x2580a106e001,0x20050000000000001580a11d5228,0x2580a105d002,0x200203e0ce0a1,0x20761af029,0x12580a106e],
 #[0x204e0760a1,0x25800102906e,0x17000102905f,0x270002031065,0x46056014029,0xb61561d5121,0x6e12700105f,0x1058076001035,0xc61d62551a2,0x251ef6000000000037000103e029,0xd081402206d0000000000006e14805e25d,0x21700010650a6,0x1f01be00000000000b600205e1dd,0x2702ae015103a000000001200203e05e0a1,0x1036046056,0x90b7a000000000000203e0f61f5,0x46056001036,0x72580a10020e5,0x38089a000000000106e14802916d,0x206e16f00206d,0x20ce05e0a1,0x2581a8121065]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows5 : Rows := #[
 #[0xc60020551c724d,0xc6002045056255,0xc613f1c51a10c8,0xc60020552562d5,0x2580a101402905d,0x1480a100e029065,0x460011580a104d,0x1580a101402905d,0x203e0f60a1065,0x203e0f60a116d,0x5600206d2af029,0x1580a101402904d,0x14807600102905d,0x10931000000000006e14805e1f525d,0x1480a100e02905d,0x204e05e0a105d,0xc61470561211cd,0x3000000000000b61561210470d5,0xc61d62551a104f,0x4605606e00104d,0x460011700a104d,0x203e04e0a1065,0x25807600102905d,0xc61d6255002045],
 #[0x460020551af029,0x17000104e0a105d,0x203e05e13d1d5,0x14805e0a105d166,0x1580a105d1660a1,0x37000104e0a105d,0xc613f1c5002045,0xb60020450561d5,0xb615612114d1a8,0x5606e12700105d,0x10931000000000006e14805e0291d5,0x60292580a105d,0xb61561d500203d,0x27000103e02905d,0x5617000102905d,0x203e05e0a105d,0x1480a10651d6029,0x4606e12700104d,0x1c5600000000000c613f1c51a104f,0x460013700a104d,0x17000206d12d0a1,0x6e0c61d6255039,0x5600206d0ee0a1,0x4605612700104d],
 #[0x3000000000000b61561210471cd,0xb61561210401d5,0x27000212d0a105d,0x1580a104d002035,0x204e0f60a1065,0x1480a105d00203d,0x3000000000001580a104f0dd255,0x204e05e14d255,0x6e0c6147031165,0x4605600104f0e5,0xc61d6255012041,0x17000212d0a105d,0xc613f1c51a10e0,0xc600625e2dd121,0x1270012580a105d,0x14805e0a116e1d5,0xb615612114d060,0x6e1480290651d6,0x10931000000000006e14805e02916d,0xc61d6255228221]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows6 : Rows := #[
 #[0xb61561210470d51cd,0x6e14805e02916d1d5]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows7 : Rows := #[]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19audit6 := atlasRow g19frame 6 g19rows6 g19rows7 0 g19rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check6x0 : Span g19audit6 0 2 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19done6 : Region g19frame 6 2 g19rows6 :=
  atlas_sound g19proper g19frame g19vframe 6 2 0 g19rows6 g19rows7 g19rot (by intro j hj; omega) g19check6x0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19audit5 := atlasRow g19frame 5 g19rows5 g19rows6 2 g19rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check5x0 : Span g19audit5 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check5x8 : Span g19audit5 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check5x16 : Span g19audit5 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check5x24 : Span g19audit5 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check5x32 : Span g19audit5 32 40 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check5x40 : Span g19audit5 40 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check5x48 : Span g19audit5 48 56 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check5x56 : Span g19audit5 56 64 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check5x64 : Span g19audit5 64 68 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19done5 : Region g19frame 5 68 g19rows5 :=
  atlas_sound g19proper g19frame g19vframe 5 68 2 g19rows5 g19rows6 g19rot g19done6 (join_span (join_span (join_span g19check5x0 g19check5x8) (join_span g19check5x16 g19check5x24)) (join_span (join_span g19check5x32 g19check5x40) (join_span g19check5x48 (join_span g19check5x56 g19check5x64))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19audit4 := atlasRow g19frame 4 g19rows4 g19rows5 68 g19rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x0 : Span g19audit4 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x8 : Span g19audit4 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x16 : Span g19audit4 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x24 : Span g19audit4 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x32 : Span g19audit4 32 40 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x40 : Span g19audit4 40 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x48 : Span g19audit4 48 56 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x56 : Span g19audit4 56 64 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x64 : Span g19audit4 64 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x72 : Span g19audit4 72 80 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x80 : Span g19audit4 80 88 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x88 : Span g19audit4 88 96 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x96 : Span g19audit4 96 104 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x104 : Span g19audit4 104 112 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x112 : Span g19audit4 112 120 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x120 : Span g19audit4 120 128 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x128 : Span g19audit4 128 136 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x136 : Span g19audit4 136 144 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x144 : Span g19audit4 144 152 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x152 : Span g19audit4 152 160 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x160 : Span g19audit4 160 168 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x168 : Span g19audit4 168 176 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x176 : Span g19audit4 176 184 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x184 : Span g19audit4 184 192 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x192 : Span g19audit4 192 200 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x200 : Span g19audit4 200 208 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x208 : Span g19audit4 208 216 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x216 : Span g19audit4 216 224 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x224 : Span g19audit4 224 232 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x232 : Span g19audit4 232 240 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x240 : Span g19audit4 240 248 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x248 : Span g19audit4 248 256 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x256 : Span g19audit4 256 264 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x264 : Span g19audit4 264 272 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x272 : Span g19audit4 272 280 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x280 : Span g19audit4 280 288 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x288 : Span g19audit4 288 296 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x296 : Span g19audit4 296 304 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x304 : Span g19audit4 304 312 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x312 : Span g19audit4 312 320 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x320 : Span g19audit4 320 328 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x328 : Span g19audit4 328 336 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x336 : Span g19audit4 336 344 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x344 : Span g19audit4 344 352 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x352 : Span g19audit4 352 360 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x360 : Span g19audit4 360 368 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x368 : Span g19audit4 368 376 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x376 : Span g19audit4 376 384 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x384 : Span g19audit4 384 392 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x392 : Span g19audit4 392 400 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x400 : Span g19audit4 400 408 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x408 : Span g19audit4 408 416 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x416 : Span g19audit4 416 424 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x424 : Span g19audit4 424 432 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x432 : Span g19audit4 432 440 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x440 : Span g19audit4 440 448 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x448 : Span g19audit4 448 456 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x456 : Span g19audit4 456 464 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x464 : Span g19audit4 464 472 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x472 : Span g19audit4 472 480 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x480 : Span g19audit4 480 488 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x488 : Span g19audit4 488 496 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x496 : Span g19audit4 496 504 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x504 : Span g19audit4 504 512 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x512 : Span g19audit4 512 520 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x520 : Span g19audit4 520 526 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19done4 : Region g19frame 4 526 g19rows4 :=
  atlas_sound g19proper g19frame g19vframe 4 526 68 g19rows4 g19rows5 g19rot g19done5 (join_span (join_span (join_span (join_span (join_span (join_span g19check4x0 g19check4x8) (join_span g19check4x16 g19check4x24)) (join_span (join_span g19check4x32 g19check4x40) (join_span g19check4x48 g19check4x56))) (join_span (join_span (join_span g19check4x64 g19check4x72) (join_span g19check4x80 g19check4x88)) (join_span (join_span g19check4x96 g19check4x104) (join_span g19check4x112 g19check4x120)))) (join_span (join_span (join_span (join_span g19check4x128 g19check4x136) (join_span g19check4x144 g19check4x152)) (join_span (join_span g19check4x160 g19check4x168) (join_span g19check4x176 g19check4x184))) (join_span (join_span (join_span g19check4x192 g19check4x200) (join_span g19check4x208 g19check4x216)) (join_span (join_span g19check4x224 g19check4x232) (join_span g19check4x240 (join_span g19check4x248 g19check4x256)))))) (join_span (join_span (join_span (join_span (join_span g19check4x264 g19check4x272) (join_span g19check4x280 g19check4x288)) (join_span (join_span g19check4x296 g19check4x304) (join_span g19check4x312 g19check4x320))) (join_span (join_span (join_span g19check4x328 g19check4x336) (join_span g19check4x344 g19check4x352)) (join_span (join_span g19check4x360 g19check4x368) (join_span g19check4x376 g19check4x384)))) (join_span (join_span (join_span (join_span g19check4x392 g19check4x400) (join_span g19check4x408 g19check4x416)) (join_span (join_span g19check4x424 g19check4x432) (join_span g19check4x440 g19check4x448))) (join_span (join_span (join_span g19check4x456 g19check4x464) (join_span g19check4x472 g19check4x480)) (join_span (join_span g19check4x488 g19check4x496) (join_span g19check4x504 (join_span g19check4x512 g19check4x520)))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19audit3 := atlasRow g19frame 3 g19rows3 g19rows4 526 g19rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x0 : Span g19audit3 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x8 : Span g19audit3 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x16 : Span g19audit3 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x24 : Span g19audit3 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x32 : Span g19audit3 32 40 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x40 : Span g19audit3 40 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x48 : Span g19audit3 48 56 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x56 : Span g19audit3 56 64 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x64 : Span g19audit3 64 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x72 : Span g19audit3 72 80 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x80 : Span g19audit3 80 88 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x88 : Span g19audit3 88 96 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x96 : Span g19audit3 96 104 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x104 : Span g19audit3 104 112 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x112 : Span g19audit3 112 120 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x120 : Span g19audit3 120 128 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x128 : Span g19audit3 128 136 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x136 : Span g19audit3 136 144 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x144 : Span g19audit3 144 152 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x152 : Span g19audit3 152 160 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x160 : Span g19audit3 160 168 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x168 : Span g19audit3 168 176 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x176 : Span g19audit3 176 184 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x184 : Span g19audit3 184 192 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x192 : Span g19audit3 192 200 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x200 : Span g19audit3 200 208 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x208 : Span g19audit3 208 216 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x216 : Span g19audit3 216 224 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x224 : Span g19audit3 224 232 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x232 : Span g19audit3 232 240 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x240 : Span g19audit3 240 248 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x248 : Span g19audit3 248 256 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x256 : Span g19audit3 256 264 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x264 : Span g19audit3 264 272 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x272 : Span g19audit3 272 280 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x280 : Span g19audit3 280 288 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x288 : Span g19audit3 288 296 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x296 : Span g19audit3 296 304 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x304 : Span g19audit3 304 312 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x312 : Span g19audit3 312 320 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x320 : Span g19audit3 320 328 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x328 : Span g19audit3 328 336 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x336 : Span g19audit3 336 344 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x344 : Span g19audit3 344 352 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x352 : Span g19audit3 352 360 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x360 : Span g19audit3 360 368 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x368 : Span g19audit3 368 376 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x376 : Span g19audit3 376 384 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x384 : Span g19audit3 384 392 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x392 : Span g19audit3 392 400 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x400 : Span g19audit3 400 408 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x408 : Span g19audit3 408 416 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x416 : Span g19audit3 416 424 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x424 : Span g19audit3 424 432 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x432 : Span g19audit3 432 440 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x440 : Span g19audit3 440 448 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x448 : Span g19audit3 448 456 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x456 : Span g19audit3 456 464 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x464 : Span g19audit3 464 472 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x472 : Span g19audit3 472 480 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x480 : Span g19audit3 480 488 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x488 : Span g19audit3 488 496 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x496 : Span g19audit3 496 504 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x504 : Span g19audit3 504 512 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x512 : Span g19audit3 512 520 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x520 : Span g19audit3 520 528 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x528 : Span g19audit3 528 536 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x536 : Span g19audit3 536 544 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x544 : Span g19audit3 544 546 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19done3 : Region g19frame 3 546 g19rows3 :=
  atlas_sound g19proper g19frame g19vframe 3 546 526 g19rows3 g19rows4 g19rot g19done4 (join_span (join_span (join_span (join_span (join_span (join_span g19check3x0 g19check3x8) (join_span g19check3x16 g19check3x24)) (join_span (join_span g19check3x32 g19check3x40) (join_span g19check3x48 g19check3x56))) (join_span (join_span (join_span g19check3x64 g19check3x72) (join_span g19check3x80 g19check3x88)) (join_span (join_span g19check3x96 g19check3x104) (join_span g19check3x112 (join_span g19check3x120 g19check3x128))))) (join_span (join_span (join_span (join_span g19check3x136 g19check3x144) (join_span g19check3x152 g19check3x160)) (join_span (join_span g19check3x168 g19check3x176) (join_span g19check3x184 g19check3x192))) (join_span (join_span (join_span g19check3x200 g19check3x208) (join_span g19check3x216 g19check3x224)) (join_span (join_span g19check3x232 g19check3x240) (join_span g19check3x248 (join_span g19check3x256 g19check3x264)))))) (join_span (join_span (join_span (join_span (join_span g19check3x272 g19check3x280) (join_span g19check3x288 g19check3x296)) (join_span (join_span g19check3x304 g19check3x312) (join_span g19check3x320 g19check3x328))) (join_span (join_span (join_span g19check3x336 g19check3x344) (join_span g19check3x352 g19check3x360)) (join_span (join_span g19check3x368 g19check3x376) (join_span g19check3x384 (join_span g19check3x392 g19check3x400))))) (join_span (join_span (join_span (join_span g19check3x408 g19check3x416) (join_span g19check3x424 g19check3x432)) (join_span (join_span g19check3x440 g19check3x448) (join_span g19check3x456 (join_span g19check3x464 g19check3x472)))) (join_span (join_span (join_span g19check3x480 g19check3x488) (join_span g19check3x496 g19check3x504)) (join_span (join_span g19check3x512 g19check3x520) (join_span g19check3x528 (join_span g19check3x536 g19check3x544)))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19audit2 := atlasRow g19frame 2 g19rows2 g19rows3 546 g19rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x0 : Span g19audit2 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x8 : Span g19audit2 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x16 : Span g19audit2 16 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x24 : Span g19audit2 24 32 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x32 : Span g19audit2 32 40 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x40 : Span g19audit2 40 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x48 : Span g19audit2 48 56 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x56 : Span g19audit2 56 64 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x64 : Span g19audit2 64 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x72 : Span g19audit2 72 80 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x80 : Span g19audit2 80 88 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x88 : Span g19audit2 88 96 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x96 : Span g19audit2 96 104 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x104 : Span g19audit2 104 112 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x112 : Span g19audit2 112 120 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x120 : Span g19audit2 120 128 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x128 : Span g19audit2 128 136 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x136 : Span g19audit2 136 144 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x144 : Span g19audit2 144 152 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x152 : Span g19audit2 152 160 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x160 : Span g19audit2 160 168 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x168 : Span g19audit2 168 169 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19done2 : Region g19frame 2 169 g19rows2 :=
  atlas_sound g19proper g19frame g19vframe 2 169 546 g19rows2 g19rows3 g19rot g19done3 (join_span (join_span (join_span (join_span g19check2x0 g19check2x8) (join_span g19check2x16 (join_span g19check2x24 g19check2x32))) (join_span (join_span g19check2x40 (join_span g19check2x48 g19check2x56)) (join_span g19check2x64 (join_span g19check2x72 g19check2x80)))) (join_span (join_span (join_span g19check2x88 g19check2x96) (join_span g19check2x104 (join_span g19check2x112 g19check2x120))) (join_span (join_span g19check2x128 (join_span g19check2x136 g19check2x144)) (join_span g19check2x152 (join_span g19check2x160 g19check2x168)))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19audit1 := atlasRow g19frame 1 g19rows1 g19rows2 169 g19rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check1x0 : Span g19audit1 0 8 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check1x8 : Span g19audit1 8 16 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check1x16 : Span g19audit1 16 17 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19done1 : Region g19frame 1 17 g19rows1 :=
  atlas_sound g19proper g19frame g19vframe 1 17 169 g19rows1 g19rows2 g19rot g19done2 (join_span g19check1x0 (join_span g19check1x8 g19check1x16))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19audit0 := atlasRow g19frame 0 g19rows0 g19rows1 17 g19rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check0x0 : Span g19audit0 0 1 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19done0 : Region g19frame 0 1 g19rows0 :=
  atlas_sound g19proper g19frame g19vframe 0 1 17 g19rows0 g19rows1 g19rot g19done1 g19check0x0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawNo : ¬Feasible g19X 13 1 (wires g19V) := by
  apply full_raw (positive_checked (v:=g19V) (by decide +kernel))
  exact cut_sound g19nd g19f6valid (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fullNo : ¬Feasible target 13 1 start.toFinset := by
  rw [show start.toFinset=wires rootV by decide +kernel]
  apply root_choices g19frame extra g19V (by decide +kernel) _ (whole g19done0) rawNo
  apply forced_except _ (by decide +kernel)
  intro w hw
  change w ∈ rootStep.out :: rootStep.rest g19V
  apply List.mem_cons_of_mem
  simpa [rootStep,Step.rest] using hw

end PEqualNP.Outside.L_meta_2161

open PEqualNP.Outside.L_meta_2161

theorem PEqualNP.Outside.L_meta_2161 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → x4 = x3) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C hf hn hfirst he
  by_contra fail
  apply fullNo
  apply starts (C := C) (by omega) hf hn hfirst
  intro y
  exact congrFun he y
