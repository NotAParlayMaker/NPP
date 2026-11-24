import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2956

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


open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma twoCount (gs : List Gate) (i j : Fin gs.length) (ne : i≠j)
    (hi : (gs.get i).op=GateOp.not) (hj : (gs.get j).op=GateOp.not)
    (only : ∀ k : Fin gs.length, (gs.get k).op=GateOp.not → k=i ∨ k=j) :
    (gs.filter negative).length=2 := by
  classical
  have eq : Finset.univ.filter (fun k : Fin gs.length=>negative (gs.get k))={i,j} := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    rw [neg_iff]
    constructor
    · exact only k
    · rintro (rfl|rfl) <;> assumption
  rw [←List.countP_eq_length_filter]
  have h:=List.countP_ofFn gs.get negative
  rw [List.ofFn_get,eq] at h
  simpa [ne] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def packedWord := [18440827511444797640,18441957826578283724,18446744073709222136,18446744073709485308,18446744073708175304,18446744073709551615,18446744073709223928,18446744073709551615]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def tableAnswer (x : Fin 9 → Bool) : Bool :=
  let i:=PEqualNP.MetaComplexity.tableIndex x
  (packedWord.getD (i/64) 0).testBit (Nat.mod i 64)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma table_row (r : Fin 512) : tableAnswer (testRow r)=edgeF (testRow r) := by
  have q : ∀ i : Fin 512, tableAnswer (testRow i)=edgeF (testRow i) := by decide +kernel
  exact q r
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma table_mem (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = tableAnswer y) :
    target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have e : w.getD C.output 0 = target := by
    apply BitVec.eq_of_getElem_eq
    intro r hr
    change bit (w.getD C.output 0) ⟨r,hr⟩ = bit target ⟨r,hr⟩
    rw [targetRow, ←read_bit]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ (fun g hg => (hf g hg).1),rawRow]
    exact (he _).trans (table_row _)
  have h := read_mem w C.output
  rw [e] at h
  simpa only [pool,Finset.mem_insert,List.mem_toFinset, targetProper.1,targetProper.2,
    false_or] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma startsTwo {C : Circuit} (hsize : C.size ≤ 15) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hn1 : (C.gates.filter negative).length=2)
    (hw9 : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2))
    (he : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = tableAnswer y) :
    Feasible target 12 2 start.toFinset := by
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
    have hm := table_mem C hf he
    rw [hgs] at hm
    change target ∈ execute gs (raw ++ [gv raw g]) at hm
    rw [hv] at hm
    have h := extract targetProper gs start (fun a ha => hf a (by rw [hgs]; simp [ha])) hm
    have h' := weaken h (show (gs.filter (fun g => !negative g)).length ≤ 12 by omega)
      (show (gs.filter negative).length ≤ 2 by omega) (by rfl)
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initial_price_any {t : ℕ} {x y : Word} {f : Basis x} {S child : Finset Word}
    (hy : proper y) (forbidden : ¬Feasible y (f.lo-1) t child) (ex : f.proj.q x = y)
    (inc : available f.proj S f.base ⊆ insert 0 child) :
    (Price.mk f 0).Valid t S := by
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
lemma cheap_cut {x : Word} {c : Charts x} {f : Frame c} (v : f.Valid)
    (h : f.ps.any (cheapCut f.b f.v)=true) : f.No := by
  obtain ⟨p,hp,hc⟩ := List.any_eq_true.mp h
  exact cut_sound v.1 (v.2 _ hp) (cheap_sound_cut hc)

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
theorem g0bound : ¬Feasible g0X 0 2 (wires g0V) := by
  apply full_raw (positive_checked (v:=g0V) (by decide +kernel))
  intro h
  have total:=exact_size h
  have card : (wires g0V).card=2 := by decide +kernel
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
theorem g1bound : ¬Feasible g1X 1 2 (wires g1V) := by
  apply full_raw (positive_checked (v:=g1V) (by decide +kernel))
  intro h
  have total:=exact_size h
  have card : (wires g1V).card=3 := by decide +kernel
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
theorem g2bound : ¬Feasible g2X 2 2 (wires g2V) := by
  apply full_raw (positive_checked (v:=g2V) (by decide +kernel))
  intro h
  have total:=exact_size h
  have card : (wires g2V).card=4 := by decide +kernel
  omega

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
theorem g4bound : ¬Feasible g4X 2 2 (wires g4V) := by
  apply full_raw (positive_checked (v:=g4V) (by decide +kernel))
  intro h
  have total:=exact_size h
  have card : (wires g4V).card=4 := by decide +kernel
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
theorem g6bound : ¬Feasible g6X 2 2 (wires g6V) := by
  apply full_raw (positive_checked (v:=g6V) (by decide +kernel))
  intro h
  have total:=exact_size h
  have card : (wires g6V).card=4 := by decide +kernel
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
def g3f0 : Basis g3X := basisFor g3X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g3V.map Wire.w) 3 (assignRows [9,0,1,2,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f0valid : (Price.mk g3f0 0).Valid 2 (wires g3V) :=
  initial_price_any g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f1 : Basis g3X := basisFor g3X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g3V.map Wire.w) 3 (assignRows [0,9,2,1,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f1valid : (Price.mk g3f1 0).Valid 2 (wires g3V) :=
  initial_price_any g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f2 : Basis g3X := basisFor g3X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g3V.map Wire.w) 3 (assignRows [0,2,9,3,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f2valid : (Price.mk g3f2 0).Valid 2 (wires g3V) :=
  initial_price_any g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f3 : Basis g3X := basisFor g3X 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff (g3V.map Wire.w) 3 (assignRows [2,0,3,9,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f3valid : (Price.mk g3f3 0).Valid 2 (wires g3V) :=
  initial_price_any g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3f4 : Basis g3X := basisFor g3X 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff (g3V.map Wire.w) 3 (assignRows [2,3,0,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3f4valid : (Price.mk g3f4 0).Valid 2 (wires g3V) :=
  initial_price_any g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g3prices : List (Price g3X) := [⟨g3f0,0⟩,⟨g3f1,0⟩,⟨g3f2,0⟩,⟨g3f3,0⟩,⟨g3f4,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g3valid : ∀ p ∈ g3prices, p.Valid 2 (wires g3V) := by
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
def g3frame2 : Frame g3C := ⟨5,2,g3V,g3prices⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g3bound : ¬Feasible g3X 5 2 (wires g3V) := by
  apply full_raw (positive_checked (v:=g3V) (by decide +kernel))
  exact fast_sound (fun _=>false) (by intro f h; contradiction) g3proper 3 (f:=g3frame2) ⟨g3nd,g3valid⟩ (by decide +kernel)

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
theorem g5bound : ¬Feasible g5X 3 2 (wires g5V) := by
  apply full_raw (positive_checked (v:=g5V) (by decide +kernel))
  intro h
  have total:=exact_size h
  have card : (wires g5V).card=5 := by decide +kernel
  omega

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
def g7f1 : Basis g7X := basisFor g7X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g7V.map Wire.w) 3 (assignRows [0,9,1,2,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g7f1valid : (Price.mk g7f1 0).Valid 2 (wires g7V) :=
  initial_price_any g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g7bound : ¬Feasible g7X 3 2 (wires g7V) := by
  apply full_raw (positive_checked (v:=g7V) (by decide +kernel))
  intro h
  have total:=exact_size h
  have card : (wires g7V).card=5 := by decide +kernel
  omega

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
def g8f0 : Basis g8X := basisFor g8X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g8V.map Wire.w) 6 (assignRows [9,0,1,2,3,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g8f0valid : (Price.mk g8f0 0).Valid 2 (wires g8V) :=
  initial_price_any g3proper g3bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g8bound : ¬Feasible g8X 6 2 (wires g8V) := by
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
def g9f0 : Basis g9X := basisFor g9X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g9V.map Wire.w) 4 (assignRows [9,0,1,2,3,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9f0valid : (Price.mk g9f0 0).Valid 2 (wires g9V) :=
  initial_price_any g7proper g7bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9f1 : Basis g9X := basisFor g9X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g9V.map Wire.w) 4 (assignRows [0,9,1,3,2,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9f1valid : (Price.mk g9f1 0).Valid 2 (wires g9V) :=
  initial_price_any g7proper g7bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9f2 : Basis g9X := basisFor g9X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g9V.map Wire.w) 4 (assignRows [0,1,9,2,3,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9f2valid : (Price.mk g9f2 0).Valid 2 (wires g9V) :=
  initial_price_any g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9f3 : Basis g9X := basisFor g9X 0x550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055 (g9V.map Wire.w) 3 (assignRows [9,0,1,9,2,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9f3valid : (Price.mk g9f3 0).Valid 2 (wires g9V) :=
  initial_price_any g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9f4 : Basis g9X := basisFor g9X 0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333 (g9V.map Wire.w) 3 (assignRows [0,9,1,2,9,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9f4valid : (Price.mk g9f4 0).Valid 2 (wires g9V) :=
  initial_price_any g2proper g2bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9f5 : Basis g9X := basisFor g9X 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f (g9V.map Wire.w) 3 (assignRows [0,2,9,1,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9f5valid : (Price.mk g9f5 0).Valid 2 (wires g9V) :=
  initial_price_any g4proper g4bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g9prices : List (Price g9X) := [⟨g9f0,0⟩,⟨g9f1,0⟩,⟨g9f2,0⟩,⟨g9f3,0⟩,⟨g9f4,0⟩,⟨g9f5,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g9valid : ∀ p ∈ g9prices, p.Valid 2 (wires g9V) := by
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
def g9frame2 : Frame g9C := ⟨5,2,g9V,g9prices⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g9bound : ¬Feasible g9X 5 2 (wires g9V) := by
  apply full_raw (positive_checked (v:=g9V) (by decide +kernel))
  exact fast_sound (fun _=>false) (by intro f h; contradiction) g9proper 3 (f:=g9frame2) ⟨g9nd,g9valid⟩ (by decide +kernel)

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
theorem g10bound : ¬Feasible g10X 4 2 (wires g10V) := by
  apply full_raw (positive_checked (v:=g10V) (by decide +kernel))
  intro h
  have total:=exact_size h
  have card : (wires g10V).card=6 := by decide +kernel
  omega

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
def g12f0 : Basis g12X := basisFor g12X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g12V.map Wire.w) 4 (assignRows [9,0,1,2,3,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12f0valid : (Price.mk g12f0 0).Valid 2 (wires g12V) :=
  initial_price_any g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12f1 : Basis g12X := basisFor g12X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g12V.map Wire.w) 4 (assignRows [0,9,2,1,4,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12f1valid : (Price.mk g12f1 0).Valid 2 (wires g12V) :=
  initial_price_any g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12f2 : Basis g12X := basisFor g12X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g12V.map Wire.w) 4 (assignRows [0,2,9,4,1,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12f2valid : (Price.mk g12f2 0).Valid 2 (wires g12V) :=
  initial_price_any g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12f3 : Basis g12X := basisFor g12X 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff (g12V.map Wire.w) 4 (assignRows [2,0,4,9,3,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12f3valid : (Price.mk g12f3 0).Valid 2 (wires g12V) :=
  initial_price_any g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12f4 : Basis g12X := basisFor g12X 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff (g12V.map Wire.w) 4 (assignRows [2,4,0,3,9,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12f4valid : (Price.mk g12f4 0).Valid 2 (wires g12V) :=
  initial_price_any g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12f5 : Basis g12X := basisFor g12X 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff (g12V.map Wire.w) 4 (assignRows [4,2,3,0,1]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12f5valid : (Price.mk g12f5 0).Valid 2 (wires g12V) :=
  initial_price_any g5proper g5bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g12prices : List (Price g12X) := [⟨g12f0,0⟩,⟨g12f1,0⟩,⟨g12f2,0⟩,⟨g12f3,0⟩,⟨g12f4,0⟩,⟨g12f5,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12valid : ∀ p ∈ g12prices, p.Valid 2 (wires g12V) := by
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
def g12frame2 : Frame g12C := ⟨6,2,g12V,g12prices⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g12bound : ¬Feasible g12X 6 2 (wires g12V) := by
  apply full_raw (positive_checked (v:=g12V) (by decide +kernel))
  exact fast_sound (fun _=>false) (by intro f h; contradiction) g12proper 3 (f:=g12frame2) ⟨g12nd,g12valid⟩ (by decide +kernel)

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
theorem g14bound : ¬Feasible g14X 4 2 (wires g14V) := by
  apply full_raw (positive_checked (v:=g14V) (by decide +kernel))
  intro h
  have total:=exact_size h
  have card : (wires g14V).card=6 := by decide +kernel
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
def g11f0 : Basis g11X := basisFor g11X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g11V.map Wire.w) 7 (assignRows [9,0,1,2,3,4,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g11f0valid : (Price.mk g11f0 0).Valid 2 (wires g11V) :=
  initial_price_any g8proper g8bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g11bound : ¬Feasible g11X 7 2 (wires g11V) := by
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
def g13f0 : Basis g13X := basisFor g13X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g13V.map Wire.w) 7 (assignRows [9,0,1,3,4,2,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f0valid : (Price.mk g13f0 0).Valid 2 (wires g13V) :=
  initial_price_any g8proper g8bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13f1 : Basis g13X := basisFor g13X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g13V.map Wire.w) 7 (assignRows [0,9,3,1,4,5,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f1valid : (Price.mk g13f1 0).Valid 2 (wires g13V) :=
  initial_price_any g8proper g8bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13f2 : Basis g13X := basisFor g13X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g13V.map Wire.w) 7 (assignRows [1,3,9,0,4,2,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f2valid : (Price.mk g13f2 0).Valid 2 (wires g13V) :=
  initial_price_any g8proper g8bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13f3 : Basis g13X := basisFor g13X 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff (g13V.map Wire.w) 7 (assignRows [3,1,0,9,4,5,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f3valid : (Price.mk g13f3 0).Valid 2 (wires g13V) :=
  initial_price_any g8proper g8bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13f4 : Basis g13X := basisFor g13X 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff (g13V.map Wire.w) 7 (assignRows [0,1,4,5,9,2,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f4valid : (Price.mk g13f4 0).Valid 2 (wires g13V) :=
  initial_price_any g12proper g12bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13f5 : Basis g13X := basisFor g13X 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff (g13V.map Wire.w) 6 (assignRows [0,3,1,4,2,9,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f5valid : (Price.mk g13f5 0).Valid 2 (wires g13V) :=
  initial_price_any g9proper g9bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13f6 : Basis g13X := basisFor g13X 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff (g13V.map Wire.w) 6 (assignRows [3,0,4,1,2,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13f6valid : (Price.mk g13f6 0).Valid 2 (wires g13V) :=
  initial_price_any g9proper g9bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13prices : List (Price g13X) := [⟨g13f0,0⟩,⟨g13f1,0⟩,⟨g13f2,0⟩,⟨g13f3,0⟩,⟨g13f4,0⟩,⟨g13f5,0⟩,⟨g13f6,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13valid : ∀ p ∈ g13prices, p.Valid 2 (wires g13V) := by
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
def g13frame : Frame g13C := ⟨9,2,g13V,g13prices⟩
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
 #[0x31424005003800c00fb006019e00301600051aad00d196d00d0f5b0040d7900102e5007349400b0e7b002244b0080fd3009379900b172c0072deb002388100e02b900811590092a9f007181500b25700020fcf00a0c2400018a40082b260091e3c00b3d620070e4e0021f9a000097d00a18fc00e2b0c008354e009028c0000054321]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rows1 : Rows := #[
 #[0x2825b7028102f04308640302d1801c302101c03be030180b041028f0000000001040,0x570fdf0520085054337b0242d6202436130542cd204d21a005416fc02404570090b0b043178b0241c490540d35043086400917e304d09f30191dbd01903ae0590d6805303dc0000043251009,0x4a1c0901e368102a2eb6015136d02e267301d3a100423e5d0443c3a00000000020c8,0x32018602717aa055084d04006cf049160d03c1adb02201f603d152d0472d35017349d0452eb8022257703d3c1f0511986047088804c0ac4017150004502b00380efd0101a3700b074502b15cb01104d802b33860112080000005432100c,0x3c0d9f03c1adb01208540121e4202a033203f095102a176803f1ad402a2eb603f24a402a3e8103f3ec90070ec500714b6000004321500a,0x480b9500a3ab504a308504f3a2501e04bb04b3ef000a11aa04a1c09034085e02804de04f1a8801e2bd402825b7004153604b17460370e0c056094600f097e00d1bfd00337e200d3d290031db4018041305303dc000005432100d,0x551dd5055084d05200850021539002083f0023bdc002202c0580a6e00000000002d4,0x223e7404f1a8801715000540d350142a2602111ec00504f2036388f01a2cdc00c1dbb0000000001050,0x453ff90472d3503f095101a182f033321901d17e6026365403b0d2e03a1fbf02906fe0142a260302d1801f01260350c4600816300000053214008,0x2c2f86002202c01b07fb0392de902123220502d0902e02d904e15ba0052c79015270f006214703626a300013fe0423e5d0013ab201c1732013292e02f0a1a046053d05303dc0000054312001,0x34085e051198600402d60090b0b03a1fbf00112c803a36650013ab20310fe500000000020c0,0xa3ab503d152d0242d6203332190251725000351f02305a604e08bc0200fcb0502d0902d2d8e00000000001d0,0x270d3202717aa05a042a0570fdf02c149602c079c02c3b3902c2f8600e0b1100000000002d8,0x401f810480b95049160d0121e4201b32f903905ff01b199c0392de903e0cae0000000000250,0x4b3ef004b296804d21a00263654026295a0063cf7006214701609530000000003140]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rows2 : Rows := #[
 #[0x418e200d1d400000000000058005,0x2a18da0000000001038009,0x25017c00000000000052d4,0x61375000000000200b038,0x2a0c0200000000020c000d,0x260e2c0000000001050007,0x82aea0000000001030007,0x281d22000000000000a05a,0x62b86000000000000605a,0x2a0c0200000000020c000b,0x17154800d1d40000000000005800d,0x1404a5000000000000c04e,0x2617f300000000000d8001,0x1524c7000000000300b040,0x270b3e02b00d900000000002d8001,0x281d22000000000500d050,0x309dd0032c2002c0eec000000000000e052,0x3712000000000000c03e,0x2094b000000000000a2de,0x1b20530000000003005054,0x41d8,0x103f780000000000048007,0x802970000000003140001,0x2617f300000000000d800f],
 #[0x2c11b30201cea0281d220153fa10062b8601510d0006015b000005432100d002,0x1404a5000000000500904c,0x262dc900000000000061d6,0x2094b0000000000001258,0x1a095b0000000001040005,0x10185f00000000000061ce,0x10185f000000000314800f,0x24127e000000000100200a,0x2258,0x2617f300000000000d8007,0x1d800e,0x4258,0x50bc100d054e00000000000d000b,0x1e151c0173f9100537c90070f83001032301d277001922b10000000000158221,0x82aea00000000000020b6,0xc006402b00d900000000002d800f,0x1a188200000000000b800f,0x221fd4000000000200400a,0x10042900000000001c800b,0x1b2053000000000000e03e,0xf1acb02b00d900000000000052d8,0x183f7900d054e00000000000d0001,0x10042900000000040011c8,0x1b6a000000000100104c],
 #[0x1a1882000000000000413e,0x2a0c0200000000020c0001,0x210a5d0290b00000000000000c010,0x72d2400d1d4000000000000020de,0x2a0c0200000000020c000f,0x153fa1000000000000805a,0x26347200000000040051d8,0x1c395601c1c0100b103602c11b3000000000000d058,0xa20ce00a03110201cea000000000000c05e,0x21f390000000000005250,0x2a18da0000000000038007,0x92942000000000300600a,0x23028e000000000500a010,0x1e151c00d370a000000000015800f,0x21f390000000000250001,0xe07b0000000000400800c,0x25800e,0x1a095b0000000001040001,0x10185f0000000003148009,0x1a095b000000000104000b,0x10185f0000000003148001,0x1f3daa000000000100200e,0x1b0a7e0001b6a0000054321001002,0x11368b000000000200400e],
 #[0x21f39000000000025000f,0x2094b000000000025800f,0x103f78000000000004800d,0x82aea000000000103000d,0x5800e,0x82aea000000000103000b,0x1d316600d2e5900000000000031d0,0x2617f300000000000d800d,0x1337e00d054e00000000000d0007,0x38010,0x25017c00000000000092d4,0x2b00d9025017c002094b0021f39026347200d2e59010042900d370a0262dc9010185f008029702617f300d054e0102fad02a0c0201a188200d1d400260e2c0103f7801a095b02a18da0082aea0000054321001001,0x260e2c000000000105000b,0x25017c000000000000c35a,0xb10360201cea0132628013086b000000000000d054,0x120b8d02b00d900000000000092d8,0x25017c00000000002d4001,0x141eb401404a50000043215009002,0xc006400c1ad900f07c500f1acb00f2e6800f32b801602b500000000002d82a1]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rows3 : Rows := #[
 #[0x30020da,0x438c00000000000003158221,0x1001258,0xe052045,0x13f6800000000000010d00a1,0x40cb800000000000d00a1009,0x205a001,0x438c000000000000061de221,0x1001140,0x2006029,0xc05e121,0xb0540dd,0x5040800000000002d82a100d,0x40cb800000000000010010d0,0x800c029,0x5040800000000000072d82a1,0x10011c8,0x109b40000000000006010029,0x30b2d00000000000092d80a1,0x23c0f000000000000d05403d,0x90020d2,0x2052001,0x5040800000000002d82a1001,0x40cb800000000000d00a100d],
 #[0x158001045,0x41e740000000000058121001,0x1001040,0x10020da,0x300000000000000b0581a1,0x41e740000000000058121005,0x4270300000000001d01a100b,0x8010029,0x2034800225f3000000000000b0020da,0xc01002d,0x2008029,0xa010029,0x4008029,0x10012d4,0x1001050,0x2d800104d,0xa052001,0x30b2d000000000000c010029,0x10010c0,0x5040800000000000010012d8,0x20bd0000300000000000000b0020de]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rows4 : Rows := #[
 #[0xb0020de1a1,0x6010029045,0xb0020da045,0x92d80a1001,0x10010d00a1,0x10012d82a1]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13rows5 : Rows := #[]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13audit4 := atlasRow g13frame 4 g13rows4 g13rows5 0 g13rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check4x0 : Span g13audit4 0 6 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13done4 : Region g13frame 4 6 g13rows4 :=
  atlas_sound g13proper g13frame g13vframe 4 6 0 g13rows4 g13rows5 g13rot (by intro j hj; omega) g13check4x0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13audit3 := atlasRow g13frame 3 g13rows3 g13rows4 6 g13rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x0 : Span g13audit3 0 12 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x12 : Span g13audit3 12 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x24 : Span g13audit3 24 36 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check3x36 : Span g13audit3 36 45 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13done3 : Region g13frame 3 45 g13rows3 :=
  atlas_sound g13proper g13frame g13vframe 3 45 6 g13rows3 g13rows4 g13rot g13done4 (join_span (join_span g13check3x0 g13check3x12) (join_span g13check3x24 g13check3x36))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13audit2 := atlasRow g13frame 2 g13rows2 g13rows3 45 g13rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x0 : Span g13audit2 0 12 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x12 : Span g13audit2 12 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x24 : Span g13audit2 24 36 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x36 : Span g13audit2 36 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x48 : Span g13audit2 48 60 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x60 : Span g13audit2 60 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x72 : Span g13audit2 72 84 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check2x84 : Span g13audit2 84 91 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13done2 : Region g13frame 2 91 g13rows2 :=
  atlas_sound g13proper g13frame g13vframe 2 91 45 g13rows2 g13rows3 g13rot g13done3 (join_span (join_span (join_span g13check2x0 g13check2x12) (join_span g13check2x24 g13check2x36)) (join_span (join_span g13check2x48 g13check2x60) (join_span g13check2x72 g13check2x84)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13audit1 := atlasRow g13frame 1 g13rows1 g13rows2 91 g13rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check1x0 : Span g13audit1 0 12 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check1x12 : Span g13audit1 12 15 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13done1 : Region g13frame 1 15 g13rows1 :=
  atlas_sound g13proper g13frame g13vframe 1 15 91 g13rows1 g13rows2 g13rot g13done2 (join_span g13check1x0 g13check1x12)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g13audit0 := atlasRow g13frame 0 g13rows0 g13rows1 15 g13rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13check0x0 : Span g13audit0 0 1 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13done0 : Region g13frame 0 1 g13rows0 :=
  atlas_sound g13proper g13frame g13vframe 0 1 15 g13rows0 g13rows1 g13rot g13done1 g13check0x0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g13bound : ¬Feasible g13X 9 2 (wires g13V) := by
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
def g15f0 : Basis g15X := basisFor g15X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g15V.map Wire.w) 6 (assignRows [9,0,1,2,3,4,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g15f0valid : (Price.mk g15f0 0).Valid 2 (wires g15V) :=
  initial_price_any g9proper g9bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g15bound : ¬Feasible g15X 6 2 (wires g15V) := by
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
def g16f0 : Basis g16X := basisFor g16X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g16V.map Wire.w) 10 (assignRows [9,0,1,2,3,4,5,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g16f0valid : (Price.mk g16f0 0).Valid 2 (wires g16V) :=
  initial_price_any g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g16bound : ¬Feasible g16X 10 2 (wires g16V) := by
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
def g17f0 : Basis g17X := basisFor g17X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g17V.map Wire.w) 10 (assignRows [9,0,3,4,1,2,5,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f0valid : (Price.mk g17f0 0).Valid 2 (wires g17V) :=
  initial_price_any g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f1 : Basis g17X := basisFor g17X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g17V.map Wire.w) 10 (assignRows [0,9,4,3,1,5,2,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f1valid : (Price.mk g17f1 0).Valid 2 (wires g17V) :=
  initial_price_any g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f2 : Basis g17X := basisFor g17X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g17V.map Wire.w) 10 (assignRows [0,4,9,3,5,1,6,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f2valid : (Price.mk g17f2 0).Valid 2 (wires g17V) :=
  initial_price_any g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f3 : Basis g17X := basisFor g17X 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff (g17V.map Wire.w) 10 (assignRows [4,0,3,9,5,6,1,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f3valid : (Price.mk g17f3 0).Valid 2 (wires g17V) :=
  initial_price_any g13proper g13bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f4 : Basis g17X := basisFor g17X 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff (g17V.map Wire.w) 8 (assignRows [0,1,3,4,9,5,6,2]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f4valid : (Price.mk g17f4 0).Valid 2 (wires g17V) :=
  initial_price_any g11proper g11bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f5 : Basis g17X := basisFor g17X 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff (g17V.map Wire.w) 8 (assignRows [0,3,1,4,5,9,2,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f5valid : (Price.mk g17f5 0).Valid 2 (wires g17V) :=
  initial_price_any g11proper g11bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f6 : Basis g17X := basisFor g17X 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff (g17V.map Wire.w) 8 (assignRows [3,0,4,1,5,2,9,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f6valid : (Price.mk g17f6 0).Valid 2 (wires g17V) :=
  initial_price_any g11proper g11bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17f7 : Basis g17X := basisFor g17X 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff (g17V.map Wire.w) 8 (assignRows [3,4,0,1,2,5,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17f7valid : (Price.mk g17f7 0).Valid 2 (wires g17V) :=
  initial_price_any g11proper g11bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17prices : List (Price g17X) := [⟨g17f0,0⟩,⟨g17f1,0⟩,⟨g17f2,0⟩,⟨g17f3,0⟩,⟨g17f4,0⟩,⟨g17f5,0⟩,⟨g17f6,0⟩,⟨g17f7,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17valid : ∀ p ∈ g17prices, p.Valid 2 (wires g17V) := by
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
def g17frame : Frame g17C := ⟨11,2,g17V,g17prices⟩
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
 #[0x658120054a41004326000062fd00631f70052e0800417b000040710030ecb0021f6e0061f3000508800031b5e00200a700407400002ae00042d2e00007b60060b4c00510b8001056c00128720014c0f001605f0000004321]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows1 : Rows := #[
 #[0xf1df7026002900f07dc02613f00221e65022069d031679e02e6b5101f2e5701f41f702106440160347016176d0323ff9000064321524c,0x2405fb02166980171b4b01f140c0100269007230c0101ef900744420170adb01f0e7b02500cc02e6b5102801af0000003214007,0x8491700c10cd0000cde00c3e0600027560081f8b01b750a007444201b5fd9007674801b2e5e0071ae501b016c0073f320271c8e01d38a2027351701d1e6402f170b000084321525c,0x2550f02d173e0031ef100a0b050033c2d00a257d034085b00e0e9c01c4c91002084902d4db20100269010256f010590c0107d5900e5d8a01c10e003015e203308e400006743212d8,0x197d810013fb002033e30042766012037a02a0d1f00e0e9c029412201914a20012def020080900430be01266270170adb0252de1024418101765ce00e3d0d02959cf02c45e201140720000574132258,0x1790f02669ac02d221000027560012def0263192006049300d07af014239301a2eca0065bd800d5d2d0233f1f02801af000000432100b,0x501900192bdb00f6c780094b72019012e00f49ec002084900c58ec00968ae00354dc00a4a450081f8b00430be012662702229c700416ac0124c15022069d02b4a220151a4501840b901e445e013662700b0c9801e61340134c1500b2289000005432100a]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows2 : Rows := #[
 #[0x9651440060c130960a980065da307b215109e1a9e01d1641087160a08320bc0850085000084321525c00f,0x12089708e2bff058593f039505702f00bd00526ea0614d430902d0c000056432125000f,0x19074204e1d8302a5b78098560f04f53f70655262000000004300a360,0x3842950000000058260012,0x6367e3000000015625000e,0x88006605f1a9f01b72dc05f377501b58ca05f42bc01b2df905f603001b034c088506604416fa038429503815cf0941c40000085432100a012,0x711f860740f6b023487e00c4dbf000031824600b060,0x94c7101741dd07e04c205934c40626cfa0851f4c03d132500f455400007421360052d4,0x4a2c7f00241eb05a74d0011758805a24d20112d080851f4c04a73330021562000004321600c35a,0x97396405c55d8033411202b614a0244984097596402b76d802429f405c370e0332da208124a40630b93063157801f6541000087432100e012,0x19349500a0ad600038cb00a59c40006d170862ee008a0ea900007643212d800f,0x1b72dc035493b02459fa0144616064613f05579dd082072e0574ab000c3af5000004321700a05a,0x8c417d0683462068151a05234640521c9a04c54f409a4e8209c08cd00000000062d4012,0x392a6d023487e0142e4e03140de0377b2a04d15ad0082d8d000064231800b05c,0x8e470f00a0ad600a254e04e1d83020023a020254005318dd0533d2a0180911000000002125005e,0x7777c404563a704b602202e4629000000000524c010,0x5d2bf6020023a07c002f08a0ea90534128043147b00006721430072d8,0x630b9306315780662d6006742b406646d509d00b20672ecd04910d60340ce904905370341c6c05b33470512fb101065d1090323e0000783421360001,0x93795900a0ad60464d59091544304e2947056260903a14a607f1755090071e000074531225800f,0x6e737909945c20970484000000000700e04c,0x6a43c10603e0600d0f8306a1b67000043261700d058,0x30057c0883cf6000000000600c05c,0x457bb70270f7e08f49f603c422e03b06e208d69e802d2d8503241d50407469000000000024c066,0x73577e04860bd020023a07054bd0546ba4090071e05320ab05e2d6a0000571432007258],
 #[0x3341120950af4033144c0296aba07d0eb902933b200d2cbf000003142600e052,0x931c060916b4400a4eac01e233403561b80043dc80692520067097d000000003200a368,0x603e060950af40892abd00367050033ffa000073142600d054,0x5a19dc05201920065da30682ecb096281b0114053059050707e680d0627baa06c631f06d10c0000008432525c0a5,0x7c7b02a10450362aba00022f204307a607c3aac0435e4907c629904703a500000000002603a3,0x8c417d09e03ac002677300241eb0176ed401741dd00f357a00f19c702c0b4a021574900007643212d42a5,0x97396401c2b8a05f208503a14a60841b4302b3c9e031746d000002134700e066,0xb57d40792abe08d444a02d60f90000732145007254,0x12107c09154430917eb80546ba40544eaa073624a073469707a5b38066555c066713b00000000002502de,0x9f662c079079403241d503225fb000064321500124c,0x226685079079403c422e08f2654000004321500a2d2,0x7f289004114fe08345a107f0de00610d70016211306123610160de6086419100c792d0141abf031746d00c56a1014301203159bd00d16d709513c00894d6b000008432100f002,0x733e09053412802640ef073577e042015b05320ab0262550075680400e3774090323e0000783241007360,0x42015b0547ff80546ba40902d0c020136300720a3020023a00747e70000563421007250,0x2820110271fdd03e32d30160de60790794000064321524c011,0x4c54f404a58bb04a733307b1b6803d301f03d132500936c20091b0f03f4b2c00000000002d4066,0x90323e07962db090178e079404f08a0ea90851f4c08a1b3c0850085090071e0792abe0902d0c07907940000004321001001,0x460a250567dec058286401e009c026255008013ae070185605e7bf3007504307a18a106b05fb00000000003602a3,0x936592093795909303d10931c0604860bd04223c304247600480bad09d465109d25710000000000258368,0x5c55d80883cf6072177605c09120724f1c08907f9000004231700e056,0x7660440000000478360002,0x8e2bff036005109b207c06f155b0410b7308a1b3c000058342126000f,0x3b677d03b741d07962db000084321700135c,0x9a4e8209a11bf0134ecf0254101013181e0251d870851f4c00007432162d4001],
 #[0x58260002,0x22154f02209160770a3e028338e077165a0285bc309f007a00b138000b071d078231f001354d000008743235c0a5,0x4b376704b20bf01a04ed01a6a13079404f00004318262dc001,0x650f25038290a03806460921274065526201547f408b107e01513a808b419005015d108a0ea900006743212d8001,0x1950ce01934950191f0a019074205d2bf605d0efc05d129c05d36e9092094e09212740000000000260360]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows3 : Rows := #[
 #[0x4d23f5000000000000a2e6323,0x224f16057441700000000002541a5001,0x503880000000000500a2e205d,0x362af5000000000300905c056,0x291cd8000000000400c3e80a5,0xd57ca000000000025800d02b,0x381fee0314fb7000000000825c1a500d,0x20f42019007100a19ad0000000000005258062,0x2c113800b6101000000000000d05c03d,0x150c6c000000000000125c05e,0x3b4e7a000000002125005e00f,0x570cba000000000200335c125,0x4a72e601b10bd00000421350090020d6,0x2e376502e6f0b000004321700c05a001,0x1a48e6003249d00000000000032580a1,0x501e42000000000100125c055,0x476aa20000000156250001002,0x312dfe00000000072d412500d,0x441a9d03e2c3b000000000025036600f,0x551cde043315f000000000025c001052,0x2c1138000000000700d0020e4,0x5318f30000000000260001056,0x3d7dce0236a3e000000000524c011002,0x503880000000000100125c05d],
 #[0x307334030542e03b4e7a000000000025005e001,0xa2e6360,0x2322a100000000002dc00105a,0x566f7c0373ee0000000000600a01205a,0x65ec5000000000000c0663a3,0x4308bc055574200000000002d401102f,0x17629500a41930356788000000000000a3e8321,0x3925a802974450394cec029631c03f38060030f41000056432100a00e029,0x3b4e7a000000002100725005e,0x2647ff0505e8e00000000002d4065001,0x570cba000000000700e3e2125,0x3600904c0d5,0x2b18b10067c01000000000700c012062,0x120fa204c2f1d000085432125c001051,0x20780200a642b00e450700000000000052e02a3,0x114325000000000024c06600f,0x3d5a69057441700000000002541a500f,0x1c85000000000300a062056,0x4d10be00000000002d8062011,0x1e3f4b000000004500a05e00e,0x2d42a5002,0x11608d0000000000001254066,0x9477a000000000025401202d,0x343461000000000125000f02f],
 #[0x461ea8000000000000c05c05d,0x3a11a701f13e60100cf600b05080043d0b00000432160090020d2,0x110d390000000000003254056,0x3c72c7000000000500c012052,0x144bfc0344aa20000000000360001052,0x2e0010069,0x4d23f5000000000026032300f,0x1f282f000000000000d04c05e,0xc360001,0x3a766000000000002e000f063,0x3a766000000000002e0011066,0x114325000000000000724c066,0x110d39000000000025405600f,0x150c6c000000000000325c05e,0x2322a100000000002dc00f02f,0x1524f5000000000025c056001,0x11356d000000000035c2a7001,0x21142005338ff000000000026000f002,0x512d9b00000000000072503e8,0x4d03e900000000000072603a3,0x490ebe04550f0049580d0450d76000074321600c01002d,0x11356d000000000000a3e4325,0x524c1e035311400a419300000000003602a3011,0x4d03e900000000002603a3001],
 #[0x510cfd0000000000001258368,0xd1257000000000036000104e,0x1545ae00000000002d42a700f,0x401210000000001700a3e4001,0x1545ae000000000000a35c325,0x1029cc0000000000009054056,0x3b2fa3000000003125006600d,0x2d17e300000000002d8012029,0x58260001002,0x143310276d130015a4f027066b01a2f1600000004212e000103d,0x25c0a500e,0x425cc603b2fa30000000001005250066,0x3e03c1002572f00000000000012583e6,0x2f46b6000000000001005205e,0x83abb00a3ce3000000000025006200d,0x2c11380562e7102b0a8d01668e6000000843100e062035,0x332d980441a9d00a642b00000000002e02a300f,0x31114a000000005400725c125,0x31063700000000072d40a500d,0x474a0d0000000000258001037,0x9ca000000000700a01005e,0x5260360,0xe45070486aad00a3ce30000000000005250062,0x2f46b6000000004600c066010],
 #[0x905c0e5,0x3a65f0034700200d4f1a0000000002258011002,0x3164e8000000008300525c225,0x165f5000000000000e01202b,0x1e3f4b000000000000e04a056,0x4156bf04b1a1200000000002d8001012,0x3e1a4c00000000002e00013e7,0x27066b013335204b27d7000000000000a368001,0x25c12500e,0x395526000000000000a3e80a1,0x24626902e7c6d000000000000f050062,0xa419300000000033602a3001,0x2d4225002,0x7430e031063700000000062d40a5001,0x4078d000000000300c06405d,0x535f9700000000002d801102b,0xa2d2f00218f00000000002003360323,0x4a58a80000000000009058062,0x52f7703c2b7f000000000001004e052,0x3e03c100e32e200000000000032583e6,0x2a361301b589a000000000600b060323,0x476aa200000000000012500a2,0x3f38060000000001250002035,0xc3e4125],
 #[0x2dc125002,0x57677c0114325011274b000004321500100124c,0x355ae903575610445d9600e724d00e555300218f00023d3d01c4d5a00000000002e03a3065,0x150c6c000000000025c05e00d,0x4d4c6f00000000000072d82a3,0x2818d2000000000000c05a056,0x317dfc00000000730052d4225,0x3862e0011002,0x8262605229ed01774650331c9a020315104804570193c4100c10270000000000360323125,0x924dc0093a02000084312600c01202d,0xf1060000000000200a05a04e,0x38325b0322d2a0386baf0327eba02535f304e2bb5043315f000000000525c00d002,0x18384e0370d01000000000001005e323,0x3164e80314fb70313e3c031114a0150c6c050388001524f50501e42000004321500100125c,0x6700b002060,0x4c17ff04550f000000000002d401102d,0x280c3f000000000000a066012,0x3615590364db00461ea8000004231700b0020da,0x3b4e7a04d4c6f03b1d6804d10be00000043210010012d8,0x1d277b01d724d0211420000000000026000105a,0x25c05d00e,0x1158cd000000000000535c327,0x3b0ceb000000004225806600d,0x110d39000000000000a2da056],
 #[0x3e03c10510cfd03b4e7a00a710003e47e703b0ceb00a19ad0000003412001001258,0x355ae903e1a4c00000000002e001046d,0x260001360,0x510cfd000000000025800e3ee,0x2d17e304f006d02d439704f517f000067432100c010029,0x700d0020dc,0x325e730313e3c000000000525c12500d,0xf1060000000000400a05e010,0x4f006d00000000212d801202d,0x1005c045,0x12271c0551cde0543288000004321525c00100e,0x213168000000004226000d02f,0x490ebe00000000002d401202d,0x512d9b00000000002503e8001,0x25016c0500b1700000000002d42a500f,0x570cba000000000400735c125]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows4 : Rows := #[
 #[0x6267e000000000000a01005e0a1,0xa00e02b035,0x8187f00000000000052580623a5,0x12500a1001,0x300b0020e202e,0x1004e05a1a5,0xa05201002d,0x25c125001002,0x3310700000000002e03a30a500f,0xc3e40a5001,0x331070080e8d00000000000010012e03a3,0x90020d203d,0x3038c00000000003602a31a5001,0xb0023e8121,0x85b16000000000000125005a2a5,0x70cdb000000000000c062056001,0x90020d205e,0x1001254056,0x25c00105100e,0x200c3e800102d,0x2e000104a03d,0x100125c05e,0xa052035002,0x363b3000000000025005a1a500d],
 #[0xe04e062125,0x359ab0000000000005258062125,0x73600a1002,0x24ccf000000000000a052001062,0x83e410000000000250062325001,0x260001052045,0xa052066001,0xa05600105e,0x359ab0000000000003258062125,0x212d8001062001,0x35c0a5001002,0xb0023e4125,0x7141000000000000b058323225,0x2d42a500f002,0x25c055001002,0xa368001045,0xa06204e001,0x56e08000000000000a3e80a5001,0x2583d000000000000f0603a32a5,0xa01006a03d,0xf0020e404d,0xa01202905e,0x657a00000000000090020e6323,0xa056012029],
 #[0x2d806600103d,0x10012d40a5,0x25c22500d002,0x3038c000000000000b360323225,0x3009002368125,0x85b16000000000025005a2a500d,0x40090020e205e,0x8400c01006a02d,0x2d412500f002,0xa010029066,0xa0560012de,0x42001001258066,0x300a06201002d,0x90023e41a5,0x8187f00000000000010012583e6,0xc01202903f,0xc3e4001029,0xa36000102d,0x403ba00000000000012500660a1,0x2d4001062001,0x85b16000000000025005a2a500f,0x92d40a5001,0x90020e202e,0x40073600a2001],
 #[0x31d9100000000000053603231a5,0xc01002d062,0xe0620012a3,0x4734300429d8000000000000a3e8001029,0x25c001059002,0x10012603a3,0x25c00f002125,0x1116c0013bea000000000000c010029062,0x10012d42a5,0x1001258368,0x33107000000000000c3663a3125,0x9002360121,0x2d4001012029,0x92d40a7001,0xc06202d00e,0x100135c0a5]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows5 : Rows := #[
 #[0xc05a001062125,0xa01202905a03d,0x90020de3231a5,0x10013602a31a5,0x12500660a1001,0xa00e02905a02d,0xa00e0660a102d,0xc06205600103d,0x10012e03a3065]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17rows6 : Rows := #[]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit5 := atlasRow g17frame 5 g17rows5 g17rows6 0 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check5x0 : Span g17audit5 0 9 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done5 : Region g17frame 5 9 g17rows5 :=
  atlas_sound g17proper g17frame g17vframe 5 9 0 g17rows5 g17rows6 g17rot (by intro j hj; omega) g17check5x0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit4 := atlasRow g17frame 4 g17rows4 g17rows5 9 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x0 : Span g17audit4 0 12 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x12 : Span g17audit4 12 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x24 : Span g17audit4 24 36 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x36 : Span g17audit4 36 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x48 : Span g17audit4 48 60 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x60 : Span g17audit4 60 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x72 : Span g17audit4 72 84 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check4x84 : Span g17audit4 84 88 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done4 : Region g17frame 4 88 g17rows4 :=
  atlas_sound g17proper g17frame g17vframe 4 88 9 g17rows4 g17rows5 g17rot g17done5 (join_span (join_span (join_span g17check4x0 g17check4x12) (join_span g17check4x24 g17check4x36)) (join_span (join_span g17check4x48 g17check4x60) (join_span g17check4x72 g17check4x84)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit3 := atlasRow g17frame 3 g17rows3 g17rows4 88 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x0 : Span g17audit3 0 12 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x12 : Span g17audit3 12 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x24 : Span g17audit3 24 36 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x36 : Span g17audit3 36 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x48 : Span g17audit3 48 60 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x60 : Span g17audit3 60 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x72 : Span g17audit3 72 84 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x84 : Span g17audit3 84 96 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x96 : Span g17audit3 96 108 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x108 : Span g17audit3 108 120 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x120 : Span g17audit3 120 132 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x132 : Span g17audit3 132 144 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x144 : Span g17audit3 144 156 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check3x156 : Span g17audit3 156 160 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done3 : Region g17frame 3 160 g17rows3 :=
  atlas_sound g17proper g17frame g17vframe 3 160 88 g17rows3 g17rows4 g17rot g17done4 (join_span (join_span (join_span g17check3x0 (join_span g17check3x12 g17check3x24)) (join_span (join_span g17check3x36 g17check3x48) (join_span g17check3x60 g17check3x72))) (join_span (join_span g17check3x84 (join_span g17check3x96 g17check3x108)) (join_span (join_span g17check3x120 g17check3x132) (join_span g17check3x144 g17check3x156))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit2 := atlasRow g17frame 2 g17rows2 g17rows3 160 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x0 : Span g17audit2 0 12 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x12 : Span g17audit2 12 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x24 : Span g17audit2 24 36 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x36 : Span g17audit2 36 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check2x48 : Span g17audit2 48 53 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done2 : Region g17frame 2 53 g17rows2 :=
  atlas_sound g17proper g17frame g17vframe 2 53 160 g17rows2 g17rows3 g17rot g17done3 (join_span (join_span g17check2x0 g17check2x12) (join_span g17check2x24 (join_span g17check2x36 g17check2x48)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit1 := atlasRow g17frame 1 g17rows1 g17rows2 53 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check1x0 : Span g17audit1 0 7 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done1 : Region g17frame 1 7 g17rows1 :=
  atlas_sound g17proper g17frame g17vframe 1 7 53 g17rows1 g17rows2 g17rot g17done2 g17check1x0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g17audit0 := atlasRow g17frame 0 g17rows0 g17rows1 7 g17rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17check0x0 : Span g17audit0 0 1 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17done0 : Region g17frame 0 1 g17rows0 :=
  atlas_sound g17proper g17frame g17vframe 0 1 7 g17rows0 g17rows1 g17rot g17done1 g17check0x0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g17bound : ¬Feasible g17X 11 2 (wires g17V) := by
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
def g19f0 : Basis g19X := basisFor g19X 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 (g19V.map Wire.w) 11 (assignRows [9,1,6,5,0,4,2,3,7]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f0valid : (Price.mk g19f0 0).Valid 2 (wires g19V) :=
  initial_price_any g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f1 : Basis g19X := basisFor g19X 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 (g19V.map Wire.w) 11 (assignRows [4,9,1,6,3,7,0,2,5]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f1valid : (Price.mk g19f1 0).Valid 2 (wires g19V) :=
  initial_price_any g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f2 : Basis g19X := basisFor g19X 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f (g19V.map Wire.w) 11 (assignRows [6,1,9,4,3,5,2,0,7]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f2valid : (Price.mk g19f2 0).Valid 2 (wires g19V) :=
  initial_price_any g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f3 : Basis g19X := basisFor g19X 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff (g19V.map Wire.w) 11 (assignRows [5,6,1,9,0,7,3,2,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f3valid : (Price.mk g19f3 0).Valid 2 (wires g19V) :=
  initial_price_any g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f4 : Basis g19X := basisFor g19X 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff (g19V.map Wire.w) 12 (assignRows [0,4,7,3,9,5,1,2,6]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f4valid : (Price.mk g19f4 0).Valid 2 (wires g19V) :=
  initial_price_any g17proper g17bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f5 : Basis g19X := basisFor g19X 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff (g19V.map Wire.w) 11 (assignRows [1,6,5,7,2,9,3,0,4]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f5valid : (Price.mk g19f5 0).Valid 2 (wires g19V) :=
  initial_price_any g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f6 : Basis g19X := basisFor g19X 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff (g19V.map Wire.w) 12 (assignRows [4,0,5,6,1,7,9,2,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f6valid : (Price.mk g19f6 0).Valid 2 (wires g19V) :=
  initial_price_any g17proper g17bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f7 : Basis g19X := basisFor g19X 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff (g19V.map Wire.w) 12 (assignRows [6,5,0,4,1,3,2,9,7]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f7valid : (Price.mk g19f7 0).Valid 2 (wires g19V) :=
  initial_price_any g17proper g17bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19f8 : Basis g19X := basisFor g19X 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff (g19V.map Wire.w) 11 (assignRows [7,5,6,1,2,4,0,3]) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19f8valid : (Price.mk g19f8 0).Valid 2 (wires g19V) :=
  initial_price_any g16proper g16bound (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19prices : List (Price g19X) := [⟨g19f0,0⟩,⟨g19f1,0⟩,⟨g19f2,0⟩,⟨g19f3,0⟩,⟨g19f4,0⟩,⟨g19f5,0⟩,⟨g19f6,0⟩,⟨g19f7,0⟩,⟨g19f8,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19valid : ∀ p ∈ g19prices, p.Valid 2 (wires g19V) := by
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
lemma rootValid : ∀ p ∈ rootPrices, p.Valid 2 (wires rootV) := by
  intro p hp
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
  exact advance_bin (g19valid r hr) (by simp [g19V] : g19W0 ∈ g19V) (by simp [g19V] : g19W2 ∈ g19V) true true true
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19frame : Frame g19C := ⟨12,2,rootV,rootPrices⟩
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
 #[0xf0ae300205df00b1448015080f00c18db0010937000128700b0abc00c05c4011065500117ad0000f700041f0b00a127900300270120d4701213fe00909c400e00260100b24013030001406160040e92009102400a0a6300605a300800a40050c9100707920051e2a007192b00d0ae801605e90296431785]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows1 : Rows := #[
 #[0x2c1c7602902a907203c20ac10e50680d5f02a03c103f0ebf01b03bf008193e051143f081002f03e1b2d055198b0a3148c037179c0910bb30962431785009,0x2508450360f8a02b032605c0d04054050f07815bd0b40d8604b13f9040072606308860b600620110bf40471d8303a0e0309a13430420e41030168d08f084a0b9034b01305d008310d1094218573600e,0x65005f094091509307510931e0501f13ce03d0a2d045052e094189c01f0a2b0b0169b0b2119c0b008340b203350950aa60a805a70880ad20910bb30642931785013,0x280a2e024089700c0c5e0b40d8607216d60241f0b07203c203916c80120a650390eb20160fec0a7028106404790690a380860b960000075231170,0x6d0da0094189c07307050791acc0110bf4029154402f0d7907c00d807802300af01cb0b1053608a1e7e01c1c8100b13e209605bd04618d301403610620da500a18a600f0d2400317a400000784530c6,0xb0169b00e050405918cb09a13430021b78081002f070133502706d20101b1f07506a505a0f290000000168058,0x490faa0430e1302e01dd0080c52043148a008193e0561c440310fe105604310800fb4007061a0000000019070,0x7f06a00b2119c038100509d13cc0420e4106106790bb015f030036a03e1b2d0211e33082125404e0a490a50eba04801d3097162007b16c005d1ae70990a2a0642195378056,0x500aab06a19140840cdb07b16c003a0e03051075306a0f8807b075103a1c79051143f01413da00517450160fec0a702810aa07cc0530ae201403610050f2f0770ae7044011b096423185706e,0x8e08d201f13ce015023704d05fe040072601b10760a018ab047059c0680d5f001050305b040501c1c81000185208708d701a03d800b073506b092f0171488000007581213f,0x181769023145204c14e30b11d990390eb20901bd5009028c00018520221eb103309b205604310050f2f0101b1f09716200700cb802107b90910bb30296438751003,0x407c206f14ab02d053c0731df20241f0b0350c2e07402e50a018ab05e1f0a08c0a0b02f0d790151f08043148a06a0f880021b78061067900e1d1103808120910bb3029643178500b,0x660fcb0041e3405201fe02b032602c0c7306f14ab036195f0180c650580005023145207b07510ab05460980fd508b05f90000000531270,0x7109f608f084a08f16c00621e1e08708d709c0a3702002130620da50871f340800fb407506a5075183e0ae0b1e06c05dc06c15cd05f08810964218753002,0x3d0a2d05e089609b0c5d02a16d505e1f0a02a03c102206c70600a640221eb109c0a370a10b970000000321128,0x6612e502508450660fcb034056302516bb06d1e190280a2e03b0c5508e08d20a60a3209f020e06d0da008e1f2f0490faa0500aab07f06a007f183907109f605704f70a4008e07a0b8c0426783159014,0xa60a32045052e08c139701d075e063088603f11d608c0a0b06316fc03f0ebf03311c8076056503309b20a7028104e0a4904e110306e0ae709e06980296431875127,0x340563065005f02d1ec50b5028f05c0d0402d053c05c19f007c12db04c0cf60890d7d07e009607c00d804c14e30bb015f01e0bc90b3006900d05680000000217258,0x3b0c55093075107415ba026098104b13f90350c2e067091f0ac10e508a09cd00b073500913eb085078800114ac0901bd5082125404e0a490b709d103c175b0190e730000004381158,0x9f020e0b600620890d7d0b61ed509616360120a6508507880851e3c05b04050600a64076056509605bd05b1a620aa07cc0a50eba0a5105602002130ba0d11041032b0920e290964785312006,0x58131c058000507e0096046094c04618d30310fe10530ae202706d204801d3027186b048136c0a20d7a04f087b0a902ef0910bb30964231785005,0x52151505201fe0b5028f0790b4500c0c5e0260981026103804d05fe09b0c5d01d075e0791acc04d1c5b02e01dd0840cdb05918cb09d13cc0590a6409d05650910bb3029643185700f,0x5704f709812ef0b9034b0980fd50b300690b911c100a091f0690a3803c175b03c0e0f01a03d80ba0d1100a18a601a1a35006054304a061f08d00010ad00dd08d1fef0ad10ce0b802a6032038207d0ad70910bb30964237851001]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows2 : Rows := #[
 #[0x1370b4d1611a8303706f00d0100200007815230b6007,0x1220f0a0121d730ed013d0b11bb211713ea071089e1441f8313713910091ad305c0f1401f0fc40cc18c4000000000013f1c6,0x1111e080000000145048013,0x170130e0731a0002f11fe044038d051140d12a0a6f14113ff13912a6095191e0781ee900007351861d6001,0x1c15a70c307d514e18b9000000001500b370,0xf0054e0a105df13102680cd1e7a027110f06114da0c50082006432857106e003,0x1a0b0d14b0a9f0000000719001070,0x18a002e0391619039061911f05810000000019070001,0x11f0581000000001907000f,0x13713910ad07a51030f8e081185c0a503dc0000000001003148,0x1510cec05713e10e811490aa0bdc0540d6b02b19550240c841241e0d0781ee900005736810011d6,0xa113f02e0fa50b5036f1151de413a161c0d51ad0034017616105c30e811490310715000000000113f056,0xce0c260280eb817b00b3187022c0f500050000000321170011,0x13511ee1350fe81920f79038055d07606cd18206330000002179258001,0xdc15e01110c6f0000000016058013,0xcb1fc715a005000000035140c6002,0x13b10aa1111e080000000045048009,0x10c078706c187a00000000430c600e,0x490a2d16d0cbf0f20eb70b905910f5000500000007310061f6,0xe912560e00ada0050fe113005cb000000000100e02a,0xf31d680331bd102c0f981211a10186024808606fc1311a020d40d9f0e513d80510c70000000000406e0c6,0x121d7308304f402e0fa50d009a2000007581213f011,0x8b185f0ce0c2603e069e08b0ed303e138a0cd06900490a2d0cd1e7a105006614d0b5e000000031206e16f,0x3b194b01f1a9d16707a31430a8f05f15e812f1d130d0100200007813520b6001],
 #[0xf01df204d0be714e05a20000000003007270,0x320af90cc05d8023138001808870720c700bf08c50a51d250000000493158001,0x5c0f14054169500713ab15f08c60d009a20e81149000073582100113f,0x9d06f50b1084701906520481f400ef1be80d0100200000785320b6009,0x11e1d610e30bca0ea1f9108c1a09083124109d06f5144013202d1d980540d6b0560fe103b194b044038d00000000000b61d6,0x280eb807c068307c1d3a10d0b02003196485712700f,0x2005d30d3143c17e0803013127b0d30ab00130f64176184f0e4026d07502f4068060a176064c0e41a5718400ec12305f100000000002580a1,0x11e1d611221eb300a0de916b1f1e0d0100200000785320b6013,0x1880b861250d3c0000000312002008,0xad07a51030f8e0a105df0a31fea01705eb0af19090029638751046003,0x7002a315d00040000000023128009,0xa11d610580f8f14e18b90000000003007370,0x8b185f0b30af10cf1ce90f500050000007321170013,0x10f1fdc10418ee02a02d1000000039600e016,0xd806070b5036f0ed10e60f91e8b07c0683108060b0a51d250000003481158011,0x1110c6f0000000168058007,0x1680c8801b0e800f500050000073291170015,0x1d680d51ad009d06f5121077509b1ad20781ee900000058611d6009,0x15d0004000000002112800b,0xe70abd0880c7a0000000000270010,0x461e001140bf518101800fc033d14e05a2000000000127000f,0x12901c200d1fbc05200460d30ab01820633000000021725800d,0x11f05810000000019070011,0xd1fbc0b410b20691d650e31b6802e12c918602480931c310780e7000000085430c600b],
 #[0x114fa02106020980911000000008405600a,0x11f05810000000019070007,0x6d029016500e41800dff1651f571500ae707e038c0fe18e40fe08e10c40ad607a0e180296487513001036,0xba09dd10d0b02027110f00e08d71030f8e003964187500312f,0x9258016,0x9608b413a161c0120393099113b0e619300ee18b80a51d25000000348115800d,0x1560d6f06f1f9d14e18b9000000001600e3f6,0xef0715126087509b0be30f61d720e10df20d6167c09f05bf03010c0019432785600d002,0xf417fe03c0fe708916380520046029070d11814b70af1909002196387504600b,0xcd1e7a027110f05a03070f500050000000723003170,0x1560d6f0861a891521e7a0b20ffc000000003606e00e,0x9158016,0x5c0f1405708920e80df30fe08e10911bf00a503dc01811d30000000014001148,0x15d00040000000021128015,0x18d0fc605507b20461e0008e015e0d6167c0af1909002196387504600d,0x79061c0551de417f0c6112616eb10d0b020001964875127009,0x1151de406a051b0c71074000000002113f00e,0xf7043012c05900f71a8d1250d3c11a0870000000000100602a,0x1080e06410fb1560d6f0e00ada0af0770004295376805600d,0x11f05810000000019070013,0x1521e7a1520cf00e50451105006613208430e513d80360b6e0a001ad0a012a60ec1b6e1730c230ec0b6e1480ad60c50082064298531706e001,0xc804530c81b0a174078418c0a2110d0b020031649875127013,0x1711d190660c090d41e18158048c17516250781ee900000576810051d6,0x71089e08c001f000000002113f00a],
 #[0x80b9d11b110104317a004f1ea90af07700043962578056005,0x17a005611f05810000000001070015,0x12008011770381120145917711f702b195507e038c0ff0d4702b08dc1850ad60220b7b096428537100106e,0x71089e115077d064049e0061d690a503dc000000001414800b,0xa807790a308000e4026d18206330000000027007258,0xed013d0ea08bb0b5036f0d009a2000005871213f00f,0xc8045303c12bc07c068306410fb0e619300551de410310ed0c6048a00e08d70bb17710000000008056127,0xbe02fb07a0e1815e0d7309419c70940b54096438257100502b,0x11610ca116015b0f30de11680c880f31d6817a00560c50082064321859706e013,0x461e0003e069e07919301211a1003a06bf0e10df20c50082004216853706e00d,0x16c038b015018014e05a20000000001270011,0x11b110111b01920d41e180d40d9f1720fd500307bb0c50082006491285706e005,0x620e3f0621ca608d0557000000136400a010,0x9f05bf000000006100d02c,0x41000d11f05810000000009070005,0x16f0fe816f1fd906d029018a002e164010a0364287519001014,0x11b01921790f8414e05a20000000001005270,0x1111e080000000145048011,0xab093d0b60a280eb0f281091f281110c6f0000000016058001,0x2d06c20f704300d009a2034017600008735120061c5,0x10c0787001080e013127b1820633000000021725800f,0xb00a1d0040ae60500ae60db0ae60000000005046002,0x15d00040000000021128013,0xa619860100ae60a60fe304b02950f1031a000000032100203e],
 #[0x12c059015d000400000000010061ae,0x520046099113b0e6193001c15a70af0770000429375805600b,0x1590050000000041300214e,0x6410fb0c903fa07b0388000000001612700e,0x1b0e800cf1ce917b00b300b1b280cf036000b081405a1b1a0f20eb705a030708a0d4100000000021700a1,0xc01ce20c00adf0650b6602005d318206330000002197258015,0x116015b0770f4d14e05a20000000001270015,0x2505a50dd05a909e0252000000001415800c,0xd51ad00f6058b0d009a2000007581213f009,0x4e052c1500ae707e038c1120d6e0f5000510b05aa0000007391001170,0x1c15a7089163803302c108b0ed30b3116818602480c50082006432185706e00b,0x13e026f03f0986000000013213f002,0x15912620041ae61630fed09f05bf000000006100205e,0xf31d680140e4900000000430c6014,0x5d0ae60100ae605d1ae60000000000127002,0x890f30106116114e18b90000000001370013,0x8518941111e080000000045048005,0x14b0a9f08206090000000139002016,0x3e138a079061c00b08140f50005000000732117000b,0x12919480b40a3b09616f108304f413a0c520331bd10780e7000000084530c6011,0x11713ea0691d6502e12c90f417fe03c0fe704c08b50a503dc000000000114800d,0x41ae61110c6f0ab093d00000001680020de,0x12c059010d0b0216d0cbf0c6048a0c61b4103196428750061ad,0x1900ae606e0ae606e1ae6000000000006e002],
 #[0x6c056608c001f115077d08606fc0e900620780e7000000815340c6009,0x671f120d806070b5036f1070e020ea1f9102c10140781ee900000576811d600f,0x10418ee10407640141ec20de02b70140e4917a00561000b8517c06bd01e005b01e158d07d0b071850ad6169060e0642938571014029,0x116015b01c0fc116c038b0461e0008916381561aec0f01df211b01920a105df0b80a69000000000504606e,0xc00adf12919480670d0f10c078700d1fbc1460d5b0a807791710b16176064c1511ae917009e71350fe800000000000c6256,0x1241e0d15f08c61830a261240d9415f1f2301a0b0d13005cb13015bc11a08701540fa31420694142182d0129643785001002,0x1711d191710b160080b9d068060a0be02fb18206330000000127005258,0x11610ca14009380e201ab0000000389056014,0x1900ae611f058118a002e00000000190020f6,0x1110c6f000000016805800b,0x12e0321099018a0f9055118d0fc60f417fe0c21fb812703580ad07a511d187d0230cd80000000002046147,0x10f0feb0620e3f09e02520b7080815702571021d7d0e01af812b05b20fa0ad60d910bd096241875300a029,0x16c12fa16c038b02c10140ce0c260280eb802c0f980c50082006432185706e00f,0x74140e03401761271c920c6048a18904120a51d2500000034810061de,0x14d0b5e10b05aa17801a616003e116a043b16e0e1d0f500050000000253170001,0xa6198600000002310021c7,0x1331e0816b08c118c0a211330d8f16b1f1e153068f153182818b007d0220b7b0316427859013002,0x1910a0307502f416608a900000000120062e0,0x11303d706902400d8060709608b402505a50001d68074140e14401320c1085b149165705713e10320af90731a00000000000015825d,0x10e000d18e0f2d0161f680471d5014e05a20000000053270001,0xb311680e6193003c0fe710d0b02003196487512700b,0x240c8413005cb0050fe10000000061001058,0x2113f014,0x50fe11100f180000000136002010],
 #[0xc115221611a830c21fb800e17a409200720a503dc0000000000148009,0x14e18b914e05a218206330781ee90f500050a51d250a503dc0d009a215d000410d0b020780e700d0100211f05810c500821110c6f0af07701111e080af19090296431785001001,0x1340d3709c0b8b16608a909c1a010b90591097032405e0f7505e110512c05900c40ad614f03710964287531006029,0x11303d700a113f1221eb312e1c5b0c8045313d03db0a51d250000034891158015,0xc01ce211303d700a113f13c0bd211e1d610d708dd1331e080781ee900000576811d6013,0x18b007d14505d7000000001901302c,0x7408bf02d06c20341e2003d16e700000000430c6006,0xc21fb800e17a40f01df20a308000421dfe0af19090021968375046007,0xdf0ac912014590ca124114e05a210e000d0000000001001270,0x1400938021060211d04ec0d2115508700010bc188f0bd15290351d8f01d08980111d8f080045b00f1d8f1191ad60af07700942617583056001,0xe01af81111e08000000001504800b,0x15d00040000000021128011,0x100ae615d000414a05ab00000000120021af,0xf9055107c1d3a16c038b0020d960af1909002196387504600f,0x14c05a60c903fa0c9127005b044006b0e2106b18f4162166b17d066b162066b1360ad610d0b020964287513127001,0x1340d370de02b715c0b850000003192006016,0xe30bca1170d1c13a0c520d0100200000785320b6011,0x14a05ab0f80b960f81b9615d00040000000312128001,0xf1031a000000002100502c,0x18101801380be003010c00d1056f15b15ca0451c6f009426857300d02b,0x17a005614b0a9f0a20bbc01a0b0d000000000101402a,0x1271c920c6048a0d211550fb1d4e0000003862056006,0x1680c8814c05a61280d690000000009127014,0x1680c880b30af10280eb807919300b31168079061c027092216d0cbf027110f11c0f39000000000706e127],
 #[0xd708dd0d718640220b7b0a905a014700d80da1a730da0fa513f0522036429857101302b,0x175162517505ac00307bb04f1ea904f00450f1031a07a0e180964317852005002,0x490a2d16d0cbf13208430840586000000391206e006,0x770f4d0c31db601501801140bf5106042d06f08e104d0be71790f8405813d410a1c7400000000002700a1,0xb11bb200005300d50a9118d0fc605507b206300800a503dc000000000114800f,0x16f0fe80df0ac904a0adc0fd0cb204e052c0fe18e4026080512008010fa1ad603010c00429615873001056,0x1900ae607f053218b007d0000000719002076,0x13c0bd20b40a3b1070e0206c187a0b410b21460d5b06c05660660c090aa0bdc155073f02f0ada02f11fe00000000000c61d6,0x1111e080000000145048015,0xa807790c115221611a831311a0204013680780e7000000814530c6007,0x12e03210c81b0a0650b660530c5415318280af19090032698175046013,0x1510cec1511ae91800dff04a0adc1010c4c18206331920f790000000127001258,0x60052018f07c90000000000170010,0x671f120670d0f0020d9617e080318206330000000217258011,0x9c0b8b0b717f90ae0e620000001632006010,0x13d03db04c1244108060b00600830ee18b80dd05a90631d6c1491657081007518904120090136092185f0ac02d00a4005c00c17e900000000121580a1,0x713ab0070a0811a08701250d3c0000000321001038,0x17703810fd1e2d16500e40ab093d08f0a19039428751600100e,0xff0d47026080502617f614a05ab0a706870396487512001006,0x650b6605219cf0020d96001080e052004600114fa0a308000080b9d0a31fea12d005e0000000058046056]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows3 : Rows := #[
 #[0x4f16350010b000a61e5c00000000000c614700d,0x2013d000000005804605600d,0x2013d000000005804605600f,0xba0575000000009206e005002,0x100204e0cd,0x6001058001,0x8817e50b3097f0cc170b0d409af00000000011580a100d,0x731fd2000000000000103813d,0x2013d0000000058046056005,0x660b3d00a09a60700d6d08817e5000001d07804d10281db90a517d704e07270261f4b00000000000b6156121,0x1213c000000000030b6046013,0x81045700000000021700a1009,0x2608f103f126f0d419ac00000000871480a1001,0x5a15ce04000c209e12b900000000001d6257011,0x600a27000000000805600312f,0x8b0a5c0800a5c08e1ad5000000000004600103f,0x100203e1ad,0x741a5c0800a5c0761ad5000000000004600102f,0x530019000001d003148a00000000000b615600b,0x4c1bea0290ba70621487000000000000a2de121,0xc6014031,0xca052400000000002700a100f,0x5c119f000000000037000102d,0x761ad5000000000004600302a],
 #[0x3d07d806d07600000000000001158001,0x20b600902c,0x8a0ad500000000790010020f6,0x81045700000000001700a1013,0x9d072f000000000504606e011,0xc209000000000000056001046,0x711400000000000014029056,0xd00a4704e159700304e1000000000013f0011c6,0x8f025908f10560bf0af30290ba700000000002580a1013,0x5f0101020004d000000000405600100a,0x310eb10311e380d50b7408d06ac098004a098157c0b50af6000642875900106e001,0x9f08f50000000000046147001,0x481251000000000000105825d,0xcd022f000000000015825d00c,0xae1be90000000002001056006,0xc7025f000000000706e127007,0xa003900c7025f000000000006e12700f,0x491a0c000000000004600b02a,0x960fe80a80997000000000000e016029,0x311e38000000000000106e0c6,0x1c033f000000000406e0c600f,0x251c5f0671c9200000000000c60061c5,0x120713000000000113f056011,0x42166d0ce01a900000000000c60011d6],
 #[0x4502460720d6c01b05a10009628754001046001,0x120713000000000013f056001,0x77125e0a609ab000000000015800125d,0x1c13b8000000000606e1d600b,0x12071300000000010061c5056,0x8b0a5c0741a5c0581ad50000000000046001047,0x4d1b6d04d0b6d08a0ad5000000000006e00106f,0xa41fd200000000000b600702a,0xd60c3b000000000025800102d,0x1070001035,0x101feb000000000006e00d02b,0xd00a470251c5f00000000000c613f001,0x91158606010e1000000000004612700b,0x100625e0a1,0x1e0fca000000000206e16f00f,0x113f00203d,0x4a125100000000000031d60a2,0x2f16080000000000070005029,0x8e0ad5000000000005600302a,0x7c13f7000000000004600502b,0x501165025033800000000000b61d6001,0x1b05a1000000000000902b03e,0x9d169e000000000805606e009,0x520b3601607f00000000000370001029],
 #[0xc81063000000000013f00d02b,0x1e0fca000000000206e0061f5,0xb406bc0000000000001046056,0x200203e003,0xa19ba027033802d18bc0650cc40d419ac00000000321480a100b,0xca05240000000000007270121,0x1056170,0x7c13f70000000542046005002,0x1046002045,0x1c033f000000000406e0c6001,0x6416d6002013d000000000804605600b,0x6e022b000000000004601302b,0x140b4302503380aa09f500000000000010b61d6,0x6010e1000000000504612700d,0xc009eb08708540c60c1b056069307d0ec8071137f0d10db90670a220aa09f508918e000000000000b61d60a1,0x1419970a61e5c00000000000010c6147,0xca18cc0000000000007370121,0x15800b033,0x8104570000000002003170121,0x190d58000000000012700106e,0x14199700304e1000000000000113f1c6,0x1127002045,0x4702230000000008006029056,0xa40975000000000013f001037],
 #[0x170010031,0x181ad5000000000006e00702a,0xb406bc000000000600a02900e,0x7811850010b0003c1087036048f0d419ac00000000321480a100d,0x6010e10000000005046127009,0x2013d0000000058046056013,0xcf079c0d301800ce01a900000000000c60051d6,0xc50995099128609e00b600000000000c625600f,0xf129000f008d0290ba702a0b2a0000000000005258121,0xa219a20271ec70a609ab000000000015825d011,0x13f00e02a,0xe13770000000000127001056,0xc1ada0ce01a900000000000c61d6009,0xc90e740000000029001036014,0x106e002045,0xca0524000000000000a2f6121,0x151b850000000000128009029,0x880e6e00304e1000000000013f1c6009,0x5b1528000000000015800102d,0x5008950901d600a61e5c00000000000c6001147,0xd20e8f0a61e5c00000000000c60061cd,0x62e0121,0xa90acb0000000000258001029,0xca052400000000002700a1013],
 #[0x9e00b60ce01a90a61e5c0251c5f01213c001c033f00000008350010010c6,0xc7025f000000000706e127009,0xc103130441f6404400f40009648752001036001,0x7f1e10000000000012700e029,0x600a27000000000805612700f,0x8406910000000000014029036,0x610e0c000000000700103606e,0x79002076003,0x7c0d3d0000000000056001036,0xa517d70b6097101a16fd0d409af00000000021580a1007,0x2f060802f16080000000009002016029,0x5317f607d1ac40251c5f00000000000c613f011,0x6c0c12000000000006e006029,0x541f170000000000058009029,0x1c033f000000000406e0c6009,0x6e119a000000000005600106e,0x270010029,0xaf134809d169e000000000005606e011,0x81045700000000001700a1001,0x1e0fca000000000206e16f00d,0x5615ef0251c5f00000000000c613f009,0xa1054c0b406bc000000000000a010029,0xc21a8a000000000004600d02b,0xbb0fed03a087e094051809708870b8044a096432187500100e029],
 #[0x17000f02b,0xb20c5f00000000000011580a1,0x690af206f007903b04810d419ac00000000321480a1007,0x7a1a1a00000000611d601102a,0x4400f4000000000500502b046,0x7a0fb604a003f00000000140c6001002,0x530019037153e0a609ab000000000015825d00d,0xc90e74000000000000602906e,0x970887000000000005600a029,0x9f08f50000000002046147011,0x1046158,0x430c600d002,0x2318b4000000000600602900e,0x4f04cd071137f025033800000000000b61d6009,0x15800c031,0x100205e001,0x101feb000000000006e001056,0x9d072f000000000504606e003,0x9305d0000000000101402a065,0x2013d0000000058046056007,0x571a6302d08cc08c0c930cc170b07b0c3103c03f701a16fd0321a9a06f1ee709c0c3100000000001580a104d,0x304e10a61e5c01213c009f08f506010e10d419ac0000000000001001148,0x200203e13d,0xac042f07f1e1007f08e309643218750010060a1],
 #[0x1d1ced09e00b600000000000c6007256,0xd50b74000000000001302b067,0x21076f0ce01a902b015300000000000010c61d6,0x9a043c000000000000100e02a,0x6b1cd70651b400b3097f00d11b707e0ea5036166b0b609710061d0e03b115e00b171000000000001580a105d,0x9f08f50000000002046003147,0xb20c5f02318b40000000003006010029,0x2013d09f12320600a2709d169e0000429578001001056,0x3a19830000000005046002055,0x4f04cd07804d1003148a00000000000b6156009,0xc3019c000000000006e00e029,0xc7025f000000000706e127011,0x5a15ce0351faf0ce01a900000000000c61d6011,0x120713000000000113f05600f,0x9a043c000000000105800106d,0x2308b7000000000200600c031,0xbd162e09d072f000000000004606e001,0x410ad6000000000700602916e,0xad1ad5000000000000312f0a2,0x5106f606010e10000000000046127001,0x491a0c000000000004600104f,0xa716d505f15290431eef03e1041000008743104600104d,0x502b258,0x6a08d30000000000158001029],
 #[0xbe076508f105609e00b600000000000c6256013,0x6914e50a609ab000000000000315825d,0x9f12320000000002056003157,0xca18cc000000000000b370121,0x950ad50000000000001036002,0x9d169e09d072f01c13b801e0fca0c7025f01c033f000064287500100106e,0x600a2700000000080560061ad,0xb600a029,0x600a270000000008056127013,0x6d0760000000000612700100e,0x960fe800000000000013700a1,0x611d600206d,0x77125e003148a00000000000b6156001,0x1e0fca000000000206e16f009,0x1e0fca000000000206e16f011,0x81045700000000021700a100b,0x304e10251c5f0120713000000758200100113f,0x451e9b000000000000d02b06e,0x431eef06d10a90000000002046001006,0x82173604015330851fd00290ba700000000002580a100b,0x1c033f000000000406e0c6005,0x1213c000000000030b604600d,0xc209000000000084056009002,0x310eb100000000001d6013033],
 #[0x460d6902c02910a609ab000000000015825d00f,0xa90acb06a08d301607f0004295387100e029001,0x98157c000000000001302b04e,0x1046002035,0x300cb5000000000104800d029,0xcd022f07e0ea507b0c3100000000001580a100a,0x390de50610e0c0000000002006016031,0x1056270,0x580ad5000000000005600d02a,0x101feb000000003606e00d002,0xbb0fed0000000000056014029,0xa219a20870854025033800000000000b61d6011,0x1d1ced0290ba7013178d0000000000007258121,0x1c13b8000000000006e0011d6,0x6010e10000000005046127011,0x270010031,0x1213c000000000030010b6046,0x48003f00000000000c6009032,0x461bbd0c61e8b0251c5f00000000000c613f00f,0x1058001045,0x4d0b6d02e0b6d0180ad5000000000006e00102f,0x461bbd070170d00304e1000000000013f1c600f,0x13460370cc100d06500d419ac00000003281480a1011,0xc81063000000000113f00d002],
 #[0x9d169e000000000805606e003,0x100203e001,0x81045700000000020061f6121,0x1c13b8000000000606e1d6013,0x9f12320000000002056157011,0x1e0fca0c7025f08104570000000072001001170,0x2113f009002,0x730975000000000000602a1c5,0x1128001045,0x9f08f5000000000204614700f,0x581ad50000000000001046002,0xb81d900000000000046006029,0x27000f02b,0x340291000000000400105600a,0x2308b70000000000001036046,0x840691000000007200106e006,0xb00607000000000001402905f,0xa1054c00000000000012580a1,0x340291000000000500e029046,0x6010e1000000000504600312f,0x5902950a81d3f000000001400a016031,0x1e0fca000000000006e00116f,0xca052400000000002700a100b,0xc5099509b03790ce01a900000000000c61d600f],
 #[0x2c02910700d6d08c0c930d409af00000001271580a100f,0x1048001045,0xca18cc00000000003700a1001,0x240bb70bc0d300110f280000000000001170001,0x4c0cfb09e00b600000000000c625600d,0xc7025f0600a2706010e10000964875001001127,0x51c6304b1a580000000000001270001,0xa81d3f000000000900a029014,0x301a170541f170041f170000000006002010029,0x8001001058,0x5d042a00000000090011700a1,0x380b3901f00610a609ab000000000015825d013,0xca052400000000002700a100d,0x1213c000000000030b6046009,0x9d072f000000000504606e013,0xa219a200a09a6003148a00000000000b6156011,0x3e0d0409405180000000000056011029,0x491a0c0581ad508e1ad50761ad50000000005046001002,0x7309750950ad50731fd200000003120010020be,0x9d072f000000000504606e005,0x86063f0c7025f000000000006e127001,0x9f12320000000000056001157,0x38198d0c01c5b0251c5f00000000000c613f013,0x1001070],
 #[0xa80997000000000700105606e,0x1c13b8000000000606e1d6009,0x38198d06614dd00304e1000000000013f1c6013,0x68027706810740290ba700000000072580a1001,0x48003f000000001300100214e,0x2001038001,0xe1377000000000612700d002,0x9f08f500000000020460061cd,0xac042f0000000000127014029,0x5a0c42082173609e12b900000000001d625700d,0x7a1a1a00000000061d6001067,0xae0be6000000000000a029036,0x950ad50000000000006029037,0x6317ef06305a6002013d0000000000046056001,0x9f08f50000000002046147013,0xa40975000000003213f001002,0x4812510580ad500000000160010020de,0x1c13b8000000000606e0031d6,0x110f28000000000206e001006,0x311e3800000000030c6013002,0x610e0c0000000009006029014,0x90c6e09e00b600000000000c6256001,0xad0ad50950ad50ad1ad50000000000127001002,0xa517d7003148a00000000000b6156007],
 #[0x17000f033,0x4a003f00000000000c600103f,0x1213c000000000030b6046011,0x41f170000000000058005029,0xbe076509201490ce01a900000000000c61d6013,0x1f00610660b3d06b1cd70571a630d409af00000000121580a1013,0x13f00205e,0xb50af6000000000001302b03e,0xa7043704b0ae90000000009056001014,0xa316d600000000000c6001036,0x580ad5000000006800100205e,0xc80b8300000000000b6001046,0x380b390a219a20460d69053001904f04cd0281db90140b430d10db90d01723077125e050116500000000000b61561d5,0xc40bab000000000101302c06d,0xbe076505a15ce0c5099505a0c420cf079c0ab02d2021076f042166d0420d8e0090c6e00000000000c61d6255,0x8d06ac000000031901302b065,0x8a0ad50181ad50180ad5000000000006e001002,0x1f1e580370cc102c108b0010b0002703380690af202805560d20e8f0901d6003f126f00000000000c6147121,0x10060a3,0x9305d00000000009001070001,0x110f280000000009127001014,0x1e0fca000000000006e16f001,0x9d072f0ca05240000000000001001270,0x410ad60b7037b06a08d306a18d00096418573006029001],
 #[0x7900103616e,0x21076f09e12b900000000000011d6257,0x4b1a58000000000406e00100a,0x6e119a0000000089056013002,0x8a0ad50000000009001002076,0x9201490351faf09b037900c0dee035062600c1ada0d3018002b0153055018500000000000c61d60a1,0x9d169e000000000805606e00d,0x5e0f41000000000000a02906e,0xa30a2900000000010051d60a3,0x400204e14d,0x30c6002045,0x720d6c000000000800902b056,0x75019505d042a0610e0c0000000000006016029,0x1001128,0xc10313000000000000502b06e,0x73097500000000310010021c7,0x17000105e,0x120713000000000100313f056,0x79066a083066a0ad1ad5000000000012700102f,0x600205e003,0xc3019c0c3129506c0c120964321875001014029,0x470223000000000600103600e,0x6029258,0x20b6001048],
 #[0xc7025f000000000706e127013,0x1607f001614480b7037b0064285371014029001,0x80d5d000000000017000102d,0x113f013002,0x9d072f000000000504606e00f,0xc7025f000000000706e0061ad,0x330d260b7037b0000000000170001029,0x5e12ec0000000009001056014,0x42166d0220f5b09e00b600000000000c6001256,0xcf079c00f008d09e00b600000000000c6005256,0xba0575000000000006e00502b,0xba0575000000000006e001036,0x190d58000000000012701302b,0xa316d600000000430c6005002,0x8f10560820ebc099128604c0cfb04015330ab02d201d1ced00f008d0220f5b068107400000000000c6256121,0x71140000000007600106e00e,0x240bb70000000001170001065,0xca05240000000000005270121,0x8a0ad5000000000006e01302a,0x81045700000000021700a100f,0x59141f05902950390de50cb06e9000009853101402905d,0x83166a083066a0950ad50000000000127001037,0x99048909912860290ba700000000072580a100f,0xe08a4000000000012700902b],
 #[0x1036258,0x27000f033,0x9e12b909e00b6002013d0290ba70000000007001001258,0x950ad500000000020010021a7,0xbf0af3085095c062079b0851fd00621487013178d02a0b2a0130f770b908f400000000002580a105d,0x8a0ad50b00607000000000700106e002,0x1c033f000000000406e0c600b,0x7501950000000001170011029,0x151b850150b8500000000020020080a1,0xd210980d409af0061d0e0321a9a00000000120061de121,0x101402a,0xc40bab0000000000002076001,0x190d580000000009127013002,0x9f08f5000000000204614700d,0x27000105e,0x170010029,0x10020760f5,0x625e2df,0x1705e0020004d0000000000001258001]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows4 : Rows := #[
 #[0xa0ca000000000000b6156121009,0xe1c0500000000000c614712100b,0x58001001046056,0x211f61000000000000100113f1c6,0x100200c029045,0x137000102d,0x151dbb00000000000061ce12105d,0x106e00a029,0x917000102d001,0x220d3900000000000c61d6255001,0x14162c00000000000b615612100f,0x151dbb00000000001480a105d001,0xc61d60a100b,0x151dbb00000000001480a105d00f,0x127001046001,0xd1000000000000c60052561a1,0x6e001046001,0x3062e0000000000001170001029,0x100100113f056,0x500ca000000000000325812105d,0x21011000807cd00000000000010b61561d5,0x10020080a1035,0x700e02900106e,0x700125800102d],
 #[0x106e0010020b5,0x12700106e001,0x709b30000000000003148121065,0x1046001036,0x400100106e0c6,0x31d62571a1,0x200100106e16f,0x1017c300000000001580a11d5011,0x207de00215950000000000001258001029,0x220d3900000000000010c61d6255,0x1e0be100000000000c6001256121,0x1036046001,0x1170001065,0x21011000000000000010010b61d6,0x1c0374000000000013f1c6121001,0x14043d00000000000c6147121009,0x100f5d00a1dc6001119000e1c05014043d0201e6501f04c1009101a01c037400000000000c613f1c51a1,0x500ca00000000000010012580a1,0x500ca000000000000525812105d,0x10c61d60a1,0x109f300000000001580a11d500d,0x7103a00000000001580a104d00f,0x6e00102f0bd,0x1002016029045],
 #[0x200c029055,0x106e0011d6,0x709b300000000000061ce121065,0x17000102905d,0x1a020a000000000000105600a029,0xc61d60a1009,0x151dbb00000000001480a105d00d,0xa1dc600000000000c614712100f,0x1017c302307c3021011000000000000b61561d5011,0x6016031065,0x100e029067,0x151dbb00000000001480a105d007,0x7103a00000000001580a104d009,0x7500115800102d,0x56001065002,0x1c1bd100000000001580a10011d5,0xb1b4200000000001d625712100f,0x7900602900116e,0x1e13050220d3900000000000c61d6001255,0x56001065006,0x5001036001046,0x104600106e,0x109f301309f3021011000000000000b61561d500d,0x604fb000000000000103600e029],
 #[0x10020ce14d,0x80560010020ed,0xc60010020c5,0xc02af0000000000001370001029,0xc625612100b,0x6e00102f0ed,0x903ad00000000000b6001156121,0xe015701b0157021011000000000000b61561d5009,0x201e650211f6100000000000c600113f1c5,0x4612700104d,0x37000102905d,0xa0ca00170ca0021011000000000000b61561d500b,0x100200c029035,0xc61d60a1001,0xb61d60a100b,0x709b300000000001480a1065011,0x100100205e0dd,0xa016031065,0xb01b90220d3900000000000c61d625500b,0x14800102d001,0x27000102d001,0x11700a1001,0x1046014029,0x5600106500a],
 #[0x8001001056127,0x1d0d15000000000000103606e001,0x500ca00000000002580a105d00d,0x4605600104d,0x207de0000000000046056011029,0x151dbb00000000001480a105d00b,0x1017c300000000000b6156121011,0xb60051d6121,0xd0cf700000000001d6257121001,0xc6147121007,0x6029001056,0x151dbb00000000001480a105d011,0x1014029036,0x18065f0000000000001158001029,0x4600106e001,0x709b300000000001480a1065007,0x109f300000000000b615612100d,0xc613f02900b,0x8001046001056,0x10020be1c5,0x5600103f0d5,0x6016029065,0x10560010020c5,0x211f6100000000000c613f1c5001],
 #[0xe015700000000000b6156121007,0x12700102f0bd,0x30c60010020d5,0x1580a104d00a,0x56001036001,0x170ca000000000000b61d60a1009,0x1580a105d00a,0x10060a1046,0x4600102f0bd,0x20010011700a1,0xb1b4200000000000c625612100f,0x12700102f0b5,0x106e006029,0x500ca00000000002580a105d00f,0x6e12700105d,0xf062c00000000000b61d60a100f,0x13f1c6121007,0xc613f029001,0x10010020760f5,0x4600103f0c5,0x7103a00000000001580a104d00d,0x106e00105d,0x10560010020b5,0x160cd900000000001d6257121011],
 #[0x200dec00000000001580a11d5001,0x18065f0000000000056127011029,0xc61d60a1011,0x1070001065,0x100e029065,0x10010020be1ad,0x13700a1001,0x100e029046,0x106e001056,0x40f0900000000001d625712100d,0x100e02a06d,0xc61d60a100d,0x7103a00000000001580a104d001,0x500100104606e,0x220d3900000000000010010c6256,0x2001001046147,0x3062e000000000006e12700f029,0x12580a1001,0x14043d0211f6100000000000c613f1c5009,0x500225e121,0x313f0a2001,0x313f1c61a1,0x210110000000000000100115825d,0x56001065012],
 #[0x191b25000000000000105606e001,0xa029001056,0x807cd00000000000010b61d60a1,0x160cd900b1b420040f0900b01b90000d1001e0be101e130500d0cf700000000000c61d62551a1,0x10060a106e,0x11270010020c5,0x1046006029,0xc161d000000000004606e00b029,0x700106e002065,0x1f04c1000000000013f1c6121004,0x11580a1001,0x1502ae00000000001580a105d00d,0x1046056001,0x106e001036,0x1502ae00000000001580a105d007,0x700602900106e,0x100e029036,0x500ca00000000002580a105d001,0x6e001036001,0x100e02906e,0x117000102d,0x5606e001065,0x160cd90220d3900000000000c61d6255011,0x500ca00000000002580a105d011],
 #[0x2307c300000000000b61d60a1011,0x103600106e,0x56001046001,0x1014029056,0x2076001065,0x40f090220d3900000000000c61d625500d,0x1309f300000000000b61d60a100d,0x700100106e127,0xb6001046001,0x1036014029,0x10012700a1,0x1402905d002,0x709b300000000001480a1065009,0x1580a11d500a,0x220d3900000000000010010c61d6,0xd100220d3900000000000c60051d6255,0x9101a0211f6100000000000c613f0011c5,0x2307c300f062c01309f30170ca001b015700807cd0110ee501206b800000000000b61561d5121,0xc60061cd1a1,0xc60051d6121,0x1502ae007103a00000000120010011580a1,0x106e00105f,0x25800102d001]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows5 : Rows := #[
 #[0xc60051d6255221,0xb615612114d00b,0x1258001029065,0x117000102905d,0xc61d62551a100b,0x10012580a105d,0x103600e029065,0x10011480a1065,0x10b61561d5121,0xb600115612114d,0xb615612114d009,0xc61d62551a1009,0x1370001029065,0xc61d62551a1001,0xb615612114d007,0xb61561d512100d,0xc613f1c51a100f,0xb61560011d5121,0xb61561d5121001,0xb61561d512100b,0xc613f1c51a1007,0x10011580a105d,0xc61d62551a100f,0xb61561d5121009],
 #[0x1158001029065,0x104606e00105d,0x105600a02904d,0xb61561d5121007,0xc613f1c51a1001,0x103606e00105d,0xc60011d62551a1,0xc613f1c51a1004,0xb615612114d001,0x10010b61561d5,0x10010c61d6255,0xb61561d512100f]
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19rows6 : Rows := #[]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19audit5 := atlasRow g19frame 5 g19rows5 g19rows6 0 g19rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check5x0 : Span g19audit5 0 12 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check5x12 : Span g19audit5 12 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check5x24 : Span g19audit5 24 36 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19done5 : Region g19frame 5 36 g19rows5 :=
  atlas_sound g19proper g19frame g19vframe 5 36 0 g19rows5 g19rows6 g19rot (by intro j hj; omega) (join_span g19check5x0 (join_span g19check5x12 g19check5x24))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19audit4 := atlasRow g19frame 4 g19rows4 g19rows5 36 g19rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x0 : Span g19audit4 0 12 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x12 : Span g19audit4 12 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x24 : Span g19audit4 24 36 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x36 : Span g19audit4 36 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x48 : Span g19audit4 48 60 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x60 : Span g19audit4 60 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x72 : Span g19audit4 72 84 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x84 : Span g19audit4 84 96 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x96 : Span g19audit4 96 108 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x108 : Span g19audit4 108 120 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x120 : Span g19audit4 120 132 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x132 : Span g19audit4 132 144 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x144 : Span g19audit4 144 156 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x156 : Span g19audit4 156 168 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x168 : Span g19audit4 168 180 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x180 : Span g19audit4 180 192 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x192 : Span g19audit4 192 204 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check4x204 : Span g19audit4 204 215 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19done4 : Region g19frame 4 215 g19rows4 :=
  atlas_sound g19proper g19frame g19vframe 4 215 36 g19rows4 g19rows5 g19rot g19done5 (join_span (join_span (join_span (join_span g19check4x0 g19check4x12) (join_span g19check4x24 g19check4x36)) (join_span (join_span g19check4x48 g19check4x60) (join_span g19check4x72 (join_span g19check4x84 g19check4x96)))) (join_span (join_span (join_span g19check4x108 g19check4x120) (join_span g19check4x132 g19check4x144)) (join_span (join_span g19check4x156 g19check4x168) (join_span g19check4x180 (join_span g19check4x192 g19check4x204)))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19audit3 := atlasRow g19frame 3 g19rows3 g19rows4 215 g19rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x0 : Span g19audit3 0 12 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x12 : Span g19audit3 12 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x24 : Span g19audit3 24 36 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x36 : Span g19audit3 36 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x48 : Span g19audit3 48 60 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x60 : Span g19audit3 60 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x72 : Span g19audit3 72 84 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x84 : Span g19audit3 84 96 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x96 : Span g19audit3 96 108 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x108 : Span g19audit3 108 120 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x120 : Span g19audit3 120 132 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x132 : Span g19audit3 132 144 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x144 : Span g19audit3 144 156 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x156 : Span g19audit3 156 168 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x168 : Span g19audit3 168 180 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x180 : Span g19audit3 180 192 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x192 : Span g19audit3 192 204 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x204 : Span g19audit3 204 216 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x216 : Span g19audit3 216 228 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x228 : Span g19audit3 228 240 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x240 : Span g19audit3 240 252 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x252 : Span g19audit3 252 264 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x264 : Span g19audit3 264 276 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x276 : Span g19audit3 276 288 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x288 : Span g19audit3 288 300 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x300 : Span g19audit3 300 312 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x312 : Span g19audit3 312 324 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x324 : Span g19audit3 324 336 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x336 : Span g19audit3 336 348 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x348 : Span g19audit3 348 360 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x360 : Span g19audit3 360 372 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x372 : Span g19audit3 372 384 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x384 : Span g19audit3 384 396 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check3x396 : Span g19audit3 396 403 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19done3 : Region g19frame 3 403 g19rows3 :=
  atlas_sound g19proper g19frame g19vframe 3 403 215 g19rows3 g19rows4 g19rot g19done4 (join_span (join_span (join_span (join_span (join_span g19check3x0 g19check3x12) (join_span g19check3x24 g19check3x36)) (join_span (join_span g19check3x48 g19check3x60) (join_span g19check3x72 g19check3x84))) (join_span (join_span (join_span g19check3x96 g19check3x108) (join_span g19check3x120 g19check3x132)) (join_span (join_span g19check3x144 g19check3x156) (join_span g19check3x168 (join_span g19check3x180 g19check3x192))))) (join_span (join_span (join_span (join_span g19check3x204 g19check3x216) (join_span g19check3x228 g19check3x240)) (join_span (join_span g19check3x252 g19check3x264) (join_span g19check3x276 g19check3x288))) (join_span (join_span (join_span g19check3x300 g19check3x312) (join_span g19check3x324 g19check3x336)) (join_span (join_span g19check3x348 g19check3x360) (join_span g19check3x372 (join_span g19check3x384 g19check3x396))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19audit2 := atlasRow g19frame 2 g19rows2 g19rows3 403 g19rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x0 : Span g19audit2 0 12 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x12 : Span g19audit2 12 24 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x24 : Span g19audit2 24 36 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x36 : Span g19audit2 36 48 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x48 : Span g19audit2 48 60 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x60 : Span g19audit2 60 72 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x72 : Span g19audit2 72 84 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x84 : Span g19audit2 84 96 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x96 : Span g19audit2 96 108 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x108 : Span g19audit2 108 120 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x120 : Span g19audit2 120 132 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x132 : Span g19audit2 132 144 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x144 : Span g19audit2 144 156 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x156 : Span g19audit2 156 168 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x168 : Span g19audit2 168 180 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check2x180 : Span g19audit2 180 188 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19done2 : Region g19frame 2 188 g19rows2 :=
  atlas_sound g19proper g19frame g19vframe 2 188 403 g19rows2 g19rows3 g19rot g19done3 (join_span (join_span (join_span (join_span g19check2x0 g19check2x12) (join_span g19check2x24 g19check2x36)) (join_span (join_span g19check2x48 g19check2x60) (join_span g19check2x72 g19check2x84))) (join_span (join_span (join_span g19check2x96 g19check2x108) (join_span g19check2x120 g19check2x132)) (join_span (join_span g19check2x144 g19check2x156) (join_span g19check2x168 g19check2x180))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19audit1 := atlasRow g19frame 1 g19rows1 g19rows2 188 g19rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check1x0 : Span g19audit1 0 12 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check1x12 : Span g19audit1 12 23 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19done1 : Region g19frame 1 23 g19rows1 :=
  atlas_sound g19proper g19frame g19vframe 1 23 188 g19rows1 g19rows2 g19rot g19done2 (join_span g19check1x0 g19check1x12)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def g19audit0 := atlasRow g19frame 0 g19rows0 g19rows1 23 g19rot
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19check0x0 : Span g19audit0 0 1 := check_block (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19done0 : Region g19frame 0 1 g19rows0 :=
  atlas_sound g19proper g19frame g19vframe 0 1 23 g19rows0 g19rows1 g19rot g19done1 g19check0x0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawNo : ¬Feasible g19X 12 2 (wires g19V) := by
  apply full_raw (positive_checked (v:=g19V) (by decide +kernel))
  exact cut_sound g19nd g19f6valid (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fullNo : ¬Feasible target 12 2 start.toFinset := by
  rw [show start.toFinset=wires rootV by decide +kernel]
  apply root_choices g19frame extra g19V (by decide +kernel) _ (whole g19done0) rawNo
  apply forced_except _ (by decide +kernel)
  intro w hw
  change w ∈ rootStep.out :: rootStep.rest g19V
  apply List.mem_cons_of_mem
  simpa [rootStep,Step.rest] using hw

end PEqualNP.Outside.L_meta_2956

open PEqualNP.Outside.L_meta_2956

theorem PEqualNP.Outside.L_meta_2956 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.gates.length = (15 : ℕ) → PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x4 : Fin x1.gates.length) (x5 : Fin x1.gates.length), x4 < x5 ∧ (4 : ℕ) ≤ ↑x4 ∧ ↑x4 ≤ (7 : ℕ) ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x6 : Fin x1.gates.length), (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not → x6 = x4 ∨ x6 = x5) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → ∃ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6) ≠ ([(18440827511444797640 : ℕ), (18441957826578283724 : ℕ), (18446744073709222136 : ℕ), (18446744073709485308 : ℕ), (18446744073708175304 : ℕ), (18446744073709551615 : ℕ), (18446744073709223928 : ℕ), (18446744073709551615 : ℕ)].getD (PEqualNP.MetaComplexity.tableIndex x6 / (64 : ℕ)) (0 : ℕ)).testBit (PEqualNP.MetaComplexity.tableIndex x6 % (64 : ℕ)) := by
  intro C size hf marks first
  obtain ⟨u,v,lt,_,_,hu,hv,only⟩:=marks
  apply Classical.byContradiction
  intro no
  apply fullNo
  apply startsTwo (C:=C) (by change C.gates.length≤15; omega) hf (twoCount C.gates u v (ne_of_lt lt) hu hv only) first
  intro x
  exact Classical.byContradiction (fun e=>no ⟨x,e⟩)
