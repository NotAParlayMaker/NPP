import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3188_aux
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
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
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

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

private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
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
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
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
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
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

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
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

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
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

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
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
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0

theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
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
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

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

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
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
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
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



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
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
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

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

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
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

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

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

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
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

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
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
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
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
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
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
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
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

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
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

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
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
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
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
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
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
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
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
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
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
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


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
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
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
  exact hi k t hk run

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
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 2 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 2)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 2) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (2 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 2 zero).getLsbD (asRow v i).val = (v 2).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 2 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
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

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
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
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
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
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def ImpossibleT (T : Sig) (cap tmax : Nat) (S : Finset Sig) : Prop :=
  ∀ k t,k ≤ cap → t ≤ tmax → ¬Live T k t S
theorem imp_to_impT {T cap tmax S} (h : Impossible T cap S) : ImpossibleT T cap tmax S :=
  fun k t hk _ => h k t hk
theorem rotate_excludedT {T n tmax} {ws : List Sig} (hi : ImpossibleT T n tmax ws.toFinset)
    (p : List Move) (ok : autoOK T p=true) : ImpossibleT T n tmax (ws.map (movedWord p.reverse)).toFinset:=by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p):=fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk ht h
  have run:=live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T=T:=(moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x)=x:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p))=ws.toFinset:=by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩; simpa only [inv] using hw
    · intro ha; exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk ht run
theorem enum_stepT {T : Sig} {cap tmax : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : tmax > 0 → ∀ a ∈ ws,∀ keep,neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      ImpossibleT T (cap-1) (if (childOne ws a keep).length=cap then 0 else tmax-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a≠b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleT T (cap-1) (if (childTwo ws a b d ka kb).length=cap then 0 else tmax)
        (childTwo ws a b d ka kb).toFinset) :
    ImpossibleT T cap tmax ws.toFinset:=by
  classical
  intro k t hk ht h
  generalize he : ws.toFinset=S at h
  induction h with
  | stop hp =>
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let keep:=decide (a ∈ U)
    have er:=erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset=U:=by
      rw [kept_fin,er,he]; by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup:=by
      have na : a ∉ ws.erase a:=hn.not_mem_erase
      refine List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h)),
        kept_nd keep a (ws.erase a) (hn.erase _) na⟩
    have eq : (childOne ws a keep).toFinset=insert (neg a) U:=by simp [childOne,rest]
    have sc:=(live_size tail).2
    have len : (childOne ws a keep).length ≤ cap:=by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have ht' : t ≤ if (childOne ws a keep).length=cap then 0 else tmax - 1:=by
      split_ifs with hlen
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; omega
      · omega
    exact oneStep (by omega) a am keep fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er : rest.toFinset=(ws.toFinset.erase a).erase b:=by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset=U:=by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases hja : j=a
      · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hab]
      · by_cases hjb : j=b
        · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hja]
        · by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hja,hjb]
    have rn : rest.Nodup:=(hn.erase _).erase _
    have ar : a ∉ rest:=fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest:=(hn.erase a).not_mem_erase
    have nk:=kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest:=by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))),
        kept_nd ka a _ nk ax⟩
    have eq : (childTwo ws a b d ka kb).toFinset=insert (bin d a b) U:=by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset=_; simp [ke]
    have sc:=(live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap:=by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have ht' : t ≤ if (childTwo ws a b d ka kb).length=cap then 0 else tmax:=by
      split_ifs with hlen
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; omega
      · exact ht
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
theorem closeChildT_sound {raw T pools links k tmax rest op}
    (pValid : ∀ p ∈ pools,ValidPool raw T p)
    (lValid : ∀ tag xs,xs ∈ links tag → ImpossibleT T k tmax (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op=true) :
    ImpossibleT T k tmax (choiceVal op :: rest).toFinset:=by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]; exact lValid _ _ hx
  · exact imp_to_impT (scalarPoolCut_sound (pValid _ hp) nd ok)
def childT (tmax cap len op : Nat) : Nat :=
  if len==cap then 0 else if op==2 then tmax - 1 else tmax
abbrev LinkFn:=Nat → List Sig → List (List Sig)
abbrev NodeContextT :=
  Nat × Nat × Nat × List Decor × CovPair × List BoundPool × List QuickPool × LinkFn × LinkFn × LinkFn
def ctxWireT (c : NodeContextT) (i : Nat) : Decor:=c.2.2.2.1.getD i defaultDecor
def ctxLinksT (c : NodeContextT) (ct : Nat) : LinkFn :=
  if ct==0 then c.2.2.2.2.2.2.2.1
  else if ct==1 then c.2.2.2.2.2.2.2.2.1
  else c.2.2.2.2.2.2.2.2.2
def evalMoveT (c : NodeContextT) (op : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let (cap,tmax,n,ws,cov,pools,qpools,l0,l1,l2):=c
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len > cap then true else
    let ct:=childT tmax cap len op
    let d:=ct==0
    if (restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1||ws.any (fun v => v.1==z.1) then true else
    if qpools.any (fun qp => fastCost qp (cap-1) a b op ka kb) then true else
      let rest:=(opKeep un ka kb a b ws).map Prod.fst
      let links:=if ct==0 then l0 else if ct==1 then l1 else l2
      closeChild pools (fun tag => links tag (choiceVal (movedChoice op a b)::rest)) (cap-1) rest (movedChoice op a b)
theorem evalMoveT_sound {raw T r s ws pools l0 l1 l2 cap tmax a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0 < cap) (htmax : tmax ≤ 2)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv0 : ∀ tag child, child.Nodup → ∀ xs, xs ∈ l0 tag child → ImpossibleT T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag child, child.Nodup → ∀ xs, xs ∈ l1 tag child → ImpossibleT T (cap-1) 1 (List.toFinset xs))
    (lv2 : ∀ tag child, child.Nodup → ∀ xs, xs ∈ l2 tag child → ImpossibleT T (cap-1) 2 (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMoveT (cap,tmax,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1,l2)
      op a b (movedDecor op a b) ka kb=true) :
    ImpossibleT T (cap-1)
      (childT tmax cap (moveFront ws op a b ka kb).length op)
      (moveFront ws op a b ka kb).toFinset:=by
  let z:=movedDecor op a b
  let rest:=opKeep (op==2) ka kb a b ws
  let child:=z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws:=keep_sub _ _ _ _ _ _
  have ndc : child.Nodup:=List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
  have val:=moved_full op a b
  have fr : ws.any (fun v => v.1==z.1)=false:=by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
    exact fresh ((beq_iff_eq.mp he).symm ▸ List.mem_map_of_mem hx)
  have pp : properB z.1=true:=by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))=child.length:=by
    change _=(z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk ht h
  have hsz:=(live_size h).2
  change child.toFinset.card+t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap:=by omega
  unfold evalMoveT at test
  change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
  rw [leq,if_neg (by omega)] at test
  let ct:=childT tmax cap child.length op
  have ht0 : (ct==0)=true → t=0:=by
    intro hct
    have hc0 : ct=0:=beq_iff_eq.mp hct
    change t ≤ ct at ht
    omega
  have sep:=cover_sound h rfl (pair_sep pairs) (ct==0) ht0
  let d:=ct==0
  have g : (coverage d rest).1=covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz:=rest_coverage ha hb (op==2) ka kb d ne
  have hf:=moved_faithful (faith _ ha) (faith _ hb) op
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst)=_ at sep
  change z.2=pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768)=false:=by
    rw [sep,bne_self_eq_false]
  change (if (_ != _) then true else if !properB z.1||ws.any (fun v => v.1==z.1) then true else if _ then true else _)=true at test
  rw [be,pp,fr] at test
  simp only [Bool.false_eq_true,ite_false,Bool.not_true,Bool.false_or] at test
  have nd' : (choiceVal (movedChoice op a b) :: rest.map Prod.fst).Nodup:=val ▸ ndc
  have h' : Live T k t (choiceVal (movedChoice op a b) :: rest.map Prod.fst).toFinset:=val ▸ h
  by_cases hq : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb)=true
  · obtain ⟨qp,hqp,hfc⟩:=List.any_eq_true.mp hq
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hqp
    exact scalarPoolCut_sound (pv p hp) nd' (fastCost_good ha hb hfc) k t hk h'
  · have hqf : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb)=false :=
      Bool.eq_false_iff.mpr hq
    change (if ((pools.map (summarizePool ws)).any fun qp => fastCost qp (cap-1) a b op ka kb)=true then true else _)=true at test
    rw [hqf] at test
    simp only [Bool.false_eq_true,ite_false] at test
    have hct_le : ct ≤ 2:=by
      dsimp only [ct,childT]; split_ifs <;> omega
    by_cases hct0 : ct=0
    · have hctb : (ct==0)=true:=beq_iff_eq.mpr hct0
      rw [hctb] at test; simp only [ite_true] at test
      exact closeChildT_sound pv (fun tag => lv0 tag _ nd') nd' test k t hk (hct0 ▸ ht) h'
    · have hctb0 : (ct==0)=false:=beq_eq_false_iff_ne.mpr hct0
      rw [hctb0] at test; simp only [Bool.false_eq_true,ite_false] at test
      by_cases hct1 : ct=1
      · have hctb1 : (ct==1)=true:=beq_iff_eq.mpr hct1
        rw [hctb1] at test; simp only [ite_true] at test
        exact closeChildT_sound pv (fun tag => lv1 tag _ nd') nd' test k t hk (hct1 ▸ ht) h'
      · have hctb1 : (ct==1)=false:=beq_eq_false_iff_ne.mpr hct1
        rw [hctb1] at test; simp only [Bool.false_eq_true,ite_false] at test
        have hct2 : ct=2:=by omega
        exact closeChildT_sound pv (fun tag => lv2 tag _ nd') nd' test k t hk (hct2 ▸ ht) h'
def testPairT (ctx : NodeContextT) (a b : Decor) (d : Bool) : Bool :=
  let op:=if d then 1 else 0
  let z:=movedDecor op a b
  let f:=evalMoveT ctx op a b z
  f false false&&f true false&&f false true&&f true true
def testRowT (ctx : NodeContextT) (a : Decor) (bs : List Decor) : Bool :=
  let unOk:=if ctx.2.1==0 then true else
    let z:=movedDecor 2 a a
    evalMoveT ctx 2 a a z false false&&evalMoveT ctx 2 a a z true true
  unOk&&bs.all (fun b => testPairT ctx a b false&&testPairT ctx a b true)
def testAllT (ctx : NodeContextT) : List Decor → Bool
  | [] => true
  | a :: bs => testRowT ctx a bs&&testAllT ctx bs
theorem all_unaryT {ctx} {ws : List Decor} (h : testAllT ctx ws=true) (ht : ctx.2.1 > 0) {a : Decor} (ha : a ∈ ws) (keep : Bool) :
    evalMoveT ctx 2 a a (movedDecor 2 a a) keep keep=true:=by
  have hne : (ctx.2.1==0)=false:=beq_eq_false_iff_ne.mpr (by omega)
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllT,Bool.and_eq_true,testRowT,hne,Bool.false_eq_true,ite_false] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm
theorem all_binaryT {ctx} {ws : List Decor} (h : testAllT ctx ws=true) {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (d : Bool) : testPairT ctx a b d=true∨testPairT ctx b a d=true:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllT,Bool.and_eq_true,testRowT,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm:=(List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left; cases d <;> first | exact (h.1.2 _ bm).1 | exact (h.1.2 _ bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right; cases d <;> first | exact (h.1.2 _ haTail).1 | exact (h.1.2 _ haTail).2
      · exact ih h.2 haTail hbTail
theorem testPairT_at {ctx a b d} (h : testPairT ctx a b d=true) (ka kb : Bool) :
    evalMoveT ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb=true:=by
  simp only [testPairT,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem nodeT_sound {raw T r s ws pools l0 l1 l2 cap tmax}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv0 : ∀ tag child, child.Nodup → ∀ xs, xs ∈ l0 tag child → ImpossibleT T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag child, child.Nodup → ∀ xs, xs ∈ l1 tag child → ImpossibleT T (cap-1) 1 (List.toFinset xs))
    (lv2 : ∀ tag child, child.Nodup → ∀ xs, xs ∈ l2 tag child → ImpossibleT T (cap-1) 2 (List.toFinset xs))
    (htmax : tmax ≤ 2)
    (checks : testAllT (cap,tmax,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1,l2) ws=true) :
    ImpossibleT T cap tmax (ws.map Prod.fst).toFinset:=by
  by_cases hc : cap=0
  · intro k t hk _ h
    have ke : k=0:=by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset=S at h
    have eqS : S={T}:=by cases h; rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  have hc' : 0 < cap:=by omega
  apply enum_stepT nd out
  · intro htpos v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hv
    have hf:=unary_front nd ha keep
    have hev:=evalMoveT_sound (op:=2) pairs faith nd ha ha (by simp) hc' htmax pv lv0 lv1 lv2 pro fresh (all_unaryT checks htpos ha keep)
    have hlenEq : (moveFront ws 2 a a keep keep).length=(childOne (ws.map Prod.fst) a.1 keep).length:=by
      have nd1 : (moveFront ws 2 a a keep keep).Nodup:=by
        unfold moveFront
        have sub:=keep_sub ws a a true keep keep
        exact List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
      have nd2 : (childOne (ws.map Prod.fst) a.1 keep).Nodup:=by
        unfold childOne
        have na : a.1 ∉ (ws.map Prod.fst).erase a.1:=nd.not_mem_erase
        refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd keep a.1 _ (nd.erase _) na⟩
        rw [keep_mem] at hm
        rcases hm with ⟨heq,_⟩ | hm
        · exact fresh (heq.symm ▸ List.mem_map_of_mem ha)
        · exact fresh (List.mem_of_mem_erase hm)
      rw [←List.toFinset_card_of_nodup nd1,←List.toFinset_card_of_nodup nd2,hf]
    rw [hf,hlenEq] at hev
    simpa [childT] using hev
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
    have ab : a≠b:=fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a ∈ ws) (bb : b ∈ ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPairT (cap,tmax,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1,l2) a b d=true) :
        ImpossibleT T (cap-1) (if (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length=cap then 0 else tmax)
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
      have hf:=binary_front nd aa bb ne' d ka kb
      have eq : (movedDecor (if d then 1 else 0) a b).1=bin d a.1 b.1:=by cases d <;> rfl
      have hev:=evalMoveT_sound (op:=if d then 1 else 0) pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' htmax pv lv0 lv1 lv2
        (eq ▸ pr) (eq ▸ fr) (testPairT_at test ka kb)
      have hop : ((if d then 1 else 0)==2)=false:=by cases d <;> rfl
      have hlenEq : (moveFront ws (if d then 1 else 0) a b ka kb).length =
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length:=by
        have nd1 : (moveFront ws (if d then 1 else 0) a b ka kb).Nodup:=by
          unfold moveFront
          have sub:=keep_sub ws a b ((if d then 1 else 0)==2) ka kb
          exact List.nodup_cons.mpr ⟨fun hm => (eq ▸ fr) ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
        have nd2 : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup:=by
          unfold childTwo
          let r0:=((ws.map Prod.fst).erase a.1).erase b.1
          have rn : r0.Nodup:=(nd.erase _).erase _
          have ar : a.1 ∉ r0:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ r0:=(nd.erase a.1).not_mem_erase
          have nk:=kept_nd kb b.1 r0 rn br
          have ax : a.1 ∉ kept kb b.1 r0:=by cases kb <;> simp [kept,ar,ne']
          refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd ka a.1 _ nk ax⟩
          rw [keep_mem] at hm
          rcases hm with ⟨heq,_⟩ | hm
          · exact fr (heq.symm ▸ List.mem_map_of_mem aa)
          · rw [keep_mem] at hm
            rcases hm with ⟨heq,_⟩ | hm
            · exact fr (heq.symm ▸ List.mem_map_of_mem bb)
            · exact fr (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup nd1,←List.toFinset_card_of_nodup nd2,hf]
      rw [hf,hlenEq] at hev
      simpa [childT,hop] using hev
    rcases all_binaryT checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · have hsw:=childTwo_swap (ws.map Prod.fst) nd a.1 b.1 d ka kb
      have hlenSw : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length =
          (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).length:=by
        have ndA : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup:=by
          unfold childTwo
          let rA:=((ws.map Prod.fst).erase a.1).erase b.1
          have rn : rA.Nodup:=(nd.erase a.1).erase b.1
          have ar : a.1 ∉ rA:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ rA:=(nd.erase a.1).not_mem_erase
          have nk:=kept_nd kb b.1 rA rn br
          have ax : a.1 ∉ kept kb b.1 rA:=by cases kb <;> simp [kept,ar,ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd ka a.1 _ nk ax⟩
          rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
          · rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        have ndB : (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).Nodup:=by
          unfold childTwo
          let rB:=((ws.map Prod.fst).erase b.1).erase a.1
          have rn : rB.Nodup:=(nd.erase b.1).erase a.1
          have br : b.1 ∉ rB:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have ar : a.1 ∉ rB:=(nd.erase b.1).not_mem_erase
          have nk:=kept_nd ka a.1 rB rn ar
          have bx : b.1 ∉ kept ka a.1 rB:=by cases ka <;> simp [kept,br,Ne.symm ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd kb b.1 _ nk bx⟩
          rw [bin_comm d b.1 a.1] at hm
          rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
          · rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup ndA,←List.toFinset_card_of_nodup ndB,hsw]
      rw [hsw,hlenSw]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro) (bin_comm d a.1 b.1 ▸ fresh) hh
abbrev W := BitVec 24
abbrev JGate := Bool × Nat × Nat
abbrev Code := List JGate

def raw (i : Fin 9) : W :=
  let p := ([(49,1348),(67,2083),(134,788),(268,105),(24,2706),
    (2592,27),(1088,220),(640,3296),(3328,3840)] : List (Nat × Nat)).getD i.val (0,0)
  BitVec.ofNat 24 (4096*p.1+p.2)

def base := List.ofFn raw ++ [raw 0 ||| raw 2]
def goal : W := BitVec.ofNat 24 (4095*4096)
def seed02 : Sig := inputs.getD 0 0 ||| inputs.getD 2 0
def roots := inputs ++ [seed02]

lemma inputs_spec : ∀ r : Fin 512, ∀ j : Fin 9,
    (inputs.getD j.val 0).getLsbD r.val = r.val.testBit j.val := by decide +kernel

def edges : List Nat := [3,6,12,24,17,33,66,132,264,160,320,288]
def nonedges : List Nat := [42,50,69,104,116,138,201,208,261,276,385,402]

lemma graph_spec : ∀ r : Fin 512, graph.getLsbD r.val =
    edges.any (fun e : Nat => (r.val &&& e) == e) := by
  decide +kernel

-- For each assignment choose a posted edge below it or a posted nonedge above it.
def boundaryIndex (r : Fin 512) : Nat :=
  if graph.getLsbD r.val then 12 + edges.findIdx (fun e => (e &&& r.val) == e)
  else nonedges.findIdx (fun m => (r.val &&& m) == r.val)

def compatible (positive small full : Bool) : Prop :=
  if positive then small = true → full = true else full = true → small = true

def Bounds (v : W) (w : Sig) : Prop := ∀ r : Fin 512,
  compatible (graph.getLsbD r.val) (v.getLsbD (boundaryIndex r)) (w.getLsbD r.val)

def op {n : Nat} (d : Bool) (a b : BitVec n) := if d then a ||| b else a &&& b
def boolOp (d a b : Bool) := if d then a || b else a && b

lemma bit_op {n} (d) (a b : BitVec n) (i : Nat) :
    (op d a b).getLsbD i = boolOp d (a.getLsbD i) (b.getLsbD i) := by
  cases d <;> simp [op,boolOp]

lemma compatible_op {p a b x y : Bool} (ha : compatible p a x) (hb : compatible p b y) (d : Bool) :
    compatible p (boolOp d a b) (boolOp d x y) := by
  cases p <;> cases d <;> simp [compatible,boolOp] at * <;> tauto

lemma bounds_op {a b x y} (ha : Bounds a x) (hb : Bounds b y) (d : Bool) :
    Bounds (op d a b) (op d x y) := by
  intro r
  rw [bit_op,bit_op]
  exact compatible_op (ha r) (hb r) d

set_option maxRecDepth 10000 in
lemma bounds_inputs : List.Forall₂ Bounds base roots := by
  apply List.forall₂_of_length_eq_of_get (by decide)
  intro i h h'
  have ok : ∀ j : Fin 10, Bounds (base.getD j 0) (roots.getD j 0) := by
    unfold Bounds compatible
    decide +kernel
  simpa only [List.getD_eq_getElem _ _ h,List.getD_eq_getElem _ _ h',List.get_eq_getElem] using
    ok ⟨i,h⟩

lemma bounds_goal {x : Sig} (h : Bounds goal x) : x = graph := by
  have ok : ∀ r : Fin 512, goal.getLsbD (boundaryIndex r) = graph.getLsbD r.val := by decide +kernel
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 512 := ⟨i,hi⟩
  have hv := h r
  rw [ok r] at hv
  unfold compatible at hv
  change x.getLsbD r.val = graph.getLsbD r.val
  cases he : graph.getLsbD r.val <;> cases hx : x.getLsbD r.val <;> simp_all

def ordered : Nat → Code → Prop
  | _, [] => True
  | n, (_,a,b)::t => a < n ∧ b < n ∧ ordered (n+1) t

def gateVal (g : JGate) (w : List Sig) :=
  op g.1 (w.getD g.2.1 0) (w.getD g.2.2 0)

def run : Code → List Sig → List Sig
  | [], w => w
  | g::gs, w => run gs (w ++ [gateVal g w])

def runBool : Code → List Bool → List Bool
  | [], w => w
  | g::gs, w => runBool gs (w ++ [boolOp g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)])

lemma read_bit (r : Fin 512) (w : List Sig) (i : Nat) :
    (w.map (fun v => v.getLsbD r.val)).getD i false = (w.getD i 0).getLsbD r.val := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> simp

lemma run_bits (r : Fin 512) (c : Code) (w : List Sig) :
    (run c w).map (fun v => v.getLsbD r.val) = runBool c (w.map (fun v => v.getLsbD r.val)) := by
  induction c generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run,ih]
    simp only [runBool,List.map_append,List.map_cons,List.map_nil,gateVal,bit_op,read_bit]

def legal (s vs : List W) := ∀ i : Fin vs.length,
  let u := s ++ vs.take i.val
  vs.get i ∉ u ∧ vs.get i ≠ 0 ∧ vs.get i ≠ -1 ∧
    ∃ a ∈ u, ∃ b ∈ u, vs.get i = a &&& b ∨ vs.get i = a ||| b

lemma pick_wire {s : List W} {w : List Sig} (hw : List.Forall₂ Bounds s w)
    {a : W} (ha : a ∈ s) : ∃ i < w.length, Bounds a (w.getD i 0) := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem ha
  have hi' : i < w.length := hw.length_eq ▸ hi
  exact ⟨i,hi', by simpa only [List.getD_eq_getElem _ _ hi', List.get_eq_getElem] using hw.get hi hi'⟩

lemma compile {s w vs} (hw : List.Forall₂ Bounds s w) (hl : legal s vs) (ht : goal ∈ vs) :
    ∃ c : Code, ordered w.length c ∧ c.length ≤ vs.length ∧ (run c w).getLastD 0 = graph := by
  induction vs generalizing s w with
  | nil => simp at ht
  | cons v vs ih =>
    have step := hl ⟨0,by simp⟩
    simp only [List.take_zero,List.append_nil] at step
    obtain ⟨_,_,_,a,ha,b,hb,eqv⟩ := step
    obtain ⟨i,hi,hai⟩ := pick_wire hw ha
    obtain ⟨j,hj,hbj⟩ := pick_wire hw hb
    obtain ⟨d,hd⟩ : ∃ d : Bool, v = op d a b := eqv.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
    let g : JGate := (d,i,j)
    have hbound : Bounds v (gateVal g w) := hd ▸ bounds_op hai hbj d
    by_cases hv : v = goal
    · refine ⟨[g],⟨hi,hj,trivial⟩,by simp,?_⟩
      simpa [run] using bounds_goal (hv ▸ hbound)
    · have tailLegal : legal (s ++ [v]) vs := fun i => by simpa [List.append_assoc] using hl i.succ
      obtain ⟨c,ho,hc,hg⟩ := ih (List.rel_append hw (.cons hbound .nil)) tailLegal
        ((List.mem_cons.mp ht).resolve_left (Ne.symm hv))
      exact ⟨g::c,⟨hi,hj,by simpa using ho⟩,by simpa using hc,hg⟩

def Produces (c : Code) := ordered roots.length c ∧ (run c roots).getLastD 0 = graph
def Trimmed (c : Code) := Produces c ∧ ∀ p : Code, Produces p → c.length ≤ p.length

lemma extractCode {vs : List W} (ht : goal ∈ base ++ vs) (hl : legal base vs) :
    ∃ c : Code, Trimmed c ∧ c.length ≤ vs.length := by
  classical
  have absent : goal ∉ base := by decide
  obtain ⟨p,ho,hp,hg⟩ := compile bounds_inputs hl ((List.mem_append.mp ht).resolve_left absent)
  let P := fun n => ∃ c : Code, c.length = n ∧ Produces c
  have ex : ∃ n, P n := ⟨_,p,rfl,ho,hg⟩
  obtain ⟨c,eqc,ok⟩ := Nat.find_spec ex
  exact ⟨c,⟨ok,fun q hq => eqc ▸ Nat.find_min' ex ⟨q,rfl,hq⟩⟩,
    eqc ▸ (Nat.find_min' ex ⟨p,rfl,ho,hg⟩).trans hp⟩

def binaryWitness (w : List Sig) (z : Sig) : Prop :=
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma j_bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ binaryWitness w (bin d a b) := by
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
  exact Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩

lemma positivePull {w : List Sig} {z : Sig} {k S} (h : Live T k 0 S)
    (hz : represented w z ∨ binaryWitness w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' S', k' ≤ k + 1 ∧ Live T k' 0 S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨d, a, b, ha, hb, pa, pb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live T k 0 (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, Nat.le_refl _, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha


lemma live_of_code {T : Sig} (hp : proper T) (c : Code) (w : List Sig)
    (ht : T ∈ run c w) : ∃ k S, k ≤ c.length ∧ Live T k 0 S ∧ ∀ v ∈ S, v ∈ w := by
  induction c generalizing w with
  | nil => exact ⟨0,{T},by simp,Live.stop hp,by simpa [run] using ht⟩
  | cons g cs ih =>
    obtain ⟨k,S,hk,hl,hs⟩ := ih (w ++ [gateVal g w]) ht
    obtain ⟨j,U,hj,hu,hU⟩ := positivePull hl
      (j_bin_rep g.1 (get_rep w g.2.1) (get_rep w g.2.2)) hs
    exact ⟨j,U,by simp; omega,hu,hU⟩




def j_absentRow (i : Fin 9) : Row := Fin.ofNat 512 ([20,1,9,4,1,1,2,4,8].getD i.val 0)
def j_presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((j_absentRow i).val ||| (1 <<< i.val))


theorem j_seed_witness : ∀ i : Fin 9,
    (bit (j_absentRow i) graph != bit (j_presentRow i) graph) &&
    ((inputs++[seed02]).all fun w => w == inputs.getD i.val zero ||
      bit (j_absentRow i) w == bit (j_presentRow i) w) = true := by decide +kernel

theorem j_all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed02]) :
    S=inputs.toFinset ∨ S=(inputs++[seed02]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := j_seed_witness i
    simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (j_absentRow i) (j_presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed02 ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed


lemma roots_of_code {c : Code} (ok : Produces c) :
    ∃ k ≤ c.length, Live graph k 0 inputs.toFinset ∨ Live graph k 0 roots.toFinset := by
  have valid : proper graph := by unfold proper; decide +kernel
  have member : graph ∈ run c roots := by
    have out := ok.2
    cases h : run c roots with
    | nil => simp [h] at out; exact (valid.1 out.symm).elim
    | cons a l => rw [h] at out; rw [←out,List.getLastD_cons]; exact List.getLastD_mem_cons
  obtain ⟨k,S,hk,hl,hs⟩ := live_of_code valid c roots member
  rcases j_all_roots hl hs with rfl | rfl
  · exact ⟨k,hk,Or.inl hl⟩
  · exact ⟨k,hk,Or.inr hl⟩

lemma extractLive {vs : List W} (ht : goal ∈ base ++ vs) (hl : legal base vs) :
    ∃ k ≤ vs.length, Live graph k 0 inputs.toFinset ∨ Live graph k 0 roots.toFinset := by
  obtain ⟨c,hc,hn⟩ := extractCode ht hl
  obtain ⟨k,hk,h⟩ := roots_of_code hc.1
  exact ⟨k,hk.trans hn,h⟩

def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def samples : Array (Bits × Bits) := #[(0xfff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff,0x544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff,0x823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000,0x314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000,0x69069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069),(0xfff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000,0xa92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000,0x1b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000,0xdc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00)]
def jPop (x : Nat) :=
  let x := x - ((x >>> 1) &&& 0x5555555555555555)
  let x := (x &&& 0x3333333333333333) + ((x >>> 2) &&& 0x3333333333333333)
  let x := (x + (x >>> 4)) &&& 0x0f0f0f0f0f0f0f0f
  ((x * 0x0101010101010101) >>> 56) &&& 127

def jLookup (nb sz sw rw iw vw : Nat) (s m r v : Nat → Nat) (tag : Nat) : Option (Nat × Nat) :=
  let idx := (tag/nb+packedAt s ((tag % nb)*sw) sw)%sz
  let b := idx/64
  let o := idx % 64
  let x := packedAt m (b*64) 64
  let n := packedAt r (b*rw) rw + jPop (x &&& ((1 <<< o)-1))
  if x.testBit o then some (n,0) else
    let w := packedAt v ((idx-n)*vw) vw
    some (w &&& ((1 <<< iw)-1),w >>> iw)


inductive MonoRun {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : MonoRun goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → MonoRun goal s xs → MonoRun goal s zs
  | two {s a b rest} (op ka kb : Bool) :
      MonoRun goal s (combine op a b :: kept ka a (kept kb b rest)) →
      MonoRun goal (s+1) (a::b::rest)


def Improves {R} (T a b : Wire R) : Prop := ∀ r, a r = T r → b r = T r

theorem improve_combine {R} {T a b x y : Wire R} (op : Bool)
    (ha : Improves T a x) (hb : Improves T b y) :
    Improves T (combine op a b) (combine op x y) := by
  intro r
  have H := ha r
  have K := hb r
  cases op <;> cases u : T r <;> cases v : a r <;> cases w : b r <;>
    simp_all [combine]

theorem kept_rel {R} {T : Wire R} {a b : Wire R} {xs ys : List (Wire R)} (keep : Bool)
    (ha : Improves T a b) (hs : List.Forall₂ (Improves T) xs ys) :
    List.Forall₂ (Improves T) (kept keep a xs) (kept keep b ys) := by
  cases keep
  · exact hs
  · exact .cons ha hs

theorem improve_run {R} {goal : Wire R} {k xs} (h : MonoRun goal k xs)
    {ys} (rel : List.Forall₂ (Improves goal) xs ys) : MonoRun goal k ys := by
  induction h generalizing ys with
  | stop =>
    cases rel with
    | cons head tail =>
      cases tail
      have same := funext (fun r => head r rfl)
      rw [same]
      exact .stop
  | perm perm _ ih =>
    obtain ⟨zs, aligned, permuted⟩ := List.perm_comp_forall₂ perm rel
    exact .perm permuted (ih aligned)
  | @two s a b rest op ka kb _ ih =>
    cases rel with
    | cons ha hr =>
      cases hr with
      | cons hb ht =>
        exact .two op ka kb (ih (.cons (improve_combine op ha hb)
          (kept_rel ka ha (kept_rel kb hb ht))))

theorem monoErase {R} {g : Wire R} {k xs} (h : MonoRun g k xs) : Run g k xs := by
  induction h with
  | stop => exact .stop
  | perm p _ ih => exact .perm p ih
  | two op ka kb _ ih => exact .two op ka kb ih

theorem listMono {T : Sig} {k u S} (h : Live T k u S) (no : u=0) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : MonoRun (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact MonoRun.perm (eq.map _) MonoRun.stop
  | unary => omega
  | @binary k u U a b d ha hb hab fresh _ ih =>
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
    have progress := ih no (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change MonoRun _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact MonoRun.perm (perm.map _) (MonoRun.two d ka kb progress)
theorem monoRestrict {R S : Type} (rows : S → R) {goal s ws} (h : MonoRun goal s ws) :
    MonoRun (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact MonoRun.stop
  | perm p _ ih => exact MonoRun.perm (p.map _) ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact MonoRun.two false ka kb ih
    · exact MonoRun.two true ka kb ih

def mWitness (p n : Sig) (r t : Row) : Bool :=
  let b := bit r graph
  bit t graph == b && bit t (if b then p else n) &&
    (if b then (t.val &&& r.val) == t.val else (r.val &&& t.val) == r.val)

def mGeometry (d p n : Sig) (rs : List Row) : Prop :=
  ∀ r : Row, bit r d = true → rs.any (mWitness p n r) = true

theorem mWitnessInput {p n r t} (h : mWitness p n r t = true) {a : Sig} (ha : a ∈ inputs) :
    bit t a = bit r graph → bit r a = bit r graph := by
  rw [←input_list,List.mem_ofFn] at ha
  obtain ⟨i,rfl⟩ := ha
  change (inputs.getD i.val 0).getLsbD t.val = _ → (inputs.getD i.val 0).getLsbD r.val = _
  rw [inputs_spec,inputs_spec]
  simp only [mWitness,Bool.and_eq_true] at h
  cases e : bit r graph
  · have he : r.val &&& t.val = r.val := by simpa [e] using h.2
    have hb := congrArg (fun v : Nat => v.testBit i.val) he
    simpa only [Nat.testBit_and] using (show t.val.testBit i.val = false → r.val.testBit i.val = false by
      intro ht
      simpa [Nat.testBit_and,ht] using hb.symm)
  · have he : t.val &&& r.val = t.val := by simpa [e] using h.2
    have hb := congrArg (fun v : Nat => v.testBit i.val) he
    intro ht
    simpa [Nat.testBit_and,ht] using hb

def mDominates (p n w v : Sig) : Bool :=
  (p &&& w &&& ~~~v) == zero && (n &&& ~~~w &&& v) == zero

theorem mDominatesBit {p n w v : Sig} {r t : Row}
    (hw : mWitness p n r t = true) (h : mDominates p n w v = true) :
    bit t w = bit r graph → bit t v = bit r graph := by
  simp only [mWitness,Bool.and_eq_true,beq_iff_eq] at hw
  simp only [mDominates,Bool.and_eq_true,beq_iff_eq] at h
  have hp := congrArg (bit t) h.1
  have hn := congrArg (bit t) h.2
  rw [bit_zero] at hp hn

  simp only [bit,BitVec.getLsbD_and,BitVec.getLsbD_not,t.isLt,decide_true,Bool.true_and] at hp hn ⊢ hw
  cases b : graph.getLsbD r.val <;> cases u : w.getLsbD t.val <;> cases y : v.getLsbD t.val <;> simp_all

abbrev MFace := ColumnInfo × Sig × Sig × List Row

def mValid (c : MFace) := mGeometry (subcube c.1.1 c.1.2.1) c.2.1 c.2.2.1 c.2.2.2

def mZero (p w : Sig) := (p &&& w) == zero
def mOne (n w : Sig) := (n &&& ~~~w) == zero

theorem mZeroOK {p n w} (h : mZero p w = true) : mDominates p n w zero = true := by
  have eq : p &&& w = zero := beq_iff_eq.mp h
  simp [mDominates,eq,zero]

theorem mOneOK {p n w} (h : mOne n w = true) : mDominates p n w one = true := by
  have eq : n &&& ~~~w = zero := beq_iff_eq.mp h
  simp [mDominates,eq,zero,one]

def mScore (p n : Sig) : List Sig → Option Nat
  | [] => some 0
  | w :: ws =>
    let save := mZero p w || mOne n w
    if save || inputs.any (mDominates p n w) then
      (mScore p n ws).map (fun k => k + save.toNat)
    else none

theorem mScoreSound {p n : Sig} {f t : Row → Row} {bank : List (Wire Row)}
    (witness : ∀ r, mWitness p n (f r) (t r) = true)
    (avail : ∀ a ∈ inputs, Available bank (restrictRows f (observe a)))
    (ws : List Sig) {m} (hm : mScore p n ws = some m) :
    ∃ better, List.Forall₂ (Improves (restrictRows f (observe graph)))
      ((ws.map observe).map (restrictRows t)) better ∧ supply bank better ∧ m ≤ mass better := by
  let G := restrictRows f (observe graph)
  induction ws generalizing m with
  | nil =>
    have e : m=0 := (Option.some.inj hm).symm
    exact ⟨[],.nil,by simp [supply],by simp [e]⟩
  | cons w ws ih =>
    simp only [mScore] at hm
    split at hm
    next yes =>
      obtain ⟨k,hk,eq⟩ := Option.map_eq_some_iff.mp hm
      obtain ⟨tail,hr,hs,hl⟩ := ih hk
      have add (v : Wire Row) (ok : Improves G (restrictRows t (observe w)) v)
          (av : Available bank v) (costLe : (mZero p w || mOne n w).toNat ≤ cost v) :
          ∃ better, List.Forall₂ (Improves G) ((((w::ws).map observe).map (restrictRows t))) better ∧
            supply bank better ∧ m ≤ mass better := by
        refine ⟨v::tail,.cons ok hr,?_,?_⟩
        · intro x hx
          exact (List.mem_cons.mp hx).elim (fun e => e ▸ av) (hs x)
        · rw [mass_cons]; omega
      cases hz : mZero p w
      · cases ho : mOne n w
        · obtain ⟨a,ha,hdom⟩ := List.any_eq_true.mp
            (show inputs.any (mDominates p n w) = true by simpa [hz,ho] using yes)
          apply add (restrictRows f (observe a)) _ (avail a ha) (by simp [hz,ho])
          intro r h
          exact mWitnessInput (witness r) ha (mDominatesBit (witness r) hdom h)
        · let v : Wire Row := fun _ => true
          have hc : Constant v := ⟨true,rfl⟩
          apply add v _ (.inr hc) (by simp [cost,hc,hz,ho])
          intro r h
          exact (bit_one (t r)).symm.trans (mDominatesBit (witness r) (mOneOK ho) h)
      · let v : Wire Row := fun _ => false
        have hc : Constant v := ⟨false,rfl⟩
        apply add v _ (.inr hc) (by simp [cost,hc,hz])
        intro r h
        exact (bit_zero (t r)).symm.trans (mDominatesBit (witness r) (mZeroOK hz) h)
    next => simp at hm

def mCut (c : MFace) (k : Nat) (ws : List Sig) :=
  (mScore c.2.1 c.2.2.1 ws).any (fun m => k < c.1.2.2.2.2 + m)

theorem mDirectedCut {c : MFace} {k ws} (geom : mValid c)
    (face : Slice inputs graph (subcube c.1.1 c.1.2.1) c.1.2.2.2.2)
    (nd : ws.Nodup) (cut : mCut c k ws = true) : ImpossibleT graph k 0 ws.toFinset := by
  classical
  obtain ⟨f,src,dom,avail,nc,prior⟩ := face
  have extRow (r : Row) : ∃ t, mWitness c.2.1 c.2.2.1 (f r) t = true := by
    obtain ⟨t,_,ht⟩ := List.any_eq_true.mp (geom _ (dom r))
    exact ⟨t,ht⟩
  choose t ht using extRow
  have eq : restrictRows t (observe graph) = restrictRows f (observe graph) := by
    funext r
    have h := ht r
    simp only [mWitness,Bool.and_eq_true,beq_iff_eq] at h
    exact h.1.1
  unfold mCut at cut
  cases he : mScore c.2.1 c.2.2.1 ws with
  | none => simp [he] at cut
  | some m =>
    have small : k < c.1.2.2.2.2 + m := by simpa [he] using cut
    obtain ⟨better,related,sup,saved⟩ := mScoreSound ht avail ws he
    intro q u hq hu live
    have orig := monoRestrict t (listMono live (by omega) ws nd rfl)
    rw [eq] at orig
    have alt := monoErase (improve_run orig related)
    obtain ⟨j,bank,reach,hit,bound⟩ := contraction nc alt _ Reach.start sup
    have lb := prior j bank reach hit
    omega
def jCols : IndexTree ColumnInfo := (.fork 145 (.fork 72 (.fork 36 (.fork 18 (.fork 9 (.fork 4 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12),(0,2,440,69,8)]) (.leaf [(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12),(0,4,369,138,8),(5,0,506,0,8)])) (.fork 4 (.leaf [(6,0,505,0,9),(4,2,440,65,7),(2,4,369,136,7),(7,0,504,0,7)]) (.leaf [(5,2,440,64,6),(8,0,503,0,12),(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8)]))) (.fork 9 (.fork 4 (.leaf [(12,0,499,0,9),(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7)]) (.leaf [(10,4,369,128,6),(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)])) (.fork 4 (.leaf [(16,1,460,34,7),(19,0,492,0,8),(21,0,490,0,7),(21,2,424,64,5)]) (.leaf [(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8),(9,16,486,0,8),(27,0,484,0,5)])))) (.fork 18 (.fork 9 (.fork 4 (.leaf [(11,16,484,0,5),(24,4,353,130,6),(29,0,482,0,5),(26,4,353,128,5)]) (.leaf [(32,0,479,0,12),(0,32,94,385,8),(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7)])) (.fork 4 (.leaf [(34,1,460,16,6),(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8)]) (.leaf [(49,0,462,0,8),(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)]))) (.fork 9 (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7),(74,4,305,128,5)])) (.fork 4 (.leaf [(80,0,431,0,11),(83,0,428,0,7),(96,0,415,0,9),(96,1,396,18,6)]) (.leaf [(98,1,396,16,5),(128,0,383,0,13),(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11)]))))) (.fork 36 (.fork 18 (.fork 9 (.fork 4 (.leaf [(4,128,347,32,9),(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6)]) (.leaf [(133,2,312,64,5),(136,0,375,0,9),(140,0,371,0,8),(132,8,99,272,6),(138,4,369,0,5)])) (.fork 4 (.leaf [(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11),(160,1,332,18,6)]) (.leaf [(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8),(176,1,332,2,5),(180,0,331,0,5)]))) (.fork 9 (.fork 4 (.leaf [(192,0,319,0,11),(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8)]) (.leaf [(260,0,251,0,8),(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6),(296,0,215,0,7)])))) (.fork 18 (.fork 9 (.fork 4 (.leaf [(40,256,151,64,6),(304,0,207,0,6),(273,32,78,128,5),(56,256,135,64,5)]) (.leaf [(320,0,191,0,11),(256,64,189,2,9),(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7)])) (.fork 4 (.leaf [(324,8,163,16,5),(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5)]) (.leaf [(224,256,23,8,5),(11,0,484,0,5),(1,16,486,8,9),(18,0,493,0,9),(5,16,482,8,6)]))) (.fork 9 (.fork 4 (.leaf [(7,16,480,8,5),(13,16,482,0,5),(15,16,480,0,4),(31,0,480,0,4)]) (.leaf [(33,0,478,0,9),(48,0,462,0,8),(40,16,454,1,6),(41,16,454,0,5),(65,0,446,0,9)])) (.fork 5 (.leaf [(68,0,441,0,8),(71,0,440,0,5),(10,64,181,256,6),(80,1,396,34,6),(81,0,430,0,8)]) (.leaf [(82,0,429,0,8),(82,1,396,32,5),(84,2,424,1,5),(85,2,424,0,4),(87,0,424,0,4)])))))) (.fork 73 (.fork 36 (.fork 18 (.fork 9 (.fork 4 (.leaf [(80,8,163,260,6),(73,16,422,0,5),(84,8,163,256,5),(33,64,156,258,6)]) (.leaf [(97,0,414,0,6),(98,0,413,0,7),(35,64,156,256,5),(112,1,396,2,5),(114,1,396,0,4)])) (.fork 4 (.leaf [(129,0,382,0,9),(130,0,381,0,9),(5,128,346,32,6),(7,128,344,32,5)]) (.leaf [(135,0,376,0,5),(141,0,354,0,4),(145,0,366,0,8),(146,0,365,0,7),(146,1,332,32,5)]))) (.fork 9 (.fork 4 (.leaf [(147,0,364,0,5),(148,0,355,0,7),(21,128,330,32,5),(133,16,354,8,5)]) (.leaf [(146,4,353,8,5),(144,8,99,260,6),(152,0,359,0,8),(153,0,358,0,5),(148,8,99,256,5)])) (.fork 4 (.leaf [(156,0,355,0,7),(141,16,354,0,4),(157,0,354,0,4),(154,4,353,0,4)]) (.leaf [(158,0,353,0,4),(32,128,347,4,9),(129,32,94,256,6),(161,0,350,0,8),(162,0,349,0,7)])))) (.fork 18 (.fork 9 (.fork 4 (.leaf [(37,128,346,0,5),(39,128,344,0,4),(167,0,344,0,4),(40,128,339,4,6)]) (.leaf [(44,128,339,0,5),(176,0,334,0,7),(177,0,334,0,7),(178,0,332,0,4),(178,1,332,0,4)])) (.fork 4 (.leaf [(52,128,331,0,5),(53,128,330,0,4),(181,0,330,0,4),(168,16,326,1,5)]) (.leaf [(184,0,327,0,5),(169,16,326,0,4),(185,0,326,0,4),(193,0,318,0,7),(194,0,317,0,8)]))) (.fork 9 (.fork 4 (.leaf [(193,2,312,4,5),(195,0,316,0,5),(192,4,305,10,6),(196,0,313,0,7)]) (.leaf [(194,4,305,8,5),(196,2,312,1,5),(197,2,312,0,4),(199,0,312,0,4),(202,0,305,0,4)])) (.fork 5 (.leaf [(200,4,305,2,5),(202,4,305,0,4),(206,0,305,0,4),(224,0,31,0,7),(193,32,30,256,5)]) (.leaf [(225,0,286,0,5),(102,128,281,0,4),(230,0,281,0,4),(257,0,254,0,8),(272,0,175,0,8)]))))) (.fork 36 (.fork 18 (.fork 9 (.fork 4 (.leaf [(276,0,227,0,5),(289,0,222,0,7),(289,16,198,8,5),(296,16,198,1,5)]) (.leaf [(297,16,198,0,4),(313,0,198,0,4),(321,0,190,0,7),(259,64,188,0,5),(262,64,185,0,5)])) (.fork 4 (.leaf [(72,256,151,32,6),(264,64,181,2,6),(328,0,183,0,8),(266,64,181,0,5)]) (.leaf [(268,64,177,2,5),(332,0,179,0,5),(270,64,177,0,4),(272,64,173,2,6),(336,0,175,0,8)]))) (.fork 9 (.fork 4 (.leaf [(337,0,174,0,5),(274,64,173,0,5),(275,64,172,0,4),(339,0,172,0,4)]) (.leaf [(280,64,165,2,5),(344,0,167,0,7),(329,16,166,0,4),(345,0,166,0,4),(282,64,165,0,4)])) (.fork 4 (.leaf [(346,0,165,0,4),(340,8,163,0,4),(348,0,163,0,4),(352,0,159,0,8)]) (.leaf [(289,64,156,2,5),(291,64,156,0,4),(355,0,156,0,4),(356,0,27,0,4),(104,256,151,0,5)])))) (.fork 18 (.fork 9 (.fork 4 (.leaf [(360,0,151,0,5),(368,0,143,0,5),(120,256,135,0,4),(376,0,135,0,4)]) (.leaf [(384,0,127,0,9),(390,0,57,0,4),(404,0,99,0,4),(404,8,99,0,4),(412,0,99,0,4)])) (.fork 4 (.leaf [(384,32,94,1,6),(416,0,95,0,8),(385,32,94,0,5),(418,0,29,0,4)]) (.leaf [(432,0,79,0,5),(401,32,78,0,4),(433,0,78,0,4),(448,0,63,0,8),(449,0,30,0,4)]))) (.fork 9 (.fork 4 (.leaf [(386,64,61,0,5),(450,0,61,0,5),(390,64,57,0,4),(454,0,57,0,4)]) (.leaf [(200,256,23,32,5),(456,0,55,0,5),(464,0,47,0,5),(472,0,39,0,4),(416,64,29,2,5)])) (.fork 5 (.leaf [(480,0,31,0,7),(449,32,30,0,4),(481,0,30,0,4),(418,64,29,0,4),(482,0,29,0,4)]) (.leaf [(356,128,27,0,4),(484,0,27,0,4),(232,256,23,0,4),(488,0,23,0,4),(496,0,15,0,4)])))))))
def js14 (i : Nat) : Nat := 0x81000a02ac02009400040001e6070020
def jm14 (i : Nat) : Nat := 0x1bd0007ac4149abfe4202
def jr14 (i : Nat) : Nat := 0x6c0
def jv14 (i : Nat) : Nat := 0x11a419cb00000125490000000108724000011200105478000010742902925190008a22d1152cc932d1812c004411d40d0f0011b45500000004800047000
def ji14 := jLookup 26 83 5 6 6 10 js14 jm14 jr14 jv14
def jc14d1a (i : Nat) : Nat := 0x2
def jc14d1b (i : Nat) : Nat := 0x48000
def jc14d1 (i : Nat) : Nat :=
  let i := packedAt jc14d1a (i*1) 1
  packedAt jc14d1b (i*10) 10
def jmasks14 (i : Nat) : Nat := 0xffdff
def jfields14 (i : Nat) : Nat := 0xe
def jFields14 (i : Nat) := packedAt jfields14 (i*3) 3
def jRecipe14 (i : Nat) : Nat × Nat :=
  let x := jFields14 i
  let i := (x/2)%2
  (jc14d1 (x/4),packedAt jmasks14 (i*10) 10)
def jb14 (i : Nat) : Nat := 0x7200e
def je14 (i : Nat) : Nat := 0x1451880e61e505a4c40c545135e8
def jh14 (i : Nat) : Nat := 0x401c000b90047002380110046a00358014000a20034001a000c40038001d000600030000a00000000
def jHints14 (row : Nat) : List (Nat × Nat) :=
  let i := jFields14 row % 2
  let b := packedAt jb14 (i*10) 10
  (List.range (b % 32)).map fun j => Id.run do
    let i := b/32+j
    let i := packedAt je14 (i*5) 5
    let h := packedAt jh14 (i*17) 17
    return (h % 512,h/512)
def js13 (i : Nat) : Nat := 0x198560294b00c150441301803018570403221c00050200b964004282b0000082b0e434000100005902c0a1483f0002a00c4e0140f0280b000731b82901c090007c0042c010141641715d373100005086020096141501e75078250000500000090080bc131142e054440d40d054240a494024150010a248f80143a0147f000bf040970002e00c09002790080500cdd094216102900033018ba0009a31c1e0e83c010621fc004a00c0686819c8c04476004184f52e0d4d30680904c300187d0480005c0007020098290f83d01018034010084240949050020041300466020030814101dd88e00901016039230183f6c000038200241e008430002601431000d50142313400064980fc09054bb064730041702c00004210004b0449a0744636006000ba0cc080041856c4c03081018200f03d18804004430303d2bc340112302ccf01c9f000880280000c0200057028010000503002
def jm13 (i : Nat) : Nat := 0x158141ffdddcf85dd95725bd292edc9f89f0f3b7f4a8b8797f6e858ba6b1bb9d2ee17b5b3e68fe8f6a226bbe640983a245419359ca8ae9cbab6828bf2d0af180c9d0ffc133b8dfbcfc6e2f5b9d5fd7f4d2eed7cab89fbfefcfcd989c5db675b3cdd6e7ede6cbe72e6fa328e58572467f128d9d6deca6d75c9bd7209df5f12cecef86
def jr13 (i : Nat) : Nat := 0x24c88e01761b6645765553943ce52e0931a44b08c00
def jv13 (i : Nat) : Nat := 0x2898e26482e0b7452054648898020000627173e174225104a46f543d523d11b40f509041551bc428e5141019147437d08d12390cf38fc592472d22c432486f4885e03480124148b50aa41484d668e1974477d59660fa1cd416c58a44a8c01485513c430117741191e2445116743e045446d91b4593d0d117a121c47b10b8437540f43a6e2490991aa49299cd46cd24048990b542fd0e452460d000010f443c50a2788863e86f901740bc00062dd12945e9013000118a285124e448d07d41799a763a1181444d1a920c50c44092df646e121014f112555cd24644bd194158d16046361734568000439522bb8710fc68dc000410524f000000000010bb0000e0248258b240c91270001126411505d38504bb488d14f725d0e614fd00c00010be000104f0001098774ae0a459520a4295140487912071bc000425c000a61800000008ec46c90624735031410153c4331110382640e41b901646b90a14655130449194647d91ba16ad00842a50d9400153f40ad1ac480958a45d10d8469d1ff4211c064202622429c47e41b064f48a9cb94702e2da1511e84546a2d460d11a41c6a2c45f5138413517072c524746aea2448c519d43a10274151042443e49740daa1c28090c1471d09a46151a040558d04916e4f45790a0440d592473ca09759d19241e11c441a6567466ee2c60910d34025122412508b46d5c44476d085416523343d921b770101f478d1b7152907447b4470409443d47910066209004a93d039769d23695b51c9749918943e45a376e902349211d14940c2644d51bba82907740e187f44e6d86468d051234e5baa7285174529e01237a0b243b517cb69c48f75b513770390e345b5152b648d6453b29d100004c547a900700011644850000000299248a0c6f464dd14a2e1243441109c124400066f909947dd01c40a145441f1d75000112d0001d462621c7248905a740d652640391f176bd0af45e51a242991c196b903f103d80640c105800011ca490800000019734911086445c00076b963e452c00015ce5c0419800046391fa46910ff466898641d521a45e119f49250d06042c5400011a14758596
def ji13 := jLookup 272 1037 10 10 10 14 js13 jm13 jr13 jv13
def jc13d1a (i : Nat) : Nat := 0x24
def jc13d1b (i : Nat) : Nat := 0x13048110
def jc13d1 (i : Nat) : Nat :=
  let i := packedAt jc13d1a (i*2) 2
  packedAt jc13d1b (i*10) 10
def jc13d2a (i : Nat) : Nat := 0x80e5c376cd5a3364c582f5cb562b54a54274c952234485000
def jc13d2b (i : Nat) : Nat := 0x66196651936458661183605805d1735c16458d6158153541414c5304409120c00
def jc13d2 (i : Nat) : Nat :=
  let x := packedAt jc13d2a (i*7) 7
  let i := x % 32
  (jc13d1 (x/32)) ||| ((packedAt jc13d2b (i*10) 10) <<< 10)
def jmasks13 (i : Nat) : Nat := 0xfffffaffbff
def jfields13 (i : Nat) : Nat := 0x35c31e086fbb78bba4dcbadba68b324981ebdb585ab9544e9df491a38d09e7d73b49abcc085ec280127c86e3bf1958b9c4a61b30a5826c0
def jFields13 (i : Nat) := packedAt jfields13 (i*13) 13
def jRecipe13 (i : Nat) : Nat × Nat :=
  let x := jFields13 i
  let i := (x/64)%4
  (jc13d2 (x/256),packedAt jmasks13 (i*11) 11)
def jb13 (i : Nat) : Nat := 0xe32770ed5b7351c6b6fb0b6c2ca8aea2ac7a43a6b394b236e863dfce7649baf66c177257b13934a2118841a4e8f3338a9223b47aa1644390073800e
def je13 (i : Nat) : Nat := 0x15d99640342322b224b32d010a01c342840f21914b3529a213082ba485189d71669be6a2614140386850891a3c28c4f1b85050a00a103a438c8a4966b4b8b848500e1b203b2145165db54a8cd92ed5c03e4419a48c8abd665812426f18961e0860748c8d16041c193649ed577ed569994c098700d0c27c586fdebb72bd09eccb0b82806b22a9c562c37eb4c20842816520d529b2510f0d00f8c068d91596ed9a21e24142821423a3491915bb6abd2665a0a02410aa4646b0d9a33a6b3130a08e1a142076490a58b95e63766660a01a10a325474c5eb8ed9ae325a221401421a90c8ae2c37eedcaed99972c2c3211c9d9159125f3b443c31f180e4322b82d498f15fb566a4c96120908e90c8aa7930500d088d894828040418bd194930100d1098a2f59467cd925c14242806c828c8eacbd768d01e2c121909ca323aaab546ecd5992c2614140142242ac5e55a1359a1403868490c8a23595e933403642364553debb31cb32c3e32140342849075914bd721b32c0ada54280d484ec919592cd423428070d072e4324e5649b325878285050a034c9395
def jh13 (i : Nat) : Nat := 0x40466021d0102807c403c601d700e50072c031a017600bb805a402b0015900a980504026e0119008b80434020a00f9007b0039801ca00e0027080338019600be005f802e0117004b8005c802dc016a00ae005780298094e00a2025180274012a0092004980238111c008e064401224010600800040801f808fe00770037011b800dc006c0635011ac00a00850022800144008800440021800f8087e003a001d800e400680834001a030c0086000310012800701038041c000e800600032000c02060003400080804020200014000008000000
def jHints13 (row : Nat) : List (Nat × Nat) :=
  let i := jFields13 row % 64
  let b := packedAt jb13 (i*14) 14
  (List.range (b % 32)).map fun j => Id.run do
    let i := b/32+j
    let i := packedAt je13 (i*7) 7
    let h := packedAt jh13 (i*17) 17
    return (h % 512,h/512)
def js12 (i : Nat) : Nat := 0x28c2a005054008148000040040e00101e008050211fe211ba80000024093c920c6034098150600881780900000c3f8080103fc1b81d0000a081009010000000130844f0090040240300480000c0b00900d00627c0005d03e000050140040844601b006518028090f2028278050900153902c0a003c1b84532e0000080b00600c0019e1021800000207822c188040001300e009044064570000804480e8060160b4048140340180002502a0b00404606c0000a0031420007ab3501402e1f0020de0800f0030041b0120270960340480207a1440180105e01c4826900402816800508035000093b67500a0950087740100b0320009d80000a040018001eb2100e02a00e00002887012058002d335e02c0a10e0040200a8160240040086f0120040016b03a048005f40c62f8010000380000c0240000100100204e0c4018020000000e00f0061480c001048608328000060d40100200a0a800bdf0180391200b1100280b89400008c0200405a0104280d00c004001dc1d00081a00504a0000004e61a030008011760f40b86f0440605913b1660203396f23e00a1202e0060a40700101e0200480401e1281820300e0e02e8040720400a8040000040200400e0a406a720220293f06c0860640480100c1c4170031820bc06814020000008060080000000504e0b80001410c3644200703a0240002100e25c020030000041180e0000640204026801809817002d38003461fc0080c8110304b4008280020280b00401800804805000029368010000780080400a0004104358a010098010021684b80700887400004000008ee8050ce0040213000202c008a301418403800082740008450121f40001600010c078004bc01c1d01202010859839002488122950aa010028ce0361d8148021060340703700208cee8e11fc0301580d00200d7080d0040300800101a024090570020042f8140010042300b0100e06d81e09218c02004004101a203910201c048060700a0018640088fc108000d60980c000012044088010000100480182609018009002004048040082f01002d0240848001c0026e00a800018a581380f0160101a806484085198e300a0000819e0ee8d40702400c1b0078152ae0022681305a0041e80b0624b00a80c030044008000001dc2b85f
def jm12 (i : Nat) : Nat := 0xc9edece7f95f85cfc8eefffbafeb3cffe0a5c4abeffacf50b9b71dd25b857daf2e8cfef9b5e7ffb9abab8fbcd6ae47a23f8d98efdaf57f1d6b97e6beeba5b37fc7fed89ae27bfd62a77b4ecce5cc9ddd23bd246d7937f79ef5ed4904a648bcc02537575223586cbdc8efb6bbbbdaf39ef63394db664fbbd32fd0ef06a79ecf3ce27d5cb66cff67139729b93d237addd8984fde3a1de25d7fba3bcc4de75b6d8fbce7fd6c8092f9eafadad3fdfb3fff7f3b5f5aee65eb32fcae626ef1bed3f5fa5adfedde6dff469e89ddfff3ffcbfe6d4f36b25bf9fe4f3cdebfdec7bdf7b7663af9e1f9f4eff597a665575ba99f7dfefd9c6ecdf7b715f3f7c44eb16eb33fd7ffffffefa0eb3c3df6f4174fd8e59bd744f99d1be3bbf553e92fe9ff5ffb3a
def jr12 (i : Nat) : Nat := 0xb2358e9cd169d330a4cc7188b085fd3da77ce49b5b4563abe96baae51296117a063b26a4c015124e4006a0ac0f615016000
def jv12 (i : Nat) : Nat := (if i<1 then 0x911abdaa000095f905fa3494b188c62d330000000161090518000000091440000000000149f5281221a0000f49de70a0d879ae9346d35a4551adb41c65cb509b000000011d00aaa70bc0001d75ca0243849671c7a245a4b588c28654b8ec76509645cd22214401c88080001920450a82ba10d3228490cec580000000815443c8eb6a3976972e0750f5a2ab623880f00002019780a93ad12b8000000092b000000004a3000011b4a00541e690e80000000452a00010eb223a9372e94d2aaa45c73648d74e11800049988cdc5d6a889a3d800000001ac800000000a869147448726e9d54a11141f2657856b0b324af292ed12da31f828f74b914023d44546846d237a4fd41340000000220a832883a502ab34d4014844d22ba06d4b2ed08112820a84194870460f952a46f69599d9cc22ca95891992961c8147aaee5058ed54e74d495c2157a26b482288c90d1d36a4b4000012b2a3e3b50b507d187cc8726d800011a932af25c680ad191800044be82f9c95a0c926144b16693a4af40bc952651a2096404c8b6d1330a68449b61c5278243840614674e2ed98d4b264765ea6224545aa827d0a4a407343e94e1d6a186c756c9494a2fd8e3418287f526d2569407d62c981da3e46458f0f90d3a3554ade865126223eb4262808400024ba4316cfbde96a4e4a2ce8abe94ca43d000041b1e0e205d314600006098a9b419b2215cf923fa00000001c5ca0a500008d650f74d2324288390924424f486b4e15d87a1fe45968ec10eed8572b40f3bd172a5b0373a902d2a621c543a6806924910d320ea91910b138394b1f70690cf4a5f95708372985233e557f0fd9d1a3a3175904ad90838b1b60e68f28ce0c9f046a281fc5da252a4550503e85ba13a470c26466bda170234e84a60f0a35f7a5248751f6a10125a88be50e63a0973372dd909539404930ede507eb995709af549d8da5ad45356e891fc236295daed190c6a2b396364c8d0612af7a3708fd10fba383487881a126ba4951704899dcdd0c2324690f394eca38c4622f5a10dd20af9ae680dd286555a451482b14a8a14c4068823aa7f930f4b2d4876a5f21be499d64dacae10aa773a88b91e8a0cea5a8adbcdb6247041f693ede91b1f831a646ed1cfb1e110b486ccabca582436cae1524a337241de26e11b3251a496890c45aba000413a89f111420ec46b48ff90794879465a86c9085a283401e72bd00aa5233932e5c11d5a2be46d4428e4c6507c42c080bd128a06598e289bd221dc7f49dc92b91ffdb0a46b68d9503ea229363c686d59923db493a8158dd3215d432448bd229a0524b5289b4c4f327412a296985b3a185498083126133552494e8505073aa3f4636892122820db721f7685091d30f667f26f12b9ba454094912ee68a4211b5695ad11c22df436e8cdacb3a51f47be21a4d62ba7e else 0x6900856d148a3fc10634f6ddaea3af4628a6e295f9c684a7d71911953baf79c88a7906d1592441a487d0a5218245db417d1d620d44153530e95b217e422c8ad25dfa246484687a519cb43841c227b10f611c1aa9284b9a39cad2718144d92c8498543f492f527fa381476c86fd0edc280645f4339016a1bd462e82d65f73d7b41eb670d8cda0d24526f3d20c1209b44568232232d384227e9322d2b58234b08ee59185d93fb84b08a10f349c7497d525e4be2193356490bd1cb225a30ea2a990e43a16298ac6ad94049b24585335d26f204c99288d2d04e08d847ee50e51fca1ed4073027598ca13546112a0da32b4eb40e4f51d064229cb964b36042e145d419f08bd2c020042454942126092d045fa90e51ca21b14806f4d105b3ac445c62761cdba1ca418070be1d4139740ae84399c924003b2481ccd58498621aab06913f131e964c879d22f225344d4819d11e5403167e82f11d3a5a177dccea0533255118344790000344d0000e1e59f6b24f64fc95d521a2432aa5c8c2519e48ff730c6b8c000249300008e6104240c645ff617dcf8224473be88f8d850000440081e5168a48745ee66ec6512081135e00000000000488c6e9e61f2195425e000000055860000890119d80007928860d11a21e800008414d175b3b4674866d130d02343fe8791081000000000001a9aa50000000000470119e69e8829d15c800099c80001d2fa28c00000000000240f429ad38c000213d46868815a0e2125000095a)
def ji12 := jLookup 603 2297 11 11 11 15 js12 jm12 jr12 jv12
def jc12d1a (i : Nat) : Nat := 0x24
def jc12d1b (i : Nat) : Nat := 0x13048110
def jc12d1 (i : Nat) : Nat :=
  let i := packedAt jc12d1a (i*2) 2
  packedAt jc12d1b (i*10) 10
def jc12d2a (i : Nat) : Nat := 0xa6f1dba72e1bb66acd93160bd72d58ad5284e952224280c952824303
def jc12d2b (i : Nat) : Nat := 0x1986599464d916198460d82605805d1735c16458d615815354950505324c5304811024483
def jc12d2 (i : Nat) : Nat :=
  let x := packedAt jc12d2a (i*7) 7
  let i := x % 32
  (jc12d1 (x/32)) ||| ((packedAt jc12d2b (i*10) 10) <<< 10)
def jc12d3a (i : Nat) : Nat := 0xf80f3bf38f16f0af09f07f01eb6e96e8ae89e87e36e35e34db6db5db2dafdacda7da6da5da0d8ed8cd8bd88d36d34d2cd2bd25d24d1fd1ad04cc0c40c36c35c34c2fc26c16c0cbb6bb5bb4bb3bb1bafbadbacba7ba5ba0b8cb40b3db3bb3ab37b36b34b32b31b30b2eb2cb2bb25b24b20b1fb1ab16b0fb0db0ab07b06b02b00ac0abdab9ab8ab4ab1ab0aaaaa7aa3a9fa9da98a92a87a86a40a3fa36a34a2e9bf9b69b59b49b39b19af9ae9ad9ac9a59a099b93f93693493393293193092e92d92c92b92992692592492392192091f91d91b91a9189159149129069048c08bf8be8b68b58af8ac84083f83e83c83b83983883783683583483383283182f82e82d82c82b82682582482081b80f80c8087b67b47b17ac7a97a579a73f73e73c73a73673573373172f72d72b72a72972872672472372272171f71d71a7187127076c06b86b76b46b26a56a068f68968368063f63d63a63963863663463163062f62e62d62b62a62962762462362262161f61e61d61a6136126076066045c05bf5be5b65b55b45b35b25b15af5ad5ac5ab5a95a75a65a45a35a15a059f59a58553d53c53753653553453353153052e52d52752152051b51450f50e5055004c04bf4be4bd4bc4b94b84b64b54b44b34b24b14b04af4ae4ad4ac4ab4aa4a94a84a74a64a54a44a34a24a14a049f49e49d49c49b49a49949849749549449349248f48e48b48648548043f43e43d43c43b43a43943643543443343243143042f42e42d42c42b42a42942842742642542442342242142041f41e41c41b41a41941841741541441341241141040f4074054043bf3bd3bb3ba3b63b23ac3a539a38434033e33d33c33b339338337335333280200180100080000
def jc12d3b (i : Nat) : Nat := 0x1a96a1a7699a5691a3689a16819865d966559464d9161d866158460d82605805d9755d1735c5705956458d6258560551535495154143509414c9314c1212a4a8298a5290a32849524c9121483204530c400
def jc12d3 (i : Nat) : Nat :=
  let x := packedAt jc12d3a (i*12) 12
  let i := x % 128
  (jc12d2 (x/128)) ||| ((packedAt jc12d3b (i*10) 10) <<< 20)
def jmasks12 (i : Nat) : Nat := 0xfffffeffdffcffbffaff7ff6feffeefbff7ff7eeffdffdfedfddefdbfd7fbffbfebfdbfbbf7befbdfbbfb7faff9ff7ff7fe
def jfields12 (i : Nat) : Nat := (if i<1 then 0xbea39b9251b18928a3c7d44933ea19f6050ac49a83608140a6409fa5604faf2927a49313cccc09dbf204e9bd0273325538aac09bc4df4d82c626ad78134233e99879b4c80d0262c7813078c097df0c4ba97025ae1812c163e959b604a8d90252154928363e93c59f49973024b78492436be91a12048a9f024266812074bc8fd9cc478ed023aba811c1d3e8d85124698c12322f7d18a1408ba2e04586f022b1681147c40898ddf44adf02223f49108040879a1f43893021ac2810c80c0858e1f428bafa12dc8108b14083e2124197d020b8f8104692c81e512408610202307d003d827fb1a03fad501fac130fccc407de1523ea5ca9f32880f8cfc07bd8123d8f101ea6b80f46040799d9f3ca7061e36780f03c3e77925f3bb1691db4e04ec071875a4983a93901d28080e853c073b5a0398d6f9ca4c80e4263e71ae20389fe91c37680e038246f8f1237a50f9ba190cdc5b406d9a5f36ad701b22680d8c3246b9e4c3596501aa617cd4a0c069959b3488301a28948d016c067c41f33a21019a5e7ccc4cc0658be03288101926180c84d3063cce031868f98a417cc4c0c061b3e03084cf9831c54c016be5f9c602fb1d017b9740bc86245d8ae02e99a6173a148b810405bb0602d880f96a5064b4624059881f2cafd01630880b06d4057c7552b856f95ae480ac2b40558d602a8e501520c18a810c053ac602995f014a3e7ca4b2c0518d5f2882e3942217ca08ea84fc99227a05013a60809c9cc04d9c9f268acf9325e809865c04bd1a0259db012a0104947ac049c12024a966123994890cea447b65f23aa3011a5c7c8ca2c045aa6022b2d01125c8088284043981f21b26910a717c8432be41941f208250102267080463e3fd2201fa38a0fa517c7cbec03d81011e97900f2266c7828c03baba01dae100eb247c7455403984601c8ccf8e33f8070469837ad201baa6b0db25806c058e359dcc1aa4af8d2878068cd2433d7e019b3d00cafb80643cc031c38c1892900c3217c6008402f90a01792700ba797c5cc1402db8a01682e60b2398058c3b02ba79815872f8aa42485437be29e3d214a1500a2918050213e279fe013a49009a4f7c4c8d3e25d4a0129070093218048504023cd2011b2c908aca80440798219ce0109310083284840cc241fc4a00fa56607b9c803c9e981db9a00ea22f873954838913e1bca110da10606b5a80349d4019a90c0c8000062f480305bc017db200bb13005a4e7c2c6ec01590520a9c29052f95828adc0138081098b4f84a8e302494c011b8e0088ef0042bd802039be0f9ddf07ade903b64801c44400dd5a006812603305801835400b9f20058b5002b6c4c14353e09d7530489ab822443010d02407b260038e4901a40480c99a405c0e002959001240440894be0392800180f000afd800419be01910b0084ae8036e8000 else 0x120824d71252626e092c186494092a49bbc1243ae091ee3048d1b82458dbf22418c90dca6485354a4111bf2060e08fc50fc7c75323d12c11e3b528ee12c474ee82398cc11c49df8de9a146c7e3235893f1a4d958cc64fc64a2823138a51837e08bf38945cf0822d14bf16465f8ac6cfc54368229c8a514602089c88fc4d207e25d10312095f88e770444db82212c3f1015df87ee0943c1f7e1d22410e4d1286d860c34677e199bc10c3f9685c8efc2cfb4a1543410a0f6084ca6fc24d08211123f08071f83ed3041d5f4a0d744106362082d42941463820909c10419e081cab040c597e0551990233a080d510404227601664100155f7fdcf03fcfd49fd98c0fe0f5f7edd873f56681f931befc42e07de5f03ec9e3df511b6fa2d607ce5b03e40f09f13a40f83d9a7bec703dccd09ed3a3ef657a07adf503d57f81e92a3ef44aa079def03cd4781e583c0490aa07901463c77281e20dc0f094db7832093bf3a49de8404eeb36077054fbb6227dda91beecc34c762a0f3ae7581d68faaeaca9f7527863a6bb81d23abee8b292740e6939f1f51cecda4e6dd207311093970681cabcc0e49cd172062fb8f6181c62bb2e2a5a0712d103870f31c242c0e0915f702b1037e2781be293edea0606f230fb764831ba56c0dc89df6e1ed036e647db62dc0da920b6d0b6fb677881b23240d8e4926c1d8b35ee581ae6318d6b4606b05cfb563f81aa9f40d4d7206a167034e0a25a63d04d2b55f691e703470c81a2a4c0d095e0680c4fb3e1b7d9ebd98cedd586726b03361a7d9a1fbeccca52660fc132e0d146b4ec0cb52a0656b30328fe3993c6c0c928926466c6b2154318f0d40c72ae0636f5031818158b7040c551206262efb10050587792cc300c1616610309873d83c5c0c112206063ca3008a817f5fc0bf121f5f5ff02f870817b2198bd25e05e4e0faf04b817725bebb3be05d58b02e8828173a040b922605c47a92e01e7d6fcbbcb742d25b52102d98a816b5340b5020c5a41c22d0082d673b18b334d6596af02c9157d63a1c0b1064c584befac173815f50c0af3516574d102b878315b583ead05883730892b21d7d588a36ab9e0b55aa902ab6d81544fc0a9dc525494a62a2c881507540a7e5ca53a4d029a46814c1dc0a5b98c52a5902928f81481d)
def jFields12 (i : Nat) := packedAt jfields12 (i*25) 25
def jRecipe12 (i : Nat) : Nat × Nat :=
  let x := jFields12 i
  let i := (x/1024)%64
  (jc12d3 (x/65536),packedAt jmasks12 (i*12) 12)
def jb12 (i : Nat) : Nat := (if i<1 then 0xabed917cd72f65b5e824bcc2179232efb55ddccbb53576052e9d25d098b9ca57342ae3f55c554b84b16fc6add905b818b6aad6c67ad6735a826b4d1969052ce9c59b4eb312d64bbac84958dd6b1725618b2c12f57f58afa255e76abb6c57416ae1b55b28ab431565d4ac9915901ab1655614cac10d5756aad6a557d8aa9b154952a71154c8ca93ad51f42a0d953b72a68f14c942967652a54a4fa948d928ed751c88a32b5459628a285111aa15e541a8a816f4fea29f1dd3d09a77f14eae89d2993929a6f774dae09adc13499267cb4cd529971d32642611e4bf56976452dc8259904adea956a92a82a54654a55c940552755a4d4b4962492539234b2452b4871a909a5207623f8b47dca8f62d1d8a237da46c5a8d4251959a310d45c6e8af4d149aa2657448a088d9d1143a1ff5439f086d350d43219c6430d685e990a7b2134d4235a83fb9073620cae413708196d0209200f93fce87ed64fd339f9c53f01c7daacfa0a9f2ab3e2967c0a4f64e9ea713cfe8795d0f1899e0b33bed477544ee339dbc53b51476148eb759d4363a49e74238e7f29cdd1397a072648e3e71c5543856a6fde8dea89ba773730e6dbd4daa69b4c4366d66c25cd8021ad943598c6ab40d4589a72c34a6068bc8d0a699f5033d0c67430ccaf1978e32d4e6571cc9d8992c7321de639d0c5ac9881a30aea6102cc0e91804c2fb2c5edc4bc899776d2eaa25c960b87596faa2dbdc5b41cb64216a712d21659fa4b336164512c46258598b08195fab2bb605731cad39958ec2b08a55a38aa671532d2a1a653f20a74514d4a2966252254a30a1448c286945099ca07613fe827ae84eeb89c3d1376826c924d04898e91310625e204b5b4966292b4c254144a5189424125f32489a48940906611eef23bd046dd08d629190e22cac451bc89669116b21c7442ed085731092e20cec417908226901d42005a3f93c7e568fab01f02a3d6507a538f2151e09c3b9bc76570eacf1d0e63994472b38e3321c2dc381246fd28de891bbca36ec86d350d9871b18c357dc69ba0d1cd19e2c331d465668c94c18c7230be8601b0bf8517c182ec605c880b7e916d162d0cc59848b2081628c2bd4057050ac2f1568e2aa1854670a6b1146f428a1c50d389e5b138de26ca84c3b09578125e823fe046d908c2c114dc225a0435b0854b1075a209a8408587dda0f9901f0183cd9877530ec521d42439f48728b0e2561beb0370686d270d7d41ad903505868100cc9c1959c31a885ffb0bdd0173442de4059b10af22156402a630536b0a2a213bcc268784ab308f7011644219983fbc07e0a0f9941ed303c89074660e0c01aab833cc0645a0bc64165982b4b0507209844124602290040a4076d40e63819d802f2405358092a010eb01e1e03918064700b690131e023180403006ab00a5800fa8016480016 else 0x20cc741733826fd0444e07c640c98816d3025c20424c066f80865008c1ffbb3fd707f7d8fe365fb683f58a7e666fc5b9f789bebf97d45cfa2b1f386be4947c55ef8435f013bddb47b98ef69cdecc3bd7ed7ac1ef5139e937bd01379e8cf3449e5883c94e78edef19a1e209bc21078020ef5d5dd6abba2576fe4ed6c9d9e7bb24c7611cebc31d63abab877558cea629d415ba57674854e87c9cfaab9d3173796e64d5cbb73962a72768e473dc7d8b8e2c71a12e309dc5a3b881a70be2e087dbf8c37b9c6f320de221bbb4b75ae6ea0adcbc5b8f4370e86dcaadb2b5b5c4b6ac66d1a0d9c39b297b62766c216d7a51ae8635ab36b40ad6231ac02356e96aad8d4b55a912b516669e64d334da5a63483968d1ad1431a197b41ac67fdccfe0d9ed7b3c0d67556ce5a99c1533576664f0cc4a997d632ea865732cab1994c5328a764e1ac97a59264b230e64356c812d8e8d31bca635cec5f658b07315086265ec44c18788b0d4e61662c253d83a8306676091ec09497ff9afd935f7d)
def je12 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0xc02aa8915dbb0c0d2e894333b193ab7490f2a3b0a1a74a6230f0300e98718f210b7c0cccae114185e59b5c3ccd8841039acfab72608cdb669fed6b74b999086e004dca0cac1dd5b67b33412ccae5505825284647b8c7956d2d5e673294c6840094ea61c6b9554a34b4b99248d6375bed70375a5cf666c4260c56e6a03a648ceeab4ff6bb0d2e1eeb61a952e894095c3a14f0771308223052c0d41c963b12e3b55d5e664c71ab0d2bb96607017cb3d5e0e82769a0b0530b82d32e3a89329d332a88034334b1c761add15f6eb70b0d125ac820ac2f32c781324bb4d9e974780a95125b1ac408c0a023a94ec13cdd6b72384c0dd6af436aa08841e062c8997adac9c3d2871bf33383abcae4ef10f4a1f8e324ed34b5399e14f423110816e747983aa3af1e38b6f91b0d2e4f108019cba220fbb5cab0519ec789789ed361a5c3d84441f581d0d551728f12f13da6c34b87c0dd6db2d7f3f5aa6c2c1307a99713baf5badaec34b90c0dd6a5438a44214426715caa4c6d81dd2996b90dc5b8d853a994ba0c691a5f6303440534b1c47735ccdb6bf5793a7d044f210a498461085026e3ab1ca27b4cae06db61af54a7b2b93b55849f4110946812c131c6b74a119ce413855a130ba8a493b130f8450ee89fd787811719267f819994c442009b193313c0d5e4f144119c7cb32a93013552304d324471cb2278096c9c9e3e6315442097a0ccd2972660a7fb0d2e670f83c0e02eb4b8a35484f46195ca8ed3a00ed6992260b6181be44184d13495440e951c274b99c0d2e893d6131922550720e59badaec355a5c8606f1529ecce350a6ab10980a5b9a892f0772671f09daec34b87c0cce4f064f9602eb701ba532a32238a59bbda6009ee2b515456991ebbb79b5da63aeb57a952a813d95c9d04b72485c180b3584cfa4a4cd8079b8daec3034499bc4844c17072dd346c195c6b0be5d6812b93a4c420071a610f13c0e02f975abd12528294160189919de9f84cb6d5e572993c55044f1f2dc42092604d60e34c91b6bb0d2e1f0375b6d4a81379b4cc80765911dd5513838a1327278f84c6b4c9136152a751287409ec9e00f13390992c45987d6eb27e1d12b511e44f61a5c3df2eb6d99a08d255103d932721ea3e598fddeeb698dabd1e893a9992d90c6218781362a11ad6241ab1331d7cb2c4200ff7bb80cec862a741608581ac943c4bc4eef1e8e458a81f599c132ed43ec34b99c1d7aaf4b6ab14e3564c2c5e5252c156f23b7455b61a5c0e024f1c5ba4ce2231138d8313a74ce39167c9c1328776ed6af3d99c518c55100255a3734d4531136315412694b9136b334dca1cb2cda656973393a44aa05728deadb8c054e9d338186c6f50ab4d5834e8fc0de2424d83d327422ccd3eb703001606b1ba6777b5d6e1f0375a250e8314c91541809671326af46f8f5c497 else 0x9a8f227b8a740de2427a1ac6efc4c846a382964f666c81984d88204cc4e66c21b9c96f99abd007c5008bc90725daccdf8e3966c34b91c85669d4ba0a359c550902002917111111a9c0ccca6221004dc69989ccd6e0f000dd6074da666803c4bbf361add3e974599cae2b03808e1b4c36c3c015c6139a9a663561e6d35babcce06af4ba24f5749126025ca46152c2f53489edf6ba5a04f675334d9c86e9871edb69acd3e8b3380abd12813396b2590c60f9d4c42847a0d2e3cd55e2af4ba24cdaaec632dc98179a2c0bc4509808a3283a607016d939a4aa212604dc6724c91b0380a9c51046a2bb44229d2286b6167a9512873d99cae53278d3c5aa9f21325889b2605ea274232c213b5d86ab51a5c5e065b278e468d261118884013044d1deee071ca63511e6d761a5c3e06eb6da942a0d0261328b02351b2c7a7060b8a13174ea483513d86970f277c0a4b00c01a65c444da602f95e9ecce5b278e419aa4f621b0b0075b8881e694c8f1dd3fdbe96af4aa0cf667552a869c64556a8d3113c0dd67b3303a0c88fc964ccae551108128741ecfdc52cdae06eb4b9eccd906a2a8cc0e943a11432ee84ca2278199b7d90c410015072cda49caa05729a889569e8f1e89724c4f69b0d2e1eaf33ba484b05306069f49971133617cabd2a67148d8d65909d2d6e89419ecca3514210253ae322ae531b59984c985071cb266911004c3513d8602cf10832dd266828930468776c4e4f1f3393c843e2a8dc42f25a1c866972666227bbdd6d35b91c260f0375abd067b148bb3cae4c0e02df8942d115c6ad0d6d3002210265c513a5cae413f209310fbcdbed769b0c855ea752a75324eed5b9a846221007027353ea64e7600d0f36b75a5cf66727599847e6b17d3c892589ed666b44a01d1e740e53c99b8dbed76957a9d4a9d3381a7ddab71004c340a71ac06e993a6c3214ea5d16813388401e2670d9d8ae541107c0cb471a64781a89e06db578a3e1bca7411098cb32a9043c0935a651f56266f36bb4d86b34ba3bad2e0ed54d954983404e49da221eb8d2eb8cc6f36bb4c3cda29092608f491276bf170e21e25d0d81c0318d055bcac834ed961310fb5c0d3a66e359d5960702284c352c89df296c2289307f517e6df678ec0d9ea744a04da67164d88c45b1a8ac4e4051e261c77ca04adf0422205ed48f4b92769a599cca2b148306d372842a6227b5d85d5e282622c85c45756c3014ea5b093676262faad51d86972181c056eb553a5d1287418a3419ea34d83016b11038d3a8f4c0f303338314498874044d6ca54c4d16f2cd4df2e557a74bd84a1641b0540b00ac4d411b8d448ba9bbd5ea73d99c51f0ba5b930e4692d38d62465442666b303add509971112273d9988826c61e0793313d8606f8e92a931468784ec34b4b9a3143e71d89f56f3ccb5ca67166125) else (if i<3 then 0x68e9354bcb29743a045980c91185ce21c3e8f16fb8dbed7014e99c0c36c65bac0ec200d21ddc993844e66350f04c44e34cc4f59a2c0dd64e8e260ce50fc99c722cf961228d4991ebb769b0d2e1f0375a3cce265471120e8991e63d0da0c8e430781a5d024f147f318b01a02a5102779abb4e087dae970375a5cf666c44d930441403d55546b588f65913b6ccd045e2a824d6454cee47756c0d3a96f10d28c0e027e4274a2310045c6619fed7034e99954409443b8e58709f90848040e8006e9939697233d99c9daa9f33adc981a9ab70bd98b1cb1f8c6396e3074e99c0de2c62abf1561a384b213bbdd6d365a5c8e0eaf479ecce28ba643196e4c0e4d5f85a581d08aad0d3321a702a8dc66e8ab6d361809eccea27a7742687369242e149a3390a50c90b844186b1045c78b7da6130770a74cde21b631d8aa450d265dc87385584620089e9d13fa2502672d95b2590c6109d56a4947a0d2e3cc8606f14ea5954401a03809467a848d650974ec4f61a5c3c9df0296c8300699711136977a65027b33068092efc8e27d41345bcff4b802988c05859844f6b81a74cc84c65990c7e2009d596070208cc352c89ec3037c83c0904d134955d24519d476b81a953a670a81bc5465522ba834993842697337c27c84e94a0fd3a4c209c36bb4c260e9d336320caa330d1d12efc9649d4e9a21044d6455bec34ba3d163aeb4b8e451aac82b8781074d74a07898899606c817455af92b8a3f884c96426c9221358f12f3fde6df6badc3df6cf61a25026d2d8e2b4b04c11831303c71ab303577fb79044f63154988339112509789d5ea92d53b189800391256a834bcb2eb409ebf9264910b8d303c89ecb53a5c1e070165a4502672d93c51aa4f632dc1899390acfb014bec477bad2dd6cf57a0469e2d54f908ae2006581a41a7125c793d999d1c55689ef3617ca752c50c6069543c3b4b1c5f9bbda6973b83c0df696d5dcb213683369313a79354fef697586d1657a774f666582988c3c0c038b878e24bc4f538abe5a2cf6199c1e04f9639587099051aa583b781176b81a5ccd04672e09e361a9fcb0e5b4d86970f80bad9ecc58119e9323a714ff5581be30904d13515c2e11518821383c0d5e4e82278f98c55248252e692255b31bad9e02ef67b0d0c36e74d88c45b1a8ac0e405710f12ebed8667034ba249e38c964318c21f099c6687d174c6a23cc0e02661a08a0259a0cce0f037ea04ae28fe7035504c6b52c82eef5a110d249cce07017ca250e57147ba08841e1e3f3075781a9c9e294e155c69b2611aac979fed7036d99c24ae554a1190ee35a2125981abc9e2855261181299099a488e3ab4fef94093c50cec52c1541809622d02611718e9324c89e670781abbc504421f3f1e85571a5c93562260a66744d85c993f7e53281338d45200ba4d19c362207b956eb else (if i<4 then 0x168540c841bab318aa334d868e8979acb3617cabd2e7b3378b093e822109c2ec62a8b802702225e13bba9d22893395b55744f6fb196e4c0e04412019ccd0a61e7e1aec6991eec35b7dbadcae15ba24895a6a2c0326b792649769b0d2e7f0f8199cb64f1c83311366c2b08c3c0f3926478ee9fe070133611a9012cdd6c34b87badb66667622ccae5511082aa941e81dc72c89df2873685324980c569ac76fc5bc9668924ec4f698199a7dc2572611476e5966eb6bb0d2e1edb1a88419046a2b95082380f82ddae51da649b091e25e5113de6d71d83c0dfaeb409ebf88057792c8e42102a6078e3d287ec0119e44f038096c9c9e2963085e4b4390cd2e4ccc44f616da24da4f1488428840c9026034e32345d6fb5c0cce0cd134968aa2a1028e132b93ae8ce4214b186e09581ac664cc125e27b8dbe13074e769a4aa431b88014e35da5d0f5189ef361a5d1dd696fb0566cd73f264976bb0d2dd6671a2105dd2551001c769771427600c8bb896f25da52e6e5d0db240eb289c849887daed367b2d8602eb67a952e87158a440c794c9bb53a4c1f888ca1c71ae09c891e25f6152a241d3e8a33b196e615f0ec98fcc0d2c005c08a7627b4d852936c1404ff0781b6d025b27788f8364c1088826724cb8f054b26140223c4ec4f03578a27d1482211305c13088027f28396d767acd2e2f0380a04ce38b711888160588ec5303c71ed361a5c8e431587c0d85c0de41274a8482302dca97b53b5783d5c55b79b4d2e130781c05faef67abd1267297eb55669d11031ea74265ed2f3cd2e66f94ba049e38c862add68900e82c106b4c8f2784e89ef34b91b3d669cfc2d25c3487dae96af4ba24cd7555630801334358de5892842de97336127d144274a506e9d209c361add2e670f81a24f65f276833cc20c058800b354c38e623ccce0f0380abca64e82cc4a0aa3339265f982266ef5b81c05d6af43a8d35364c1abd9dae29ade52ebea9d32894099cb63c9f338352e3c9aef36bb4d856667146ab2098113a0d403137e2c2f975acd1287409ec9e210b8513c84580601d6eb41103dc6991e44f3357a44ba5ab671a5e78b79ae66af2b210a56097ab3ca4bb0b3cf667278d4413ec71188826b489adc980f001ad60464bc5d3b13c0dcaa5338b409f2c22b9500c27a8a647b2c76d4e81274988c3535383b4f513dae9666f14daa172e392edf6781b3cb5e2a3cf26d24e394667016d9393c52b758084124c09b8cd2464cc4f0375a945084d62c15caa3f768d500514cde8985d8b8692eb4849c20913cce0e914396c51fc4292a5e5181c05f2cf5783a0a42ed2c01ce89971be899338a5564a98944b29d4099c51e21b76954401362b11680a71a64741a89edf033341955c6a322868a29789e1c981a7d4b36181c052e5b276127d8c7a2a9c2a309dc55e9d419bccd8c83228 else 0x879dab759255c63ca8c4f1581c054e667c2b931ca451d9aa59bbda4ccaa1e729049956da61e29a4c9a6cf423110812e74d8a00bce25c0f179b0b6d0e6c9a0f04c19207191a2eb7daec35590c0df2cf5283bc1dc932b930146a20871c2ec960ec8b52a5d2a81339945628041f8cc40e34eadd464c4c44f0357a5ccd849f4520884e9621306eb7138792928209c259b0d2e1f0167a5d2a873696c51849b3d1a9ca802d29970741e25f7184c1d3a4e9f63238b8200521d2ebb9ac266706812807e1a386d666912a815cb2cda6c353a5c8e0eed3694c51f18f864159109395893285266c34591bedd6a544a04520cfdbcb20dc6100e3e847432de93284264f666a1201d16e942601c7b3f714b1882a118812f13da602a26a4ec4f6984c1cde66f10da6624fc43dd67a357e06a27bcda66687409ecae28ffc9bd136210b830164971ae11e971e6d7034b99a0840b009808833f961d3336d93c509e55049308ce35c25f313d9d4ce651a4fb193a099ca48d6455bed359a9ccc9e299b348816f3c9addeaf02b995ca82204358d24e4c8f1db83c0df2db57a749e29068119c9e3e5993027557e38d60440d4b227b8dbed769b0c0e02db61ac55ea54b93c693e8a6d3b5bab7170707ae3583f375b5d854a9733783b8d40a6897838507620d6045dae07017cbad025714854191442779a4ae49042c842ee75ca11f511e6d761a5c3e06eb6db0d4a14d573961467023bb982e284ed761a5c3e06f975b6d9e9d3d99c1966833402ea2b74a1307ae59644eeac61e3d12e4989e96661a9ac4f71b7dae13074ea04cde2404ca1ce0e3dae0697334104c9942541050f2f7c379746727ac5363807801ce9d291043add43a64cc1adbe13073381bc658970d4fd8367b0d027a231139ce4997144f033d99a098c550720e59b0c8e430781c054e9744a1d0681148590a2eed6833cae1c5908014b34c38c343cd96974590a9d1256c65194c19384eec4fab79e6ef6bb4d2e06af3dc2da96e4c05ba02969768f75f56716130781c05c29d4199c7e290b76954261a0538c8a993a6d33383c0dd6af3d93c51885512825285a285aeac44d86972b4ea652e6714480883eed72adcde991e4d627b49eccd058c2a8146ee2ab6670781c049e3f14210f9e8553933c92992260ab34e48880f41a89e952623b044f685a2c154222bb526476eec260f0380abd3a66f176954401a7184c669943bf3078194c520d827e4a10b13266d361a5c3e070175a9cf65b14b51e8b0573a202d65e4c8f1c5badae066655103a9285e2185dc2079638b79b5da6c2eb4b6ab64990f30c4df8b0d8694b93589ef36b4b99c9e29937a26c6a0b2338d70fb89a5f6980b0d2e894396b553e23712c8e0a35a21f6b8dc3db666de64318820b04ac1066b909192f13c1d2e8b4396c5a14674db8d2e1a1e4d76f83a750667))) else (if i<7 then (if i<6 then 0xad0d6cb6180a50b57a762621ea399c0d5e4e4f632dd609126554e4134c9125913ba84c98d29e44edb3278930442109b8e2782586d3014b2d1b0ab7aab6ab4da5cbd5e893d99c9daaea6fb256e532607a73353317a58fca31cb71b7daec33381c052e66c24fa296e6d0e009c68c3b145337f7e44ce1b0c0e02f967b0d4a8943a045220f878a0884582b87c2eed6a265c88f1754479809eccd849f03a0259bcd86830778bad7a9d4ca5cccae540f3b5cab437a6478fc89d5e670b813c66afa2886983b5c0ccd84941eb957670966d361a5c8e1f03616f174a81f89bb52e3c5c4a10db2c05deeb67b254a8f3d94c51f0c86314c7e350e588a2993a13098857dc4f67a5c5e065ab7498300a2a71916c1b0d2e1ecefc4d96018995a38893b0d283006a55bb8889b0d2e1e4ef814a6cb00c24a65c444d2e070175a04ce5b278e451fe4f64b11689b0601d606b07889323c89ed3017c96c19aa9fb5318f45805880d099770f375b4d86067a8234160aa4c4a5e50643776d7695ba952e67298d4553e9d7191524a389adf75a5d1e8b2181bf586813d6ada9a8582b85dcf6b2f3b9323c716d7034b99c69849f45109283774b116e4c752748270a04ae286714b218c1e0602c12b035ca0749789eeb2181add5e7b338a208aa4c0f025b62a0bb893313bd61e664c4eca227b4d861f01338327d8cb73d08c168e459a1323c774ff3383c0e02fd65a250e813d95c5084580b8319c990f3c91e3c24d0e81248519d92c44e8300e6b1125cfa3c5bec2894096c9e389f33b24a6234e9d4fab79e6d74b87c0dd6db338315caa22102507ae35d9c25953a5c9e289f213f0b41a4ba1e7b1a8ac64d64c5bc955527539092e6b232df6b8199b080ea37542777b5d2e470375b0d5ea952a250e3514884296e4c0f0301609b1b75a2991ee71aee2d9697034b99b19224c1fcb22781b94ce290b834099c572a022de691ea66f4eddaec34b87a74cd88b329a511c3c3a0729e4cd8696914497cae44c856832c4fa35adc9925d2e8f4599c3e07016db0d5e52551cb9d641abc932ace243d2e66c2451f1ca991e868e033942493b13d2d38b93589ef36990a1c5200ed4d9a4401a4b8f26bb4d86970f80bad9e7b379b4cecc58118796e744c8f1c53fd852a914191805304c9e2de51b0c0d9e67322888c98c65844f71b5da53a83338a40de2ed3a15440370d38d2f35de5f2eb5e9eb558a541abc8e28f4b92779b5da6c30775af56697076ab1d364c1a028066b2325e7eb0dc613074e99c09f897382ec35b5a5cf6671463156ac7219ca13113d859ea4f113879f8e3966d666825a2506f563a01e272c84eeb6b81b6cccd4075893083096a88dc5669fe02eb678a10a46111f9325928d86972390c3e06c2824e950440b76b589097728f17128d8566a54ea04f667278a44214f145109666811 else 0x74cd32fc59a1f69b0c09310aee84ec32390c1ddea74ba04f667278a3258cb70e4d5ca20099f4e6b00d0f3038094c5204049fbecaae34ccb2264cd860696c24293212fcdae96b757a9cf667324f909c69b51c4d834ba1d022cf133b2588230f1d12e1c3e8f16fb0d3e0281332b08c4005348a9c680309c92e3cc1d3a670378b196e130d02960454c9d377b4d6e470981c05d6af1485b55646a76a0ef580b6d5e9cfe7e8a4364c71ac08c975f55b0780a04ccb0571085900e33f17892694b8f29d3378a5c6e745be02db57a75009ec62a930124934a5f052cc0e02ef5799c720c55273892872260a9017a9fa137980a550e812b8a3fdfc9b10d45c6b0390152e3c5f6d70375a5ccd88b32b954980b04d546a992238e5913dae0666c24f909c4941ba027e709608dd14989d4e89375d19c9e6b298793a41a14a035b4d96970f78b3d4e7b3396c9e28f86a93d6e7a729d0aa2040039e699350f36f4ba0c9e2d034f86d8c2210395607a518e92f13d2ccd3e910981e6b139988800114ec4f75b5d86972181b6d5ea4822b95482d622869d2df4cb8877acc02de78be9aec34b8793c19f0292c03006a57111361a5bad2ca4ed358792e3cda6c34b4ba54ce4f144f95c440b729aaa23a4bc4f0f4ba1cb616d541162d49792d5b69332605928862338a262210265c513cce0ecb48a04ae28fe7c3558cb70b830c0990f3c91e3c24e66812b8fbed366b264fe4bb8dae129d337884c153571c4d61b5b6ccd66531a8780e9447b969e4cc0e02f967b0d5de28290960189922395f44c99c5216c252a6c260571ac4d32cdc6d69d337884c14fc71d588bb5c0d3a9733632dd06912284ce1359644f61a5a9d2e951c8b4518a220fac4d208a8bbc789889b093e8221118702c0039d6e9d208741e6f4c8f5021aa59087efb2644f6110789a4462008b1d3313dd6d761a5c3e06af52a5d0e6d0a61295366a2a829eaa8943c1dc745c49a12973407410464c8f5dbb599a6c983702b8d7cb01ad5b0380be5d6974799c5104639f9d8ae5427089323f2438c792c89cbdbc8233874d6461eadf6b81a5cccd6074e905dd280d6df6181b3bc62e0a71bf365a9d2e8b3380a4512812f96c9d8c5906014d6dd29868053cdd643035733b6da8572a82434464cb88794b99b093e8a2139d28374e904e1b4d4a44442072a64d513d858629102106d40231126dca979fd4a9544a04ce651a8aca226b79e6f3714e9d8418c55488794487da5f20f066f34ef4fc5921250ee266e361a5c853a971a78b341a551002076e24b22377b7d2d5e56b6cda94180b943d531561eebd6f7cbad2dac611f910d63b92aac98fb9fa5e31139e9ac8aaa5be1e669d4dd4658979a44f7184c1d398c20581ac6e188c25e27b499a6c0b2872ac13a37ab666973364319221e098f0449989ed74b81bacf6665a4b8f0e) else (if i<8 then 0x99a9c0e025a6a088813b09d4e057413089166b027c90066992621f65b0d4e0ecf52a250e7b3395ca64ede6aa7d8cb726070b660390f53382a04fa572993c513e295b885c64c09cfc8c9989ec355a5d16670f6db2d92c35dabd12873d99ca64f106f3553ec65b9315e8fbcd588674da6c35ba9d2e8b3395c0d2e3907481208c0b5bda8ece5581a87b56ddedf6badc3e06cf57a451e87409bcda5b167899d50572603136f543e0930e3dae0e9d4b99b1967567e2c0e0330986a591399c722cf9382647aeddaec303333b1a546ea84e0ebf3281b4c9e4214930d6464bac27f332621a5113dd6b70f83c055dfa82213d5ac55099c89925944ce2082168193274263e1144007a50664c43ec35399c055e914499cb59a612b08c400c029705ce31e25f61adc3e0e8f366f48e12132621651b0d2ccc0cb701a65c444be084223c7e44f69b0d2e1f0375b6c5216e72c0f532e2775eb6181bc56620f1689a4b455103a54709d8696eb4b99b55363854bb5624635a647b4e93c7dfcf1339087cfc631546e21792d132333925c999889eeb6bb0c0cccae223828c3509dded76987d264ed49c41931ceb04d8f5e935775e9c497dded2eb3d7195c0afc710dc3556cce07012d93bfc52c65bad03c720984475304c9322642102493b13dd6b74591c26070157593b4997a99aa03513c1e029740789c0f4c184ec34b2d95c19e2580b031f8e292ed32390c6e06af449eb3d469b2a930120594395709d41c97600a0d4d627277c0cd286b266d6db3d99b218cb32b954a00b049ad323347d3c99b0d2e2aeb728e40a7f2c629a4700858919303c77ab2eb4b8e354d452180188c991ebb76bb4d96ab5383abcf667146ab196e912b93044033916c662a4ce0a27b8c260ea74e99bc5c61a38200a2c1c0d4a9d338a40e04f19f86a5887dbed76957a952a671a4e880e4921bebd6fb4d84f60c1b7d3102e74772dc99b5c0d4a97338530914941ba79d47084910a113d859e890a6a99c36c9118013a754da3e79b5add5e7b33aa954124571cb13113d8586af3d88031f41a71adc99aca5ccd90c609984409989e06ae3e63154e4f22225e27b0d4dde672f8e41a04d53f99d6e486e9b010b1231a5323d77df2eb48a04f667278a441fe8233900ae541102c10b40eb8d323c89cf667325d10836ae358dd6fa5c3dd666560c80c1c997a9c88bbcc2606ae0c264f2f5b0d2e672b81c05f2af4ba24ca0ec2642dd20487689c2956580f4e92c9396023797455b2390c0d5e664c4e8d51f284119c901d71a648db7b853a671f8e40c36744bcfd56fcdae067b3361544e0ee8489008b70e801606b1ba6769b0c05f2cf4499cc89823732c12f3fdde130375a2310185a692c2f5b5b6ccd885303afd68eea79336fb5d86070167a5d027b3699cb5e2c23b160ae4c0e204782e4ce08e0e3dc6df0983a else (if i<9 then 0x77a6172bc966130757a74ce3ef978b18aa20438ce1297ab6eb5b91c0db6ae9126238661a7e54ea54ea0d0267037cbc53e3e0dcfd6e331004e78e305264981a89bf36b75a5cf666c962160a650061ac34444bc4ecf4ea5c683407010356909dae970f81badb6c33388208ce6c0fabc7ae2ab44ce9b4d86970f5783484b00c42265f4e2266ef6bb4beccdaa4f641302e11401b40264c4e3df8b0da6c34ba3d1643034ba551228d54d9b6d951589e1c698419793abc1e6d6b73a99a9d8c5510558e52a2626227b0d2dd66682339483a067125c7981c055d848207a0c0e9d20d0a501adbd5ea54ba24f6673278a7c85566327536855ca62a32cc0e025ede4119c8517358788c83941456fb8daed3094e99c0de2748ba5d613fc0ccd8c3f264b2277ca04ce3914833fc80c53615ca81d041a5324a778f27fb419881ca993544f0380be5729d2f8828504673515c029d08d5835b922ed1998c0f046f556da60297339686c46e3591a6a2b343ed34b579ecce649f04a7530e322af17356dc613074e99bc5da5541915c61a4bcb30753a04ce5b0b78a7dda20470652e3c0d6d70f81bacf666c8631306a0b04ac1066b234a12f13c399d361a9acb371b7c260e9c42632ccaa33358441445a8265f913daed34b529ecce3469100253ae31bae53151d2dd6491a46ba89255093103e91380ef6b52a74ce28f1632dd22450d4fe6a7084ed2af33262b1c6bb966d361a9bad9ea72d3d160ae5511881a4803a0f12ee2a04a628fd3392c7c04632de7efc39266264ccce5f0667278f852f4632dd327224ac08982d86b757a5cd667034ba24516e902402ddace58119ca991ee0e9d3393c51fc676315caa1372ad0220a249c1323a7e44e9c111fbf227b0d6e97334b64315244805822ad35521ac7b2c5bec34b3397c69aaba4f99cc01763024a61e34a5c7799b6d5de2821f20caa00391308897c14b267144110aaab15284c0ae35bcb369816627d904c11025321e418f5dd2cdc6df6984c1d393ee33828d6687da6c34fa5d1e830f75af52daa572a394e8034cd58886acc6c29d3d998695109bacf4263f7e44f335795c7c8441c120c9925da6c2cf4b93a7d147a352022781c053a813396c72070033b196e2009a5ce00a98068753589ee29cf14f84c23519a91435b4d86b72384c0dd66d298a42e130542031644cbd6d769b0d46970f81bc5d6966a2b950983272bb48a993a0f761a5d1e8b3387b0d0e387d2c132f31d4baad0fb4d2d9d3623113956097354ff037cbad92c3154118cba9d2a089dae55ba8d0e4e1e25e277c95c51fc2964b213621001ad2f3c9fe06af332a85c264c90a1df999c1d22813d96cae0cf121160ae0c691785c4971a5c797ca5cae4f1a4fa2992c82488426b41e44f017ca04b64f1483160aa0909b8c7499261a67f678e40c2b1d64b102e803a2dc else 0x361a5c8606970a3488010b74ea487951da6c34b87c05d6cf2d339ecae541107ce8991e38a7fb5da6cf65b0c05d6cf64b0d5ea752a5d2a5315413b56e4c1f888a21cc3266c6891e6d761a5c3cce4ef84f8a5360cb036434034cb8889afd86970f277c0a5d25801a65c444de6d70f81b6d5e871a6a90b24d62a88819a19abf330df4b8f1c4aadadd67b3319b94e95689e0701579ecce28c22a93128722d202f52c71696a7402988f5cb79844f6fb5da56e67154febd3a0922b8d79135bec3016db0d7a4efe2106e2e0f72918343d775596fb0c052e94670db10461ea883c0a3c7721d6fb0d2d5e97339745a17023fb14d85724021483d))))
def jh12 (i : Nat) : Nat := 0x101228090c04800241011f808f0047a023b011c808dc046802350119018c80466022f0116808ac044e0225011180884043e021c010e8086c04300219010b8085004260210030800844041a020a010580824040e0204050201810040a020301000080403fe01fc00fd807dc03e801f400f9807c00be001f100f7807b003da01eb00f4007a403ce01e500f1047880bc401e300ef8077403b201d600eb0075403a401d300e800738039a01ca04e501728039401c700e280700038201bf00de006f0037601b600db806d4036601b100d7806b4035601a700d280688034401a100cf806740334019a00cc0065c0328019300c8806340314018b00c480618030e018500c0805f802fe017d00bd005ec02f2017600bb805d402e4017200b8805bc02d8016c00b5805a402cc116600b38058c02c2015e00af8057002ba015a00ad8056012b0015900a90054802a0014c00a580524028c014500a10050c02800140009e004ec026e01350099004c80260012f0096004b402540128009180484023c011e008d80464022c011400888043c0218010b008380414020601000080003f801fa00f9007b803d001e400f00077003b001d600e808730239809cc00e608720239009c800e402710038831c014e008700338009c000df006d0036401ac00d6006a00348099c00ce006601328019600c8006480310018800c2045f012f8017c00bd005d012e8017418b80a5c042e0197008b8025c002e4016c00b7005a052d0196808b4025a002c4015c10ae0457002bc015808ac0055002a0314c14a6065302298094c00a40a5103288094400a20050802701138009c004d00260012e0094004a8024811240092044800244011c188e084702238091c008e0e440622029100c88044400218010a008204410020c0100108004400020028fc0c7e023f001f400f4007a003c801d810ec00750039041c800e410700438011c000e0186e0a37041b818dc086e0237001b820d8046c0036071a828d40c6a0235801a000d0006600328018820c4006200300017000b60058002c0015800a800520c280514020a00c5004280114000a0004e00268011020880844002280108208400420020060f8287c0c3e021f000f40074003b001c000e400681834081a020d0006808320019070c0306014300818030c0106004300018000b8005a002a0015000a0004e00240012000880040001f000e060702838101c060e020700838001c000d8006000300016000a00040001e000c0c06040301818080c020600030001400080c020501020080c0404020101000080003000006000200008000000
def jHints12 (row : Nat) : List (Nat × Nat) :=
  let i := jFields12 row % 1024
  let b := packedAt jb12 (i*19) 19
  (List.range (b % 32)).map fun j => Id.run do
    let i := b/32+j
    let i := packedAt je12 (i*9) 9
    let h := packedAt jh12 (i*17) 17
    return (h % 512,h/512)
def js11 (i : Nat) : Nat := 0x11c140e8030a4a60004401013000601a811358010258926c2e0248a20800360b00cc080880000c01018230701c004060a412058350092754004000000340006400004a60f8010040506c0809421098bf33c100143b000120480200800114080002c01003000270f8000b4000041b0048a050c90101466c0902c0201c110080100015008142b0d5184080b4000000619c39080000c01b670040a8290180a0280937c2002811004480101838c48124170240b1e44a01c043654312c8002030008130fc6507c0c1900d020290e5d211c0308c250a47310c00010430341200c00000098786216c010c8020f44d008090000915c1901cc60d10332c3e00c1e00803048000440700414014003bc0105858000440cc1b01c03000511404702005010000141a00006090d9004461981b000000283819402034005808a004190040b00c00470030281f
def jm11 (i : Nat) : Nat := 0x3fcdfd5b3bbbf5d7fe1ad6ffe7b14479bdfdde8ecd9bd2ee57fe67e1956956edb386979eed99310b5c5bf9779c1bdfacb9677c7fad5c346dd16d7bf9fa53c1fad0ce477c9fafc5feb13a58e7bdb333bd3ef7a4d1eccb7d9eadddc09cdfebef2fbdecfaf72ef5edefadfff789bf5bd6becfd8ef9febe69957ffcddffa66
def jr11 (i : Nat) : Nat := 0x9ae3c855ed71da45e9534bd07380b8228590b000
def jv11 (i : Nat) : Nat := 0x1c6c434d0ee4271e62347d96f4819070709e5bd24acdb745d1068412d1023869cea4a048474065c6899e645c755924d809e64e42fa5474565012b2b924b446c8ad44d8c214655a2f420d2674a151e9271d1267a0915a704512d63c5099763112540f9a61b8f925290f800042e9e049451a3d0001082b37000017accea43500000001025453d143758c0008618000703100a000100f000000045600003a1568635fd01c293510042ddd810000000000000049d9059289d1a800009b711b00000000000723de4e000119a466126c497a46867ac00000000000001000000118a4831248440d170409925940519d563d90bc4639ddb46209bc3944db2413000040151c5482509b9051858468400049c1219992e20941b89b800011c14735079a6e08704601067000266200000004a009b2000108191ea99c00025ab46a4d91463100e348125b0000a8541f9039455c00038f11ff48099e146cd0a748aca4200011d847c5018000104826f4c6b481117d45410c944f925044e909d31b091e4805176a9dcded73b2d7278291b0489c9e840465734758c759758900472ea6a972d24c42be41134add0b46151183571d374789d7c40b520b6668911395d00743dd1d7b8d11c625124fa472a205b92ae6a42cd05151b2dbc63ad26346fd07d425222f68168019631d6b428902887c511e41850cc32811df439da73404cc2c247d11140f5116397d254418ec01719d12721b10c1476e0bc49011bdb67125f27b1145b74114c498a23d43e8a1a90a1e7547a115676089b3451108d405482792525384549e49441e4ba725924e72e90f445cd0453300815451ee77410241344dd0f1466d21579b111465a8822
def ji11 := jLookup 260 998 10 10 10 14 js11 jm11 jr11 jv11
def jc11d1a (i : Nat) : Nat := 0x24
def jc11d1b (i : Nat) : Nat := 0x13048110
def jc11d1 (i : Nat) : Nat :=
  let i := packedAt jc11d1a (i*2) 2
  packedAt jc11d1b (i*10) 10
def jc11d2a (i : Nat) : Nat := 0xa6e9cb86ed9ab466c98b05eb96ac56a94274a911214024303
def jc11d2b (i : Nat) : Nat := 0x1986599464d9161183605805d1735c16458d615815354950505324c5304811024483
def jc11d2 (i : Nat) : Nat :=
  let x := packedAt jc11d2a (i*7) 7
  let i := x % 32
  (jc11d1 (x/32)) ||| ((packedAt jc11d2b (i*10) 10) <<< 10)
def jc11d3a (i : Nat) : Nat := 0xdffb635d695d13a2343680ceb95724e48c8d8cefadf4b8f67ac1d73aab52e99d30a5742e7ccf69eb3c275ce49c737a6ccce999326634c59832ce5149e92321a42c7386b0d219c3085d0ae1241a7e6fc1f7beb7d4fa1f2be47c6f89f03df7bcf71ed3d97a8f4de8bc5786ef5bfb756e6dc9b8b706dcdb5b636b6d4d95b23636b4d2da3b28632ba573ae35c4b85702de5b8b656bad158cafd5bab6566a91472885049f139a694c29812f2594a291922a4347a8d51a2334648b915a284468890fa194087ecfb1f53e87ccf91f03de7b4e99ce39a710df1bd3786ecdc1b736a6d0d99b23626c0d79ae35a6b0d59aa3526a0d39a634a68cd11a134067ccf19d33866ccc99832e658ca193324644c718d314614c217e2f25d4b91702de5b0b596a2d25a0b39662c858cb11612c057caf15d2b6568ac9582ae558aa1532a4544a814f29c518a214327c4f09d1392624ac921192063f07d8fa1f03dc7b0f21602a43a82c0540640c017
def jc11d3b (i : Nat) : Nat := 0x6a5a869da6695a468da2685a066197659956519364587619856118360981601765d5745cd715c16559163589615815454d525455050d42505324c530484a92a0a6294a428ca1254932448520c8114c31
def jc11d3 (i : Nat) : Nat :=
  let x := packedAt jc11d3a (i*11) 11
  let i := x % 64
  (jc11d2 (x/64)) ||| ((packedAt jc11d3b (i*10) 10) <<< 20)
def jc11d4a (i : Nat) : Nat := (if i<1 then 0x2434243324322430242e242d242c242724262424242324222421241f241e241b2415240d240c2409240824072401240023ca23c823c423b823b523b423ac23ab23a923a523a423a2239e239d239a23942389238023482338232f231c2317231622bf22b822b722b622b522b122b022af22ac22a922a822a422a1229e229d229b2283223f2238221e221d21c821c7219e219d214a214921482147213e213d213c213a213821372136213521322130212f212b21292125212421232122211f211e211d211c21192116211521142113210c21092103210020ca20c820c720c32047204320161fc01fbf1fbe1fbd1fb81fb71fb61fb51fb11fb01faf1fa91fa81fa41f831f4a1f491f481f471f461f451f1e1f1d1f1a1f0d1f091ecc1ecb1ec91ec81ec61ec51ec41ec31ec21e111e0d1db81db71db61db51db11daf1dae1da41da31d9f1d941d901d0d1cc01c401c3b1b9a1b311abf1ab11a3f1a2f1a2e19b519ad199f193f193b1938192c1927191e191d191a18bf18be18bd18bb18b318af18ab18a618a2189e189d183117ca174a173717311727169a1696164a1640163b162616251622161e161d15af15a9153f152e14c014bf14bb14b614b014ad14a3149f142213c013bf13bb13b813b713a413a2139e139d134a132e132712c812c012bb12b612b512b112af12ad12a912a712a612a4129f1294128d124a1249124612431240123f123e123d123b12361231122f122e122d122c1229122812271226122412231222121f121e121b12141212120f120d1205120211ca11c411bf11bb11ae11ad11ac11ab11a711a611a311a2119d119a118211481140113b112f111e111d111c111610ca10c710c010bf10bd10bb10b810b710b610b510b310b110af10ad10ac10a910a810a710a610a410a210a1109f109e109d109b1083104a10471040103f103d103b1038103710361035103410331031102f102e102d102c102b10291028102610251024102310221021101e101d101c101a101810030fbb0fac0f9a0f4c0f1d0f1c0f1a0f190eca0ec90ec80ec70ec00ebf0ebb0eba0eb60eaf0eab0e9e0e9d0e970e4a0e470e460e400e3f0e3d0e3b0e2e0e2d0e2c0e270e260e250e1e0e1d0e1c0e1a0e170e020dca0dc70dc50d490d480d470ccc0ccb0cc90cc80cc60cc50cc40cc30cc20c4c0c4b0c490c480c470c460c440c430c420c350bc60bc20b8f0b380ab80ab70a470a420a380a370a340a310a2e0a270a1a0a1309c009bf09be0940093f093e08c008be084c0840083e083c083b081a081407cc07c907c807c707c607c407c307c207c007bf07be07bd07bb073706cb06c406c306c206b70637063505c705c305b705b5054b0549054705440542053705350516051404c904c704c304b704b5043f043e043d03800300028002000180010000800000 else (if i<2 then 0x5fad5fa85fa75fa65fa35f9f5f2b5f275f1e5f1a5eae5e955e4a5e485e435e425e365e2e5e2d5e2a5e235e1f5db85db65db35db05dad5da75da65da25d9e5d9b5d4a5d2e5d285d265d255d235d225d1e5d1a5cca5ca75ca35ca25c9e5c9a5c995c4a5c485c475c465c455c275c1a5bcb5bc85bc75bc65bc45bc35bc25ba85b385a9a5a1559b859b7599a59965995598e593658b658365795574b5744571a57165695561555b655ae55a755a3553654b854b6544a5436543153b6534452cc52c852c652b65238523651b6512450bf50a650a450a250a0509e5037503150244fb74f4a4f384f284f264f254f244f224f1e4eb84eb54eb34eaf4e404e384e374e354e2d4db84dab4d484d384d264d244ca44c224c164bc94bc84bc74b1a4a944a2649be49a2499a4995498e498d493648ca48c848c348c1484b484247c647c24738471c468e462a45be45ab45a2453644b6443e442a439643944349434842ca42c942c842c742c642c5424c424b424942484247424642444243424241b8413e413b413a411a41174115410d40ba409a4097401a3fba3f9a3f403f0d3eb13e8d3e343db73db13d373cb83c0d3bcb3bc93bc83bc53bc43bc33bc23b383b363b143a963a2b3a163a1539963922391e391638c03896388d3816380d3796372b372237163696364a364936483647361e35cb35c935c635c435c235b33596354b3548354635433542350d349b349634903438341b341033c033bf33b833b7339b339733963390338d3340333f3338331b33163310330d32b8329e3296323e323d322f321e321d321b321432103209319b31963195318f318d311630c030bf30b830b7309b30963095308e308d3086303830373029301b301630153012300d2fb62fb52f962f402ebf2eb62e9e2e9d2e9a2e892e4c2e4b2e1b2dcb2dbf2d962d402d3e2d3d2d362d352d312cbf2c9b2c4c2c2f2c162bcb2bb62b9f2b9b2b8f2b8a2b892b862b4c2b4b2b492b472b442b422b402b3f2b3c2b392b382b372b352b332b312b302b2f2b2c2b282b272b262b1f2b1e2b1d2b1b2b1a2b182b142b112b0d2b0a2b092b062b042b002abe2aac2aab2aa92aa22a972a4c2a4b2a4a2a402a382a3129b829b1294a293829372936293128cc28ca28b828b728b128ab28a928a4289e289b289a28942889284a2840283e283d28362835282b2828282628252822281e281727cc27cb27b627b027af27a9279b273f273826cb26c926c026bf26b626b026ad26a6264c264a2638262c26242622261e261b260925b625ab25a1259e259d259a2589254a25492540253f25382537252f252425222520251e251724cc24cb24c824c424c324bf24be24bc24b824b724b624b424a924a724a624a324a22494248e248d2489248824812480244c244b244a2448244624452440243e243c24382436 else 0x81808100808f801a7fc97fc87f467f447ec97ec87e447e427d9a7d1a7cc77c387c1a7bca7bc97bc77bbd7b0e7a9a7a1a79c879c6793678c978c878c778c678c478c378c2780e77b677b577b1774b7744768e761675b675b5754b75447542748b7435740b739a731572b1724a720b71b771b1713b713071157094708d708b708070456fbf6fb86f446f426f0b6ecc6eca6ec96ec86ec76ec36e486e456e416e386e346e276e1e6dcc6dc36dc26d0e6c946c366c156b946b496b486b476b366b356aca6ac96ac86ac76ac66ac56a406a0e698d691668c068b768b1688e68406837683167b8673166b6663665c0658e652764a764a6649a64286424641b63af63ae63a7632e632d632863276326631e631a6311630462b662386236623061b861b661b361b061ae61a3612e612d612b61236122611b6114610260b660af602e5fc05fb65fb0))
def jc11d4b (i : Nat) : Nat := 0x1ba6e5b86ddb66d5b46cdb26c5b06a5a869da6695a468da26859865d966559464d9161d866158460d82605805d9755d1735c5655916358961551535495150d42505324c5212e8b92e0b72d8b42ccb12a4a8298a5290a12609524c912148320400
def jc11d4 (i : Nat) : Nat :=
  let x := packedAt jc11d4a (i*16) 16
  let i := x % 128
  (jc11d3 (x/128)) ||| ((packedAt jc11d4b (i*10) 10) <<< 30)
def jmasks11 (i : Nat) : Nat := 0x1ffeffefff3ff7ffaffcffe3fefff6ffa7fcbfdffeeff67faffd5fe8ff37f8bfbffdefee7f6ffb5fd8fe97efff7dfbdfddfedff3ff7ffbf7defef5f6af7ffbfbdfbefbf7bfaffbffdfeefef7efbefdf6ef7f7bbb7fd7fe7ff3fb9fbbffdff6ff77f9bfbdfd6fe77efbf6df7efbb7bfbdbddfedff5ff9ffcff67f73ef9efcdfe5ff1ff7ffbff5ff6ff97fbbfd5fdefed7f5bf7dfbafbf7debdfdefaf7b77fbbf5bfedfd5ffaff57f6bf75f7af7d6feaff3ff9ff4efe6ff1ff8dfbffdffcffc7fdbfe9fecdff
def jfields11 (i : Nat) : Nat := (if i<3 then (if i<1 then 0xe45df87822d238a11563dcc8a0347244e2c98225114d9118535c881934e43dc8de21cb1f810d6d3348607a4e42cd570214515f909080c0844814c41d773f20c1a139050bca08213df040e0cdd204125c1015b0fc80171303fcfff41fc90af0fd21d347e022803ee2e331f483b38f9183d07c31ce63dd46f81ec9b220f5807b07a38aba3cc5d741e4daa68f1129d8780d9ec3bd2bcc1dd14e58ed3ede0762bae83ad9c4b1d45e380e961500743ac9e39c77741cce32b8e58175c723493038dd2581c45f8b02638fd070c5b1838194981beaa938de8555c6e98d6c371fa0b1b630ba0da669006c9ba4e361a69f0284f3a0d7159d86b0874e35470f61a8180d8d31c1e06929bf0344d7701a0fa3a0cf12fd86707c4e3361f9b1743efa0cc433e0658356e328e0f419217130c835fc06394d7e3195fb018a17908c49103c61be2e83082ea41826e538c03819c5fc16ae2f8ca8117ad8d38bc45c9c5dc3d3e2e8de70172f06b8b892c505b92ce82da3ca616acbe20b414fd85994ff02c8decc162d3110b079e9c57c4c4e2b8aa3f15a523c0ac1f5305588dec2a874d615282c08a8409d053a6aae29a20a814ac24a0a43bfe051928d82888cdd142b9a60a02d89c4f9d898278477413aa2bc09c2069c4dab6e026a240c1321e3a098917284bc9b1e259a03012ae26e8947889049934e624808bc122dbaf09039dd0479ede823a1e2811a1d3a08c4ab5c458fce8228a0f8113083c0885e5c0439ade0218766410a7d7c0842f28441930ae20902f4102979388059a983fa9af01f8b9130fab6a407c56e9c3d9687e1e9f7cd0f241bc07818bd03b837621d86c630eb1d4a0747a3d0398485a1c950ec0e2aaf387023f74378857e1b8b79e0da79d386c628c03597a3c1a8a14c0d22e7a068207d0338491619924f00cb07fc0645f7e0318c9e8189b9a80c2b7fc060547c42fa10e0178b6a80baa56105c8a1dc2da4480168cd270b20d200580e7d02bbf5d815906700aa14668548cf3829a4dba148232d0a2f76b8500cc5c278c8e8139bd7109a7eba04c565e0258ede812915bf092ced80488ac98238137c11824bf08a462e8440a890219ce98109cf9f083086b840531e01fa4abc0f9dac507a81ba03c7a9e01d809660e8e16e0722afb0381988c1ba754e0d8857806a2bdf8344d73419986d80c9cadd0628878030519e0179cde80b9f06905a649382c8115c15b4a280a9dc5c052b9df82890f141397b3a0982d0c04a233a02454d3411c8a94088262c042663802061a240fb308e079097003a2f7a01c6af000d948ea06a1ad803287380182e9b00b8894e058f5f402ad44b01405e6c09909f004a3033022b43801050778079ecd203a3c4d01aaa3c00c6ff680585b4e02811b5012dad30087406c03c00ba0182f2700a11d68047849c01c575000959f40024536000 else (if i<2 then 0x82a29447c1143a78a89dcdc544ca23a22533dc1121d9e888dfff844469782218569510096ec87c4bf443cbf93a1d621cd0e0c0e886c4deb4348aa621993e410c1394e85e21cd42c32ba2153c5310a36c6084cf24c424e65fa1100011080767683d841841c49e020d89c31062e5e082d7e704140041209092e4131fce88221c5640f264c2068651102881f08101eb140614d32024b4fd00a34ec80106f03fef7b61fe75568feadd987f0fbf43f615cd1fa13bd8fc8ece87e226a63ee84781f683b5cfa8cc4e7d12ff43e6ae761f26e1c4f8a4e287c058763de1f781ee08ae4f68e6e87b1a79b160d71f9eb06cccf5217e07a4ccf03d088139e790a6cf3233ba79518743c899e61e3086e4dd410ae78875743c213c61e01ddd4efa62f07798d4d3ba773c1dc75b68eda52f0768d3f03b2cbac1d87c3d0ebb0492759e69c3aa12d81d480b14e9989d828002053a4351f9d13d9b0e828ff073ca85239cf5939cd6fb70e6297f072d6e6c39509ab9c947fc0e447a4871c0a3f38c407a1c506f00e2286e870db38738499a21c1219e0e04071a6fc2f221a6f1939be17fd0dec14ae6f06c613760e599ba3ddd0dc9f0dc6e23fa636e41fc1b61629cda86ff06d068f8366a5661b2385c0d883e5614512dd360287b1af523e0d71f1f06b60c763588a661ab80500d53b0b66a444273511c999a74a1e0d30a4d8695a58c054f27a1a40dbd8d1c128868813b3342dbe29a02acfccfb671867a005e33af67c19c106fccd8d7e46696bc8333168b1983669ccb9a9e06586aa732afafc1946cea0c9b0b186490cf032223ba9901a1d0c786ee8639ca7831a727a18c6fd14c5bb9666291df431286bc1882e450c390df06180b3e30a02991848bca0c1b7c366085b743024aae9801f1d0bf86be45f9a91b2fb006297c2f28813075e85ee478d2f43b329796b5e0bc0c4e85dd98b72ecf0d29756ea60ba493285ccaeb62e4c8d817119f90b81efe85be330c2dc87f816d4d560b63b2365ae2a992d427bb16933de0b42efd859d89f32cc1593965549c0b211fbc58d5c272c4c83a161577d0b017c3457caf2f2bc92f215d91ac0ae0d6ec56cdbf42b49b661591f3d0ac0491855df6782ad2607155262fcaa31bb454d20702a5224715176830a833d9653d3d7829c2b5e94d06060a63b33652cb722294397a14951d48a4265ae51c787428cd90a1451c2fca231d1850dc5d7285175394154e9ca011c7e4fdcf4527cd98413d00c0c9e35bf04ec4aec274091993926d5c9c17e4e4dc26ab26ccb62135403d09a1519a4ccfdf4264c57993131bb0982d6984bcb89725c095c92d2b6c0961fee84ac697825462361294b2fc940efe849ddc1924cb4d8125503e09232a2848d49cd245274c1217096490296f047dd2c523c36bb11d01efc8e0534a46c97d7234f4bc1190d9d08c1734 else 0x49c85928ce8daa7673118c3388a8819ba41bacd88aa766aa793b345895d9987fe0cc94cf8662cf1833084be197c9836cb8162465a977632c4efe195be7e8ca999b0652b365b281ebd593a34eec99197064a7c6fb248135d91970344b9b894644f1cdb210c62d9034260c7ca95263c492f31d79685473b1b6c705af4636fa7a31a2b1d18c890e8c61fe5762e85383164e89d8a906c8c5198ac626495fb121afd98888a4ec40e87461e2c93b0e179a5869d7d8c30a1bf616e36bb0a2230184c7e8ec20b2b060ef8eab0655f3582b6650c11f6f8606a2783020ce9d80a4e4ec0215a65fee8462fe4fa157eaf0e8bf248145f6160bafa753157c9e1f0be235445ee557c2f668a917a9ac9abd243183cd10a6af323afd790a0ecbc4d3705e090dfaef86ec177494d4bb550785d90c622eb7987975266aeba4e3745d0511fae71fef17340eaeb960e575c928032e3187d17149728b8631065c05a5fadf02ef96f184d8b7476755b83fba2db4a3e16d22fd8b65713f5b015cdad739eed6b3be18b554e785a802dfad33ac15690c7e8b4482785a0dae5acf4df5d6700500b3582a75989d93acb3e7d165137aeb2527a7590cdf52c7449e163397bab1475f458800c2ac37ffc1612e978b04311358077bb2bf501b15f3c650af51ff1578d40c2bb3e1c15d1eae8ae4223957076fc2b75eafd5b412aead47227568f63c2b37f7755905f3cac5908856039fa2af6591d5741eaeab420b9558f209aab9365155196e0aa5c345550dee6aa70549d532929aa943cf454881d3aa374715510dfeca8449f6540363129f5fe994f2cfe8a749e785391aef29b2f86c130867ea6907f05326ffa2986edcd4b95a60a58fecd52b1b862941edd149b9da2a4a00dd523111429001afd47bcf2aa39027851a8d62a8c52b354597b4ea29477851238bb288847e1439724ea1a17d850a2ebc284861614195f7ea08a73f5030c6c2805a6fd3fc65289f93cf84fafe2ba7c18dd13dc40302ea4b914f4d0d3a7903adc04c6da69e07af44ee48b82763e3853aba89a9d1f2f44e6c04da720aca1389b3429c16bc94de5f4ba6e295e136a95a49b1e5a74d6055d26a8df4134898f09a090dd4ce6d13a66036f1328086a991243f4c6bf582620fdd130b03e69803097188e0d9a5f477d52f21ee09742c934b8e5aea5b12ba12d23c9896518f44b00a19257849b12b3c34c95427b14a80b8e813513e129afad89494fa74a2267b25085d11279c3e8939c04549af1cd24c2fca125891e8929763f492ba7a248579c123c072e919624448a397aa4433bbd21b473a90925e5482d18fa40098c11fa28f08f8925d47a37bb23c05a7c0983f548ecdc704750d13239227b11c19ce88dc113446c54fc235281491a071e88cd36574649c6ba313c1d9181f1e08be2ea845c7ebc22d2ccc11615c988ad4a4d454)) else (if i<4 then 0x6db688836304432669e211c8e9104d3ef8808213c3f585321f3c53c930c82787a40ba43c1bbda1da83bb0e858a58730f8e8ba5abd21c24bf10dc526b86cf0d3c3580d621a28bf10ce0bc486429bb43182b5e183f6e90bce57485c0f1942d2775e16077e90acd2708548893c29291d2143c638930c77484efc7c426361c212a3abb091b38a846bdf64227b75e1091b990804e7683eaf6641e034f20ebf24f070b721836713a41a2715e0c970363fc6bf483067fa4178b06e0b08f170550b708285b5241359bda09237e10450af08202b5fc0f3b5e20741ae90363628818a0bc40b219920524629025aa148102a35c0776f16032eb6101552f880832fa4034425201135e9005acc580068f83ff48f305883a626e967307fc441fbfd07031fe3878afecb2bf7f52479bf924b01fc3e6e8fddfed77ec154f1fa5a8c1fabbab6fd0e0667e7224a3f21b7d9f8c1188fc1634d7de14d3bee1e3d1f6bc060fb2419f7d6055f3ea70b15f49f1c8fa1f7787ce952bbe64e531f292ef0f90d6707c7026c3e2630c1f087ef0f802b1c3f42575bdf155d9ef3254cf74b5a77b8c9923db47375ed3d0ecf663bc37b0f38d1d509501ebae1f0f58c16c7ab1f63bd4345c1e99124ef487dbb7a226bb3d055d35e7c843a799694c79cd77c3cd319b1e60147af2da998794a17c3c928fd1e4392b0f1dc84478c1613bc580991e205830f0db39b7842b7b3c14e535e006318efc8d4c77d25653bd8e891de3588aeed941b1bea23c3ba9386ddcab0f0ee21ac476ee8923b644d75da9a7eced21cb0766f72bbb293235d8a60e0ec0063f2390e933af59135d71b1e0eb43b3f75834dfbab5a331d53e4a8ea595b07508d6eba76ade1d31617ee962514748631b3a315dd9d10107ce84113574022fb39f38bd1cf04f80e74c8a77389713b9b85b35cd09fece647678730188a397471c1cb3828ae553e3f7285b93b938d361c9072e8e445df472058dfb8f3b04dc70d8ece3575cc718194d38b37cfd31a7098e2971bf712932eb880be7dc398f4ee18edf070ab1ba3847905001adae0e0dce5c7044af23811c7c9c0216f0dfcbfec6fc8626b7d48701be44728dedfe586f528433798a505bc2d7e0dddb40c6ed01abb752ccfdba1647edcd16a76e4321db7166ba9b80b7d2dbca6436dc52e936d4d09db6278f0dac9d276d4a1f836984549b4401bcd9c34a76cc417c3651efd1b23d3e0d8e32306c509fa361040d5b024f18d7df5646bc42f835d4b6fdae1a1e0d6c0f376b4f7d3b59281e1ac39388d5e4d146ac363235591e61aa0cd4ed4cb6a36a4dbef351731e1a84719ad3d437869c065e34d62369a603b66d2c79e16947e3a3498155da413ff0d1d30f068ccd9e34558ac1a23244e37c3098686a429342458fda0a36d8d00be9804c581fb3f703159f17d4ecf556d267866f833b03ed else (if i<5 then 0xd4d052c6a61d84f52da41b480116054a15fdaa486034310bca7a90b0e65477e4a2a33c4475143da7a888f53d432b2fea1031195061630a80eda2d3f1d98a9f3073e838cbe7a7a7cbc53c8a89a9dab47f4e8f402a729b93d382af4a9b8e9ab4d88074a6a7c7a5347f5e299acb994c82831a6260f65302477697aeae123239a7a5c84f852d0a49e96317e74ae19b0a54c08a529084f2942d86149cc5eca4c039fd25415d292070e548d31d7a4478f25212f1e2901108147d801fa3cd79351d2eb328e1898d46dbbdaa34863851978a7d90985d94605176a2ef6b651689fde8a83a814512f14a265dfa51247c9e888cee94418951a1f1eca50e86d1286acd4b4300abca170a2bd0a067d6849944f421afb5a0e2574d061d1d282bc63b4118588a060ca6d02357c280a0a4f4015aa79fe20a64fe93daa7eaa3e13f1c4789f6993c4fa17dd27c8def13e170709ee7a7a4f6224a27a854473d05bec9e695bc4f26c29e78bbc8b3c1dfbc9deeb864ee49b16768216b3b234399d7126f4ea241e274c412c2ea07d79d11da1ce76e4f27319de1394093e01324974e460c9271b4e3b389b2b09c2c3054e02cefe6fb3ed5378f0789baf2abcdc030f8f32009b36c993f9b523094d98235e6c355e735d673f9acfcfc42625be26a87a47350eaa79a65b53cd254e4e6886ae9341996d99e74b24ce2f670af8553eb5cc56c99a733a4cc904926582279328cd1499268384c80c89e63b3f793182d0b98a9ffc4c4131da61a4abb30815a698304ebcc01f6f25f987d8280273197d1c19cbd583325e11e7f2ed7a3097506fc4b936c9e5c0563ab5c847096ee9944b6397d25ab27452d2308c9664a5fcb2674f258a03e92c08bf895ed8184ae21f3256bcc4f2b172749565dba4aa5953254a844f2a1cd5e94effabca6101e252a39bd2916cf494625f94a25dafe50abe7f281870c93e9fbb49e5b1324e8266a4b59130938ab7c49b5b0be4d2dbd9264fa7493112d34974e7e24b27bf125459f492917e74938195e49202e92458607920051f48f24cfe472c0e92357c7091845ba48b3a3c2452a2f12240e3c910ce754873cbd24305f4f215563f908d0584838a52e4115961204a33f900ba3647f2e62e3f374371f425398f8b15fc7b599323d38f4f1e631de8f074fc477563e23b3444d1d4b62525c94eb88b485163a181d91cceee48e4d88fc7171d3238379bd1bcb7288dc527c46d8a32e363f9ed1ac7ef48d4863c4697477a340ff8119e4c948ccc59846553fe2323715118c3b748c401c04611d986301f5e917d79b08bcc7e8c5d171d22e0ffe916dbc598b4f56bc595b3322c43b6115d7a4c8ac803a4556d4c22a21de114db6f58a4be5fc513a932282c99913e117889c6a3844d108fe264455112df97884c5b130ff5bfd225319e7124d970890297b4479009e2316a67115 else 0x11f36d7961fcebc2454f5dc493faec9fbbd75530feba242bb5cc7974ae4a77c57127de2b806fe95bcbf152be2a7b56e437c212aa9f15b61e22ad8eaf8d6b5ecfeb52f1735a4fcf4ad07993d6744f74d81268159995c0aca1712d641f6feb1c5e495896f70ac29a53d6081b5eaf85d475787a74abaef62d5c377d2ad8dced569ebe9ab2329dd582e632abbbbb755904a70582d34d55301b2aa0a3ed54cb13faa4ebc65514b132a84962753dfbf8a9c1014)))
def jFields11 (i : Nat) := packedAt jfields11 (i*29) 29
def jRecipe11 (i : Nat) : Nat × Nat :=
  let x := jFields11 i
  let i := (x/2048)%128
  (jc11d4 (x/262144),packedAt jmasks11 (i*13) 13)
def jb11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xa52890a4e1949442918851f20a392946a428ad451298a1f3143262850a502bca00293f0827bd24f5149e6213c44278044e9b49cc393888270084dd189b621364426b884d22899f293364266064ca1098f293107260ca4bf9097a292ec425c4a4b70c967392c83258844ad2094f5929452501449a3092d3924892474e487b890c1921042408c47e948f7311de8239d046e2c8cb8918e422f9245aa48af31158322a0844d388924111a5222864440887c610ee521d444381486e110d252171a428ac84849082720d1a4188c82e1904e7208c840e9880d8100e6201063ff947f170fd281f8cc3ef147d450f9e51f28a3e2947bf30f7641ed8a3d8947a370f4031e5d23c91478b38f0e41e0c83bda076f60ecc91d84a3af0c75c10eb041d22039e3073820e6271cacc390a871b30e3031c5083852870528dfa81be0a37a106f118dd851b98c36c386d138d9851b18c35f206bb18d6681ab8a354186a328d4031a5943498c68f20d1451a1883418c67380cdc5197de32a2c64a50c8e3190c83200c63b28c6a618c483170c62b18c4681880630d9461720c2641838a304185fe50bf4417d4a2f8145ee10bd25179c42ef245d548b8ee171062df945b740b68316c082d49c5a618b4441651c2c79458930b0a4160482be9057638ae44159982b11055470a9e5152c82a31454220a70a14bd22960c52820a38c1451028338502209fc413e4a27a904f0289d271394826f1c4da209ac4134882659c4c72097e812ec82563c4a82094841280824d9449720918b11f9c23b9c473208e03119d22319045a4889cc112882231044220876710dc8218984218083a410648209984111081851018c1fe283f4407e040faca1f3903e2287b480f50c1e8103ce1079060f0ca1e00c3ba3076e30eb541d3983a22873c40e6881c99c38d3071620e2061bd38375286dc70d9141b01035c206b230d5861a5ac34818676d0cdc8199903301865c20ca88194083251864240c5d41899030e2861250c10a17f942f6485da90ba48172902df305b640b5c8162c82bb5056680ab8a1513029d28520d0a3081429c280284db30995012da8258184a460930c123182422047c408e4a11a1423020458408a84113102231843a60864810a9020f30414508188101101fe203f2507c8e0f7101e5483be6075d00e9901d018382f06f0a0da9c1b0283546068ce0d08819e1832e7063920c58c17e682ec805c0c0b708169282c470574a0ad0c1505029c20505a09e1413a1026a504c48096901292024a40480a08e101134821e4042c808390101301f8503d8c079100ee201d630398a0718c0d6681a250328e063100c030178402e4605b0c0b12815850298c0501809d181324024cc0480c08748104501f0c038ac06c280d230185002e1405918094f010ce01d2402a80040a0074600b98008780008 else 0x9946c5a8d0451908a310945a428b02513d2a260d4491a88a450f8ea193143012854650988a111141e2282a950350a00b13fe1a7f444fd889f98d3ef227d834fa089efa53db227ac54f4889e4a53c71277c94ee889db113b222750a4e69c9ca9538d4271244e1489c01537a326ea54dc869b711368326c654d78a9ad113524269864d1ca9a09933c2a66e54ccc8990c931752618b4c20897fa52fd125ec74bb909758d2e81a5c464b70c96b952d13259664b10e9608d2b94256a44ac0a955952a43a53694a54c9479928a2a50a549f5093b1d26f3a4d4549a0492c412532a49c54924a9211d23a4246a548ad49129921e3a43064844e908052055a402447f488fc911f3323da647a868f19d1dc3a3ae5474c88e5251c71a382646f488dc151b32a352a468128cd951972232264630a8c29d17e3a2f0645d468b89116d222ce6457d08ac99151422985452088a09d13e1a276344c928959d121522385446088889d10b3220e4440c887e1d0f91a1ea443b8e873210e12a1b0943508863b50c03a176542e06859190a18a1309425468489108b3210e44204c83e910744a0ced4190683011056520a254130a8248d0461a084440f4a81c150332a05e440a8a812950148a01c6402888019cffe29ff443fd0c7f794fe931fcc33f84a7ed98fd629fa253f09e7df10fb929f6663eb8a7d320fa129f3a43e5cc7c81cf8b29f0e43e1827c110f7e21ef443dd887b894f6d21ed433d94a7af98f5a29eac43d4887a59cf4629e8443cf4a79c14f2f49e5833c85678a34f0c41e00c3bf0877928eef19dd263b88e76c28ed329d9c53b24a7630cec129d7a43ae8675b10ead49d5243a8cc7500ce9b29d2493a2ce74298e8121cfc339e0c73994e6b41cce43988a72f8ce5a29ca86393ca72514e4339c78738e0871a10e3021c565389c871098e1a39c2a53831270030dfa31bdeb37b066f318ddf39ba4d372146e210dbf29b74536d0c6d528da719b483367ca6cd90d9531b07235d1e6b908d6e21ad25359486af98d5741aa83354086a49cd3b71a6e434c4c6970cd2b19a42a3474868c14d0a719fad33cd46761cce7299baa3358e66910ccb39986832fc865c98cb619956b3279a64b9cc941991883220864210c7d398d72319c863190c5e298ac8313526231cc412986ea30c4c6151cc243183e53068a608a4c0d217fee2fdd05f3c0bde497b252f50a5e88cbcd2178e62f00e5de8cbb54175c72ea4a5ccc0b914171a42e1cc5c288b81216fa42de0a5b6acb69216ca42d80a5af08b5b196ae42d40e5a68cb473168262ce8e59a18b2b4965032c88c58d20b171962262c30a58394b00395f652be0657a10aea515ce32b84c56f0cad6415a062b15655ea0ab82956652ab8a5539caa41953882a49454710a8b19500b29dd253a88a6f314d8329a0853118a5e214b442954) else (if i<3 then 0xd33cc2c79786f2d8de562bca4479388f2419e413bc6ea788aaf0e95e182bc284783caf0591e062bc06377f4cefd0ddf433bde577a4cef291de123baea7740eee519dbf5bb72676d0aed719da833b3ca7664aecb0dd9223b186760d2ebf15d7b1bae2a75b0aeb395d568ba9a975248ea30dd412ba76674d4ce9815d2463a3c674514e8811d0c23a0a774048e7e91cf5439de673a8ae7311ce2239bc4736c6e6b91ccd5399057308ce5f11cb64395e772992e4f9dc9933928572408e4595c862b904471f88e3c95c73338d87719cae3115c5e238aa971312e2411c451b880570ecae1b15c2d4b85437094ae0f99c1a2b826770406e03a5c032380226ff0adf9a5bee2b7d446f75adeaa1bd12379856f246dde35bb82376276eb48dd415ba42373e56e706dc9a5b911371476e0cedbf15b78336e846dbcadb515b66236c066d746dac15b551b6a056d308da221b3f2b67646cdc8d96a9b282b632f6c548d8891b0c2b60e56c0c8d800daf4635dc66ba4ad7215ada535ac46b488d6809acd1b59246b0ccd5f91aba2b56c46ac88d578daa83b54656a806d4e8da944b514a6a1c6d4099a7d234f0569c8cd378da6b234ca6697ccd2d91a543b49696918ad2019a3d1b46e668d06d1985a2763446468844d0ca1a133341a667f60cfd0d9f52b3d4b6790ccef199d54b390d67108ce0119b74b36a266c0acd1b59985b324666388cc1ad97c3b2ee565d06cb62195d7b2b0565546ca7999483b288465084c9f1193a23260a64a10c93099231b238764456c870d90833206563f4cc7c918f61b1de763916c708d8de1b1b06634cac65a18c24b170a62ccac57918ac1b1504628cac500d8936b11c562288c3eb58782b0e2761a50c319985c3b0b236150ac281184a3308e3610c8c1f9183b2305706098ac109581d230305602dac00a97fb32fea65fb8ebf2a57de3afae75f48abe6957c922f8855f084bdf117ba22f6e35ec8abd4297a232f3c45e6c6bca997848aefe55ddd0bb81d7693aec665d70ebac8d7542ae9a75d248ba21573d3ae6a85cc48b942571d5ae2895c3cab849970712e0835bed2b7b156f31adda65ba48b72916e312dba65b60ab62516bd3ad7055ad08b57956ac1ad4c65a80cb4e8d69922d2a45a40ab45956824acfa559e0ab391966282cba55960ab2a8d6502ac9a35920ab219563e2ac66b58b8ab15116252ac3a85858eb081960a32c0a558048afe155fa12bea557c0aaf5195e622bc8257808aed955d43ab9e5572c8ae3915c41ab78856d10ad4315a232b3a556512ac81158a32afcc55e88ab99d56e2aad06558caaada15562aa94c551c6aa20d53d3aa72454b58a93995222aa38654646a882550c22a0e55400ea7e114f15a9d665379aa6d8d4d81a9a08532caa63914bb6296a652cc4a57914ae0a944c5274aa48b148d22904b51f4aa3b else 0x20fe1c1f6383e0707a8e0f21c1d298390b0708e0dd241b438331d063960c41c180482ecb05b920b32415878294f04f9a09a2c11cc822890421a07f2c0f4581c910342a0651c0bc78168902b8e0503c09278110b01f960345c05e5809550101601a3402a58038f0051200243ffa57fdccffa0dfed3bfd247f90afef19fd643fa447f34afe491fc143f7097ec8cfd239f9a53f2e37e1a2fbf9df7743ee457db0cfaebdf582be96d7d244fa199f3a4be5eb7ca8af9219f211be3857c5caf8899f0943e0287bf86f7d11ef623de257b996f7111ede23db257b548f6799eca2bd8c47af90f5c95eb42bd5697a94cf510de9c33d3047a44ef4599e862bd02579e12f3995e6))
def je11 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0xc144b0042a9041fd9b505b33e1897b82268983378cd205cb3246d4507f138232d1ff6261a394616a4db25c02551a26280c728ea6cdbf15c235c98929c37080c41b9a659d15128765490a7fd897acc92851e541a21c5ff6248b3b8336259e084fe624af03dc54710e259a00509d1fd2f278cf68a1d82dfa789cb6fdb869d60578e2099a8264885419f2d61b72db569cf5329a9220e85fe1e801df02c081290a795b8728ed1fda2861ec6fda7325141150d1a8b8689891b45f1c54168a007b9ec7add6749cb325975a9705a07f85cc5689624c52d3b4560cce8625675c9524287f876007ade97a1d672da13493f470ee2904b1283e0c57b67e067b0ca1581e03887689cb6296d3246d450262d1ca1fc125749f7bdee7a0cf1fdca644f536c97305a272cc921cb83599b8008612d893e0aa08c0c6544b0801b5d21b1a9541c1b32acc72b96912d723a088128637f914139890188645dec32424871a262618650ab09deb56808796007b0ca0980c6884e0980e1304b7588e301a2850234719f3d4a15a9896a4da1154b0221d85dec3840e541627ac8b08d89861ec6fda7325b64046a33e1a759b8698ef6261b708f508dc5468700b47f158856cdcd22d1a7b9e972dc86e1b46294e470040091a404d61c5411e8534e49686dcb3d49d620536cda34c41e3f5897b13f03802625a282d293253f3e0355fcf868820505a285deb0e012444cf58a1a849ec759c159c14549722094668a1e8621769d322582e31df87d02d4287f869e873d041a97d1fd1b6014114d9f3a0c46bd1a85dbf7cc737298b36c971f15479da285dbc32c7f5fcde7c1a27546d7b519751b3159ff6247f67d8972dc66d5b43d5c346421001706cd891fd2c08c0c0cc9f7291a72dbe0789f5fc2203c086752f1cd9b624e110159624db14d6a625ff3bcaa650813d52f66d89869c659c3065c7f471ca66d2c084fd6261a6f91c68a083edd1626176102d161597293c4c4713a18924c570b40e589ca6fc871a9898481c5c9891387f5fc3603c7d5488667c7168a187b1bf6f1a7325144346a208b86898972d6a0cd727b5ec4a4c93286a4642d43cb81e17f819fe20c10429ed86def1fdb325c4625831018d68298e3f4231288b14c20505b37b06a08804641894b0ed638673a189008d6689bf08da86261821c7f08d52689a24687f862127b9bf4fc8e0e5275fdec30d3142589861354d0c01b8c46d1b26458a2840443c431c5896885502c4b0b44a12c4c12a177ada34ed112a06358a120508b6a58936df068a0b789cb6fda76282d6a556440961d572424b487a177ac751a90a58a1a85dbc6b9414047f548eb86e187bdec709671fc2c0ac2312c146a55242989861ec6fda73259727c883c5274b0fd6260b2ac8b6a14e0c615851ee7b1eb7a5bd5a0822044a0781b2d156680655911c22c7f05172 else 0x5099a8264887fd9f2d60b799293253f2ac93098f80d57f7b1c7324c724d3f564f11c02d0b5706cd2c0ecfd6260a0891a80131379096251c2800f420b0208115d04e714310b589088b527e1d69c594fdb6404b51a8265c9a24c456081d96ccf5028986261e051a925a1b08814048968618072423621c572cf53246d4504e080b87fd894c41e3fd8977c236bd406252f0dc5e351a25c8733680d0202d25c4a8061877dd64c0c425014795ca284831b5684506f17dff6261b869ef7b9eb72dc768519084191b9ca158ed3e1ca7b8ee2a8234521a7e9eb6dcc91cd1a67e174959f85d1a4298986e1a7bdee7ac2c625a72bc9c1fc506617286e1885de84bd1c2ec7f0ac043291e2c9a915d57468ea6ce187b839434b85fe006d04a3a830558716cc810dc88715cb4504e12c2201189099190484e8760f819fb7bdec7adcb585111fde586e17259ca869fa73dbf6f9b768d322ac26081011851a29c391b91c71519548706a55b08a0c54d412086f519a284a0b6293f28889098f80d57f849ec759a7698404292c6247366d891fd025c5b37b1eb6e1955108e5a114080737fd896f9b86d07427d19715af86def7b9eb72db5629ff238210646e32903294f10c56b22c21505a245c8b0f4b86cdec1fda26252c140143d9894bc9614c200110a5fe12051a9625e9759cb2607f0ac1229c37328317b12f405894bd88419a272db56b12f300e86888b2e1015fe1b7b92f45c53074ca6cc4a67c3346a0b755cb6fdbc6e1a7581316a1b9138f12d47f5508266da2849156a5890306f5a9892a891078fe5fd2b18cea6261b861ef69d6708c14429526a58987e1885e12731a750c87145570b50a1fd897a1bc628661587f72a12261a9624ea5a1a2801cb718301a9681fcca66d0229d096cdcb3d4c90b4e81bcb47fd89825ee5dd5e538ee12c086a5a25c8b47ac23119b369c3f3c589680881fd89861a7258873b474864df0307b624f50c11a379ab6cdec7add073dcb6fd8a639553882d259e35c9092d11a0d08867d2f40c7f624f52747f0b4140b082625ec6fc236a189861cf1b59f27d27861a74fcab0ac0821cca4287086e177bdcf0c41e5f51b45c2b3a0ca86c1a5912768a1b4c50a5fdc73d40626db33d4a120c8b17ded3a18945ca722c5312db3088fd469ff4fc26849d611572549a27ad75715ca46a172e1723844004800589895a873625c25f1671b44a08d414b10a625a13d4c9450026261b59c962e1a2719806248186cc03a9a2856147b9eb71c667fd580cdd14a9427298f5fd881c5a2861ec6fdbc69cc94509819cec200b468989110a92408168a1768d2f055c5184ea869ec759a359cf8810e05499f6391419dc50ec030c5a229033129881cda286dee7a5cb8654b4684a550371f04e0981b7bdee7b1e973dcb6298e1fc176cd722e157184ee6cdee3d4986c) else (if i<3 then 0x75b336c126a5a27e1592a0965a6007b1eb0c04a7b5e736838564b8624ae0b4c768a002901c5a1a25384a2583b77c326bd406261b72d1a849d652d303e03b5fcfd6a1a2578ca85deb4b0900f1a518d627bdee4bd1936c6e0842d1597d1fe1b7ad623a1a986e18851cb3d421351a92210a86dee759a75e5671fc2d2c9ca5c97f7b11d2bcae08c706a60a784930d00f18c24425637bde9759cb434b85ca0a799cb709293dd32364152ad1a1c17f689ee12822829a8020ea4bcdb0844e33db37b1cb3cccf5ca0859d017161966e0a7b1eb68cab3c4355fd293b8081289c2019c5961b7096a4489d7119b14d897b5a2849d669cf02f8785654e52d4146882138453b1895fdd6038316261d86de96e1b46843745c7c861df75894021e55456272a1425c10008db7b4223b99b0cd50565ca861ec719bf69d804a4d2160f22c9275897f7bdee1fc500ac206899f7a572138310ede4505b30b5ca86e183d51b3b8230ac141c1a2549721fc6f17d416882f2c99522c503a9891317f4c48b0ecd4689ec72d8a3d4d23246d450235c4b46898986dc2654d42699b598313a1b37b61e86e007ad414643e08d52364ad2540e089d868a1b69cf54711a258110114b1382b550728184668832505a286e146d56729c726a43321c6a625a1811ad470eb25a177b1e6709a4324a15aca524c2d3c5621c1f968a1a4b4513e0ea6241231da27b18a291da7b61f86217849eb731a750ca515d615c90a6261769d583b408805e5729ec2a4900dc816882357c6106d52719957fd88220567b51e7147f6a07f3b5526883303150565ca77c23501af6261b69d4b32896688c93282068a1a7b98a0311a86e170b10a626148215e538ee2545b6a4965a972424a02d01e2657f7b1c66792a3b4ae0997268a176f8b531db3860c93b808138705793a3a8fd625eb078c0625e13490f2b482098057d21b7b9d63b4ad2b0595c14c638a00b61f86dfa4b219128602d90b3e00f6a0ea310120b17f67da21fc356891a875fa7b1cb628c91b52c3b84b08d4e404b462572861ec6fda7325140e50d1a8b8689897b009221c54bc210108b0dcd4688f5368980942d021ee7a5cb53d4e4705345cd6205ec69cca15972689445a989378711f18976da659c3f0f8235490a7fd89861a721d5668a12454dd294374ecec6252f1e853351a271812010984bc736252d468cc3a9b386e177b91a0b18985dec6fcd232532388ca320755640c5c9a24b45104d3d3bcc5625c66003e008d6758671652c68989862003687d15c3657cc44695768a177ad49101a52a063588530807a3106e8282203c7356dca86e17469885fd303f58986d673d4230342b1c1a2549720c4186cdbd4042346d701b8125d1a2141395a989695af4721e86e1482929538ee2ac086a44a5290b585c51c1a72445606dca82dcb6fdb869d312444 else (if i<4 then 0x676261d3486d16d141c44e624f73bd5a5fd410d94e4504e625203a09f759b569c392581f29c532610a5fdec72d8a5e567450ed1fc1c5c8b868989849d659c455c9526882d32962849a74fca2098354297f22c565a9890099b1fd896d4536a4b64298968a1b851ee7a5cb6d1a35a5684711a25882204210104a5502d00d19404ab24c266891b3287367da286dee15822050125c8087b1cb69d3f2442665ccf5ca127b00d3e12c5c97f68d2d144ea6ce1d801ec325525043e328232d1cb50d141380262615851d672c230319f85d811fd11795626559b0808462449724fa469a286e1859c23050705c952689ef660f65fe1b85e147b9cb6d5a74bc7f084d46a48842a126fda74fcab0d50a5fdee6f5a1628835391c468330c4021fd775c56a6261a749b4614aa5c57d4111b7192c300ea689ee3b477729b31c44f625a51591b3a05708c0b3e55a6cdef0e4200111e33d7f264185fe1869c4c0996a659276a61b3d4ca0841d6a5a24b51c0dcea6ce0b789cb6fdb869d5b4c4266a10f264742219f2d5cb1f9761fc4a0cdff625c60cd68689eb4b0d80b43b7b57268a002d02068a003d5ca625ee4fc36729b37ddcf6f5bc6ddae6a9011fc22864f5429176892a0ccf162617818a5258c1468d6270452fcd208c4b32a177b04a841e32956232871485ec3247a434b45fdee6658d22022209cb6e0661587f465bb8603306c0d559a2861cf6fda71b45867c9f49cf12098923c3f03d5a4718986dee22c085c85339cb60891527db824556108ea689cb718aa0313f7b9b53282268a1a6e0a412c23275c585deb3e1515fd413107c66c7113d8986a177a5d66e0f10f5af3591b3a1c97b5ef7b016429de208200ada26d58b3d52f36c97341a2861cb6e1605794e801ee7b1e8600aa67c6e14d89205a45b51d440f12806a5845702d573b9b37b9cb68435051b821d274646a862083e0ed4059b8648e33da27a1d273db46b86641a1972da7629673d5196a4312e1a269c26661721c47c6ce14759a63d4a143c041f071689897b1eb72da75542d440ce5c8be2d5d60442d1fc9f5fc2b1382a68c12010987b07d3a836549f96f1831fdff7ac23001897b039434cf5fd6a4fcaa3a2060dcea861803cd277ac362a98985d5a4b0f13288c3ac0885dec205555892c33c286ce127b18a4a53f244145a0f85fdbd6dcee3c41b66def7b1d672cb85c8ed1fce617d8968a18759a93d97f869fa73dbf6f9b76312e31ca7088f903c634721869c87565a285e0a7849c04cec1916386e177bdcb15831079ca46e177acf15657f85caf0d4e07152233c7f0b5897a1d66d5a13d5884647f19c5f205b35fcc9285405adca1c58982d8a6193f4a8f80d57f7a4f10eded801eb6d01b2d1ed0d5620a1b332c7f08d1c85caf2b8a782a06801d072da72b8891a9a972d2f22c4a6242d26431019a32 else 0x329b33d414449a987e1d73d084d83129456088fd625a11bd4c3a07a62554209b37b1eb2adc05fe124aca541cfd626141f4e30b4868603367d5e5ca1b85def7b9cb6e1b56291c1fc21011016a58969cb80c58985d3138035689c75394b50826022120803b5c989861cf6fda71b59f27d276e04b45c863a8eb33d5a6253f5783602c63311cb3484b08d14139895052c0dcca0810a3a1ab5fd0b4b11540589510234fd9b7acbe0b17e5acfd08c4a274211fc9e5c83d49d1b5fc4a08d9b4c501078fd625d6618ab5856b5fc570ed243a008869d25f5ce4bc674058969cb40b4708718968a0838435745892ac144fd0386cc122ce568a177bcca2a962284495a9191f1ca1c5ed68a0e209097bde872dbc6e1b7628f16247f66e1b862127b1b869d676a17a5189f5490a87dec759c10c41402172759c66e0f51b5684343a1fdc57fd89388571f1897b1cb3d4c908d713b8b46898940c2b2e1ec3242303101625cf69c6d06ced49da2862157584c3e0031cd72555a227c1200c6e72a142202b1fc6885d621fccf5c823329ff848030ed7268948379536881e1fd89585197a9a97b9324c51845c56048ca6cdc60ed7272a177ac335ac63588a407463850970c5147b5a744846090091c1526898985deb5092c870615896d1a404388cf1fe000d968689b472989861a73b55621da286e1a8559b67dec759a38112c381c567da70e4f1625fe5392c0dd681c59b625952903e66d897bdeb1fc6131da24b80f32d1c68a002085060da285cc852c4e47ddc18e18821674b1ca8659b860871a81b86035051a24c4563a1894c45612cc66cdee1296a625bf6e0874646a49e085a9323e4573fd897054b011a9259c67fded6cd8914c887147f856087d9ec68ce10c416129521c1d187deb5685708cd4856087d9ec68ce10584a5487074503209897adf130023020aa85d870b488588b272a1b861d66d5a03d5610e42c0ac2d624e8861ec6fdae69cc94051b1a8cf819e0119ed6fcc90b5c96a51e1fc14429727b1e959c4b2d1a27c9d61254851c035547384da27b83505031039895e4ed0a1a9688ca0cd1a68a1e86deb5492146a1d801ec7ade97a1d66d14e5052c4711a2643e0c48b08e14801cb6e1b46b9ac284972587f1290a12d17578c445c4b3a84a314cf591c56240e3f819624f815c0b3a19f311ee4b08b0b4082d87039cb431d8903d5b209a2829e1034990b5a2591cb721b46294e46caa2041e0091a40482624f5348995fde83d46d624816cdcf12d257b9015fe1873dcb6fda7161093d09e49dd61589f5fdd672c7f625a286e18849ec709b869c2b771a85189f5490a86a187b1eb7a5bd208811296831431559ef7b9e836c6e0842d159891fe177bdac6207f67ccf7ac3654900625e669c9c01cc83b1015b070625ee5905012c14315a92bc2d021da86d2f15974394))) else (if i<8 then (if i<6 then 0x9d6741a768543538e22bc016a1192709702d7f6ed727b61a855ec759a359e043815267e1b861c269c981b81c429526a589648a6471a27bdee72db55847f050355c8262c9ef7b1eb6f04a1c5e76d5314bc8b39456345a2621af6889e0b5a26d07f0d4145c9a273dae0807046dca6f420468fd7b61e86deb4fd74469ee464141fc535c9f6789cb4c4ec1fccf078ca7b61b719b56d1a01fce85fc50050f6626004c4c60edb372c8b3f8b85fe1a0b4e533d1e6a47f685913486d10914220716252a14435078ea626174c8ab0fcee6ce182941e5389603d0c1cc827aa124c115368544ecec625bc601961fdca4659b7847d03d5a53063352147b9430b40c08d1c876007f9c66d1b25391b468aa0d8310087f5a9894b1030482d6252c08c0c3f5b3638e03d02d6261e7ac3f5186a4296272cc94b087264e82d0714c45612c296ce0a72d8a618ee02110129537a8143b4706a55268a0a784820d80f3aa16325410dc1e2644e869fa208342ac7d468e8856087d9ec68ce10582554870745e915c452f52d36c4a02217078c0626147bdee7ac56716007ac7f06dca7141e725ed7083a04cc51911b58deb0c0ab1bdd3201a2504960ec26008b966d1b7fe1873dbf69c6d3c47f27d27030ee6ce007add50c0827292a0881e27c37454a5019b36f0223351c67e1a6ddaa6002d0819f2a9a246e1b861e9458d82947c1ec524bc211fccf6cc92030c668a185815e538b50c4aa0f4e80b589849673244d4c03172a007b1eb6d0081cded68c8906497258067b9ab6ccf14687142a00220716252f14c22030e86261a849ec75967051525c9807b47f4658966e174ddf84a833021e5729cb3493f29c3136e010ed8972d913d4d20dce86244e33db30382d25a0a784f7440961d42d4256387a1b7b9e95390a46a1f8488a75c411194e39c602d9d602001549a24b0503a89f6d12f29c7c22c1d689ee591410d4e56a43e4b19b6cc9f19cc7689eb7a5a350cc012c37871596261b3d496689ee6d42d258e71c0b685dcf72d8a715523ad257b130314636cda759d150900942952689896448b469b3801ee7b1a165580540aa2206e640d61c5ec759a33b4086960168cc90800466d196a18972dac1e9563a9a286e147b9e972dc86c94b5051c468822041d00826552007b1cb69c8e0999733d726f44b0dd31158e86cd2f3f4a70891c68a183f8b85fda66882346c9f1fe1708ccb67da759c231fc145490a5c989759d071d8650d293b4ac164ad6d99f0b4f50b5b3368122098986a18759803c4aa0f42d6251b861a721d5468a0869d2c3599b648806246d5a9890e10a811897a559538965a4231fd2c67d894f80b21c63310a7239015fe004b0423a9a203c053a8825921b862177b1eb7a5e8719b55851c1fc11011a94517f7bd2f434881fd89018995fda9849a759d414b10a5fd313140c else (if i<7 then 0xd468707e5a2801ee6f9b3689a72a82d4797215d24468530800c451ed1384c5fd310d5153a9893243b3a04a625b1408ac4647f789a650d4e4c4ef255a86887f341ec138230318952c895309686c4e12c216258a4fced0fc0b4a0ea6cda165580239683599b7bd2f278e81c17f861300807f31da2820e800df0688672207f5fe007b830209b306d5e0747a1cc2d6248b15cee1198903c056e8eb2788285def3a1b30b0ea848096a589801b4258ea7b6177add9234fb18d624a8e1145d9625ec22d3a7b422581535add66a5a27bdee6d5ca3b4661fda286dcb7182b465017b5726d1a1629753d4d2325724507f67d8986e18719b53a1a9798560d96a6261b708f531c236a5621c02d0d8ea871b34bc530880c081b387a1b801eb6d1414711a2583e08d52848145c18972da13b83e031525c9a13d44b429894c4de0ec0c359a27b1311bd09626187b1a74a5513e0b25fe1b7ad192a96285e147a5d669d6946402266056a57f725244683e5a989784af2700f1043b18da33c40866e0b7414b4fcab24ddc3c41d584630b6076fda3080f13f47b0c41b29c5369cc96ccb86897f4c501625cb4a8ae2253f328f11a82d69d54471a21380e314c76261b8698a0ac08085ff4b0231189f72ded7291e3b41c1b8567fd891fd934c4de19d89689c7719b56d0f519519085700b5b36247f0c41a6242c0497f875ee6293f2903121d1a7ad5a4b008795642911a5ca007b9ec759c6540aa0c48867d891c60f7bdcb6e07f66c2638035028ea6242386e177bdee72d4f47096085ca17da986a17489ca7161882de26fc95035191fc416d99f58131621af68a15821f67b1a338416129551cdd14a83e1a9596ce146e07f4111967dee6d58a591624b11c4682322c1473ccc3a9b37187f27d7265da2851d63c4a422c237159f088b5869fa7ad322ac341386346898319a20ac20689eb0b4c7689a022c350507f345a276da65f1671dc3e1281e5490a7fd8985d1d7ea0c3b8a83a008310aa4ccf871871518ca36c8e555a286a177b1a332094131ff589ec72da72442665ccf5ca1b862177bda75e567728e5449a968877469a286a174717f3f8083a18e7b91a6ccde5589d688f96a1898481463989875ec7adb45a03e138232d1eb078aa626006d0225a1a21fc216217285deb4c48d71582139dc18cee6ce1e86e0072dc76856a36d1a0a002505a2848095c9893b4e8405ed7b1eb71cc92ac934fcf11c02d861ec719bf69d804a4d2388582c8f25897f7b1a31283b7b5cb71964470d8050c05c8a408cfd6256a08cfd625ee4c8043ad897b14114c0c4e4c47b13f03989688236207f29493099a2860871fc1e549a2801ee6559b6cde9130041c5411fd5466db35a93f3b43d03402341b6314570fcec569893d4e52602c01a187ad5a2cc6e31200468ca12d894647f388ac1621a85d1c72 else 0x147f4c43b03002359a2801cb08caa7bdec7adcb5840433d97551701fe186f96708ced3e1a2854871381b0c5413a1ca7852e29c3803d0e3c1b386217851ef7b9eb719b57fd611582d209893a12f29d06425b36f1ca625ee7adcb128827fdec72da73c51b33d7286deb2e1a92617f8004e0c5894b03a66d8986e1872dc646c96009a9688b8851ee7a5cb6f5560ed726951c5047a6261b801eb6d141264ea85deb474a120cf11a9b65659f0b5413a98972dbe19c5627d7f588da0e0b8625ef7b9eb2ec886244a030c56250d555a285c7f4b0f827d22471db59c6d4e87f0d8235490a7fd89800826242d2211a759c66a47f1b9896e18a258ca68a177997c324f80d5625fe1b70912138ed1c0b87fd8987a14755d272d73871c54911a77c1e501af6255631501626005a1a27fd1a1fdb30787f0ad895c9b8128e872dc66f1b86d1802a86a3e06e67d89410ab0c5600b53f0806e21cc4869ee72d64589414b1191fc4e08c350512b15c0b1f5b382d7a2bc0b4646a6a61869d1319c2c355c51fe176fcde0dddd72a087992a150363b1891b5462061b1597433db335c635a9897bdb31fc5f5f9a2261f36257f1fd895c8c50dcc7624de0b41e7b60872db869d434a8910f4266a09925c887fd9f2d43801211565894bc35454db62557278cc689eb2fcc812ccf86a157bde872dbc6d2137b45c1995441a1a7a1cf6b9314106a6887f46c5104cfc56927625871602d031627299e5b4f50c0e22b07f87e1715c410950a2b6116261a6d52f1fc20335a986a077e9bf66d1c67e00020fd0b4865f0350342b689c25e51a68a1780d62470825c1a2848035c9a285e0218d8912c22689b86b6054707f869fa73dbd6dda3080614699f7ac8202036871ca2f98f02127030c7626176f8bd0b41b49e1a85e12801a44fcdd294952047910408729c57a9b67b9a15c8e8221ef72d6e0b02d31ce81fdec69c881fc6731d89849d669da64b031625df0f8234b1af6261269da61692c689890884a7b5b8715041fda27855803d0c208627a84e0984512c560f8225c941801ee7ad0d0212466e1d86a144fd6448c7320823030ca7b6177b92c470d829c4b5d16286dcb6e17943c7f011ca46589689ef7b92f2ec8e0b5a21fccf3687d4e49653cc90ec374b101624214b1413a18986d675c95d080730c55568a0a7b1191c1a950448329ec718aa245015fe0a0d4223ba172e0c76cd1a68a1885dcb7152586612051526a57287a17829eb785c76f5b86851d20dad6a1593c5f95fd636ed722787f08011159725fd6c15c36498088481c6a58986a17714b86249e331a27bdec25825429e58284a0d00f18df445ce832a17539da6887a14d4c5042304d9958d1b85c9622de5729ee7ada350d2f28c94138717b0c91383b7b4370786a0b61c1b4201fda246d9f7b1eb799d0708f7324a1364ca2ac2)) else (if i<9 then 0xf50b40c451ed86cf52f0231c1a92440233da257512090ed1c152689897adcb34831008d60b6147bdee4bc68220567147f87a1b801eb8712146a184b0231fcc7688fd29c22471a254d1518db3861a75788768a120f5333e1894bc3b66d89588aa31d8915021765596cdad4b0aa08cf846dec628a422cf108ded869ee6a4db4695b0760d2ac4b4bd8866da2849ec759a7698a04292c626007b1cb721a70cd623c57286e173a1893c4f86892f45c5312db368cbc31c082e0ad0e0d3501b386e1a7b9a70202d035a2591041fdb34c456030d6689ec3d4ba074816cc374b0de0ed897b1cb721b2030f15c8d40095186a177a13142cf12a89f46c7a06cc01b8a41c40c0083b359a2851b569d0d20868185a26248b158220809f4c41e3f58982dec72d8a7712a2b8894fcca3c46a0b5ec600d232541138232d0e21c47c624f73700d5917f5a93f3a1e66794d324a13889c115661c61c689890f82213d89819b468d8a25871729554042d625eb484533a8080ec371842086def5507f6ccb80c58986a1773dcb6e1b70c57d4707c6cd293d475130f11a961849ec081303e1725fe1b85c1e46dca1b5310ec5e359a21fc9f66ded85da3048c26ce004c44c3a9891b4021287c820db00dd1555a219cf8689e975802359b30507f625cb46c1e5199f374cf20589861ec2ac2c06d0d1c95e0440e18d6a624f60f4e86259b0f96a625db709a64e43f07152429ff626170d4f15657f82dcb6fdb869d2f23845099a8264887fd9f2e13a078fd6256a1c47c626173b8a23a9898614e4d9340c60008c042745376541856087d9ec68d5f3844a0c5521c1d1829e103c731f563801ee1099b6cdeb1382303189821fb6c54c811a94052c2d07f85dfa4958925c022949625945578b80ae187b0ab5fe18801d260125715ee3d4c16cdeb6844b1283b7d57201482018f83289a4891a68a0b378ca039196a1a229c53080c41b9a70302614d725fe1b848845289a504b6180e77b9a75e5674647f0841d729a27b881625eb4c0544f0e8625a732431729eb71d7e315a27b91722c3929db3294c76261a1fd1b5ca1d4b07c3503a689bf2881346c8158c56765406cd2f22c3708404351a272da7538ad230370b4f15fc53428e85a9897ad772788114c4a084fd6252c2283b0d9006251a3a09f412007b9db749cb7184e0e8043e17d5c81e1c16a625da5661b4c5171584b074ac6cdeb69d29028c7728530e820031416ce1885e147bdee7adcb71dc658482045981597d5c8285c989848ca314316cdeb6556a448911b822358537b5a269cf5464e22b0583b88b0d40a3a989801ee7a1cb3d51912856752007f9ee7b1db7187f1b83a0cdff715ed2907a3a9a2325ff1cd8986dbd686193b826405521e91768a180e4b24297f875ee7b1cb600c94fcd40f8237b5ca2d1d671db55e0f56200019d1e7 else (if i<10 then 0x54887689cb12c0c1fcf16244e6356a7bd2f0e420278565fc230314168931378711f18985d2c2bcf10210e862086f9674b1c38659b4b0ea4057f8003308568688565a81e626183b4871fc46029526895a2888c0f03704dfc3bd8985cc9209f31cdca826067edfa7b9a3628310854b465a9728637ac6d5a1142203a5fc5f7fd896b1af20618801ee7b1bf601434a4d2324e22c84e115ed5fd62801bd6d0080791b7b5912847c129541c50a6258a0742d469ed86dcb719613a1a986e1885dcb709b569d9162c213291226d0a689a73d4db6a5a281a0072dbd6294e4bc972584b3290a1c5b01fdcb3490d0ec02625ec72da74fc8e0999733d72801ee6859a5408e109093104f1ce177bd4154962801ec50008429e51fded62612050355c9894c4de1581b729fc154130651b7b6126fd671148b06d52689ec64d433d59b33c80688e21f1894bc3e081b3820fc745894bcdb14cd468a1a7bdee759a75e5676882d6cd277b80c7291a7b023031b3138230987f12c0866c2d12e1269d675490a5c9ec6fc236a5891a8e8205897aca1449506896a1cd8985c12715625fdcb20c4a5a9897b9eb685956290d020737fdef3d48e1fcd1689226259f861a750d2d2ac27874266516f628af15c0b3a8876cc1e07404008d66892c14022031b37b1d6028986cdec7adbf69d29715682ed7f87c0b42882794c94c4aa0dd1b689ec72d8a348c930d1208d722d1a2624030c5a20b5016a5430780327c804bcea1cd892c40a31db372d8a0b5b31fccf86dc23d4ca075a968a1a855ec759a359da53815267e1482e0a801d6709434a4f53b49d1d45913169561151a8c8815a950d4e2f9ad5de004bcdb405894b0503a98912823030336cd6433d27624ab24c6f201a23253868a17300a8021cd468de728317bdeb71db533dca758980b0120ac8b15822009147b591284d66892c2942d2f21b8617c59c1e050705c952689c7719b51fc2d3a9723e05703d9f3a8c4821d43b9a952c4e5052c5c91e2d2173248e0eddd329300489e14da269d582507f509ca2285703ceb56989862127b1d67d087695015547385ca2715625fcca099512fc9d33c7f72c35088b74719f8760f7b14f4fdea48c56209302052514da20c47f625bf69cc90e50d19153479092e1d659d72549a27b1bf260f162617851cb69d4e4bd1c46c530ec055c0db5fc825a98985dec324f11a9b65659f0b4f83904e62467625a27a5cb348d60c4ba098225c47f6a48a03ce33147d21a1a0dc2249db3861ec6fda7325320fd124406c404cf72453550e9471a2801ec6f5324643106c2d72863314c70dd89060f84291a759cb6282d6cc7f33d2c08c466cc8b0784a7b4c92843217d3f3a9ff6261869d7c2e017689ec72c5d049fd7b023001b34bc3e3a1894bca71cdb35c95268a1b0ed488160b801d0628570740b3c4c85c8 else 0x3b5a95020867714e87254612c4768a181acc4801b4600aa5041e67d7d46dec7acca0eda21fd1a689ee4fca70c52c32962851ee759cb69d8a4bd191fc176a5945c8b87b12f36da2625414fc3b69c4c3c58973d5c414a81fca4159d927cb1028c7624a129c7c0dc8b395a2800d23b84b12823626172fc2d078087294327c261fc8886e1869d672607f08c0d1b952429895c9563a9a2861673242c1c15e1fc0227d9b7b595141413a98986a1772c6a14c317291c69d672607f078142590a549a2851ca6a5373248e14c3b565ca6989f209a28691e6a5cb6f0f13e0e06247f7bd670706e159ca465df071af501897b1eb2047172a1b7b1c659cf50b4215c0cf1fdca8008610873625ef7b9b55848e1a088159c51fdcb1fc21519726fd584a9e5745ca15c3603cde625a72d02d1c21c68989728f808dce875bf69cc96d9011a8cf861a7))))
def jh11 (i : Nat) : Nat := (if i<1 then 0x1dd00ec807580bac01d400e6807280b9401ca00e40070c038201bc00de006e4036c01b700d7806b0035801a900d380688034401a100cf806740334019a00cc0065c032a019000c7806340316018900c3006180308018300c0805f802fe017d00bd005ec02f2017608bb005dc02e4017300b7005bc02d8016c00b5805a402cc016500b18057802be015d00ad0056c02b0215804ac0056402a8015200a7005300296014800a28050802860140009f004f002740139009b804d4026401320098004bc025a012a009400498024a0121008f004780238011b008b004500226010f00860042802120102008180400020000fe007e003ec01f200f60079003c001dc00ec0075803a001d020e608730239809cc00e608720239009c800e410710438811c404e200710d38059c024e00e700538019c004e0006f0037001b200d6006b0035001a008ce026700338019804ca006580320019000c6006200308018020be085f022f8097c00be045e802e8217408ba025d002e869702cb8125c072e0317014b8065c022e0097200b6045b002d8596824b40e5a062d029680cb4025a002d0016200ae1057042b8115c00ae0856022b0095800ac0055042a0015038a61a530b298494c1ca60c5305298194c00a416510a288494418a20a5103288094400a0104e042701138009c104d022680934009a004c80250012a009210490424811240092104804240112000901c470c238511c208e0c4705238211c088e004700228791038881a440c2205910288812440722031101488064402220010c108400420020c0100208008400020048fc1c7e0a3f031f800fa007a003d001e010ec0076003a801c840e410720039081c020e008700238001c058dc286e1237071b830dc146e0637021b808dc206c0836021b008d8006c1e350d1a858d4286a1235071a830d4146a0635021a808d6006800340019800c8006200300017800b8005a002c0015800a800521c280d14060a02c5014280914038a018500a280314010a00450002700130009400480023801104088104404220011400842042082102108008420400820011000080343e161f090f8387c143e061f010f8007a003a101d040e800760038101c000e0006e00341c1a0c0d0506820340c1a040d0006820320619020c8086400321e180d0c0586028301218070c0306014300618000b8005a002a0015000a0004e0024081202090004800230010040800040001e1c0e0d07060382c1c140e0907040381c1c0c0e0507020380c1c040e010700038001b000c0806010300018000b00050402408120009020400020000e1c060c0305018200c0c06050302018080c000600028401010080004010187008340418020a010480820040e0206010280810040602020100808000400010e00060002800100006000200008000000 else 0x80914048602400120808fc0478023d011d808e004720237011a008d4046402320118808b8045c022a01148089c044a021f010e8086c043002180109808401420061101050082c04100a0401028080c0400020000fd807e403ee01f400fa007cc03e009f002f8807bc03d801ed00f5807a003d201e700f20079403c405e200f10078403be)
def jHints11 (row : Nat) : List (Nat × Nat) :=
  let i := jFields11 row % 2048
  let b := packedAt jb11 (i*19) 19
  (List.range (b % 32)).map fun j => Id.run do
    let i := b/32+j
    let i := packedAt je11 (i*10) 10
    let h := packedAt jh11 (i*17) 17
    return (h % 512,h/512)
def js10 (i : Nat) : Nat := 0x990c001300100001173335143c02a700010e0a8c3c1b60112a102e9f3b0333734f0a05010a051e05043700000d00
def jm10 (i : Nat) : Nat := 0xb9c5b55dff917b2a1651b1db5d7ebeb8d2fec7bec1fd1
def jr10 (i : Nat) : Nat := 0x131400
def jv10 (i : Nat) : Nat := 0x8b8002383a20011620b4632dcf0a424228f506a6333441deda4d4089ad1bb040000010ea3b4c08f0003ab44e001003b33aee25d924944c001dfa0e48c20d2396145061dda4044680010b22d70e49d0f213474949149984908710120a0009910aa62
def ji10 := jLookup 46 180 8 7 7 11 js10 jm10 jr10 jv10
def jc10d1a (i : Nat) : Nat := 0x2
def jc10d1b (i : Nat) : Nat := 0x48110
def jc10d1 (i : Nat) : Nat :=
  let i := packedAt jc10d1a (i*1) 1
  packedAt jc10d1b (i*10) 10
def jc10d2a (i : Nat) : Nat := 0x7bbcdeb38bdab494603
def jc10d2b (i : Nat) : Nat := 0x196605805c16358153541414c5304811024483
def jc10d2 (i : Nat) : Nat :=
  let x := packedAt jc10d2a (i*5) 5
  let i := x % 16
  (jc10d1 (x/16)) ||| ((packedAt jc10d2b (i*10) 10) <<< 10)
def jc10d3a (i : Nat) : Nat := 0xe0f56d4b45d0b19c5b0bc0ee4b7eddb6edab66d6b56d3b4aceb36c2b02a7a8ea1a829fa125292e2989e08749cb68da0649815ad67599655894851d414b1294a127491214791d471194611745915451124451043d0e4350c42d0741902404dd370d8348d1340cf338cd32cca324c02b4aa248801ac6904410
def jc10d3b (i : Nat) : Nat := 0x6a1a6695a3685986599564d9161d866158460d82605805d1735c5705956358560551535495154142505324c530484a92a0a428c9524c9121483
def jc10d3 (i : Nat) : Nat :=
  let x := packedAt jc10d3a (i*10) 10
  let i := x % 64
  (jc10d2 (x/64)) ||| ((packedAt jc10d3b (i*10) 10) <<< 20)
def jc10d4a (i : Nat) : Nat := 0xbec6f0fba2ae38b8dadbcb6e6daab67ed97b43acacb03abacaeaeb13aa96a1fa84ea03a6b292ca4a688ea20682ca07a8189e867939c9270f9af26a39a6e69898b261f987a617969259d964e539947e51392ee4ba92e24b7928240b8e3e30f8a3e22c86ea11c824200e7ec9f9a7e2df3c7cd5eb27839d8a749dd0a7229c3f6eb9b176c41a8a68299a1664193b645d8b862d98a9624183f60f183a60dd83660297915c5d7165c1d690582d6055659532523148852154175059414504d408501d405500d3914cb53134a7929d4a6922c46b119e4485116424503740b902d40b101a403900b401d0064000fba3eb0fa33e6cf973e50f8f3e24f873e18f803cb8f213c74f173c58f0e3a40e2c3888e193858e143808dae3658d1632eccb232c4caf32b8cad32b0cab32a0ca63284c973258c953248c90323cc8e3234c89321cc8230dcbb42eccbac2e94b822cf8b3d2cf0b3b2ce4b172c58b132c1cac02afcab72858a13265c996245888e20e88302060817203080420047a11e587931e0473c1c5c6a21a786821890621187461618546131808596165451612e84b012744971254493124448110ec43a10e043710ac38c0cec3360c342b20ac029308f423c08ec23a08e023708d823208c423006e01b704ec13804d810e025c016
def jc10d4b (i : Nat) : Nat := 0x1ba6e5b86ddb66d5b46cdb26c5b06a5a869da6695a36899865d966559464d9161d866158460d82605755d1735c565591635895454d5254543509414c5212e8b92e0b32c4a92a0a5290a1254932448520c81
def jc10d4 (i : Nat) : Nat :=
  let x := packedAt jc10d4a (i*14) 14
  let i := x % 128
  (jc10d3 (x/128)) ||| ((packedAt jc10d4b (i*10) 10) <<< 30)
def jc10d5a (i : Nat) : Nat := (if i<1 then 0x703f703d703a70216fc96fc46f226ea26e496e446e226dbd6dbc6d166cc26c446bc76bc46b0b6aaf6a09699d6948688f6886680667b5679d67966786673866bd660965c8654a6486644763c7631662926213619d614860c960c8601d5f9d5f255ebd5e435e2c5dac5d935d3e5d3b5cbe5cbb5c135b865b065a865a0659cd59135884581a580457a95793571456b656865646559a551254c754c654c3544a53c853c653075304530052b1529a52975287528452805231519a5197514d5144514350b15046504550434fc84fc74fc54f9a4f994f864f104e934e174daf4d104caf4ca04c0b4bb64b8b4b834b2f4a994a1a499349104892481247bd478b4789472f46c8464445b645a3454444cc44c944c644c44411438b43084288424b42484243423b423842354233422f422d4221421e421d4210420b420a420842064204420041a8414a414340c7403740364022400a40083fcd3fca3fc73f9a3f4c3f463f453f1a3e923e263e093e043e003d9f3d093c9a3c893c483c463c453b943b0b3a973a17399a39973931392f392e392b391f390238cc38cb38c938c838c538c3383a379a371a36b13690361335933513349334923413339333133293321331bc31b131aa3199318d31843180310930bc309a30192fb12f992f932f1a2e932e492e482dcb2dc92dc62dc42d932d472d432d132cb12ca92c932c4c2c4b2c482c462c432b9a2b132a932a0b29b7294d294c294b2949294829452944294328862806278627452744270626862684264d263f263e263d263c263b261025bf25bd25bb25ba259a253f253e253d253c253a24cd24bf24be24bd24bc2413240c23932345234422b2229a222121a9211a209a20481f911f101f0c1f081ea81e371e321e2b1e271e201e1f1e1b1e121e101e081e061dcc1dc31d491d481d471ccd1ccc1cc91cc81cc71cc61cc31c191bc91bb61bb21ba71ba61ba11ba01b9e1b9d1b9a1b8e1b811b2e1b261b211b1f1b1a1b191acc1ac91ac61ac41a181998191b1892184c184b184918481845184317ab171917161696163c163216281622161e161d161a160e15991596153815371536153415311530152f152e152b1529152615231522151f151c1519150214cc14cb14c914c814c514c414411399131a12b6123c1215120c11bb1132109910150fbc0f4c0f490f480f470f460f430ecb0ec40ec30e2e0dae0d440d2e0cbd0cbc0c490c480c470c460c440c420b960b900b3c0b160b100b0c0ac90ac80ac70ac60ac40ac20a0909c209890937093609350934093208b70837083607b707b607b5073707360735073406b706b606b506b406b20637063606350634063205b705b605b505b405b2054d053e04cd04be04bd043e043d043c043b038e03400339031002ae0290023e01bc01b901ae019301490148014700800000 else 0x86be8644864285c5850584858438843183c783c283b883b183b083ad83a1833d82bd823d823a81c5810b80c9803e7fbe7fbd7f217e9a7e077da17d877d487d477d457d217d167c8b7c0b7ba47b457ac87ac77ac67ac47ac37a0b79af791178967821778a77457743768f761975997511748b7431742f742a739273487289721671a2712170bf70bd70bc)
def jc10d5b (i : Nat) : Nat := 0x72dca725c871dc6715c470dc2705c06e9b96e1b76d9b56d1b36c9a96a1a7699a5691a366197659956519361d866158460d82605805d9755d1735956458d62551535495150d4250531484cb328c9320c7318c4304ba2e4b72d8a9298a42548520c00
def jc10d5 (i : Nat) : Nat :=
  let x := packedAt jc10d5a (i*16) 16
  let i := x % 128
  (jc10d4 (x/128)) ||| ((packedAt jc10d5b (i*10) 10) <<< 40)
def jmasks10 (i : Nat) : Nat := 0xffe3ff4ffcbff0ffb3feaffa3fe6ff93fe2ff73fdaff63fd6ff4bfcaff0bfbafedbfb4fec7f7cfdebf78fddbf6afd6ff5afd63f3efbf3ef4fb7beb5f7f3df9f7dbdf4f79bdbef6dfd7ef4ffcfaf3dbcf4f3bbbfaefe3bf3efcbbf1efbbbeaef9bbdbef6bbbbedefb7aed6fafbe7f79fae7df9f6e7bf9dde6ff7fcdfeb7f9dfe37f6dfd77f4dfcb7eadfa77e6df7b7dcdf6f7dadf5b7cedefb7bddeeb7b9dedb7aeddfb77cddeb779dddb76edd7b73edbfb6fadbdb6eed9fb5fed7f75fcd7ef5fad7e75f6d7d75f3d7bf5eed7af5e7d77f5ded6ff5bed6f75afd5ff57ed5df4fed3d74bdcffb3fdcff33facfe73f6cfd73f3cfbb3e7cf7b3ddcf6f3d7cf3f3bfcefb3bdceef3b7cebf39fcdfb37dcdef377cdbf35fccff2fecbf72fbcbbf2dfcaff27fc7ff1fec7f71efc77f1bfc5feffcbfeaff9bfe2ff6bfd6ff4bfcafeebfb2febbfaafe7bf9afddbf72fdbbf6afd7bf5afbebef6fbcbeeefbabedafb5bebaf7cbdeef7abddaf6fbdbaf5fbd7af3fbcfaefeb7fadfcb7eadf6b7bad7eb2febfeaff2bfaafdabf3afbebeeaf9ebdfaf7abddaf5ebbdaedeb7daddeafeabeeaefab7eabfa9fe9fda7de9efa77e9bfa5fe8ff9ffa7fa9fe67f69fba7bf9efa77e9dea5ff97fa5bf95fe3ff8ffa3fb8f7e3bf87fdffc7fe9ff67fd1fda7f61fd2
def jfields10 (i : Nat) : Nat := (if i<1 then 0x5afa01d18100bce65c574c6f946596f826a0af72960af6219c2f555df0f4201f4f337172c93b534f257e10f1829f0f06a61eef2d498ee2e9eced0fc4e43659deec21d92eb8b132ea4921ce94c144e88193ce784816e681cc6e58adf0e422216e375438e23458ce10a8ea5c11c4ae077cd6df5f8bade8d52edd48a1cdc27616db35578c21a49cda5e0ae5e62622d97685cd846206d744026d646990d52b4c28d708d43c7e166d48e942d38ed8ed2181b8d14561cce3d892ae4d476d05fc96cf7b814ce5c4c6cd70cd2cc51e08cb28a0eca36d7cc9674c00553e06c8015c21032e0cc70d9a84119cc2c61e6161b910cac587dd0c409ce0c33596cc250210c11ac78c0404ae5e84416bf12c425c128445c18d18be1ea16bd2bca8bc894aabb08d100d0c9c0ba73540b98dd42b87a532b78586cb6234ba813f0b6b513136b44f610b344a1cb264470b1430bab01648caf0e0665e3d0b2ae608c8ad34192ac00002ab054e81f1c216aa39d76a933dc4a84aa1ca74be06a60e866a514d7ea42b8b4a08f18ea33e072a241dd6a12c09aa073d009f410665e06cfe4a811f09e6d0c09d5381e9c878249b324a0756e9d89a2d0a6997cd5e986389c8f0b0f4974a61c967a41c953f5b85a8688c9454868932820a92084f091319b890514268f23c8c8150c2c5e1453e8e540ba8d6359a8c8fcfe8b5ecc08a02840422060a89558308876c6287109be865280c8537e06842e60c835be06827fd96192446881598c6547d15c8074c387f8f92e7e27e0a7d76c3c7c570c67b8d98e7a4d08c793a1624b6309c78045041f60dfe779043e768aa08757a4287461432735d1f672601fe71331e27061e1c6f260906e6aa066d094fa6c7b4946b17d926a28e0a6949a1c685e48a5e59a06676980a6652150655f21464060101f5aa06634fa1e621de1661641d460019a65f4d8685a5e8665e544b25d0acde5c048f81f0b8dc5c83a0c5b2fe064c3f9b85a02516593a82c58714cc57610c0563998255578c654890c85347de45238d965168e10501f6164f7f9724e0f456435d8684d2c48c4c3bd7a4b0690a4a4221c495a206482a60a47900fa4617216457e560440f852430303a420d1b0418e142407fd583f58dec3e20e163d7040e3c7d9923b7a9fa3a6bcb83913532383e46037664bc361be163575ddc344ea10337f1f03278d94317c416300ec642f3edba2e385882d2ae0a2c629d22b6d4322a7253829309b4284858c2721616267f58a25569b824151362352e1a22285ea2171d86200410c1f4a21c1e586141d1ba161c6adcc1b2ee0c1a8096a19678b81848e1c17649d0161760a1533a0c142e9ee13668c81254e06111686810230c20f22a220e091060d7a06e0c784cc0b2cc300a90c140938d58081ca16077c970066b0080502d9c048a1f0038d174026ccae018708200 else (if i<2 then 0x94de11c86f1bbc74961dc67ed5ed45f5b7c50a4f69718918be428c1c486491c3554c7c24f1d7c146c07c02646bbf42e1dbe41a15bd22e1a190f05e43375674f7411dbc79d9bbb1ce17ba120485c2f60db903dabb81a0bcda481d9b73fd91b66edb85a19919b53a557b479175b356db9b25d4c3b11960bb06a2006632a0daf15ca63b00c549126e23ae6b615ad8781bac0211bab7d569aa3d4afa93897208740d3a829e0ba78e523712e0682c85dcfa62c868934e611a51a890da4ba07a484d0fa3179c5a224831a1088e29150a1da0416119f3b97d9e668ab9d192079c47a239b7e97c0a8f52f9a8747f9947a2198605da1972d93978688f963b831951b06b948c98f9313d921044e1f923dc86ae2f20d91079129173144b9158b23b5314d9043c745e481e58f701bd8e35d611049c2d8d16d921001050910a102973060d652720b8c531998b481c98a10d145823898811fe0b895ca0788851f1873642ac2580018662dd5856b9ff84400bce13c9518364e1182124465c7382f81070f3125dcba5e115c0ba3a16b80226177f618c17e6aa0d7d472137c88a237b149817a749e17930207786c47d778ed8d7603507754c4c279710d03c59a0d7461875736f5b9728f521711fa177039d6e4b312196f8609d6e4f2116d664bf6c2bca68d3b1456b608bd6a080fc91004056927a23681da17673bd82a90c4d85c535e7665260f651ee1764160983b680c9632b20b6225cb76165e23600dda35f240767d750375e721655d8cd755c59e075b7c014092b8b31f561b95a050f41f315ad59058121f3c924f2309c558550a60a4e2115782df15614d7c0a2120b55098eec36c8bf3520a23544621f53651f45d8a5e8194388ab0890bd5287084fd1184d514442550379594f510734e7dd694d255814c8055d1c320694b6fa074a154c21088491497292748586034701dc210475fd4647a1d4556605440d5ae4179575436fdb742668ad412920b40185c33f3997b3e5ae073d31da53c0085891605513b2aa0b3a3ccb6ae66c9f393698b381b617372fa0d366d0a5357ad333486c88fd6547b332dcc332101b7031c617316da0730408965e759fb2f8c4212e7999b2d04cec1f4521d2c684c72b5c2072a24e192940c745e59207288c09f2790816303c130f252145260e59b254b01e765b607241edb9238202322662212107d089136155104ee11202c0991f719471e6c0a11d8015f1c67dc71b7894f1a5fcc0197600f191e217188609f17038cf16309b3157683a7c670c9144b5445e34198be1c21b13074e512688331134d0f1088df90f7819b0e83e0c5b2d88d0d1d6170c880910b2520f0a391db094cc98796e14d081414b078b52b0663df305065144a7bc19043ad8503504c3024fe11010b4e85c29a0b0085622ff33618fe05ce61f87480fd6dc72fc8989cfb3a5 else 0x695cbfb2a5b3fa7653bf97781df85ecbbf769e19f62b4c5f539585f48407df3105a1f234949f1434aeb01f217f04fa07ef1394fee6c8bc013818a0a59607ed745fbec4401deb3511fea8345be93a591e8459d9e78b92be65a607e56921fe480d63e36ccb1e2830c3e1815f1e04c8bbdf3c528f20cdb5de111a3dd7b12ddc5ba07db8bc1bda825f1d951951d88e543d70c0da5c424bdd65b207d53e82aae1d217d489e001945e07d34ae1dd27719e1966c9dd16e51bd080953cf2a20bce86c879977435cd58a07cc258c3cb5cdf61930db5ca6d0a20162207c))
def jFields10 (i : Nat) := packedAt jfields10 (i*28) 28
def jRecipe10 (i : Nat) : Nat × Nat :=
  let x := jFields10 i
  let i := (x/512)%512
  (jc10d5 (x/262144),packedAt jmasks10 (i*14) 14)
def jb10 (i : Nat) : Nat := 0xc142c0e3c0a2c043c002bfe1bfa2bf24bee2be83be42bdc4bd82bd23bcc3bc25bb66bb22ba66ba22b9e2b9a2b943b902b8c2b882b823b7e2b7a2b743b702b6a3b643b5a5b4e6b4a2b3a8b362b322b266b203b184b0a7b043b002af08aec2ae63ad87ad23aca4ac43abe3ab83ab04aac2aa63aa22a9e2a983a942a8c4a882a823a801a784a723a6e2a6a2a662a603a584a523a4a4a424a3e2a3a2a381a323a2c3a282a204a1c2a163a0e4a0839fe59fa29f439f219e669e039dc29d639c879be59ba29aa89a629a229a019984994298e39864982297e29745970296c2966395e495459486942393a493439248920291c29182910490c29082902390018fc28f828f428e678de48ce88ca28c248be28ba28b628b038a4689e389a2892488e28883882387c38782874286c48644862185a4854384c483e78383834282e382a2820581c28163810380e1808380237fc37f827f427ea57e437de37d837ca77c627c417c217b857b047ac279a97943784877e377c1774476e37645760275a3754374c474a17462740373a37343732172e272a2724371c4716370e4708370236fe26f836f426ec46e826da76d626ce46cc16c446c026b466b026a846a426a0269c269636922690167e967a26781674266e3666465e46583652364e264a264816404632762c362a1624361e3618361426102608460235fc35f635f225ee25ec15e635de45d645d225ce25ca25c625c225bc35b635ae45a835a045984594258e35883582357c35782570456c2564455c45582552354c35444540253a35362532252a4522451c35163512250e2508350234fc34f444ec44e634e224de24ce84ca24c624bc54b634b224aa44a2449c3494448c448a1484347e347a2474346c446a1462445e24545450244e144834442440243c2434442c442824242420241c24182410440c23fe73f643f033ea33e243dc33d633d223ca43c623c033bc23b823b233ac33a4439e339a23981390438a338433786372336e23645360235a3354334e334833442340233e133833323330132a3324331a53181310430c230442fc42f442f022ec22ea12e432e022d462d212ce22cc12c822c042bc22b822b612b222ac3292d28c327c82782270426c2258a25612541252124c32482240423c223822342230222c222a12262220321c22144212120e220a2206220031fe11ee81ea21e431de31da21d431ce31c451c021b651b031ac21a4419e3196419031884184217e317a2172416e21683164215e315a2152414c3148214231385130412c21263120311a31162110310e1108310420fe30f830f230ec30e630e030ce90ca20c430c020bc20b250ae20ac10ac00a440a0209a30962092208c3084407c407a10743072106c305e704e804a2046203e4036402a602620222012800a400430002
def je10 (i : Nat) : Nat := (if i<1 then 0xa827491541caa98d04d45305d1e48e7e19144f50596a906a1280514e431ac52a5a380133cdca47a4e1dc70442559e4f74c883f0b941c1830b69c49d2aa1a381910e76c683b3020bb9105e8f1aa1c9459a48a8ee76ba508c185c5e1cb20652048218a2a1083518cf53e3010090f30e152a8c45e44244591895af5a91aa0cf662c318c34e82897c7808ee24c1cce6f872b5da455635046597d24c54827497910343b43a8cff8d3123d3447246a27925c2150718755218bc6e12ddcce3d12482c185b063c873946a1ecd8d54ea0828d178df0ea8d41dc71703161b1aa84397b1e8d491691a7498142722cbbdc50271ac1431a3922271472ec5e527044badba7418c0e35415f42ea6b18ec686a88009e634254954111549f23217469e9227f561047a82dd8752948883a2f497459f0aa34d42583ea87934c811a4565c2dd05f0e9306a48914a232777736c6b07821d234dd24b85a6fc6642d6048248c16b3e5e92e44bd453fe355740865ba5618439c4ab0b4688e053cc6a7c5e443a634dd1843a52861542c6ae05718e1635045521829a44b1d67875d51d70b4e8a8e058364395e480a8d560f739468931a29a2096eb8f46884889e920622974c8a484f572363d1a85d067a748712c5429488bc3eb0288c67e7a39439ba7987208051c6f8add237440e9d28876820544b2b2224eee73920aaee25a21b8d98d0e8f51aaa1e4cd20709e6345182c6aa74c9bc962efe94b5a34818d4717aa417c686b1a8a9ea453d14c395a1076af5051a0bc58490e24540e51a41002342c5ebae44a8420d49224042aa3481571ba011aabc8aa8793336aa6523cc6878cb4c42c97223a5250554880acd9229f4f60aa420c68ee2a758a6a62a9e92452486021490360da1216f232c7a974a9748ddcd5489c46ad4395221c7978c6aa73e829229d3947bf6832cabd4c5f305f9eaa13177364e8356a1c6910e521c1aef31c469947243975451a089a88abf74a21091a3cc69ac4991390832c423ada69b9e478f648201ec710c74d1a470b7751a813e9da46230e388c614c64446a1e828d352353125a21c279874a202f71ec14e30e7033c404f964d40b3081c2ea87934b61ba798d3f0e1528281d1075aa4f9d12c4446848c08d54ce4fc69cf23d548d4a9fb0b2f1c55e157688110a30e8a67f3d514681c9f704561c2a04269ab179e80d0e730f220f2f28d3a486234201a34cf8d098225a213a82aeb24c55dae985d40107212b06450f644895a10412a10862a9c91dea4429e9934f911ca60de3cc69551a692d9c0ae3a29e34c18709d502a55188630e13044d42e962445ecd1202550e9420a6a0990346945572b4894a797ac6aa94c9b8696e5b7f54ddcd8571cc9f2c9b20a3400608940c848d5067a74964fa7aa43980e343555116913491a44bc3184b54e3548823056a373c6a411a else 0x25c383e19961ce354d92d0a6a88550d413318312d111b6d97a030e404691a5093c2ce545058117f4b5546aace938929394d9b94d76f9829243d50931c0a2d38bcc5087a3a0c5ecb938c6a7e7127c78905763c3634b8859ca4488039d53e49541d2844f7fc6a645a514f1a93491b14b8d99d2c0e5549f1fc8a300ed15f731759ba45419ecc4105c99af46b1a7194495229f43150a3258a52ec111439111eabd4e63246cb063d0b15474c86e913583008792086065aa231034a24cc21ccb2b439d24c14029450e3e88dd288943a652c131540964b9fa8dbb0b40c2e5a3d7fc6a2643993b45a2a3f9d1411a431c496ec60bba7f311aa043d1a98bb89688458cc90d13e9264427042a6344b96065a8711f98954dc82b65db0baa1a46ad81da229ae68023430838d098223ea04f66248a291a35516b45c3941a049160703140495093143904028d4fa18a851a5c9629a5b4010f8913a497549f23c601d659a1f6c16dafc97303c8d4600943469ba7c85c71d0e2158d428b44150e71235428c6b0e4ba227c4a4455ead3d85cf5d2841482a7ca3a24c2450ba828a34ae27bce353438c397a8a469b89ec9a4c3a0a72550d4def0a01266122234b096294849e160d25bfdd30b1129a4010013d5046925d4e589685d4281246cb50f67013984dca30e88e7eed60924708275890f5228e28e44988d42c9c8885bb50d5372aca34c8873a0c01d2f1ba7f312443a811a3a135c0ae60c394684258d5a820284ce16a8551899e9035cb1b618043c9da652588804a44f058a4798d41661548e389182b525161ed18d335691a10d18ad0e614363553a8468e44e249f2a90c74875b8203cc3948d48d2f497229dc8632bd36b3a1cc13122182cf489484945480c5911e0abad146180aa8ae44324fe34a37fc2e8123773b4e872258d680cd8d54cba2874a22a8600ed5ea6d41842ce30b9892110e054c6a2a49aac8a0b1f85d50c0a1759c644cb3a43872480481924f93507656bd4146)
def jh10 (i : Nat) : Nat := 0x10120808fc0478023d011d808e004720237011a008d00462022701128087c0430021801090083c0414020a00fd807d803ea01ef00f6007b403d601e800f48079003c801e100ef8077003b601d900de006f4035e01a200d100684033e019a00cd80650031e018b00c40061c0300017f00be805e802f6017600b9005b802d8016b00b40059002be015c00ae0056842b0015800ab805500aa4014c00a28050002640131008f004780238011b008b0042802100100007f003f001e000ee0076003a811cc04e600730139081c408e23a7017380a9c04ce022700f38039c00ce0006f0037001b000d4206700330019400c60060022f001746cb8325c172e0a9704cb81e5c0d2e059701cb8005b182b8a15c40ae18570a2b8415c10ae0457002b8915828ac0856022b0015400a826530f298394c0ca6005219288a94444a21e5103288094400a0004f00260012a00920849002488120209008481e238d11c588e144700230e9106c882e4416220791038880e4405220010c008500401020001004c7e003e801e800f000741039081c020e008700238001c0d8dc5c6e2237031b850d8106c0436011b000d86c6a2e35151a898d43c6a1a350b1ac00d0046800330019000c4085c002d0016000ac005426280f14068a02c500e2803140009c004c002480110c088484420220c1104088104400220c10820841040321f170f8a87c4c3e1e1f0d0f8587c1c3e0a1f030f8007a003a081d020e800740038001b1e0d0e0686034281a0c0d01864083200191d0c0d8605c3026180f0c058601c300017000b00054002800130209000480022081000080e038641c2a0e140709838441c1e0e0c07040381c1c0a0e040700838001b000c1006040300018000b00050002440100808020400020700c340618030b018500c24060e0306018200c0c06040300018000a02031c010d0086404300216010a80850042602110107808380418020b01040081c040c020401018087000300016000a000480020000e000600018000000
def jHints10 (row : Nat) : List (Nat × Nat) :=
  let i := jFields10 row % 512
  let b := packedAt jb10 (i*16) 16
  (List.range (b % 32)).map fun j => Id.run do
    let i := b/32+j
    let i := packedAt je10 (i*9) 9
    let h := packedAt jh10 (i*17) 17
    return (h % 512,h/512)
def js9 (i : Nat) : Nat := 0x8425c6016001
def jm9 (i : Nat) : Nat := 0x39b8ffa87
def jr9 (i : Nat) : Nat := 0x0
def jv9 (i : Nat) : Nat := 0xe900ed8d008b878a2682
def ji9 := jLookup 8 34 6 5 5 8 js9 jm9 jr9 jv9
def jc9d1 (i : Nat) : Nat :=
  let i := 0
  288
def jc9d2a (i : Nat) : Nat := 0xe4
def jc9d2b (i : Nat) : Nat := 0x5c1534c110
def jc9d2 (i : Nat) : Nat :=
  let x := packedAt jc9d2a (i*2) 2
  let i := x % 4
  (jc9d1 (x/4)) ||| ((packedAt jc9d2b (i*10) 10) <<< 10)
def jc9d3a (i : Nat) : Nat := 0x3deb6cb0b9f75c6d96175944d24481c6140
def jc9d3b (i : Nat) : Nat := 0x68596605805c15454d5254542505312909121483
def jc9d3 (i : Nat) : Nat :=
  let x := packedAt jc9d3a (i*6) 6
  let i := x % 16
  (jc9d2 (x/16)) ||| ((packedAt jc9d3b (i*10) 10) <<< 20)
def jc9d4a (i : Nat) : Nat := 0xb26c2ac68fa3a69952538960b7ade2721ad64d926356c59d6458d6052d2a451104310b419013c8d4330cb2cc8c1ac4e0a414
def jc9d4b (i : Nat) : Nat := 0x1b56c596611815d17358d5354943509312e8b82c4a42849121481
def jc9d4 (i : Nat) : Nat :=
  let x := packedAt jc9d4a (i*10) 10
  let i := x % 32
  (jc9d3 (x/32)) ||| ((packedAt jc9d4b (i*10) 10) <<< 30)
def jc9d5a (i : Nat) : Nat := 0x9df36a67cca94b2463445489f0e60cbf3798eb1ce39b718e2db3b4e64ec5d832f15b0b5568ad059ab1d62ac2570a1541a7b4988b1009f23ac72ce11a432c5e4b495d24c4688c8f71ec3305c8870c012010818
def jc9d5b (i : Nat) : Nat := 0x725c6715c3709c16d9b56d1b369998659945d1735915354942484cb324c12e8b92dca421483
def jc9d5 (i : Nat) : Nat :=
  let x := packedAt jc9d5a (i*11) 11
  let i := x % 32
  (jc9d4 (x/32)) ||| ((packedAt jc9d5b (i*10) 10) <<< 40)
def jc9d6a (i : Nat) : Nat := 0xec3e90e5ce5be1ce19e10ddfd89d5fd10cd7cd6c9dc5dc0ac02bc1b83b81b80b42b21b20b02adcadba9ca99a8fa64a119e39859569459099058cb88c85c84d84984880d7c47a378f75f7137087067046cb6a56696215de5da58556756656456355f50d4d24954874814804524233cb39f35d35a30e2e828b2592081e01a819719619418b1591230e90e70e40e209f067066064063061018
def jc9d6b (i : Nat) : Nat := 0x771db769d9761d7759d474dd2745ca71dc6715c470dc26e1b66d5b469d986597454d21370da364d8344c9318ba2e4b72d8a929000
def jc9d6 (i : Nat) : Nat :=
  let x := packedAt jc9d6a (i*12) 12
  let i := x % 64
  (jc9d5 (x/64)) ||| ((packedAt jc9d6b (i*10) 10) <<< 50)
def jmasks9 (i : Nat) : Nat := 0xffc1ff43fe17fb0ff25fda3fa97f42fe55f74be9b7ce4f785df4bbe877c2ef25ddabbb1772aeda5d9abaeb75b6e9e9c6f77f86fe0dfb1bf537e96fc2df71bed37ba6f70deb9bcf36fa6df0dbb9b6f36db6bd2cfe19f633e96778ceb57f82fe95fd0bf917ed2fd45fa2bf357e4afb45f62beb177a2ef15dd2b7d56fa2df15bd8b7a55f4abdb56bdabf54fba7f84fd89fa53eea7db4f6a9bf535fa3fc47ec8ef517d9ff83fd2
def jfields9 (i : Nat) : Nat := 0x2cf9056b23364a41da52014b45aca223e310eba726de890672e15b07043a36d104906c7a00054d88927ee923e6895ed888f2e8e77663101431b5c3ae8ecc72d85108c19c51aadc41b6c65a353f5da1760ce73a64b058e30f073572420b12135db118ac91452c0b045f6612e21292c45a403055a10d2173388459ab00a6429131804850c87aacd8f1ae12906c7c84f5caa62f5309b108f5940d9c9d2a0303e3a638452ca74921c0212db23a8f8810868819d436a2a04608fe26479e933b7a91c8088da73261b5320fe01a5e1ccaa703931c304e010a000ba9825a9530824a15c6d4832aa509121cf29902b0499a1a497172392790aa4078e90394151b25b8cbef459e022a9cb12f928843243b0a01b0370a82a0444fc1e1660968802c6580
def jFields9 (i : Nat) := packedAt jfields9 (i*21) 21
def jRecipe9 (i : Nat) : Nat × Nat :=
  let x := jFields9 i
  let i := (x/128)%128
  (jc9d6 (x/16384),packedAt jmasks9 (i*15) 15)
def jb9 (i : Nat) : Nat := 0xf21f01ee1ec1e82e61de4dc1d82d42ce3ca2c43c21c01bc2ba1b81b42b21ae2a83a61a229e29a29439028c28828428027c27a17817617036e16c16826426215e25a25815425214e24a24814614414213e23e03c13a13813233012c22442211e21a21621220e20c1063003
def je9 (i : Nat) : Nat := 0x198b1ce09414add91a1d0c8bd6271088771450c78edc8f2ea171c385cdb63ed89808861ea17f095940c0da932c90b046a99b923f0099f50dcfc04105aa144257a3124468d5454d0e4ca4cab2078bb83b1a0120a053052638e120ecc12c74b60054e9871f2e25f3080e0e34
def jh9 (i : Nat) : Nat := 0x404760236010c0082c03dc017e00af0056c0280013200980040001d400de006e0036001a800c60059002c1815c00aa0054002900140009e004c002580124dc8800430020000f80078003a3b1a8d8d4006600320016800ac2c5000270012980882044321f000f02074003a7a18000b00050002608103107000342018000c00050402010100008320317018b00c00051e0107808b0003800
def jHints9 (row : Nat) : List (Nat × Nat) :=
  let i := jFields9 row % 128
  let b := packedAt jb9 (i*12) 12
  (List.range (b % 32)).map fun j => Id.run do
    let i := b/32+j
    let i := packedAt je9 (i*7) 7
    let h := packedAt jh9 (i*17) 17
    return (h % 512,h/512)
def js8 (i : Nat) : Nat := 0x2
def jm8 (i : Nat) : Nat := 0x7594
def jr8 (i : Nat) : Nat := 0x0
def jv8 (i : Nat) : Nat := 0x21000ee6
def ji8 := jLookup 3 15 2 4 3 6 js8 jm8 jr8 jv8
def jc8d1 (i : Nat) : Nat :=
  let i := 0
  288
def jc8d2a (i : Nat) : Nat := 0x24
def jc8d2b (i : Nat) : Nat := 0x17054d30
def jc8d2 (i : Nat) : Nat :=
  let x := packedAt jc8d2a (i*2) 2
  let i := x % 4
  (jc8d1 (x/4)) ||| ((packedAt jc8d2b (i*10) 10) <<< 10)
def jc8d3a (i : Nat) : Nat := 0x51a418820
def jc8d3b (i : Nat) : Nat := 0x6598154d524c491
def jc8d3 (i : Nat) : Nat :=
  let x := packedAt jc8d3a (i*5) 5
  let i := x % 8
  (jc8d2 (x/8)) ||| ((packedAt jc8d3b (i*10) 10) <<< 20)
def jc8d4a (i : Nat) : Nat := 0xc2a81e511343
def jc8d4b (i : Nat) : Nat := 0x19660553548b129091
def jc8d4 (i : Nat) : Nat :=
  let x := packedAt jc8d4a (i*6) 6
  let i := x % 8
  (jc8d3 (x/8)) ||| ((packedAt jc8d4b (i*10) 10) <<< 30)
def jc8d5a (i : Nat) : Nat := 0xe79ea4272d98b04260a05
def jc8d5b (i : Nat) : Nat := 0x705b56999654d52508c12e8a4
def jc8d5 (i : Nat) : Nat :=
  let x := packedAt jc8d5a (i*7) 7
  let i := x % 16
  (jc8d4 (x/16)) ||| ((packedAt jc8d5b (i*10) 10) <<< 40)
def jc8d6a (i : Nat) : Nat := 0xbbb6a3958a746c625d4841403e27190a
def jc8d6b (i : Nat) : Nat := 0x1d8745c670db66d5a76617454cd9360d1324b7
def jc8d6 (i : Nat) : Nat :=
  let x := packedAt jc8d6a (i*8) 8
  let i := x % 16
  (jc8d5 (x/16)) ||| ((packedAt jc8d6b (i*10) 10) <<< 50)
def jc8d7a (i : Nat) : Nat := 0xfaecded0ccb6b2ad99948c8477685d4f4331291b05
def jc8d7b (i : Nat) : Nat := 0x7b5ec799c6661743b4eb3a4e8364c92e8b92dca9
def jc8d7 (i : Nat) : Nat :=
  let x := packedAt jc8d7a (i*8) 8
  let i := x % 16
  (jc8d6 (x/16)) ||| ((packedAt jc8d7b (i*10) 10) <<< 60)
def jmasks8 (i : Nat) : Nat := 0xf592f4d0f342ef90ef60ef28ed92e5b4df90ddd0dd92d36ad0bdbf82b3c2aeb49f929f429dd294f486bd
def jfields8 (i : Nat) : Nat := 0x5b8892a4ac81420ce584290206977349aa2a408c725309a42399841584510238a09e5228c66f0
def jFields8 (i : Nat) := packedAt jfields8 (i*14) 14
def jRecipe8 (i : Nat) : Nat × Nat :=
  let x := jFields8 i
  let i := (x/16)%32
  (jc8d7 (x/512),packedAt jmasks8 (i*16) 16)
def jb8 (i : Nat) : Nat := 0x1c36096150521388c12088010802
def je8 (i : Nat) : Nat := 0xc4b13eca537829d60
def jh8 (i : Nat) : Nat := 0x40474015e006e002ca7944009e1049001f1d8d4005a0027000f04074002c0808
def jHints8 (row : Nat) : List (Nat × Nat) :=
  let i := jFields8 row % 16
  let b := packedAt jb8 (i*10) 10
  (List.range (b % 32)).map fun j => Id.run do
    let i := b/32+j
    let i := packedAt je8 (i*4) 4
    let h := packedAt jh8 (i*17) 17
    return (h % 512,h/512)
def jm7 (i : Nat) : Nat := 0x43
def jr7 (i : Nat) : Nat := 0x0
def jv7 (i : Nat) : Nat := 0x12
def ji7 := jLookup 1 7 0 2 2 5 (fun _ => 0) jm7 jr7 jv7
def jc7d1 (i : Nat) : Nat :=
  let i := 0
  288
def jc7d2a (i : Nat) : Nat := 0x2
def jc7d2b (i : Nat) : Nat := 0x54d30
def jc7d2 (i : Nat) : Nat :=
  let x := packedAt jc7d2a (i*1) 1
  let i := x % 2
  (jc7d1 (x/2)) ||| ((packedAt jc7d2b (i*10) 10) <<< 10)
def jc7d3a (i : Nat) : Nat := 0xe88
def jc7d3b (i : Nat) : Nat := 0x6595354931
def jc7d3 (i : Nat) : Nat :=
  let x := packedAt jc7d3a (i*3) 3
  let i := x % 4
  (jc7d2 (x/4)) ||| ((packedAt jc7d3b (i*10) 10) <<< 20)
def jc7d4a (i : Nat) : Nat := 0x19a2903
def jc7d4b (i : Nat) : Nat := 0x196605532c4a4
def jc7d4 (i : Nat) : Nat :=
  let x := packedAt jc7d4a (i*5) 5
  let i := x % 8
  (jc7d3 (x/8)) ||| ((packedAt jc7d4b (i*10) 10) <<< 30)
def jc7d5a (i : Nat) : Nat := 0x95a510243
def jc7d5b (i : Nat) : Nat := 0x69996548c12e8a4
def jc7d5 (i : Nat) : Nat :=
  let x := packedAt jc7d5a (i*6) 6
  let i := x % 8
  (jc7d4 (x/8)) ||| ((packedAt jc7d5b (i*10) 10) <<< 40)
def jc7d6a (i : Nat) : Nat := 0xaa4650343
def jc7d6b (i : Nat) : Nat := 0x761b66d4d8344b7
def jc7d6 (i : Nat) : Nat :=
  let x := packedAt jc7d6a (i*6) 6
  let i := x % 8
  (jc7d5 (x/8)) ||| ((packedAt jc7d6b (i*10) 10) <<< 50)
def jc7d7a (i : Nat) : Nat := 0xa23752244
def jc7d7b (i : Nat) : Nat := 0x719983a0ba2dca9
def jc7d7 (i : Nat) : Nat :=
  let x := packedAt jc7d7a (i*6) 6
  let i := x % 8
  (jc7d6 (x/8)) ||| ((packedAt jc7d7b (i*10) 10) <<< 60)
def jc7d8a (i : Nat) : Nat := 0xb2781a655383
def jc7d8b (i : Nat) : Nat := 0x7f5fc7b5ec3f8f8324b9
def jc7d8 (i : Nat) : Nat :=
  let x := packedAt jc7d8a (i*6) 6
  let i := x % 8
  (jc7d7 (x/8)) ||| ((packedAt jc7d8b (i*10) 10) <<< 70)
def jmasks7 (i : Nat) : Nat := 0xe6c8692d3268580bdaf4850daa69a10eb4
def jfields7 (i : Nat) : Nat := 0x7b82a557cf0c08c
def jFields7 (i : Nat) := packedAt jfields7 (i*8) 8
def jRecipe7 (i : Nat) : Nat × Nat :=
  let x := jFields7 i
  let i := (x/4)%8
  (jc7d8 (x/32),packedAt jmasks7 (i*17) 17)
def jb7 (i : Nat) : Nat := 0x82610300
def je7 (i : Nat) : Nat := 0x1913
def jh7 (i : Nat) : Nat := 0x6e002c8009c003c0016
def jHints7 (row : Nat) : List (Nat × Nat) :=
  let i := jFields7 row % 4
  let b := packedAt jb7 (i*8) 8
  (List.range (b % 32)).map fun j => Id.run do
    let i := b/32+j
    let i := packedAt je7 (i*3) 3
    let h := packedAt jh7 (i*17) 17
    return (h % 512,h/512)
def jm6 (i : Nat) : Nat := 0x1
def jr6 (i : Nat) : Nat := 0x0
def ji6 := jLookup 1 4 0 1 0 0 (fun _ => 0) jm6 jr6 (fun _ => 0)
def jc6d1 (i : Nat) : Nat :=
  let i := 0
  288
def jc6d2a (i : Nat) : Nat := 0x2
def jc6d2b (i : Nat) : Nat := 0x54d30
def jc6d2 (i : Nat) : Nat :=
  let x := packedAt jc6d2a (i*1) 1
  let i := x % 2
  (jc6d1 (x/2)) ||| ((packedAt jc6d2b (i*10) 10) <<< 10)
def jc6d3a (i : Nat) : Nat := 0x188
def jc6d3b (i : Nat) : Nat := 0x19654d52
def jc6d3 (i : Nat) : Nat :=
  let x := packedAt jc6d3a (i*3) 3
  let i := x % 4
  (jc6d2 (x/4)) ||| ((packedAt jc6d3b (i*10) 10) <<< 20)
def jc6d4a (i : Nat) : Nat := 0x861
def jc6d4b (i : Nat) : Nat := 0x19654cb1
def jc6d4 (i : Nat) : Nat :=
  let x := packedAt jc6d4a (i*4) 4
  let i := x % 4
  (jc6d3 (x/4)) ||| ((packedAt jc6d4b (i*10) 10) <<< 30)
def jc6d5a (i : Nat) : Nat := 0xa41
def jc6d5b (i : Nat) : Nat := 0x1a6658c1
def jc6d5 (i : Nat) : Nat :=
  let x := packedAt jc6d5a (i*4) 4
  let i := x % 4
  (jc6d4 (x/4)) ||| ((packedAt jc6d5b (i*10) 10) <<< 40)
def jc6d6a (i : Nat) : Nat := 0x960
def jc6d6b (i : Nat) : Nat := 0x1b6360d1
def jc6d6 (i : Nat) : Nat :=
  let x := packedAt jc6d6a (i*4) 4
  let i := x % 4
  (jc6d5 (x/4)) ||| ((packedAt jc6d6b (i*10) 10) <<< 50)
def jc6d7a (i : Nat) : Nat := 0x942
def jc6d7b (i : Nat) : Nat := 0x1c64c0e8
def jc6d7 (i : Nat) : Nat :=
  let x := packedAt jc6d7a (i*4) 4
  let i := x % 4
  (jc6d6 (x/4)) ||| ((packedAt jc6d7b (i*10) 10) <<< 60)
def jc6d8a (i : Nat) : Nat := 0xa41
def jc6d8b (i : Nat) : Nat := 0x1523e0b9
def jc6d8 (i : Nat) : Nat :=
  let x := packedAt jc6d8a (i*4) 4
  let i := x % 4
  (jc6d7 (x/4)) ||| ((packedAt jc6d8b (i*10) 10) <<< 70)
def jc6d9a (i : Nat) : Nat := 0x960
def jc6d9b (i : Nat) : Nat := 0x1fd7b0c9
def jc6d9 (i : Nat) : Nat :=
  let x := packedAt jc6d9a (i*4) 4
  let i := x % 4
  (jc6d8 (x/4)) ||| ((packedAt jc6d9b (i*10) 10) <<< 80)
def jmasks6 (i : Nat) : Nat := 0x38690d324304b4
def jfields6 (i : Nat) : Nat := 0x41a
def jFields6 (i : Nat) := packedAt jfields6 (i*4) 4
def jRecipe6 (i : Nat) : Nat × Nat :=
  let x := jFields6 i
  let i := (x/1)%4
  (jc6d9 (x/4),packedAt jmasks6 (i*18) 18)
def jHints6 (row : Nat) : List (Nat × Nat) :=
  let i := jFields6 row % 1
  let b := 0
  (List.range (b % 32)).map fun j => Id.run do
    let i := b/32+j
    let i := 0
    let h := 0
    return (h % 512,h/512)
def jc5d1 (i : Nat) : Nat :=
  let i := 0
  288
def jc5d2 (i : Nat) : Nat :=
  let x := 0
  let i := x % 1
  (jc5d1 (x/1)) ||| ((339) <<< 10)
def jc5d3 (i : Nat) : Nat :=
  let x := 0
  let i := x % 1
  (jc5d2 (x/1)) ||| ((406) <<< 20)
def jc5d4 (i : Nat) : Nat :=
  let x := 0
  let i := x % 1
  (jc5d3 (x/1)) ||| ((177) <<< 30)
def jc5d5 (i : Nat) : Nat :=
  let x := 0
  let i := x % 1
  (jc5d4 (x/1)) ||| ((422) <<< 40)
def jc5d6 (i : Nat) : Nat :=
  let x := 0
  let i := x % 1
  (jc5d5 (x/1)) ||| ((216) <<< 50)
def jc5d7 (i : Nat) : Nat :=
  let x := 0
  let i := x % 1
  (jc5d6 (x/1)) ||| ((304) <<< 60)
def jc5d8 (i : Nat) : Nat :=
  let x := 0
  let i := x % 1
  (jc5d7 (x/1)) ||| ((338) <<< 70)
def jc5d9 (i : Nat) : Nat :=
  let x := 0
  let i := x % 1
  (jc5d8 (x/1)) ||| ((169) <<< 80)
def jc5d10 (i : Nat) : Nat :=
  let x := 0
  let i := x % 1
  (jc5d9 (x/1)) ||| ((492) <<< 90)
def jFields5 (i : Nat) := 0
def jRecipe5 (i : Nat) : Nat × Nat :=
  let x := jFields5 i
  let i := (x/1)%1
  (jc5d10 (x/1),491664)
def jHints5 (row : Nat) : List (Nat × Nat) :=
  let i := jFields5 row % 1
  let b := 0
  (List.range (b % 32)).map fun j => Id.run do
    let i := b/32+j
    let i := 0
    let h := 0
    return (h % 512,h/512)
def jCount : Nat → Nat
  | 5 => 1
  | 6 => 3
  | 7 => 8
  | 8 => 22
  | 9 => 109
  | 10 => 647
  | 11 => 1461
  | 12 => 593
  | 13 => 34
  | 14 => 2
  | _ => 0
def jDep : Nat → Nat
  | 5 => 10
  | 6 => 9
  | 7 => 8
  | 8 => 7
  | 9 => 6
  | 10 => 5
  | 11 => 4
  | 12 => 3
  | 13 => 2
  | 14 => 1
  | _ => 0
def jRecipe : Nat → Nat → Nat × Nat
  | 5 => jRecipe5
  | 6 => jRecipe6
  | 7 => jRecipe7
  | 8 => jRecipe8
  | 9 => jRecipe9
  | 10 => jRecipe10
  | 11 => jRecipe11
  | 12 => jRecipe12
  | 13 => jRecipe13
  | 14 => jRecipe14
  | _ => fun _ => (0,0)
def jHints : Nat → Nat → List (Nat × Nat)
  | 5 => jHints5
  | 6 => jHints6
  | 7 => jHints7
  | 8 => jHints8
  | 9 => jHints9
  | 10 => jHints10
  | 11 => jHints11
  | 12 => jHints12
  | 13 => jHints13
  | 14 => jHints14
  | _ => fun _ => []
def jIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => ji6
  | 7 => ji7
  | 8 => ji8
  | 9 => ji9
  | 10 => ji10
  | 11 => ji11
  | 12 => ji12
  | 13 => ji13
  | 14 => ji14
  | _ => fun _ => none

def mF0 : MFace := ((1,0,510,0,12),0x100000001000001000000000000000000000000010000001000000000000000040000000001001040,0x40000000000000000000000000000001000000000000000010100000000000000040000100100000000000004040000000000,[6,24,160,320,116,402,12,66,288,132,42,264,200,276,50,104,138,208])
def mF2 : MFace := ((2,0,509,0,12),0x100000001000001000000000000000000000000010000001000000000000000000000000201021000,0x10002000000000000000000000000001000200000000000010200000000000000000000100100000000200000000000000000,[12,17,160,320,116,201,24,33,132,264,261,288,400,104,69,208,276,385])
def mF6 : MFace := ((4,0,507,0,12),0x100000001000001000000000000000000000000010000000000000000000000040000000201020008,0x40002000000000000000000000000000000000000000000010200000000000000040000010100000000000004040000000000,[3,24,160,320,201,402,17,66,264,33,42,288,112,385,50,104,138,208])
def mF12 : MFace := ((7,0,504,0,7),0x100000001000001000000000000000000000000010000000000000000000000000000000001000000,0x10000000000000000000000000000000000000000000000010100000000000000000000010100000000000000000000000000,[24,160,320,104,400,264,112,200,288,208])
def mF14 : MFace := ((8,0,503,0,12),0x100000001000000000000000000000000000000010000001000000000000000040000000200020048,0x40002000000000000000000000000001000200000000000010002000000000000000000100000000000200004000000000000,[3,132,288,17,66,116,402,320,160,6,193,33,261,50,69,208,276,385])
def mF16 : MFace := ((9,0,486,0,8),0x100000001000000000000000000000000000000010000001000000000000000040000000000000040,0x40000000000000000000000000000001000000000000000010000000000000000000000100000000000000004000000000000,[6,160,320,116,402,66,132,288,50,208,276])
def mF18 : MFace := ((12,0,499,0,9),0x100000001000000000000000000000000000000010000000000000000000000040000000200020008,0x40002000000000000000000000000000000000000000000010002000000000000000000010000000000000004000000000000,[3,160,320,402,17,66,112,288,193,33,50,385,208])
def mF21 : MFace := ((14,0,497,0,7),0x100000001000000000000000000000000000000010000000000000000000000000000000200020000,0x10002000000000000000000000000000000000000000000010002000000000000000000010000000000000000000000000000,[17,160,320,112,385,33,193,400,288,208])
def mF26 : MFace := ((17,0,494,0,11),0x100000001000001000000000000000000000000010000001000000000000000040000000000001040,0x4000000000000000000000000000000100000000000000100000000000000040000000110000000000000040000000000,[6,160,264,66,42,12,320,100,386,200,132,288,104,138,260])
def mF28 : MFace := ((19,0,492,0,8),0x100000001000001000000000000000000000000010000001000000000000000000000000000001000,0x1000000000000000000000000000000100000000000000100000000000000000000000110000000000000000000000000,[12,160,320,100,200,132,264,288,104,260,384])
def mF30 : MFace := ((21,0,490,0,7),0x100000001000001000000000000000000000000010000000000000000000000040000000000000000,0x4000000000000000000000000000000000000000000000100000000000000040000000100000000000000040000000000,[66,160,264,42,200,386,288,320,104,138])
def mF32 : MFace := ((24,0,487,0,11),0x100000001000000000000000000000000000000010000001000000000000000040000000200000048,0x6000000000000000000000000000000200000000000000002000000000000000000000010000000200000000400000000,[3,132,288,66,69,386,33,320,100,6,160,193,261,34,385])
def mF34 : MFace := ((25,0,486,0,8),0x100000001000000000000000000000000000000010000001000000000000000040000000000000040,0x4000000000000000000000000000000100000000000000001000000000000000000000010000000000000000400000000,[6,160,320,100,386,66,132,288,34,192,260])
def mF35 : MFace := ((9,16,486,0,8),0x1000000010000000000000000000000000000000100000010000000000000000400000000000000400000,0x40000000000000000000000000000001000000000000000010000000000000000000000100000000000000004000000000000,[22,176,336,116,402,82,148,304,50,208,276])
def mF41 : MFace := ((32,0,479,0,12),0x100000000000001000000000000000000000000000000001000000000000000040000000001021048,0x40002000000000000000000000000001000200000000000010200000000000000040000000000001000200000000000000000,[3,12,320,17,201,132,402,24,66,264,84,6,261,138,69,208,276,385])
def mF45 : MFace := ((35,0,476,0,7),0x100000000000001000000000000000000000000000000001000000000000000000000000001001000,0x10000000000000000000000000000001000000000000000010100000000000000000000000000001000000000000000000000,[12,320,84,24,132,200,400,264,276,208])
def mF50 : MFace := ((49,0,462,0,8),0x100000000000001000000000000000000000000000000001000000000000000040000000000001040,0x4000000000000000000000000000000100000000000000100000000000000040000000000000000100000000000000000,[6,264,138,66,132,200,386,320,12,68,260])
def mF53 : MFace := ((56,0,455,0,7),0x100000000000000000000000000000000000000000000001000000000000000040000000000000048,0x6000000000000000000000000000000200000000000000002000000000000000000000000000000200000000000000000,[3,132,320,69,386,6,193,261,66,385])
def mF56 : MFace := ((66,0,445,0,11),0x1000001000000000000000000000000010000001000000000000000000000000201021000,0x10002000000000000000000000000001000200000000000000000000000000000020000000000000000000010010000000000,[12,17,160,264,52,137,132,288,261,400,24,33,40,276,385])
def mF58 : MFace := ((67,0,444,0,8),0x1000001000000000000000000000000010000001000000000000000000000000001001000,0x10000000000000000000000000000001000000000000000000000000000000000010000000000000000000010010000000000,[12,160,52,24,400,288,132,264,40,276,136])
def mF60 : MFace := ((70,0,441,0,8),0x1000001000000000000000000000000010000000000000000000000000000000201020000,0x10002000000000000000000000000000000000000000000000000000000000000020000000000000000000001010000000000,[17,160,264,137,400,24,33,288,40,385,48])
def mF62 : MFace := ((74,0,437,0,7),0x1000000000000000000000000000000010000001000000000000000000000000200020000,0x10002000000000000000000000000001000200000000000000000000000000000000000000000000000000010000000000000,[17,132,288,52,385,33,261,400,160,276])
def mF64 : MFace := ((80,0,431,0,11),0x1000001000000000000000000000000010000001000000000000000000000000200001048,0x6000000000000000000000000000000200000000000000000000000000000060000000000000000000000041000000000,[3,12,160,264,42,261,6,33,137,132,386,288,36,138,385])
def mF65 : MFace := ((83,0,428,0,7),0x1000001000000000000000000000000010000001000000000000000000000000000001000,0x1000000000000000000000000000000100000000000000000000000000000010000000000000000000000011000000000,[12,160,36,264,136,132,288,260,40,384])
def mF66 : MFace := ((96,0,415,0,9),0x1000000000000000000000000000000001000000000000000000000000001021048,0x40002000000000000000000000000001000200000000000000000000000000000060000000000000000000000000000000000,[3,12,402,17,132,264,137,261,6,24,138,276,385])
def mF72 : MFace := ((132,0,379,0,11),0x100000001000001000000000000000000000000000000000000000000000000040000000201020008,0x400020000000000000000000000000000000000010100000002000004040000000000,[3,24,288,66,42,17,73,274,264,33,112,320,50,104,257])
def mF74 : MFace := ((133,0,378,0,7),0x100000001000001000000000000000000000000000000000000000000000000040000000001000000,0x400000000000000000000000000000000000000010100000000000004040000000000,[24,66,288,42,112,274,264,320,104,50])
def mF75 : MFace := ((134,0,377,0,8),0x100000001000001000000000000000000000000000000000000000000000000000000000201020000,0x100020000000000000000000000000000000000010100000002000000000000000000,[17,264,73,33,112,320,24,288,104,257,272])
def mF80 : MFace := ((140,0,371,0,8),0x100000001000000000000000000000000000000000000000000000000000000040000000200020008,0x400020000000000000000000000000000000000010000000000020004000000000000,[3,288,50,17,66,112,274,320,33,65,257])
def mF83 : MFace := ((144,0,367,0,11),0x100000001000001000000000000000000000000000000000000000000000000040000000200001048,0x240000000000000000000000000000000000000110000002200000040000000000,[3,12,288,66,42,69,33,320,261,6,264,73,100,104,258])
def mF85 : MFace := ((160,0,351,0,11),0x100000000000001000000000000000000000000000000000000000000000000040000000001021048,0x1400200000000000000000000000000000000000000000001002200000000000000400,[3,12,320,17,69,274,6,24,73,66,264,84,261,10,276])
def mF88 : MFace := ((164,0,347,0,8),0x100000000000001000000000000000000000000000000000000000000000000040000000001020008,0x400020000000000000000000000000000000000000000000102000000000000000400,[3,24,320,73,274,17,66,264,10,80,257])
def mF89 : MFace := ((36,128,347,0,8),0x10000000000000100000000000000000000000000000000000000000000000004000000000102000800000000000000000000000000000000,0x40002000000000000000000000000000000000000000000010200000000000000040000000000000000000000000000000000,[131,152,448,201,402,145,194,392,138,208,385])
def mF93 : MFace := ((192,0,319,0,11),0x1000001000000000000000000000000000000000000000000000000000000000201021048,0x1400200000000000000000000000000000000000000000000000000014040000000200,[3,12,288,17,42,261,6,24,52,274,33,264,9,50,276])
def mF94 : MFace := ((198,0,313,0,7),0x1000001000000000000000000000000000000000000000000000000000000000201020000,0x100020000000000000000000000000000000000000000000000000001010000000200,[17,264,9,33,48,24,288,257,40,272])
def mF95 : MFace := ((256,0,255,0,12),0x10000001000000000000000040000000201021048,0x10200000000000004040000100100000000200004040000000000,[3,12,160,17,66,116,201,24,132,33,42,6,146,69,50,104,138,208])
def mF96 : MFace := ((258,0,189,0,8),0x10000001000000000000000000000000201021000,0x10200000000000000000000100100000000200000000000000000,[12,17,160,116,201,24,33,132,69,104,208])
def mF98 : MFace := ((264,0,247,0,9),0x10000001000000000000000040000000200020048,0x10002000000000004000000100000000000200004000000000000,[3,132,116,17,66,160,146,193,6,33,50,69,208])
def mF101 : MFace := ((268,0,243,0,7),0x10000000000000000000000040000000200020008,0x10002000000000004000000010000000000000004000000000000,[3,160,50,193,17,66,112,146,33,208])
def mF103 : MFace := ((273,0,238,0,7),0x10000001000000000000000040000000000001040,0x100000000000000040000000110000000000000040000000000,[6,160,42,12,66,100,200,132,138,104])
def mF106 : MFace := ((288,0,223,0,9),0x1000000000000000040000000001021048,0x10200000000000004040000000000001000200000000000000000,[3,12,201,17,66,132,24,84,146,6,69,138,208])
def mF110 : MFace := ((296,0,215,0,7),0x1000000000000000040000000000020048,0x10002000000000004000000000000001000200000000000000000,[3,132,69,146,17,66,84,193,6,208])
def mF112 : MFace := ((304,0,207,0,6),0x1000000000000000040000000000001048,0x200000000000000040000000000000000200000000000000000,[3,201,12,66,132,69,138,6])
def mF116 : MFace := ((320,0,191,0,11),0x10000001000000000000000000000000201021048,0x4060000000000000000000014040000000020,[3,12,160,17,42,6,24,52,137,146,33,132,5,50,138])
def mF120 : MFace := ((324,0,187,0,7),0x10000000000000000000000000000000201020008,0x4060000000000000000000004040000000000,[3,24,160,42,137,146,17,33,50,138])
def mF144 : MFace := ((11,0,484,0,5),0x100000001000000000000000000000000000000010000001000000000000000000000000000000000,0x10000000000000000000000000000001000000000000000010000000000000000000000100000000000000000000000000000,[132,116,288,320,400,160,208,276])
def mF159 : MFace := ((1,16,486,8,9),0x1000000010000000000000000000000000000000100000010000000000000000400000000000001400000,0x40000000000000000000000000000001000000000000000010000000000000000000000100000000000000004000000000000,[24,22,176,336,116,402,82,148,304,50,208,276])
def mF163 : MFace := ((18,0,493,0,9),0x100000001000001000000000000000000000000010000001000000000000000000000000200001000,0x2000000000000000000000000000000200000000000000200000000000000000000000110000000200000000000000000,[12,33,320,201,132,160,100,264,261,288,104,385,69])
def mF219 : MFace := ((15,16,480,0,4),0x1000000010000000000000000000000000000000100000000000000000000000000000000000000000000,0x10000000000000000000000000000000000000000000000010000000000000000000000010000000000000000000000000000,[176,112,336,400,304,208])
def mF223 : MFace := ((31,0,480,0,4),0x100000001000000000000000000000000000000010000000000000000000000000000000000000000,0x1000000000000000000000000000000000000000000000001000000000000000000000001000000000000000000000000,[160,96,320,384,288,192])
def mF224 : MFace := ((33,0,478,0,9),0x100000000000001000000000000000000000000000000001000000000000000040000000001001040,0x40000000000000000000000000000001000000000000000010100000000000000040000000000001000000000000000000000,[6,24,320,402,132,66,84,264,200,12,138,276,208])
def mF310 : MFace := ((48,0,462,0,8),0x100000000000001000000000000000000000000000000001000000000000000040000000000001048,0x6000000000000000000000000000000200000000000000200000000000000040000000000000000200000000000000000,[3,12,320,201,132,264,261,66,386,6,69,138,385])
def mF430 : MFace := ((65,0,446,0,9),0x1000001000000000000000000000000010000001000000000000000000000000001001040,0x40000000000000000000000000000001000000000000000000000000000000000040000000000000000000014040000000000,[6,24,160,402,264,288,42,132,52,12,138,276,50])
def mF438 : MFace := ((68,0,441,0,8),0x1000001000000000000000000000000010000000000000000000000000000000201020008,0x40002000000000000000000000000000000000000000000000000000000000000060000000000000000000004040000000000,[3,24,160,402,264,17,42,288,137,33,50,385,138])
def mF523 : MFace := ((81,0,430,0,8),0x1000001000000000000000000000000010000001000000000000000000000000000001040,0x4000000000000000000000000000000100000000000000000000000000000040000000000000000000000041000000000,[6,160,264,42,386,12,288,132,36,138,260])
def mF529 : MFace := ((82,0,429,0,8),0x1000001000000000000000000000000010000001000000000000000000000000200001000,0x2000000000000000000000000000000200000000000000000000000000000020000000000000000000000011000000000,[12,33,137,132,264,261,160,288,36,385,40])
def mF572 : MFace := ((85,2,424,0,4),0x4000004000000000000000000000000040000000000000000000000000000000000000000,0x4000000000000000000000000000000000000000000000000000000000000040000000000000000000000040000000000,[162,42,266,386,290,138])
def mF573 : MFace := ((87,0,424,0,4),0x1000001000000000000000000000000010000000000000000000000000000000000000000,0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000010000000000,[160,40,264,384,288,136])
def mF638 : MFace := ((97,0,414,0,6),0x1000000000000000000000000000000001000000000000000000000000001001040,0x40000000000000000000000000000001000000000000000000000000000000000040000000000000000000000000000000000,[6,402,24,132,264,138,276,12])
def mF644 : MFace := ((98,0,413,0,7),0x1000000000000000000000000000000001000000000000000000000000001021000,0x10002000000000000000000000000001000200000000000000000000000000000020000000000000000000000000000000000,[12,17,137,276,132,264,261,400,24,385])
def mF805 : MFace := ((114,1,396,0,4),0x2000000000000000000000000000000002000000000000000000000000000002000,0x2000000000000000000000000000000200000000000000000000000000000020000000000000000000000000000000000,[13,137,261,133,265,385])
def mF915 : MFace := ((129,0,382,0,9),0x100000001000001000000000000000000000000000000000000000000000000040000000001001040,0x1400000000000000000000000000000000000000100100000000000004040000000000,[6,24,288,116,66,12,42,320,274,264,104,276,50])
def mF919 : MFace := ((130,0,381,0,9),0x100000001000001000000000000000000000000000000000000000000000000000000000201021000,0x1000200000000000000000000000000000000000100100000002200000000000000000,[12,17,288,116,320,33,73,24,261,264,104,276,69])
def mF1005 : MFace := ((145,0,366,0,8),0x100000001000001000000000000000000000000000000000000000000000000040000000000001040,0x140000000000000000000000000000000000000110000000000000040000000000,[6,264,42,66,100,288,12,320,104,258,260])
def mF1013 : MFace := ((146,0,365,0,7),0x100000001000001000000000000000000000000000000000000000000000000000000000200001000,0x200000000000000000000000000000000000000110000002200000000000000000,[12,33,320,69,104,261,264,288,73,100])
def mF1022 : MFace := ((147,0,364,0,5),0x100000001000001000000000000000000000000000000000000000000000000000000000000001000,0x100000000000000000000000000000000000000110000000000000000000000000,[12,100,288,104,320,260,264])
def mF1028 : MFace := ((148,0,355,0,7),0x100000001000001000000000000000000000000000000000000000000000000040000000200000008,0x60000000000000000000000000000000000000100000002000000040000000000,[3,264,42,33,66,73,288,320,104,257,258])
def mF1057 : MFace := ((152,0,359,0,8),0x100000001000000000000000000000000000000000000000000000000000000040000000200000048,0x240000000000000000000000000000000000000010000000200000000400000000,[3,288,69,6,320,33,100,261,66,34,258])
def mF1067 : MFace := ((153,0,358,0,5),0x100000001000000000000000000000000000000000000000000000000000000040000000000000040,0x140000000000000000000000000000000000000010000000000000000400000000,[6,100,288,66,258,320,34,260])
def mF1097 : MFace := ((156,0,355,0,7),0x100000001000000000000000000000000000000000000000000000000000000040000000200000008,0x60000000000000000000000000000000000000001000000020000000400000000,[3,288,34,66,65,33,320,257,96,258])
def mF1101 : MFace := ((141,16,354,0,4),0x1000000010000000000000000000000000000000000000000000000000000000400000000000000000000,0x400000000000000000000000000000000000000010000000000000004000000000000,[82,50,304,112,274,336])
def mF1105 : MFace := ((157,0,354,0,4),0x100000001000000000000000000000000000000000000000000000000000000040000000000000000,0x40000000000000000000000000000000000000001000000000000000400000000,[66,34,288,96,258,320])
def mF1113 : MFace := ((154,4,353,0,4),0x1000000010000000000000000000000000000000000000000000000000000000000000002000000000,0x200000000000000000000000000000000000000010000000200000000000000000,[37,69,324,100,261,292])
def mF1115 : MFace := ((158,0,353,0,4),0x100000001000000000000000000000000000000000000000000000000000000000000000200000000,0x20000000000000000000000000000000000000001000000020000000000000000,[33,65,320,96,257,288])
def mF1116 : MFace := ((32,128,347,4,9),0x10000000000000100000000000000000000000000000000000000000000000004000000000102001800000000000000000000000000000000,0x40002000000000000000000000000000000000000000000010200000000000000040000000000000000000000000000000000,[132,131,152,448,201,402,145,194,392,138,208,385])
def mF1121 : MFace := ((161,0,350,0,8),0x100000000000001000000000000000000000000000000000000000000000000040000000001001040,0x1400000000000000000000000000000000000000000000001001000000000000000400,[6,24,320,84,274,12,66,264,10,276,72])
def mF1127 : MFace := ((162,0,349,0,7),0x100000000000001000000000000000000000000000000000000000000000000000000000001021000,0x1000200000000000000000000000000000000000000000001002200000000000000000,[12,17,320,69,276,73,24,264,84,261])
def mF1151 : MFace := ((39,128,344,0,4),0x10000000000000100000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000,0x10000000000000000000000000000000000000000000000010100000000000000000000000000000000000000000000000000,[152,200,448,400,392,208])
def mF1155 : MFace := ((167,0,344,0,4),0x100000000000001000000000000000000000000000000000000000000000000000000000001000000,0x100000000000000000000000000000000000000000000000101000000000000000000,[24,72,320,272,264,80])
def mF1193 : MFace := ((44,128,339,0,5),0x10000000000000000000000000000000000000000000000000000000000000004000000000002000800000000000000000000000000000000,0x40002000000000000000000000000000000000000000000010002000000000000000000000000000000000000000000000000,[131,402,448,145,193,194,208,385])
def mF1223 : MFace := ((176,0,334,0,7),0x100000000000001000000000000000000000000000000000000000000000000040000000000001048,0x240000000000000000000000000000000000000000000002200000000000000400,[3,12,320,69,73,261,6,264,66,10,258])
def mF1230 : MFace := ((177,0,334,0,7),0x100000000000001000000000000000000000000000000000000000000000000040000000000001040,0x140000000000000000000000000000000000000000000001100000000000000400,[6,264,10,66,68,12,320,258,72,260])
def mF1241 : MFace := ((178,0,332,0,4),0x100000000000001000000000000000000000000000000000000000000000000000000000000001000,0x200000000000000000000000000000000000000000000002200000000000000000,[12,69,320,73,261,264])
def mF1250 : MFace := ((178,1,332,0,4),0x200000000000002000000000000000000000000000000000000000000000000000000000000002000,0x200000000000000000000000000000000000000000000002200000000000000000,[13,69,321,73,261,265])
def mF1253 : MFace := ((52,128,331,0,5),0x10000000000000100000000000000000000000000000000000000000000000004000000000000000800000000000000000000000000000000,0x6000000000000000000000000000000000000000000000200000000000000040000000000000000000000000000000000,[131,201,392,194,386,448,138,385])
def mF1261 : MFace := ((53,128,330,0,4),0x10000000000000100000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000,0x4000000000000000000000000000000000000000000000100000000000000040000000000000000000000000000000000,[194,138,392,200,386,448])
def mF1268 : MFace := ((181,0,330,0,4),0x100000000000001000000000000000000000000000000000000000000000000040000000000000000,0x40000000000000000000000000000000000000000000001000000000000000400,[66,10,264,72,258,320])
def mF1289 : MFace := ((184,0,327,0,5),0x100000000000000000000000000000000000000000000000000000000000000040000000000000048,0x240000000000000000000000000000000000000000000000200000000000000000,[3,69,320,261,6,258,66])
def mF1294 : MFace := ((169,16,326,0,4),0x1000000000000000000000000000000000000000000000000000000000000000400000000000000400000,0x1400000000000000000000000000000000000000000000001000000000000000000000,[22,84,336,274,82,276])
def mF1297 : MFace := ((185,0,326,0,4),0x100000000000000000000000000000000000000000000000000000000000000040000000000000040,0x140000000000000000000000000000000000000000000000100000000000000000,[6,68,320,258,66,260])
def mF1329 : MFace := ((193,0,318,0,7),0x1000001000000000000000000000000000000000000000000000000000000000001001040,0x1400000000000000000000000000000000000000000000000000000014040000000000,[6,24,288,42,276,12,50,264,52,274])
def mF1335 : MFace := ((194,0,317,0,8),0x1000001000000000000000000000000000000000000000000000000000000000201021000,0x1000200000000000000000000000000000000000000000000000000010010000000200,[12,17,288,52,261,24,33,264,9,276,40])
def mF1344 : MFace := ((195,0,316,0,5),0x1000001000000000000000000000000000000000000000000000000000000000001001000,0x1000000000000000000000000000000000000000000000000000000010010000000000,[12,52,288,276,24,40,264])
def mF1350 : MFace := ((196,0,313,0,7),0x1000001000000000000000000000000000000000000000000000000000000000201020008,0x400020000000000000000000000000000000000000000000000000004040000000200,[3,24,288,42,274,17,264,33,9,50,257])
def mF1376 : MFace := ((197,2,312,0,4),0x4000004000000000000000000000000000000000000000000000000000000000004000000,0x400000000000000000000000000000000000000000000000000000004040000000000,[26,42,290,274,266,50])
def mF1378 : MFace := ((199,0,312,0,4),0x1000001000000000000000000000000000000000000000000000000000000000001000000,0x100000000000000000000000000000000000000000000000000000001010000000000,[24,40,288,272,264,48])
def mF1412 : MFace := ((202,0,305,0,4),0x1000000000000000000000000000000000000000000000000000000000000000200020000,0x1000200000000000000000000000000000000000000000000000000010000000000000,[17,52,288,261,33,276])
def mF1464 : MFace := ((202,4,305,0,4),0x10000000000000000000000000000000000000000000000000000000000000002000200000,0x1000200000000000000000000000000000000000000000000000000010000000000000,[21,52,292,261,37,276])
def mF1465 : MFace := ((206,0,305,0,4),0x1000000000000000000000000000000000000000000000000000000000000000200020000,0x100020000000000000000000000000000000000000000000000000001000000000000,[17,48,288,257,33,272])
def mF1602 : MFace := ((224,0,31,0,7),0x1000000000000000000000000000000000000000000000000000000000001021048,0x1400200000000000000000000000000000000000000000000000000000000000000600,[3,12,261,17,274,264,6,24,9,276,10])
def mF1611 : MFace := ((225,0,286,0,5),0x1000000000000000000000000000000000000000000000000000000000001001040,0x1400000000000000000000000000000000000000000000000000000000000000000400,[6,274,24,276,264,10,12])
def mF1649 : MFace := ((102,128,281,0,4),0x100000000000000000000000000000000000000000000000000000000000102000000000000000000000000000000000000,0x10002000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000,[145,137,392,400,152,385])
def mF1656 : MFace := ((230,0,281,0,4),0x1000000000000000000000000000000000000000000000000000000000001020000,0x100020000000000000000000000000000000000000000000000000000000000000200,[17,9,264,272,24,257])
def mF1787 : MFace := ((257,0,254,0,8),0x10000001000000000000000040000000001001040,0x10100000000000004040000100100000000000004040000000000,[6,24,160,116,66,138,12,132,42,146,200,50,104,208])
def mF1870 : MFace := ((272,0,175,0,8),0x10000001000000000000000040000000200001048,0x200000000000000040000000110000000200000040000000000,[3,12,160,201,66,33,42,132,100,6,69,138,104])
def mF1899 : MFace := ((276,0,227,0,5),0x10000000000000000000000040000000200000008,0x200000000000000040000000100000000000000040000000000,[3,201,160,66,42,33,104,138])
def mF1992 : MFace := ((289,0,222,0,7),0x1000000000000000040000000001001040,0x10100000000000004040000000000001000000000000000000000,[6,24,84,138,66,132,146,200,12,208])
def mF2164 : MFace := ((297,16,198,0,4),0x10000000000000000400000000000000400000,0x10000000000000004000000000000001000000000000000000000,[22,84,146,82,148,208])
def mF2166 : MFace := ((313,0,198,0,4),0x1000000000000000040000000000000040,0x1000000000000000400000000000000100000000000000000,[6,68,130,66,132,192])
def mF2195 : MFace := ((321,0,190,0,7),0x10000001000000000000000000000000001001040,0x4040000000000000000000014040000000000,[6,24,160,42,52,146,12,132,138,50])
def mF2225 : MFace := ((262,64,185,0,5),0x100000000000000000000000000000002010200000000000000000000,0x10200000000000000000000010100000000000000000000000000,[81,201,224,88,112,97,104,208])
def mF2243 : MFace := ((328,0,183,0,8),0x10000001000000000000000000000000200020048,0x4000200000000000000000014000000000020,[3,132,50,17,160,6,52,146,33,5,129])
def mF2273 : MFace := ((332,0,179,0,5),0x10000000000000000000000000000000200020008,0x4000200000000000000000004000000000000,[3,50,160,146,17,129,33])
def mF2288 : MFace := ((270,64,177,0,4),0x100000000000000000000000000000002000200000000000000000000,0x10002000000000000000000010000000000000000000000000000,[81,112,224,193,97,208])
def mF2296 : MFace := ((336,0,175,0,8),0x10000001000000000000000000000000200001048,0x60000000000000000000000041000000020,[3,12,160,42,137,6,33,132,5,138,36])
def mF2305 : MFace := ((337,0,174,0,5),0x10000001000000000000000000000000000001040,0x40000000000000000000000041000000000,[6,42,160,138,12,36,132])
def mF2321 : MFace := ((275,64,172,0,4),0x100000010000000000000000000000000000010000000000000000000,0x100000000000000000000000110000000000000000000000000,[76,100,224,200,196,104])
def mF2323 : MFace := ((339,0,172,0,4),0x10000001000000000000000000000000000001000,0x10000000000000000000000011000000000,[12,36,160,136,132,40])
def mF2370 : MFace := ((344,0,167,0,7),0x10000001000000000000000000000000200000048,0x600000000000000000000001400000020,[3,132,5,33,34,6,160,129,36,130])
def mF2375 : MFace := ((329,16,166,0,4),0x100000010000000000000000000000000000000400000,0x4000000000000000000000014000000000000,[22,50,176,52,146,148])
def mF2378 : MFace := ((345,0,166,0,4),0x10000001000000000000000000000000000000040,0x400000000000000000000001400000000,[6,34,160,36,130,132])
def mF2382 : MFace := ((282,64,165,0,4),0x100000010000000000000000000000002000000000000000000000000,0x2000000000000000000000010000000200000000000000000,[97,69,196,100,193,224])
def mF2386 : MFace := ((346,0,165,0,4),0x10000001000000000000000000000000200000000,0x200000000000000000000001000000020,[33,5,132,36,129,160])
def mF2394 : MFace := ((340,8,163,0,4),0x1000000000000000000000000000000020000000800,0x60000000000000000000000040000000000,[11,42,168,137,41,138])
def mF2396 : MFace := ((348,0,163,0,4),0x10000000000000000000000000000000200000008,0x600000000000000000000000400000000,[3,34,160,129,33,130])
def mF2401 : MFace := ((352,0,159,0,8),0x1000000000000000000000000001021048,0x4060000000000000000000000000000100020,[3,12,137,17,146,132,24,6,5,138,20])
def mF2417 : MFace := ((291,64,156,0,4),0x10000000000000000000000000010010000000000000000000,0x10100000000000000000000000000001000000000000000000000,[76,84,200,88,196,208])
def mF2419 : MFace := ((355,0,156,0,4),0x1000000000000000000000000001001000,0x1010000000000000000000000000000100000,[12,20,136,24,132,144])
def mF2427 : MFace := ((356,0,27,0,4),0x1020008,0x4060000000000000000000000000000000000,[3,137,24,146,17,138])
def mF2456 : MFace := ((360,0,151,0,5),0x1000000000000000000000000000020048,0x4000200000000000000000000000000100020,[3,146,132,17,5,6,20,129])
def mF2496 : MFace := ((368,0,143,0,5),0x1000000000000000000000000000001048,0x60000000000000000000000000000000020,[3,137,12,138,132,5,6])
def mF2532 : MFace := ((120,256,135,0,4),0x10000000000000000000000000000000480000000000000000000000000000000000000000000000000000000000000000,0x6000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000,[259,261,388,386,262,385])
def mF2541 : MFace := ((376,0,135,0,4),0x1000000000000000000000000000000048,0x600000000000000000000000000000020,[3,5,132,130,6,129])
def mF2545 : MFace := ((384,0,127,0,9),0x40000000201021048,0x100100000002200004040000000000,[3,12,116,17,66,24,33,42,73,6,50,69,104])
def mF2596 : MFace := ((390,0,57,0,4),0x201020000,0x10100000002000000000000000000,[17,73,112,24,33,104])
def mF2742 : MFace := ((404,0,99,0,4),0x40000000200000008,0x100000002000000040000000000,[3,42,73,33,66,104])
def mF2822 : MFace := ((404,8,99,0,4),0x4000000020000000800,0x100000002000000040000000000,[11,42,73,41,74,104])
def mF2823 : MFace := ((412,0,99,0,4),0x40000000200000008,0x1000000020000000400000000,[3,34,65,33,66,96])
def mF2828 : MFace := ((416,0,95,0,8),0x40000000001021048,0x1002200000000000040400,[3,12,69,17,66,73,84,24,6,10,18])
def mF2844 : MFace := ((418,0,29,0,4),0x1021000,0x1002200000000000000000,[12,69,17,73,84,24])
def mF2920 : MFace := ((432,0,79,0,5),0x40000000000001048,0x2200000000000000400,[3,69,12,73,66,10,6])
def mF2929 : MFace := ((401,32,78,0,4),0x4000000000000104000000000,0x110000000000000040000000000,[38,42,100,44,98,104])
def mF2930 : MFace := ((433,0,78,0,4),0x40000000000001040,0x1100000000000000400,[6,10,68,12,66,72])
def mF2971 : MFace := ((448,0,63,0,8),0x201021048,0x14040000000220,[3,12,42,17,52,6,24,33,5,50,9])
def mF2982 : MFace := ((449,0,30,0,4),0x1001040,0x14040000000000,[6,42,24,52,12,50])
def mF2990 : MFace := ((386,64,61,0,5),0x2010210000000000000000000,0x100100000002200000000000000000,[76,116,81,97,73,88,69,104])
def mF2992 : MFace := ((450,0,61,0,5),0x201021000,0x10010000000220,[12,52,17,33,9,24,5,40])
def mF3036 : MFace := ((390,64,57,0,4),0x2010200000000000000000000,0x10100000002000000000000000000,[81,73,112,88,97,104])
def mF3037 : MFace := ((454,0,57,0,4),0x201020000,0x1010000000200,[17,9,48,24,33,40])
def mF3046 : MFace := ((456,0,55,0,5),0x200020048,0x14000000000020,[3,50,6,17,52,33,5])
def mF3092 : MFace := ((464,0,47,0,5),0x200001048,0x41000000220,[3,42,12,33,5,6,9,36])
def mF3152 : MFace := ((472,0,39,0,4),0x200000048,0x1400000020,[3,5,34,6,33,36])
def mF3159 : MFace := ((480,0,31,0,7),0x1021048,0x140620,[3,12,5,17,10,6,24,18,9,20])
def mF3167 : MFace := ((449,32,30,0,4),0x100104000000000,0x14040000000000,[38,42,56,52,44,50])
def mF3169 : MFace := ((481,0,30,0,4),0x1001040,0x140400,[6,10,24,20,12,18])
def mF3174 : MFace := ((418,64,29,0,4),0x10210000000000000000000,0x1002200000000000000000,[76,69,81,73,84,88])
def mF3177 : MFace := ((482,0,29,0,4),0x1021000,0x100220,[12,5,17,9,20,24])
def mF3179 : MFace := ((356,128,27,0,4),0x102000800000000000000000000000000000000,0x4060000000000000000000000000000000000,[131,137,152,146,145,138])
def mF3185 : MFace := ((484,0,27,0,4),0x1020008,0x40600,[3,9,24,18,17,10])
def mF3186 : MFace := ((232,256,23,0,4),0x200480000000000000000000000000000000000000000000000000000000000000000,0x1400200000000000000000000000000000000000000000000000000000000000000000,[259,261,274,262,273,276])
def mF3195 : MFace := ((488,0,23,0,4),0x20048,0x140020,[3,5,18,6,17,20])
def mF3207 : MFace := ((496,0,15,0,4),0x1048,0x620,[3,5,12,10,6,9])
def mGood (c : MFace) : Prop := mValid c ∧ colCheck 511 c.1 (boundsBefore known383) = true
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF0 : mGood mF0 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2 : mGood mF2 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF6 : mGood mF6 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF12 : mGood mF12 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF14 : mGood mF14 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF16 : mGood mF16 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF18 : mGood mF18 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF21 : mGood mF21 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF26 : mGood mF26 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF28 : mGood mF28 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF30 : mGood mF30 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF32 : mGood mF32 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF34 : mGood mF34 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF35 : mGood mF35 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF41 : mGood mF41 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF45 : mGood mF45 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF50 : mGood mF50 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF53 : mGood mF53 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF56 : mGood mF56 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF58 : mGood mF58 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF60 : mGood mF60 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF62 : mGood mF62 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF64 : mGood mF64 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF65 : mGood mF65 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF66 : mGood mF66 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF72 : mGood mF72 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF74 : mGood mF74 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF75 : mGood mF75 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF80 : mGood mF80 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF83 : mGood mF83 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF85 : mGood mF85 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF88 : mGood mF88 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF89 : mGood mF89 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF93 : mGood mF93 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF94 : mGood mF94 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF95 : mGood mF95 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF96 : mGood mF96 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF98 : mGood mF98 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF101 : mGood mF101 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF103 : mGood mF103 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF106 : mGood mF106 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF110 : mGood mF110 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF112 : mGood mF112 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF116 : mGood mF116 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF120 : mGood mF120 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF144 : mGood mF144 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF159 : mGood mF159 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF163 : mGood mF163 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF219 : mGood mF219 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF223 : mGood mF223 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF224 : mGood mF224 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF310 : mGood mF310 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF430 : mGood mF430 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF438 : mGood mF438 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF523 : mGood mF523 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF529 : mGood mF529 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF572 : mGood mF572 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF573 : mGood mF573 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF638 : mGood mF638 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF644 : mGood mF644 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF805 : mGood mF805 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF915 : mGood mF915 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF919 : mGood mF919 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1005 : mGood mF1005 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1013 : mGood mF1013 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1022 : mGood mF1022 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1028 : mGood mF1028 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1057 : mGood mF1057 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1067 : mGood mF1067 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1097 : mGood mF1097 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1101 : mGood mF1101 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1105 : mGood mF1105 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1113 : mGood mF1113 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1115 : mGood mF1115 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1116 : mGood mF1116 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1121 : mGood mF1121 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1127 : mGood mF1127 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1151 : mGood mF1151 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1155 : mGood mF1155 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1193 : mGood mF1193 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1223 : mGood mF1223 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1230 : mGood mF1230 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1241 : mGood mF1241 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1250 : mGood mF1250 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1253 : mGood mF1253 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1261 : mGood mF1261 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1268 : mGood mF1268 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1289 : mGood mF1289 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1294 : mGood mF1294 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1297 : mGood mF1297 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1329 : mGood mF1329 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1335 : mGood mF1335 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1344 : mGood mF1344 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1350 : mGood mF1350 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1376 : mGood mF1376 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1378 : mGood mF1378 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1412 : mGood mF1412 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1464 : mGood mF1464 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1465 : mGood mF1465 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1602 : mGood mF1602 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1611 : mGood mF1611 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1649 : mGood mF1649 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1656 : mGood mF1656 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1787 : mGood mF1787 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1870 : mGood mF1870 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1899 : mGood mF1899 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF1992 : mGood mF1992 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2164 : mGood mF2164 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2166 : mGood mF2166 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2195 : mGood mF2195 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2225 : mGood mF2225 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2243 : mGood mF2243 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2273 : mGood mF2273 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2288 : mGood mF2288 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2296 : mGood mF2296 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2305 : mGood mF2305 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2321 : mGood mF2321 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2323 : mGood mF2323 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2370 : mGood mF2370 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2375 : mGood mF2375 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2378 : mGood mF2378 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2382 : mGood mF2382 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2386 : mGood mF2386 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2394 : mGood mF2394 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2396 : mGood mF2396 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2401 : mGood mF2401 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2417 : mGood mF2417 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2419 : mGood mF2419 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2427 : mGood mF2427 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2456 : mGood mF2456 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2496 : mGood mF2496 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2532 : mGood mF2532 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2541 : mGood mF2541 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2545 : mGood mF2545 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2596 : mGood mF2596 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2742 : mGood mF2742 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2822 : mGood mF2822 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2823 : mGood mF2823 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2828 : mGood mF2828 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2844 : mGood mF2844 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2920 : mGood mF2920 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2929 : mGood mF2929 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2930 : mGood mF2930 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2971 : mGood mF2971 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2982 : mGood mF2982 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2990 : mGood mF2990 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF2992 : mGood mF2992 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3036 : mGood mF3036 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3037 : mGood mF3037 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3046 : mGood mF3046 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3092 : mGood mF3092 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3152 : mGood mF3152 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3159 : mGood mF3159 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3167 : mGood mF3167 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3169 : mGood mF3169 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3174 : mGood mF3174 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3177 : mGood mF3177 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3179 : mGood mF3179 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3185 : mGood mF3185 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3186 : mGood mF3186 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3195 : mGood mF3195 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mOkmF3207 : mGood mF3207 := by
  unfold mGood mValid mGeometry
  constructor <;> decide +kernel
def mGet (i : Nat) : Option {c : MFace // mGood c} := if i<187 then (if i<103 then (if i<59 then (if i<29 then (if i<16 then (if i<6 then (if i<2 then (if i==0 then some ⟨mF0,mOkmF0⟩ else none) else (if i==2 then some ⟨mF2,mOkmF2⟩ else none)) else (if i<12 then (if i==6 then some ⟨mF6,mOkmF6⟩ else none) else (if i<14 then (if i==12 then some ⟨mF12,mOkmF12⟩ else none) else (if i==14 then some ⟨mF14,mOkmF14⟩ else none)))) else (if i<21 then (if i<18 then (if i==16 then some ⟨mF16,mOkmF16⟩ else none) else (if i==18 then some ⟨mF18,mOkmF18⟩ else none)) else (if i<26 then (if i==21 then some ⟨mF21,mOkmF21⟩ else none) else (if i<28 then (if i==26 then some ⟨mF26,mOkmF26⟩ else none) else (if i==28 then some ⟨mF28,mOkmF28⟩ else none))))) else (if i<44 then (if i<33 then (if i<31 then (if i==29 then some ⟨mF30,mOkmF30⟩ else none) else (if i==31 then some ⟨mF32,mOkmF32⟩ else none)) else (if i<34 then (if i==33 then some ⟨mF34,mOkmF34⟩ else none) else (if i<40 then (if i==34 then some ⟨mF35,mOkmF35⟩ else none) else (if i==40 then some ⟨mF41,mOkmF41⟩ else none)))) else (if i<52 then (if i<49 then (if i==44 then some ⟨mF45,mOkmF45⟩ else none) else (if i==49 then some ⟨mF50,mOkmF50⟩ else none)) else (if i<55 then (if i==52 then some ⟨mF53,mOkmF53⟩ else none) else (if i<57 then (if i==55 then some ⟨mF56,mOkmF56⟩ else none) else (if i==57 then some ⟨mF58,mOkmF58⟩ else none)))))) else (if i<83 then (if i<71 then (if i<63 then (if i<61 then (if i==59 then some ⟨mF60,mOkmF60⟩ else none) else (if i==61 then some ⟨mF62,mOkmF62⟩ else none)) else (if i<64 then (if i==63 then some ⟨mF64,mOkmF64⟩ else none) else (if i<65 then (if i==64 then some ⟨mF65,mOkmF65⟩ else none) else (if i==65 then some ⟨mF66,mOkmF66⟩ else none)))) else (if i<74 then (if i<73 then (if i==71 then some ⟨mF72,mOkmF72⟩ else none) else (if i==73 then some ⟨mF74,mOkmF74⟩ else none)) else (if i<78 then (if i==74 then some ⟨mF75,mOkmF75⟩ else none) else (if i<81 then (if i==78 then some ⟨mF80,mOkmF80⟩ else none) else (if i==81 then some ⟨mF83,mOkmF83⟩ else none))))) else (if i<92 then (if i<87 then (if i<86 then (if i==83 then some ⟨mF85,mOkmF85⟩ else none) else (if i==86 then some ⟨mF88,mOkmF88⟩ else none)) else (if i<90 then (if i==87 then some ⟨mF89,mOkmF89⟩ else none) else (if i<91 then (if i==90 then some ⟨mF93,mOkmF93⟩ else none) else (if i==91 then some ⟨mF94,mOkmF94⟩ else none)))) else (if i<95 then (if i<93 then (if i==92 then some ⟨mF95,mOkmF95⟩ else none) else (if i==93 then some ⟨mF96,mOkmF96⟩ else none)) else (if i<98 then (if i==95 then some ⟨mF98,mOkmF98⟩ else none) else (if i<100 then (if i==98 then some ⟨mF101,mOkmF101⟩ else none) else (if i==100 then some ⟨mF103,mOkmF103⟩ else none))))))) else (if i<153 then (if i<130 then (if i<122 then (if i<109 then (if i<107 then (if i==103 then some ⟨mF106,mOkmF106⟩ else none) else (if i==107 then some ⟨mF110,mOkmF110⟩ else none)) else (if i<112 then (if i==109 then some ⟨mF112,mOkmF112⟩ else none) else (if i<116 then (if i==112 then some ⟨mF116,mOkmF116⟩ else none) else (if i==116 then some ⟨mF120,mOkmF120⟩ else none)))) else (if i<124 then (if i<123 then (if i==122 then some ⟨mF144,mOkmF144⟩ else none) else (if i==123 then some ⟨mF159,mOkmF159⟩ else none)) else (if i<128 then (if i==124 then some ⟨mF163,mOkmF163⟩ else none) else (if i<129 then (if i==128 then some ⟨mF219,mOkmF219⟩ else none) else (if i==129 then some ⟨mF223,mOkmF223⟩ else none))))) else (if i<140 then (if i<134 then (if i<131 then (if i==130 then some ⟨mF224,mOkmF224⟩ else none) else (if i==131 then some ⟨mF310,mOkmF310⟩ else none)) else (if i<135 then (if i==134 then some ⟨mF430,mOkmF430⟩ else none) else (if i<139 then (if i==135 then some ⟨mF438,mOkmF438⟩ else none) else (if i==139 then some ⟨mF523,mOkmF523⟩ else none)))) else (if i<144 then (if i<143 then (if i==140 then some ⟨mF529,mOkmF529⟩ else none) else (if i==143 then some ⟨mF572,mOkmF572⟩ else none)) else (if i<149 then (if i==144 then some ⟨mF573,mOkmF573⟩ else none) else (if i<150 then (if i==149 then some ⟨mF638,mOkmF638⟩ else none) else (if i==150 then some ⟨mF644,mOkmF644⟩ else none)))))) else (if i<173 then (if i<163 then (if i<155 then (if i<154 then (if i==153 then some ⟨mF805,mOkmF805⟩ else none) else (if i==154 then some ⟨mF915,mOkmF915⟩ else none)) else (if i<160 then (if i==155 then some ⟨mF919,mOkmF919⟩ else none) else (if i<161 then (if i==160 then some ⟨mF1005,mOkmF1005⟩ else none) else (if i==161 then some ⟨mF1013,mOkmF1013⟩ else none)))) else (if i<169 then (if i<164 then (if i==163 then some ⟨mF1022,mOkmF1022⟩ else none) else (if i==164 then some ⟨mF1028,mOkmF1028⟩ else none)) else (if i<170 then (if i==169 then some ⟨mF1057,mOkmF1057⟩ else none) else (if i<172 then (if i==170 then some ⟨mF1067,mOkmF1067⟩ else none) else (if i==172 then some ⟨mF1097,mOkmF1097⟩ else none))))) else (if i<179 then (if i<175 then (if i<174 then (if i==173 then some ⟨mF1101,mOkmF1101⟩ else none) else (if i==174 then some ⟨mF1105,mOkmF1105⟩ else none)) else (if i<176 then (if i==175 then some ⟨mF1113,mOkmF1113⟩ else none) else (if i<177 then (if i==176 then some ⟨mF1115,mOkmF1115⟩ else none) else (if i==177 then some ⟨mF1116,mOkmF1116⟩ else none)))) else (if i<183 then (if i<180 then (if i==179 then some ⟨mF1121,mOkmF1121⟩ else none) else (if i<182 then (if i==180 then some ⟨mF1127,mOkmF1127⟩ else none) else (if i==182 then some ⟨mF1151,mOkmF1151⟩ else none))) else (if i<185 then (if i==183 then some ⟨mF1155,mOkmF1155⟩ else none) else (if i<186 then (if i==185 then some ⟨mF1193,mOkmF1193⟩ else none) else (if i==186 then some ⟨mF1223,mOkmF1223⟩ else none)))))))) else (if i<244 then (if i<214 then (if i<198 then (if i<192 then (if i<189 then (if i<188 then (if i==187 then some ⟨mF1230,mOkmF1230⟩ else none) else (if i==188 then some ⟨mF1241,mOkmF1241⟩ else none)) else (if i<190 then (if i==189 then some ⟨mF1250,mOkmF1250⟩ else none) else (if i<191 then (if i==190 then some ⟨mF1253,mOkmF1253⟩ else none) else (if i==191 then some ⟨mF1261,mOkmF1261⟩ else none)))) else (if i<195 then (if i<194 then (if i==192 then some ⟨mF1268,mOkmF1268⟩ else none) else (if i==194 then some ⟨mF1289,mOkmF1289⟩ else none)) else (if i<196 then (if i==195 then some ⟨mF1294,mOkmF1294⟩ else none) else (if i<197 then (if i==196 then some ⟨mF1297,mOkmF1297⟩ else none) else (if i==197 then some ⟨mF1329,mOkmF1329⟩ else none))))) else (if i<207 then (if i<202 then (if i<200 then (if i==198 then some ⟨mF1335,mOkmF1335⟩ else none) else (if i==200 then some ⟨mF1344,mOkmF1344⟩ else none)) else (if i<205 then (if i==202 then some ⟨mF1350,mOkmF1350⟩ else none) else (if i<206 then (if i==205 then some ⟨mF1376,mOkmF1376⟩ else none) else (if i==206 then some ⟨mF1378,mOkmF1378⟩ else none)))) else (if i<210 then (if i<209 then (if i==207 then some ⟨mF1412,mOkmF1412⟩ else none) else (if i==209 then some ⟨mF1464,mOkmF1464⟩ else none)) else (if i<211 then (if i==210 then some ⟨mF1465,mOkmF1465⟩ else none) else (if i<213 then (if i==211 then some ⟨mF1602,mOkmF1602⟩ else none) else (if i==213 then some ⟨mF1611,mOkmF1611⟩ else none)))))) else (if i<229 then (if i<219 then (if i<216 then (if i<215 then (if i==214 then some ⟨mF1649,mOkmF1649⟩ else none) else (if i==215 then some ⟨mF1656,mOkmF1656⟩ else none)) else (if i<217 then (if i==216 then some ⟨mF1787,mOkmF1787⟩ else none) else (if i<218 then (if i==217 then some ⟨mF1870,mOkmF1870⟩ else none) else (if i==218 then some ⟨mF1899,mOkmF1899⟩ else none)))) else (if i<223 then (if i<222 then (if i==219 then some ⟨mF1992,mOkmF1992⟩ else none) else (if i==222 then some ⟨mF2164,mOkmF2164⟩ else none)) else (if i<224 then (if i==223 then some ⟨mF2166,mOkmF2166⟩ else none) else (if i<226 then (if i==224 then some ⟨mF2195,mOkmF2195⟩ else none) else (if i==226 then some ⟨mF2225,mOkmF2225⟩ else none))))) else (if i<238 then (if i<233 then (if i<232 then (if i==229 then some ⟨mF2243,mOkmF2243⟩ else none) else (if i==232 then some ⟨mF2273,mOkmF2273⟩ else none)) else (if i<235 then (if i==233 then some ⟨mF2288,mOkmF2288⟩ else none) else (if i<236 then (if i==235 then some ⟨mF2296,mOkmF2296⟩ else none) else (if i==236 then some ⟨mF2305,mOkmF2305⟩ else none)))) else (if i<241 then (if i<239 then (if i==238 then some ⟨mF2321,mOkmF2321⟩ else none) else (if i==239 then some ⟨mF2323,mOkmF2323⟩ else none)) else (if i<242 then (if i==241 then some ⟨mF2370,mOkmF2370⟩ else none) else (if i<243 then (if i==242 then some ⟨mF2375,mOkmF2375⟩ else none) else (if i==243 then some ⟨mF2378,mOkmF2378⟩ else none))))))) else (if i<268 then (if i<256 then (if i<250 then (if i<246 then (if i<245 then (if i==244 then some ⟨mF2382,mOkmF2382⟩ else none) else (if i==245 then some ⟨mF2386,mOkmF2386⟩ else none)) else (if i<247 then (if i==246 then some ⟨mF2394,mOkmF2394⟩ else none) else (if i<248 then (if i==247 then some ⟨mF2396,mOkmF2396⟩ else none) else (if i==248 then some ⟨mF2401,mOkmF2401⟩ else none)))) else (if i<252 then (if i<251 then (if i==250 then some ⟨mF2417,mOkmF2417⟩ else none) else (if i==251 then some ⟨mF2419,mOkmF2419⟩ else none)) else (if i<254 then (if i==252 then some ⟨mF2427,mOkmF2427⟩ else none) else (if i<255 then (if i==254 then some ⟨mF2456,mOkmF2456⟩ else none) else (if i==255 then some ⟨mF2496,mOkmF2496⟩ else none))))) else (if i<261 then (if i<258 then (if i<257 then (if i==256 then some ⟨mF2532,mOkmF2532⟩ else none) else (if i==257 then some ⟨mF2541,mOkmF2541⟩ else none)) else (if i<259 then (if i==258 then some ⟨mF2545,mOkmF2545⟩ else none) else (if i<260 then (if i==259 then some ⟨mF2596,mOkmF2596⟩ else none) else (if i==260 then some ⟨mF2742,mOkmF2742⟩ else none)))) else (if i<264 then (if i<262 then (if i==261 then some ⟨mF2822,mOkmF2822⟩ else none) else (if i==262 then some ⟨mF2823,mOkmF2823⟩ else none)) else (if i<266 then (if i==264 then some ⟨mF2828,mOkmF2828⟩ else none) else (if i<267 then (if i==266 then some ⟨mF2844,mOkmF2844⟩ else none) else (if i==267 then some ⟨mF2920,mOkmF2920⟩ else none)))))) else (if i<279 then (if i<273 then (if i<270 then (if i<269 then (if i==268 then some ⟨mF2929,mOkmF2929⟩ else none) else (if i==269 then some ⟨mF2930,mOkmF2930⟩ else none)) else (if i<271 then (if i==270 then some ⟨mF2971,mOkmF2971⟩ else none) else (if i<272 then (if i==271 then some ⟨mF2982,mOkmF2982⟩ else none) else (if i==272 then some ⟨mF2990,mOkmF2990⟩ else none)))) else (if i<275 then (if i<274 then (if i==273 then some ⟨mF2992,mOkmF2992⟩ else none) else (if i==274 then some ⟨mF3036,mOkmF3036⟩ else none)) else (if i<277 then (if i==275 then some ⟨mF3037,mOkmF3037⟩ else none) else (if i<278 then (if i==277 then some ⟨mF3046,mOkmF3046⟩ else none) else (if i==278 then some ⟨mF3092,mOkmF3092⟩ else none))))) else (if i<285 then (if i<282 then (if i<281 then (if i==279 then some ⟨mF3152,mOkmF3152⟩ else none) else (if i==281 then some ⟨mF3159,mOkmF3159⟩ else none)) else (if i<283 then (if i==282 then some ⟨mF3167,mOkmF3167⟩ else none) else (if i<284 then (if i==283 then some ⟨mF3169,mOkmF3169⟩ else none) else (if i==284 then some ⟨mF3174,mOkmF3174⟩ else none)))) else (if i<288 then (if i<286 then (if i==285 then some ⟨mF3177,mOkmF3177⟩ else none) else (if i<287 then (if i==286 then some ⟨mF3179,mOkmF3179⟩ else none) else (if i==287 then some ⟨mF3185,mOkmF3185⟩ else none))) else (if i<289 then (if i==288 then some ⟨mF3186,mOkmF3186⟩ else none) else (if i<290 then (if i==289 then some ⟨mF3195,mOkmF3195⟩ else none) else (if i==290 then some ⟨mF3207,mOkmF3207⟩ else none))))))))
def jForest : Forest := ⟨511,14,fun j => samples[j]?.getD (0,0),jCols,deadautos,fun _ => emptyPacking,jIndex⟩
def jRead (k i : Nat) : Nat × List Decor × List Decor :=
  let (ops,mask) := jRecipe k i
  let bank := decodeBank (jDep k) ops (wiresOf jForest)
  (ops,bank,selectLive mask bank)
def jSet (k i : Nat) := (jRead k i).2.2.map Prod.fst
def jLinked (k : Nat) (p : Nat × Nat) : Option (List Sig) :=
  if p.1 ≥ jCount k then none else
    (deadautos[p.2]?).map fun perm => (jSet k p.1).map (movedWord (perm.map swapRows).reverse)
def jRules (k i ops : Nat) (bank : List Decor) :=
  (jHints k i).filterMap (fun (a,b) => if b==128 then none else buildRule jForest ops (jDep k) bank a b)
def jCtx (k i : Nat) : NodeContextT :=
  let (ops,bank,ws) := jRead k i
  let pools := jRules k i ops bank
  let faces := (jHints k i).filterMap (fun (a,b) => if b==128 then mGet a else none)
  let lk := fun tag child => if faces.any (fun c => mCut c.val (k-1) child) then [child] else
    ((jIndex k tag).bind (jLinked (k-1))).toList
  (k,0,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),lk,fun _ _ => [],fun _ _ => [])
def jNode (k i : Nat) :=
  let c := jCtx k i
  let ws := c.2.2.2.1
  let vals := ws.map Prod.fst
  decide vals.Nodup && !(vals.contains graph) && testAllT c ws
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem jGeom : graphValid jForest (boundsBefore known383) = true := by decide +kernel
theorem jTarget : targetOf jForest = graph := by decide +kernel
set_option maxRecDepth 16384 in
theorem jLinkOK {k p xs}
    (h : ∀ i < jCount k, ImpossibleT graph k 0 (jSet k i).toFinset)
    (hit : jLinked k p = some xs) : ImpossibleT graph k 0 xs.toFinset := by
  have geom := jGeom
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geom
  unfold jLinked at hit
  split at hit
  · simp at hit
  next hr =>
    obtain ⟨perm,hp,he⟩ := Option.map_eq_some_iff.mp hit
    subst xs
    apply rotate_excludedT (h _ (by omega))
    rw [←jTarget]
    exact geom.2 perm (by change perm ∈ deadautos.toList; simpa using Array.mem_of_getElem? hp)

set_option maxRecDepth 16384 in
theorem jStep (k i : Nat) (h : ∀ i < jCount (k-1), ImpossibleT graph (k-1) 0 (jSet (k-1) i).toFinset)
    (ok : jNode k i = true) : ImpossibleT graph k 0 (jSet k i).toFinset := by
  have geom := jGeom
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geom
  have pairs := chart_pairs geom.1.1.1 geom.1.1.2
  change properPairs (targetOf jForest) _ _ at pairs
  rw [jTarget] at pairs
  simp only [jNode,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at ok
  apply nodeT_sound (raw:=vars jForest.mask) pairs _ ok.1.1 ok.1.2 _ _ _ _ (by decide) ok.2
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful jForest) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,hc⟩ := List.mem_filterMap.mp hp
    change (if b==128 then none else buildRule jForest _ _ _ a b) = some p at hc
    split at hc
    · contradiction
    rw [←jTarget]
    apply buildRule_sound jForest _ hc
    intro c hc
    exact col_sound c _ (before_sound known383 valid383) (geom.1.2 c hc)
  · intro tag child nd xs hx
    change xs ∈ (if _ then [child] else ((jIndex k tag).bind (jLinked (k-1))).toList) at hx
    split at hx
    next yes =>
      obtain ⟨c,_,cut⟩ := List.any_eq_true.mp yes
      have hx' : xs=child := List.mem_singleton.mp hx
      subst xs
      apply mDirectedCut c.property.1 _ nd cut
      have hh := col_sound (m:=511) c.val.1 _ (before_sound known383 valid383) c.property.2
      exact hh
    next =>
      have e : ((jIndex k tag).bind (jLinked (k-1))) = some xs := by simpa using hx
      obtain ⟨p,_,hh⟩ := Option.bind_eq_some_iff.mp e
      exact jLinkOK h hh
  · simp
  · simp

def jBlock (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => jNode k (start+n) && jBlock k start n
theorem jBlockAt {k s n i} (h : jBlock k s n = true) (lo : s ≤ i) (hi : i < s+n) : jNode k i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [jBlock,Bool.and_eq_true] at h
    by_cases he : i=s+n
    · simpa only [he] using h.1
    · exact ih h.2 (by omega)
theorem jMerge {k s a b} (h : jBlock k s a=true) (g : jBlock k (s+a) b=true) :
    jBlock k s (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [jBlock,Bool.and_eq_true] at g
    simp only [Nat.add_succ,jBlock,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using g.1,ih g.2⟩
theorem jAll (rows : ∀ k ≤ 14, jBlock k 0 (jCount k)=true) :
    ∀ k ≤ 14, ∀ i < jCount k, ImpossibleT graph k 0 (jSet k i).toFinset := by
  intro k
  induction k with
  | zero => intro _ i hi; change i < 0 at hi; omega
  | succ k ih =>
    intro le i hi
    apply jStep _ _ (by simpa using ih (by omega))
    exact jBlockAt (rows _ le) (by omega) (by omega)
def jCells (k s n : Nat) : Nat → Prop
  | 0 => jBlock k s n = true
  | d+1 => jCells k s (n/2) d ∧ jCells k (s+n/2) (n-n/2) d
theorem jCellsOK {k s n d} (ok : jCells k s n d) : jBlock k s n = true := by
  induction d generalizing s n with
  | zero => exact ok
  | succ d ih =>
    have h := jMerge (ih ok.1) (ih ok.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using h
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z5t0 : jBlock 5 0 1=true := by
  apply jCellsOK (d:=0)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem jK5 : jBlock 5 0 1=true := z5t0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z6t0 : jBlock 6 0 3=true := by
  apply jCellsOK (d:=0)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem jK6 : jBlock 6 0 3=true := z6t0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z7t0 : jBlock 7 0 8=true := by
  apply jCellsOK (d:=0)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem jK7 : jBlock 7 0 8=true := z7t0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z8t0 : jBlock 8 0 22=true := by
  apply jCellsOK (d:=1)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem jK8 : jBlock 8 0 22=true := z8t0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z9t0 : jBlock 9 0 109=true := by
  apply jCellsOK (d:=4)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem jK9 : jBlock 9 0 109=true := z9t0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z10t0 : jBlock 10 0 80=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z10t80 : jBlock 10 80 81=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z10t161 : jBlock 10 161 81=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z10t242 : jBlock 10 242 81=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z10t323 : jBlock 10 323 81=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z10t404 : jBlock 10 404 81=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z10t485 : jBlock 10 485 81=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z10t566 : jBlock 10 566 81=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem jK10 : jBlock 10 0 647=true := (@jMerge 10 0 323 324 (@jMerge 10 0 161 162 (@jMerge 10 0 80 81 z10t0 z10t80) (@jMerge 10 161 81 81 z10t161 z10t242)) (@jMerge 10 323 162 162 (@jMerge 10 323 81 81 z10t323 z10t404) (@jMerge 10 485 81 81 z10t485 z10t566)))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t0 : jBlock 11 0 91=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t91 : jBlock 11 91 91=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t182 : jBlock 11 182 91=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t273 : jBlock 11 273 92=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t365 : jBlock 11 365 91=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t456 : jBlock 11 456 91=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t547 : jBlock 11 547 91=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t638 : jBlock 11 638 92=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t730 : jBlock 11 730 91=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t821 : jBlock 11 821 91=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t912 : jBlock 11 912 91=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t1003 : jBlock 11 1003 92=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t1095 : jBlock 11 1095 91=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t1186 : jBlock 11 1186 92=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t1278 : jBlock 11 1278 91=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z11t1369 : jBlock 11 1369 92=true := by
  apply jCellsOK (d:=3)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem jK11 : jBlock 11 0 1461=true := (@jMerge 11 0 730 731 (@jMerge 11 0 365 365 (@jMerge 11 0 182 183 (@jMerge 11 0 91 91 z11t0 z11t91) (@jMerge 11 182 91 92 z11t182 z11t273)) (@jMerge 11 365 182 183 (@jMerge 11 365 91 91 z11t365 z11t456) (@jMerge 11 547 91 92 z11t547 z11t638))) (@jMerge 11 730 365 366 (@jMerge 11 730 182 183 (@jMerge 11 730 91 91 z11t730 z11t821) (@jMerge 11 912 91 92 z11t912 z11t1003)) (@jMerge 11 1095 183 183 (@jMerge 11 1095 91 92 z11t1095 z11t1186) (@jMerge 11 1278 91 92 z11t1278 z11t1369))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z12t0 : jBlock 12 0 148=true := by
  apply jCellsOK (d:=4)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z12t148 : jBlock 12 148 148=true := by
  apply jCellsOK (d:=4)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z12t296 : jBlock 12 296 148=true := by
  apply jCellsOK (d:=4)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z12t444 : jBlock 12 444 149=true := by
  apply jCellsOK (d:=4)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem jK12 : jBlock 12 0 593=true := (@jMerge 12 0 296 297 (@jMerge 12 0 148 148 z12t0 z12t148) (@jMerge 12 296 148 149 z12t296 z12t444))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z13t0 : jBlock 13 0 34=true := by
  apply jCellsOK (d:=2)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem jK13 : jBlock 13 0 34=true := z13t0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z14t0 : jBlock 14 0 2=true := by
  apply jCellsOK (d:=0)
  simp only [jCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem jK14 : jBlock 14 0 2=true := z14t0
theorem jRows (k : Nat) (hk : k≤14) : jBlock k 0 (jCount k)=true := by
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact jK5
  · exact jK6
  · exact jK7
  · exact jK8
  · exact jK9
  · exact jK10
  · exact jK11
  · exact jK12
  · exact jK13
  · exact jK14
theorem jBare : ImpossibleT graph 14 0 inputs.toFinset := by
  have h := jAll jRows 14 (by decide) 1 (by decide +kernel)
  have eq : jSet 14 1 = inputs := by decide +kernel
  rwa [eq] at h
theorem jHelper : ImpossibleT graph 14 0 roots.toFinset := by
  have h := jAll jRows 14 (by decide) 0 (by decide +kernel)
  have eq : jSet 14 0 = roots := by decide +kernel
  rwa [eq] at h

end PEqualNP.Outside.L_meta_3188_aux
open PEqualNP.Outside.L_meta_3188_aux in
theorem PEqualNP.Outside.L_meta_3188 :
have x1 : Fin (9 : ℕ) → BitVec (24 : ℕ) := fun (x1 : Fin (9 : ℕ)) =>   have x2 : ℕ × ℕ := [((49 : ℕ), (1348 : ℕ)), ((67 : ℕ), (2083 : ℕ)), ((134 : ℕ), (788 : ℕ)), ((268 : ℕ), (105 : ℕ)), ((24 : ℕ), (2706 : ℕ)), ((2592 : ℕ), (27 : ℕ)), ((1088 : ℕ), (220 : ℕ)), ((640 : ℕ), (3296 : ℕ)), ((3328 : ℕ), (3840 : ℕ))].getD ↑x1 ((0 : ℕ), (0 : ℕ));   BitVec.ofNat (24 : ℕ) ((4096 : ℕ) * x2.1 + x2.2); have x2 : List (BitVec (24 : ℕ)) := List.ofFn x1 ++ [x1 (0 : Fin (9 : ℕ)) ||| x1 (2 : Fin (9 : ℕ))]; ∀ (x3 : List (BitVec (24 : ℕ))),   BitVec.ofNat (24 : ℕ) ((4095 : ℕ) * (4096 : ℕ)) ∈ x2 ++ x3 →     (∀ (x5 : Fin x3.length),         have x6 : List (BitVec (24 : ℕ)) := x2 ++ List.take (↑x5) x3;         x3.get x5 ∉ x6 ∧ x3.get x5 ≠ (0 : BitVec (24 : ℕ)) ∧ x3.get x5 ≠ (-1 : BitVec (24 : ℕ)) ∧ ∃ x7 ∈ x6, ∃ x8 ∈ x6, x3.get x5 = x7 &&& x8 ∨ x3.get x5 = x7 ||| x8) →       (15 : ℕ) ≤ x3.length := by
  change ∀ vs : List W, goal ∈ base ++ vs → legal base vs → 15 ≤ vs.length
  intro vs ht hl
  obtain ⟨k,hk,h|h⟩ := extractLive ht hl
  · by_contra! hlt; exact jBare k 0 (by omega) (by decide) h
  · by_contra! hlt; exact jHelper k 0 (by omega) (by decide) h
