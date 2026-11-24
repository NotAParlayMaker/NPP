import PEqualNP.Defs

-- The finite certificate for the OR of inputs zero and four is by JLDC in PR 6373.
-- The live-set calculus and induced-graph certificates are from PressF10, L-meta-1667.
namespace PEqualNP.Outside.L_meta_3138
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

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

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
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
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
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
def orSeed : Sig := inputs.getD 0 zero ||| inputs.getD 3 zero
theorem seed_table : ∀ r : Row, bit r orSeed = (sample r 0 || sample r 3) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : orSeed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def neighbor (i : Fin 9) : Nat := [4,2,1,2,0,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (([10,1,2,5,1,1,2,4,8] : List Nat).getD i.val 0)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (absentRow i).val)

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[orSeed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[orSeed]) :
    S=inputs.toFinset ∨ S=(inputs++[orSeed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : orSeed ∈ S
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

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[orSeed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = orSeed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = orSeed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = orSeed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


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

end PEqualNP.Outside.L_meta_3138
namespace PEqualNP.Outside.L_meta_3138_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]
theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp
theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)
def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false
def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)
def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)
def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc
theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp
def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g
theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk
theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false
theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩
theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm
theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h
end CircuitProof
namespace PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitProof
def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b ∧ a ≠ cut ∧ b ≠ cut
theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut) {out : W} (different : x out ≠ y out) :
    ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a out := by
  classical
  have track : ∀ k b, rank b = k → x b ≠ y b →
      ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b, hInput, diff, Relation.ReflTransGen.refl⟩
      · obtain ⟨p, hp, dp⟩ := localStep b hInput diff
        have earlier : rank p < k := (order p b hp).trans_eq hb
        obtain ⟨a, ha, da, path⟩ := ih (rank p) earlier p rfl dp
        have pOff : p ≠ cut := by rintro rfl; exact dp sameCut
        have bOff : b ≠ cut := by rintro rfl; exact diff sameCut
        exact ⟨a, ha, da, path.tail ⟨hp, pOff, bOff⟩⟩
  exact track (rank out) out rfl different
theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a, input a → x a ≠ y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out := by
  by_contra different
  obtain ⟨a, ha, da, reaches⟩ := difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches
theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y, w x = w y → f x = f y) :
    ∃ outer : Bool → Bool, ∀ x, outer (w x) = f x := by
  classical
  let outer (b : Bool) := if hb : ∃ a, w a = b then f (Classical.choose hb) else false
  refine ⟨outer, fun x => ?_⟩
  have hx : ∃ a, w a = w x := ⟨x, rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)
def inputWire {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)
def readEdge {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ b.val = n + p ∧ a.val ∈ g.inputs
theorem read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val := by
  obtain ⟨p, g, hpg, hb, ha⟩ := edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha
private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val ≠ vl gs y b.val) :
    ∃ a : Fin (n + gs.length), readEdge gs a b ∧ vl gs x a.val ≠ vl gs y a.val := by
  let p := b.val - n
  have hb : b.val = n + p := by dsimp [p]; omega
  have hp : p < gs.length := by have := b.isLt; omega
  let g := gs[p]
  have hpg : gs[p]? = some g := List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs, vl gs x a ≠ vl gs y a := by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a, ha, da⟩)
  obtain ⟨a, ha, da⟩ := differingRead
  have ha' := (hcl p g hpg).lt a ha
  refine ⟨⟨a, by have := b.isLt; omega⟩, ⟨p, g, hpg, hb, ha⟩, da⟩
theorem circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n, x i ≠ y i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    vl gs x out.val = vl gs y out.val := by
  apply cut_agreement Fin.val (fun v => v.val < n) (readEdge gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => read_order hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n := ⟨a.val, ha⟩
    have sameWire : inputWire gs i = a := Fin.ext rfl
    have di : x i ≠ y i := by
      rw [vl_input gs x a.val ha, vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di
theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  let Fiber := {x : Fin n → Bool // ∀ i, ¬ group i → x i = base i}
  obtain ⟨outer, ho⟩ := unary_factor
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply circuit_cut_agreement hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer, fun x agrees => ho ⟨x, agrees⟩⟩
end PetersenCutTrace
namespace CircuitProof.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof
def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs
end CircuitProof.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
namespace PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitProof CircuitProof.Readers
def predecessors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; omega
    let g := gs[slot]'hs
    g.inputs.attach.map fun a => ⟨a.val, by
      have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
      have before := (clean slot g atSlot).lt a.val a.property
      omega⟩
  else []
theorem predecessors_values {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (predecessors clean b).map Fin.val =
      (gs[b.val - n]'(by have := b.isLt; omega)).inputs := by
  simp [predecessors, internal, List.map_map, Function.comp_def]
theorem predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : predecessors clean b = [] := by
  simp [predecessors, show ¬ n ≤ b.val by omega]
theorem predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (predecessors clean b).map Fin.val = g.inputs := by
  have isGate : n ≤ b.val := by omega
  have which : b.val - n = p := by omega
  have located := (List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which, located] using predecessors_values clean b isGate
theorem predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ predecessors clean b ↔ readEdge gs a b := by
  by_cases internal : n ≤ b.val
  · let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; dsimp [slot]; omega
    let g := gs[slot]'hs
    have wire : b.val = n + slot := by dsimp [slot]; omega
    have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
    have valList : (predecessors clean b).map Fin.val = g.inputs :=
      predecessors_values clean b internal
    constructor
    · intro mem
      refine ⟨slot, g, atSlot, wire, ?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a, mem, rfl⟩
    · rintro ⟨q, h, atQ, wireQ, inside⟩
      have same : q = slot := by omega
      subst q
      have gateSame : h = g := Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a', mem, equal⟩ := List.mem_map.mp inside
      exact (Fin.ext equal : a' = a) ▸ mem
  · have empty : predecessors clean b = [] := by simp [predecessors, internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot, g, _, wire, _⟩
      omega
end PetersenCutTrace
namespace PetersenScratch
open PEqualNP.MetaComplexity
def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => occurrences i p + occurrences i q
  | .or p q => occurrences i p + occurrences i q
def hasPair {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < occurrences i p ∨ 0 < occurrences j p
def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k
def pairValue {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n) :
    Bool → Bool → Bool :=
  fun a b => p.eval (pairInput i j base a b)
def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a && b else a || b
noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool → Bool → Bool) : Bool → Bool → Bool := by
  classical
  exact if hasPair i j p then
    if hasPair i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q
noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Bool → Bool
  | .lit k sign => fun a b =>
    let bit := if k = i then a else if k = j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)
private theorem eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k, 0 < occurrences k p → x k = y k) : p.eval x = p.eval y := by
  induction p with
  | lit k s =>
    have e := h k (by simp [occurrences])
    simp [DMFormula.eval, e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
private theorem absent_left {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences i p = 0) (a a' b : Bool) :
    pairValue i j base p a b = pairValue i j base p a' b := by
  apply eval_agree
  intro k hk
  have ne : k ≠ i := by rintro rfl; omega
  simp [pairInput, ne]
private theorem absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b' := by
  apply eval_agree
  intro k hk
  have ne : k ≠ j := by rintro rfl; omega
  simp [pairInput, ne]
def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b, f false b ≠ f true b
private theorem changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hQ : ∀ b, Q false b = Q true b) : changes P := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp, hQ])⟩
private theorem changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hP : ∀ b, P false b = P true b) : changes Q := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq, hP])⟩
private theorem constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false := by
  have hi : occurrences i p = 0 := by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occurrences j p = 0 := by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)
private theorem neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b', binOp conj (P a b) c ≠ binOp conj (P a' b') c) :
    ∀ a b, binOp conj (P a b) c = P a b := by
  cases conj <;> cases c <;> simp [binOp] at h ⊢
private theorem bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a := by
  cases conj <;> cases a <;> cases b <;> rfl
private theorem combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : occurrences i p + occurrences i q ≤ 1)
    (hj : occurrences j p + occurrences j q ≤ 1)
    (present : hasPair i j p ∨ hasPair i j q)
    (dep_i : 0 < occurrences i p + occurrences i q →
      changes fun a b => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (dep_j : 0 < occurrences j p + occurrences j q →
      changes fun b a => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (ihp : occurrences i p ≤ 1 → occurrences j p ≤ 1 → hasPair i j p →
      (0 < occurrences i p → changes (pairValue i j base p)) →
      (0 < occurrences j p → changes fun b a => pairValue i j base p a b) →
      ∀ a b, pairValue i j base p a b = pairKernel i j p a b)
    (ihq : occurrences i q ≤ 1 → occurrences j q ≤ 1 → hasPair i j q →
      (0 < occurrences i q → changes (pairValue i j base q)) →
      (0 < occurrences j q → changes fun b a => pairValue i j base q a b) →
      ∀ a b, pairValue i j base q a b = pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (pairValue i j base p a b) (pairValue i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b := by
  classical
  have pl : hasPair i j p → ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact changes_left (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_left (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have ql : hasPair i j q → ∀ a b, pairValue i j base q a b = pairKernel i j q a b := by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact changes_right (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_right (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (pairValue i j base p a b) (pairValue i j base q a b) ≠
        binOp conj (pairValue i j base p a' b') (pairValue i j base q a' b') := by
    unfold hasPair at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
  by_cases hp : hasPair i j p
  · by_cases hq : hasPair i j q
    · simp [combine, hp, hq, pl hp, ql hq]
    · rw [constant_pair hq a b]
      have hn := nonconst
      simp_rw [constant_pair hq] at hn
      rw [neutral_right conj _ _ hn a b, pl hp]
      simp [combine, hp, hq]
  · have hq := present.resolve_left hp
    rw [constant_pair hp a b, bin_comm]
    have hn := nonconst
    simp_rw [constant_pair hp, bin_comm conj (pairValue i j base p false false)] at hn
    rw [neutral_right conj _ _ hn a b, ql hq]
    simp [combine, hp]
private theorem stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1) (present : hasPair i j p)
    (dep_i : 0 < occurrences i p → changes (pairValue i j base p))
    (dep_j : 0 < occurrences j p → changes fun b a => pairValue i j base p a b) :
    ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k = i
    · simp [pairValue, pairKernel, DMFormula.eval, pairInput, hki]
    · have hkj : k = j := by
        by_contra h
        simp [hasPair, occurrences, hki, h] at present
      simp [pairValue, pairKernel, DMFormula.eval, pairInput, hkj]
  | and p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base false p q hi hj present' dep_i dep_j ihp ihq
theorem fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b, outerA (pairValue i j baseA p a b) = (a && b))
    (hO : ∀ a b, outerO (pairValue i j baseO p a b) = (a || b)) : False := by
  have depAi : changes (pairValue i j baseA p) := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depAj : changes fun b a => pairValue i j baseA p a b := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p) := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have depOj : changes fun b a => pairValue i j baseO p a b := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have present : hasPair i j p := by
    left
    by_contra! h
    obtain ⟨b, hb⟩ := depAi
    exact hb (absent_left (by omega) false true b)
  have stableA := stable_pair i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO := stable_pair i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false ≠ pairKernel i j p false true := by
    intro e
    have f := congrArg outerO e
    rw [hO, hO] at f
    cases f
  have zeros := hA false false
  have other := hA false true
  have one := hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all
end PetersenScratch
namespace PetersenCutFormula
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open CircuitProof
open PetersenScratch
def negFormula {n : Nat} : DMFormula n → DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (negFormula a) (negFormula b)
  | .or a b => .and (negFormula a) (negFormula b)
theorem negFormula_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
    (negFormula p).eval x = !(p.eval x) := by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [negFormula, DMFormula.eval, e]
  | and a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
theorem negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
    occurrences i (negFormula p) = occurrences i p := by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [negFormula, occurrences, iha, ihb]
  | or a b iha ihb => simp [negFormula, occurrences, iha, ihb]
def wireFormula {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w, hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op, g.inputs with
      | .not, [a] =>
        if _ha : a < w then negFormula (wireFormula fallback gs a) else .lit fallback true
      | .and, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _, _ => .lit fallback true
termination_by w
decreasing_by all_goals assumption
theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true := by
  rw [wireFormula]
  simp [i.isLt]
private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = negFormula (wireFormula fallback gs a) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha]
private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]
private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]
theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wireFormula fallback gs w).eval x = vl gs x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w, hi⟩, vl_input gs x w hi]
      rfl
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha, negFormula_eval, ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0 := by
  rw [wireFormula_input]
  rfl
theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum := by
  rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha, inputs, negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb, inputs, occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb, inputs, occurrences]
theorem wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]? = some g)
    {b : Fin (n + gs.length)} (hb : b.val = n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val = g.inputs) :
    occurrences chosen (wireFormula fallback gs b.val) =
      (parents.map fun a => occurrences chosen (wireFormula fallback gs a.val)).sum := by
  rw [hb, wireFormula_count_gate fallback hcl chosen hg, ← parentsVal, List.map_map]
  rfl
end PetersenCutFormula
namespace PetersenCutIndependent
open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutTrace PetersenScratch
theorem wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    occurrences chosen (wireFormula fallback gs a.val) =
      if a = inputWire gs chosen then 1 else 0 := by
  let i : Fin n := ⟨a.val, ha⟩
  have e : i = chosen ↔ a = inputWire gs chosen := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change occurrences chosen (wireFormula fallback gs i.val) = _
  simp only [wireFormula_count_input, e]
theorem cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut = out ∨ ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  rcases controlled with rfl | blocked
  · exact ⟨id, fun _ _ => rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked
end PetersenCutIndependent
namespace FirstBranchRoute
open Relation
variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)
def Branches (v : Fin m) : Prop := ∃ a b, reads v a ∧ reads v b ∧ a ≠ b
def Terminal (v : Fin m) : Prop := v = output ∨ Branches reads v
def Follow (v w : Fin m) : Prop := reads v w ∧ ¬ Terminal reads output v
lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b := by
  by_contra separate
  exact first.2 (Or.inr ⟨a, b, first.1, next.1, separate⟩)
variable (forward : ∀ {v w : Fin m}, reads v w → v < w)
variable (live : ∀ v : Fin m, v ≠ output → ∃ w, reads v w)
include forward live in
theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m, Terminal reads output root ∧ ReflTransGen (Follow reads output) v root := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v, terminal, ReflTransGen.refl⟩
    obtain ⟨next, edge⟩ := live v (fun e => terminal (Or.inl e))
    have increase := forward edge
    have closer : distance next < distance v := by
      dsimp [distance]
      have bounds := next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root, stopped, route⟩ := ih next closer
    exact ⟨root, stopped, route.head ⟨edge, terminal⟩⟩
include forward in
theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next, edge, tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_, edgeB, _⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB, edgeB, tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal := follow_unique reads output edge edgeB
      subst nextB
      have increase := forward edge.1
      have closer : distance next < distance v := by
        dsimp [distance]
        have bounds := next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB
noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (exists_boundary reads output forward live v)
theorem first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).1
theorem first_path (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).2
theorem first_of_terminal {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v = v :=
  boundary_unique reads output forward (first_stops reads output forward live v) stopped
    (first_path reads output forward live v) ReflTransGen.refl
theorem first_of_follows {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v = first reads output forward live w :=
  boundary_unique reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (first_path reads output forward live v)
    ((first_path reads output forward live w).head step)
include forward in
theorem path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w := by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))
lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1
theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))
theorem read_before {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w ∧ first reads output forward live w = first reads output forward live v := by
  induction route with
  | refl => exact ⟨ReflTransGen.refl, rfl⟩
  | tail _ edge ih =>
    have predecessorBefore := lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked, label⟩ := ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _ := ⟨edge, fun stopped => by
      have self := first_of_terminal reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step, (first_of_follows reads output forward live step).symm.trans label⟩
theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b := by
  have earlier := lt_of_lt_of_le (forward edge) bound
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge, fun stopped => ?_⟩
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same
def Avoid (cut v w : Fin m) : Prop := reads v w ∧ v ≠ cut
lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1
theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v := by
  induction route with
  | refl => exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label := (read_before reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier := lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _ := ⟨edge.1, fun terminal => by
      rw [first_of_terminal reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same := (first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _
theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after
include forward in
theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA, stepA, laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next, stepB, later⟩
      · exact bHere
      have equal : next = goal := follow_unique reads output stepB edgeA
      subst next
      have increasing := path_forward reads forward (follows_is_read_path reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB, stepB, laterB⟩
      · subst b
        have equal : nextA = goal := follow_unique reads output stepA edgeB
        subst nextA
        have increasing := path_forward reads forward (follows_is_read_path reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal := follow_unique reads output stepA stepB
      subst nextB
      have increase := forward stepA.1
      have closer : distance nextA < distance source := by
        dsimp [distance]
        have bounds := nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB
theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b := by
  have aBound := le_trans (le_of_lt (forward edgeA)) bound
  have bBound := le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (read_before reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (read_before reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)
lemma witness_of_positive_sum {α : Type*} (weight : α → Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs, 0 < weight a := by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a, by simp, h⟩
    have hr : 0 < (rest.map weight).sum := by
      simp only [List.map_cons, List.sum_cons] at positive
      omega
    obtain ⟨b, hb, hbPos⟩ := ih hr
    exact ⟨b, by simp [hb], hbPos⟩
lemma sum_le_one_of_unique_positive {α : Type*} (weight : α → Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs, weight a ≤ 1)
    (unique : ∀ a ∈ xs, ∀ b ∈ xs, 0 < weight a → 0 < weight b → a = b) :
    (xs.map weight).sum ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons, List.sum_cons]
    by_cases h : weight a = 0
    · rw [h, Nat.zero_add]
      exact ih distinct.2 (fun b hb => small b (by simp [hb]))
        (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum = 0 := by
      by_contra some
      obtain ⟨b, hb, hbPos⟩ := witness_of_positive_sum weight rest (by omega)
      have equal := unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero, Nat.add_zero]
    exact small a (by simp)
section Count
variable (parents : Fin m → List (Fin m))
variable (reads_parent : ∀ a b : Fin m, reads a b ↔ a ∈ parents b)
variable (weight : Fin m → Nat) (source : Fin m)
variable (other_weight : ∀ v : Fin m, v ≠ source → weight v = ((parents v).map weight).sum)
include forward reads_parent other_weight in
theorem weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v := by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v = source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a, member, hp⟩ := witness_of_positive_sum weight (parents v) positive
    have edge := (reads_parent a v).mpr member
    have earlier := forward edge
    exact (ih a earlier hp).tail edge
include reads_parent other_weight in
theorem weight_before_le_one (rootWeight : weight source = 1) (distinct : ∀ v, (parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1 := by
  revert bound
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro bound
    by_cases isSource : v = source
    · subst v
      exact le_of_eq rootWeight
    rw [other_weight v isSource]
    apply sum_le_one_of_unique_positive weight (parents v) (distinct v)
    · intro a member
      have earlier := forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact unique_predecessor_before reads output forward live bound
        (weight_positive_path reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (weight_positive_path reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)
end Count
end FirstBranchRoute
namespace PetersenFirstGroup
open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutIndependent PetersenCutTrace PetersenScratch
noncomputable def firstInputBoundary {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i = cut
theorem mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut ↔ firstInputBoundary clean out live i = cut := by
  simp [firstInputGroup]
theorem wire_le_output {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (w : Fin (n + gs.length)) : w ≤ out := by
  let last : Fin (n + gs.length) := ⟨n + gs.length - 1, by have := out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last := by
    change v.val ≤ n + gs.length - 1
    have := v.isLt
    omega
  have lastOut : last = out := by
    by_contra notOutput
    obtain ⟨v, e⟩ := live last notOutput
    exact (not_lt_of_ge (top v)) (read_order clean e)
  exact lastOut ▸ top w
theorem firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (fallback chosen : Fin n) :
    occurrences chosen (wireFormula fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1 := by
  let weight (a : Fin (n + gs.length)) := occurrences chosen (wireFormula fallback gs a.val)
  have sourcePrimary : (inputWire gs chosen).val < n := chosen.isLt
  have atSource : weight (inputWire gs chosen) = 1 := by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback chosen _ sourcePrimary, ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length), w ≠ inputWire gs chosen →
      weight w = ((predecessors clean w).map weight).sum := by
    intro w other
    by_cases primary : w.val < n
    · simp [weight, wireFormula_count_input_fin fallback chosen w primary, other,
        predecessors_nil_input clean w primary]
    · let p := w.val - n
      have hp : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have hw : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]
      have atSlot : gs[p]? = some g := List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback chosen clean atSlot hw _
        (predecessors_val_gate clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (readEdge gs) out (read_order clean) live
    (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
    (inputWire gs chosen) otherWeight atSource distinct le_rfl
theorem firstInputGroup_controlled {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) :
    cut = out ∨ ∀ k : Fin n, k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
  by_cases terminal : cut = out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out := lt_of_le_of_ne (wire_le_output clean out live cut) terminal
  have firstHere := (mem_firstInputGroup clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out := by rwa [firstHere]
  have blocked := FirstBranchRoute.no_avoiding_after (readEdge gs) out
    (read_order clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (readEdge gs)
    (firstInputBoundary clean out live k)) (inputWire gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1, e.2.1⟩) _ _ path
end PetersenFirstGroup
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open scoped BigOperators
def operands (gs : List Gate) : List Nat := gs.flatMap Gate.inputs
def notGateCount (gs : List Gate) : Nat := (gs.filter fun g => isNotGate g.op).length
theorem operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs := by
  obtain ⟨g, gAt, before⟩ := read
  exact List.mem_flatMap.mpr ⟨g, List.mem_iff_getElem?.mpr ⟨slot, gAt⟩, before⟩
theorem two_readers_operand_count {gs : List Gate} {wire p q : Nat}
    (neq : p ≠ q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (operands gs).count wire := by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g, atGate, _⟩
    simp at atGate
  | cons a rest ih =>
    simp only [operands, List.flatMap_cons, List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using first
        have later : Reads rest q wire := by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using second
        have later : Reads rest p wire := by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire := by simpa [Reads] using first
        have late : Reads rest q wire := by simpa [Reads] using second
        have different : p ≠ q := fun eq => neq (congrArg Nat.succ eq)
        have count := ih different early late
        simp only [operands] at count
        omega
theorem operands_count_length (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2) :
    (operands gs).length + notGateCount gs = 2 * gs.length := by
  induction gs with
  | nil => simp [operands, notGateCount]
  | cons g gs ih =>
    have gArity := arity g (by simp)
    have rest := ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega
theorem clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2 := by
  intro g gMem
  obtain ⟨p, atGate⟩ := List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [op, args, isNotGate]
  · rcases ops with op | op <;> simp [op, args, isNotGate]
theorem branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w) :
    branches.card + (operands gs).toFinset.card ≤ (operands gs).length := by
  classical
  let W := (operands gs).toFinset
  have subset : branches ⊆ W := by
    intro w wm
    have t := twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) = branches.card := by
    have same : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches, if w ∈ branches then (1 : Nat) else 0 := by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W, (operands gs).count w) = (operands gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W, ((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W, (operands gs).count w := by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (operands gs).count w := List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib, aux, total] at bound
  simpa [W] using bound
theorem branching_budget {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length, w ≠ out → ∃ p, Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches, ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w) :
    branches.card + (n + gs.length - 1) + notGateCount gs ≤ 2 * gs.length := by
  let W := (operands gs).toFinset
  let required := (Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W := by
    intro w inSet
    have spec := Finset.mem_erase.mp inSet
    obtain ⟨p, read⟩ := everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read read)
  have numRequired : required.card = n + gs.length - 1 := by
    change ((Finset.range (n + gs.length)).erase out).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid), Finset.card_range]
  have twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w := by
    intro w mem
    obtain ⟨p, q, different, pReads, qReads⟩ := twoReaders w mem
    exact two_readers_operand_count different pReads qReads
  have up := branch_card_add_wire_card_le_operands gs branches twice
  have used := Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total := operands_count_length gs (clean_gate_arity clean)
  change n + gs.length - 1 ≤ (operands gs).toFinset.card at used
  omega
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace
theorem branch_slots_of_read_edges {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (readEdge gs) w) :
    ∃ p q, p ≠ q ∧ Reads gs p w.val ∧ Reads gs q w.val := by
  obtain ⟨first, next, pRead, qRead, separate⟩ := fork
  obtain ⟨p, g, atP, src, ap⟩ := pRead
  obtain ⟨q, h, atQ, dst, aq⟩ := qRead
  refine ⟨p, q, ?_, ⟨g, atP, ap⟩, ⟨h, atQ, aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))
noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)) := by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (readEdge gs) w
theorem in_circuit_branches {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs ↔ FirstBranchRoute.Branches (readEdge gs) w := by
  classical
  simp [circuitBranchWires]
open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutTrace Relation
open PEqualNP.CircuitLowerBounds CircuitProof
open PetersenCutTrace
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup
open PEqualNP.CircuitLowerBounds CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup
end PEqualNP.Outside.L_meta_3138_aux
namespace PEqualNP.Outside.L_meta_3138_aux.Coloring
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3138_aux
open PEqualNP.Outside.L_meta_3138_aux.CircuitProof
open PEqualNP.Outside.L_meta_3138_aux.CircuitProof.Readers
open PEqualNP.Outside.L_meta_3138_aux.PetersenCutFormula
open PEqualNP.Outside.L_meta_3138_aux.PetersenCutIndependent
open PEqualNP.Outside.L_meta_3138_aux.PetersenFirstGroup
open PEqualNP.Outside.L_meta_3138_aux.PetersenCutTrace
open PEqualNP.Outside.L_meta_3138_aux.PetersenScratch
theorem boundaryDiff {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (i j : Fin n) (baseA baseO : Fin n → Bool)
    (hA : ∀ a b, vl gs (pairInput i j baseA a b) out.val = (a && b))
    (hO : ∀ a b, vl gs (pairInput i j baseO a b) out.val = (a || b)) :
    firstInputBoundary clean out live i ≠ firstInputBoundary clean out live j := by
  intro same
  let cut := firstInputBoundary clean out live i
  have hi := firstInputBoundary_occurrences_le_one clean out live distinct i i
  have hj := firstInputBoundary_occurrences_le_one clean out live distinct i j
  rw [← same] at hj
  have controlled : cut = out ∨ ∀ k : Fin n, (k = i ∨ k = j) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
    rcases firstInputGroup_controlled clean out live cut with h | h
    · exact Or.inl h
    · apply Or.inr
      intro k hk
      apply h
      apply (mem_firstInputGroup clean out live cut k).mpr
      rcases hk with hk | hk
      · rw [hk]
      · rw [hk]
        exact same.symm
  have factor (base : Fin n → Bool) : ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue i j base (wireFormula i gs cut.val) a b) =
        vl gs (pairInput i j base a b) out.val := by
    obtain ⟨outer, ho⟩ := cut_factors clean cut out (fun k => k = i ∨ k = j) base controlled
    refine ⟨outer, fun a b => ?_⟩
    unfold pairValue
    rw [wireFormula_eval i clean _ cut.val cut.isLt]
    apply ho
    intro k hk
    simp [pairInput, show k ≠ i from fun h => hk (Or.inl h),
      show k ≠ j from fun h => hk (Or.inr h)]
  obtain ⟨fa, ha⟩ := factor baseA
  obtain ⟨fo, ho⟩ := factor baseO
  exact fixed_pair_invariant i j (wireFormula i gs cut.val) hi hj baseA baseO fa fo
    (fun a b => (ha a b).trans (hA a b)) (fun a b => (ho a b).trans (hO a b))
theorem groupBudget {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v) :
    (insert out (circuitBranchWires (n := n) gs)).card ≤ 2 + gs.length - n - notGateCount gs := by
  classical
  let branches := circuitBranchWires (n := n) gs
  have h := branching_budget clean out.isLt (fun w hw hne => by
    let wire : Fin (n + gs.length) := ⟨w, hw⟩
    obtain ⟨v,p,g,hg,_,hw'⟩ := live wire (fun e => hne (congrArg Fin.val e))
    exact ⟨p,g,hg,hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at h
  have card := Finset.card_insert_le out branches
  have positive := out.isLt
  change (insert out branches).card ≤ _
  omega
theorem boundedColoring {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (conflict : Fin n → Fin n → Prop)
    (witness : ∀ i j, conflict i j → ∃ (baseA baseO : Fin n → Bool),
      (∀ a b, vl gs (pairInput i j baseA a b) out.val = (a && b)) ∧
        (∀ a b, vl gs (pairInput i j baseO a b) out.val = (a || b))) :
    ∃ colors : Fin n → Fin (2 + gs.length - n - notGateCount gs),
      ∀ i j, conflict i j → colors i ≠ colors j := by
  classical
  let palette := insert out (circuitBranchWires (n := n) gs)
  let boundary := firstInputBoundary clean out live
  have member (i : Fin n) : boundary i ∈ palette := by
    rcases FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs i)
      with ho | hb
    · exact Finset.mem_insert.mpr (Or.inl ho)
    · exact Finset.mem_insert.mpr (Or.inr (in_circuit_branches.mpr hb))
  let rank := (palette.orderIsoOfFin rfl).symm
  let whereAt (i : Fin n) : palette := ⟨boundary i,member i⟩
  let cap := 2 + gs.length - n - notGateCount gs
  have bound : palette.card ≤ cap := groupBudget clean out live
  let col (i : Fin n) : Fin cap := Fin.castLE bound (rank (whereAt i))
  refine ⟨col, ?_⟩
  intro i j edge hi
  obtain ⟨baseA,baseO,hA,hO⟩ := witness i j edge
  have eq : rank (whereAt i) = rank (whereAt j) := Fin.ext (congrArg (fun v : Fin cap => v.val) hi)
  exact boundaryDiff clean out live distinct i j baseA baseO hA hO
    (congrArg Subtype.val (rank.injective eq))
end PEqualNP.Outside.L_meta_3138_aux.Coloring
namespace PEqualNP.Outside.L_meta_3138

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_3138_aux
open PEqualNP.Outside.L_meta_3138_aux.CircuitProof
open PEqualNP.Outside.L_meta_3138_aux.CircuitProof.Readers
open PEqualNP.Outside.L_meta_3138_aux.PetersenCutTrace

private lemma color_bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma color_bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]


structure ColorPrefix {n : Nat} (row : Row → Fin n → Bool) (S : Finset Sig) where
  gs : List Gate
  loc : Sig → Nat
  range : ∀ w ∈ S, loc w < n + gs.length
  injective : ∀ x ∈ S, ∀ y ∈ S, loc x = loc y → x = y
  value : ∀ w ∈ S, ∀ r, vl gs (row r) (loc w) = bit r w
  clean : CleanL n gs
  distinct : ∀ g ∈ gs, g.inputs.Nodup
  used : ∀ i < n + gs.length,
    (∃ w ∈ S, loc w = i) ∨ ∃ g ∈ gs, i ∈ g.inputs

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

noncomputable def colorPush {n : Nat} {row : Row → Fin n → Bool} {S U : Finset Sig}
    (p : ColorPrefix row S) (z : Sig) (hz : z ∉ U) (g : Gate)
    (keep : U ⊆ S)
    (consume : ∀ w ∈ S, w ∉ U → p.loc w ∈ g.inputs)
    (legal : CleanGate (n+p.gs.length) g) (nd : g.inputs.Nodup)
    (value : ∀ r, g.op.eval (g.inputs.map (vl p.gs (row r))) = bit r z) :
    ColorPrefix row (insert z U) := by
  classical
  let last := n + p.gs.length
  let out := p.gs ++ [g]
  let loc (w : Sig) := if w = z then last else p.loc w
  have stable (w : Sig) (h : w ∈ U) : loc w = p.loc w :=
    if_neg (fun (e : w = z) => hz (e ▸ h))
  have existsG : g ∈ out := by simp [out]
  have snoc (r : Row) (i : Nat) (hi : i < last) :
      vl out (row r) i = vl p.gs (row r) i := by
    unfold vl
    rw [show out = p.gs ++ [g] from rfl, wiresFrom_append, getD_wiresFrom]
    simpa [last,length_wiresFrom] using hi
  have register (r : Row) : vl out (row r) last = bit r z := by
    unfold vl
    rw [show out = p.gs ++ [g] from rfl, wiresFrom_append]
    let b := wiresFrom p.gs (List.ofFn (row r))
    change (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]).getD last false = _
    have size : b.length = last := by simp [b,length_wiresFrom,last]
    rw [←size,getD_snoc_eq]
    exact value r
  refine ⟨out,loc,?_,?_,?_,?_,?_,?_⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hu
    · simp [loc,last,out]
    · rw [stable _ hu]
      have := p.range w (keep hu)
      simp [out]
      omega
  · intro x hx y hy e
    rcases Finset.mem_insert.mp hx with rfl | hux <;>
      rcases Finset.mem_insert.mp hy with rfl | huy
    · rfl
    · rw [stable _ huy] at e
      have h := p.range y (keep huy)
      simp [loc,last] at e
      omega
    · rw [stable _ hux] at e
      have h := p.range x (keep hux)
      simp [loc,last] at e
      omega
    · rw [stable _ hux,stable _ huy] at e
      exact p.injective x (keep hux) y (keep huy) e
  · intro w hw r
    rcases Finset.mem_insert.mp hw with rfl | hu
    · simpa [loc] using register r
    · rw [stable _ hu, snoc _ _ (p.range w (keep hu))]
      exact p.value w (keep hu) r
  · intro i h hi
    by_cases old : i < p.gs.length
    · exact p.clean _ _ (by simpa [out,List.getElem?_append_left old] using hi)
    · have ix : i = p.gs.length := by
        have hlt := (List.getElem?_eq_some_iff.mp hi).1
        simp [out] at hlt
        omega
      subst i
      have he : g = h := by simpa [out] using hi
      simpa [←he] using legal
  · intro h hh
    rcases List.mem_append.mp hh with old | tail
    · exact p.distinct h old
    · have := List.mem_singleton.mp tail
      simpa [this] using nd
  · intro i hi
    by_cases old : i < last
    · rcases p.used i old with ⟨w,hw,eq⟩ | ⟨h,hm,hpin⟩
      · by_cases hu : w ∈ U
        · exact Or.inl ⟨w,Finset.mem_insert_of_mem hu,(stable _ hu).trans eq⟩
        · exact Or.inr ⟨g,existsG,eq ▸ consume _ hw hu⟩
      · exact Or.inr ⟨h,List.mem_append_left _ hm,hpin⟩
    · have eq : i = last := by simp [out,last] at hi old ⊢; omega
      exact Or.inl ⟨z,Finset.mem_insert_self _ _,by simp [loc,eq]⟩

def ColorRealization {n : Nat} (row : Row → Fin n → Bool) (T : Sig)
    (gateCount nots : Nat) : Prop :=
  ∃ (gs : List Gate) (clean : CleanL n gs) (out : Fin (n + gs.length)),
    gs.length = gateCount ∧ notGateCount gs = nots ∧
    (∀ i : Fin (n + gs.length), i ≠ out → ∃ j, readEdge gs i j) ∧
    (∀ i, (predecessors clean i).Nodup) ∧
    ∀ r, vl gs (row r) out.val = bit r T

theorem finishColor {n : Nat} {row : Row → Fin n → Bool} {T : Sig}
    (p : ColorPrefix row {T}) : ColorRealization row T p.gs.length (notGateCount p.gs) := by
  classical
  let out : Fin (n+p.gs.length) := ⟨p.loc T,p.range T (by simp)⟩
  refine ⟨p.gs,p.clean,out,rfl,rfl,?_,?_,fun r => p.value T (by simp) r⟩
  · intro w hne
    rcases p.used w.val w.isLt with ⟨u,hu,eq⟩ | ⟨g,hg,hpin⟩
    · have he : u=T := Finset.mem_singleton.mp hu
      subst u
      exact False.elim (hne (Fin.ext eq.symm))
    · obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
      have lt := (List.getElem?_eq_some_iff.mp hi).1
      exact ⟨⟨n+i,by omega⟩,i,g,hi,rfl,hpin⟩
  · intro w
    by_cases hi : w.val < n
    · simp [predecessors_nil_input p.clean w hi]
    · apply List.Nodup.of_map Fin.val
      rw [predecessors_values p.clean w (by omega)]
      exact p.distinct _ (List.getElem_mem _)

theorem realizeFrom {n : Nat} {row : Row → Fin n → Bool} {T : Sig} {k t S}
    (run : Live T k t S) :
    ∀ p : ColorPrefix row S, ColorRealization row T (p.gs.length+k) (notGateCount p.gs+t) := by
  classical
  induction run with
  | stop hp =>
    intro p
    simpa using finishColor p
  | @unary k t U a ha fresh tail ih =>
    intro p
    let g : Gate := ⟨.not,[p.loc a]⟩
    have am : a ∈ insert a U := Finset.mem_insert_self _ _
    let q := colorPush p (neg a) (fun h => fresh (Finset.mem_insert_of_mem h)) g
      (fun _ h => Finset.mem_insert_of_mem h)
      (by
        intro w hw hgone
        have he : w=a := (Finset.mem_insert.mp hw).resolve_right hgone
        simp [g,he])
      (Or.inl ⟨rfl,_,p.range _ am,rfl⟩)
      (by simp [g])
      (by intro r; simp [g,GateOp.eval,p.value _ am,color_bit_neg])
    have h := ih q
    change ColorRealization row T ((p.gs++[g]).length+k) (notGateCount (p.gs++[g])+t) at h
    simpa [g,notGateCount,isNotGate,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  | @binary k t U a b d ha hb hab fresh tail ih =>
    intro p
    have am : a ∈ insert a (insert b U) := Finset.mem_insert_self _ _
    have bm : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    let g : Gate := ⟨if d then .or else .and,[p.loc a,p.loc b]⟩
    have nd : p.loc a ≠ p.loc b := fun he => hab (p.injective _ am _ bm he)
    let q := colorPush p (bin d a b)
      (fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))) g
      (fun _ h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      (by
        intro w hw lost
        rcases Finset.mem_insert.mp hw with rfl | hw
        · simp [g]
        · have he := (Finset.mem_insert.mp hw).resolve_right lost
          simp [g,he])
      (Or.inr ⟨by cases d <;> simp [g],_,_,p.range _ am,p.range _ bm,rfl⟩)
      (by simp [g,nd])
      (by intro r; cases d <;> simp [g,GateOp.eval,p.value _ am,p.value _ bm,color_bit_bin])
    have h := ih q
    change ColorRealization row T ((p.gs++[g]).length+k) (notGateCount (p.gs++[g])+t) at h
    cases d <;> simpa [g,notGateCount,isNotGate,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem realizeLive {T : Sig} {k t : Nat} (front : List Sig) (hn : front.Nodup)
    (h : Live T k t front.toFinset) :
    ColorRealization (fun (r : Row) (i : Fin front.length) => bit r (front.get i)) T k t := by
  classical
  let loc (w : Sig) := front.idxOf w
  let row (r : Row) (i : Fin front.length) := bit r (front.get i)
  have valid (w : Sig) (hw : w ∈ front.toFinset) : loc w < front.length :=
    List.idxOf_lt_length_of_mem (List.mem_toFinset.mp hw)
  have getLoc (w : Sig) (hw : w ∈ front.toFinset) :
      front.get ⟨loc w, valid w hw⟩ = w := by
    simpa [loc] using List.getElem_idxOf (xs:=front) (x:=w) (valid w hw)
  let p : ColorPrefix row front.toFinset :=
    ⟨[],loc,(by simpa using valid),
      (by
        intro x hx y hy eq
        have eqi : (⟨loc x,valid x hx⟩ : Fin front.length) = ⟨loc y,valid y hy⟩ := Fin.ext eq
        exact (getLoc x hx).symm.trans ((congrArg front.get eqi).trans (getLoc y hy))),
      (by intro w hw r; rw [vl_input _ _ _ (valid _ hw)]; exact congrArg (bit r) (getLoc w hw)),
      (by simp [CleanL]),(by simp),
      (by
        intro i hi
        have il : i < front.length := by simpa using hi
        let ix : Fin front.length := ⟨i,il⟩
        left
        refine ⟨front.get ix,List.mem_toFinset.mpr (List.get_mem _ _),?_⟩
        simpa [loc,ix] using hn.idxOf_getElem i il)⟩
  have result := realizeFrom h p
  change ColorRealization row T (0+k) (0+t) at result
  simpa only [Nat.zero_add] using result
end PEqualNP.Outside.L_meta_3138


namespace PEqualNP.Outside.L_meta_3138
open PEqualNP.Outside.L_meta_3138_aux.CircuitProof
open PEqualNP.Outside.L_meta_3138_aux.PetersenScratch
open PEqualNP.Outside.L_meta_3138_aux.Coloring

def rowValues (ws : List Sig) (r : Row) (i : Fin ws.length) := bit r (ws.get i)

/-- The four supplied input rows give an AND or OR cofactor while all the other
    frontier coordinates retain the same values. -/
def SquareOk (ws : List Sig) (T : Sig) (i j : Fin ws.length) (isOr : Bool)
    (sample : Bool → Bool → Row) : Prop :=
  ∀ a b, bit (sample a b) T = (if isOr then a || b else a && b) ∧
    ∀ v, rowValues ws (sample a b) v = pairInput i j (rowValues ws (sample false false)) a b v

instance {ws T i j isOr sample} : Decidable (SquareOk ws T i j isOr sample) := by
  unfold SquareOk
  infer_instance

def ColorConflict (ws : List Sig) (T : Sig) (i j : Fin ws.length) : Prop :=
  ∃ andRows orRows, SquareOk ws T i j false andRows ∧ SquareOk ws T i j true orRows

theorem colorsOfLive {ws : List Sig} {T : Sig} {k t : Nat}
    (nd : ws.Nodup) (run : Live T k t ws.toFinset) :
    ∃ c : Fin ws.length → Fin (2+k-ws.length-t), ∀ i j, ColorConflict ws T i j → c i ≠ c j := by
  obtain ⟨gs, clean, out, rfl, rfl, live, distinct, values⟩ := realizeLive ws nd run
  have hc := boundedColoring clean out live distinct (ColorConflict ws T) (by
    intro i j edge
    obtain ⟨andRows,orRows,ha,ho⟩ := edge
    refine ⟨rowValues ws (andRows false false),rowValues ws (orRows false false),?_,?_⟩
    · intro a b
      rw [← funext (ha a b).2]
      exact (values _).trans (ha a b).1
    · intro a b
      rw [← funext (ho a b).2]
      exact (values _).trans (ho a b).1)
  exact hc

def Inversion (ws : List Sig) (T : Sig) (r s : Row) : Prop :=
  bit r T = true ∧ bit s T = false ∧
  ∀ i : Fin ws.length, bit r (ws.get i) = true → bit s (ws.get i) = true

instance {ws T r s} : Decidable (Inversion ws T r s) := by unfold Inversion; infer_instance

theorem inversionHasNot {ws : List Sig} {T : Sig} {k t : Nat} {r s : Row}
    (h : Inversion ws T r s) (run : Live T k t ws.toFinset) : 0 < t := by
  by_contra! ht
  obtain ⟨v,hv,h₁,h₂⟩ := mono_row_difference run (by omega) h.1 h.2.1
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hv)
  have impossible := h.2.2 i (hi.symm ▸ h₁)
  rw [hi,h₂] at impossible
  contradiction
theorem cliqueCut {ws : List Sig} {T : Sig} {k t m : Nat} (nd : ws.Nodup)
    (pick : Fin m → Fin ws.length) (tooMany : 2+k-ws.length-t < m)
    (edges : ∀ a b, a < b → ColorConflict ws T (pick a) (pick b)) :
    ¬ Live T k t ws.toFinset := by
  intro run
  obtain ⟨color,prop⟩ := colorsOfLive nd run
  have inj : Function.Injective (fun a => color (pick a)) := by
    intro a b eq
    rcases lt_trichotomy a b with lt | same | gt
    · exact False.elim (prop _ _ (edges _ _ lt) eq)
    · exact same
    · exact False.elim (prop _ _ (edges _ _ gt) eq.symm)
  have := Fintype.card_le_of_injective _ inj
  simp only [Fintype.card_fin] at this
  omega

theorem oddCycleCut {ws : List Sig} {T : Sig} {k t s : Nat} (nd : ws.Nodup)
    (route : Nat → Fin ws.length) (small : 2+k-ws.length-t ≤ 2)
    (closed : route (2*s+1) = route 0)
    (edges : ∀ i, i < 2*s+1 → ColorConflict ws T (route i) (route (i+1))) :
    ¬ Live T k t ws.toFinset := by
  intro run
  obtain ⟨c,prop⟩ := colorsOfLive nd run
  let val (i : Nat) := (c (route i)).val
  have bound (i : Nat) : val i < 2 := lt_of_lt_of_le (c (route i)).isLt small
  have diff (i : Nat) (hi : i < 2*s+1) : val i ≠ val (i+1) := by
    intro eq
    exact prop _ _ (edges i hi) (Fin.ext eq)
  have same (i : Nat) (hi : i ≤ s) : val (2*i) = val 0 := by
    induction i with
    | zero => rfl
    | succ i ih =>
      have h₀ := ih (by omega)
      have d₀ := diff (2*i) (by omega)
      have d₁ := diff (2*i+1) (by omega)
      have b₀ := bound (2*i)
      have b₁ := bound (2*i+1)
      have b₂ := bound (2*i+1+1)
      rw [show 2*(i+1) = 2*i+1+1 by omega]
      omega
  have last := diff (2*s) (by omega)
  have h := same s (le_refl _)
  apply last
  exact h.trans (congrArg (fun x => (c x).val) closed.symm)

end PEqualNP.Outside.L_meta_3138
namespace PEqualNP.Outside.L_meta_3138
open PEqualNP.Outside.L_meta_3138_aux.PetersenScratch

def checkWires (f : Nat → Sig → Bool) (offset : Nat) : List Sig → Bool
  | [] => true
  | w::ws => f offset w && checkWires f (offset+1) ws

theorem checkWires_sound {f off ws} (h : checkWires f off ws = true) (i : Fin ws.length) :
    f (off+i.val) (ws.get i) = true := by
  induction ws generalizing off with
  | nil => exact Fin.elim0 i
  | cons w ws ih =>
    obtain ⟨hf,ht⟩ := Bool.and_eq_true_iff.mp h
    cases i using Fin.cases with
    | zero => simpa using hf
    | succ j =>
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih ht j

def patternOK (i j v : Nat) (z x y w : Bool) : Bool :=
  if v = i then !z && !x && y && w
  else if v = j then !z && x && !y && w
  else (z == x) && (z == y) && (z == w)

def quickSquare (ws : List Sig) (T : Sig) (i j : Fin ws.length) (isOr : Bool)
    (sample : Bool → Bool → Row) : Bool :=
  let rf := sample false false
  let rx := sample false true
  let ry := sample true false
  let rt := sample true true
  !bit rf T && (bit rx T == isOr) && (bit ry T == isOr) && bit rt T &&
    checkWires (fun v s => patternOK i j v (bit rf s) (bit rx s) (bit ry s) (bit rt s)) 0 ws

theorem quickSquare_sound {ws T i j d rows} (ok : quickSquare ws T i j d rows = true) :
    SquareOk ws T i j d rows := by
  simp only [quickSquare,Bool.and_eq_true_iff,Bool.not_eq_true',beq_iff_eq] at ok
  obtain ⟨⟨⟨⟨hf,hx⟩,hy⟩,ht⟩,hs⟩ := ok
  intro a b
  constructor
  · cases a <;> cases b <;> cases d <;> simp_all
  · intro v
    have hv := checkWires_sound hs v
    simp only [Nat.zero_add] at hv
    change patternOK i j v _ _ _ _ = true at hv
    by_cases vi : v = i
    · subst v
      simp only [patternOK,ite_true,Bool.and_eq_true_iff,Bool.not_eq_true'] at hv
      cases a <;> cases b <;> simp only [pairInput,rowValues,ite_true] <;> first | exact hv.1.1.1 | exact hv.1.1.2 | exact hv.1.2 | exact hv.2
    · by_cases vj : v = j
      · subst v
        have ij : j.val ≠ i.val := fun h => vi (Fin.ext h)
        simp only [patternOK,if_neg ij,ite_true,Bool.and_eq_true_iff,Bool.not_eq_true'] at hv
        cases a <;> cases b <;> simp only [pairInput,rowValues,if_neg vi,ite_true] <;> first | exact hv.1.1.1 | exact hv.1.1.2 | exact hv.1.2 | exact hv.2
      · have v₁ : v.val ≠ i.val := fun h => vi (Fin.ext h)
        have v₂ : v.val ≠ j.val := fun h => vj (Fin.ext h)
        simp only [patternOK,if_neg v₁,if_neg v₂,Bool.and_eq_true_iff,beq_iff_eq] at hv
        cases a <;> cases b <;> simp only [pairInput,rowValues,if_neg vi,if_neg vj] <;> first | rfl | exact hv.1.1.symm | exact hv.1.2.symm | exact hv.2.symm

end PEqualNP.Outside.L_meta_3138

namespace PEqualNP.Outside.L_meta_3138
namespace Packed

def size (p : Nat) := (p >>> 2) % 16
def inverted (p : Nat) := p % 2
def isCycle (p : Nat) := (p >>> 1) % 2
def vertex (n p i : Nat) : Fin (n+1) :=
  Fin.ofNat (n+1) ((p >>> (24 + 4*(i % size p))) % 16)
def witness (p edge : Nat) (isOr a b : Bool) : Row :=
  let row := 8*edge + 4*isOr.toNat + 2*a.toNat + b.toNat
  Fin.ofNat 512 ((p >>> (24 + 4*size p + 9*row)) % 512)
def cliqueIndex (m i j : Nat) := i*(2*m-i-1)/2+(j-i-1)

def edgeOK (ws : List Sig) (T : Sig) (i j : Fin ws.length) (p edge : Nat) : Prop :=
  quickSquare ws T i j false (witness p edge false) = true ∧ quickSquare ws T i j true (witness p edge true) = true
instance {ws T i j p e} : Decidable (edgeOK ws T i j p e) := by unfold edgeOK; infer_instance
theorem edgeOK_sound {ws T i j p e} (h : edgeOK ws T i j p e) : ColorConflict ws T i j :=
  ⟨_,_,quickSquare_sound h.1,quickSquare_sound h.2⟩

def valid (w : Sig) (ws : List Sig) (T : Sig) (cap p : Nat) : Prop :=
  let m := size p
  let palette := 2+cap-(ws.length+1)-inverted p
  (w::ws).Nodup ∧
  (inverted p ≠ 0 → Inversion (w::ws) T (Fin.ofNat 512 (p >>> 6)) (Fin.ofNat 512 (p >>> 15))) ∧
  (if isCycle p = 1 then
    m = 2*(m/2)+1 ∧ palette ≤ 2 ∧
    ∀ i : Fin m, edgeOK (w::ws) T (vertex ws.length p i) (vertex ws.length p (i+1 : Nat)) p i
   else
    palette < m ∧
    ∀ i j : Fin m, i < j →
      edgeOK (w::ws) T (vertex ws.length p i) (vertex ws.length p j) p
        (cliqueIndex m i j))

instance {w ws T cap p} : Decidable (valid w ws T cap p) := by
  unfold valid; dsimp only; split <;> infer_instance

theorem sound {w ws T cap p} (ok : valid w ws T cap p) {k t : Nat} (hk : k ≤ cap) :
    ¬ Live T k t (w::ws).toFinset := by
  intro run
  obtain ⟨nd,hi,shape⟩ := ok
  have minT : inverted p ≤ t := by
    by_cases z : inverted p = 0
    · omega
    · have ht := inversionHasNot (hi z) run
      have hlt : inverted p < 2 := Nat.mod_lt _ (by decide)
      omega
  have budget : 2+k-(w::ws).length-t ≤ 2+cap-(ws.length+1)-inverted p := by
    simp only [List.length_cons]; omega
  split at shape
  · obtain ⟨hs,hcap,he⟩ := shape
    have cyc : vertex ws.length p (2*(size p/2)+1) = vertex ws.length p 0 := by
      rw [← hs]; simp [vertex]
    apply oddCycleCut nd (vertex ws.length p) (le_trans budget hcap) cyc _ run
    intro i h
    have hi : i < size p := by omega
    exact edgeOK_sound (he ⟨i,hi⟩)
  · obtain ⟨hcap,he⟩ := shape
    apply cliqueCut nd (fun (i : Fin (size p)) => vertex ws.length p i)
      (lt_of_le_of_lt budget hcap) _ run
    exact fun i j h => edgeOK_sound (he i j h)

end Packed

def colorOk (ws : List Sig) (T : Sig) (cap p : Nat) : Bool :=
  match ws with
  | [] => false
  | w::tail => decide (Packed.valid w tail T cap p)

theorem colorOk_sound {ws : List Sig} {T : Sig} {cap p : Nat}
    (checked : colorOk ws T cap p = true) {k t : Nat} (hk : k ≤ cap) :
    ¬ Live T k t ws.toFinset := by
  cases ws with
  | nil => contradiction
  | cons w tail =>
    exact Packed.sound (of_decide_eq_true checked) hk

end PEqualNP.Outside.L_meta_3138
namespace PEqualNP.Outside.L_meta_3138


open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3138_aux
open PEqualNP.Outside.L_meta_3138_aux.CircuitProof
open PEqualNP.Outside.L_meta_3138_aux.PetersenScratch
open PEqualNP.Outside.L_meta_3138_aux.Coloring

def RowLE {n : Nat} (a b : Fin n → Bool) : Prop := ∀ i, a i = true → b i = true

instance {n : Nat} {a b : Fin n → Bool} : Decidable (RowLE a b) := by
  unfold RowLE
  infer_instance

theorem vl_mono {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (noNot : notGateCount gs = 0) {a b : Fin n → Bool} (le : RowLE a b)
    (w : Nat) (range : w < n + gs.length) : vl gs a w = true → vl gs b w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases input : w < n
    · rw [vl_input gs a w input, vl_input gs b w input]
      exact le ⟨w,input⟩
    · let p := w-n
      have index : p < gs.length := by dsimp [p]; omega
      let g := gs[p]
      have hit : gs[p]? = some g := by simp [g,index]
      have pos : w = n+p := by dsimp [p]; omega
      rw [pos,vl_gate gs clean a p g hit,vl_gate gs clean b p g hit]
      rcases clean p g hit with ⟨op, j, _, _⟩ | ⟨op, j, l, hj, hl, pins⟩
      · have empty : (gs.filter fun v => isNotGate v.op) = [] := by
          simpa [notGateCount] using noNot
        have member : g ∈ gs := List.mem_iff_getElem?.mpr ⟨p,hit⟩
        have bad : g ∈ gs.filter (fun v => isNotGate v.op) :=
          List.mem_filter.mpr ⟨member,by simp [op,isNotGate]⟩
        simp [empty] at bad
      · have Lj : j < w := by omega
        have Ll : l < w := by omega
        have J := ih j Lj (by omega)
        have L := ih l Ll (by omega)
        rcases op with op | op <;> rw [op,pins] <;>
          simp only [List.map_cons,List.map_nil,GateOp.eval] <;>
          cases aj : vl gs a j <;> cases al : vl gs a l <;>
          cases bj : vl gs b j <;> cases bl : vl gs b l <;> simp_all

def MonoSquare (ws : List Sig) (T : Sig) (i j : Fin ws.length) (isOr : Bool)
    (base : Fin ws.length → Bool) (sample : Bool → Bool → Row) : Prop :=
  ∀ a b, let value := if isOr then a || b else a && b
         let corner := pairInput i j base a b
         let row := rowValues ws (sample a b)
         bit (sample a b) T = value ∧ (if value then RowLE row corner else RowLE corner row)

instance {ws T i j isOr base sample} : Decidable (MonoSquare ws T i j isOr base sample) := by
  unfold MonoSquare
  infer_instance

def MonoConflict (ws : List Sig) (T : Sig) (i j : Fin ws.length) : Prop :=
  ∃ a o ra ro, MonoSquare ws T i j false a ra ∧ MonoSquare ws T i j true o ro

theorem colorsOfMonoLive {ws : List Sig} {T : Sig} {k : Nat}
    (nd : ws.Nodup) (run : Live T k 0 ws.toFinset) :
    ∃ c : Fin ws.length → Fin (2+k-ws.length), ∀ i j, MonoConflict ws T i j → c i ≠ c j := by
  obtain ⟨gs, clean, out, rfl, noNot, live, distinct, values⟩ := realizeLive ws nd run
  have hc := boundedColoring clean out live distinct (MonoConflict ws T) (by
    intro i j edge
    obtain ⟨a,o,ra,ro,ha,ho⟩ := edge
    have lift {isOr base sample} (hs : MonoSquare ws T i j isOr base sample) (x y : Bool) :
        vl gs (pairInput i j base x y) out.val = (if isOr then x || y else x && y) := by
      obtain ⟨eq,le⟩ := hs x y
      have eval := (values (sample x y)).trans eq
      cases v : (if isOr then x || y else x && y) with
      | true =>
        rw [v] at le eval
        exact vl_mono clean noNot le out.val out.isLt eval
      | false =>
        rw [v] at le eval
        cases e : vl gs (pairInput i j base x y) out.val with
        | false => rfl
        | true => have bad := vl_mono clean noNot le out.val out.isLt e
                  have contra : false = true := eval.symm.trans bad
                  contradiction
    exact ⟨a,o,lift ha,lift ho⟩)
  have z : notGateCount gs = 0 := noNot
  rw [z,Nat.sub_zero] at hc
  exact hc



namespace SplitCut
open PEqualNP.Outside.L_meta_3138_aux.PetersenScratch

def shape {n : Nat} (p palette : Nat) (edge : Fin (n+1) → Fin (n+1) → Nat → Prop) : Prop :=
  let m := Packed.size p
  let v := Packed.vertex n p
  if Packed.isCycle p = 1 then
    m = 2*(m/2)+1 ∧ palette ≤ 2 ∧ ∀ i : Fin m, edge (v i) (v (i+1 : Nat)) i
  else
    palette < m ∧ ∀ i j : Fin m, i < j → edge (v i) (v j) (Packed.cliqueIndex m i j)

instance {n p palette edge} [de : ∀ i j s, Decidable (edge i j s)] :
    Decidable (@shape n p palette edge) := by
  unfold shape; dsimp only; split <;> infer_instance

theorem excludes {n p budget actual} {edge : Fin (n+1) → Fin (n+1) → Nat → Prop}
    (hs : shape p budget edge) (le : actual ≤ budget) (c : Fin (n+1) → Fin actual)
    (h : ∀ i j s, edge i j s → c i ≠ c j) : False := by
  unfold shape at hs; dsimp only at hs
  split at hs
  · obtain ⟨odd,small,edges⟩ := hs
    let v (i : Nat) := (c (Packed.vertex n p i)).val
    have two (i : Nat) : v i < 2 := lt_of_lt_of_le (c _).isLt (le_trans le small)
    have diff (i : Nat) (hi : i < Packed.size p) : v i ≠ v (i+1) := by
      intro eq
      exact h _ _ i (edges ⟨i,hi⟩) (Fin.ext eq)
    have same (i : Nat) (hi : i ≤ Packed.size p/2) : v (2*i) = v 0 := by
      induction i with
      | zero => rfl
      | succ i ih =>
        have h0 := ih (by omega)
        have h1 := diff (2*i) (by omega)
        have h2 := diff (2*i+1) (by omega)
        have u := two (2*i)
        have w := two (2*i+1)
        have z := two (2*i+1+1)
        rw [show 2*(i+1) = 2*i+1+1 by omega]
        omega
    have cyc : v (Packed.size p) = v 0 := by simp [v,Packed.vertex]
    have last := diff (2*(Packed.size p/2)) (by omega)
    apply last
    calc
      v (2*(Packed.size p/2)) = v 0 := same _ (le_refl _)
      _ = v (2*(Packed.size p/2)+1) := by rw [← odd]; exact cyc.symm
  · obtain ⟨small,edges⟩ := hs
    have inj : Function.Injective (fun i : Fin (Packed.size p) => c (Packed.vertex n p i)) := by
      intro i j eq
      rcases lt_trichotomy i j with lt | eq' | gt
      · exact False.elim (h _ _ _ (edges i j lt) eq)
      · exact eq'
      · exact False.elim (h _ _ _ (edges j i gt) eq.symm)
    have card := Fintype.card_le_of_injective _ inj
    simp only [Fintype.card_fin] at card
    omega

def mrow (p edge slot : Nat) : Row :=
  Fin.ofNat 512 ((p >>> (24+4*Packed.size p + 9*(6*edge+slot))) % 512)

def mrows (p s : Nat) (isOr a b : Bool) : Row :=
  if isOr then mrow p s (if a then 5 else if b then 4 else 3)
  else mrow p s (if a then (if b then 0 else 2) else 1)

def monoEdge (ws : List Sig) (T : Sig) (i j : Fin ws.length) (p s : Nat) : Prop :=
  MonoSquare ws T i j false (rowValues ws (mrow p s 0)) (mrows p s false) ∧
  MonoSquare ws T i j true (rowValues ws (mrow p s 3)) (mrows p s true)

instance {ws T i j p s} : Decidable (monoEdge ws T i j p s) := by unfold monoEdge; infer_instance

def valid (w : Sig) (ws : List Sig) (T : Sig) (cap pos mono : Nat) : Prop :=
  (w::ws).Nodup ∧
    shape pos (2+cap-(ws.length+1)-1) (fun i j s => Packed.edgeOK (w::ws) T i j pos s) ∧
    shape mono (2+cap-(ws.length+1)) (fun i j s => monoEdge (w::ws) T i j mono s)

instance {w ws T cap pos mono} : Decidable (valid w ws T cap pos mono) := by
  unfold valid; infer_instance

theorem sound {w ws T cap pos mono} (ok : valid w ws T cap pos mono) {k t : Nat}
    (hk : k ≤ cap) : ¬Live T k t (w::ws).toFinset := by
  intro run
  obtain ⟨nd,hp,hm⟩ := ok
  cases t with
  | zero =>
    obtain ⟨c,proper⟩ := colorsOfMonoLive nd run
    apply excludes hm (by simp; omega) c
    intro i j s e
    exact proper i j ⟨_,_,_,_,e.1,e.2⟩
  | succ t =>
    obtain ⟨c,proper⟩ := colorsOfLive nd run
    apply excludes hp (by simp; omega) c
    intro i j s e
    exact proper i j (Packed.edgeOK_sound e)

end SplitCut


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
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def vars (m : Nat) :=
  let raw := (selected m).map Prod.snd
  if m.testBit 11 then raw ++ [vertex m 0 ||| vertex m 3] else raw
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


-- The low nine bits select vertices. A set bit at position eleven supplies
-- the disjunction of the two surviving endpoints as an additional input.
def poolMask (m : Nat) (c : ColumnInfo) :=
  if m.testBit 11 && !c.2.2.1.testBit 11 then m % 512 else m

def poolColumn (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) :=
  if m.testBit 11 && !c.2.2.1.testBit 11 then
    (chartGoal (m % 512) == chartGoal m) && colCheck (m % 512) c prior
  else colCheck m c prior

theorem poolColumn_sound {m} (c : ColumnInfo) (prior : Nat → Nat)
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : poolColumn m c prior = true) :
    Slice (vars (poolMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  unfold poolColumn at ok
  unfold poolMask
  split <;> rename_i tag
  · rw [if_pos tag] at ok
    obtain ⟨same,check⟩ := Bool.and_eq_true_iff.mp ok
    rw [←beq_iff_eq.mp same]
    exact col_sound c prior low check
  · rw [if_neg tag] at ok
    exact col_sound c prior low ok

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


abbrev Bits := BitVec 144
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 144 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 144 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 144 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 144 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 144 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 144 → Row) (d : Bool) (a b : Sig) :
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

def asRow (cols : Nat → Bits) (i : Fin 144) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 144) (j : Fin 9) :
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
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 144) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 144) :
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

def closeChild (pools : List BoundPool) (links : List Sig → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  pools.any (fun p => scalarPoolCut p k rest op) || (links ws).any (sameWords ws)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · rw [sameWords_sound ok]
    exact lValid _ _ hx

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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (List Sig → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 144 then true else
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
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 144 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 144) = false := by simp [sep]
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
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 144) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 144) (hq : chartSamples m q = 0) :
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
  let (_,depth,_,_,pw,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := if pw=249 then data (4*i) else stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (if pw=249 then data (4*i+1) else recp >>> len) bank)

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
    materialize (vars (poolMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars (poolMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    exact materialize_sound (raw:=vars (poolMask g.mask ci)) (cols ci (g.cols.read_mem e)) h

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

def conflictRows (i : Nat) : Nat := (if i<2 then (if i<1 then 0x52280a8500a040d868160a0a8500a04a1d06070121110040429948a254018080204f038380c09108a0402d52ab148a9108a0402d42a310889108a0402b098682419108a0402948a612099108a04029d8ea64328582a04029d0ea64328502a0402d24930904510890402528950a05510890402568b5542a420110402f0701c0c0914084402d5629548a91408440294c24520991408440286c241a09914084402da6526914512084402d2612490451208440272b14ca4551208440252a144a055120844028cc2623010d02824020e8342a050d0282402aad50aa548540814029acd06a348540814029d4c8743285408140296490582485408140292c904a248540814028cc4613010d04814020e8541a050d048140292c904a2484408100254aa05228422080802b118a4422a09060201a512a140aa090602018e8762b14848260201a69368a45848260201a613288448482602019c0e26030848260201751a9d068428150201570b9542a428150201560b15028428150201530994422428150201b1488c422a0c048201a5428940aa0c048201a341a8b0521008820166b1594c1068141401a6d149a4584c04120196490582484c041201934904c2484c041201c7e171781068141201c6e1713810681412010f0583412068141201763a0d86842a040a01562a0582842a040a01532884c2242a040a01c7e270b81078240a01c6e270b81068240a018742a0d02068240a011f0e86c32068240a010f0682c12068240a01271349449030140401e532b148aa01020000b118a4422a01020000a512a140aa01020000f038380c0900820000d42a31088900820000b09868241900820000a61328844840220000960b24824840220000d24930904500810000729958a45500810000528950a05500810000508850a05500810000761b1d0684201100005b0d96432420110000560b15028420110000530994422420110000b94c8e432a04008000b1488c422a04008000a5428940aa04008000e1e0f8381210088000ab45aa914210088000a3c1e8b05210088000a341a8b05210088000a341a8904210088000a1c0e8301210088000f0701c0c090400400094c245209904004000da6526914502004000d2612490450200400058a45609010804400051a0d44821080440000e8342a050c02020000d82c340a088042000ac540b05084400100096490582484400100092c904a248440010000e8541a050c04010004e2513090060101000562a0582842200080054aa05228422000800532884c224220008004e2612890060200800e1f070781211000400ab5522d14211000400a35120d04211000400a1d0607012110004006331184c003010040043a15068103010040027130944803010040007834160903010040029948a2500180802000b8582a14018080200 else 0x1613010480773b1d4e84321104806733194c843211048047a351689432110480d1e8b078250a8102807cbe1d2e848a4102804da69168a48a4102804ba592a9441a0902805d2c93492329908a44468350a05651258241abc5eab15390c8e030a1c0e8301390c8e0308f46a2d121e0e06830c66232990160a068306b351a4d01b0d064303f1f0f4781b0d06430371b0d4681b0d064300783416091b0d06430a1c0e8301350a8d028a3c1e8b0531088c020a341a890431088c020a1c0e830131088c0200e8342a051c0a060200d82c340a0880460201f0d874321609050201f0e86c32160a048200f0682c12160a04820371a8d8681308848200f0682c12060204820a3d160f053118044206331184c0130904420371b0d4681309044200783416091309044200e8541a050c0c010200783416090309004200b8582a340180802205da6d749a1c8647018a9d4627112d1603418bd9e4f4788d8643418ddaeb369a1c8e032183d9e8f2780d8683218b89c6a2519a0d22814b29968a459a0d22814b94c8e432aa450a81451a0d64921281468149d4ca35121a8d02a14f83c3a0d0990ca2412d52ab148a990ca2412948a61209990ca24129acd06a348d4483412ae976aa558c8662211ad468b41aa8c44a211b91ca6432a81422010ad16a341aa81422010f83c3a0d0980c22010dc2e33098980c22010d42a31088980c22010da4d32914580c12010a5428940aa8440a010ab45aa91429048a0109e4d078348c4403010562a058284a2402810ab5522d142914024106b351a4d00b0502410964d05834844401010138d84a3401848021052a144a0555228540a71309c0c0058285009d24930904540a11008528950a05540a11008a1c0e8301250289008d2612490454220500852a144a055422050089ac56691414824500891c0e45021482450081180e450214824500858a45609014824500855a2d548a14824500851a0d448214824500851a0d548a108045008e2f070b81251201408a3d160f05251201408a1d060701251201408b49a4d468848241408359a4d468058241408d5aab168a148a01208d4aab128a148a0120855aa9168a148a01208522890882148a01208522810880148a012088bc5a2b14058281208359a8d26805828120831988c2600582812080b8582a14058281208319a8c268018280208a5428940aa2c148a05b118a4422a211208047138184c0920920804d52ab148a920920804d42a31088920920804b29968a45920920804b09868241920920804948a61209920920804e5629948aa24108804a1c0e8b05210088804b2d14ca459241048049ac56691412814480491c0e450212814480455a2d548a12814480451a0d448212814480451a0d44821080448049acd22b14128900a0498cc22310128900a045d2c93492128900a041c8e) else (if i<3 then 0x408300230188402a241083000e8541a050c44011000783416090341005000d868160a08c4003000b8582b140180803004ea352a856c321a0c07cba5f0e868b05a0c04da2d348a68b05a0c04da69168a68b4182c04ea352a855c2a160a04ea551a855c2c150a0c3e1b07825629150a05f2d974b25629150a05fae96cb256aa148a05f2e96cb2562a148a0773a9d8e85328948a0e37130d847138144a04dae916aa48ac102a0dd6cb35925aad12a94daed16ab4cd6493492f8bc7a2d1d82c32090dcae73299d82c32090d4aa71289d82c32090f96c9e4b2e8641a090e5629948ae8641a090d9e4f659258a4560904fa6d3a994b2492890eb7532d946934124907dbe9f2f849a492290e1e0f8381652299088dae57699454a255088d9e4f659254a255088d8e47619054a255088d361b458254a255088d1e0f458254a255088e3f170f85653211488e1f07078165321148875ba5d4e845a251488d329b48a4c5229128877ba9dae845a29128875ba9d2e845a29128853a994aa445a291288359a8d26845a291288f2b978ac5d22930884d4aa71289d22930884e5629948ae26118884d5e0f4582562154884dae57699452a154884d1e0f458252a154884daed32b9452a910a845cae152a84aa510a844da69168a4aa510a84f0b8782c1d128b0482d4aa71289d128b048256aa51a89d128b0482ddaeb64b2c5a2b0482dd2eb64b2c522b0482d4e255289d16094482d8e47659250a0544824ea352a854d22924824ea352a854c2212482dd6c974b2c560914824ea551a854d2491482dc6c970b2c460910825cae152a848a4902824da69168a48a490282f138b44a2e0b070281e532b148ae0b070281e6b378ac5c4a270281e5629948ae0e058281e4e278381e42258281d361b4582562155081e6f159ac5c4e051281e671198c4c4e051281d669158a4c4e0512815f2d974b246a15128147a191682462151081c762b0d8246a250a815f2e96cb246a250a81f138b44a2e03030080f2b978ac5d02830080f0b8782c1d02830080d4aa71289d02830080e633388c4c42230080d62b348a4c42230080f96c9e4b2e06018080f1689c4a2e06018080e5629948ae06018080e361b8984612098080e5e2f8381612098080e1e0f8381612098080d8e47619050a054080d1e0f458250a054080cce2723814c22120806eb35aac54c22120804ea352a854c22120805caa570a848a0520804da2d348a48a0520804721d188545a091280ec741b0d0c46011080d669158a4c460110804ea551a854c2411080c3e1b07824621110805f2d974b24621110804f2593492462111080c762b0d824622108804f2692c92462210880773a9d8e843209088075ba9d2e84320908806732998c843209088047a2d1a89432090880eb7532d94613010480e37130d84613010480e1f07078 else 0x5caa570a8c8e0721806732998c8c360b0980773b1d4e8c36130580cbe5b2b94c1e0b038075ba9d2e8c1e0b03804ba592a94c1e0b0380472191884c1e0b03800783416098b45225100d82c340a8ac1629048c06210088ac520b040e8342a050d02a25025c0e1502848c430100530994422c24130100711894422e010701000e03030080ac1221000d82c340a88c0621000e8342b040c02221000d82c340a088062100562a05828c2602090054aa05228c26020900532884c22c260209000782c1a098340a09000f0682c12060220900c6e171381834120500c3e170781834120500371b0d4688341205000783416098341205008bc5a2b1481c0a0300138984a2481c0a03000b8582a1481c0a03002d068940aa84))
def invertedRows (i : Nat) : Nat := 0x323d060f0305a0c0e8155a044e2f038844e22092012480452005424130980c20150804c20110864b0990c24130954a37428550a140a8510a04128102a049269249858245029142a31148bc2a1b0886522190a8641219048440a1008844520d048340a0c90422210882420110868311209854211408402211906024180905a22138a04620111a044281109044140d048340a0d12030140c048300a0c02030140b0482c0a078101848061101814060281808060101a04038080c54030500c04030080c0000
def recoverEdges (count codes : Nat) : Nat :=
  match count with
  | 0 => 0
  | n+1 => packedAt conflictRows ((codes % 512)*72) 72 ||| (recoverEdges n (codes >>> 9) <<< 72)
def unpackShape (cycle m n tag : Nat) :=
  let inv := tag % 128
  let pins : Nat := 0
  let codes := tag >>> 7
  (if inv=0 then 0 else 1) ||| (cycle <<< 1) ||| (m <<< 2) |||
    (packedAt invertedRows (inv*18) 18 <<< 6) ||| (pins <<< 24) |||
    (recoverEdges n codes <<< (24+4*m))
def colorShape0v1 (i : Nat) : Nat := 0x0
def colorShape0v2 (i : Nat) : Nat := 0x9d56a2d5a2d474d37a528ed17d50874f26ce0dce0e4d47cc1f4b1f4a1f4918c94b480e473cc679c597c482c4b943a7438843734181c0193e1f3d7dbb97baa2b997b876378bb67a3570b484b3883215b01c2f7d2eb82d9bad81ada6abae2a1faa26a91f28442758a655261f251f2414a326a21f2009a05f9e0e1d4e9b0e9b269a2d9926982697189664154e9524153d9415930e13679233124f102790330f188f268e0e0d268c0e0b0f0a4b094e861f064b8550046403268341813f813c81b580b380b000af009000810069806880678067006680650054004c804600440041803f803a0036002d002b8026801c001580120011000980
def colorShape0v3 (i : Nat) : Nat := 0x20b2e7e4f091d0ff25d96d73b70622856be10f273ac291d060a8a28b15a96d1908692d44eb19d2a9d0fc40aa74180f081d0fc0ddd70b900a3cb6dc024d0da480a0d0a8002391e91805eae9780164b656802c1d15a0120824680339b0e800d08e39802c9c8d800f27a2c80300e09a00b2db1800
def colorShape0v4 (i : Nat) : Nat := 0x166b45544954b29c
def colorShape1v5 (i : Nat) : Nat := 0xaed4ec550a94c210c838051c4986449f8e28342a23fa0148a2bf63b0998c060bc78415f8e075378ac0a35148c327840a35137ab293ca6652c98b1108c0ea6e37af7e8c12d2a71ae86445f4e083ad6fc6e211679ab562fd76be582651abdb0d56b22210c99cc41c222b8c99ec51b221da792c880221228b92c8848a05c2e56ea2529f499145c9b251a55a591091229a17a510a91229a180540207111a208c488341a993fa591092421717a591091109205a7d2c880112231a92a8848911c108d29b24083318c5a0e0588422e5348649074f25910031d86361708e3821031d8a4324d1f032113c37591c03181e2ac07110315858000505831d194c24d1f021c10968a124811c10502a124811c108d85d13811c108d85f13011c108fe5e12011c1096a5c12011c108601712011da792c88b6001a952c958ad80af8a52b58ad800503c2757ad00b08a4ef56ad001a94ec889ac80854a24b21a780864a24943a58085ca24b22a580a55cee171a300a553656e1a3009ecfe77389c809e4fa6b2c980087cfa692c980087c7e652c98008bc0a654c8c80813e1b930878086445f8e1838086445f4e0838086415f8e28300824cdd0e47f0078c124add7b807840df2de7b006fc6e21167980723fa02ed74807fc0a692c72807fc0a4b2b72807f4126d2c720075bbde76f7100753bde72c700053ab9b2d46b801da792c88698064018424b6580208c5a0c464802b0c59cc464806321058cb6400068a52c885200532792c87520044244426c4a80422e53486490054ab52c884880229fcf28848801906d1e8c3100209f4f2712d002b9b0ec702d0049888601825001c900fc1725001c108d8a1248035a591091230059a84923821003e85c8e38210040270903820801d8ac344d1f00060a0344d1f001e0a8344c1f0005994c4671e80210c8395b1c002113d3ad31c00211419cc31c00210c83ea41c002113c38051c002113c36051c00210cc40031c002113d3ad21b800b928704218001825910911100181e2ac0711003fa5510911080089fcee700a003e1fd2c880480118c12c8804006503c27570280058a52c880280058ac2c010280
def colorShape1v7 (i : Nat) : Nat := 0x9e2236a62a3692101
def colorShape1v9 (i : Nat) : Nat := 0x128281e130081844300b80
def cutCode (id : Nat) : Nat :=
  if id<1 then unpackShape 0 1 0 (packedAt colorShape0v1 ((id-0)*7) 7) else
  if id<124 then unpackShape 0 2 1 (packedAt colorShape0v2 ((id-1)*16) 16) else
  if id<151 then unpackShape 0 3 3 (packedAt colorShape0v3 ((id-124)*34) 34) else
  if id<152 then unpackShape 0 4 6 (packedAt colorShape0v4 ((id-151)*61) 61) else
  if id<272 then unpackShape 1 5 5 (packedAt colorShape1v5 ((id-152)*52) 52) else
  if id<273 then unpackShape 1 7 7 (packedAt colorShape1v7 ((id-272)*70) 70) else
  if id<274 then unpackShape 1 9 9 (packedAt colorShape1v9 ((id-273)*88) 88) else
  0
def monoRows (i : Nat) : Nat := (if i<3 then (if i<1 then 0x140188044061805004641110860500118044061a0500460110186014010a04442381400424110186014010904442181400420110186814010804406180500420110c00c143200844300d0504802110c00c1412008443021140400211018682405140342d0889050140d422830405050350811c8090120d0300e0424048350909c0814120d424230205048343011090a00a0d0c044240a028361285c08240a0d84a130209028361084c08240a0d0d01a2409028343406190240a0d0b0606414140300c1819014500c03060640414030301609028280c0c25120080a0300c1889014140c030606405050300c1809014140c030602404050310818c8014100c4242302050403108a0c0014100c420612405040310908c0810100c420612004040303406190a00a0c0c0186428028303406090a00a0c0c0182428028303006890280a0c0c211200a028303006090280a0c846130209028321084c08240a0c0c2112009028303084c80200a0c846130208028321284c08200a0c842130208028303006890200a0c1c0986408028303406190200a0c0c0186408028303006190a0080c0c018640a02030300609028080c846170208020321285c0820080c84213020802030841838408120b01a13020a8201908426009204064200f020581019084260016040642109820481018848464c0848062121181021201818423401444064200f02041101818423401044064200f03040501908426001414060600c12050501908426401014064200d020405018184234010140606108900405018180304810140621030d022028188484608080a0601830120202818848460c08080625030d02202018840c240280806210b0d00202018840c3400808064200f030401019084260814040616188d00501018584234014040606108d005010181803048140406c280f0204010190842608100406421098004010190a034081004064200d020401018184a34010040616108d0040101818423401004060600c12040101884112840a02030b04628128080c0c118a02a020321084d00a8080c84112802a020303044680a8080c22160a01424030881a29010500cc24234104140310908d0010500c9421340480a0303046280a0280c8411380280a0321084d00a0280c8411280280a0303044680a0280c0c110a0280a0325084d0020280c8421340080a030304428020280c22060a014040330908d0010100c84183a408020321044a9020080c0c110a408020325084d0120080c2c211a048020303046280a0080c841138028020321184d00a0080cc42134028020325084d00a0080c842134028020303054680a0080c0c111a028020303044280a0080cc42134008020325084d0020080c842134008020321034d0020080cc4213000802030308448020080c0c110a0080203 else (if i<2 then 0x110a8103809000442a000e02400110826b04d064743d09c6224151d0f4271889054703d8c25322190a8f4220c028c8503809ae934151a0d56094490e02a3509ac134151c0c426b24d044703149ac134111c0c426b04d044703109ac13411190c426b049044643109ae93411180c426b84d044603109ac93411180c426b04d044603109ac92411180c426b0490446031582512438088c5601bc90d02231582512432088c508a0c1014502d0c2832409120b430a048024482d0c4822805120b54108c0814122d420612424140b00c1a09090502c01a811409150a54084410a01229900462824048a54018490901229502110428828954084410a80a2551019042a028954084c10a00a25502111428028954084400a00a259204628240289640118a0900a255021304288088406b0c9404602101aa114011808406a0c1404502101a8915011408406a045404502101a8114051408422a0c8004502181c8204011408406aa45004502101aa114011408406a245004502141a8114011408406a045004502101a8904011408406a041004502108a812101120843120190a0482108a8120051208406a0c1004482108c9228011208406a045004482101aa114011108406a045004442101a8104011108406aa45004402101aa114011008406a045004402101a810401100854084410a00a21980462834008855003450c802215000d142a008854084410a802219041a042800885410b450a0022150211142800885500d450a002215000d1428008854084410a002215004720240088640118a09002215006124240088540184809002215400d14220088540034508802215000d042200884271889054701d0bc6224150d0763294c88642a1d0b04e24340c0723016890682a1c8c25320180a072301689060281c088340b1205068220d028c8141a0a8300a320506a230880848141a08c220212050681811028206018840460208090601811028202018088300b1404060220c02c48101808c22031004060220c02c401018088340a3204060220c028c01018088300a14040602308808481018088340a1204060220c02848101808c22021004060220c0284010180e148b1140d058a41d3c0c8281625030d0320a058a4946804828164280f03140905928526885424160e04c32150905b2813c885024164a149a0140905928134885024160e148f01409058184a3405024160e148b0140905838130c85024160600c121409058061a050146815290c4e01a8884ce2523c0443413290c4f01a0a84c2c311a0682a130b0c468120a84c2c1c1a4482213390c4f01a0884ca4313c0682213290c4e01a0884c2c311a0682213290f4f0120884ca4313c048221329074f0120884c2c351a04822130b0c468120884c421814006281101860140189044061a0500620110186 else 0x313086c92210a8c4d219648842a313086592210a8c4d219248842a313086492210a8c4c21964a842231348649221088c4c219248842231229a68205148b712e1e98244a2d06cc64a09888661285d1825221918c274215448646329d08451219068c44a090a8641a35138242219848d74209088661231908242219068c44a0908864620d92c44121918c26431104864630992854121918c26421504864620d12854121918c27421104864632990844121918c264211048646a0d128441219188344a11048661285d08240a19848d74209028654084508a02a1418a81501104840328044044121098a03401100840328054044021058a014011008406a8050044021018a0140110084132804404402100ca011011008450084518202211400611608088450018458002211400615228088450084508a02211400611228088450018548802211406134208088450084548202211402914208088450084508202211440611208088450018448202211400615204088450030508102211404c34200088455018548002211400615200088450034508002211400c14200088451018448002211400611200088461245a182c2a0d0c914a60b028343245288ac0a0d84a174229928343245e88a60a0d0c914a229828350b09d1814520d42c274305148350b09d0814520d8491682290a8343245288a42a0d0c914a2090a8368a1b29814120d0c914a609028365285d0a240a0d84a17428902835324568a240a0da49168249028343285689240a0d2c914a249028343247288a40a0d84a174229028361235d08a40a0d0c915a229028343681488a40a0d0c914a229028321084d08a40a0d0d91ca209028343247288240a0d94a174209028361285d08240a0d0c914a2090283a805a2870191c960134d1e0a271a000e02681118a8006829804462a041a08601118a8203809804462a000e02601118806a045124d061502110468209854003411a082610b54228123a1482d508a048a8520b54228122814aa2138a9502452a805a28540914aa013889442452a824f22500914aa0168a9402452a845a28500914aa8168a1402452a805a28500914aa013889402452424230245249321084c09248a4ca041a08480512a820380920144aa000e0248051280d40820089242424230244241080d40820088842035020a02209080d4082008824201d020202209080d408280880420351208022010a0d408200880420350208022010807418080880428550202022010a074080808804201d0202022010a8108809900442a001a08600110a8084c09200442a080e02480110a8108809140442a080e0a440110a8006821100442a042202440110a8006829040442a000e02410110a8083c09000442a041a0a400110a8006829000442a000e0a400110a8806821000442a001a084)) else (if i<4 then 0x84820a914aa92212082a452a84284028a914aa48e832089552a52286ca2a148a94c21b24a8522a74086c12a112a9d026320a444aa44285028a110a8428840a88142a1588344a9144a6436830485542952286492a948a548e832085522974086c12a90aa59221208224128a40848208904a210a140a224128842840288904a241e8324815828523b0c820560a1c8e8320815528523a0c820554a141e8304815528523a0c820550a14368304815428507a0c120550a148a1b28a8522853086c92a148a148e8328815228507a0c120548a141e8304815128523a0c820540a141e830481502876091c92c902a1d021b04a840a874091ca29102a1d024720a440a8640848208304a0902120820c028240848208114a0902120a204128240848208104a0902120a2040a8042840288102a09061208204028248848208100a0902120820402804a840288100a010a100a204028109208260840a0420340b8010281080c02e0040a0424820a811028109248220040a0c248208801028109208220040a04b66324955c2773296c92652a9dcc25b24984a271169140a29a09a48a310b9245269228c42ac9149ac8e23029245269228d42a49149a48a310a9245269189142a232098462450a884a2631091c0a212498462450a88492631191c0a212098c42470288482611a9142a212098462450a8848261228c42e49109848a310ab244261228c42ac1109848e23029244261228c42a49109848e23029044261228d42a41109848a310a904426118ca742516496692f5f0924a259a49d7c24928964eb49b2954925938d26c251249646b4992944925938934ca5124965805c64920aa542cb0190512494062a05414492503ab01c05120940e2c07014482502cb0190512094580c464920a25160161924828945d05874900a251601c1c24028945905864900a251601619240289458a5969914d24d62d27c345349358b49f0914d24da4b17c26922934b6c1689a48a4ca4313c26922936d2c5f09248a4da4b17c2492293692c5e09248a4d2cb15a249229341a611481c9245069a45207209145a69148168245069855205649141a6114815924506b855205609141a61548158245429854205609141a69148158245069845205609141a61148149245429854205209141a6914814824506984520520914c20d159240a4530a15564102914c285519040a4530a15425102914c285509240a4530834524902914c2a5549040a4530a15424102914c20d149040a4523a0c8215688d4b24d24b4542352da0c9215508d48a1924895223523a0c9215488dc4a5b24894a2350c83c1291128d43683048544a353091492a10a8d4c245248a42a353086492250a8d4c25964a84a2310da0c1215108c432616485442310c9849211108c4c21964a842a313086492290a8c4d21b248842a else (if i<5 then 0x892092410d04822482491450a4508a052212d008a2082481414064082052050501802880c814108440a2032010c20122280c81414060882032010c20122080c814140640a20120505018228804814108440a2012010c20122880481414060892012050501802080481450845082012050421142080481410944882012054421102080481410844082012010c20922080480434120882012010c2012208048210a044400512010908d02411482804220c104120a021183021048280a060c0441208428111011048280a0604004120842a1110010482102124c004120980c469120cc66a01d2ac4433190ed40aa1888c607b502a86221180ed40aa18884603b301a0622118a8070e9101c462a01c2ac403518a8070ab110c462601c1a4403118ca04f231489458061a05406211108d00a8098142c432012026050b0d480640a814280c2c1240a030a21500800a80c2a401a19408150a06d008a0980c2680112a408130990084490204c26820d22c041309a00348b0104c26880c22c04130992084490004c24315028022210806cc06808884203130180222108265008a0880c201b40228220308065008a0880c2019402202203080c480640880c20312018022030816480480880c2019201202203080c500a008804201941228220108065008a08804224021124081308a00308b0104c22401819404130890060610104c2260111a44811089806061100442280113a4081108a0044a9020442240111a408110890084490204422804c22c041108a00348b0104422880c22c041108a00308b0104422800c224041108a08308b0004422400c124001108c240f03048141b0803c0c12050621084d10280c0c85402002a03035b7472ab2783c96dd0ca2c9e0f2e8a4f22d84d3692dd1caa49a2d24b74328926834927d1c8a49a0d2ea25b2ad04934ba096ca34124d2e8a4f22d04934ba093c8b4124d2e0a0f02c8453290dc0c2209c0c2437030982623090dc0c220988c2437030a8260b0907c1c0a2980c2c370308826030b8283c0b2104c2e020f0ac44130b8086c231104c2e062302c44130b8086c2b0504c2e062b0ac04130b8086c2b0104c2e020f0ac04130b8086c230104c2e021b02c04130b8283c0b0104c2e020f02c0413092db0c925570bdccadb24b85a2f261948a0e934ba1aa502a3a4d2e922ac42ac150b85e3c9f0b4592d958f2742d164b618a502a324d2ca61948a0c924b29a2522832492c862940a8c924b249ec324955c2c527b0c924570b149ec32491582c44294828c320b0982522830492c260948a8c122b0982562a30482c260948a0c120b018a502a30482c129308a24060b04a0c42a90182c10da0c121554ad4c21964aa522b523a0ca21548adc4adb24a85a2b10da0c122550ac4c21924a8522b131a0c822548ac5c299648942ab241 else 0xd834965956a751e5995d3c323d16966574d1c8f45a5984d34723d1d8349659168f4730da4d645a3d17962554f0c8741a4934d3c321d06966134d0c8741a5894534321d0cc349359068f4360d259641a1d0cd34935906874330d24d641a1d06120d14e0c0f0710ca4560583c16168144e0c070185a05530301c06168144c0c070185884530301c0c430955807070340c25160189c0d030955806070340c25160181c0c530915806070310c24560181c058e6132b4ca6d163984cae321b058f51aab0c86c17bd06aac321b058f41aab0c86c163d068ac321b058e6532b0c86c163984cac321b050e2112b0c86c310a144e4161b052f018aa0c1681438844aab01a050e2112a8c068143c060a9301a052f018aa0c068143c060a8301a050e2512a0c0681538844a8301a050e2112a0c068380c260e0555a058a7169914d66d38b15a26b2399e8af1e9915c667a29d6ae4533994ef41aa98c8663a29c6ae413198d827169904c661741e1d64229945905865908a651069a4560721914c2855590c0e4571c47a227058b48f01e089c162d43a052227058be030981854562ba0ac7a6415189d8235699044e278091786091389d0285498244e27828d62e051389d0231498144e2531b0582232188467018a89c0e2119c062a230388466814888c0e2119c0722a30188466814888c0623808c62e051388d0231498144e2340a1526091188e03098981446234098596051188d0231498144623828c62e011188e02318b8044623808c626011188d0261618044623408c52601118841a311382c2e1942c2742930586062805104c061140211460a098455038558082611400611602098448e81608ac160d0c914a60b038361701808ac0e0d0da05222b03839814865142a552305a0d444a351294c0647488540a5181d1c2215098148751028d4230520d440a350981c8651028542645219440a1509814865102854230520d440a15021480444482510850a05112094491108450422512104205410894421488444180d06406211404834184128150120d04850805192014021480444980500852211106014021480444180500852211102014021480444080500850a05102014021420144080500850305102014090108450030502404215400914084108150020d0240421540081409018845002050240421140081408412815002050214420540081408410815002050063190c8d22934594693432894c96150680e2233058541a23088cc161184c0c2233018c60323088cc16150688e22130584613038884c063180c8e2213058541a234884c063502a8ca213058541a030884c161184c0c22130544211030884c04341208c2213018c603230884c04308048c221308c2c13110184c210b0444406130842a11110184c1414060092092412d108a24824904b4022)))
def monoInv (i : Nat) : Nat := 0x0
def recoverMonoEdges (count codes : Nat) : Nat :=
  match count with
  | 0 => 0
  | n+1 => packedAt monoRows ((codes % 1024)*54) 54 ||| (recoverMonoEdges n (codes >>> 10) <<< 54)
def unpackMonoShape (cycle m n tag : Nat) :=
  let inv := tag % 1
  let pins := (tag >>> 0) % (1 <<< (4*m))
  let codes := tag >>> (0+4*m)
  (if inv=0 then 0 else 1) ||| (cycle <<< 1) ||| (m <<< 2) |||
    (packedAt monoInv (inv*18) 18 <<< 6) ||| (pins <<< 24) |||
    (recoverMonoEdges n codes <<< (24+4*m))
def monoShape0v2 (i : Nat) : Nat := 0x34448d38a22f86d7c97498390c4c5172d798b39426f0c97f3296849b291a36075371571c754619bd448e5179105b8416e0c5f7216f0857b211348421210588580907e201848052a033870a31c28c6043d8354509bd408e406f481f9106f441bb10604404d10090402210
def monoShape0v3 (i : Nat) : Nat := 0xb7135c5daa2a14eb195a8456dba9d0a2a536ae04a7a8d3ec6525d924264f297cd8e18c4a5d9538a2f197664df8bc65d933722d197d8284df161f41a177b48745a2c67145c878ad94517aa8e5bf8e5aae36ae8396a990db9ce599339a3419664cdf8cc65b428eb6438669cde9586199340e371866595f8bc6199443a2f1866450a8bc6199d3762f18664cdc8b421b51a0f7b37652d374f0c5aa7366f1695aa10cbc8e56a7412f329564cdc8bda16bd362f5385b04dbba0a159c42238185661078d86158841a2e18564cdc8b46159337e3308564cdc8b42159937e2f975d3639d989d5ff45e6a1756210b8d05d6599625713590a3b8e8496c2416f618464cdc8b4212d5463032747f9269b45d1fe46669164d4b668e58522a1c1a06839425294454ddd73e1a153442c60ed50e6298261523b26f6415c0e2a1c19f57222c8231c5491244d14542771d08685088b208c71422308131c10a6699265512745d475544b1ab1541971c5a9a5025c77bcc6898714a52c4acd05d8759d7421889ed6f90877dcc28e760dfd6fa29d43867d695650ccf30cc9cc0d1290b6320214120f8c41d25e9b721021854138840850503e210
def monoShape0v4 (i : Nat) : Nat := 0xb76c83cae8380db7814
def monoShape1v5 (i : Nat) : Nat := (if i<1 then 0xeacbbcec234c895043cef618f5d985e1410f3dda2487821c75043a8b245143117ea048d89930f802831a8123cd65e3e80aa725c48ebfc65430b47f97123aaf194fc5018e5c48d908b4ef01c4297123626303d4040d25c48d89938ff02831971236265c3a8050c65c48d8d974fa0282b971236223239c010da5848f579d124288b2861237ee73490a22c61848d888dd000102f86123d6785a560888dd848dc2841e55a5af4612373a0e789686ad1848dc0875e35a1aa4612317528248060dd1848c6a3248f0002f461237ee75474a02c61448f589e91f26ecb75123b3f2c56cad339d448dfb9c924288b1751237f67949c9c2b1d448f5ce2e9682624651237060f7896a6e51448dbf835e95e5ad4512373a1e78d6a6ad1448dc7885ee5cdaa451237162079d706a91448dc387f565b1aa451231f4cd2600f0c51448c5c32caa02431451231f0cc250080c51448c582ec8e0642e45123d0f7ba2db16fe1c08c692ec8e0002f46023849e65c1ac7110408cd0b37019a204496821e2a9bfe5580d25a08d0b3b0299e00374626462fb62b51d25e9098a8bed8adc7197a4264632b66b41d65a909918b6deabc76869421b45308c8a3184c1098a8cedaadc7196a322dd4ec7ebc1ec5e4ca80dd34772db589432304960284f1fd24049888bcf602838a8012622333d80a0e29c04abfc65461407f97012aff19524381fe5c0498c8b4f602848970126222f3d80a0e25c049888bcf607431970126462f3f41d0b25c04b4bdee8b6c5bf8701262a2d3d80a14a58049888d4fd07435960127ea6a4809e2ce180499b8bcf60284b860126222f5800d0be18049918d0fd0742c860122fc9301c4315518048552fc9301c424601270a10795696bcd80486b2f8910104c360127ea6c484a22d214049fe9b52529caf850126422d3b80711614049fc9a51c2a4b9750127ea6a488a22d1d4049fa9b902040ab75012d4387a627698d9404b4fe129581dd365012198ba2381a0c51404a12799706b1c43501272611795696e8d4049c2841ec5e1b03501271a147bd726bcd4049c484deb5c9af350127220f7897d6b8d4049bf835e4619ac350126fe0d791856b0d4049bf835e2609ac350121acbe24404130d40485a2ec8e0984a3501217cc526828124d4048672e8900a03935012178c42640a0e0d4048662f8910603535012d778ca66779ed50049cd83de25da0c34012712127a1836ccd0049c3875ee5adaa340121e0bb238202b8d0048592e88e0704434012188c225c0f0e0d00485b3009509431340121a0c325c1f0b0d004a787a9779525f430121faa3b9e2668d25a04772e8900a4b5230518166bbeed034dd60c5fe9aafaaec88758314d713abc72101e58c684dd34772db8894314bf10ad86e0f228c8538c36b11cc3a8a321a0376d15ca6d1e0c8680de746729b567321 else (if i<2 then 0x8934f802831625a84a311b7cf603161a7128c42df3d80a4ba9c4a37ed863f5aa8f97128dd3638fd69a225c4a376d8e415ba7e971288bcf602838621a806310b9cec06d38a7018c42e73ac044d69c06310b98f80292da7018c42e73d80a4b69c06376d923e5f28797018ddb649056e9f65c0630dbb4e80792fa6018d96535c682de14419f77d21cc6e28486257c152228952ca90415ed24a89f54b2641057b44d42e152ca88415ec0c85420c080a8237a871950c3117ea04dd35c36b71bc3f8a327a871952032192a049ea1c65490e05fa8127cbafd478a556a5849f1fb7ce70094e96127dfb6b92974a3e1809f26c1d1c28552950278c0f6028316216405f26bf51c2995996017c9f01488a254a5805f1fbf1010454e96017c4ee93f01d4c65805f14ba4f60292d96017ddb648f97e9f61805f26c1d1c2995995017c36f13d80a4b65405e2f3cc2a1498b53017899a11febfb9e08e5ad6ae55163a2f94286b62c32118c8be50a1ad8b0c8462e2f94186244d7b5eb02e91e95b729c1f6a438342056d6e2582a92e008415891356d8ad4bc37a46244d5b62b52f49e91b6d9bdf0a4789350464db0dadc7110228c9935c4eaf1c840793264d70dacd110fde4c9aa4c754c0bd5097126ab71b5203817e5c49b88dce6f7c29775126e076c9c1f2a41d449ad8c79470555e97026c4edf3a00e4b61405b88db26f7ce9775016e036f9c5f2a41d405b82dba6f7c29075016ddb648f587a05d405b26c1d1c2855284016cfb618f9da8565c9969eb8ced22cc6a7165d33638f9da85a5c5973ed863f7721597165ceb618f9da8565c5949635ad9ad0c036a45264e3b7aaf308da51491392f9ae8ba36945ceb7aa2db16fe60517709f20ba4b8231045bef2d574a859a1809782db26f7c29274015cab04488a2549d005461a86e789f375b8a417ea1b9e266896e2905fa8af78a1a05b8a417ea1b9e266816e2933fd864177a1b97164cff61905de86e5c19340d863f7721997064cfb618f5d985e585533cda249d561886154cf36296ddb856185533ed863e76a1586154a7ae23b08d322581533dd9e477861c86054cf767919df87218152c4c613f1286ca8234a87195129d196a08d3348c4fba6e9d97234622303d0040be5c8d35ae2a9481a237623473a0e7896a6ad588d1c0875e35a9aa5623415ccab28050cd588d0562e88e0142b56234a8b255143117ea04d2a1c654313c64a81246264e3e00a0c6a0491fb9c91b26cb086124a871950c4f192a0091888bcf602831a80247ea694689b2c2180938ddc66f7c6936301417ea1bba296812de8c58a7ee3955a65a793182bebd62867969e4c5fa86eb8999e4a793cff61905de86e5814f40d863f7721a96053cff61905de86e1814f43d863f77215860530f54ec7eb01e4a290d8a8ced9ac87196a4362a2fb7aaf1ca1a50 else 0xbd0f802930c8dcc62af83ac044ef227318ab88f603162c81cc62ae73ac06597117318ab9cf603163c45cc62ae33e40b53f0f7318ab9cf603164c45c862ae73d80a4cf107218aad47a10535c34c862ae73c0134b7107508ab9ceb01135c41c822ae73d81d4bf107208ab9cfd0292dc41c822af13d80a4bf126208abb8f602936c418822ae7899a11febf7934ab9e266805fa85e48eb1951c47156a08723ad863d5a28fdf9d4a270c488a25532f63179c052228d67ca58c5e70b490a254f2863179c052228955c9d8c5e6e239c0253b1f62179b8ce90154dc3d885e6c7224034b70e32179ae0830f92dc34981e6e53f8274f71562079bacf602935c4d881e6e73dd6d4d31062079c252228953c9d481e6f03d80a4bf1352079bb0f602932c51841e6f13d80a4cb0d51079b862669150a91a08e6e4899a11febf681398bed8ac86e63de8ca71c5203817ead761298d0fd0742c645804a62f3d80a1199771029c36b71c4404dad0c659a8b4f10704475019dae4a5d28fdf9905e361911699f77563178d86405ea80dd9901e36192d75a037663078d86415ba80dd9841e361915a99ff7661078d96536a27fdd9841e361915729f77661078da6536da86dd9441e310adc7110136a7268d2a0d7963cda9141a306488a254f2b52068bf5237d157c9d481a30a488a254f2642068ba8f60292dc4d441a308470a155b2641068b4cd427558c98841a3009a20133ecc57238dfb618f568a3e5c4e3019a20234ad45713))
def monoShape1v9 (i : Nat) : Nat := 0x226694582ec8e05d39c7ee79245018a6
def monoCode (id : Nat) : Nat :=
  if id<47 then unpackMonoShape 0 2 1 (packedAt monoShape0v2 ((id-0)*18) 18) else
  if id<129 then unpackMonoShape 0 3 3 (packedAt monoShape0v3 ((id-47)*42) 42) else
  if id<130 then unpackMonoShape 0 4 6 (packedAt monoShape0v4 ((id-129)*76) 76) else
  if id<426 then unpackMonoShape 1 5 5 (packedAt monoShape1v5 ((id-130)*70) 70) else
  if id<427 then unpackMonoShape 1 9 9 (packedAt monoShape1v9 ((id-426)*126) 126) else
  0
def splitLookup (i : Nat) : Nat := (if i<1 then 0x2ae10a48428c109c04260109784252108e84238108c0422e108b042221088042181081041e21073041c6106f041ba106a841a8106904190105a0416610550415010528413c104e84138104d041321049841201047041041032840a6102384078101d840a40dd501b5206d401b4e06d301b4806d181b4206d001b3c06ce81b3806cd81b3406cc81b3006cb81b2c06ca81b2806c901b2206c801b1e06c681b1806c581b1406c481b1006c301b0a06c201b0606c081afe06bf01afa06be01af606bd01af206bc01aee06bb01aea06ba01ae606b901ae206b801ade06b701ada06b601ad606b501ad006b381acc06b281ac806b081abc06ae81ab806ad81ab406ac81ab006ab01aaa06aa01aa606a901aa206a801a9e06a701a9a06a601a9606a501a9006a381a8a06a181a8406a081a80069f81a7c069e81a78069d81a74069c81a6e069b01a6a069a01a66069901a62069701a5a069601a56069501a52069401a4e069301a4a069201a46069101a42068f81a3c068e81a38068d81a34068c81a2c068a81a28068981a24068781a1c068681a18068581a14068481a10068381a0c068281a08068181a020680019fe067f019fa067e019f6067d019f2067c019ee067b019ea067a019e60679019e00677819dc0676819d60675019d20673819ca0670819c0066f819b8066d819b4066c819b0066b819ac066a819a60669019a206680199e06670199a06660199606648199006638198c066201986066101982065f8197c065e81978065d81974065c81970065b8196c06588196006570195a06560195606548194e065301948065181944065081940064f81938064d81932064b8192c064a8192806498192406488191e06470191a06460191606448191006438190c064281908064181900063f818fc063e818f8063d818f4063c818f0063b818ec063a818e80639018e20638018de0637018da0636018d40634818d00633018c80631818c40630818c0062f818bc062e818b8062d818b4062c818b0062b818ac062a818a206280189e06270189a06260189406248189006230188a06220188606210188206200187e061f0187a061d01872061c0186e061b0186a061a0186606190186206180185e06760158a0545014e60535814c8052a0149605d48134404cf8133a04c48130e04c1012d204b1812c404a501288049f01240048e812160479011e20476011d40474011ce0470811a4046501180045a8115c044d81132044c010f6043d010ee0436010ce0432012c001710052601860005c00168005800158005400148005000138004c001280048001180044001080040000f8003c000e80038000d80034000c80030000b8002c000a8002800098002400088002000078001c00068001800058001400048001000038000c00028000800018000400008000000 else 0x10280c705660157205564155785546154d8548a15d48434a10c98431810c0042ea10b0842be10ae84)

def insertWord (a : Sig) : List Sig → List Sig
  | [] => [a]
  | b::bs => if a.toNat ≤ b.toNat then a::b::bs else b::insertWord a bs

def sortedRep (ws : List Sig) (perm : List Nat) : List Sig :=
  ws.foldl (fun acc x => insertWord (movedWord (perm.map swapRows) x) acc) []

def wirePins (ws : List Sig) (p m : Nat) (cyclic : Bool) : Nat → Nat
  | 0 => 0
  | i+1 =>
    let edge := if cyclic then i else i-1
    let shift := 24+4*m+72*edge
    let row₀ := Fin.ofNat 512 (p >>> shift)
    let row₁ := Fin.ofNat 512 (p >>> (shift + if cyclic || i==0 then 18 else 9))
    let v := ws.findIdx (fun w => bit row₀ w != bit row₁ w)
    (v <<< (4*i)) ||| wirePins ws p m cyclic i

def derivedCut (ws : List Sig) (p : Nat) :=
  let m := (p >>> 2) % 16
  if m<2 then p else p ||| (wirePins ws p m ((p >>> 1) % 2 == 1) m <<< 24)


def leafRep (ws : List Sig) (perm : List Nat) (id : Nat) : List Sig :=
  if id < 274 then ws.map (movedWord (perm.map swapRows)) else sortedRep ws perm

def resolvedCut (ws : List Sig) (t : Sig) (cap id : Nat) : Bool :=
  if id < 274 then colorOk ws t cap (derivedCut ws (cutCode id))
  else match ws with
  | [] => false
  | w::tail =>
    let pair := packedAt splitLookup ((id-274)*18) 18
    decide (SplitCut.valid w tail t cap (derivedCut (w::tail) (cutCode (pair % 512))) (monoCode (pair >>> 9)))
theorem resolvedCut_sound {ws t cap id} (h : resolvedCut ws t cap id = true) {k u} (hk : k ≤ cap) :
    ¬Live t k u ws.toFinset := by
  unfold resolvedCut at h
  split at h
  · exact colorOk_sound h hk
  · cases ws with
    | nil => contradiction
    | cons w tail => exact SplitCut.sound (of_decide_eq_true h) hk

def extendedLink (g : Forest) (k : Nat) (ws : List Sig) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 < (g.levels k).1 ∨ !g.mask.testBit 11 then linkedSet g k pair else
    (g.autos[pair.2]?).bind fun perm =>
      let rep := leafRep ws perm (pair.1-(g.levels k).1)
      if resolvedCut rep (targetOf g) k (pair.1-(g.levels k).1)
      then some (rep.map (movedWord (perm.map swapRows).reverse)) else none

theorem extendedLink_sound (g : Forest) (k : Nat) (ws : List Sig)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : extendedLink g k ws pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold extendedLink at h
  split at h
  · exact linkedSet_sound g k names earlier h
  · obtain ⟨perm,hp,h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    next ok =>
      simp only [Option.some.injEq] at h
      subst out
      apply rotate_excluded _ _ (names _ (by simpa using Array.mem_of_getElem? hp))
      intro t u le
      exact resolvedCut_sound ok le
    · contradiction

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos (if g.mask.testBit 11 then 5+lw else 5)
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let pairs := if pw=249 then getPairs (fun _ => data (4*i+3)) cw depth (data (4*i+2)) 0 else getPairs data cw depth nr st
  let rules := pairs.filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k (keySet tag)).bind (extendedLink g (k-1) tag)).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars (poolMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
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
    have e : ((g.index k (keySet tag)).bind (extendedLink g (k-1) tag))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact extendedLink_sound g _ _ names (prior (by omega)) h


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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 144) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => poolColumn g.mask c prior) &&
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
      (fun x hx => poolColumn_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => poolColumn_sound _ prior lower (geometry.1.2 x hx)) geometry.2
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
def lanePlace (v : Nat) (upper : Nat) := 2^145*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^145 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<145 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<145 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<145 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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

def fullMarks (r packed : Nat) := ((packed+r) >>> 144) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (145*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^145)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 145*(i+1)-145=145*i := by omega
      have ge : ¬145*(i+1)<145 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 144 = (a==BitVec.allOnes 144) := by
  by_cases h : a=BitVec.allOnes 144
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^144-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^144 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (145*i) =
      (f xs[i]==BitVec.allOnes 144) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^145*u+x+(2^145*v+1)=2^145*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^145 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬145*(i+1)+144<145 := by omega
      have di : 145*(i+1)+144-145=145*i+144 := by omega
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
theorem top_xor (a : Bits) : BitVec.allOnes 144 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 144).toNat) op
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 145) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (145*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 145) (i:=i) (by simpa using hi) _ ok.2
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
    let z := packedOp (r*(BitVec.allOnes 144).toNat) op a b'
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
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 144 then true
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
        packedColumn d (packedOp (r*(BitVec.allOnes 144).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 144
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
  let nr := packedAt data pos (if g.mask.testBit 11 then 5+lw else 5)
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let pairs := if pw=249 then getPairs (fun _ => data (4*i+3)) cw depth (data (4*i+2)) 0 else getPairs data cw depth nr st
  let rules := pairs.filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k (keySet tag)).bind (extendedLink g (k-1) tag)).toList
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

theorem quickBlock {g : Forest} {k s n : Nat} (ar rows d : Nat)
    (h : cells g k s n ar rows d := by
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel) : block g k s n = true := cellsBlock h
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
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0x11,0x19),((~~~0x9),0x4),((~~~0x10),(~~~0x15)),(0x9,0x15),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def g31samples : Array (Bits × Bits) := #[(0x2ad2,0x18c2),(0x3a5,0x2305),(0x1876,0x72),((~~~0x2036),0x1e81),((~~~0x1ac0),(~~~0x1ec3)),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def g47samples : Array (Bits × Bits) := #[((~~~0x0),0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),(0x0,0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[((~~~0x0),0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),(0x0,0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[((~~~0x0),0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[((~~~0x6252),0x1c24),((~~~0x36ac),(~~~0x3ebe)),(0x36e2,0x24a2),(0x3e1c,0x5a1c),(0x0,0x0),(0x22fd,0x62d9),(0x421e,0x221e),(0x0,0x0),(0x0,0x0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[((~~~0x0),0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),(0x0,0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def g189samples : Array (Bits × Bits) := #[(0x14bb3,(~~~0x2bd4d)),(0x0,0x0),((~~~0x2a9ca),(~~~0x6bdda)),((~~~0x19a27),0x60598),(0x2b866,0xb844),(0x385cd,0x2054d),(0x0,0x0),(0x4ba1e,0x4b812),(0x0,0x0)]
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
def g127samples : Array (Bits × Bits) := #[((~~~0x0),0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def g191samples : Array (Bits × Bits) := #[((~~~0xf6fe9b6ad7435976a),(~~~0x5ed75ffaf743d9f7b)),(0x61047347514a1b071,0x2175722504019071),(0xe02c1a542bb27198a,0x71a808c421326088a),(0x698182b92c9ed649,0x8854712992898d241),(0x16800cbac44618dfa,0x56800e92444210d3a),((~~~0xe7a87e5f099c2bd83),0x185518e8e242d0258),(0x0,0x0),(0x9272e7035c1109323,0x8602e7031c0109121),(0x0,0x0)]
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
def g251samples : Array (Bits × Bits) := #[((~~~0x0),0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),(0x0,0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[((~~~0x0),0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),((~~~0x0),(~~~0x0)),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def g383samples : Array (Bits × Bits) := #[(0x98b196c38b49cb24e,0x30c414c28b49c120c),((~~~0xed2d07d273495963b),(~~~0x3ee7f7d2fb4bd97bf)),(0x284389d0f21f9909a,0x284381d0e20b9809a),(0xe4097fa73d4025621,0x182b83e031c4025620),(0x4d03c43822b0461b3,0x4d03c03820b002193),(0x18232e32a049a1e418,0x18232e32804120e410),((~~~0x1fc1b0c2db99c766d7),0x2e6f3c2424289128),(0x0,0x0),(0x1010c005ce1ed706d7,0x1d000014a1ad500c7)]
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
theorem s15_3_0 : block g15 3 0 1=true := quickBlock 4 0 0
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
theorem s31_5_0 : block g31 5 0 1=true := quickBlock 5 0 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := quickBlock 6 0 0
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := quickBlock 5 0 0
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
theorem s111_6_0 : block g111 6 0 1=true := quickBlock 6 0 0
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
theorem s189_6_0 : block g189 6 0 1=true := quickBlock 6 0 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := quickBlock 7 0 0
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := quickBlock 6 0 0
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
theorem s191_6_0 : block g191 6 0 1=true := quickBlock 7 0 0
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := quickBlock 7 0 1
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := quickBlock 8 0 1
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := quickBlock 7 0 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := quickBlock 8 0 3
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := quickBlock 9 0 2
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := quickBlock 7 0 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := quickBlock 8 0 1
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := quickBlock 7 0 0
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
theorem s383_8_0 : block g383 8 0 23=true := quickBlock 8 0 2
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := quickBlock 9 0 0
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := quickBlock 8 0 1
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := quickBlock 9 0 4
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := quickBlock 10 0 0
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := quickBlock 8 0 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := quickBlock 9 0 1
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := quickBlock 10 0 2
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := quickBlock 8 0 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := quickBlock 9 0 0
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := quickBlock 8 1 0
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
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := #[(0x14442f40718d81862873c61180e4,0x1a21068502898106284344108064),(0x260084881a0767913e320615888,0x14458400800467813a000615888),(0xaa4283539398b760868a12c170,0x42a812043c3988560068a000160),((~~~0x1776efda3bd13a97f3d2eab911f7),0x18802e1d8024056808211546e200),(0x55ed1207d107e95d79cfc21139d,0x55ed1207d107a91d79ca8211199),(0x1910a9300b264b09d680336f6142,0x1ca293081264a090680320f6100),(0xea2262d8176a10ca10a3f8e9261,0xea2262d8176a104a00a3f0e8241),(0x1a1056c204192662997949582993,0x1a1056c204182462997941500893),((~~~0x1ef83bebd5b6e72d95bbff5be340),(~~~0x1fea3fbdf176ef6dbfbbff5fe341))]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := quickBlock 9 0 0
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := quickBlock 9 0 1
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := quickBlock 10 0 1
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := quickBlock 9 0 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := quickBlock 10 0 3
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := quickBlock 10 0 3
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := quickBlock 10 0 3
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := quickBlock 11 0 3
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := quickBlock 11 0 0
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := quickBlock 9 0 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := quickBlock 10 0 3
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := quickBlock 10 0 1
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := quickBlock 11 0 3
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := quickBlock 11 0 3
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := quickBlock 11 0 2
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := quickBlock 12 0 2
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := quickBlock 9 1 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := quickBlock 10 1 2
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := quickBlock 11 1 2
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := quickBlock 9 1 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := quickBlock 10 1 0
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := quickBlock 9 1 0
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun


-- If the supplied wire vanishes from the live set, its original circuit
-- lower bound applies. Otherwise the raw input witnesses force the entire
-- augmented starting set to be live.
theorem augmentedLower {raw : List Sig} {e T : Sig} {k : Nat} (hp : proper T)
    (old : Lower raw T (k+1))
    (must : ∀ a ∈ raw, Essential T (raw++[e]) a)
    (no : Impossible T k (raw++[e]).toFinset) : Lower (raw++[e]) T (k+1) := by
  intro p bank hr ha
  obtain ⟨n,t,S,hn,run,sub⟩ := reach_live hp hr ha
  by_cases he : e ∈ S
  · have eq : (raw++[e]).toFinset = S := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨?_,sub a⟩
      intro hm
      rcases List.mem_append.mp hm with hw | hw
      · obtain ⟨r,s,hd,iso⟩ := must a hw
        exact raw_required run _ a sub r s hd iso
      · have same : a=e := by simpa using hw
        exact same.symm ▸ he
    by_contra! small
    exact no n t (by omega) (eq.symm ▸ run)
  · have supp : supply (raw.map observe) (S.toList.map observe) := by
      intro a ha
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
      have mem : v ∈ S := by simpa using hv
      apply Or.inl
      apply List.mem_map_of_mem
      rcases List.mem_append.mp (sub v mem) with hw | hw
      · exact hw
      · have eq : v=e := by simpa using hw
        exact False.elim (he (eq ▸ mem))
    obtain ⟨q,W,reach,goal,budget⟩ := contraction (observe_proper hp)
      (list_run run S.toList (Finset.nodup_toList _) (by simp)) _ Reach.start supp
    have bound := old q W reach goal
    omega

def taggedPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := (hints >>> (9*i)) &&& 511
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

theorem augmentedGraph {m k hints tagged}
    (hp : properB (graphGoal m) = true)
    (rawEq : vars tagged = vars m ++ [orSeed]) (goalEq : graphGoal tagged = graphGoal m)
    (old : Lower (vars m) (graphGoal m) (k+1))
    (ess : checkEssential (graphGoal m) (vars tagged) (taggedPairs m hints) = true)
    (all : (taggedPairs m hints).map Prod.fst = vars m)
    (no : Impossible (graphGoal tagged) k (vars tagged).toFinset) :
    Lower (vars tagged) (graphGoal tagged) (k+1) := by
  rw [goalEq,rawEq] at no ⊢
  apply augmentedLower (proper_of _ hp) old _ no
  intro a ha
  rw [←rawEq]
  apply essential_ok ess
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem countImpossible {T : Sig} {S : Finset Sig} {k : Nat} (small : k+1 < S.card) :
    Impossible T k S := by
  intro n t budget run
  have h := (live_size run).2
  omega
theorem reachFromSupply {R : Type} {initial seed bank₀ : List (Wire R)} {n : Nat}
    (base : Reach initial n bank₀) (ready : ∀ v ∈ seed, Available bank₀ v)
    {p bank} (path : Reach seed p bank) :
    ∃ out, Reach initial (n+p) out ∧ ∀ v ∈ bank, Available out v := by
  induction path with
  | start => exact ⟨_,base,ready⟩
  | @one q old a h use ih =>
    obtain ⟨out,step,supply⟩ := ih
    have hu : Available out a := use.elim (supply a) Or.inr
    refine ⟨_,Reach.one step hu,?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Or.inl List.mem_cons_self
    · exact available_cons _ (supply v hv)
  | @two q old a b op h ua ub ih =>
    obtain ⟨out,step,supply⟩ := ih
    have ha : Available out a := ua.elim (supply a) Or.inr
    have hb : Available out b := ub.elim (supply b) Or.inr
    refine ⟨_,Reach.two op step ha hb,?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Or.inl List.mem_cons_self
    · exact available_cons _ (supply v hv)

theorem lowerAppendOr {raw : List Sig} {T a b : Sig} {L : Nat}
    (lower : Lower raw T (L+1)) (ha : a ∈ raw) (hb : b ∈ raw) :
    Lower (raw ++ [a ||| b]) T L := by
  intro p bank h hit
  have av {x : Sig} (hx : x ∈ raw) : Available (raw.map observe) (observe x) :=
    Or.inl (List.mem_map_of_mem hx)
  have base := Reach.two true (Reach.start (roots:=raw.map observe)) (av ha) (av hb)
  have eq : observe (a ||| b) = combine true (observe a) (observe b) :=
    obs_bin true a b
  have supply (v) (hv : v ∈ (raw ++ [a ||| b]).map observe) :
      Available (combine true (observe a) (observe b) :: raw.map observe) v := by
    simp only [List.map_append,List.map_cons,List.map_nil,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with hm | rfl
    · exact Or.inl (List.mem_cons_of_mem _ hm)
    · exact Or.inl (by simp [eq])
  obtain ⟨out,reach,sup⟩ := reachFromSupply base supply h
  have bound := lower _ _ reach (hit.elim (sup _) Or.inr)
  omega



namespace Free31

end Free31

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound31 : Lower (vars 2079) (graphGoal 2079) 6 := by
  change Lower (vars 31 ++ [vertex 31 0 ||| vertex 31 3]) (graphGoal 31) 6
  apply lowerAppendOr (L:=6)
  · exact fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 31 p bank hr ha)
  · decide +kernel
  · decide +kernel

def entries31 := extendKnown known383 6 [(2079,[]),(2361,[130, 114, 98, 81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound31 : Known entries31 := extendKnown_ok valid383 seededBound31 (by decide +kernel)
namespace Free63

end Free63

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound63 : Lower (vars 2111) (graphGoal 2111) 7 := by
  change Lower (vars 63 ++ [vertex 63 0 ||| vertex 63 3]) (graphGoal 63) 7
  apply lowerAppendOr (L:=7)
  · exact fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 63 p bank hr ha)
  · decide +kernel
  · decide +kernel

def entries63 := extendKnown entries31 7 [(2111,[]),(2365,[129, 113, 82, 97, 48])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound63 : Known entries63 := extendKnown_ok sound31 seededBound63 (by decide +kernel)
namespace Free95

end Free95

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound95 : Lower (vars 2143) (graphGoal 2143) 7 := by
  change Lower (vars 95 ++ [vertex 95 0 ||| vertex 95 3]) (graphGoal 95) 7
  apply lowerAppendOr (L:=7)
  · exact fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 95 p bank hr ha)
  · decide +kernel
  · decide +kernel

def entries95 := extendKnown entries63 7 [(2143,[]),(2207,[118, 33, 48]),(2425,[129, 33, 114, 81, 48]),(2489,[98, 134, 114, 81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound95 : Known entries95 := extendKnown_ok sound63 seededBound95 (by decide +kernel)
namespace Free175

def data7 (i : Nat) : Nat := 0x3fd30

def liveLevels : Nat → Packing
  | 7 => (1,1,0,0,0,0,0,data7)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def samples : Array (Bits × Bits) :=
  let padding : Bits := 0xffffffffffffffffffffffffffffffffe000
  #[((padding ||| 0x14cb),0xcc9),((padding ||| 0x1734),0x1134),(0xa99,0xa88),(0xd43,0x1543),(0,0),(0x3f6,0x316),(0,0),(0x52d,0x1421),(0,0)]

def symmetries : Array (List Nat) := #[[]]

def columns : IndexTree ColumnInfo := (.leaf [(8,0,167,0,7)])

def forest : Forest := ⟨2223,7,fun j => samples[j]?.getD (0,0),columns,symmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem geom : graphValid forest (boundsBefore entries95) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel, by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b7at0 : block forest 7 0 1=true := quickBlock 7 0 0

theorem all7 : block forest 7 0 1=true := b7at0

theorem tables : checkedTables forest 7 := by
  intro j hj
  interval_cases j
  · exact (rfl : block forest 0 0 0=true)
  · exact (rfl : block forest 1 0 0=true)
  · exact (rfl : block forest 2 0 0=true)
  · exact (rfl : block forest 3 0 0=true)
  · exact (rfl : block forest 4 0 0=true)
  · exact (rfl : block forest 5 0 0=true)
  · exact (rfl : block forest 6 0 0=true)
  · exact all7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2223) 7 (vars 2223).toFinset :=
  root_index (g:=forest) (before_sound _ sound95) geom tables (k:=7) (by decide) (i:=0) (by decide +kernel)

end Free175

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound175 : Lower (vars 2223) (graphGoal 2223) 8 :=
  augmentedGraph (k:=7) (m:=175) (hints:=36893523332462805514) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 175 p bank hr ha)) (by decide +kernel) (by decide +kernel) Free175.noRun

def entries175 := extendKnown entries95 8 [(2223,[]),(2477,[129, 97, 82, 65, 48])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound175 : Known entries175 := extendKnown_ok sound95 seededBound175 (by decide +kernel)
namespace Free189

end Free189

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound189 : Lower (vars 2237) (graphGoal 2237) 7 := by
  change Lower (vars 189 ++ [vertex 189 0 ||| vertex 189 3]) (graphGoal 189) 7
  apply lowerAppendOr (L:=7)
  · exact fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 189 p bank hr ha)
  · decide +kernel
  · decide +kernel

def entries189 := extendKnown entries175 7 [(2237,[]),(2395,[130, 114, 98, 33, 81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound189 : Known entries189 := extendKnown_ok sound175 seededBound189 (by decide +kernel)
namespace Free365

def data6 (i : Nat) : Nat := 0x3fd20

def liveLevels : Nat → Packing
  | 6 => (1,1,0,0,0,0,0,data6)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def samples : Array (Bits × Bits) :=
  let padding : Bits := 0xffffffffffffffffffffffffffffffffff00
  #[(0x6,0xfe),(0,0),((padding ||| 0xb),0xf3),((padding ||| 0x4e),0xc),(0,0),(0x15,0x1),(0xae,0x8e),(0,0),(0xf1,0x70)]

def symmetries : Array (List Nat) := #[[]]

def columns : IndexTree ColumnInfo := (.leaf [(0,1,332,32,5)])

def forest : Forest := ⟨2413,6,fun j => samples[j]?.getD (0,0),columns,symmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem geom : graphValid forest (boundsBefore entries189) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel, by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b6at0 : block forest 6 0 1=true := quickBlock 7 0 0

theorem all6 : block forest 6 0 1=true := b6at0

theorem tables : checkedTables forest 6 := by
  intro j hj
  interval_cases j
  · exact (rfl : block forest 0 0 0=true)
  · exact (rfl : block forest 1 0 0=true)
  · exact (rfl : block forest 2 0 0=true)
  · exact (rfl : block forest 3 0 0=true)
  · exact (rfl : block forest 4 0 0=true)
  · exact (rfl : block forest 5 0 0=true)
  · exact all6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2413) 6 (vars 2413).toFinset :=
  root_index (g:=forest) (before_sound _ sound189) geom tables (k:=6) (by decide) (i:=0) (by decide +kernel)

end Free365

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound365 : Lower (vars 2413) (graphGoal 2413) 7 :=
  augmentedGraph (k:=6) (m:=365) (hints:=37783543584160634372136) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 365 p bank hr ha)) (by decide +kernel) (by decide +kernel) Free365.noRun

def entries365 := extendKnown entries189 7 [(2413,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound365 : Known entries365 := extendKnown_ok sound189 seededBound365 (by decide +kernel)
namespace Free127

def data5 (i : Nat) : Nat := 0x40cce5240854530

def data6 (i : Nat) : Nat := 0x81b780854530

def data7 (i : Nat) : Nat := 0x102085ce31ec28998408078cbc077d514c37eb02616f1d130

def data8 (i : Nat) : Nat := 0x3f35990823fd30

def move6 (i : Nat) : Nat := 0x70

def move7 (i : Nat) : Nat := 0x30

def move8 (i : Nat) : Nat := 0x7404b4

def liveLevels : Nat → Packing
  | 5 => (1,4,3,0,0,0,0,data5)
  | 6 => (1,3,3,0,0,0,0,data6)
  | 7 => (3,2,4,0,0,7,0,data7)
  | 8 => (1,1,3,0,0,0,0,data8)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 move6
  | 7 => lookupWord 1 2 0 4 0 0 move7
  | 8 => lookupWord 1 5 0 6 2 0 move8
  | _ => fun _ => none

def samples : Array (Bits × Bits) :=
  let padding : Bits := 0xffffffffffffffffffffffffffffffc00000
  #[((padding ||| 0xa3daa),0x3229a8),((padding ||| 0x15d345),0x1d204),(0x322a37,0x320833),(0x26f790,0xcf780),(0x1484c,0x10044),(0xcc6f7,0xcc657),(0x25a4ca,0x2424ca),(0,0),(0,0)]

def symmetries : Array (List Nat) := #[[]]

def columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(0,8,99,20,6),(4,8,99,16,5),(16,8,99,4,5),(32,0,95,0,8)]) (.fork 2 (.leaf [(16,32,78,1,5),(17,32,78,0,4)]) (.leaf [(64,0,63,0,8),(2,64,61,0,5),(34,64,29,0,4)])))

def forest : Forest := ⟨2175,8,fun j => samples[j]?.getD (0,0),columns,symmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem geom : graphValid forest (boundsBefore entries365) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel, by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b5at0 : block forest 5 0 1=true := quickBlock 6 0 0

theorem all5 : block forest 5 0 1=true := b5at0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b6at0 : block forest 6 0 1=true := quickBlock 7 0 0

theorem all6 : block forest 6 0 1=true := b6at0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b7at0 : block forest 7 0 1=true := quickBlock 7 0 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b7at1 : block forest 7 1 2=true := quickBlock 8 0 0

theorem all7 : block forest 7 0 3=true := (@block_merge forest 7 0 1 2 b7at0 b7at1)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b8at0 : block forest 8 0 1=true := quickBlock 8 0 0

theorem all8 : block forest 8 0 1=true := b8at0

theorem tables : checkedTables forest 8 := by
  intro j hj
  interval_cases j
  · exact (rfl : block forest 0 0 0=true)
  · exact (rfl : block forest 1 0 0=true)
  · exact (rfl : block forest 2 0 0=true)
  · exact (rfl : block forest 3 0 0=true)
  · exact (rfl : block forest 4 0 0=true)
  · exact all5
  · exact all6
  · exact all7
  · exact all8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2175) 8 (vars 2175).toFinset :=
  root_index (g:=forest) (before_sound _ sound365) geom tables (k:=8) (by decide) (i:=0) (by decide +kernel)

end Free127

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound127 : Lower (vars 2175) (graphGoal 2175) 9 :=
  augmentedGraph (k:=8) (m:=127) (hints:=36064050782142986) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 127 p bank hr ha)) (by decide +kernel) (by decide +kernel) Free127.noRun

def entries127 := extendKnown entries365 9 [(2175,[]),(2429,[129, 82, 113, 48]),(2463,[101, 134, 117, 33, 48])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound127 : Known entries127 := extendKnown_ok sound365 seededBound127 (by decide +kernel)
namespace Free191

end Free191

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound191 : Lower (vars 2239) (graphGoal 2239) 10 := by
  change Lower (vars 191 ++ [vertex 191 0 ||| vertex 191 3]) (graphGoal 191) 10
  apply lowerAppendOr (L:=10)
  · exact fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 191 p bank hr ha)
  · decide +kernel
  · decide +kernel

def entries191 := extendKnown entries127 10 [(2239,[]),(2399,[133, 117, 101, 33, 48]),(2427,[130, 114, 98, 81]),(2493,[129, 82, 97, 48])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound191 : Known entries191 := extendKnown_ok sound127 seededBound191 (by decide +kernel)
namespace Free223

end Free223

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound223 : Lower (vars 2271) (graphGoal 2271) 8 := by
  change Lower (vars 223 ++ [vertex 223 0 ||| vertex 223 3]) (graphGoal 223) 8
  apply lowerAppendOr (L:=8)
  · exact fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 223 p bank hr ha)
  · decide +kernel
  · decide +kernel

def entries223 := extendKnown entries191 8 [(2271,[]),(2553,[118, 130, 81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound223 : Known entries223 := extendKnown_ok sound191 seededBound223 (by decide +kernel)
namespace Free319

end Free319

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound319 : Lower (vars 2367) (graphGoal 2367) 10 := by
  change Lower (vars 319 ++ [vertex 319 0 ||| vertex 319 3]) (graphGoal 319) 10
  apply lowerAppendOr (L:=10)
  · exact fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 319 p bank hr ha)
  · decide +kernel
  · decide +kernel

def entries319 := extendKnown entries223 10 [(2367,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound319 : Known entries319 := extendKnown_ok sound223 seededBound319 (by decide +kernel)
namespace Free367

def data6 (i : Nat) : Nat := 0x3e505a5853158130

def data7 (i : Nat) : Nat := 0x810d058416083c16294f0ba52e03cf0b2b0ac09847e2257458130adca48e2b0261ed1614c5604c3370f0242c0987e250d4248130

def data8 (i : Nat) : Nat := 0x1a0208340e038100450d42441b07c2460e02083c1d0d8c321104014005088380030d0580430d064083100641005001432160983c16023064220803810a0e02882c0a10441c021880338d18580420d8642c31006c0430f0582030f058200220702c02186020200682c0d18580220d05841d0b082c10d85841b0b0240240dc541e0d20501e20b03041604883a190b03c0458dd0f0a995384b015f73ce738df1ae33c614b3d4ea864de93d17a183f06e0dc1d837063cb79582a638070133238414500ee1c0324500770c012419000dfd7558530dfd7258530dfc7858530f7c5858530ff96158130ff961481309fd189dd309fc685d5309fd181d5309fc78955309fd78549309fd78509309fc585c5309fd681c5309fd581c5309fd281c530bbd481c5309fc7858530b7c5858530bf908185309fd7814530afd6814530bbd4814530bdd3814530bed2814530bf90814530dbd74505309fc7848530ef66684530df97558130df97458130df97258130df87158130ef96158130fd93158130df87858130fb848581309fd7854130fd94348130fe96248130fe94248130fe92148130bf968481309bd481c530

def data9 (i : Nat) : Nat := 0xb050480906c584301c2201a19160e8d30d0b0706906c5a5434281cc38342e2a1a140e0881b160d18b07008c685a543a3408c36322c0441a1916950e8d30f0b08040114705a342004a342d2a201a140e71a1916100d0230e8b0ac686945838346342d1a1a41b16150e0d89028140d8b09448301409c807c64605438340912b1a0231a16120e0d0234a86886c5848362604c32302c1c120e04028958d030120d8b4484906c58543834a2b1a123a7d4a68a4df9752162042380cf45d6377694c75702ab4fc8f130a3c3ee6e8ba9582464386c8940de1280e800ffcee987fd754c3fe3aa61ff95530ffae4987fd524c3fea1261ff5c530ff8e2987fd614c3fe30a61ff54530ff8a2987fd414c3fe90a61ff84530ffac0987fd504c3fe90261ff44130bfcee985fd754c2fe3aa61df95530bfae4987ee224c2feb8a617f1c530fec22987f9604c3fc90261fe80130

def data10 (i : Nat) : Nat := 0x2a68bfd30

def liveLevels : Nat → Packing
  | 6 => (1,5,0,0,0,0,0,data6)
  | 7 => (6,4,5,0,0,7,0,data7)
  | 8 => (44,3,6,0,0,11,0,data8)
  | 9 => (32,2,6,0,0,11,0,data9)
  | 10 => (1,1,5,0,0,0,0,data10)
  | _ => emptyPacking

def liveIndexValues7 (i : Nat) : Nat := 0x400e3a53a1ca53e000
def liveIndexShift8 (i : Nat) : Nat := 0x81830a2c2c0810820386670c08f0050003c000100
def liveIndexValues8 (i : Nat) : Nat := 0x12b800003901f40d6234001072000000001900c0003b7db7a000000400202200080d604459e85b00056d403fda8edfd6f401881a50236fc27f0080004046b7e00000061a501000000fa07c00000040261c109200080fc0540010150004031006000000207d23d81f0003694001811000695203f5ac002800201881c406207eb7401d80ee0fc000811c8f40330358016dfa00902b81fc0a80d2038815
def liveIndexShift9 (i : Nat) : Nat := 0xf800495700435cd461a83c08441c5329c002c0028e01150007958060f88822838a81c053e8f0747608854423400034922d010300222220b400093193c3f190205c22a10000498110c00014040e1d4005b1b838022617914181a0c80000052a820020a019300a030cb0586863004002189000006470016c02000d568000301a60089f
def liveIndexValues9 (i : Nat) : Nat := 0x200a80b92305f3b029dae50a7c19700cc0c90371af0003425803280cb65cc0ca00d998c0320d0c34708c3028c16b057811664280ca02e455a032c259057c0b872c59a863740cb0459b4300e999665cc0cb270196105a856d05a815c03200ca03b5a3e02040ae03240cb65c80bb97180c8017c0cb68441f031403fd032c1976815a07230c0c969918e107c03ff661c24a05759b1699c03d032c9d7677c3fc66180dd0ff5971032597105180b865cdae568159730574136032d93f08f99b001cc1770578005065597306f993703200ec0ff40cb0578d0d021805503200cb08f407963b008803240dd04580bb032c04a057815e0a6d96301d8409254c9fb0a719a9081c062254c1d1051d8d2263409d274d97306f80b903280cb65cd961008410a68f19710654169032da78040810072980c865c80cb04299ed07cc0c806fc16a62e80ca658c0c802eddc5000c10a0445a10006415d08f40ca6d0851d01f1973032196105a80cb65cd8ae032823c0659962023c0ca05a404f0195a9b05a43ff032015e007823e06fc0cb779423e65cc06b6501970042d971032c09a0571a9806562a314f9946039da0701180b805a19706b91ae6729c0ca6dddca7032423c65c040b681192e65c015d102c02c6c040b903280c805a00ca0ffc09765840b868fc19465440ba02481970165a076b940ab02e40ca65c023d6d15971032db01002626d092833903b40ba014c29f3475a1203200c865cc0ca1a41a0730080c865859630ff423f0ff4027040c0c968f02982711a3e69919b208f25b6147c0416b9806c0058194032815e2305a666840d1d03280c9057c2cc0ff840a66cc01065c98b6032
def liveIndexShift10 (i : Nat) : Nat := 0x5ca2c088037380302b22f18a000
def liveIndexValues10 (i : Nat) : Nat := 0x1414b542239f8cf1789c684e4311428a96f1f14890029b81ac21534c783800009c2055326004bc1b15c34680119846955da3d30c00d9e9b05a7b9cda0ed301c82
def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => some (317,0)
  | 7 => fun h => let v := packedAt liveIndexValues7 (((h/2)%7)*12) 12; if (v >>> 10) == (h/14)%4 then let a := v % 1024; some (a % 571,a/571) else none
  | 8 => fun h => let s := packedAt liveIndexShift8 ((h % 24)*7) 7; let v := packedAt liveIndexValues8 (((h/24+s)%97)*13) 13; if (v >>> 11) == (h/2328)%4 then let a := v % 2048; some (a % 720,a/720) else none
  | 9 => fun h => let s := packedAt liveIndexShift9 ((h % 116)*9) 9; let v := packedAt liveIndexValues9 (((h/116+s)%347)*14) 14; if (v >>> 12) == (h/40252)%4 then let a := v % 4096; some (a % 789,a/789) else none
  | 10 => fun h => let s := packedAt liveIndexShift10 ((h % 18)*6) 6; let v := packedAt liveIndexValues10 (((h/18+s)%58)*9) 9; if (v >>> 7) == (h/1044)%4 then let a := v % 128; some (a % 32,a/32) else none
  | _ => fun _ => none

def samples : Array (Bits × Bits) :=
  let padding : Bits := 0xfffffffffffffffffe000000000000000000
  #[((padding ||| 0x298140045706cfc4a8),0x1500084654506ca40a8),((padding ||| 0x107a42884fa41382373),0x3c5099ab201302311),(0x3c22e8ad9a80eca6,0x1803272200d8a808ca6),(0x2009827fd4d4674819,0x2e8d084fd054474011),(0,0),(0xae0d550080d797ae07,0xae3d428080d105ae03),(0x15c52482105ed84d1c3,0x1bc18402504e484c0c2),(0,0),(0xd25295132b2a7813bc,0x4142b5102b0a38112c)]

def symmetries : Array (List Nat) := #[[],[83,32],[82,129,48],[50,129,80]]

def columns : IndexTree ColumnInfo := (.fork 16 (.fork 8 (.fork 4 (.leaf [(0,1,332,34,6),(1,0,366,0,8),(2,0,365,0,7),(2,0,2413,0,7)]) (.leaf [(2,1,332,32,5),(0,4,353,10,6),(4,0,355,0,7),(2,4,353,8,5)])) (.fork 4 (.leaf [(0,8,99,260,6),(8,0,359,0,8),(9,0,358,0,5),(4,8,99,256,5)]) (.leaf [(8,4,353,2,5),(12,0,355,0,7),(13,0,354,0,4),(10,4,353,0,4)]))) (.fork 8 (.fork 4 (.leaf [(14,0,353,0,4),(0,32,78,257,6),(32,0,334,0,7),(1,32,78,256,5)]) (.leaf [(32,1,332,2,5),(33,0,334,0,7),(34,1,332,0,4),(36,0,331,0,5)])) (.fork 4 (.leaf [(41,0,326,0,4),(66,0,301,0,5),(256,8,99,4,5),(260,8,99,0,4)]) (.fork 2 (.leaf [(256,32,78,1,5),(257,32,78,0,4)]) (.leaf [(320,0,47,0,5),(328,0,39,0,4),(352,0,15,0,4)])))))

def forest : Forest := ⟨2415,10,fun j => samples[j]?.getD (0,0),columns,symmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem geom : graphValid forest (boundsBefore entries319) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel, by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b6at0 : block forest 6 0 1=true := quickBlock 7 0 0

theorem all6 : block forest 6 0 1=true := b6at0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b7at0 : block forest 7 0 5=true := quickBlock 7 0 1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b7at5 : block forest 7 5 1=true := quickBlock 8 0 0

theorem all7 : block forest 7 0 6=true := (@block_merge forest 7 0 5 1 b7at0 b7at5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b8at0 : block forest 8 0 1=true := quickBlock 7 0 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b8at1 : block forest 8 1 37=true := quickBlock 8 0 4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b8at38 : block forest 8 38 6=true := quickBlock 9 0 1

theorem all8 : block forest 8 0 44=true := (@block_merge forest 8 0 1 43 b8at0 (@block_merge forest 8 1 37 6 b8at1 b8at38))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b9at0 : block forest 9 0 12=true := quickBlock 8 0 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b9at12 : block forest 9 12 20=true := quickBlock 9 0 3

theorem all9 : block forest 9 0 32=true := (@block_merge forest 9 0 12 20 b9at0 b9at12)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b10at0 : block forest 10 0 1=true := quickBlock 8 0 0

theorem all10 : block forest 10 0 1=true := b10at0

theorem tables : checkedTables forest 10 := by
  intro j hj
  interval_cases j
  · exact (rfl : block forest 0 0 0=true)
  · exact (rfl : block forest 1 0 0=true)
  · exact (rfl : block forest 2 0 0=true)
  · exact (rfl : block forest 3 0 0=true)
  · exact (rfl : block forest 4 0 0=true)
  · exact (rfl : block forest 5 0 0=true)
  · exact all6
  · exact all7
  · exact all8
  · exact all9
  · exact all10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2415) 10 (vars 2415).toFinset :=
  root_index (g:=forest) (before_sound _ sound319) geom tables (k:=10) (by decide) (i:=0) (by decide +kernel)

end Free367

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound367 : Lower (vars 2415) (graphGoal 2415) 11 :=
  augmentedGraph (k:=10) (m:=367) (hints:=37778967926939224375818) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 367 p bank hr ha)) (by decide +kernel) (by decide +kernel) Free367.noRun

def entries367 := extendKnown entries319 11 [(2415,[]),(2479,[118, 130, 81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound367 : Known entries367 := extendKnown_ok sound319 seededBound367 (by decide +kernel)
namespace Free493

def data8 (i : Nat) : Nat := 0x7fd20

def liveLevels : Nat → Packing
  | 8 => (1,1,0,0,0,0,0,data8)
  | _ => emptyPacking

def liveIndex : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def samples : Array (Bits × Bits) :=
  let padding : Bits := 0xfffffffffffffffffffffffffffffffe0000
  #[(0xe2e5,0x1a2a5),(0,0),((padding ||| 0x9e17),0x9c05),((padding ||| 0x1a1c2),0x61c2),(0,0),(0x49cb,0x4942),(0x25f0,0xa1d0),(0x1333c,0x12238),(0x13e21,0x11621)]

def symmetries : Array (List Nat) := #[[]]

def columns : IndexTree ColumnInfo := (.leaf [(1,0,492,0,8)])

def forest : Forest := ⟨2541,8,fun j => samples[j]?.getD (0,0),columns,symmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem geom : graphValid forest (boundsBefore entries367) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel, by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b8at0 : block forest 8 0 1=true := quickBlock 8 0 0

theorem all8 : block forest 8 0 1=true := b8at0

theorem tables : checkedTables forest 8 := by
  intro j hj
  interval_cases j
  · exact (rfl : block forest 0 0 0=true)
  · exact (rfl : block forest 1 0 0=true)
  · exact (rfl : block forest 2 0 0=true)
  · exact (rfl : block forest 3 0 0=true)
  · exact (rfl : block forest 4 0 0=true)
  · exact (rfl : block forest 5 0 0=true)
  · exact (rfl : block forest 6 0 0=true)
  · exact (rfl : block forest 7 0 0=true)
  · exact all8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2541) 8 (vars 2541).toFinset :=
  root_index (g:=forest) (before_sound _ sound367) geom tables (k:=8) (by decide) (i:=0) (by decide +kernel)

end Free493

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound493 : Lower (vars 2541) (graphGoal 2541) 9 :=
  augmentedGraph (k:=8) (m:=493) (hints:=37820437072308053475368) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 493 p bank hr ha)) (by decide +kernel) (by decide +kernel) Free493.noRun

def entries493 := extendKnown entries367 9 [(2541,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound493 : Known entries493 := extendKnown_ok sound367 seededBound493 (by decide +kernel)
namespace Free255

end Free255

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound255 : Lower (vars 2303) (graphGoal 2303) 11 := by
  change Lower (vars 255 ++ [vertex 255 0 ||| vertex 255 3]) (graphGoal 255) 11
  apply lowerAppendOr (L:=11)
  · exact fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 255 p bank hr ha)
  · decide +kernel
  · decide +kernel

def entries255 := extendKnown entries493 11 [(2303,[]),(2527,[118, 133, 33, 48]),(2555,[118, 130, 81]),(2557,[82, 129, 48])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound255 : Known entries255 := extendKnown_ok sound493 seededBound255 (by decide +kernel)
namespace Free383

def data12 (i : Nat) : Nat := 0x422f1d0a27fd30

def data11 (i : Nat) : Nat := 0x5d2c5088434194bc582a13c7614046974b0421a4bc5e218e876140a0230ba58a1108692f178b23a1d050118732c1409e42194bc591d050116612c13e84421f8dc6c2f1647414046974b142210d25e2f10c743b0a05011a501a0cc511d0218b142210ca5e2c8ec280893a174b0508e81808739960a046210ca5e2c8ea4c25827d08843f1a0cc5f1d0bc2985828108652f164741c0a4960a0421a0cc642c8e811258a11087e34978bc431d0bc2808c35174b03f1382cc692c11886421f8d25e218e85e140469ce843f17c280c6218fc4e17216284421f8d25e2c10c741c0b05011a5827d08843f1a0863a17850116501f89c0c04296086421f89c2e0b03011273a14bc591d8502806014984852f8e8701d0a39cc8c4297c7614639d0a5e2c8e8701403413e852f1647414639d0a5f1d0e4281204413c671d1d0a5f1d850280862c50a5f1d09c28d42190b0742978b23a0a2d087f1d09c28146a479d69658fd8838097ce7787346de66d6175c155051549b4604373bd3553232cd2772331f81ab1701231030c808d06d03b000ffe884c3ff61930ffd824c3ff58930ffd524c3ff60530ffc814c3ff5c530ffc714c3ff58530ffd514c3ff48530ffe114c3ff5c130ffc704c3ff58130ffd504c3ff0c130ffd204c3ff44130ffc104c3ff80130bfe884c2ff61930efe664c2ff60930fee224c2ff60530bfc814c3fd84530ff9704c3fe0c130ff9204c3fe80130

def n10f3 (i : Nat) : Nat := 0x299a227799a558ce228458961d8661582605795d9755c9715c16959563589615815954d5254550525394c529485204650922487204791c4701a4590e42906409
def n10r (i : Nat) : Nat := 0x14348cdb6a1bacd433a9a2e65b53cde6997a0d32b31a64e034c2f26903c0c33385794e8a84de049a1c08b5381066f01e54e038fbc0621b7a174c9c3265085c31b0aea40a6be69491c12943e453a3c60565940ada87d30cef9adc9f1ed3bc015d783ed4f1622de96593ceba87414d4e9d22dd95cf3a48b274ef50e06599c2b21391072710114db05a1b50b236109e6d1330dac641b445434616f6a6958d47ea9a2545b4c6856866e4d03ea1988b532d19e65a720cb4a31941cdb08260604f54c2ba2d896523047b261d762ba82a5737342e46675cb33ab87699731ab2e206a5e2ed4b9e22d75e4f2e15925e6280bcedc973cd42c5f675806b6b30ea967345ad2ca458133cb2e261604592ceaa31255c424a32049c782b1da8554696abe69c33af1072edd0e1db61887583136a86edcf0ce7d61b8f2c3306f067ad80d6da419db0c383e806f0cd0d1b821c4bc836073a8dc62522a92a0a545428a228cf725029509ad14537b2f26b5904dad1a98b6c523853a47b5d496eb8901d9921db2a45b5a4854a2921591257d9246fa84552cc8a4d5516f28a2fd5f45ab488a2e7915354204b5f41c13c81f23502ad8824fe90485940c13c011c7402dae3047dce0a6b881126e823cdc060dca097b24185f00223c705c9b40bf354181e88305eb0549c8098b20191ef02a8d8054b9a0a7b041487902f4f13c6952790d28f07341e67673cd0ae7a5284f06cb1ee2a53db2a27b613cf282f9e25863e493279aa50f90521e139e3c35307a72c8f4dc51c28703a655070595ce8c531c1e553a2d2271317ce78cc9cb38e38751674c290e18cf1c5d98394f24716a40e43d91c538a357ad06b7d7cd89c71b27a434313c6a2a48d97c81acea0023dd063bd44c79af99218e31ff3c58024cb3628160b8d2c39185cd94e122191402b124e35e425ec8802553c052a740c62399aa074ab78e96a71d32dc39a6b8676410c6572182f5c2c3e905514c0ab2986d0854d0c82da0915322f13646018c8b89d715952e110b5c1800bb74a9620188857a911ca9423e1c0463d408ab6f11dd4e22a9b845853088f6c111d1623e90c48e25aa1b0355904e192588336b70708ac0e01221b9dac384c20645720d7f16a3dc0d48d08269d310a376014cebc299d70533ab0a674814f67908a1882beb005fd5e0bfab81814b823fa104732c08de9411aa882224f046cd60bfa90120d90301833e6a5470b02ce5c819d192435883c6b1060d62099ac41235f6206b10c40294500f570009d50027dbc03957010a97026f5a01fe98032360092a5018a9203c94405db5807e8b0274c80496400914996db18165a161ce4
def n10g (i : Nat) : Nat := 0x7c40f872f0a5e0cbc0977f2efa5decbbc97772eea5dccfb81f6d3ed47d9cfb21f613ebc7d6cfac1f553ea47d3cfa61f493e8c7d0cfa01f3d3e747cdcf9a1f313e5c7cacf9427244e409c7138c27144e209c3138427044e009bf137c26f44de09bb137426e44dc09b7136c26d44da09b3136426c44d809af135c26b44d609ab135426a44d409a7134c26944d209a31743ae825cfab9e1739ae6e5cd2b99172fae5a5caab941725ae465c82b8f171bae325c5ab8a1711ae1e5c32b851707ae0a5c0ab8016fdadf65be2b7b16f3ade25bbab7616e9adce5b92b7116dfadba5b6ab6c16d5ada65b42b6716cbad925b1ab6216c1ad7e5af2b5d16b7ad6a6ac8d579aac35526a98d519aa0353a6a68d4b9a9435226a38d459a88350a6a08d3f9a7c34f269d8d399a7034da69a8d339a6434c26978d2d9a5834aa6948d279a4c34926918d219a40347a68e8d1b9a34346268b8d159a28344a6888d0f9a1c34326858d099a10341a6828d039a043c0177f4efcddf63be577bcef5dde83bc97784eeeddda3bad774cee7ddcc3b917714ee0ddbe3b7576dced9ddb03b5976a4ed2dda23b3d766cecbdd943b217634ec4dd863b0575fcebddd783ae975c4eb6dd6a3acd758ceafdd5c3ab185530a8614cc29185130a0613cc27184d3098612cc2518493090611cc2318453088610cc211841308060fcc1f183d307860ecc1d1839307060dcc1b1835306860ccc191931125fe4bb496d92c9256e4a94949928124de49749259239244e485490191f123be47348dda1a7432685fd0b5a157428684bd08da10761e2c36d862b0af812f01fe033c04fa06b406e800
def n10p (i : Nat) : Nat := (if i<1 then 0x82cc760a018681604f0fb1c05c055092fc751d428060146813c489083e07c04170470d02c0ab1c01072560340871dc2804178500d31d0760a0115713d3fc751382804178500d02c4750a0106a120320b02701c0450b1c0400b828060104e0c421c70130480355d4f0ff1d44e0a8045d11f420d22f08401140340871c05c0e0045d0c421c7413828015a4588ff1d84f090062fc70130490a01801170470d021040030046f18c48100358ca2c0b05c114420d02f0b02ac747219063174574bc21c74741243c09c21c74190486d190400c42a09f1d040601543f0d033c7412034741bc641852f0871dc285dd0834cbd1d07418c287416c430d8310841f8285d140314bc2c0871d8286f1743e0d31d06413828691784d0fc3ec74108285dd08344bc2ac740b8285d16c310ab1d0640b8285d128310871d05c0b8285d0d12f0ab1d0580b82873172420c42107c174285d1404f0c421c70174285d1472f0af1d064170285d140310871d02c0a824510f8374bc2cc741902451140340af1d064170245d1383ec74190420a0245c9083109c2104c0b020741905a1404350b1d014731c05d1382c0871d0155793c420f82fc701701474178581403409c2001074160500b02a0871d010741705814021c74130106c1745810c3f09c1001061174500f82cc741001072184340c821c770a00c6856050118340871c0045653c460d0330841a005731cc5c8b31d00801000701bc6c170581384790b1d1a86418c5d4bc21c74170586f160500c52f0871c05e0a1745b1412f0ab1d0640b8285d16d420fb1d0641002e0a174500d021c74190400b8286f1a45d508310871d05d0a1c9580e434c7419054100287317450100344bf1d8280a17157128460f81f05d0a018745604c120340cc32c74041a44e0d0320b0270871d010571403b0d0270871d040041a05813d420d026c760a0105c508420d02a8751d828041b05b160500fc2704806010731744e0f8230871d0140417157140420f81f84c0600c741103c0d02a09f1d040019a4570fb1c04c12c24060045d55c51108310bc21c701302c6d1b05713c3fcbc27c7413c28721a45d138348bc2c0ab1d0146c190581402f09c21c7412010741b0641744509c21c7410011731cc6c0a027090170420a0057317451cbc27c741902a0400455d08390d0330a31d04c03004731744dcbc2c0a31d428030046017443100360c42c09421c76135a464174420f827c741904c1081173178420f0390d027c7419040011c5581304310b2fc7413c2a0400472174571504d11a2f0871d07016828711b057146420fc340871d0560a00c7317051134340b02ac761702e0a00c5d55c5413c4c0bc2c08821c7613008711b05d15c4c10e421083b0d02ac740e1a05d13c4e0c12f0bc2c08821c7613828711b86c15c5513142108320b028c7403 else (if i<2 then 0x90a31d1885010027c745d148430871d177420d021c745c1403ec741d1604f4bb1d4705d14034084191d0580d02145d730fc360d0171742a09f1d05c6f1903f85c131b04c8fc3f048720fc340bc1010c3f0d02702c6918c3f0840bd0b2f4741dc285d0c42c0860a5a43e0b010828340841002e0a17834c751d4285d1343f02c0a1cc3f8da2f019428fc328bc061d05c1431d0185d14033c74061d02ac741d0186c12043c70061d0730ff0a018500fc120280616c4309e1f0146c11e42c70051b45b50b1c0145b50b1c428055092fc7006014480d02c09c045845893f1d0106c16027c74045a43fc7509010500fc27018045cc50c74060104309d1f014041b06009c0c00c6f15c340780116257c74130071d84e0a028015cc27030050043409f1d01001c7413011030043409f1d00c01184460d42c000711431d048001cd581243f0d12f1a8641845d4bc211d05c130481081f1c46c1785d0e01f1b04f508420d31d18c4f0f0330cb1d1804f0d0330cb1d5864f4c92f0bf1d1a8490d02f0b31d170450d02c0ab1d17443908310871d17441100310861d5845050842c751c55c4f4bc2fc751c1d0368bc2107e171744f508340ac171a8601383f084171d0490fe2f08417174510d92f08417174500d021064171b0500d021082131b06413c3fc74131b04c0d02108012154340cc32c741255d421083fc750e174500f81905c0e1a85d1603f09c0b1c86a0fc2104c0b128310871c04c0b174500c42c0860a55c4f4bc2cc760a178420d02c8760a1cc5050b1d8720a5cc4f50b1d85e0a585420b31d03a0a1d03f0d12f02e0a1ce328bc2107d0a53e3fc751705d0a17834c751d0550a140340841902c0a58450c751c4280a13d36c75174280a1bc5d5083e4bc061b05c10b1d474061d03f0fa3605c061a0501083f048061c45010b1d0480614033c7412028061a84f0fb1c04c0516c4309e1f01805120439083408404140340cc27c7404160500fb1c04c041c450c7415018041b05b1631c01404174450c421c7403d06324b31d04c0153e3fc76130100150b1c0180500c011bc6c12043108320b0681504f9083f4bc211bc69175420d12f0786a1804e0d0330b31d17045108340b02ac74601604d11c370a31d1a85d160314bc2147474174580c421c751d1744a108310871d0746a1905d0871d05c165a54f508428ff1d84c6913e421093fc7513174439083109c2104c6e10e420c421c701317c4e0fc340cf1d048741bc610d12fc770a177420d32f47418c285e14c4a0fc340b20a17542108340b01e8296193d324bf1d85e0a1c95713c3f086138286a55c310b02184e0a5cc2cc76170380b8285e12c480d834c750a55d460ff1d45c17428720fc340cf1d0490a174510f92f064178246c170424db1d470061a8580fb1d45c17019611302cc741503806174500f else 0x2cc743f0d0324b0730b157c743f04d2c04c2602f1c0122c0071c000630d0330d0270985d09c1f1d05bc744f0cf1d14027c743709f1d5a442c705d0d31c5842fc70500fc190d11d061570fc131743f02c5dc740b0fc174283f0f8060fe0a01a42c700450b1c0131c01203c74044062c804010b31d0002c00400174540fc3418c4f0fc3418c4e0fc341cc3f4d83410c320b0271705b0fc211705b0d021178500d020170500fb1d93c330cb1d1d05c0c71d1b05013b1c908374db1c14034084195cc3f4da1316257c76131852fc76131bc644b013174510b20a1742c0660a1771d05e0a0d31d0560a4bf1d84e0ac741702e0a95f1d05d0a0fc2102d0ac76138280a8fc328bc061431d05406174500fc045cd2cc74040d027c74045cc57c74031cc2c01803174488fc015cc57c74010f81902c01084130140153f1d00c011bc5d160310846f1905d4bc2118c430e02107d7313d4210b1d1906117034c74730fc364bf1d1c46214028c74621403))
def data10 (p : Nat) : Nat :=
  let r := packedAt n10r ((p/4)*23) 23
  let old := packedAt data11 (((r >>> 11)%64)*30+20) 10
  let op := (packedAt n10f3 (((r >>> 17)%64)*10) 10)
  let rm := (if (r % 4)%2=0 then 1 <<< (op % 16) else 0) ||| (if (r % 4)/2=0 then 1 <<< ((op >>> 4)%16) else 0)
  if p % 4=0 then (packedAt data11 (((r >>> 11)%64)*30) 20) ||| ((packedAt n10f3 (((r >>> 17)%64)*10) 10) <<< 20) else if p % 4=1 then ((old ^^^ (old &&& rm)) ||| 1024) else
    let w := packedAt n10g (((r >>> 2)%512)*15) 15
    let n := w >>> 11
    if p % 4=2 then n else packedAt n10p ((w % 2048)*10) (n*10)

def n9f3 (i : Nat) : Nat := 0xa2277629866157a5d5725c5705a9695955a54d525454a4e9394c52a4811a4289a2288921c69168590e82a0680a
def n9r (i : Nat) : Nat := 0x154a17138889c44460a1a88240744210ea1110cd04446c982b943880cc6da3c4b4c4109a68cb73e701b158a6dadc825554a736a7728c0139e0cccf85a627a2530331997b6894bd884a5c5c252b5a128e9707474704402c38e5529602a9ea89550100aa3495160308889a90c419c66206c410d6f20289e24945d280a0dca504552180228b934de5c983f1e4c2c5e2605471312e41f05a3cf86b127c3f873e1742dee5e464780a222c0d110606887f013ae55f1f713305388383dc2ee06e07c201b3ead8d8753c6cc8903634981b1c4cb6cc011b4f012da32036d3e02360fc49b0f422d864166bbc8f3510859a8c636d37116688b08b45048064a89e324f4f66218932c646856ad40b869125b13072d0947046492cab2b0e55a88e2a9d44952a02aa7491453ac0529c346c44a52a21598f10abcf084c6503efd361f65490faf2287de10c3efc82a2681e4f940ca7ca0593e50249f28114fa609275d0393ad81c9b5b094b8301a5c3c552cd41c914e0e45060d06d1244f4821c795c200c9da68649e243254927505070c15268609e80e8760e1729600b9d2685c9e1c2c54c0163b5a0b3dc68589e802a72b4157b8d0aa5438508d802876b4147b8d39269101e02880d032466011232bb0918c2038b20e1251041e260c0913078389812244a480e24300d8e02c0c4a362a24000f10810704980
def n9g (i : Nat) : Nat := 0xf987ca3e42f11780bbc5dc2ed1760bac5d42e91740b9c5cc2e51720b8c5c42e11700b7c5bc3dc9ed8f667b03d69ea8f4e7a43d09e78f367983ca9e48f1e78c3c49e18f067803be9de8eee7743b89db8ed67683b29d88ebe75c3ac9d58ea67503a69d28e8e7443a09cf8e76937499a4bd256927491a47d236917489a43d216907481a3fd1f68f7479a3bd1d68e7471a37d1b68d7469a33d1968c7461a2fd1768b75592ab5550aa354f2a65528a8f5452a15500a7b53b29c54d8a6753129754b0c526263119880c3a61a30b9850e2170d404a413200
def n9p (i : Nat) : Nat := 0x1c778e40107e0d01a02b0e80843202107e0841a0210620841a01e0bbc772111de3a0641a0180420601a01002001b8e0050d800c108030d80040c8010c80fc1a03c0620bc360320581401a02b0d80b8118630c20843783404216c1a0210c60cc1085d0620843184f0405cc2bf1d0de0c38e85107c0641f8340325cc128190e60880c8340380601a71d02c0d38e81503205c0a86f07e04c1a0140241781f811a840d00805de3a0401a02b01e1740c80e0bc1740585d05602c1a02b0161740c80b07e0640581902a02c1a71dc148748e8060b604c0362f016014318610060c4108030bc1740086400c004150010000d01983206016c1a032042178280310401801c82104015c1c82104018c1c02103e1801c02103e1701c02103e1cc2d83403c19dac055e3a1902d048e3a16829843e3a1d01d021e3a174188210381441882102e0ac1381902e1bc319260260c010f1c02609c1081c02418c1e0340201201a41f0200d01081901c1b0180270181b0168270180d0108190160d00f81901617418821c14174158174141778e8190121b01802701010c1391f00a16c9301700a16c13c1f0081bdac04807e0d02183f0680a41386f0c8184190210ba11418821e3a17428f2f0580641a03204fc740c85cc840c4108180de0fc1a02701617021027e3a0183583ee39c240305b0860ca0f8050b610c13c1f00a1c835064e380142d85a0a3c700285b0b210b8e0050660640580600a0c01602700b81032034e3a0580085b069c74058012e61982e84a04e0643205c0900878e8100de1901a02703e02c2883f06809c0c80b0ba1341a02c0318282f04d07dc740810a0dc0c01380900b8103602d04e04c040010ca1722c4500400600306c0b810c1681b0100182e8500680878e8100170283886c0bc174266420680908e85d0a20dc9782ae3a06405c0a
def data9 (p : Nat) : Nat :=
  let r := packedAt n9r ((p/4)*25) 25
  let old := data10 (4*((r >>> 10)%512)+1)
  let op := (packedAt n9f3 (((r >>> 19)%64)*10) 10)
  let rm := (if (r % 4)%2=0 then 1 <<< (op % 16) else 0) ||| (if (r % 4)/2=0 then 1 <<< ((op >>> 4)%16) else 0)
  if p % 4=0 then (data10 (4*((r >>> 10)%512))) ||| ((packedAt n9f3 (((r >>> 19)%64)*10) 10) <<< 30) else if p % 4=1 then ((old ^^^ (old &&& rm)) ||| 2048) else
    let w := packedAt n9g (((r >>> 2)%256)*13) 13
    let n := w >>> 9
    if p % 4=2 then n else packedAt n9p ((w % 512)*11) (n*11)

def data8 (i : Nat) : Nat := 0x5b05405192600528028410c0ca07c014806806404fe3a403403202771d23ac02401f81a101200d040c6068205b034101a010880f1cbc40b6068065e3b0165034027101e8160138121000ba0a8058050032505d05103d02c028019302e828f978160140081ae9b62a336cdb36e6e8e5e7811e7729ca729156b590641734c915380db36cdb36cdb2684d00336e3487494ae29867d9315e80954530cf72e2a5012a8a61f745c49a4c5704c3fa415a622cae098536d2b21d5920530aaf2f6052b240a615ce52c0a564814c32ec98af404aa2986739655280954530cf3262a5012a8a619764e57a025514c33cc9ca9404aa29867c9394a809545308f72964d2a2b8261f545c531165704c339c2ca940cae0984bb88b528195c1309f92b61d2e4902619d654c9a545204c23dca5934a8a40984f8d4b0e97248130a3da56452f2082614bb4ac875a4104c29b69590eac8209853ad2b21d490413087db5643a52082613d256c3a5c9204c27c4a5874b9240984fc11b0e97248130

def data7 (i : Nat) : Nat := 0xfd41710ad31165704c2bd26b02b4c4595c130

def data6 (i : Nat) : Nat := 0x1ad41716b02b4c4595c130
def liveLevels : Nat → Packing
  | 6 => (1,7,0,0,0,0,0,data6)
  | 7 => (2,6,0,0,0,0,0,data7)
  | 8 => (30,5,7,0,0,10,0,data8)
  | 9 => (159,4,7,0,249,13,0,data9)
  | 10 => (331,3,7,0,249,15,0,data10)
  | 11 => (34,2,7,0,0,12,0,data11)
  | 12 => (1,1,7,0,0,0,0,data12)
  | _ => emptyPacking

def liveIndexValues7 (i : Nat) : Nat := 0x10038c731
def liveIndexShift8 (i : Nat) : Nat := 0x217002400481c22050c1040088301
def liveIndexValues8 (i : Nat) : Nat := 0x117e004005b01e00f82580000d001889a60580e484180621ca0830524045dc0000018806a1ca082000802420226f1d7c06e03101a000400e12d0000004041dc401e000c0b61d13ae86e000000200800fc8c01a011491b00040373b1ebf40200020e80774180022010852
def liveIndexShift9 (i : Nat) : Nat := 0xe0101b00320104038aa04083f402050680c04000642446f3040000817011080810008c012010080416012006000073400c36013a800aa0008324b82b5b814540d010067c027481c00032503d5c3c058ec2002910000c0301814024e00008c60d0e9b002000051008060280008fa230683004000102a28
def liveIndexValues9 (i : Nat) : Nat := 0x4100a35e52069c0c380c907c208a813880d30cea02492d400c91ef0028006db07e0102004000183b0042404c81150164053808e41080002014404900000080010408a413883db0d400810001475601220498057820704e004c179200020102032c280b49501a219dc0dd815c00440a44115808000980f1004953416038020401700ad4ad02cd011402050122019583e0656040e13e451200af012001b0038016b0496087c0afafc00190020c0edb0460376a7f470c8093010603240af008001040ec804802110158a141acd015f01900200093867a74ae13440ae000000040499f3c877e012002b97e48093012202000ed00cb012403280b453480cee034c5e3c05e04a28e4005480a501fa04c404981270456037c0282fc2010605a1d2e80a300340840020afb00006024c1080001030e0204049009301067418120002501240341215800c6320000806517cb024c06ec111008201060672bb923fa040a024c014926d608a97240dc81cf656402441c5314a5f64024402f821347f205a86ed00390106029c04080d0017a0498041015f04520328001004801920575ff480a41ef602400508082026408e80ed02120120061d7a08213611400d8041a4b760fc05dc05100320124074c04100a70440024810900d15e9807ac03a0f7a012203b97e200d004e2024806981741a4e024c06481e90120029ccf0005b4842081400b829909a4096c09986a7072602000ae80925f8c088400200a3037602940220577003a029582804f1186200200930565019002bc01f00925f64018c0490b3d5e4402441d80205015801ac0ec820503a81400cd13044637c01540dd022b02d605a005000af18d8049
def liveIndexShift10 (i : Nat) : Nat := 0x77c65fb8338190742f6110392e40dc1182237c0087e81e4440383100202400c7c0750c00000007804a1a81704e0061840085307783c6381043c4a41a00701c0940031a000bc80f6c04783140a8eb0260000300601605d8780a08638a77000110005158110019ac225ff04e03c2185001047c0280c46e6cd770004f0038028010229e4708090000109604700220807ddd032a240e808011cac0005902403000004008034090380028640c0160f030940877a9c10c2c0010d2004038012240c8398000c386c279146ce0d80d807012541c301644015c01003dc0250178250009bc83006e120981700804a75c0301602c000001f501204cdb02302011c1d08e0d9d84074930007982e8140c5945738001687900100900200c0d032032048918173640000788c02a0200703609a1900600101801c007c30020001c80100025c1795ae5e03c2f8841aa0b43bc8c192000028070641c03000004c000098320000048301a01c2f0038a10bc030668790100040480001e8b03a073010004028000620144c80b338055e980e4080000b81925e0000d8380760080080b0040b43f00402e0639c02800602c000000ee0000100c0e00000180202fb884101404405c1680d03006400cd00020800001b00000800005e682340784d0080080008ad94002a18260f40640019e02000c000010000300000304005007809000088048230143600000e09c06c0301776e1140000e0090e80480c00200c0000e01c0b81b848224048000000021b0000000000540002a006008050000201b85200e0b80432200300202fff00583a0381c002000194050000200300f009c8e0000402900a0280f1220060200000b003084060100060f80154f0e00000a802002000208170554ac0e804000006288540035cc0085e01c0000100500a0680b012003dd8030016820084c0010020005201001e0000084b00c0182280300c0dc08800b800080001402e00402011fc00040b0050420340081800443800001002013ef2090ea0038080300a038040040000b81460d011a4c0041b00001004000010000000030680164c000000e554e8000040100081ca200c1ab02e00e2280000102011c01d800740480f0040000080300107e00c0201c000000000000020500280404e0800181c39230400000000034088000020380000200200000017001cdc1301202e0001280000a13a3b00800bb3c000030069c400c50015fa8000010000042c086888000000020006c80a92d0000000380000004c3811001403400088
def liveIndexValues10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x50c0dbc1430362742eeb501b00296050a0cd414303bc15ad15bd66a838a028cec5414a39be052a0e2014a85bd059c03edde5bdf2030c0b3c12e80ef05ae0a5de520334050e0c0819b0362066a0ca0010ba8c06860d05da082b30562eb182db06f9059807fc2b282a806c031d41b102cd052e0a58142842775d00aa16dc816976ea0a5819401ab05980b05dd70e59050c0a5c1943bfd76e81601dff03bd15ac0ca400d82a808100aa01de02a7066e15960d090a705287d5dd6a893406680aac19a0294136c172402c90dc05280cac154042e052887a5cb9baf106c20cd86edbaeb75cc0ca419b02ab192afc541df2d4f052a0b3014a838808120a1c14b842f05f6e10819b82a9058aeb1d6623b7777fa172c1b0811f085e0a581b685af0b6c10b96100276082c0de816b02970668073838691cf050e0cd0222036205081110195bba0066a1025dd703bf76d00a19e24842f76ec041414a836105540db813d02cc05280ef9dba029776ec0a181debad706520a1c1948294066b05cdd6a840806500a5809700c7052c31d814b832875e6edd8142869d05080e25e32008a01640a19d630d633d760a501b72b2d7bec03645ff8dbb0b6ef26c2043b6971300aac11403bf18f80a5c20c3ac60656f19c19503bd1ace4298217bac7059a0d89dbb83bf78920ca5c2d833503a211481778a4c06000a14167bae405e00ca416639cd0b5a3834155832a75d4eb5010156f40018429021783bcab4930640a406ae082c0d84ecf001db08c0aa416782947c10e5bc1f51c4d059c0aa414b836d0810159c283bb75052cef2c1f2bac50554e921e2b82320b920ca56370f6d89a61571dba0361066cf88c2ef45c9056512d9d753b6a0acc0a106f6828475e40cd328c828406dc0b3c19b8285279c0e2c1de028608160aa02e503dfca6f60e016701017bee0a14154032b0ace0ca0194bac706520cd9dfec4b50ace7c7823a0ad700260d8014a41db775e10501428296052e109419b82a8052a1df9dfe05a076ec114816b840b05480efddbabb74066831dc15482e10b6e1d3420482ab1ce8176414a3ad572be0a5c0be829406c0119006b03bc050a0a1016785bf75a80a1815482d704361058368809b0650102020b032b06c01095db402960812129c2130ad5050e10bdd7582960600f18814a032906520a5020502cc076a2665da0036303580cd81678287053607540ed03be050a06ec19a02b13cf60ca0faa832906c20a5c1bc0d47071009681c5bad701eaecc41c503e005520cd414382c5050a0ca814b8d4477fe0ef819b3c6c050eec004cd02aa05600e21d6285b50b480ca022f82cd066e0aac1df921b59eaed00159806d0668e4d00ac3bfe0528429c2f6838b75a810bc14a3baf066e0b341580335034a0da1d57baea08480a59dd1836001e01748217843d071016d else 0xd42048286059a42949bb03370ace0ca4212803f052e159420a032908120ef81df82d6761cedd820583d00814f69abe0905b08160fc4194819476080cd814302cf214c0d89d6b041675cc0b1ddb50340059a0bb4143842f76e80a181de387f0668102c21f826c01d6050000102a97c260a5966d02a877fa10b81423aeb0314eb142cd83be166ced09e3e044f05280a5c19b0329077e5b5023a0427239a10207b284277b48e3902b382860b6e109e3cd028476ee10201940295941e0a1c20582a90098155ddd0842e75d00cd1d7301b70b6a05c819a3ae60552eb14195059475d2eddc14b82fe783810f0143842e00640b341df44de052c0a5c155842706dc0aab29a02cc054ceb1c59b0d881cd3607419a02b07848ecbc1b00dee054809041e9833405f00d82b96029705080c701540247059c0aa9dbb90a63da20ef48f5bb7571da429803382671b641df419402ce07ae0de9d8b8409050a0a1c16682d505600aa419b03be08b0ec31d6b91cc08100d8016a3bca050c0a11d6b842f077a0efc14b8408059c2cdd7fd813b011a0a523563c48ca32272059a042f14d60a18195c92705080a901668337050e44e815282ce94b6f125dd1047705600a1019b0409059a0d8019a3e0675cc063814b832807440b541663c6577f845cc2e5bac6059c0aae53a3b7520be0aa5d62044e07cc43740cdbc4a7cf80da02c90335762803281bc836e052c2b5ead1829600e411981de038b77420aa890d0db00e42172414285b706540cd0154832a084e0a122bf82cd777610997ca446406547d58fef812415aa0d001bd836f077810bc213002404a0084c2b2830277f80a5a05302de06f410241df3e0e065617282128c8105561055db583351b6a102414303bd0b8eeea802e02850528ec34195828776eafbcc55e80c175aeeb10852029675884519ed30336059a10b0194832906540acc195b98076e80e2002590a70554f86414b0297796ceeb46c50297052a131889d85c805520d0dd79072176ee08142e0029606560a18126832a066c0a501b0bbfc72047b2c1ef01bc78ca31d40fa836d0acc0e28195050575d20e281c5032a0aca0b541a10336052e05b9dd13ac6081247d819a83be084ae78416a82ab0aae16dc0a8bb6a190a0cac2e4899472c0159de2b829710c20a51de4042675ac0ca0eb4029675a808fc3b70425015a102c19502961b60ecc8231812806680ef415402cf06c410244cc9171050c0a1e8c3802b077c0aa5ed382967680258828202cf7c24f6901b0bad6050b946003b0287066ef12c2e5d6ac91f6092c15482aa05e61651dff02d608a4ebcc1b603d804d64f342163fbd055004c9d633ae90842376c05c0334084cb074fd54a5b08160aa81b702dd0364ef2c14a8566050b8f0dd638426066e0a120838d5c071417203593aea00844868143b88) else (if i<3 then 0xe01080d0409082850508109016685ef0168eb1c1958409066a0cade2a040886220ac81943b693f540a501a202a97b4c0ca5d74056507740aa1d9f913b05ae7e341c5bb0e038a119419b82b0065634bc194b18b05540ca217f05bb0af015901c4bae477feeddc208842506520d8c1c40362782a0aa063b0336050a0a1404f0295aa8b2f782e0832806dc26e81b5913b758c0d801c505cbd5a816742093b74059e0aa81df032b75d40a5defb03bd27b20b5ddb40d8670acecc02173b6a050c2cd41e82c797796b2d42aa2cd60654102059b82ce059a801c568036e1a62eb5c19401630b920cd01f2084d085c103c16383bc10d4eba021349850448a25c1523c65054b5cd815490a476d6109485d055e02eae134106bb68052aec80155bac677fc45f9dbb05d27bec0ef5dff80690444e36014b0335055208d1d98858c07155f02e938c9d76280a5c16e0003052e0b341d53b690b6a0a1de360de0052f28d9efb036c059aec3404003a04050e029dba82f3066ce59c167bb680508b3f414abad7052e0f40ac682a706520b35d6a83bd13fc10bc23382970825611c14a82a859aceb1404b910e045e0aa814281080006ec5c02285c90b880ca000102b10bd016d000182cf0eb0000000058470572eba820a82a70b940820000871c214b3030000000000060b31d6b028675880008faa0000000045cdd6a00007ba800000000001052cac8416a063c077c0a1c2120002758eeba4142bac400000a181b183bc00000008155811000020ac1ed3836205541acc2e503bd06c4ec510f4000175ae0cd1d6300df07dcf7a814382c489a6ef2000002d676d2ece805202a90554159b27a02cd052f028c14b03ba05ae01e9ceebba20ace0b3419402940007023000182840000ef2414a000306520a5d001829740540851db405b40000eba069e8e0c000000046480003052a077c39982e00508000c3c03bfd0b6c1020853036d026c0ca44e683340002039dddd498516680000166815e027c0b5414a113800060e21dfe000205980008155415577580a5dd7581c10b2aeeb82db028408580a1000000000000f198359392f050e0a5814383bd758c15581420ad50b42ec30001899f75a80aec1b081f9b03e0a1dd6a0002761aee841428329077c119814b85b70010015c00a833774ee2cd422f0567033c0cdd6643dd7085e0cac03e05b106680a1c1ea829505280791d75ca33082823141958285729e068c77dae100a0cee882db040a04c40a5c3c202ab02981591dff3b4307140e281b082a806541179dd7832a06f410bc14abac705080aa9d63bac607780a141b1029705c622801c505b001460cdc8e6bb69081616dddb40296ab680cd81c4c62306c00cacfaa82950528eb5a4750296050e0bf1dc2c374081432381de0287066a0466c0ed86a02280aac154021d071631 else 0x30710b2d41de000305560ca814301800b9aee8c2e20000000208e889d01f20800114016600027088b6a0001bb740002edd00000002066800040f4032800000cd0142028705a8000c21e82cc0006eda01debac505280a15d6bbba0052c0d8816b829777440efc06702f077720aac2208864052c0ef419b83000006f7d01dd0302424e0ac414202f20668000016abda4052c03480e4833506c62af41953b171b620a1819a040a0ba20c401de0e0c052c44ec14a00033d9616f819a033675aa0ac019b036f8f980a181b182cd017a0a14142baea0b840efddbb0287054a3d547b5836e052c0a5420483011114eb501540002b03aeff416602a6082a10b801a85c805a8edd32f51ed2052e0a9864c0287729393d2262040808480cd8155840a055010541398759050ceb583680ab905980ee414b82970b840a5822d82aa0886159807facd6066e0a5f28b836dae5ae3e5e25bb74050c04341c53b5f085f10f41d53bc976eceeb42da036305c2ee8c2201f57050e0c7c142bb680810159820b81e20508edac18f030212623098155b8f207140a1019b0329066c0cdc167809105aa0a5416782cf59b61d69d6391f473b4095407182870bc00a1567a44b48c980d0414a2cd527980ca9dd6bae9054eb649dfc0c89082eeb1814bba1f24ea018c142553f06da3245dd0bad4794512d45228b3602c80a101b0041505080d8f28c90a6066e0b3dd8602f25923253863a832838c40b54159828407ec0a547cf832805560a1816302860dac0d800021f5577400ca9ee70294052ceadc0bd3e0908a6f1f814b3a820d6010581de829676e8000c194be1294b00a181b082cf07c41029d0dbc8206da0a5c01d8d522148ee8c1b68328066c0aa40c8040806540ca1c7a036f050e00b448a3cb70d120aa00298295083c0cd9c9cbb76050c0a5c85385ca78ff26142d4829477fceba82b23b6801551a41eed8295b2084519d750287059a0b380f602a8596eb36c1b0036007800c0c216034206680efc8351139050ceb5eb7b8156066a4299dd1029607ae0ef0205c98405520d8c19485b505980cd01543b68059e2cd4155832906520a582db3b))
def liveIndexShift11 (i : Nat) : Nat := 0x86403009070e0c0002e5501ad6c800058020002922b601435b9d3b810c0780510a0001a8220040000380f026005e644300e0100bc0305eab00087f5561080d87b10a1380000f01a070040001ee00c4d80c0dc0022b03f010000080001c81f5c400a02e00003000068464028020240f4df80d000dd00145f0020d83f00d0000f06aaf32080201b87c0ec0100027f1200140b03c306524008170062094a81d00800810007052e3c0400101c2f41a8090a64d02e0021560943d81204412c12b3a0260d01581402006009bb43acc94100040ba0140101e01621c1281a12a03403016006150028044ea7e0021ea0040b00080500c0180000e036000000390240140300003a1cc02805044008003d1000294018370240d00009a0040d4d30010340000f00001602c00002066090048b900400c018065260f00580b0400480300200401c0332502a2780300f010010000450000580e80003e1080083906015c000040084f00000007001000802026000070000020000333e00470c000072e204806018000084050090000140300201c764000045b80041c0380040000581d01007800011014d51788060100100080000a000000080100b400018006008028010000480001302000006009036004028016cafb809801001150f30ac00200802802018154000030000300006700036c000000100f000000370004ba800
def liveIndexValues11 (i : Nat) : Nat := (if i<1 then 0x30c700a3406308068784125e2a680f2eeb20afeae549ea00e036242ed84c10f080c94214c86507a4dd342ec86c48d990eee1b201a0283127a41454c90023a00002f28a048d7a19c230f029f0ac411e62aa02db90cc15181ec0dda1de10fc006544af0d70142c1d900a50b0e15623d8104586ea05402e9055a0019245e43a83f4ef2326700ae854694081518264817093e8127a4cf8df70476348a39f00d50386151829b853593d3110620f48640bb00fe24ce5047f54e148e4cf8dec0c25242e48483fe0bb335ac05bcd0a034a4c108600443083e156029a45d590eb4898186003d8984344819000260b1f1c6022312ca0a8e0a8e48a89fa13b712c40b30875045619b64f584360ab214d02a3b6b705c60d46a290d8e0a33ea8c24243d2915b168c2be05860cdc282c20785b39085267829bc9168b3b1ce42f2857c0b6619ae444865b0ab4205829a066d0c240d70201035613a606f029b499e235a14d06f402f105aa008227f00cda24013ea4fa491692d616c030800f80a487a9029b004a0ab046c42eccae6915c08862ff05e7013d2196445057f080a0e0c0ad0dc90a893eaa43305e5083214dc362854701ec5b74141499d0a8d1c802bf44a71c693e7c2be48b609c5222e3a983968e82119c02114110cd818e42ac02108b34036403fc99f92161564087c88b0a6e176409d85451f35242431dc96b069b22dc26a832b2d7de9fa1e7c73605ff1fd4116c5619a5205280dbc72a0a6f34222f38e2f12af5bdc714001530940aec03b15c6005521d42a305db0a6c0e7c251487791c118d646b05f190cf24580cd84e5041607ce432812c093605d400e077d90ced43c13345691ddb169a47105450b604c5833743868dc8151a485863a04c0030014b467c0298013417b044d0a6b3eaa42ac819904620502d8853792870e8016605b300f407882a300e506d9219c2a20427229006be8218559875a8b442a205368c46161e4458204038e1ed400902480b4b41301bcc756043218e035c86b900c20da49edc8e08e610f606ee86696c551b6429bc86690c88c1a4f401de1be34e94071487401d846862c905340bb10fa22ec45978a5a176829b8335077921dc328c641915b20f24a00559068411d44a7487407afca8029a046144f615101ef037606f923842ad85479408151830705e60a8e15146890537abdf2196c980234915e00b040b057e0b095d204070817147014d64576adb06ce19be4840a0a031f222435c4d3a0032179c29a00990a8e19b64578c7890cc09fe4cf90c90bb4151c31d05e403f20e801a485470a8e122a2010c6ca2a841de432c86508d6134e50381138bde334405c893f0a020a164b5017a87ab1818199463e0d7214181f486f392860f1c4ec031a8c048e2408a06b913b00f272d6c8668cda0c5c1828c76030a09d009a470b0afd127 else (if i<2 then 0x6e28255000925a23f282260bb71ff417c05440bca1568126c60f0cd8173e248866f04da07900018610b3c414d000083cd916b22d637a673808bb21d43370587006012933808423070a0e6c7120003a4680000225cd380615446825dc94300a00008309006489d80004b0886100d74151e29005e768c013664c0e80f92d4415c29a0312a2360b9c0f780a0000000080239437915800080d88d1790cb4490000b776a2ac1799b59c5420370000a41901ce03200ce40c0000002f918200010df09a5418e829be54400021610000805a883513440fe06b791581e0e1a686bb054e0cb42a200030cd6da9c43d49eb071a9a4a1f7055a8ca8347c6fb02500bb40f84309054709ea1a0c04648b60a1819b000186c30167b112ab404f028500210624c4da92d40b1005786d4a1ed5064274000093d134f822d02450c733dec2f3c5f40a6e17963ec82c00ab614d483703888ce0939c2a38e34096286f812d04af024121d32ce03b407da114036386bb90ed442643285e708e71fe02a283b9053717cc12180389a00156232f8544047c0510000d37710f327ac2ed945393d40c782a245ea0af920e01d64688904d115008d21b489ae0c086fb85590a6b1e784fc02b40a6b21dc30885590f6e133688548e10bb20f92573a77f86da01bf2cb0587020a015014905da90ce511451f8dec0dbe120035cb42a0cde14d42d8816b2190022c43d8a0c0cd4151a44581d8267922d0237053420ee124c21703c38cb5111e88785da0c24067e21059560a2f23880aa066d095535bc075c99e897014d63500e241de9156835c83700da925ac0544888933f31bc2a3c4a9a70a02fc035013388a61b1a8b3021486f409cc35d48b70550075a52385340a6e07443090e1601f8ddc2433066c00052450049c4f00a6927abcac03918dda04a043783a90a6e137c080858790ea389e43bc867933e147412f515605d492c000146840c20307c119d2c80a689bce47002b30979245036200030bcb27a84ee0000d064466c35d07150b0c09ec1ac50fa8aa11b2230b487790ce0d85b5745cb92d407a80e5887990ce2058334c8af1c4922dc10e843286e12e7628bae0d0bce15f40a005b1922d16342a3905605a607dc2a2c36b0afda05ab86c62a1e0c017c33780d08a6202041770a08902311ac16482ac0a6d20162246abb08ff456d255b75718f0042741384ef8b12102e3ae89610d6d21dc1060df30a5418442f2861212a52666800d1560bb110f28b253f94d980007d43c7d000020b7809e003793cf0dfe40bc9400689222e4b40546aa6c1b5029bc88a94430f162c149a190ce05b4288063b0a8d0fd4639c4f78ec0058e36b84c6024c1ae643bc513012800086ed44735424151243a470603553d3a37102001130dda029b04b688b637a42a3446e0311e0f071304120a6b2006362249 else 0x6129338000821e8438000124f466805d80004184013480dd07e60e9e2fcc9170bca105219814311290000033486100006179027f8194091a50b04fd109708ad22242a2800b067800))
def liveIndexShift12 (i : Nat) : Nat := 0x31820c10c41790030c2000037dc0
def liveIndexValues12 (i : Nat) : Nat := 0x43aa0e33160031b0001f000002688d00117843148008f02ea742a898139cc6406000030030263b9466c004341a0011800113a8c12003a66661e00221002054270f8701d2580062e1141d97257a400001001880039f64215a748ae7b20c210c
def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => some (284,0)
  | 7 => fun h => let v := packedAt liveIndexValues7 (((h/1)%3)*11) 11; if (v >>> 9) == (h/3)%4 then let a := v % 512; some (a % 306,a/306) else none
  | 8 => fun h => let s := packedAt liveIndexShift8 ((h % 19)*6) 6; let v := packedAt liveIndexValues8 (((h/19+s)%65)*13) 13; if (v >>> 11) == (h/1235)%4 then let a := v % 2048; some (a % 473,a/473) else none
  | 9 => fun h => let s := packedAt liveIndexShift9 ((h % 106)*9) 9; let v := packedAt liveIndexValues9 (((h/106+s)%328)*15) 15; if (v >>> 13) == (h/34768)%4 then let a := v % 8192; some (a % 754,a/754) else none
  | 10 => fun h => let s := packedAt liveIndexShift10 ((h % 665)*11) 11; let v := packedAt liveIndexValues10 (((h/665+s)%2054)*15) 15; if (v >>> 13) == (h/1365910)%4 then let a := v % 8192; some (a % 900,a/900) else none
  | 11 => fun h => let s := packedAt liveIndexShift11 ((h % 367)*11) 11; let v := packedAt liveIndexValues11 (((h/367+s)%1132)*15) 15; if (v >>> 13) == (h/415444)%4 then let a := v % 8192; some (a % 1075,a/1075) else none
  | 12 => fun h => let s := packedAt liveIndexShift12 ((h % 20)*6) 6; let v := packedAt liveIndexValues12 (((h/20+s)%76)*10) 10; if (v >>> 8) == (h/1520)%4 then let a := v % 256; some (a % 34,a/34) else none
  | _ => fun _ => none

def samples : Array (Bits × Bits) :=
  let padding : Bits := 0xffffc0000000000000000000000000000000
  #[((padding ||| 0x263d41822a2029b20f4f206ca2f0444d),0x410c996a40e08320f060068a2d00008),((padding ||| 0x1185442c1095f94588417f1bd50ec232),0x20c7302051b1630500417b134108c232),(0x8054dac8ac062613c1fc4b840214e,0x1038440fae429460211c04c49840214c),(0x802335005782813c6e7cada632a3b01,0x2786034011280803c6e34a1a23221001),(0x1869240909d1b3cc3498a18358c49ec6,0x1869240908d1b3cc3018a18158048ec6),(0x2680828afb208644e0526d85053093e9,0x3a8006495b21c444e0406d8405209341),(0x17700861144710edd10080e4af470159,0x172003492c4618c0d10080c4a6470149),(0,0),(0xd2da13c00287383b1050315a99ccb6,0x59d8b2809003380810102158984cb6)]

def symmetries : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[84,66,16,98,129,48],[98,82,16,66,49,128],[100,49,128]]

def columns : IndexTree ColumnInfo := (.fork 58 (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(0,1,332,50,7),(1,0,382,0,9),(0,2,312,69,7)]) (.leaf [(2,0,381,0,9),(2,0,2429,0,9),(1,2,312,68,6),(2,1,332,48,6)])) (.fork 3 (.leaf [(3,0,380,0,6),(0,4,369,10,7),(4,0,379,0,11)]) (.leaf [(4,0,2427,0,10),(5,0,378,0,7),(2,4,369,8,6),(4,2,312,65,6)]))) (.fork 7 (.fork 3 (.leaf [(6,0,377,0,8),(6,0,2425,0,7),(5,2,312,64,5)]) (.leaf [(7,0,376,0,5),(0,8,99,276,7),(8,0,375,0,9),(9,0,358,0,5)])) (.fork 4 (.leaf [(4,8,99,272,6),(8,4,369,2,6),(12,0,371,0,8),(13,0,354,0,4)]) (.leaf [(10,4,369,0,5),(14,0,369,0,5),(0,16,358,9,7),(16,0,367,0,11)])))) (.fork 14 (.fork 7 (.fork 3 (.leaf [(16,0,2415,0,11),(16,1,332,34,6),(17,0,366,0,8)]) (.leaf [(18,0,365,0,7),(18,1,332,32,5),(16,4,353,10,6),(20,0,355,0,7)])) (.fork 3 (.leaf [(5,16,354,8,5),(18,4,353,8,5),(24,0,359,0,8)]) (.leaf [(9,16,358,0,5),(25,0,358,0,5),(12,16,354,1,5),(20,8,99,256,5)]))) (.fork 7 (.fork 3 (.leaf [(24,4,353,2,5),(28,0,355,0,7),(0,32,94,257,7)]) (.leaf [(32,0,351,0,11),(32,0,2399,0,10),(1,32,94,256,6),(32,1,332,18,6)])) (.fork 4 (.leaf [(33,0,350,0,8),(34,0,349,0,7),(34,1,332,16,5),(35,0,348,0,5)]) (.leaf [(36,0,347,0,8),(36,0,2395,0,7),(37,0,346,0,5),(38,0,345,0,5)]))))) (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(44,0,339,0,5),(48,0,334,0,7),(17,32,78,256,5)]) (.leaf [(33,16,326,8,5),(48,1,332,2,5),(49,0,334,0,7),(0,64,61,258,7)])) (.fork 3 (.leaf [(64,0,319,0,11),(64,0,2367,0,10),(65,0,318,0,7)]) (.leaf [(2,64,61,256,6),(64,2,312,5,6),(66,0,317,0,8),(66,0,2365,0,7)]))) (.fork 7 (.fork 3 (.leaf [(65,2,312,4,5),(4,64,57,258,6),(64,4,305,10,6)]) (.leaf [(68,0,313,0,7),(6,64,57,256,5),(66,4,305,8,5),(68,2,312,1,5)])) (.fork 4 (.leaf [(70,0,313,0,7),(70,0,2361,0,6),(72,4,305,2,5),(32,64,29,258,6)]) (.leaf [(64,32,30,257,6),(65,32,30,256,5),(34,64,29,256,5),(0,256,23,104,7)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(256,0,127,0,9),(256,0,2175,0,9),(258,0,61,0,5)]) (.leaf [(262,0,57,0,4),(8,256,23,96,6),(256,8,99,20,6),(260,8,99,16,5)])) (.fork 4 (.leaf [(272,8,99,4,5),(32,256,23,72,6),(256,32,94,1,6),(288,0,95,0,8)]) (.leaf [(288,0,2143,0,7),(257,32,94,0,5),(40,256,23,64,5),(272,32,78,1,5)]))) (.fork 7 (.fork 3 (.leaf [(304,0,79,0,5),(64,256,23,40,6),(256,64,61,2,6)]) (.leaf [(320,0,63,0,8),(320,0,2111,0,7),(321,0,30,0,4),(258,64,61,0,5)])) (.fork 4 (.leaf [(322,0,61,0,5),(260,64,57,2,5),(72,256,23,32,5),(96,256,23,8,5)]) (.leaf [(288,64,29,2,5),(320,32,30,1,5),(352,0,31,0,7),(352,0,2079,0,6)]))))))

def forest : Forest := ⟨2431,12,fun j => samples[j]?.getD (0,0),columns,symmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem geom : graphValid forest (boundsBefore entries255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel, by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b6at0 : block forest 6 0 1=true := quickBlock 7 0 0

theorem all6 : block forest 6 0 1=true := b6at0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b7at0 : block forest 7 0 2=true := quickBlock 8 0 0

theorem all7 : block forest 7 0 2=true := b7at0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b8at0 : block forest 8 0 3=true := quickBlock 7 0 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b8at3 : block forest 8 3 22=true := quickBlock 8 0 3

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b8at25 : block forest 8 25 5=true := quickBlock 9 0 1

theorem all8 : block forest 8 0 30=true := (@block_merge forest 8 0 3 27 b8at0 (@block_merge forest 8 3 22 5 b8at3 b8at25))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b9at0 : block forest 9 0 15=true := quickBlock 8 0 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b9at15 : block forest 9 15 127=true := quickBlock 9 0 5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b9at142 : block forest 9 142 17=true := quickBlock 10 0 3

theorem all9 : block forest 9 0 159=true := (@block_merge forest 9 0 15 144 b9at0 (@block_merge forest 9 15 127 17 b9at15 b9at142))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b10at0 : block forest 10 0 3=true := quickBlock 8 0 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b10at3 : block forest 10 3 106=true := quickBlock 9 0 5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b10at109 : block forest 10 109 168=true := quickBlock 10 0 6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b10at277 : block forest 10 277 35=true := quickBlock 10 0 4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b10at312 : block forest 10 312 19=true := quickBlock 11 0 3

theorem all10 : block forest 10 0 331=true := (@block_merge forest 10 0 109 222 (@block_merge forest 10 0 3 106 b10at0 b10at3) (@block_merge forest 10 109 168 54 b10at109 (@block_merge forest 10 277 35 19 b10at277 b10at312)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b11at0 : block forest 11 0 12=true := quickBlock 9 0 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b11at12 : block forest 11 12 22=true := quickBlock 10 0 3

theorem all11 : block forest 11 0 34=true := (@block_merge forest 11 0 12 22 b11at0 b11at12)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b12at0 : block forest 12 0 1=true := quickBlock 9 0 0

theorem all12 : block forest 12 0 1=true := b12at0

theorem tables : checkedTables forest 12 := by
  intro j hj
  interval_cases j
  · exact (rfl : block forest 0 0 0=true)
  · exact (rfl : block forest 1 0 0=true)
  · exact (rfl : block forest 2 0 0=true)
  · exact (rfl : block forest 3 0 0=true)
  · exact (rfl : block forest 4 0 0=true)
  · exact (rfl : block forest 5 0 0=true)
  · exact all6
  · exact all7
  · exact all8
  · exact all9
  · exact all10
  · exact all11
  · exact all12

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2431) 12 (vars 2431).toFinset :=
  root_index (g:=forest) (before_sound _ sound255) geom tables (k:=12) (by decide) (i:=0) (by decide +kernel)

end Free383

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound383 : Lower (vars 2431) (graphGoal 2431) 13 :=
  augmentedGraph (k:=12) (m:=383) (hints:=37778967927007943852554) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 383 p bank hr ha)) (by decide +kernel) (by decide +kernel) Free383.noRun

def entries383 := extendKnown entries255 13 [(2431,[]),(2495,[118, 130, 81])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound383 : Known entries383 := extendKnown_ok sound255 seededBound383 (by decide +kernel)
namespace Free495

def data9 (i : Nat) : Nat := 0x10b0d809002405c020008c0e00900c306005406009201701201860600b881602201e306e0b00b8052033e360247c900b805c00407607c405c03081b81700c306e0bb9271b03005d0600c61601b002c1b82ae49c6c0ba0c0180240326aea22628c60b7c1f07c1ca66573509274310c430e61a000a7f5e8825c530aef5288250530afd4688250530afe5e88448130afe4688448130bbe5a87448130bde5687448130bf64e87448130fe650d4248130ef650d8148130ff45c53148130ff250d2148130d7e5c57948130b7e5e81948130bde5681948130bee5281948130bf64e81948130fe250d4248130ff04c52148130

def data10 (i : Nat) : Nat := 0x2490dc1886103705e0c43081f8709604b920458dc360ba18062c421003e09825c931b86c170441002401686a18a58160430d83204a0380d4270841e05c0c38761304a1083b8d80670fb24c6d0c26498d82e86018510f240731b05c0c02807406c96052108240621604a0390c02105c0528761d06a1a64810e360be00910c2105f0026498d82f8580a505c1402405c00a1a86615e480fe360b02006616a0dc2f08c1805ca1b8580881900153d0b0160440c286e1a86617e48116368d82208012bc931b05c110380c82ce1b85811822061541094170330b285e1182e0700c00193d0b017c2c8160500f82f8580060dc320bc29c90210831b04c0d8300cc2e05c01e1d86c1664810026061c430c826c902005c0c01901905a15e4810020061c3b0a724c6c1a04f0b02404c0141a85e1505392040099c370d42708017286e1a85f92040510c3c0dc29c9022c6c17c2c03c0161b864180418580c60dc300806200781785b926378581203e00a0d0320b02005413306e160400b90370b0200548966480ee368b01985e0084f3244300c42c01326a1ae4910637858058021354b3240771b0330bc01098649106360b6160160084b31b4310b0180132581664910637858058021410dc350b32408b1b05c16c2d41ac599263706616001c30c6c170400c000d166498d82d066170580080dc2f0b32408b1b060170580c42c0b01a00001e18057926360bc180661680dc2cc9023c6c160470b02521b8559203f8d82e088180480ca0af2407f1b05e0c0330b445992637066170580070dc33c9023c6c170470b02d392637060198580d001e4692078ca443617106d8113fd5f7cf6978a3b75cfce5170d378daf4d4368633558c4c175f02ea5676b6859dabe94bea144dfa5d12168c0444a148fbe79e3bd9c48da26a435219dcc445e12c614dc9c44a12260f8c730357181099c4241b30a503d415404b0007ff509714c3ffae4a0a61bfe885c530dfec12e2986ff209714c37fb02b8a61bfd895c530dfe44ae2986ffa21414c37fb04a0a61bfc8250530dfec0a82987fd5c5414c37fb12a0a61bfc8950530fee9ca82987fe5d1204c3ff0e890261ff97248130ffca1240987fe5c5204c3ff28290261ff92148130ffcbca40987fe525204c3ff09290261ff91948130ffc0ca40984ffa65814c27faf240a613fd49205309fe94902984ff625714c27fb1238a616fd691c530bfc848e2984ff625414c27fb1220a617dd39105309fec4a42984ff624214c2efab210a617bd4908530bfc84842986fd61e114c37e90f08a61df67784530dfac2422987ed912114c37e90508a61fe62284530dfcc3a409877e9dd204c37f10890261fba4448130feca1a40987fa509204c37f30290261fd93148130ff490a40987fc845204c2ff2f2902617fa9948130

def data11 (i : Nat) : Nat := 0x7a3716490451b0b8581900510459241046c361686032170058dc6b241005ca35180b248208d85e180c85c0163010036160428d459241046c2d0c0642e00a1b8b0401720d459241005c2c0d0642d235164903b1b0b030e3516490411b0b42e0089208018002490411b8642e000038b2491b0642c166d2ee3ac64985db863d393d4a81fc3b003ff60530ffd714c3ff1c530ffd414c3ff10530ffd214c3ff08530ffe114c2ffa2130bfd814c2ff20530ff6114c3fe48130

def data12 (i : Nat) : Nat := 0x2436305802ffd30

def liveLevels : Nat → Packing
  | 9 => (19,4,7,0,0,10,0,data9)
  | 10 => (63,3,7,0,0,13,0,data10)
  | 11 => (13,2,7,0,0,10,0,data11)
  | 12 => (1,1,6,0,0,0,0,data12)
  | _ => emptyPacking

def liveIndexShift9 (i : Nat) : Nat := 0x112603c901c180140
def liveIndexValues9 (i : Nat) : Nat := 0x268bd381229cc53e0000000000005c0a5f0300a885021801407284b03600af0d8000c5081100000028244017c9fcfd41c80152fb0058028bb9efd0b4
def liveIndexShift10 (i : Nat) : Nat := 0x14052e93c064c2c85d20213c808c80b0680006160000538d1001240209350040200005d5ba1204060220002000b2237d8553c14128240015308041206010005c02000001c001a0088201238800c000600000036f83822050087c00d407256d2030301c0817008a018004baa09a01980240b10150300008076200401000100400008240002004101a00000301005068440002008040002
def liveIndexValues10 (i : Nat) : Nat := 0xc3023a580f90cc80fb3344063018cb612f1c0628c940015f080fb946016d67ec0335bdc3338c996e33250333317013203e406500141300d596f00000003249176703e484805782050c38e8f03e4b5c015406005b01308a3809f081176c04c0002018c3333a58303018c30e0c0c2040000001015833000dc2075f2006304157c10560003002cc9607d033384049590cc00610cc0130317833005698cc0184e7101883300cc024301883330cccbd70180062019467e3174055018c133019c3020b340fa1a1a32705e0e958cb40608e198ce01881310814c9700fd7291d2ca388c9c15b0c400012f1c1f8000c2048c9015828fc062081e7bf03e41338cb018e5f002055f30003004830e00882065f20da4633c130041000135a00010f400f894e000304c830108100030b8c18e8c9000032f8bc601e435831768b028b0106922c0f800000000000000000000208181640158c5f6610003317000302e02150560000000813000080540008b410568691672c014000059124b804605b80400cc628d5c7a2e4000815b019cc5e018c062018c0f80564e2201816e703e00025fe4104000d6ee961000103e0c5f0b8c0fb01840615c980fb018172801801040c322753174332b16c0a701557c0018813104199fb081016c0c3d59e0818c5e018c06303ed1e901749ea27c42ec0004a2a00640f8000c1050560003018868104a01980000064019433000000002f2c33028c80485cb83330cc0207081c2bf03e80f800000630074b7c000e3300008e9724b00015be238400900000005984000c1300009834000e2720d5a26e5ca80b8000c21709700550ccd8cc015c10289300012d700fa0cc42ee8b9806103e572901797fb03e00f8000000303e0bb901c42bf00a98ce081810400080556338a2e0af0002081983400080630af000001500fb8e6000005b021400000608c9415b564030db1680f800040fa03e0e9401500390bbd7c30ca02cd03e016c027c2050c301052884065003410201780fa03ecba18a0416f0afc33200b4bcb5fe806103e06242e6c1300c000f9056c0fa676c0600bbc0652e7554e0c0830304041598c9c055018cbb8027182f2ee809f5c940ea0af00f95ca0103027
def liveIndexShift11 (i : Nat) : Nat := 0x1c000ca3012000041d0028da2010002800bf59820103f109bc7400128985200158ce64000735400103c0ccd0268e0180a00013cc00dc0982c20230c96086161745840176e802602a0004c000010854030d0100008000185022002104c4800030618619618320041000ac2e9d000f00819140240009
def liveIndexValues11 (i : Nat) : Nat := 0x2800d8000d9a3240a71f40b00029a18b4235baef26a8000232501055f78106360c1079915d949c9267b446edd7a848a840f819aa0ef005e0264d3502241e1012891300659dc000810401300000006582354c0b203000016eb505c77f411104400bd0f8236666c0b619c7e5c808543bc1214a6e989caf13288a6e688170100108ff07f03e340b6621a4925c00ecc1aa1279039020c03901040cf019a570039c00c01d0e90bf4049e06a83bc018d9fc678e66196aa1f602101126aa03e063f56e832e43b004459d0681820a03b43bd6bd01122d903e336300450f8c3b203103e338981a90f82924985cd9301cdaa8a4c1a0a2d9994203e96f572a48660f8c8c3bb941b00ad0d4406a4096007810c01bc8c25378a7b65983bf04156d936044d4681850606c806a03d01ab0d86e360411b0c3605a09681d7bd99e1f45041007e4408e906828e8434c192636081053536a48917c05172a668119400034600d8f04427548fae71f9c703b329c59af00dc64d06a59c3b8d810c06a193e57b80e0004c5c10f8669e992c0a400b665c2d9ea10679c02499e403e002267840b808f04ac3b3043c10431e012906a4d8c034d57e008692703aa8d699e88616828105a4c8058348009206a17e12440104085c10602acc9d02b885906c5c58015c014a4401a90ef102c00a9a23035efee0f8463a01eca5e0ecaa7b3898112127839f648c0f300c667b027d53c127cd2b02d40df0ec0e252d74d4a72d01120452678971a58d25c88c39c9c3e1032497f3899aa202e
def liveIndexShift12 (i : Nat) : Nat := 0x1035011030000b2e041
def liveIndexValues12 (i : Nat) : Nat := 0x4900006300000057c75400001c1f00000053888eca0000854c00990067004600000000000000000000290000002c049b0000000000330000cde60000d20040820000180000eac100680000509d8b9a8f03e2
def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 9 => fun h => let s := packedAt liveIndexShift9 ((h % 11)*6) 6; let v := packedAt liveIndexValues9 (((h/11+s)%38)*13) 13; if (v >>> 11) == (h/418)%4 then let a := v % 2048; some (a % 617,a/617) else none
  | 10 => fun h => let s := packedAt liveIndexShift10 ((h % 134)*9) 9; let v := packedAt liveIndexValues10 (((h/134+s)%458)*14) 14; if (v >>> 12) == (h/61372)%4 then let a := v % 4096; some (a % 729,a/729) else none
  | 11 => fun h => let s := packedAt liveIndexShift11 ((h % 104)*9) 9; let v := packedAt liveIndexValues11 (((h/104+s)%319)*14) 14; if (v >>> 12) == (h/33176)%4 then let a := v % 4096; some (a % 799,a/799) else none
  | 12 => fun h => let s := packedAt liveIndexShift12 ((h % 13)*6) 6; let v := packedAt liveIndexValues12 (((h/13+s)%83)*8) 8; if (v >>> 6) == (h/1079)%4 then let a := v % 64; some (a % 13,a/13) else none
  | _ => fun _ => none

def samples : Array (Bits × Bits) :=
  let padding : Bits := 0xfffffffffffffffc00000000000000000000
  #[((padding ||| 0x417a04282aefd004f00a),0x91e8c3282a225000a00a),((padding ||| 0x21a742042c6c963df1b36),0x81228c2c4c903071334),(0x9881006d1b229e51eac0,0x351c9102013229c50e8c0),(0x220343036c65030f006b,0x2e1607032c45030f0023),(0,0),(0x1448e3df3b54c8bfa60c5,0x62071443954c8bf84041),(0x263459037393634b84550,0x263459035393624b84040),(0x8c10ab9c54116423973a,0x8c10ab9c40116003173a),(0x1b188d288c3925900bebd,0x190a8608842805000be9c)]

def symmetries : Array (List Nat) := #[[],[118,130,81],[82,129,48],[118,133,33,48],[133,115,96],[48,33,115,82,129,96],[48,33,99,130,81,112],[99,33,112]]

def columns : IndexTree ColumnInfo := (.fork 34 (.fork 17 (.fork 8 (.fork 4 (.leaf [(1,0,494,0,11),(2,0,493,0,9),(2,0,2541,0,9),(1,2,424,68,6)]) (.leaf [(2,1,460,32,6),(3,0,492,0,8),(5,0,490,0,7),(2,4,353,136,6)])) (.fork 4 (.leaf [(4,2,424,65,6),(5,2,424,64,5),(0,8,227,260,7),(8,0,487,0,11)]) (.fork 2 (.leaf [(9,0,486,0,8),(11,0,484,0,5)]) (.leaf [(4,8,227,256,6),(8,4,353,130,6),(13,0,482,0,5)])))) (.fork 8 (.fork 4 (.leaf [(10,4,353,128,5),(0,32,78,385,7),(32,0,462,0,8),(1,32,78,384,6)]) (.leaf [(32,1,460,2,6),(33,0,462,0,8),(34,1,460,0,5),(40,0,455,0,7)])) (.fork 4 (.leaf [(41,0,454,0,5),(64,0,431,0,11),(64,0,2479,0,11),(64,2,424,5,6)]) (.fork 2 (.leaf [(66,0,429,0,8),(66,0,2477,0,8)]) (.leaf [(66,1,396,32,5),(67,0,428,0,7),(68,2,424,1,5)]))))) (.fork 17 (.fork 8 (.fork 4 (.leaf [(68,8,163,256,5),(96,1,396,2,5),(128,0,2415,0,11),(128,1,332,34,6)]) (.leaf [(130,0,365,0,7),(130,0,2413,0,7),(130,1,332,32,5),(132,0,355,0,7)])) (.fork 4 (.leaf [(132,8,99,256,5),(136,4,353,2,5),(140,0,355,0,7),(160,0,334,0,7)]) (.fork 2 (.leaf [(129,32,78,256,5),(160,1,332,2,5)]) (.leaf [(161,0,334,0,7),(0,256,135,104,7),(256,0,231,0,8)])))) (.fork 8 (.fork 4 (.leaf [(8,256,135,96,6),(256,8,227,4,6),(264,0,231,0,8),(265,0,230,0,5)]) (.leaf [(260,8,227,0,5),(32,256,135,72,6),(256,32,78,129,6),(257,32,78,128,5)])) (.fork 4 (.leaf [(40,256,135,64,5),(320,0,175,0,8),(320,0,2223,0,8),(258,64,173,0,5)]) (.fork 2 (.leaf [(322,0,173,0,5),(320,8,163,4,5)]) (.leaf [(328,0,167,0,7),(96,256,135,8,5),(384,32,78,1,5)]))))))

def forest : Forest := ⟨2543,12,fun j => samples[j]?.getD (0,0),columns,symmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem geom : graphValid forest (boundsBefore entries383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel, by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b9at0 : block forest 9 0 2=true := quickBlock 8 0 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b9at2 : block forest 9 2 17=true := quickBlock 9 0 3

theorem all9 : block forest 9 0 19=true := (@block_merge forest 9 0 2 17 b9at0 b9at2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b10at0 : block forest 10 0 35=true := quickBlock 9 0 4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b10at35 : block forest 10 35 26=true := quickBlock 10 0 3

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b10at61 : block forest 10 61 2=true := quickBlock 11 0 0

theorem all10 : block forest 10 0 63=true := (@block_merge forest 10 0 35 28 b10at0 (@block_merge forest 10 35 26 2 b10at35 b10at61))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b11at0 : block forest 11 0 5=true := quickBlock 9 0 1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b11at5 : block forest 11 5 8=true := quickBlock 10 0 1

theorem all11 : block forest 11 0 13=true := (@block_merge forest 11 0 5 8 b11at0 b11at5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b12at0 : block forest 12 0 1=true := quickBlock 9 0 0

theorem all12 : block forest 12 0 1=true := b12at0

theorem tables : checkedTables forest 12 := by
  intro j hj
  interval_cases j
  · exact (rfl : block forest 0 0 0=true)
  · exact (rfl : block forest 1 0 0=true)
  · exact (rfl : block forest 2 0 0=true)
  · exact (rfl : block forest 3 0 0=true)
  · exact (rfl : block forest 4 0 0=true)
  · exact (rfl : block forest 5 0 0=true)
  · exact (rfl : block forest 6 0 0=true)
  · exact (rfl : block forest 7 0 0=true)
  · exact (rfl : block forest 8 0 0=true)
  · exact all9
  · exact all10
  · exact all11
  · exact all12

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2543) 12 (vars 2543).toFinset :=
  root_index (g:=forest) (before_sound _ sound383) geom tables (k:=12) (by decide) (i:=0) (by decide +kernel)

end Free495

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seededBound495 : Lower (vars 2543) (graphGoal 2543) 13 :=
  augmentedGraph (k:=12) (m:=495) (hints:=37815861415086643479050) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun p bank hr ha => Nat.le_trans (by decide +kernel) (before_sound _ valid383 495 p bank hr ha)) (by decide +kernel) (by decide +kernel) Free495.noRun

def entries495 := extendKnown entries383 13 [(2543,[])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sound495 : Known entries495 := extendKnown_ok sound383 seededBound495 (by decide +kernel)
namespace Free511

def data14 (i : Nat) : Nat := 0x13066230d03e130480c029ffd30

def data13 (i : Nat) : Nat := 0x4c8e3330992306a1743e09802a264719984c918350be1f07e138057330981743e0094b62d0719984c918460d6340be1f84e09805c5494c4cccc2643e0700e82669821266132460be1f84c0a82601005a549082643f0981c039c99a60719984c918358d02f87e1303a01696c448e22643e0c80e72d8991c666130358d02f87e1304c0e01da4cd3038ccc2648c1ac68170440981301b4b4a60719984f918358d02e08813824036930384cc25c8c1a05c1143f0982700b0981c266132460d21f07a1380554c4cc2648d1a43f09c1300802a1c66691a1f84c13024f4c4cd234681704409c1301a76164fc3161e994ab8c0f65c73075007e4be11315417c007ffa6530ffec8a61ffc914c3ffb02987ff20530ffea8a61ffc514c3ffa42987ff08530fff08a61ffd204c3ffa20985ffa6530bfec8a61ff6114c3ff240987fe80130

def n12f3 (i : Nat) : Nat := 0x2aaa66889563388a1166998655926458a61583609816017a5a95a54d525454a4e9324c52a485204690a26898254922448a214822045a148510e82a0680a
def n12r (i : Nat) : Nat := 0x69a56e968bf3db00d468fb09adcd069b3c1a83da60c3bd6c7e65acf31699e158e795682e95a6f3d6dbd758775160ec25b17416eff059a785471ef4a1b9d232cd4af38d287e5489365200e949573d304dc4873192ccd04adbc1260e341cf250f6e338bb84e05da381ba0cfbee31c39ccf1e3310324cd5ed319f6cc62e1311368c54e533c780c03c733ab64c89c433e754c53d33283a8c98e4332b28ce5dc325f18ce7d733c344cfdc1339bc0cf3e3285388a84db29bb84a15da283358a72e02a4b64abfd52ba74cab5c1235390664ca1aab70663c61b3b50663c21acbc0647ef79d2a1e316778b199e08707846a1cc06772f599ca76472be71cd0947346a5a3cb0681ebd828a6622da588c94626a418ebaf580a99612655841a562169588a3d6f4575965016b470585abd465a652b5a5476975246514cb90535abd201a7488d952176948e9a523b9c4976c120baf41269d0946942767109e9043caa043fce13139c43de3107b244c6cc130b8441fc8130f68413c512af284c1c6137b084e1ef3836a0e2d6e39069ce466d390a98e196b390e64e389339a2bc278e8089b382feee0a039c218cd0aef8c261c90b4bb424fe1095f9422bcb0aeb8024dc70ab36424cc40b774c26bea09b73c2e8e4092f28290dc08a7182a6d70b4f4422ac10a3fc020fef316ea0c276e30d29cc456d30d66cc589a317aacc85a5314154c77533221a8c1a9f302aa4cbe64317e0ccf8703012bca4aa828cdb8a1ba729a9b4a369b2a5698a516b28de64a81952bdd7ca25922826a4acd64292270a75972a7e50a52b0296a8407fc80367580cfeb022b8004ed9019b540b0d301bf609085123f2621023019e695d0e296aa43db0d296320798e218641c418f5295a4c3d6d72953245d501294aa03d30c2943b8750df1c43806110b104380bc420a811f5b847aa711f9b447ba61171ac47c8f12c50c506653a703cf0a2f0adeb82a5ad0a8e6c2b98c0c26682a2ab0bfe942e3550b614c2a16a0a92902ec830be9c02b8a92bb4bc0e4ac0416980966b0236940ae550369a808e98240c
def n12g (i : Nat) : Nat := 0x63b0a18ec1c63b0418ec0463afe18ebec63af8212bd084af0212bb084ae8212b9084ae0212b70a5ad7296b48a5acd296b20c6ac231aaf0c6ab631aac0c6aaa31aa90c6a9e31aa60c6a9231aa30e7a8539e9f8e7a7739e9c0e7a6939e988e7a5b39e950e7a4d39e918e7a3f39e8e0e7a3139e8a8e7a2339e870e7a1539e838e7a0739e800e79f939e7c8e79eb39e790e79dd39e758e79cf39e720e79c14226e5089b14226a5089a142266508991422625089814225e5089714225a50896142256508951422525089414224e5089314224a50892142246508911422425089014223e5088f14223a5088e1422365088d1422325088c14222e5298b04a629d2989e4a62552988c4a620d2987a4a61c5298684a617d298564a6135298444a60ed298324a60a5298204a605d2980e4a6015297fc529fc94a7e8529f794a7d4529f294a7c0529ed94a7ac529e894a798529e394a784529de94a770529d994a75c529d494a748529cf96b7335adca16b71d5adc496b7075adbf16b6f15adb996b6db5adb416b6c55adae96b6af5ada916b6995ada396b6835ad9e16b66d5ad9896b6575ad9316b6415ad8d98c62a6318798c6126318198c5fa6317b98c5e26317598c5ca6316f98c5b26316998c59a6316398c5826315d98c56a6315798c5526315198c53a6314b98c5226314598c50a6313f98c4f26313998c4da631339ad4c16b52d1ad4a76b5269ad48d6b5201ad4736b5199ad4596b5131ad43f6b50c9ad4256b5061ad40b6b4ff9ad3f16b4f91ad3d76b4f29ad3bd6b4ec1ad3a36b4e59ad3896b4df1ad36f6b4d89ad3556b4d21ad33b6b4cb9ad3216b4c51ad307738be5ce2eb738b75ce2cf738b05ce2b3738a95ce297738a25ce27b7389b5ce25f738945ce2437388d5ce227738865ce20b7387f5ce1ef738785ce1d3738715ce1b77386a5ce19b7bc631ef17d7bc5b9ef15f7bc541ef1417bc4c9ef1237bc451ef1057bc3d9ef0e784035e100c78402de100a784025e100878401de310668c4156310448c40ce310228c404631000
def n12q (i : Nat) : Nat := (if i<1 then 0x497380f0d710b6719091504122e970f4a1b7d0b612718081524463e5a4b391d30180817152435233e3d0f2a580b192536044c2322203d0f6c1b0b19093604122383200e961b0b191725360412235420631d520b194f18152423222d8e0e580b931918410614047812111095580b940a184116041234110e6c0b93191806140478126e11440f300b7618082f0604123e1144330d0b7618080604122e3e11101d920b4d185c0412212e3e111f4491900b1a1808361604345b100e8f580b0a2f06050412030048321c0b5018172507242322684832520b5018090724232e3f680f32520b1918410724232d8e685a4b2a290b18250724233e8e684b0e528d1b0b1a8c1808171405246d0e431b0b664d1918412f1479044b441b580b0a1808174115048b788a75440f3b3a0b271908067904354089886d580b87661808411604218663851b0b190807068405044c83822c710b6719090817158180042e440f0e0d580b420a18081504782e440e300b6649180841144604232e0e6c0b474918085c1e043512222d0e300b49187f08411e0435122e2d39447e0f560b55190816140504545a4b1b7d0b18087c171524464e3e5a44300b66180841144604232e694b0e4a1b0b4718081714054620626d0e7b0c0b0a7a41147904780277100f6c1b0b1a19182f15045d12114433300b76661808170604123e11755f74710b731808177204123e1110710b0a18700614050412343e11105a580b18412516041234022011105a6f6c0b182f1604126e3f20115a596d580b5766180908061e21005a326c300b1a1816046b120111006a101b0b501817250724233f54680f322a290b271825072423226968380f0c300b67190908171504352322440e300b664918084115144604232e100f1d2a0c0b0a140565045d4c21643332300b0a180908172f1504123f3e104b442a580b471825152423224e6263520b614f1809152423222e3f4e620e323b580b511a0a184116041202115f0f2a580b5519180815045d1202114433300b6160180807140504123e115f0f5e1b0b0a081405045d1221035b0e1c0b491808415c46043512222d5b5a590d580b57180908160412211100380f1b560b55190817161505044c1254480e32533b520b51504f18152423224e3332300b4d0a182f2515044c22032e3e4b0e4a1b300b49180817411546342d3e4832300b472718081725144623224520440f0e43300b420a180817411504121140100f33300b0a182f251504123f3e112c3d0f3c3b3a0b3719082f3606050435233938332a0c0b3719082536060504352334333231300b0a18082f2515072412222e2d2c2b2a29280b27182608251524232221201f0f1b0b1a19180908171615141e041211100f1d1c1b0b1a19181716151413041211100f0e0d0c0b0a09080706050403020100 else (if i<2 then 0x2297206844338d7b300b0a2f152410331d300a08140504a9b733300a7f2f0504aba910710b0a701405045d12b60e580b87a6180804ae5f3944330d0b0a1504224458304d1806140434212b0ea7490814057922020e323028607f0714242d4a580b73187c1424a94e48520b47180914242e4e44381b7d671909ac0497b52ab40bb31918041211388daf0b0a091405225b5f44330d0a1e054c02685a39449b310b042202680b4908b204359d030268320b2718250724233f6832580b18250724a98e689b338d300b0a2fac0504abad440f0c0b1909087904350e323b58b127187c1524a90f32293a0b271808142423320b276018082507142422866391900bb018361604229f5a1c0b471841061404220f321d3019181714242322a38da80b662718142434222c8933af3a0b184116046e0e43af0b0a082f1404ae6e32520b4718090714243f4e5a39449b300b4115042d695a580b187c251524a94e8e106c0b1a182f045d123e115a33710b1870045d123e1132580b1918250412022011326c0b19182f04123f20110e330b19182504123f2011ada50b19181404124e2011440e300b491808411404680f2a0b271808142421a16844330d0aac0504ab1202aa4b32300b18090798243faa48440e1b580b0a18081741156f3944537b1b2719080679046d0e8d1c0b662718171424348a9544532a601906050435349f6a2c2b5a638d290b1524220e32580b27187c251524a922a30e8da80b662718142434220e300b49084115043523342210958d580b0a1841061334215a304d18415c1446044c2203104852a70b1a18091405242e590e8f0d0b93a6180804346e100e6c710b0a250605044c02630e1d52477f0841142423020e32520b2718091524236e3f38a52a37197f0614050412545a448d580ba4871841042197440e8d580ba4871841042197a30e520b476618142434223e5a6c1b0b1815041223022d690e320c4d412516044c2202200e0d1b0b0a1808250798248e321d520b471808071424648e3332996c1b0b19181504121110580b671870045d12023e110f4a521b0b1a19180817145b33321c0b4727092f0705225b750ba21809081704213e11000f520b471918081424a12e685a39443018411504353469682c3d533b300b510a18a03616049f0e439e0b664d1808411665045a0f3253301918082f152435236d0e7b310b2718081714249d3433320d0b4727180825079824229c48521c0b47180817140524220f4a2a7d0b2718087c152446210e531d6c4918081581042334022b9b0e520b2718262515246e3f5a1b300b49182641150412232d0e1b300b49180841150412232d0e6c0b49187f081e0435122e2d100f521b0b471a19180817145444381c1b551908161405049a545a990b18082f25079824023f4e5a448d580b661841140565 else 0xb0a15100b14711a14300a140b0a143018140b18c5330b0a140b0a061e0b1814240c4d06040b18abc50b18c7c50d0a044e2c0b18160430181404a95a1b0b143432ce7f2422cfa50b49181482304f081524310b18141e22636c277f0522311814b234220b0a081405212c39530804204bc80b0504208f550906040032ce08b2a9681030470a0906059f0e304f0815246d0e284f081524b60ba6180908135f300a0504c7a9c91dcd0b0a24345a1b0b180412be1f4b9b8d0b05225aa708140579220e8d0b271424229b301808141ea16331470814b2022ba7600814b2025a636d31b222024a520b271814450b491804122e6482c8331d0a044e103b580a044c4e101d300a04a94ecc1d300a04a94e106c0a0412034e6c4904352322972c443b581804200b18081604c5000b27181424be685a635824a922680b491804be2e680b5518cb14ca68630d0a060522aa6a5a1d52bc7f081444380b1a49097a14440e30491808411e5a39449b1d6c0804330c300b0a2f140433300b0a082f14040e520b27181424a95fa56c18097a04121071af0b0a0905346f0c4d7a41044c225f330d0a15044c220e2847071479242dc90d0a0504c71264c833a50b0a04c74e0b18081604c5344e5aba3b6c092f0420325855180804c6205a380b0604c534205a3b58044c22022058180604340302205a6fba710b044e2040710b190908155b10af0b0a0908055bc43018087c1e225b386c0b1a1915975bc36c0d1806140400536c1808140434680b490814353422680ba2184104be2e681b0b180412be5b680b1815042e645b6832c20b18251322aa100b0a0905225baa0bc12718087c1506130e580b8718081404ae44b90c5818c0810421103a0b0a7006bf04035a520b1814249dbe6e2c333a0b0a2f1404024a920b27187c14244538bd2a19bc043522975a449b0b0804352269bb58180941044c0220405a5f44bab90b041148a50bb319180412111f1b0bb31918041211380c0b55190815b85b1d6c471804122202685a1b0b180412232d681b0b49180412232d680b18410412232e2d681d6c0b1814041264680b4918140412036468321d301824))
def n12v (i : Nat) : Nat := 0xe7f3b9bcce5f2b93c8e3f1b8bc4e1f0b83c0dfefb7bbcddeeb73b8dbedb6bb4d9ecb63b0d7ebb5bacd5eab53a8d3e9b4ba4d1e8b43a0cfe7b3b9ccde6b3398cbe5b2b94c9e4b2390c7e3b1b8cc5e2b1388c3e1b0b84c1e0b0380bfdfafb7cbddeaf378bbddaeb74b9dcae370b7dbadb6cb5daad368b3d9acb64b1d8ac360afd7abb5cadd6ab358abd5aab54a9d4aa350a7d3a9b4ca5d2a9348a3d1a8b44a1d0a83409fcfa7b3c9dcea73389bcda6b3499cca633097cba5b2c95caa532893c9a4b2491c8a43208fc7a3b1c8dc6a33188bc5a2b1489c4a231087c3a1b0c85c2a130883c1a0b0481c0a0300
def n12p (i : Nat) : Nat := 0x1662503e0b106800c4c0a603c05c0a2b3182244b203b04804c49040580a804e80c14a31c6106d0b20a1294520e80485f03003e0000c8770d81444585f15b96805c4618a1e80a8b81410644802d00d1d45604d0bc9f24829011180c4344f83e324538a44b4b2049c2d81c30f16c2707f280380380f20dc1321f004168550964b20ac3aa345528284fa840302f5020010ba15c1280915700c3084e15220d0f031802ad0542710c41a83240711421d3344b08e01c2981c168a61264b40c6089048a24fb1691a8b9c130125b08c5121ac5189b0ad0bc0da13133a603907106b02a048b756d2123806709e91b1a422826044080041908b44487b8e214a2664686a8bc1782e44584f008b6932a6442076ccc1301d03985c8b813e1f01c02802a01
def n12join : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,z => let e := packedAt n12v ((z % 256)*9) 9
             let b := (e >>> 8)*11
             (packedAt n12p ((e % 256)*11) b) ||| ((n12join n (z >>> 8)) <<< b)
def data12 (p : Nat) : Nat :=
  let r := packedAt n12r ((p/4)*22) 22
  let old := packedAt data13 (((r >>> 11)%32)*31+20) 11
  let op := (packedAt n12f3 (((r >>> 16)%64)*10) 10)
  let rm := (if (r % 4)%2=0 then 1 <<< (op % 16) else 0) ||| (if (r % 4)/2=0 then 1 <<< ((op >>> 4)%16) else 0)
  if p % 4=0 then (packedAt data13 (((r >>> 11)%32)*31) 20) ||| ((packedAt n12f3 (((r >>> 16)%64)*10) 10) <<< 20) else if p % 4=1 then ((old ^^^ (old &&& rm)) ||| 2048) else
    let w := packedAt n12g (((r >>> 2)%512)*22) 22
    if p % 4=2 then w >>> 17 else
      let c := ((w >>> 12)%32)
      n12join c (packedAt n12q ((w % 4096)*8) (c*8))

def n11f3 (i : Nat) : Nat := 0x2bba66889563388a116ad9b66998655926458b62985609816017b5ad5b54d525454b5293b4e9314ad2a4852046d0b2ac9b268952489122c8516c510ec2b06c0b
def n11r (i : Nat) : Nat := (if i<1 then 0x282e3416cb83e5b2e6ba38b98f5b7187034b587722d3c6a9c3cc2a7062879c136167073c4dc1360e7062ca9bfca2a6f74059bdee136f77439bdab1a2cc8a80b3859c2cf0238b3544d2cde535bb1b1b2c5ce50b16f5c2c4fa94ac9f602b0b550ad4c512b15d50abb9512ad65c8aaf6b12a65e94a93d602a35550a9125f2a646a8a9f44c2a79d0ca9a9696d55ca9b5a62a6c3fc75afe0166bfeca9abc8246a78879a9e21d6a78471a9e2166a7886d9c213124f4e58936b592461a70915fa723b75888f1a5b23c7e988f716023f7d648f619423fc56c8d1e9a23092648d10942370da88d2a6423346841106df2247640888f9f20f4a4083b881004ff5d9142241a00a706801981a1814c68048e1a40e6183070e60a2861803f165bd68c864109318ba27568861859accc86009b11782a985e6166171b19960512a581a09c5a486616ad5615c330d572e0355aeb321601a4c564e8b54770554e7018539a84d4e4c2a53278394c6d1852ac8c8540ca614a55a94241184f8f0c850039c13ec6a93437184c3e4c84c1eb11284ea04ab96712999c44813a8122e5a8484a56122659d2a4a2a4a9089c470c7111076a044bc67111a59043409310d06c8402fb10f83ac83c2eaa4853c31216c2a47a9c791f041d47c14591f050e47bf4c43a0fb00e242bc38918c46bb8311796164538c3914e7310d8369c36926f0d86ac034d2af0d34eb434d4a40d5467035529644760c033b6af0cedab433b69c0cf8e610c250d4299c3506490d40aa4c03087af0c232b4308db00bdbab42f6da40bb06702f0b930ba6e3c2dc1983ee60c42a788d0af6934f4ae133c684a8ec9d1e3b2e874ecbb183b6bc58ec4f133b1783cecbb2b3b1b8c42879b00a3120c29e4420a76dc427668d09e22bc25be9b0970a7025f5b008a0ac822e5b0084a6bc21279b0844ec01f62af07da6341e3853394dca8e0631e3816c60e0da16380e44ce0592b3815434deaa2a3738458dc56133737cc41d66af07446801ca8b106b3ac01a81af06a066c1a75a506a71701ae2b206b9250da5a31061dec018c4af063126c18c59a061eab418e68c0660d0819ce653660844d9250c364c4c416c6ad05f5a8016ec54058a1b017648c0597d0c165d7205d8e74cf321833e3458ce5c30055fabc157e9c055f690c8a61e3225074c8a61c3229860c94d16320d8c41276b0049cabc12749b0490e2413769a04ca29412cb5104c91b0127396319c460c4b11b2e0d434b3d1142c2acacacb6162930c60a23d3004226bc108890042b2c81008aa2208ca886172a208e8c408faa8022fdc008278c027d934097c661e16034797b3001a5ab80698ad01936c00480ad011fe8005569c01582c804e0941c4d4a002be70009129c02bd6f0092e6c0297ae00c8eb40246981a798305dd50c11fc060433b1b08e8c501b811803fbc else 0x8551b5e153fcb84df80e4611023a1b211d85d40685c65dc5802e685a11d85764d4d5c6b8f57752ad5dc59884cf0c95a509c83a8c3e0f20325633e845826f255cc2845619d354a962d50ca8c547350151c94b8132456027e2a80fa43202c01580370aa00af1d805186201ad16803cc3a0144157ffb0a9ff6a1553f2d554e8492538c64d4e53957f71031fd840e7f43c8454c2e114dcb85422c987e3e03df4de257befc6451b3d679ce0adde8b221301f884a16c612e67904815d612427892a14a44a84a8846dbe21106f18459ae41124fbd1bf9b045fea8837fce10badf70f78e8f3da3a34f58ca43c2b63cf0d98d3bbca58edf78f3b3faaced4a8d3afaec427d9eb09ecb342600c33a75dc02229ea08e8b302347e4088ef1c234ed608993c82378e207953181f5ce107e7b141eb4cd07caf28e6c85b399f668e61f9b3946268e519a43940a70e5a09b3881684e3775a3886234e31c9b3869268e19d9c383c2ace1f89b37d1694df7f603794a58dfc65337d9d34df684d37b6290dc34ab377b69c1d53ca07457881c2bc607697641dc7ca06b1f641b9bcd06edf6cda2aa436ba66cd94b9a3640634d9bca835cb59cd6ea5b35bb668d795a535cb150d77a5135e5190d70a9c35f963cd726b105d97841790e505ec320167cd905ac3101743d105c03b016f5cc05eab5817f3cf05e4b0416fcf205eb36cd5499a351ee94d5ba603535944d5144b356aa30d57443357796cd32e9a34a8270d2628f34e266cd148a53467d64d17051343dd8cd0f48c347a190d1bba533c5d50cf165133b318ccecda43388a3ccf33a3336726ccb349a32cea8ccad7a432dd66cc8839a3211680c92f8b3228a8cc847a43208270c8ef96326f66cc6a49a319be8cc7399c31faa3cc7b4b230a6ac8be32aa7469ca9cfa81e73c3475cf0e1673d744dcefb0f73d7839cf082b73d60a0bb5b622e8c238bb554d2ea1535caa1)
def n11g (i : Nat) : Nat := (if i<1 then 0xa3453a3155a2c55a2755a2255a1d53a1a55a1555a1055a0b55a0655a01549fd559f8559f3559ee549ea559e5519e4549e0549dc559d7549d3539d0529ce559c9559c4539c1539be549ba559b5549b1559ac559a7549a35499f5599a55995549915598c55987549835597e5397b53978559735596e559695396654962529605295e5495a5395753954539515494d54949559446693e66938669326592d6692765922629206691a64916659116590c6590766901668fb668f5668ef668e9638e6638e3648df668d9658d4658cf658ca648c6648c2638bf668b9668b3658ae668a8668a26689c66896648926488e66888668826687c63879668736486f6586a64866658616385e66858648546684e6684862846628446683e6483a64836648326682c6482863825648216681b65816658116580c6680666800667fa667f4657ef667e9647e5667df647db647d7657d2647ce657c9647c5667bf657ba727b8767b2767ac767a67779f7779873795757907678a777837777c77775757707676a777637775c767567774f7274d76747767417773a777337672d76727767217771a757157770e7770775702746fe766f8766f2736ef766e9776e2776db776d4766ce766c8746c4746c0766ba736b7766b1756ac766a6766a07669a766947768d75688746847567f7767873675756707666a766647665e77657766517764a746467763f7563a75635746317762a776237661d75618756137560e7660877601885f9875f2875eb875e4875dd875d6875cf875c8865c2885ba865b4885ac865a68859e885968858e86588845848657e86578865728756b87564845608655a855558854d855488854087539875328752b885238851b885138850b87504864fe874f7884ef874e8874e1874da874d3874cc874c5884bd874b6874af874a8884a088498864928648c884848847c874758746e86468874618745a874538644d85448854438643d864378842f87428834258841d86417844138440f8440b8440784403853fe853f9853f4883ec873e5883dd873d6873cf973c8993bf983b7983af983a79939e9739796391993889738198379973729936998361983599835198349983419733a963349932b983239831b983139630d9630796301982f9982f1982e9982e1992d8972d1982c9982c1982b9982b1942ad992a49729d982959728e982869827e99275a926ca9263a925aa8252aa248a923fa7238a922fa9226a721fa9216a820ea8206aa1fca81f4a91ebaa1e1a91d8a91cfaa1c5a71bea71b7a91aea61a8a919fa9196bb18bba181bb176b916dba163b715cba152bb147ba13dbb132bb127ba11dba113b910acb0ffc80f7c80efc80e7cb0dcca0d2cb0c7cc0bbca0b1ca0a7ca09dcc091dc085dc079dc06ddb062dd055db04ada040ed033ed026ec01afe00cfc000 else 0x11b9922b9722b9522b9322b9133b8e32b8c32b8a33b8733b8433b8133b7e33b7b32b7933b7633b7333b7033b6d33b6a44b6644b6244b5e42b5c43b5943b5643b5344b4f44b4b44b4743b4444b4044b3c44b3844b3444b3042b2e44b2a44b2643b2344b1f44b1b44b1744b1344b0f44b0b43b0843b0544b0144afd44af944af544af144aed43aea42ae844ae444ae044adc43ad942ad744ad344acf43acc44ac843ac544ac144abd44ab944ab544ab143aae44aaa43aa755aa254a9e55a9955a9454a9055a8b54a8755a8255a7d55a7855a7355a6e55a6955a6454a6054a5c52a5a55a5554a5153a4e55a4954a4553a4255a3d53a3a53a3753)
def n11q (i : Nat) : Nat := (if i<2 then (if i<1 then 0x9c212291a210216e06c28836d960def904b70760723270defd8392878e8381bc1207831b0726823415c61d478ae082f2f0a41ef96e0f02aa1199bc1cb3478ada62f2f0a56a090aa84d8d319961ce096e06c78506b9c1ce093c1b0082210880121b6c149262081b9a046c8090a000e103d4a0c24c1c12e411002542d72c1bc1e2e1002436146d94820b5100257cff2c1bc048e668e0de0e01028121b7f29004fd331280e4e29041f8071a0bd0e387d809f4f959b702aa15d04002f80abdc0e7b4f3d912f52fa380ef436108440c03bcc0ad21c24c188c038d1a442523ac18093ea00f0e83b041804503bc9e0f12e809807457824b807780c86cef078dd108c03bb8d8b121088188803a65da9b4a83110c3760ad624275831102b69ba802e944001285c401e1d076081582e262db78b252739583a090d925cce5082b0ace404aac0e0602aa9500e15b4c66125c108529607299560746a940aaa718394cab0caa952d5538382ae27081dc012291a042820b825bede158cc842141375b81b6dae8de2004ab892da46968d832012144e486c81c4a6c3780812086c270de0f4d9cc2a0764814d04207004168f50b5c08214d8054cd60c8bdaaa7073504c3b46b4da48738345a08967b399a126632c523105825940764a7884bc4899494c86381d8c6c1c0403e666381d8c34628e0201f620fd86c24c1c12ec10f8fc14262d94ca410600d97ebe5e9c0debc012217678362e94002442e4e6094001d706f5ba2012505b03d6a005a2cd642b5890960880005d5e09572b45638561594cab03a945eaa549c150a707299183c2f8514a394c25d48a31f855080709a880c6c21208168f0da840c6c1994940091e17d3e0703278842e0102836084ea70de9b4d0f028991ca612e104b2545a943e1e0b23921840467a20024fa7c3c1ecb23921a4c80733c018d89219908520200a45203f04a3d1c784696070101b230be07459b0ba371b07c30661f054d2073da288c8944029002b180e50e6f430010a1704a110607098180a42412047e09400f00c593f0fc12801e018b2763f19c4c3c04164fe763f024fa7c3c1ec9c4d21840f440370fc123c3c9e0ee763a8d8e873049c80e71198e0e06f1b1b85808039b4d86b179a820230f984d207320d0d05e2e8d83067331940e6431988ba360c184c05f15978ba201b8d830092e124b65a2c960ae430808cac55049280e5429938245223144204c0492c94152813c9c4d21840804c0492c94492411c66462184080450485428082210c8423209005a1e1f8f87a3c1d8e87238080dc6c27048d458071a0cc64231887c1409040ac602f020b80400168245808158a820290783804280609c4c1a0a01c4a241188842200107c3c1d0e024361a0c8401e0e060602e160a8500e13028482210078381a0c058281208038180a04018080200 else 0x20a09cc349a80df61b471b0229c4b080768d383441e20013e4135976a6db6ed4b26ccc2b1c038069b059e00c98b000414b66a1a4f6f023176a00b570ed84394e0ddc48daf94998021b99a9aad0384c8cf6730d0235e08255b4630808840950acf86e9515a806e955089044201425680215b82542776b9bda115231081e4050b5ca49310301435d364ed26313302476774c0d81208032e802361fd247887230dc6cf9ae01eb72b1e568532bacd61389695be4762f29105052babb0656c3ab55484bf9517e5047082fcce5f23d5020bf3391ea8108fafd663b46918e0bfa992429021ca61d3528f3c05f0c073a456a04aba41414468e5a62f445440ad273a229c0f00ba510cd9da4e389a349ede142a8470288d490bd98210053c0ab8080a400ae15a4dd200a70b840880053948c1440004c8e02a704113928255c5b2c8e0aca31fd340e13631648c15a601c68121c119665f9701ddc9e213b2960777278864261d280eee4f10c84b304924f0e81c841f2b304b702aa19abe566096e2850735599a4f0e85d0401269041ede0380808c7d49039390f097c829b42fa41c12e213302494471c9bc288d1d0e5242f10a5813475301d4a2f5403a8cd652d155270540394cd60c8be880e050256cbc3eb9a7e349abedf20aa18240ea047a85c06c19a8012144191e84211001e3c05341081c20a0d001a208701e7ef276808133e5e00c04f932a85e1279e84136d84e1bc1e9b0b1a4f6f01c11936fa0a234729814a58023c364f27693010a11d3a3411938704a82d1c6c93a1d38204aaece6090384052014aaba7278469c270214349412693dbc0b010683e566dc5096064d003cddaeed103420e073dc18b29844acc97361da348c70448242a782c9da6a0c9a4cc57326603c18071a1a08c42170326330159092f2f06024b6591d161cec01e239ae6f07a6d806657050f871219c06c619701d8c241b8da5528039ec48370f99ccc077a0906e1f951f11b2d38422581f7c8f11c07230a4052b9517e5047922fe525f9411e48bf1f824782f9391a4cbf4a01cee5a1c84044bf83c964047211057f0e0a91c744220afcce479248e3ebf9101cfeb12ebac300b15c11a40290ba59e8e15848bc318e8f132ed4b0dd11208a2556e888a47d2ab74430db91521031111521088400c441ccb71e1c1a8051d8e024f11b8d04420007783800bb0a044a42120a1801168c0412a86000562ee9004662ee90046140e90045c02e90033540880045a28e9440022ae774a20011460ba51000049211c6c19a7041133981de6056580a26147014842866800226f91e055426f5a9580ef3361756b122b2cc94698881dd0984282410073dc40d8382301de67102b49983887824fa7885ba072f008438124a0a01dd052080fc3407633c85f0d86040127d3c42dd0f019428e64a3911212b90ab8) else (if i<3 then 0x76c201899f5091e1d0bc1380032eb065c7bb188c09c030872467c8f142984f8e86611233980a382323d5c14701c304a1630e8e181469a0bc701da34d05e381319f634e1c0163b46a70e02671234e1385c8269f35048f133350acf97380710e4423c509b213596bd6d76153c1c0420957368de074cbb4377f469c200db9a8a47e3cb7df8796f04b341caebe8bcd00e2fdf0d838073845f7ba1038a02fbdd081ccd53839f23b17949057a46918e08204ab9c421412e5423910a09f2e20391840a146a7840f904a3938207c8ec7243104dac88d38081f20903b9d1c6c4e00c416d8f2608602130ac840217cf01c030136cd0104db6dd49b9f26c122f10a09370617c30049b8ad0802bdb0005cc6384005cc6c844000361010046e072d10805211e01ca4214ab68d86f4ab68c6014a9f11b5f383055c14701c10c074c10818092d96420c03302466701b142c2c1958bc862018cacb8445fa0c88bf33a04700ebcbc05e12013a4fb78830be3a15a700282f39a801fc009f0005e68498029cbc005396a00a72dc008d8d106262b212f2262f2b8086d132633c92ca1d0bc98cf249e4742f048511a39490bc1409b5c69a409b1820b23a2330e22e04c10ed0709c9f0768d2f1c186dc5e90812da032ea10096d309750804b69af61841f58e076316420c86381d8c59085de448403dd820f703cfcd8c5082e4123c19844208e6dd6dfa78ba824f11b768242a14701c200bb0505234295d9e23560148f056b8080a47ee63ddbc786c69dbdcc34b7828a0c2380a41e090a0200e99072049e2b1c03ae807b99b0700e4a01ee42f54838e765038bc840e570ed8439840399b3d5383832d55383976e21c8444241478eee23910a0ab8531784420fb712744081280bc8670102f4842210026e11a14880786cb78802aa14697440dbad8090b6e780bc1c0204b6cde9b5d9cc123c080049850630e59837b68dedb21308ed1a43382556678b62562d1808254f16c3d2546646a11c040956d9a1ce958c39d2b1821038800717b488402060fc12e612301cc6c9da4c620a04dae3436721e05e97100d8986604850e01f471b13896104ad1c5a43a712abf05aad1b1aa981d322f43885103c4cd6d1014468e52c2044546d4024453cd95b00389af6120800f16900800e45ab0ba4014e5e220008c592345e9789d05e73501c4ed11a26076c6831d468127d401e1d04642c1c0ec62ca61b87870b087246a10242a7c3d9c4b05eb4044e00903c1ab0a804abace4749109f2652fa85e127083e4caa1b33c24e102e06828072d188448f1e239b7095da840e2fa11bc12e246948d0218009a6d65b20cce0297c82478159a8a5f25f50bc24e1007bbc1e4c0ed8c751a0740e9607b118c1c0955a945ea8a2039fa07469b27aa707269c4e16bd8482260a1de130020be5663bb083d041b711e11a7 else 0x24c2f4e63a4d26208e440b308961cc6370a7aca2f2f2f85e5e178e1962f2183cf189070ac1c39218806670103c05e0217a712a2f4e44d0a4f9f8be684917948778d179a032467cb8530a1319788e38b030f162f4e633162f4e2051c2f4e19a744359851c07033b187470349ede0106d1b022107c81cd010049d54259c504012e229085b424804940f89074185f88072345eb807130287041238d89c106187470104dac2206d35dce73c39ec0564630e404733b0bc05861ca7004737818805861cce004d79a80ad40217cf01c02780bd6a021790c40023c27802bd008bd0e02008570a021b9e11495048841e95b08052a7c469c18384469c10c21010058033380803f5c290825647a12fce62f014))
def n11v (i : Nat) : Nat := 0x1808c026002ff97f8bfa5fc2fd97e8bf25f82fb97d8bea5f42f997c8be25f02f797b8bda5ec2f597aa3cc5e52f2178cbc45e16ef1776bb0dd52ea3745b9d5c92e4171cb8c5c52e2170d3825c02df96f8b7a5bc6dcc6d4b68db1ad616adb505a72d31694b485a32d1367cb3c59d2ce166cb345992cc165cb2c5952ca164cb2558d2c64620b0e5862c2a60cb045812c015fd2fa57c2bd95e8af25782bb95d8aea5742b995c8ae25702b795b8ada96b2b515a4ad05672b31594ac85632b12580abed5caab9559aa714f2a71534a9854b2a51524a905472a315152865422a09500a7e53e29e94f0a7653a69bc4cca6453129814bca5c52d29614aca54529294149ca4c525c8f9479a3651a28ca45ca2c9144891444a2050f2871434a1850b2851424a105074829410a06d0027f93f89fa4fc27d93e89f24f827b93d99e64f227893c09de4ee27693b09d64ea27493a09ce4e627293919c24e026fa3749b84db26d53549a84d326913449a04cf26713349984cb26513249904c726313149884c32611304980cbd25e22ea16c4b525a12cc9648b025792b895a4ac45512a49504a725312949484a3251228093e49e24e927093649a24c926092e49624ad24091e48e246923091648a244922190a484241920890248043f11f48f847b23d11e48f047723b11d48e847343891c08de46e23691b10d4469234119c8cc465232118c8c4461230117c8bc45d22e21688b245822b91588aa45442911448a0c4d226112c894449224111c88c445222110c88444122010fc87c83c21da0e487043721b10d486843341890c085e42e21690b0856829214109c84c425212108c844421210107d83841b20d106483041720b1054828413209104482040f207103481840b205102500ec042019008802400
def n11p (i : Nat) : Nat := 0xa660542b129222005e03427f2ca04a87b0bf0ab07867da7d0b289004882f47b00327c0a704604e03902601b28b04b64c047a90039e1f01705c09d09503f028010e4682ee1fc90e46039e1fe4602ee1f0bd0ba08908704087c26d09407f08744f03902622d24622c06107603902e01be4603902ee1f06ee4603902e06c04e03902601b47504e039026823c03069a84a0a684e66e46e1f082a7148746809302c0a10b003d01a0a4a2d188e66e4603902ee1f05de66e4602ee1f02303322f04e03929802225c09a039e1f2bd27b8382be887a0967c8466092048b62a9a7c035e1e0a682ee1fa1e09c40a88980e04da01601a5a03f03946de66e4642ee66e4642e02ee1f489e66e4682ee66e4682ee1f0012010730502220c8e2d02b0700b402e01b4220c205161f043698659438019089e66e46e66e46039e1f0c500f01200c2b40b107560aa98a5916444c03203a09e06c04e03902601b252039e1f01b4a0e0902ee1fc0105d84ce1f011271049cb401607a0710580910832c30a0e6624c47107ce6624c03924cc8421fc0a03c0380200090b5068e66e4603902fa220840622820800528350c42b604ec09006004690e66e4602e813ab40390306b442f809e66e46039e1f01b0136b30a3a70e34e030a809d06f00dc71c35029024214c99c4cc130c605928402ee1f011085e4602ee6624c03902e02800ea99a4c03902e82201700a0a5e1f01403bc046c009e072063e98852e4682e00880182e4090c707406d6132c008c04c03962e026e1f80a09b07b06481907787105b03e03902ee1f8b40aa06b04f026e1f01b0bb060e4604402508842e2c80b62a0452e4642e6224b649228962de1fe1309888405684c0308270000c906605303102106c06a84c03962f0bd8a089908b07ee6684c02e0cae6684c82e027c22a138070b709708e08a06704003f22e80a804096e4603a037026e1f005a460394130c0081e66e4602a01820a0b309f05fe46e1f01d01c01b0114040bc0ba0ae29908fe66c4ce46e010be0af089086065036235e1f015014e130070ad0ac0a2079e66057e4603903002ee1f21301000b401
def n11join : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,z => let e := packedAt n11v ((z % 512)*13) 13
             let b := (e >>> 10)*12
             (packedAt n11p ((e % 1024)*12) b) ||| ((n11join n (z >>> 9)) <<< b)
def data11 (p : Nat) : Nat :=
  let r := packedAt n11r ((p/4)*26) 26
  let old := data12 (4*((r >>> 11)%512)+1)
  let op := (packedAt n11f3 (((r >>> 20)%64)*10) 10)
  let rm := (if (r % 4)%2=0 then 1 <<< (op % 16) else 0) ||| (if (r % 4)/2=0 then 1 <<< ((op >>> 4)%16) else 0)
  if p % 4=0 then (data12 (4*((r >>> 11)%512))) ||| ((packedAt n11f3 (((r >>> 20)%64)*10) 10) <<< 30) else if p % 4=1 then ((old ^^^ (old &&& rm)) ||| 4096) else
    let w := packedAt n11g (((r >>> 2)%512)*20) 20
    if p % 4=2 then w >>> 16 else
      let c := ((w >>> 12)%16)
      n11join c (packedAt n11q ((w % 4096)*9) (c*9))

def n10f3 (i : Nat) : Nat := 0xa22556f1ac6ad986458c629826057c5b15c54d525313c4ed3a4c52c4a921470bc2b09c2683c
def n10r (i : Nat) : Nat := 0x241f30a1a3c7a1a193b19f7bb3cf82b41794700b176c0258d403c06bfd4c6bf94453e12853df2813ded051a14951a02239a00e519f49519e0a819e6d53ce2853c92c93b0a0dbb09c93a3048ba30863a2fcdba2f8e941e68b92c8638f406b83a88b7e34cb7d74837d846b7d842b7d501804037b78ec7b763c7b6ed8936ef0936bb08b6bb0636ba47b5e107b5a407356e86357a878d5de7b50047b4a9478d3aa78d18e78cfa270cee278cb8e5b3cb878c70298c7ce5b3ab46b3aa48b39d86338c48b2d8c70ba3a7b1c987b12ac6b0558b2ff5c708e9222fc8c62fbd442fbd492eed46aef6462edd022ea647ae8b022e7207ad8547ad724a883b6b8815548813d308111a8819ebabbc87ab4807aac187876de70764aaaa56478750ea874d678737270724a98727a08739aa8736698707aa871666071714070717aa36c42a37c786ee6706e76a86f66706c7e986c6aa86d6a806daa7a9c50429518429318c055ad7a6ea842691c9249349a3b38984fb9104ef5004fe16a31bc9a2bc0222b886a096099f4bc79f02c69bc1c51a014519e1469845c697e5c69706069648869528869448878e6c078e24ce0024678a030108084786024683acc
def n10g (i : Nat) : Nat := 0x184ca11283ca0d282ca09281ca05280ca0137f8dfb37e0df537c8def37b0de93798de33780ddd3768dd73750dd13738dcb3720dc53708dbf36f0db936d8db336c0dad36a8da73690da13678d9b3660d953648d8f3630d893618d8345fd17b45dd17345bd16b459d163457d15b455d153453d14b451d14344fd13b44dd13344bd12b449d123447d51a5455510542d50654054fc53dd4f253b54e8538d4de53654d4533d4ca53154c062e98b462b98a8628989c6259890622988471f5c7671bdc687185c5a814a04a810a03a80ca4299082417b033000
def n10p (i : Nat) : Nat := 0xf0f00e406203901700e405003901300e4043e46f0f80fc0220aa00800e402007e02a80e414804e01c80fc07803901f80ec0720aa01f80e014403901800ec07203005100e405c03f01c80b0072c2e01402dc15802601c88b24440a201cf87c073c2200e02880f401b05600e4036087018806c07222e00d82b184401b01cf87c036039f0f806014403900a80e404c01503180e4028039013005007202100a00fc05001105101e802004a01c804007203600800e406601001c80c00200390170040072026008015b844010055088002003900a0040144030005828bc3e00b013006c012073000800003600100002bc100055015022807302e0100234114039f0f82e810c039f0f82e80dc039f0f82b007202ef0f82dc10c030f0f02dc114026f0f019c08e03f00d81e806c03100ddad2cfa03000d81b807302e00d810807202e00df99807302000d82b0073e1f00d822bccc03e00c00e404c01b00af91807202b00a799bc8c41400a02780e40280088288072030005c1c7c8c02e005813c05c02600280e406c010a0080e4858010a00ead015807a01c80c410c03c01ca0bd45b6b4042c1c407262d0c4059007242c01002880dd85d01cf87814408802280e7c3c0a203ce96807201b051022b49882e00df99bc8c039f0f806c158039017787c037e66f23187c828214942791807202800a028b52003f00d8047ccc039810006c01de66126787c03600ef3300e604001b003f998073e1f00d801fccd22200d804000e0a2126787c01c00605682180c603f01c8060145871c2600fc04801605161c7098039012005bccde4601c806802400cd5a02a814408a417002c0f405801f806c02e00b045799bc8c02ef0fc02bccc039f0f806c01c007f33791a05de1f8070810115a4c01ca0b8037801045799bc8c42ff0f806002e0ac055799bc8de1f00d8040159e6672300f3c3e0100059227ccde46217787c02300ae5a022851208601f8043003e66f2300e406d2220080004913e66f2300f085de1f005c02816a072f33791806c22e316801716809f03600e405202400b6010115a4c01ca0b80360178056004155e660317918073222008000414408a043693006002ec11787e0140b5034799bc8c03901b00be44400505a81cbccde4601c80d9c5a01b00282b014408cf33791b48c030417787c0360100560288119e660317918078030217787c036010
def data10 (p : Nat) : Nat :=
  let r := packedAt n10r ((p/4)*24) 24
  let old := data11 (4*((r >>> 9)%1024)+1)
  let op := (packedAt n10f3 (((r >>> 19)%32)*10) 10)
  let rm := (if (r % 4)%2=0 then 1 <<< (op % 16) else 0) ||| (if (r % 4)/2=0 then 1 <<< ((op >>> 4)%16) else 0)
  if p % 4=0 then (data11 (4*((r >>> 9)%1024))) ||| ((packedAt n10f3 (((r >>> 19)%32)*10) 10) <<< 40) else if p % 4=1 then ((old ^^^ (old &&& rm)) ||| 8192) else
    let w := packedAt n10g (((r >>> 2)%128)*14) 14
    let n := w >>> 10
    if p % 4=2 then n else packedAt n10p ((w % 1024)*13) (n*13)

def data9 (i : Nat) : Nat := 0x5500202006c01010159f333c8c01e7c3e0081807a00f840180036200e4010142c80208056302b0039006c601c8036202a808500e46042806220108039006c605100362fe76fb6000060ac3400047de0c1501c4a0210073e66093a52c0a54530e7e49d31895814a8a618fd93a6312b029514c31f3356a6076c12409863f46ad1c0ed8248130bf24b6958a9aa490261bd49535f2bb549204c33e92a49e2b648a409877c254d5252c8148130c7cc9da9855aa29026127b89d530ab545204c3b692a6a93160d24098779254d525ac1a48130cfa49e258ad834902619f49534b15b069204c3be12a6a92960d2409867d25495c4ec1a48130
def liveLevels : Nat → Packing
  | 9 => (17,6,8,0,0,9,0,data9)
  | 10 => (146,5,8,0,249,13,0,data10)
  | 11 => (528,4,8,0,249,16,0,data11)
  | 12 => (274,3,8,0,249,15,0,data12)
  | 13 => (17,2,8,0,0,11,0,data13)
  | 14 => (1,1,8,0,0,0,0,data14)
  | _ => emptyPacking

def liveIndexShift9 (i : Nat) : Nat := 0x28
def liveIndexValues9 (i : Nat) : Nat := 0x14528a11400000b02802
def liveIndexShift10 (i : Nat) : Nat := 0xa001907074600012c0c3e0100050f0a015b60036100050015df01019d1d01b50200df040c000d0c04d31600f9002b1b030100a203090902182034011800e35700112a120c01002a01030001050212196e5e01
def liveIndexValues10 (i : Nat) : Nat := 0x201783c60040009c1980000b30f01f80160194073d00b4013802d80f003fe013802c00fe009e3ba4013005500b603c00a983163be00088035804c01fccc31a22805b1db400b80279d4c00000000027805a01facc7407e809502b80160000804f025003c163f81523a9c04a00a8804f0498433c026330f113a04ac195817067d0017405601f700b607fc0ae083200b6cc30078c18d03080000e83005900140ca000100fe00b4586037b078e03f83b600012c702c3001380958096009c0164027005900b2b3d86d0803d047003c076d804e00b008e401b804d026e06400fe81f7047a016c026824d04787484026005800020160000000210d403c9a5eb3eb3bfe0540001015e03ea061802c01c6009a3b648660030301c0c5d9df1d2a03fe01600ff80580498cc6c76c812800b4c78807f809c01e60010027236100980134026017247e804a804a00586618016c02c805a01bae890095005b00b2013476c013502a205dc01cb30c01e2195c0e38058009e3b6002d02f8002c016815bb3eb00981fbc12400fe009808059d9002800b600780fe8edb00b401340fe812873bc01359878eda00b2b1cc006004f0ee203f40c981f5661c0134027804d002607f038f004f009a603841f2d060d8c025802d804d09c603f002d00f200b401380c3001b009c013
def liveIndexShift11 (i : Nat) : Nat := (if i<1 then 0x150020013fc9b500201000001604d97c8a4c2900502a018000025000cb000200122d24300800200902200104e02c002005638b2d03d00174800023c02e00402501a0000022bf02500000000f01a02e2ef00209b00d23000000d00d3bf00300251900100102a02c88703e03c018006b4702e00000481e00d00a00200000004d01305f00200900307801a01105401800300300900000500300300400800006401800704400002e00500000000000600f00104000d2b201001203843800003200400041000000000598402500000100800001400069d000613000a7f0504a401500000d01f03d05300c002000002bce00002200101303c09fb9432206300f005036ca600c001000b6990802302c00a00000001f01800000300700304401401b0020006ca00000160a00303100100100b00100200401f00000b9df01200401900001a0060262d001d00300901a01604b01800100000d00000001900400500100001908f00400800303000700502702700400001400306200700201732501d02a00e01801000100100300844903500100000600001d0051e04d000000001304701500000e018b08000007001012000cbc0090000b100900b940000cad00e01872e00001602e00300001557b0020002e9ab300200100e0014190066ad02500743400113d0517df00001700200b004000430009002ca300500600601f00000000300b025002003011001000001940001ac5003000a1c35d004000005ba600100652b00f002aae00900dc9600000457500100a012006001004000001022058003b4d00500100000500700100e00f00d01200900f51d0000057ab0080180093f100802b00000000700008d00601a02600300500401f01c04a0030008721fe1200020320039d600090900000100000e61e00002e00000000c4ce000004002c0891500000000000400001e002021003003a2502700100d00100a00000401302141d005659001013adf00001100000900000f04800100500105300002700500e00901b03e00200600500400100000e00000100100002b00b00300700d04700002600200200200100f00000d00000d00001900000700001400200800400200500002e08600000002b0060010207a600005c00802e01000101a00201c00400001500400c0010050244cc00500700200f00c01d00a00300000b03c00201400101500600200300a00901f01ca150000003970000050007ef00000300500701100500500340600900000496600c01300300500600300000202700902500202500900200000049e008cb900600a00900300000400200000c00100000500200100000400366f0010020130085b600400301700800500600248400000500f00802e0000020200091bb00000300600600100b02301b0000000090001e800a00400e0060080022af01d042 else 0x2207b06d027042001001024ac00180280ca00000100f0053870032bc00d77a06f00b00201a05201100106000b01100eb100e50020ec00601404800503300b09d5c100302800a9195a4316000b2703c00200073101e21707f0010c601b00100f00b00001200309501300000000100700500000f00700000000100500700107900b04d0044bc01415401300103700600002201714c01401a001004047c1401f032005018030001000000008025019000b7f00d00b0217204f755a27a06f0c700e00302c00201d003bc507e02e05c29901f00c0ec00d0695d503003c00142692101f04001f0143f2026001098b0904b00002603900200400601202b00549a0a500100000804d03600202f000005005000606a3102087c00000107200f00e00005833100c07500102002b0550000385ef0000130240ea00c022bc80000100365ba01a02f00006703d01a01900900700400800029b04200006701200001900603904800494a00800f01f0009e602700024700807d00f8f400100202c3e71d60370200f205d00600a00000000000d17104e02d00000300000000301800a00a0491ef01c00703d00201703200000600803c03a04700700f05100300000c00d01001601f0000180007fd001008017013000008000006048003000028017815006049010007b8f04500304a01e0180)
def liveIndexValues11 (i : Nat) : Nat := (if i<3 then (if i<1 then 0xc0cb40c04172414b55840015009780ce802b00bd95c3196b8097c47d95bc40e200cb40a6e317d8ff00bd80e200bd40bd157700944098c13b810000ac004880fe00bd410f0094043a00bda379960dc097c0974094c09700bd23b880348e88c27a00bd834601004094992880bdc0970094c14680dc4094c08955ad40bd8094c0bd80e200940f0380bd005918ffc09640978100c0fe80c080970ef2ce5d171000c00225594d002c809455ae407a0006c094410000d6c0bd00bdc001c0d5ce8881434094c0bd80dd817200bdd8cf40d598ff8b0d409400c0c097c1008097810040fe40bdc097c0ce00fe1584813f40fe00bdc0bd037c80fec0cec097c0f2dca500d547c5414b409410160100c0979902814b8100d92880c040dd00c08100996b592b40ce5902838e847d8411cef095828097c414e022c79140a6c0bd40bd014bc0948eb14b4d821340bd009486ec80d6c10095aec0d580cbc097192a001a010700fc00bd801c80fe171a81f098ff829e809480cbc791430cc0d6006e8097562d01004137013fcf03d5788028c0cd40ce409f4791445559e5843a414ac094c10040d5c0cbc097c411c3e540bd40fe414b014b5902810040bd812740989a9980d555d080e200bd40d6cb4d009d0100009440c0d92840bd441540d840fec14245b48094042340bd40bdc0e240cec0bd831f0ebf810040ce814bc09715ae1a93c09455ab8097809740bdc0cbc097c03880c0809719aa00b5d99980d5809440d515fec0c00e9ac0d500c04094079140cc009700bf80e2841501884100c0a68142445307918017004a0098c0d89902c0c0c0a8c0bf80bdc0d5c3e49902c0d580cec064843d00c040bd42e8c172414200c04097a3f6003380cbc100013ac80e80c0c0bd669400bd8100809480fe8094c09740bdc0bd00c040bd00bd815446f9c0c080d58094809480c02378410080ce958400cb80bd80970150c0fe40c2814bc0bd014b809442e88097c14bc0944413843a0138409480cbc13f010080cec09441475936810080bd80fec097422a014203f080d1010080944131c0ce807b5928812e009740bd00c0836f00bdc13f41728791814b1902414880940100c0d5a6f6c094c09404c040fe8097c1fe806d4100ce42410000c080d580ce84f7d92a80bd00c380cb80ae009440974137847d8100023b40974100c45f409d193940fec0cb010055b9cec24094c0bd40fea4e300c00097c0c000cb80bd40bd153ac0d5022e55850ed65e3f8097414580b9c146c0cb80c040c00098443a40bd87afc097592b80bd814180964154009700cb411300d500c098ff80d680d895ae0094809793ed8374558200cb00fe80cec0bd038ad96b002d00c000fec0970094c47d014b4e5c40fe028240e5c0bd844b590240b1413080a680e5047dc79100bf0098c0d54097c0c0844b0791 else (if i<2 then 0x80e5c0bdc12ec09400bd80bd98ae8e8880bd0097c1000104a37f40c0859580fe014b58ff014b98ffc094c0a68097d5d080ce00cb009640bd40adc0bdc097409755abc110809740c08094c094422cd5aed8cb413ad71384115901027cc057d9015f8200bd4b0340e202370e88009740978415cb0e595dc09700c002228098996bc06f009780cb80c0013a804ce02200c095ab40bd814b014655ae55c4c0c0843a00c0d96b8097c0e2009781000097c0bd4097414bc0cb045540bd413a479140fe196bc0948096c47d40c055ae4414009d80d680d5c100c1429c7c010040d5838f95fec094010080e20100c08ac146996b81070097c0bdc094c09d414bc137c12e405c009440c040bd80bd80bd426f40bde02e013ac0fc0e18d8ff00c0843a80970415814c80d58097d634409780bd1928845f40e24327009d40bd409440c080cbc0c04a9a083cc47dc094c100c0bd80a818e38b1680d8c0978142013fc0cb40bd40bd40bdc1d740c0ce57c0bd4097193680cb80bf425e014b8411009480ce009740bdc0fe4100cb0e009484c8c0a6c0c080d5c411596b010780d554f2014b0205409740d5c0c09625d5ee81fd809480d8001040c000d523790094025e843a8097010040bd40bdde64c0bd40adc14b014b009d80a1555b80bf00fed62d40ce01008137c14b1901841141100237591c520580978097814244144097c097e379409f409400fe40cec094013fc0dd41a3043a15b915fe40d5843a4053c31f0003d90240bdd582041380bdd5ab814b00d5c0dd809441420791c100409740bd59395f81414b00ce40bd80fe4142409d4448c09715ab041a4094813a447d9871c0bd414b4100cb0e8289c09740bd00fec2f3c0c0809780c0158240c0806015ad01008066c14ba00201720094443ac0cbc02300b9c35001491908c0bf00fec0bd079100b895fe4094996b80e4c0d5c10006a1c0bd00948029c43dc47d80c00142410080bd00cb40970e1a009787914e8b43280079810080d6014258ac014255ae80c0843a00bf803d809440d580f2c05f958b00c04094009440c095c7c0788a90047d40bdc08c5928588bc0d5000dc228409480bfd639c0fec154014b40bd00a68eb4c096447d80bd40c00080c0bd813a4097c049014b40bf4368814dc0c0014cc0bf809400ce009740cb55ae409400bf80c085a5009780bd80d500c080c000c0809440fc409719281582c09600cb9928c255c0e580fe022d444800bd00d657254148414358a4813fc0948100005000cb80e2412c401fd9288094014bc14b4097192a00bdc16f42e8996b550383205902057a40bd80cbd01e81425734009b414255abc08200d88142c0aec0c0c14b410795ae0100d5ad8100c14240bd40980ebf812ec0bd00c08094013a40bd409700bd410000ff5ffd043a80c0006a414b80bd0367d5ab else 0x95ae845f000055ab40d580e580bfc13a0097c14bc411009400fc8094883cc0e2c43a00a6c0cbc083999240d800c000fe02ed80940448010080c0813a0000c11000000000410080940000c47d0000409795ee6002810200bd00004094c0940000014bc035000000000000c0bd84534097c41441100000c100c137431fc0a6409780bd00000000c1370098815442e64097596bc03c40fc00bdc0ce80c080974098c0bd40ce0000c09d4eb18ef4c0cb00d5801d40fc55aec0bf02214094c0bd40bd958d80944094c0e240094098809440d515ae00c0d5b9c0e58141c09d8027c0fe0414c0cb98ff447d158b0054ceb140c0014b0094879180d5041180cbc097014b80c0c137c41104485ff980cb40e5814280d6c08d009740fe403e8326c0d6d5aec0c0d93642e80094009480c9c13a84bf809740bd80d5c08fc030c0629c80443c55ae410000d500bdd902402f00fe80c0c0bd4448c09d00a0c094410000070097443d00cb80bd95ae00bd8f48996bdff99928c2460790c1420414011000bfc14bc172009441ac444bc0bd4094555680bd809800bd40c0a379c0db0e8b010000c00094403740940097163980bd0350c09780cb0094c100c098c14bcb0d009740d5d92ac13f22f640c0445f40fe40bd40e500d8d5c3571a511b40c0c094407d40bdd5855939c22903f7c097590b00cb4094c289d639809d0e8c486cc142809400dd831f409400c00132000f409fd5ab80978f1b00cb95ad80bdd5ab00cb013f008b014bd5b901130098190b409701434098817a8094802a558b40ced903014204ae014bc0c080ad409795bc9cf780c000d5429e41020100c12e813f40d680bd010080bfc14bc07e814c55c480c5c17300fe0097883c990300bdc0c040f240c00eb1443ac14b40c081008094410040dcc0fe8233c09480bde37d00970098c14b8094022ad5cc4096443a8100014b9585c097014b8414c0974070809780d80097005e4b76017a806bc28a43f640cec09400901903c0c099024097409400adc0981008009840ce020743294097832400d5d63080fe596bd5ae409700cb01540025c7ba80fec0cb40d580e5c0bf4111d5ae55b9009480c0192340bf80bdc0c0c0c08237022680bd404655ae80971725c47d00c080bd4100cef4c094c14bc4488100c0bd410001421939c14640bd00d3c09759284e8b00d5c0204131c149c094845240940eae409482e780a8d63440a600bd441180c040c0c022c0bd00969903414b4170c0bf96818094c1278097d5ee8430411ece4e04bfd5fe00e540564452413a0ef8588a410f413f00cb810080fe80d518d08094414b4094c47d01101c7c80c28143996bd94301008e04c100996b80cb595dc22fd5ee40fec0945c4a55824094d908c14bc0bd00c000bdd90200bd40438100c13f84bec0bdcf044094192bc17ad58b)) else (if i<5 then (if i<4 then 0x9d553b0098c0c080bd809481a38000da93804080bd40ce809480d5403255b980bfcb504115810000c0813f40bd4097409d40e2014640fe409755d3c0974257010000ad422c40970094c0cbce910000d58215d080bd809752058411409400970000c43a15c40000c04ec0a68094c110592b40fec0c0c0bdc0974094c0c000fe0000013f4100c09440bd40cb006100fe8094a3974100c03bc0d8c0974172c0c0009f4100c09480d640c04413d90280c0e75fd5ad15ae478e40978097831f4097c03600ce80bd40d600cb80cbc44880c04097c0ce4eb4c173009680e580e580bac0d5c098443d80fe00a6c0fe0100814b809755ab0e88c0fe043a8100c100000080bd410080d5c0d5c100c14b00004100958240bf0098823200000102c0fec10ed58b00004e880b0e0000590200ae4110c14bc014186ec0cb40d5c148010040c0c097c094443ac0978094592b40940097c0b3c10000008100814400008150c10788fb80cb4096c0bd0455014bc09480fe414b40a6000000004094c79180bd41008b0dc138c09780cb963455c3c43a843ac0c0844800bd8073c0bd40cb03534098810040c080ddc43d413a414cc0970005400b9205013780bd00bd990340a000d515ae996b920580c0047d02104100994d80cbd615009741078142c0940000814b047dc0bdc0c000d5814cc0bd000000bd0000809480dec0bd0000186c834095ae000040970000c0940000639f00bdc0fc0000c846cb0e409400000aa7d4f8c097e3b840fed5fec02e596b409415bc15ab40cb04ca40cbc0c1c142c0bd8100810000971b58421800cb00e280fe80c00000000095850000411080bf845240d640bd98ff81e40791c13f03910110922e00cb00ce15ae00c0c0e20000c5d440944041c0bd44c9c09700000000418e045300f1d5644b0e444b857ecf4840d5c09480e5441140e2814b40cb00bd43fe414898a3c0bd414295fe592800000000d928c22c409740bd41004100c114c097814845a2155c4411a42400e240fec0d5d5c340bd009441004097c0bdc097000004bcc414c097c00a000080cbc0c08097000085a9c448d5ec000040d8d908c30c87270000407640e200dc0000c13f0000c3450000014900ce0000409400940000414c409400e50000443ac41180bd40cb8096000000bd00c58e88dfb3804f0000c0970026043a000018ff80940000814b00000000da9615d0c098d5ae80e580c0c10055ae0000d5af000080a6c0e2000018c5000000bdc32480cb0000c0fe009701000000809480fe000018ba809795ae1a7bc0d5dd2a000040df809400009ffd44530000012300cdc13f0000c2e9809740970000c0a880974096c4f70100443a80bd0097808e00004097c0245205dc8080a6008700004097c23d8074c11080cb0000153f4b4dc00e40ce80bd8094413f009447c5 else 0xc094c0e280975fc8c0970000048e55ae40bd4791409800bd000000bd814bc0bd8055d58244118e58006800005928000007910000c0bdc0c05928c09795ffc09780bd000005a9810f8452c05d811040c015ae414bc4c840bdc201c09680c0992b8eb115abc0ce409700580e88c0cb043d423400cb009402f0c0bd8b4d80bdc5afc0c0009740944100c411000080d500008100017a00bd010f4100c094000000690000409440c0000087918094cb0e0000c10f000080bd00cb4791000055fe413b80adc094843a55ae80bddca510230000043d15ab00cb8448009400d31fc91582814bc173591e00004086c0d5c29d0000c096414bc14640bd0000812d18ffc0bd9928410080cf8100866580c04100809700bd8452034e80c30000414b80c0000040bd00bd95ad99ad0000010081d040cc55af00008011193940cec4110000000099280000000000000000409780940000413200cb80bd00000eb400000000808819020000009480bd443a00000000000040bdc042409780bfc13c0000c067978b811041a544140000810080c0809700000000d58545a540a0c094d9030000806c95cd423718da4b0d41330000000001934411000000000000010000000000414e00000237c0fe00000000c79140970000813f000040c000008eb1043a8b0ec1000000000040cbc0cb8084000081005c7c0000409d809763e20000d96b00bd00c0e3798114996b8100814b859ec10084484411814200bd95ae00bdc3fcc4114455409484144094044b04b4c0bd80fec0e24414c0ce8200009700004217c0965903409400bd40d5c031413a988781008096843d9936c0c0809700c040bd82f398c440c04105000040cb424600008113c094000040c0009860300000443a414b40bf40c0c2dd80754246c41580cb95ab479059adc0bfc094586a086c95fe831fc14b00e240cb5939409800945908c1000000c411809716344096810000b24b8ac0978e9155ab40cb841140bdc0b8443a81008100c0cbc1008100c100809480c0812780ae409d0214013f010700c0c1420094c10000008094021740cbc09680c040d55c7c000040bdc14380bd4eb180d5809716284eb4c0bdc097409780d5010058d1d99880e280944b380100014240940096c0c0000000c0c1000063043a80e5047d8100c37d80cb00978b8a80e500d5c0a040bf041440978097c0a640e2c18dc0e280cb9393d8b940bd847dc09740e541225a938097d58201000097409d96e48097079540e50000813fc100c0d5009480bd40bd009740bd95ae0000c0cbcb68c278014b40e5828201004094c0cb40c0c0d580cb809401f6c41140d640cb4415d5ad8097c13a5cf84097c0045a9ad9b6009740cbc08115ff043a4094414bc0bd1582409400bd0000c0f200c080cbc0d5d9020000847d00fe00bf13c8c09442525928) else (if i<6 then 0x80c01928196bc13a41a301220000000000d5c09419f90000829d40d90000958240cb19024231820281469c7cd96b00000000409400004148c4c89969000000bd0000827c003a447d000040f180fe4097410080941928014b409404bf809400cbc04bce8880948077558dc0ce40bdc13f40ba000080980018009802340000000000000000c3fad5ee000080cb0000000055f000970000000040e5414b810000000000413f000000c000bd00bd55bcd5c3591101000000014b000080fe5ffc0000c228065a814c00e240940000000000c040c0443d00c080944154d96b40bd40cb80e2000094f9443a0000d4ee80e2c0bd412d000043969902c0970000407c4448401e40d680bd558242278142c43ac17300000000879100000000c0c101070000810000bd40dd00d5000004c9813f413e00000094000040cbc09400e20000d702c0ce00bdc0a080cbc100c0c080cbc230c07f00bd009799b6043c5582422c80974e100000c0979943c094c1a3014b801bd9280000c09440d596c50097c0968097045f009800bd04bf80e615ae814200bdc0fe80ce409640cb80c08098c100000000c000cb0000d5854094c09800004173c2cd013fc100cf045582c107c01340bdd5ec80cb95ab196b45c38107ce888228000000bd022b0000402100bdc0f20000c1004791009f00bd1928c09780bd55d04094405a5582004d45a300ce4415847d0000d928000083c54111d92a95ab0000447d00000000000041460000cef2041440bf010040a68100c448810080ddc09d80bd40bd02d8427780c600ad459f40d6814bc0ce40a5414cc2e6da9380969928409400970000043ac0bd409480c0c0d84104c0bd158bd4fa0b0e014b80cbc039424680e501d0009dc14200bdd77080cb6063c0948100000c00d580e5c0fed63995c4c12f1745814d80cb409440fe8094013d8094501f40d50000c41100000097839500c080c001480e8880c000970000c146c0cbc4119928c0bdc10083c9814240bd40fe55abd5adc0c0c43a414b023600e2990800d759dd80dcc0d5996940bd95844100809740cb80cb0097c0086424c130010040940eb4d96bd73480bdd5aec0b496288097023400fe039b00004b8b414b40cb40bdd58280e555fe843a80e58096c100c11040d50012c0d5c14bc0bf4094c11fd5fdc791013a814ac14b8100c0bd82d94411d5dfc7d0813a80fe413fd902410040d881008100841142e900000094000000bd012e414bc0c0c0d580bdc097c45580bd80a6201f80bdd5add586023519501634043a00000094c0940000d715c4520000c05b000040e50414000080c000cb95ab00c00000409480d5c0d500000000c100814bc0ce0000d9111902c098c10080bf009fc09484bfc09440d680fe00be000001728097472ac09f44550000c0cb8142443a8100c4ca5928c094 else 0xbde4540097014bce44c3fd55ad809700c0041540cbc052809dc0940000c0a600970000c0bdce88000041000000963300008100000080c0410000a080510000c094c0c080a640949943c142c0d5c13a409780d6c0c080bd00008044c43a40d5d936d8d900c09aa28094809402460047c09780d68452c4c985ab414b40c0811100c0044b00d5000000168094409140450000c11041a40097845f40c080fe003fcb0e5a72d90b8094c0c00000d95d40bde773d8ce00d5c0948b4d808500bd813fc0c040fe813c8448c09480d55902409440d640f200cb80cb0000c0bdc26a994d40ce8b0e80944172809f010000d5c097c0cec0fe07b715ae00020019c43ac100414b00a6c0940204c43a95ae000000bd00978100c228c0dd8df987adc429c0bdc14340ce15c3043a04ad41004065c411a065c0f255ee00004b8700000113520e822ac43ac0d5c0d5409640bd414b8e8b40e280fe009780e50000c09445a5c411c0bdc0bd822c00000094c0bd0096c0c0c0c040cb80948072ce884097c097814200714097000080bdc0bd0000)))
def liveIndexShift12 (i : Nat) : Nat := (if i<1 then 0xc0000190001cf800c00a2bb000ddf105c00022e9b4400400a004000401601d800001c003001004400000100680e8032007002800001c00b00080640120060070000032003002000c006019769000401003d000002c00000100e00cc01c000000003001a00100000100120060121b04cd2008003801801400400100040180220000994016011008000000800000080a40480010010000030001000802c76c000001000400000100a002c03e00800b006800a01d24e801400800100b8014000034000897000200600a00240003130053b106ac00600b001800c002000800000000e00c800c0001a8002000400200c002001c0240050000038032c62000006400800099f003800a00100f000000a002004803c00e0000000141f180064d20001d22035003cdb08b6016001800000000300480000000050000050036003010806c002000000000c000004000000001200700280200000080098004002020005000402201c004000c0000053dc8004008001000805c00c008004000c060000006800001a27c0049780006000067000401401c003003800d039195000000656d000024d144000002245800000a00000640b600200000000400001f58d28008a1200a801000e00202d803802200801c800402400700000080180050040018008005000000001200b001800a184797000108000800e8948000018004001005800e0070000420000005000004000c015001c0680840000030004008024000002979200046bcbf000c01c00a000c00002a017806c038013000a468009174002001001c001000344400000c007002c000004000a52800a02101380000031ad000005400000100095d401e00577400000549ea0010024004000005002800134700d8074048ce500c0001724022002802c000018016807c0040000080044cba00028db40c034001000004c0380040030014002002000001802c000001800401b110000adbe56a0010cc002000000e7130006402006001000000c00200380180060031238038000007000001c0000000020028004012000000000400019e001000001900900000060110003e0e004000012c4f800c017000000000400879b80000020039178000058000000003c00800600032f000601900000a57349164c1000001e001000003800a0000000040004005002800000800000080000020039a0000006800500780390ba0200088001ad20020000018008002003800000000100800016d800a009000000000b005cba00000000070028000009003c238012000001800000c00661980080043b0002802c030000006a24001002d00821d400000100280040040000020020c8600a10200058b00000028010000000001800000200b0ba800802200100f3950b9a00100600500084d900d80bc0200050008024010024000003802a000 else (if i<2 then 0x3019800002802a0d4000000001f000004c00008c01293148f601c000000569a00100a800000200096300000ee0000000054014000018804c0120042f0000800058f0010021df60450250020052000006029c5fc005000001c02200049e00d4000001002800c0c80000d501600310d10068044d6200700d803000800500f86f801ee8a0018008004003000005d46a00300300000012e800e80040020410038055e5c02b027801008e01d00105980140010ec816001000000c800c05e013002003400e0080024aa003400728d00000e8ac80003d380280037b400b401c0000000000078004045803800225c001800013a005016000000e0480000060058008003036017a00000045117a4013002800002800400c8010812051003017009a005000001c00000a0188005aba0310000030000001000000800a074001003800200501d8078044056865aaa403a017001002c01c6a4032801807200000382980b200500c8088000025000003c02c0130018000c9a01f1550040024000810801c00c2e8000886801c8102d780441e496c000004400002800900040160020070150002008008803c04e00085eb518004059000000009201c4db00a400000323f810800002b000002c01601e000814402400f0530068008005221a72800000100a007800c03800d00240bf295005000c0024a4000807c0000260018016050004014807806000101580000320000051844030017001800000000a001800802401463e011c00a00c00018b0038006052802d25402500900f4002007000811001e0020038000022005020800403a000000192405094b000800000a0037f1002000c34c000000400000400201d800203e00000b002c0040040010000000000c12400000000d80051b400f000802000400200200ac03efb9000002804c0000050000008000004000004d378445994002400b000002494c00b01e2f4cd7a01f0229db002400500980140000040051868000003000001000800000580000001ab013000c00000165100040280030008d200000250009a8400008300480308e4000005805001e0000040000e04002000806c0220b90000d11b4e017001000c00a1e6001000c0140050158000000efc001806c09059100080140040000034ae400e00126b0008000002669c8280260120000010c0617c02149c0004b87010ae9400007000d80f800000a00e00040000030080040052005009800009800f002802405200000900164b200784d0130016bf8002003c06200d00f0058000003003004000800b00e800400d33300000c801e0493f28014002010001805000400300080d8000013007806403e61a0012cf812800b1faacec00604d000000c000ffb0028048000005003800812e00000a001800200d48a4348012000000800400ed395d1002c00e00d00180e else 0x5701700400244ab000052401802a0000009dde02e0348b30000001002a13c04c013007229c02204200580080d40008a78498002015021803834002f040005c00800f01f834070601c53c800001c27c003950c0320020a2005003e011007800c0181a2038001c000017003806002c017754000800003800000b8000014001000004e03706b004002459494c815000c0ae01fa4080cc1ba000003485a00700b14b005002501d80b8038045002800e09400000700800160a2379000000200001bb8e800600003202fc05600000802b00a05a400181c806800702d800185004a00105f800c00500000300180001a40001c3a05e00280f0000c91398800412800a001004c060001001817c07e023790801c03e01912d000000c00100180c401e000007800403cc8205b800008000f017800400001400c001c034085015800002c01b000003800000500e8004222006001801c01e05600d814803a000020004404601401f81880840005018094000000002008c02e0d000c80000120000000002130000000005c8cc0140040010048013573005c01805601d80140ae0270048158014ccd001006002ed8a0138004060022009007a40200000a00f003e00))
def liveIndexValues12 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x201a5fee652ac4748249c154821b65ce823e4215447cc23ec737201984b1c6d207105ff085ecf3d9379f02128212c70ec74d821583bf201a00244214409ad61303c14c095e24870f82d2c23ec212821560254092dfee677640fe4285e09c43fb021bc25602c995fa02159e2586b691034735648447389fee07106765c06e4249435807370321541242f0875a78d3fa2682c98212e5135ff70215a1dbc70c02fd0c088215470f55fe819fc2c0b48433d91feee02555109ff791035fee55fa03038212e06d03ff01bc429cc23e027ac23b8212421551ae601a82c942490101a511827c8212df74805fa4ebdff707bac1f469e2c23d84f3404c0212659638fd070fc2124249c739023e407a418f42542501c2124439f8d3c09ea978e0a51ff702d0829d6522c75a8212021603c39e64c196413d62972501c4d042f25eb302b8601ac735c21221f40175814f470f201a87358215c22b00f6874e451a8b9bc215414529e2cc0944f680e5c2c902b5e4ec78668224823e45eb003ac216ecf48215417704605fee25d38212023b4735821bc282c2150260403f9ff20417c1e280ea1623023d02154699dfee023ec483023e8214028ec263dfee827e827e023be5542017802b40a8201a021282c0474d5ff15ff703f45ce7421444d8c0c1c2bd00200215e59fa01a80c8021682fd411cb3d9c176070f80b007b28735c70f1de3c1e3910380c6c29b651365132025c71065544249c05402c9c151035a82ff42c002fd02b5c21580bc02150215846382161ff147f7474e0c0907b715979152823e1eef42494214e554c73580f3e01a1f75027e0212c21b42c0c0fae4eb423de300c256870c425482140156c23bc5a747f061d8823e012bc2f86134c21bd882e0a58212443d82c90cb58c09a0d4c5e733d9423b8214012ca895c2c90009c7b7dff040ed601aa59f023da0d48253c2bd423b23b3c1b5c73aa554c2b6870cc21202544212c70f60d4a09c8215649bdff7021243fe82c0c2a542c1241580c0c4cf423b55fe826082150eedc2124306c7c342534671c4b3dfee24eb422b07c391014541c7b98302c11bc2824212c74ec92f0141dfee816b47505ff14525634ae134026349c1a025421542530432439842c9b41802534215425a82c9dfee05cda1ae4356c163c199a143a4e8020d82c914e0021200a942f8910225115e398169c4af071e87359ff773d9821266dd65d5421b423b82608575e3820215238983ff8738c71ec23dc2c0c2122348823b60999ec9e4f183ba8357e9e244f3a4eb1afd8173806f42ac1102c6258215c2c6c3028305c23e24e80725023ba01a424c8249c2bd824f0260e01a023b841741b806d9a78c65c9e554e0258212601a0212023bc378c7f289b4c62608eb474d23c3c2b3e4fa543f02c9423b55fa035c95fd80654234c14702d20215 else 0x2158037213202c0e522a01a423dcb2782494260a0171ff2c23d4212042329e260855e82e01a4c094212c6760283823ee4ff01de0215025480f565114417201ac74640155fe9421224faa025c743023d825302125ded4253c2bd820e1ff0a38442c9a0250710023e417f4218e5540212018064e8c212823e820741508214e4e8c215023ba4e880931ddf423b42b005eac4ad807c026082bd0214a4ebb485c435a539421542c9c206474d899523dbb41806311103c21507af82c9dff7a42d42568c09274a070c60a5827ea749823b823b609c967564faf868c22404b182c941cf82c0870f81c865135fee42c9c285c069470fa33c63af9508229002a3821501da823b0eea809c9feec49c82b82594c21642c0201947100957c2c020a50743c735022bc1c5823e800042c902fd423d074dc2f8c93760198008a43f21d78c09a4fa46168738021540df1af4845d4254073500a0023b023624ebc6f403ffc253816fe653823b425a021682169dffc249241600a340fd82f01af4423e423bc2152514427ec2b30119ccb4a4a0c181c1f502538310c216c27c023b02fdc33e5ff1c2c1e19602126407e41b4215423bc23b070f9e4f8159870c6092e017816ac2224260423f21a31af800b8c2fb0212423dc0a140e7823ec3ff823ea589023bc23e8214413c43fb8253c209023e42f89666458fc249027e9fea4979c212670bcd5cc30a474da58e24ec6094804d423bc27a060e02fd825442498048c05b42be4710475024a79dfb163182c0894b8cb4c215823ec75a82126a90a1fea01904b8c4b4010dd04687350215421201d00059c2120214c2f61f3de33d825b82accc54c2120019824901cb5ff7c2fd38c80077470e027e4726e4e8c8306554c23b5fee9feed6644735023b422bc051423b42c0c2c9823be4e872dac23d82128253e505c2c9c2c9423b42f502c9c23e297f424be02f82158263427e023e437d4212a19f9fee655482c0c01f427c04a3c2c0a4e885bfe4ea02c0876940bb423dc214a596235ea4eb8143c21200fc60d87427c2c0846ac735e017a546c21224eb02c91fee449a423e42f8821542c9c2c9857a023e0215cc0980f90778603c24f1dfeea09c073842165feee511027e074d0c0902c6c7c3823bc2a9e2d9c1c604eb406bc750c212c1148413c3ff8249849f44515ff1c35b82fa4215c2b51feec23b4c4b5fee64dd821240d10057601a423de4eb424c8451e2e241d180e442129142008a6a0b021241d482c9c212c23e1e7d02c08253c172826345c2c70cc224448424eb0215c3628222c2bd65ce873542569603813a471502f8c03b29fb4263341882634212e09ca63849770089c263dfae423d470ca5130260c16e5fee82c978d3470c47ba017c69e243c201ea42160735473544730212a07fa486a5cf0641c215473981821efd80c9) else (if i<3 then 0x464082c900000000c35989c5c27ec27c000000000000000042d2c215800d023b5ef14212d1ae424cc23b8c09c263823e4434458a02121df947f2c4226ee05f5542f220d98254f8e982565fd911124103823e423e90150215873584bac216823b95fa877c03c8815c58220056821502c0423ddff7823ba35d6025c3ff00d2421580e0823d247e81ccc23b843ae4f142c0589c9ff781dc83fb8735c1c9023e25864224c2c5e6a3a01a255400810c09c249421be4eb0108c70c8735019c0212422bc2c602b5c954c2d202154256d6030861dfd702634240877842d1c0c502c9023b8735800ac91be7794026a0d9075a81eb421b0212c2c05ff20735474d4245821228de02c0025682ba02fd421621a3c735482b03fb423b023e0215403e49b1cc0902125ef6e36b023e84185deec121427e81f2c592206a02c0400b41c002ca4212c70f0249c2cdc13fc21202c982128423907e8254d623021242c107ecc3eb82ca424991020215407464eb431fc739e59fdff7040842cac2c9237cd10265111fb5c01b5fee023ee58202150253c23e821221d70215c152a58221dbdff7c94b1ff7d0432554c19e80f1448481a8c215c21581b2827ee017e4e80315255409f302b5c285c0428254470c427ea38503bf823d651b8212d17f47c395efc061c222c27091024215201acc09c28e074d41f78256c70c213f023b82bde4e347c32017c062c6b504290c4840aa82bd80d847ba421bc21440b307358212474e1e0186a20256c2150212423d88f9c70c835c02c0497d02b02355d1318cb4c2c90c090363e2078022070f82c0423e82a5e36702f042fdc2154212c2c14212030f659f8263201a42472099a443a419dfdb1521028204cb023b023bc23be513823ec675126702b8442b82bd823b021b15fa82b52513870fc064c40742128215470f070fe4ebe5e086100451a58dc21282bd421420e28198423e86b3e25b413b0305073882c90097c43d473502122099e554a5540260601a48440212827e81b16554c35d2030c59a428201925e7184c6e07d4256a01782c903c040f2201a8216855be59361c7c2549e90252d82c980bec2180c09823b02540238e01ac2854254021482120376070f02c0023b644b0483e01ae52a870c027e027cc34a470f0923262064ea07b74200341b02c9c2c0c2c0827e470c855c43068302c2a3c70c81fb80838216209482b0a37e87f1c13e0216423ea025822482120212c2b802150735426082c00226c0dc487702c9070f651345421021827ec2c9821447356133c75d82c122cf823e821502c0aedc655482c0910242f847370127c2c995f08212470c4215e786474e427c021224ea835dc034dedec59fc3fe87f282c904b91e9b85f8a4ebc70c475042531ec1e01a427e423b4157c23be01aa05ac73842c9421242c9474d else (if i<4 then 0x4c0a000020e28216a09cc70f823b00009af7a356411a2099421447ba8212823e84f04212423e601ac215e51138d32017e017070fc1420165e4eaa3bb41a13b18419556ad02a9c223823daf484216cc0900001f5b021582550282a01782121fee1ff1823e000002490000c60fc212c56be4fadff0017147efc2c969eb000002c9023e43b700000000c21224f10000000080fb00004212447d00000000807b870cc23d0000447684b642c900000254063c251346fec2814215000045be603000000000c4c31fee87bb044cdfadc226e51900004052801ea01ac2c0027cc21583c356b9423d0000470f000041d9a554a554601a00000000827e0000a1ef0000023d427e33d924e8dfee027ec216023b421542128305000000000000019a0000020b202523b200000000000002c90000c20800000000201a00008256650cc56f201f33d9000087f2a51100ae025b4215009d421b02530000409500005af807c3234c0000df03423ee01a470c437585da00008215807082bd4224470ce4e825130b9e43fca4ea1ff74215823b823e64f1a025c24c823b421b0215c202000043685ff7d25e000081df422c8212c21500006a5d4215c0ce429fc3dbc260000045df4e8f1fee02120000c710421283dde0170000470fc21240cc4215dfeec44d0212023e000041d707100000a007a01a601adeeb802902c9602542bd024221cac27e023b82c9c42a000064f1000000d08249407907380000023b203c023b0214c2120086209403ff0000054cc23ee5540000c212000002f1000082f80216a4fa2019000064eba25f9ff2070fc253c3fb201f874d47430212425300000cb500b4407ec735c710023e42c6e025013187ba55facc0983fb023e0253474d64e8c23e601f60190000c23b47ba02c19edd5feec2c9a501c23ec2b803fd41171ff7c370821b42c94028c566962347690000411507354830c2538215a4091623e19bc743000081660000c183e01a07b82058825300cb0000c257203c00002edf601aa01aa0d2e4f1c23ef3d90000c4a0000087464122aed18212e4ec8c25023b201a00004236c45100000203c253070c2025000000004249ddf1c41343efe4eb0279e0a6474d023b021264f1dff40000000045038100c21200110000c74d209c023e60199febc23be01ac23e000000004710000002c9dff751034672e4eb5ff08249077c017a0000c212c253a52ccbfe02b85571c2530000c7ca8738c21269e2e017c73502bdc23e421580db0738419b60a5825382bd96a8c212c57d02c9e52c69e600000000c24982c902bd00008214d5fe00004212023b0000023e027c00008212021503040000423e24ebc21602534effc099a0194212833145055103022c000000009623dfee42f84336c2c024eb9feedbb35fee823b0000c1180000c26082c9c5fd00000000 else 0x1f8445a83584c0964e8000000cd027e42c086b19ff242f843ddc71083ee423e823e4c4885a40214c21b0000c21202d2423e04088058287500009ff74502000021b90212a0120000a5110000c23b425387358c489fee000061d7c212072ec2b8021202156025411242156a90e10d82128253cce402636099821bc2f80000050f02150000e0d407125feec47da59fa007c754823b9e31e4ec80b582498215823b0000a4ea023b000015a182120000823bc0390253824900000212000084160000c70c423b000000000000000006080000c21624ebc21200000000c21582f891429fee0000823e0212070c9eec823b000047c302c9000000000000a5ca06560000605a000040b600000715000096a600008236c1e90000e522023b00000214823ee52ccc0900000000821b47381fee82538021000000009f6c425441ec473587c300000000a4eb08bc5ff1a344423ea025421b83da07bb42b88c080000c212c236c2c008d5c23ba52c00009ef720a50000c1100c09000001ba87500000d102c1e8e4eb000044ba6a8e024901d5431bb3d8b911423d07bbc2bd00004335094b20a5a51160a5021be5110000c2c6823b1fee421242c9a5010000402a000087afc67a000061d7a4f1027cc27e8155441a82430000e01ac17dc23b8216827e423e014ddfee41edc236cb4c02498216c04be025c17b005c474dc75a4249601795fe823d423b78d3c1a2c22b070c02c6c1619df4423e070c0405a59fc46956031ef486ef823fe0a2e554423d429cc244070e873869e6c16282fd02bd4451c21582c9c2534735c2c0474302fd00009ff24212e017410742c002120000000084d020d9423e0000e02500000215c06a4c08009600000750c23b83c3c2c00754421400000000a017c030000041a4c5070212809b8212a32f202e00000000e59f42ef0158423b026080ac4215c212821200002edc0000000000009095021b02120000d103e4eb000000009fee00000000c23d0000d5fd09ea03fb000f0000a58e000000000000c70f02b8811624ea000045f500000000d5fec70c41ee9e948111c23b00009feed0f9000024e8c05d423e8212c30ac09f42850000c003823b5fee42124738640c021200001fee877882c00000823b61120000c5f640e2023e821b4483b418059dc2c9423ea33fe713023bc2b50212074d42150000c0f70362124a00004c09424cc27a0000070cdfeee47a263d0000005e0573c5c3c1aaa06ac75a48cec2c1818907c483b5c28042120c48c70cc7bae09c0000c0d9201700008025821242c063e5c23b43bf5fff023b01d6425600000000e5540000348442c0023b006ce5130000027c9ff1000065140000c70f00004224018d1af4a63d0080830e6025c2120000a73000002025e646c21297ff0000000081c20000230800002513c237c2c90000))) else (if i<7 then (if i<6 then 0xc21400009ee7c10f021bc212c1063adf8c09801200320102849a1fee07b800001defe0e482155af800001e9600008215c7ba0000000040da5feec5774249470c0000c4af02c08014008ec212c77c070f873807492f9b023d0000473800000301027ec2162554421543fb0000a025272747ec07af82c9000040c7f8e983bf41440000023dc3fc4b9cc1536030870c8214e51f82bdc18a490c021be3596513012dc21282128254c6ecc2b0c70c96034260023bc7698216a4eba0d30000414cc2a0d142de9e02248212c6c205f482158b664cb4e597821607ba1df0959f636fe55484d7404e07c38d2a2331c212070f05fe82159fee42a500000000023b8124425426030000830904f983dda643df9a000002600215021b470f423b82044417b4bdc7784212f8d3823da03f250c0379650c42c06017c75084aedfeec6180000c0d5e554c37ac253e01a64e881040000821287bac24b82120738c007070fc2b80000000002b582c09e4c80ca0000001dc901e01a0000a5540000000001e1e4f1b3d8423b82c04715823b21d842120af089a95dfe823b842fe4fa02539ff7427c9feec23e82f38090021b209c8212816c026342fd1ba081850000877842244253a02f02b883fd0000510482140000615924ebc1498256025600000c0f0212427e8263023d02150215c73881ab870fc23ec212c627a5ce1fee42490000023ec1c702120000821b00010000e4ea48ee42fd4212412aa09c423f202505aa81f1000001f0c2150046427edfeee4e8202b66074253601ac37201c400004212c06842c9000002b8829d4241000002499fdcc2c9094b01461fb482120000000080c302560000c0768cb4658900004249dd0603fd15fa0000a0e280b78212802f4215812900000000023bc2c90285c7bb823bc21500001ff16025c336a4e833df823ec2c01ff72406c27c823bc2156554470ce6f942f8c22b423b855483fb4476c21b32f791dd824346eec2c015fac2c91feec27e408d80e6c21542f882536002827e470f1fee4381470fd1af64eb401ac70f2e044215823e0710423b64ee21348215c2a3e511a4e802a70c0941dda0194187028e423e02c9e727c075021240ff6aa1027e8212c212a19c33d9e07964f843b84cb4810e20d9a62fc25385fa4256823b46c147352030827e0264601ac23bc2154188c0d6023b427c02b81e7c24fa404502c05ff7c27e821529e2c63ac40382ac081b06af42a5cc098049a01a423e427e81cde01a057c423bc0d44214421242160035074e5e9a9fee4253c451c02da4eb8212c27c2511823e24e862eb1fe2c1ffa01a421202b8828564eb83c700000212827e0000413382bd201a0224c216470f219fc4a333d942140260652c4623658aa51c423e5eca0212c24300f4c253c23b423ec2ac82128215c74dc21b4215c215c2f48249 else 0x426fa0a5023b8439426460782536070ff8d300bac212826343c3e09a823b00004215870f00a7000002b8027e00c280de0000427e9fee021502c0423b5f5e0000c21b0184a98c027edff742bdc2bf0000201a4253c27ec2c49feec735c23e9ef52ee05fee023be4eb0000203c00006025470fc6b4000001a30000423b64ebc2b5e98bc23e0000c21282d24212e511252c02c0c27e021542bdc23e8027821bc2c94212a58247b7e4eb874d219bc23d823e9103028d023b024f601709ae42c9c2c9c23ec21543c5c215c21529e2c23b0000c0064215a425823b0000c212c253c2152a8e8215966a00171ff2c24ca01a8412c27ec212a5540000811d8710c08ce01aa0d1823b00004256258e021240160000470c873542c91fde42fdc1be560c4215421501489fee0000c80400028937421253be07ba474e24eb82b88679811f9dea4c096be22554c738804fdf58e099a97dc27e874d4710aedf8212074e9feea03081fcc306c213a4eb8254823b023e025685e8827e423b0236c27e4013a099429142bf60944215e01a209c470f027c42b00000a09cdff20214255407f26650023b07af0000824c42c900e340721e02027e41d824eb8469e0d4426f241ec28e63c465de0038473864ec1e954249848f823e423b050d000041ef023b021564eb8214c45fa55442158214a4eb0000c21b0000000000000000c23ec2158419877c823bf4b365cd8215c1e44215a296c2bd81f6c215470f436702050000460a255482b51617047cc738c21264f141b7c4bba4eb021247c3421202c9a01a23430748874dc7384047eac70000609c8738edcfa5394031110940430000023e9ddcc408875a8253c1c3000007ed8c094212510362fb823b42bd6a0e47230000c23b023e4214000060178130c738c21283ca0c080000499dc21202b3000045749fee024f11420000e030c2c9e59343fbc21605ab0000824900009103c8f7800e823d024900004735c21287f38136800cc3eb000002c90000c2c9070c5fee0000c2535feee536c517c0b9023b070c000009ed6494823b24eae50ca4e80c09000064e84249023b8214024942c083f20000c2548212e4eb815a424c201725f6e0a6021482c98212024920d9c3cd609c023b061116200963c08bc746d137821202560000c21542f90256b7d482b524ec1f940000c7c342158407037147385ff4dff28957e4aec23b828241e6c24c41fe209d0c0a043541e00000823e00008224821204b2000002c9d103421500001ef342c9c7c3c47d027e0194023b023ec212f7dc29e5601a024982121142e09c646004eec260474300a4807d17c541adc3778738c256c2709104c1fd01af02bd0738c27e84dc821242310000025302c042c0876a00c46557854002498212a41a07ba2511209c02492017a52503fb82150000000002f8c2490475) else (if i<8 then 0xe01ac212000082c981ca0000c00486ff824984b502c0a511659495f100006126252cc0cfc27e00000000421602c000000000c21242c0e5546511658647b70000c23b823e0263c40842a3251383c5023bc2c6635261faa33e0000421b02f84c098224c516097e0224000003580000849b0417d5fa6081000000001ea84c0f84b7821202bdc254823e02c0201a2357e017000024088249821b805a423b00004128e512c212c23b83d264ea23f8203c9de402b8823d823e9e795f0442120000c21582c96017a01755faa47bc738c0bf000042604212209902c0201acc1f823b00000040c215071c823d823e44b4c216c27cc23b87c302f000008712c2490236c12f82a1c2534249c22621f5b8e782b847381ff70000000064eb0000c2a3c212870c02b5a09ac3fdc23e0224a03c2478021b073541b082c942490000c71066950000423b9142a05a02128215c15b81aec70fc23e03fb02c942158216421584060216c193c15e0060021b821504af023b0215a2ec82124190792d6c97421582c9e58120171e3ac21b006dc11e51ae000042c90000c23b823b0000423db3d8c23ec2c95ffed5fa40e1000002f802c940d3c249c215c3d46bf40000c212c2c0c21b024ce03c0216c2c0e01900e9823be09a0000025b82c100009df782c99feec23ea4f1c2c984fd4cb4d1034cb44212d103c082070f823b275205c4dff2a02502c9653605c9609c021b0000c42402c9025a24200956c2c0421b07bac1a747150215894b8197951ff3d801a5c29e00000215a09c870c063b86e202b89ff281b6e008023b027b0000e06ac212c21282220000a4eb04db0000804a4212c253b8d4de93c35e42b84260023ec212023b65195df8000065148282421260199fee0000c1c1423ec0d7c7c7470f0215070f823e00000260421282c065360000c23ec2c92554e03c64f1609cc4ba8178d5fac2b71dec8087c2150249003c827a00a54053000002bd82c9203c84211ff0c21500ec4215c21287af8576c02300000000eb98870f017900006019874d82c00254c2c060179deb0000000082c09f5a02b884ac06178c4800180000c21b8c4840550216201a02380000e3d700000000000000001feec36a0000df38c21242534212a5cee4f149b00000c16d0000407102c9824c42b8c8ffc1b96552027e0000473502490000c2150000e4eadfee823b0000e9e60000421582b8e09915fa00004191dfee000040849f71024fc70c2511a4eac0af0000c8b9c12660d9c2fc000042151e32c125457e000000000000428e0000c23b81b46514c12e00000000012304ba02f800009ff7000006da55955e800000025455220000c27e00001f9002c9445f2025e09c023b0000a0250000821502c9809401a0a59627c6030ac2c9021202a5000084b602f90000c2b54215c70e00440000423ecad5 else (if i<9 then 0xc21202f1a01a2058e01a026fc18ee413825703ec83bf82cac7fbd104c21581740249cf4bd5a0c2fd850605f98212601a870c84f324ea470f864382f80270000085a182b4470ca4f1023b60e6e9e200002501c212e554014e4738c1f924eb203c00004135c15fc2f7601a423b427c8212c710c186637500004cb44212ebd5c21542630367c23e0000c7ba45a9e522daf44ae582b5451084350725c9a8c14bc45d00b2827e60d9423d470ec2158212c282070f02c9e4f89ff7c10a47c3a38102a8c253c23600008b4984330000c8cc0000000002b584ba423ea4fce4eac256c451000025460216601ae6de0000824c15fa421b24eb027e05985ff2023d420f65110212e514423e82be49ab8746870c023b0000423ba59602140088827e8750c750827e1e3824eb42bd023e423d021538d3202524eac2705f63c27ee354c23e0212423ea30182123912d5fa8256c14a82c9020a04b5d102e556051f9103c23d02128215510282f8021282f843cb4253423e252582bde09c87ba01e5c2c9831e427e0000c2c94078e07fc3022019a0a583c780ddc212423c822442c000001fb1000001db960ccd6d821507505e00c2a325118215c229843587454291a02564eb82b5c253406655fa822482125ff2c22fc21b42158212a01ae4a186cb5f5c823d6513de4d82c924e842c0de2b0000601a8252c23e427ec23e9fee42bd423b023ba582c21b816740a202bdc2c0c08f053fc256d1039fb9074e823b62de4263e558c21507504215c417c0efc2abc5824c094212a554023e2511423ee01a64e80ec45f014c094212c254c2c9e57f0137c23ec23e821b9ecf01f3420102125e73a4eb85f782150109424c42c1803301d282155af40000824902150212470f823e60d442c9042bc138c260a58bc36602538249027ec2b5c23b02248256c7b2410c602f823d0c09a03cc73847740000c10bc70c7484c264441ea3b0a01a823bc23b45a882150000418c423e209c02c040e8870c42851ff7cc48023b0000c2150000417e64ebe53003f10000474e64eb00000000c212000064e8423dc216870f8212c010047dd623251fc27eeee0c26002c5c33624e847ccc23e423b023bc23d427ea327827e8256c2158215c23b421bc249416047c351ae070fc21282bd827e41bfc22440854735023be64f51038063000044b0074d047f24eb8c482edc42530000423ec4e84254c1394212b3d81e07c21507c30000000080f0a5138036c2240215021be01700000253a0170214000055fadff1823be0a10263426042bd41bd5ff7255400008253099a023bc2c9825bc1a964fac23b427e0000a02800006191e58b0000000002490ce3a1b90000023b82122511874d0000823b2467023ec263018b00000000021582f8023be4ee0000dff20000874d007f40ee0000070c030888fd42148642 else 0x9fee8216423d4743021200000000000081d301cec215421b60a542f60000e4f160178105c7b7e43164eb0000000007c30000000042c90000ccb40000c23b8164201ea465870702168249000000005e6b425342120000422b827ec27e82a502abcc0982c9000002c000006017201a023e23fc40509fee00008212a0306554a7c7c4074215423b4307a50c46be823ed8dec24c24e842c0232982c047bac23e0000823e823bc23b64e880eb814000008214c23b821501e7024c9459421244ebc710021ba4e86a0e024cc212472b2017024e8236c21202f70249873542fd82fd655449a9603002c00c09c74d86ab4263e017203cc74d021547b7419d023b874d821604c7023d42f842820000424c60d4c2c1e01af3dfc47ec2535ff0a1e3023b85ee000024ecc27e81b324f1470f00000000d1038212821282b8a54f02bd8215a552402c82c080ab0215cc08c70cc2120000023e568d4619821282638ced421b0739a019c2be021bdfee417022dfa64c80a647501102c13207354c0942f80000641d823ac2ac00f8874d95fa0000470ccc091feec21582c09df6823bc4ba82120212638bc28e90606554c2248e15c738a24fc2fd43688750c0738212823b8243000024eb421506dbc168a554dfee652ac21502124216e5112025c74d01bb4249c74647b200bd00050000870e8c09823bc3fb4572023b000084f10c0902c0c23b9fee874dc2c9c21482b544b102c9a51442b59fddc74325d30212c2b7421b64fa82120000023fa4144407c23e9f93649342c942b524ebc2c9c746c2bd2056635002bdc20cc212c2c900b1c2c1023ea09c9e2215fa8098c4cec9b50c0924eb5ff7a03c33da5ff702534ad68215023e835ec75ae596423b82155fee9feec2600000608415a25623e1dba207c23e64e8a554e019a4eb82c0c214823bc27e1feec134821264eb60d4422b021242f9824955fa40ad0000890142c0cc3307ba89aa9f020000a51464f122cd9feec041870c252542bd4710436f48c40429023b9e4bc2f8021b5ff2045ce017424c00000120dea221e121a1c7370000c2158305423b4215002e8091077f8212801c82c0003dc23b036ddff144290735432d95fa46b0c31641a6c7c342c9025a8214e0250246c451f7b0a513023b423dc7c3427e825402fe4373030d2386c70fc23e06959e04023b0282815ddfe1c06741139ff74c09827c821b81ac023e24fa82be01fa29e20260677906e15ff71e9de4ebc2fd8215d102875a427e4320))))
def liveIndexShift13 (i : Nat) : Nat := 0xe2770cb08056019801480e07c1709c023cc00000003c000014a408c18000c2001c711c21000980601e3cc0a3100707800184443d6440167c01023000280380f7c4034ac850040369c030000b0600209c163f0cd044162b5306100800405010730f8270000000c2e0280000401650017681a018095b423000440018d2bc140a8140000003c110045b0500600c02000030180501005008910cc2808c0101007008191a802070020003e098000ec00030030380a014230280d0140127c000080002815064000040543c05020d80040409804064020040501c04009c28b8010182900010008460000e0016800004010013315a0140e5b40207d7803402000000940a0000d06c1805ca305403
def liveIndexValues13 (i : Nat) : Nat := (if i<1 then 0x1a9ec4af81bf032b801613d00000c055000097f5447c80b2c02f4004c4c217e640c78420c3e3c45cc020c4832b80c4d201c2c40200095da780ab5917c04c410f9c23175d045d984f01cb5c04c32e00e000001c08000080239e5540605fabc0845952c345000040d340350094d7dec0ff98225a9d826bc1fac06941fa40598446008d00b40c1d975f97fddc4880b70000c06600aad79640ee40cc0000c0dd00dac0375821984c17c5006c44669ed741c29774d7e50435dbc1d7d6487d1c29c31f0083001c8461407505a6041ac0cbd77c83e643460074003b40985a86800004d4045241004405c0d7ebd7c0b800fb00274333804381c2402c01ff9bad57e4d7a29da98057805440b040e944c397ef577a04ca408a17b38045032e805fd952983440705bb71cfe9bb81bccd85280ec976840e7407e191a8063402208d45bee872b80d948394012d7a0406dc3fa800eda8b406f4005c0e8400344cc409e803a0040d7ed041d1c271779480c08d540d1c1c25bc280959a9d405881abd7ecc0e440b517b100f58091db69c729410c00f30703179484e400a3c1cb801fc03100e388a901ff1bb0979981051b80449e80794092c10a6759006704281c1d5bebd05ec5e3407b80f900518015c0ac8032c00c5c2684e0d76500c3c47e5f3184dbc0334101402ac4b6808f4459405ec01e9c20db9e042d0421046e80768080c00b97915b9dc26e802988d387121bb95b525d3b1763c00701bf4050410e41c29b72c467c0c00474804917d8871200c80090008e00a2c05605dec0895790c082005b800d1e6757b0c442c08cc1cb009ae7f403e94042c87cc2f540a60077408b405c01098014c1c2d86140a7c0bb432e44319c0bd7e24fec40ea80cf803640ae01ff5bcb81bfd820c3478044845b442b5b8c8008009b804a191727f6804b801d272cc0b100bf41ff44ec1c2ac47b00b9c345dbb64028c5a3c0a5c0a0c06845a380d8d75c40a8004817d585e3001840efc04100c1809741cbd75ac0c91da901cbd84a01108453dc49403f03f8406a00308491801ac1c240d480c2c106db8d808840cd4053c0be185fc0a9044084d085e341bf5903c0f040bd67c9807a409981ff40345fba58604087401b810884cb00f79bc05850c1bf9bfcc06b97a94010048840f6c02517fc407f003d80389805c00284ee44a4077fc102d84bc0e1405dc0e21bac191a9fee80ca40b69917403904638103c0ad8011578e182641fadf7cc0e500c44473d7be582ec072004f1bb3800a9ce7c1fa00bc80f8c0249827d9c51d3640195b5140a4995780af0086c5e3005a40df5daa80fa00dcd80a9c1c404e039b826240fd046ad8189bcf8346c3e8c45a000180ba57a303e79bce8064579a0096c09dc07357cc600343f5049740f4d95780ce0319c2f9c5e3c8d6c0de9c24177d44ac00d580c6 else 0x409c8347c803a723c0f257ac026d1e5bc4cdc5a345a340d2c1bfc4ebd40e57601cfbc0710026c01740130085d806c03e04e9003c00001bc9c1f4c0fc5c0ec02e983c9c0c40f140eb57adc0789bf7449001c2176a041cdb5c1442009f57974062db99441f80fe00b3c04d000fc05219c5802d9a88db9c200cc4de27f541fa9c4a1bb2d9174cba179583e547140cb91853576ec10bc06ec4c7044341bf04dfc00681c20330806141119bc88107000081ff000044b24081404757f247125bec00c50000847540ed84324104984557d9581104e5406545d8d7b480d657f6807c00a1db8b407dc26e5855db778345802b4482c0db026d810d05af846fd7ba991a4046cc8d902a40d0000000005b5d8021809300e6db88c7290485)
def liveIndexShift14 (i : Nat) : Nat := 0x78060804b3550000a1074363
def liveIndexValues14 (i : Nat) : Nat := 0x267e81f7987a0d1b213c0c00001140030e0030485f85999069e81adac005c1080001247d0cc0616d9d1d1e00000a681d4009b40061918c3c0082c009d3101a705dc77cc670a9f420
def liveIndex : Nat → Nat → Option (Nat × Nat)
  | 9 => fun h => let s := packedAt liveIndexShift9 ((h % 2)*3) 3; let v := packedAt liveIndexValues9 (((h/2+s)%7)*11) 11; if (v >>> 9) == (h/14)%4 then let a := v % 512; some (a % 277,a/277) else none
  | 10 => fun h => let s := packedAt liveIndexShift10 ((h % 83)*8) 8; let v := packedAt liveIndexValues10 (((h/83+s)%257)*15) 15; if (v >>> 13) == (h/21331)%4 then let a := v % 8192; some (a % 464,a/464) else none
  | 11 => fun h => let s := packedAt liveIndexShift11 ((h % 1010)*12) 12; let v := packedAt liveIndexValues11 (((h/1010+s)%3271)*16) 16; if (v >>> 14) == (h/3303710)%4 then let a := v % 16384; some (a % 893,a/893) else none
  | 12 => fun h => let s := packedAt liveIndexShift12 ((h % 1533)*13) 13; let v := packedAt liveIndexValues12 (((h/1533+s)%5058)*16) 16; if (v >>> 14) == (h/7753914)%4 then let a := v % 16384; some (a % 1274,a/1274) else none
  | 13 => fun h => let s := packedAt liveIndexShift13 ((h % 213)*10) 10; let v := packedAt liveIndexValues13 (((h/213+s)%652)*16) 16; if (v >>> 14) == (h/138876)%4 then let a := v % 16384; some (a % 996,a/996) else none
  | 14 => fun h => let s := packedAt liveIndexShift14 ((h % 16)*6) 6; let v := packedAt liveIndexValues14 (((h/16+s)%58)*10) 10; if (v >>> 8) == (h/928)%4 then let a := v % 256; some (a % 17,a/17) else none
  | _ => fun _ => none

def samples : Array (Bits × Bits) :=
  let padding : Bits := 0x0
  #[(0xa2190815e901072fd0f351981e1510070128,0xd4130104d1590f2980414190121510030128),(0x1c9ec00108a527806c1ca049bf3e8794f654,0x94cca430802c000681c8009ad0a0694f654),(0xc2756405028095db42767126370204911e8,0x2402148c24200c1d942327020270204001a8),(0x4060d102044e93aaca5c94d708cc5e297a14,0xc0b4c031c2ce8382425c90d108045e297810),(0x2b083cc2240270501fa32a26a5c9f4840495,0x2b083cc2240070501da22a26a5c8a0840485),(0xc18020b92712e8867940be07a022cefe59a2,0x3a8d419262600867900b407a020c47c5880),(0x72b2041cc4cc20d29342896200b0f929a429,0x72b2041cc4cc20d29342094200b0f9290021),(0xd0012262d8119061038c48f9598f2b122a83,0xd0012262d8119060028c48f8598f0b022203),(0x5408dcc82504e3904a943a8d74200e2474f,0xc4129c009115c2904a1422857420082074e)]

def symmetries : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[116,80,100,128,48,32,16],[116,83,32],[100,116,81,128,49,32],[118,133,33,48],[82,129,48],[100,131,116,50,33,16,80],[116,50,129,80],[100,49,128],[116,100,49,32,81,128]]

def columns : IndexTree ColumnInfo := (.fork 101 (.fork 50 (.fork 25 (.fork 12 (.fork 6 (.fork 3 (.leaf [(0,1,460,50,8),(1,0,510,0,12),(0,2,440,69,8)]) (.leaf [(2,0,509,0,12),(2,0,2557,0,11),(1,2,440,68,7)])) (.fork 3 (.leaf [(2,1,460,48,7),(3,0,508,0,9),(0,4,369,138,8)]) (.leaf [(4,0,507,0,12),(4,0,2555,0,11),(5,0,506,0,8)]))) (.fork 6 (.fork 3 (.leaf [(2,4,369,136,7),(4,2,440,65,7),(6,0,505,0,9)]) (.leaf [(6,0,2553,0,8),(5,2,440,64,6),(7,0,504,0,7)])) (.fork 3 (.leaf [(0,8,227,276,8),(8,0,503,0,12),(9,0,486,0,8)]) (.leaf [(10,0,501,0,8),(11,0,484,0,5),(4,8,227,272,7),(8,4,369,130,7)])))) (.fork 12 (.fork 6 (.fork 3 (.leaf [(12,0,499,0,9),(13,0,482,0,5),(10,4,369,128,6)]) (.leaf [(14,0,497,0,7),(0,16,486,9,10),(16,0,495,0,13)])) (.fork 3 (.leaf [(16,0,2543,0,13),(1,16,486,8,9),(16,1,460,34,7)]) (.leaf [(17,0,494,0,11),(18,0,493,0,9),(18,0,2541,0,9)]))) (.fork 6 (.fork 3 (.leaf [(17,2,424,68,6),(18,1,460,32,6),(19,0,492,0,8)]) (.leaf [(21,0,490,0,7),(6,16,480,9,6),(18,4,353,136,6)])) (.fork 3 (.leaf [(20,2,424,65,6),(8,16,486,1,9),(24,0,487,0,11)]) (.leaf [(9,16,486,0,8),(25,0,486,0,8),(20,8,227,256,6),(24,4,353,130,6)]))))) (.fork 25 (.fork 12 (.fork 6 (.fork 3 (.leaf [(28,0,355,0,7),(0,32,94,385,8),(32,0,479,0,12)]) (.leaf [(32,0,2527,0,11),(1,32,94,384,7),(32,1,460,18,7)])) (.fork 3 (.leaf [(33,0,478,0,9),(34,1,460,16,6),(35,0,476,0,7)]) (.leaf [(36,0,347,0,8),(40,0,471,0,8),(41,0,454,0,5)]))) (.fork 6 (.fork 3 (.leaf [(17,32,78,384,6),(48,1,460,2,6),(49,0,462,0,8)]) (.leaf [(50,0,460,0,5),(40,16,454,1,6),(56,0,455,0,7)])) (.fork 3 (.leaf [(0,64,189,258,10),(0,64,2237,258,9),(64,0,2495,0,13)]) (.leaf [(64,1,396,50,7),(2,64,189,256,9),(2,64,2237,256,8),(64,2,440,5,7)])))) (.fork 13 (.fork 6 (.fork 3 (.leaf [(66,0,445,0,11),(66,0,2493,0,10),(65,2,440,4,6)]) (.leaf [(66,1,396,48,6),(67,0,444,0,8),(66,4,305,136,6)])) (.fork 3 (.leaf [(68,2,440,1,6),(70,0,441,0,8),(70,0,2489,0,7)]) (.leaf [(72,0,183,0,8),(73,0,422,0,5),(74,0,437,0,7),(68,8,163,272,6)]))) (.fork 6 (.fork 3 (.leaf [(72,4,305,130,6),(80,0,431,0,11),(80,0,2479,0,11)]) (.leaf [(80,1,396,34,6),(80,2,424,5,6),(82,0,429,0,8)])) (.fork 3 (.leaf [(82,0,2477,0,8),(80,8,163,260,6),(96,0,415,0,9)]) (.leaf [(96,0,2463,0,9),(65,32,30,384,6),(96,1,396,18,6),(98,0,413,0,7)])))))) (.fork 51 (.fork 25 (.fork 12 (.fork 6 (.fork 3 (.leaf [(128,0,383,0,13),(128,0,2431,0,13),(128,1,332,50,7)]) (.leaf [(129,0,382,0,9),(128,2,312,69,7),(130,0,381,0,9)])) (.fork 3 (.leaf [(130,0,2429,0,9),(130,1,332,48,6),(4,128,347,32,9)]) (.leaf [(4,128,2395,32,8),(128,4,369,10,7),(132,0,379,0,11)]))) (.fork 6 (.fork 3 (.leaf [(132,0,2427,0,10),(133,0,378,0,7),(130,4,369,8,6)]) (.leaf [(132,2,312,65,6),(134,0,377,0,8),(134,0,2425,0,7)])) (.fork 3 (.leaf [(128,8,99,276,7),(136,0,375,0,9),(132,8,99,272,6)]) (.leaf [(136,4,369,2,6),(140,0,371,0,8),(144,0,367,0,11),(144,0,2415,0,11)])))) (.fork 13 (.fork 6 (.fork 3 (.leaf [(144,1,332,34,6),(145,0,366,0,8),(146,0,365,0,7)]) (.leaf [(148,0,355,0,7),(32,128,347,4,9),(160,0,351,0,11)])) (.fork 3 (.leaf [(160,0,2399,0,10),(129,32,94,256,6),(160,1,332,18,6)]) (.leaf [(161,0,350,0,8),(162,0,349,0,7),(36,128,347,0,8),(36,128,2395,0,7)]))) (.fork 6 (.fork 3 (.leaf [(164,0,347,0,8),(164,0,2395,0,7),(40,128,339,4,6)]) (.leaf [(144,32,78,257,6),(176,0,334,0,7),(192,0,2367,0,10)])) (.fork 3 (.leaf [(192,2,312,5,6),(194,0,317,0,8),(194,0,2365,0,7)]) (.leaf [(192,4,305,10,6),(196,0,313,0,7),(192,32,30,257,6),(0,256,151,104,8)]))))) (.fork 25 (.fork 12 (.fork 6 (.fork 3 (.leaf [(256,0,255,0,12),(256,0,2303,0,11),(257,0,254,0,8)]) (.leaf [(258,0,189,0,8),(258,0,2237,0,7),(260,0,251,0,8)])) (.fork 3 (.leaf [(8,256,151,96,7),(256,8,227,20,7),(264,0,247,0,9)]) (.leaf [(265,0,230,0,5),(260,8,227,16,6),(268,0,243,0,7)]))) (.fork 6 (.fork 3 (.leaf [(24,256,135,96,6),(272,8,227,4,6),(280,0,231,0,8)]) (.leaf [(32,256,151,72,7),(256,32,94,129,7),(288,0,223,0,9)])) (.fork 3 (.leaf [(257,32,94,128,6),(289,0,222,0,7),(40,256,151,64,6)]) (.leaf [(296,0,215,0,7),(48,256,135,72,6),(272,32,78,129,6),(288,16,198,9,6)])))) (.fork 13 (.fork 6 (.fork 3 (.leaf [(256,64,189,2,9),(256,64,2237,2,8),(320,0,191,0,11)]) (.leaf [(320,0,2239,0,10),(321,0,190,0,7),(258,64,189,0,8)])) (.fork 3 (.leaf [(258,64,2237,0,7),(322,0,189,0,8),(322,0,2237,0,7)]) (.leaf [(324,0,187,0,7),(72,256,151,32,6),(320,8,163,20,6),(328,0,183,0,8)]))) (.fork 6 (.fork 3 (.leaf [(336,0,175,0,8),(320,32,30,129,6),(352,0,159,0,8)]) (.leaf [(352,0,2207,0,7),(384,0,127,0,9),(384,0,2175,0,9)])) (.fork 3 (.leaf [(136,256,23,96,6),(384,8,99,20,6),(160,256,23,72,6)]) (.leaf [(384,32,94,1,6),(416,0,95,0,8),(416,0,2143,0,7),(448,0,63,0,8)])))))))

def forest : Forest := ⟨2559,14,fun j => samples[j]?.getD (0,0),columns,symmetries,liveLevels,liveIndex⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem geom : graphValid forest (boundsBefore entries495) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel, by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b9at0 : block forest 9 0 14=true := quickBlock 9 0 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b9at14 : block forest 9 14 3=true := quickBlock 10 0 0

theorem all9 : block forest 9 0 17=true := (@block_merge forest 9 0 14 3 b9at0 b9at14)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b10at0 : block forest 10 0 16=true := quickBlock 9 0 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b10at16 : block forest 10 16 125=true := quickBlock 10 0 5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b10at141 : block forest 10 141 5=true := quickBlock 11 0 1

theorem all10 : block forest 10 0 146=true := (@block_merge forest 10 0 16 130 b10at0 (@block_merge forest 10 16 125 5 b10at16 b10at141))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b11at0 : block forest 11 0 7=true := quickBlock 9 0 1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b11at7 : block forest 11 7 168=true := quickBlock 10 0 6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b11at175 : block forest 11 175 64=true := quickBlock 10 0 4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b11at239 : block forest 11 239 168=true := quickBlock 11 0 6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b11at407 : block forest 11 407 118=true := quickBlock 11 0 5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b11at525 : block forest 11 525 3=true := quickBlock 12 0 0

theorem all11 : block forest 11 0 528=true := (@block_merge forest 11 0 239 289 (@block_merge forest 11 0 7 232 b11at0 (@block_merge forest 11 7 168 64 b11at7 b11at175)) (@block_merge forest 11 239 168 121 b11at239 (@block_merge forest 11 407 118 3 b11at407 b11at525)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b12at0 : block forest 12 0 1=true := quickBlock 9 0 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b12at1 : block forest 12 1 55=true := quickBlock 10 0 4

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b12at56 : block forest 12 56 145=true := quickBlock 11 0 6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b12at201 : block forest 12 201 73=true := quickBlock 12 0 5

theorem all12 : block forest 12 0 274=true := (@block_merge forest 12 0 56 218 (@block_merge forest 12 0 1 55 b12at0 b12at1) (@block_merge forest 12 56 145 73 b12at56 b12at201))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b13at0 : block forest 13 0 5=true := quickBlock 10 0 1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b13at5 : block forest 13 5 12=true := quickBlock 11 0 2

theorem all13 : block forest 13 0 17=true := (@block_merge forest 13 0 5 12 b13at0 b13at5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b14at0 : block forest 14 0 1=true := quickBlock 10 0 0

theorem all14 : block forest 14 0 1=true := b14at0

theorem tables : checkedTables forest 14 := by
  intro j hj
  interval_cases j
  · exact (rfl : block forest 0 0 0=true)
  · exact (rfl : block forest 1 0 0=true)
  · exact (rfl : block forest 2 0 0=true)
  · exact (rfl : block forest 3 0 0=true)
  · exact (rfl : block forest 4 0 0=true)
  · exact (rfl : block forest 5 0 0=true)
  · exact (rfl : block forest 6 0 0=true)
  · exact (rfl : block forest 7 0 0=true)
  · exact (rfl : block forest 8 0 0=true)
  · exact all9
  · exact all10
  · exact all11
  · exact all12
  · exact all13
  · exact all14

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem noRun : Impossible (graphGoal 2559) 14 (vars 2559).toFinset :=
  root_index (g:=forest) (before_sound _ sound495) geom tables (k:=14) (by decide) (i:=0) (by decide +kernel)

end Free511
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem liveSeedImpossible : Impossible graph 14 (inputs++[orSeed]).toFinset := by
  have target : graphGoal 2559 = graph := by decide +kernel
  have roots : vars 2559 = inputs++[orSeed] := by decide +kernel
  simpa only [target,roots] using Free511.noRun
theorem boundB (C : PEqualNP.CircuitLowerBounds.Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3))
    (h : PEqualNP.MetaComplexity.circuitFun 9 C = edge) : 16 ≤ C.size := by
  by_contra! small
  obtain ⟨k,t,hk,hdead | hlive⟩ := initial_live C legal first h (by omega)
  · exact dead_start (before_sound _ valid383) geomdead tablesdead k t hk hdead
  · exact liveSeedImpossible k t hk hlive
end PEqualNP.Outside.L_meta_3138
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_3138 :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             ∃ (x9 : Fin (9 : ℕ) → Bool),               have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ))]);               (x10.getD x2 Bool.false || x10.getD x3 Bool.false) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  let Gate := PEqualNP.CircuitLowerBounds.Gate
  let Circuit := PEqualNP.CircuitLowerBounds.Circuit
  let FanInTwo := PEqualNP.MetaComplexity.FanInTwo
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let prefixOr : Gate := ⟨.or, [0, 3]⟩
  let mergeOr (p q : ℕ) : Gate := ⟨.or, [p, q]⟩
  let withAux (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 3]
  let interim (gs : List Gate) (x : Fin 9 → Bool) : List Bool :=
    (⟨gs, 0⟩ : Circuit).wires (withAux x)
  let fanin (gs : List Gate) : Prop := FanInTwo ⟨gs, 0⟩
  have step_length (w : List Bool) (g : Gate) :
      (step w g).length = w.length + 1 := by simp [step]
  have fold_length (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons, ih, step_length, List.length_cons]; omega
  have prefix_length (gs : List Gate) (x : Fin 9 → Bool) :
      (interim gs x).length = 10 + gs.length := by
    change (gs.foldl step (withAux x)).length = _
    rw [fold_length]
    simp [withAux]
  have fold_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by rw [step_length]; omega)]
      exact List.getD_append _ _ _ _ hi
  have prefix_eval (gs : List Gate) (x : Fin 9 → Bool) :
      (⟨prefixOr :: gs, 0⟩ : Circuit).wires (List.ofFn x) = interim gs x := by
    change gs.foldl step (step (List.ofFn x) prefixOr) = gs.foldl step (withAux x)
    simp [step, prefixOr, withAux, PEqualNP.CircuitLowerBounds.GateOp.eval]
  have single_fanin (gs : List Gate) (h : fanin gs) (o : ℕ) :
      FanInTwo ⟨prefixOr :: gs, o⟩ := by
    intro g hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp [prefixOr]
    · exact h _ hm
  have merged_fanin (gs : List Gate) (h : fanin gs) (p q o : ℕ) :
      FanInTwo ⟨prefixOr :: (gs ++ [mergeOr p q]), o⟩ := by
    apply single_fanin
    intro g hm
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact h _ hm
    · simp [mergeOr]
  have append_eval (gs : List Gate) (g : Gate) (x : Fin 9 → Bool) :
      interim (gs ++ [g]) x = step (interim gs x) g := by
    simp [interim, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_append, step]
  have merged_eval (gs : List Gate) (p q : ℕ) (x : Fin 9 → Bool) :
      (⟨prefixOr :: (gs ++ [mergeOr p q]), 10 + gs.length⟩ : Circuit).eval (List.ofFn x) =
        ((interim gs x).getD p false || (interim gs x).getD q false) := by
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    change ((⟨prefixOr :: (gs ++ [mergeOr p q]), 0⟩ : Circuit).wires
      (List.ofFn x)).getD (10 + gs.length) false = _
    rw [prefix_eval, append_eval, ← prefix_length gs x]
    simp [step, mergeOr, PEqualNP.CircuitLowerBounds.GateOp.eval]
  intro gs p q hlen hfanin _ _ _
  let C : Circuit := ⟨prefixOr :: (gs ++ [mergeOr p q]), 10 + gs.length⟩
  let F := PEqualNP.Outside.L_meta_3138.edge
  change ∃ x : Fin 9 → Bool,
    ((interim gs x).getD p false || (interim gs x).getD q false) ≠ F x
  classical
  by_contra hbad
  have hsame (x : Fin 9 → Bool) :
      ((interim gs x).getD p false || (interim gs x).getD q false) = F x :=
    Classical.byContradiction (fun hn => hbad ⟨x, hn⟩)
  have first (y : Fin 9 → Bool) :
      (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3) := by
    change ((⟨prefixOr :: (gs ++ [mergeOr p q]), 0⟩ : Circuit).wires
      (List.ofFn y)).getD 9 false = _
    rw [prefix_eval]
    change ((gs ++ [mergeOr p q]).foldl step (withAux y)).getD 9 false = _
    rw [fold_getD _ _ _ (by simp [withAux])]
    have last (w : List Bool) (z : Bool) : (w ++ [z]).getD w.length false = z := by simp
    simpa only [withAux, List.length_ofFn] using last (List.ofFn y) (y 0 || y 3)
  have computes : PEqualNP.MetaComplexity.circuitFun 9 C = F := by
    funext x
    exact (merged_eval gs p q x).trans (hsame x)
  have lb := PEqualNP.Outside.L_meta_3138.boundB C (merged_fanin gs hfanin p q _)
    first computes
  have hs : C.size = 15 := by
    simp [C, PEqualNP.CircuitLowerBounds.Circuit.size, hlen]
  omega
