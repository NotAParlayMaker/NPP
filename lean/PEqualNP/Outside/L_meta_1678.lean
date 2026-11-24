import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1678
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
def seed : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 2) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
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

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
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
  by_cases hseed : seed ∈ S
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
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
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
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
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
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
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
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
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
-- The first gate x4 OR x6 as a signature, and rows witnessing that every input is needed
-- even when that signal is available.
def seedB : Sig := inputs.getD 4 zero ||| inputs.getD 6 zero
theorem seedB_table : ∀ r : Row, bit r seedB = (sample r 4 || sample r 6) := by decide +kernel
theorem seedB_nonzero : seedB ≠ zero := by decide +kernel
def extraB (i : Fin 9) : Nat := [0,0,0,0,64,0,16,0,0].getD i.val 0
def absentB (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< neighbor i) ||| extraB i)
def presentB (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i) ||| extraB i)
theorem seedB_witness : ∀ i : Fin 9,
    (bit (absentB i) graph != bit (presentB i) graph) &&
    ((inputs++[seedB]).all fun w => w == inputs.getD i.val zero ||
      bit (absentB i) w == bit (presentB i) w) = true := by decide +kernel
theorem all_rootsB {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seedB]) :
    S=inputs.toFinset ∨ S=(inputs++[seedB]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seedB_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentB i) (presentB i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seedB ∈ S
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

theorem initial_liveB (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seedB]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seedB := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seedB_table r).symm)
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
    exact False.elim (seedB_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seedB := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seedB at headEq
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
    rcases all_rootsB run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)
def orfd8 (i : Nat) : Nat := 0xde2ec802d90020e58140ae2e79ecc6115260160592f839e72d5845498058164be8c784b561152601605927cb1e7b75525056044164
def orfl8 : Packing := (4,7,7,1,4,6,0,orfd8)
def orfd9 (i : Nat) : Nat := (if i<1 then 0xa113d2704cc97129248448869081ec3c4760e71c42a4520780b20b41402303c0640a00f01401400437f36dc7aa9a05496486feee57653b40a92c945fdd7aeeaa549905922bfbae65cab11320b2517f75ebb6a55260164d2bed4b8e52aa4c02c9a775a9704a554980592dadbae52b44a9300b25bd9744a56895260164c6dee3a825d444c02c925fdd732a22645805920ff9b6e4554caae0b241ffb74cb6a1955c16483fe6db9155326b82c907fcdb722aa649705920ffdba65b50c92e0b249df756cc6a1915c164ae5eebd76c22a4b02c954fdd7aed93549605933cbaa665ae6a92c0b2473f75ccb95622581649a7eebd98a9322b02c93cbdd7b3152505605923ddba56636e98ac0b25eae748b56118058164be3c6ab6eb9b00b02c9bab9c5610b26016059279f3af662a4c02c0b25f1e75cb55498058164bf2ce996aa9300b02c97e71d12d55260160593757598c22a4c02c0b26eae71d845498058164fc5c63b08a9300b02c9fa38b56115260160593f472eac22a4c02c0b27eaa61172549805816483ff6e996cc34ea82c907fedd32da764d505920ffdba65b50c92a0b241ffb74cb69d9254164a2feebd76d4aa4982c94cfdd7aeda6549305920ff9b6e4554cba40b241ffb74cb6a1974816483ff6e996cc34a902c945fdd7aed98695205920ff9b6e4554caa40b241ffb74cb6a1954816483fe6e374cc2ea902c92dbdd7b31a5611205920ff9b6e4554c9a40b2497f75ecc695934816483ff6e996d2b26902c907fcdb7297564d2059259fbaf6634ab1a40b267d354ccb5cd524816492feebd98d2b22902c92dbdd7b31a550520593ead330baaa4b8240b27f4a5d5845497048164fab4bab26a92e0902c9fc697558d525c120593ead2eaa9322b8240b27f4a5d5525057048164faf0cc2e290ae0902c9fda1845c5215c120593ebc326b8a42b8240b27f3858d714857048164ff60b1a6290ae0902c9fd48c754d524c1205937e938aa926298240b27af46a1814c5304816483ff6e996d3b26882c907fedd32da7649105920ff9b8dd330b9220b241ff371ba64d7244164a2feebd76d4aa4882c907fcdc6e9935491059279f3af662a4b0220b25facb75525056044164bf58ebaa4a0ac0882c9fcb0d75494158110593fd42e4a9282b0220b27f5835d525452044164fbb0c9aa4a8a40882c9fe61635495148110593fb41aea928290220b27fc85d552505204416482fe6db8f55352a92c905fddbb31a929d52592f471aadbb08c02c0b2762eaee776118058164bc5ceb96ac2300b02c97aa9d22d58460160592f563a25ab08c02c0b2768eaee556118058164fc1d3bcaac2300b02c9daaabb6122260160593f154eec2444c02c0b27e8a955848898058164a9bc6db2ac2b00a82c97b31d12d58460150593f944ef11282b0220b27f88956225056044164 else 0x571420002e041000000001a36f000b4001f0007c001e00041e00083c818231000bc5f20081e4008000b206f144b860cea42000000d0c04010100000080801d360802020003a1c106c841d02082e6c105c3820d81040f36081e1c1000000000000000000f521001e1c100000d20608ef8a034203480033c118c06782316903801823180000000000228c4c88f10a1ec2b84d0860e40a80b001fdbf67e2fb1f3bc876ce91c93806f6da5b2345680ced8e31760ac017daf65aeb1559aae552a914fa9a5109d938a6c4ce9552824b47289d1121d430818fa1ef3ba760e31c135e6a8cc1933025f0b51652c056cab15129851c)
def orfl9 : Packing := (105,6,7,2,4,11,0,orfd9)
def hashorfl9 (i : Nat) : Nat := 0x103208005a400a05800000000
def orfd10 (i : Nat) : Nat := (if i<1 then 0x87fccbaa9934816487fccb6959348164c77cba9559348164a7ecca6555248164e76da995622481648dfdc72e93148164fec5634c52148164fd69755497048164fde1714857048164ff49535493048164ffc131485304816487fccb69d934416487fccb69d9244164e5eda99de2244164e76da99562244164fc7a779556044164bef1c11496044164fcea778896044164fe6a558896044164feb1725056044164feb1525056044164feb0525056044164feb2225056044164ff61525452044164dfb2bb5052044164fdb2775052044164ff32555052044164ffa1525052044164ffa222505204416497f8cb61d9580164f1fa889dd9580164b778cb6625580164f579989de5580164f97a889de558016497f8cb6625580164f37a886565580164fd3a77955848016497f8cb61d9380164d778cb9559380164f57a77955938016497f8cb9559380164dcfabb9dd6380164de7abb9556380164fc7a779556380164bedacc60d6380164fcda7760d6380164fe5a5560d638016497f8cb61d9280164f1fa889dd9280164d778cb9559280164f37a889559280164f57a77955928016497f8cb955928016497f8cb65d828016497f8cb655828016497f8cb64d8280164fad98358d82801649df9c7aed5280164d5f9b92dd52801649df8cb9dd5280164ded9b68cc5280164b7e8cb6622280164f3ea8865e2280164f5e9989de2280164f9ea889de2280164b7e8cb6562280164f3ea886562280164f5ea776562280164f769989562280164fb6a889562280164fd6a779562280164f769959562280164fdaa776122280164ff2a556122280164b7e8cb64e2280164f5ea7764e2280164f76a5564e2280164beeacc58e2280164fcea7758e2280164fe6a5558e2280164fec98358e2280164fdca778ce2280164ff4a558ce228016497f8cb662228016497f8cb656228016497f8cb64e2280164f3ea8864a2280164f76a5564a2280164f1fa889dd9180164f37a889559180164f57a779559180164f3ea888899180164f5ea778899180164f76a558899180164a7f8ca6e55180164f9ba889dd4180164fb3a889554180164fd3a779554180164fbaa888894180164fdaa778894180164ff2a558894180164dedabb58d3180164fcda7758d3180164fe5a5558d3180164fec9638893180164fed1634c52180164f5f27764e1180164fcf27758e1180164fbd2888ce1180164fdd2778ce1180164f5f27764a1180164f7e19888a1180164fbe28888a1180164f7e19788a1180164fde27788a1180164f7e19588a1180164ff625588a1180164ffa18488a1180164f7e19388a1180164fee16388a1180164ffc23388a1180164f7e19288a1180164dababb6118058164f8ba776118058164fa3a556118058164faa9848898058164fcb2775056044164fea2225056044164 else (if i<2 then 0x87fccbaa99260164c5fcba9dd9260164c77cba9559260164adedc72ea2260164a7eccb6a62260164e5eda99de2260164a7ecca6562260164e76da995622601648dfdc72ea226016487fccb6a62260164a7ecca64a22601648dfdc72e931601648f7dc5aeda85c16487fdc52e9985c16487fdc12e9985c164c7f6112e9985c16487fdc82e9955c16487fdc12e9955c164c5fd712e9955c164c7f6112e9955c16487fccb6a1955c1648f7ccb6a2555c164a77cca662555c16487fdc82e9935c164c3fe882e9935c16487fdc52e9935c16487fdc12e9935c164c7f6112e9935c164c77cba955935c16487fdc82e9925c16487fdc52e9925c16487fdc12e9925c164c7f6112e9925c16487fccb6a1925c164c77cba955925c164ec7eaa9de5558164fc3e779558458164d67ccb9559358164f47e77955935816496fccb95593581649cfdc7aed52581649cfccb9dd5258164eceeaa9de2258164f4ee776562258164ee6eaa9562258164fc6e779562258164f66d959562258164fcae776122258164fe2e556122258164f4ee7764e2258164f66e5564e2258164f47e779559158164f4ee778899158164f66e558899158164fcae778894158164fe2e558894158164be78c56dd8058164dcfabb9dd8058164bcf9c72d58058164bed9c32d58058164bee9c22d58058164bef1c12d58058164de7abb9558058164fc7a779558058164fababb6118058164fab9b76118058164fab9b56118058164fab8b56118058164fab9756118058164faba556118058164fab9846c98058164fab9842c98058164fab9845c98058164fab9845498058164baf9c81498058164fab9841498058164deeabb8898058164fcea778898058164fe6a558898058164fab984889805816487fccb65eaa5416487fccbaa9985416487fccb661a75416487fccbaa9935416487fccb69d935416487fccbaa9925416487fccb6a1925416487fccb69d9254164a7eccb6a62254164e5eda99de2254164e76da9956225416487fccb6a62254164bf71c12d5805416497f8cb6558054164f379956158054164dbbabb6118054164ebbaaa6118054164f9ba776118054164fb38b56118054164fb3a556118054164fba9848898054164a7eccb6a6224c164e5eda99de224c164ecee7769a224c164e76da9956224c164ee6da6956224c16487fccb6a6224c164fbd1814c5804c16487fdc52e9984816487fccbaa9984816487fdc82e9974816487fccbaa9974816487fccb6a197481648dfdc7aeda54816487fccb661a548164c5fdb92dda5481648dfccb9dda54816487fdc82e9954816487fccbaa9954816487fccb6a19548164a77ccb6a65548164a77cca6625548164e57da99de554816487fccb6a65548164a77cca656554816487fdc82e99348164c3fe882e9934816487fdc52e99348164 else (if i<3 then 0xcefebb58da244164a7fecc69592441648ffecc6e98244164c7fdba6617244164cfbdba6117244164c7fdba64d7244164cefdba58d72441649dfdc7aed52441648ffecc6e95244164cdfcc76e95244164c7febb6a55244164c7fda96dd5244164cdfdba2dd5244164d5fdb92dd5244164e5fda92dd5244164c7fdba64d5244164cefdba58d5244164e7eda95c952441648ffecc6e852441648ffdcb68c5244164cfddb368c5244164c7fdba64c5244164cefdba58c5244164cff9a86c05244164d7f9986c05244164dfb9846c05244164cff9a36c05244164d7f9936c05244164def9636c052441648ffecc6e932441648ffdcb6a132441648ffdcb69532441648ffccb6a2224416497fccb66222441648ffccb696224416497fccb656224416497fccb64e2244164befacc5cd6044164befacc54d6044164bef9c754d6044164fed97354d6044164fcf9735c96044164befacc5496044164bef9c75496044164fcf8c75496044164fe79755496044164fe79535496044164fee9725496044164bef9c31496044164befacc4c96044164bef9c74c96044164bef9c54c96044164fed9734c96044164e7f99869d2044164bff1c12d52044164efb9a76112044164e7f9a764d2044164eef9a758d2044164f7e9985492044164fde8c75492044164f7e9955492044164ff69755492044164ffa9845492044164efe9a35492044164f7e9935492044164fee9635492044164ff69535492044164f7f1935452044164fef1635452044164ffe1c25452044164f7f1925452044164ff71525452044164ffb1b85052044164ffb1b75052044164ffb1875052044164ffb1b55052044164ffb1855052044164ffb1755052044164ffb2555052044164ffb1825052044164ffb1525052044164a5fdc5aaa7764964a5fdc7aa9a954964a5fecc6a4a754964c5fdc92ea7754964c5fcba6a67754964977dc5aed9254964a5fdc7aa9925496497edc12e9958896497edc02e99588964d5eebb9dd9588964bd6dc72ea558896497edc2aed958896487fdc12e9958896487fdc02e995889648dfdc72ea5588964d76ccb955928896497eccb95592889649dedc7aed5288964a7ecca6555288964d76db99555288964a77dc82ea5564164a77dc32ea5564164a77dc22ea5564164e57eaa9de556416495fdc7aed5264164c5fdba2dd526416495fccb9dd5264164a7edc82ea2264164a7edc52ea2264164a7edc32ea2264164e5eeaa9de2264164e76cca9562264164e76cba9562264164e76eaa9562264164f56e779562264164c77da92d5a760164c5fda96dca560164c7eda96c8a560164c7f5a96c4a56016487fdc22e9956016487fccbaa99560164c5fcba9dd9560164a77ccb6a65560164e57da99de556016487fccb6a65560164a77cca656556016487fdc52e99260164 else (if i<4 then 0xa7fdca6159148164a7fdca5d59148164e7eda85499148164f5ecc75499148164e7eda75499148164f76d755499148164aff5c1aa98148164e5fd9869d7148164edbda76117148164e5fda764d7148164ecfda758d7148164c7fd952e951481648ffdc32e951481648ffccbaa951481648ffccb69d51481648ffccb68d5148164c7fcba64d5148164cefcba58d5148164fd6cc75495148164ef6da75495148164f76d935495148164fe6d635495148164afbecc6a14148164afbecc69d4148164afbdca61d4148164afbecc6954148164edbcc76954148164afbdca6154148164afbdca5d54148164efada85494148164fdacc75494148164efada75494148164ff2d7554941481648ffdc82e931481648ffdc52e93148164eedeaa58d3148164eedda758d3148164eedda558d3148164cfecba5493148164df6db55493148164fecd635493148164cff4ba6053148164efd5a36053148164efd5a34c52148164fed5634c52148164ffc5324c52148164d7ed986d52148164ddecc76d52148164dfadb56112148164d7edb564d2148164deedb558d2148164f7e5985c52148164fde5a75c52148164fde5875c52148164f7e5955c52148164ffa5845c52148164f7e5935c52148164fee5635c52148164bfe5c74c52148164ffc5a34c52148164ffe1c04c52148164e7f9986957048164f5f9985d57048164efb9a56117048164fdb9756117048164e7f9a564d7048164f5f97564d7048164eef9a558d7048164fcf97558d7048164f7e9985497048164ffa9845497048164f7e9935497048164fee9635497048164ff69535497048164e7f9a56457048164f5f9756457048164f7e9526457048164f5f9985c57048164fdb9845c57048164f5f9935c57048164fcf9635c57048164ef79a55457048164ff69525457048164efb9a55057048164fdb9755057048164ffa9525057048164fed9634c57048164f7e9984857048164bfe9c54857048164f7e9954857048164fde9754857048164ffa9844857048164f7e9934857048164fde9734857048164fee9634857048164ffe1314857048164bef9c62953048164bfd9c32953048164efe9a85493048164fde8c75493048164ff69755493048164ffc9535493048164ebf9a86053048164aff8ca5453048164ff69525453048164efd9a84c53048164bfd9c54c53048164ffc9524c53048164ffd1814c53048164ffd1314853048164dfe9b74853048164bfe9c54853048164ffc9534853048164ffe17148530481648ffdc3aeda744164afecc26dda344164a7fecc69d9344164c7fccb69d93441648ffecc6e98344164aefecc69d63441648ffdc8aeda2441648ffdc5aeda2441648ffdc3aeda244164c7febb661a244164c7febb65da2441648ffccb61da244164cfbebb611a244164c7febb64da244164 else (if i<5 then 0x8ffdcaaed87481648ffdc52e987481648ffdc32e987481648ffdc12e987481648ffccbaa9874816497fccb6a587481649dfdc7aeda54816497fccb661a548164c7fdc9aeda5481648ffdc8aeda548164cdfdc7aeda5481648ffdc3aeda5481648ffdc1aeda548164adfdc7aeda548164a7fccb661a548164c7febb661a548164cdfebb2dda548164cdfdb82dda548164e5fd982dda5481648ffccb61da548164cdfcb76cda548164cdfcb76c5a548164a7fdc8aa99548164a7fdc1aa9954816497fccb6a19548164a7fecc6a19548164c7fccb6a1954816497fccb61d9548164a7fcca61d95481648ffecc6e98548164cdfcc76e985481648ffdc32e985481648ffdc12e98548164a7fcca6e58548164a7fcca6558548164c7fdba66175481648ffdc82ea55481648ffdc32ea55481648ffdc12ea55481648ffccbaaa55481648ffccb6a2554816497fccb6625548164a7fcca6625548164c7fcba6625548164afbdc7aa98448164afbdc5aa98448164afbdc1aa98448164afbecc69d8448164afbecc6958448164edbcc76958448164afbdca5d58448164afbcca9558448164aefdc6295a3481648ffdc8aeda3481648ffdc5aeda3481648ffdc1aeda3481648ffccb61da348164aefdc62d5a3481648ffccb955a348164a7fdc8aa99348164a7fdc7aa99348164a7fdc5aa99348164a7fdc1aa9934816497fccb6a19348164a7fecc69d934816497fccb61d934816497fccb6959348164a7fecc6959348164c7fccb6959348164e5fcc76959348164c7fcba6159348164a7fdca5d5934816497fccb9559348164a7fcca9559348164c7fcba95593481649fedc2aed73481648ffdc82e973481648ffdc52e973481648ffdc12e97348164cdfcba61d7348164aefdc72e96348164aefdc52e96348164aefdc8aa96348164aefdc7aa96348164aefdc5aa96348164aefdc1aa96348164aefecc69d6348164aefcca61d6348164aefdca2d56348164beedc22d56348164aefecc6956348164ecfcc76956348164aefcca6156348164aefdca5d56348164aefcca95563481648ffecc6e95348164cdfcc76e953481648ffdc12e9534816497fccb95592481649dfdc7aed52481648ffdcb6a15248164bdedc7aed5248164cfeccb6a15248164ef6cc56a15248164ddedb82dd5248164ededa82dd5248164f5ed982dd5248164e7ed9869d5248164ef6da85d55248164f76d985d55248164fd6d875d55248164fdacb76115248164efada76115248164ff2d756115248164f5ecb764d5248164e7eda764d5248164f76d7564d52481649feccb5cd5248164fcecb758d5248164eeeda758d5248164fe6d7558d5248164fd6cb754d5248164ef6da754d5248164ddecb76c55248164a7fecc6a19148164a7fdca61d9148164a7fecc6959148164e5fcc76959148164 else (if i<6 then 0x9efecc6dd3158164deecc26dd3158164dcfdb75c931581649efdcb1493158164beddc31493158164bef5c11493158164bef9c32d58058164bef9c22d58058164befacc5cd8058164fcf9b75cd8058164bef9c52c98058164bef9c32c98058164fcf9735c98058164befacc5498058164bef9c75498058164fcf8c75498058164fe78b55498058164fe79755498058164fee9725498058164bef9c31498058164c7fdc9aeda8541648ffdc2aeda8541648ffdc1aeda854164c7fdb92c9a8541649f7dc5aeda75416497fccb661a7541648ffdc8aeda7541648ffdc3aeda7541648ffdc1aeda754164a7fccb661a754164c7febb661a7541648ffdcaaed87541648ffccbaa9875416497fccb6a58754164afbecc69d845416497fccb6a1935416497fccb69d9354164a7fecc69d9354164c7fccb69d935416497fccb61d9354164aefdc72e96354164aefdc22e96354164aefecc69d6354164aefdca2c963541649dfdc7aeda25416497fccb661a25416497fccb64da25416497fccb6a19254164a7fecc6a19254164c7fccb6a1925416497fccb69d925416497fccb61d92541649dfdc7aed525416497fccb6a622541648ffccb6a2225416497fccb662225416497fccb656225416497fccb64e22541649ff9c0aeda154164a7fecc6a19154164a7fecc69d9154164a7fdca61d9154164afbecc6a14154164afbecc69d4154164afbdca61d4154164eedeaa58d3154164eedda758d3154164fbb9a76118054164fbb9842c98054164fbb9846898054164f3f9856498054164fbb9845c98054164fbb9845498054164fbb9848898054164fbb9846858054164f3f9856458054164fbb9845c58054164fbb9855058054164fbb9844858054164d7f9b864d7054164def9b858d7054164d7f9b86457054164f5f9985c57054164fdb9845c57054164f5f9935c57054164fcf9635c57054164dfb9b85057054164fed9634c570541648ffdc1aeda74c1649dfdc7aed524c164c7febb6a5524c164c7fda96dd524c164cdfdba2dd524c164e5fda92dd524c164cefebb699524c164cefdb7699524c164ecfcb7699524c164e7eda95c9524c164eeeda65c9524c1648ffecc6e8524c164bf78c56dd804c164bdf9c72d5804c164bfd9c32d5804c164bfe9c22d5804c164bff1c12d5804c1649ff9cb149804c164aff9ca149804c164bbf9c8149804c164bfd9c3149804c1649ff8cb889804c164ffd131485804c164c7fdc9aeda8481648ffdc5aeda8481648ffdc1aeda848164af7cc56dda848164a7fdc7aa99848164a7fdc5aa99848164a7fdc1aa998481649fedc2aeda7481648ffdc8aeda7481648ffdc3aeda7481648ffdc1aeda748164c7febb661a748164a7fdc8aa99748164a7fdc1aa9974816497fccb6a19748164a7fecc6a19748164c7fccb6a19748164 else (if i<7 then 0xcdfdba2dd5260164e5fda92dd5260164e77da92955260164bd7dc72955260164bf75c12955260164e77da95d55260164ef6ca56895260164e7eda95c952601648ffecc6e852601648ffdc52ea22601648ffdc12ea2260164cfbd412ea22601648ffccbaaa226016497fccb6a6226016497fccb6562260164a7fcca6562260164af7cc569da160164adfdc7295a160164afddc3295a160164afedc2295a160164aff5c1295a160164a7fdc7aa99160164a7fdc5aa99160164a7fdc2aa99160164b77cc569d9160164b5fdc72959160164b7ddc32959160164b7edc22959160164b7f5c12959160164a7fcca9559160164a7fcca5499160164a7fdca1499160164b3fdc81499160164b7f9c01499160164a7fcca88991601648ffdc22e93160164cfbd416e2aa5c164cfbd416d6aa5c1648ffdc86ceaa5c1648ffdc56ceaa5c1648ffdc36caaa5c164cfbd416caaa5c1648ffdc86c6aa5c1648ffdc26c6aa5c1648ffdcb546aa5c1648ffdc1aeda85c164a7fdc5aa9985c164a7fdc2aa9985c164a7fdc1aa9985c16497fccb661a55c164a7fdc8aa9955c164a7fdc1aa9955c164c7fd852e9935c164a7fdc8aa9935c164a7fdc5aa9935c164a7fdc2aa9935c164a7fdc1aa9935c16497fccb6a1935c16497fccb695935c164a7fdc8aa9925c164a7fdc1aa9925c1648ffdc82e9525c1648ffdc32e9525c1648ffdc12e9525c164cfbd412e9525c164c7fcba661525c164f57d985d5525c164c7fcba64d525c164f57d7564d525c16497fccb661a15c16497fccb64da15c164a7fecc6a1915c164e77cc56a1915c164e5fda85d5915c164f57d75549915c1648ffccaaed315c1648ffdc82e9315c1648ffdc52e9315c1648ffdc22e9315c1648ffdcbaa9315c164bdecc26dd315c1649efdc5aed87581649efdc3aed87581649efdc2aed87581649efdc8aed73581649efdc5aed73581649efdc2aed73581649efdc1aed73581649efdc8aed5258164dcfdc7aed52581649efdc7aed52581649efdc3aed52581649efdc1aed5258164bcfdc7aed52581649efecc6dd5258164dcfebb2dd5258164dcfdb82dd52581649efccb61d5258164fc7d875d55258164debebb6115258164debdb76115258164fcbcb76115258164fe3d756115258164dcfcb76cd5258164d6febb64d5258164d6fdb764d5258164f4fcb764d5258164f67d7564d52581649efccb5cd5258164fead845c95258164f6ed935c95258164fced735c95258164dcfcb76c552581649efecc6e05258164debdc46e052581649efecc6cc52581649efccb9562258164b6fecc5499158164b6fdc75499158164f4fcc75499158164f67d755499158164f6ed725499158164fced725497158164bebecc5494158164bebdc75494158164fcbcc75494158164fead725494158164beecc26dd3158164 else (if i<8 then 0xadfc5bbeb7396deadb85b66b6b96d4ada45aaeb489676acac5846aec95caab8456feab4955aaa08535ea6794c6a97c52d6a5994a4a94451a6a1e9434a81c4f6e9c29346a67c4c2e96f92bea56c4a0e93d9272a45c48968ed91a2a33446468a390f0a17c42d6829904aa09040e68189028a02840167fe8ffa9fe43fbe7f38fde9fa03f067dc8fb09f503e7e7cb8f949f243dde7ba8f609e983cde78e8f1a9e303bf676e8eb69d20398e7188e0a9bc836f66cb8d769aac354e6a88d4e9a2c338e6588c5498382f465cc8b3695a82b2e5648ac6951c2a2e53b8a6294b429465248a40947028be5138a249438286650889de936425b649a88de914c20f6402879c8f041de639186ea8d281a2e341867a8c48186e2e285bc8afc151627784e689c8136e25a849488d010be20783fa87480dae1b4836686c80d261a3834486480c0e17182b085140a0613c827084d0097e12b825484a4093e1268244848408e6118822e8458088e110821e842c083610281fc83e807c60f781ec83d407860ec81d0839006fe0db81ae8358068e0d0819e833806660cb81948324063e0c6818a831005fe0bb817482e405be0b6816482b8054e0a8814e828c04f609a8132826004b60958128824c048e09081188220041e07f80f681dc039606e80d48198030e05d80b8816002b605580a8814c028e050809e81380266048808e810c020e040807280bc012601a801a8000adfdc7aa9a054964cdfebb29da054964c7fdc02e9958896497fdc8aed5264164d5fdc7aed526416497fdc7aed526416497fdc3aed526416497fdc1aed5264164b5fdc7aed5264164c7febbaa9526416497fecc6dd5264164c7feaa6dd5264164d5febb2dd5264164e5feaa2dd5264164d5fdb82dd5264164e77eaa5d55264164d5fcb76cd5264164e7eeaa5c95264164d5fcb76c5526416497fecc6cc5264164d6fdc66cc526416497fccb9562264164cfbd416deaa60164cfbd416d6aa60164cfbd416caaa60164af7dc52caaa601649f7dc5aeda7601649ff9c0aeda760164cf7eaa2d5a760164c7fda96c8a560164d7edc96c8a560164d7f5c96c4a560164dbf5c86c4a560164dfb5c46c4a560164ddbdb7504a560164df9db3504a560164dfadb2504a560164dfb5b1504a56016497fccb69d95601648ffdc22ea55601648ffdc12ea5560164cfbd412ea55601648ffccbaaa5560164af7cc569da260164adfdc7295a260164aff5c1295a26016497fccb655a260164c7fda96d4a260164a7fdc5aa9926016497fccb69d9260164b77cc569d926016497fccb6959260164b5fdc72959260164b7edc22959260164b7f5c12959260164a7fcca9559260164a7fcca65572601649dfdc7aed52601648ffdc12e95260164cfbd412e95260164af7dc5aa95260164c7febb6a55260164c7fda96dd5260164 else (if i<9 then 0x978ebb1c8e374c6af8ceb18ee300c5c78b1b154e298c4f789ab12ce248c457886b104e1f8c3cf872b0dce1a8c317852b096e110c1e7835b056e09cc11781eb034e04cc0177f8afe2dfa8bf2f7dbafa2df1cbe177beaf74ded8bd777a7af40de7cbcef79caf30de38bc4f785aefcdddcbb67762aeb6dd5cba9774bae94dd18ba0f740ae7edcf8b9b7732ae5cdc9cb92f71eae2edc58b88f70aae06dbf0b7a76f3add8db94b6ef6d6ad9edb20b6076b9ad70dac4b5676a8ad48da80b4c7691ad14da0cb3df67aace6d9b0b32765dacacd93cb23f640ac72d8c8b157623ac3ed86cb0b7612ac1cd828b0475feabfad7f0afbf5f6abe4d7acaf4f5e5abc8d774aeaf5ceab94d70cadf75b7ab60d6a4ad0f59aab26d630ac0f57aaaecd5c8ab6f569aac4d56caa87546aa7ed4d4a96f529aa3ed460a89f512aa16d428a8174f8a9e2d3a8a7174d8a9a8d334a62f4bba968d2b4a51749ba928d24ca45f481a8f4d1cca347461a8b4d14ca277447a880d0e4a177424a840d064a077407a800cfd89f5f3e4a7bacf4c9e473c1a780ced89d773a4a73ace589c77387a700cdf09ba736aa6c6cd649a8f34aa686ccf099bf330a652cc8898d7313a618cc1497d72f0a5d2cb7c96bf2d0a592cb0895d72b3a552ca8894d7293a518ca149407279a4e4c9b8933725fa4b0c9509267242a470c8d0917f22ba442c8689097208a408c7e88faf1eea3d4c7988ef71daa3a6c7248df71b7a35ac6988cdf197a320c63c8c57186a304c5f88be717ba2f4c5cc8b5f167a2c0c5708ad7153a298c5148a07139a264c4b8893711ca22ac438881f0fca1f0c3d0877f0eea1c8c38086c70d4a19ac2e885970aba148c274846707ca0f6c1dc83af071a0d4c19882f705aa0acc13c8257043a078c0d48187029a044c06c80b700fa010c01c8016ffb9fe8bfb47f46fe49fc0bf707ea6fd09f92bf147e06fbc9f5ebea07d1ef9c9f2abe387c4ef859f08bdf47bc6f749ee6bdb07b3ef669ec4bd847ae6f589ea2bd347a5ef4a9e8cbd147a06f3c9e70bcc47966f289e42bc8078def149e26bc3c786ef069e04bbf877b6ef59de8bbcc778eeea9dd2bb887706edc9db6bb5c7696ecb9d94bb187626ec39d78bac87556ea99d3eba607486e899d04b9ec739ee6c9ccab97872b6e4f9c90b91071e6e389c62b8b47116e1b9c28b834702edfe9beeb7c06f2ede19bb4b7406e46dc19b74b6cc6d5eda19b34b64c6c46d819ae8b59c6afed559a9cb51c69fed3b9a68b4c06946d249a46b4886906d1c9a30b450687ed0b9a0eb40067c6cf499dab398670ecda99acb354666eccc9990b30465fecb89968b2cc6576cad994cb27c64d6c999930b2506496c91991ab224640ec7d98d4b150627ec4b9876b0946106c199830b05c6096c0297d8af405e76bca978caf085deebb99764aeb85d66b90970 else (if i<10 then 0x4601e01c00e00c006004002000c06404601e023f1800f007003001482382280f01b21180cf8c00c0078070038030018010008004019017c0780d908c067c6006003c03801c01800c0080040020b0c100019011d61803c01c00c0080040012014902306b183396a9150d200290014800da0052003100158608286020618080a003ac30030018010008002019fd03cd88e7ca608fc18e0be08a05406de3003001e01c018002000b040046f3602af1801300700500148326e2822f9b01b015014f8c00c00780700600080038190103cd80abc6003c01c00c0052010033a81e6c06c054053e3003001e01c00e00c0060040020011030f4002ad29f0e007e06f02e1a4da0023822f9b01b00400cf8c00c00780700380300180100080045d7dc39c0800481921064047045f3603602a029f1801800f00e00c001000703202301901578c007803801800a411c1140c80d80a80a508c03c03801c01800c00b869de301c800b01040ac0a80780a7c6006003c03801c01800c008004001d9001064047045f3603602a029f1801800f00e00c00100073400417c1140a80da08c03c03803000400140c808c040055e3001e00e006002906405f047045d2042300f00e0070060030020010007540040c041f400d9d02c2301ee1a300ac04911834f0d14a180b00afd03c38327c08e50c03c01a00be801b3e52193e1c90350d9f40f024232fa0794a118c19017f4800a80a508c03c03801c01800c008004001c0c80be8460060041b2002001390900000686328ee872400006e1ddf21ea608ca036108f8b0470ee501b8777c88237862c1c842411befbe2bd4bc33c72002c028364567d03c38c90014800a400608c29001e1808000070c041a6c1c8e080191c1003438304618230c118721820000190c1c860e4307218390c1c860e43040a0c10000000000000166c1b3608000058706c3824461001218290c148608000000000001874083a041d020e81074083a0418230c118608c28461882082c38200000000000736081c38200411c3b8a90208e1dc74810470ee36404234771c20c0243bc11921060121de08c9d43ba78f4e0e987d29ba3ef460e86fd03b9f8f3d4e76fce6b9bef360e69fcccb990f304e5b7cb2b956f290e4ffc92b916f204e3cfc72b8d6f190e2b7c4cb88af0f8e1b7c2fb850f084e0cfc0fb810f004dfb7befb7d0ef84decfbd2b796ef04ddcfbb2b756ee90dce7b8fb716ee10dbcfb72b6d6ed90dae7b52b69ced1cda17b3bb674ecccd95fb24b63aec4cd85fb04b5faebc0d717ad5b590eaecd587aa9b544ea60d457a7db4e0e98cd2afa4eb482e8e8d167a1fb430e844d067a08b402e7e8cf979eeb3c8e774ceaf9ceb388e6f4cdaf9aeb354e68cccdf997b320e624cc0f97ab2e6e5bccb27957b29ae518c9af928b248e45cc89790bb208e3f4c7 else (if i<11 then 0x7604100381788005314408161c98a39a90806000880041000606108446200100c12065870821806c5104446288273693718431118a2084dc5104e1c4463001019100082001b00c10004100314060801400e20010042231805003880040104002008282308a04118a08c27520462423080003860a1184ea4284618230c1184f1608c470c04628860e4318c8921acd8490c1486b0e12118408080582039b0421908c4070e4231211840e1c100020058802d41848021001f142002c30402c2f8a0162c860857eafe87681003e80181afcd80a802cc8cc03714e15e10070800015009805003942bf57f0a404c02c01f400e00610010061000d0c100b002003001000282f8228030070000010009c0bfd026a64a7c3aa1a81bc0bc0120c860e430401c2a8a1f18080790c0801c2002f052e5f02ac29e0e007c06e024b2fb07003b015e294130c00c29860cc304000000c46e0db8b35200a002634570602e62321833a281731190c09d140a5c1988ca03208a06c05203001c00e006004002000b02304603202af1800f0070030014a11a3a8bc602002b02a5a9029f1801800f00e007006003002001000711193a880641140a80dbc6006003c03801c01800c008004001c08c03c05484600e00a0027a800d40066182b0c1011193a881e801b3e520cfe1d30d20de05c34904702a58601300b0010003e4007d03ca7c1b40b08f868c055e81ae9e1c193e0de05c34804901902a036f1801800f00e007006003002001000722080c81b01480c00700300180080029a0020c904600e00c2ee0020019aa805f03602982300e00000a38bbc19411a6a82515a00284601e01c0060041b3c359aa80c90e40040640d80a419348001c01800c0080040016d00105f02a03682300f00e007006003002001000602f81b014c1180700300180080025a0035001036029064f1801800f00e00700204d001000602f80c81501b78c00c0078070038030018010008003817c0640d80a40600380000290d00142301901e03602a029f1801800f00e007006003002001000854004186dc002f180e00074801b50e47c800582e0008280020e000b00068db800546dc002a000d000700038001c000801c818eb78a0684072063a81a0f1d419c0d07c818ea0683e40034033c7520000ce068f050464a408237867c503429203e2bc300dbc1411998de901f540d00ce08ccfab480066f0d0eef050467240033c007c57867a978282341205e2819dc100da1199902f22e191dee0908cc037790c817528468ee6067640bc5423033477372003e98ca3a81a168def200d2e0908ca000019e0e9903002f16ea6e1ae0908d20c8864047e3001e00e0060028046232023f1800f00700300145a079b01b11180cf8c00c0078070038030018010008003c19011808008fc6003c01c00c00520c80bfa408 else (if i<12 then 0x2bc5180178a10416840b608c40b020812a4d7c495361c24a98321654872a5cd859521ca970e1254d810b2a408c400a0322e40e18100080388004160400ec80c30300702f150c06860343019a90cd4b0c0806c0644037847c403033c23e201819a11880cf08f8806067846208e084900da118c0ccc6448461011ca1188003205620030057021800fa00802011840100562003005502184004064100401e0262003005702180c800880208d8400600aa043001008100c80088000208020190400c518138348800c030403200219230010081000818080040204060101904010180008803c04c400600ae0430c50010301818040640044192c46002300174010008180806410031460036816303001030100411b0800c01540860020100003019001100004022b14603201020190010c91800fa00803c09c4018032202a0081015004080042032080200f027018180180608064004324603205420010081014804080640205a6c1208d36110469b080674d84033a6c2d40d36102069b088234d8584604fa303040036019180c81588014065c08603204e2027f18100c813880208d8401008c200802b1001802a810c004020401e002200100810008040803c004406010010301015004080042002010200f008101480408200208184620190400c518060436118d0dc3a1c1d0e081f0206870c1034384081a1c2016d0e7021e87048674381a47a1c1280d0e1687074383a1c4322d0e090ce87080043240646003e81e30300300c10008040030c01c0c0400208018a3e1a0803fa0080d0014a90f0d062a42000286acd8495366c2b360817f0d092a4200860d9170d587092a6c38561c1e1ab20105486c8aa00200600220010412a91801800880040c0400208258a300104111548786825521006fea069b0e208290566c24820a41587094080de208066201800c04e06e200d001101680c8809c0dc401006e9040329005037b0e4824194802803642070e0802e810b4083a045522d020e8107408b145a0412a9d02160d68108aa74085a041040c23100c8200805a08c504616c5823106c843080846143708210410908820901c402614070c4007868290166c24800a405870a1782304105e0c2f1a2b0006c92179cd850bc105e70e100f0648860801440d218c5081316cd8566c14c5081316c38561c1039b040e1c10d90820a628a10420039b040e1c10d9086c85316c0856041b020e430118801b2104a0d9101cd82023c0c9138704324390c0102000004233291008642004082308208c22421013a061002002000078200bd03c6308c601e0022000081b80c8c8674384018080200c02b1006009880300044018002201900c120659b08030004481961c2007001100081b88004208166c20010820587080c020320021923001030100080388004104400e060200 else 0x7030128c80388a182002082202f0071020823b228c00404c4002016c0431c500702f18178008800401c400e00226190071003b0c8801d904530c1007a4114d48401c0c0400201e26c3012080080389c08100405c17020408c508224338008bd001f406c61000fa262300110039830801c19c40cec46c0006842416230341b1181a0a88c0d044460682a23034151181a0908c0cc400e08020030400361b8100c880640044003a8138a3c23d401611ea00888c0cc4002652200702b100088c8800619e51460022322c2306710038338b08c19c400e054200704822327527200400c1004e040331523086dc5100080388004160400ec80200702f4291ee285717d005e8010559861026a50a440320022019040100581e89c080640f46032002200110610008038801801c88c9d49a81a6c0fa0364d40d3607d03326a069b03e819935034d81f40cc9a81a6c066300304110018158800c104b1478838478000684c41c23c000342620a11e0001a1310708f0000d08883847800068400302a1001817954e00100041044500233800068400828603442320018038801c0544e04170208078200803c100400e0802702080182001b0c00c100400605c2003005100c815a948c01c124400600a2001119100c8400c01440940c8200f08078158801c124400600a2001119100088c8801c200600aa043f400c50a907d202031181b8d9040f44e0506f15207b18a501902f4a94c524c3040bc0dd2a53148b0c1001119100088c8800c004400388380032a9c0011c36000806400c40818462019040100380a8800c100422b8462119e00108cf000b8002081c002e000f00078002081c002e000f00078003c0011c5e001700078002c81c002e001c51191a901b2cc37000a8db800546dc002a36e0012c351b7000f80034001a000d000561a8004036233c0030c38a59a9636e001cd4b000a6a78005c001119e001181b1b70003e8c0e81038007c001c000e0007000270d80023a9c0011d4f00080001d4878030e708c7c001e0008c3700080378004069c008463e003190341a11e3a8b90030461e4082310108c284610001c8178a238609d48406d08c4000704010018028801001001119100c8200803c100400600a2000c800880041004032002202d001100ce9b080044644002232200f0011000b40045a1c1d0e0e870743820020602001119100088c88004464400e0022000088c880b400440540602001106100c8038800401c400200e200100710400168800c004400600220010411681074083a0418230c1184d002034003))))))))))))
def orfl10 : Packing := (959,5,7,7,4,15,0,orfd10)
def hashorfl10 (i : Nat) : Nat := 0x819c0005856000000038306ba110b21424826000000000000000102c0001c11888cd02d801c20680000000e05600022a6800000000000000383c0000e495825e02a00000003c920000e09e0001420d80200000003830a8510001649c00049260000000000000000000000000000000001a54fa813868701f4448c0e383d50c80000889b8542ac000018098000b05e00000000000000180cc42f583b5a966031803201252a9c4044000000302f806e424684e10b0801dc025bd60000000000039209aa8000000000001aca0001c0180000001e0355f2a05300004058000000020cc00000002d4c808e6f500000000000041880001baad03c000242ea83f279ee04700e8000705200dc0000000007c000182d3043d0a021540000000609a000000000000000605643280000000e10000000000001211080510630000000188ab030000000000000000000060b8000485f2043811400000000001a02640ca02300020001c88d8100000e0d8000356292a3e0e80003835600a0000c1a28390001407c00068389abd805240c08312064a09bc24e0523094408902e3d5fd016a4a342171239ab1c5954046827b040016e0880057ea5820940003bd10001c09381400000200020303010001040201000001030000020a0402030b030203080a0001030200010000010008010103010003000600
def orfd11 (i : Nat) : Nat := (if i<1 then 0x4c600592ffd5da43002c9dfe6e52180164bff37090c00b277f99848600593dfd44243002c97fe6dd2180164eff32e90c00b27dfa7748600592ffcdaa43002c9dfe6552180164fef4aa90c00b27fb98448600592ffcd9a43002c9dfe64d2180164fdf2c690c00b27fda3348600593bfcc9243002c9ffa8892180164ffe2e290c00b27ff13148600593ff8c1c23002c9ffc5ce1180164ffe30508c00b27ff17284600593ff8a9423002c9ffc14a1180164ffe26508c00b27ff222846005923fedad54c92c997faaa77649649bfb6f552a4b265fda929d525926fe5d4eea92c997f6a67754964afdb7252c44b257eebb65622592bf65d32b112c9d7b9dd9588964fadcef2ac44b247fcba65622593bb72ab25112c95fb6e55288964cbfd553bb20b2677cba955905933bf554aac82c9d5f9de5564164cfd97511320b267eeaa88990593af73bc44c82c9ddb9562264164cbfb533bb00b247fcba655805933bed4caac02c91ff2e99260164cfdb5311300b247fcba661705923fe5d32ab82c91ff2e9935c1648ff974c92e0b26cfeaa9dd60593a7f3bb2ab02c9b9faaa5558164f8fcef2aac0b2767d9595560593e5f3bb08b02c9f8f9558458164e9fceec9ac0b2767e5564d6059377755444b02c9f3b9de2258164eddb2b112c0b27e6e5588960593f56c2444b02c9dbb64e2258164e9fceec8ac0b2767e5564560593b7711322b02c9f2f9dd4158164fd5c44a0ac0b25efabb60160593e7d3bb00b02c9f9e9558058164fdd444c02c0b265fda99dd505933bed4caaa82c99fb6a62254164f77308c02a0b265fda99dd3059367f3bb4c982c99fb6a6224c164dddb4d11260b247fcba661205923fe5d32e902c997f6a677481648ff974caa40b2677da9955205923fe5d326902c99fb6a62248164cbfb533ba20b267eda988910593e7d3bac0882c9f9e9556044164fdd444b0220b27fb14148110593afccc4ef002c9e7ea227780164e7f510cac00b275fa7765600593bbccc4ab002c9edea225580164faf4ef2ac00b277799595600593edd3bb09002c9fce9558480164ebf4eec9c00b2777a5564e00592f7d5dac7002c9f3e9dd6380164fcf4aab1c00b27ed98358e00593eed3bc67002c9cfea219280164ebf4eec9400b2777a5564a00592f7cdb0a5002c9dfa6622280164f7d51111400b277e99788a00593ef53bc45002c9dfa6562280164fed4ab11400b27fa98488a00593bf4c9c45002c9fba58e2280164ff946711400b277e99288a005939fd44323002c9d7e9dd9180164eef4aac8c00b277ea2264600593ddd44283002c9f6e9dd4180164fe74aaa0c00b27faa2250600593f6cb1a63002c9dfc65e1180164fbe4ef08c00b277f19384600593f78b1c23002c9ff48ce1180164efe32508c00b27fe22284600593d5cc2300b02c9fac5056044164 else (if i<2 then 0xc9fbe2c96380164bff576a9c00b25ff9b854e00592ffcdbaa7002c9f7e9dd5380164fef30aa9c00b27f7a5554e00593fecc1aa7002c9ff65cd5380164eff30ec9400b277f98564a00593bfcbab25002c9dfe9559280164bff576c1400b277f9b960a00593bfccbb05002c9efe61d8280164fbf4eec1400b277f99560a00593fbd2ab05002c9dfe64d8280164f7f306c1400b27ef96360a00593bfcc9305002c97fe6e17280164eff330b9400b27bfa885ca00593bfccaae5002c9fde9557280164ff7308b9400b277f9935ca00593efcb9ae5002c9fbe58d7280164ffb466b9400b25ffabb54a00593bfcdcaa5002c97fe6e15280164eff330a9400b27bfa8854a00592ffcdbaa5002c9f7e2dd5280164fbf4eea9400b277f99554a00593fbcbaaa5002c9fde9555280164ff7308a9400b277f99354a00593f7cb1aa5002c9fde54d5280164ffb466a9400b277f99254a00593ff4c12a5002c9ffa5c95280164bff37029400b277f99814a00593dfd440a5002c9fee6105280164bff36629400b277f99314a00593f7cb18a5002c9ff68cc5280164bff36229400b25ffabb4ca00592ffcdc265002c97fe6dd3280164fbf4ee99400b25ff9b54ca00593fbd2aa65002c9ff65cd3280164ffd30499400b27fe98788a00593ff45ac45002c9ffa6162280164ffd2eb11400b27fea5588a00593ff4c1c45002c9ffa5ce2280164ffd2a711400b277f99888a00593dfd44445002c9dfe6562280164fef4ab11400b27fb98488a00593bfcc9c45002c9fbe58e2280164ffb46711400b27fe98288a00593ff4a9445002c9ffa4ca2280164eff30ec8c00b277f98564600593bfcbab23002c9dfe9559180164eff304c8c00b277f97264600593bfca9323002c9dfe1499180164eff444c8c00b27dfa7760600593fbd2ab03002c9ff68cd8180164f7f304c0c00b27fea2260600592ffd5dae3002c97fe6e17180164eff330b8c00b27bfa885c600593efcc3ae3002c9dfe6557180164fef4aab8c00b27fb9845c600593bfcc9ae3002c9fbe58d7180164ffb466b8c00b277f9925c600593efcb92e3002c9ffa8897180164bff576a8c00b277f9b954600592ffcdc2a3002c9dfe6615180164f7f510a8c00b25ff9b754600593bfccbaa3002c9f7e9dd5180164eff32aa8c00b27f7a5554600593fdcc22a3002c9dfe64d5180164fdf2c6a8c00b27fda3354600593bfcc92a3002c9fde5495180164ffd444a8c00b27ff18154600593ff8b8aa3002c9fee61d4180164ff730aa0c00b27fb97550600593fdd2aa83002c9fee6094180164ff72e4a0c00b27fb95250600593fdc29283002c9fee8894180164bff57698c00b25ff9b84c600593dfd44263002c97fe6dd3180164fbf4ee98c00b25ff9b54c600593fbd2aa63002c9ff64c93180164ffd44498c00b27ff181 else (if i<3 then 0x50a0a40b26fbda750520593edf3ba82902c9bef6954148164fe7caaa0a40b27fad5250520593fd711282902c93ff2e93148164dfbb4698a40b27edd634c520593bf6c9242902c97fbaed2148164dfdd5490a40b277edb948520593bf6d4a42902c9dfb6612148164fbdcee90a40b25fedb548520593bf6caa42902c9fdb9552148164ff5b0890a40b277ed9348520593f76b1a42902c9ff95c52148164ffca6290a40b25ffabb5c1205937fd552e0902c9dfe6a57048164eff330b8240b26ff9a55c120593bfccaae0902c9f7e5d57048164fef4aab8240b27fb9845c120593bfcc9ae0902c9f7e5cd7048164fdf2c6b8240b27fe9525c120593bfcc8ae0902c9f7e5c57048164ff7282b8240b27fe9215c1205937fd55260902c9bfe6a13048164bff36e98240b27dfa774c120593fbd2aa60902c9ff654d3048164ffd2a498240b27fea224c120593fec98a60902c9ffa48530481649ffd76d3a20b24ffebb68d105936ff3bb46882c99ff69d9344164ebfceec9a20b24ffdba60d105927fedd2e6882c9bbf69d6344164f9fceeb1a20b24ffebb689105933fedcb44882c99ff661a244164cffb2ed1220b26dfe77689105937dec2344882c99ff64da244164ddfac6d1220b267fda764910593aff3bb24882c99ff6959244164cffb44c9220b24ffdba609105927fedd2e4882c99ff6a572441649ffb74a9220b267fda9549105927fedd0a4882c99ff6a45244164bff36029220b24ffdba4c9105937f6d4444882c9dfb6622244164dfdb4f11220b27dee77889105937f6d2c44882c9dfb6562244164fedcab11220b27fad84889105937f6d1c44882c9dfb64e2244164fddac711220b267fda9889105937f6d1444882c9dfb64a2244164fdf2eab0220b27efa5558110593f7cb9ac0882c9fbe54d6044164fdf2e4b0220b27ef95258110593f7c292c0882c9fbe4c96044164fdf444b0220b25ffabb48110593bfcdca40882c9dfe6612044164dff34e90220b277f99748110593efd3ba40882c9dfe6552044164fef4aa90220b27fb984481105937fcd1a40882c9dfe64d2044164fdf2c690220b277f99248110593ff4a9240882c9ffa8892044164ffe2a290220b25ffabb61e00593bfcc3b2b002c97feaed8580164eff372c2c00b27bf98761600593efd3bb0b002c9dfe6558580164bff370bac00b277f9985d600593dfd442eb002c9f7e61d7580164fef30f2ac00b27f78b295600593bfccc4ab002c9efea225580164fef30b2ac00b27fb97561200593fdd2ab09002c9dfe61d9380164eff30ac9c00b277f97564e00593bfd2ab27002c97feaed8380164fbf4eec1c00b27f7a5560e00592ffd5dae7002c97fe6e17380164fbf30eb9c00b27f7a555ce00593f7cc3ac7002c9fbe2d56380164fdf30ab1c00b27ef97558e00593f7d2aac7002 else (if i<4 then 0x593fdcc22e0a82c9dfe64d7054164fbf2e6b82a0b27ef9635c150593bfcc92e0a82c9ffa8897054164eff322b82a0b27df9715c150593fdca0ae0a82c93ffaeda74c164cffb52b9260b26efda65c9305933fed4aa4982c9bbf699524c1649ffb7429260b267fda914930592f7edb0a4982c9bbf698524c164bff36029260b26feda788930593ef73bc44982c9fdb956224c164cffb5311260b26efda688930592ffd5db00982c9f7e9dd804c164f7f30ac0260b27f7a5560130593ff511300982c9efe605804c164ffb262c0260b24ffdb8aa9205927fedbd54902c93ff6d6aa481649ffb6755240b24ffdb1aa9205933ff55352902c99ff6a5a8481649ffd76d4240b267fdb96a1205933ff55330902c99ff6a5a7481649ffd76d3a40b267fd9869d205933ff5532e902c99ff6a197481649ffb74c3a40b24ffcba61d205936ff554ee902c9d7f6a67748164dbfb513ba40b275fd989dd205933fed4b4a902c93ffaeda548164cffb72d2a40b267fd98695205936fe5bb4a902c9b7f9dda548164cffb5252a40b25efdb6295205937bed294a902c99ffaa99548164cffb50caa40b267fda765520593aff3bb2a902c99ff69595481649ffb74c2a40b24ffcba615205927fedd2ea902c99ff6a57548164def9752aa40b26f7eaa95520593bbed4caa902c9bdf6a25548164eefb312aa40b26f7da795520593ebf3bcaa902c9fdb2ca55481649ff9752aa40b267fda9955205937bed2caa902c9ddf6565548164df7d54c2240b26fbda761120593edf3bb08902c9bef6958448164fe7caac2240b24ffebb68d205936ff3bb46902c9bdf955a348164cffd54c9a40b267fda764d20593aff3bb26902c99ff6959348164eefcaac9a40b24ffdba5cd205927fe5d2e6902c9b7f69d7348164bdfd76b1a40b26efcba58d2059377f552c6902c9bbf69d6348164f9fceeb1a40b26efda558d20593f3f2aac6902c93ff6e953481649ff974a9a40b267feaa649205933fed4324902c99ff6959248164eefcaac9240b277ed92609205933fed4aa4902c9dfb6495248164bfdd76a9240b26feeaa54920593bf6dcaa4902c9dfb6a55248164dfdb50a9240b277ed9854920593ef65baa4902c9bfb69d5248164fbdceea9240b27f6ca554920593bf6caaa4902c9fdb5d55248164fedcaaa9240b27fad8454920593bf6c9aa4902c9fbb58d5248164fedaa6a9240b277eda9889205937f6d4444902c9dfb6622248164dfdb4b11240b277ed9588920593fb72ac44902c9feb6122248164dfdb4711240b277ed9388920593f76b1c44902c99ff6a5a148164cffd54c8a40b267fda8645205933fed3b22902c9d7f9dd9148164cffb4ac8a40b2777e5564520593bf6a9322902c9dfb8899148164dbfb4eb8a40b24ffcba54520593fb6a92a2902c9befaa94148164df7b else (if i<5 then 0xf9557358164ddfd54b92c0b276fd955c960593f3f2aae4b02c9faf6117258164edfb26b92c0b27cfd735c960592f7f5daa4b02c9bbfaa95258164bdfb6ea92c0b27cfcb754960593e7f3baa4b02c9dbf6555258164fcfaeaa92c0b27e7e5554960593f5ec22a4b02c9dbf64d5258164fddae4a92c0b26efeaa14960592f7edc0a4b02c9faf6105258164bdfb66292c0b276fd9314960592f7ed88a4b02c9fbb61e2258164fdd96b112c0b27eed7588960593f772ac44b02c9fbb5ce2258164ddfd55112c0b276fd9588960593f3f2ac44b02c9faf6122258164edfb27112c0b27eed5288960593b7ebab22b02c9dbf9559158164edfae4c8ac0b276fd5264560593b7e29322b02c9dbf8899158164bdfd76b8ac0b27e7e555c560593e7eb92e2b02c9fbb8897158164fd7ae4a0ac0b27ebd5250560593f5e29282b02c9faf8894158164bdfd7698ac0b25efdb74c560593e7f3ba62b02c9f9f9553158164fddc4498ac0b27efabb60160593f7cdbb00b02c9fbe6d58058164fdf16ac02c0b27ef97560160593f7d2ab00b02c9fbe6cd8058164fdf2e6c02c0b27ef9b260160593f7c59300b02c9fbe5c98058164fdf2a4c02c0b27ef85260160593f7d11300b02c99ff65eaa54164cffb52d42a0b24ffebb6a1505933fedcb50a82c99ffaa99854164cffb52d3aa0b24ffebb69d505933fecc34ea82c93ff6e98754164dbfd553baa0b275fda99dd505936fed44eea82c9d7f6627754164cffb50caaa0b2777d95615505937bed44aaa82c9ddf6625554164df7d54c22a0b26fbda761150593edf3bb08a82c9fcf9558454164cffd54c9aa0b267fda764d50593aff3bb26a82c9ddf9559354164bdfd76b1aa0b26efcba58d5059377f552c6a82c9bbf69d6354164f9fceeb1aa0b27e7e5558d505933fed4b44a82c99ffaa99254164cffb50c92a0b267fda764950593aff3bb24a82c9ddf9559254164cffb52b92a0b267fda9549505937f65d444a82c9bfbaaa2254164efdb53112a0b26feda888950593bf6cc444a82c9bfb69e2254164fbdcef112a0b277ed9588950593fb72ac44a82c9feb6122254164efdb27112a0b27eed63889505933fed4c44a82c9dfb64a2254164cffb52d0aa0b267feaa645505933fed4322a82c99ff69d9154164ebfceec8aa0b2777e5564550593bf711322a82c9befaa94154164df7b50a0aa0b26fbda750550593edf3ba82a82c9fcf9554154164ff5c44a0aa0b27edd634c550592ffd5db00a82c9bfeaa98054164eff372c02a0b277f9a960150593efd3bb00a82c9fde2d58054164eff32ac02a0b27bf98560150593fbd2ab00a82c9dfe64d8054164fdf2c6c02a0b277f99260150593ff511300a82c9dfe6458054164ff7282c02a0b25ffabb5c1505937fd552e0a82c9dfe6a57054164bff370b82a0b277f9985c15 else (if i<6 then 0xaa4b275fda99dd52592bff5db24a92c99ffaa99254964eef96ac92a4b26feeaa5c952593bf6d4ae4a92c99ff6a5a054964dbf94ed02a4b25fedb129622592ff6d814b112c9dfb2e99588964fed9752ac44b257febb656225933fe5d32b112c93ff2ea5588964efd96ac9444b277ee5564a22592ff75daa5112c9dfb6e55288964efdb2aa9444b27f6e5554a225933ff552eac82c9ddf2ca5564164cffd552ab20b267feaa5c990593bbf2aae4c82c95ffaed5264164cffb74a9320b267feaa54990592bfedbaa4c82c9d7f2dd5264164ebfceea9320b2777d7554990593bbf2aaa4c82c9dfb5c95264164cffd5429320b257fdb814990592bfed98a4c82c95ff6c45264164efd96b11320b277ed7588990593bf72ac44c82c99ffaaa2264164eefcab11320b277ed52889905927fedbd54c02c93ff6d6aa601649ffb6555300b24ffdb1aa9805933ff55352c02c99ff6a5a760164bef96ad3b00b26dfeaa9dd80593afed4ceec02c99ff6a5a560164cffb5252b00b25dfdb7295805937bed294ac02c97fb6c8a560164bfeb6252b00b267feaa65580593aff3bb2ac02c99ff6a57560164def9752ab00b26f7eaa95580593bbed4caac02c9f5f9de55601649ff9752ab00b267fda995580593bbecacaac02c99ff6a5a260164cffb5251300b26feda2289805933ff55324c02c9d7f9dd9260164eefcaac9300b267fda95c9805927fe5d2a4c02c99ff6a552601649ffb7429300b267fda914980592ffcd80a4c02c9bfb2ea2260164dfdd5511300b277eda988980593ef73bc44c02c9dfb6562260164fedcab11300b24ffcba889805933fed4c44c02c9dfb64a2260164cffd54c8b00b275fe7764580593bbf2ab22c02c9dfb88991601649ff97498b00b24ffdb8aa9705927fedad54b82c93ff6ceaa5c1649ffb65552e0b24ffdb1aa9705927ff5db50b82c9bdf2d5a85c164cffd54cc2e0b267feaa655705933fed432ab82c9b7faa9755c164dbfb50baae0b275fd985d5705937bf554aab82c9bdf6a2555c164eefb312aae0b267feaa64d70593afebab26b82c9ddf955935c164dbfd54b9ae0b267feaa649705933fed4324b82c9d7f5d5925c164eefcaac92e0b24ffcba54970593ebebaaa4b82c9bfbaaa225c164dfdb51112e0b277ed9888970593bf6cac44b82c9f7b5d6225c164fedcab112e0b277ed9388970593ef6b9c44b82c99ffaa9915c164cffb50c8ae0b275fd7564570593bbf2ab22b82c9dfb889915c164dbfd54b8ae0b275fd935c570593afec92e2b82c9f7b889715c1649ff97498ae0b25dfdb74c570592f7f5db0eb02c9bbfaa97558164f9fb0ebaac0b27e7d8795560593f3e594aab02c9bbfaaa5558164fd7aeac22c0b27ebe5561160593b7ebab26b02c9dbf9559358164bdfd76b9ac0b26efeaa5cd60593e7ec3ae6b02c9f9 else (if i<7 then 0x7fed4242902c9dff6612148164bffb6a90a40b26ffda548520593bfecaa42902c9fef6112148164bffb6690a40b26ffda348520593bfec9a42902c9fbf58d2148164ffdb0490a40b27fed5248520593ff699242902c9ffd4c52148164ffdd5490a40b27fedb848520593ff6d4242902c9ffb69d2148164ffdb0e90a40b27fedb548520593ff6d2a42902c9ffb2952148164ffdb0a90a40b27fed7548520593ff72aa42902c9ffb6cd2148164ffdb4690a40b27fed7348520593ff6a9a42902c9ffeaa97048164fff350b8240b27ff9a55c120593ffcc2ae0902c9ffe68d7048164fff2a6b8240b27ff9a15c120593ffcc0ae0902c9ffe5457048164fff262b8240b27ffaaa4c120593ffcd4260902c9ffe69d3048164fff30e98240b27ff9a54c120593ffc52a60902c9ffe6153048164fff2ea98240b27ffa554c120593ffcc1260902c9ffe5493048164fff34298240b27ff9814c120593ffcb8a60902c9ffe5453048164fff24298240b26ffdb868d105937fedbb46882c9bff6d5a344164dffb64d1a20b25ffebb60d105937fedd306882c97ffaed7344164bffb70b9a20b26ffda85cd10593efec3ae6882c9bffaeda244164dffb70d1220b26ffdb7689105937fec3b44882c9bff6d5a244164dff96ad1220b26ffdb3689105937feb9b44882c97ffaed8244164dffb74c1220b26ffda760910593dfec3b04882c9bff6958244164dffb46c1220b26ffda260910592ffedc2e4882c9bff6a17244164effb30b9220b26ffda55c910593bfecaae4882c9fef6117244164dffb46b9220b277fd935c910593efeb9ae4882c9fbf58d7244164bffd76a9220b26ffdba54910593bfedcaa4882c97ff6dd5244164fbf96ea9220b26ffda354910593bfec9aa4882c9fbf58d5244164dffb44a9220b277fd9254910593ff6c12a4882c9ffb5c95244164bffb6629220b26ffda314910593bfec98a4882c9fbf58c5244164bffd7699220b26ffdba4c910592ffedc264882c9bff6a13244164bffb6e99220b26ffda74c910592ffedaa64882c9bff6953244164ffbae699220b26ffda24c910593ff6c1264882c9bff6a22244164effb3111220b26ffda588910593bfecac44882c9fef6122244164dffb4711220b277fd9388910593f7eb1c44882c9ffeaed2044164fff37090220b27ff9b748110593ffcc3a40882c9ffe6d52044164fff16a90220b27ff98548110593ffcbaa40882c9ffe9552044164fff36690220b27ff98348110593ffcb9a40882c9ffe54d2044164fff30490220b27ff95248110593ffc99240882c95ffaed955c964dbfb6f552a4b24ffdb7aa9525927fed8554a92c977f6deaa54964affd76d4aa4b267feaa6a552593afe5bb52a92c99ff6a5a7549649ffd76d3aa4b26dfeaa29d52593afed494ea92c977f2ea7754964dbfd553b else (if i<8 then 0xa348164dffb50d1a40b26ffda768d205937fed2b46902c9bff295a348164dffd76d1a40b26ffdb868d205937fedbb46902c9bff61da348164dffb6ad1a40b26ffcb568d205937fec2b46902c9bff5d5a348164dffcaad1a40b26ffdb168d20593bff55326902c9dff6a19348164effb4ec9a40b277fd8764d20593bfed2b26902c9dff2959348164effb0ac9a40b277fd7564d20593bff2ab26902c97ffaed7348164bffb74b9a40b26ffeaa5cd20593efed3ae6902c9f7f61d7348164dffb4ab9a40b27efcba58d20593f7f552c6902c9fbf6a16348164fdfb4eb1a40b27efd8758d20593f7e5aac6902c9fbf6956348164fdf94ab1a40b27efd8558d20593f7ebaac6902c9fbf9556348164bffb74a9a40b26ffeaa54d205937fed3aa6902c9dff6159248164effcaac9240b26ffeaa60920593bfecab04902c97ffaed5248164dffd54a9240b25ffdb8549205937fed42a4902c9dff6615248164effb2aa9240b27fbd84549205937fed1aa4902c9dff64d5248164fdfac6a9240b27fed8254920593ff75daa4902c9ffbaa95248164ffdb70a9240b27feda854920593ff6dbaa4902c9ffb69d5248164ffdb0ea9240b27fed8554920593ff6d9aa4902c9ffb68d5248164ffdae6a9240b27fed5354920593ff6d8aa4902c97ffaed3248164dffd5499240b25ffdb54c9205937fed2a64902c9ffb5493248164bffd76d0a40b26ffeaa685205937fed4342902c9dff661a148164dffb4ed0a40b277fd97685205937fed2b42902c9bff295a148164effb2ad0a40b27fbd84685205937fed1b42902c9dff64da148164fdfac6d0a40b27fed5268520593bfed4322902c9dff61d9148164effb4ac8a40b277fd8564520593bfebab22902c9dff9559148164effb04c8a40b277fd5264520592ffedd302902c9bffaa98148164f7fb50c0a40b26ffda7605205937fed2b02902c9bff68d8148164ffdaa4c0a40b25ffdba5c5205937ff552e2902c97ff6e17148164dffb50b8a40b277fd985c520593efed3ae2902c9f7f61d7148164dffb4ab8a40b277fd955c520593fdec22e2902c9bff68d7148164effb26b8a40b27efd635c520593ff6a92e2902c97ff6e95148164dff974a8a40b26ffeaa545205937fed3aa2902c9bff68d5148164effb26a8a40b27efd6354520593ff6d92a2902c9dff6495148164fefaa4a8a40b27fbda850520593fded3a82902c9fef61d4148164ff7b4aa0a40b27fbd8550520593fdebaa82902c9fef9554148164ff7b04a0a40b27fbd5250520592fff5da62902c9bff6e93148164bffb7498a40b26ffeaa4c5205937fed4262902c97ff6dd3148164dffb4e98a40b25ffdb54c5205937fed2a62902c9ff768d3148164ffdaa498a40b27fdd324c520593ffac0a62902c9ffe6c13148164dffd5490a40b25ffdb848520593 else (if i<9 then 0x26ffda85c550593bfecc2e2a82c9f7f61d7154164ff7b08b8aa0b277fd935c550593f7eb1ae2a82c9dff6497154164fbfae4b8aa0b27fbda850550593fded3a82a82c9fef61d4154164ff7b0aa0aa0b27fbda250550593fdeb9282a82c9fef5494154164ff7c44a0aa0b25ffebb4c5505937fedd262a82c97ff6e93154164dffd5498aa0b26ffda84c550592ffedba62a82c9bff69d3154164bffb7490aa0b26ffeaa48550593bfed4a42a82c9bff69d2154164bffb6690aa0b277fd9348550593f7eb1a42a82c9dff6492154164fff576c02a0b27ff9b760150593ffcd3b00a82c9ffe6cd8054164fff346c02a0b27ff97360150593ffcd9300a82c9ffe2c98054164fff344c02a0b27ff97260150593ffca9300a82c9ffe4c98054164fff444c02a0b27ff9b160150593ffcd0b00a82c9ffe5c58054164fff262c02a0b27ff92160150593ffcd42e0a82c9ffe68d7054164fff344b82a0b27ff9325c150593ffcd0ae0a82c9ffe4c57054164fff242b82a0b25ffebb549305937fedd2a4982c97ff6dd524c164fbf96ea9260b27fed7254930592ffed88a4982c97ffaed714c164bffb70b8a60b27dfd875c530593efeb92e2982c97ffaed214c164dffb7490a60b25ffdb7485305937fed3a42982c9ffd5c5214c164fff576c0260b27ff9b760130593ffcdab00982c9ffe2d5804c164fff2eac0260b27ffa5560130593ffcd9300982c9ffe2c9804c164fff2e4c0260b27ff95260130593ffc29300982c9ffe889804c164fff362c0260b27ff97160130593ffc90b00982c9bff2d6aa48164bffd76d4240b26ffeaa6a1205937ff5db50902c9bff6dda848164dffb6ad4240b26ffcb56a1205937fed8b50902c9dffaa99848164bffd76d3a40b26ffeaa69d205937fed434e902c9dff661a748164effd54cba40b277fda865d20592fff5db0e902c97ff6e98748164dff974c3a40b26ffeaa61d20593bfed4b0e902c97ffaeda548164dffd54d2a40b26ffda869520593bfecc34a902c9f7f2dda548164dffb4ed2a40b26ffebb695205937fedc34a902c9bff6dda548164dffb0ed2a40b26ffdb3695205937fed8b4a902c97ff6e0a548164dffb5052a40b277fd9829520592ffed994a902c97ff6c4a548164effd54caa40b277fda865520593bfed3b2a902c9dff61d9548164effb4acaa40b25ffebb615205937fedd30a902c97ff6e98548164dffd54c2a40b277fdb961520593bfed4b0a902c9bff69d8548164f7fb0ec2a40b26ffda561520593bfecab0a902c97ff6e97548164dffd54baa40b25ffdb85d5205937fed42ea902c9dff6617548164fbfb0ebaa40b26ffeaa955205937fed44aa902c9dff6625548164ff7d54c2240b27fbda761120593fded2b08902c9fef2958448164ff7aeac2240b27fbe5561120592fff5db46902c9bffaa9 else (if i<10 then 0xd262c02c9bffaa93160164dffb71552e0b26ffdb3aa9705937fed8d54b82c9bff546aa5c164bffb71552e0b25ffdb3aa970592ffed8d54b82c9fef506aa5c164effd54cc2e0b277fd9869570593fdea0b4ab82c9dffaa9935c164effb50c9ae0b277fda564d70593bfecc344b82c9dff64da25c164effb30a92e0b277fd9354970593bfecc342b82c9dff64da15c164effb50c8ae0b277fda564570593bfea9322b82c97ffaed315c164dffb7498ae0b25ffcba4c5705937ff55262b82c9bff6a1315c164fbfb6e98ae0b27dfd754c570593f7f5db0eb02c9fbf6d58758164fdfb66c3ac0b27efdb261d60593f7f5dae6b02c9fbf6e17358164fdfb6ab9ac0b27efdb25cd60593f7ed8ae6b02c9fbfaed5258164fdfb70a92c0b27efdb754960593f7ec3aa4b02c9fbf6cd5258164fdfae6a92c0b27efdb154960593f7f2ac44b02c9fbf6d57158164fdfb66b8ac0b27efd525c560593f7edba62b02c9fbf6d53158164fdfaea98ac0b27efe554c560593f7ed9262b02c9fbf5c93158164fdfaa498ac0b27efc524c560593f7f11262b02c97ffaeda854164dffd76d42a0b26ffdb76a1505937fed9350a82c9bff2c9a854164dffb62d42a0b25ffebb69d505937fed434ea82c9dff661a754164fefaa2d3aa0b25ffebb61d50592ffedd30ea82c9bff2e98754164dffd54c3aa0b277fda961d50592fff5db0aa82c9fef69d8454164bffd76d1aa0b26ffda868d505937fed3b46a82c9dff6a19354164effb4ec9aa0b277fd8764d50592fff5dae6a82c97ff6e97354164dffd54b9aa0b27dfd875cd50593f7ed42c6a82c9fbf69d6354164fdfb0eb1aa0b27efcb258d50592fff5db44a82c9bff6a1a254164effb30d12a0b27dfcb7689505937fed3b44a82c9fef611a254164dffb46d12a0b277fd9368950593f7eb1b44a82c9dff6a19254164effb4ec92a0b277fd8764950593bfec2b24a82c9dff6899254164bffb74b92a0b26ffeaa5c950593bfed4ae4a82c9bff6a17254164effb30b92a0b27fbd845c950593bfec9ae4a82c9f7f5cd7254164fdfac6b92a0b25ffebb549505937fed42a4a82c9dff6615254164ff7b08a92a0b277fd9354950593f7eb1aa4a82c9dff6495254164bffb74992a0b26ffeaa4c9505937fed3a64a82c9bffaaa2254164effb53112a0b26ffda888950593bfecc444a82c9dff6562254164ff7b09112a0b277fd9388950593f7eb1c44a82c97ffaeda154164dffb50d0aa0b277fd98685505937fed3b42a82c9dff65da154164ff7b08d0aa0b26ffda368550593bfec9b42a82c9fbf58da154164dffb44d0aa0b277fd9268550593bfed4322a82c9dff69d9154164effb0ec8aa0b277fd8564550593bfed1322a82c9dff5c99154164effaa4c8aa0b277fe2264550592fff5dae2a82c97ff6e97154164dffd54b8aa0b else (if i<11 then 0x15ee0af0457362b8b15ad0acd056322af315668aac855182a7115258a89453fe29e414d98a66052fa296214a38a4b0522228f6146d8a2d45134287414218a074500427dc13db09e144ed42744139489c384de626d8135909a884ce2264b1318098284bc825c912cc095c84aae253c128b093c0499424af1244891b848a62438120908fdc47b823c111cd88dd446b4233f116088a14445021731085883104110204c0ff787e483e541eac0f1c878203b821d9b0eaa0740839b81c950e2186f9837281af50d570683c339019600c7c06214302417e10bd285dd02eb2171d0b7605ac02cfe164e0b0e858082ba215b60ac2855502a4614e70a5b0521428a8142e0a0404f8827781375099704bc82540124e090e84758234a112708548415c1fb20f92079503b601cf60e3406f68366c1aa80cec064d0309c17ec0baf05b402c0015300a510515827e81350096104980242811c808b30430820c00fd207ad03a801c240d42066502fe817040ade05490281013440914044301fe00f00071e035e019680c4805ee02d101500096403e201aa00c2004f401ec0099002900002fff5db40a92c9bffaa9a054964dffb50d02a4b27dfcb7681525937fed3b40a92c9f7f29da054964fefaead02a4b26ffda368152593ff6b9340a92c9bff685a054964effd76a9320b277fdb854990593bfedbaa4c82c9dff6cd5264164effb62a9320b277fe55889905937fe5ad54c02c9bff2caaa60164ff7a8355300b25ffebb69d805937ff5534ec02c9fdf2d5a760164bffd76d2b00b26ffeaa695805937fed3b4ac02c97ff6c8a560164bffb6252b00b27fbd4129580593bfed3b2ac02c97ff6e97560164dffd54bab00b27dfda75d5805937ff554aac02c97ffaeda260164dffd54d1300b26ffda7689805937fed2b44c02c9bff295a260164effb2ad1300b25ffdb5289805937fed2944c02c97ff6c4a260164ff7a8251300b277feaa64980593bfed3b24c02c9dff6959260164eff94ac9300b277fd7564980593bff2ab24c02c9dff6899260164bffb74b9300b26ffeaa5c980593bfed4ae4c02c9dff6557260164bffd76a9300b26ffdba54980592ffedd2a4c02c9bffaa95260164effb52a9300b25ffdb754980593efe5baa4c02c9fdf2955260164fefaeaa9300b27feda254980593bfec92a4c02c9ffb5c95260164bffb7429300b26ffeaa14980592ffed88a4c02c9bffaaa2260164effb5311300b277fd9588980592fff5db42c02c9bffaa9a160164dffb4ed0b00b26ffda5685805937fe52b42c02c9bff68da160164dffb44d0b00b26ffca268580593bff55322c02c9dff69d9160164effb4ac8b00b277fca564580593bfebab22c02c9dff9559160164effb44c8b00b277fca264580593bfeb9322c02c9dff5499160164eff8a4c8b00b277fe2264580592ffed else (if i<12 then 0x4c90a62d52d229441490ea41451f728f2146d6a2ed516928ab14538a2765128288a94434a1f450f2286f94330a17d5069a82b540329f9b4f8ea7a7d3cf29e534f16a77153afc9d374e8e2740539cc9c944e42271d138449bc54dd526e3d367a9ab44d4ca68c5340099ae4cc9a6505322099004c78262a5309897ef4bd425d2d2e0896c84b3b2596d2c2895b74ac32542128e8942249d7a4dcd25be926c48fca469d22aa91244884a43b920888ff247eba3ef11ed48f4f479a23b891d0a8dfc46b42332518968bd845ad22b19143889a9447fa21ad0fae8738433c219490bbe855642982145509de84c9422020da90604826e40ed206d102c4810540802012cffdc7f863faa9fb04fc2e7d993e8d9f274f8ee7c513e1b1f040f7ea7bcf3ddf9eebcf6787aa83d3b9e944f3d279763ca81e374f16e78233bf91df04ee1876783b291d724eb5c753b3a699d230e8e2741439cb1cce4e62672b639481c81ce328711638469c010dfbc6f9737871baf0dd586e9c37251b7b4dade6d1d365a9b1b8d8a66c4e35fe1aea8d71e6b6935809ab40d5126a63351e9a85cd3cc69b534d29a5fcd29c692834811a1b8cff66788337f99b90cca06635330219778cb2e651932639917cc84663e731e098e14c6be6339318998a80c47061d030b99858cc2a661013057981a0c09a5ff02fc997de0bea45eea2f5717918bbe85de42eea175b0ba345cd32e40970bcb8285be32dc316cd0b5f05aa62d1f16784b334593d2c96963c4b154588f2c3a16088afcc57cb2bc795d4cadd656622b1e15674ab0454f92a43150a4a80653642989149cca39251a32898141c09ffa4f9527bd13b149c4c4d9d268f9320097c24b7925729299c93e8496b24a2924a8920848f42467122cc9146487d242b920f0902c476c23a311cac8dc84687230f917088ab445082266111e88824440221d810d78861842ba214f908b0842241e020bc103e8817c407720020ffa47ec03f3a1f8f8fbe47dd23ece1f598fa347cce3e411f130f82c7be03dd51edd0f67c7b083d691ea18f47479ee3cd11e5b0f26c79003c651e1f8f06477fc3be31de40eeb477243b771dae0ecd876203aea1d620eaa4751c3a731d2c0e8f4742e39f11ce58e6c07314396f1caa0e4e4723c38f81c6e8e308714e38811c2d8e0d4701e37f41be70decc6f3037721bab8dcf06e4236fb1b700dabc6cfc36581b190d85c6bf835cb1ad80d6286ac835331a868d3c86998349b1a400d194687e340e19f40cedc6722336019978cc5065dc32c819510c9f064c23230190a8c7e863be31c418d48c63862e63158189e8c488620e30ec18688c2d86136308018328c0fc60322ffe17ec0bef45f2e2f7117a58bc945dfe2ed917540b9dc5ca22e2b17028b77c5b882d9e16bc0b51c5a422d0616758b2e8593e2c84162f0b0e0583a2bf7 else (if i<13 then 0x21d4905247b123b291b5c8cbe45fd22e3914e489da44b7222a91024874e4345217c90ab4846a41bd208c902dc7ffa3fb11f7b8f8f47b063d211e6a8f11c77723b2b1d648e9f47436398d1c7f8e2cc701e37ad1ba58dc546d6636251ae18d58469fe349d1a288d01466ee32ff196f8cafc64ba322718ed8c63c622e30cb18348bfc45ef22f17175a8b8f45b5e2d37166a8b17458222bdb15c78ad0c55c22a7f14ed8a58c51aa283113d189bfc4d3a262512cb89424494e242f11ba88bf44536224f10eb885d4422620c7101c87f5c3eea1f290f6e879ec3c321db70eb5874d439d21c870e1d86fbc371a1b2b0d648699c340a19a30cab863d4312618470be785db42e4216d50b2e857942ada150b0a548511c27f61399099b84bac253e125308e28453421aa104707dc83db41dea0e930723836e41aae0d0b06548306c17460b5705598299c13de0977047f8221c0ff20797038481a440c5e05a1029f81424094e042f01f180dac05e602bd010c806840252009b00067ff5bff41ff28ff4d7f88bfb55fd32fe687f163f7c1fb68fd787e9e3f42df9cafca97e41bf11df816fbcf7dc9bed31f5f4fabe7d363e8edf414f9d97cd9be5ddf276f9157c77be2cdf0eef8517c0abdfbdef92f78d7bb3bdc29ed44f6457aeebd5d5ea04f46379fdbcd9de5d2f26b79123c825e3b0f1bd789fbc3b5e120f080781cbbf45de64ef0177733bb59dd76ee1c76da3b4d9da4ced0b7672bb355d974ec9f761bbb045d6faeb0a75723a75dd2b2e8fc740839d6dce6ae6c27348b9879cb40e54e7262b91a1c884e41c71fb38d5dc662e3007141387b9c29ee0d1703a3805dbf06df5d6fa6b7bc1bd3cde156f0837675ba54dca16e4336ff5b7aedbb16dd0b6e45b5e4da5e6d21b6799b2fcd9796c6d362fdb148d8266bd435ca9ad16d6186acd355d1aa9cd53e6a973544daa06d46469e834ed5a642d2f0695fb4a39a44cd192689534259a004cf6e677833a219ba6cd6b6687333f99958cc4f6614b300d97d0cb49657bb2b719598ca2d64dd32575926ec8c4643eb215d904cc80063ed31efd8f48c77e63b1b1b698ce4c62b6302b177d8b9ec551627a3136588e2c41f61ec30f218718c36661a5b0cc185d2c28c611d3077582d4c15a6089b03e181d0c096603db00d17fc4bfb15f942fc357d4abe3d5f112f7997b80bd9a5eaf2f48979e2bccb5e3caf0c97794bb6d5d98aec2d75cabaca5d522ea2574f2ba115cfb2e6917278b9165c622e1c97040b7e45bc3adc516d6eb69c5b35ad9416c12b5cd5ac8ad4fd69c4b49b5a3aad13d6852b3f859d8acda9665cb2dc594aac93963e2b1b558bcac49d61aab0a45823abf255e6aae8b5727ab6ed5a4eac9e56052ae5d56e2ab61559daac555518aa5b551aaa83d534ea93454872a3cd50d4a7e153dda9e554f0aa72853602998d else (if i<14 then 0x8236407c243e115b080983dec1d160df3068182eec15ee09af04758209c0ec6067302d7812fc084e0363014f806bc017dfffaff6f7f86bf9a5fbe2fd797e80bf225f87afb997d9bbeafdf462f9cf7ca0be37df0a2f8057bd1bdd05ee16f6bf7b2ebd845ebb6f54d7a6abd11de822f3af7990bcbade4e6f1fb78d7bc535e126f01b77d1bbcadddeaee937718bb68dda82ecf57628bafbdd6eeeb41756fba945d3b2e9357453ba00dceeae6d17337b97ddcafee51d7247b905dc6e6e3117157b88ddc352e11b7051b80adbf3adf516f82b7ae5bc82dddf6ebeb746db99edc6d6e1bb705db76adb536d8eb6b9db562da396ce0b662db2aad8f36c53b60bdaf42d7296b6eb59edabaed5a16aaab5375a94ed4716a1db4fbda772d39969bcb4d0da5eed2ab693ab48a5a3e6d1bd68c3b44eda236d0e5684cb4135a002cf9f6793b3b6d9cf2cdeb66c4b33ed9906cbf565dfb2dcd967acaf16547b285d93c2c97f6478b22959086c7cb63cab1d258dfac68562fbb15a58a66c4fd6242b0fdd872ac31d6152b0a1584cac22f60f1b05ad81bac091602daff8d7f02bedd5f48af96d7c4abdef5ebbaf3a5793abc515de1aeddd75d2ba715d12ae6b57296b9155c64ae0ed6f2eb7355b48ad8bd6b16b5135a4dad08d6756b375597eaca15641ab1ab5899ac345610ab00d57ebabd7d5e52aef35732ab8bd5bf2ad6b569aab3a5593aac2555ecaaddd55feaa5b54f1aa5555212a89153f6a9d7d4dcea68552fba96554a0ea4a55242a9195485ea3e351d6a8ddd462aa2b35112a870d42c2a0e95038a7f353eaa9ef34f32a78653b169d134e4da713d37da9ba14d94a6b1d349e99d74cc5a64a531ba98654c0ca5edd2ed6971f4b53a59152bf295ad4ab0a53fd290e942549d6a4d2d25d2927148f1a460521e690914822a3f351e528e6f4706a36ad1a0e8ca54600a2d7515f68aaf451ba275512e6893d4462a218d105a87e143bfa1ccd0dce866f4311a175d0b1685134258a108d07da83a1419fa0bcd0522822f40e6a0555021280a740389ffe4ff5a7f4b3f699f9c4fbf27d813e799f29cf8e27bf93db59ec7cf5a67a453cf19e65cf23e78913c0c9dedceeaa76dd3b489d8bceb6e75553a6e9d244e88a73b739b59cc24e4f6721938ba9c3f4e18e703937d59bc74dd4a6e4336e59b4f4d9b66c79362c9b08cd7566b5f35739a9bcd41a697f34789a134cfaa6731337299a64cbea659332a3992e4c82a6387319d98b64c546625730e4985f4c20a60a3301597f24be4a5ed92f25977fcbb0e5cf92e61971dcb8ae5c372df596e7cb6d25af12d5d969bcb41a59ab2c9996294b05a57b52ba995abcac9a55d52aa3952e4a82a5371297c94954a362514f284a941249ffa4f9b279c93bb49d164e2926ee935ec9a064ccd263593024974e4b45255b928a49362494f24769 else (if i<15 then 0x304388110042c8abfcd8eaf18a1d40a8021a2d29c0dd039b718e1dc0b80240cda9e305dc0b00b591cd891a86e34b2535022055f991cdb8c50ea0540145d66413924644ea88520a39433868c75520e1a1a754429051ca19c3463ab97f9b60ec0d80b0d1ce4241c3434ea90510a39433868c7232ff36c5383b0161a3a29cbf12722f36c1d80b0d22e2e7445288503239c34709210033806f8a1b6d4823e401df9c075c35a01d9d122a2140c8e70d1833849053500205c80da08ec3077e71cdb0d680767448a8a510a39c346ae9cdb6a84d04612b9c61ad009ee9cd826823e713542561ad009ee9cdb6a82309b48025738c35a015dd025736daa13411f3899186b402920a75473868875611c75873868a9053aa39c344c81868475511a75473868b0da11c7783448810da11c778345a411d61ce1a25208eb0e70d1120a7547386899030d0911a7547386899030d091b2234ee8688c813aa39c3448471d61c61a24418471d61c61a2c238eb0e30d1211c77871068908e3bc388344901c623b8f207188ee3c81c623b8f207188ee34eb35510a06473868c9d66aa2140c8e70d193aa454428e70d146fb40065cd83e823e707b8a9d514e2040c8e70d1f104398eb86889d522a29c408e70d1b102394eb86895d2ef84af8bcd811f20e30030046805f74e6c166ea823e41c60065c5011a0169d514a219908091ce1a3f74e6c100255a9047c838c00c011a0169d522a214048e70d1bba04af8bcd81180ca4002340253acc845288501239c3474829d514a2143281b1c61a42754828a510e38c3468830123bc39e310e0d106a04048ef0e78c4383c418091de1cf1887060820f7ba2380397239b023b0c9b8add39b32960cc09119dafd45c01d039b729e31c3b837025545847418bb92aff363ab41a11d02337468bcd98330244666bf4a700740e6dc6387706e04968b4a700740e6dc6387706e0496be7579b306446c08d5d39b4231d40ae9cda1191e2d5fe6d4a683423a047abf5179b506847408d868bad202724e31c0a118f8c7028463a8008f8c1772740e6dca78c706e0508cf51694c232ee4abfcda949c8a0508cd57ea2f36a0508cb868e41a92ebc638718627286e8d179b32960488ccd7e83600e81cdb94f18e1dc092d7f9b159446c08ad1683600e81cdb94f18e1dc092d7da2f36446c08b800acf40e6dc63877023b74e6c88c6d7da2f3665288d8119a0718e0488c9d039b729e31c091199af9c8e6cca5812233441a53c6211d06a7068834a611d06a70588308e835382441a5308e9c1220d408474e0908e9c0a11d3815408474e06d00bb82327042eef179b329446c18cd1681600e81cdb94f18e1dc1925dda2f3665288d8319871774463e81cdb94f18447c18c5dda2f36653c61119983502c01d039b729e31c390903e28236401df1c182081c0ef5d3e2 else (if i<16 then 0x18c70a10120842004102b014364acf40653cdb87506e30cc30464a00c8ce181618232500786026a70c0a11d401119c3057c78608c94019192ab860708ea008d4e1812236802446c18488c948aa0529122368028314d845029b423191991c57c6464b548e19192ab238708c9488a042315408462a8108c52388c9401c8e232500663a470a11d40148ea1c291d438523a870a4750e148ea1c250c63a870e47119280391c464a00e471192803847500463a470a11d4011a9046235223844664314519192d52186464aac861c23252290c464a00e4330e111990c230d218508ea0088cc862be384750044664308c3486148661c48464644315f1c862325006464a44861c23a802232522430e11d40148666c2232522430cc3486148661c224350052188c9401c8668a290c464a01c521192b121ae29211d40b8a390c464a00e4312f1423a80223321ae2906218690c2847502e28e43336b8a3232562435c5248661d714661a430890d40b8a323221ae292921a910c23522184218a0119190690c4dc8c928317584632332199b17520862244dc641a43137232426f21987121250624225044248c8e43112280390c464a00e43119280384750052188c94038a4847500461a4308c708612236802446ca4488da00911b401340652268088c488da00911b40122320c2a81418488c830aa0506148666c24464184c38a02231d40447418688da00911b4078a3446448446420c821919083208646420c8218418464a4646420c821919083208646420c8278a420d2089b919204184641875029b4231d40a6d08c75029b12119829042a814da118e411192803904464a01362119297208708ea008c14821119297208a29211d40148266c223252e410e4130e28032435004464a5c821982904284750052088c9401c820c822325009b108c82d904384750052088c940191905b208708ea0088cc8220438460b452099b119191905b2087209871401921a8022320b6411022182904284750046a44108d48821482a042905408520a810a415021482233408720a810a4150278a323320a811392140a0508c65021188a01362ee3a805de118e411192806189502118a411192803a8108c4608118aa042311212ee2904424a00e4106411192804d8846484c821c23a802904464a00c8c909904384750052088c94038a4232426410e11d40148266c2904464a00c8c9099043904c38a00c90d401119904408708c8488c30821186104268088cbb8d11b4012236802446d00488da03c51b0627288c688da009a030611a90921d76402ac81a181cf38047c6961153ae4047288ca717ba720e702bfa0736e3486bf3578c30e990c09bb81601771436f36054c8c03f1a80afe81cd86af18e1c3238170048494eb3566423944662eb320d493924652ea126a013924652beb239b286e else (if i<17 then 0xa78761aa708012021afb4505880111d384280900281888e9c0c048086bed1594a23c34c829c2604977c34c809c142f052e81cdb94f0e192f170d240f740e5288f9b320c3471001100190cd7ca2823d0c0af8c30200a9094022e2b29d0cc08119c00f40b8bc3b810d9304a010d7ee2823604364e0afa070e3abc6064f02388090c268171743023204a010d7ee2b29d0c08d81200f74050c36464f02046761d717437020465057d02e2f18e1dc086c9e62c8608203594823d0dc619c240f005e81c3b8c0d9190ce113164303dd0c08d9c1826805e81ca78c70eb8ace102003d0394e06e0508ca21ba00d9193c08119840486108090c206a367a0329c0dc08119c6cf40653c0a1194400861740e5381811b382f40e5308e903382819e8036794f0e193c1b1c61a48df18bd001b0a9e5209443706c0508f0d322041884638eeb7eaf945e6c8d954d2950d08e83003805869d0121c88648c5e81cd81b0a9e5221b83602847869837fa0036153ca44360284786864aaa00405531dd43423871869143a20423180c1be32462f40153ca44770e10801e83638c34e6be1c7e2f36057c60099c060641bed1662f3686cca65490640488c00a00700c4ef37f9b4362b32a511c8e00e41801a02002801ea020cc401c0c080dd06fcc5e6d0da54a23434a0189de6fb4598bcda1b32995288c0788e00e41801a02c35181810262ca96402393b8134718694b7eafa36804366118018007213012118816c775bf57c64ac5a8bcd91b12900e21a014230030020064022dfabeb16a2a365534a50c0130160060038648c5e802a79488ee1d1dc03d06c71869837fa00d9e523244770e00f41b1c61a5a75b909079b5364536a51080700d20805001900e03237c648c52b3d001552911dc3803d06c71869c906e28294420193ac8201586920040c8df391d00d492911dc38c3106c71869a1c6e4037052886c300600720800c8059c8e8006c9bf0e30c418d4f18c70a1be32462f40e6c0d854f29a0d80a11e1a624046c9dc6811118a402194803c801900865200d0223916400b364809dc69010c2231a04472261c901118eefa41b8b4d914da941d61ac721900c00e41001900f900864060d02223101b8ef0e5eaf188706280f163bb8e872e1941034401b1091ddd4bc570d0e141023481b108f163bb86870a0811a1e401b108ea63bb8e873c621c240d88478ae3a3bf18870779008e3bc390685036211e2ba98ee08e1c1c423c57531ddc338e873c621c2440064335f68a8081582300a7010011a2b2920c08f1c1c43001e81c3b8c0d9c707010011af8232b3c631c1c404821008008d7da28d904602c83718c70a101208503202023c70404a21864f40e53c6283023c709010011afb4565208c0a00b20dc631c2d874044ee08d1c140235f390ca41180b30800160ac6c959e80ca7877 else (if i<18 then 0x60da5de11a0252dfabe8d941423a043670d254041909500081016fd5f46d08d4750e80ca0a8102a3ab869a064648c58b3d0015529ae823b87007c0c20b8161a78c9e81cd80c871e1c0784170207b869637fa00360554a44770e19220b8161a5dd54ea0a510d8e9908091cd824338697c610ca401c804329007201810a40219480390086452010ca401e4008860819e81cdb8701e105c081e9d5c34a4bf77d22dc5a6c88643202b536090c801900d900865202c5248043280075d06fac5e6c8d954a828470693500205741bfcd91b2a950508e0d29405368803a80102ba0df58bcd91b2828470694a029b44018df192317a073606c2a794e06105c0a11e1a6a808331020c11404198810608b7eafac5a8bcd91b2a9a5308c0788e00ea0806d02c350094b7eaf945e6c8d954d2980ca0a11d02c34d501064250d6fd5f58b5179b23625301941423a058698a020c886ff4006c2a7948c9105c0a11e1a574006fca6e2f028460784361a4f401b232781423c34650108440f954d2011d438ba939c34806e0f8098405beb1554a82e0508f0d2c1b83e5beaa5417028478690a0287421183707cb7d62a82e0508f0d214050e84231be32462f40e6c0da94e06105c0a11e1a60c9e800df03035105c0a11e1aa40a08157ea281ea53c600980b10c006002c0c8402beb16a2a365534a50c00b80004d8064192dfabe8d894a1802602c00c00990c501066000ca04804003200980b30194bf77e9b02999146009a0201720003b24035f25280064013016750015001c34d7da2a000a404c059e4035f2521498102b02602d02a4038d98b3d0036d296e9c3b8161a582f0101b1a292960488ce01fa002ca53c838770278b86922a7a070ee043670d19404801000406d6040b1001d5446705814ba070ee04f170d1d4048013406e888c60bc0435f68a4a511b02c34c813c0911e1a640406bd0381223641868c106403021c8043290072010c8081c80432901629240219010800990032019b2401c804329010c12402190103900c39108c0cb5fbbed16e2d366536a68c01320401400b56fac58828d954d29846a3a8700d52c5883cd91b2a9a530184100d846a09b1079b2365534a61180780c20806e1a641988225beb1620f3646c4a611d0e00f0184100dc34d833104510494c23a704501064040fa070e1b34e06461a30c98b3d001bd29033c380f606a71869603405859e81c3a9c61a38405beb141eaa9a7020a11c1a4ac55534e211c1a2adf5534e211c1a2a80a050646b7d62d38847068aa02814191c23a710686a028141918c9e800df94882a0508c0f086c34aa7020ba0736e5381a81023c34904a05762ea92ee08c34e1a2709205201afb294003200980b42800a800c826beca50004d02640cf201afb29204148098053809010d1594a23a706501200401c2cf40058c else (if i<19 then 0xab7d62c4146c8c943423a0c00c4161a5ac5883cd91b42950d08e830031058696b7e20f3646d0a543423a0c00c4161a5a808330c86a020c82d1a808330c874096fac546ca18190828470692b154353810508e0d196fa86a7020a11c1a3280a0425014084a02810834825681b17430232ee7100110019bed151482b046c18029e5495f68a8ab8c30e60c0150202548ba002310675aa08d873062ee1ace0ad152d5e8108d54a29e6dc6387706e04c1002a4419c1695f68a8a411b2060c5dd208d9030e2ee40ce0b5a28d94525dc119c404a914df9521051482360cce0f37e54b380464100110016be8a811b06b8a014c2a400f406e9c63877021b280940b4364d560d715810234340064dd26adc504660940b5afcd560d71411b024032953d006cf02046661d356e2f020465952d7ca2c32604364119c404a910419aa08d835c567060652a402f40e31c399c0d944d5b8ace01193a07361b3ca464886e0c20b81423c34b4eb72022a29b53c628c48e0280191c801900db916a710239c352013a9c17a45b8a0a64701400c9d51ce1a55c5c408e53ae1a28df390317a001b06e0d894906105c0911e1a6866b900dc0c80f00c0bac1001900a39188da060e3524e700175e3061940dc34dc84478801a03339c8e8006cd4906e0488cf2010ca404304c8186059030c092fddf48b7169b229b532390c80a40561ac1001900f431716d4d82447200349e3ac2314758462e801d594f36e0dc0a119e3ac2314758462e808e794c23e0d8819c1c33f40473ca78357467008d0317a00a9e52dd04770e03c20b8103dc34c1bfd001b0d9e52f144770e03c20b8103dc34d1be3152cf4006c0a99488ee1c0784170207b869c37c62f4006c2a79481e105c0911e1a58df18bd0054f2911dc399c01ec34a08157ea281ea53c6009a80a0401400ac0c95f68b7169b329b534600980760401400b40c8c918bd0054f29ae823b8706700f81841702c34ff8bcd815f1861c04c03b0200a00541906fac5a8bcd91b2a9a5301941502846a1800c0078196bf77ca2d366536a68c01300ec08028016819e81cd86cf2911dc3a640071041378161a684a0c837ca2f3686cca654a0660520911801400e5bf57f9b2368b2aa694c23a1ca0003a8201b4094300180118b25de118fa00a9ae823b870d9105c0864e1a5019e8171794d740f7c380f082e040f70d32402194803900c0852010ca401c804321286065afddf68b7169b129a3004d81005002c03237c648c58b3d039b03603c0aa9488ee1c0c803e06105c0b0d4c35b45f8bcdb8c01360401400a4320df68b3179b436252819814824460050037ba740e6c0aa94f20e1c01f03738e04f170d354041988030e37541bb0205d609119cba81ee1d81b8c6003aa4e5005bf57c6cac5a8bcd91b02a15308e870075040368161a80d958b51454c else (if i<20 then 0x9061a9009d51c9f201c8447868806c1d1dfc80714c302c31c6a4c161a100c501714406c1d1dfc800b0c7182c3420138df20e74c800b39063878b8692a03000ac71d50db8691c97203c5c343501802e28d1b5c54468693b96e2b204eb8691c97201d578b8688a001d4231e400807208c98ec349dce8dae45864468693b983483707477f201c830488f0d26e411964161b0d4804ea8e504653b9c8069868b2012060019864478007203000a40240c0039018004a002802e29a9a3163ac34804ea8e52a0300091b5c5b0d6a511a1a4ee7401716d4d1831d61a402754729901801e28deac2371ce1a3ae1a8707800f7e20bc5846e181a1de43a984786940475870778b08e3ae1a87058011d620bc88460341a10a440078aea58c38e304e1940475214a3526382f186c342023bc384280c00239186a3bc382280c002790ea611c77871068cf1611c77871068b1dde4423069068af15c33a98471de1c41a3840c00714d49868471dc12a0d4bc530d1df0d438360087308c78021cc231e0087308c62023a8670684c80e3a3ab8678a0d0c901e2b8e8eae181a1b203d50471d41a17200337abc61c73868ee7480f15c747570c0d0d901e2b1870c0d011980d867c80ea5e2b868ee08d1901e2b8e8ea0d0b901e471870d1dca06de4640753c61c74773867c80f178c38e0671dcef2011c7506840cf901e2ba9e30e19c7477435f9be3161b30690c88d814329058696064afb45b8b4da8c30eb1cc1ac3302003609a064648c5e8019c15629ae823b87086e0c20b8161a7fc5e6dc818300528df58b5151b286a0c8c94150284786800c0068196bf77ca2d36a30c3ac7306b0cc0800d826819e81cda6a82ac53c3864f06105c0b0d30320df28bcda1b22960d219814824460050037a002ac535d04770e19220b8161a5480432900720032010ca401c804328c86100afac5a8a8d943506054a0a11d02c34c2801ac6ae1a248043290072010c82d1d361beb151b286064a0a11c1a4d400815d06ff3646ca1941423834a5014da200e9b03212dfabeb16a2a3650d4191928284740b0d316fd5f28bcd91b42950d41941423a058698a020cc321a808320b46a0028ca9008ea1c5d543139c34807cb7d62a86464a0b81423c34906e0f96fa86505c0a11e1a4280a1c25014384065afddf68b7169b51861d63883005002c5bf57d62d4546c21919282a0508f0d001800d192b16a2c2900e218bba82a0508c00c0062dfabe8da148c950540a11801800a501066190d4041905a34eb721108069aa8e400c804019a6c83ac70060d7355015820558696865190a4021948039001900865200e402194643900865200f20064021940034641900cd9200e402194643900c38497eefa45b8b4da54a0eb1c86405202b0d60800c807c804328c86065afddf68b7169b51861d63983586002409 else (if i<21 then 0x4001e819d39070eb91c1ae2f38e046a79b61a6c8043290072002d16e2d3625288d8358600a8baa0dd8302eb5337d119ca4f400cfc83870c9e0dce381736c346a5803abd0033f20e1dce381736c346a54757a0067e41c386c706e6d868d4a962d45846a3a87286a0c1b5415028011d5908e3a8aea8450d80a510d8e40d6191cd824338699c610ca401c80432900720039002064eaf40e6c6a49486711dc3843706105c0b0d3a6fa45b8b4d910a06b0c80ad4d82432006403511a751345b8b4d91190605601400a2e4329b0c0193bd824460064024032562d455534a4038868eea0a81423c34006003940419128083220c972022a29b5288403239432006402c0cf40e6c19f870a91b141841702c34b05f37d22dc50528840306c4728670d2c00819391d00d4929ce823b8718620c20b8161a7064b900dd1080605d6090c801900a391d000d9373539d38c70e30c41b812cc32194803900865200e4007200511a7516400819391d039b06de5219c4770e30c41841702c34e9be916e2d364536a510a02b0d6090c801900d9008644b1620aa9a5308d4750e50d418018828011d5b10611c008ea488308e0047524418470023a9064f40e6dca7835020cf08f0d240cf40d8a2a794b7411dc384308209bc0b0d340cf40e6dc386c88209bc0b0d246ff40e6c0d854f29d8a21b83082e0488f0d340cf40e6c3679488ee1c01f6288209bc0b0d34018191bfd0054f2911dc3843706d8ace30d340cf401b3ca6ba70e193c1841702c34be815d39070ee71c0864ad5c3490921906fc45e6c8d954d2950d4194150284786800c00855fe6c3654350650508e8161a495f46ca0a11d021b386a6aa14007a0374e1c3278161a9aa70941b183302447869004d5448043290072010ca401c804322092b7eafc45e6c8d954d2950d41941423a05869c12aafd0684740b0d2d53a8083225001abf1179b0d95534a40388650540a11e1a003001c57e22a36552a0a814230030006caaaf8c9a0508f0d4005aa3210a020cc451f4006fc385484de04367628c5c34ae81c3b810d9191868d2010ca401c804329015492402190943900864250e402801449c802900864250e4028012df8828d954d2909aa1a11d0600620b0d3220aa9a52a1a11d06d8b4e30d2620c23a0c0370d2d53419883000706620c001a80084b0945df9b329d5288ec300d205869612dafa2300a802400d919085012005d039b025e5221b835028478693d00c35028478686c8c939a931c61b0d0808ee65001c80756c361a4ee5900903000cc3600144046e27ab0da11b868351dcc1021b3c5846ea5c341a8ee87ab480c73868eb86a1c9de298e752e1b0d2808eb0e5006c1d1dfc806a4c318284786840294007203a931d61b0d2773280c0025001b9088ceae1a9009d51c9d4060015c846d6a511a1a4ee6b916a5 else (if i<22 then 0x8c059b2027711a9c80210844806137446510c9028343943088cc419024862328e4a4de4330e81888ca24842140c8108ca900039124304108503204234ee5124902a02364ee5192210a0640846519224920423a805108503201c5846512490211d402186c8008c74804700c00e448b90211a7718864815011b2772a0490d07111c802886014902835402a0490d072402392c86038cda064804ee610c0952054043088e401d024868392011c964341c61c5020622390070022000f03d228290c005a01243001680a08920811b401a8290c005a03c52c8647208c4003d2c82046d00720811b401c82046d00c32822a8290cd018c0232b404ee08c63264134030c08cb209a00231c8268002c7209a03c5016418b2088902318492ebb2003cd527248f4023ba740e41c3b9c70215fc6b80246ff405abaa790738193c69037fa003611dc38417026343612317a0736e31c3857f02e35c01210035849f8bcd81500b247c6803a8200d8abe14aa2f36e3004e8700ba040b003d0075400d63639b02a02602f8d00748196be360a2d36a30c3ac7302b04c0003d8068c9e800d80c08ee1c20b810d8101c016f7fa0336630e3b87382e04e0057f005b5f02602c57f1a00e615e0bc43164321948040932184100baedf03d8d8154c801648f400075840abe04c058d800f400e064354c8f8a04c05f1a00e810c16bf7140980b60001cc065afddf68b7169b518200149377fa0736a6c0ab14d8ee1c01f03582e04f168d3a43119280c0884649909430417b401175dbfb2362932c6c5025480ad0448c80686d00e2ebdd1647c550c4e54100b24691bfd001b01811dc38417021b0203802c8c864312914862325007320321ae28817dc515d54ea886c7241b0c8e6c161a49864328186066efdc5b1c906c302e4056a6c161a003201a9d6e4241b5288403a39c34006402940419882305e064209dfcbe71624e45e6c4d8c302a853c608c18ec1c6a403c0630580800880c06b48bf179b02ae3004d0100bd0001d6906e282a44201d3aa39c348032160209dfcbef1522f3626c0aa14f1823063b0700780c60b010011015c3390417f74cbfcd815429e4183803c06e71809e2e1a828083310461541502fcbf838e440678b80b0d294041905f71481200382fcbe75614bc5c1d80b0d2820871b900dd10d8605d60b0d001900b082723070064ee1c70d1c091dfcbe0dc9b029390018c160244386980240ce0e4ee72017186c34830c865148e402194823900905148eefdc54336a50758e48202901586b0586800c80728088301872010c82f78a4e800d86cf290ce23b870c9105c0b0d2fa0036054ca7e288ee1c21b83067105c0b0d3462f4006c2a436f2911dc3803b060ce20b8161a70c5e802a79488ee1c19c437064ef8696102a2d2984619e830050028a6c0ad11b06b0d71402801 else (if i<23 then 0xf4da11a00280ca7031921d90ca40a814da118824076432902a02c5a6d08c41203b2194815029b2182422090a02a05368464280004060c0f0cb480036a00c530c903c5021c80d26c619686520423a80324c0350c80c8bc4304014060c6485e873900832d0ca40a803146c990c80c8bc515000d9345e66c900632465a19480486a0218380d4320322f102f30e28088495006c88a0001018714803416a3710486540180f00d05c2a489021182e1b2448048417218200d05a8640611871404423500034168c16a1903c02c812003182c3403005a0628050805083da05065629002bc5103da0506460f6814191aa907b40a0ca862c1a50002c7069403c5016404a0780b00d10054800550c069846528000406118201e04a05a119012a4002c5de11940f140842034430c9302548005864c23281e281084069012a4002cb161194c100c046302d08c460806023180d2425dc6a180a869046410401e0481e261a1005000613600f208f4e120007812208a0240461a00e01a411b0d080280030e280780c7a7090003c0958a208c0240461a00e01a412003a1a66d03241130d08002a01c061511a40812860038823009011868038069046c3502409c822280900d00039822d38304a01a0007012f164120c128002401e41140f00c02701880140f0861a80904d0003b362c8000ad00c11240005680608920111b401a80904d000380978a600ad01e2d3824800104e5119240223680390088da00c1e480446d008a024100702a46800158c538203c446d00688da0080081e100390c005a01c52001e81714721811b401b400037158c124302368036492180080c38a490cd019b02324860460b86c924334019208c80040f0801c86003d00c710c7486680004921890b40198e90c005a03c52808846484401243121680390c485a00e4312168063943160d08668063809944334078a04d0314c74860180049219a0336242419321890b4024862420b862190481340c4e80cdb8c4232740e3108c7d038c4231f40e3108c638842140c8108e3b9ba023643108c34946708428190211946488428190211a7730c919c902a02364ee6c8108d3b8c0080c1080784495a0001018cd88d000080c18c9446d020cc4018a6680004063c5202b01888c6d000080c630419233911b40833100c1e042140c811dca01fa023618c90f086520423a80218e61b20077187843290211d4028254815010c2232a4103803003d4028c91085032027728c9190902a02364ee62908120e22320c919086520423a8062908106cc1c4725038cd92027720c904a902a021844662908120e23926404462838c392022320d8108464a06402807e80b14681012b4505802ca32442119281900a2bc180812a40a817150c08644672b08120e5c54725838c39205c5446548207006007a81714c8120e5c52528 else (if i<24 then 0x475c805003d00d48d0c849e80314886520423a80324a0040f5c56044232007a00321b05152006a05c503c56e86a5a0001a81714c004045c51801060278ad0000d4038a5446007a001e064360c007a03c51801e80f14632511b40833100629800f4078ac608007a03c519df2801c4041192a23680020bac2390064460209b919900504e88c04137202e2320700f1000808500a1a00140080880030940040440020d983212962c002801010f1600100f1192801c720141574058a3003d00e28c0f0ea43290211d40302a1d480065a80081e60441923a90ca40847500c6a43ae4058a4ae837d0ca40847501629c8c9400543a9001400f40101e1aa86520423a8061920788c9404eb900c3246aa1948108ea0188c95543212a6a94d48d54eb90080790c82b847500a2a50ca4084750243188ca1995321894d90428050c4a801a80f1444669b2082eaa00ab569b4401aa92814da20286280104e46411092288e00209c0f129018e680006a0518352031cd0000d40a306a40639a0001a80f168c1e11827243461401400827243c600f0221247003d038c0c00f40e303192485a04198803160c1c00f4078bc60908c13f1818ea242d020cc40830619235490b408331020c1c54921681066204183001e81c6060040428050c400202041280080819190f70642515f58a6002021e28e1180826e46540148c96a0e30648464aaad5832128a46554c1950c419c0788c940843900401c00f40230303c33920423a80314c63809f40198e1930872048628ce432902a00c51b26a1d08c404d40286181308130d0e842b146aa687421181378a226f43a119215005a1d0844b56874211aa9a1d085431000f4038a46080781aa40847500a0d520423a802a46c98b501e83201e00140381e83221a00146f807a8007881840461a90057c03a00388000f9006c1054807a817140f170d080281900e28073240a817145480780c605e0230d480b8a01c031c0461a9017140380640074352019b240b8a544608920007a817150c1c17808c35202e280700c7c35202e2813261a501201a0007c81714d4a0038861b0300e078430f0d34000ef14920003f403524c3401da00cd4c8000fd00836640223680490088da00f0d007680f14808a40007680c60ad006c881ab404464a4986803f4078a410001c13892208e00f0480f130d08028001f201c5352048001e092c511c631ca024000702450020304208920820020300f129c1826800040614060010103a70d000080c3045018004040e9c182680004063c5300d0184e511a80280c00202100119b40c1320304d000080c6306018004040e06013101c50001c061020801010301b06620ac52041002021e29006c19882301b066208d5480d833105431420e1a500020039417e1a500021e280700c728000406136201e0ec031205401b else (if i<25 then 0x1a80714acd8a0032b8a4640619a0001a817158c1c0082db8a361d714400416880082d12328330c8a28d929190d58694041905a60020b5e28ca000146430643210ca40847500c5200083218c919086520423a8062325210ca328645064cd9200c8c9484328ca1914c343244390090c98708154321b0310c86520423a81714c46417a1905b86a405c53a1a66c0cae2908c82f4320b70d480b8a7c35201875c5211900e0b4c3480b8a0a4e50000a3238a460a0c849240847500a32449240847500a2190ca40a0d500a00419084321948141aa0148321946521a19148321990c0c900164303266c90084180a23290d0c8b21a1930e28040020b4420e9c18268000416940082d1538304d000082d280105a266d0b44c80c13400020b58c180082d130e85a2a70609a000105af14c00416882080105a3082004168c8c84146506619142082d846308200416bc521190828ca0cc32291905f8694041905af14e41820a320150c8a32c191192810e72018a000105a319690211d40464519232d0ca40847500629c8c94b4320b6194c531824650e7200d9283266c90262908c94b4320b6194c5343261c5026290a5a1905b0ca628d931824650e720128106810419502141a5014087409e28819502141a501409e29143032281408809419119281087201ba02180d308c85000082d230406409520540846504a902a0177846506450210e4058a6186c9c648254815021194a000105a71480c844a1948108ea0188480106431922250ca40847500c0c88c940443900a46484a1905b0c8b0c987140191905a01c4490400670fa35abd01e2aa90fa51ab2a400b4022a99bed018c0232b4006477d8c0232b401b208c6aa66fb400fa41b008d830cef8016800c9e29654823680315208da03c524a968008c72a5833401aa99bed019b07d29df952004169011b401b236805dc118e548236803952005a01c52340002714193182b400027141912548236807146c965480105a71492a5a00d9046495208da01c51b251b00888c940c81860c01fa02c543041920888c940c81860d88c97e40c3043539030c0c44e400684670c146582223250320439c3071920888c940c804da1ce184182c810e70c10c16408738608224111092819021ce183a400064250c106482223250320439c3071922250ca408435010c1cc3640073860806e118671b4078a06e11e202b4003708d4710ba833847880816e1189a01df06708d4717a001b84788081a61189a04758463680f163ac23217506708c6d0034c231b4066c06e11a8e2b4047308c6d011cc231a23002078646400f400ce1e0a37c00d4003c4446007a001e0ce1e0c007a00800f4078a3057d00baa232001e80cd860040428050c4232007a00c820c50035000f12e29c5680006a014250010103002021402862001010203c464a else (if i<26 then 0xa1f40d908cf400641f47501b30a90035003391e2b40a80714d487d036730c467a00d860c5e800708cb3806854472009ccdf06850cef14d4c230665e801f40d8c648d543290211d4018a73abd003e83320a94320ae11d402919e800783e878036610c006a006723c5681500e287d036630cd0000d4023298475013aa235be60ce88c198cd4919e80360888da0423a0c4e809dc4c0911a7718010cea016f900086778a300219c508c33a8026e4656f98aaad58321b464948caa98321b56fa8030010ce2e806a43e81b20c919086520423a80600372045206ccc84469d4a36033919281900a01fa02c51f4038a1f40d90338d843290211d40b8a219056033dc52520aca3246c119281900a2bc3692fc812a4bd02e288c30d5c8032486a7a007d06640da362e292995201cc6a46ce409524e801f40d8c338864320ae8347584671139008c83420864329028354028010ce290c1b511a7527401084dc3e87603661055029b0670365a70d02a01c5a6c1f40d9e9c1826815029b01b35402734d91187d5be0cced02a053663088c0d9a9c1826815029b07d036760d5029b4772441846b7e000342c4178b08e000342c418470001a1220937846b7e0003432d588308e004752aa9882b7e11a808000d0f10611c00068488308e0047522c888308e004752c4178aaa611c008ea650d1049bc238000d0ca1a20c238011d4bd009b11884606ca19c12a40a811de1199a004a1923447d01900c25005670319288e0c82e10451be467a00c9208e233d00649041119e803248c0a404c51801094a0162900084a13020801094a0162900084a2beb54800425080084a100109422321610c84a98a52321610c84a98a50021284004250800c415ab000800620c00184d83310562c00282523250210e4018a6e8086034a868465847d00400c12a40a8108c809520540192aa4bbc233f408462193502118d11e40c00714ef97206001640c002c818005800c71c51a40c002c001c001c007205800c31a91a40c00f147801e2892060038a378ac805800e28b003c5118648180078003800e4082f60038a3c010e6118f00439846304b8021cc2320254818001a4232e0087308c609700439846404b801e2c3930d08cc8df00034846430c0970043930508cc46400c320ce3a8a88c00f4006419c751800f401001e80f14688fa00800f4066c3232006190d525c538ad0000d40280105a2304a0002d4020322325023ae401006280005190ca4f4046eaa480c90ca40847500a0c80088154321d432814d8190c00c320444641a969018e680006a0518352031cd0000d40a3060020b4400416888ca328330c8af946703223250210e4031400028c88c10672408475011914c72328439006c96870687051950e128631d438646400c3203c360add0c3340003502e2980082db8a30020c04f15a else 0x8c807e803640f032308000f5006c128d18068001ea03c5b8a7a3401c180e8d34000f500e2941800705e350c0aaa01c51b25a34d0003d4078b714c71d54807a807149468c034000f501e2dc5380705e618d4912080705ef1489040382f78a448201c17bc5640548201c17bc52186432906034412a2300219c60053aa230ce44472026f83420c5233d003e81b28c5446006a00c92f40b8))))))))))))))))))))))))))
def orfl11 : Packing := (1638,4,7,10,4,17,0,orfd11)
def hashorfl11 (i : Nat) : Nat := (if i<1 then 0x5701e405f4a430000097c400000b05ec0000000002ba900003818400000000000002035400000000010dc4000000000c2870000101b2000000000000028197000000000e0a2c000000001c09e20e400000d0be1c0c1000022b60000000134000031f29d2780000000000000080a680000000000000000000000ea318000000000eb75a24c80000f088702c300001402400001834d0000000007078edd6400000000000000a926e00ec00000000042e582d700000000019e910000000003a0838045d032689efea350000090188000000000000060a3001d89033080014055c0000000000000000000000000000000c026c0000e2cd7801850d7c0000000000acb00000300000300100200700000100000200300100200200200000000000100400100500000200000000100100000000200100000300100900000600200300000000800000600000200000000000000300100000000800300200100200000500300200700200f00100000100000100000000200000a00000000700f00000200000100300000900100400300800b00000000300000a00100200500000100500500000100200100300000200000600200200200000800300200400200000300000000100000100000000000600600100100100100100000000000a00100100000300300400100000000400500100100100000200000100100000000000200000000300200000200000000200001100200000000000400100100000400500100500300300001100700200200000000500600000000300100200100000200700100200100000000000100700000000200000000000000200900400100200000100000100300600100100800200000400100100100000300500100a00000900000000000000600000000000100000000100200100000200200000000000200500000000000000000800500200000400100200200100000000000600300100100200100000200000000400000000000000200100300200000100000200000000100100a00200500400200500100000000000000100000000100b00600200300000300000000000100000500200000400000000000000100400100000000100000100200100a00500100200200400000000300100000000000400000100000000500400000100000000000400000100000400000000100500000700100000000000100600400000300000000200600000300500000000000200000000000000000100100000000000000300000000000000000100700000100200000000100000000200300100200100000400000000000200200000100200300000300000000100300100100000000000100100000000100300100000000000300300100000500000000200000000100700000300000000a000000000004000001000002000 else (if i<2 then 0xab655016c28d2000000000000000000a71100000000032b0b5045400005776a81810000301f0207ee0816302b5832aa1a0fc25a006c40000aa11c0000000000000000000000000000000000008362000000000000031e93000000000a09496a020000000000000000000000000000000000000000000000000000000000000001077400007021400000000000000000000000000180d7e0527423ca0e30dc33904080000000000000e2c06827b00002803600000000072edc000010dc000000000082670000189ee000000000907cce8622094dc0df1a31f8011b06e3c37f000000000a0c412af56aae2c2be00000000000743c3525adabe99d805bc0000ca0adc3a5000014208000000000000000000b0bf800000000000000000000000ad9c0000d042000000000340ffc01ee42cd521b00000f0cd80000000000000000000000000000000000016b95000000000000000000d08005cd9400548230b0b10000000002896c0000000000000002de205b000000000000000000000009ac880000c05b8c0066021b0812301da9f240000000006758c0000000005d150000349ec000000000000000000000000000d05849e347064a037667ef80000e015b011a00000000030a4c80bb00002c01aa21bc0000725e682d200001a860000018186000000000000000000000024305000000000000000000000000000d061741a20000382ae90024403c27bf602030712f017200000000000000283e000000000000000000f0738022400003aac13091302d71003c296600000000000001c01e00003c295903f888d200003c241e2c2f03b83042c000030135838f7a2d4c223b01c34294ea0a1c1c95044d424d000000000300c8000000000c05a00000c10000001481c42ecbc0bc00000001200c54000000000000000002c0d0f05184a1c0000000000000000000000281416ad7c000067538000000001c394e0a400000000000000025040000924a00000ba7a400000000000000000042af9a0980b5f00e629c3500003001b000000000e03d5c885227440080d24e4000000000000000000000000003dd9c000000000001b4000000000000000000000000002c06ad264c000070dd51c4e00000000000002881b000014007000000000328685ebd7092f1d6060cd7c9f8000035eaacace0000000000000090eb40000a015ddf20000002b2617a750373000000000270e0000000000000000000000000002c155b0e24000000000000000000000000003c92370d20430c0000000005ae4702f067748000000000cb0660a8ac116000000000ea4840000d019c00000000283a72a30ecb2200003439f802d00000000000000000000000aa6c4000020553c2d600002093a0009c0000205a800000000000000000000001ad9000001069b81f6f7cec00000000140930 else (if i<3 then 0x10b2f000000000000000000000000000b08ac0000000000000000000000000000000000000000009abaacbf02e000000000000000000000001aad380dc2031a6ae97ada00000b01e40000e08d528a60000000002a128000020335836900001cbb6b00c3439300000000000000000000ca5c1eea00840000d09fc00000000000004aa62a8363276201c252874c22c000000000b7295680f901000000000000000e0900000000a1400000000243960000000001038e835300000000040210000000002dfb9000000000d0c5eddd53726600acdabd240197025640c000002ea9670e6e5c3130e74c0d3103edc0b3d0ae0898d0000040430000142adf095a808300002c1e2f07300000705c40000f02900000c06ac000080af20870000000000000000000000000000000000000a7c89031627c466ba7d2044000000000000000002084c307fa417d000030961300e400001268a9daf0000000001a4580000c0d6f838a00000000000002097b000000000dae8c41969032e006c70ad60097e02c5493cfab080000f0a038017e70c00000000000000000000000000000000f059400005a31581a50000168b29a7dc0343607ad81997269ac156203df82ba0000040810000000006a274000000000000000000000000000cab1871d4c1f10087a42f22003381df4ad98493d30a96c09a00003035d878300000000000000000030269b24740000e01bc00000000000000000000000000140b70000143ac6088a8825d7654c0a70000049fa00000000000002026800001834780b738bba00000e9c0d26a000000000282a400000000040e08000000bc7033cb04f9c29d000000000000000000b0817c2d3000000000c0c664951000000000105440000000000000c028800000000000000000241a830ddec2e4b2663421600003c1369059c0000b0cb00000000010052b2564000000000805c000024b07000036bbe704c40000d7a5000000000243a0603f3eb7400000c346c060c0000e0704000000000000040ec4000000000c27c000000000904eb9d14aa17c0000c0b19c337000002abb57ed0000000000000060d8400006a110000017c980000704280000703ebc1248262e018d0000000000000000000000342d000003804b000000000f08ee411eaa84449c9e0866402f70c900000a040400000000341e40000249a0000000000000000000276a40000000000000000000000e0b2c00003a6ffc12d609880000d0682c09f40e200000000000000000000000000000000b0b38000000003e83b00001829c000000000e21dcaa8e00000000000001c9cc008480000a02524259000020358ba313017900000020dd03129efe00002c2fb000000000000000000000026b83000000000a2024000090bfc0000000005ecbe70d00000000000000521140000b043a else (if i<4 then 0x800001045c000000000eb364023c000000000000040cac00008218c423a901200000378140000000018356a087ec943fab121f14f0eba42f3b0345026b000000000000000000109d0000000000020400002c32700001dd6bba868000000000ea120000003410000100aa10a38000000000000000002801000744000040b140000f203501c00051f9c58daa668839500dd00d600000039a5031e02c800002c321070bf0250021a602f50000000000000000004269c000000001810db05f84945000000000026ac028a0000329e4000000000001d4000000000000020ac00000ca80c0000608cc0000000000000000032a95d09dc000010ab1cafcf775d4264000000000b072349f3c0660407a6a870000000000c91f000000000000000000d02e800003281043b500001000b10e48000000003aa7f50d70000000000000020b1c0000000008b855086c0000e08cb0228a0c1ec1a9da35cc2e25a1161fb2009180000b069cc9ce00000000000000000017a54831200000000060ee4000000000000080ecc493b00001aaeef24c4000000000ab6c00002aa930000000000000309ca3aa6c0000008d001c4027dacb0fc27f0000000000000000000000000000000000000000000000000000000000000003409de070e034200000000010be71c8520a7c000000000000000000000000000c0da000020350000000000000039e1c000000000000038933c0248000000003c34c00000000000002833b00000000000000000000000cabf0000000000000000000000381ae42c200000e013c00000000000003abbc00007a1400000325a982cc000031d6a000000000000000000000000000d0d240000d0a27c1f89711400000000041d5506900000000000000000000000000000000008d8000050598000000002080e126b2c0e6078680000000000000e0ba40000e08f400000000000000000000000000000004a09d0091606b3c0ee8abe4000000001034b0000000007007000000000000000000381e8a06fc835730094de0800000c029e24318333b01b99d57b787a8ba9000000000403be037a000015f2f00000000070aec0000a0ce5481e00c3f5d7800003425d4262000000000309df000000000000000000000000000509f80000b02ae6a9400000000000000000000000000000001c39100000000000000000000001029200000dd9300eec0000000000000a04b802da000026824000018359daec000006030c0000000000000000000000f03b40000000020022f235c000000000000000003412900003020e40c0641140000003b4104f6c2b98252b40d9c0bf5437d60151c0e81734b4118000000000000016aecd7c2c000000296c17f000000000d03d800000000188085a16c00000000000000000041af070480000903880000000000968000000000 else (if i<5 then 0x4000000000000000000c05080000b24c140f46232b4053000010137727adc238000000000f0a840000caadec91650db40000000000000506f000000000000000000340ce000000000600c40306000000000000030328c04ff4229d05dc0000007cac2d900003c1e100000000000000000060029683700000000060a81289c9063c4b0a20e79c966000032aedc073e008e4097c0000576f0000000000000010af789a370d3e439980c4c837220aa80000000000000c0719426600001007d000000000d0cfb0251000016a140000380d50ad74000000000000000001412382c24828d00001c0e5000000000000000000206b44135d0c6a89b21a5739cd70000101e7c061c093827ee94016a0758000000001030d0000049d3709940000000000000000000000a0c6301e6000000000000000000707680000204ec000060ec00000000000000000000000000000133ea838c099602a640c52a4880000fa4500000f27340000601800000902c9abb40000000000000281aa00000000097150000000000000000000000000001c0f3e782dc12030564000030d9503a8000000000000000000000000000000000000707f6eb6d0000000000000201b400003cb0000003024ad05e8000000002eb3700000000000000000000000000000002ab61000000000000000000000000000000000000baad800004acb00000000000000e0de0000000000000020224000000000c3b20000000000000000000000000002ab1f802a000000000805ac00000000209aa8271c421500000000060685087200001691500000000000003c9690000000006058c0000eab834138000000000000000000000031d4d10c96c1f770561a92700001ea9a00000000000000000000000000000000000002d800000b06eea9e2a07e8000000000004600003406100001c9e1000000000b0476283c00003c23e000038106000000000000000000000000000c76580387c054b83bd506206b6f504bc80e900000000000000000052347c957b7ca0c27d901c40000000000000000000000000000000905c00000000039cda0000382706083000f12753000000000000000000000000000000009089c0000000000000000000000000000000f0c0b4065000014105200d4000000000803d00001c15a075b301ba775a5ab62202a0000052be80000405d40000a06300000000026b1f000034207000000000000024aad8007c0000000000000d04a802b1000000000f030aa840000006b7bb7ee00000608ddc80a000000000000000000000000000c067c432f0000103a2000031c4ce229642cfb05d0000000000000000000000000000000060b50092f0000040135205449ae000000000000000000000000000a03e469b90000302e3c2750000000002caff3023400000000241ff00001e87bf247 else (if i<6 then 0x5daa4df0b00c86680075eaf07095dddbb000000000000000000000010026327a80000603500000e0c51c00800001414300000c2b70000000006219341cd0000000000000209d200000422d401d0000047346412c0000308c900000000000000000000000000000000000000000000090b240000d08aac33dd039000a1400aedc52b0498000000002c09c00000000000000000000001c33800002412700000000010440eb2d000000000a26874935821940000e25622af800000a8c1000000000e01ae6b1e000000000000011efb00003835100000000060d54000000acb80420000000005776c0000d098583a600000000000001e81f109500000000000000000000000103200000000034aa962003c00dc00165e0d0273c0000000000000000000000000000000000000000000000000000001c51101330364d7bcc5d5847a7a80dde0b7c418ea0bb80000000000000000000000b02dae8d610466410ff0c38ab21000028b25000000000107529effc0c1102a7f0362005000002427500002437e000000000000000000000000000000000000000000000800f8000000000000000000c360000015f2a0000000003000c00000000081500022dc0586754542f7d0eea42710a83c9d0ce7ea4000030c0f018010b85c84600000000050cc7c05e600a0022e8082881b0602b9c0deaa0e400000000000008038082b6005a5022000000000070bbc00000000000005089b02a8c090a5d94fae6b01f5f2a99018a6053b82bf4271a83a100000000010c7f4210804c0000000000000000000000000000000000000000000002814f7acf4000072eb000000000000002aac0000000000000000003003300000000000000000000000404a807be5e0767bf2c2ea400e8dc3277068c39cd01a400be0000102430000041f900000000000000000000000000000000432e00002c12b00000000040e380000000000000000000000000000000407640000000000000000000000000000000905740000708e40000000000000000000000370bac33f000000000000000000e70e7832000002c29947a9c000000002824fa0ef0000030cb7c19dba973dc980000000000000280b0624a40000e705e9f188003b0195000000000caee509907011eab69000000000b7ed800000024380b5806e48284a02300000000000000a087400000000081b500003015b7250b09c31232fc2d1826b7815f0000100bdf072f82ebe0a0cc023b0bf00000000000000000000000000016b6e925f2002dd23580000000000000000000000000010b2100000000000000000000000000040258000000000df1500000000000000000000002c0a640a98000012052c07c00001dd4b00001c1ed000000000e05e00000f25480000da2800000810381dd827874819b00000000000001026e0000002f else (if i<7 then 0xab9c00000000000002816240a200000000000000000000000000000000000038077d0e03825ba2c8e829ee05f00000b7118000092452c21302ed1c1a30000089d582741026000bb4000070593c1b647cac000000001834400002c9a400000000000001821800003e89e208440000000029f1300000000020ebdeb1d00000000080104c33a006500000d7bdee9fdc06f55e9600000000000000000000000000000000000000001804922bf502f6000000000f091c01e5000000000e0b04000080bb08190205360276aacb843226062dcb5ef21391d8f0733949fec0d28805d00003424c77abc000000000000092715096580de681820000000000000000008057b436f00003437c02582c1fcc7358880c4a26e6ab300003483837c84000000001e842a05cc000000000000000003c255809e3019a00000de38c0410c16d40447415300000000050cc1436300000000090a0800003aa4a9d72aad4a4286a25c3820b61a100000000000000601a00000708500000f76ddc17610aa70231b07a40000721e48191000015ccd00000000000002491582042a908000000000000000000000000202902bd497e0000000000000000000000143000201c000000000000000000000000000000000000815c0000342dd0000002e0000000000808058189527238209000020997000000000000000000e01932bbb20155cb2007c5c000047824000000000000000000000000000000000000c0e1000000000606ce2b9ba036ec38bb7164000090b980000a03ac000000000000000001403800000036a000000000000000000000000000ba85c41f4000030385d0714000077c5b8272000000000a08bec3670000303a4000000000000000000d03f7410c00000e9e790ea5e99650cca5d9a00000000000000000000000826de0110c1685049400000000280b900000000040a600000b089400006064c000080c9a4b05d028d080fda7fc0000b0edc6b84401c8011cf033fc078000012a15d77d428a200000000000001c27a0000089440000140820000000000000241b700001814b0000000000000000001052b035a00002c29600002034e00000eba8000020066000000000000000000f067b1d3d0000000000000000008ac950073a0c70000040960831de7c00c37b000000000000000000000000000000000000000000000000000000dab3002d8d0ef8c020c2791c1211085c00000000289530000000000000000000000080146076c000050488000000000000000000000000000000000000431b000000000000000000c0222c0f2000000000000000000000000000000000000000000000b7bdb40639aec80000000000000a00b2c308b0e18000000000000000000000000000000010d780000e0db183b6402834059209240000b075f89a5000000000f0e else 0xb7eb800000000000000000000002a2cc42dbe0a8d28c00000000001074c000000003858330427086d00000000000000000000001c0874a59d8291625bc000012018c20f000000000f0dd0000047aa000007a07702b400001ca91e0b545d9220da2007e000000000e00100000000018000000000000000014384000032bb60000009e3d032a4823000004b26d09e5c3347255482fa6053000000000000006252241dc3050041ca10db81e0a0000148440000340e7309bf42452046c40bf9a2c6eb960000000008ac9c0000000000000a25e8000000002c28100000000000000810780c298bb900001c9e7503ab8112e25534248e7888421af0acc03456a12400000000000000000000000000000000000000000000181be300080000000030925000000000700d12af2002280000e208beab2e08fc0000000000000e71596ba6000000000000028afe306700000f00ffc30900000000090e0c0000000024128809734144e0c780000000000000e093800000000000006040d496ee03c2eaf130aae096780eaa428fd0a5f4139f76d80000d071c0000d05140000c0e3543ab00003021c0000282c200000000000000000080144000000000c340000025f2500000000000000000000000000097750000040ba0000000000000000003414897067dd161aab142ca00000dc55000000000000000000e01fd82636058341ec40c440000f0d98000000000000000000c13c7a118000000000000000000025e408180000000000000d074800000000042e700002c0f800000000000000000000001030b0aef2c1328034800003aee80000709cc0000300ba426c000000000000000000000000000203b00000000000000475640000127ecdd9b000000000daaffc0980000141e030a6d8323e7062cbbe000000000000000000f27896b2000002c84bfa841838100000404e0000101ea00003011f00000000000778000000000000050e546b8870dac000000002c3a30000000000000000001233000)))))))
def orfd12 (i : Nat) : Nat := (if i<1 then 0x3ffd8748164fff69520593ffca548164fff61520593ffd7548164fff95520593ffda348164fff5cd20593ffd5348164fff60920593ffd5248164fff4c920593ffda148164fff60520593ffd7148164fff54520593ffd3148164fff48520593ffd8344164fff5cd10593ffd8244164fff5c910593ffd5244164fff14910593ffd3244164fff889105937fca564964dff65572592ffeaa54964dff6a552592ffda754964f7f29d52593dfe7754964dff64952593fed7254964bff68052593feca588964ffb5d6225937fd9588964fdf95622593fed5288964dff5d5905937fe5564164dff5c9905937fd5264164dff149905937fe2264164bffaa9805937fda960164f7f9dd805937fd9560164fdf955805937fd9260164ffb889805937fd9160164bffaa970592ffda85c164dff661705937fd955c164f7f5d570593f7e555c164dff64d70593dfd735c164dff64970593fee225c164dff64570593dfd715c164fbf61d60593efd7558164fbf95560593efd7358164fbf5c960593efd5258164fbf14960593efe2258164fbf5c560593efd3158164bffaa9505937fda954164bff6a1505937fd9854164bff69d50593dfe7754164dff65550593f7e5554164fef611505937fd9354164fbf58d505937fd9254164ffb889505937fd9154164fef50550593ff98054164ffe5c150592ffda74c164f7f9dd30593fee224c164ffe60130592ffeaa48164dff6a520592ffda848164dff66120592ffda748164dff65d20593dfe7748164bff695205937fd9548164fdf95520593fbd8448164bff68d205937fd9348164fbf58d205937fd9248164ffb54920593fee2248164dff64520593fbd4148164ffb48520593ff97048164ffe4c120592ffda744164dff65d10593dfe7744164bff68d105937fd9344164fbf58d10592ffda244164dff64910593fee2244164ffe48110593ff98780164ffe61600593ff97580164ffe95600593ff98380164ffe5ce00593ff95380164ffe60a00593ff97280164ffe54a00593ff85280164ffe4ca00593ffa2280164ffe60600593ff97180164ffe54600593ff93180164ffe486005927feaa65d649ffaa9925935fe77649649ff6a5525927fda914964bef69052593dee7788964dfb65622593f6e5588964dfb64a225927feaa64164d7f9dd9059377e5564164dfb889905927fda9601649ff6a570592efeaa58164f3f9dd605936fd9558164f9f95560593ebd8458164dbf64d60593eee2258164dbf64560593ebd4158164fbe601605927fda9541649ff6a530592efda64c1649ff6a5205927fda944164fbe581105937f99880164efea22005937f99780164f7e9de005937f99580164fde95600593fb98480164dfe64e00593ef96380164ff68ce005937f99280164ffa88a005937f99180164fee50600593ff21180164 else (if i<2 then 0x46900ee0d5007f1520638750e61aa00f20c81e2e40c34ef1c4354027c508f201d43886a803f8a118ee1c035401a40f1718c80778e0d6a80c3aee9e2d5210e401ce710d500c0a4061d774f1620a3839ce21aa017e2c41470729c0eb0d50080a475b2021a18020e73886a805052030ebba78a10e411c5050d500b1041c1dd74f1720c6038a09294a0de2ae811e7065d21ad0306f173677e23c633852bf9b252acb90bbb8a11e70980340dd1d5c3b36721c588f18ce16afe6ceaa0de2b52bb8479c261ad0306dd3c5cd9a988f18ce15e2ae811e70457f364a506f1423a017748338578abb846902705ca706dd3c5cd823ce0eafe6c94b90c32ee11e70886b40ca774f170ecd98688f18ce1694a0dba78a11e409c3048dd3c508d38608a9c435a060dba78b9b6319027c3ef800eef3dadbb08f576e9b7d1039dcf30ae4dfc7538a1f06cdfa3bcb3752ee0adb07b46b653ec52d7bfad63581ea68d3c3a543455e7f2ceff9b1b31ae59ac9eb90f31cbe31ac49b86cb077e09ac04f7f22fa5debabc677702e92dc9eb81b6d2ad52da46b2f3637ac17d7b2addf58b2abed4d8a87b4f029a6d29ea3a344b2848d0009ea33ada721cd949a2f32425ffcb9696472ac24fbc98e925f22ca406c7ae8e631afa31bc5c48a8f12da226c3bc86a70a9210ec196820b0221ffbbf7a7de6fa01efcbd7c79d6f191e02bb927652ea89d12b9a8726ae291c18b7be6ebedc29b50b6246b9ed521a6ab46c681aceb9998b2aa645ac6c1899b0c06086bf417aeaec25c9eb7216a5acba588eaf795baaae4551ea9114f2a9545186a1193eea7604dda99e92efa56249ca91f11faa36e461e8a4910fa1ac425e834102e9ff43f2a7c38f489e0a3af273c8e3a9bee36f66c20d4f99fa32d263b0c2897de2ec25bb8b2495e02ab25398a3993e2271a4bc893a9216234644e886d90721ffe3e587a08ee21cca37f06bf8d0c194630985d48b36157229b850789b012a2241845d885c10221f403c787120d3e19282f0856e0a1e1338232840607260cd0165829e046a07f80d9815e01d6025802f8000fffaa952593ffda754964fff68152593ffe5588964fffaa980593ffda760164fff69580593ffca560164fff5d580593ffe5560164fff68980593ffca260164fff5c980593ffd5260164fff14980593ffe2260164fff68580593ffd3160164fffaa970593ffda85c164fff69570593ffda35c164fff68970593ffd525c164fff68570593ffd315c164fff6a150593ffda754164fff61d50593ffd8554164fff68d50593ffd7354164fff68950593ffd7254164fff54950593ffd3254164fff88950593ffda154164fff5c550593ffd3154164fff48550593ffd724c164fff54930593ffc524c164fff88930593ffd814c164fff5c530593ffd214c164fffaa920593ffda848164fff69d2059 else (if i<3 then 0x9159025dc52cd82e01c0508e1aa01c0c953a06538759143446ba6710d500c02129aa6c8a1974ce02386a805033a06e8eae1d9b193119919c43540300857f365dc59323387142386a805dbfa066d54e534761c6450581434b06740dd0c5165d56a70eb2336a1a23ce21aa01e042bf9b3aad4d91432ef9c0470d500c2a6dfb1459d0336a3b0e81a82c0a1a6280205536450cba67011835402b40100a9ca774b2336a18234833886a806810afe6c94d536450c11aef9c2410d500daa6c8a197708d384821aa012afa520f552812ef9b016640470d500cd0374165d56a70ecda23ce21aa0176fe819b55394d1d87505811910d2c4113529036a9dd2c8a18234e21aa0181ed53ba591430469c03540245e0f340ca774f1623c813886a805e81ba3ab8766c648478c1919c2b40ca774b2336a1823483384833a06e8e2953874466cb911c5050d500d71529104775642372238a0b3686a80618aa2c83a055394d1d8750d834719b434dd00402a72909486c1b74f14238e28286a807252830830e50c3bee9e2a40c70730d500d10041872861dd74f14230e28286a80603254e8194ee987446e430d1c5050d500d4a4411ddc8618238e282cda1aa0164320d20e8154e534761d1c66d0d2f741070e0702372186c6238a0950d29211c01a035394ae98c31d8730d8338ac1605086823801c5d01295d31863b0e61b0660b027047006819b3ab8c31d8730d8330581321a801dfd022375736c618ec3986c1982c09a97ae8e2e80d4e539b30d8330581046b77f40cd9a9ca5c5c6186c1982c082363bee2e819b2538c30d8330581046b86823801c5d01a9ca574c618ec39df61b3660b028047006819b6538c61ce430581282377dc556740cd98ec3a1a6a58660b026c01a03919b0478c61cd4b0cc1604b77dc5d03366a729c610660b0208d70d400efe80d4e5387446e466d8c3058130ced032908f18c3977c19384434a4847003bfa035394b8b8c31d8730d83270f08ddf7174086929c618ec3986c193863bee2e80d4e52c360c11a70908ddf717406a72963b0e869064e163aee82cdaa24d901ce7011e34a12475b2240a1839ce023c6932fbab8c41d3be719b44664634a116d5aa475b2318a1839ce023c6963aee86478a5490c1ce7011e34add336320a921b3808d1a46e8eae419c38b436819b634957c49755a9c610e5df38a1b3648f1a66e82cf8b90670d4d0da066d8d29401015f4a71843977ce0c8cd923c698208ebba78a10e401ce700cc35402e5fcd9d5c81c871677ce21aa0152f8b39b4830378b903533be710d500c97c49cda418a7c5c81869df3886a806052034e96ff8a10e401ce710d500b1d774166d508720126c80e73886a806083e2e403a8730d5007901d5c81c8716778e21aa012eaf8ad4847900ea1cc35402641903c5c81a99de3886a80486de28 else (if i<4 then 0x6936fe819b1ab8c51d871914160540600c57d400a6a9c610e409770580b01cc8cd92321b1a81b1ba6419c191a066c6ae349d03740df0ecd83248ca9ce0c84698066819b190d4e30c761cc1604c0600b2184981b40cd9d5c618ec3982c0980c01aafb538c21cbbe716466c91d0d8d2edfa39a9d02c8cdb18a0b02a0300a198efe819b152949918c31d873058130043600e0665fcdb20722777573886a8050832fb0d20c0d904053bbab9b3521743540381997f36757209ddc8ce21aa0140cc82178832fb8a24e6ceae40e4352c34ef9c43540465f0dc19c81a980a77723366182e86a8068832fe6cd4c8314e413bb90c36710d500d064a921b40c1bc519e239d338b7f3686a8072522b20c33f8a158ee02e6c11c354031c551740aa7299d28ec3a86c1a82c0b36869c33a0d4378a36b523be703a8470d500c2a529b17409d28ec3a86c1a82c0b36869a33a5354b90c30ef9c66c11c35402c8641ac5d02a9ca674a3b0ea0b02cda1a688294d528350de2a70c10ea11c3540304a06740dd0a9c3b36366c888f38b161aa01c0ce8054e1c431b264c46ba58b9c43540344ab56c85d2c508f3886a804894afe6d431b2bb8479c1ab0d500bd0374c3b3632623ce0d586a8051aa2cdbfa066d4761d4360d62d0581434d1295fcdad5b20235dec54833886a806681ba552c366c6c99211a419c43540304a57f36b54c95dc23ce0c886a80599024dbfa030d62e6d54e534761d416050d3841dd2d5136c508ec84e18286a805e81ba553874466c9909c3050d500b9004075720715c81de1aa01320640e44eeeac710d500861a41903209ddd56a43486a8054821d480eab913bb8a11a411c435403240757209ddc88e21aa011208752038aeae40e4352c34ef1c43540343790023c81a99ddc86183486a805b5320c81904eee430d1c4354029d571720179c81dc3886a804b5212b0de28463b8710d500921b40c1b74f173688c32ce2a986a8062bea2a0c19204bb8af9b0541180b0d500d066d521b40c1bc5aa6235d33886a8060656aa0d1950de2d5211e70ba435403019d0374c3886cd8c988cd5ce21aa0196fe819b1ab4761d4360d416050d2d5fcd9060ca860a97708f383561aa018196819b51d8750d83505811ab0d2c40b5432a1bc5aa423ce17406a805864afe6d6aa0d1950de2d5211aee906710d500fb5632a1bc5aa57708d204e21aa01619464afe6d6ad52e430cbb8479c435403486b7ec516740cda29a3b0ea0b028698195aa83465436e9e2d5211e409c3050d500eb5432a1b74f16a908d386081aa0176a865a060de2d5211ae98c670a0cb40dd30ecd8d908cd5c63385680206e85490d9b1b264b8a11c419c4354038c5d0336ca706c0a238690436819b653814470d1f401d729c1bc55d02388338483254e8194ee9875919b03d11e714343540395ff152 else (if i<5 then 0x75d00d563a8ec398660a82c08d95d1c586a019046150eba0446c751d8730d4360cc1505812e86ac35277dc5d033661b0660832c082386966499c193bf6fe819b46c6ab0d4360cc150581046e2c3520042377dc516740cd98ec390660832c0a1a70476fe819b46d4761ce420c6ab0541604e2c34f0a82377f40cd83263a8ec388641982a0b023561a8124193bf6fb8b62e819b46c54c524320cc1505810470d483277edfd03368d8a98a58ea3b0e60a82c09c886a000846efb8ba031d8730c1960c9c434c324cb0c94908c570e5dfb7f4063a8ec3986a1b06355387161aa04a193bf6fb8b62e8054c52c350d8327011c34f2243208c3977edf716c5167402a62963a8ec38864193886a7a066d94e0511c358c390877dc536740cd92941982c0a238696e46819b353814470d630c325df72340cd9a9ca582c0a2386b186198bbb8ba0072d4e52c3447834409c2e90d630e325dfd00396a7297158688f064e21ac61aefb8ba0072d4e5311a0d102710d2ddf71740cd9a9ca58ec398207b020f68621a1a7847e2e80d4e52ba6418700f0367181434d08f74d033675729c830e01f38137027161a71920f092118eba035354e52ba31d4761c6430541604e2c35308f74717c516740cd9a94a720c380781b38c0a1a86819b0478703d8107aeac3493a81e08c75716c5167402a5295d18ea3b0e21a0660a82c0a1aa0462b5bfa066d1b51d873aa6430541604e2c34f0782b77edfd03368d98ea3b0e21a0660a82c09d586a3ba78ba066cd4e5303671810470d240c3381e77edfd03368d9a9aa72932182a0b0208cc97161a48261a83cefdbee2d8ba066d1b1529490d033054160411a410d4c2301c75d01a9aa7295d30e88f3660a82c08c886886884603bbf6fe8054a53874479b30541604644354041dfb7f40cda366a6a9ca582a0b0208cc8869207847ba78ba035394e418700f034349c32c5d02a9ca423a3b0e5de06869385846290722f5bfa035354e52c751d8719064b8b0d27110780d08c2e0e5dfb7dc5b1459d00a94a58ea3b0e21a064e21aa04a0f3bf6fb8b62e80d4d539490d03046904349c402301c390f2dfd01a9aa729c3a233221a219387b8b20e80d4d5394b0d4360c11c34404003bb8c977e41d01a9aa72971586a1b068e08280823cda1a8b8b20e80d4d5394b1d4761c4320d0d101000eef08e41d02a9ca68ec3a38cda1a721611bbee29b320ab3a015294b1d4761c4320d1c66d0d4641723400e423a3b0e6a638cda1a6198efb8b20e80d4d539490c830471c66d0d35df905c8d01a9aa72963a8ec3a38cda1a619cea8803ad90d4d0c1ce7011e34a0655fc610e5df38cd8d548ec8c6960cee9e2e4154d0d9c6806ce6d8d2d5f517c5c610eaa686409770580b1b4d9cd82a48c07c6a40cee99067064e819b1aa64634a2bf74c8338d0336354c8c else 0x1dfd033621b1863b0e2a582c08d8c6b0069b1a038b9b630c761cc16046ce35803374717c5d03360ab20c3807ce3023651a6bbf6fd91a026d1b2310c31d4761cc150581352c050d406013717406a46dca58ec3986c1867ce302b7cdfcda1a804600e80eae533a641873918338b9c6059b434f08c01f17406a46d4a720c3986c1b38c0a1a9d1eeae803a84633e41871b183671811bf9b434d4bc2315b409d28ec3a86c1a82c0b36869d568ce15baba04e8c751d8730d4360cc15058166d0d353108c01f17406a7299d320c398641b38c0b36869e11b91a00db948ce4961cc320cc11138166d0d3c23d02a9ca674a3b0e7210660a82c0b36869c33846e29b362ab3a015236a52c751d8710c834e8c15058166d0d542b723401d4239d28ec398641a82c0b36869a978cee4680d4d5394ce8c751d8730cc15058166d0d43c5d03364d9a9ca718c830e61b0680077684a33b8b62e80d4d5394b0d4360c118ee90434f08f74d0336c830ece04dc08c5868d9325ba01aaba64187671814346c992add34035529c830ece30286ac53257ba6819c60411c346c9928dd340c830e3233813702868d9b15611dbfa066d1b51d87505811b26a9910d3774d0320c3938868d932506484aefdbfa035354e52c350d8358a9c0470d3c0108dc5d018ec3986c19820cb025d21a680211bbfa066cc761cc360cc10658138b0d383208c)))))
def orfl12 : Packing := (246,3,7,11,4,15,0,orfd12)
def hashorfl12 (i : Nat) : Nat := (if i<1 then 0x140030000008004002000800400000000100000000010008004004000000000800a0000018000002000000801800000000000040080010010000000000000000000400500200000020000018000000003000000c00200700000100020020008000002000001000c000000001800000c00400000040020000008030006000000001000000200000040020030018000008000000000000000000300200020030000014004000000800000200000000040040000008000004001001000400000700100080000060000008002001000000000000100000380040000000000002000001000800800800000000040000008000002001000800000a0000000008000000002000800c0000010000002000002000c002009004000000400600600080000000008000000000000000400a00000000000000030018004008000000800000000100080000000000008014002001000000001e0000000000006005000800c00000100080080020040020014000000000000000a000000000000000100180080140010000010000000000802000400000000040020000000000004000000000800a0010000014006001000000800000300000000020000008000002000002800c0000000008000006000001000400400300000080020000000004004001000000000e00200000000040000000000000000000000000c000001000800000000080100040070000000004002003000000600200080000060010000000002001000000400000100000000020000010000004000000000c0000040008000000000000000000000200080000000000030014002002000800000000000200000000020010000000000000001c014001000000000000000000000020000000000000001001800400400200000000000010000004002000000000000c000000000800000400000080000000000008000001000000400000000080100000020008008002001000000800000000000000040010000004002000000000400000100100080020000028004000005001000000000600000000040030040000004000001800000000000000000060000000008000000000000400000500000040040010018018002002000000001000100180000000000010014000001000000c0120040010010002001000000c008000005800001400300200000020010008008000001000000400200400000080000000030004000000000000400200200480000020000000000002005002000000200000000040080000030000008001003800c004004000800000200400080000020030020000000000000000000a00200080100000000018004000001001000000400000000000020030008004000000004000800000300000000000000008008006000000000000000500000240000020008000006000 else (if i<2 then 0x800a0000007360000003059200000000000000000000066780af8c24fe0140972e7811a00000000000000000000000000000a0caa000000000000008068bc1877c18600000000000000000001ba9a9a8dace97c80dbb810120bbb204cb026a000000000000000000000000000000000000005d14f2050600000000000000000006eb3cc0ed35147000000000000004021d2acb4000000000000000000000000000000000000000000000001143300000a0615c065b018287439e102add69101f700000814d9405900000aa248cf6580000201f6000006f4c789e300000000000000342030000000000000000000490d600b680000380e40000060334000028aeb38373805a575840000048419000006138c0000003d800a86af2f6812318322c031e000000000000000000180798023a7839e6a255819280000484d5000000000000000821f000000000102d600000000000000000000000090153a4c97dd53fd1ea127af80102c2c3284f400000002d400000000072a5de110e5d0828110000012e26c00000000050b420000000000008600000412dc0000600de60262055800000754d700001241a28285954bf000004434800000b8a000000000000000000000018018000000000000c0000000010000000003000800c0000040000004000001000000c002000000000400800200000000160010048000000002000800000000500080040000060010000006000002005c00000b00080000000010018004000000000000c00200000100000000000008030002002001800400000f000000001600000380180060000008004000001000000c000000000000800e0050048004002000000000c002008000000400a0020020018002000000802400e000000000c01000a00000080000020028024000004000000400000200080100020030068008000005008000c012000000000000200900000100020000038004018001001800c0000040000004004000003000400000100680040040000010000000000000000000a00200180000040010060008004000000000000600600400100060000010004002000002000400a002000000c0000050000004004008001000000a0000000000000000000000000200000000000020000000000000001001800800601a000000000000100000000040010008000000002000000000c000000000400000700000200020010000004000000000000c0000020000000002000000000800200000300000020010000004002000000002400800100280040020010008000000003001800400800200080200040000010000002007000000000000000100140020010050000002000001800400400200000000020010008004008001001000000400f0008000000000000800401800000000180020000008018004000000800 else (if i<3 then 0x87a599802c00000293d1c04080000000004042aa09020000000003835e57892c099400000d294b07dbe165441b88000000000000000000000000000000000000040238402904040eaa496838400001d54971de30000040b4a000000000096109725c0000301bd0000000000000000000001e5000000000000000000000000810e00000400420000000000000000000574230edf800005d63b000000000040700000000000000000000000000000000000000000000a0ada000000000011fb7ac420000000004012300000000039e1ff04b920bfe00001c1aae004d00001c18700000000000000000000000000000400fba041c00000000000000000000000000000000000e6108e513931000008509900f07839b5a278000000000000000000000002480100000809116404000000000000000000000000000007210600cec000000000c2450a08e4000053905000000000328a2c546c42794000000000000000000000003406b2058a3286000c1a2a73000000000000000000000000f0896654fbe82200400000000000000000000000000e037d284a800006793200000000000000000000000000000000000001c0a87410b63afd000000000000000000000001a0607dd061860600000000000000604b400000148540000483d4d22c92019902144800340173d584d417ad002a30b2d413d50237139f140c90c4e0781208000000000a16a0000000000000000000000006049300000000000000000000000000003c976e009a000000000048050000000000a00ee018a0000000000000000000000000000040388000000000000000000000000000060a2800000000000000f01a8000000000000000000124b440000611f700000000000000282df0000000001004b800007006a000000000000008a1de000000000000000000000002205c8000000001a13c400007b935603dc4e44a42d5000000000100c64000038423000000000000004d377000002424800000000000000000024011000006a1ba140b4000018350904c40000000001527900000000000000000000000000000802d0000080770e4be400000000000000204f800004529b3732f753ba08e17d2b000000141a4c30100000ba8d694b2780358000000000000004ab70000000001a1595286d79319000000000000003020da085d40b9068916d2fd57912012000000253ea00001cf6460326d108cbaa4400000c2ec80000b704a210fceabb00000705ba0000000000399542bb0015900000000000000000000027280000f24b2854d881be8d509000000000000000000000000000000000185180000000000000058545228a00f271804af80b300000413f00000381f47007a0000000000000000000c0fac0000000002218200000031c680a10000000003c8b000000b00de4069042ea else (if i<4 then 0xc90097a020728100000000000000000000000000a0e98000000000ba42600000000000215c090fa0e2fc2e580000b0957e17ad1ee6813b60000021979e9d7d01df0000000000000000000003fc00002c2320000000000009dc80d60000000001417ca831c800000000000002020380000d07740000000000000000001211dc403d000000000000002414d000000000000003c40d303d240b0a000000000193ac0000000000000000000000000000080399bd920000084b3e032b0817a0000000000000000000000000e874000010034d244800000000000000e11264f96000000016c00b27e01e400000000000000000000000612d2a04b1d4128826e000009091fe10f8484a251197018a0000301b3610886a78ba0bcea87f80000000000000000000d11f00000000030a226809042c4e0000203186d27500000000016928800000000000000c145303120076c000000000000004284380b380000010ad8034c015d39cba1831eba0d00000000002d26b5a1940000280be0000000000000000000485e100000000000000000000000000001ddcc0820b00000f57dc00000000000000000011e0b8836e000000000000000000000000000000000000000000000001deac000000000000002418e0000090b999537c00006109040c0e00000000000000e09d80000381469510b3075c000036939000004aa9860ea8000031187d262c000000000112f800001c07a0000000000000000000101344063f77bb200003ca8c8000000000000000000081b1f0acc00000000000000000000000142c3b006d00000000008a4f951f9d095a0000240638000000001e190000000000000000000000000300a3021340000000000000000000a0e69ea64ed0c6aa01a000000000000000000000000000000000000002e5f8000000000000000000000000000000000e4ba528f900000309a600001418f8000092199955ac000000000e01b3204de00e100000000000000380e8e3968000000000169a1c01cc028d6000000000295733a9c0000031d0400000000000000000004bbcb0000000000000000000000008e4130b06183e7c28ce000020a1bc80c200001607cc000000000d779a000000000785e3000000000000002060300001a57af9dc28000000001804140000785db0000114fb4000000000e081a0000000000000000000000028270882da00000000000000181dd0000100e540000702d3f79640000000005138c0700800000000000000907ba0000000000000000000000000000181fb00000000000000000007acb6c4b7000000000000000000000000000000000000003c0f521195f7114450d00000302e12a46515764000000000ca30c0000000002000e7000c80fe4000000000000000000000000000030ab221428dd07704d7608d734790e9c03009 else (if i<5 then 0x93b9000000000180026135c7a3e000002297500000000000000000000000060976000000000000000000000000406780039000000000000000000070a9fa0738000000000b084c00000000073bcef062a6ee000000283d10000000000000013daf70a740000000000000000001a1165c0fa88513aa2aa247b081ca2560a00000000011efb282d66232e34b35ea9fa8562000000000000001d46800000c4c600000000000000000000000000000f0a800000101598900500000ee42400006063b00000a512a2a932043100000a01f000005107e2014800000000000000527d000000000000000000000000000000000000001b440800000000000001415a8000000000000000000000003846287abcef747c27fb115e00000d525c0aa80000020bf800000000008625f0237814e40000000000000000ff32ac800000974bc00000014c0000000000000016aa41b9c7000000000000000000000000000000000000005088e00000a979800000000000000000000000000000000240df784830000000000a8718000000001651b4000000000000012ebd00000000000000000000000045381407b7354c94088800000000000000000000000000000000181921d1100000000000409000000000000000000000000000000000028aabd02d42214800000000000000d25fa0000000005b9a1000000000140e300000b02ea000000000104e6506c60000342290013b000000000000000000000000000028a2600000a00ffa52900000080fe3a1ea00000000000000000000000000000000040cc6000038107b8124000000000242af00000923aa000000000000000000154d362b0a113c8dac39b42af08c57803fa065ee09b80000651f500001e080c0000182210000000000000000000000000000068a4a81faf720d214dc00000000000000000000000580eb701239558c0000000003a752000000000005380000000003c33200000000006e100000000000e76100000242cf039df00001c4274000048532000000000169fd00000000000000000080000000000a0f5c00000000000001815a0000000000000006048600c1f10849771000001691b40305000010149ec1cba04c8000000000000004007200000000000000000000000000001081d78591000000000000000000000001208ce8aaf10346000000e1b3e8d70000000000000025ef5105d8000018442182023100ec285b740604304000007030cae4c0000000000407c68f02fc84360237004446efed826780000000000146aa9cc00000000012185782550000000001e0d20000000000aa524000000000000000000060baa884b791cc00000604744a2d38285a777a000000000000000000000003c0aa8000000000e42c40000239410000000003c0dec9555000010013c00007942e028 else (if i<6 then 0xa03000001203c00000000000000b7bb8000000000404f30000000000000018a3dc0bfc0000000002817d0000000002ea4c8000000000000000000000c4b0a020000000000bbc9aa0a9413e3015b8000000000000000000000000000080c1c00000000000000000000000103a552b9a000000000605e080a0b05050c0b7000005a4f6416e400000d255000002122de8f8ad1da4238a000031d94181b2c7608000030a9fa108b427cf6121182bf5864e1a79a00000000000000b291b4143c9e21ad0e250aaf408070193abc6050abfa0d440000000003a03b1444a017d6020700000000000000000000000000000000000000d08032f7c3cb14c042f000000000108ebc037600000ee689c0cce062f4ab0f601d9415e7bbbe00000f565a02968000030adc4166c000000000500100000280573ba4eb001e00000825eb00c3000000000000000000000001a099800004d6648a58600000000019159000001487c0000000000000000000000068410000000000000000000000000000014283000004a2a600002c19bd80412727421070000000000faa3d444a40000000000000000000000025476021eea17472aefe956a209636e1a381f4604b6104aab4e5e80ba038e74011a0000000000000000000e088042529816800001a458c00000000000000000000000080c6a0c88af10a68bc5109fe0bb960211c1c38000000001a46e0de64985b2e75a60000000004863c0000000000000000000000003433c00000000000000247d40000784020000000000000073939da5d800e8901c19b8f0aa833e0728c027200c1609d40000342aee831600000000020aec9037c00818eec06c109806627722260bf0000070504802c000000000000000609180053bca29f044d82216544818076a02bd72497cf104000070617703fac066c0000000000000000000000000000627ca80eb36960d14369a7d774326c006800003087604f492ae3d83610000184a0c1e9180000000000000300e38000000000211d8c143d04465a94d4ea7b400c98408ba9c4954738134d80bbc02ef555b280558000000000000011c51800005a80c000000002990ac0000000003c1f62850900000000000000000000000000000000000000fac1800000000060c8252a5000002c8b100245000000000000000000067cc8c08450253e02d9528b260f880000211860000000003c1b6a047200000000035c8c00000000000000000003001c00000213db40530847aa0490c13080000153e500000000035e5c43bd3f2629c0baf81fb5858b40392000000000783b2000000000000000000000000000009dcbe8071805ce0000300b80baf76a9500000203228000027a3b6e8600000000000000000003019e0000000000000000000280540000000001df2d800003211a000000000000004063400 else (if i<7 then 0x2540000000002028f8000000000000000000000000000000000000000000000000000000000000050b9c615a76b0be83e40000000001484d8000000000000000000611f100000205fcdd280000000000402dedef2a026c00001eef4800000000067bde0000000000000000000412eb485000000000000000000004860d00000000009c86304940000000000000013c1d0000000000498d0000007b6444a0800000000000000000000000180470000000000a9f7000000000000000000000000ba55cc17d40000606051abc0819748094983770000184e6180cbf129a00000000020290a03cd2a63ec191b81d49064f00001c014000005011eda8c20000000000000000001410e581acd051d5791c2157000007061f305100430800006d2fa00001c0a184993f93d08002e21114000050069aa202000000000000000000000003819ab00e7000000000000000000082ba200000000000000000012183c00000000000000000010a9980000000000000080d4c849200001e0459c1028000000ba9e0279c12200000b0c166442841080000017baa00000000000000000016125c000000000e086864f5800002016d00001200c800002823b70aa6000000000000000000000003013c000000000144b78000000000000000000102b5800000000000000000000000902af0004800000000000000000001c590000000001957a400000000000001451c800000000040c330ee04000000000000000000208bd00000821d40000000005039960932000000000012910000000149c2b3e0601c058800000000013b0d87a94e4d1c000000000e74020000248488000000000000000000000000000000000407d000008021c0000000000000000001ae4cc000000000474a6000020265b82ff00001f43780000000007239e407c4000000000970b6000000000205330062e00003a89b8000020063ef1b00000001cd0000000000000008118a065800000000000293920e800000000000000000000000200c4b542f000000000342b1bba2900000000000000000009271cef29d68d21121cd0b800000201e0b93593211c0152f0af600000f27c600000000001076c058de4b800000000008042ee434c0000502280000000002288e000000000000000000010326109bc000021ca5702c2000000000202104034ff0857e51d00000000000000000003009ec83dcf08e0000000000384e80000000000000000560ba7ac1441c00000000000000000000000000009052b20bba88c400000507dc00000000018364f705600000000000000928af01247de5500000fab260000000007b822000000000000000000000001a0394000048301ca9ac0043000000000000000000000000000000000000001de56800003a5d60000000005053d10bbe20c83419f0000000000000038 else (if i<8 then 0x3032c000014144b10a6aab6d406a800000000000000000000000000000000000000000033845505d8000000000000000000000000000000000000007528b0aed1bbb040057e0d4800000000000000000034ab0f0524300fd214d08098000000000160220c17800000000000000302fd00000000000000102e9d84ac00000000000000000002013600002c260b82ed00001e08aa8af7e85f19006c0000000000000027657cef8d42e4183ea0000000000000013d5d000000000000002d10f4713c000000000000000000000001021978612d25b4845a9c17c0000050bca000000000238524ab28000000000600d8302e7b513b4016d847c000016072fca2e2001fa04f8353700000000000052884ebb81c28000000000000031e5f78358b0522645e0000038546401c800001432880000e28780000100bcb065a0000000000000000000000016f97c41a748523c00b7e161000000000000000000038889282abb215200002480ed3a030000041664c9400000000000450e48b04183ff6760a000000000702615021b013758214800000000140b3c0000084f90000000000000000000ba2468e1680286000000000000001a9f48865bd0c740000000002517da024c000015cce8000000000000019c1d506110000000002c197000008077800002c1465381700001a55b50170000009727d7478a011258454e77b0000000000083f470a9200000000000000e734744261026f80000aa1cc000000000683800000181358029d9936100001245b801b290184c05cc0000000007939c00001e4b4c000000000f0bd00000000000000032c6be13c982724d589000010f73c00000000000000000000000493b40000000003ca24f824d0000000000c266e393b007ee00000000000000c07c0b41490b150000020597a0bec00000000082602805d800007052aa7054a0ad00000390aef0964000000000000008a4fa40fa7c0ce40256d07cc00000000000000002858495169b7000000000000000000045439000000000000000000000000000000000000000068000000000000000000000000000000000000000000000000000000000000000006df8125e00706174000004143fd06620f781825058212e758ef4c1500c05bcbc0000000000c32c0000000000246644864800000000000000e9e000000da7d1e487bc2dab3bdf00000445f400007038ef7448e0a8000007bb12a2cb2816e8000000000000000000000003065ce26fb8ebeb81e848463e056400000000000000d059400003011e800000000020ebc0000082700000000000000000000000000000000001814fd7ba44131a43158000060664000000000305f300001402519c1fe832a80836213020184800000293200000000030015e75220000000001024a0000000000000000000225efa10c000006 else (if i<9 then 0xf8059c000078193a27a80000181968000050026000000000000000000160e08000073db55007c00003c1dd800000000000259c10d800000000000000000000000000000000000000000000000046380000000000000000000000000000000000000000006955d7aa87058479d12800009a2a400003030000000d07e780f7941b38000000001e4a076888802dbf0cc114f0f02df8840900000000018168800000000000002008a000006a23a40c2ec26c00000000000000000000385d0000000000000b000000000000000000003999000000000000001145f50572000000000480ea0000000ac00000284a800000000000000000007053bc0473c043b05f47019d246315c9f8824b000000000000000000000000411cc00000000070b100000000006b823b792a00003dcf5d80a8ba8c8806ccc2ed484ee60bac00000412b8bafb00000000000000393fa0000000000826380000000000000000000046c0083e00000000000000000014582c000000000000000000001ba00000000000000000000000000001845d6c12800000b0b38743ac000000000006c160d7cc1d3800000000000003808980000c00f7403e680bdc01d002327417bd9c1700000226f0042c1e9d953cab32883001440000115d5a0b4e00000c09a252ce30479415599c94000000000020ba6022d283a1000000000000006062c375d00000042ad800006a42c14ae4000060342724c300ca1c211000000000000002ea9380000725100000000005bd9700001400f000006100400001203700000000000000000001dc868000000000055c4c298dd54e000000000281c8800009022e00000000000000307400000000005907fb0c820000000000000000000000000000385ed3261a0000000005050300000af030697300000a26ff659900000081ed0000000000000000000000000000000006052f00000003e00000300639a8cece4d8000000000004100000142328000012724000000000000001032a015e2882d800000000080ce000000000000001b4400a97d80000a090d2e3a30b0490027128b0e4e5c007af0081aa9e1a00bc00004209300000615dc00005121d00001a03ba1d2a8917c5216c2189000000000000001254d109f6800000000000000000000000000002ea8b00a82142a00000000000000000000000021882c07e00000000000000000000000010601d59740000000007789000000022a8000000000000000000304cc500d064613c07bdbba900000000000000702710000000000dd058000000000410600000000004a61c7586400000000000001d473eeb0a800008a7aba55521c7cdd144e2175e042bc024b0223000000000000000000080199eec7f49f2000007080b20a3c000013bfa0000000000000000000603c400002422b8000010c4c00000000050057 else (if i<10 then 0xb800000000000000000021c78b03cf00001ee958c0695046600000000000000195527078e811ec9e190000000000000034186f944297048000000000000000000000000000000000b73dee0d040000000000000000003c2fb800000000000003002208159906680000141f8000000000000001401d2145500000000019d54000000000000003c18d80000b2ace00003815280000d0a360000189cd1d127b0b2e00ed400004025d305218113380a4905ea5793b402140000000000000000000000000000b013800000ca2b0850280944000000aad213c100000000000000104eb0000080164c2160000000000000006a740000000000000008a9b80000d71f52f2a400000000000000000011d83800000000000000000000000520a400000000033e600000000003aa570000000000000004242a001a0000000002c86ae007790c7da00994079f11c46abd000002e9ea0000030948000000af50012cb2845d43b54251a84d9aa645009080000000000000000003c8cc0000000001b4d8c0000000000000000000000000000000008e3d800000000022ae80000000000000000000818580000000000000000000000000000000000000000004960d602b0415e5680ce0378508fc4019c0000305ae000006e9cd482d00000203880000000000000040a5800000000000000906920130c00002829b0a93c000034129c8136000014e4f52949d004800000a4862807453cc7e032580d6e42802d03800001a08021ce3000001217000003a990085170000144dd7c1578000000000000000000000009037e0000302cd481a8e791ea015b02980000000001aea8c00000000000000000000000613838735600002c0eb80000000000000000000000062a58000000000000000000000000000000000000000000040360000092b9e00000000050279d025c04361286bb816af741a000000000412865a622000000000000000000000000000000000027640000000000000000000a1228000079341008a0000020209282a900000612ff0a98510b4d091b412bc022ea833af72264070028a800000000006ef2081148009900000555140000193c400001a0dac81747801400000000000000000001780c00000000000000cacb200000000000000000004e11b00651bbd90000014dc8000000000f003c000000000000008a948257800000000000000000000000000000000012139c00003049c00bae0000340320000070124ee9480000400cda0bcc0000000000000000000000000000205bb0000000003804f80000000010163a80a30000000000000015cee800005006e000000000000008a1dda4be80000000001037000002ca949546e30a500089c81c0800000000000000000000000703a400000000035121e2ba440a5800000000000000ee4512a7500000709e else (if i<11 then 0x33800000000000000280b800009239da0194000000000fa1d300b78000000000000000000202baf062300000000000000000000230a745e800002b915f7bc880d1c00000049e00000000019d7fbbb2ce218ff024c000000234800960000000007860e00590c0f154069b11a6000000000000466032340297842bc00000000000000000000000201bc0000161346eb069838fb288b0472c820e800008751c0597c00001513b000000000000000000000000000039ea220515000c400000000000000e262e603200000050120000020bc881c510161622fe00002412cc80a7000000000029878d5b2000014e779413aa024c120bb611f4000048d0b40689007b3c84380000c07266f0fbe94653d320000000000681e0000032222a0aa9ddc1f8411f06424519b4135b952d1245200000000000000c216e00aa10095e93bf0072c000000000201c5c722c2529f410c0000092320000000000000000000000002eb07fba57c70ac0000000003833900000000019ccf912fbd05b894de809c2201adc061de10f4000058164000000000000006d4eddac1600000000053c5e10012011e400000000000000a09c889f36054200000000000000000002011e0428c0000000000000000001094380000708740000000001046a00001202740000580a570438000000000000000abcf64d08416b80000109300000201050103600000000000000000005003a00000000000000000000000029468000000001214ae488c102c50000000002c0120944d425b18e5b000000000000000c0424000000000008912120800002926240cc20000288bb0000000000000025ecc6537f000000000200f1800002704c000000000000000000000002032babb2520b89657c40000000002011200000000000000d079820d88000000000b22e20000000000000000000000022886000000000060b0000000000060b05af63c00000000000000000000000000006035ea098200b880000a24ff614b80000113c34aca600001020bc85f900001818a40000286421000200000c16a882d07778e0000000002bb09000000000000000000032aac00002ddee9028e00001c0ad4000000000b72eaa0528822b30375428c4000026b303829e10042000000000000000000040a7000000000000001c0bdc80c880000ba47c0000000003817eb0310000000000000003088800000000003d9900000000000000686340000000000c884d85710000000003405f8000000001216cc00000000000000000000000000003200600001a8930000000000af7880000503a40000000000000000000a0935c01c00000653ec00000812c042680000000000000000000111bc000000000181276002900000a13a4000010618000000000000001117e3023f20ecfc28700000000016e50bc0e78000070192eeb else (if i<12 then 0x5ded0571943939e5bad2ca57bd6a0b89e944e557750b8e00d5100e0990c56043574a750056e10be80a7ca0d5c000040496825bac4d0342c08061e000000000000000000000001756232a9180000f0a7e0000000000000000001b4434000040572000014117c0000000000000000000c2a93002390608000000000438570086a04fc4000000000306fc0000000000000000001000944315000000000000003c2fb000000000000000000060083627b200000000000000d017c000000000000000000000000000078284000019445c000000000601fa0000302b080000eacc2358480000205a30000134fbca8f1a839d00000ee02780a0800005087800000000000000000000000000006854880af4000000000000003743d7566801887d14b9096600002e823b3bdb70b442070e485f80000000018469d496d800000000000000000000000d0bd2000000000482b10000000000000000000000002067f809c000002a49a0000000003bc33207100000341c6e381340461ce09c00002860400001a04880000000000000000000000000000404fc00000000000000008174155000000000000001e54ac0000000000000000002422480000000008096ec16480000000000000042ac78198528dc8063880eaed0a87036d8010c0000750fcfa256000032b08800000000140186cb2b00000000004054c00006537342294c0c20030d5022cc034160f0ce927e015deab4520a5c423ae04ae40c9320a7f815180413700500000000000000000001a08c80000100f6a0154c1435802a80000207f77530b8008980f0e01a20000342f75902b00000000000000753cc000000000000000000050145c0feb406d00000000000000180da285501024e000000000193284702800002c3199116c803fe0000381e980000d03200000000000000000000ce6b3c24da93d50000000003011f8000000000000000000252c46033c00000000000000227600000040ab50078000014136800000000000001c46fc000018637b7cc2c556000000000000000057c000000000000001ee864a9a05d51f0025000000405d0917b0000121464000000000b74fc00000006a80000b0a200000000000d3f0471e7801d3c9f70000000001e0162885e381d420288b528000001d616225afeebf80000101ba00001e114c018e8000ab74cc414a59cf6800000000000000000000000000000000000000000000000000000000181b50000100118000063e59e040c94b180000000af62112003c4000003b7d000004eaa5c8dd0000000000000000000000007a4ee0000302509059d304e8000000000783030000000001a9610000000000000000000782ad103140000000ecdd521906234163c0000405fb00001c18da82b6000007079dc1480c2e4800003041200000000000000908b1b547441 else (if i<13 then 0x794412410859800002036000002494f00000000000000300dd800000000000000000079179701cc14559422e0000000000000014210e827bd27d8f41278097b91d300000208ac000040225d06ad2f616c9ccf02a46abbdc04f28292d9660905458ef4168514b8c4aa5c400000029e7d5c200000000000000781fcea4a044635c96fd82a70000120e7c0000615530000000001415d000006202e8f751827d0000000000811c7c045681ab1208a84f32807d8000030ab4000000000000000000000000000033dce102080000000000000000000000000000486090000121953c0c3d86133a9260000000000000000000000000000000000000000001c1fc000000000000000000000000000000000000007d0ce520e0a0ad800000000050c62a05352a39bbc080000000000000040299007c200001c1ed000002a70800000431e80000a011c4017a00ce80000e23b2000011c7a0000000000c40a8c25c3131200000000019cca054e5f71b8e41c7a9cb00000602f000000000000000000000000241a6ab9fb000000000000002842d979980000000000000000000000034827000000000160972c24a8917237258000000000000000000000002c0ae18045205de00000000000000476f3c116c80d14b9e8000000000348eb0858c00001aea3c000000000000006eeca48de80000a086ec151000006857000001e0ab86a7d804d29262b64f0342d6dba3000000000000000502acea684000030aa01918b000000000000006d14600000af6380000000000000000002c00d8d14362a54000019e9d0000000000607600000000000000000000000043bcc909fbc06b8000048469000000000300060000000001a00028076401f0000012109c000000000b2abe015db5eb4e3c0ae72ef80efc8077d880800000e1535420ad8621c76fe000038166600b8000004174b4819483ef4a12e81708000000000000000000000005854120b6e0000000000d32f0000000000000000000c777e0000000000000000000c08980000000000000180b1e6a73984c900000000000000000000000154b2c01294141500001a0374c2b9f83e560afba057c000003bf950ca6000000000000000000000002e89f8000050b6d217e05cfbb12e1b07600000000007110c209e00000000001827fb0a98740586a92751705017800d7000000000000000000000000581330000000000409d0000000000c51d602c6a004c00000c1277819ee03250000000001c29115290000000000000000000000001d553f81e5e03c800000000032b2580000000000000108e68000000000000000000000000000015254000000000000000000000000000000001a0569490d2011a60bfa00003686d80000ca03e000000000151250000000000000000000e2a5e0000142278000000001e4a16030808 else (if i<14 then 0x1d5e60000000003c096d564a00001a0684000000000000014162781d6c84ca40c9974349c09a80000000000000203218bc2d000000000000003388d0000000000000002125000000172a69a08000000001402085de5506225079200000000000318405fc6432c00001bd1e2205c000000000000000000000000698dc10b9d28080119f80eb4501c042c4446260a2edd04322250e40d2894e3bb1da00a6e074c41b43800b60c5a8f222ddf000000000012413d81e2480e9109da00000000000000126a60000000003d29500000000000000000000000000001c8af80000b03de00001c05b000004047524760c886c0194607b22258800000000000000e10cc00000000020772000015ee833a283a4f000000413180000000000000000000000000001ae37c0000000000000160464000000000408c3e017d0317306594749e000034aa8d80d000000e00c0000000000a06e420944000000000a08a38020000003041ea23500000088550000000000000000000000009abba0000000000000000000000000000000009067e00000000030151403e40000000000000070163b595a1e9100000521800000301c9500f4f2096000039d8f3131f1a2ec0053081a18000040b71c024dc2a5183308028a6138000000000000000000000000505c1000000000000000bc4400000000039c9e791c90000000000000000000000000000000000000000001d44780000000006a70600002408580000000003446c000000000000000000008b7dbad0571c1d43b2c9c2800000000000000c181003f2000018edd400006844eb077d60d4ec09cfd029a2c6d4f54c0b10f82810ab375462409da990b50000084295486400000b0373a0830000000000000000000000002d423aa782000000000000000000000003a95698329a0c3600001c8c7c919400000000015eef0000000001054680000000005045f23428000000000d02cb2ebd800001b85027548000020187800002021e0000001850044a00001a0633013980000b77b8147bc000000000903c94179e49c5c03d600000a197cc9d480000b0b8a0000000003bc9f000002f784000000000000006129800000000000000743fbc2c180000105f200ea05c4e80000000000000000000000000000445a4000000000000000000000000000082862000000000000000000140eac5c9780000aa7c82e30ec2628000000000a5254084f4d63c00001a4fd4096c8000000001247ae5d33e5511526fd80d292a04a804a303ce00000811f611b700000000000000506500000000000000000000c2ac92022c000055154fac34000011ee9f8219f7211c0d6a5c0a80000000000000182d25016600001af228000000000000004e2700000183a372381416ac000000000000000000000000000000000000000000752302 else (if i<15 then 0x5dd551816bda66400000000000000304860000082378000000000000000000502f400001b49a400004d61b000000000282d30000000000000000000284db0000004265c2778000000000e18a102c06d44b000008e0780000100200000080420000078075000014118000003037feaa8c00002c0f08d60e701c2000000000000000000000003c14100000904920000241a6000000000000002a8140812afa7ce0000281404864700000e11ff80370000000001c035c00000000000912246e588668000000001406960a240000000000000014aea00000000004110b5cc9a05269a559c069d40aa000000000000000000000000000000000000006baef72b9c00003e829c82d8402b7c099140b4b1559000000000000000000000001c105001e3201024043c40e300000783fed0bd80000281eab39ec20953b48ab09e6a02c100000eeb46c0edd5151000004189c000075549000000000000000000000000a263d430a085a90000000000000000000c05ec000000000000000000000001c1c30946cf05c6a15ee9e4d93b847066c2192c000073d8600000000028a1a80000521a2e0dbc5de8904c400000813ec00006bd8db2104000024ab400000008352038c000000000f069600000000000000000000000000002baf90000000001c2f200000024980000000006b929304f5747e00000000000000000000dc7d80000000000000142cfd392d00000a08dac2d831388407ea0000000000166100000000000000004160000000000000043bcfa2847c50f5090ce05a0baadde15f3428913a0a00001ae27c000000000e045bc16bc82e35d14c00000000009ef1800000000104f2748363824f000000000000000000080a0f0ea7000000027d728d000000a8244837ba04da14786c030493e900000000022981291ef00000000000000752f1000000000201b480000d017be12f140af00000e77f820b9400002138d000006429ec2e1cd24e40848a165381da08002903476e42c0000000000000000000c1effbcac909fca54c49e521043600001149d00000105f00000044f4c00007141e00000c0c4dc1bc8000000000000024220cd1fc00000000039cf4c02cd00000000000000154b800000000000000183fd000000000000000000070a2200002885e80000906e134b202941800006099c0000000000000000001804560319653210000024f680000282bb0000000003c11a800002a29c00001a97c80000000000000000000000010a6a000000000000009051680e7000006805c308bc00000800c00000c0aa2a02d000005ba07000000000000000000000000000000000605bc00000000000ab9690460000000003c0ee00000f2cae000021eedc900b77a7e0000000000000072c14015fc0000000009088000000000005225000000000000000000000000 else 0x305cf0000000000c135405bd404812ef841d7c5836a0000000000000000000306ba00000000003bda0000000000000000000000000000342d8f8112107e2000000000000000000000000000000000e201ee1643807f800000000160db000002543a2a199405c80000000000000000000000000000000000000000000123000000c57400000000000000000000000000000d076e805bc0000285be000000000000000bd29025a80000000000056f575d2000000000203bd000000000000000000000000000001e48e52140000000002c28f011ed00000e49bc00000000000000c080a5d96eba042244a000000000694200000081996c0b1800003a3c0a0f080000351f70000000003400380000027b0000019c850000000000000000000201e9000000000000006d376077c4000035f2b2025fb284e4103f031a9854ed2886e565980c5b5395705fa00002de078bcc800000000000000184be00001617370306302f1e2c5e0000000000000000000000000000000000a022a091f43294bb2777435808ba80fcad3c4da8f0e0afc00000000000000000000000612d000000c46f8000000000000016e3a8000050033475c6611e00000080f200000000000000000000000000003c0a18000000000812d58803552c5c0158050c8000018555c71e400000000000000721b200003801700000000000000000002108f00000000000000000001aa400000201c49050800000000011eac8000000000b49c58aef339f5000008596d48062104d0000144bd8000000000604b40000000000000000a38c138b1c993517c000000000008dde826f502a400001a97290106902c40000180f5a11d45078000000ca318040300000617880000481de50720812388aebe942c00001e1661e9be3821402700000000000000000000000000000000000000000000000000000000000000000000538e1000000000000007042510c1400000000030276000012e80800007046d50524400b20a1c00000528a800001281888516921a8000000000000000a176000000000190357031b00cac00003005d00000000000000000005027ec07e00000000000000004f0840a39020e3a569455b3c16199161f0a8fc01ab81530000052ba7e0ec400000000010181608c)))))))))))))))
def orfd13 (i : Nat) : Nat := 0x1746ac8271409b322348ba314b2d59032152869c5026d1a65d24138a03226ca9434692a9ba4827140644d90d1a4aa50d408371446749c4d83480592681746ac3a6cc811b16701a4031aa32435020d74e2cd952239c06900d204a60d74e2cd846209c06900b54d025374873226c8611ce0348061043886a041ae9c5900e105360d201a5f14c601c59641de70c59b08e34cba35640c89c31681368d24be298c03990863bce26c238d2ee9c5904e10d409b46905f9b0a48206e2c80ef380d2016412071640771c0690080d5020d74e2cd847189c27255d9b074b662c547b4dc980a8742c700ac10b146158007ff5c964ffea92c9ffc52593ffc44b27ff60164ffeb82c9ffd50593ffa60b27ff48164ffe882c97fd97593bfceeb25ff64964ff7112c97fd90593dfac0b27fe80164
def orfl13 : Packing := (17,2,7,8,4,11,0,orfd13)
def hashorfl13 (i : Nat) : Nat := (if i<1 then 0xb48cda8e3016b439c0003dc508308c27340ac00002a7c0190000000035d67e8310a3d8919488cc26e815000002908000000000000000000000000c05c000000000002ca640002c16c000000000000000300c0000200f000001c6c00000001c15a81e40000000100b4000000000000000383ae4228000142540001037029a6a9701ebde9e400001f3b805400029e54decb81c883cddd5600fcdcea001b0b78000083a2e9440000000000015d6301601d4e495e42941df28b389dbc9d682b6680bac3b25fcfc1ebddc088c303c402fbc203c19ee98440c48130400f5daedd50428a2968dcdae948ab2502840000000168d00001a95800021efa1db3015e4ad1082b09be49c1eb780002825803964209c99c69779527034000034a70482c5d6ec0400003c80489a28a600003de5a01f40001d56c000000000000c261c8f80001df711d1c00020d26880800000000000143bf29e800034038000000000000000008300000000001880001df196886010c000000000000000180821cdc000141200002412c0000c11a5e200003812bc965427acabcc3000000000101f2c2b40ad65d470316033f8354430fde15886e0850091400014225038c0002c2d400010126c0494183a8e4000281700000000000004a8780040000000000000000027c000000004a69def4000003939e7c000000000000000341c001a989dc0000c13c000000000002021c000000031cf00000c366cb2ba8d8c350000000000000000000000003c3c8000188f48a42dd2000006ab40002c1b3ca47a90f05271dd8000000000000000000000000ca5741d94bb65d151d1ac1c400020a32987ecbcd490d907e01b7c35ee9c24ab400000000000000014acb8d6d490bca1ba9a942369d279c700002dc7682a4000000011cd400000000000129c80000000269b45df9c0cac3111c646b500a1c00000b2c00000000e8df42dd0968000002e9c962a5268af9017982e741bdc09500a0c96cc19643abc2e089388060000000008346aa0b40500003493c0905c2c7002f4087c010000000020a5b41bbc3808100000202f40003c8c4000000009c8880e0d030824c0001607c000000039d2dc20c000000000000000000000000000000000002801c0700c050001c000000080306004000050000000401000010501e00001008040080001c07010030000200c0100400004070840001001028080040601c130140c0000300000004000040202000000010140000011000000000001c0000c040000002001000000200000c000480700c010081b0081004805004000181400c0000805004010000400803018010040d00400000020000800001000090000000c00004030040200000004050080100400004000300000001008010000e00c0000400004040000200c00004090000100403004000040100c03 else 0x3a8628031c11c0001a8f0000000000000cbb3eaa40000000000000000000000000001802388da9c2442140001491c000000000001431c00000003e88dc388c2ec49d80000000000000000000000000002299ba9fc80140003ddf4000289440003eb46818d6a5c000000000000000281cc5f4cc870c2a11ee0c09e9cee0af482ac0875c274000000000002cb1aaae00003a8fcc09b80580002cb4d89f81f1c0002c02803300003c0fa417c000000000003083e485c0000c8dc0002c02400000000000000d0000000000000c1a08044c22000000000000000000000000142a80000000000022ab8c218000302c80002487c00000003c090000000000000c03c00000000836a0aba8b70000000000000000000021f780000000382b9c2b0000381980000000300a4000202ff0b9c0000000000030376c212014c00021eae9d8400012a5000000000a9880aa7c2451dc543a70a21a964000082380001680c0000000000008a058935c1dc000042cf434b9f31c280000000021de501d0414280ce9d881ede037f40340003c34fc324000381d6888949f5aafc00036a31c337856f48a5807840b0c3c00000800969008b1c000202d9ea0f02bf007400000003c8bc000081fdc08c4ba0000000000000000081ec41104a7f5eb0000000031c8c00036a240003425c0000000000019cc240da8204000000028065a87c0000000000009e640000000000000000000000026874000000035de80000abcc000000036b4dc06a80a9804e43840003e9ef4174000103598ae21c28000000015c2c0003c2400000836cc3b643211db9dd5f28ccdc1a03badcf80003c23c0001422d826b9c1d039b69400000000042c3813bc0eb00d40001183000036a54000389b94a9d40e7ab94000380dc000388b00003ca6ddeedc0f6c2991f59882580bc489f007001fb88a1029d837800020328000002484aa84116c267006d0a776b0b89e7800041e0000109110291c088000000038b3f0250c1040000000301865eab6033433800000000000000005e60000049c588c800028108000000000000000000000000a846de19e85400000000000000000003a9e00000aa58000202f000000000828c0000000000014318c0ec000241ae43631e1f43069cf44155c2d00003c14400000002407c0000000000018165c3d5c137432d2ad4282c0000c9e982324a80000081a4e8108ac40003498c00000000000000000000eb30000000019f27a82003d2683bc14)
def orfd14 (i : Nat) : Nat := 0x3a62901c201b0d1c0ffd64
def orfl14 : Packing := (1,1,7,5,4,6,0,orfd14)
def hashorfl14 (i : Nat) : Nat := 0x1c48000501c000000000000000000000033a80000000a100000000002a440200000000000000000a0b000000000000000000000000000000000001650000790f48380c0000000001e4b00000001ce000104800000000060500000000000000000c0a000a020001c9a0000000000694000000452d8210020000000000000300883c0000007758000000000000000000000060700031d000000000000000000005910c800005a0183400000000000000000002255b80000000824800000000000000000000008018000001141000000000000000000005c2ae2f0300000000000000000000000b260000000000000000000000000000000000000000000000000000000000000000000000000000000001c840000000000000000000000000000000000100000000000000000000000001000000
def orflevels : Nat → Packing
  | 8 => orfl8
  | 9 => orfl9
  | 10 => orfl10
  | 11 => orfl11
  | 12 => orfl12
  | 13 => orfl13
  | 14 => orfl14
  | _ => emptyPacking
def orfindex : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 2 9 4 10 2 4 (hashorfl9)
  | 10 => lookupWord 48 239 8 15 7 4 (hashorfl10)
  | 11 => lookupWord 509 3172 12 18 10 4 (hashorfl11)
  | 12 => lookupWord 984 6141 13 19 11 4 (hashorfl12)
  | 13 => lookupWord 171 853 10 16 8 4 (hashorfl13)
  | 14 => lookupWord 19 179 8 13 5 4 (hashorfl14)
  | _ => fun _ => none
def orf : Forest := ⟨511,15,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,orflevels,orfindex⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf8_0 : block orf 8 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allorf8 : block orf 8 0 4=true := gorf8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf9_0 : block orf 9 0 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf9_16 : block orf 9 16 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf9_48 : block orf 9 48 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf9_80 : block orf 9 80 25=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allorf9 : block orf 9 0 105=true := (@block_merge orf 9 0 80 25 (@block_merge orf 9 0 48 32 (@block_merge orf 9 0 16 32 gorf9_0 gorf9_16) gorf9_48) gorf9_80)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_0 : block orf 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_6 : block orf 10 6 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_38 : block orf 10 38 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_70 : block orf 10 70 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_102 : block orf 10 102 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_134 : block orf 10 134 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_166 : block orf 10 166 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_198 : block orf 10 198 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_230 : block orf 10 230 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_262 : block orf 10 262 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_294 : block orf 10 294 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_303 : block orf 10 303 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_335 : block orf 10 335 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_367 : block orf 10 367 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_399 : block orf 10 399 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_431 : block orf 10 431 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_463 : block orf 10 463 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_495 : block orf 10 495 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_527 : block orf 10 527 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_559 : block orf 10 559 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_591 : block orf 10 591 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_623 : block orf 10 623 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_655 : block orf 10 655 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_687 : block orf 10 687 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_719 : block orf 10 719 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_751 : block orf 10 751 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_783 : block orf 10 783 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_815 : block orf 10 815 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_847 : block orf 10 847 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_879 : block orf 10 879 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_911 : block orf 10 911 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf10_943 : block orf 10 943 16=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allorf10 : block orf 10 0 959=true := (@block_merge orf 10 0 943 16 (@block_merge orf 10 0 911 32 (@block_merge orf 10 0 879 32 (@block_merge orf 10 0 847 32 (@block_merge orf 10 0 815 32 (@block_merge orf 10 0 783 32 (@block_merge orf 10 0 751 32 (@block_merge orf 10 0 719 32 (@block_merge orf 10 0 687 32 (@block_merge orf 10 0 655 32 (@block_merge orf 10 0 623 32 (@block_merge orf 10 0 591 32 (@block_merge orf 10 0 559 32 (@block_merge orf 10 0 527 32 (@block_merge orf 10 0 495 32 (@block_merge orf 10 0 463 32 (@block_merge orf 10 0 431 32 (@block_merge orf 10 0 399 32 (@block_merge orf 10 0 367 32 (@block_merge orf 10 0 335 32 (@block_merge orf 10 0 303 32 (@block_merge orf 10 0 294 9 (@block_merge orf 10 0 262 32 (@block_merge orf 10 0 230 32 (@block_merge orf 10 0 198 32 (@block_merge orf 10 0 166 32 (@block_merge orf 10 0 134 32 (@block_merge orf 10 0 102 32 (@block_merge orf 10 0 70 32 (@block_merge orf 10 0 38 32 (@block_merge orf 10 0 6 32 gorf10_0 gorf10_6) gorf10_38) gorf10_70) gorf10_102) gorf10_134) gorf10_166) gorf10_198) gorf10_230) gorf10_262) gorf10_294) gorf10_303) gorf10_335) gorf10_367) gorf10_399) gorf10_431) gorf10_463) gorf10_495) gorf10_527) gorf10_559) gorf10_591) gorf10_623) gorf10_655) gorf10_687) gorf10_719) gorf10_751) gorf10_783) gorf10_815) gorf10_847) gorf10_879) gorf10_911) gorf10_943)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_0 : block orf 11 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_2 : block orf 11 2 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_34 : block orf 11 34 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_66 : block orf 11 66 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_98 : block orf 11 98 28=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_126 : block orf 11 126 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_158 : block orf 11 158 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_190 : block orf 11 190 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_222 : block orf 11 222 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_254 : block orf 11 254 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_286 : block orf 11 286 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_318 : block orf 11 318 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_350 : block orf 11 350 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_382 : block orf 11 382 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_414 : block orf 11 414 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_446 : block orf 11 446 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_478 : block orf 11 478 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_510 : block orf 11 510 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_542 : block orf 11 542 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_574 : block orf 11 574 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_606 : block orf 11 606 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_638 : block orf 11 638 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_670 : block orf 11 670 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_702 : block orf 11 702 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_734 : block orf 11 734 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_766 : block orf 11 766 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_798 : block orf 11 798 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_830 : block orf 11 830 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_862 : block orf 11 862 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_894 : block orf 11 894 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_926 : block orf 11 926 15=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_941 : block orf 11 941 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_973 : block orf 11 973 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1005 : block orf 11 1005 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1037 : block orf 11 1037 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1069 : block orf 11 1069 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1101 : block orf 11 1101 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1133 : block orf 11 1133 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1165 : block orf 11 1165 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1197 : block orf 11 1197 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1229 : block orf 11 1229 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1261 : block orf 11 1261 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1293 : block orf 11 1293 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1325 : block orf 11 1325 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1357 : block orf 11 1357 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1389 : block orf 11 1389 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1421 : block orf 11 1421 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1453 : block orf 11 1453 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1485 : block orf 11 1485 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1517 : block orf 11 1517 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1549 : block orf 11 1549 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1581 : block orf 11 1581 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf11_1613 : block orf 11 1613 25=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allorf11 : block orf 11 0 1638=true := (@block_merge orf 11 0 1613 25 (@block_merge orf 11 0 1581 32 (@block_merge orf 11 0 1549 32 (@block_merge orf 11 0 1517 32 (@block_merge orf 11 0 1485 32 (@block_merge orf 11 0 1453 32 (@block_merge orf 11 0 1421 32 (@block_merge orf 11 0 1389 32 (@block_merge orf 11 0 1357 32 (@block_merge orf 11 0 1325 32 (@block_merge orf 11 0 1293 32 (@block_merge orf 11 0 1261 32 (@block_merge orf 11 0 1229 32 (@block_merge orf 11 0 1197 32 (@block_merge orf 11 0 1165 32 (@block_merge orf 11 0 1133 32 (@block_merge orf 11 0 1101 32 (@block_merge orf 11 0 1069 32 (@block_merge orf 11 0 1037 32 (@block_merge orf 11 0 1005 32 (@block_merge orf 11 0 973 32 (@block_merge orf 11 0 941 32 (@block_merge orf 11 0 926 15 (@block_merge orf 11 0 894 32 (@block_merge orf 11 0 862 32 (@block_merge orf 11 0 830 32 (@block_merge orf 11 0 798 32 (@block_merge orf 11 0 766 32 (@block_merge orf 11 0 734 32 (@block_merge orf 11 0 702 32 (@block_merge orf 11 0 670 32 (@block_merge orf 11 0 638 32 (@block_merge orf 11 0 606 32 (@block_merge orf 11 0 574 32 (@block_merge orf 11 0 542 32 (@block_merge orf 11 0 510 32 (@block_merge orf 11 0 478 32 (@block_merge orf 11 0 446 32 (@block_merge orf 11 0 414 32 (@block_merge orf 11 0 382 32 (@block_merge orf 11 0 350 32 (@block_merge orf 11 0 318 32 (@block_merge orf 11 0 286 32 (@block_merge orf 11 0 254 32 (@block_merge orf 11 0 222 32 (@block_merge orf 11 0 190 32 (@block_merge orf 11 0 158 32 (@block_merge orf 11 0 126 32 (@block_merge orf 11 0 98 28 (@block_merge orf 11 0 66 32 (@block_merge orf 11 0 34 32 (@block_merge orf 11 0 2 32 gorf11_0 gorf11_2) gorf11_34) gorf11_66) gorf11_98) gorf11_126) gorf11_158) gorf11_190) gorf11_222) gorf11_254) gorf11_286) gorf11_318) gorf11_350) gorf11_382) gorf11_414) gorf11_446) gorf11_478) gorf11_510) gorf11_542) gorf11_574) gorf11_606) gorf11_638) gorf11_670) gorf11_702) gorf11_734) gorf11_766) gorf11_798) gorf11_830) gorf11_862) gorf11_894) gorf11_926) gorf11_941) gorf11_973) gorf11_1005) gorf11_1037) gorf11_1069) gorf11_1101) gorf11_1133) gorf11_1165) gorf11_1197) gorf11_1229) gorf11_1261) gorf11_1293) gorf11_1325) gorf11_1357) gorf11_1389) gorf11_1421) gorf11_1453) gorf11_1485) gorf11_1517) gorf11_1549) gorf11_1581) gorf11_1613)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf12_0 : block orf 12 0 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf12_32 : block orf 12 32 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf12_47 : block orf 12 47 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf12_79 : block orf 12 79 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf12_111 : block orf 12 111 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf12_143 : block orf 12 143 26=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf12_169 : block orf 12 169 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf12_201 : block orf 12 201 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf12_233 : block orf 12 233 13=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allorf12 : block orf 12 0 246=true := (@block_merge orf 12 0 233 13 (@block_merge orf 12 0 201 32 (@block_merge orf 12 0 169 32 (@block_merge orf 12 0 143 26 (@block_merge orf 12 0 111 32 (@block_merge orf 12 0 79 32 (@block_merge orf 12 0 47 32 (@block_merge orf 12 0 32 15 gorf12_0 gorf12_32) gorf12_47) gorf12_79) gorf12_111) gorf12_143) gorf12_169) gorf12_201) gorf12_233)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf13_0 : block orf 13 0 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf13_7 : block orf 13 7 10=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allorf13 : block orf 13 0 17=true := (@block_merge orf 13 0 7 10 gorf13_0 gorf13_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem gorf14_0 : block orf 14 0 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allorf14 : block orf 14 0 1=true := gorf14_0
theorem tablesorf : checkedTables orf 15 := by
  intro k hk
  interval_cases k
  · exact (rfl : block orf 0 0 0 = true)
  · exact (rfl : block orf 1 0 0 = true)
  · exact (rfl : block orf 2 0 0 = true)
  · exact (rfl : block orf 3 0 0 = true)
  · exact (rfl : block orf 4 0 0 = true)
  · exact (rfl : block orf 5 0 0 = true)
  · exact (rfl : block orf 6 0 0 = true)
  · exact (rfl : block orf 7 0 0 = true)
  · exact allorf8
  · exact allorf9
  · exact allorf10
  · exact allorf11
  · exact allorf12
  · exact allorf13
  · exact allorf14
  · exact (rfl : block orf 15 0 0 = true)
theorem geomorf : graphValid orf (boundsBefore known383) = true := geomdead
-- With the first gate available as a signal, fourteen further steps cannot reach the target.
theorem orf_start : Impossible graph 14 (inputs++[seedB]).toFinset := by
  have noRun := root_index (g:=orf) (before_sound known383 valid383) geomorf tablesorf (k:=14) (by decide)
    (i:=0) (ws:=inputs++[seedB]) (by decide +kernel)
  have tgt : targetOf orf=graph := by decide +kernel
  exact tgt ▸ noRun
theorem dead_only : Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) (before_sound known383 valid383) geomdead tablesdead (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun
theorem boundB (C : PEqualNP.CircuitLowerBounds.Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6))
    (h : PEqualNP.MetaComplexity.circuitFun 9 C = edge) : 16 ≤ C.size := by
  by_contra! small
  obtain ⟨k,t,hk,hdead | hlive⟩ := initial_liveB C legal first h (by omega)
  · exact dead_only k t hk hdead
  · exact orf_start k t hk hlive
end PEqualNP.Outside.L_meta_1678

theorem PEqualNP.Outside.L_meta_1678 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size :=
  PEqualNP.Outside.L_meta_1678.boundB
