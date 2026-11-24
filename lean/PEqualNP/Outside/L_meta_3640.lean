import PEqualNP.Defs

-- The live-wire verification framework and the subgraph bounds are adapted
-- from the checked proofs of L-meta-1667 and L-meta-1920 in pull requests
-- 4332 and 5546. The latter credits PressF10 for the framework.
-- Those contributions are distributed under the Apache 2.0 license.
namespace PEqualNP.Outside.L_meta_3640
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
def seed4 : Sig := neg (inputs.getD 4 zero)

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed4_table : ∀ r : Row, bit r seed4 = !(sample r 4) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed4_nonzero : seed4 ≠ zero := by decide +kernel
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
def vertex (m j : Nat) := if m.testBit j then (if m.testBit 9 && j == 4 then neg (inputs.getD 4 zero) else inputs.getD j zero) else zero
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

def supportPairs (baseRow mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,Fin.ofNat 512 baseRow,Fin.ofNat 512 (baseRow ^^^ (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  let base := if m.testBit 9 && m.testBit 4 then 16 else 0
  (selected m).map fun (i,a) =>
    let r := base ^^^ (1 <<< ((hints >>> (4*i)) &&& 15))
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ^^^ (1 <<< i)))

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
def colFree (m z o : Nat) := (m &&& 511) ^^^ ((m &&& 511) &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  let count := (xs.map Prod.fst).toFinset.card
  let drop := colFree free q 0
  let lz := if m.testBit 9 && drop.testBit 4 then drop &&& (511 ^^^ 16) else drop
  let lo := if m.testBit 9 && drop.testBit 4 then 16 else 0
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows lz lo) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) _ hh.1 p bank hr ha)
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
  let x := fun j => if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then (if m.testBit 9 && j.val == 4 then ~~~(v 4) else v j.val) else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · by_cases hf : (m.testBit 9 && j.val == 4) = true
    · have hj4 : j.val = 4 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hf; exact hf.2
      simp only [vertex, hh, hf, ite_true, bit_neg, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
      exact congrArg Bool.not (asRow_bit v i ⟨4, by decide⟩)
    · simpa [vertex, hh, hf] using asRow_bit v i j
  · simp [vertex, hh, bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
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

abbrev ExtraCut := Nat → List Sig → Bool
abbrev ChildLinks := (Nat → List (List Sig)) × ExtraCut

def closeChild (pools : List BoundPool) (links : ChildLinks) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links.1 (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op) || links.2 k ws

theorem closeChild_sound {raw T pools} {links : ChildLinks} {k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links.1 tag → Impossible T k (List.toFinset xs))
    (cutValid : ∀ ws : List Sig, ws.Nodup → links.2 k ws = true → Impossible T k ws.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with (⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩) | cutProof
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · exact cutValid _ nd cutProof

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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × ChildLinks
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
theorem evalMove_sound {raw T r s ws pools} {links : ChildLinks} {cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links.1 tag → Impossible T (cap-1) (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
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
  exact closeChild_sound pv lv cv nd' test k t hk h


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

theorem node_sound {raw T r s ws pools} {links : ChildLinks} {cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links.1 tag → Impossible T (cap-1) (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
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
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv cv pro fresh (all_unary checks ha keep)
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
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv cv
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
  cut : ExtraCut := fun _ _ => false
  cut_sound : ∀ k (ws : List Sig), ws.Nodup → cut k ws = true → Impossible (chartGoal mask) k ws.toFinset := by
    intros
    contradiction

def wiresOf (g : Forest) :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
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
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls,g.cut) ws)

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
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (g.cut_sound _) (by simpa only [h0,if_false] using checked.2)
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
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true,Bool.true_or]
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
  (k,ws.length,ws,preCov ws,rules,ls,g.cut)


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
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]

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
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index,fun _ _ => false, by simp⟩
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
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index,fun _ _ => false, by simp⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index,fun _ _ => false, by simp⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index,fun _ _ => false, by simp⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index,fun _ _ => false, by simp⟩
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
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index,fun _ _ => false, by simp⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index,fun _ _ => false, by simp⟩
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
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index,fun _ _ => false, by simp⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index,fun _ _ => false, by simp⟩
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
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index,fun _ _ => false, by simp⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index,fun _ _ => false, by simp⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index,fun _ _ => false, by simp⟩
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
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index,fun _ _ => false, by simp⟩
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
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex,fun _ _ => false, by simp⟩
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

theorem dead_start : Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) (before_sound known383 valid383) geomdead tablesdead (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

theorem low511 : Lower (vars 511) (graphGoal 511) 15 :=
  lower_forest (g:=dead) (i:=0) (hints:=13438755073)
    (before_sound known383 valid383) geomdead tablesdead (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def bounds511 (q : Nat) := if q = 511 then 15 else boundsBefore known383 q
theorem bounds511_sound (q : Nat) : Lower (vars q) (graphGoal q) (bounds511 q) := by
  unfold bounds511
  split
  next h => exact h ▸ low511
  next => exact before_sound known383 valid383 q

private lemma cutLiveSize {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
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

private lemma cutBitBin (i : Row) (d : Bool) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]
private lemma cutBitNeg (i : Row) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
theorem inverted_pair {T k t S} (l : Live T k t S) {p n : Row}
    (pp : bit p T = true) (nn : bit n T = false)
    (h : ∀ w∈S, bit p w=true → bit n w=true) : t ≠ 0 := by
  intro eq
  obtain ⟨w,hw,wp,wn⟩ := mono_row_difference l eq pp nn
  exact Bool.noConfusion ((h w hw wp).symm.trans wn)

def Sensitive (T : Sig) (S : Finset Sig) (r : Row) (v : Sig) : Prop :=
  ∃ s, bit r T ≠ bit s T ∧ ∀ u ∈ S, u ≠ v → bit r u = bit s u

def Pivot (T : Sig) (S : Finset Sig) (r s : Row) (v : Sig) : Prop :=
  Sensitive T S r v ∧ Sensitive T S s v

private theorem sensitive_mem (l : Live T k t S) (h : Sensitive T S r v) : v∈S := by
  rcases h with ⟨s,d,h⟩
  obtain ⟨u,hu,hd⟩ := live_row_difference l d
  by_contra z
  exact hd (h _ hu (fun e => z (e ▸ hu)))

private theorem sensitive_unary (az : a∉U) (h : Sensitive T (insert a U) r v) :
    Sensitive T (insert (neg a) U) r (if v=a then neg a else v) := by
  rcases h with ⟨s,hd,hn⟩
  refine ⟨s,hd,?_⟩
  intro u hu ne
  rcases Finset.mem_insert.mp hu with rfl|hu
  · by_cases eq : v=a
    · simp [eq] at ne
    · rw [cutBitNeg,cutBitNeg,hn _ (by simp) (Ne.symm eq)]
  · apply hn _ (Finset.mem_insert_of_mem hu)
    intro e
    subst u
    by_cases eq : v=a
    · exact az (eq ▸ hu)
    · simp [eq] at ne

private theorem sensitive_binary (az : a∉U) (bz : b∉U)
    (h : Sensitive T (insert a (insert b U)) r v) :
    Sensitive T (insert (bin d a b) U) r (if v=a ∨ v=b then bin d a b else v) := by
  rcases h with ⟨s,hd,hn⟩
  refine ⟨s,hd,?_⟩
  intro u hu ne
  rcases Finset.mem_insert.mp hu with rfl|hu
  · by_cases eq : v=a ∨ v=b
    · simp [eq] at ne
    · rw [cutBitBin,cutBitBin,hn a (by simp) (fun e => eq (.inl e.symm)),
        hn b (by simp) (fun e => eq (.inr e.symm))]
  · apply hn _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    intro e
    subst u
    by_cases eq : v=a ∨ v=b
    · rcases eq with e|e
      · exact az (e ▸ hu)
      · exact bz (e ▸ hu)
    · simp [eq] at ne

private theorem sensitive_pass {g a b : Sig} {d : Bool} (az : a∉U) (ab : a≠b)
    (law : ∀ r, bit r g = (if d then bit r a || bit r b else bit r a && bit r b))
    (l : Live T k t (insert g U)) (h : Sensitive T (insert a (insert b U)) r a) :
    bit r b = !d ∧ bit r g = bit r a := by
  rcases h with ⟨s,hd,hn⟩
  obtain ⟨u,hu,uh⟩ := live_row_difference l hd
  rcases Finset.mem_insert.mp hu with rfl | hu
  · have eq := hn b (by simp) ab.symm
    rw [law,law] at uh
    rw [law,←eq] at *
    all_goals cases d <;> cases a' : bit r a <;> cases b' : bit r b <;>
      cases c' : bit s a <;> simp_all
  · exact (uh (hn _ (by simp [hu]) (fun e => az (e ▸ hu)))).elim

private theorem two_split {U : Finset Sig} {i j a b : Sig} {d : Bool}
    (az : a∉U) (bz : b∉U) (ab : a≠b) (hf : bin d a b ∉ insert a (insert b U)) (l : Live T k t (insert (bin d a b) U))
    (p : Pivot T (insert a (insert b U)) r s i)
    (q : Pivot T (insert a (insert b U)) r s j)
    (hi : bit r i ≠ bit s i) (hj : bit r j ≠ bit s j) (ne : i≠j) :
    ∃ i' j', Pivot T (insert (bin d a b) U) r s i' ∧ Pivot T (insert (bin d a b) U) r s j' ∧
      bit r i' ≠ bit s i' ∧ bit r j' ≠ bit s j' ∧ i'≠j' := by
  let f (v : Sig) := if v=a ∨ v=b then bin d a b else v
  have lift {v} (pv : Pivot T (insert a (insert b U)) r s v) :
       Pivot T (insert (bin d a b) U) r s (f v) :=
    ⟨sensitive_binary az bz pv.1,sensitive_binary az bz pv.2⟩
  have passA {row} (pv : Sensitive T (insert a (insert b U)) row a) :=
    sensitive_pass az ab (d:=d) (fun i => cutBitBin i d a b) l pv
  have passB {row} (pv : Sensitive T (insert a (insert b U)) row b) :
      bit row a = !d ∧ bit row (bin d a b) = bit row b := by
    apply sensitive_pass bz ab.symm (d:=d) (fun i => ?_) l
    · simpa [Finset.insert_comm] using pv
    · rw [cutBitBin]; cases d <;> simp [Bool.and_comm,Bool.or_comm]
  have val {v} (pv : Pivot T (insert a (insert b U)) r s v) :
      bit r (f v)=bit r v ∧ bit s (f v)=bit s v := by
    by_cases eq : v=a ∨ v=b
    · simp only [f,ite_eq_left eq]
      rcases eq with rfl|rfl
      · exact ⟨(passA pv.1).2,(passA pv.2).2⟩
      · exact ⟨(passB pv.1).2,(passB pv.2).2⟩
    · simp [f,eq]
  have fresh {v} (pv : Pivot T (insert a (insert b U)) r s v) (h : ¬(v=a ∨ v=b))
      (fv : v=bin d a b) (hf : bin d a b ∉ insert a (insert b U)) : False := by
    subst v
    obtain ⟨row,hd,ex⟩ := pv.1
    obtain ⟨u,hu,uh⟩ := live_row_difference l hd
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rw [cutBitBin,cutBitBin,ex a (by simp) (fun e => h (.inl e.symm)),
        ex b (by simp) (fun e => h (.inr e.symm))] at uh
      exact uh rfl
    · exact uh (ex _ (by simp [hu]) (fun e => hf (e ▸ (by simp [hu]))))
  refine ⟨f i,f j,lift p,lift q,by rwa [(val p).1,(val p).2],by rwa [(val q).1,(val q).2],?_⟩
  by_cases ei : i=a ∨ i=b <;> by_cases ej : j=a ∨ j=b
  · rcases ei with rfl|rfl <;> rcases ej with rfl|rfl
    · contradiction
    · exact (hj ((passA p.1).1.trans (passA p.2).1.symm)).elim
    · exact (hj ((passB p.1).1.trans (passB p.2).1.symm)).elim
    · contradiction
  · simp only [f,ite_eq_left ei,ite_eq_right ej]
    intro e
    exact fresh q ej e.symm hf
  · simp only [f,ite_eq_right ei,ite_eq_left ej]
    intro e
    exact fresh p ei e hf
  · simpa [f,ei,ej] using ne

theorem tight_no_conflict {T k t S} (l : Live T k t S) (tight : k+1≤S.card+t)
    {r s i j} (p : Pivot T S r s i) (q : Pivot T S r s j)
    (hi : bit r i ≠ bit s i) (hj : bit r j ≠ bit s j) (ne : i≠j) : False := by
  induction l generalizing i j with
  | stop hp =>
    have mem := sensitive_mem (Live.stop hp) p.1
    have mem' := sensitive_mem (Live.stop hp) q.1
    simp only [Finset.mem_singleton] at mem mem'
    exact ne (mem.trans mem'.symm)
  | @unary k t U a ha hf tail ih =>
    have hfU : neg a ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have az : a ∉ U := by
      intro hal
      rw [Finset.insert_eq_of_mem hal] at tight
      omega
    rw [Finset.card_insert_of_notMem az] at tight
    have next : k+1 ≤ (insert (neg a) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    let f (v : Sig) := if v=a then neg a else v
    have lift {v} (pv : Pivot T (insert a U) r s v) :
        Pivot T (insert (neg a) U) r s (f v) := ⟨sensitive_unary az pv.1,sensitive_unary az pv.2⟩
    have dv {v} (dd : bit r v ≠ bit s v) : bit r (f v) ≠ bit s (f v) := by
      by_cases e : v=a
      · subst v; simpa [f,cutBitNeg] using dd
      · simpa [f,e] using dd
    apply ih next (lift p) (lift q) (dv hi) (dv hj)
    have mi := sensitive_mem (.unary ha hf tail) p.1
    have mj := sensitive_mem (.unary ha hf tail) q.1
    by_cases ei : i=a <;> by_cases ej : j=a
    · exact (ne (ei.trans ej.symm)).elim
    · simp only [f,ite_eq_left ei,ite_eq_right ej]
      exact fun e => hf (e ▸ mj)
    · simp only [f,ite_eq_right ei,ite_eq_left ej]
      exact fun e => hf (e ▸ mi)
    · simpa [f,ei,ej] using ne
  | @binary k t U a b d ha hb ab hf tail ih =>
    have hfU : bin d a b ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have lim := Finset.card_insert_le (a:=a) (s:=insert b U)
    have bl := Finset.card_insert_le (a:=b) (s:=U)
    have bz : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight lim
      omega
    have az : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    rw [Finset.card_insert_of_notMem az,Finset.card_insert_of_notMem bz] at tight
    have next : k+1 ≤ (insert (bin d a b) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    obtain ⟨i',j',pi,pj,ii,jj,z⟩ := two_split (fun hm => az (by simp [hm])) bz ab hf tail p q hi hj ne
    exact ih next pi pj ii jj z

theorem tight_no_binate {T k t S} (l : Live T k t S) (tight : k+1≤S.card+t)
    {r s i} (p : Pivot T S r s i) (hi : bit r i = bit s i) (goal : bit r T ≠ bit s T) : False := by
  induction l generalizing i with
  | stop hp =>
    have mi := sensitive_mem (Live.stop hp) p.1
    simp only [Finset.mem_singleton] at mi
    exact goal (mi ▸ hi)
  | @unary k t U a ha hf tail ih =>
    have hfU : neg a ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have az : a ∉ U := by
      intro hal
      rw [Finset.insert_eq_of_mem hal] at tight
      omega
    rw [Finset.card_insert_of_notMem az] at tight
    have next : k+1 ≤ (insert (neg a) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    let f (v : Sig) := if v=a then neg a else v
    have lift {v} (pv : Pivot T (insert a U) r s v) :
        Pivot T (insert (neg a) U) r s (f v) := ⟨sensitive_unary az pv.1,sensitive_unary az pv.2⟩
    have dv {v} (dd : bit r v = bit s v) : bit r (f v) = bit s (f v) := by
      by_cases e : v=a
      · subst v; simpa [f,cutBitNeg] using dd
      · simpa [f,e] using dd
    exact ih next (lift p) (dv hi)
  | @binary k t U a b d ha hb ab hf tail ih =>
    have hfU : bin d a b ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have lim := Finset.card_insert_le (a:=a) (s:=insert b U)
    have bl := Finset.card_insert_le (a:=b) (s:=U)
    have bz : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight lim
      omega
    have az : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    rw [Finset.card_insert_of_notMem az,Finset.card_insert_of_notMem bz] at tight
    have next : k+1 ≤ (insert (bin d a b) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    have nz : a∉U := fun h => az (Finset.mem_insert_of_mem h)
    let f (v : Sig) := if v=a ∨ v=b then bin d a b else v
    have lift : Pivot T (insert (bin d a b) U) r s (f i) :=
      ⟨sensitive_binary nz bz p.1,sensitive_binary nz bz p.2⟩
    apply ih next lift
    by_cases eq : i=a ∨ i=b
    · simp only [f,ite_eq_left eq]
      rcases eq with e|e
      · subst i
        have pick {row} (pv : Sensitive T (insert a (insert b U)) row a) :=
          (sensitive_pass nz ab (d:=d) (fun j => cutBitBin j d a b) tail pv).2
        exact (pick p.1).trans (hi.trans (pick p.2).symm)
      · subst i
        have law (row : Row) : bit row (bin d a b) =
            (if d then bit row b || bit row a else bit row b && bit row a) := by
          rw [cutBitBin]; cases d <;> simp [Bool.and_comm,Bool.or_comm]
        have pick {row} (pv : Sensitive T (insert a (insert b U)) row b) :=
          (sensitive_pass bz ab.symm law tail (by simpa [Finset.insert_comm] using pv)).2
        exact (pick p.1).trans (hi.trans (pick p.2).symm)
    · simpa [f,eq] using hi



def DOnly (T : Sig) (S : Finset Sig) (v : Sig) (p n : Row) : Prop :=
  bit p T = true ∧ bit n T = false ∧ ∀ u∈S, u ≠ v → bit p u = true → bit n u = true

def DPivot (T : Sig) (S : Finset Sig) (p n : Row) (v : Sig) : Prop :=
  (∃ s, DOnly T S v p s) ∧ (∃ r, DOnly T S v r n)

private theorem donly_vals (l : Live T k t S) (ht : t=0) (h : DOnly T S v p n) :
    v∈S ∧ bit p v = true ∧ bit n v = false := by
  obtain ⟨u,hu,pp,nn⟩ := mono_row_difference l ht h.1 h.2.1
  have eq : u=v := by
    by_contra ne
    have z := h.2.2 _ hu ne pp
    simp_all
  exact eq ▸ ⟨hu,pp,nn⟩

private theorem donly_binary (az : a∉U) (bz : b∉U)
    (h : DOnly T (insert a (insert b U)) v p n) :
    DOnly T (insert (bin d a b) U) (if v=a ∨ v=b then bin d a b else v) p n := by
  refine ⟨h.1,h.2.1,?_⟩
  intro u hu ne pp
  rcases Finset.mem_insert.mp hu with rfl|hu
  · by_cases eq : v=a ∨ v=b
    · simp [eq] at ne
    · have a' := h.2.2 a (by simp) (fun e => eq (.inl e.symm))
      have b' := h.2.2 b (by simp) (fun e => eq (.inr e.symm))
      rw [cutBitBin] at pp ⊢
      cases d <;> simp_all [Bool.and_eq_true,Bool.or_eq_true] <;> tauto
  · apply h.2.2 _ (by simp [hu]) _ pp
    intro e
    subst u
    by_cases eq : v=a ∨ v=b
    · rcases eq with e|e
      · exact az (e ▸ hu)
      · exact bz (e ▸ hu)
    · simp [eq] at ne

private theorem incompatible {T : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (az : a ∉ U) (bz : b ∉ U) (ab : a ≠ b)
    (l : Live T k t (insert (bin d a b) U)) (lt : Live T (k+1) t (insert a (insert b U)))
    (ht : t=0) (pa : DPivot T (insert a (insert b U)) r s a)
    (pb : DPivot T (insert a (insert b U)) r s b) : False := by
  cases d with
  | true =>
    obtain ⟨s',h⟩ := pa.1
    obtain ⟨s₁,h₁⟩ := pb.1
    have bb := (donly_vals lt ht h₁).2.1
    have bz' := h.2.2 b (by simp) ab.symm bb
    have h' := donly_binary (d:=true) az bz h
    simp only [true_or,ite_true] at h'
    have g0 := (donly_vals l ht h').2.2
    simp [cutBitBin,bz'] at g0
  | false =>
    obtain ⟨r',h⟩ := pa.2
    obtain ⟨r₁,h₁⟩ := pb.2
    have bb := (donly_vals lt ht h₁).2.2
    have hmb := h.2.2 b (by simp) ab.symm
    have bz' : bit r' b = false := by
      cases e : bit r' b
      · rfl
      · have h' := hmb e
        simp_all
    have h' := donly_binary (d:=false) az bz h
    simp only [true_or,ite_true] at h'
    have g1 := (donly_vals l ht h').2.1
    simp [cutBitBin,bz'] at g1

theorem mono_tight_no_conflict {T k t S} (l : Live T k t S) (tight : k+1≤S.card+t) (ht : t=0)
    {r s i j} (p : DPivot T S r s i) (q : DPivot T S r s j) (ne : i≠j) : False := by
  induction l generalizing i j with
  | stop hp =>
    obtain ⟨_,dp⟩ := p.1
    obtain ⟨_,dq⟩ := q.1
    have mp := (donly_vals (Live.stop hp) rfl dp).1
    have mq := (donly_vals (Live.stop hp) rfl dq).1
    simp only [Finset.mem_singleton] at mp mq
    exact ne (mp.trans mq.symm)
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb ab hf tail ih =>
    have hfU : bin d a b ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have lim := Finset.card_insert_le (a:=a) (s:=insert b U)
    have bl := Finset.card_insert_le (a:=b) (s:=U)
    have bz : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight lim
      omega
    have ax : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    have az : a∉U := fun h => ax (Finset.mem_insert_of_mem h)
    rw [Finset.card_insert_of_notMem ax,Finset.card_insert_of_notMem bz] at tight
    have next : k+1 ≤ (insert (bin d a b) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    let f (v : Sig) := if v=a ∨ v=b then bin d a b else v
    have lift {v} (pv : DPivot T (insert a (insert b U)) r s v) :
        DPivot T (insert (bin d a b) U) r s (f v) := by
      obtain ⟨⟨aa,haa⟩,⟨bb,hbb⟩⟩ := pv
      exact ⟨⟨aa,donly_binary az bz haa⟩,⟨bb,donly_binary az bz hbb⟩⟩
    have before := Live.binary ha hb ab hf tail
    apply ih next ht (lift p) (lift q)
    by_cases ei : i=a ∨ i=b <;> by_cases ej : j=a ∨ j=b
    · rcases ei with rfl|rfl <;> rcases ej with rfl|rfl
      · contradiction
      · exact (incompatible az bz ab tail before ht p q).elim
      · exact (incompatible az bz ab tail before ht q p).elim
      · contradiction
    · simp only [f,ite_eq_left ei,ite_eq_right ej]
      obtain ⟨n,hn⟩ := q.1
      exact fun e => hf (e ▸ (donly_vals before ht hn).1)
    · simp only [f,ite_eq_right ei,ite_eq_left ej]
      obtain ⟨n,hn⟩ := p.1
      exact fun e => hf (e ▸ (donly_vals before ht hn).1)
    · simpa [f,ei,ej] using ne

structure Six3640 where
  p : Row
  n : Row
  ni : Row
  pi : Row
  nj : Row
  pj : Row

def invRows3640 : List (Row × Row) :=
 [(139,138), (101,100), (401,400), (170,138), (154,146), (325,261), (6,10), (180,52), (298,42), (98,104), (7,261), (120,116), (404,402), (43,42), (403,402), (197,201), (277,276), (320,68), (131,385), (304,50), (13,5), (132,384), (152,146), (273,257), (81,80), (168,138), (160,136), (105,104), (152,400), (66,72), (288,40), (264,258)]

def sixRows3640 : List Six3640 :=
 [⟨160,69,128,101,32,197⟩, ⟨17,10,1,26,16,11⟩, ⟨320,50,256,114,64,306⟩, ⟨24,5,16,13,8,21⟩, ⟨33,272,32,273,1,304⟩, ⟨132,42,128,46,4,170⟩, ⟨66,385,64,387,2,449⟩, ⟨288,138,32,394,256,170⟩, ⟨17,104,1,120,16,105⟩, ⟨12,385,8,389,4,393⟩, ⟨264,50,256,58,8,306⟩, ⟨6,104,4,106,2,108⟩, ⟨12,208,8,212,4,216⟩, ⟨288,65,32,321,256,97⟩, ⟨33,208,32,209,1,240⟩, ⟨3,80,2,81,1,82⟩, ⟨6,385,4,387,2,389⟩, ⟨12,50,8,54,4,58⟩, ⟨24,257,16,265,8,273⟩, ⟨264,69,256,77,8,325⟩, ⟨320,138,256,202,64,394⟩, ⟨3,104,2,105,1,106⟩, ⟨17,138,1,154,16,139⟩, ⟨3,276,2,277,1,278⟩, ⟨6,208,4,210,2,212⟩, ⟨264,208,256,216,8,464⟩, ⟨160,260,128,292,32,388⟩]

def inversion3640 (ws : List Sig) (rn : Row × Row) : Bool :=
  ws.all fun w => !bit rn.1 w || bit rn.2 w

def deviates3640 (p n r s : Row) (w : Sig) : Bool :=
  (bit p w != bit r w) || (bit n w != bit s w)

def pick3640 (ws : List Sig) (p n r s : Row) : Option Sig :=
  match ws.filter (deviates3640 p n r s) with
  | [w] => if (bit p w != bit r w) && (bit n w != bit s w) then some w else none
  | _ => none

def pairCut3640 (p n : Row) (a b : Option Sig) : Bool :=
  match a,b with
  | some u,some v => (bit p u == bit n u) || (bit p v == bit n v) || (u != v)
  | some u,none => bit p u == bit n u
  | none,some v => bit p v == bit n v
  | none,none => false

def sixCut3640 (ws : List Sig) (s : Six3640) : Bool :=
  pairCut3640 s.p s.n (pick3640 ws s.p s.n s.ni s.pi) (pick3640 ws s.p s.n s.nj s.pj)

def shapeCut3640 (k : Nat) (ws : List Sig) : Bool :=
  (k+1 ≤ ws.length || (k == ws.length && invRows3640.any (inversion3640 ws))) &&
    sixRows3640.any (sixCut3640 ws)

def sixValid3640 (T : Sig) (s : Six3640) : Bool :=
  (bit s.p T != bit s.n T) && (bit s.p T != bit s.ni T) &&
  (bit s.n T != bit s.pi T) && (bit s.p T != bit s.nj T) && (bit s.n T != bit s.pj T)

theorem sixRows3640_valid :
    sixRows3640.all (sixValid3640 (chartGoal 511)) = true := by decide +kernel

theorem invRows3640_valid :
    invRows3640.all (fun rn => bit rn.1 (chartGoal 511) && !bit rn.2 (chartGoal 511)) = true := by
  decide +kernel

private theorem pick_single3640 {ws p n r s v}
    (h : pick3640 ws p n r s = some v) : ws.filter (deviates3640 p n r s) = [v] := by
  unfold pick3640 at h
  split at h
  next w eq =>
    split at h
    · cases h
      exact eq
    · contradiction
  next => contradiction

private theorem pick_pivot3640 {ws p n r s v T}
    (h : pick3640 ws p n r s = some v) (dr : bit p T ≠ bit r T) (ds : bit n T ≠ bit s T) :
    Pivot T ws.toFinset p n v := by
  have good := pick_single3640 h
  have agree (u : Sig) (hu : u ∈ ws.toFinset) (ne : u ≠ v) :
      bit p u = bit r u ∧ bit n u = bit s u := by
    have hd : deviates3640 p n r s u = false := by
      cases e : deviates3640 p n r s u with
      | false => rfl
      | true =>
        have a := List.mem_filter.mpr ⟨List.mem_toFinset.mp hu,e⟩
        rw [good] at a
        exact False.elim (ne (List.mem_singleton.mp a))
    simpa [deviates3640] using hd
  exact ⟨⟨r,dr,fun u hu ne => (agree u hu ne).1⟩,
    ⟨s,ds,fun u hu ne => (agree u hu ne).2⟩⟩

private theorem six_impossible3640 {ws k t T s} (run : Live T k t ws.toFinset)
    (tight : k+1 ≤ ws.toFinset.card+t) (valid : sixValid3640 T s = true)
    (cut : sixCut3640 ws s = true) : False := by
  simp [sixValid3640,and_assoc] at valid
  obtain ⟨diff,dr,ds,er,es⟩ := valid
  let pi := pick3640 ws s.p s.n s.ni s.pi
  let pj := pick3640 ws s.p s.n s.nj s.pj
  change pairCut3640 s.p s.n pi pj = true at cut
  cases hi : pi with
  | none =>
    cases hj : pj with
    | none => simp [pairCut3640,hi,hj] at cut
    | some v =>
      have pv := pick_pivot3640 (v:=v) (show pick3640 ws s.p s.n s.nj s.pj = some v from hj) er es
      exact tight_no_binate run tight pv (by simpa [pairCut3640,hi,hj] using cut) diff
  | some u =>
    have pu := pick_pivot3640 (v:=u) (show pick3640 ws s.p s.n s.ni s.pi = some u from hi) dr ds
    by_cases eu : bit s.p u = bit s.n u
    · exact tight_no_binate run tight pu eu diff
    cases hj : pj with
    | none => simp [pairCut3640,hi,hj,eu] at cut
    | some v =>
      have pv := pick_pivot3640 (v:=v) (show pick3640 ws s.p s.n s.nj s.pj = some v from hj) er es
      by_cases ev : bit s.p v = bit s.n v
      · exact tight_no_binate run tight pv ev diff
      exact tight_no_conflict run tight pu pv eu ev (by simpa [pairCut3640,hi,hj,eu,ev] using cut)

theorem shapeCut3640_sound (k : Nat) (ws : List Sig) (nd : ws.Nodup)
    (cut : shapeCut3640 k ws = true) : Impossible (chartGoal 511) k ws.toFinset := by
  intro j t budget run
  simp only [shapeCut3640, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.any_eq_true] at cut
  obtain ⟨room,s,hs,why⟩ := cut
  have tight : j+1 ≤ ws.toFinset.card+t := by
    rw [List.toFinset_card_of_nodup nd]
    rcases room with room|⟨eq,p,hp,inv⟩
    · omega
    · have test := List.all_eq_true.mp invRows3640_valid p hp
      have sign : bit p.1 (chartGoal 511) = true ∧ bit p.2 (chartGoal 511) = false := by simpa using test
      have need : t ≠ 0 := by
        intro zeroNot
        obtain ⟨w,hw,h1,h0⟩ := mono_row_difference run zeroNot sign.1 sign.2
        have wi := List.all_eq_true.mp inv w (List.mem_toFinset.mp hw)
        simp [h1,h0] at wi
      omega
  exact six_impossible3640 run tight (List.all_eq_true.mp sixRows3640_valid s hs) why

def nd9 (i : Nat) : Nat := 0x68401c8080342003ad82075b04000d080002e02688000000c8608000000002c08000000e8209147616f97a3bdbad8633055eaa52a19027c3b9c8da5b2b1449847210f45626108702e05007cd90e5825498154600fa3a1caecb2ae2a8c01e9cd7a61d824c931803e78872c12a4c0a63007db10e565589314860082fe3eb585caca9940186bca65309b8cd818020df9acd6172b9b030061bd2991c2e57360600837e6b3585ca64c0c0105fc7d5712b2a5818020dfb7a4e5545330300417f1f52c2e56a54600b9b26cb04a9302a8c0107f8dc4c2bb2a5518020df9acc625654aa300417f1f53c4aca95460083dea699295d5498c0107bd4d272bb629318030bd96464b0ebd2630041bf3598c2e57a4c60082fe3ea585cab498c0106fd6db318b2a5318020df9acc625654a6300417f1f55c4aca94c600837eb69395db1490c0106fcd6630b9569218020f7a9a4e5769d2430041bf3598c2e53a4860082fe3eb585caca90c0105fc7d6b0b954d218036d8992b1ac498a430041bf5b6cc62ca948600
def nd10 (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0xaee8c66922260600aef16caaa11606008ef96caeda760600ccf8b69dda4606008ef8bc999a460600ce78b6955a460600cbb8ba9118260600fae18258961606008ef96caeda060600ccf8b69dda0606008ef8bc999a0606008ef8c66ad70606008f78c56ad70606008bf8ca62d20606008ef8c66ac59606008ef8c66ac3960600cef0a646c39606008ef8c66ac2960600ceb8a652c29606008ef8c66ac5360600cef0a66c453606008ef8c66ac52606008ef8ac5ac5260600ceb8a652c52606008ef8c66ac3260600caf8a662c3260600ccf8a65ec32606008ef8ac5ac3260600ce78a656c3260600ceb8a652c3260600cef0a66c432606008fb84c4eeaa546008fb94c2ae3354600af994c2ae3354600a7f0c96921154600c6fa662e5a4546008fb9c42e982546008ef8cb5a962546008fb9c42ad4254600cfb0ba9118154600cfd0ba8cd8154600fb61825498154600fc71765957154600fd617254971546008ef96c2ad20546008fb94c2ad20546008ff0ca62d105460085fc7c4aca9546008df87c4aca9546008df87c56eaa4c60087bd4c26eaa4c6008df97c2ae554c600ad797c2ae554c600aed8c662a334c600afc8c25ea334c6008fe8cb5ea224c600afe0c25ea114c6008ef96caed8a4c600ccf8b69dd8a4c6008ef8bc9998a4c600ceb8b69118a4c6008fe92caed7a4c600cbe8b2a217a4c600cee8b29997a4c600cf68b29557a4c600cfa8b29117a4c6008ef8c662d7a4c6008fe8c262d7a4c6008df8cb61d7a4c600cde8b261d7a4c6008fe8c25ed6a4c6008bf88c5ad5a4c6008bf8cb629824c6008df97c2e9824c6008fb94c2e9824c6008ef8cb5a9624c600ced8ba58d624c600cf58ba955324c600cf98ba911324c600bbc98c289324c600bf894c289324c600cdf0ba9dd814c600cf70ba955814c600cfe0ba889814c6008ff0bc569814c600fad18658d814c600fbc1824c9814c6008fb94caeda04c6008ef8c662da04c6008fe8c25eda04c6008df97c2e9804c600ade8c25e9704c6008fd8ca4ed204c6008df97c2ad204c6008ef96c2ad204c60086fcc662ca94c6008ef8c662ca94c600aee8c662a2248600adf07c56a11486008ef96caed8a48600ccf8b69dd8a486008ef8bc9998a48600ce78b69558a48600ceb8b69118a486008ef8c662d7a486008df97caed5a48600c9f87ba215a486008df8bc9dd5a48600ccf87b9995a48600cdb87b9115a48600cdd87b8cd5a486008ef8c662d5a486008df87c5ad5a486008ef8c662d3a486008df87c56d3a48600fce1765897148600cbf0baa213148600cef0ba9993148600cf70ba95531486008ff0cb6293148600fec1635893148600bee16c2c931486008ef8c662da0486008df87c56da0486009fe0cb5c52048600bde17c2c52048600bfc13c2c520486008ef8c662ca948600 else 0x87fcc95ad5a4860087fecc2e55a4860087fd8c2e55a4860087fd7c2e55a4860087fd6c2e55a4860087fd3c2e55a4860087fc8c2e55a4860087fc3c2e55a48600c5fc7b2e55a4860087fc9caed3a4860087fcc962d3a486008efcc662d3a4860087fcc95ed3a4860087fcc95ad3a486008dfc7c56d3a4860087fcc956d3a4860087fd8c2e53a4860087fd7c2e53a4860087fd6c2e53a4860087fd5c2e53a4860087fdac2e5874860087fcac2e5874860087fdac2e5654860087fdac2e5834860087fdac2e5634860087fdac2e5534860087fcac2e5534860087fdac2e5824860097bd4c2e58248600d6ecb95956248600d6ecb958d624860087fcc96e98148600b5f4c961d7148600fce576589714860087fcc96e9514860087fdac2e5514860087fcc96e931486008ff4cb6293148600e7d4396293148600b7d4c958d3148600f7c42958d3148600fec5635893148600b7e4c95893148600f7c4395893148600b7d4c94c9314860087fecc62ca94860087fcc562ca94860087fecc56ca94860087fd8c56ca94860087fc8c56ca94860087fd8c4eca94860087fd5c4eca948600a5fd7c214a948600a6fd6c214a94860087fdcb214a948600a7bdc4214a948600a7ddc3214a948600a7edc2214a948600a7f5c1214a948600a7f9c0214a948600d5ec295ec8548600d6ec295ac854860087fcc96e88548600c7ec296e88548600d7ac296d08548600d7cc296cc854860097ecc96c88548600d7e4296c48548600d7e8296c08548600c5fca95ec8348600d5ec295ec8348600c6fca95ac8348600d6ec295ac8348600c77ca956c8348600d76c2956c8348600c7bca952c8348600d7ac2952c834860087fcc96e88348600c7ec296e8834860097ecc96c88348600c7eca96c88348600c7f4a96c48348600d7e4296c48348600c7f8a96c08348600d7e8296c0834860087fcc96e85348600c7ec296e85348600c7f4a96c45348600d7e4296c45348600afc8c36922260a00ced8b3999a460a008ef8cb6996360a00aed8c36996360a00f8e9875d96260a008df8cb69d7160a008ff0c16ad6060a00c6be6652ca960a00ceba6652ca960a00c7ae2252ca960a00cfaa2252ca960a00cde8ba9dd824ca00f9c9875cd824ca00bdc97c2cd824ca00bfc1c12cd824ca008fb94caeda04ca008ff0c15ada04ca008efacc5aeaa60600aaf96caaa8860600acf96caaa77606008ef8cb69e66606008efacc2ae6660600ccfa772ae6660600ae796caaa5560600ae78ac99a5560600aeb96caaa4460600ecb8a69de4460600aeb8ac99a4460600ee38a69564460600aeb8c669e4460600aed96caaa3360600ecd8a69de3360600aed8ac99a3360600ee98a69123360600aed8c669e3360600aee96caaa2260600aee8ac99a2260600eea8a69122260600eec8a68ce2260600) else (if i < 3 then 0x87fdac2e5654c60097dd2c2e5634c6008bfccb629824c6008dfd7c2e9824c6008fbd4c2e9824c60087fcc92e9824c600c7dc392e9824c60087fdac2e5824c60097bd4c2e5824c60097f51c2e5824c6008efccb5a9624c600c6fcb95a9624c600cedcba58d624c600d6dcb958d624c60087fdac2e5524c60097dcc95ad324c60097dd6c2e5324c60087fcc96e9814c6008ff4bc569814c600e3f489569814c600e7d439569814c600f3d439619814c600fad58658d814c600b7d4c958d814c600b3f4c9609814c600f3d439609814c600fbc5824c9814c600b7d4c94c9814c600f3d4894c9814c600f6d4392d9814c60087fcc96e9514c600cdf97a62d704c600c5fca95ec8a4c600d5dc395ec8a4c60087fc8caeca94c60087fc5caeca94c60087fcbca20a94c60087fcbc954a94c60087fecc62ca94c60087fdc762ca94c60087fdc662ca94c600c3fd8262ca94c600c6fcc662ca94c60087fcc562ca94c60087fecc56ca94c60087fd7c56ca94c60087fd6c56ca94c600c77d5256ca94c60087fc8c56ca94c60087fd8c4aca94c60087fd7c4aca94c60087fd6c4aca94c60087fd5c4aca94c600c5fd7b61ca94c60087fccb61ca94c60087fdcb5d8a94c60087fdcb60ca94c60087fdcb5cca94c60087fdcb54ca94c600c5fd7b5c8a94c600c6fd6b588a94c600a5fc7c548a94c600c7ec2b548a94c60087fdcb604a94c60087fdcb5c4a94c60087fdcb544a94c600a5fd7c214a94c600a6fd6c214a94c60087fdcb214a94c600a7bdc4214a94c600a7ddc3214a94c600a7edc2214a94c600a7f5c1214a94c600a7f9c0214a94c600d5dc395ec854c600d6dc395ac854c60087fcc96e8854c600c7dc396e8854c60097dcc96cc854c600d7cc396c8854c600d7d4396c4854c600d7d8396c0854c600c3fca962ca24c600d3dc3962ca24c600c5fca95eca24c600d5dc395eca24c600c6fca95aca24c600d6dc395aca24c600c77ca956ca24c600d75c3956ca24c600c7f8a96c0a24c600d7d8396c0a24c60087fcc96ac824c60097dcc94ec824c600d7d4396c4824c60087fcc96ac524c600c7dc396ac524c600c6fca95ac524c600d6dc395ac524c60097dcc94ec524c600c7dca94ec524c600c7f4a96c4524c600d7d4396c4524c60087fc8c26eaa4860087fc3c26eaa4860087fdac26e884860087fcac26e884860087fcac26e554860097bd4c26e334860087fcac26e33486008efd6caed8a4860087fc9caed8a4860087fecc2e58a4860087fd7c2e58a4860087fd6c2e58a4860087fd5c2e58a4860087fd3c2e58a4860087fc5c2e58a4860087fc3c2e58a48600c6fcb62e58a4860087fcc962d7a486008efcc662d7a4860087fcc962d6a486008dfd7caed5a4860087fcc962d5a486008efcc662d5a4860087fcc95ed5a486008dfc7c5ad5a48600 else (if i < 4 then 0x87fdac2e53254600f374596198154600b3f4c96098154600f374596098154600fb65825498154600f76429549815460097f57c2e58154600d775522e58154600d6f4b92d98154600f674592d9815460097f4c962d7154600b5f4c961d7154600fc75765957154600b774c95957154600fd65725497154600d774b9549715460097f58c2e57154600c7f930aeca95460087fc3caeca95460087fc2caeca95460087fcbc8cca95460087fecc4eca95460087fd6c4eca95460087fcc24eca95460087fd8c4aca95460087fd7c4aca95460087fd6c4aca95460087fd3c4aca95460087fc8c4aca95460095fc7c4aca954600c5fc7c4aca954600a5fc7c4aca95460087fc3c4aca95460087fdcb5d8a95460087fccb58ca954600a5fc7c688a95460087fccb608a954600c6fd6b588a95460087fccb588a95460087fccb4c8a95460087fdcb604a95460087fdcb208a954600a3fd8c0c8a954600a5fd7c0c8a954600a6fd6c0c8a954600a77d5c0c8a954600a7bd4c0c8a95460087fdcb0c8a954600a7f5c10c8a954600a7f9c00c8a95460087fcc96ac825460097f4c96c48254600d774596c4825460087fcc96ac3254600c77c596ac3254600c7f4196ac3254600d37c5962c3254600d3f41962c3254600d57c595ec3254600d5f4195ec3254600d67c595ac3254600d6f4195ac3254600977cc956c3254600d7741956c3254600d73c5952c3254600d7b41952c325460097f4c96c43254600d774596c43254600d778596c03254600d7f0196c0325460087fcc95eeaa4c60087fcc95aeaa4c6008dfc7c56eaa4c60087fcc956eaa4c60087fcc94aeaa4c60087fd8c26eaa4c60087fd7c26eaa4c60087fd6c26eaa4c60097bd4c26eaa4c600a7bd4c26eaa4c600c7bd4c26eaa4c60087fc8c26eaa4c60087fc5c26eaa4c60087fc2c26eaa4c60087fdac26e884c6008dfd7c2ae554c600c7dc392ae554c60087fcac26e224c60097dc3c26e224c6008efd6caed8a4c60087fc9caed8a4c60087fd7c2e58a4c60087fd6c2e58a4c60087fd5c2e58a4c60087fd2c2e58a4c60087fc5c2e58a4c60087fc2c2e58a4c600c6fcb62e58a4c6008fed2caed7a4c60087fcc962d7a4c6008efcc662d7a4c6008fecc262d7a4c6008dfccb61d7a4c600a5fcc961d7a4c600cdecb261d7a4c60087fecc2e57a4c60087fd8c2e57a4c60087fd6c2e57a4c60087fd5c2e57a4c60087fd2c2e57a4c60087fc8c2e57a4c600c7ecb22e57a4c600c7eca92c97a4c600d7cc392c97a4c60087fcc962d6a4c60087fcc95ed6a4c6008fecc25ed6a4c60087fd8c2e56a4c60087fd7c2e56a4c60087fd5c2e56a4c60087fd2c2e56a4c6008bfc8c5ad5a4c60087fcc95ad5a4c60087fecc2e55a4c60087fd6c2e55a4c60087fd2c2e55a4c60087fc2c2e55a4c60087fdac2e5874c600 else 0x87fcc95eeaa60600c6fcc95aeaa6060087fcc95aeaa60600c6fc595aeaa60600c6fc395aeaa60600c6fc295aeaa6060097f51c26eaa60600c6fd6b26eaa606008efecc2ae666060087fcac26e5560600c6fca626e556060097bd4c26e336060087fcac26e3360600c6fca626e336060087fcac26e226060093fc8c26e2260600c6fca626e22606008efd6caeda76060087fecc2e5a76060087fd6c2e5a76060087fd5c2e5a76060087fd3c2e5a76060087fd2c2e5a76060087fc3c2e5a760600c6fcb62e5a76060087fcc96ad7660600c6fca62e5a56060087fdac2e5656060097f51c2e56560600c6fca62e5a36060087fdac2e5736060097f51c2e57360600c6fca62e5736060087fdac2e5636060097f51c2e56360600c6fca62e5a26060087fdac2e5826060093fd6c2e58260600b3bd4c2e5826060097bd4c2e58260600d3bd4c2e5826060093fcac2e58260600d2fca62e58260600e2fca9299826060093fcc962d6260600b3ecc9609526060087fdac2e53260600c6fca62e53260600b3f4c96096160600fae5825896160600b6f4c9589616060087fecc56ca96060087fd7c56ca96060087fcc356ca96060087fcc256ca96060087fecc4eca96060087fd7c4eca96060087fc5c4eca96060087fcc24eca96060087fecc4aca96060087fd7c4aca96060087fd5c4aca96060087fd3c4aca96060087fc5c4aca96060087fc3c4aca960600a5fc7c548a96060087fdcb14ca960600a7f5c114ca960600a3fd8c148a960600a7bd4c148a96060087fdcb148a960600a7f5c1148a960600a3fd8c0c8a960600a5fd7c0c8a960600a77d5c0c8a960600a7bd4c0c8a96060087fdcb0c8a960600a7f5c10c8a960600a7f9c00c8a960600a6fc9caa8a660600a6fcc969ca66060087fcc96ac5360600c3fc896ac53606008efcc66ac5360600d3f4896c45360600cef4a66c4536060087fcc96ac5260600c3fc896ac52606008efcc66ac526060093fcc962c52606008efcac5ac5260600d3bc8952c5260600cebca652c5260600d3f4896c4526060087fcc96ac3260600c3fc896ac32606008efcc66ac326060093fcc962c3260600cafca662c3260600d1fc895ec3260600ccfca65ec32606008efcac5ac3260600d37c8956c3260600ce7ca656c3260600d3bc8952c3260600cebca652c3260600d3f4896c43260600cef4a66c43260600d3f8896c03260600cef8a66c03260600a77cc9596aa54600a77cc954aaa54600e76c2954aaa5460097bd4c26e335460087fcc95ed6a5460087fecc2e56a5460087fd8c2e56a5460087fd7c2e56a5460087fd3c2e56a5460087fd2c2e56a5460087fc3c2e56a5460087fc2c2e56a5460097facc2e5a45460087fdac2e5635460087fdac2e5825460097bd4c2e582546008efccb5a96254600c6fcb95a96254600))) else (if i < 8 then (if i < 6 then 0xd7dcb95d5634c6008ffcbc569824c600a7fcc9569824c600e7dc39569824c600e9fd7a61d824c600f6dc39595624c600c7fca962d524c600d7dc3962d524c600c7fca95ad524c600d7dc395ad524c600b7dcc958d524c600ef6d5a609524c600afecca609524c600e7eca9609524c600f7cc39609524c600eddd7a61d324c600efcd7a609324c600fbcd87609324c600f7d4395d5814c600fbe582549814c600f7d439549814c600e5fd875d4a94c600e6fd76594a94c600e6fd65588a94c60097fcc95ad5348600f6ec395956248600beed6c54d6248600b7ecc954d6248600f7cc3954d6248600ddf57b61d3148600f7d4396153148600f7d4395953148600fee565589314860087fcc95aeaa60a00c7dc394eeaa60a0087fd6c26eaa60a0097ed2c26eaa60a0087fd2c26eaa60a00c7ed5226eaa60a0087fc1c26eaa60a0087fd7c2e5a660a0087fd5c2e5a660a0087fd3c2e5a660a0087fd1c2e5a660a0087fcc96ad7660a008efccb6996360a00a6fcc96996360a00aedcc36996360a0087fdac2e56360a0097ed2c2e56360a0087fcac2e56360a00f8ed875d96260a008dfccb69d7160a00a5fcc969d7160a00c7ed52aeca960a0087fc1caeca960a00c7bd7b52ca960a00c7bda752ca960a00d3bd8752ca960a00c7bd8752ca960a00c7bd7652ca960a00c7bda152ca960a00c7bd7152ca960a00c7bd6152ca960a00c7bc5152ca960a0087fd6c4eca960a00c7f61146ca960a0087fd7c46ca960a0087fd6c46ca960a00c7bd4b46ca960a00c7f57146ca960a0087fc5c46ca960a0087fdcb5d8a960a00c6fd6b58ca960a00c7bd4b58ca960a00c5fd7b5c4a960a0087fccb5c4a960a00a7ed2c144a960a0087fdcb144a960a00c6fca95aca360a00c7bca952ca360a00c7f4a96c4a360a00c7f8a96c0a360a00c5fca95eca160a00c7bca952ca160a0087fcc96ac5160a0087fcc96ac3160a00c3fca962c3160a00c7eca94ac3160a0087fcc95eeaa4ca0087fcc95aeaa4ca0097bd4c26eaa4ca00a7bd4c26eaa4ca0097dd3c26eaa4ca0087fcac26e554ca0087fd6c2e58a4ca0087fd1c2e58a4ca0087fcc962d6a4ca0087fcc95ed6a4ca0087fecc2e56a4ca0087fd8c2e56a4ca0087fd7c2e56a4ca0087fd5c2e56a4ca0087fd1c2e56a4ca0087fc5c2e56a4ca0087fdac2e5874ca0087fcac2e5874ca0087fdac2e5654ca00b5dcc961d734ca0087fcc96e9824ca00f9cd875cd824ca0087fdc662ca94ca0087fecc56ca94ca0087fd6c56ca94ca0087fd6c46ca94ca00c5fca95ec854ca00c6fca95ac854ca0087fcc96e8854ca00c7dca96cc854ca00c7eca96c8854ca00c7f4a96c4854ca00c7f8a96c0854ca0087fcc96ac814ca00c5fca95ec814ca00c7dca94ec814ca00c7eca94ac814ca0087fcc96ac514ca00c7dca94ec514ca00 else (if i < 7 then 0x44f68979126a224442688090f8a1c8436e86690c4a178429e84f908aa10441e68359062a0b441468249028a034402e8018fee9fc03f5e7e78fc09f703ebe7d38f9e9f2c3e367c28f709ed03d7e7a58f369e5c3c7e78b8f0e9df43bc676b8ece9d8c3aae7518e9a9d243a267408e789ce0399e72f8e569c9c391671e8e229c1037e66f88dd69b7836b66c98d8a9b0435ce6b58d629ab435466a48d409a7034be6938d1e9a2c34366828cfc99e833ae6718cda99a433266608cb89960329e64f8c96991c321663e8c7498d8318e62d8c469864308e60d8c1298082fbe5f38bde97a02f065dc8baa972c2e1e5bf8b7096d02d665a58b36965c2c965888b0896002bc656e8ace958c2ade5548aa0952429f653a8a6c94bc29265208a2c943027f64f489e093b026f64da89ac933c26264b7896092b0253e4a3893e9260249e486890491f823ce46f88d6919022ce45588969104219e4298844905420563fd87ec8fb01f3e3e387b88f601e9e3cf87968f1c1e163be87748ed81d8e3ad87528e941d0639c87308e501c7e38b870e8e0c1bf637a86ec8dc81b6e36986ca8d841ae6352869c8d281a1633b86628ca8192e31b86228c28182e30185fa8be417a62ed85d28b8816ee2d685a48b3816362c2857c8ae815ae2ae85548a98150e29a852c8a48146e289850489f813b627284dc899c12fe25b84a88940125e247848688fc11d6236846488b8114e2258436885c109620e841488000fde1f783e687bc0f561e683be87600e9e1cf8396871c0e161be836886b40cfe19b832e864c0c7618a830c86080bee17982ea85c40b6616882c885800ade15782a6853c0a56146828484f809ce135826284b409461248240847008a61108218841407d60f681e483b8074e0e281bc836806ae0d181948318060e0b7815a82a405260a081388260049e08f8116821c041607e80f481d8038e06d80d28194030605c80b08138024e045808280f401960288048808000c600e80088000beedc65cd6260a00faed8758d6260a0097fcc95ad5a4ca00a7fcc95a95a4ca00f9ed875d9824ca00f9ed87609714ca00c7fda726e336060097fc9caed736060097fcc962d7360600f3ec396095260600ebeda76093260600fbcd73609326060097fcc95ed6354600c7fcb95e96354600e6fc395a96254600b7f4c95cd8154600f3f4396098154600f774395498154600fbe5824c98154600d7f43962d7154600f5f43961d7154600f5f4395d97154600f774395957154600b7f4c958d7154600a7fd7c58ca954600e6fd63588a954600e7ed824c8a954600a7fc9ca217a4c600c7fcb95957a4c600dded872c97a4c600e7dc3961d5a4c600e7dc395d95a4c600c7fd872e55a4c600c7fd762e55a4c60097fc9caed874c600f5dc3961d754c600f6dc395d9654c60097fcc962d734c600 else 0xc10860a54852a43ffc11dd0f70d918e406c881280b40783dc804610a9082284314218a1019086c84364256c1286086c84a1821ee14b6087b852d821b214860a4305218290c10b608430437c290c1086086f8421821b210230843043dc3784904148208490e40872024808c691c148e0a470437c23e81ee2ffe0811842d8210c10670d91143042083a340181b2304a01e0f7181b042d8256c12c5087b852d821ee14b60a5b042d821b214c5086c85314298a14c5085b04314216c10c5087b86c86f0d218290c14860847042f0ed83dc617211259030b60862874683784094082018304a04100c185b06540ca7094bf293a524ca389437282a4f6c9dc93af271a4dac9a49327260a4b8c96092b7252a49cc928922f241a47ac8e491bf230a458c8a09137225a43cc85c909720ea414c80c900f1faa3ecc7c88f6f1e9a3cac7848ee71d8a3a8c7408e771caa38cc7088dd71b9a370c6d08d7f1a8a348c6748cc7194a320c6308c3f183a304c5f88be7172a2dcc5a88b2f161a2bac5648aa714da286c4f089a7130a24cc48888bf110a218c3fc87d70f3a1dec3ac86ef0d3a198c30885bf0aaa140c258842f081a0fac1e483a7067a0c0c17082bf053a09ec12c823703ca064c0b8814f025a042c07480c700ea014c018800effa9fe6bfbc7f3efe39fbebf6c7e9efc99f84bef87d9efaf9f50be847ce6f8f9f16be047b9ef6f9ebebd6c7a9ef4f9e96bd1c7a16f3e9e74bcd8798ef2d9e52bc947906f1c9e30bc507866eff9de4bbb8774eee59dc2bb68767eecb9d8ebaf475c6eb49d60bab0753ee9d9d32ba54746ee839cecb9c87356e639cb8b9487256e439c72b8c8716ee239c38b8547086e0c9c04b7e06f6ede99bc4b7786eb6dcf9b8ab7046dcedb29b5cb69c6d16d9e9b34b6406c5ed879b06b5d86b8ed649ab4b5586a8ed4d9a8cb50869d6d339a58b4a06906d199a24b42c6806cf999e4b3a06706cd999aab3446666cc89982b2f465c6cb4995ab2a46526ca09932b2546486c8c9910b21063fec7598e2b1b46346c6498c0b17062bec53989eb12c6236c3c986ab0c46136c229830b038604ec0597fcafdc5f7ebe597c2af745eaebd19794af185ddebb79766aeb05d3eba3973eae545c3eb8096e0adb05b3eb6096b8ad605a9eb469684acf8599eb2f9656ac8458e6b189622ac345846b049600abf057beaf395deabac5736adc95a4ab2055d6aad9546aa58545ea8494faa9e453a6a6d94d2a9945306a5c94b0a950527ea4b948ea90c51f6a3a946ca8c8516ea299444a86c50b6a0f9410a8044fe69f893e8a7b44f2e9e193baa7644ea69ca938ca7084dee9b0934ca6884cee9969312a6144c0697992d8a5944b0695c92b0a5444a66948927ca4e849969289248a45c489690e920ea40047de8f191daa39846c68d4919aa318460e8b79166a2a4)) else (if i < 9 then 0x1b2048360e0808840383f8bd1c1ea03e403b07c01f1824840dc205603e2fc5043b0001f201484018207607a2fb6e8edd501f200080f882d8210c10df0b8006c8921820921fb607c01f181b840ac07c408760003e305f0d80064829026900542c1c100101f100080f8821820ad60003e3049081580f8b7d015ac0007c81be100101f100681a080dc3f8a07e0e430060d8002200f8ff140f41c8607a05020860efa06c8120c08c2022160e083d82200f8c08420ca07a2086081e077203dc09060781fc503d072181e844dc200203e20df0aaf858382c1c11f4fc5f980b903d2b8d01e881940f44c1c1fc5f9803d1b8d01e8957c2c1c100101f1064840442c1c105f0814840442022104d03d0731824840dc202a02c0de3d0007d01f1814840ac07c40921037080a80b0368c17c3f6da000f803e4049081b841aff160f807c80921011081b85008280414020824840dc278a10060a0705038281c1047d003f403421eae801fa01a100ac07c404613d502d3f403421ef829021814100ac07c408ca007e8068460e0b070400407c4c1c10620b07058382c1c10110b07040442c1c10110b07040442c1c10110b07040542024160e080a84034202a160e080904054201a160e082f8403820ce100908048405c20121fc50f501f181d83e00f8c0340d040921037081581e881ec10c07c6052100e081d81e8800407c416c100101f17db0390180c00407c416c100101f10628400407c401a0682fb607c01f1824840dc3f8a0f403e305f0807040340c040ac0f203e300101f105b0400407c400203e20c5080080f8bed81f007c60921037081580f88112c0015060121fc503f072182258002a0f7d00bac001509f8a07e0e4300908af873201e04860308078103c080080f89c0271436467e9f301b207a400101f109484054211c150e0b8d01e898183f8bf301ee07a403c0a870404830780f803e3029081580f8a1781cc0f460be183c07d01f1831c2f00f8cf7c11f0f00d087e9896068302b01f11ef891e2f01a10f7f1780d067be05a8bc068440901f11efe2f01a0d8182c0c100101f1303058182c0c10580b0305818202a1606080a85818202a1606080a85818202a1606080904054202a1606080a85818202a1606080a85818251c148e08470423823ba1ee1b230820841041e208c4de904626c80788231b644118923821a078a1b230c90922a018491500808c210411b6095c07714378a1ee28b80c7a45c0bff825e85702d980b5b04bd0ae04d6c12b60fff05ad825e857026b6095b07ff825e857026b60b5b04ad8297010f70d9125b043dd08c496c14820c5c07b8b4683dc496c1d1a0f7105b042a4210410b6085b05ad8216c16b6085b05ad8216c10e09a90de1b5b042d82d6c16b608704d006f0dad82d6c16b6084c0408c20461cb8223135c4118808c210 else (if i < 10 then 0x84002c160e0864843247204000068583827aa08e2043095cc0a880142e1c10b90edb04c382192102870400fa07e068330e081b8419c20ce1b000801041242054068205693a069180280f8811c0d0411c1d8e71a0f71847041f2c000a079e80a4203e08ee86cf8d07b90208208e1b22d000801041e246819415c80f12340f63078065137a41183d8e08c1e1f747f8b2340f00ca48216c80571c1083c0220c1c5f55ee1030094a06e1d000824840dc2076a340ca0ae47c503d1014840dc206e102108248412c3a007aa08833d513a03418308418420c21061083084184208c2740683065083284194200204e200102710108401c05c40101012081b8401407c408ce000683047034101b8415ec001cc6092102a034100280f880a43f6dbab63408e40120fe2edc0390c366715c681ec80ca13c5fb60d00d9f1a281b840a80d0406e103708328419420ca106508328419420ca1015080a84054202a1015080a8411c0d0416ee340fa07a404603d0f5034239485c382e0c1067083e00f8bf1438007c60c016b6082b83c8880c1802d6c1060082f85ad821ebbaa03e3049081b840ac07c560008603e302b03fb0001f2007040ec0f4400203e203b03d158003e00f8c5080f4407607a2fb607c01f18a701e89ad820af60003e303e03d101d81e88418226e1b00078065182b89183c0c15c1941106008104403d1030042e40f440ae0882fb607c01f1b5b041100f441bc03e203c080681a08124201c1006082681e8348c124205210060c0602681f80f901243a01f8a07e03e4fc5ef401f181484038278a102b01f101e84030034405603e202b01f1006851d807c58ec03e2c7601f163b00f8bf151d807c68ec03e200101f102603981e8c0ec0f4400203e265f085b0597c2d6c100101f132f842d820d4104303d132f85ad82cbe100101f132f842d820c416b60b2f85ad83f8b1d007a365f0b5b0597c2d6c165f0b5b0597c2d6c17000b8005c0022200ae088300101f101b86c001f007c60921fc507a01f1fe281f8390c038200c102e03d101700f880b80f442420ae0883086081e040b807c4c52102e03d131487f141c80f4660c103d0836826880f42c52103d0b8006c8220c777e603dc0f4800a07a21c8fb6f980d904d2825840f42a34068200e0803040b4209a0580f203e4037080307ed81f007c609210370fe2f5c0390c17c228a103001f11e284038206e102d09e2840b4206e102d0809050a43f8a0f403e32de12201f196f09100f8cbdcb7848807c9f8a71c0f403e42de12201f1fe29c703d00f90b7848807c600203e200101f1004858a4200203e26290b01058a42c0416290b01058a42c04103d0b01058a42c0410090b14858a42c04100102410120220831420020482024034103181208124206e1021080180b8800405c40be102908030419c20f4 else 0xf5087a85c00376c100648648815c4292104703b1387040f8a102e082b85c3820f8170e0b87040e1c170e0b8705c38205c12b9081e8400afb8a20430f80040004606d101e81d885242c1c160e08238028800da1ca200d0b07043242c1c10160b07040582c1c103f0836))))
def hx10 (i : Nat) : Nat := 0x5036e04a00680478a360780010008001209583c0000000000500ec076826608281b40bb0040002028c020001005a83320ad80a20c0038000300c00000000000000000303a80d68012050000000311da0f9018610102c000000040888557484408021
def nd11 (i : Nat) : Nat := (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0x5c5218037f8ad2e290c01f7c61d7148600fbe2ecb8a43007fe1625c5218027fcdd2a290c013fe2e95148600def0b4a8a43005fe8b254521802ff95da6290c01bfcaa93148600f7e51098a43007df2774c521803f793326290c01fdc9553148600ff648898a43007fe2224c521802ff8bda6290c013fe6e93148600dfe31498a43006ff14a4c521803fe8b1a6290c01ff85893148600ffa26498a43006ff0ba4c521802ff85d26290c013fe2e931486009fe97498a43007fd03a4c5218037ec1d26290c01df50e53148600efc85298a43007fe0b24c521802ff45926290c013feaeda048600d7f510d0243006dfa776812180377d3334090c01bde955a048600dfb466d0243006fea22681218037f908b4090c013fe62da0486009ff2f6d0243004ff96b681218027fcadb4090c013fe4eda0486009ff116d0243004ff85b681218027fc1db4090c019fe2e5a0486009ff174c0243007df1715c1218027fc5d2e090c013fe2e95048600ffa26298243004ff8ba4c121802ff55da4090c01bfaaa92048600f7d51090243007dea7748121803f753324090c01fda9552048600ff946690243007fe21148121802ff4b5a4090c01bfa5692048600ffc2e290243007fe13148121803bf454a4090c019fe2a52048600ffc16290243005ff0b1481218033fc54a2090c01afe6288a48600def2b42d243006fd93a0e9218031ff4415290c01afea20a948600dbf4ee54a43006efa662a5218033bf2a95290c01bde954a948600cfbc6654a43006fda332a5218037f51115290c01bfc844a9486008ffb1654a43004ff98b2a5218027fcbd95290c013fe5aca9486008ffab654a43004ff95b2a5218023fe9d95290c013fe4eca9486009ff11654a43004ff85b2a5218027fc1d95290c013fe6ac8948600bf729644a43004ff9ab165218027fcd587290c017fc46c3948600ffa2621ca43006feaaa0a521803df54405290c01fba9982948600fed4aa14a43007fca330a521803ff10885290c017fa5ac2948600dfd2b414a43007fe1310a521802efcbd90a90c017be5ac85486009ff37442a430057f9b921521802fdcda10a90c017f66cc8548600bfd36442a43005ff1b121521802efcbd90690c017be5ac8348600bef2b641a43005fb94b20d218027fcdd10690c015fe6e48348600bfd36441a43005ff1b120d218027fcdd0a690c017fc6c453486009fb166d23050047bd4b2a5828027dca5952c14013fa2e9824ca009df2d755303006cf8a69dd8180277c55cccc0c01b9e29a5560600dd714d22303006ed8a68cd8180377453444c0c013be2d9a7606009df16cd2303004bf8ba6098180277c5b340c0c011fe2e5a4546009fe174c0aa3004ef8b6629318027f4592f498c013f62e9324c6009fe174c0a63004ef8b6629218026fc3dab490c013fc2e93148600 else (if i < 2 then 0x1fe69123348600dfb29519a43006fd85a8cd21803be614c6690c01bfaaaa2248600f7d51111243007eea6688921803fb52ac4490c01fea9122248600dfd31511243006fe96a889218037f4ad44490c01bfa52a2248600dfd275112430057ec9b889218037f44544490c01bfa16a2248600dfd075112430067eca9889218037f95542290c01efca221148600fbe4ef08a43007f725584521803fd92242290c01ff48ce1148600ffc44508a43006ff18a845218037f8bd42290c01bfc56a1148600dfe29508a43006ff08a845218037f82d42290c01bfc0ea1148600cfe95308a430077e429845218027fd5db1490c01afea218a48600dbf4eec5243006efa66629218037bd2ab1490c01bee9118a486009ff368c52430047fcb9629218027fc5cb1490c01bbe2d98a48600bdf16cc5243004efcb6629218027fc5ab1490c013fe2cd8a486009ff576bd243006bfa885e92180377d332f490c01bde9557a48600df7488bd243004ff98b5e9218027fcda2f490c013fe22d7a486008ff972bd243004ff8b95e9218027fc59af490c013feaed6a48600d7f510b5243006dfa775a9218037bd2aad490c01bee9116a48600dfb466b5243004ff98b5a9218027fcbdad490c013fe6d16a486008ff972b5243004ff8b95a9218027fc5aad490c013fe2cd6a486009ff576ad243006bfa88569218036fd3bab490c01bbe9995a48600def4aaad243006fba44569218037ed19ab490c013fe62d5a486009ff2f6ad243004ff96b569218027fcda2b490c013fe22d5a48600dbf0f6ad243005df87b569218026fe3dab490c011ff2e55a486009ff172ad2430067ec29569218027fc59ab490c01afea214a48600dbf4eea5243006efa66529218037bd2aa9490c013fe22d4a486009ff0b6a5243004ffabb4e9218035fd4427490c01b7e9dd3a48600ddf4cc9d243006f7a554e9218037dd2227490c013fe62d3a486009ff2f69d243004ff96b4e9218027fcada7490c013fe52d3a486009ff1169d243004ff85b4e9218023fe5ca7490c013fe2e53a486009ff174c3a43004ff8ba615218027fc5d2ca90c013fe2e984486009ff174aa243004ff8ba60d218027fc5d2e690c013fe2e963486009ff174a9a43004ff8ba609218035fc4530490c017fc2c58248600bfd576b1243006feaaa58921803df5442c490c01f7a9dd6248600fed4aab1243007faa44589218037f4c52c490c01fba5d96248600fdd2cab1243007ee96358921802bf65cac490c017fa2e562486009ff174a9243006f785a54921802ff858aa490c017fc2c542486009ff17499243006fd83a4c921802ff858a6490c013fe6e981486009ff174c0a43006bf88a60521802ff45930290c017fcaed7148600dfe554b8a43007bf2885c521803f79332e290c01fdc9557148600ff6488b8a43007fd233 else 0xb6d0263004ff88b681318027fc2db4098c013fe2c9a04c600f7e302c0263004ff8ba601318036fcbd2e098c013fe2e9704c600ddf2d4b0263007ed963581318027fc5d2a098c017f6aed304c600dfb55498263007bda884c131803eed3ba6098c01fb6999304c600feb4aa98263007fca224c131803fe908a6098c017f65ad304c600dfb2b498263007fd1814c131802fec9da4098c013fe2ad204c600bbf2f645263005fb94b229318035fcc511498c01bde5685a4c6008ffd7654a630063fe882a5318035fd4415298c0197f9dca94c600dbf4ee54a630066fe662a53180377d3315298c019df954a94c600def4aa54a630067de332a5318037ed1995298c019fb888a94c600dfd44454a630067f6112a5318037f90895298c011ff62ca94c6009ff31654a630047fd7b2a5318027fcbd95298c011ff5aca94c6009ff2d654a630047fd5b2a5318027fcad95298c011ff4aca94c6009ff25654a630067f90b2a531803bec9815298c019fe4c0a94c600cff22054a630047fc8b2a5318027fc4595298c011ff16ca94c6009ff0b654a630047fc2b2a5318027fc1595298c013fe6ac894c600bf729644a63005ff11b22531803df8c091298c013fe6ac594c600dfb5541ca63007bda880e531803eed3b87298c01fb6998394c600feb4aa1ca63007fca220e531803fe90887298c017f65ac394c600bfb2561ca63006fd95a0e531803fe8c087298c013fe6ac294c600bf729614a63005fd93b0a531802ff88d85298c0177e5ec854c600bdf2d642a63004ff9ba21531802bfcdc90a98c017ee6d0854c600bfb36642a63005fe9b221531802ff8d890a98c016fe62ca24c600bbf2f651263005ef96b28931802fbcad94498c017ee52ca24c600aff37251263006fe9a2289318027fcd590498c017f64ec824c600bfe36241263004ff9ab14931802f7cb58a498c017ee52c524c600bfb27629263005ff1b1149318035fd4455490c01b7e9deaa48600ddf4cd55243006f7a55aa9218037dd2255490c01bf68ceaa486009ff31755243004ff97baa9218027fcb5d5490c013fe56eaa486009ff29755243004ff93baa9218027fc85d5490c011ff26eaa486009ff11755243004ff85baa9218027fc1dd5490c019fb0a6aa486009ff15744243006bf8aba21218035fc2d51090c01afe0ea8848600e7d853442430079fa889dd218036fc454ee90c01b7e0ea7748600cbf9533ba43007afa8899921803e7d3bccc90c01bbe16a6648600ddf075332430066fca999921803b7614ccc90c01edea225548600faf4ef2aa43007e7a66955218027fc55caa90c01bde2ae5548600def1152aa43006f783a95521803bb614caa90c01eeea224448600fb74ef22243007eba6691121803f9d2ac8890c01bee22a4448600df70b522243007eda668cd21803fad2ac6690c)) else (if i < 5 then (if i < 4 then 0x1803bea1cc2298c01bfc28a114c6009ff576c5263006dfa776293180377d3331498c01bee9118a4c6009ff368c52630047fcb9629318027fc5cb1498c01bbe2d98a4c600bdf16cc5263004efcb6629318027fc5ab1498c013fe2c98a4c6009ff576bd263006bfa885e93180377d332f498c01bde9557a4c600df7488bd263004ff98b5e9318036fcc3af498c013fe6d17a4c6009ff116bd2630047fcb95e9318027fc5caf498c01bfa2c97a4c600bfd164bd263004fecb25e9318027fd5dad498c01b7e9dd6a4c600def4aab5263006fba445a9318027fcc5ad498c013fe5ed6a4c6009ff368b52630047fcb95a9318027fc5cad498c013fe2d56a4c6009ff164b5263004ffabb5693180377d332b498c01bee9115a4c6009ff2d6ad263004ff9b4569318023fe5cab498c013fe2e55a4c600cfb872ad263004ff8b2569318035fd4429498c01b7e9dd4a4c600ddf4cca5263006f7a55529318027fc45a9498c013fe16d4a4c6009ff164a5263004ff8ba61d318027fc5d2ca98c013fe2e9844c6009ff174aa263004ff8ba60d318035fc4530698c017fc2c5834c600bfe162b9a63005fdabb58d318037ed552c698c01f769dd634c600feb4aab1a63007f9a4458d318037ecc52c698c01fb6619634c600fdb2c8b1a630057dcb958d31802fec5cac698c013fe2e9534c600bfe162a9a63006bf98a609318027fc5d30498c01b7e5e9724c600ddf2d4b1263007ed963589318027fc5d2c498c0177e1ed524c6009ff174a9263006fe8a2549318027fc5d28498c017f6aed324c600dfb55499263007dda774c931803f6d3326498c01fd6955324c600ff348899263005fd96b4c9318037ecbd26498c01ff2609324c600ff928499263006fd8ba4c931802fec5d26498c013fe2e9324c6009fb974992630057dcb94c931802fec5ca6498c01ff2289324c600dfd14499263007fd0b14c931802ff858a6498c017fcaed814c600dfe554c0a63007df27760531803f793330298c01fdc955814c600ff6488c0a63007fd23360531803ff11130298c013fe6e9814c600dfe2d4c0a63006ff15a60531803df8c330298c017fc6d1814c600ffa2c6c0a63007bf18260531803fe89930298c01bfc2e9814c600bfe174c0a63004ff8ba605318027fa5d30298c01efc229814c600d7f114c0a630073f48960531803bea1cb0298c01fbc2d9814c600ffa166c0a63005fd8b360531802fec59ae298c013fe6e9514c6009ff174a8a63006f785a54531802fec59aa298c01bfcaa9414c600f7e510a0a63007df27750531803f793328298c01fdc955414c600ffc444a0a63007fd16350531803fe89928298c013feaeda04c600d7f510d0263006dfa776813180377d3334098c01bf68cda04c600dfe422d0263004ff98b681318027fcbdb4098c013fe5ada04c6009ff2 else 0xe999a054600dfb466d02a3004ff96b681518027fc59b40a8c013fe2c9a054600ddf2d4b02a3007e7965581518027fc55a60a8c01fda54920546009ff156902a3005ff2bb441518037f955220a8c01f7c9dd1054600fde4cc882a3007fd23344151802ff8c5a20a8c017fc5ed1054600fee2ca882a3007f7152441518023ff5d952a8c019bf998a954600ddf4cc54aa30067de332a5518037ed19952a8c019fd844a954600dfe42254aa30047fd6b2a5518027fcb5952a8c011ff4eca9546009ff27654aa30047fd2b2a5518027fc95952a8c019fe42ca954600cff26054aa30077f1102a5518033fc88152a8c011ff0eca9546009ff07654aa30047fc2b2a5518027fc15952a8c013fe6ac39546009ff35614aa3005f795b0a551802fdca5852a8c01fda5482954600dfe5540caa3007df27706551803fb92a832a8c01ff48cc1954600bfe3160caa3005ff17b06551803fb8a9032a8c01bf668ca354600bdf2d6512a3005fb94b289518037f4d1144a8c013fe6ac8254600bfe362412a3004ff9ab0c951802dfcc5864a8c0177e5ec3254600bdf2d6192a3005f795b0c951802fdca5864a8c015fe6e43254600bfe362192a3006bfa88aa9318036fd3bd5498c01bbe99aaa4c600def4ab55263006fba44aa9318027fcc5d5498c013fe5eeaa4c6009ff2d755263004ff95baa9318027fca5d5498c013fe4aeaa4c6009ff217552630047fc9baa9318027fc45d5498c013fe16eaa4c6009ff057552630067dc39aa9318035fc2d51098c01cf70e6884c600d7f145442630079fa889dd318036fc454ee98c01d770e6774c600f9f4ef33263006ef85a99931803b6e1cccc98c01bbe28a664c600f6f5112aa63007d7a7795531803f3d334aa98c013fe2ae554c600def1572aa63006f788a95531803bae1ccaa98c01bde28a554c600f7751122263007dba7791131803f5d3348898c01fce956444c600df711522263006fb85a911318037dc5148898c01bf6aaa334c600fbb4ef19a63007eda668cd31803fad2ac6698c01bf662a334c600dfb2f519a63006fd96a8cd318037ecad46698c015f726e334c600dfb11519a63006fd85a8cd318037ec5146698c01bfaaaa224c600f7d51111263007dea7788931803f753344498c01fda956224c600ff548911263007fca33889318037f4bd44498c01bfa5aa224c600dfd2b511263006fe94a88931803fe4b1c4498c01ff24ca224c6009ff15711263006fe8ab88931802fec1dc4498c01ff20ee224c600bfe03711263007fe01b889318037f44544498c01bfa16a224c600ef987311263006ff2aa84531803df94442298c01f7c9de114c600fee4ab08a63007fb24484531803fe919c2298c01ff888a114c600dfe31508a63006ff17a845318037f8ad42298c01bfc52a114c600dfe11508a63006ff05a8453) else (if i < 6 then 0xb03006ff2112a5818023febd952c0c013fe5eca9606009ff2d654b030047fd5b2a5818027fcad952c0c011ff4eca9606009ff27654b030047fd2b2a5818027fc95952c0c013fe16ca9606009ff07654b03004ff82b2a58180377c53152c0c01afeaa88960600f3f4ee44b03007b7a5522581803ded19912c0c01efa8888960600f7e42244b03005bf92b225818027fcd58b2c0c017fc46c5960600ddf14c2cb03004ff9ab0e581802ff88d872c0c01bbe29839606009ff35614b03005bf98b0a581802fdca5852c0c01bbe2982960600ddf55453303007cfa772998180377cd394cc0c019bf2a4a660600def34a52b03006ef8a6295818037ecd1946c0c01bbe298a3606009ff35629b03005ff1b114d8180377c530a6c0c01bfa688a260600ddf14c51303004ff9ab14981802dfcc58a4c0c017be5ac5260600bf729629303005ff1b11498180377c530a4c0c013fe6ac3260600b7f31619303005df97b0c981802f7cb5864c0c017de56c3260600bf7296193030057f9b90c981802ff8d8864c0c01bbe2983260600ddf4cd552a3004ff96baa9518027fca5d54a8c013fe4eeaa546009ff257552a3004ff90baa9518027fc1dd54a8c013fe0aeaa54600cfe833552a3007cfa7799951803b3e2cccca8c01bbe28e6654600ddf145332a3006fbaaa91151803f5d33488a8c01bee5aa4454600df7145222a3006fdaaa8cd51803f6d33466a8c01fe69123354600dfb2d519aa3006fd9a48cd518027fc55c66a8c01bf62ae3354600efa83319aa3006fd8a28cd518037f955422a8c01f7c9de1154600fee4ab08aa3007fb24484551803fe919c22a8c01bfc5ea1154600dfe34908aa3007f715284551802bfa4dc22a8c01bfc22a1154600eee8b308aa3006ff0a3845518037f851422a8c013feaed6a54600dbf4eeb52a3004ff97b5a9518023fe5cad4a8c013fe2e56a546009ff166b52a3004ff8b25a95180377d33348a8c015fe2e5a4546009ff164d22a3004ff9ba591518027fc5d2c6a8c0177e1eda2546009ff174c12a3006ef96a589518027fc5d2c4a8c01bee69142546009ff156a12a3004ff8ab4c951802ff95db02a8c01bfcaa98154600fbe4eec0aa3007ef26660551803fd922302a8c01ff48cd8154600dfe2d4c0aa3007bf18660551803df8c1302a8c01fdc5498154600dfe174c0aa3005ff0ba605518027fc5d302a8c013fd2e98154600f7e114c0aa3006bf88a60551802bfa5cb02a8c017fc2e58154600e7e912c0aa30077745960551803f785b302a8c01fdc2d58154600bef16ac0aa3005ff2bb5c5518037f9552e2a8c01fbc9997154600ff6488b8aa3007fd2335c551802ff8c5ae2a8c01f7c61d7154600fbe2ecb8aa3007f71655c551803ef8b92e2a8c01fdc5497154600afe972b8aa3005ff0b95c5518027fd5db40a8c01bb else 0x9f644c44c0c01fba29a2260600ddd94d11303006fe8a3889818037f955422c0c01efca221160600fbe4ef08b03007f725584581803fd922422c0c01ff48ce1160600ffc44508b03006ff1a7845818037f8d2422c0c019fd2a61160600e7e91308b03006ff0a5845818037f851c22c0c01bfc28a11606009ff576d3b03006bfa8869d818023fe5cb4ec0c013fe2e5a760600ddf16cd3b03005ef8b669d8180277e5b34ec0c013fe2cda760600bfe162c3b03004ffabb699818036fd3bb4cc0c011ff2e5a6606009ff172d3303004ff8b5699818027fc59b4cc0c013fe2c9a660600d7f554c33030079fa77619818027fcd5aecc0c01b7e69d7660600bdf16cd2b03006ef8a66958180377c532eac0c01ebe61965606009ff156b2b03006bfa88691818036fd3bb48c0c01bbe999a460600def4aad2303005ef8b66918180377c53348c0c013fe2d5a4606009ff164d2303005ff0b1611818027fcd5ae8c0c01bbe29974606009ff356b2303006fb9a4591818027fc55aa8c0c01bbe2995460600bdf16cd1b03006ef8a668d818027fc5d306c0c01bf628d8360600bfe162c1b03004ff8ab5cd8180377c532e6c0c01ebe61963606009ff156b1b03006ef8a650d81802f7c5b344c0c01bbe299a260600b7f576c1303006bfaaa60981803cfd3bb04c0c01ebe9998260600f77488c1303006bf9a7609818035fc5d304c0c016fe2e982606009ff174c1303004bfcba609818029fe5cb04c0c016fe2e58260600f5f14cc1303007be8a2609818037f451304c0c01efc2c58260600bfe162c1303006ef8a65c981802dfcc5ac4c0c01efa60962606009ff156b1303007be982549818027fc55aa4c0c0177e1ed52606009ff156a1303006ef8a650981803df4c1264c0c013fe2ad3260600ddf14c99303005bf88b5c5818037f9552c2c0c01f7c9dd6160600fee4aab0b03007fb24458581803fe919ac2c0c01ff88896160600f7e304b0b03007ef162585818027fd5db40c0c01afea21a060600dbf4eed0303006efa66681818033fc5cb40c0c01bbe2d9a060600bdf16cd0303006ef8a6681818027fc5ab40c0c013fe2cda0606009ff164d0303005bfabb601818035fd55300c0c01e7e9dd8060600f5f4ccc0303007bea2260181803df8b0b00c0c01cfe2a58060600cff152c0303007af8a660181803df858b00c0c017fc2c580606009ff356b8303004ff8ab5c18180377c532e0c0c013fe6ad6060600b7f316b0303007ef161581818027fc55aa0c0c01bbe29950606009ff15698303006ef8a64c181802dfcc5a40c0c013fe2ad2060600ddf14c90303005ff0b1481818033fc54a20c0c01afea20a960600cbfcee54b03006dfa772a58180377d33152c0c019df954a960600def4aa54b030067de332a5818037ed19952c0c019fb888a960600dfd44454))) else (if i < 11 then (if i < 9 then (if i < 8 then 0x824ca00dfd2d4c1265007be98760932802ff4da30499401efa60d824ca00ff92e6c1265006fe8ba60932802ff45d304994013fe2e9824ca009fd974c1265007be88a609328035fc4530499401ff22cd824ca00bfb166c1265005fd8b3589328037f55528499401f7a9dd424ca00fdd4cca1265007f6a5550932803fe4b9a84994013fe2e9714ca009ff174a0a65004ffabb681328036fd3bb4099401bbe999a04ca009ff316d0265004ff97b681328027fcb5b40994013fe22da04ca009ff0b6d02650067f8b9681328027fc58b40994013fe2e9804ca00fbb2e6b8265004ff8ba5c1328027fc5d2c0994013fe2e9504ca00cff15298265005fd83b481328033fc54a40994013fe2ad104ca00d7f31445265006f795a169328036fd3b952994019bf998a94ca00ddf4cc54a6500677e552a5328037bd2a95299401bf68cca94ca00dfd44454a650047fd8b2a5328027fcc5952994013fe5eca94ca008ffad654a65004ff96b2a5328023fead952994013fe56ca94ca008ffa3654a65004ff91b2a5328027fc45952994013fe16ca94ca009ff03654a65004ff9ab22532802fdca5912994017fa4ac894ca009ff3562ca65004ff9ab06532802fec9d8329940177e5ec854ca00bdf2d642a65004ff9ba21532802bfcdc90a994017ee6d0854ca00bfb36642a65005fe9b221532802ff8d890a99401bfc684a14ca009ff35640a65005df97b20532802fdca5902994017f64ec814ca00bfd25640a65004ff9ab14532802fec9d8a2994013fe5eeaa60600bdf2d755303004ff96baa98180277eb5d54c0c01bbe5aeaa606009ff2b755303004ff94baa9818027fc9dd54c0c013fe4aeaa606009ff21755303004ff85baa9818027fc1dd54c0c013fe0aeaa60600c7f91355303006bfaaaa21818029fe4dd10c0c018ff2a68860600d7f14b44303006bf8a3a21818035fc51510c0c01b7eaaa7760600f3f5113bb030071fc899dd8180367e534eec0c01b7e28e7760600ddf55533303007cfa779998180377cd3cccc0c017be2ae66606009df957333030066fca99998180377c52cccc0c01bbe28e6660600ddf14533303006f7aaa95581803f3d334aac0c01bde69a5560600e6f9132ab03007e78a69558180373e534aac0c01bde28a5560600df755522303007bba8891181803edd3bc88c0c01fae99a4460600fe74ab22303006fb9a7911818037dcd3488c0c01eee61a4460600fd714d22303006fb8a5911818037dc51488c0c01bf6aaa3360600fbb4ef19b03007eda668cd81803fcd22466c0c01bf669e3360600dfb34d19b03006fd9a48cd818039ee44c66c0c01fb629a3360600ddb94d19b03006fd8a28cd818037f555444c0c01efaa222260600fdd4cd11303007faa4488981803fe519c44c0c01bfa69a2260600f7d30d11303006fe9a488981803 else 0x5bf88b50982802f7c5b342c1401b7e69d7160a00f3f30eb8b05004ff8ab5c582803f74b12c2c1401bee6914160a009ff156a0b05004ffabb6818280377d33340c1401bfa889a060a009ff166d0305004ff8b1681828027fcd5ac0c14013fe2ad6060a009ff15698305006fd8a34c182802dfc45a40c14013fe2ad1060a008ffd7654b050066fe662a58280377d33152c14019fb888a960a00dfd44454b050047fd6b2a5828027fcb5952c14015ef52ca960a00bf729654b050067bd4b2a5828037dca5952c14011ff4eca960a009ff27654b050047fd1b2a5828027fc8d952c14019fe42ca960a00cff24054b050047fc3b2a5828027fc1d952c14011ff06ca960a009ff03654b05004ff9ab0e582802ff495872c14013fe6ac1960a00b7f3160cb05005ef96b28d82802fdca5946c14015fe6e4a360a00dfb34651b05005ff1b128d82802efcbd942c14017ee52ca160a00dfe34250b05004ff9ab14582802ff4958a2c14013fe6ac3160a00b7f31618b05005fe92b0c5828036fd3bd5499401bbe99aaa4ca00def4ab55265006fba44aa9328027fcc5d54994013fe5eeaa4ca009ff2d755265004ff95baa9328027fca5d54994013fe46eaa4ca009ff21755265004ff88baa9328027fc2dd54994013fe06eaa4ca00dbf1153ba650065fca99dd328036fc50cee99401f3e9de664ca00ddf0b533265007e7a66955328037bc50caa99401f6e9de444ca00fd74cd22265007f3a55911328037dc4548899401bee16a444ca00df714322265006fdaaa8cd32803eed3bc6699401fb699a334ca00dfb2f519a65006fd96a8cd328037ec4546699401bf616a334ca00cfb95319a65006fd8a18cd328037f55544499401fba99a224ca00fed4ab11265007faa4488932803fe519c4499401bfa5aa224ca00dfd29511265006fe88a889328037f42d444994019fb2a6224ca00dfd14311265004ffabb6293280377d3331499401bee9118a4ca009ff368c52650047fcb9629328027fc5cb14994013fe2c58a4ca009ff576bd265006efa665e9328037dd222f4994013fe6d17a4ca009ff116bd2650047fcb95e9328027fc5caf4994013fe2c57a4ca009ff576b5265006dfa775a9328037bd2aad499401bee9116a4ca009ff316b5265004ff97b5a9328027fcda2d4994011ff2e56a4ca009ff172b5265004ff8b55a932802efc3dab499401b7e9dd4a4ca00ddf4cca5265006f7a55529328027fc45a94994013fe16d4a4ca009ff162a5265004ff8ba61d328027fc5d2ca994013fe2e9844ca009ff174aa265004ff8ba60d32802ff459306994017f6aed734ca00dfb554b9a65007eda665cd32803fcd222e699401f7661d734ca00fbb2e8b9a65005fe8b258d32802ff55db0499401bfaaa9824ca00fbd4eec1265007eea6660932803fd522304994013fe6e9) else (if i < 10 then 0xda7490c013ff22d3a486009ff8b69d2430067fcb94e921802bfe5ca7490c019ff2a53a48600cff9129d2430067fc594e921803bf614a7490c013ff2e98748600aff972c3a430067fca961d218033fe54b0c90c01dfb0a586486009ff974c2a430077ec29615218033fe54aea90c013ff2e96548600aff972b2a430067fca959521803bf614aca90c017fe62d5448600ff7308aa243004ffcba60d21802bfe5cb0690c01dfb0a583486009ff974b9a430057fcb95cd218033fe54ae690c013ff2e96348600aff972b1a430067fca958d21803bf614ac690c013ff2e95348600aff972a9a430077dc3954d21803bf614aa690c015ff2e58248600cff952c1243006fed8a58921803f76bb2c490c01fbb5956248600fddac6b12430077ec5958921803bf61cac490c015ff2e55248600cff952a92430057fcb94c9218033fe54a6490c013ff6e98148600aff972c0a430067fca9605218039fe44b0290c01dfb0a58148600dfeab4b8a43007df5875c521803efabb2e290c01ff95897148600efe912b8a430077f4395c5218027fedd2a290c015ff2e55148600cff952a8a4300777c5954521803bf614aa290c017fd5ed31486009ffb7498a43006ff58a4c521803feab1a6290c01ff95893148600ffaa6498a43006ff4ba4c521803bfa5ca6290c015ff2e53148600efe95298a430067fca94c521803bfa44a6290c01dfd1653148600efb87298a430077ec294c5218033ff4415290c019ff954a948600cffb0a54a430067fd832a5218033fea995290c019ff214a948600bbfaf642a43005efd6b215218027fedd10a90c017ef6d08548600bfbb6642a43005fedb221521802ffad890a90c017fe6c08548600efd85242a43005dfd7b20d21802f7eb590690c017df56c8348600bf7a9641a43004ffdba20d21802ff6d910690c017fd6c48348600bff36041a430067fca920d21803bf61490690c013ff6e85348600bfeb6229a430067fca914d21803bf6148a690c013fe5aeaa60a009ff29755305004ff93baa9828027fc8dd54c14013fe42eaa60a008ff93755305004ff83baa9828027fc0dd54c1401bbeaaa6660a00f9f4ef33305006ef9a79998280377c52cccc1401bbe28e6660a00df755522305007eba66911828037dcd3488c1401bee2864460a00dfd55511305007bea8888982803f7533444c1401fea9122260a00dfd34d11305006fe9a4889828037f452c44c1401bfa28e2260a00dfd14311305004ffabb699828023fe5cb4cc14013fe2e5a660a009ff16ad3305004ff8b3699828027fcd5aecc1401bbe999a460a00bfb166d2305004ff8b1691828027fcd5ac8c1401bbe6996360a009ff156b1b05006fb9a450d82802ff55dac4c1401bfaaa96260a00fbd4eeb1305007faa4458982803df4c3ac4c1401fba5d96260a00fdd2c6b13050 else 0x6009ff974992630077dcb94c931802bfe5ca6498c01df72a5324c600cff952992630077dc894c931803bee2ca6498c013ff6e9814c600dfead4c0a63006ff55a60531803dfac330298c01ff558d814c600f7eb04c0a63007fd532605318037fa5d30298c017fd2e9814c6009ff974c0a630077f4b960531802bfe5cb0298c01cff225814c600efe8b2c0a630077dc3960531803bfa14b0298c01fbd2d9814c600aff972b8a630077dc395c5318027fedd2a298c015ff2e5514c600eef8b2a8a630077dc39545318037fcbd30098c017fe62d704c600ffe302b8263007fd9874c131802efebd91498c017ef52c8a4c600cff952452630077dc39229318033fe548b498c01df70e45a4c600cffd1054a630067fe552a531802bfec595298c019ff62ca94c600affaf654a630067fd7b2a531802bfead95298c019ff56ca94c600cffb1454a630067fd7a2a5318033fead15298c019ff61ca94c600cffb0c54a630067fd762a5318033feba95298c019ff594a94c600cffb0654a630067fd732a5318033fea995298c019ff608a94c600cffae454a630067fd622a5318033fea915298c01dfd604a94c600cffb0254a630067fd712a5318033fea895298c019ff214a94c600bbfaf642a63005efd6b215318027fedd10a98c017ef6d0854c600bfbb6642a63005fedb221531802ffad890a98c017fe6c0854c600efb87242a63005bfd8b28931802efebd94498c017bf5aca24c600befab651263005fbd4b28931802ffcd814498c019ff2a4a24c600efb87251263004ffdab20931802fee9d90498c017fd6c4824c600cff952412630077dc39209318027fed58a498c017bf5ac524c600bf7a9629263005fdd3b14931802ffad88a498c019ff2a4524c600efb87229263004ffc8baa9218027fe2dd5490c013ff0eeaa48600cff913552430067fc59aa9218033fe1cd5490c013ff2ae8848600aff937442430077ec29a21218027fe55caa90c015ff26e5548600efd8532aa43004ffcab8cd21802bfe4dc6690c017fd06e33486009ffd76c52430067fcb962921802bfe5cb1490c019ff2a58a48600cff8b2c52430067fc3962921803bf614b1490c01bbf2d98a48600bdf96cc5243004ffcb5629218027fe59b1490c013ffaed7a486009ffb16bd243004ffc8b5e9218033fe44af490c019ff0e57a486009ff966bd243004ffebb5a9218027fec5ad490c013ff5ed6a48600cff8b2b52430067fc395a9218027fe5aad490c013ff2cd6a486009ffd76ad243004ffd8b569218027febdab490c013ff5ad5a486009ff916ad243006dfc7b56921802efe3dab490c019ff2e55a48600aff972ad2430067fca9569218033fe44ab490c019ff0e55a48600efd852ad243004ffcb3569218027ff5da7490c013ff62d3a486009ffaf69d243004ffd6b4e9218027fea)) else (if i < 13 then (if i < 12 then 0x58b5c551803efac3ae2a8c01f7d5d97154600feeacab8aa3007df5725c551803fbaa92e2a8c01dfd2e57154600aff972b8aa30077f4895c551803bfa1cae2a8c019ff8cca954600affad654aa30067fd6b2a551802bfe9d952a8c019ff4eca954600affa5654aa30067fd2b2a5518033feb5152a8c019ff5d8a954600cffb4654aa30067fd632a5518033fed1152a8c019ff608a954600cffae454aa30067fd622a5518033fe99152a8c01dfd604a954600cffb0254aa30077f5712a5518033feb8952a8c019ff208a954600cff86454aa3004ffdab20951802ffad8904a8c01dfd06482546009ffb56192a3005bfd8b0c951802efebd864a8c017bf5ac3254600befab6192a3005fbd4b0c951802ffad8864a8c017fe6c03254600eef8b2192a30077f4190c9518027fec5d5498c013ff5eeaa4c6009ffad755263004ffd5baa9318027fe95d5498c015ff26eaa4c600cff93755263004ffc8baa9318027fe2dd5498c013ff0aeaa4c600cff953552630067fc89aa9318033fe2cd5498c01df70e6aa4c600cff853552630057fc9ba2131802ffa0dd1098c013ff2ae554c600aff9372aa630077dc39955318027fe55c4498c015ff26e224c600bfb87711263005ff41b889318033fe54c4498c01df70e6224c6009ffd76c52630067fcb962931802bfe5cb1498c019ff1658a4c600efb872c52630067fc296293180377e5b31498c017bf2d98a4c6009ff96ac5263004ffcb2629318027ff5daf498c013ff62d7a4c600dbfb0ebd263004ffc8b5e9318033fe5caf498c015ff2e57a4c600cff912bd2630077dc395e9318037f6592f498c017fb2c97a4c6009ffd76b5263004ffd8b5a9318027febdad498c019ff2e56a4c600aff972b52630067fca95a9318033fe2cad498c01df70e56a4c600cff852b5263004ffcb55a9318027fe592d498c013ffaed5a4c6009ffad6ad2630067fcb956931802bfe5cab498c01df70e55a4c600cff852ad263004ffcb2569318027fe5d30e98c015ff2e5874c600efb872c3a630077dc3961931803bee1caec98c01df70e5754c6009ff974b2a630057fcb959531803bee1caca98c013ff2e9834c600aff972c1a630057fcb95cd318037eec52c698c01fb7619634c600efb972b1a630057fcb958d31803bee54ac698c019ff2a5634c600efb8b2b1a630077dc2958d318027fe5d2a698c015ff2e5a24c600cff952d12630077dc39689318035fec530498c013ff2e9824c600aff972c12630077dc39609318036febd2e498c01df70e5724c600ddfad4b1263007edd63589318027fe5d2c498c015ff2e5624c600efb872b1263005dfc7b549318027fe5d2a498c015ff2e5524c600efb872a92630077ec29549318037f6512a498c017f75ad324c600dfbaf499263007fcd824c9318037ee5d26498c017f72e9324c else 0xc0c017bf2d9a360600ddf94cd1b03004ffcba60d81802bfe5cb06c0c019ff2a583606009ff956b9b030057fcb95cd818039fe44ae6c0c01bbf2997360600f5fb0cb1b03004ffcab58d81802bfe5cac6c0c015ff2e5a260600cff952d13030073fc8968981802f7e5b344c0c01bbf299a260600d7fb4ec1303007bf954609818035fe5d304c0c016ff2e982606009ff974c13030073fcb960981802bfe5cb04c0c01cff2a58260600cff952c13030073fc59609818039fe1cb04c0c01ebf2998260600e7f912b9303006efca65c981802dfec5ac4c0c01efb60962606009ff956b13030057fcb958981803df6c12a4c0c013ff2ad5260600bbf8f6a93030077ec2954981802ffcada84c0c01fee5514260600f7db0499303004ffcab4c981802bfe5ca64c0c01cff2253260600ddf94c993030057fcb95c5818033fe54ae2c0c01cff2257160600f7eb04b0b03007ef56258581803bfa2cac2c0c01dfd0e56160600efe852b0b03007bf97360181803efcb9ae0c0c017fe5ed3060600dff34e983030067fe552a5818033ff19952c0c019ff888a960600cffaea54b030067fd732a5818033feb9152c0c019ff548a960600cffa6454b030067fc532a5818033fe29152c0c019ff0c8a960600ddfd5453303006efda729981803b7e2c94cc0c01dbf0e4a660600edf85253303006efca62958180377e53146c0c013ff6ac5360600bfeb6229b030073fc8914d8180377e530a6c0c01bbf298a2606009ffb5629303005bfd8b14981802f7eb58a4c0c017ef52c5260600bfeb62293030073fc891498180377e530a4c0c013ff6ac3260600b7fb1619303005dfd7b0c981802f7eb5864c0c017df56c3260600bf7a9619303005ff5b10c981802ffcd8064c0c01cff2243260600ddf94c19303006f7d65aa9518037bea9554a8c013ff0eeaa546009ff857552a30067fc39aa9518033fe14d54a8c013ff2ae3354600aff93719aa30077f4198cd518027ff5dad4a8c013ff5ed6a54600cff972b52a30057fcb95a951803bbe2cad4a8c019ff0e56a54600cff852b52a3004ffcb35a9518027fe592d4a8c015ff2e5a354600efb872d1aa30077f41968d518027fe5d2c6a8c015ff2e56354600eef8b2b1aa3005dfc7b68951802bfe5cb44a8c01ddf165a254600efd852d12a30077f419689518037fcd2304a8c013ff2e98254600aff972c12a30077f41960951803bfa0cae4a8c01bbf5a962546009ff974b12a30057fcb958951803bbe2cac4a8c017fe62d42546009ff956992a30057fcb94c951803bbe2ca64a8c01dfd0653254600dfead4c0aa3007bf58660551803dfac1302a8c01fdd5498154600ffe284c0aa3006ff4ba60551803bfa5cb02a8c015ff2e58154600e7f912c0aa300777c5960551803bfa1cb02a8c01dfd0a58154600fde96cc0aa3005ff) else (if i < 14 then 0xffb1755265004ffd7baa9328027feb5d54994013ff56eaa4ca009ffa37552650057fc9baa9328033fe4dd54994013ff22eaa4ca009ff8b755265004ffc1baa9328033fe44d54994019ff166aa4ca00cff833552650057fc9b955328027ff5db14994019ff2e58a4ca00aff972c52650067fca9629328033fe0cb14994013ff2c58a4ca009ffd76bd265004ffc8b5e9328033fe44af4994019ff0657a4ca009ff962bd265004ffebb5a9328027fec5ad4994013ff5ed6a4ca00cff972b52650057fcb95a9328033fe54ad4994019ff1656a4ca009ff96ab5265005dfc7b56932802bfe5cab4994019ff2a55a4ca009ff974c3a650057fcb961d328033fe54b0e994019ff2a5764ca00cff952baa65004ffcba59532802bfe5caca994013ff2e9834ca00cff952c1a65007ddd875cd32803bee44ae699401df7065734ca00aff972b1a650067fca958d328027fedd30499401bfb5a9824ca00f7db0ec1265007bed8360932803fe6b9b0499401bfb2e9824ca00bfd974c1265004ffcba60932803bf65cb04994015ff2e5824ca00efd952c12650067fca960932803bf62cb0499401dfb065824ca00aff972b12650067fca958932802fee59ac4994015ff2e5a14ca00cff952d0a65004ffcba5c532802bfe5cae2994019ff2a5714ca00fdf2cab02650067fe552a5328033fec3152994019ff594a94ca00cffac254a65005dfd7b21532802f7eb590a994013ff6e8854ca00bf7b6842a65005fddb321532802ff6d910a994017fd6c4854ca00bff36042a650067fca9215328027fed59029940177f5ec814ca00bf7a9640a65005fdd3b20532802ff695902994019ff2a4814ca009ffb5628a65005fdd3b145328033fe548a2994013ff5eeaa60600bdfad755303004ffd6baa98180377eb5d54c0c013ff56eaa606009ffa7755303004ffd2baa981802bfe4dd54c0c019ff26eaa606009ff8b755303004ffc3baa9818027fe15d54c0c019ff166aa60600cff873553030067fc29aa981802bfe4dcaac0c017fd06e5560600ddf94d2ab030057fc9b8cd81802ffa0dc66c0c01bbf29a3360600aff93711303005bfc8b8898180377e53444c0c013ffaeda760600cff972d3b030057fcb969d818033fe54b4ec0c01cff225a760600cff872d3b03006efcb669d81802f7e5b34ec0c013ff2cda760600aff972c3b030067fca961d818027ff5db4cc0c019ff165a660600cff872d33030067fc29699818027fe5ab4cc0c013ff2cda6606009ff964d33030073fc59619818039fe1cb0cc0c01cff0a586606009ffb56bb303006dfda75d981802bfe5cb4ac0c019ff2a5a560600e7f912d2b03005efcb66958180377e5334ac0c01cff2257560600ddf94cbab03007afd86595818027fe55acac0c015ff2e56560600aff972d1b030067fca968d818039fe44b46 else 0xd932802fff5daca99401fbf619654ca00fdfaecb2a65007fdd865cd32803feeb2ae699401ffb5d9824ca00ffdacac1265007efd6558932803efec3ae299401ffb609714ca00dffb4f19b030077fc395d5818037fed3b06c0c017ffaed7360600dffd54b9b03005ffd8b5cd81803efec3ae6c0c017ff6d97360600f7fb0cb9b03007efca65cd818037fed3ac6c0c01eff5cd8260600fbfae6b93030077fc39549818037fed3a64c0c01ff75cd3260600ffeae6b0b030077fc395d951802ffebdac6a8c01bff5e96354600eff872c12a3007efd6358951803bfe1cac4a8c01bff5a93254600ffdb04992a3007ff57360551803ffa99302a8c01ffd60d7154600ffeac6b8aa3006ffd87aa9318037fec3b1498c01bffa217a4c600fbfb0ebd263006ffd865e9318037feb2af498c01bff61d6a4c600dffaeab5263006ffd87569318037febb2b498c017ffaed874c600fbfb0ebb263007dfd875d531803f7ebb2ca98c01bff5e9834c600bffb16b9a63006ffd8a5cd31803efec3ae698c01ff761d634c600ffbaeab1a63006ffd7a609318037fead30498c01eff61d824c600bffb16b9263007efd6558931802ffec5aa498c017ff5ad524c600dffad4a9263007fdd6354931803ff6c12a498c01ff761d324c600ffbaca99263007ff58760531803ffabb30298c01ffd5d5814c600ffeae6c0a63007ff55260531803efec3ae298c01dff0e58548600eff872b2a43007dfd875cd21802ffeb5aa690c01ff760d5348600ffdaa6b1243007ff5835c521803ffac3a6290c01ffd6153148600ffeaca98a43004ffd6baa9828027fe9dd54c14013ff46eaa60a00d7fb0f55305006fed52aa982802bfe4dd54c14019ff26eaa60a009ff87755305004ffc1baa9828033fe54d54c14019ff0e6aa60a00cff83355305004ffebb699828033fe5cb4cc14015ff2e5a660a00cff8b2d33050067fc39699828027fe5ab4cc14013ff2cda660a009ffb56bb3050057fcb968d828033fe54b46c1401bbf6996360a009ff956b1b050057fcb958d82803df6c3ac4c1401fbb5d96260a00fddac6b13050077ecb958982802bfe5cac4c1401dfb1656260a00efd872b13050057fcb968582802f7e5b342c1401b7f69d7160a00f3fb0eb8b05004ffcab5c582802bfe5cae2c1401fbb5896160a00dff34aa0b050057fd7b2a5828033febd952c14015ff46ca960a00cffa3654b050067fda72a5828039fec3952c14019ff61ca960a00cffaec54b050067fd632a5828033fed0952c14019ff5c4a960a00cffac254b050067fc512a582802f7eb5946c14017ef52ca360a00bfeb6251b05005ff9b028d828033fe54946c140177f5eca160a00bf7a9650b050067fca9285828027fed58a2c14017fb4ac5160a009ffb5618b05005bfd8b0c582802ff695862c14019ff2a43160a009)))) else (if i < 22 then (if i < 18 then (if i < 16 then 0xcf1e5a0f26478fc3c581e240f0b477f83bcb1dcd0edfc769c3b1d1d7b8eb7075823a9b1d400e96874523a031cf98e78c734e39811cad8e47c71c638c81c510e1f070ac38301c050dfbc6f9237ae1bbe8dc806df436ea1b620dad06d1c363c1b0b0d7946b7e35991ab98d5346a6435221a890d40869e434e21a690d2b0690c34551a178d02467dc33d319dc0ce746704336719a60ccc4662c32fb19700cae86528326319190c7d86374317e18b70c520621830d0184a0c18c60642ff617e28be7c5f1e2f7f17ac8bca05dee2ec6173f8b9385c3a2dec16d80b6285ac82d28167b8b2ec592a2c6416198b03457fa2bd715de0ad7c569e2b3f15978ac7c55f22ad315618aacc55462a7215310a94854842a1114fb0a79853ac29c614db0a5bc527c290d14738a304516228a114488a154503227e813d609e704f182750138489b604d9026b8135409a084ca226361302897504b5c259312b68951c4a4224fb12758936c499624bb124a891904892241811f908f04474c238011b288cfc46322309117c88ba445b222c9114c089c84482221010ef886b8433c214c1093083d441ca20d51062882d4413420691027080a03fd81fc60fdb07e983f2c1f7b0fb587d403e541f0f0f6f07ab43ce21e4b0f12878543c0a1dea0eed077283b321d680e9b8741839c01caf0e398710838381bf60df306f58374a1b950dc286ccc361a1afd0d7686b1c352c1a650d1f868bc343e19ee0cde8663032b6192a0c7c863203144187c0c25860ec3056181b0bf505f102f3c17780ba905cb02e3816f60b6285a7c2d0816740b32059502c7216290b07057cc2bc615d30adc056742aee15510aa0854982a2c15060a7b0539829ac14c60a5b0521428ea14650a2a850e82854141a09ff84f9027a813c409d484e0c26d01358099384c5c260e12f7096304a5424de12490911847f423ae11a608c584568227e112f088a043b8219010b80854042602110106d082e84134207a1022080903fb01f8c0f9507b783d241e300ef2076b83ac41d160e65071f838641c120df906f4837641b7c0d8d06b9035881a620d21067d8338019740c8906370312018440c0705f602f4417400b7a05b502d6816680b24058a02c1015e80ad9055982a3414e40a5705188282c13ca09b404cc825f8129a0932048602398116a089a043482138107c082e040f01fe00f78079603b281cd00e3206fe037181b200d5a0692033b819440c6c061002ea016600ab8054c028281324091a0451020500f3807240356018d00c28059c0292013080894042a01ef00df006b802fa016d0098804840222010100788038401a200c100588020000e0006000280010000600020000800002ffebdac6c1401bff69d6360a00dffb4ab1b05007fed73589828037feb2d54994017ff5ad5a4ca00dffad4ad265007dfd875 else (if i < 17 then 0x6900147ffa3ff51ff3cff527f6d3fa91fcb0fe0c7ee03f579fa24fcc67e483f1c1f848fbd87da53eba1f4e0fa0e7cd63e529f254f90a7c753e2d1f0fcf8487c093df71ef4cf7707b923db61ececf6567afa3d6a1eb10f53c7a783d1e1e8b0f40c79bf3cbc1e5a0f29a791c3c809e340f13e786e3c2f1e10cf02477e13bd81ddfcee7077073b7b9db18ed1476593b141d7dceb8c75b63ac29d5d4ea8875133a819d348e94274703a301d140e880740439fa1cf90e7a873a339b91cd04e66272f5395c9ca20e498723c39109c7c0e3c071d038cf9c5b8e290712238789c300e134706938271c0f8e05c701e38071bfa0df426f7b379a1bc38ddfc6eee375e9ba30dcf86e6c37289b904dc626e1636f81b780db8a6daa36bc9b520da5a6d0736709b2ecd9406c85363a9b194d8aa6c45361a9b094d8146bfa35df1ae60d7106b7835a91acdcd64e6b0c35731ab58d5766aab35481a9d4d4b46a3f35121a824d39a69b234c09a56cd2546904347a1a390d19268ae344f1a1b4d0786821340319f80cfa0679f33c219d78ce9c6728336b19ac0cd146659331419834cbe465e232de195a8ca8864f23266192c4c9166470322a99114c86a6425320a98f90c77c638d31a898cacc60a62df315718a4cc4c462313105987c0c39461a430c49858cc26460f6305d181f8c06e5ffb2fdf97ebcbee65f2c2f7297aa4bcda5e3c2f0017768bb525d6d2eae97484b9e05c882e3c171a0b8b05c482e1c170a0b8305bc62ddb16e98b6be5b4f2d9f96cbcb5d05aac2d3d96954b45e5a1f2d07967fcb39c59872cab16468b21458fa2c75162e4b0e458362c0295f50af1a57512b9015c14adea56e52b6a95a64aca456162af295678aada553c2a8595368a95254782a34150dca82253eb29ed94f00a760539529c294dd4a6ca5334297c14ac4a500525a2914947e0a3a4519628b814528a274512a288d14428a1b2509d2836140eca0564fce27d413ddc9ece4f5727a393cdc9e224ed52747139749c2c4df026ea937149b6a4d63269913404998a4cb5264793120982e4be625e012e6897144b43258e92c3495fa4acc254d929a894724a2924eb926c49342499124b01249091e648cd245e922b4913a4856241812054900a47f523f291f548f8a47aa23c791dfc8ede475f23a211ca48e0646c7235b91a9c8d2e467c231a918688bfe45ef22e4916e48b3c458e22b9915088a2244eb2268112a8890844692227110f888464413220190fcc87c643a721c610d9886ac433b219590be8859242a3213e9095c8462420b20f2906a4831c417320ac10520825a411d2086903f481da40dd2066902c881444092204110144806c4026200b0ff947faa3fc51fda8fe687efe3f641fa48fcb87e263ef81f6e8fab07d0c3e4a1f120f7f87b843d9c1ebb0f5407a543d1a1e850f3e879be3c else 0x3606bb031d8142c07b6025300657fd0bfc25fd92fe897f24bf6c5f9dafc297df4beea5f622fa4d7cc4be525f212f89d7becbde65ee5af6c17b40bd905ebaaf5697a94bd3a5e952f43d79e8bcce5e59af28d7926bc6d5e1e2f02d77f6bbeb5de2aeed5774abb955dc2aedd5765cbb135d712eac57500ba705d252e80d73a4b98b5cad2e4a57206b8b15c45ae1957068b8245c0a2e0116fe8b7c35bc92ddb16e76b70a5b6cadb256d72b6885b262d8416c00b5da5ad4ad5e16a8eb5165a72ad27968aeb4265a002cf3d6752b38359b9acd35664eb3175983acbdd65ceb2d75963aca0164e0b21e59072c7496316b14f589fac4bd623eb0f95869ac23160ccb01f5807abffd5fdeafdf57dcabdc95e6caf05576faba8d5cfaae6d572eab9355c7aae0c56edab6a95b34ad6956a1ab4cd5a30acd1564aab21558eaac6556252b0e9583eabd855ce2ad55565eab09557caaac95502aa715530aa8c153e8a9ce54df2a6b9533ca97854a92a4b15238a90c547e2a38551a2a8c15458aa22d50caa855541229fcd4f9aa7b253cba9d994e96a730539029be94da8a6c4535a29a914d28a6795334a99394c7ca62e5309a97e14bbaa5c252ce295ad4ab6a52a5277292c94918a4665220290c14840a410520028f954768a39951c4a8de546d2a35951a4a8ce5463ca30e5179a8b354522a26b5122a88a9441ea1d350d6a861d42eea151507a283394124a06c502e281314078a0164ff827f293f489f7e4fac27c713dc09ea44f4a279b93c649df64edd2767d3adc9d274e7b2731539289c6e4e1ea705d37e29bc04dc226d7936709b284d8126b71356c9aa64d4b26a1934ec9a504d0fa683d33fe99ef4cefa666132a299414c98a648531e098a94c312611d302c98064bfb25f992fac979a4bb4a5ce12e5096f74b73a5b5d2d36965f4b06a57712b4095594a942543529b894cc4a5e251d5284693e749d5a4d9126509318498424b31257892ac4938248fd241c91d248c5a4569227e91194884a4361219090b84849241b1204a8fe947dc23df11e808f04476f23b391d7c8eae474f23a391ce68e3746f2a36d11b068d7346b1a354d1a868d284670a3345196c8ca6464b2321918d68c5046152301117e88bc345d9a2e6116b88b36457d22b2515468a9345312294914848a32451122849140489f244f1227491384899144c0a25c512c2893b4495a244111be88cf445fa223910ba882c4408a1fad0f8a87aa43cd21e290ef4876a4386a1bc90d9886b14350a1a190cec86664325a18c10be885e442df216b90b26858342b9a15350a7a852d4289213dd09b884c142532122d08e08455421220fa10758837b41b5a0ce9065482f94174a0b6505928298413920931044c820040ed207290374819440b72057902708112408120371018280a6404b2021900ec80664025a00)) else (if i < 20 then (if i < 19 then 0xa02f101688096403ee019500a4804a4021200e90064802a4008e002700037ff9bff09ff64ffa27fbe3fdb1feb8ff4c7f9e3fcb1fe0cfef67f733fad5fd4afe957f42bf9d5fccafe3f7f17bf87dfbc6fda77ebb3f541fa80fd307e903f441fa00fcf07e703f341f93efc637e13befadf774fb897dac3ed21f670fb287d8c3eb71f598faa67d353e8e5f3faf9cc7cd33e57df25cf8dc7c55be191f050f7ec7bd2bddfdee86f71d7b7bbdb45ed40f66f7b24bd8e5ec10f5e27ade3d62deab4f5347a873d3a1e9b0f4c87a40bd115e812f3c279c8bcd55e648f31479823cbd1e5c8f2d479623cad1e548f25279213c819e3aaf1c578ca3c5b9e2bcf14e789f3c4b9e1cef0c17842bc1d5e0caf055780cbc025dff2efe977d13bd99de6aef25777a3bb39dd7ceeae7733bb8addbc8eda876b63b571da98ed3c76963b471da18ecfc76763b295d8bcec2d7603bafddd7ceebd775c83ad7dd69eeb3f7597bac7dd5dceab275513aa49d504ea72751b3a815d3eae9e574eaba715d36ae9a574caba615d2eae965749fba439d178e8ac74383a181d05ee7fe73e139ec9cf44e79273b0b9cc1ce40e710738039b3dcd26e6577323b98ddcc4ee6177303b97ddcbcee5d772e3b962dca9ee51e7276b92c5c916e45a7225390e9c854e41a720538fe9c7d4e3da71e538e39c6fce36e719938c05c5e2e2e17168b8b05c562e2a17132b8955c48ae2357112b8855c3c8e1a870bbb8545c22ae0ef705f38261c0cee041700837ecdbf04df516f8ab7b91bd66de8d6f2e37881bbf4ddc96ec6b759dba6cdd106e75372e5b8fadc416e0837001b788db886dabb6c6db616dada6d54b69b5b478da2c6cfdb67adb3b6d9aa6cc236579b29cd93e6c86b6371b198d8a66c40361c1b0c0d8506c20360c1b040d8106c0035fc1af52d7996bc4b5d61ae90d7386b78b5b85ad34d6746b21b58cdac46d6136b01b5749ab84d5b26ad1355f1aa96d53b6a95b546daa16d4e56a5a3520da8e6d4636a29b510da824d3e169d834dfda6ded3336991b4bc9a582d2b16950b4a45a502d2716915347b9a364d176689d344a9a234d10a687d343a9a1b4d0ca685d342a9a09ad03d6816b4075a01acffd67f6b3f759f42cf9167c0b3dc59ec2cf51678ab3c159deacee5676ab3b159d12ce796734b39659c24ce0266f9336d99b4ccd7566a23344d99c4ccd26661332c99944cc92664133119986ccc26660b3301997aacb9965aeb2c859622cb01656832aa99534ca8a653d329259430c9e764d5b25e99292c9396494b24659212c8f96474b23659192c8b964443215d9062c80b63f2b1efd8f06c747638b31b698d3cc6626318b17d58bcac5a962bc3151d8a2cc4e5625a3120d888ec4376213b0fd987a0c3c061d830dfd86dec33e618130b7184e8c264612a3088d83cec1a060c830601829ec11 else 0xd90680fa1741700d90680fa1741700d907d0d01741700d907d0d0148007417001a07d0d0147b700d907d0d017db7003407549edb4302d3aa680a2383b203c0231d00de9b2011904707ff7c5e343808ad822e3e28f4082380aad82ad82ad82ad822d822d8220822d836636aeb80464152116c110c1104111c116c118a110c19be8cdeda6f2137759bad4dd2a6e5f37149b824dba66d9d36a89b46cd99e6c9936319b0b4d7ee6bc135d09adacd66a6ae9354e9a99cd48e69fb34cc9a534d22e68e134609a22cd0aa680933f499e74cea26731337299b14ccf2665933119980ccb9a6581329a993a4c93a647d320d98f3cc7066321317598a7cc4d2621d30f3986c4c2f6612f307c9830cc11a60412ffa97ea4bee65f3d2f8397b9cbd625e652f179783cbbb25da32eb6974dcba025cb52e4a9717cb87e5c1f2df496e74b6fa5b5d2d9396bc4b5a25a9b2d1196704b29259292c84962f4b0e258512c1896044afe257d12bb795d3cae5e570f2b7795b3cad5e564d2b1695834ab5655332a68951bca81a53ab29c594daca696532b296494aa4a48e51e528c19458ca22e50f7286b941d49ffa4f9b27a793c0c9d424e3f26e39353c99da4c8b261492f1c969e4ad7252f928fc938e494f24979233490d647f323c891cbc8e1e469722f9916448a3244a1221f90f74877a439d21be90d74867a431d2147908b4841a41ed20e6906b4831a4115207a90354816a409520198ff447eb23f0d1f558fa2c7cd63e4b1f158f7d47baa3d311e5c8f26478f23c591e068ee5476ea3b551d6e8eaf4753a3a251d028e634722a389d1c1d8df0c6f4637831bb18dd0c6e4637031b718db0c6d4636831b318d90c6c4636031ac58d5ac6a96352b1a598d19c683633cf19ab8cb7c64ce324718e78c55c6192305118188bee45e822f21175f8b9745c7a2df116c78b5bc5a1a2c95160e8aeec56862acb15348a7c4531e296f14a78a4bc521e28ef14678a1b4509a282d13cf89dfc4ebe26bb134d899ec4c0625b712b58952c4a56250b12548922448d223c511d288d0c46462303117188b0c4546228311318890c444621c110af8844c41e620d3105988144406220110fcc87cdc3dd61e730f29878cc3c261d9b0ebd8756c3a761cd90e308710438421ba90d9886b3c34da1a4d0d1686834335619490c948642431d218c90c3385fbc2f9e17af0bc785dbc2e4617030b7185a042c3e15bd0ace8549429b214b90a4c851e428b213e109bf84c1c25ce12c7095384a1c24ce120508c6845b4229a112d0886843b4219a10ad0830840541f920f7d077783a8c1c820df506c98351c19f60c99061b8305c17ee0bd705ba82c4c15620a4f05178283c135a094b04748221c104a07c303d181e0c0e4206bf032e817ec0b320537026a81174087a041d01fe80f74077a039d01be80d74067) else (if i < 21 then 0x8f803a0d912e080306f0be2f1a9703e003785f178d4b81fc597088c6b7c2aa42a38202428183f17db71affc4f8bc68fa0fdb3d5e34b2087d3e2f1a5704f6dc69eaffe27c5f6ce818d1011842b03df8b7d0268446347f8bed98d0cfa7c5e34ae086d822d822a4223823646f0aeaf1a7e93209c006f0bdb7981b23f6d755d04c86345f6de606c8c11846f8425858d0de108e08f51bc2f8be607b8f800de15f4e34f565c12fa7c574010497d3e2f007412e0bf17cc0f718f51bc364608c20f02c686f0854844707e2fb6e35ff89f178d3f4ffc4f6c7578d2c823f4f8bc695c13db71a3aa3f8bed9d031a27c5f6dc01d07fe2fc5f6dffb8d13db7981b23f8be607b8c11846f87db1d5e34b208714231420f7e2fb605c1343d31a3fc5f6cc68681822383f17db4231fb67aab221191fa7c557108c9f17db42318df08a90fc5f6dc6bff13e2f1a7e9ff89ed9eaf1a59047e9f178d2b827b6e34f57ff13e2fb6340c689f17db7fee344f6de606c8fe2f981ee3f8bedbff71a202308df08a90856086c680a93e2fb66343b8bc006f0f800ea1bc3e003086f0f800e81bc30641e003a06f0e6470019c37896db800de1f001bc210411be110411bc3dc437836d87b8adb0de14b808410db61ee21bc3dc42f0db0f718bc36c3dc60f02c686f084104548441044104410447044104eff1a5912e08218237c221823646f086f066406e28de15c51b22990199011b3320432ce28d918d91bc21bc1353c6a5c2c8208608a908860c82b1da1bff12c7482ffc224963b437fe18cbb1cb2076385e3b61d8ed0dff87a198d1a01889b1d20964106cac817005912e0d012c77fe102308bc76c21722f1db0c44892590311c110c110c110c13403784238243828182225640843046f51a0183f8afd28d0dea8de5914688fd06f0411fb67ab4687f17db38ea344591468060c2080c17c5f6d4687eda8d0d91fc5a343dc7f17db51a1fc5f6d468637c22a422382024219c6f0a8d00c38a36494686f0819040612231d468808834686400c1d1a0182d0521a8d0c250cb19146882f0208b41486a343d0521a8d0c2080c10411ee290d468403065d1a190490c0328d0c04840484250410183104101211bc11bc13403784f7e8d45e1fc57e946874686f0a8d0de13a9a351787ed9ead1a1b8ea351787f17db38ea344a3437854686f080ad1a0e6178837a8d0a8d0d91bc3a343d46f0c0ad1a0e4178837a8d083185ea34054837a8d086f8454844707641f4a343d0448f645003e85f6d468ea8cc77c5f6d4689edb435003404a0068054686f0a8d4c8151a1bc2a35320546a640a8d0de151a1ee378746a640844d1a9903d05a1b8d1f43aa5d05a1b8d1d53e85d05a1b8d1f43aa52001265a0b431233e8754da0b4371a3aa7d0ba086c71a3e8754ba1816f1a3e8754a343417001b27d0d01b417 else 0x2088208650a01118d0152e826342f6c248e40c43055c0d010820c82d1dff87b93475df905ff8977f473c51e8e1ec7d0777f477fe1ddf634a80777e412a01ddfd1dff8677fe2f005412e0a7d07b8aefffe10f63e82046176c3dc5ff83ff8237c22382238223823d8fa086f84af850707470e0e007d08a807b0847044707801d5970a80823822a42238320a118acc42315988462b3108c5662118acc42310230822b3008c5f161143aa344f8afd28d0fdb3d5790f168d15fa7c50823f8b0e8110fe282d0190882097e2fb6a343f6d4686c8fe2d1a1ee3f8beda8d0c6f8454844304efd1a10670d1a1b22a3412854687b885c0411ee30641d04088508b4148ea344d0508a4751a268284523a8d1247041168284523a8d134142291d468923a1104118f7082291d468508a4751a1e82a342095468060f4168ee347d09f14fa02319f409d50fc50ac0fa8d0152fc57e94687f15fa51a1fb67aaf21e2d1a2fb67aaf21e2d1a2d1a07c27e9f14208fdb3d5a343f6cf568d0c1f51a02a3f8bed8110e8d01517b679146861040a8be282d0181049f142683e0f80f40a87da348f8beda8d0c2487db51a1b2306e1f8b4687b8fe283d07c0542687aa347f8beda8d0fe2fb6a340549f17db51a183e23405460f88d015183e54005461040a882f846f841484548403044307e29f4a343f8a7d0118c7b68ea347d083da8d1f41fb63ab4687012500a804a01500940291c1045402500a804a0148e08221ee1045a0a8d0a804a015009402f6c7228d0fdb1c80463d0424a8d1c82089d1d468e4134168ee34754fa174168ee34754fa174168ee34754fa148004ea9f40463d0438b8d1d53e85d05a3b8d1d53e85d1c0b78d1d53e85f6da80061c827b6d40030e4105e68ee343dce417db6a00187209ed8e4023190009c80f1a3e87207a08491f43904113a38fa1c827b63524c8e4105e68e3524c87b9c837b63527201190d489205a72086a74702d39047bfc6bff6b8d9057abe606f0dfa7981bc3753c6bff6b8d905741ae36431a2700741ffb5c6c82f980183787e60060d91bc4f300307a8de2798018378608c3e60060de1b1a1bc20860fd8d0de0b69042a00c40df08a9088e0a060f003be3787f178d1f41aa90a8e0a060dd5e34fd264116f8547042587e2f1a3e92e09c006f09548547041e05030741686e35755fa7fe37b6e347556411fa71abaaae09c00d48de1fb6e347546b7c2a3828183683416c87e9468bed9eada0a34b20afd3e2da00824b41a1b5c3d5a3455be155217e9f17805a05705d0dc035c5a07abff8dae3641a063440461552140c1f300306f0deff1ad713209c006f09d4f1ad713208e835c31a9904f6dc6a640f800de17b6e353207eda642231fb6e353206c686400c1adf0aa90a8e08090f980183786f7f8d6c89704e003785e6016ec89704741b202))) else (if i < 26 then (if i < 24 then (if i < 23 then 0x8ea344f6c7228d0f410d8a347209aa491eb8a00720a3628d1c81d1a9700b46b568d4b81cb8a34b5416928d4b810f605a2e28d128d0b878a36480b68d4b819a005a2172720168c919c805a33900b45c68fa1c81889d527d0e413db6a9018680e417db6a9018680e417db6a9018680e4145e6a9e003dcd01c837b61b0030d01c82fb6d52030d01c829000fb6d52030d01c82fc5e00f7fff6b8d4067aaf23806b8d40f14cfd3e2e8ee34ae0bc01eaffed71a80bf158d2415404f8bffb476b8e345f6cf4c6c8fe2f985703dc9f17ff68ed71c68a08c3ffbe2e8ed71c68bf17476b86344087f143da22474c682d87903e91be1152110c141c1552141c150c1bab7234168ee34fd2e29d6f850706fa3d5791c69e2cb832a90a0e0a860e82d1dc6aeabf4ffc6791a3b5c71a3aa57e9c6aeaab827b6e347547edb8d1d51adf0a0e0a860fc5a34fd25013db3d5791469e2ca033f4f8b2802093e2fb6a344ca50156f8554854307e2f005712808f55e470078bae25019fa7c5e012815c17803d5d712809f17db7009404f6cf55e470078b280cfd3e2f00940ae0bf17db7009404d040884b7c2aa42a183c02e47fed71a80ba0b4771ab90fd3ff19eae8ed71c68e415fa71ab90ae09a3ac36b8e34f57ff1bdb31ab90a809c02e46b85404f6de61e28d923f4e357215c13db71ab91ff89f17db39844645701d04249471c827b6e347207edb8d1c8188e09c854021041390ae04b7c2aa428383f17802a09704f8bc01efea097057aaf23803c5d412e0df1416ea09704f8aa80208fe2f005412e09f14066a09704f8bc6a5c0deabc8e34f165c17e2f1a9703f8b2e1118d6f85548507054307e2fb6e35ff89ed9eabc8e34f14a7d3e2f1a5704f8bed95031a20230856d1c0f7e2df409a1118d23e2fb663433e9f178d2b821b608b608a908860dc5e003647756e471a7e9714afd2eadc8571c68ee9bdb798b8a3649edaeaaa0b917158d1bdb7981b237be364408c237c371421fb607a3642931a3dc5f6c3658d13db798b8a3649edaeaea0018720a2183c025c0f71df47aaf225c71a3ba6be9c69eacb825f4f8aa802093e2f981ee3f303dc6c8c1186fa03f0ac1358d03e35f4f8a10462a422183f17db71affc47e9f178d2b827c5f6ca818d13e2f9876c3dc808c3a381edd5d701343d31a3fc5f6cc68683822183f17db5988464f6cf55e43c584657e9f155c42327c5f6d08c637c22a422183757475c8d71c6ae29b804b818430463a040c82208237c2208220832e07b8a474b814b80cb8084108f73e823e83dc4700118f71df407e15c1f0412841088208820d86ffc2bbfa3bff5c8d71c68c7206c8ac30f710f70f0097037867143c006c0843041181e148ed05ff849134158691dff89a08681c81d865702b0da0bff0ec368263435703dc4364e40bff05cc02310860882088 else 0xa5e85f6cf55e43c5a3455e9f147b04120760af4f8a3d82090db057a7c51c010482a422382218219c7a0f7a3449be3de8d0f414dfa3431ec3d0208f414dfa3431ec3d0208c3b043b047a0e008231ec19c208c4107db51a1b23a341287b0d5b07e2d1a1ee30823dc41047b8819055b0411055b074151a104aa343d806115b0441043b068d0f613c5a351d87ed9eabc878b468b4687b09d4d1a8ec3f6cf568d0dc751a8ec3f8bed9c751a2386a351d87ed9e451a1d1a1ec20921f6d4686c8e8d0b71ec3f8a0a826d1a0b61d8df17db0f7a344f8ae3828d1a0ec5f8bed87bd1a23c8a341503b13e2fb61ef46882a4223822183468700a8d0f6151a9e82a353d0546a7a0a8d4f4151a1ec21ed4687a0fdb1d5a34305bb7e8d1d522b60fc5f6c63a8d137a500340356c1f6c7228d0f4151a3903d0448f7a500390556c1f8be60700deabc8971c69e2cf434f478af55e471a97060c013aa3d84bd3805d51c043403d84bd3805a01c04f6dc00ea9a0202dde8754d0115b04e40f612b8e003806f13db1a92647209a08751863aa4e00618ea8f72132d05bd0919a93906113b7cd49c822b60ef4018720d013db0e2018720d0177a00c3407209c00e41a01ee4de8030e41a026f4018720d01080077a00c3407208ad82fd36af1a5704f8be60168f720230fc5f6de601693e2fb6f300b49f17db31a05a411c110c14041be8f238d2d59705452151c150c1b41ae36ad1a23f4f8b6802091fa7c5b401048a183c02d07fed71b54afd3e2f00b40ae0bae36a9a063447e9f17805a0570504613400b45f17db7003404404150c1f30b565c02d23c8e352e16a916acb805a3741b54208f803a0dab2e08f225c4415aa4f8b2e1118dc302d5532e080b420896f85148547054307804b81ee3be8b55e44b8e34774de607b8d91fc50563d43684d0826be9f14208c47044305fa7c557108c9ae36a923234410c10461b6c0b4471420b436187b8a5c02d1bc3046103c0b440b4680a416a9ffc3dc977e417fe05a4bbeb545aa47b1f41ddfd52c68777f54ffe19f41ee21ec7d05ff83ff8237c22a422a422a427d016886f841686d09ac683b147b82d63432be14521d52380fa0d6a8f610a90cd51b2205b20a6a8e6a858d4d514d50cd51b221aa36447746c886f1dd11c81b22b8a36440366a82d634178ac6a6a8be2fb6a340b48fd3e28411fc5f6ce3a8d13e2d1a1ee311c110c1a343dc41047b8811040602d30d468812816d1a01840820b45468168a412d5a3430821809aa64151a202da3425ab4686c8c20864102da34307bf143d51a09b104169dfa7c508237e9f14208fe2fb671d4689f17db38ea3440820b4410416881b87e2d1a1ee30f7ae0166d509a1e68d1fe2fb6a3430a5f17db04d0f40fe8d1fe2fb6a3432340b44005c711a191a05a20820b440382238201822183f17db1) else (if i < 25 then 0xce3404340e2d1a1b24a3434040e820c8204822382048201027d0680868068d0d013b6a351406fd3e2bb876d468aea68d4501fb67ab4687468680a8d0d010150a01f68d0652fc5f6d46874686c8d018370fc5a343dc6197db04402a1ea8d0340a08f8beda8d0c328440a14680a97e2fb6a3431be115211041f8a7d28d0fe29f40463d1d468fa0fdb51a3aa3f8a6e28d0f4351a3703d0da3b8d1f43aa5d0da3b8d1d53e85d0da3b8d1f43aa520013aa7d0118f430e2e34754fa17470d8e347d0ea974368ee347d0ea94dc0d017c5e3477cdc1065e8ee3477c6c9b837c53be6e01193430e23047d08227471df3704e346e0ea8fcc6863aa6e09e607b0d91bb6e003807f17cc0b71ec4f8a0f4268e0e345f8be60700fe2f981ec30461f8be607b0fe2f981ec3f8ac687b0c5484470443052f87e2f981ec30cfa098d0f420760aa90a8e0a860dd5b91c6b416f4b8a6bab7238d5c5d04bd0c97c2ad82a383f17cc5b61ec47aaf225c71a78b3d0d3d1e2bd5791c6a5c1b800e017c51e838020903b055485470543078d5d5d05ffb7a178d2f4baaae08bd38d5d557044be1e34bd2eaab822b60a860fc5b41a0b7a51a2fc5b41a0a8d2f42bd5b40f23416f478b468ebd3e2da00824b41a0b7a3d5a34578bed9eada0791468cbd3e2da008245e81044bd3e2da00824552150c1f8bc02d0682ffdbd0cf55e4682e01bd2d03c53fc5e00bd2d02b82fc5d05bd0d031a2fb67aaf23805a078a65e9f17805a0570504614be1f8bc017a5a0570556c150c1e35723417fede85e35723412f422b8e357217a11d0682de97218d1741700de9721d07fe32f4e357215c115c2f417c5f6c88c697c2ae38d5c85e8456c151c1f8be607b0e5c7001ec37aaf238d6df78b2e0df17cc6df05b2e0bf15d06df0824f8bc036fba09705f8be636f80c970578af55e471a9705f8b2e1118c3b052f85548547054307800d915c5bab7238d2f42dc507bbd0268d9088c68f717db0d963445e9e615c0d921b608b6088e088208b71ec29e8f55e44b8e34774c1d82c687b085484470443067a0f714b89e82f303dc6c8e7a4b81b2336c1f8aae38d2f422b608f41ee2e003dc614f41ec5f8abd2118fdb3d5790f1611957a7c557108c9f17db42319b60af4f8b680209054844304410411855b041184118419055b04db057a7c5e34ae08208223822083c007b0d01ab608f41ee2e003de7a0f622b609b60fc5571c697a12c34dfd05ff8961a6fffe1ee4d0472056187b2b81d86d04c6867206c884304410441044106e468208815c32b1a07a0d11a098d0ac30e057033903d8421823d95c0841055b065c0f715b61ee2971c007bcf41bc5ffc1e003d86c0ce2840f0f612b60ffe0f001ec3406ad8237c36d87b8a5c4f414f497029e810453d25c0a5c4f410f6970236c3dc5f147bc3aa344f8a3da0251 else 0x90ea9a007a302a140c1f8be617a0f720230ffede9b238d136fffed90ee38d17646f4634307e1bfe2852089bd18d07d050911c11041b71b238d4f423d5b71c6a7a2c82cf47aab22dc71a3ba6552151c1b41b237a51a27c5b40ee28d2f42fc5b40ee17a51a2a820f1a5e93207c697a4c81bb8e34bd26411d06f46353208ee38d4c85e84f6d321118d548547054107804f41ee30f215d8d07827c5b713d18d1054844707cc0f71b23f8aee17a42326c8de9468d01041041186c70f717c5b71c6a7a1011867a0f714869e829e819e811bc77447747b887b846f84db06c10d910c81b22e013206f0cdc0f71023081c0fc5f6d4687f15dc2f4a344f6c0316451a208e08820fc5a343dc60e820882238237c20103f142b878089468329a8d07817c5770bd28d1164078a341949ed80651a590406e1f8b4687b8fe29190d21e2800653123d91bd2801091d000ae1e01a06537c5f6c48e8013e2fb6a341949f17db51a1857f8a1e03284c089468fedb6451a187823419461e08d2c80ca401c111c100411041f8bed8c751a2092dbf400d013e2d1a3703d0c3da8d1b82700d903dcd013806c8de8680840026803c03646f43404197b7f8d0d93705239b7f6412337053701e34754dc0c44edf3aa6e09f17801b83404d0c388dc1a02089dbe6e0d013db3d5f303408fd1dc700d91a81db1bdb700753ffb646a037b6d90c695013db7981a03f6de606c8d027981a03dc7edbcc0d018230fb6f303407ed98d0d018df08a908820adf08500a820df47ab6e38d5b6590655217e9a1b473b8e35755db1d4107db3d5a34b225015fa7c5a34ed8a0ca037c5f6d468994a02adf0aa90a820fb69403407282118d01bf4771c01db6c8940694108c680dfa7c576cee3804a032df0aa908120a820fb65403406fd1dc70076da82641bdb700753a826417db31a990a808a81118d01bf476cee38d4c82fb699088c6b7c2aa420482a083f17db71affc4f8aee38d1f427c5f6ca818d1011842b8446341949f17db31a188208d91a027e9756643b8e34774dedaeaaa0990c68a08c237c21402c6868084107800f715f4b6cf56dc71a5906be96e38d3d5b6c5be9f16db2a0b70c68df17cc0f71f981b23dc608c36db476c81ee15d8d1adb7c51eec6882a427143ed9eaac884647e9f15dc3b68465f8beda118c6f8454844106e2f001a03e00308680c680231d03064110c110c11b23404340332033202340e28d918d00463646218321aefe8effc4bbf21bff09225df1a0f147a38fa0aefaa017003e93215010fa0f710d078a20461124389500c648d078a31be111c111c111c13e8340437c22495008470447064342315988462b3108c56621188681d30463991c00490de201c0fc5f6d08a8d13db3d51a0b228d15fa7c5770eda8d17e2fb6a343f6d4686c8fe2d1a1ee31be11521024110410)) else (if i < 28 then (if i < 27 then 0x5948507058307e2f003e9a801e9425850705477c54441e80f97e2f9805a0f484a428383400340034003400211c4af003e8090a08c20442838204428383f160ad1a7e84a0010e0abd50685f8b4681f03d205607c07c652408d000a40f4a0442301f1fc5a340441e900882b03e3f8be601f03d20150a40f47f168d01107a4790148268477aafd20ad1a403fa34fd01f102951a7ba0f88135ea852a0016ca0fc1f0410884f8a0fa8d015203ea341487f141f51a02a402a0fe80052050502a134140c2901507a0a080541fd000a40a0b4000883d1857a340f81e900885207a30220b41e8e803d57e80d09a3b411d53e84c8ba3b411d53e84c8bf147113207a404611c5a08ea9f42645d1da08ea9f42645f8a3889903d268ed04754fa1322a0e0fc5e000901e90e47000480f483dfe2f000480f4bf178002407a40461f8ac001203d20110a0e0fc5e003a01e90e40e807a33903a01e8c0a850707470de05a07c83dc6813207a404611a04c81e8c6813207a302a141c11be1152111c16be1652161c10181f8a59c2ba0c3e8c68c81820303ed9061d5264440c101810cc0bbe2fb6418488c208377e0604d07bc000f9be2b1a07a3f8ac680603d20090b290b0e0a060ddff8a8e80f90db04548447046c8de03e3e00fd06c81f20df0b5f0b0e088e08f51bc07c7c03e28f503e4be83646f01f23290b0e08a9088e084de001e80f93807c50f407c8327800de0e4416fc006f07220df0ac80f5c001801f29c50b00f8a1e80f93e2b1a0180f480242d7c2c3828182238363a0604d07bc000f9ac7700f8afd00f978058ef6c3640f978058ef8a3d40f96c77c5e000f439146f8454840a840a840485af8594850304060423a0cbaa1375c07b990c69012c20f0281820302818212c203037d3e283d082508a0f02818248c266020303f14328446005a0a81820302140212c203037d01f0576340fca0f02818203025bbe2fb64181698d18870503058d4c80f003032940487e2c411ee0f48f546f71a1ee4752378208f7238e1bc1047b91948587042c04048409040486169dff8b1041e943b040484af850307cc5c51b20f48f7ce28dee34364afd0eef981b20f4afd2eaf981bc0f4ad7c2c383c016407a03e405a0301e8c048494850305645a01b20f490b46843a03e47bff16d003d23f4f8aedb8d03d2bf4f8b6801e904971a5900f4823820542054202420242d7c2ca42438281830568d3df8bc482aea62f0342415a3517860568d45e1815a351786f7e2f0341e86d04754fa1322e86d04754fa13229dff8a4c81e93436823e87549197436823aa7d099146c6823aa7d09914effc52640f49a1b411d53e84c8a81823404a8d93e8488bf144a9f42444f8a254fa12227c512a7d09110effc52440f49f144a9f424443bff149103d202ef8a254fa12228150a060fb63aa4880f else 0x2640f4897c2ad83b7fe292207a41c5f149103d26df3904881e93e29221ee0f49b7fe292207a4dbff149103d26dff8a4881e90176dff8a4881e952f855b055c078004470443058705830416842b92208834041b6dc005b84403e5e00b547a81f230016e1100f918002e07a3452161c160c111c110c16000b81683d210e0a02082d083f0ae0f81a111484e2858002e07a3452120c14041446105a10aec68220d01050107cc6d51ea0f480b420f028a4248c20b42110a80341a290a0208f5f8a1c8fa03d29f4f8be603d03d286df31b541e902687207a373011be10ec10ec12be1452161c160c1f31b54fa03d20d97bfe626a83d2c2d1aafd38d0d92bf4f307746c83d2bf4f307741e90e47981b20f49717cc0d907a4096109616be161c1a01f17db42d2445072105a0ec0f8c36fc5a340b41e97e287a05a07c81b7e2d1a05a0f4bf17db02d0e4405a1100f8d6abf47901e9ee84137c50f40b40f901ec2d71cbdf6a87a0827f8a1e81681f206d7e90b5e403da346791ed96ad1a09a50f4fd3e2d1a07a5f6ce3a16bc807b468d4001683d1fc55714681683d2d0005a0f46b542b83d1bc80f407c6f201e92203e4f8bc003903d21c80e40f4680821b76a92207a4daa4881e8c6c12207a31efb549103d206d1b04881e936a92207a3daa4881e8c0602e07a34521404101a257807c57e8090c137807b61b2090bc03e28f507a090a0344afc5e001e8121be2f0007a0908c01022220480f4a8111102403e41be1152110c102216be1652141c160c1f8a59f476820ae7d18d1c41044a9d50f40b43917471d5d704c88838237b8002403e40180581e8c470441040a850706efe8e09a0f78001f37c56340f4777c177c56340f4aca428382c18377f477c547407ca6d822a4221837174770007a3640f9b8068e7e83640f97503f408e364837c2c006485203e46001481e8daf850707805c5d1ded86c81f368eb8b7578d03d2db6d1c1361d0f503e6e01a3be28f503e5e01a3afa0d903e507c107c107c1652141c160c1152110c1d1d0b426f000f407cdc01db68ebaa3d40f9be2b000f407c97558d03d1a0e0b0608860dd512b7d3805c5048609a1118d07b220e0a0e0a0e0a0e0f0018410c1212fa7c507a104a1150704410431042707e2db68823dc1e97e29f41ee10480f820f820f820f82ca42c1822082054205428383f175003d1fc5e003e01210170650f61e406b000d2741c1f6c723500d909a541c1f8ba807a83d27c5f303dc1e92fa0241bd1041e941e050704e287db7001b00909ed806b1a2b0441c120c110c1f8a9047b83d27b61a07206c81f2bdff8a0375c71a28860882088208120812081508150b5f0b290c2d3e9f151103d28f5f8ba80fa03d2fc5d1c1c81e93e29f4d400f49f15db7981ee0f4bf175003d1ddff8bc681e906f84470447043b043b04af8) else (if i < 29 then 0xa638728d02824f8a6387294120650f0012afd0680272f001caf17db0471b209cfc03e28f704e4e002546807a04e5e00395dc0d004e560088813852209244401c13906f8454844105af859485810496e8ed0ded8ea932368ed917d38d1032843284090581044107db7981b234023946f85af8581044107476c8e343dc9a3b6471a1ee4e017d3500d908e5f8ac687b8efa7c5b70c6880482ca422a427142c682d080906e2dd5e00256fa0d004e7b8bedaeab1a0f650a010a010a011a1c68220efa7c5b70c68a11443040904e2bf41a1c686c95af858106fa7c5b6cc681f940906060e53e93211117e2e8e3e9c687b97db3d51a0f178d17e2fb61ca88897d06c8d078bc68a37c2238223821942194204820482ca42c0820f02048223820542048237a640d0e3415ca12c214034003195d48438a00d0b469fa4501d1a8a0110746a28044192d1ca754fa132292d1ca754fa132292d1ca754fa1322823092d1ca754fa132292d1ca754fa132292d01a394ea9f4264625a394ea9f426450ca125a77fe28e52825196254ef8d928250461f8a77c7294121dff8a394a0900a844a9d52823f8a2546c94120150bd5e343d82691db7c5e343801e97e2bb6e343d41e97e2f001c007c8037807c51ec1c8a035c77c5e343d8bc03e28f603e40988107b87307a54081f07b81f20a9088e08860b290b0e0b060edf3abae0991041055b0417066dbff175c12230820ab6082e02c0336ffc5f300f4e37c2ad83b7f8003d1b207ca3658d03d1dd56340f461d8297c2c383b7d1d0d903e436c111c1d057542687bb8ac6a7a1c3b07e28b71ec07c8ca42c382c1822a4223822182ca42c382c183b7e1d0d903e4dbf1046c83d25d56340f461d8297c26d82bd2eaf1a07a44be156c10da3d2ea8411ee59e810c7bc4120411ee1f460bac77c56340f4a1d8297c26d83b7ec77c5e340f4a208218821d837546871a1ec4f6c134a831a0f854be156c11e9f16c70411ee5f8b63a7a0f7882507ec687b83e202ef8ac681e903b052f84db057a7c5e340f49e60e40d907a4730110c11041104101ac683c065205701a1958d078287608760b290b0e0fc54820f4697c2ad83f16208b907a4f8be607b83d20de1ef1041e901e040686dbabae38d146c71a1ec338a120c12461330101bf16c76b8e345e003407b02720650880358d1502a5f0ab6084b08760a5f0fc5b6de601e907afc5f303d01e95948587058306800680068d068d05eac760683f8b1d8910de447603e3a351d82b8deabc808ef168d476351a8ec1347f1436d1a8ec4f8b46a3b0dc73d58ec0d08f223b81f1bc88ee07c7f178d0e007a4dbef578d03d23290b0e0b060af4baa9042213e2af4b1c9049bd0ea92203e4dbe754d003d225f0ab60edfb909041e936f8de05a07c83abe293207a4f8a4c87b83d26df3aa48c1e936ffc5 else 0xf5e0032476db80083d5b6e003e007744edb800b8005db70017003ba2e001e007d05c00ee8b803f4b8a3e0077447d3803dd1f003e8290dc004327800b805c5158ee00261c19e9c00411f800ae284de00308fc017a0f802f410f70af4e0077461357a5c5e00407b6da1d0c269c81700390261c101bc005c01e28a7a7003ba361c1e00b545c8c1ef003ba361c1e002e01e8d870406bb6e003e001e00b545c003c026a8b803b69aa309af17800cfa70078a37bf717800f80041edc57e9c0080f7801dd1f003e83d46136db7007aa4e001b440f5eef001847e0023ba11e1d0cea84717003ba278bc00411e477001f00b8a208f2385c02db0b803d53ba3e00720648c36f0001a3e001345c00238b8003d170008b9e002e00ed8268ddb23a170009c8e002e00ae05c00ef89ee8f717007aa2e00f15470c2684e2c04130e0b0e0f00192276c2e51d0f80061d07804c817005902e001e00ed84ed872ec8e343dcae3b7a6c8e3441cbf17806f403e5e001e0010fac68290d8007d050311c110410c2161c160419e9b238d0f7207808780b290b0e08a9088e0cf4e34364239032843286c76c8e343dc96e3640be9e9c68bf167a31a07e47aa37b8d1dd23d53bbc687b93e2b8ee343dc80f020f02ca42c382037e2db8634436c1f31bd06c84720c8b71c686c906f4c8e3415c812c3f147a9411d9808490878a341942b93e280a0f146832941dd1a0ca15c81e28d07b1d1a0f01ec6b203c51a0f640f3469ee87820440f61e2800692fc501a1e28d065287ba34b202b903cd1a0f01108031ea93a06841f1b207b92227b631df147c122298ef8a0f47c1222fb6601f147c1222861080c1963946c941292d1c3b209194128610edfd0c754a0936f8893aa50484b4c70e51a0504)))))
def hx11 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xc100d1007e70c1c000020a380000409df41d5409f7003b20b9400006005cc27310ad10180b0825829e5065040c95060d41424029fc2f0908a2006d0000281ac30500000010bf9c105508bac06c61b60017400001668f40688000000000830400003e0f6e05c0c58171c7780cdc06a102a8d0a5b8083e06bec0c15078300c34034a40ab0000380f200001430e00098000030564000041609c2af20bb40000000000000703bc0000000000000b074c41ad00002c2cca1b9d40b7a0a4f80ff502998276000000000703820094b06f0c20590b40000081b6a813230a99c1ef000000000409a5025230b3dc2a9b04eb41ed1072bc07400000000000000c25080ac00000c06e881fa7085e000700003c72100000c2b29078842e60000000004043881d77063c4036000018167000000316007d8000000003c1bbc1268000060c14c26b909b8000021b074299d04c40000206328023000000000905fc0000f007b41dd000000000404020262503b40000202680578f065c0000b00c80000c0b3b0166000000000000000000f073c0000008c000007043140b6c0c5c0000000008099000000000000000000f01700000809fe82fbd0bea445d400a4000000001819c90247805f8031c0000536d8015300001408500000c1a410760021ab06adc08c50c91808b10069c0973077ec1d6c0b60028f8a4434050e079065aaf09eb407fc02180000001e7408790134c1cea0ae00000e04040000b196780900000082c7a0b74000020582431aa04ec00007046c000000001c56d417e800009095f45f1c045a02cdf086c00000000041e7219600000000000000f027800008086000007088c812a0028a81925040e0001717a6644b0000040f89044400000000382b100003011d00002c16e0000241b0e028c000000002c5e8805c5849f00000000000003c6c2000000451000024135000000000d861000000000280dc00000c31c00002819ff0b8c4025167a80000000010110000000000000014178000000000807f8000000000403f7010000009051640d700003015df445c00000000202e87041c005040400b02280040400289020c08000ac58200046040a000088208420048001f1e0c28b001000a000020300080010800680000001106200030058205300010100000050000080142000b00000040200401000020a001420210001020a3c30c121c08808000880800400000000e500800600140031200000001028212180800a0400810001801800200001c00200043041a100120010184020020200280840204000000400002000860008187000020400100000c2000000044010a28189040c006000c4000c000810004005000000a020c502000408a0414084045400000040010e302050a2068416004000a00001020458400100000004001000008a000008d0208001 else 0x380bd0000181c530711244c20bb10014e0c4902b9d0481c212007ed4144d0b500000f078d02eb0000040bce0a0b8155f03d301c00000345710000280c86093801fdb0a07c2956098c0000d0669c29dc04b8c6e4908dc89ee301df424a705bc0000100d5427820bd0403d0000000000000141c120c4c0000a07a781980000000000000102bb2016c00000000000002046240d5d0ad40000000000000000000000001a4404370c6242dc5038c000000002825160b040000b0593806bc0b0c00000014a02fc701280000008330058302b90031d05040000901140000903cd80893024800007195d00ba00492830b8030340212015c423cc02bc0000b08e6c1f2c0213c1853004c806ac0a1980038025bc114e0013c00851b2a81d40000082c00000080ec4052682e700002820f0000341cd0000282043074a845ce03ddc32240428404fb049ba9b490350000070c8e42f6801878d5350af9c1a5a0914c055c0b1b402800000000000002800b5014c0000708780000e0a618081a0779406fe048dc207000008046e0af2018dd0138830a106fb008000b13011900001802a00741c150704db4082805b481aa302fec314d0834000000000c1305a34ac232b3130420bb07a000608076bc6be7043400000000180e900551c13f406fd00248048782d750159025f702d0413411b6dc2c94003b0301a127946b2000038112b01e00000f0c560297000000000200f1c2fd9079780f0000000000602cb85e4f036d031d0000000000000040f500000000000001409dc05d6803e907dd46a0b0aaf00ad409c642d6407b04309f08c4415800002c125d0a53408f001240000d02e5c199000000000e99300000506d7812f00000000030a20000000003c49d0000041060000281aea02940000517e3c29af088ac54540bdf80ce608b181270000080aa104b0428b00000c258c0808c2d3807440000c062b01e1f13a100fb000000000000000000b02a3c25600000000000002403040075c98400000000000001015b000000000803f7828300001c11a00000a10f817c200e2a1267428a802540000905e400001045501d93032f8138e04cfc02e6071800ac000020275e0a1f40486139a4006d0c87c1f56094c00008026e407be0064c306c04f1c1eb10bfd802f70ba6029090a34000070b544109c02e2019e3035800b360999c3207013241c7c0b23431fd00ae825be0684c200c05f2c07271a44c15c00002421cc07f0414600364000040a88000000000826a70c3680718005400005051dc24420865025c00000000040709014db03d8000010892c1c80068c0000904dc000000001124450c6d416c000000000000034291400800000000000000000000000d0828000030933018e1050c00000000381c97070f007ac04b50027d07fe427c60a4ac24b40ad98700f059402a) else (if i < 3 then 0x9661281f920c01026000002000fc0a9c000040a6d416100000c03af05d8c208002f8000080ab8000000bbdc255000000000000000000d08cc0000403900000308adc0cc00b47c162809b2028c3a566c268f017440b0d008ac1b240a8f017dc0953015a600480000a06e406ba40733c1520000042cb114090064d00b40000105df829cc08e242a4f09ee4285000030011000000226c04ac000000002425da040b01dc5047f82ad603798098817f4000000000000060478c0ee0000302169412180c4a138dc5f2e06774215009200000b01a2c42bc0c94000000000000000bc74173304f5c19611150c065e09c800000000001b4906d88cd0000000000003630063000000000600080000909c202d9608ffcc4b72443401c3b1200000207b882ba0000281130000000000000242d260b8090fe70a0000f130902c0df000000000b099ec26f0000000000000182dbb05f9c1a01084dc0000ab6240fcf0bcd8236d098400004076d4206f0af440a9101da01b85062d40eba7923c23530644405e40be00000e08eac15eb080742da90271c0473053b406e406a40000004a081846023581bd000000000707c202a0b037402c2a08f800000000000003053f0088e0b780000000000000e0c7800000000380e740340c49ce024c000000000c16b20a85c0b1609fa4187136aa80cff0394000000001c16a00002c72400000000000000000030c0dc0050000000004060a015181b20421da0a7c00006104180a1a045c40370000340c6404700000f02ef81f1303840000c0410c21f000000000c061ac2f200002825ee1c2c000000002c041b0328000000000c265000000000b00324203f0043030270a10424200b7c00000000102a51018800f970060030800000c042f0b880000000000000000000000000000000c04fa8181200cd4195c08ef426d1160f4210e00b2c07590b1501a7c05ef019bf006d8051f05c8c2f5e0aab82bf50641824f0000200c5f0be70310d034ec122e0c3d815f603f800006091a00a05002bc009408d282b3b08948279b04a5400dc091c00002058f81680000082ee8007f81b30000380a4908aa0319c064dc69fa06c40000e0926027450558420e0084680ea608bc0000a00e400000000081f40000000004042f022d00001023d0000182b7d0a24418900000824100169408ad089c000000002414b0000201ea70623407c00000000000001c2e400000000000000000000003030cc17b280daa04214073503a2c6ecc02380000107e082293085000594090e8220b1b70007000002004400002024d70ba80000f1b0381f300001c2218072d00c200c46014ad069b010ff0b87814c60b280000c096400d1107998066803e80000100e201399096a0067805ea01b7100580000a099300e6a027ec04b105a4d1b5301500000000000000000 else 0x5052201570000340b500003407d0000000000000000))
def nd12 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x3ff61148600ffe62921802ffd8a48600ffe5e921802ffd7a48600ffe5a921802ffd6a48600ffe56921802ffd5a48600ffe52921803ff93a48600bff4e921803ff98748600ffe61921803ff97648600ffe61521803ff97548600ffe59521803ff98448600ffe5d121803ff96448600ffe55121803ff98348600ffe5cd21803ff96348600ffe54d21803ff94348600ffe60921803ff96248600ffb58921803ff95248600ffe50921803ff93248600ffe60521803ff97148600ffd5c521803ff95148600ffe50521803ff93148600ffd4c521803ff9a048600ffe60121803ff97048600ffe58121803ff95048600ffe4c121803ff92048600ffe44121803ff88a48600bff22921803ff85a48600bff16921803ff83a48600bff0e9218037fca948600ffe2a5218037fc8948600ffe225218037fc5948600ffe165218037fc3948600ffe0e521803ff88548600ffe20d21803ff85348600bfeaa982803efa6660a00fee91182803fea2260a00bfe69982802ff9a460a00ffa58982802ff9a060a009ff2a582802ff8a960a00bfe28d82802ff8a160a00bfeaa932803dfa774ca00fbe99932803f7a554ca00fee91132803fda334ca00ffa88932802ff98a4ca00bfe5e932802ff96a4ca00bfe52932803fd9734ca00ffa60932803fe9424ca00bfe68132802ff88a4ca00bfe169328027fca94ca00bfe2a532802ff8a14ca00bfeaa981803bfa8860600f7e9dd81803efa6660600fde95581803fba4460600ff68cd81803fea2260600ffc84581802ff9a760600bfe69981803bf98660600bfe69181803bf98260600ffc58581802ff9a060600efe601818027fca960600bfe2a5818033fc8960600efe22581803ef8a660600bbf29981802ff8a560600bfe28d81802ff8a260600bfeaa951803efa6654600fee91151803fda3354600ffc84551802ff96a54600bfe69151803ff18154600ffc5c551802ff9a054600ffc441518027fca954600bfe2a5518037f41954600ffc06551802ff8a354600bfe28951802ffaaa4c600efea2131803dfa774c600fbe99931803f7a554c600fee91131803fda334c600ffa88931803ff2114c600bfe62931802ff97a4c600bfe5a931802ff95a4c600bfe52931803fd9634c600ff64c931803ff1814c600ffc50531802ff9a04c600ff64c131802ff88a4c600bfe169318027fca94c600bfe2a5318037dc394c600ff60e531802ff8a24c600bfeaa921803bfa8848600f7e9dd21803efa6648600fde95521803fba4448600ff68cd21803fea2248600ffc84521802ff98a48600bfe5e921802ff96a48600bfe56921802ff94a48600bfe4e921803fe96248600ffc5c521803ff13148600bfe68121803fe92048600bfe22921802ff85a48600bfe0e9218027fca948600bfe2a5218037ec2948600ffa0a521802ef8a660600 else 0xffe21532803ff8a14ca00bff28532803ff8814ca00ffe14532803ffaaa60600bffaa981803bfe8860600f7f9dd81803efe6660600fdf95581803fde3360600ffb88981803ff61160600ffe69d81802ffda760600ffe61d81803ff9a660600bff69981803bfd8660600ffe5d981803ff9a560600ffe5d581803ff96560600ffe69181803ff98460600ffe5d181803ff96460600ffe55181803ff9a360600ffe60d81803ff97360600ffe58d81803ff94360600ffe68981803ff98260600eff60981803ff97260600ffe58981803ff95260600ffe50981803ff93260600ffe5c581803ff56160600ffe50581803ff9a060600ffe60181803ff97060600ffe58181803ff95060600ffe4c181803ff92060600ffe441818037fca960600ffe2a5818037fc5960600ffe165818037fc3960600ffe0e5818037fc2960600ffe0a581803efca660600ffe29581802ffca560600ffe28d81802ffca360600ffe14d81803ff8a260600bff28981803ff85260600ffe0c981803ffaaa54600bffaa951803efe6654600ffe8cd51803fde3354600ffd84551803ff96a54600bff5a951803ff97654600ffe69151803ff96454600ffe68d51803ff96354600ffe50d51803ff9a254600ffe60951803ff97254600ffe58951803ff94254600ffe4c951803ff98154600ffd60551803ff97154600ffd5c551803ff94154600ffe68151803ff96054600ffe4c151803ff92054600ffe441518037fca954600ffe2a5518037fc3954600ffe0e5518037fc2954600ffe0a551803ff8a354600bff28d51803ff8a254600bff28951803ff88254600ffe0c951803ffaaa4c600bffaa931803bfe884c600f7f9dd31803efe664c600ffe95531803f7e554c600ff78cd31803ffa224c600ffb88931803ff6114c600ffe62931802ffd8a4c600ffe5e931802ffd7a4c600ffe5a931802ffd6a4c600ffe56931802ffd5a4c600ffe52931803ff9874c600ffe61931803ff9764c600ffe5d531803ff9654c600ffe61131803ff9744c600ffe59131803ff9544c600ffe60d31803ff9734c600ffe58d31803fdd634c600ffe54d31803ff9a24c600ffe60931803ff9724c600ffe58931803ff9524c600ffe50931803ff9324c600ff74c931803ff9814c600ffd60531803ff9714c600ffe54531803ff9414c600ffe68131803ff9804c600ffe5c131803ff9604c600ffe54131803ff9304c600ffe48131803ff9104c600ffe22931802ffc8a4c600ffe16931802ffc5a4c600dff2a531803ff8a94c600dff22531803ff8894c600dff16531803ff8594c600dff0a531803ff8294c600ffe21531803ff8a24c600bff28931803ff8824c600ffe14931803ffaaa48600bffaa921803ffa8848600effa2121803dfe7748600fbf99921803ffa5548600fdf95521803fde3348600ffb8892180) else (if i < 3 then 0x3ffeaa60600fff95581803ffe3360600fff88981803ffda760600fff61d81803ffda660600fff5d981803ffda560600fff5d581803ffd6560600fff68d81803ffd8360600fff5cd81803ffd6360600fff68981803ffd8260600fff5c981803ffd6260600fff54981803ffd3260600fff5c581803ffca560600fff28d81803ffc5360600fff28981803ffc5260600fff0c981803ffe3354600fff5a951803ffd7654600fff68d51803ffd6354600fff68951803ffd8254600fff5c951803ffd6254600fff4c951803ffd8154600fff5c551803ffc8254600fff0c951803ffeaa4c600fffa2131803ffe554c600fff88931803ffd8a4c600fff5e931803ffd6a4c600fff56931803ffd874c600fff61931803ffd764c600fff5d531803ffd654c600fff60d31803ffd734c600fff58d31803ffd534c600fff68931803ffd824c600fff5c931803ffd624c600fff54931803ffd324c600fff60531803ffd714c600fff54531803ffc8a4c600fff16931803ffc854c600fff28931803ffc824c600fff14931803ffe8848600fff95521803ffe3348600fff62921803ffd7a48600fff5a921803ffd5a48600fff4e921803ffd8748600fff61921803ffd7648600fff61521803ffd7548600fff59521803ffd8348600fff5cd21803ffd6348600fff54d21803ffd8248600fff58921803ffd5248600fff4c921803ffd8148600fff5c521803ffd5148600fff4c521803ffc8548600fff20d21803ffc5348600ffeaa982802ffeaa60a00fbf99982803fee2260a00ffe69982802ffda660a00ffe5d982803ff9a460a00ffe59182803ff9a360a00ffe58d82803ff94360a00ffe58982803fed6260a00ffe50982803ff9a160a00ffe5c582803ff96160a00ffe50582803ff9a060a00ffe58182803ff93060a00ffe48182803ff91060a00dff2a582803ff8a960a00dff0e582803ff83960a00dff06582803ff81960a00ffe28d82802ffca360a00ffe28582802ffca160a00ffe14582803ff83160a00ffeaa932802ffeaa4ca00f7f9dd32803efe664ca00fdf95532803fde334ca00ffb88932803ff98a4ca00bff62932803ff97a4ca00bff5e932803ff96a4ca00bff5a932803ff95a4ca00ffe52932803ff9874ca00ffe61932803ff9764ca00ffe5d532803ff9654ca00ffe61132803ff9744ca00ffe59132803ff9544ca00ffe60d32803ff9734ca00ff75cd32803ff9634ca00ffe60932803fed824ca00ffe58932803ff9424ca00ffe68532803ff9714ca00ffe58532803ff9414ca00ffe68132803ff9804ca00ffe5c132803ff9604ca00ffe54132803ff9304ca00ffe48132803ff9104ca00ffe22932802ffc8a4ca00ffe16932802ffc5a4ca00dff2a532803ff8a94ca00dff22532803ff8894ca00dff16532803ff8594ca00dff06532803ff8194ca0 else 0x29ddd37aa69b4caa96fd29ea4a748228edd19aa2c7448a87ad0aaa10f414280ccfe29f433dd279ecefc9d9f3a8a72bce2a9bd3367a6b3cd3a9a07335a645cc4097ff2f225c8cb5a966f2ca2582caf695cf2b3a55fca929507293251eca1093b326da4d3c9709273240a45bc880907f204a3f2c7ae8f031d0237ac6a08cbf18ca2f8c5ba8b2f155a28fc4f2896311c2212c40c87830dda19fc2f4858f0a42127c22283eb06fa0c8c150821f033a041c04c803eff79fd3bf667e9afc59f6abe9e7cbaf939f1abe267bf2f7a9ed9bda47aeef501e8ebd0e79d6f371e52bc8278e6f0f1e02bbd8771aed81d99bb0675b2eab1d2bba1673d2e6f1cbdb93a721ae331c45b85e7026df49bc8b75a6e1edb89b50b6746cb6d8e1afbb5b66b12d549a9cb52a69fad3b9a60b4a86932d201a38b43a6806cf319c0b34a6612cb71957b28264aac8a18fdb1c46306c4e187bb0a260eac0a97f9afa85ef6bcc1781aec25d16b929709addc5b5eb6096a5ad005992b249632ac2e57daaed95b5ab2a560eab41551aa6c5456a7814d4a98652b2a489470a8b450faa119407a7d84f429e493b2a7564e529bf1376a6b64d4e99e9335a63e4c0e97692e5a5944aba9499277a4c2492a9179218a40447ae8ea91bea35a46328b8915fa27444a288690eca18e42c28481074a09e40e281390069fe03f2a7d50f899ee63d4a7990f0c9dce3b1a7580e999d1039c672b0e3a9c3e380e6f90dd69b7636926c48d689ab8350268d8d0999d2332265b8ca59928323263d8c7398c4316a6298c46987e30a26108c0a98062fb25e88bb597342e0e5b68b56968a2ca65898afc95d62b3e55f0ab6955e2a3a5370a4d945a285a4fd89df9388267a4bc8967929824c248d090391f823d246c88c29176225643d0859907c208a40387e68f961ebe3c507698e9c1cca38e07008dd41b4e36106a68d3e1a2233686658cbc195a32786338c3a181a2f585d48b72168a2c605758abe150e29685168a1e13e227884e9899c12b6246847188ac10fe214840d87ee0f5a1d8839086ea0d8e1a6833686360c1217702d285960b0e1540291851409ce136024b846008520fc81dd838e06ae0ca817e82c6050a091010681e0035205f00a7811801d602f805780a0012201b80208032001e0003ffeaa60a00fff69982803ffd7660a00fff68d82803ffd6360a00fff58982803ffda160a00fff5c582803ffd6160a00fff28d82803ffca160a00fff14582803ffc3160a00fffaa932803ffe554ca00fff62932803ffd7a4ca00fff5a932803ffd5a4ca00fff61d32803ffd864ca00fff5d932803ffd754ca00fff59532803ffd834ca00fff5cd32803ffd634ca00fff60932803ffd624ca00fff68532803ffd714ca00fff58532803ffc8a4ca00fff16932803ffc854ca00fff28532803ffc814ca00fff145328)) else (if i < 6 then (if i < 5 then 0x5076d8d1a06a83b6754d0c68c833e95037164634db1bfeedaa0b231a754ddb141642344b23b6c00d0280a4976d805406417fea81f4b231a2bab5076c681b38d19077d1b8a81b6b231a3dcfdb590118fb6340d9c68c82ffde2d40fa6345663c5ed823251ddb5908d10df09521197b60551a140be2f6c6823442083ff5057a1efe2e347b1e82f14f6c68f42de8eab918d570e298b83dbc5104f42ffd7a5718d3aa5f15a0bd2b8468bff5e9e2e015c3406ffaf4ae31a720b6ff8a7b6345c15d5722f4716b8c68d939ec5c16fe29e82098b83dbc5104f42b317a78b5c0465ff9c8ae31a2171e29ee209e85bd3c5ae11a21bfe2d708d13c5468761f6c7bf8a7b234517c3e29ec8d1e842e0e0f14413d0a5b04a9091c12183ff6355c5aa1695f4b571a2e08d05ab5c2344ffb00b56b8680b8d5aa1697047d0b8b54f7104acc5ab5c0464ff9f4b571a276d8d1b26a92d5ae02d4688410756a85a8d16d5ae02d46896ad7016a344008216daa5c234423824307fef1700ae2a02ffde2d415c634fa19d5a81c8c6ab8714d503e9e29702097fea82b8c69d52f8a505708d13c5c02b82809ff5415c634e417c5c02a02e09ff3e95078b5c6346755c8a81c5ae31a364efa541e29707b8826ffaa0756b8c68be2d70118fc53df1a2e09ff3915c6344ffbc5a81f4c68acc78bdb0464a3bc5ae11a211de28455c234537c25487b6f143e0551a2d1de2d708d100e0a01e29402090860819ff571646346f1bfeae2c8c69f42f6ceae34641bc5f15f42e041378bff5915c634ea95a0b22b84689ff60164570d016b8c68c83789646345c1bc4ff9f4b22b8c68bdb3aa641b38d1bc67d3c52e0f7104de37fcead915c6345662c8ae02327fcd05915c63453df1a378b821b38d1bc6413feed9a0b231a2d915c0188d10c8ae00c46886f84a9091c10551a1787e2f6c8d1bc40182642346f0cb60fdb4fafbf4f3e82fcc4f907f133e00fbcaf713ecfbd83fabcf4cfe873cf2f9aef2dbe503c7ff8c8f0fbe11bbfdf7c4ef1bdd33b85f6b6ecffd8abaf4f5b2eacfd49ba77f4a4e8dbd0b39faf3b4e70fcd43987f2d8e543c9d3919f1f2e377c613892f0e4e16fc203824f01cdfa3be437a7ef22ddebbad3743ee5adc47b78b6daed6ada53b32b649ec3ed80faf1b5bdeb3ad607ab5b54fea5ed44fa7c34e1e98cd2aba453473e888d0a3a01b3e2e770ce5f9b9334ce662cc6b97d32d9e57cca77939b248e45ac8338f8b1d5e36ac67b8c43171e2acc4d788830f4e1b2c30b8563090e0d6c13f81a3013dfe6bf237d42f7ddea6bccb78e2f05ddd4bb3b7572e8ddcdab91f713ae0bdbd6b7536e1adacdb2cb5ff6b22d43da5ab433678acd0d974b28f646ac71d8acb0c360d2bf9d7d0af1f5d62b95d6f4ad8f5a92b4ad668acb358b2affd5f0ab8756d2abed546aa1f5362a50d460a8534ff else 0x5a243835c5aa803404418354d708d39046802d111c17202d110c1a0aa9c69f4720b54d7180340e417fef1700ae2a0289b4778b5c0481ee347f168ea09f4c68aead1ce4570e2e346a39f4f1441260150570ea928eae1d5c6884778b5c0444c02a0ae1c8251d5c3918d102d033c5a38412bbf477fde2d718d184da0a8ef15f40f71a3d1ceab915c634e299d57228e0f5c5ae0d9c690fa78b8d17042ddb6f168e7d04d104f477fcead718d143da39d5ae04d1eb1a3f8bdb3301191df755c8a3ab8c69c53f8b8d170fa11f4755c8c68b8774ce451d5c634ea95f4a38f77571a2e0c50505e2be81197b6755c874c232be9e2846209198ae1d508c9e2e015c1c45015c8754d0c02b8281c53be9e2e005017056dbc50f4f7104b803ab5c1404a3bfe722b8c68bff3bf473915c63467568eae31a720afa179471eee46345c1ffe6a68e722b8c68d5c390118fc5ae300340a02d70e407b8d128ef14f6c68b8289be2d1cfa07b8d1a8e32dd57231a2e1c53d1de285b8d1705f142310474778b5c2344f1682a39f4468aeab9147570e2a3467d3c52e041205b47570eaa345f17b62391a088a0651d5c3908d17c50b40c400412f8b4151d8d3e8537c3475718d3aa42a43e287c8d02a4a3bc5ae11a22be1f1682a391a7d0a94868eae11a754883068eae11a72094151d8d3aafa168eae31a7208430682a3b1a7d1c82d1d5c634d4b905e6282a180c378be2f6c6f634061682c6ac87d0941590fa634432dd5ae0c8c68a5e3e9640824a1b1aae1d5250d5c3ab8d118eb22b8c689db634640184f1441030644bbfff571646346a09f4b203dc68ae2e006f0fb67540d320d937b1a3b6d801bc37d3c53d4de104a44b53ff5716463460f686756b81347ac68ed05716423442258effab8b231a331d5c5901ee345324cb77dd5ae31a320fe2e345c3e84777003787ff3bed4d71646346edb1a321d523e85e3527bd918d170748ddf682b8b211a376ceab408d190e999f4f15a0104891a64d0571642346ff9df63ab8b231a33aa659a06cd718d19077d0bc638f7b231a2e0fff352c7571646346ae2c8469a023e85e6346413002e0de187a7b9bc2093b6360bcc68c8283cd0570642345ed8922f31a320be29ec65e345c1700320de181a6c9bc646345f142d32f1a2e0be2b40cc0824f158e32f1a2e0bdb018c75901ee3464680c101941590fa23453240c129d5ae11a320efa78a208c0c0b686ae1d5468c06244c7571642346468c8030680018208ddfc00de19be16a7003786548700680de191c102428d1bc257c3415908d3e844a43435708d3aa443835c590803404a0a86c69f4754b41591803e8d01686ae300755a02ffd646357a11b8b231a3d08d05e9642344c6af43206dc173646347a1598bd2c808c9e2e347b9e84bd2c84687db5903c0ca8d16c8bd11a191c12083ff591) else (if i < 7 then 0xb8076d4354068168eb23b63431a2f6cea9a06463457d28e6e2c86db1a376d4750ceae34524bb6b202220184976d471918d1892a3bfe7d2c8c68d473e9646344717003406ea88fdb190681b38d1e8e7d1b8b231a6d8cfa370db51d641ef8d1c926a68effbb6b231a3f8bdb3301190c9754d07d31a320d4737164634fa15f4755b8c68c8774ddb634643aa46a5f4a39b8b231a6d8f643e8118fb6754c874c232be9e2b70e00465a1bb6661d508cbe2f6d801c4681406c00c8280d0276c681b26463457d1b8c02c8281b633e8496346413c5a39f4c68947178fa3718d190db1fb6280c808c947125ff590dc6346754cb340d96e31a320efa51d64634dc1598b21b808c94776d641a08d168eb21f4468864895db3aa68234641d3a7d28e6e2c86d91a3a65db50d473aa8d1bc5ed892468222f6c061246423454128eb21b8468b803e8680cdf0b53801a032a4209051a3404af868eb211a7d089487b6a1a8e469d52a041a3ac8469b8250d47634fa3aa5c01b8340641068eb231a77db82d0d47634eab705a0bc5b7f1a3d8be2d057a1ee269ed8d1cf6f16823d31a2dbeeab915c38b8d18f6f14f410496fd70eae344b7fc563ab8c68b6fd70e463440b40c3dbc5b7c4135047bbaae45e98d38a7755c87143dbd2b83671a4504eab918d38a7a19b6c00f73d885bf8a7b1e82688263dbc50f4f4104b803ba7b8e82ff9d53def4c68ce45057a634ea97c5c69b63dc94178a7bb417a234668282f14e83d11a33aad0391415e88d3a67104f71246993416fbab5c234763a82ffbc53def4c68fe29ec716347a158e755c8b7eb8c69c53f8b8d36c7b93c5a0af4469a02d05ff3907bde98d19c83db1a3d095c3901ee34475682bd31a720be2b6d8d1ee4ff986b7dd5ae31a3246d05bee45708d1bfe63adf722b8c68c65dbeeab918d170e29fc53d8f4134412f8ad03302090f7a0bc5bd0f6468c33f8a7b2347a15d5722dfae1c5468c209ee20b6dfae1d5468a9178b6fb1d5c2346032dfae1c8468be285a061ec8008261d828d1ec24a43415e88d3aa44383e2d057a200d015060d057a234e413c5380f4134412e00ea9ec32a43803407b0c8e0d057a600eab405c01c83d86430682bd31a6a5c82d057a600e43405e62b8b542d209bdb0f5e287b8d05a72e1f4b544126016ad70d0118eb56b8c689e29042085a47d3c5c68b820885bb6cfa5aa3689a20a1f47231a354b8774cd05716aa3447d3c568041231c16ffd5c5ab8d19f4638f7b571a2e0d5c5aa8d34046182dffab8b571a37fcefb0d5c5ab8d1bb6c68d57208fa179549eee46345c1d23619a0b56b8468dff30cc75ab5c6346f142d3db1a2e0a2685afa0f56a87b8d1dc8c68b83549db1b22b87a6ae346f15a06604122341689f4f14411a4416b1d6ad708d180c0b6a9ae1c8468c801041688241e84d0f51a0b4a8d else (if i < 8 then 0x755f44c8c72e006837013952d03300f149577d4138198012aeaa825f1682b7f1a3d83d35bf80570eaa645b7d8ef1700ae12235bee46341e91c5b7dd5c683d2baae41ece29e98d18f7f143a3d81f2baae43ba209ee5b7dd5c683d25be26b915c3ab8d183d6d86d754413dcd6fb1de2e341e97c5388f63d31a288e26dbec73aae4570e2e3490f5b663bc5104f735bfe2e341e900d3d9c83d31a2b90eade98d09a5f14413dc3d25bed481a36b915c6347b7d8e035c8ae31a35bf803aae28821e9b00755323d89e2e00911ec40b6dfc02b87552233918d1ec1e92dfc69d50f496fb91803401e962d63b00b56b8488c5c0742203e40f4b87d1c8355dd104ec70dbe2e341687a62e62d1e83d638b87d2d5105236f8b8d05a1e962d1b5dfaa40d722b8c690e476c6ae3426947a2e1f4b54410f4d16d52c701ae45718d1ddff14b8c682d0f4c411ab800ae1e946d7231a0f48e45ab803401e97c5a0a8ec00240f4d47505e2be98d168ec02b8755322d1ce46341e928e77fc5c683d2d1ce2bab8d07a56da8e7d3c50e81f351ceae341e90477144da3a82755c87d31a487b4778afa08250f68e7d1d5721dd104f4709ae4570eae3462e4446d83da39f47544140484778a715701118ce239d5722b871422387adb17cfa78a4708270908e756b8088b4778b8d07a477e8e035c8ae31a351ce476ceae34269a8e7d3c5c683d2b534701ae45718d1824257002384dae0d008918005aefd1c4178a2087a8a39d57141c0f4b47105e2e341687a6f1495c01f4090bdb12b803aa121700a382d755f44c8d803901207a4389c8c683d251d8d3aa1e920ca0ac87d31a2c19436015c3aa9918958318ec02c8ae1223bbfe2e340607a5031d5c68cb0f4afa0746f03e47571a0303d231de2e340607a511c4d7d1d5378c8c68e1e979643e82095dd7d1d5c68de2c18efb53645718d1bb6134c8379d5c68c1e9722236cfa3aa6f0828831df63ac8ae31a33abdb09a6c9a06f1918d23c50f4b96d98e7d0de105106352c75915c63467d31a3200c23e86f0821e93b63631a3200c2f6c496346401850b5dff14410303d338aeae000603e6f1bc5e60820302d0f4c16b1de29058d0181e9f00a182d755f44c8d8078a4abe891142dc03b6255d5488dff635645e84b22f4c686dc5907a6344032f43231a278adc6347a11b83d2c83df1a2baadc1e98d190ee99a0b22f44689e2b40dc2347a380663bfeb22f4c68ac7371641ef8d1e86b22f4469a023718d1907a13c53dcf4c6880f3417a1908d16dfffac86e31a29976fbaa6cb718d1907f171a3d1b82246d02397a5908d1ac8bd11a19ea9d371642347a192263af4b211a28197a1908d1104b7ec86e11a2f8a3c2343292c8bd11a1a1c1b22f4401a022041b7ec8469b825917a600d0108e0dbf64634dc10820d0d6fe34eab705b7ec8c01b8680 else 0x396c8bd31a21f07a590dc6345321d53d0de7771a331de2f6c72e3456e18e3dec83d31a307a7c370641e98d180db7ec86e31a2baa06de86c9bc646347c01b8b20f4504bdb601e2b1c7c24464b700033c5608e5504f6fe00063aaa0952d03300396c86394139ca4ad0d4776d801a013a12da3a86c03b6755323f8a72be8686345717b67571a340be2b6cfa1a0dc6346ed9d53431a2192ea9a0fa1918d1a8e6e2c87d31a2990fa3aa681bceee347ed8d0321d5c68ad4d1cfa36d643718d1fc5389f4340222f6cea9918d1a05249f46e2c86d82231ca06124fa1918d180c0f5f4248bc321b6c69006f8adc12b8d17b67540d364d0378c8c6918051cfa371642826257007d0d009ca72f6d8012a991a0139d2dc00e5))))
def hx12 (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0x30066c00002c1295c4c9c000034123e41e8084d0800003c5d5a001380000301e2b816cc0000000002415640000000000023a6c19c880f34000028443cc1a9300130000000000000000000000000244a0e41115005a3817e400000000000000181a1e00d390220a810c5001de4c1d381c0b44fbb4563300731c2098000014210b8161c000000000000001805c740a4c000021d0f6817340000100e7bc16bd8ca98423fac2157c23a800000000000000000002004f981e7541870000008141584fce01da0000000000000002c01240000000001815f581293c1a7000001c19e80000000002411a5c074c000008228a4007f818cac55e800003409c8000000114a0208bc60f400000000028169800becc6406c0a5740c91c213f4053d80d958140d814f4000032016a02394000000000080434000018240800000000000000000003418f90235c69844870010460d104100808334044d2063800ea60d5810010a738b0472420800000410120041c300015000100704860b20006a20e00630308730144038101508001604688641e2c000204400244224510c09008408018704000420d80320b00628000104100c1415c0042080282108047f800014c518004008c05104d0000470c20cc00110000c00300000204000014605b8c10412ce2440020486000c00002471cb2003c910000508828500024344200b1880010044c51000401031deb0000218030d04108200000028304028008114100e54408304108e2830460080001800420400c00001410524c90993530400000003c908128800204ba0d18d3811006400000004871c30033430402c03310141830cf0415c00080400904000010c13810c22000010c00c00853412001802001050d270d4000471c50831420c02932c01830c0000100ff030104a0811010441090010410030010411411820c00010410411804c00430000060078022441010000402080450414841810cb0021401030400c04c001000000120508008008004100008700100000214e00520140200400c6823c020114100404808210a0c70022020011000010021c12050000032ca09630010224700118210000104e0420031521170c03c108104a00204200000e0000c001214058024604c0060811800070400420400000400400490410000c10060c200500100d4800000c014154854110218204208b00030d1840410021911df00a0000c004100318008028010500100014124108200000601000300028608008f1040810880430020040418090460061c07490064940480404000050001000000000c01400050000060c510400128800000108a00204604105110204400001b2c30000c40c01800004050801830c21421160412040801c140f0411820020850420842030455070000c00001410000c50810024026030cb003200 else 0x452c088d80cf400f63014de4174f00cc0c1143660a882121c067e80493c1152c63e3c218540e6440fb900fb1805ad4151ac14da80978c22e1c235241b5085cf380fd4000000000000000000038125b80b5e01a5341362c0656012ed81c1b8033cc22dbc43a941b3dc4c2380218417a400fb4c1bd2c127602145c159a0100a815b59417f412f80000240e955cd3ec163ba99ecc090f0116400000000000000000000000000000000003420f80000000000000004154300754e4e8d80df4c1ff68c23004d5400002413024047a818b2c07414077141a5cc0cd80000080a76809b000002c01bc0000040f1400000000000000000001414cc800bac1e0f00da00000000001417e280f8940de0000000000000002c2371d0a2800001818f6807f8000000000000002422ec00001406c0000000000302365c001e4022c017cc00003c02f88c51281a300000000000400824139ec0525c0b87019b00000000f300000000003421ae81e2501f6781b3800003c61e000003c14b2822200000040bcc00000000000000381917881c40000201dc1c1a7bc0661c110d41723c1ed40000081d2b006a04234600d5800001006fc0000101493c0214000000000201ba0000000229aa88e4804bb01d9000000407e40000341f08000000000000001c0f4c81769004710107281fd7c064e009d800001c61640000000003047db421c2412e001468812ea0191084eb40000000ed000000019b8000038042c00002c1440c13c6c1a16c1b7c022040000000001c14f1c1dad800500000040c58000020008400e618624c015334c4b40000040f9fc1e8bc14720146dc10d3008d380cca85cb5818a601aafc1e02822fbc0057c0b6d023cd85403019f6c0972c025ec0da901ac7821d000003021b4808880000084d100000000003004e1c031f008f34190a82328c07d3c21b0023b000001c0024000030184b81b84000000000000000816e441f8380a38000fec5523c0f6601b1281f8c00000000014536440249c180f4073981c7b008500000081d8080f4400002c53480000240c7400003c139681f9800003980b80000000002c16dcc09eb020e4c1368000000000100620000028228000000c13a4000024c173c63c2c492541c134109b419ae81d56c1a3e682d6809d6400e081b17c00ef011b80000141fd2c2433c4b2d51ff8000000000181ee740591401538116f44d0d4082045c88000034092a486f6c1db6c00cc0000280bc204b5745f0400000c037282270000000000000000809634067b40d3dc130685db80000000001c08ca02106813b0000034641f021428237d000a0462e9055580000000000c0c5fc21ca4066bc0b7040dbd81d850c50741e900000000002011ec01a58000000000000003016c40000141bf6c0f55004c0c1d0881d884142c44f71c56484227fc0cf8) else (if i < 3 then 0x4c874e00407408aac1c64c0b9b4239c00000000000000000000000008081c0000202124000000000000000c4bc100618801a4404c885d89020ab8099d80ac0c4d1a85f180000141582418380000040bab0632a85c840000001cf40000000003c101800003422a780c1800000461fd84394000000000281b4b8166000002909fc00003807a80000340e508055a81b6904992006b340b8f01d9e40dc085ccbc135881fe6c18f2c126c002d1421f4000000000000000000038050940f8f80a43c1be7407f0003b40000085567c08dc0000000000000000000000000000000000141010000000000181e64000000000000000000000000340b7bc22ab023980000185cf5c148b005a480d87013f185ae40000000000000000000381dbc8014a8230d01a6d0093e405b6c5561819700000040b68c206f81cb341a2b4015780d4080b124155f841b60140800000000028181e4242480e2e844400000044d7181812c541441c24c11b6413318199285b4c00000c0c1006272003d11e0044028b80e24000028188400001801ab0094e008bcc13d204ca00000000002000000000000000c06abc13140000281b71c0550000014005f402e6022ea8185400002404d800000000000000000002c1daa81fc8941df40b0000002007e8000000000000000000030c272c1f380000181dfc010bb822400000180cd000003c02bc0000201d6701d0040a8d421024074741ae40233bc09f800000c178800003c10a400002c087c860f0c1d4f40c1481462c5c940000242075002440000241cb54114501ff8000000000341f0000003403a48221341dec01a4000003423200000000000000000000000000000000000000003017408021c00000000004189400003c118c000000000301ce65076c01af485534809980000080166c0ce041778000004198000001008b400001c62ec81f5c0000042029c0a82862d805ec500415004a480424000000202d81c5441ae180e22058640000041ec40000000000c02c240f184080000003009b701e3bc1987c011344c3400002543a9c1dd800588823f1c4bc90199ac059c0000280c44000000000380844598dbe8a7f8100f405680000180eafc589d811340000000003413a9c01c50171c000e90218301dce802000194000001c0e1d855cb061840000000003843880014cd10d8013a301de61ce8400003824578216b44b5b80efe817594020ec05f0000018023d80b580149c0000041ad2c14fa40af40000345adc000024192cc1a6800002a492c00003c131ecc6fe80647808298178c8003ec201880ba00240dc0e4c80a3741e60817be41f8ac10008244101d6241c9041df40044a412a141a5501aa0c4bf900d616ca33005df81575c142ac0f228639680b49c189a043a3509eb416f9c00bec058201ec3c1f7e01f8540e70c0465c6 else (if i < 4 then 0x2010c0292c22c6805c9c0f0245635415a800002008ef020d00000000240018dcc02cf80a000000101aabc0a2fc1b1c0000200095c07b400002420a000003808c7420f5c1c1400000000000000164a8fc18680000000000814b440bbb8184f90e3000000000018138400000000008149800000000000000380ef800001c16f400000000000000200eb2c5ec9415f8013f58204400000412300000000000c17ee04c3dc03698002a81fc400000000084085b8103bc17b8000000000200f6f0183000003c2219824100000381facc196a414200000000003012bc021a886327a433981f5a4063b84b5c0000000000000000000381bb3407b2011560086981b5d018b40000185dc5c034241d300000281f0f84c938186398268000000000000003817f40000000001c00a90563880e9800000000000000000000c1208000000000000000c1c748164400002c05724183418d3140758000038071800000000000000000003c10f80000000002c0a7b41fd800000000018243acca738049f42130000000000000002405e504d280dc03816880000381558000010232e01a7400002c162240e7dc094a001fbc200400000463080000000d20420ac00002806e1813fc0039c80763015044130ec11c101182420b5c028d41195c1a240000080a1c0000258c0e80b834194b104a4000000000241a4f82384c0d7a81c28408a28091a017b001b0e0124ac4d8881c996443481c4b421e400000c155000000c0c51c562cc0fa5d09c20176c411e80000002378000000000280bf4000000000240aea41774c06d8000000000000000000000000040b38000030108400003c19ec0000040329c1b5741a64000028211d0098400000406ea00a040000081c3c0000000000000008200000001c1c8301c5e8015e022240000200d2400000823584107f41d1a0579c00003c0812c63ab819cc0000091e7000c388032481ea7c1d3f003e2c03964205bc2148000038244f4044640b540000080f5b00fe100128e548680d7e413934068c409044028601808023da4219700dcfc0e10000000000000003001d4000030055400002c0f7681f3400a5100ac800000000000000000000022f5019740000000000000000196400003415e8c1bbc00003c030c42090000000000000002819d3c4897c0c8d8056000000000018227800000823429d10a80068000000000380b914017c0000000003000d00000000fc28134b01ceb41ab6eca230045a46360c068741b97403f80000201068c177d0050400001803f400002c038481864015cb8154b41b080000280ff3c17dd40515403dec078a82037809258037fc23634062440312020f2416000000284b9b0049800003c1d1c00001818428163ec1cd42836041e8c80bea406c481afc408bb45ab2c0d5d00b53c05bac19b781454000010128 else 0x2fc4bf000003001c9413e40000000003c1bcbc018240fc4000018013708adb013440000381228c1bb8c17440000342315eca02048fe41ef08226b415e6c55cf86181c0c4da89d40000000000415bb40443c21ec0095c413b8c1df800000401bbc182240ccc817708032c000000000000002c114f810b1c1ebc80f71417d504b52803395c7e800000c16658027b809080096e409f410ef8000000000000000c60fe84bcc00000000000000140e8de4a9800003011cb80df8000028cafc00001c212800000000000000310e7c00000000000c771c201400000000000000000000000000552c000000144f81a09c16ee2046940860c5b898163000c9780a72c091e013ecc001400000000000000000000000000000341a8c00000000038024f81669c5c74c1aecc0d1c000000000280c61410e00000000000e52940000041054000018200a0135e4010bc11c401fe000003422e500e0f01c898112700dc80000281bfe008e1c050c00003c1b476dbf5c1ca50089c00000c1bd80000000003016c9581cc0000380f04000030109000000000014209501eee41e1140d68000000000280d98020400000000002400f000e8498d4028441402ed857300000000000000000000000000000030081a45ecc00003804b42547b0191dc1fcf82078000020016bc1513c0a08000000000000000c079dc0784c07500000280c28c0f93415fe016420153704c138023710a2681ef8815ac0043341b0701792282780072b80d1480089c0dd301d39406d586231c102681f33c550b85655c02ddc143c00002016d7c16580000145f1e4026c420c9456180000000001817c000000000038194e4036384bd40000281b43c115c811e58225b40d8d4098c984d9420e180b04000000000000002c1224cc354d049c000000000000000000038228c0000000002415bc00003006940000000003c1e440000380e574223c0127c00000000004165768408416a3822c9c1a3540c2fc0fcc0121940f8342306c1467014e50432580b29062180000040ade409a65847340a33821f00000000001ec9fa40f5c0000381de80000000001c0caf022b7c05b3c01ac85ca50148dc198dc6333413c8c5593821c5004f08622601db0c1e9b862504006c00001411acc19a00061fc02ea420d4413c200fe400000814340000100df000000000000000000001c06dc0000000002c1264000000000000000000000000201b800000240ed40000000001002976852841ec842447c0d744170a81334423800000000002c11fc000000000184bb044d5301f56c4c87403bc4566640a6c000000000301101c084b813e1022ff41e184622f51bf70167e00aba40d32016280426400002005fa81c400000381366c13760179f81d5080d91810a28121200f280000000002402b441319417fb81528000038ca90c))) else (if i < 8 then (if i < 6 then 0xc0e6a00a4542348000010048200d6c0000340261c07980000040c85d8ad84158c2859608169c1fdd0040000000c01ce021ea423e0411680000140658000028171b4141d014240000000000cc39c8097e0071c000004165c000000000000000c118a423e400000000000000000000001c201637a5c0000000404978137c00002409ac00003018a8000000000040f2ec1786405ec40d12016f3c16760013c00001dcc90000000000180006c19bf823ebc1653405654103d45cf90218980c5400000c1918009eecc2cee484000003004c400c8000000000000000080a9000000000008057bc070b80ac480dde84b76c08da0c96000002c09330532000000000000000000002104ac000030045c000018586080d2a04d20c197e04c6c0000000001803800000000003d83cc00000023034170d4181800000c021000003011100000000eecc21fc0172a018ec41c44822140000000000000000120c00000000000000000003c03e700dec0000080a124499981a94000000000000000000010196c0c3d4000000000000000000000000000000000024065000003e01c400fc80000280baf848ebc1371c14e241d3741c33c01e80000301cd36ca0998bda816ac00001c0475889b701f6fc233201eb881ef781931819f900ef54199580fd1404d740174c14c800e3e010ce0095301f1101d7a8243640afe0172641f1d457c4c21d400c6c823a280bc941c8c00001021d80000181f2400000c0d464073d00fe8420ba2ca1600303c1bd40c50f411a08225601f16407688161540dfd80dda40059c1e43c5ce741cc20007ba543e819470083441ca3c4fa1c0e3281893c10bd00acd808f6c1b66c09d3011dfc12b6c4c030175e81310c0071c15d94124ecc9cec040c81c1cc1b594495b81e48406b4c0205803ebc1e8481c4f807af0218e80c0c0000201a200000140b3440a6880830008fa250cac1d9400003409680000000002012a80000101df0809c2c00dd40f48000000000081ee941e5f41e3400000c0e000000100a62019e701b740000380aa705385510eac0a9f811d00000000001019600000000001003c7c0c7305ccc00001c15a000001401f1816fc864236c6fa416a4000004239280840401b6c0de4405cdc17c80000000001023d1010d9a854901255c21be0106480cfd01e6a0212ec2228410b400000000000000000000817d2862f401ea000001420cec12b0043334012d8098284c0800d53819dd0029d8150dc1716a0d0b422a08085684904000000000300ebc000000000000000403ac00001401d80000241262c0eb40000000000c054000000c156b01af2863f8dd0c000000c1d7c0000381e508029800000c1a81014c54008c0000304ba505a680000285c900000180671001154129800000016a8000004209d4233c40a0c00002c117c00003813 else (if i < 7 then 0xc0d015d3809de015dd204624106f055680000000001004df022ac0000000000000000000280826810f184b45421580000000001400a64182a443990144a00c1c00002012f2c145245c7c000020156ca84f00000000002c12bb01250c5c8d018880000000002184c8020bd8136c806d140e5f01de38092d84cee8056c000000000240bd681825c08868078d41c2c81d14053568190f81241418cd01f3c406ec81b3440255019000137940f128198a01d758009000003c1dc901e2000001400f80551f003b28072f81e78c621000003819f0000038164b02060c1ed000003415f1c187cc1f95807e00000101feac0ed88215040359c5b1602428823c9c180001767dca500000000003c122dc1d2f803518533c0000000001c1b7800000c1560000008169040077010ac0004b813980000000002c0d0e64e38000000000000000c0e38000000027d4189d413fb01380009b8820fc00000c13cec10c8000000087080bf000003018e400000000000000181b880000240a4801fb400002018ebc0bbf8185a0036d401b140b26c041c00003c17b48183dc173c80675c003501fc2c159501c71c221dc0067004e8c109c4105881f2f0223245556c07ee41b2000000000000000000000000000000281cdf4119880abc000024c502010ec417ea4028204b62023dc00003809ce0231341309419a580f3c000006502e002fcc0b40000000000000000000024164d4147ec02a181bdfc23d6c0595c8561c634000002014fc0000000001011900000000000407cc00000c0db400ea5010fc00aaf0425425162405ab00b1500956283dc000000000041e1400000c150101eb6819070553b80e35810c00000180c3400000c15840000000001c034c016240000140ce7c242c000000000000001804500000341b9880b3e01874020d8000000000145cbb004280000000020000000000000003807800000044fbd415b1c02380000000001c1a864044ec57e80012301b91c0a240000000001411f80000000000843840046bc01638199f023f781cba409c6806f0010404193901923011208120000000800c54215c00003449b40000000000000010100400000000000000000001c0d64011e18103184d8f8022a45dcc00002001d301cc8420ea4211400000000000000000000000020161000000000000000000000000000000184c8a41bf9c222d01ba9c0e400000000003c10d4001fe817abc235401dd4000010064800002409340000000002855d381afb50a3140a6481fab247f3c05758151f4070c015c5819c54138f80ae0405d00000000b1c00003c0fffc0e740000380584000028635c404f400000463ad0082dc178000000c12c0819c380cdd8149540f7c1ce340000000000000000000044ccfc0764462e340604406838217400002c011b4004c8086e805340077f else 0x2c220e681de020a400267c1049c22bd002aa41389862bb42111c116201ba4000034238fe4a90000004111f800d8400180000180f0e8203ec060c0000041f700000000000818500000244c2f018040000000000c2081810ea422b8000038558bc07bec08384226c0000281673c1879c17ac000000000000001409a000002c01440000101b2800000420dc0000101d6b41cf2c102a02070c00400000341ee08217000001021e000002cc40381c6c00cb3058250134204d6cc5a20000038048441eac00b640000000002c03c1c19342ca040210c4042280b8800003007c9c1cc641694000000000000002c0632c03a9c1b4d4216300e9c0000080db800000c195c000000000000000402c800000401ec00000000002875c00cd48110b0030698d3444c97412c80000124f4c0000001f400000000002818d94096504430421a5812ac820efc1a0441a1801175c1dd301fbcc0e83815ce05650407a20c8da41ce3c5515c4d4cc204cc5d2400001014a581abc40dd5854e6462d2811bc000018216c0000324a9400003c0d3500eab423894059980f7b00adb8003a0574f0022640c8940c99823b58231c0000000001c0b9e81ddc00002401908193d400b400000423ef8129f01413c162ec176340bc40000081951d98d0c0a952c9f00000204b88000004108b4224981da48206b01c9ec1928c5f0800003853cc00000000000000242055014b8016c2420c7c1e5581b2d81d5c80ef000000000000000084997dcf468632c00000802e1c150a40e080000000002802300175000001402aec1e3ec101c000038098800002c112800000405440000140ee100667422904487e41aa480ec64208fc12d1844a74041380fab00c7ac051f455ac0000180db200419c0bd041015dcd4401272c62225475e4240342325807fcc0c3c408d58017a44d278051901cac00003803990055d814aac08658153dc06914092304d47a8628c16e80000001ac8000000000000003c644bc089000000cc58b80a5805c98c1707c0bdc000014043b40b3000000c099000002421f800000000000000000001803d80000101f500000001a8ac205c00000410500000340e28415e000000413d800003802755816c0000000000023ba81757c2260d0a22806be0105c000034113800000001e641486462af4068b04bd0c241b01080817990119c415c340f8681fa604162408c000003aca2a408940000102203404a8841c1c0ab00000080cf0806f60019e4080f404fcc1eb0c15720143100d4b8217c4069d01280409aac031400000412fc00000000000000000000c1077c135381b9cc16068622b81b2700d0780d2c4558400000000000000340cc400000c009cc06cb8128a2870800001814c00000245c9c41475c07c4000024052800002c1a01c0ec344be3009fc81f4441c380000000000c1)) else (if i < 9 then 0x4ae0061200fa100f1c0241501bf20083c0000000003410aa0154e4001080b2384d2e40a7c000000169c0000301c20000000000000000000000000381e2c000000000000003aca18c18a1017000036745bb3411180000300c69c0c3101a9e80aa000be501685011040000000001c1fec000006489e054fa81a9800003c0e90408e98621400000c058c8053a4080400000c0edc4091069c040000000003e877d81e70c1dc6404bc01e7c8054c0000000000000030203301881815880000000000000000000000000013ad8202400002e4aff41a7e823ac000000000241dbbe86c7459a40000100c67c5cbd00454412f5c0ab4400e641956e853a4062c41f4a417c7c0c0382285816080000000ecc000034487b44c3001bcc01fb0a84bcc010c84c7bc18bc0233725e7ac07dc4031b405e2c01e381d58440af81bc64439d008ae00ad214f33019ab41a4a8121741e5a01cbfc16db8166f422398109605832003348611e014ee4186cc0bf8c00f78244b0079400101855f3419d7809e6c21b9c55c280e8b2601081a0c00002c00b3416b981ccc403cb84be68035f021cc00000000000000200198000000000000002800c00000000003c1d44000000000000000c154700d884037bc4b9501b18401840000198d4800003015140000318c38000008153b82020000000000000000000000000340dac80fdf416198208405b5d0014204bbd41321415a4404a10559440d1b0134e401710087a00b97c579001f28000028182c0121cc102105c724533881eabc4d16802c7022c280cb48236c0000281ece01bb6c0628c009b82406c22d1404ee01b6c8089a4214d81b618069900d9d80ba742374000038224404a5041bec00000c025a403d40000341b30812d80000000000c0c21c088280fda00e5a0077580045013d400002014d2c1593d09f8c06364152f40b0f406afc234c456700126a40ffb81480c071141a2f0123581d12011d400002c09386c9fdc11db004b341ab80217bc438c0000040601822d4000000000000003510fa00874c0debc213400002c06cd4c4e5c225f84c44422b080b740000202237018d241f9d01e1e80a8481324000010016f018fe416e000001c1b01414380000000001843f80000041be2c140181172812cc00000c0d7000000000000000000001c241f41407802d4000000000000001413dc00002c022181d48000000555c00a28000000000000001003cc40ee5c070000000000000000180aab417a00000000000000000000000002812dc8620fc145bc0f94000000000000000000000000000002006a5c0b4400003c019601c8400002807d800001422940104f007c2c0cbc00002402f4000038018e0157b8634b000c881cef803f00000200da780e168224fc10340000000001c620581046816b40000346358c243f418c2c242 else (if i < 10 then 0x7881187423ff01baf183950573501c5800705c1d0540510000034236ac0bfc0000380eeb8000e85ca8407220065ec01a041ac000000eca1dc207d0133d40268c0f5381cf80000301c0400000000000000000002c125c00001209bd803900000000000000000000000f6ba8510c56df801f6c1130000034035581814000000000280fbf411f342049c06fb42250c1f1840f9ac09f0c0331809e104b7a80a884107a82052ac49e80f4280309822de01f784057c84d7cc16d1c14a3408fc80808c064101c7e423c7253094127840fae00e1b80cee40522805d941060c084fc20c200e0540d4f8061505e6340ff602038803fe649614038b00548c1c534002d409584172c41b8e6848142190184d7c113d01d7385d2b8179500b0800003843a7c0b6104bd800002c0104c132800001c18b8c19fc000000000001fb80000000000821a04074a01c61813be80b2e40e4741d8c0173800348822cdc1ab3c0e6d81c3550a1202276c474bd87514535e4195a422f241a390108d00bb00000000000653a8000000000000002c157c0000241355c1f6344d3ec05fd40a3f41edd8201d81d9a004e541caa811aac4bac803b80000141adbc2319c63a00000000000000038079301d6e44cd681acc0000000001411f6c0b4de09b40000040d080000241d240000140c0441cd941749005c301847c159e6514d80d5400000c1524007b901e97802b1018e040ad5423bfc02f34060800002004cc8122000000cca8cc03204147800001014ea44fa54219c410e681bc0000000000010a1400000000000000000001c0d00000016823ec06e5007d6c06b8c0c4b00a980000000000c003380c9d40a1400000110f40000180734003ef0145dc12a4007f781f0741f7601be941f6b000ae40aec4197a812d781cff4219980bb5019e104c3900c7f24a54c0b1a81c038037480503c633c00000c18d70c338000000000281e30000028200f41e0b00f2601d2180ca800000000000120400001813b5c0af8c04d00000098a478128d507e40141ac160c0000000000c0a21415d50112f8185c00000000000000044b8400002823c000000862f3c1a102854c00002c17118025100533c21dc41adf408a6c05e80000202066819d80000000001c05d59de75c188f81fa1017fc01d4000002809760123985b4800001c052d00fec0000180ca082453014acc0ae6c10f48102f817db81f2000002c12c500d8380461c18c4c0c2600be041ffc405f5c0a5dc211984fc78043ec048d00940000010085d8115a4038f421380000140345d8d1680188c15570094584ba94168fc124400000000000000000001007178048a802bbc02a400ea3c0b7c82308c09bfc0725c12e7c13eb80a18c075c8562081e6c0000301f4fc1339c08b000001c20b341e4ec1f93d0229017f3411b000003c0917000d54 else 0x407780000000002c216681efe01ad400003c0ce9414bd455b0411cc00002802714047e80f3880c0800003c040900f0a4015901d0c0117800003815ec80eb8414d7c10de00c4001522d811800000c18ac41a44000008173000000c03a3c1682c1ff341c6800003805bc00000000038c50941aea002080000201678000020076c00ec80000381ed8000030046c00000000000000000001c229c40816808cf81e9e00995c07a6c1c94c00614011d00dc540cba00e4a014440000000003816b00063e8226440af2c090000001808e5a817e002d84192540ca400002c1e0641a6180bd94c4))))
def nd13 (i : Nat) : Nat := 0x1e8c88d0d1db6644688f4e2ae234416b55711a223b8ab88d1018c85c4689fe7a322344ff6d940c88d17fcf4e2ae2345ff355711a27fb8aa05c468bfe642e2344ef6d719639d445d0b64216c5200ffec1401ffd32803ffb03007ff54600ffe98c01ffd21803ff305007fe4ca00ffcc0c01ff951803ff263007fe48600
def hx13 (i : Nat) : Nat := (if i < 1 then 0x2083202100000000000000102ea0000181b00000482f342e5f094f62ef10295a055d835f609c8842340ae10a7232190000012875186400a2602b20000082c1e2f3402926065400da405e2004f20fce8477c10dd03c240046001720498840be051e0ca7802a8000000000000000f7480dc0078880540000583314066800000000180a6000065194c05ad8a49c004900e4a0290000032dc884ca000000000400ad982ea01e00000000000001a28a80216802e000306109f89592080104d06079000000000084c9601de044c0000281352069902f4c08ac83d5201b981cc0000684ac00004044e207600001e0b8802f9a0a0c01e1e06950305805770ccdc0322011b205320babe0c7684b8000028c4960ef280460000204200000582a740a7701b8803180001ec6268447c0e7a044b80d0d812c60b230ba5a03cad85f410ed09dc00a698346c70e4846c80b40000000000000000aae8136000000000603c784b000007848dc034d8018004878cd56018e842aa0d708a71e0cef842f00f3e036ec2958020b40c210163203e8028b200338270c01f7006c2027382212086901a1c06db01fc000078334c03fc82cae6fe880324135e08ec00001a216e02680000000000000010500001406600000012a9047c4070081aa8c9d9803600000000040efb53fc412f1805100334020e41151881e0000083b620beb81a80000000002079d03b56084800000000000000000283640000381c5e012000014057e0b8ba0e62a05e612f902bce038d0480a0f2200eb0058682840000484b4000068c0a000010b880000602458278a83ac0000584d2000000000a0dc4033200001035840e6a80d60000183740000000000000000002d16001eb229900001a0c480001810f0000000007032800004842400007da16a0f1884cc01003004de0b9e045060c458143a0ea2824260b0902d3a27bc02238129583af60964807000f100000000030299001f904da8333882b622ee1832d20770000000002026642970000000000000000006029600002008f802300000000010252000070088000f1049ea33218bbe0000601320000000000000201ba00001802e62b11018c000068192c00ed8026000028a520400000080000250000000000000001050620dc2001d300002418b000060a160000020200050a2808434000001638200300c0000a0c00a021400012040000804005220810102041820064183040070110000070e280080a0000406680031e180000864024022800002080100400000041c0010604204000860006285040c042010000090101430000086000e0c1000028082000008006140011c00005082400002140000000084040000d000c00206200000810080080c00102041800004007122000b18040010008000140020104042080010600000078500100010430081 else (if i < 2 then 0xa039d8024e02a400003847b624f00000000000001c00800000a05ec82cd408600000000008341c052e81ce000040b42e080c04b68315904a380556007a000048c46610c68496a0f8e03b86118e011f4115c5034208980000000000000a10088407210a68387e0b6a82a3811d000008064582bbe2e000000c90de005e000000001e07e800000000703a400000000000006838200004025ec065800000000700b6000028148c07a58321610cc834ac25d20260813600000606fe00bd20242041c000070434000050ba0e0470000b012ec02b16032c8361c0e588a5ae03f000010886001eca11ac02d4208e50044e0de000000117c825600000025c000000000000000001609378c18d48900000e08df80d44687282be000000000a12c80001806f48014a056800004076d8356a01d5baf46107e0c50000058bae0000481ff204300000e0aa582068050400de570d80001601c80001207480000000000001c0f438395e04298066a01800c22000070115c13578327808ce83a66662800a1c0ec5824e00001808a8119a0172e28c604138077a0112e114a8c4b80d2702dc00003009e0c2200000e09ef8279c04015193c0da6801c209d700a3c09b7033c809af81f3a02fc0324000000001010250246c062b8c70a0fe80000000000001e06100000000000000000000001e12a00001e0db00001421d302e02042000000000701c260f9a835a4098c89cf00f0283cb0112000000000503b2021cb83aa00000000020380000000000000120bff82496103780e6c0b5c8097c11678131ac9d00000003448b9480b600001008a40c7922b08000000e2a81f8c133800002041e83a1806710393602bc026560d380001203d80001e02a2031ac0e22006900cf803d800000000180414039180fc000000000703ba02e8a849ba23ed03182310a817442938000000005032a0000581f600000000181183830620c38000120fb70080000040440029e7033622e0f89014116983ee0000000012072e016ee0c3083d28260000000000480340000681f4000010880a13188a54000010484e12848c4e0000000000000000010101083540000381220000780b100ab8000042d000001205f0000000fd74af7e02e80001c2215015920bf000e8000000001002c80000000040bb2000030ba7003ba0085825200000000030488000000182000030493028be8053411e103626216e8008229348209c0c8a823d80b948301003b5013d2009701d5202600000000000001e03d180060000781c800005823b805900250c0fa381b56067c8351602500000804600000e0d480000e12280000011cd08f7428e20499c3311828140ded0444e131482c5404580001200a2821e000030cda008900000028d80000411930064000000001e017681b20000083da000000000004a6047e625480000 else 0x83115823160d11004060a800000000000000000000000812b80001e0598000040bb000008040881388096c003f20a7b82682123902f7007c08a6fa0f80000060dd80000a030d82f0e074081ae000028001409dd8384e09bf8bd4e09030a4200003887a60fda0acea22a000000000381ac40e8b0a1000000000000000849da08f98b9f812458381a0f3601802103e029000000000000006014f60ab0000000003838f005df83e461108000000000831e00007028da2940801fc21fc024a00000000000006838da2ea0000100a1980c4c117684c2a05b00001811c2022d822360187010e00000c09ff817000000000080d34001b20876814402091021540128000000000000000007813a20dfb0bda0000702e860ce28a60000000000a1218000080688000000001800e22f6000014049003dfc234e8316a008e8469805fa4a1ea29a1cc39a68780000a03038004811b901c60000303fd60d998314e07580000629600001a13700001e04f902ee000068002000010302821bb802cc0b3f00d980da984188081280560000683ff002b00000c0ad000000000483ea000000000a0dce8b9a0000204c0000000000000028189c663080ce405a18042e00e00c3e00000808260638000042f86042c68bcb041b80b1a00f800000030b42df7012b608d3025460df4843fa0446022e000000000000010bbb801aa0410000010483c0a380001610580001a1257032e6043e8152c09f603d6e334c02de000030151a0160005a000000000000038a44604b800000000280b40000103f8e23f000000000784a6e021e81ef233470887168600001a304))
def lv : Nat → Packing
  | 9 => (33,6,7,0,0,9,0,nd9)
  | 10 => (806,5,7,0,0,15,0,nd10)
  | 11 => (2326,4,7,0,0,17,0,nd11)
  | 12 => (623,3,7,0,0,15,0,nd12)
  | 13 => (12,2,7,0,0,9,0,nd13)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 11 53 5 14 6 4 hx10
  | 11 => lookupWord 298 1259 7 18 10 4 hx11
  | 12 => lookupWord 929 3908 6 20 12 4 hx12
  | 13 => lookupWord 255 1075 7 18 10 4 hx13
  | _ => fun _ => none
def allColumns3640 : IndexTree ColumnInfo := .fork 126 deadcolumns (.leaf [(0,0,511,0,15)])
def candidate (cut : ExtraCut) (hc : ∀ k (ws : List Sig), ws.Nodup →
    cut k ws = true → Impossible (chartGoal 511) k ws.toFinset) : Forest :=
  ⟨511,13,fun j => deadsamples[j]?.getD (0,0),allColumns3640,deadautos,lv,ix,cut,hc⟩

def search3640 := candidate shapeCut3640 shapeCut3640_sound

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk9_0 : block search3640 9 0 28=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk9_28 : block search3640 9 28 5=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_0 : block search3640 10 0 96=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_96 : block search3640 10 96 71=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_167 : block search3640 10 167 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_263 : block search3640 10 263 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_359 : block search3640 10 359 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_455 : block search3640 10 455 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_551 : block search3640 10 551 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_647 : block search3640 10 647 88=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_735 : block search3640 10 735 71=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_0 : block search3640 11 0 24=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_24 : block search3640 11 24 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_120 : block search3640 11 120 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_216 : block search3640 11 216 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_312 : block search3640 11 312 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_408 : block search3640 11 408 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_504 : block search3640 11 504 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_600 : block search3640 11 600 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_696 : block search3640 11 696 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_792 : block search3640 11 792 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_888 : block search3640 11 888 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_984 : block search3640 11 984 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1080 : block search3640 11 1080 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1176 : block search3640 11 1176 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1272 : block search3640 11 1272 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1368 : block search3640 11 1368 69=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1437 : block search3640 11 1437 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1533 : block search3640 11 1533 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1629 : block search3640 11 1629 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1725 : block search3640 11 1725 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1821 : block search3640 11 1821 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1917 : block search3640 11 1917 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2013 : block search3640 11 2013 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2109 : block search3640 11 2109 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2205 : block search3640 11 2205 26=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2231 : block search3640 11 2231 95=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_0 : block search3640 12 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_1 : block search3640 12 1 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_97 : block search3640 12 97 33=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_130 : block search3640 12 130 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_226 : block search3640 12 226 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_322 : block search3640 12 322 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_418 : block search3640 12 418 64=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_482 : block search3640 12 482 96=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_578 : block search3640 12 578 45=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk13_0 : block search3640 13 0 6=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk13_6 : block search3640 13 6 6=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all9 : block search3640 9 0 33=true := (@block_merge search3640 9 0 28 5 chk9_0 chk9_28)
theorem all10 : block search3640 10 0 806=true := (@block_merge search3640 10 0 359 447 (@block_merge search3640 10 0 167 192 (@block_merge search3640 10 0 96 71 chk10_0 chk10_96) (@block_merge search3640 10 167 96 96 chk10_167 chk10_263)) (@block_merge search3640 10 359 192 255 (@block_merge search3640 10 359 96 96 chk10_359 chk10_455) (@block_merge search3640 10 551 96 159 chk10_551 (@block_merge search3640 10 647 88 71 chk10_647 chk10_735))))
theorem all11 : block search3640 11 0 2326=true := (@block_merge search3640 11 0 1176 1150 (@block_merge search3640 11 0 504 672 (@block_merge search3640 11 0 216 288 (@block_merge search3640 11 0 24 192 chk11_0 (@block_merge search3640 11 24 96 96 chk11_24 chk11_120)) (@block_merge search3640 11 216 96 192 chk11_216 (@block_merge search3640 11 312 96 96 chk11_312 chk11_408))) (@block_merge search3640 11 504 288 384 (@block_merge search3640 11 504 96 192 chk11_504 (@block_merge search3640 11 600 96 96 chk11_600 chk11_696)) (@block_merge search3640 11 792 192 192 (@block_merge search3640 11 792 96 96 chk11_792 chk11_888) (@block_merge search3640 11 984 96 96 chk11_984 chk11_1080)))) (@block_merge search3640 11 1176 549 601 (@block_merge search3640 11 1176 261 288 (@block_merge search3640 11 1176 96 165 chk11_1176 (@block_merge search3640 11 1272 96 69 chk11_1272 chk11_1368)) (@block_merge search3640 11 1437 96 192 chk11_1437 (@block_merge search3640 11 1533 96 96 chk11_1533 chk11_1629))) (@block_merge search3640 11 1725 288 313 (@block_merge search3640 11 1725 96 192 chk11_1725 (@block_merge search3640 11 1821 96 96 chk11_1821 chk11_1917)) (@block_merge search3640 11 2013 192 121 (@block_merge search3640 11 2013 96 96 chk11_2013 chk11_2109) (@block_merge search3640 11 2205 26 95 chk11_2205 chk11_2231)))))
theorem all12 : block search3640 12 0 623=true := (@block_merge search3640 12 0 226 397 (@block_merge search3640 12 0 97 129 (@block_merge search3640 12 0 1 96 chk12_0 chk12_1) (@block_merge search3640 12 97 33 96 chk12_97 chk12_130)) (@block_merge search3640 12 226 192 205 (@block_merge search3640 12 226 96 96 chk12_226 chk12_322) (@block_merge search3640 12 418 64 141 chk12_418 (@block_merge search3640 12 482 96 45 chk12_482 chk12_578))))
theorem all13 : block search3640 13 0 12=true := (@block_merge search3640 13 0 6 6 chk13_0 chk13_6)
theorem tables3640 : checkedTables search3640 13 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact all9
  · exact all10
  · exact all11
  · exact all12
  · exact all13

def pairs3640 : List Nat := [12,13,15,18,23,28]
def code3640 (p : Fin 6) := pairs3640.getD p.val 0
def x3640 (i : Nat) : Sig := inputs.getD i zero
def n3640 : Sig := neg (x3640 0)
def or3640 (p : Fin 6) := bin true (x3640 (code3640 p / 10)) (x3640 (code3640 p % 10))
def bank3640 (p : Fin 6) := inputs ++ [n3640,or3640 p]
def signed3640 (p : Fin 6) := inputs.tail ++ [n3640,or3640 p]
def witness3640 (p : Fin 6) (j : Fin 8) : Row :=
  Fin.ofNat 512 (([4, 2, 4, 1, 1, 2, 4, 8, 9, 2, 18, 1, 1, 2, 4, 8, 36, 2, 4, 1, 130, 2, 4, 8, 257, 2, 4, 1, 1, 2, 4, 10, 1, 8, 4, 1, 1, 2, 4, 8, 1, 258, 4, 1, 1, 2, 4, 36] : List Nat).getD (8*p.val+j.val) 0)
def present3640 (p : Fin 6) (j : Fin 8) : Row :=
  Fin.ofNat 512 ((witness3640 p j).val ||| (1 <<< (j.val+1)))

lemma isolation3640 : ∀ p : Fin 6, ∀ j : Fin 8,
    (bit (witness3640 p j) graph != bit (present3640 p j) graph) &&
    ((bank3640 p).all fun w => w == x3640 (j.val+1) ||
      bit (witness3640 p j) w == bit (present3640 p j) w) = true := by decide +kernel

lemma tail_required3640 {p k t S} (h : Live graph k t S) (sub : ∀ v∈S, v∈bank3640 p) :
    ∀ v∈inputs.tail, v∈S := by
  have each (j : Fin 8) : x3640 (j.val+1) ∈ S := by
    have cut := isolation3640 p j
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    exact raw_required h _ _ sub _ _ cut.1 (fun v hv ne => (cut.2 v hv).resolve_left ne)
  have eqn : List.ofFn (fun j : Fin 8 => x3640 (j.val+1)) = inputs.tail := by decide +kernel
  intro v hv
  rw [←eqn,List.mem_ofFn] at hv
  obtain ⟨j,rfl⟩ := hv
  exact each j

lemma after_one3640 (dead : Impossible graph 14 inputs.toFinset) {x k t S}
    (gate : witness inputs x) (m : k≤13) (h : Live graph k t S)
    (sub : ∀ v∈S, v∈inputs++[x]) : False := by
  obtain ⟨k',t',S',hk,l,rs⟩ := pull_gate h (Or.inr gate) sub
  have lose : ∀ j : Fin 9,
      (bit (absentRow j) graph != bit (presentRow j) graph) &&
      (inputs.all fun w => w == x3640 j.val ||
         bit (absentRow j) w == bit (presentRow j) w) = true := by decide +kernel
  have all (j : Fin 9) : x3640 j.val ∈ S' := by
    have cut := lose j
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    exact raw_required l _ _ rs _ _ cut.1 (fun v hv ne => (cut.2 v hv).resolve_left ne)
  have eq : S'=inputs.toFinset := by
    ext v
    refine ⟨fun hv => List.mem_toFinset.mpr (rs _ hv),?_⟩
    rw [List.mem_toFinset,←input_list,List.mem_ofFn]
    rintro ⟨j,rfl⟩
    exact all j
  exact dead _ _ (by omega) (eq ▸ l)

lemma seed_meta3640 : ∀ p : Fin 6,
    x3640 (code3640 p / 10)∈inputs ∧ x3640 (code3640 p % 10)∈inputs ∧
    proper (x3640 (code3640 p / 10)) ∧ proper (x3640 (code3640 p % 10)) ∧
    x3640 (code3640 p / 10)≠x3640 (code3640 p % 10) := by
  dsimp only [proper]; decide +kernel

lemma roots3640 (dead : Impossible graph 14 inputs.toFinset) (p : Fin 6) {k t S}
    (m : k≤13) (h : Live graph k t S) (sub : ∀ v∈S, v∈bank3640 p) :
    S=(bank3640 p).toFinset ∨ S=(signed3640 p).toFinset := by
  have no : n3640∈S := by
    by_contra hn
    obtain ⟨a,b,pa,pb,ne⟩ := seed_meta3640 p
    apply after_one3640 dead (x:=or3640 p) (.inr ⟨true,_,_,a,b,pa,pb,ne,rfl⟩) m h
    intro v hv
    have z := sub v hv
    simp [bank3640] at z
    rcases z with base|n|o
    · exact List.mem_append_left _ base
    · exact False.elim (hn (n ▸ hv))
    · simp [o]
  have oo : or3640 p∈S := by
    by_contra hn
    have gn : witness inputs n3640 := .inl ⟨_,by decide +kernel,by unfold proper; decide +kernel,rfl⟩
    apply after_one3640 dead gn m h
    intro v hv
    have z := sub v hv
    simp [bank3640] at z
    rcases z with base|n|o
    · exact List.mem_append_left _ base
    · simp [n]
    · exact False.elim (hn (o ▸ hv))
  have tail := tail_required3640 h sub
  have raw : inputs=x3640 0::inputs.tail := rfl
  by_cases zeroIn : x3640 0∈S
  · left
    ext v
    refine ⟨fun hv => List.mem_toFinset.mpr (sub _ hv),?_⟩
    simp only [bank3640,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false]
    rintro (hw|rfl|rfl)
    · rw [raw,List.mem_cons] at hw
      exact hw.elim (fun e => e ▸ zeroIn) (tail _)
    · exact no
    · exact oo
  · right
    ext v
    simp only [signed3640,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    refine ⟨fun hv => ?_,?_⟩
    · have z := sub v hv
      simp [bank3640] at z
      rcases z with rawv|n|o
      · rw [raw,List.mem_cons] at rawv
        exact Or.inl (rawv.resolve_left (fun e => zeroIn (e ▸ hv)))
      · exact Or.inr (.inl n)
      · exact Or.inr (.inr o)
    · rintro (hw|rfl|rfl)
      · exact tail _ hw
      · exact no
      · exact oo

def edgeCode3640 (x : Fin 9 → Bool) := [1,12,23,34,40,5,16,27,38,57,68,85].any
  (fun a : Nat => x (Fin.ofNat 9 (a / 10)) && x (Fin.ofNat 9 (a % 10)))

lemma rows3640 : ∀ p : Fin 6, ∀ r : Row,
    bit r (or3640 p) = (sample r (Fin.ofNat 9 (code3640 p / 10)) || sample r (Fin.ofNat 9 (code3640 p % 10))) := by decide +kernel

lemma edgeSame3640 : ∀ r : Row, edgeCode3640 (sample r)=edge (sample r) := by decide +kernel

lemma exact3640 (dead : Impossible graph 14 inputs.toFinset)
    (audit : ∀ p : Fin 6, Impossible graph 13 (bank3640 p).toFinset ∧
      Impossible graph 13 (signed3640 p).toFinset) : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ x2 ∈ [(12 : ℕ), (13 : ℕ), (15 : ℕ), (18 : ℕ), (23 : ℕ), (28 : ℕ)], ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → ∃ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ)), x7 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) || x7 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)))]) ≠ x1 x7 := by
  dsimp only
  intro code mem C fan small
  obtain ⟨p,eq⟩ : ∃ p : Fin 6, code=code3640 p := by
    simp at mem
    rcases mem with h|h|h|h|h|h <;> subst code
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
    · exact ⟨5,rfl⟩
  subst code
  by_contra! computes
  have goalEq : (execute C.gates (bank3640 p)).getD C.output zero=graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r _=bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg => (fan g hg).1)]
    rw [show (bank3640 p).map (bit r) = List.ofFn (sample r) ++
      [!(sample r 0),sample r (Fin.ofNat 9 (code3640 p / 10)) || sample r (Fin.ofNat 9 (code3640 p % 10))] from by
        simp only [bank3640,List.map_append,List.map_cons,List.map_nil,←sampled,rows3640]
        rw [n3640,bit_neg]
        rfl]
    exact ((computes (sample r)).trans (edgeSame3640 _)).trans (edge_table r).symm
  have out := get_rep (execute C.gates (bank3640 p)) C.output
  rw [goalEq] at out
  obtain ⟨k,t,S,sz,h,hs⟩ := extract C.gates (bank3640 p) fan graph_proper (out.resolve_right (fun x => x graph_proper))
  have cap : k≤13 := sz.trans small
  rcases roots3640 dead p cap h hs with e|e
  · exact (audit p).1 _ _ cap (e ▸ h)
  · exact (audit p).2 _ _ cap (e ▸ h)

def checkedForest3640 := candidate shapeCut3640 shapeCut3640_sound

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem indexes3640 : ∀ p : Fin 6,
    indexedRoot checkedForest3640 13 (6+p.val) (bank3640 p) = true ∧
    indexedRoot checkedForest3640 13 p.val (signed3640 p) = true := by decide +kernel

theorem audit3640 {prior : Nat → Nat} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid checkedForest3640 prior = true)
    (tables : checkedTables checkedForest3640 13) (p : Fin 6) :
    Impossible graph 13 (bank3640 p).toFinset ∧ Impossible graph 13 (signed3640 p).toFinset := by
  have target : targetOf checkedForest3640 = graph := by decide +kernel
  rw [←target]
  exact ⟨root_index low geom tables (by decide) (indexes3640 p).1,
    root_index low geom tables (by decide) (indexes3640 p).2⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geometry3640 : graphValid checkedForest3640 bounds511 = true := by decide +kernel

end PEqualNP.Outside.L_meta_3640

open PEqualNP.Outside.L_meta_3640

theorem PEqualNP.Outside.L_meta_3640 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ x2 ∈ [(12 : ℕ), (13 : ℕ), (15 : ℕ), (18 : ℕ), (23 : ℕ), (28 : ℕ)], ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → ∃ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ)), x7 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) || x7 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)))]) ≠ x1 x7 := by
  exact exact3640 dead_start (audit3640 bounds511_sound geometry3640 tables3640)
