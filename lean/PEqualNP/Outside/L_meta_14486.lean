import PEqualNP.Defs

-- A seven-variable restriction certifies a lower bound of twelve binary gates on the full graph.

-- The live-set compression proof is adapted from L-meta-9136 and its credited sources.
namespace PEqualNP.Outside.L_meta_14486.SignedCert
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def phase (b : Bool) (a : W) : W := if b then ~~~a else a
def norm (m w : W) : W :=
  if (m &&& w).toNat ≤ (m &&& ~~~w).toNat then m &&& w else m &&& ~~~w
def opList (m a b : W) : List W :=
  [norm m (a &&& b), norm m (a &&& ~~~b), norm m (~~~a &&& b), norm m (~~~a &&& ~~~b)]
def ops (m a b : W) : Finset W := (opList m a b).toFinset

theorem mask_neg (m a : W) : m &&& ~~~(m &&& a) = m &&& ~~~a := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and,BitVec.getElem_not]
  cases m[i] <;> simp

theorem mask_pair (m a b : W) : (m &&& a) &&& (m &&& b) = m &&& (a &&& b) := by
  rw [show (m &&& a) &&& (m &&& b) = (m &&& m) &&& (a &&& b) by ac_rfl, BitVec.and_self]

theorem norm_of_mask {m a b : W} (h : m &&& a = m &&& b) : norm m a = norm m b := by
  have hh : m &&& ~~~a = m &&& ~~~b := by
    simpa only [mask_neg] using congrArg (fun x : W => m &&& ~~~x) h
  simp only [norm,h,hh]

theorem norm_neg (m a : W) : norm m (~~~a) = norm m a := by
  simp only [norm, BitVec.not_not]
  split <;> split <;> first | rfl | apply BitVec.eq_of_toNat_eq <;> omega

theorem norm_cases (m a : W) : ∃ t : Bool, norm m a = m &&& phase t a := by
  by_cases h : (m &&& a).toNat ≤ (m &&& ~~~a).toNat
  · exact ⟨false,if_pos h⟩
  · exact ⟨true,if_neg h⟩

theorem phase_cancel (t : Bool) (m a : W) :
    m &&& phase t (m &&& phase t a) = m &&& a := by
  cases t <;> simp [phase,mask_neg,← BitVec.and_assoc]

theorem proj_norm (m q a : W) (h : q &&& m = q) : norm q (norm m a) = norm q a := by
  obtain ⟨t, ht⟩ := norm_cases m a
  rw [ht]
  have e : q &&& (m &&& phase t a) = q &&& phase t a := by rw [← BitVec.and_assoc, h]
  rw [norm_of_mask e]
  cases t <;> simp [phase, norm_neg]

theorem norm_idem (m a : W) : norm m (norm m a) = norm m a := proj_norm m m a (by simp)

theorem op_mem (m a b : W) (s t : Bool) :
    norm m (phase s a &&& phase t b) ∈ ops m a b := by
  cases s <;> cases t <;> simp [phase,ops,opList]

theorem op_cases {m a b z : W} (h : z ∈ ops m a b) :
    ∃ s t : Bool, z = norm m (phase s a &&& phase t b) := by
  simp only [ops, opList, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨false,false,rfl⟩
  · exact ⟨false,true,rfl⟩
  · exact ⟨true,false,rfl⟩
  · exact ⟨true,true,rfl⟩

theorem recover (m a : W) (s : Bool) :
    ∃ t : Bool, m &&& phase t (norm m a) = m &&& phase s a := by
  obtain ⟨u,e⟩ := norm_cases m a
  refine ⟨xor s u, ?_⟩
  rw [e]
  cases s <;> cases u <;> simp [phase, mask_neg,← BitVec.and_assoc]

theorem norm_gate (m a b : W) (s t : Bool) :
    norm m (phase s a &&& phase t b) ∈ ops m (norm m a) (norm m b) := by
  obtain ⟨s',hs⟩ := recover m a s
  obtain ⟨t',ht⟩ := recover m b t
  have e : m &&& (phase s a &&& phase t b) =
      m &&& (phase s' (norm m a) &&& phase t' (norm m b)) := by
    calc
      _ = (m &&& phase s a) &&& (m &&& phase t b) := (mask_pair _ _ _).symm
      _ = (m &&& phase s' (norm m a)) &&& (m &&& phase t' (norm m b)) := by rw [hs,ht]
      _ = _ := mask_pair _ _ _
  rw [norm_of_mask e]
  exact op_mem _ _ _ _ _

theorem proj_op {m q a b z : W} (hsub : q &&& m = q) (hz : z ∈ ops m a b) :
    norm q z ∈ ops q (norm q a) (norm q b) := by
  obtain ⟨s,t,rfl⟩ := op_cases hz
  rw [proj_norm _ _ _ hsub]
  exact norm_gate _ _ _ _ _

end PEqualNP.Outside.L_meta_14486.SignedCert

namespace PEqualNP.Outside.L_meta_14486.SignedCert

theorem norm_zero (m : W) : norm m 0 = 0 := by
  change norm m (0#256) = 0#256
  simp [norm]

theorem op_swap (m a b : W) : ops m a b = ops m b a := by
  ext z
  constructor
  all_goals
    intro hz
    obtain ⟨s,t,rfl⟩ := op_cases hz
    rw [BitVec.and_comm]
    exact op_mem _ _ _ _ _

theorem op_flat {m a z : W} (hz : z ∈ ops m 0 a) : z = 0 ∨ z = norm m a := by
  obtain ⟨s,t,rfl⟩ := op_cases hz
  have h1 (v : W) : (~~~(0 : W)) &&& v = v := @BitVec.allOnes_and _ v
  have h2 (v : W) : (0 : W) &&& v = 0 := @BitVec.zero_and _ v
  cases s
  · left
    change norm m ((0 : W) &&& phase t a) = 0
    rw [h2,norm_zero]
  · right
    change norm m ((~~~(0 : W)) &&& phase t a) = norm m a
    rw [h1]
    cases t
    · rfl
    · exact norm_neg _ _

theorem op_same {m a z : W} (hz : z ∈ ops m a a) : z = 0 ∨ z = norm m a := by
  obtain ⟨s,t,rfl⟩ := op_cases hz
  cases s <;> cases t
  · right; exact congrArg (norm m) BitVec.and_self
  · left; exact (congrArg (norm m) (BitVec.and_not_self a)).trans (norm_zero m)
  · left; exact (congrArg (norm m) (BitVec.not_and_self a)).trans (norm_zero m)
  · right; exact (congrArg (norm m) BitVec.and_self).trans (norm_neg m a)

theorem more {α : Type} [DecidableEq α] {o : α → α → Finset α} {g : α} {k l : ℕ} {s : Finset α}
    (hkl : k ≤ l) (hh : build o g k s) : build o g l s := by
  induction hkl with
  | refl => exact hh
  | step _ ih => exact Or.inl ih

theorem enlarge {α : Type} [DecidableEq α] {o : α → α → Finset α} {g : α} {k : ℕ} {s b : Finset α}
    (hsub : s ⊆ b) (hh : build o g k s) : build o g k b := by
  induction k generalizing s b with
  | zero => exact hsub hh
  | succ k ih =>
    rcases hh with skip | ⟨a,ha,c,hc,hn,z,hz,tail⟩
    · exact Or.inl (ih hsub skip)
    · exact Or.inr ⟨a,hsub ha,c,hsub hc,hn,z,hz,ih (Finset.insert_subset_insert _ hsub) tail⟩

def bank (q : W) (S : Finset W) : Finset W := insert 0 (S.image (norm q))
def flat (q : W) (S : Finset W) : Bool := decide (0 ∈ S.image (norm q))

theorem tailBank {z a b : W} {r A : Finset W} {q : W}
    (h : bank q (insert a (insert b r)) ⊆ A) (hz : norm q z ∈ A) :
    bank q (insert z r) ⊆ A := by
  intro x hx
  simp only [bank,Finset.image_insert,Finset.mem_insert] at hx
  rcases hx with rfl | rfl | hr
  · exact h (by simp [bank])
  · exact hz
  · exact h (by simp [bank,hr])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem projected {m q g : W} {k : ℕ} {S : Finset W} (sub : q &&& m = q)
    (nz : norm q g ≠ 0) (run : live (ops m) g k S) {A : Finset W} (ha : bank q S ⊆ A) :
    build (ops q) (norm q g) (k - (flat q S).toNat) A := by
  induction k generalizing S A with
  | zero =>
    change S = {g} at run
    subst S
    rw [Nat.zero_sub]
    exact ha (show norm q g ∈ bank q {g} by simp [bank])
  | succ k ih =>
    rcases run with skip | ⟨a,ham,b,hbm,hab,z,hz,hnew,r,hs,tail⟩
    · exact more (by omega) (ih skip ha)
    subst S
    have za := proj_op sub hz
    have am : norm q a ∈ A := ha (by simp [bank])
    have bm : norm q b ∈ A := ha (by simp [bank])
    by_cases free : norm q z ∈ A
    · have h := ih tail (tailBank ha free)
      apply more _ h
      cases flat q (insert a (insert b r)) <;> simp <;> omega
    · have zne : norm q z ≠ 0 := fun e => free (e ▸ ha (by simp [bank]))
      have an : norm q a ≠ 0 := by
        intro e
        rw [e] at za
        rcases op_flat za with zz | zz
        · exact zne zz
        · exact free (by rw [zz,norm_idem]; exact bm)
      have bn : norm q b ≠ 0 := by
        intro e
        rw [op_swap q, e] at za
        rcases op_flat za with zz | zz
        · exact zne zz
        · exact free (by rw [zz,norm_idem]; exact am)
      have ne : norm q a ≠ norm q b := by
        intro e
        rw [e] at za
        rcases op_same za with zz | zz
        · exact zne zz
        · exact free (by rw [zz,norm_idem]; exact bm)
      have liftA := Finset.subset_insert (norm q z) A
      have htail := ih tail (tailBank (ha.trans liftA) (Finset.mem_insert_self ..))
      have eflat : flat q (insert z r) = flat q (insert a (insert b r)) := by
        simp only [flat, Finset.image_insert, Finset.mem_insert, Ne.symm zne, Ne.symm an, Ne.symm bn, false_or]
      rw [eflat] at htail
      have step : build (ops q) (norm q g) ((k - (flat q (insert a (insert b r))).toNat) + 1) A :=
        Or.inr ⟨_,am,_,bm,ne,_,za,htail⟩
      have hkpos : 0 < k ∨ flat q (insert a (insert b r)) = false := by
        cases k with
        | zero =>
          right
          change insert z r = {g} at tail
          have h : flat q (insert z r) = false := by rw [tail]; simp only [flat, Finset.image_singleton, Finset.mem_singleton, Ne.symm nz, decide_false]
          exact eflat ▸ h
        | succ => exact Or.inl (by omega)
      apply more _ step
      rcases hkpos with h | h
      · cases flat q (insert a (insert b r)) <;> simp <;> omega
      · simp [h]

end PEqualNP.Outside.L_meta_14486.SignedCert

namespace PEqualNP.Outside.L_meta_14486.SignedCert

abbrev Recipe := W × W × W
structure Bound where
  mask : W
  inputs : List W
  goal : W
  cost : ℕ

def Valid (b : Bound) : Prop := ∀ k < b.cost, ¬build (ops b.mask) b.goal k b.inputs.toFinset

def recipe (q : W) (raw : List W) : List Recipe → List W → ℕ → Bool
  | [], need, _ => need.all (fun v => raw.contains v)
  | (z,a,b)::rest, need, credit =>
    let out := norm q z
    let u := norm q a
    let v := norm q b
    if need.contains out && !raw.contains out && out != u && out != v &&
        u != v && (opList q u v).contains out then
      credit != 0 && recipe q raw rest (u :: v :: need.filter (· != out)) (credit-1)
    else recipe q raw rest need credit

theorem recipe_sound {q g : W} {raw need : List W} {h : List Recipe} {d n : ℕ}
    (ok : recipe q raw h need d = true) (run : build (ops q) g n need.toFinset) :
    build (ops q) g (n+d) raw.toFinset := by
  induction h generalizing n d need with
  | nil =>
    have sub : need.toFinset ⊆ raw.toFinset := by
      intro x hx
      exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (List.all_eq_true.mp ok x (List.mem_toFinset.mp hx)))
    exact more (by omega) (enlarge sub run)
  | cons hd rest ih =>
    obtain ⟨z,a,b⟩ := hd
    simp only [recipe] at ok
    split at ok
    · rename_i yes
      simp only [Bool.and_eq_true, bne_iff_ne, List.contains_iff_mem] at yes ok
      let u := norm q a
      let v := norm q b
      let out := norm q z
      let newPool := (u :: v :: need.filter (· != out)).toFinset
      have hu : u ∈ newPool := by simp [newPool]
      have hv : v ∈ newPool := by simp [newPool]
      have uv : u ≠ v := yes.1.2
      have gate : out ∈ ops q u v := List.mem_toFinset.mpr yes.2
      have cover : need.toFinset ⊆ insert out newPool := by
        intro x hx
        by_cases e : x = out
        · simp [e]
        · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨List.mem_toFinset.mp hx, bne_iff_ne.mpr e⟩))))
      have step : build (ops q) g (n+1) newPool :=
        Or.inr ⟨u,hu,v,hv,uv,out,gate,enlarge cover run⟩
      have r := ih ok.2 step
      have dc := ok.1
      have e : n + 1 + (d - 1) = n + d := by omega
      rw [e] at r
      exact r
    · exact ih ok run

def cut (m g : W) (b : Bound) (k : ℕ) (ws : List W) (h : List Recipe) : Bool :=
  let q := b.mask
  let left := k - (ws.any (fun a => norm q a == 0)).toNat
  ((q &&& m) == q) && ((norm q g) == b.goal) && (b.goal != 0) && decide (left < b.cost) &&
    recipe q b.inputs h (0 :: ws.map (norm q)) (b.cost-1-left)

set_option maxRecDepth 10000 in
theorem cut_sound {m g : W} {b : Bound} (hb : Valid b) {k : ℕ} {ws : List W} {h : List Recipe}
    (yes : cut m g b k ws h = true) (run : live (ops m) g k ws.toFinset) : False := by
  simp only [cut, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at yes
  obtain ⟨⟨⟨⟨sub,eq⟩,nz⟩,small⟩,rec⟩ := yes
  have flat_eq : flat b.mask ws.toFinset = ws.any (fun a => norm b.mask a == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [flat,decide_eq_true_eq,Finset.mem_image,List.mem_toFinset,List.any_eq_true,beq_iff_eq]
  have bank_eq : bank b.mask ws.toFinset = (0 :: ws.map (norm b.mask)).toFinset := by
    ext v
    simp [bank]
  have p := projected sub (eq ▸ nz) run (A := bank b.mask ws.toFinset) (fun _ h => h)
  rw [flat_eq,bank_eq,eq] at p
  have bad := recipe_sound rec p
  exact hb _ (by omega) bad

end PEqualNP.Outside.L_meta_14486.SignedCert

namespace PEqualNP.Outside.L_meta_14486.SignedCert

def sep : List W → W → W → Bool
  | [], p, n => p == 0 || n == 0
  | x::r, p, n => (p == 0 || n == 0) ||
    (sep r (p &&& x) (n &&& x) && sep r (p &&& ~~~x) (n &&& ~~~x))

theorem some_bit {x : W} (hn : x ≠ 0) : ∃ i : Fin 256, x[i.val] = true := by
  by_contra! h
  apply hn
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simpa using h ⟨i,hi⟩

theorem sep_ok {ws : List W} {p n : W}
    (h : ∀ i j : Fin 256, p[i.val] = true → n[j.val] = true → ∃ w ∈ ws, w[i.val] ≠ w[j.val]) :
    sep ws p n = true := by
  induction ws generalizing p n with
  | nil =>
    by_cases hp : p = 0
    · simp [sep,hp]
    by_cases hn : n = 0
    · simp [sep,hn]
    obtain ⟨i,hi⟩ := some_bit hp
    obtain ⟨j,hj⟩ := some_bit hn
    obtain ⟨w,hw,_⟩ := h i j hi hj
    simp at hw
  | cons a ws ih =>
    simp only [sep,Bool.or_eq_true,Bool.and_eq_true]
    right
    constructor
    all_goals
      apply ih
      intro i j hi hj
      simp only [BitVec.getElem_and,BitVec.getElem_not,Bool.and_eq_true,Bool.not_eq_true'] at hi hj
      obtain ⟨w,hw,hd⟩ := h i j hi.1 hj.1
      rcases List.mem_cons.mp hw with e | hm
      · subst w
        exact (hd (hi.2.trans hj.2.symm)).elim
      · exact ⟨w,hm,hd⟩

theorem op_agree {m a b z : W} {i j : Fin 256} (hm : m[i.val] = m[j.val])
    (ha : a[i.val] = a[j.val]) (hb : b[i.val] = b[j.val]) (hz : z ∈ ops m a b) :
    z[i.val] = z[j.val] := by
  obtain ⟨s,t,rfl⟩ := op_cases hz
  obtain ⟨u,e⟩ := norm_cases m (phase s a &&& phase t b)
  rw [e]
  cases s <;> cases t <;> cases u <;> simp only [phase,ite_true,Bool.false_eq_true,ite_false,
    BitVec.getElem_and,BitVec.getElem_not,hm,ha,hb]

theorem sep_live {k : ℕ} {m g : W} {ws : List W} (hr : live (ops m) g k ws.toFinset) :
    sep ws (m &&& g) (m &&& ~~~g) = true := by
  apply sep_ok
  intro i j hi hj
  simp only [BitVec.getElem_and,BitVec.getElem_not,Bool.and_eq_true,Bool.not_eq_true'] at hi hj
  obtain ⟨w,hw,hd⟩ := live_separates (D := fun w : W => w[i.val] ≠ w[j.val])
    (by simp [hi.2,hj.2]) (fun a b z hz h => by
      by_contra! fail
      exact h (op_agree (hi.1.trans hj.1.symm) fail.1 fail.2 hz)) hr
  exact ⟨w,List.mem_toFinset.mp hw,hd⟩

def Canon (m : W) (s : Finset W) : Prop := ∀ w ∈ s, norm m w = w

theorem op_canon {m a b z : W} (h : z ∈ ops m a b) : norm m z = z := by
  obtain ⟨s,t,rfl⟩ := op_cases h
  exact norm_idem .. 

theorem no_zero {k : ℕ} {m g : W} {s : Finset W} (ng : g ≠ 0) (ca : Canon m s)
    (h : live (ops m) g k s) : 0 ∉ s := by
  induction k generalizing s with
  | zero => change s = {g} at h; rw [h]; simpa using Ne.symm ng
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,_,z,hz,hout,r,hs,tail⟩
    · exact ih ca skip
    intro h0
    rw [hs] at h0
    rcases Finset.mem_insert.mp h0 with e | h0
    · rw [← e] at hz
      rcases op_flat hz with he | he
      · exact hout (he ▸ e ▸ ha)
      · exact hout ((he.trans (ca b hb)) ▸ hb)
    rcases Finset.mem_insert.mp h0 with e | h0
    · rw [op_swap,← e] at hz
      rcases op_flat hz with he | he
      · exact hout (he ▸ e ▸ hb)
      · exact hout ((he.trans (ca a ha)) ▸ ha)
    have cr : Canon m (insert z r) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hm
      · exact op_canon hz
      · exact ca _ (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    exact ih cr tail (Finset.mem_insert_of_mem h0)

end PEqualNP.Outside.L_meta_14486.SignedCert

namespace PEqualNP.Outside.L_meta_14486.SignedCert
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

abbrev Node := List W × List Recipe
def next (m : W) (ws : List W) (h : List Recipe) : List Node :=
  (pairs ws).flatMap fun (a,b,r) =>
    (opList m a b).flatMap fun z =>
      if ws.contains z then [] else
        (keepChoices a b r).map (fun kept => (z::kept, (z,a,b)::h))

def allowed (m g : W) (bounds : List Bound) (k : ℕ) (ws : List W) (h : List Recipe) : Bool :=
  decide (ws.length ≤ k+1) && !ws.contains 0 && sep ws (m &&& g) (m &&& ~~~g) &&
    !bounds.any (fun b => decide (k ≤ b.cost) && cut m g b k ws h)

def walk (m g : W) (bounds : List Bound) : ℕ → List W → List Recipe → Bool
  | 0, ws, _ => ws == [g]
  | k+1, ws, h => ws == [g] || (allowed m g bounds (k+1) ws h &&
      (next m ws h).any (fun st => walk m g bounds k st.1 st.2))

theorem allowed_live {m g : W} {bounds : List Bound} (bv : ∀ b ∈ bounds, Valid b) (gn : g ≠ 0)
    {k : ℕ} {ws : List W} (ca : Canon m ws.toFinset) (nd : ws.Nodup) (h : List Recipe)
    (run : live (ops m) g k ws.toFinset) : allowed m g bounds k ws h = true := by
  have card := live_card run
  rw [List.toFinset_card_of_nodup nd] at card
  have nz := no_zero gn ca run
  have no : bounds.any (fun b => decide (k ≤ b.cost) && cut m g b k ws h) = false := by
    apply List.any_eq_false.mpr
    intro b hb
    by_cases hcut : cut m g b k ws h = true
    · exact (cut_sound (bv b hb) hcut run).elim
    · simp [Bool.eq_false_iff.mpr hcut]
  simp [allowed,card,sep_live run,no]
  exact fun h => nz (List.mem_toFinset.mpr h)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem walk_live {m g : W} {bounds : List Bound} (bv : ∀ b ∈ bounds, Valid b) (gn : g ≠ 0)
    {k : ℕ} {ws : List W} (ca : Canon m ws.toFinset) (nd : ws.Nodup) (h : List Recipe)
    (run : live (ops m) g k ws.toFinset) : walk m g bounds k ws h = true := by
  induction k generalizing ws h with
  | zero =>
    have hs : ws = [g] := singleton_list nd run
    simp [walk,hs]
  | succ k ih =>
    rcases first_live run with done | ⟨a,ha,b,hb,hab,z,hz,hout,need,hs,tail⟩
    · simp [walk,singleton_list nd done]
    have ok := allowed_live bv gn ca nd h run
    simp only [walk,ok,Bool.true_and,Bool.or_eq_true,List.any_eq_true]
    right
    obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (pm : (a,b,r) ∈ pairs ws) (perm : ws.Perm (a::b::r))
        (hset : ws.toFinset = insert a (insert b need)) (hop : z ∈ ops m a b) :
        ∃ n ∈ next m ws h, walk m g bounds k n.1 n.2 = true := by
      obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm nd hset
      have hznew : z ∉ kept := fun hu => hout (hset ▸ Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
      have newCa : Canon m (z::kept).toFinset := by
        intro u hu
        rcases List.mem_cons.mp (List.mem_toFinset.mp hu) with rfl | hu
        · exact op_canon hop
        · exact ca _ (hset ▸ Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      refine ⟨(z::kept,(z,a,b)::h),?_,ih newCa hnd _ (by simpa [hfin] using tail)⟩
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),pm,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      have hzws : z ∉ ws := fun hh => hout (List.mem_toFinset.mpr hh)
      simp only [List.contains_iff_mem,hzws,ite_false,List.mem_map]
      exact ⟨kept,hk,rfl⟩
    rcases hm with direct | swap
    · exact go direct hp hs hz
    · exact go swap (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (op_swap m a b ▸ hz)

def verify (m g : W) (bs : List Bound) (k : ℕ) (raw : List W) : Bool :=
  !raw.sublists.any (fun ws => walk m g bs k ws [])

theorem lower_of_verify {m g : W} {bs : List Bound} {raw : List W} {b : ℕ}
    (bv : ∀ c ∈ bs, Valid c) (gn : g ≠ 0) (nd : raw.Nodup) (ca : Canon m raw.toFinset)
    (v : verify m g bs (b-1) raw = true) : Valid ⟨m,raw,g,b⟩ := by
  intro k hk run
  change k < b at hk
  change build (ops m) g k raw.toFinset at run
  have run' := more (show k ≤ b-1 by omega) run
  obtain ⟨s,hs,hl⟩ := compress run'
  classical
  let ws := raw.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have walks :=  walk_live bv gn (ws := ws) (fun w hw => ca w (hs (eq ▸ hw))) (nd.filter _) []
    (eq.symm ▸ hl)
  have yes : raw.sublists.any (fun u => walk m g bs (b-1) u []) = true :=
    List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),walks⟩
  simp [verify,yes] at v

theorem canon_checked {m : W} {xs : List W} (h : xs.all (fun x => norm m x == x) = true) :
    Canon m xs.toFinset := fun w hw => beq_iff_eq.mp (List.all_eq_true.mp h w (List.mem_toFinset.mp hw))

end PEqualNP.Outside.L_meta_14486.SignedCert

namespace PEqualNP.Outside.L_meta_14486.SignedCert.Source
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

def bit (k : Fin 256) (z : W) : Bool := z[k.val]
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 100000 in
theorem compile (goal : W) (nz : ~~~goal ≠ 0) (no : ~~~goal ≠ ~~~0) (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim (nz zero)
    · exact False.elim (no ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩


theorem source_op {m a b z : W} (hz : z ∈ basicOps a b) :
    norm m z ∈ PEqualNP.Outside.L_meta_14486.SignedCert.ops m (norm m a) (norm m b) := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact norm_gate m a b false false
  · have h := norm_gate m a b true true
    change norm m (~~~a &&& ~~~b) ∈ _ at h
    simpa only [← BitVec.not_or,norm_neg] using h
  · exact norm_gate m a b false true
  · rw [BitVec.and_comm]
    exact norm_gate m a b true false

theorem to_canonical {m t : W} {k : ℕ} {S : Finset W} (run : build basicOps t k S) :
    build (PEqualNP.Outside.L_meta_14486.SignedCert.ops m) (norm m t) k (bank m S) := by
  induction k generalizing S with
  | zero => exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ run)
  | succ k ih =>
    rcases run with skip | ⟨a,ha,b,hb,_,z,hz,tail⟩
    · exact Or.inl (ih skip)
    have next := ih tail
    have eq : bank m (insert z S) = insert (norm m z) (bank m S) := by
      simp only [bank,Finset.image_insert,Finset.insert_comm (0 : W) (norm m z)]
    rw [eq] at next
    have am : norm m a ∈ bank m S := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha)
    have bm : norm m b ∈ bank m S := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hb)
    have op := source_op (m := m) hz
    by_cases he : norm m a = norm m b
    · rw [he] at op
      have mem : norm m z ∈ bank m S := by
        rcases op_same op with zz | zz
        · rw [zz]; exact Finset.mem_insert_self ..
        · rw [zz,norm_idem]; exact bm
      rw [Finset.insert_eq_of_mem mem] at next
      exact Or.inl next
    · exact Or.inr ⟨_,am,_,bm,he,_,op,next⟩

theorem binary_lb {b : Bound} (valid : Valid b) (w : W) (raw : List W) (F : (Fin 8 → Bool) → Bool)
    (nz : w ≠ 0) (no : w ≠ ~~~0) (dim : raw.length = 8)
    (stk : bank b.mask raw.toFinset ⊆ b.inputs.toFinset) (tg : norm b.mask w = b.goal)
    (rows : ∀ k : Fin 256, F (fun i => bit k (raw.getD i.val 0)) = bit k w)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (evals : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : b.cost ≤ binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ raw, holds raw.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have eval (k : Fin 256) :
      (gs.foldl step (raw.map (bit k))).getD o false = bit k (~~~(~~~w)) := by
    let x (i : Fin 8) := bit k (raw.getD i.val 0)
    have same : List.ofFn x = raw.map (bit k) := by
      apply List.ext_getElem
      · simp [dim]
      · intro i hi hj
        have hi' : i < raw.length := by simpa using hj
        simp only [List.getElem_ofFn,List.getElem_map,x,List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hi',Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (raw.map (bit k)) = _
    rw [← same,evals,BitVec.not_not]
    exact rows k
  obtain ⟨t,ht,run⟩ := compile (~~~w) (by simpa only [BitVec.not_not] using nz)
    (by simpa only [BitVec.not_not] using no) gs o hg raw raw.toFinset init eval
  have can := enlarge stk (to_canonical (m := b.mask) run)
  rcases ht with rfl | rfl <;> simp only [BitVec.not_not,norm_neg,tg] at can
  all_goals exact valid _ low can

end PEqualNP.Outside.L_meta_14486.SignedCert.Source

namespace PEqualNP.Outside.L_meta_14486.SignedCert
abbrev Cell := ℕ × List W
def Closed (m g : W) (c : Cell) : Prop := c.2.Nodup → Canon m c.2.toFinset → ¬live (ops m) g c.1 c.2.toFinset

theorem has_child {m g : W} {k : ℕ} {ws : List W} (ca : Canon m ws.toFinset) (nd : ws.Nodup)
    (h : List Recipe) (neq : ws ≠ [g]) (run : live (ops m) g (k+1) ws.toFinset) :
    ∃ n ∈ next m ws h, n.1.Nodup ∧ Canon m n.1.toFinset ∧ live (ops m) g k n.1.toFinset := by
    rcases first_live run with done | ⟨a,ha,b,hb,hab,z,hz,hout,need,hs,tail⟩
    · exact (neq (singleton_list nd done)).elim
    obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (pm : (a,b,r) ∈ pairs ws) (perm : ws.Perm (a::b::r))
        (hset : ws.toFinset = insert a (insert b need)) (hop : z ∈ ops m a b) :
        ∃ n ∈ next m ws h, n.1.Nodup ∧ Canon m n.1.toFinset ∧ live (ops m) g k n.1.toFinset := by
      obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm nd hset
      have hznew : z ∉ kept := fun hu => hout (hset ▸ Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
      have newCa : Canon m (z::kept).toFinset := by
        intro u hu
        rcases List.mem_cons.mp (List.mem_toFinset.mp hu) with rfl | hu
        · exact op_canon hop
        · exact ca _ (hset ▸ Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)))
      refine ⟨(z::kept,(z,a,b)::h),?_,hnd,newCa,(by simpa [hfin] using tail)⟩
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),pm,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      have hzws : z ∉ ws := fun hh => hout (List.mem_toFinset.mpr hh)
      simp only [List.contains_iff_mem,hzws,ite_false,List.mem_map]
      exact ⟨kept,hk,rfl⟩
    rcases hm with direct | swap
    · exact go direct hp hs hz
    · exact go swap (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (op_swap m a b ▸ hz)

def trivialClose (g : W) (k : ℕ) (ws : List W) : Bool :=
  (k == 0 && ws != [g]) || decide (k+1 < ws.length) || ws.contains 0

theorem trivial_sound {m g : W} {k : ℕ} {ws : List W} (gn : g ≠ 0)
    (yes : trivialClose g k ws = true) : Closed m g (k,ws) := by
  intro nd ca run
  change ws.Nodup at nd
  simp only [trivialClose,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,
    List.contains_iff_mem,decide_eq_true_eq] at yes
  rcases yes with (⟨rfl,hn⟩ | size) | hzro
  · exact hn (singleton_list nd run)
  · have card := live_card run
    change ws.toFinset.card ≤ k+1 at card
    rw [List.toFinset_card_of_nodup nd] at card
    omega
  · exact no_zero gn ca run (List.mem_toFinset.mpr hzro)

def clash (m g : W) (ws : List W) (t : ℕ) : Bool :=
  let i := t % 256
  let j := t / 256 % 256
  (m.getLsbD i == m.getLsbD j) && (g.getLsbD i != g.getLsbD j) &&
    ws.all (fun x => x.getLsbD i == x.getLsbD j)

theorem clash_sound {m g : W} {ws : List W} {t k : ℕ}
    (yes : clash m g ws t = true) : Closed m g (k,ws) := by
  intro _ _ run
  let i : Fin 256 := ⟨t%256,Nat.mod_lt _ (by decide)⟩
  let j : Fin 256 := ⟨t/256%256,Nat.mod_lt _ (by decide)⟩
  simp only [clash,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at yes
  have hm : m[i.val] = m[j.val] := yes.1.1
  have hg : g[i.val] ≠ g[j.val] := yes.1.2
  obtain ⟨w,hw,hd⟩ := live_separates (D := fun w : W => w[i.val] ≠ w[j.val]) hg
    (fun a b z hz hh => by
      by_contra! fail
      exact hh (op_agree hm fail.1 fail.2 hz)) run
  exact hd (beq_iff_eq.mp (List.all_eq_true.mp yes.2 w (List.mem_toFinset.mp hw)))

def sameCell (k : ℕ) (ws : List W) (c : Cell) : Bool :=
  k == c.1 && ws.all (fun w => c.2.contains w) && c.2.all (fun w => ws.contains w)

theorem same_sound {m g : W} {k : ℕ} {ws : List W} {c : Cell} (v : Closed m g c)
    (nd : c.2.Nodup) (yes : sameCell k ws c = true) : Closed m g (k,ws) := by
  intro _ ca run
  simp only [sameCell,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.contains_iff_mem] at yes
  have eq : ws.toFinset = c.2.toFinset := by
    ext w
    simpa only [List.mem_toFinset] using Iff.intro (yes.1.2 w) (yes.2 w)
  apply v nd
  · change Canon m ws.toFinset at ca
    rwa [← eq]
  · change live (ops m) g k ws.toFinset at run
    rwa [← yes.1.1, ← eq]

def tag (m g : W) (bs : List Bound) (seen : List Cell) (k : ℕ) (n : Node) (t : ℕ) : Bool :=
  if t = 0 then trivialClose g k n.1
  else if t ≤ 16384 then clash m g n.1 (t-1)
  else if t < 32768 then (bs[t-16385]?).any (fun b => cut m g b k n.1 n.2)
  else (seen[t-32768]?).any (sameCell k n.1)

theorem tag_sound {m g : W} {bs : List Bound} {seen : List Cell} {k : ℕ} {n : Node} {t : ℕ}
    (gn : g ≠ 0) (bv : ∀ b ∈ bs, Valid b) (sv : ∀ c ∈ seen, c.2.Nodup ∧ Closed m g c)
    (h : tag m g bs seen k n t = true) : Closed m g (k,n.1) := by
  unfold tag at h
  split at h
  · exact trivial_sound gn h
  split at h
  · exact clash_sound h
  split at h
  · cases eq : bs[t-16385]? with
    | none => simp [eq] at h
    | some b =>
      rw [eq] at h
      exact fun _ _ => cut_sound (bv b (List.mem_of_getElem? eq)) h
  · cases eq : seen[t-32768]? with
    | none => simp [eq] at h
    | some c =>
      rw [eq] at h
      have ok := sv c (List.mem_of_getElem? eq)
      exact same_sound ok.2 ok.1 h

def tags (check : Node → ℕ → Bool) : List Node → ℕ → Bool
  | [], _ => true
  | n::ns, p => check n (p % 65536) && tags check ns (p >>> 16)

theorem tags_all {check : Node → ℕ → Bool} {P : Node → Prop} (sound : ∀ n t, check n t = true → P n)
    {ns : List Node} {p : ℕ} (ok : tags check ns p = true) : ∀ n ∈ ns, P n := by
  induction ns generalizing p with
  | nil => simp
  | cons n ns ih =>
    simp only [tags,Bool.and_eq_true] at ok
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact sound _ _ ok.1
    · exact ih ok.2 _ hx

theorem cell_of_tags {m g : W} {bs : List Bound} {seen : List Cell} {k : ℕ} {ws : List W}
    (gn : g ≠ 0) (bv : ∀ b ∈ bs, Valid b) (sv : ∀ c ∈ seen, c.2.Nodup ∧ Closed m g c)
    (h : List Recipe) (p : ℕ) (neq : ws ≠ [g])
    (ok : tags (tag m g bs seen k) (next m ws h) p = true) : Closed m g (k+1,ws) := by
  intro nd ca run
  obtain ⟨n,hn,hd,hc,liveN⟩ := has_child ca nd h neq run
  exact tags_all (fun _ _ yes => tag_sound gn bv sv yes) ok n hn hd hc liveN

theorem bound_of_tags {m g : W} {bs : List Bound} {seen : List Cell} {b : ℕ} {raw : List W}
    (gn : g ≠ 0) (bv : ∀ c ∈ bs, Valid c) (sv : ∀ c ∈ seen, c.2.Nodup ∧ Closed m g c)
    (nd : raw.Nodup) (ca : Canon m raw.toFinset) (p : ℕ)
    (ok : tags (tag m g bs seen (b-1)) (raw.sublists.map (fun ws => (ws,[]))) p = true) :
    Valid ⟨m,raw,g,b⟩ := by
  intro k hk run
  change k < b at hk
  change build (ops m) g k raw.toFinset at run
  obtain ⟨s,hs,hl⟩ := compress (more (show k ≤ b-1 by omega) run)
  classical
  let ws := raw.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have mem : (ws,([] : List Recipe)) ∈ raw.sublists.map (fun us => (us,[])) :=
    List.mem_map.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),rfl⟩
  exact tags_all (fun _ _ yes => tag_sound gn bv sv yes) ok _ mem (nd.filter _)
    (fun w hw => ca w (hs (eq ▸ hw))) (eq.symm ▸ hl)

theorem familyNil {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := by simp

theorem familyCons {α : Type} {P : α → Prop} {a : α} {xs : List α} (v : P a)
    (vs : ∀ x ∈ xs, P x) : ∀ x ∈ a::xs, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact v
  · exact vs x hx

end PEqualNP.Outside.L_meta_14486.SignedCert

namespace PEqualNP.Outside.L_meta_14486.SignedCert

def smallTag (m g : W) (bs : List Bound) (seen : List Cell) (k : ℕ) (n : Node) (t : ℕ) : Bool :=
  if t = 0 then trivialClose g k n.1 || !sep n.1 (m &&& g) (m &&& ~~~g)
  else if t ≤ bs.length then (bs[t-1]?).any (fun b => cut m g b k n.1 n.2)
  else (seen[t-(bs.length+1)]?).any (sameCell k n.1)

theorem small_sound {m g : W} {bs : List Bound} {seen : List Cell} {k : ℕ} {n : Node} {t : ℕ}
    (gn : g ≠ 0) (bv : ∀ b ∈ bs, Valid b) (sv : ∀ c ∈ seen, c.2.Nodup ∧ Closed m g c)
    (h : smallTag m g bs seen k n t = true) : Closed m g (k,n.1) := by
  unfold smallTag at h
  split at h
  · rcases Bool.or_eq_true_iff.mp h with close | sepFail
    · exact trivial_sound gn close
    · intro _ _ run
      simp [sep_live run] at sepFail
  split at h
  · cases eq : bs[t-1]? with
    | none => simp [eq] at h
    | some b =>
      rw [eq] at h
      exact fun _ _ => cut_sound (bv b (List.mem_of_getElem? eq)) h
  · cases eq : seen[t-(bs.length+1)]? with
    | none => simp [eq] at h
    | some c =>
      rw [eq] at h
      have ok := sv c (List.mem_of_getElem? eq)
      exact same_sound ok.2 ok.1 h
def smallTags (width : ℕ) (check : Node → ℕ → Bool) : List Node → ℕ → Bool
  | [], _ => true
  | n::ns, p => check n (p % (2^width)) && smallTags width check ns (p >>> width)

theorem smallTags_all {width : ℕ} {check : Node → ℕ → Bool} {P : Node → Prop} (sound : ∀ n t, check n t = true → P n)
    {ns : List Node} {p : ℕ} (ok : smallTags width check ns p = true) : ∀ n ∈ ns, P n := by
  induction ns generalizing p with
  | nil => simp
  | cons n ns ih =>
    simp only [smallTags,Bool.and_eq_true] at ok
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact sound _ _ ok.1
    · exact ih ok.2 _ hx

theorem small_cell {m g : W} {bs : List Bound} {seen : List Cell} {k : ℕ} {ws : List W}
    (gn : g ≠ 0) (bv : ∀ b ∈ bs, Valid b) (sv : ∀ c ∈ seen, c.2.Nodup ∧ Closed m g c)
    (h : List Recipe) (width p : ℕ) (neq : ws ≠ [g])
    (ok : smallTags width (smallTag m g bs seen k) (next m ws h) p = true) : Closed m g (k+1,ws) := by
  intro nd ca run
  obtain ⟨n,hn,hd,hc,liveN⟩ := has_child ca nd h neq run
  exact smallTags_all (fun _ _ yes => small_sound gn bv sv yes) ok n hn hd hc liveN

theorem small_bound {m g : W} {bs : List Bound} {seen : List Cell} {b : ℕ} {raw : List W}
    (gn : g ≠ 0) (bv : ∀ c ∈ bs, Valid c) (sv : ∀ c ∈ seen, c.2.Nodup ∧ Closed m g c)
    (nd : raw.Nodup) (ca : Canon m raw.toFinset) (width p : ℕ)
    (ok : smallTags width (smallTag m g bs seen (b-1)) (raw.sublists.map (fun ws => (ws,[]))) p = true) :
    Valid ⟨m,raw,g,b⟩ := by
  intro k hk run
  change k < b at hk
  change build (ops m) g k raw.toFinset at run
  obtain ⟨s,hs,hl⟩ := compress (more (show k ≤ b-1 by omega) run)
  classical
  let ws := raw.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have mem : (ws,([] : List Recipe)) ∈ raw.sublists.map (fun us => (us,[])) :=
    List.mem_map.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),rfl⟩
  exact smallTags_all (fun _ _ yes => small_sound gn bv sv yes) ok _ mem (nd.filter _)
    (fun w hw => ca w (hs (eq ▸ hw))) (eq.symm ▸ hl)


end PEqualNP.Outside.L_meta_14486.SignedCert

namespace PEqualNP.Outside.L_meta_14486.SignedCert

def keepBudget (k : ℕ) (a b : W) (r : List W) : List (List W) :=
  if r.length+2 ≤ k then [r,a::r,b::r,a::b::r]
  else if r.length+1 ≤ k then [r,a::r,b::r]
  else if r.length ≤ k then [r] else []

theorem mem_keepBudget {k : ℕ} {a b : W} {r kept : List W} (hk : kept.length ≤ k)
    (h : kept ∈ keepChoices a b r) : kept ∈ keepBudget k a b r := by
  simp only [keepChoices,List.mem_cons,List.not_mem_nil,or_false] at h
  unfold keepBudget
  split
  · simpa only [List.mem_cons,List.not_mem_nil,or_false] using h
  split
  · rcases h with rfl | rfl | rfl | rfl <;> simp_all <;> omega
  split
  · rcases h with rfl | rfl | rfl | rfl <;> simp_all <;> omega
  · rcases h with rfl | rfl | rfl | rfl <;> simp_all <;> omega

def budgetNext (m : W) (k : ℕ) (ws : List W) (h : List Recipe) : List Node :=
  (pairs ws).flatMap fun (a,b,r) =>
    let kept := keepBudget k a b r
    (opList m a b).flatMap fun z =>
      if ws.contains z then [] else kept.map (fun w => (z::w,(z,a,b)::h))

theorem mem_budgetNext {m : W} {k : ℕ} {ws : List W} {h : List Recipe} {n : Node}
    (mem : n ∈ next m ws h) (nd : n.1.Nodup) {g : W} (run : live (ops m) g k n.1.toFinset) :
    n ∈ budgetNext m k ws h := by
  have size := live_card run
  rw [List.toFinset_card_of_nodup nd] at size
  obtain ⟨⟨a,b,r⟩,ha,hn⟩ := List.mem_flatMap.mp mem
  obtain ⟨z,hz,hn⟩ := List.mem_flatMap.mp hn
  split at hn
  · contradiction
  · rename_i miss
    obtain ⟨kept,hk,rfl⟩ := List.mem_map.mp hn
    apply List.mem_flatMap.mpr
    refine ⟨(a,b,r),ha,List.mem_flatMap.mpr ⟨z,hz,?_⟩⟩
    simp only [miss,Bool.false_eq_true,ite_false,List.mem_map]
    exact ⟨kept,mem_keepBudget (by simpa using size) hk,rfl⟩

end PEqualNP.Outside.L_meta_14486.SignedCert

namespace PEqualNP.Outside.L_meta_14486.SignedCert

abbrev ColorPair := W × W
def mixed : List W → W → W → List ColorPair
  | [], p, n => if p==0 || n==0 then [] else [(p,n)]
  | w::r, p, n => if p==0 || n==0 then [] else
      mixed r (p &&& w) (n &&& w) ++ mixed r (p &&& ~~~w) (n &&& ~~~w)

def resolves (z : W) (c : ColorPair) : Bool :=
  ((c.1 &&& z) == 0 || (c.2 &&& z) == 0) && ((c.1 &&& ~~~z) == 0 || (c.2 &&& ~~~z) == 0)

theorem mixed_resolves (r : List W) (z p n : W) :
    (mixed r p n).all (resolves z) = sep (r++[z]) p n := by
  induction r generalizing p n with
  | nil =>
    simp only [List.nil_append,mixed,sep]
    cases e : (p==0 || n==0) <;> simp [e,resolves]
  | cons w r ih =>
    simp only [mixed,List.cons_append,sep]
    cases e : (p==0 || n==0) <;> simp [e,List.all_append,ih]

def smartNext (m g : W) (k : ℕ) (ws : List W) (h : List Recipe) : List Node :=
  (pairs ws).flatMap fun (a,b,r) =>
    let pools := (keepBudget k a b r).map (fun kept => (kept,mixed kept (m &&& g) (m &&& ~~~g)))
    (opList m a b).flatMap fun z =>
      if ws.contains z || z == 0 then [] else
        (pools.filter (fun v => v.2.all (resolves z))).map (fun v => (z::v.1,(z,a,b)::h))

theorem mem_smartNext {m g : W} {k : ℕ} {ws : List W} {h : List Recipe} {n : Node}
    (gn : g ≠ 0) (mem : n ∈ budgetNext m k ws h) (ca : Canon m n.1.toFinset)
    (run : live (ops m) g k n.1.toFinset) : n ∈ smartNext m g k ws h := by
  obtain ⟨⟨a,b,r⟩,ha,hn⟩ := List.mem_flatMap.mp mem
  obtain ⟨z,hz,hn⟩ := List.mem_flatMap.mp hn
  split at hn
  · contradiction
  · rename_i miss
    obtain ⟨kept,hk,rfl⟩ := List.mem_map.mp hn
    have nz : z ≠ 0 := by
      intro e
      apply no_zero gn ca run
      simp [e]
    have eq : (kept++[z]).toFinset = (z::kept).toFinset := by ext w; simp [or_comm]
    have good := sep_live (ws := kept++[z]) (m := m) (g := g) (k := k)
      (by rw [eq]; exact run)
    rw [← mixed_resolves] at good
    apply List.mem_flatMap.mpr
    refine ⟨(a,b,r),ha,List.mem_flatMap.mpr ⟨z,hz,?_⟩⟩
    simp only [miss,beq_iff_eq.mpr,beq_eq_false_iff_ne.mpr nz,Bool.false_or,Bool.false_eq_true,ite_false,List.mem_map]
    refine ⟨(kept,mixed kept (m &&& g) (m &&& ~~~g)),List.mem_filter.mpr ⟨?_,good⟩,rfl⟩
    exact List.mem_map.mpr ⟨kept,hk,rfl⟩

end PEqualNP.Outside.L_meta_14486.SignedCert

namespace PEqualNP.Outside.L_meta_14486.SignedCert

def evalWord {α : Type} (w : W) (f : W → α) : α :=
  Nat.rec (f 0) (fun j _ => f (BitVec.ofNat 256 (j+1))) w.toNat

theorem evalWord_eq {α : Type} (w : W) (f : W → α) : evalWord w f = f w := by
  unfold evalWord
  generalize h : w.toNat = t
  cases t with
  | zero =>
    change f 0 = f w
    apply congrArg f
    exact BitVec.eq_of_toNat_eq (by simpa using h.symm)
  | succ t =>
    change f (BitVec.ofNat 256 (t+1)) = f w
    rw [← h]
    simp

def cachedMixed : List W → W → W → List ColorPair
  | [], p, n => evalWord p (fun pp => evalWord n (fun nn => if pp==0 || nn==0 then [] else [(pp,nn)]))
  | w::r, p, n => evalWord p (fun pp => evalWord n (fun nn =>
      if pp==0 || nn==0 then [] else
        cachedMixed r (pp &&& w) (nn &&& w) ++ cachedMixed r (pp &&& ~~~w) (nn &&& ~~~w)))

theorem cached_eq (r : List W) (p n : W) : cachedMixed r p n = mixed r p n := by
  induction r generalizing p n <;> simp [cachedMixed,mixed,evalWord_eq, *]

def cachedNext (m g : W) (k : ℕ) (ws : List W) (h : List Recipe) : List Node :=
  (pairs ws).flatMap fun (a,b,r) =>
    let pools := (keepBudget k a b r).map (fun kept => (kept,cachedMixed kept (m &&& g) (m &&& ~~~g)))
    (opList m a b).flatMap fun w => evalWord w (fun z =>
      if ws.contains z || z == 0 then [] else
        (pools.filter (fun v => v.2.all (resolves z))).map (fun v => (z::v.1,(z,a,b)::h)))

theorem cachedNext_eq (m g : W) (k : ℕ) (ws : List W) (h : List Recipe) :
    cachedNext m g k ws h = smartNext m g k ws h := by simp [cachedNext,smartNext,cached_eq,evalWord_eq]
end PEqualNP.Outside.L_meta_14486.SignedCert

namespace PEqualNP.Outside.L_meta_14486.SignedCert

def flatCount (q : W) (s : Finset W) := (s.filter (fun w => norm q w = 0)).card

theorem count_nonzero {q w : W} {s : Finset W} (nw : norm q w ≠ 0) :
    flatCount q (insert w s) = flatCount q s := by simp only [flatCount,Finset.filter_insert,if_neg nw]
theorem count_zero {q w : W} {s : Finset W} (nz : norm q w = 0) (fresh : w ∉ s) :
    flatCount q (insert w s) = flatCount q s + 1 := by simp [flatCount,Finset.filter_insert,nz,fresh]
theorem count_step (q w : W) (s : Finset W) : flatCount q (insert w s) ≤ flatCount q s + 1 := by
  by_cases inside : w ∈ s
  · simp [Finset.insert_eq_of_mem inside]
  by_cases flat : norm q w = 0
  · rw [count_zero flat inside]
  · rw [count_nonzero flat]; omega

theorem count_saved {m q g : W} {k : ℕ} {s : Finset W} (sub : q &&& m = q) (nz : norm q g ≠ 0)
    (run : live (ops m) g k s) {A : Finset W} (hs : bank q s ⊆ A) :
    ∃ t, t + flatCount q s ≤ k ∧ build (ops q) (norm q g) t A := by
  induction k generalizing s A with
  | zero =>
    change s = {g} at run
    subst s
    refine ⟨0,?_,hs (by simp [bank])⟩
    simp [flatCount]
    exact nz
  | succ k ih =>
    rcases run with skip | ⟨a,ha,b,hb,_,z,hz,hnew,r,he,tail⟩
    · obtain ⟨t,h,got⟩ := ih skip hs
      exact ⟨t,by omega,got⟩
    subst s
    have op := proj_op sub hz
    have am : norm q a ∈ A := hs (by simp [bank])
    have bm : norm q b ∈ A := hs (by simp [bank])
    have zero : (0 : W) ∈ A := hs (by simp [bank])
    have fresh : z ∉ r := fun h => hnew (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    by_cases free : norm q z ∈ A
    · obtain ⟨t,ht,hbuild⟩ := ih tail (tailBank hs free)
      refine ⟨t,?_,hbuild⟩
      have h1 := count_step q a (insert b r)
      have h2 := count_step q b r
      have mono : flatCount q r ≤ flatCount q (insert z r) := Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
      by_cases af : norm q a = 0
      · by_cases bf : norm q b = 0
        · rw [af,bf] at op
          have zf : norm q z = 0 := by
            rcases op_flat op with s | s
            · exact s
            · simpa only [norm_zero] using s
          rw [count_zero zf fresh] at ht
          omega
        · rw [count_nonzero bf] at h1
          omega
      · rw [count_nonzero af]
        omega
    · have zn : norm q z ≠ 0 := fun e => free (e ▸ zero)
      have an : norm q a ≠ 0 := by
        intro e
        rw [e] at op
        rcases op_flat op with eq | eq
        · exact zn eq
        · exact free (by rw [eq,norm_idem]; exact bm)
      have bn : norm q b ≠ 0 := by
        intro e
        rw [op_swap q,e] at op
        rcases op_flat op with eq | eq
        · exact zn eq
        · exact free (by rw [eq,norm_idem]; exact am)
      have ne : norm q a ≠ norm q b := by
        intro e
        rw [e] at op
        rcases op_same op with eq | eq
        · exact zn eq
        · exact free (by rw [eq,norm_idem]; exact bm)
      obtain ⟨t,ht,hbld⟩ := ih tail (tailBank (hs.trans (Finset.subset_insert (norm q z) A)) (Finset.mem_insert_self ..))
      rw [count_nonzero zn] at ht
      refine ⟨t+1,?_,Or.inr ⟨_,am,_,bm,ne,_,op,hbld⟩⟩
      rw [count_nonzero an,count_nonzero bn]; omega

def multiCut (m g : W) (b : Bound) (k : ℕ) (ws : List W) (h : List Recipe) : Bool :=
  let q := b.mask
  let left := k - (ws.filter (fun a => norm q a == 0)).length
  ((q &&& m) == q) && ((norm q g) == b.goal) && (b.goal != 0) && decide (left < b.cost) &&
    recipe q b.inputs h (0 :: ws.map (norm q)) (b.cost-1-left)

theorem multi_sound {m g : W} {b : Bound} {k : ℕ} {ws : List W} {h : List Recipe} (vb : Valid b)
    (ok : multiCut m g b k ws h = true) (nd : ws.Nodup) (run : live (ops m) g k ws.toFinset) : False := by
  simp only [multiCut,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨sub,eq⟩,nz⟩,low⟩,rec⟩ := ok
  have fc : flatCount b.mask ws.toFinset = (ws.filter (fun a => norm b.mask a == 0)).length := by
    have same : ws.toFinset.filter (fun a => norm b.mask a = 0) = (ws.filter (fun a => norm b.mask a == 0)).toFinset := by
      ext a; simp
    rw [flatCount,same,List.toFinset_card_of_nodup (nd.filter _)]
  have bank_eq : bank b.mask ws.toFinset = (0 :: ws.map (norm b.mask)).toFinset := by ext v; simp [bank]
  obtain ⟨t,small,proj⟩ := count_saved sub (eq ▸ nz) run (A := bank b.mask ws.toFinset) (fun _ h => h)
  rw [fc] at small
  rw [bank_eq,eq] at proj
  have rebuilt := recipe_sound rec proj
  exact vb _ (by omega) rebuilt
end PEqualNP.Outside.L_meta_14486.SignedCert

namespace PEqualNP.Outside.L_meta_14486.SignedCert

abbrev RecordPage := Array (ℕ × ℕ)
abbrev Records := Array RecordPage

def getRecord (rs : Records) (i : ℕ) : Option (ℕ × ℕ) :=
  (rs[i/32]?).bind (fun page => page[i%32]?)

theorem below_capacity {rs : Records} {i : ℕ} {r : ℕ × ℕ} (h : getRecord rs i = some r) :
    i < rs.size * 32 := by
  unfold getRecord at h
  cases eq : rs[i/32]? with
  | none => simp [eq] at h
  | some a =>
    have bound := (Array.getElem?_eq_some_iff.mp eq).1
    omega

def materialize {α : Type} (w : W) (f : W → α) : α :=
  Nat.rec (f 0) (fun j _ => f (BitVec.ofNat 256 (j+1))) w.toNat

def initialWords : List W → ℕ → List W
  | [], _ => []
  | w::ws, p => if p%2=1 then w :: initialWords ws (p >>> 1) else initialWords ws (p >>> 1)

def replayOne (m : W) (n : Node) (tok : ℕ) : Node :=
  let a := n.1.getD (tok % 16) 0
  let b := n.1.getD (tok >>> 4 % 16) 0
  let z := (opList m a b).getD (tok >>> 8 % 4) 0
  let r := (n.1.erase a).erase b
  let kept := (keepChoices a b r).getD (tok >>> 10 % 4) []
  materialize z (fun value => (value::kept,(value,a,b)::n.2))

def replayTail (m : W) : ℕ → ℕ → Node → Node
  | 0, _, n => n
  | d+1, p, n => replayTail m d (p >>> 12) (replayOne m n (p % 4096))

def replay (b : Bound) (k p : ℕ) : Node :=
  replayTail b.mask (b.cost-1-k) (p >>> 9) (initialWords b.inputs (p % 512),[])

def recorded (b : Bound) (k : ℕ) (rs : Records) (i : ℕ) : Option Cell :=
  (getRecord rs i).map (fun r => (k,(replay b k r.1).1))

def LayerOK (b : Bound) (k : ℕ) (rs : Records) : Prop :=
  ∀ i c, recorded b k rs i = some c → c.2.Nodup ∧ Closed b.mask b.goal c

def cheap (m g : W) (k : ℕ) (ws : List W) : Bool :=
  trivialClose g k ws || !sep ws (m &&& g) (m &&& ~~~g)

theorem cheap_sound {m g : W} {k : ℕ} {ws : List W} (gn : g ≠ 0)
    (ok : cheap m g k ws = true) : Closed m g (k,ws) := by
  rcases Bool.or_eq_true_iff.mp ok with stop | fail
  · exact trivial_sound gn stop
  · intro _ _ run
    simp [sep_live run] at fail

def skipNode (checkSep : Bool) (b : Bound) (k : ℕ) (ws : List W) : Bool :=
  if checkSep then cheap b.mask b.goal k ws else trivialClose b.goal k ws

def sparse (checkSep : Bool) (b : Bound) (bs : Array Bound) (k : ℕ) (old : Records) (cw rw : ℕ) :
    List Node → ℕ → Bool
  | [], _ => true
  | n::ns, p =>
    if skipNode checkSep b k n.1 then sparse checkSep b bs k old cw rw ns p
    else if p % 2 = 0 then
      (bs[(p >>> 1) % 2^cw]?).any (fun s => multiCut b.mask b.goal s k n.1 n.2) &&
        sparse checkSep b bs k old cw rw ns (p >>> (cw+1))
    else
      (recorded b k old ((p >>> 1) % 2^rw)).any (sameCell k n.1) &&
        sparse checkSep b bs k old cw rw ns (p >>> (rw+1))

theorem sparse_sound {checkSep : Bool} {b : Bound} {bs : Array Bound} {old : Records} {k cw rw : ℕ}
    (gn : b.goal ≠ 0) (bv : ∀ s ∈ bs, Valid s) (prev : LayerOK b k old)
    {ns : List Node} {p : ℕ} (ok : sparse checkSep b bs k old cw rw ns p = true) :
    ∀ n ∈ ns, Closed b.mask b.goal (k,n.1) := by
  induction ns generalizing p with
  | nil => simp
  | cons a ns ih =>
    have comb (ha : Closed b.mask b.goal (k,a.1)) {p' : ℕ} (rest : sparse checkSep b bs k old cw rw ns p' = true) :
        ∀ n ∈ a::ns, Closed b.mask b.goal (k,n.1) := by
      intro n h
      rcases List.mem_cons.mp h with rfl | h
      · exact ha
      · exact ih rest n h
    simp only [sparse] at ok
    split at ok
    · rename_i cc
      cases checkSep with
      | false => exact comb (trivial_sound gn cc) ok
      | true => exact comb (cheap_sound gn cc) ok
    split at ok
    · simp only [Bool.and_eq_true] at ok
      apply comb _ ok.2
      obtain ⟨yes,_⟩ := ok
      generalize ee : bs[(p >>> 1) % 2^cw]? = x at yes
      cases x with
      | none => contradiction
      | some s => exact fun nd _ => multi_sound (bv s (Array.mem_of_getElem? ee)) yes nd
    · simp only [Bool.and_eq_true] at ok
      apply comb _ ok.2
      obtain ⟨yes,_⟩ := ok
      generalize ee : recorded b k old ((p >>> 1) % 2^rw) = x at yes
      cases x with
      | none => contradiction
      | some c =>
        have h := prev _ _ ee
        exact same_sound h.2 h.1 yes

def rowCheck (b : Bound) (bs : Array Bound) (k : ℕ) (old : Records) (cw rw : ℕ) (rec : ℕ × ℕ) : Bool :=
  let n := replay b (k+1) rec.1
  decide n.1.Nodup && n.1 != [b.goal] && sparse false b bs k old cw rw (cachedNext b.mask b.goal k n.1 n.2) rec.2

theorem row_sound {b : Bound} {bs : Array Bound} {old : Records} {k cw rw : ℕ}
    (gn : b.goal ≠ 0) (bv : ∀ s ∈ bs, Valid s) (prev : LayerOK b k old)
    {r : ℕ × ℕ} (ok : rowCheck b bs k old cw rw r = true) :
    (replay b (k+1) r.1).1.Nodup ∧ Closed b.mask b.goal (k+1,(replay b (k+1) r.1).1) := by
  simp only [rowCheck,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
  refine ⟨ok.1.1,fun nd ca run => ?_⟩
  obtain ⟨n,hn,hd,hc,hr⟩ := has_child ca nd (replay b (k+1) r.1).2 ok.1.2 run
  exact sparse_sound gn bv prev ok.2 n ((cachedNext_eq ..) ▸ mem_smartNext gn (mem_budgetNext hn hd hr) hc hr) hd hc hr

def checkBlock (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | k+1, s => f s && checkBlock f k (s+1)

theorem block_at {f : ℕ → Bool} {s n i : ℕ} (ok : checkBlock f n s = true)
    (lo : s ≤ i) (hi : i < s+n) : f i = true := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    simp only [checkBlock,Bool.and_eq_true] at ok
    by_cases e : i = s
    · exact e ▸ ok.1
    · exact ih ok.2 (by omega) (by omega)

theorem block_merge {f : ℕ → Bool} {s l r : ℕ} (a : checkBlock f l s = true)
    (b : checkBlock f r (s+l) = true) : checkBlock f (l+r) s = true := by
  induction l generalizing s with
  | zero => simpa using b
  | succ l ih =>
    rw [Nat.succ_add]
    simp only [checkBlock,Bool.and_eq_true] at a ⊢
    exact ⟨a.1,ih a.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using b)⟩

def testAt (b : Bound) (bs : Array Bound) (k : ℕ) (old now : Records) (cw rw i : ℕ) : Bool :=
  (getRecord now i).all (rowCheck b bs k old cw rw)

theorem layer_of_block {b : Bound} {bs : Array Bound} {old now : Records} {k cw rw : ℕ}
    (gn : b.goal ≠ 0) (bv : ∀ s ∈ bs, Valid s) (prev : LayerOK b k old)
    (ok : checkBlock (testAt b bs k old now cw rw) (now.size*32) 0 = true) : LayerOK b (k+1) now := by
  intro i c h
  cases ee : getRecord now i with
  | none => simp [recorded,ee] at h
  | some r =>
    have mem := below_capacity ee
    have v := block_at ok (Nat.zero_le i) (by simpa using mem)
    simp only [testAt,ee,Option.all_some] at v
    simp only [recorded,ee,Option.map_some,Option.some.injEq] at h
    subst c
    exact row_sound gn bv prev v

theorem emptyOK (b : Bound) (k : ℕ) : LayerOK b k #[] := by
  intro i c h
  simp [recorded,getRecord] at h

theorem bound_of_layers {b : Bound} {bs : Array Bound} {last : Records} {cw rw : ℕ}
    (gn : b.goal ≠ 0) (bv : ∀ s ∈ bs, Valid s) (prev : LayerOK b (b.cost-1) last)
    (nd : b.inputs.Nodup) (ca : Canon b.mask b.inputs.toFinset) (p : ℕ)
    (ok : sparse true b bs (b.cost-1) last cw rw (b.inputs.sublists.map (fun ws => (ws,[]))) p = true) : Valid b := by
  intro k hk run
  obtain ⟨s,hs,hl⟩ := compress (more (show k ≤ b.cost-1 by omega) run)
  classical
  let ws := b.inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have mem : (ws,([] : List Recipe)) ∈ b.inputs.sublists.map (fun us => (us,[])) :=
    List.mem_map.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),rfl⟩
  exact sparse_sound gn bv prev ok _ mem (nd.filter _) (fun w hw => ca w (hs (eq ▸ hw))) (eq.symm ▸ hl)

end PEqualNP.Outside.L_meta_14486.SignedCert

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T152 : Bound := ⟨0x5000000050000000500000005, [0x0, 0x1000000010000000100000001, 0x50000000000000005, 0x500000005], 0x10000000100000005, 4⟩
def bsT152 : Array Bound := [].toArray
theorem vbsT152 : ∀ s ∈ bsT152, Valid s := by
  intro s hs
  simp only [bsT152,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T152r3p0 : RecordPage := #[
(0xe, 0x0)]
def T152r3 : Records := #[T152r3p0]
def testT152r3 : ℕ → Bool := testAt T152 bsT152 2 (#[] : Records) T152r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T152r3c0 : checkBlock testT152r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT152r3 : LayerOK T152 3 T152r3 := by
  apply layer_of_block (bs := bsT152) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT152 (emptyOK _ _)
  exact @block_merge testT152r3 0 1 31 T152r3c0 (show checkBlock testT152r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT152 : Valid T152 := by
  apply bound_of_layers (bs := bsT152) (last := T152r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT152 vT152r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T153 : Bound := ⟨0x50000000500000005000000050000, [0x0, 0x10000000100000001000000010000, 0x500000000000000050000, 0x5000000050000], 0x100000001000000050000, 4⟩
def bsT153 : Array Bound := [].toArray
theorem vbsT153 : ∀ s ∈ bsT153, Valid s := by
  intro s hs
  simp only [bsT153,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T153r3p0 : RecordPage := #[
(0xe, 0x0)]
def T153r3 : Records := #[T153r3p0]
def testT153r3 : ℕ → Bool := testAt T153 bsT153 2 (#[] : Records) T153r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T153r3c0 : checkBlock testT153r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT153r3 : LayerOK T153 3 T153r3 := by
  apply layer_of_block (bs := bsT153) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT153 (emptyOK _ _)
  exact @block_merge testT153r3 0 1 31 T153r3c0 (show checkBlock testT153r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT153 : Valid T153 := by
  apply bound_of_layers (bs := bsT153) (last := T153r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT153 vT153r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T154 : Bound := ⟨0x110000001100000000000000000000001100000011, [0x0, 0x10000000100000000000000000000000100000001, 0x1100000000000000000000000000000011, 0x1100000011], 0x100000000000000000000000100000011, 4⟩
def bsT154 : Array Bound := [].toArray
theorem vbsT154 : ∀ s ∈ bsT154, Valid s := by
  intro s hs
  simp only [bsT154,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T154r3p0 : RecordPage := #[
(0xe, 0x0)]
def T154r3 : Records := #[T154r3p0]
def testT154r3 : ℕ → Bool := testAt T154 bsT154 2 (#[] : Records) T154r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T154r3c0 : checkBlock testT154r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT154r3 : LayerOK T154 3 T154r3 := by
  apply layer_of_block (bs := bsT154) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT154 (emptyOK _ _)
  exact @block_merge testT154r3 0 1 31 T154r3c0 (show checkBlock testT154r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT154 : Valid T154 := by
  apply bound_of_layers (bs := bsT154) (last := T154r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT154 vT154r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T155 : Bound := ⟨0x220000002200000000000000000000002200000022, [0x0, 0x20000000200000000000000000000000200000002, 0x2200000000000000000000000000000022, 0x2200000022], 0x200000000000000000000000200000022, 4⟩
def bsT155 : Array Bound := [].toArray
theorem vbsT155 : ∀ s ∈ bsT155, Valid s := by
  intro s hs
  simp only [bsT155,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T155r3p0 : RecordPage := #[
(0xe, 0x0)]
def T155r3 : Records := #[T155r3p0]
def testT155r3 : ℕ → Bool := testAt T155 bsT155 2 (#[] : Records) T155r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T155r3c0 : checkBlock testT155r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT155r3 : LayerOK T155 3 T155r3 := by
  apply layer_of_block (bs := bsT155) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT155 (emptyOK _ _)
  exact @block_merge testT155r3 0 1 31 T155r3c0 (show checkBlock testT155r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT155 : Valid T155 := by
  apply bound_of_layers (bs := bsT155) (last := T155r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT155 vT155r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T316 : Bound := ⟨0xf000f00000000000f000f, [0x0, 0x500050000000000050005, 0x300030000000000030003, 0xf000000000000000f, 0xf000f], 0x10001000000000005000f, 4⟩
def bsT316 : Array Bound := [].toArray
theorem vbsT316 : ∀ s ∈ bsT316, Valid s := by
  intro s hs
  simp only [bsT316,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T316r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T316r3 : Records := #[T316r3p0]
def testT316r3 : ℕ → Bool := testAt T316 bsT316 2 (#[] : Records) T316r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T316r3c0 : checkBlock testT316r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT316r3 : LayerOK T316 3 T316r3 := by
  apply layer_of_block (bs := bsT316) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT316 (emptyOK _ _)
  exact @block_merge testT316r3 0 1 31 T316r3c0 (show checkBlock testT316r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT316 : Valid T316 := by
  apply bound_of_layers (bs := bsT316) (last := T316r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT316 vT316r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T317 : Bound := ⟨0xf000f00000000000f000f0, [0x0, 0x5000500000000000500050, 0x3000300000000000300030, 0xf000000000000000f0, 0xf000f0], 0x10001000000000005000f0, 4⟩
def bsT317 : Array Bound := [].toArray
theorem vbsT317 : ∀ s ∈ bsT317, Valid s := by
  intro s hs
  simp only [bsT317,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T317r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T317r3 : Records := #[T317r3p0]
def testT317r3 : ℕ → Bool := testAt T317 bsT317 2 (#[] : Records) T317r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T317r3c0 : checkBlock testT317r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT317r3 : LayerOK T317 3 T317r3 := by
  apply layer_of_block (bs := bsT317) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT317 (emptyOK _ _)
  exact @block_merge testT317r3 0 1 31 T317r3c0 (show checkBlock testT317r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT317 : Valid T317 := by
  apply bound_of_layers (bs := bsT317) (last := T317r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT317 vT317r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T318 : Bound := ⟨0x33000000330000003300000033, [0x0, 0x11000000110000001100000011, 0x3000000030000000300000003, 0x330000000000000033, 0x3300000033], 0x110000000300000033, 4⟩
def bsT318 : Array Bound := [].toArray
theorem vbsT318 : ∀ s ∈ bsT318, Valid s := by
  intro s hs
  simp only [bsT318,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T318r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T318r3 : Records := #[T318r3p0]
def testT318r3 : ℕ → Bool := testAt T318 bsT318 2 (#[] : Records) T318r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T318r3c0 : checkBlock testT318r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT318r3 : LayerOK T318 3 T318r3 := by
  apply layer_of_block (bs := bsT318) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT318 (emptyOK _ _)
  exact @block_merge testT318r3 0 1 31 T318r3c0 (show checkBlock testT318r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT318 : Valid T318 := by
  apply bound_of_layers (bs := bsT318) (last := T318r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT318 vT318r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T319 : Bound := ⟨0x30003000300030003000300030003, [0x0, 0x10001000100010001000100010001, 0x3000000030000000300000003, 0x300030000000000030003, 0x3000300030003], 0x100010001000300010003, 4⟩
def bsT319 : Array Bound := [].toArray
theorem vbsT319 : ∀ s ∈ bsT319, Valid s := by
  intro s hs
  simp only [bsT319,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T319r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T319r3 : Records := #[T319r3p0]
def testT319r3 : ℕ → Bool := testAt T319 bsT319 2 (#[] : Records) T319r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T319r3c0 : checkBlock testT319r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT319r3 : LayerOK T319 3 T319r3 := by
  apply layer_of_block (bs := bsT319) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT319 (emptyOK _ _)
  exact @block_merge testT319r3 0 1 31 T319r3c0 (show checkBlock testT319r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT319 : Valid T319 := by
  apply bound_of_layers (bs := bsT319) (last := T319r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT319 vT319r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T321 : Bound := ⟨0x33003300000000000000000000000000330033, [0x0, 0x11001100000000000000000000000000110011, 0x3000300000000000000000000000000030003, 0x3300000000000000000000000000000033, 0x330033], 0x300000000000000000000000000110033, 4⟩
def bsT321 : Array Bound := [].toArray
theorem vbsT321 : ∀ s ∈ bsT321, Valid s := by
  intro s hs
  simp only [bsT321,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T321r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T321r3 : Records := #[T321r3p0]
def testT321r3 : ℕ → Bool := testAt T321 bsT321 2 (#[] : Records) T321r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T321r3c0 : checkBlock testT321r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT321r3 : LayerOK T321 3 T321r3 := by
  apply layer_of_block (bs := bsT321) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT321 (emptyOK _ _)
  exact @block_merge testT321r3 0 1 31 T321r3c0 (show checkBlock testT321r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT321 : Valid T321 := by
  apply bound_of_layers (bs := bsT321) (last := T321r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT321 vT321r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T322 : Bound := ⟨0xcc00cc00000000000000000000000000cc00cc, [0x0, 0x44004400000000000000000000000000440044, 0xc000c000000000000000000000000000c000c, 0xcc000000000000000000000000000000cc, 0xcc00cc], 0xc000000000000000000000000004400cc, 4⟩
def bsT322 : Array Bound := [].toArray
theorem vbsT322 : ∀ s ∈ bsT322, Valid s := by
  intro s hs
  simp only [bsT322,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T322r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T322r3 : Records := #[T322r3p0]
def testT322r3 : ℕ → Bool := testAt T322 bsT322 2 (#[] : Records) T322r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T322r3c0 : checkBlock testT322r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT322r3 : LayerOK T322 3 T322r3 := by
  apply layer_of_block (bs := bsT322) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT322 (emptyOK _ _)
  exact @block_merge testT322r3 0 1 31 T322r3c0 (show checkBlock testT322r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT322 : Valid T322 := by
  apply bound_of_layers (bs := bsT322) (last := T322r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT322 vT322r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T324 : Bound := ⟨0x300030003000300000000000000000003000300030003, [0x0, 0x100010001000100000000000000000001000100010001, 0x30000000300000000000000000000000300000003, 0x3000300000000000000000000000000030003, 0x3000300030003], 0x300000000000000000001000300010003, 4⟩
def bsT324 : Array Bound := [].toArray
theorem vbsT324 : ∀ s ∈ bsT324, Valid s := by
  intro s hs
  simp only [bsT324,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T324r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T324r3 : Records := #[T324r3p0]
def testT324r3 : ℕ → Bool := testAt T324 bsT324 2 (#[] : Records) T324r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T324r3c0 : checkBlock testT324r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT324r3 : LayerOK T324 3 T324r3 := by
  apply layer_of_block (bs := bsT324) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT324 (emptyOK _ _)
  exact @block_merge testT324r3 0 1 31 T324r3c0 (show checkBlock testT324r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT324 : Valid T324 := by
  apply bound_of_layers (bs := bsT324) (last := T324r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT324 vT324r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T325 : Bound := ⟨0x500050005000500000000000000000005000500050005, [0x0, 0x100010001000100000000000000000001000100010001, 0x50000000500000000000000000000000500000005, 0x5000500000000000000000000000000050005, 0x5000500050005], 0x500000000000000000001000100050005, 4⟩
def bsT325 : Array Bound := [].toArray
theorem vbsT325 : ∀ s ∈ bsT325, Valid s := by
  intro s hs
  simp only [bsT325,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T325r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T325r3 : Records := #[T325r3p0]
def testT325r3 : ℕ → Bool := testAt T325 bsT325 2 (#[] : Records) T325r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T325r3c0 : checkBlock testT325r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT325r3 : LayerOK T325 3 T325r3 := by
  apply layer_of_block (bs := bsT325) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT325 (emptyOK _ _)
  exact @block_merge testT325r3 0 1 31 T325r3c0 (show checkBlock testT325r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT325 : Valid T325 := by
  apply bound_of_layers (bs := bsT325) (last := T325r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT325 vT325r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T326 : Bound := ⟨0x30003000000000003000300000000000300030000000000030003, [0x0, 0x10001000000000001000100000000000100010000000000010001, 0x3000000000000000300000000000000030000000000000003, 0x3000300000000000000000000000000030003, 0x300030000000000030003], 0x1000000000000000300000000000100010000000000010003, 4⟩
def bsT326 : Array Bound := [].toArray
theorem vbsT326 : ∀ s ∈ bsT326, Valid s := by
  intro s hs
  simp only [bsT326,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T326r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T326r3 : Records := #[T326r3p0]
def testT326r3 : ℕ → Bool := testAt T326 bsT326 2 (#[] : Records) T326r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T326r3c0 : checkBlock testT326r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT326r3 : LayerOK T326 3 T326r3 := by
  apply layer_of_block (bs := bsT326) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT326 (emptyOK _ _)
  exact @block_merge testT326r3 0 1 31 T326r3c0 (show checkBlock testT326r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT326 : Valid T326 := by
  apply bound_of_layers (bs := bsT326) (last := T326r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT326 vT326r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T327 : Bound := ⟨0x300000003000000030000000300000003000000030000000300000003, [0x0, 0x100000001000000010000000100000001000000010000000100000001, 0x3000000000000000300000000000000030000000000000003, 0x30000000300000000000000000000000300000003, 0x3000000030000000300000003], 0x1000000000000000300000000000000010000000300000003, 4⟩
def bsT327 : Array Bound := [].toArray
theorem vbsT327 : ∀ s ∈ bsT327, Valid s := by
  intro s hs
  simp only [bsT327,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T327r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T327r3 : Records := #[T327r3p0]
def testT327r3 : ℕ → Bool := testAt T327 bsT327 2 (#[] : Records) T327r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T327r3c0 : checkBlock testT327r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT327r3 : LayerOK T327 3 T327r3 := by
  apply layer_of_block (bs := bsT327) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT327 (emptyOK _ _)
  exact @block_merge testT327r3 0 1 31 T327r3c0 (show checkBlock testT327r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT327 : Valid T327 := by
  apply bound_of_layers (bs := bsT327) (last := T327r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT327 vT327r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T328 : Bound := ⟨0x1000100010001000100010001000100010001000100010001000100010001, [0x0, 0x100000001000000010000000100000001000000010000000100000001, 0x10001000000000001000100000000000100010000000000010001, 0x100010001000100000000000000000001000100010001, 0x10001000100010001000100010001], 0x1000000000000000100000000000100010001000100010001, 4⟩
def bsT328 : Array Bound := [].toArray
theorem vbsT328 : ∀ s ∈ bsT328, Valid s := by
  intro s hs
  simp only [bsT328,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T328r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T328r3 : Records := #[T328r3p0]
def testT328r3 : ℕ → Bool := testAt T328 bsT328 2 (#[] : Records) T328r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T328r3c0 : checkBlock testT328r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT328r3 : LayerOK T328 3 T328r3 := by
  apply layer_of_block (bs := bsT328) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT328 (emptyOK _ _)
  exact @block_merge testT328r3 0 1 31 T328r3c0 (show checkBlock testT328r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT328 : Valid T328 := by
  apply bound_of_layers (bs := bsT328) (last := T328r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT328 vT328r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T329 : Bound := ⟨0xf0000000f0000000f0000000f, [0x0, 0x5000000050000000500000005, 0x3000000030000000300000003, 0xf000000000000000f, 0xf0000000f], 0x1000000030000000f, 5⟩
def bsT329 : Array Bound := [T152].toArray
theorem vbsT329 : ∀ s ∈ bsT329, Valid s := by
  intro s hs
  simp only [bsT329,List.mem_toArray] at hs
  exact (familyCons vT152 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT329 : Valid T329 := by
  apply bound_of_layers (bs := bsT329) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT329 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T330 : Bound := ⟨0x55000000550000005500000055, [0x0, 0x11000000110000001100000011, 0x5000000050000000500000005, 0x550000000000000055, 0x5500000055], 0x110000000100000055, 5⟩
def bsT330 : Array Bound := [T152].toArray
theorem vbsT330 : ∀ s ∈ bsT330, Valid s := by
  intro s hs
  simp only [bsT330,List.mem_toArray] at hs
  exact (familyCons vT152 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT330 : Valid T330 := by
  apply bound_of_layers (bs := bsT330) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT330 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T331 : Bound := ⟨0xf0000000f0000000f0000000f0000, [0x0, 0x50000000500000005000000050000, 0x30000000300000003000000030000, 0xf000000000000000f0000, 0xf0000000f0000], 0x100000001000000050000, 5⟩
def bsT331 : Array Bound := [T153].toArray
theorem vbsT331 : ∀ s ∈ bsT331, Valid s := by
  intro s hs
  simp only [bsT331,List.mem_toArray] at hs
  exact (familyCons vT153 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT331 : Valid T331 := by
  apply bound_of_layers (bs := bsT331) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT331 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T333 : Bound := ⟨0x550000005500000000000000000000005500000055, [0x0, 0x110000001100000000000000000000001100000011, 0x50000000500000000000000000000000500000005, 0x5500000000000000000000000000000055, 0x5500000055], 0x500000000000000000000000100000055, 5⟩
def bsT333 : Array Bound := [T154].toArray
theorem vbsT333 : ∀ s ∈ bsT333, Valid s := by
  intro s hs
  simp only [bsT333,List.mem_toArray] at hs
  exact (familyCons vT154 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT333 : Valid T333 := by
  apply bound_of_layers (bs := bsT333) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT333 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T335 : Bound := ⟨0x1100110011001100000000000000000011001100110011, [0x0, 0x100010001000100000000000000000001000100010001, 0x110000001100000000000000000000001100000011, 0x11001100000000000000000000000000110011, 0x11001100110011], 0x100000000000000000001000100110011, 5⟩
def bsT335 : Array Bound := [T154].toArray
theorem vbsT335 : ∀ s ∈ bsT335, Valid s := by
  intro s hs
  simp only [bsT335,List.mem_toArray] at hs
  exact (familyCons vT154 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT335 : Valid T335 := by
  apply bound_of_layers (bs := bsT335) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT335 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T336 : Bound := ⟨0x2200220022002200000000000000000022002200220022, [0x0, 0x200020002000200000000000000000002000200020002, 0x220000002200000000000000000000002200000022, 0x22002200000000000000000000000000220022, 0x22002200220022], 0x200000000000000000000000200000022, 5⟩
def bsT336 : Array Bound := [T155].toArray
theorem vbsT336 : ∀ s ∈ bsT336, Valid s := by
  intro s hs
  simp only [bsT336,List.mem_toArray] at hs
  exact (familyCons vT155 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT336 : Valid T336 := by
  apply bound_of_layers (bs := bsT336) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT336 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T337 : Bound := ⟨0x500000005000000050000000500000005000000050000000500000005, [0x0, 0x100000001000000010000000100000001000000010000000100000001, 0x5000000000000000500000000000000050000000000000005, 0x50000000500000000000000000000000500000005, 0x5000000050000000500000005], 0x1000000000000000500000000000000010000000100000005, 5⟩
def bsT337 : Array Bound := [T152].toArray
theorem vbsT337 : ∀ s ∈ bsT337, Valid s := by
  intro s hs
  simp only [bsT337,List.mem_toArray] at hs
  exact (familyCons vT152 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT337 : Valid T337 := by
  apply bound_of_layers (bs := bsT337) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT337 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T338 : Bound := ⟨0x1100000011000000110000001100000011000000110000001100000011, [0x0, 0x100000001000000010000000100000001000000010000000100000001, 0x11000000000000001100000000000000110000000000000011, 0x110000001100000000000000000000001100000011, 0x11000000110000001100000011], 0x1000000000000000100000000000000110000000100000011, 5⟩
def bsT338 : Array Bound := [T154].toArray
theorem vbsT338 : ∀ s ∈ bsT338, Valid s := by
  intro s hs
  simp only [bsT338,List.mem_toArray] at hs
  exact (familyCons vT154 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT338 : Valid T338 := by
  apply bound_of_layers (bs := bsT338) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT338 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T339 : Bound := ⟨0x2200000022000000220000002200000022000000220000002200000022, [0x0, 0x200000002000000020000000200000002000000020000000200000002, 0x22000000000000002200000000000000220000000000000022, 0x220000002200000000000000000000002200000022, 0x22000000220000002200000022], 0x200000000000000000000000200000022, 5⟩
def bsT339 : Array Bound := [T155].toArray
theorem vbsT339 : ∀ s ∈ bsT339, Valid s := by
  intro s hs
  simp only [bsT339,List.mem_toArray] at hs
  exact (familyCons vT155 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT339 : Valid T339 := by
  apply bound_of_layers (bs := bsT339) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT339 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T340 : Bound := ⟨0x5000000050000000500000005000000050000000500000005000000050000, [0x0, 0x1000000010000000100000001000000010000000100000001000000010000, 0x50000000000000005000000000000000500000000000000050000, 0x500000005000000000000000000000005000000050000, 0x50000000500000005000000050000], 0x100000001000000050000, 5⟩
def bsT340 : Array Bound := [T153].toArray
theorem vbsT340 : ∀ s ∈ bsT340, Valid s := by
  intro s hs
  simp only [bsT340,List.mem_toArray] at hs
  exact (familyCons vT153 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT340 : Valid T340 := by
  apply bound_of_layers (bs := bsT340) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT340 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T390 : Bound := ⟨0x330033003300330033003300330033, [0x0, 0x110011001100110011001100110011, 0x30003000300030003000300030003, 0x33000000330000003300000033, 0x3300330000000000330033, 0x33003300330033], 0x1100110001000300110033, 5⟩
def bsT390 : Array Bound := [T318].toArray
theorem vbsT390 : ∀ s ∈ bsT390, Valid s := by
  intro s hs
  simp only [bsT390,List.mem_toArray] at hs
  exact (familyCons vT318 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT390 : Valid T390 := by
  apply bound_of_layers (bs := bsT390) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT390 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T394 : Bound := ⟨0xf000f000f000f0000000000000000000f000f000f000f, [0x0, 0x500050005000500000000000000000005000500050005, 0x300030003000300000000000000000003000300030003, 0xf0000000f00000000000000000000000f0000000f, 0xf000f000000000000000000000000000f000f, 0xf000f000f000f], 0xf0000000000000000000100030005000f, 5⟩
def bsT394 : Array Bound := [T324].toArray
theorem vbsT394 : ∀ s ∈ bsT394, Valid s := by
  intro s hs
  simp only [bsT394,List.mem_toArray] at hs
  exact (familyCons vT324 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT394 : Valid T394 := by
  apply bound_of_layers (bs := bsT394) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT394 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T396 : Bound := ⟨0xf000f00000000000f000f00000000000f000f00000000000f000f, [0x0, 0x50005000000000005000500000000000500050000000000050005, 0x30003000000000003000300000000000300030000000000030003, 0xf000000000000000f000000000000000f000000000000000f, 0xf000f000000000000000000000000000f000f, 0xf000f00000000000f000f], 0x1000000000000000f0000000000010001000000000005000f, 5⟩
def bsT396 : Array Bound := [T316].toArray
theorem vbsT396 : ∀ s ∈ bsT396, Valid s := by
  intro s hs
  simp only [bsT396,List.mem_toArray] at hs
  exact (familyCons vT316 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT396 : Valid T396 := by
  apply bound_of_layers (bs := bsT396) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT396 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T397 : Bound := ⟨0x330033000000000033003300000000003300330000000000330033, [0x0, 0x110011000000000011001100000000001100110000000000110011, 0x30003000000000003000300000000000300030000000000030003, 0x33000000000000003300000000000000330000000000000033, 0x33003300000000000000000000000000330033, 0x3300330000000000330033], 0x1000000000000000300000000001100110000000000110033, 5⟩
def bsT397 : Array Bound := [T321].toArray
theorem vbsT397 : ∀ s ∈ bsT397, Valid s := by
  intro s hs
  simp only [bsT397,List.mem_toArray] at hs
  exact (familyCons vT321 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT397 : Valid T397 := by
  apply bound_of_layers (bs := bsT397) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT397 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T398 : Bound := ⟨0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc, [0x0, 0x440044000000000044004400000000004400440000000000440044, 0xc000c00000000000c000c00000000000c000c00000000000c000c, 0xcc00000000000000cc00000000000000cc00000000000000cc, 0xcc00cc00000000000000000000000000cc00cc, 0xcc00cc0000000000cc00cc], 0xc000000000000000000000000004400cc, 5⟩
def bsT398 : Array Bound := [T322].toArray
theorem vbsT398 : ∀ s ∈ bsT398, Valid s := by
  intro s hs
  simp only [bsT398,List.mem_toArray] at hs
  exact (familyCons vT322 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT398 : Valid T398 := by
  apply bound_of_layers (bs := bsT398) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT398 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T399 : Bound := ⟨0xf000f00000000000f000f00000000000f000f00000000000f000f0, [0x0, 0x500050000000000050005000000000005000500000000000500050, 0x300030000000000030003000000000003000300000000000300030, 0xf000000000000000f000000000000000f000000000000000f0, 0xf000f000000000000000000000000000f000f0, 0xf000f00000000000f000f0], 0x10001000000000005000f0, 5⟩
def bsT399 : Array Bound := [T317].toArray
theorem vbsT399 : ∀ s ∈ bsT399, Valid s := by
  intro s hs
  simp only [bsT399,List.mem_toArray] at hs
  exact (familyCons vT317 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT399 : Valid T399 := by
  apply bound_of_layers (bs := bsT399) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT399 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T404 : Bound := ⟨0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f, [0x0, 0x500000005000000050000000500000005000000050000000500000005, 0x300000003000000030000000300000003000000030000000300000003, 0xf000000000000000f000000000000000f000000000000000f, 0xf0000000f00000000000000000000000f0000000f, 0xf0000000f0000000f0000000f], 0x1000000000000000f0000000000000001000000030000000f, 6⟩
def bsT404 : Array Bound := [T329].toArray
theorem vbsT404 : ∀ s ∈ bsT404, Valid s := by
  intro s hs
  simp only [bsT404,List.mem_toArray] at hs
  exact (familyCons vT329 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT404 : Valid T404 := by
  apply bound_of_layers (bs := bsT404) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT404 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T406 : Bound := ⟨0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000, [0x0, 0x5000000050000000500000005000000050000000500000005000000050000, 0x3000000030000000300000003000000030000000300000003000000030000, 0xf000000000000000f000000000000000f000000000000000f0000, 0xf0000000f00000000000000000000000f0000000f0000, 0xf0000000f0000000f0000000f0000], 0x100000001000000050000, 6⟩
def bsT406 : Array Bound := [T331].toArray
theorem vbsT406 : ∀ s ∈ bsT406, Valid s := by
  intro s hs
  simp only [bsT406,List.mem_toArray] at hs
  exact (familyCons vT331 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT406 : Valid T406 := by
  apply bound_of_layers (bs := bsT406) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT406 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T407 : Bound := ⟨0x11001100110011001100110011001100110011001100110011001100110011, [0x0, 0x1000100010001000100010001000100010001000100010001000100010001, 0x1100000011000000110000001100000011000000110000001100000011, 0x110011000000000011001100000000001100110000000000110011, 0x1100110011001100000000000000000011001100110011, 0x110011001100110011001100110011], 0x1000000000000000100000000001100110001000100110011, 6⟩
def bsT407 : Array Bound := [T335].toArray
theorem vbsT407 : ∀ s ∈ bsT407, Valid s := by
  intro s hs
  simp only [bsT407,List.mem_toArray] at hs
  exact (familyCons vT335 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT407 : Valid T407 := by
  apply bound_of_layers (bs := bsT407) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT407 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T408 : Bound := ⟨0x22002200220022002200220022002200220022002200220022002200220022, [0x0, 0x2000200020002000200020002000200020002000200020002000200020002, 0x2200000022000000220000002200000022000000220000002200000022, 0x220022000000000022002200000000002200220000000000220022, 0x2200220022002200000000000000000022002200220022, 0x220022002200220022002200220022], 0x200000000000000000000000200000022, 6⟩
def bsT408 : Array Bound := [T336].toArray
theorem vbsT408 : ∀ s ∈ bsT408, Valid s := by
  intro s hs
  simp only [bsT408,List.mem_toArray] at hs
  exact (familyCons vT336 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT408 : Valid T408 := by
  apply bound_of_layers (bs := bsT408) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT408 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T410 : Bound := ⟨0xf000f000f000f000f000f000f000f, [0x0, 0x50005000500050005000500050005, 0x30003000300030003000300030003, 0xf0000000f0000000f0000000f, 0xf000f00000000000f000f, 0xf000f000f000f], 0x10001000100030005000f, 7⟩
def bsT410 : Array Bound := [T152, T316, T319, T329, T331].toArray
theorem vbsT410 : ∀ s ∈ bsT410, Valid s := by
  intro s hs
  simp only [bsT410,List.mem_toArray] at hs
  exact (familyCons vT152 <| familyCons vT316 <| familyCons vT319 <| familyCons vT329 <| familyCons vT331 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T410r4p0 : RecordPage := #[
(0x4a18823e, 0x0), (0x4818863e, 0x0)]
def T410r4 : Records := #[T410r4p0]
def testT410r4 : ℕ → Bool := testAt T410 bsT410 3 (#[] : Records) T410r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T410r4c0 : checkBlock testT410r4 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT410r4 : LayerOK T410 4 T410r4 := by
  apply layer_of_block (bs := bsT410) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT410 (emptyOK _ _)
  exact @block_merge testT410r4 0 2 30 T410r4c0 (show checkBlock testT410r4 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T410r5p0 : RecordPage := #[
(0x18623e, 0x2), (0x18823e, 0x9), (0x1a823e, 0x68), (0x18863e, 0x13),
(0x1a863e, 0x68)]
def T410r5 : Records := #[T410r5p0]
def testT410r5 : ℕ → Bool := testAt T410 bsT410 4 T410r4 T410r5 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T410r5c0 : checkBlock testT410r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T410r5c1 : checkBlock testT410r5 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT410r5 : LayerOK T410 5 T410r5 := by
  apply layer_of_block (bs := bsT410) (k := 4) (old := T410r4) (cw := 3) (rw := 1) (by decide +kernel) vbsT410 vT410r4
  exact @block_merge testT410r5 0 5 27 (@block_merge testT410r5 0 4 1 T410r5c0 T410r5c1) (show checkBlock testT410r5 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T410r6p0 : RecordPage := #[
(0x3e, 0x22976666686666445324216666000000006668660000)]
def T410r6 : Records := #[T410r6p0]
def testT410r6 : ℕ → Bool := testAt T410 bsT410 5 T410r5 T410r6 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T410r6c0 : checkBlock testT410r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT410r6 : LayerOK T410 6 T410r6 := by
  apply layer_of_block (bs := bsT410) (k := 5) (old := T410r5) (cw := 3) (rw := 3) (by decide +kernel) vbsT410 vT410r5
  exact @block_merge testT410r6 0 1 31 T410r6c0 (show checkBlock testT410r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT410 : Valid T410 := by
  apply bound_of_layers (bs := bsT410) (last := T410r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT410 vT410r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T411 : Bound := ⟨0x3300330033003300000000000000000033003300330033, [0x0, 0x1100110011001100000000000000000011001100110011, 0x300030003000300000000000000000003000300030003, 0x330000003300000000000000000000003300000033, 0x33003300000000000000000000000000330033, 0x33003300330033], 0x300000000000000000001000300110033, 7⟩
def bsT411 : Array Bound := [T154, T321, T324, T335, T336].toArray
theorem vbsT411 : ∀ s ∈ bsT411, Valid s := by
  intro s hs
  simp only [bsT411,List.mem_toArray] at hs
  exact (familyCons vT154 <| familyCons vT321 <| familyCons vT324 <| familyCons vT335 <| familyCons vT336 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T411r4p0 : RecordPage := #[
(0x4a18823e, 0x0), (0x4818863e, 0x0)]
def T411r4 : Records := #[T411r4p0]
def testT411r4 : ℕ → Bool := testAt T411 bsT411 3 (#[] : Records) T411r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T411r4c0 : checkBlock testT411r4 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT411r4 : LayerOK T411 4 T411r4 := by
  apply layer_of_block (bs := bsT411) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT411 (emptyOK _ _)
  exact @block_merge testT411r4 0 2 30 T411r4c0 (show checkBlock testT411r4 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T411r5p0 : RecordPage := #[
(0x18623e, 0x2), (0x18823e, 0x9), (0x1a823e, 0x68), (0x18863e, 0x13),
(0x1a863e, 0x68)]
def T411r5 : Records := #[T411r5p0]
def testT411r5 : ℕ → Bool := testAt T411 bsT411 4 T411r4 T411r5 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T411r5c0 : checkBlock testT411r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T411r5c1 : checkBlock testT411r5 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT411r5 : LayerOK T411 5 T411r5 := by
  apply layer_of_block (bs := bsT411) (k := 4) (old := T411r4) (cw := 3) (rw := 1) (by decide +kernel) vbsT411 vT411r4
  exact @block_merge testT411r5 0 5 27 (@block_merge testT411r5 0 4 1 T411r5c0 T411r5c1) (show checkBlock testT411r5 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T411r6p0 : RecordPage := #[
(0x3e, 0x22970000000044532421000066666866666666866666)]
def T411r6 : Records := #[T411r6p0]
def testT411r6 : ℕ → Bool := testAt T411 bsT411 5 T411r5 T411r6 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T411r6c0 : checkBlock testT411r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT411r6 : LayerOK T411 6 T411r6 := by
  apply layer_of_block (bs := bsT411) (k := 5) (old := T411r5) (cw := 3) (rw := 3) (by decide +kernel) vbsT411 vT411r5
  exact @block_merge testT411r6 0 1 31 T411r6c0 (show checkBlock testT411r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT411 : Valid T411 := by
  apply bound_of_layers (bs := bsT411) (last := T411r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT411 vT411r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T412 : Bound := ⟨0x3300000033000000330000003300000033000000330000003300000033, [0x0, 0x1100000011000000110000001100000011000000110000001100000011, 0x300000003000000030000000300000003000000030000000300000003, 0x33000000000000003300000000000000330000000000000033, 0x330000003300000000000000000000003300000033, 0x33000000330000003300000033], 0x1000000000000000300000000000000110000000300000033, 7⟩
def bsT412 : Array Bound := [T154, T318, T327, T338, T339].toArray
theorem vbsT412 : ∀ s ∈ bsT412, Valid s := by
  intro s hs
  simp only [bsT412,List.mem_toArray] at hs
  exact (familyCons vT154 <| familyCons vT318 <| familyCons vT327 <| familyCons vT338 <| familyCons vT339 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T412r4p0 : RecordPage := #[
(0x4a18423e, 0x0), (0x4818843e, 0x0)]
def T412r4 : Records := #[T412r4p0]
def testT412r4 : ℕ → Bool := testAt T412 bsT412 3 (#[] : Records) T412r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T412r4c0 : checkBlock testT412r4 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT412r4 : LayerOK T412 4 T412r4 := by
  apply layer_of_block (bs := bsT412) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT412 (emptyOK _ _)
  exact @block_merge testT412r4 0 2 30 T412r4c0 (show checkBlock testT412r4 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T412r5p0 : RecordPage := #[
(0x18423e, 0x9), (0x1a423e, 0x68), (0x18823e, 0x2), (0x18843e, 0x13),
(0x1c843e, 0x68)]
def T412r5 : Records := #[T412r5p0]
def testT412r5 : ℕ → Bool := testAt T412 bsT412 4 T412r4 T412r5 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T412r5c0 : checkBlock testT412r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T412r5c1 : checkBlock testT412r5 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT412r5 : LayerOK T412 5 T412r5 := by
  apply layer_of_block (bs := bsT412) (k := 4) (old := T412r4) (cw := 3) (rw := 1) (by decide +kernel) vbsT412 vT412r4
  exact @block_merge testT412r5 0 5 27 (@block_merge testT412r5 0 4 1 T412r5c0 T412r5c1) (show checkBlock testT412r5 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T412r6p0 : RecordPage := #[
(0x3e, 0x2927000024250000443166666666866666686666)]
def T412r6 : Records := #[T412r6p0]
def testT412r6 : ℕ → Bool := testAt T412 bsT412 5 T412r5 T412r6 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T412r6c0 : checkBlock testT412r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT412r6 : LayerOK T412 6 T412r6 := by
  apply layer_of_block (bs := bsT412) (k := 5) (old := T412r5) (cw := 3) (rw := 3) (by decide +kernel) vbsT412 vT412r5
  exact @block_merge testT412r6 0 1 31 T412r6c0 (show checkBlock testT412r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT412 : Valid T412 := by
  apply bound_of_layers (bs := bsT412) (last := T412r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT412 vT412r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T413 : Bound := ⟨0x3000300030003000300030003000300030003000300030003000300030003, [0x0, 0x1000100010001000100010001000100010001000100010001000100010001, 0x300000003000000030000000300000003000000030000000300000003, 0x30003000000000003000300000000000300030000000000030003, 0x300030003000300000000000000000003000300030003, 0x30003000300030003000300030003], 0x1000000000000000300000000000100010001000300010003, 7⟩
def bsT413 : Array Bound := [T319, T324, T326, T327, T328].toArray
theorem vbsT413 : ∀ s ∈ bsT413, Valid s := by
  intro s hs
  simp only [bsT413,List.mem_toArray] at hs
  exact (familyCons vT319 <| familyCons vT324 <| familyCons vT326 <| familyCons vT327 <| familyCons vT328 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T413r4p0 : RecordPage := #[
(0x4818403e, 0x0), (0x4618803e, 0x0), (0x4a18423e, 0x0), (0x4618623e, 0x0),
(0x4a18863e, 0x0)]
def T413r4 : Records := #[T413r4p0]
def testT413r4 : ℕ → Bool := testAt T413 bsT413 3 (#[] : Records) T413r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T413r4c0 : checkBlock testT413r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T413r4c1 : checkBlock testT413r4 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT413r4 : LayerOK T413 4 T413r4 := by
  apply layer_of_block (bs := bsT413) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT413 (emptyOK _ _)
  exact @block_merge testT413r4 0 5 27 (@block_merge testT413r4 0 4 1 T413r4c0 T413r4c1) (show checkBlock testT413r4 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T413r5p0 : RecordPage := #[
(0x18203e, 0x0), (0x18403e, 0x21), (0x18603e, 0x0), (0x18803e, 0x63),
(0x18423e, 0x5), (0x18623e, 0x87), (0x18823e, 0x0), (0x18643e, 0x0),
(0x18843e, 0x0), (0x18863e, 0x49)]
def T413r5 : Records := #[T413r5p0]
def testT413r5 : ℕ → Bool := testAt T413 bsT413 4 T413r4 T413r5 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T413r5c0 : checkBlock testT413r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T413r5c1 : checkBlock testT413r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T413r5c2 : checkBlock testT413r5 2 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT413r5 : LayerOK T413 5 T413r5 := by
  apply layer_of_block (bs := bsT413) (k := 4) (old := T413r4) (cw := 3) (rw := 3) (by decide +kernel) vbsT413 vT413r4
  exact @block_merge testT413r5 0 10 22 (@block_merge testT413r5 0 4 6 T413r5c0 (@block_merge testT413r5 4 4 2 T413r5c1 T413r5c2)) (show checkBlock testT413r5 22 10 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T413r6p0 : RecordPage := #[
(0x3e, 0x826081124278303498968c890803941152106d0c1)]
def T413r6 : Records := #[T413r6p0]
def testT413r6 : ℕ → Bool := testAt T413 bsT413 5 T413r5 T413r6 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T413r6c0 : checkBlock testT413r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT413r6 : LayerOK T413 6 T413r6 := by
  apply layer_of_block (bs := bsT413) (k := 5) (old := T413r5) (cw := 3) (rw := 4) (by decide +kernel) vbsT413 vT413r5
  exact @block_merge testT413r6 0 1 31 T413r6c0 (show checkBlock testT413r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT413 : Valid T413 := by
  apply bound_of_layers (bs := bsT413) (last := T413r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT413 vT413r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T414 : Bound := ⟨0x5000500050005000500050005000500050005000500050005000500050005, [0x0, 0x1000100010001000100010001000100010001000100010001000100010001, 0x500000005000000050000000500000005000000050000000500000005, 0x50005000000000005000500000000000500050000000000050005, 0x500050005000500000000000000000005000500050005, 0x50005000500050005000500050005], 0x1000000000000000500000000000100010001000100050005, 7⟩
def bsT414 : Array Bound := [T152, T325, T328, T337, T340].toArray
theorem vbsT414 : ∀ s ∈ bsT414, Valid s := by
  intro s hs
  simp only [bsT414,List.mem_toArray] at hs
  exact (familyCons vT152 <| familyCons vT325 <| familyCons vT328 <| familyCons vT337 <| familyCons vT340 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T414r4p0 : RecordPage := #[
(0x4818403e, 0x0), (0x4618643e, 0x0)]
def T414r4 : Records := #[T414r4p0]
def testT414r4 : ℕ → Bool := testAt T414 bsT414 3 (#[] : Records) T414r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T414r4c0 : checkBlock testT414r4 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT414r4 : LayerOK T414 4 T414r4 := by
  apply layer_of_block (bs := bsT414) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT414 (emptyOK _ _)
  exact @block_merge testT414r4 0 2 30 T414r4c0 (show checkBlock testT414r4 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T414r5p0 : RecordPage := #[
(0x18403e, 0x9), (0x1a403e, 0x68), (0x18603e, 0x2), (0x18643e, 0x13),
(0x1c643e, 0x68)]
def T414r5 : Records := #[T414r5p0]
def testT414r5 : ℕ → Bool := testAt T414 bsT414 4 T414r4 T414r5 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T414r5c0 : checkBlock testT414r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T414r5c1 : checkBlock testT414r5 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT414r5 : LayerOK T414 5 T414r5 := by
  apply layer_of_block (bs := bsT414) (k := 4) (old := T414r4) (cw := 3) (rw := 1) (by decide +kernel) vbsT414 vT414r4
  exact @block_merge testT414r5 0 5 27 (@block_merge testT414r5 0 4 1 T414r5c0 T414r5c1) (show checkBlock testT414r5 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T414r6p0 : RecordPage := #[
(0x3e, 0x292766668666666666680000242544316666)]
def T414r6 : Records := #[T414r6p0]
def testT414r6 : ℕ → Bool := testAt T414 bsT414 5 T414r5 T414r6 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T414r6c0 : checkBlock testT414r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT414r6 : LayerOK T414 6 T414r6 := by
  apply layer_of_block (bs := bsT414) (k := 5) (old := T414r5) (cw := 3) (rw := 3) (by decide +kernel) vbsT414 vT414r5
  exact @block_merge testT414r6 0 1 31 T414r6c0 (show checkBlock testT414r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT414 : Valid T414 := by
  apply bound_of_layers (bs := bsT414) (last := T414r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT414 vT414r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T415 : Bound := ⟨0x5500000055000000550000005500000055000000550000005500000055, [0x0, 0x1100000011000000110000001100000011000000110000001100000011, 0x500000005000000050000000500000005000000050000000500000005, 0x55000000000000005500000000000000550000000000000055, 0x550000005500000000000000000000005500000055, 0x55000000550000005500000055], 0x1000000000000000500000000000000110000000100000055, 8⟩
def bsT415 : Array Bound := [T152, T154, T330, T333, T337, T338].toArray
theorem vbsT415 : ∀ s ∈ bsT415, Valid s := by
  intro s hs
  simp only [bsT415,List.mem_toArray] at hs
  exact (familyCons vT152 <| familyCons vT154 <| familyCons vT330 <| familyCons vT333 <| familyCons vT337 <| familyCons vT338 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T415r4p0 : RecordPage := #[
(0x4810618203e, 0x0), (0x4a10618203e, 0x0), (0x816618203e, 0x0), (0xa16618203e, 0x0),
(0x4810a18403e, 0x0), (0x4a10a18403e, 0x0), (0x4a1461a403e, 0x0), (0x4814a1a403e, 0x0),
(0x816818803e, 0x0), (0xa16818803e, 0x0), (0x4810818423e, 0x0), (0x4a10818423e, 0x0),
(0x481461a423e, 0x0), (0x481481a423e, 0x0), (0x816818623e, 0x0), (0xa16818623e, 0x0),
(0x4810a18643e, 0x0), (0x4a10a18643e, 0x0), (0x4a1481c643e, 0x0), (0x4a14a1c643e, 0x0),
(0x4a1461c843e, 0x0), (0x4814a1c843e, 0x0), (0x816a18863e, 0x0), (0xa16a18863e, 0x0)]
def T415r4 : Records := #[T415r4p0]
def testT415r4 : ℕ → Bool := testAt T415 bsT415 3 (#[] : Records) T415r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r4c0 : checkBlock testT415r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r4c1 : checkBlock testT415r4 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r4c2 : checkBlock testT415r4 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r4c3 : checkBlock testT415r4 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r4c4 : checkBlock testT415r4 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r4c5 : checkBlock testT415r4 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT415r4 : LayerOK T415 4 T415r4 := by
  apply layer_of_block (bs := bsT415) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT415 (emptyOK _ _)
  exact @block_merge testT415r4 0 24 8 (@block_merge testT415r4 0 12 12 (@block_merge testT415r4 0 4 8 T415r4c0 (@block_merge testT415r4 4 4 4 T415r4c1 T415r4c2)) (@block_merge testT415r4 12 4 8 T415r4c3 (@block_merge testT415r4 16 4 4 T415r4c4 T415r4c5))) (show checkBlock testT415r4 8 24 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T415r5p0 : RecordPage := #[
(0x10618203e, 0x40d81), (0x12618203e, 0x0), (0x14618203e, 0x0), (0x16618203e, 0x41d85a8),
(0x10638203e, 0x68), (0x10658203e, 0x4a), (0xc218403e, 0x24), (0x14618403e, 0x0),
(0x4818403e, 0x0), (0xc818403e, 0x6), (0x10a18403e, 0x62e09), (0x14a18403e, 0x0),
(0x10a38403e, 0x64), (0x1461a403e, 0x10d), (0x10a1a403e, 0x0), (0x14a1a403e, 0x20f),
(0x14818803e, 0x0), (0x16818803e, 0x64e11a4), (0x10858803e, 0x8a), (0xc218423e, 0x4),
(0x14618423e, 0x0), (0x10818423e, 0x45e95), (0x14818423e, 0x0), (0x4a18423e, 0x0),
(0xca18423e, 0x4), (0x10838423e, 0x46), (0x1461a423e, 0x199), (0x1081a423e, 0x0),
(0x1481a423e, 0x29b), (0x14818623e, 0x0), (0x16818623e, 0x47e9d86), (0x10858623e, 0xa8)]
def T415r5p1 : RecordPage := #[
(0xc418643e, 0x24), (0x4618643e, 0x0), (0xc618643e, 0xa), (0x14818643e, 0x0),
(0x10a18643e, 0x88ea1), (0x14a18643e, 0x0), (0x10a58643e, 0xa4), (0x1481c643e, 0x125),
(0x10a1c643e, 0x0), (0x14a1c643e, 0x227), (0xc418843e, 0x4), (0x14618843e, 0x0),
(0x4818843e, 0x0), (0xc818843e, 0x8), (0x14a18843e, 0x0), (0x10a58843e, 0x86),
(0x1461c843e, 0x1a9), (0x14a1c843e, 0x2ab), (0x14a18863e, 0x0), (0x16a18863e, 0x8bead64)]
def T415r5 : Records := #[T415r5p0, T415r5p1]
def testT415r5 : ℕ → Bool := testAt T415 bsT415 4 T415r4 T415r5 3 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r5c0 : checkBlock testT415r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r5c1 : checkBlock testT415r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r5c2 : checkBlock testT415r5 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r5c3 : checkBlock testT415r5 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r5c4 : checkBlock testT415r5 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r5c5 : checkBlock testT415r5 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r5c6 : checkBlock testT415r5 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r5c7 : checkBlock testT415r5 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r5c8 : checkBlock testT415r5 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r5c9 : checkBlock testT415r5 4 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r5c10 : checkBlock testT415r5 4 40 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r5c11 : checkBlock testT415r5 4 44 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r5c12 : checkBlock testT415r5 4 48 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT415r5 : LayerOK T415 5 T415r5 := by
  apply layer_of_block (bs := bsT415) (k := 4) (old := T415r4) (cw := 3) (rw := 5) (by decide +kernel) vbsT415 vT415r4
  exact @block_merge testT415r5 0 52 12 (@block_merge testT415r5 0 24 28 (@block_merge testT415r5 0 12 12 (@block_merge testT415r5 0 4 8 T415r5c0 (@block_merge testT415r5 4 4 4 T415r5c1 T415r5c2)) (@block_merge testT415r5 12 4 8 T415r5c3 (@block_merge testT415r5 16 4 4 T415r5c4 T415r5c5))) (@block_merge testT415r5 24 12 16 (@block_merge testT415r5 24 4 8 T415r5c6 (@block_merge testT415r5 28 4 4 T415r5c7 T415r5c8)) (@block_merge testT415r5 36 8 8 (@block_merge testT415r5 36 4 4 T415r5c9 T415r5c10) (@block_merge testT415r5 44 4 4 T415r5c11 T415r5c12)))) (show checkBlock testT415r5 12 52 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T415r6p0 : RecordPage := #[
(0x18203e, 0x1120a05d03350988a8404062620e141818a88), (0x18403e, 0x8a8cd1509aaa1a85d0ab1311322c503e00d550d), (0x1a403e, 0x899aaa86a1f43ac4c506e01d550d), (0x18803e, 0x10912a433519a044a462624684e9580804a44),
(0x18423e, 0x20219c0b8884e8080c57a032d6574a680c4427), (0x1a423e, 0x1122213a02033966f4d681c4427), (0x18623e, 0x1819fb52243382668640407aedbaba2a26866), (0x18643e, 0x1a6b3f62226682c92d24c478574545161d134166),
(0x1c643e, 0x1a88999a0a534a313e1bd15134166), (0x18843e, 0x12fa02250044aa8d75a4c0405bb30155e8aa5544), (0x1c843e, 0x12001112ab636a301015868ea5544), (0x18863e, 0x12fa42134d606a4464cf968c98080a2a24644)]
def T415r6 : Records := #[T415r6p0]
def testT415r6 : ℕ → Bool := testAt T415 bsT415 5 T415r5 T415r6 3 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r6c0 : checkBlock testT415r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r6c1 : checkBlock testT415r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r6c2 : checkBlock testT415r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT415r6 : LayerOK T415 6 T415r6 := by
  apply layer_of_block (bs := bsT415) (k := 5) (old := T415r5) (cw := 3) (rw := 6) (by decide +kernel) vbsT415 vT415r5
  exact @block_merge testT415r6 0 12 20 (@block_merge testT415r6 0 4 8 T415r6c0 (@block_merge testT415r6 4 4 4 T415r6c1 T415r6c2)) (show checkBlock testT415r6 20 12 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T415r7p0 : RecordPage := #[
(0x3e, 0x464ba5526d167a4203433621694a43b531551471501)]
def T415r7 : Records := #[T415r7p0]
def testT415r7 : ℕ → Bool := testAt T415 bsT415 6 T415r6 T415r7 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T415r7c0 : checkBlock testT415r7 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT415r7 : LayerOK T415 7 T415r7 := by
  apply layer_of_block (bs := bsT415) (k := 6) (old := T415r6) (cw := 3) (rw := 4) (by decide +kernel) vbsT415 vT415r6
  exact @block_merge testT415r7 0 1 31 T415r7c0 (show checkBlock testT415r7 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT415 : Valid T415 := by
  apply bound_of_layers (bs := bsT415) (last := T415r7) (cw := 3) (rw := 0) (by decide +kernel) vbsT415 vT415r7 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T421 : Bound := ⟨0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, [0x0, 0x550055000000000055005500000000005500550000000000550055, 0x330033000000000033003300000000003300330000000000330033, 0xf000f00000000000f000f00000000000f000f00000000000f000f, 0xff00000000000000ff00000000000000ff00000000000000ff, 0xff00ff00000000000000000000000000ff00ff, 0xff00ff0000000000ff00ff], 0x1000000000000000f000000000011001100000000005500ff, 7⟩
def bsT421 : Array Bound := [T396, T397, T398, T399].toArray
theorem vbsT421 : ∀ s ∈ bsT421, Valid s := by
  intro s hs
  simp only [bsT421,List.mem_toArray] at hs
  exact (familyCons vT396 <| familyCons vT397 <| familyCons vT398 <| familyCons vT399 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T421r6p0 : RecordPage := #[
(0x7e, 0x186514)]
def T421r6 : Records := #[T421r6p0]
def testT421r6 : ℕ → Bool := testAt T421 bsT421 5 (#[] : Records) T421r6 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T421r6c0 : checkBlock testT421r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT421r6 : LayerOK T421 6 T421r6 := by
  apply layer_of_block (bs := bsT421) (k := 5) (old := (#[] : Records)) (cw := 2) (rw := 1) (by decide +kernel) vbsT421 (emptyOK _ _)
  exact @block_merge testT421r6 0 1 31 T421r6c0 (show checkBlock testT421r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT421 : Valid T421 := by
  apply bound_of_layers (bs := bsT421) (last := T421r6) (cw := 2) (rw := 0) (by decide +kernel) vbsT421 vT421r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T424 : Bound := ⟨0xff00ff00ff00ff00ff00ff00ff00ff, [0x0, 0x550055005500550055005500550055, 0x330033003300330033003300330033, 0xf000f000f000f000f000f000f000f, 0xff000000ff000000ff000000ff, 0xff00ff0000000000ff00ff, 0xff00ff00ff00ff], 0x11001100010003005500ff, 8⟩
def bsT424 : Array Bound := [T410].toArray
theorem vbsT424 : ∀ s ∈ bsT424, Valid s := by
  intro s hs
  simp only [bsT424,List.mem_toArray] at hs
  exact (familyCons vT410 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT424 : Valid T424 := by
  apply bound_of_layers (bs := bsT424) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT424 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T425 : Bound := ⟨0xff00ff00ff00ff000000000000000000ff00ff00ff00ff, [0x0, 0x5500550055005500000000000000000055005500550055, 0x3300330033003300000000000000000033003300330033, 0xf000f000f000f0000000000000000000f000f000f000f, 0xff000000ff0000000000000000000000ff000000ff, 0xff00ff00000000000000000000000000ff00ff, 0xff00ff00ff00ff], 0xf000000000000000000010003005500ff, 8⟩
def bsT425 : Array Bound := [T411].toArray
theorem vbsT425 : ∀ s ∈ bsT425, Valid s := by
  intro s hs
  simp only [bsT425,List.mem_toArray] at hs
  exact (familyCons vT411 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT425 : Valid T425 := by
  apply bound_of_layers (bs := bsT425) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT425 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T426 : Bound := ⟨0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff, [0x0, 0x5500000055000000550000005500000055000000550000005500000055, 0x3300000033000000330000003300000033000000330000003300000033, 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f, 0xff00000000000000ff00000000000000ff00000000000000ff, 0xff000000ff0000000000000000000000ff000000ff, 0xff000000ff000000ff000000ff], 0x1000000000000000f000000000000001100000003000000ff, 9⟩
def bsT426 : Array Bound := [T415].toArray
theorem vbsT426 : ∀ s ∈ bsT426, Valid s := by
  intro s hs
  simp only [bsT426,List.mem_toArray] at hs
  exact (familyCons vT415 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT426 : Valid T426 := by
  apply bound_of_layers (bs := bsT426) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT426 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T427 : Bound := ⟨0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f, [0x0, 0x5000500050005000500050005000500050005000500050005000500050005, 0x3000300030003000300030003000300030003000300030003000300030003, 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f, 0xf000f00000000000f000f00000000000f000f00000000000f000f, 0xf000f000f000f0000000000000000000f000f000f000f, 0xf000f000f000f000f000f000f000f], 0x1000000000000000f0000000000010001000100030005000f, 9⟩
def bsT427 : Array Bound := [T394, T396, T404, T406, T410, T413, T414].toArray
theorem vbsT427 : ∀ s ∈ bsT427, Valid s := by
  intro s hs
  simp only [bsT427,List.mem_toArray] at hs
  exact (familyCons vT394 <| familyCons vT396 <| familyCons vT404 <| familyCons vT406 <| familyCons vT410 <| familyCons vT413 <| familyCons vT414 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T427r5p0 : RecordPage := #[
(0x481421a867e, 0x0)]
def T427r5 : Records := #[T427r5p0]
def testT427r5 : ℕ → Bool := testAt T427 bsT427 4 (#[] : Records) T427r5 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T427r5c0 : checkBlock testT427r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT427r5 : LayerOK T427 5 T427r5 := by
  apply layer_of_block (bs := bsT427) (k := 4) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT427 (emptyOK _ _)
  exact @block_merge testT427r5 0 1 31 T427r5c0 (show checkBlock testT427r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T427r6p0 : RecordPage := #[
(0x4818867e, 0x0), (0xc818867e, 0xa), (0x1421a867e, 0x15), (0x61e867e, 0x0),
(0x81e867e, 0x2), (0xc1e867e, 0x2)]
def T427r6 : Records := #[T427r6p0]
def testT427r6 : ℕ → Bool := testAt T427 bsT427 5 T427r5 T427r6 3 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T427r6c0 : checkBlock testT427r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T427r6c1 : checkBlock testT427r6 2 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT427r6 : LayerOK T427 6 T427r6 := by
  apply layer_of_block (bs := bsT427) (k := 5) (old := T427r5) (cw := 3) (rw := 0) (by decide +kernel) vbsT427 vT427r5
  exact @block_merge testT427r6 0 6 26 (@block_merge testT427r6 0 4 2 T427r6c0 T427r6c1) (show checkBlock testT427r6 26 6 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T427r7p0 : RecordPage := #[
(0x18867e, 0x88aaaacc022088884646aaaa31aacccc2200), (0x1a867e, 0x88aa002088884646aaaacccc0050), (0x1c867e, 0xaacc002288884646aaaacccc5200), (0x1e867e, 0x28888880b46404606aaaaaa09cccccc070020)]
def T427r7 : Records := #[T427r7p0]
def testT427r7 : ℕ → Bool := testAt T427 bsT427 6 T427r6 T427r7 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T427r7c0 : checkBlock testT427r7 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT427r7 : LayerOK T427 7 T427r7 := by
  apply layer_of_block (bs := bsT427) (k := 6) (old := T427r6) (cw := 3) (rw := 3) (by decide +kernel) vbsT427 vT427r6
  exact @block_merge testT427r7 0 4 28 T427r7c0 (show checkBlock testT427r7 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T427r8p0 : RecordPage := #[
(0x7e, 0x88888888f598888446644668888aaaaaaaaaaaa8888ccccccccccccaaaa)]
def T427r8 : Records := #[T427r8p0]
def testT427r8 : ℕ → Bool := testAt T427 bsT427 7 T427r7 T427r8 3 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T427r8c0 : checkBlock testT427r8 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT427r8 : LayerOK T427 8 T427r8 := by
  apply layer_of_block (bs := bsT427) (k := 7) (old := T427r7) (cw := 3) (rw := 2) (by decide +kernel) vbsT427 vT427r7
  exact @block_merge testT427r8 0 1 31 T427r8c0 (show checkBlock testT427r8 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT427 : Valid T427 := by
  apply bound_of_layers (bs := bsT427) (last := T427r8) (cw := 3) (rw := 0) (by decide +kernel) vbsT427 vT427r8 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T428 : Bound := ⟨0x33003300330033003300330033003300330033003300330033003300330033, [0x0, 0x11001100110011001100110011001100110011001100110011001100110011, 0x3000300030003000300030003000300030003000300030003000300030003, 0x3300000033000000330000003300000033000000330000003300000033, 0x330033000000000033003300000000003300330000000000330033, 0x3300330033003300000000000000000033003300330033, 0x330033003300330033003300330033], 0x1000000000000000300000000001100110001000300110033, 9⟩
def bsT428 : Array Bound := [T390, T397, T407, T408, T411, T412, T413].toArray
theorem vbsT428 : ∀ s ∈ bsT428, Valid s := by
  intro s hs
  simp only [bsT428,List.mem_toArray] at hs
  exact (familyCons vT390 <| familyCons vT397 <| familyCons vT407 <| familyCons vT408 <| familyCons vT411 <| familyCons vT412 <| familyCons vT413 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T428r5p0 : RecordPage := #[
(0x481421aa67e, 0x0)]
def T428r5 : Records := #[T428r5p0]
def testT428r5 : ℕ → Bool := testAt T428 bsT428 4 (#[] : Records) T428r5 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T428r5c0 : checkBlock testT428r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT428r5 : LayerOK T428 5 T428r5 := by
  apply layer_of_block (bs := bsT428) (k := 4) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT428 (emptyOK _ _)
  exact @block_merge testT428r5 0 1 31 T428r5c0 (show checkBlock testT428r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T428r6p0 : RecordPage := #[
(0x4818a67e, 0x0), (0xc818a67e, 0xc), (0x1421aa67e, 0x19), (0x81ea67e, 0x2),
(0xa1ea67e, 0x0), (0xc1ea67e, 0x2)]
def T428r6 : Records := #[T428r6p0]
def testT428r6 : ℕ → Bool := testAt T428 bsT428 5 T428r5 T428r6 3 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T428r6c0 : checkBlock testT428r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T428r6c1 : checkBlock testT428r6 2 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT428r6 : LayerOK T428 6 T428r6 := by
  apply layer_of_block (bs := bsT428) (k := 5) (old := T428r5) (cw := 3) (rw := 0) (by decide +kernel) vbsT428 vT428r5
  exact @block_merge testT428r6 0 6 26 (@block_merge testT428r6 0 4 2 T428r6c0 T428r6c1) (show checkBlock testT428r6 26 6 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T428r7p0 : RecordPage := #[
(0x18a67e, 0x88ccaacc02208888aaaacccc31cc46462200), (0x1aa67e, 0x88cc00208888aaaacccc46460050), (0x1ca67e, 0xaacc00228888aaaacccc46465200), (0x1ea67e, 0x28888880baaaaaa09cccccc07464046060020)]
def T428r7 : Records := #[T428r7p0]
def testT428r7 : ℕ → Bool := testAt T428 bsT428 6 T428r6 T428r7 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T428r7c0 : checkBlock testT428r7 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT428r7 : LayerOK T428 7 T428r7 := by
  apply layer_of_block (bs := bsT428) (k := 6) (old := T428r6) (cw := 3) (rw := 3) (by decide +kernel) vbsT428 vT428r6
  exact @block_merge testT428r7 0 4 28 T428r7c0 (show checkBlock testT428r7 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T428r8p0 : RecordPage := #[
(0x7e, 0x8888f598888aaaa8888aaaacccc8888ccccaaaa446688884466aaaacccc)]
def T428r8 : Records := #[T428r8p0]
def testT428r8 : ℕ → Bool := testAt T428 bsT428 7 T428r7 T428r8 3 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T428r8c0 : checkBlock testT428r8 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT428r8 : LayerOK T428 8 T428r8 := by
  apply layer_of_block (bs := bsT428) (k := 7) (old := T428r7) (cw := 3) (rw := 2) (by decide +kernel) vbsT428 vT428r7
  exact @block_merge testT428r8 0 1 31 T428r8c0 (show checkBlock testT428r8 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT428 : Valid T428 := by
  apply bound_of_layers (bs := bsT428) (last := T428r8) (cw := 3) (rw := 0) (by decide +kernel) vbsT428 vT428r8 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T429 : Bound := ⟨0x55005500550055005500550055005500550055005500550055005500550055, [0x0, 0x11001100110011001100110011001100110011001100110011001100110011, 0x5000500050005000500050005000500050005000500050005000500050005, 0x5500000055000000550000005500000055000000550000005500000055, 0x550055000000000055005500000000005500550000000000550055, 0x5500550055005500000000000000000055005500550055, 0x550055005500550055005500550055], 0x1000000000000000500000000001100110001000100550055, 9⟩
def bsT429 : Array Bound := [T415].toArray
theorem vbsT429 : ∀ s ∈ bsT429, Valid s := by
  intro s hs
  simp only [bsT429,List.mem_toArray] at hs
  exact (familyCons vT415 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT429 : Valid T429 := by
  apply bound_of_layers (bs := bsT429) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT429 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def T430 : Bound := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, [0x0, 0x55005500550055005500550055005500550055005500550055005500550055, 0x33003300330033003300330033003300330033003300330033003300330033, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f, 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff, 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff, 0xff00ff00ff00ff00ff00ff00ff00ff], 0x1000000000000000f000000000011001100010003005500ff, 11⟩
def bsT430 : Array Bound := [T421, T424, T425, T426, T427, T428, T429].toArray
theorem vbsT430 : ∀ s ∈ bsT430, Valid s := by
  intro s hs
  simp only [bsT430,List.mem_toArray] at hs
  exact (familyCons vT421 <| familyCons vT424 <| familyCons vT425 <| familyCons vT426 <| familyCons vT427 <| familyCons vT428 <| familyCons vT429 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T430r6p0 : RecordPage := #[
(0x4c1cc04818a8fe, 0x0), (0x4c18c24818a8fe, 0x0), (0x6410e2c818a8fe, 0x0), (0x4c10e2c818a8fe, 0x0),
(0x4c2ca10e18a8fe, 0x0), (0x80e610e58a8fe, 0x0), (0xa0e610e58a8fe, 0x0), (0x4c1cc04a18c8fe, 0x0),
(0x6410e2ca18c8fe, 0x0), (0x4c10e2ca18c8fe, 0x0), (0xc0e610e58c8fe, 0x0), (0xe0e610e58c8fe, 0x0),
(0x2206438e18cafe, 0x0), (0x4a0421ae18cafe, 0x0), (0x4c0421ae18cafe, 0x0)]
def T430r6 : Records := #[T430r6p0]
def testT430r6 : ℕ → Bool := testAt T430 bsT430 5 (#[] : Records) T430r6 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r6c0 : checkBlock testT430r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r6c1 : checkBlock testT430r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r6c2 : checkBlock testT430r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r6c3 : checkBlock testT430r6 3 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT430r6 : LayerOK T430 6 T430r6 := by
  apply layer_of_block (bs := bsT430) (k := 5) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT430 (emptyOK _ _)
  exact @block_merge testT430r6 0 15 17 (@block_merge testT430r6 0 8 7 (@block_merge testT430r6 0 4 4 T430r6c0 T430r6c1) (@block_merge testT430r6 8 4 3 T430r6c2 T430r6c3)) (show checkBlock testT430r6 17 15 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T430r7p0 : RecordPage := #[
(0x18c04818a8fe, 0x0), (0x1cc04818a8fe, 0x101), (0x18c24818a8fe, 0x103), (0x10e2c818a8fe, 0x20e5),
(0x14e2c818a8fe, 0x0), (0x10e6c818a8fe, 0x2), (0xc210e18a8fe, 0x6), (0xc410e18a8fe, 0x6),
(0x14410e18a8fe, 0x0), (0xc610e18a8fe, 0x6), (0x4a10e18a8fe, 0x0), (0xca10e18a8fe, 0x109a),
(0x4c10e18a8fe, 0x0), (0xcc10e18a8fe, 0x1498), (0x4618e18a8fe, 0x6), (0x4818e18a8fe, 0x6),
(0x4c18e18a8fe, 0xaa), (0x4e18e18a8fe, 0x147), (0x10434e18a8fe, 0x6), (0x85ce18a8fe, 0x0),
(0x4e18e38a8fe, 0x143), (0x858e38a8fe, 0x24), (0xc610e58a8fe, 0x0), (0xe610e58a8fe, 0x1ab),
(0x4c14e1ca8fe, 0x40), (0xcc14e1ca8fe, 0x8), (0x18c04a18c8fe, 0x0), (0x1cc04a18c8fe, 0x14f),
(0x10e2ca18c8fe, 0x2a71), (0x14e2ca18c8fe, 0x0), (0x10e6ca18c8fe, 0x4), (0x4618e18c8fe, 0x6)]
def T430r7p1 : RecordPage := #[
(0x4c18e18c8fe, 0x113), (0x4e18e18c8fe, 0x88), (0x85ce18c8fe, 0x0), (0xc610e58c8fe, 0x0),
(0xe610e58c8fe, 0x2f5), (0x4a14e1cc8fe, 0x20), (0xca14e1cc8fe, 0xa), (0x4618e18cafe, 0x6),
(0x4818e18cafe, 0x6), (0x4c18e18cafe, 0x0), (0x4e18e18cafe, 0x0), (0x6438e18cafe, 0x19),
(0x421ae18cafe, 0x23b5b), (0x461ae18cafe, 0x6), (0x481ae18cafe, 0x6), (0x443ae18cafe, 0x19),
(0xa1ee18cafe, 0xb), (0xc1ee18cafe, 0xd), (0xe1ee18cafe, 0x15), (0x101ee18cafe, 0x17)]
def T430r7 : Records := #[T430r7p0, T430r7p1]
def testT430r7 : ℕ → Bool := testAt T430 bsT430 6 T430r6 T430r7 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r7c0 : checkBlock testT430r7 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r7c1 : checkBlock testT430r7 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r7c2 : checkBlock testT430r7 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r7c3 : checkBlock testT430r7 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r7c4 : checkBlock testT430r7 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r7c5 : checkBlock testT430r7 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r7c6 : checkBlock testT430r7 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r7c7 : checkBlock testT430r7 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r7c8 : checkBlock testT430r7 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r7c9 : checkBlock testT430r7 4 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r7c10 : checkBlock testT430r7 4 40 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r7c11 : checkBlock testT430r7 4 44 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r7c12 : checkBlock testT430r7 4 48 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT430r7 : LayerOK T430 7 T430r7 := by
  apply layer_of_block (bs := bsT430) (k := 6) (old := T430r6) (cw := 3) (rw := 4) (by decide +kernel) vbsT430 vT430r6
  exact @block_merge testT430r7 0 52 12 (@block_merge testT430r7 0 24 28 (@block_merge testT430r7 0 12 12 (@block_merge testT430r7 0 4 8 T430r7c0 (@block_merge testT430r7 4 4 4 T430r7c1 T430r7c2)) (@block_merge testT430r7 12 4 8 T430r7c3 (@block_merge testT430r7 16 4 4 T430r7c4 T430r7c5))) (@block_merge testT430r7 24 12 16 (@block_merge testT430r7 24 4 8 T430r7c6 (@block_merge testT430r7 28 4 4 T430r7c7 T430r7c8)) (@block_merge testT430r7 36 8 8 (@block_merge testT430r7 36 4 4 T430r7c9 T430r7c10) (@block_merge testT430r7 44 4 4 T430r7c11 T430r7c12)))) (show checkBlock testT430r7 12 52 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T430r8p0 : RecordPage := #[
(0x4818a8fe, 0xcccd1110cccd9998cccd11104848cccd1111999840415999a2223333111288190166668888ccccaaa4aaa4), (0xc818a8fe, 0x82e233110108490766668888cccc4044a0a4aaa), (0x10e18a8fe, 0x88aa66668888366622aaa8b95aacccc42644790d), (0x18e18a8fe, 0x28390d847484f9d2),
(0x14e18a8fe, 0x2209092b3334444555566661112111210d), (0x1ce18a8fe, 0x9e8490d202), (0x18e38a8fe, 0x5055649614a1f2242), (0x10e58a8fe, 0x5566334450b44aacc2564449e22a817ad02222024),
(0x14e1ca8fe, 0x10222a89081999a22219b188aaaacccc2224224220), (0x4a18c8fe, 0xcccd5554cccd9998cccd55544444cccd55559998808a5999aaaab333088a11ba356666aaaacccc88828882), (0xca18c8fe, 0x4f6a99888091da396666aaaacccc20228082888), (0x18e18c8fe, 0x21ca138875052bf4),
(0x14e18c8fe, 0x2a8890fb33344445555666611112111213), (0x1ce18c8fe, 0x1161da13204), (0x10e58c8fe, 0x334443daacc2266884568891622a824c704444022), (0x14e1cc8fe, 0x8222a88901999a2222aaaa6cbaacccc2222242240),
(0x18e18cafe, 0x2b8f8ab54e8cf0), (0x1ae18cafe, 0xbf76dd9), (0x14e18cafe, 0x2aa208911999a2222aaab33308889088ac8f), (0x1ce18cafe, 0x8eb6f8f24220),
(0x1ee18cafe, 0x92bc2bb678cb58f30922111)]
def T430r8 : Records := #[T430r8p0]
def testT430r8 : ℕ → Bool := testAt T430 bsT430 7 T430r7 T430r8 3 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r8c0 : checkBlock testT430r8 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r8c1 : checkBlock testT430r8 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r8c2 : checkBlock testT430r8 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r8c3 : checkBlock testT430r8 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r8c4 : checkBlock testT430r8 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r8c5 : checkBlock testT430r8 1 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT430r8 : LayerOK T430 8 T430r8 := by
  apply layer_of_block (bs := bsT430) (k := 7) (old := T430r7) (cw := 3) (rw := 6) (by decide +kernel) vbsT430 vT430r7
  exact @block_merge testT430r8 0 21 11 (@block_merge testT430r8 0 12 9 (@block_merge testT430r8 0 4 8 T430r8c0 (@block_merge testT430r8 4 4 4 T430r8c1 T430r8c2)) (@block_merge testT430r8 12 4 5 T430r8c3 (@block_merge testT430r8 16 4 1 T430r8c4 T430r8c5))) (show checkBlock testT430r8 11 21 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T430r9p0 : RecordPage := #[
(0x18a8fe, 0x666688886666aaaa66668888cccc66668888aaaa244243d999a222222aaaaab3330808d66668888aaaaaacccccc4444044222c9221c56666666688888888aaaaaa0c1aaaacccccccc440444), (0x1ca8fe, 0x1999a2221999aaaa9999a22233331999a2222aaa89091999a2222aaab33308081999a2222aaaaab3333311111100881122006666666688888888aaaaaaaacccccccc440444), (0x18c8fe, 0x666688886666aaaa66668888cccc66668888aaaa2222275999a222222aaaaab3331010d666666888888aaaacccc2222022446d9445c5666666668888885538888aaaaaaaacccccccc220222), (0x1cc8fe, 0x1999a2221999aaaa9999a22233331999a2222aaa88889999a2222aaab3331010199999a222222aaab33308888881101f44006666666688888888aaaaaaaacccccccc220222),
(0x18cafe, 0x666688886666aaaa66668888cccc66668888aaaa2222275999a2222aaaaab33333111110f666666888888aaaacccc2222422a42796308456666666688888888aaaaaaaacccccccc224222)]
def T430r9 : Records := #[T430r9p0]
def testT430r9 : ℕ → Bool := testAt T430 bsT430 8 T430r8 T430r9 3 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r9c0 : checkBlock testT430r9 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r9c1 : checkBlock testT430r9 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT430r9 : LayerOK T430 9 T430r9 := by
  apply layer_of_block (bs := bsT430) (k := 8) (old := T430r8) (cw := 3) (rw := 5) (by decide +kernel) vbsT430 vT430r8
  exact @block_merge testT430r9 0 5 27 (@block_merge testT430r9 0 4 1 T430r9c0 T430r9c1) (show checkBlock testT430r9 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T430r10p0 : RecordPage := #[
(0xfe, 0x2429272543416666666666668888888888886666aaaaaaaaaaaa66668888cccccccccccc66668888aaaa)]
def T430r10 : Records := #[T430r10p0]
def testT430r10 : ℕ → Bool := testAt T430 bsT430 9 T430r9 T430r10 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T430r10c0 : checkBlock testT430r10 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT430r10 : LayerOK T430 10 T430r10 := by
  apply layer_of_block (bs := bsT430) (k := 9) (old := T430r9) (cw := 3) (rw := 3) (by decide +kernel) vbsT430 vT430r9
  exact @block_merge testT430r10 0 1 31 T430r10c0 (show checkBlock testT430r10 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT430 : Valid T430 := by
  apply bound_of_layers (bs := bsT430) (last := T430r10) (cw := 3) (rw := 0) (by decide +kernel) vbsT430 vT430r10 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
def rootT : Bound := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, [0x0, 0x5555555555555555555555555555555555555555555555555555555555555555, 0x3333333333333333333333333333333333333333333333333333333333333333, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 0xffffffffffffffff0000000000000000ffffffffffffffff, 0xffffffffffffffffffffffffffffffff], 0x1000000000000000f0000000000110011010103035555ffff, 12⟩
def bsrootT : Array Bound := [T430].toArray
theorem vbsrootT : ∀ s ∈ bsrootT, Valid s := by
  intro s hs
  simp only [bsrootT,List.mem_toArray] at hs
  exact (familyCons vT430 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootT : Valid rootT := by
  apply bound_of_layers (bs := bsrootT) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsrootT (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_14486.SignedCert.GraphT
open PEqualNP.CircuitLowerBounds
def columns : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def funValue (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def network : List Gate := [
  ⟨.or, [5,3]⟩,
  ⟨.or, [8,2]⟩,
  ⟨.or, [4,9]⟩,
  ⟨.or, [8,1]⟩,
  ⟨.or, [2,1]⟩,
  ⟨.and, [4,0]⟩,
  ⟨.or, [0,11]⟩,
  ⟨.and, [5,12]⟩,
  ⟨.or, [13,15]⟩,
  ⟨.or, [16,6]⟩,
  ⟨.and, [14,17]⟩,
  ⟨.and, [10,7]⟩,
  ⟨.or, [18,19]⟩]

theorem legal_network : ∀ g ∈ network, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [network,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correct_network : ∀ x : Fin 8 → Bool, (Circuit.mk network 20).eval (List.ofFn x) = funValue x := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, Source.legal g)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gs o).eval (List.ofFn x) = funValue x) :
    12 ≤ Source.binaryCost gs := by
  apply Source.binary_lb vrootT 0xfffffffffffffffefffffffffffffff0ffffffffffeeffeefefefcfcaaaa0000 columns funValue (by decide +kernel) (by decide +kernel) (by rfl) _ (by decide +kernel) _ gs o legal correct
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_meta_14486.SignedCert.GraphT

theorem PEqualNP.Outside.L_meta_14486 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_14486.SignedCert.Source.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_14486.SignedCert.Source.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_14486.SignedCert.Source.isBinary, op]⟩
    have hb := PEqualNP.Outside.L_meta_14486.SignedCert.GraphT.lower gates o (fun g hg => fits g hg) computes
    have hl : PEqualNP.Outside.L_meta_14486.SignedCert.GraphT.network.length = 13 := rfl
    exact ⟨PEqualNP.Outside.L_meta_14486.SignedCert.GraphT.network, 20, PEqualNP.Outside.L_meta_14486.SignedCert.GraphT.legal_network, by omega, PEqualNP.Outside.L_meta_14486.SignedCert.GraphT.correct_network⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g,hg,h⟩).elim
