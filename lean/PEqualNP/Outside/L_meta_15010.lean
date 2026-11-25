import PEqualNP.Defs

-- A seven-variable restriction certifies a lower bound of twelve binary gates on the full graph.

-- The live-set compression proof is adapted from L-meta-9136 and its credited sources.
namespace PEqualNP.Outside.L_meta_15010.SignedCert
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

end PEqualNP.Outside.L_meta_15010.SignedCert

namespace PEqualNP.Outside.L_meta_15010.SignedCert

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

end PEqualNP.Outside.L_meta_15010.SignedCert

namespace PEqualNP.Outside.L_meta_15010.SignedCert

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

end PEqualNP.Outside.L_meta_15010.SignedCert

namespace PEqualNP.Outside.L_meta_15010.SignedCert

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

end PEqualNP.Outside.L_meta_15010.SignedCert

namespace PEqualNP.Outside.L_meta_15010.SignedCert
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

end PEqualNP.Outside.L_meta_15010.SignedCert

namespace PEqualNP.Outside.L_meta_15010.SignedCert.Source
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
    norm m z ∈ PEqualNP.Outside.L_meta_15010.SignedCert.ops m (norm m a) (norm m b) := by
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
    build (PEqualNP.Outside.L_meta_15010.SignedCert.ops m) (norm m t) k (bank m S) := by
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

end PEqualNP.Outside.L_meta_15010.SignedCert.Source

namespace PEqualNP.Outside.L_meta_15010.SignedCert
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

end PEqualNP.Outside.L_meta_15010.SignedCert

namespace PEqualNP.Outside.L_meta_15010.SignedCert

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


end PEqualNP.Outside.L_meta_15010.SignedCert

namespace PEqualNP.Outside.L_meta_15010.SignedCert

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

end PEqualNP.Outside.L_meta_15010.SignedCert

namespace PEqualNP.Outside.L_meta_15010.SignedCert

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

end PEqualNP.Outside.L_meta_15010.SignedCert

namespace PEqualNP.Outside.L_meta_15010.SignedCert

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
end PEqualNP.Outside.L_meta_15010.SignedCert

namespace PEqualNP.Outside.L_meta_15010.SignedCert

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
end PEqualNP.Outside.L_meta_15010.SignedCert

namespace PEqualNP.Outside.L_meta_15010.SignedCert

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

end PEqualNP.Outside.L_meta_15010.SignedCert

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T144 : Bound := ⟨0x300030000000000030003, [0x0, 0x100010000000000010001, 0x30000000000000003, 0x30003], 0x10000000000010003, 4⟩
def bsT144 : Array Bound := [].toArray
theorem vbsT144 : ∀ s ∈ bsT144, Valid s := by
  intro s hs
  simp only [bsT144,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T144r3p0 : RecordPage := #[
(0xe, 0x0)]
def T144r3 : Records := #[T144r3p0]
def testT144r3 : ℕ → Bool := testAt T144 bsT144 2 (#[] : Records) T144r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T144r3c0 : checkBlock testT144r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT144r3 : LayerOK T144 3 T144r3 := by
  apply layer_of_block (bs := bsT144) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT144 (emptyOK _ _)
  exact @block_merge testT144r3 0 1 31 T144r3c0 (show checkBlock testT144r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT144 : Valid T144 := by
  apply bound_of_layers (bs := bsT144) (last := T144r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT144 vT144r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T145 : Bound := ⟨0x500050000000000050005, [0x0, 0x100010000000000010001, 0x50000000000000005, 0x50005], 0x10000000000010005, 4⟩
def bsT145 : Array Bound := [].toArray
theorem vbsT145 : ∀ s ∈ bsT145, Valid s := by
  intro s hs
  simp only [bsT145,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T145r3p0 : RecordPage := #[
(0xe, 0x0)]
def T145r3 : Records := #[T145r3p0]
def testT145r3 : ℕ → Bool := testAt T145 bsT145 2 (#[] : Records) T145r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T145r3c0 : checkBlock testT145r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT145r3 : LayerOK T145 3 T145r3 := by
  apply layer_of_block (bs := bsT145) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT145 (emptyOK _ _)
  exact @block_merge testT145r3 0 1 31 T145r3c0 (show checkBlock testT145r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT145 : Valid T145 := by
  apply bound_of_layers (bs := bsT145) (last := T145r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT145 vT145r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T146 : Bound := ⟨0x3000300000000000300030, [0x0, 0x1000100000000000100010, 0x300000000000000030, 0x300030], 0x100000000000100030, 4⟩
def bsT146 : Array Bound := [].toArray
theorem vbsT146 : ∀ s ∈ bsT146, Valid s := by
  intro s hs
  simp only [bsT146,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T146r3p0 : RecordPage := #[
(0xe, 0x0)]
def T146r3 : Records := #[T146r3p0]
def testT146r3 : ℕ → Bool := testAt T146 bsT146 2 (#[] : Records) T146r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T146r3c0 : checkBlock testT146r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT146r3 : LayerOK T146 3 T146r3 := by
  apply layer_of_block (bs := bsT146) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT146 (emptyOK _ _)
  exact @block_merge testT146r3 0 1 31 T146r3c0 (show checkBlock testT146r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT146 : Valid T146 := by
  apply bound_of_layers (bs := bsT146) (last := T146r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT146 vT146r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T147 : Bound := ⟨0x5000500000000000500050, [0x0, 0x1000100000000000100010, 0x500000000000000050, 0x500050], 0x100000000000100050, 4⟩
def bsT147 : Array Bound := [].toArray
theorem vbsT147 : ∀ s ∈ bsT147, Valid s := by
  intro s hs
  simp only [bsT147,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T147r3p0 : RecordPage := #[
(0xe, 0x0)]
def T147r3 : Records := #[T147r3p0]
def testT147r3 : ℕ → Bool := testAt T147 bsT147 2 (#[] : Records) T147r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T147r3c0 : checkBlock testT147r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT147r3 : LayerOK T147 3 T147r3 := by
  apply layer_of_block (bs := bsT147) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT147 (emptyOK _ _)
  exact @block_merge testT147r3 0 1 31 T147r3c0 (show checkBlock testT147r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT147 : Valid T147 := by
  apply bound_of_layers (bs := bsT147) (last := T147r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT147 vT147r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T148 : Bound := ⟨0x3000300000000000000000000000000030003, [0x0, 0x1000100000000000000000000000000010001, 0x300000000000000000000000000000003, 0x30003], 0x100000000000000000000000000010003, 4⟩
def bsT148 : Array Bound := [].toArray
theorem vbsT148 : ∀ s ∈ bsT148, Valid s := by
  intro s hs
  simp only [bsT148,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T148r3p0 : RecordPage := #[
(0xe, 0x0)]
def T148r3 : Records := #[T148r3p0]
def testT148r3 : ℕ → Bool := testAt T148 bsT148 2 (#[] : Records) T148r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T148r3c0 : checkBlock testT148r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT148r3 : LayerOK T148 3 T148r3 := by
  apply layer_of_block (bs := bsT148) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT148 (emptyOK _ _)
  exact @block_merge testT148r3 0 1 31 T148r3c0 (show checkBlock testT148r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT148 : Valid T148 := by
  apply bound_of_layers (bs := bsT148) (last := T148r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT148 vT148r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T295 : Bound := ⟨0x33003300330033, [0x0, 0x11001100110011, 0x3000300030003, 0x3300000033, 0x330033], 0x1000100110033, 4⟩
def bsT295 : Array Bound := [].toArray
theorem vbsT295 : ∀ s ∈ bsT295, Valid s := by
  intro s hs
  simp only [bsT295,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T295r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T295r3 : Records := #[T295r3p0]
def testT295r3 : ℕ → Bool := testAt T295 bsT295 2 (#[] : Records) T295r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T295r3c0 : checkBlock testT295r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT295r3 : LayerOK T295 3 T295r3 := by
  apply layer_of_block (bs := bsT295) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT295 (emptyOK _ _)
  exact @block_merge testT295r3 0 1 31 T295r3c0 (show checkBlock testT295r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT295 : Valid T295 := by
  apply bound_of_layers (bs := bsT295) (last := T295r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT295 vT295r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T296 : Bound := ⟨0x55005500550055, [0x0, 0x11001100110011, 0x5000500050005, 0x5500000055, 0x550055], 0x1000100110055, 4⟩
def bsT296 : Array Bound := [].toArray
theorem vbsT296 : ∀ s ∈ bsT296, Valid s := by
  intro s hs
  simp only [bsT296,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T296r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T296r3 : Records := #[T296r3p0]
def testT296r3 : ℕ → Bool := testAt T296 bsT296 2 (#[] : Records) T296r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T296r3c0 : checkBlock testT296r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT296r3 : LayerOK T296 3 T296r3 := by
  apply layer_of_block (bs := bsT296) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT296 (emptyOK _ _)
  exact @block_merge testT296r3 0 1 31 T296r3c0 (show checkBlock testT296r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT296 : Valid T296 := by
  apply bound_of_layers (bs := bsT296) (last := T296r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT296 vT296r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T299 : Bound := ⟨0x33000000330000003300000033, [0x0, 0x11000000110000001100000011, 0x3000000030000000300000003, 0x330000000000000033, 0x3300000033], 0x1000000110000000100000033, 4⟩
def bsT299 : Array Bound := [].toArray
theorem vbsT299 : ∀ s ∈ bsT299, Valid s := by
  intro s hs
  simp only [bsT299,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T299r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T299r3 : Records := #[T299r3p0]
def testT299r3 : ℕ → Bool := testAt T299 bsT299 2 (#[] : Records) T299r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T299r3c0 : checkBlock testT299r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT299r3 : LayerOK T299 3 T299r3 := by
  apply layer_of_block (bs := bsT299) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT299 (emptyOK _ _)
  exact @block_merge testT299r3 0 1 31 T299r3c0 (show checkBlock testT299r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT299 : Valid T299 := by
  apply bound_of_layers (bs := bsT299) (last := T299r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT299 vT299r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T300 : Bound := ⟨0x55000000550000005500000055, [0x0, 0x11000000110000001100000011, 0x5000000050000000500000005, 0x550000000000000055, 0x5500000055], 0x1000000110000000100000055, 4⟩
def bsT300 : Array Bound := [].toArray
theorem vbsT300 : ∀ s ∈ bsT300, Valid s := by
  intro s hs
  simp only [bsT300,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T300r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T300r3 : Records := #[T300r3p0]
def testT300r3 : ℕ → Bool := testAt T300 bsT300 2 (#[] : Records) T300r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T300r3c0 : checkBlock testT300r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT300r3 : LayerOK T300 3 T300r3 := by
  apply layer_of_block (bs := bsT300) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT300 (emptyOK _ _)
  exact @block_merge testT300r3 0 1 31 T300r3c0 (show checkBlock testT300r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT300 : Valid T300 := by
  apply bound_of_layers (bs := bsT300) (last := T300r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT300 vT300r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T301 : Bound := ⟨0x55005500000000000000000000000000550055, [0x0, 0x11001100000000000000000000000000110011, 0x5000500000000000000000000000000050005, 0x5500000000000000000000000000000055, 0x550055], 0x500000000000000000000000000110055, 4⟩
def bsT301 : Array Bound := [].toArray
theorem vbsT301 : ∀ s ∈ bsT301, Valid s := by
  intro s hs
  simp only [bsT301,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T301r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T301r3 : Records := #[T301r3p0]
def testT301r3 : ℕ → Bool := testAt T301 bsT301 2 (#[] : Records) T301r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T301r3c0 : checkBlock testT301r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT301r3 : LayerOK T301 3 T301r3 := by
  apply layer_of_block (bs := bsT301) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT301 (emptyOK _ _)
  exact @block_merge testT301r3 0 1 31 T301r3c0 (show checkBlock testT301r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT301 : Valid T301 := by
  apply bound_of_layers (bs := bsT301) (last := T301r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT301 vT301r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T302 : Bound := ⟨0xf0000000f00000000000000000000000f0000000f, [0x0, 0x50000000500000000000000000000000500000005, 0x30000000300000000000000000000000300000003, 0xf0000000000000000000000000000000f, 0xf0000000f], 0x1000000050000000000000000000000010000000f, 4⟩
def bsT302 : Array Bound := [].toArray
theorem vbsT302 : ∀ s ∈ bsT302, Valid s := by
  intro s hs
  simp only [bsT302,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T302r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T302r3 : Records := #[T302r3p0]
def testT302r3 : ℕ → Bool := testAt T302 bsT302 2 (#[] : Records) T302r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T302r3c0 : checkBlock testT302r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT302r3 : LayerOK T302 3 T302r3 := by
  apply layer_of_block (bs := bsT302) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT302 (emptyOK _ _)
  exact @block_merge testT302r3 0 1 31 T302r3c0 (show checkBlock testT302r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT302 : Valid T302 := by
  apply bound_of_layers (bs := bsT302) (last := T302r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT302 vT302r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T303 : Bound := ⟨0x550000005500000000000000000000005500000055, [0x0, 0x110000001100000000000000000000001100000011, 0x50000000500000000000000000000000500000005, 0x5500000000000000000000000000000055, 0x5500000055], 0x10000000500000000000000000000000100000055, 4⟩
def bsT303 : Array Bound := [].toArray
theorem vbsT303 : ∀ s ∈ bsT303, Valid s := by
  intro s hs
  simp only [bsT303,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T303r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T303r3 : Records := #[T303r3p0]
def testT303r3 : ℕ → Bool := testAt T303 bsT303 2 (#[] : Records) T303r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T303r3c0 : checkBlock testT303r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT303r3 : LayerOK T303 3 T303r3 := by
  apply layer_of_block (bs := bsT303) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT303 (emptyOK _ _)
  exact @block_merge testT303r3 0 1 31 T303r3c0 (show checkBlock testT303r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT303 : Valid T303 := by
  apply bound_of_layers (bs := bsT303) (last := T303r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT303 vT303r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T304 : Bound := ⟨0x500050005000500000000000000000005000500050005, [0x0, 0x100010001000100000000000000000001000100010001, 0x50000000500000000000000000000000500000005, 0x5000500000000000000000000000000050005, 0x5000500050005], 0x10000000500000000000000000001000100010005, 4⟩
def bsT304 : Array Bound := [].toArray
theorem vbsT304 : ∀ s ∈ bsT304, Valid s := by
  intro s hs
  simp only [bsT304,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T304r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T304r3 : Records := #[T304r3p0]
def testT304r3 : ℕ → Bool := testAt T304 bsT304 2 (#[] : Records) T304r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T304r3c0 : checkBlock testT304r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT304r3 : LayerOK T304 3 T304r3 := by
  apply layer_of_block (bs := bsT304) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT304 (emptyOK _ _)
  exact @block_merge testT304r3 0 1 31 T304r3c0 (show checkBlock testT304r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT304 : Valid T304 := by
  apply bound_of_layers (bs := bsT304) (last := T304r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT304 vT304r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T305 : Bound := ⟨0x1100110011001100000000000000000011001100110011, [0x0, 0x100010001000100000000000000000001000100010001, 0x110000001100000000000000000000001100000011, 0x11001100000000000000000000000000110011, 0x11001100110011], 0x10000000100000000000000000001000100110011, 4⟩
def bsT305 : Array Bound := [].toArray
theorem vbsT305 : ∀ s ∈ bsT305, Valid s := by
  intro s hs
  simp only [bsT305,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T305r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T305r3 : Records := #[T305r3p0]
def testT305r3 : ℕ → Bool := testAt T305 bsT305 2 (#[] : Records) T305r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T305r3c0 : checkBlock testT305r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT305r3 : LayerOK T305 3 T305r3 := by
  apply layer_of_block (bs := bsT305) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT305 (emptyOK _ _)
  exact @block_merge testT305r3 0 1 31 T305r3c0 (show checkBlock testT305r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT305 : Valid T305 := by
  apply bound_of_layers (bs := bsT305) (last := T305r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT305 vT305r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T306 : Bound := ⟨0xf000000000000000f000000000000000f000000000000000f, [0x0, 0x5000000000000000500000000000000050000000000000005, 0x3000000000000000300000000000000030000000000000003, 0xf0000000000000000000000000000000f, 0xf000000000000000f], 0x100000000000000050000000000000001000000000000000f, 4⟩
def bsT306 : Array Bound := [].toArray
theorem vbsT306 : ∀ s ∈ bsT306, Valid s := by
  intro s hs
  simp only [bsT306,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T306r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T306r3 : Records := #[T306r3p0]
def testT306r3 : ℕ → Bool := testAt T306 bsT306 2 (#[] : Records) T306r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T306r3c0 : checkBlock testT306r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT306r3 : LayerOK T306 3 T306r3 := by
  apply layer_of_block (bs := bsT306) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT306 (emptyOK _ _)
  exact @block_merge testT306r3 0 1 31 T306r3c0 (show checkBlock testT306r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT306 : Valid T306 := by
  apply bound_of_layers (bs := bsT306) (last := T306r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT306 vT306r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T307 : Bound := ⟨0x33000000000000003300000000000000330000000000000033, [0x0, 0x11000000000000001100000000000000110000000000000011, 0x3000000000000000300000000000000030000000000000003, 0x3300000000000000000000000000000033, 0x330000000000000033], 0x1000000000000000100000000000000110000000000000033, 4⟩
def bsT307 : Array Bound := [].toArray
theorem vbsT307 : ∀ s ∈ bsT307, Valid s := by
  intro s hs
  simp only [bsT307,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T307r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T307r3 : Records := #[T307r3p0]
def testT307r3 : ℕ → Bool := testAt T307 bsT307 2 (#[] : Records) T307r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T307r3c0 : checkBlock testT307r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT307r3 : LayerOK T307 3 T307r3 := by
  apply layer_of_block (bs := bsT307) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT307 (emptyOK _ _)
  exact @block_merge testT307r3 0 1 31 T307r3c0 (show checkBlock testT307r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT307 : Valid T307 := by
  apply bound_of_layers (bs := bsT307) (last := T307r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT307 vT307r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T308 : Bound := ⟨0x110011000000000011001100000000001100110000000000110011, [0x0, 0x10001000000000001000100000000000100010000000000010001, 0x11000000000000001100000000000000110000000000000011, 0x11001100000000000000000000000000110011, 0x1100110000000000110011], 0x1000000000000000100000000000000110000000000110011, 4⟩
def bsT308 : Array Bound := [].toArray
theorem vbsT308 : ∀ s ∈ bsT308, Valid s := by
  intro s hs
  simp only [bsT308,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T308r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T308r3 : Records := #[T308r3p0]
def testT308r3 : ℕ → Bool := testAt T308 bsT308 2 (#[] : Records) T308r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T308r3c0 : checkBlock testT308r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT308r3 : LayerOK T308 3 T308r3 := by
  apply layer_of_block (bs := bsT308) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT308 (emptyOK _ _)
  exact @block_merge testT308r3 0 1 31 T308r3c0 (show checkBlock testT308r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT308 : Valid T308 := by
  apply bound_of_layers (bs := bsT308) (last := T308r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT308 vT308r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T309 : Bound := ⟨0xf000f00000000000f000f, [0x0, 0x500050000000000050005, 0x300030000000000030003, 0xf000000000000000f, 0xf000f], 0x1000000000001000f, 5⟩
def bsT309 : Array Bound := [T144].toArray
theorem vbsT309 : ∀ s ∈ bsT309, Valid s := by
  intro s hs
  simp only [bsT309,List.mem_toArray] at hs
  exact (familyCons vT144 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT309 : Valid T309 := by
  apply bound_of_layers (bs := bsT309) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT309 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T310 : Bound := ⟨0xf000f00000000000f000f0, [0x0, 0x5000500000000000500050, 0x3000300000000000300030, 0xf000000000000000f0, 0xf000f0], 0x1000000000001000f0, 5⟩
def bsT310 : Array Bound := [T146].toArray
theorem vbsT310 : ∀ s ∈ bsT310, Valid s := by
  intro s hs
  simp only [bsT310,List.mem_toArray] at hs
  exact (familyCons vT146 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT310 : Valid T310 := by
  apply bound_of_layers (bs := bsT310) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT310 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T311 : Bound := ⟨0x30003000300030003000300030003, [0x0, 0x10001000100010001000100010001, 0x3000000030000000300000003, 0x300030000000000030003, 0x3000300030003], 0x1000000010001000100010003, 5⟩
def bsT311 : Array Bound := [T144].toArray
theorem vbsT311 : ∀ s ∈ bsT311, Valid s := by
  intro s hs
  simp only [bsT311,List.mem_toArray] at hs
  exact (familyCons vT144 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT311 : Valid T311 := by
  apply bound_of_layers (bs := bsT311) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT311 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T312 : Bound := ⟨0x50005000500050005000500050005, [0x0, 0x10001000100010001000100010001, 0x5000000050000000500000005, 0x500050000000000050005, 0x5000500050005], 0x1000000010001000100010005, 5⟩
def bsT312 : Array Bound := [T145].toArray
theorem vbsT312 : ∀ s ∈ bsT312, Valid s := by
  intro s hs
  simp only [bsT312,List.mem_toArray] at hs
  exact (familyCons vT145 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT312 : Valid T312 := by
  apply bound_of_layers (bs := bsT312) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT312 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T313 : Bound := ⟨0x300030003000300030003000300030, [0x0, 0x100010001000100010001000100010, 0x30000000300000003000000030, 0x3000300000000000300030, 0x30003000300030], 0x100000000000100030, 5⟩
def bsT313 : Array Bound := [T146].toArray
theorem vbsT313 : ∀ s ∈ bsT313, Valid s := by
  intro s hs
  simp only [bsT313,List.mem_toArray] at hs
  exact (familyCons vT146 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT313 : Valid T313 := by
  apply bound_of_layers (bs := bsT313) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT313 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T314 : Bound := ⟨0x500050005000500050005000500050, [0x0, 0x100010001000100010001000100010, 0x50000000500000005000000050, 0x5000500000000000500050, 0x50005000500050], 0x100000000000100050, 5⟩
def bsT314 : Array Bound := [T147].toArray
theorem vbsT314 : ∀ s ∈ bsT314, Valid s := by
  intro s hs
  simp only [bsT314,List.mem_toArray] at hs
  exact (familyCons vT147 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT314 : Valid T314 := by
  apply bound_of_layers (bs := bsT314) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT314 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T315 : Bound := ⟨0xf000f000000000000000000000000000f000f, [0x0, 0x5000500000000000000000000000000050005, 0x3000300000000000000000000000000030003, 0xf0000000000000000000000000000000f, 0xf000f], 0x50000000000000000000000000001000f, 5⟩
def bsT315 : Array Bound := [T148].toArray
theorem vbsT315 : ∀ s ∈ bsT315, Valid s := by
  intro s hs
  simp only [bsT315,List.mem_toArray] at hs
  exact (familyCons vT148 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT315 : Valid T315 := by
  apply bound_of_layers (bs := bsT315) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT315 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T316 : Bound := ⟨0x33003300000000000000000000000000330033, [0x0, 0x11001100000000000000000000000000110011, 0x3000300000000000000000000000000030003, 0x3300000000000000000000000000000033, 0x330033], 0x100000000000000000000000000110033, 5⟩
def bsT316 : Array Bound := [T148].toArray
theorem vbsT316 : ∀ s ∈ bsT316, Valid s := by
  intro s hs
  simp only [bsT316,List.mem_toArray] at hs
  exact (familyCons vT148 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT316 : Valid T316 := by
  apply bound_of_layers (bs := bsT316) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT316 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T317 : Bound := ⟨0x300030003000300000000000000000003000300030003, [0x0, 0x100010001000100000000000000000001000100010001, 0x30000000300000000000000000000000300000003, 0x3000300000000000000000000000000030003, 0x3000300030003], 0x10000000100000000000000000001000100010003, 5⟩
def bsT317 : Array Bound := [T148].toArray
theorem vbsT317 : ∀ s ∈ bsT317, Valid s := by
  intro s hs
  simp only [bsT317,List.mem_toArray] at hs
  exact (familyCons vT148 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT317 : Valid T317 := by
  apply bound_of_layers (bs := bsT317) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT317 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T318 : Bound := ⟨0x30003000000000003000300000000000300030000000000030003, [0x0, 0x10001000000000001000100000000000100010000000000010001, 0x3000000000000000300000000000000030000000000000003, 0x3000300000000000000000000000000030003, 0x300030000000000030003], 0x1000000000000000100000000000000010000000000010003, 5⟩
def bsT318 : Array Bound := [T144].toArray
theorem vbsT318 : ∀ s ∈ bsT318, Valid s := by
  intro s hs
  simp only [bsT318,List.mem_toArray] at hs
  exact (familyCons vT144 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT318 : Valid T318 := by
  apply bound_of_layers (bs := bsT318) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT318 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T319 : Bound := ⟨0x50005000000000005000500000000000500050000000000050005, [0x0, 0x10001000000000001000100000000000100010000000000010001, 0x5000000000000000500000000000000050000000000000005, 0x5000500000000000000000000000000050005, 0x500050000000000050005], 0x1000000000000000500000000000000010000000000010005, 5⟩
def bsT319 : Array Bound := [T145].toArray
theorem vbsT319 : ∀ s ∈ bsT319, Valid s := by
  intro s hs
  simp only [bsT319,List.mem_toArray] at hs
  exact (familyCons vT145 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT319 : Valid T319 := by
  apply bound_of_layers (bs := bsT319) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT319 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T320 : Bound := ⟨0x300030000000000030003000000000003000300000000000300030, [0x0, 0x100010000000000010001000000000001000100000000000100010, 0x30000000000000003000000000000000300000000000000030, 0x30003000000000000000000000000000300030, 0x3000300000000000300030], 0x100000000000100030, 5⟩
def bsT320 : Array Bound := [T146].toArray
theorem vbsT320 : ∀ s ∈ bsT320, Valid s := by
  intro s hs
  simp only [bsT320,List.mem_toArray] at hs
  exact (familyCons vT146 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT320 : Valid T320 := by
  apply bound_of_layers (bs := bsT320) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT320 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T321 : Bound := ⟨0x500050000000000050005000000000005000500000000000500050, [0x0, 0x100010000000000010001000000000001000100000000000100010, 0x50000000000000005000000000000000500000000000000050, 0x50005000000000000000000000000000500050, 0x5000500000000000500050], 0x100000000000100050, 5⟩
def bsT321 : Array Bound := [T147].toArray
theorem vbsT321 : ∀ s ∈ bsT321, Valid s := by
  intro s hs
  simp only [bsT321,List.mem_toArray] at hs
  exact (familyCons vT147 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT321 : Valid T321 := by
  apply bound_of_layers (bs := bsT321) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT321 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T370 : Bound := ⟨0xff00ff00ff00ff, [0x0, 0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff], 0x10001001100ff, 5⟩
def bsT370 : Array Bound := [T295].toArray
theorem vbsT370 : ∀ s ∈ bsT370, Valid s := by
  intro s hs
  simp only [bsT370,List.mem_toArray] at hs
  exact (familyCons vT295 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT370 : Valid T370 := by
  apply bound_of_layers (bs := bsT370) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT370 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T372 : Bound := ⟨0xff000000ff000000ff000000ff, [0x0, 0x55000000550000005500000055, 0x33000000330000003300000033, 0xf0000000f0000000f0000000f, 0xff00000000000000ff, 0xff000000ff], 0x10000001100000001000000ff, 5⟩
def bsT372 : Array Bound := [T299].toArray
theorem vbsT372 : ∀ s ∈ bsT372, Valid s := by
  intro s hs
  simp only [bsT372,List.mem_toArray] at hs
  exact (familyCons vT299 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT372 : Valid T372 := by
  apply bound_of_layers (bs := bsT372) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT372 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T373 : Bound := ⟨0xff000000ff0000000000000000000000ff000000ff, [0x0, 0x550000005500000000000000000000005500000055, 0x330000003300000000000000000000003300000033, 0xf0000000f00000000000000000000000f0000000f, 0xff000000000000000000000000000000ff, 0xff000000ff], 0x100000005000000000000000000000001000000ff, 5⟩
def bsT373 : Array Bound := [T302].toArray
theorem vbsT373 : ∀ s ∈ bsT373, Valid s := by
  intro s hs
  simp only [bsT373,List.mem_toArray] at hs
  exact (familyCons vT302 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT373 : Valid T373 := by
  apply bound_of_layers (bs := bsT373) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT373 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T374 : Bound := ⟨0xff00000000000000ff00000000000000ff00000000000000ff, [0x0, 0x55000000000000005500000000000000550000000000000055, 0x33000000000000003300000000000000330000000000000033, 0xf000000000000000f000000000000000f000000000000000f, 0xff000000000000000000000000000000ff, 0xff00000000000000ff], 0x10000000000000005000000000000001100000000000000ff, 5⟩
def bsT374 : Array Bound := [T306].toArray
theorem vbsT374 : ∀ s ∈ bsT374, Valid s := by
  intro s hs
  simp only [bsT374,List.mem_toArray] at hs
  exact (familyCons vT306 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT374 : Valid T374 := by
  apply bound_of_layers (bs := bsT374) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT374 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T375 : Bound := ⟨0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f, [0x0, 0x500000005000000050000000500000005000000050000000500000005, 0x300000003000000030000000300000003000000030000000300000003, 0xf000000000000000f000000000000000f000000000000000f, 0xf0000000f00000000000000000000000f0000000f, 0xf0000000f0000000f0000000f], 0x10000000100000001000000050000000100000001000000010000000f, 5⟩
def bsT375 : Array Bound := [T302].toArray
theorem vbsT375 : ∀ s ∈ bsT375, Valid s := by
  intro s hs
  simp only [bsT375,List.mem_toArray] at hs
  exact (familyCons vT302 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT375 : Valid T375 := by
  apply bound_of_layers (bs := bsT375) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT375 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T376 : Bound := ⟨0x3300000033000000330000003300000033000000330000003300000033, [0x0, 0x1100000011000000110000001100000011000000110000001100000011, 0x300000003000000030000000300000003000000030000000300000003, 0x33000000000000003300000000000000330000000000000033, 0x330000003300000000000000000000003300000033, 0x33000000330000003300000033], 0x100000001000000010000000100000001000000110000000100000033, 5⟩
def bsT376 : Array Bound := [T299].toArray
theorem vbsT376 : ∀ s ∈ bsT376, Valid s := by
  intro s hs
  simp only [bsT376,List.mem_toArray] at hs
  exact (familyCons vT299 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT376 : Valid T376 := by
  apply bound_of_layers (bs := bsT376) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT376 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T377 : Bound := ⟨0x5500000055000000550000005500000055000000550000005500000055, [0x0, 0x1100000011000000110000001100000011000000110000001100000011, 0x500000005000000050000000500000005000000050000000500000005, 0x55000000000000005500000000000000550000000000000055, 0x550000005500000000000000000000005500000055, 0x55000000550000005500000055], 0x100000001000000010000000500000001000000110000000100000055, 5⟩
def bsT377 : Array Bound := [T300].toArray
theorem vbsT377 : ∀ s ∈ bsT377, Valid s := by
  intro s hs
  simp only [bsT377,List.mem_toArray] at hs
  exact (familyCons vT300 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT377 : Valid T377 := by
  apply bound_of_layers (bs := bsT377) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT377 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T378 : Bound := ⟨0x11001100110011001100110011001100110011001100110011001100110011, [0x0, 0x1000100010001000100010001000100010001000100010001000100010001, 0x1100000011000000110000001100000011000000110000001100000011, 0x110011000000000011001100000000001100110000000000110011, 0x1100110011001100000000000000000011001100110011, 0x110011001100110011001100110011], 0x100000001000000010000000100000001000000110001000100110011, 5⟩
def bsT378 : Array Bound := [T305].toArray
theorem vbsT378 : ∀ s ∈ bsT378, Valid s := by
  intro s hs
  simp only [bsT378,List.mem_toArray] at hs
  exact (familyCons vT305 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT378 : Valid T378 := by
  apply bound_of_layers (bs := bsT378) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT378 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T380 : Bound := ⟨0xf000f000f000f000f000f000f000f0, [0x0, 0x500050005000500050005000500050, 0x300030003000300030003000300030, 0xf0000000f0000000f0000000f0, 0xf000f00000000000f000f0, 0xf000f000f000f0], 0x1000000000001000f0, 6⟩
def bsT380 : Array Bound := [T310].toArray
theorem vbsT380 : ∀ s ∈ bsT380, Valid s := by
  intro s hs
  simp only [bsT380,List.mem_toArray] at hs
  exact (familyCons vT310 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT380 : Valid T380 := by
  apply bound_of_layers (bs := bsT380) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT380 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T381 : Bound := ⟨0xff00ff00000000000000000000000000ff00ff, [0x0, 0x55005500000000000000000000000000550055, 0x33003300000000000000000000000000330033, 0xf000f000000000000000000000000000f000f, 0xff000000000000000000000000000000ff, 0xff00ff], 0x5000000000000000000000000001100ff, 6⟩
def bsT381 : Array Bound := [T315].toArray
theorem vbsT381 : ∀ s ∈ bsT381, Valid s := by
  intro s hs
  simp only [bsT381,List.mem_toArray] at hs
  exact (familyCons vT315 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT381 : Valid T381 := by
  apply bound_of_layers (bs := bsT381) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT381 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T382 : Bound := ⟨0xf000f000f000f0000000000000000000f000f000f000f, [0x0, 0x500050005000500000000000000000005000500050005, 0x300030003000300000000000000000003000300030003, 0xf0000000f00000000000000000000000f0000000f, 0xf000f000000000000000000000000000f000f, 0xf000f000f000f], 0x1000000050000000000000000000100010001000f, 6⟩
def bsT382 : Array Bound := [T315].toArray
theorem vbsT382 : ∀ s ∈ bsT382, Valid s := by
  intro s hs
  simp only [bsT382,List.mem_toArray] at hs
  exact (familyCons vT315 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT382 : Valid T382 := by
  apply bound_of_layers (bs := bsT382) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT382 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T383 : Bound := ⟨0x3300330033003300000000000000000033003300330033, [0x0, 0x1100110011001100000000000000000011001100110011, 0x300030003000300000000000000000003000300030003, 0x330000003300000000000000000000003300000033, 0x33003300000000000000000000000000330033, 0x33003300330033], 0x10000000100000000000000000001000100110033, 6⟩
def bsT383 : Array Bound := [T316].toArray
theorem vbsT383 : ∀ s ∈ bsT383, Valid s := by
  intro s hs
  simp only [bsT383,List.mem_toArray] at hs
  exact (familyCons vT316 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT383 : Valid T383 := by
  apply bound_of_layers (bs := bsT383) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT383 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T384 : Bound := ⟨0xf000f00000000000f000f00000000000f000f00000000000f000f0, [0x0, 0x500050000000000050005000000000005000500000000000500050, 0x300030000000000030003000000000003000300000000000300030, 0xf000000000000000f000000000000000f000000000000000f0, 0xf000f000000000000000000000000000f000f0, 0xf000f00000000000f000f0], 0x1000000000001000f0, 6⟩
def bsT384 : Array Bound := [T310].toArray
theorem vbsT384 : ∀ s ∈ bsT384, Valid s := by
  intro s hs
  simp only [bsT384,List.mem_toArray] at hs
  exact (familyCons vT310 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT384 : Valid T384 := by
  apply bound_of_layers (bs := bsT384) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT384 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T385 : Bound := ⟨0x3000300030003000300030003000300030003000300030003000300030003, [0x0, 0x1000100010001000100010001000100010001000100010001000100010001, 0x300000003000000030000000300000003000000030000000300000003, 0x30003000000000003000300000000000300030000000000030003, 0x300030003000300000000000000000003000300030003, 0x30003000300030003000300030003], 0x100000001000000010000000100000001000000010001000100010003, 6⟩
def bsT385 : Array Bound := [T311].toArray
theorem vbsT385 : ∀ s ∈ bsT385, Valid s := by
  intro s hs
  simp only [bsT385,List.mem_toArray] at hs
  exact (familyCons vT311 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT385 : Valid T385 := by
  apply bound_of_layers (bs := bsT385) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT385 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T386 : Bound := ⟨0x5000500050005000500050005000500050005000500050005000500050005, [0x0, 0x1000100010001000100010001000100010001000100010001000100010001, 0x500000005000000050000000500000005000000050000000500000005, 0x50005000000000005000500000000000500050000000000050005, 0x500050005000500000000000000000005000500050005, 0x50005000500050005000500050005], 0x100000001000000010000000500000001000000010001000100010005, 6⟩
def bsT386 : Array Bound := [T312].toArray
theorem vbsT386 : ∀ s ∈ bsT386, Valid s := by
  intro s hs
  simp only [bsT386,List.mem_toArray] at hs
  exact (familyCons vT312 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT386 : Valid T386 := by
  apply bound_of_layers (bs := bsT386) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT386 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T387 : Bound := ⟨0x30003000300030003000300030003000300030003000300030003000300030, [0x0, 0x10001000100010001000100010001000100010001000100010001000100010, 0x3000000030000000300000003000000030000000300000003000000030, 0x300030000000000030003000000000003000300000000000300030, 0x3000300030003000000000000000000030003000300030, 0x300030003000300030003000300030], 0x100000000000100030, 6⟩
def bsT387 : Array Bound := [T313].toArray
theorem vbsT387 : ∀ s ∈ bsT387, Valid s := by
  intro s hs
  simp only [bsT387,List.mem_toArray] at hs
  exact (familyCons vT313 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT387 : Valid T387 := by
  apply bound_of_layers (bs := bsT387) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT387 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T388 : Bound := ⟨0x50005000500050005000500050005000500050005000500050005000500050, [0x0, 0x10001000100010001000100010001000100010001000100010001000100010, 0x5000000050000000500000005000000050000000500000005000000050, 0x500050000000000050005000000000005000500000000000500050, 0x5000500050005000000000000000000050005000500050, 0x500050005000500050005000500050], 0x100000000000100050, 6⟩
def bsT388 : Array Bound := [T314].toArray
theorem vbsT388 : ∀ s ∈ bsT388, Valid s := by
  intro s hs
  simp only [bsT388,List.mem_toArray] at hs
  exact (familyCons vT314 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT388 : Valid T388 := by
  apply bound_of_layers (bs := bsT388) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT388 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T389 : Bound := ⟨0x330033003300330033003300330033, [0x0, 0x110011001100110011001100110011, 0x30003000300030003000300030003, 0x33000000330000003300000033, 0x3300330000000000330033, 0x33003300330033], 0x1000000110001000100110033, 7⟩
def bsT389 : Array Bound := [T144, T295, T299, T311, T313].toArray
theorem vbsT389 : ∀ s ∈ bsT389, Valid s := by
  intro s hs
  simp only [bsT389,List.mem_toArray] at hs
  exact (familyCons vT144 <| familyCons vT295 <| familyCons vT299 <| familyCons vT311 <| familyCons vT313 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T389r4p0 : RecordPage := #[
(0x4a18403e, 0x0), (0x4818803e, 0x0)]
def T389r4 : Records := #[T389r4p0]
def testT389r4 : ℕ → Bool := testAt T389 bsT389 3 (#[] : Records) T389r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T389r4c0 : checkBlock testT389r4 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT389r4 : LayerOK T389 4 T389r4 := by
  apply layer_of_block (bs := bsT389) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT389 (emptyOK _ _)
  exact @block_merge testT389r4 0 2 30 T389r4c0 (show checkBlock testT389r4 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T389r5p0 : RecordPage := #[
(0x18403e, 0x9), (0x1c403e, 0x68), (0x18803e, 0x13), (0x1c803e, 0x68),
(0x18843e, 0x2)]
def T389r5 : Records := #[T389r5p0]
def testT389r5 : ℕ → Bool := testAt T389 bsT389 4 T389r4 T389r5 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T389r5c0 : checkBlock testT389r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T389r5c1 : checkBlock testT389r5 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT389r5 : LayerOK T389 5 T389r5 := by
  apply layer_of_block (bs := bsT389) (k := 4) (old := T389r4) (cw := 3) (rw := 1) (by decide +kernel) vbsT389 vT389r4
  exact @block_merge testT389r5 0 5 27 (@block_merge testT389r5 0 4 1 T389r5c0 T389r5c1) (show checkBlock testT389r5 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T389r6p0 : RecordPage := #[
(0x3e, 0x2429000066666666866666272500004341666668)]
def T389r6 : Records := #[T389r6p0]
def testT389r6 : ℕ → Bool := testAt T389 bsT389 5 T389r5 T389r6 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T389r6c0 : checkBlock testT389r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT389r6 : LayerOK T389 6 T389r6 := by
  apply layer_of_block (bs := bsT389) (k := 5) (old := T389r5) (cw := 3) (rw := 3) (by decide +kernel) vbsT389 vT389r5
  exact @block_merge testT389r6 0 1 31 T389r6c0 (show checkBlock testT389r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT389 : Valid T389 := by
  apply bound_of_layers (bs := bsT389) (last := T389r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT389 vT389r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T390 : Bound := ⟨0x550055005500550055005500550055, [0x0, 0x110011001100110011001100110011, 0x50005000500050005000500050005, 0x55000000550000005500000055, 0x5500550000000000550055, 0x55005500550055], 0x1000000110001000100110055, 7⟩
def bsT390 : Array Bound := [T145, T296, T300, T312, T314].toArray
theorem vbsT390 : ∀ s ∈ bsT390, Valid s := by
  intro s hs
  simp only [bsT390,List.mem_toArray] at hs
  exact (familyCons vT145 <| familyCons vT296 <| familyCons vT300 <| familyCons vT312 <| familyCons vT314 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T390r4p0 : RecordPage := #[
(0x4a18403e, 0x0), (0x4818803e, 0x0)]
def T390r4 : Records := #[T390r4p0]
def testT390r4 : ℕ → Bool := testAt T390 bsT390 3 (#[] : Records) T390r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T390r4c0 : checkBlock testT390r4 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT390r4 : LayerOK T390 4 T390r4 := by
  apply layer_of_block (bs := bsT390) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT390 (emptyOK _ _)
  exact @block_merge testT390r4 0 2 30 T390r4c0 (show checkBlock testT390r4 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T390r5p0 : RecordPage := #[
(0x18403e, 0x9), (0x1c403e, 0x68), (0x18803e, 0x13), (0x1c803e, 0x68),
(0x18843e, 0x2)]
def T390r5 : Records := #[T390r5p0]
def testT390r5 : ℕ → Bool := testAt T390 bsT390 4 T390r4 T390r5 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T390r5c0 : checkBlock testT390r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T390r5c1 : checkBlock testT390r5 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT390r5 : LayerOK T390 5 T390r5 := by
  apply layer_of_block (bs := bsT390) (k := 4) (old := T390r4) (cw := 3) (rw := 1) (by decide +kernel) vbsT390 vT390r4
  exact @block_merge testT390r5 0 5 27 (@block_merge testT390r5 0 4 1 T390r5c0 T390r5c1) (show checkBlock testT390r5 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T390r6p0 : RecordPage := #[
(0x3e, 0x2429000066666666866666272500004341666668)]
def T390r6 : Records := #[T390r6p0]
def testT390r6 : ℕ → Bool := testAt T390 bsT390 5 T390r5 T390r6 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T390r6c0 : checkBlock testT390r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT390r6 : LayerOK T390 6 T390r6 := by
  apply layer_of_block (bs := bsT390) (k := 5) (old := T390r5) (cw := 3) (rw := 3) (by decide +kernel) vbsT390 vT390r5
  exact @block_merge testT390r6 0 1 31 T390r6c0 (show checkBlock testT390r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT390 : Valid T390 := by
  apply bound_of_layers (bs := bsT390) (last := T390r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT390 vT390r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T391 : Bound := ⟨0x5500550055005500000000000000000055005500550055, [0x0, 0x1100110011001100000000000000000011001100110011, 0x500050005000500000000000000000005000500050005, 0x550000005500000000000000000000005500000055, 0x55005500000000000000000000000000550055, 0x55005500550055], 0x10000000500000000000000000001000100110055, 7⟩
def bsT391 : Array Bound := [T296, T301, T303, T304, T305].toArray
theorem vbsT391 : ∀ s ∈ bsT391, Valid s := by
  intro s hs
  simp only [bsT391,List.mem_toArray] at hs
  exact (familyCons vT296 <| familyCons vT301 <| familyCons vT303 <| familyCons vT304 <| familyCons vT305 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T391r4p0 : RecordPage := #[
(0x4818203e, 0x0), (0x4818803e, 0x0), (0x4a18423e, 0x0), (0x4618643e, 0x0),
(0x4818863e, 0x0)]
def T391r4 : Records := #[T391r4p0]
def testT391r4 : ℕ → Bool := testAt T391 bsT391 3 (#[] : Records) T391r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T391r4c0 : checkBlock testT391r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T391r4c1 : checkBlock testT391r4 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT391r4 : LayerOK T391 4 T391r4 := by
  apply layer_of_block (bs := bsT391) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT391 (emptyOK _ _)
  exact @block_merge testT391r4 0 5 27 (@block_merge testT391r4 0 4 1 T391r4c0 T391r4c1) (show checkBlock testT391r4 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T391r5p0 : RecordPage := #[
(0x18203e, 0x21), (0x18403e, 0x0), (0x18603e, 0x0), (0x18803e, 0x43),
(0x18423e, 0x5), (0x18623e, 0x0), (0x18823e, 0x0), (0x18643e, 0x87),
(0x18843e, 0x0), (0x18863e, 0x69)]
def T391r5 : Records := #[T391r5p0]
def testT391r5 : ℕ → Bool := testAt T391 bsT391 4 T391r4 T391r5 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T391r5c0 : checkBlock testT391r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T391r5c1 : checkBlock testT391r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T391r5c2 : checkBlock testT391r5 2 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT391r5 : LayerOK T391 5 T391r5 := by
  apply layer_of_block (bs := bsT391) (k := 4) (old := T391r4) (cw := 3) (rw := 3) (by decide +kernel) vbsT391 vT391r4
  exact @block_merge testT391r5 0 10 22 (@block_merge testT391r5 0 4 6 T391r5c0 (@block_merge testT391r5 4 4 2 T391r5c1 T391r5c2)) (show checkBlock testT391r5 22 10 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T391r6p0 : RecordPage := #[
(0x3e, 0x826081124278303498968c890803941152106d0c1)]
def T391r6 : Records := #[T391r6p0]
def testT391r6 : ℕ → Bool := testAt T391 bsT391 5 T391r5 T391r6 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T391r6c0 : checkBlock testT391r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT391r6 : LayerOK T391 6 T391r6 := by
  apply layer_of_block (bs := bsT391) (k := 5) (old := T391r5) (cw := 3) (rw := 4) (by decide +kernel) vbsT391 vT391r5
  exact @block_merge testT391r6 0 1 31 T391r6c0 (show checkBlock testT391r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT391 : Valid T391 := by
  apply bound_of_layers (bs := bsT391) (last := T391r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT391 vT391r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T392 : Bound := ⟨0xf000f00000000000f000f00000000000f000f00000000000f000f, [0x0, 0x50005000000000005000500000000000500050000000000050005, 0x30003000000000003000300000000000300030000000000030003, 0xf000000000000000f000000000000000f000000000000000f, 0xf000f000000000000000000000000000f000f, 0xf000f00000000000f000f], 0x100000000000000050000000000000001000000000001000f, 7⟩
def bsT392 : Array Bound := [T309, T315, T318, T319].toArray
theorem vbsT392 : ∀ s ∈ bsT392, Valid s := by
  intro s hs
  simp only [bsT392,List.mem_toArray] at hs
  exact (familyCons vT309 <| familyCons vT315 <| familyCons vT318 <| familyCons vT319 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T392r6p0 : RecordPage := #[
(0x3e, 0x800124800124a49000124b6da4926)]
def T392r6 : Records := #[T392r6p0]
def testT392r6 : ℕ → Bool := testAt T392 bsT392 5 (#[] : Records) T392r6 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T392r6c0 : checkBlock testT392r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT392r6 : LayerOK T392 6 T392r6 := by
  apply layer_of_block (bs := bsT392) (k := 5) (old := (#[] : Records)) (cw := 2) (rw := 1) (by decide +kernel) vbsT392 (emptyOK _ _)
  exact @block_merge testT392r6 0 1 31 T392r6c0 (show checkBlock testT392r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT392 : Valid T392 := by
  apply bound_of_layers (bs := bsT392) (last := T392r6) (cw := 2) (rw := 0) (by decide +kernel) vbsT392 vT392r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T393 : Bound := ⟨0x330033000000000033003300000000003300330000000000330033, [0x0, 0x110011000000000011001100000000001100110000000000110011, 0x30003000000000003000300000000000300030000000000030003, 0x33000000000000003300000000000000330000000000000033, 0x33003300000000000000000000000000330033, 0x3300330000000000330033], 0x1000000000000000100000000000000110000000000110033, 7⟩
def bsT393 : Array Bound := [T144, T307, T308, T316, T318, T320].toArray
theorem vbsT393 : ∀ s ∈ bsT393, Valid s := by
  intro s hs
  simp only [bsT393,List.mem_toArray] at hs
  exact (familyCons vT144 <| familyCons vT307 <| familyCons vT308 <| familyCons vT316 <| familyCons vT318 <| familyCons vT320 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T393r4p0 : RecordPage := #[
(0x4818403e, 0x0)]
def T393r4 : Records := #[T393r4p0]
def testT393r4 : ℕ → Bool := testAt T393 bsT393 3 (#[] : Records) T393r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T393r4c0 : checkBlock testT393r4 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT393r4 : LayerOK T393 4 T393r4 := by
  apply layer_of_block (bs := bsT393) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT393 (emptyOK _ _)
  exact @block_merge testT393r4 0 1 31 T393r4c0 (show checkBlock testT393r4 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T393r5p0 : RecordPage := #[
(0x18403e, 0x4d8a)]
def T393r5 : Records := #[T393r5p0]
def testT393r5 : ℕ → Bool := testAt T393 bsT393 4 T393r4 T393r5 3 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T393r5c0 : checkBlock testT393r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT393r5 : LayerOK T393 5 T393r5 := by
  apply layer_of_block (bs := bsT393) (k := 4) (old := T393r4) (cw := 3) (rw := 0) (by decide +kernel) vbsT393 vT393r4
  exact @block_merge testT393r5 0 1 31 T393r5c0 (show checkBlock testT393r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T393r6p0 : RecordPage := #[
(0x3e, 0xccccc00000cccd111150cccd1111140000cccc48588888a)]
def T393r6 : Records := #[T393r6p0]
def testT393r6 : ℕ → Bool := testAt T393 bsT393 5 T393r5 T393r6 3 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T393r6c0 : checkBlock testT393r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT393r6 : LayerOK T393 6 T393r6 := by
  apply layer_of_block (bs := bsT393) (k := 5) (old := T393r5) (cw := 3) (rw := 0) (by decide +kernel) vbsT393 vT393r5
  exact @block_merge testT393r6 0 1 31 T393r6c0 (show checkBlock testT393r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT393 : Valid T393 := by
  apply bound_of_layers (bs := bsT393) (last := T393r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT393 vT393r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T394 : Bound := ⟨0x550055000000000055005500000000005500550000000000550055, [0x0, 0x110011000000000011001100000000001100110000000000110011, 0x50005000000000005000500000000000500050000000000050005, 0x55000000000000005500000000000000550000000000000055, 0x55005500000000000000000000000000550055, 0x5500550000000000550055], 0x1000000000000000500000000000000110000000000110055, 7⟩
def bsT394 : Array Bound := [T145, T301, T308, T319, T321].toArray
theorem vbsT394 : ∀ s ∈ bsT394, Valid s := by
  intro s hs
  simp only [bsT394,List.mem_toArray] at hs
  exact (familyCons vT145 <| familyCons vT301 <| familyCons vT308 <| familyCons vT319 <| familyCons vT321 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T394r4p0 : RecordPage := #[
(0x4818403e, 0x0), (0x4618643e, 0x0)]
def T394r4 : Records := #[T394r4p0]
def testT394r4 : ℕ → Bool := testAt T394 bsT394 3 (#[] : Records) T394r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T394r4c0 : checkBlock testT394r4 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT394r4 : LayerOK T394 4 T394r4 := by
  apply layer_of_block (bs := bsT394) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT394 (emptyOK _ _)
  exact @block_merge testT394r4 0 2 30 T394r4c0 (show checkBlock testT394r4 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T394r5p0 : RecordPage := #[
(0x18403e, 0x9), (0x1a403e, 0x68), (0x18603e, 0x2), (0x18643e, 0x13),
(0x1c643e, 0x68)]
def T394r5 : Records := #[T394r5p0]
def testT394r5 : ℕ → Bool := testAt T394 bsT394 4 T394r4 T394r5 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T394r5c0 : checkBlock testT394r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T394r5c1 : checkBlock testT394r5 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT394r5 : LayerOK T394 5 T394r5 := by
  apply layer_of_block (bs := bsT394) (k := 4) (old := T394r4) (cw := 3) (rw := 1) (by decide +kernel) vbsT394 vT394r4
  exact @block_merge testT394r5 0 5 27 (@block_merge testT394r5 0 4 1 T394r5c0 T394r5c1) (show checkBlock testT394r5 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T394r6p0 : RecordPage := #[
(0x3e, 0x292766668666666666680000242544316666)]
def T394r6 : Records := #[T394r6p0]
def testT394r6 : ℕ → Bool := testAt T394 bsT394 5 T394r5 T394r6 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T394r6c0 : checkBlock testT394r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT394r6 : LayerOK T394 6 T394r6 := by
  apply layer_of_block (bs := bsT394) (k := 5) (old := T394r5) (cw := 3) (rw := 3) (by decide +kernel) vbsT394 vT394r5
  exact @block_merge testT394r6 0 1 31 T394r6c0 (show checkBlock testT394r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT394 : Valid T394 := by
  apply bound_of_layers (bs := bsT394) (last := T394r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT394 vT394r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T401 : Bound := ⟨0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff, [0x0, 0x5500000055000000550000005500000055000000550000005500000055, 0x3300000033000000330000003300000033000000330000003300000033, 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f, 0xff00000000000000ff00000000000000ff00000000000000ff, 0xff000000ff0000000000000000000000ff000000ff, 0xff000000ff000000ff000000ff], 0x1000000010000000100000005000000010000001100000001000000ff, 7⟩
def bsT401 : Array Bound := [T372, T373, T374, T375, T376, T377].toArray
theorem vbsT401 : ∀ s ∈ bsT401, Valid s := by
  intro s hs
  simp only [bsT401,List.mem_toArray] at hs
  exact (familyCons vT372 <| familyCons vT373 <| familyCons vT374 <| familyCons vT375 <| familyCons vT376 <| familyCons vT377 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T401r6p0 : RecordPage := #[
(0x7e, 0x4246a8a)]
def T401r6 : Records := #[T401r6p0]
def testT401r6 : ℕ → Bool := testAt T401 bsT401 5 (#[] : Records) T401r6 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T401r6c0 : checkBlock testT401r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT401r6 : LayerOK T401 6 T401r6 := by
  apply layer_of_block (bs := bsT401) (k := 5) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT401 (emptyOK _ _)
  exact @block_merge testT401r6 0 1 31 T401r6c0 (show checkBlock testT401r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT401 : Valid T401 := by
  apply bound_of_layers (bs := bsT401) (last := T401r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT401 vT401r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T402 : Bound := ⟨0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, [0x0, 0x50005000500050005000500050005000500050005000500050005000500050, 0x30003000300030003000300030003000300030003000300030003000300030, 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0, 0xf000f00000000000f000f00000000000f000f00000000000f000f0, 0xf000f000f000f0000000000000000000f000f000f000f0, 0xf000f000f000f000f000f000f000f0], 0x1000000000001000f0, 7⟩
def bsT402 : Array Bound := [T380].toArray
theorem vbsT402 : ∀ s ∈ bsT402, Valid s := by
  intro s hs
  simp only [bsT402,List.mem_toArray] at hs
  exact (familyCons vT380 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT402 : Valid T402 := by
  apply bound_of_layers (bs := bsT402) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT402 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T403 : Bound := ⟨0xff00ff00ff00ff00ff00ff00ff00ff, [0x0, 0x550055005500550055005500550055, 0x330033003300330033003300330033, 0xf000f000f000f000f000f000f000f, 0xff000000ff000000ff000000ff, 0xff00ff0000000000ff00ff, 0xff00ff00ff00ff], 0x10000001100010001001100ff, 8⟩
def bsT403 : Array Bound := [T389].toArray
theorem vbsT403 : ∀ s ∈ bsT403, Valid s := by
  intro s hs
  simp only [bsT403,List.mem_toArray] at hs
  exact (familyCons vT389 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT403 : Valid T403 := by
  apply bound_of_layers (bs := bsT403) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT403 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T404 : Bound := ⟨0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f, [0x0, 0x5000500050005000500050005000500050005000500050005000500050005, 0x3000300030003000300030003000300030003000300030003000300030003, 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f, 0xf000f00000000000f000f00000000000f000f00000000000f000f, 0xf000f000f000f0000000000000000000f000f000f000f, 0xf000f000f000f000f000f000f000f], 0x10000000100000001000000050000000100000001000100010001000f, 8⟩
def bsT404 : Array Bound := [T392].toArray
theorem vbsT404 : ∀ s ∈ bsT404, Valid s := by
  intro s hs
  simp only [bsT404,List.mem_toArray] at hs
  exact (familyCons vT392 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT404 : Valid T404 := by
  apply bound_of_layers (bs := bsT404) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT404 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T405 : Bound := ⟨0xff00ff00ff00ff000000000000000000ff00ff00ff00ff, [0x0, 0x5500550055005500000000000000000055005500550055, 0x3300330033003300000000000000000033003300330033, 0xf000f000f000f0000000000000000000f000f000f000f, 0xff000000ff0000000000000000000000ff000000ff, 0xff00ff00000000000000000000000000ff00ff, 0xff00ff00ff00ff], 0x100000005000000000000000000010001001100ff, 9⟩
def bsT405 : Array Bound := [T315, T316, T317, T370, T373, T381, T382, T383, T391].toArray
theorem vbsT405 : ∀ s ∈ bsT405, Valid s := by
  intro s hs
  simp only [bsT405,List.mem_toArray] at hs
  exact (familyCons vT315 <| familyCons vT316 <| familyCons vT317 <| familyCons vT370 <| familyCons vT373 <| familyCons vT381 <| familyCons vT382 <| familyCons vT383 <| familyCons vT391 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T405r4p0 : RecordPage := #[
(0x620816c38867e, 0x0), (0x620a16c38867e, 0x0), (0x620c16c38867e, 0x0), (0x82860061ea67e, 0x0)]
def T405r4 : Records := #[T405r4p0]
def testT405r4 : ℕ → Bool := testAt T405 bsT405 3 (#[] : Records) T405r4 4 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r4c0 : checkBlock testT405r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT405r4 : LayerOK T405 4 T405r4 := by
  apply layer_of_block (bs := bsT405) (k := 3) (old := (#[] : Records)) (cw := 4) (rw := 1) (by decide +kernel) vbsT405 (emptyOK _ _)
  exact @block_merge testT405r4 0 4 28 T405r4c0 (show checkBlock testT405r4 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T405r5p0 : RecordPage := #[
(0x4810c18867e, 0x0), (0x4a10c18867e, 0x0), (0x4c10c18867e, 0x0), (0x816c38867e, 0x1),
(0xa16c38867e, 0x3), (0xc16c38867e, 0x5), (0x636c38867e, 0x159), (0x4c14c1aa67e, 0x0),
(0x4a14c1ca67e, 0x0), (0x860061ea67e, 0x7), (0xa60061ea67e, 0x0), (0x880061ea67e, 0x7),
(0xa80061ea67e, 0x0), (0x10a4061ea67e, 0x1), (0x10a4081ea67e, 0x3), (0x10a40a1ea67e, 0x5)]
def T405r5 : Records := #[T405r5p0]
def testT405r5 : ℕ → Bool := testAt T405 bsT405 4 T405r4 T405r5 4 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r5c0 : checkBlock testT405r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r5c1 : checkBlock testT405r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r5c2 : checkBlock testT405r5 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r5c3 : checkBlock testT405r5 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT405r5 : LayerOK T405 5 T405r5 := by
  apply layer_of_block (bs := bsT405) (k := 4) (old := T405r4) (cw := 4) (rw := 2) (by decide +kernel) vbsT405 vT405r4
  exact @block_merge testT405r5 0 16 16 (@block_merge testT405r5 0 8 8 (@block_merge testT405r5 0 4 4 T405r5c0 T405r5c1) (@block_merge testT405r5 8 4 4 T405r5c2 T405r5c3)) (show checkBlock testT405r5 16 16 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T405r6p0 : RecordPage := #[
(0x10c18627e, 0x0), (0x14c18627e, 0x0), (0x10c38627e, 0x6), (0x14c1a627e, 0x0),
(0x14a18a27e, 0x0), (0x10a58a27e, 0xe), (0x14a58a27e, 0x0), (0x14a1aa27e, 0x0),
(0x4c1aa27e, 0x84210), (0x10a5aa27e, 0x0), (0x10c18647e, 0x0), (0x14c18647e, 0x0),
(0x10c38647e, 0x6), (0x10c58647e, 0xc), (0x14c58647e, 0x0), (0x4a1a647e, 0x84210),
(0x14c1a647e, 0x0), (0x10c5a647e, 0x0), (0x14a18a47e, 0x0), (0x14a1aa47e, 0x0),
(0x4818867e, 0x84210), (0xc818867e, 0xe), (0x10c18867e, 0x18570e01), (0x14c18867e, 0xa),
(0x12c38867e, 0xa), (0x16c38867e, 0xd5a4ea), (0x10c58867e, 0x73586), (0x4a1c867e, 0x84210),
(0x14c1c867e, 0xa), (0x12c3c867e, 0x0), (0x14818a67e, 0x0), (0x14a18a67e, 0x0)]
def T405r6p1 : RecordPage := #[
(0x14c18a67e, 0x0), (0x1421aa67e, 0x0), (0x1481aa67e, 0x0), (0x14a1aa67e, 0x0),
(0x14c1aa67e, 0x18f), (0x1481ca67e, 0x0), (0x14a1ca67e, 0x0), (0x14c1ca67e, 0x1d1),
(0x10c5ca67e, 0xa), (0x14c5ca67e, 0x0), (0x61ea67e, 0x36d07318c8cdeb3), (0x81ea67e, 0x2103750932210),
(0x1081ea67e, 0x0), (0xa1ea67e, 0x21037d0b31a10), (0x10a1ea67e, 0x0), (0xc1ea67e, 0x84210),
(0x10c1ea67e, 0x0), (0x10c5ea67e, 0x1feedaa), (0x4a18a87e, 0x84210), (0xca18a87e, 0xc),
(0x14c18a87e, 0xa), (0x481aa87e, 0x84210), (0x14c1aa87e, 0xa)]
def T405r6 : Records := #[T405r6p0, T405r6p1]
def testT405r6 : ℕ → Bool := testAt T405 bsT405 5 T405r5 T405r6 4 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c0 : checkBlock testT405r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c1 : checkBlock testT405r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c2 : checkBlock testT405r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c3 : checkBlock testT405r6 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c4 : checkBlock testT405r6 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c5 : checkBlock testT405r6 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c6 : checkBlock testT405r6 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c7 : checkBlock testT405r6 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c8 : checkBlock testT405r6 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c9 : checkBlock testT405r6 4 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c10 : checkBlock testT405r6 4 40 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c11 : checkBlock testT405r6 4 44 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c12 : checkBlock testT405r6 4 48 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r6c13 : checkBlock testT405r6 3 52 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT405r6 : LayerOK T405 6 T405r6 := by
  apply layer_of_block (bs := bsT405) (k := 5) (old := T405r5) (cw := 4) (rw := 4) (by decide +kernel) vbsT405 vT405r5
  exact @block_merge testT405r6 0 55 9 (@block_merge testT405r6 0 28 27 (@block_merge testT405r6 0 12 16 (@block_merge testT405r6 0 4 8 T405r6c0 (@block_merge testT405r6 4 4 4 T405r6c1 T405r6c2)) (@block_merge testT405r6 12 8 8 (@block_merge testT405r6 12 4 4 T405r6c3 T405r6c4) (@block_merge testT405r6 20 4 4 T405r6c5 T405r6c6))) (@block_merge testT405r6 28 12 15 (@block_merge testT405r6 28 4 8 T405r6c7 (@block_merge testT405r6 32 4 4 T405r6c8 T405r6c9)) (@block_merge testT405r6 40 8 7 (@block_merge testT405r6 40 4 4 T405r6c10 T405r6c11) (@block_merge testT405r6 48 4 3 T405r6c12 T405r6c13)))) (show checkBlock testT405r6 9 55 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T405r7p0 : RecordPage := #[
(0x18627e, 0x210109c1610739c8303301509426118484210739c8), (0x1a627e, 0x84042529c4841ce720c1cc8509426118484210739c8), (0x18a27e, 0x840421a2d4a70571210739c6509424094016118484210739c6), (0x1aa27e, 0x210108c4e10739c65094231150903cc66118484210739c6),
(0x18647e, 0x840e9b0018654a612106318831731550140711c48421063188), (0x1a647e, 0x21042300210631883213214050107d40711c48421063188), (0x18a47e, 0x210001866106318650140425415711c48421063186), (0x1aa47e, 0x84000529848418c6194050109cc6711c48421063186),
(0x18867e, 0x2108414d54c50a1066c40010a105290a32f32d60180709c256a5c2842105214a), (0x1c867e, 0x2108410ec0010a1052948339321806010dd80709c2842105214a), (0x18a67e, 0x84210262e10466e103210654152d63f61573d70184210420c6), (0x1aa67e, 0x8421030d841db13190654951991d8674571a10840c6866),
(0x1ca67e, 0x84210a745076103190854f5219358874b722108421a0c6), (0x1ea67e, 0x210840d8d0ccc632146519584d7d86619974d6dc6719d64d5e108421035531906), (0x18a87e, 0x2108431d1000428414d54053a105294646942d60180cf9580709c28421052946), (0x1aa87e, 0x210840d4c0010a105294646d31980601c2708dadc28421052946)]
def T405r7 : Records := #[T405r7p0]
def testT405r7 : ℕ → Bool := testAt T405 bsT405 6 T405r6 T405r7 4 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r7c0 : checkBlock testT405r7 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r7c1 : checkBlock testT405r7 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r7c2 : checkBlock testT405r7 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r7c3 : checkBlock testT405r7 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT405r7 : LayerOK T405 7 T405r7 := by
  apply layer_of_block (bs := bsT405) (k := 6) (old := T405r6) (cw := 4) (rw := 6) (by decide +kernel) vbsT405 vT405r6
  exact @block_merge testT405r7 0 16 16 (@block_merge testT405r7 0 8 8 (@block_merge testT405r7 0 4 4 T405r7c0 T405r7c1) (@block_merge testT405r7 8 4 4 T405r7c2 T405r7c3)) (show checkBlock testT405r7 16 16 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T405r8p0 : RecordPage := #[
(0x7e, 0x52bfdde6f554d51631ed5314063169738e5539427386163984842108421084210842108421084210)]
def T405r8 : Records := #[T405r8p0]
def testT405r8 : ℕ → Bool := testAt T405 bsT405 7 T405r7 T405r8 4 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T405r8c0 : checkBlock testT405r8 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT405r8 : LayerOK T405 8 T405r8 := by
  apply layer_of_block (bs := bsT405) (k := 7) (old := T405r7) (cw := 4) (rw := 4) (by decide +kernel) vbsT405 vT405r7
  exact @block_merge testT405r8 0 1 31 T405r8c0 (show checkBlock testT405r8 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT405 : Valid T405 := by
  apply bound_of_layers (bs := bsT405) (last := T405r8) (cw := 4) (rw := 0) (by decide +kernel) vbsT405 vT405r8 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T406 : Bound := ⟨0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, [0x0, 0x550055000000000055005500000000005500550000000000550055, 0x330033000000000033003300000000003300330000000000330033, 0xf000f00000000000f000f00000000000f000f00000000000f000f, 0xff00000000000000ff00000000000000ff00000000000000ff, 0xff00ff00000000000000000000000000ff00ff, 0xff00ff0000000000ff00ff], 0x10000000000000005000000000000001100000000001100ff, 9⟩
def bsT406 : Array Bound := [T309, T310, T374, T381, T384, T392, T393, T394].toArray
theorem vbsT406 : ∀ s ∈ bsT406, Valid s := by
  intro s hs
  simp only [bsT406,List.mem_toArray] at hs
  exact (familyCons vT309 <| familyCons vT310 <| familyCons vT374 <| familyCons vT381 <| familyCons vT384 <| familyCons vT392 <| familyCons vT393 <| familyCons vT394 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T406r5p0 : RecordPage := #[
(0x4a18830647e, 0x0), (0x4c18a92a47e, 0x0), (0x661ca92a47e, 0x0), (0x4810c18867e, 0x0),
(0x4a10c18867e, 0x0), (0x4a14c1ca67e, 0x0)]
def T406r5 : Records := #[T406r5p0]
def testT406r5 : ℕ → Bool := testAt T406 bsT406 4 (#[] : Records) T406r5 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T406r5c0 : checkBlock testT406r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T406r5c1 : checkBlock testT406r5 2 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT406r5 : LayerOK T406 5 T406r5 := by
  apply layer_of_block (bs := bsT406) (k := 4) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT406 (emptyOK _ _)
  exact @block_merge testT406r5 0 6 26 (@block_merge testT406r5 0 4 2 T406r5c0 T406r5c1) (show checkBlock testT406r5 26 6 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T406r6p0 : RecordPage := #[
(0x18830647e, 0x6c1), (0x14812a47e, 0xceee00eeaa88), (0x18a92a47e, 0xc3), (0x1ca92a47e, 0x58),
(0x4818867e, 0xa3aea1ee), (0xc818867e, 0xc), (0x10c18867e, 0xa8c9e7), (0x14c18867e, 0xa8),
(0x10c58867e, 0xca40), (0x14c1c867e, 0xa8), (0x14c18a67e, 0x0), (0x10c58a67e, 0x2a6),
(0x14c1ca67e, 0xcb), (0x14c18a87e, 0xa8)]
def T406r6 : Records := #[T406r6p0]
def testT406r6 : ℕ → Bool := testAt T406 bsT406 5 T406r5 T406r6 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T406r6c0 : checkBlock testT406r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T406r6c1 : checkBlock testT406r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T406r6c2 : checkBlock testT406r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T406r6c3 : checkBlock testT406r6 2 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT406r6 : LayerOK T406 6 T406r6 := by
  apply layer_of_block (bs := bsT406) (k := 5) (old := T406r5) (cw := 3) (rw := 3) (by decide +kernel) vbsT406 vT406r5
  exact @block_merge testT406r6 0 14 18 (@block_merge testT406r6 0 8 6 (@block_merge testT406r6 0 4 4 T406r6c0 T406r6c1) (@block_merge testT406r6 8 4 2 T406r6c2 T406r6c3)) (show checkBlock testT406r6 18 14 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T406r7p0 : RecordPage := #[
(0x10647e, 0xcc0599999999dddddddd99999c044044c8c1cccceeee8088886868cccceeeeeeaaa), (0x12a47e, 0x31d8b99999999dddddddd99999cc0c000019999dddcd0d1103888cccceeeeeeaaa), (0x18867e, 0x516bb39a399dd41ccee664607836aaab333169cceeee6466), (0x1c867e, 0x28f5d9d4999dcccc81304aaaa48aacccceeee6466),
(0x18a67e, 0x576705e8333baaa88bb80101aacdaaaa28aacccceeee0400), (0x1ca67e, 0x15d9d4155445dc0008d964aaaa28aacccceeee0400), (0x18a87e, 0xa2aece0bd55056677346ab33b99981368daaaa28aacccceeee6660)]
def T406r7 : Records := #[T406r7p0]
def testT406r7 : ℕ → Bool := testAt T406 bsT406 6 T406r6 T406r7 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T406r7c0 : checkBlock testT406r7 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T406r7c1 : checkBlock testT406r7 3 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT406r7 : LayerOK T406 7 T406r7 := by
  apply layer_of_block (bs := bsT406) (k := 6) (old := T406r6) (cw := 3) (rw := 4) (by decide +kernel) vbsT406 vT406r6
  exact @block_merge testT406r7 0 7 25 (@block_merge testT406r7 0 4 3 T406r7c0 T406r7c1) (show checkBlock testT406r7 25 7 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T406r8p0 : RecordPage := #[
(0x7e, 0x660d0b096765aaaa3aaaaaaaaaa1ccccccccccccaaaaeeeeeeeeeeeeaaaaaeccccce)]
def T406r8 : Records := #[T406r8p0]
def testT406r8 : ℕ → Bool := testAt T406 bsT406 7 T406r7 T406r8 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T406r8c0 : checkBlock testT406r8 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT406r8 : LayerOK T406 8 T406r8 := by
  apply layer_of_block (bs := bsT406) (k := 7) (old := T406r7) (cw := 3) (rw := 3) (by decide +kernel) vbsT406 vT406r7
  exact @block_merge testT406r8 0 1 31 T406r8c0 (show checkBlock testT406r8 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT406 : Valid T406 := by
  apply bound_of_layers (bs := bsT406) (last := T406r8) (cw := 3) (rw := 0) (by decide +kernel) vbsT406 vT406r8 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T407 : Bound := ⟨0x33003300330033003300330033003300330033003300330033003300330033, [0x0, 0x11001100110011001100110011001100110011001100110011001100110011, 0x3000300030003000300030003000300030003000300030003000300030003, 0x3300000033000000330000003300000033000000330000003300000033, 0x330033000000000033003300000000003300330000000000330033, 0x3300330033003300000000000000000033003300330033, 0x330033003300330033003300330033], 0x100000001000000010000000100000001000000110001000100110033, 9⟩
def bsT407 : Array Bound := [T317, T376, T378, T383, T385, T387, T389, T393].toArray
theorem vbsT407 : ∀ s ∈ bsT407, Valid s := by
  intro s hs
  simp only [bsT407,List.mem_toArray] at hs
  exact (familyCons vT317 <| familyCons vT376 <| familyCons vT378 <| familyCons vT383 <| familyCons vT385 <| familyCons vT387 <| familyCons vT389 <| familyCons vT393 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T407r4p0 : RecordPage := #[
(0xa28800c1e407e, 0x0)]
def T407r4 : Records := #[T407r4p0]
def testT407r4 : ℕ → Bool := testAt T407 bsT407 3 (#[] : Records) T407r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r4c0 : checkBlock testT407r4 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT407r4 : LayerOK T407 4 T407r4 := by
  apply layer_of_block (bs := bsT407) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT407 (emptyOK _ _)
  exact @block_merge testT407r4 0 1 31 T407r4c0 (show checkBlock testT407r4 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T407r5p0 : RecordPage := #[
(0x4a18428207e, 0x0), (0x4818848207e, 0x0), (0x4a1842a207e, 0x0), (0x4210a18407e, 0x0),
(0xc0ea18407e, 0x0), (0x630a38407e, 0x0), (0x2634a38407e, 0x0), (0x8800c1e407e, 0x1),
(0x8a00c1e407e, 0x1), (0xaa00c1e407e, 0x0)]
def T407r5 : Records := #[T407r5p0]
def testT407r5 : ℕ → Bool := testAt T407 bsT407 4 T407r4 T407r5 3 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r5c0 : checkBlock testT407r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r5c1 : checkBlock testT407r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r5c2 : checkBlock testT407r5 2 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT407r5 : LayerOK T407 5 T407r5 := by
  apply layer_of_block (bs := bsT407) (k := 4) (old := T407r4) (cw := 3) (rw := 0) (by decide +kernel) vbsT407 vT407r4
  exact @block_merge testT407r5 0 10 22 (@block_merge testT407r5 0 4 6 T407r5c0 (@block_merge testT407r5 4 4 2 T407r5c1 T407r5c2)) (show checkBlock testT407r5 22 10 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T407r6p0 : RecordPage := #[
(0x18428207e, 0x8c1), (0x1a428207e, 0x0), (0x18828207e, 0x6), (0x18848207e, 0x83),
(0x1c848207e, 0x0), (0x1842a207e, 0xc5), (0x1a42a207e, 0x0), (0x10a18407e, 0x7),
(0x4a18407e, 0x330a1cc), (0xca18407e, 0x6), (0x14a18407e, 0x0), (0xea18407e, 0x127),
(0x10a38407e, 0xb6), (0x14a38407e, 0xd6), (0x10a58407e, 0xb6), (0x14a58407e, 0xd6),
(0x1421a407e, 0xc7), (0x14a1a407e, 0x0), (0x10a5a407e, 0x0), (0x14a1c407e, 0x0),
(0x10a3c407e, 0x0), (0x81e407e, 0xcc4424cc), (0xa1e407e, 0xcc442224cc), (0x10a1e407e, 0x0),
(0xc1e407e, 0x2211124e3cf), (0x14818807e, 0x0), (0x10858807e, 0xb2), (0x1481c807e, 0x7),
(0x1285c807e, 0x1a7), (0x14618847e, 0x3), (0x1461c847e, 0x7)]
def T407r6 : Records := #[T407r6p0]
def testT407r6 : ℕ → Bool := testAt T407 bsT407 5 T407r5 T407r6 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r6c0 : checkBlock testT407r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r6c1 : checkBlock testT407r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r6c2 : checkBlock testT407r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r6c3 : checkBlock testT407r6 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r6c4 : checkBlock testT407r6 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r6c5 : checkBlock testT407r6 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r6c6 : checkBlock testT407r6 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r6c7 : checkBlock testT407r6 3 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT407r6 : LayerOK T407 6 T407r6 := by
  apply layer_of_block (bs := bsT407) (k := 5) (old := T407r5) (cw := 3) (rw := 4) (by decide +kernel) vbsT407 vT407r5
  exact @block_merge testT407r6 0 31 1 (@block_merge testT407r6 0 16 15 (@block_merge testT407r6 0 8 8 (@block_merge testT407r6 0 4 4 T407r6c0 T407r6c1) (@block_merge testT407r6 8 4 4 T407r6c2 T407r6c3)) (@block_merge testT407r6 16 8 7 (@block_merge testT407r6 16 4 4 T407r6c4 T407r6c5) (@block_merge testT407r6 24 4 3 T407r6c6 T407r6c7))) (show checkBlock testT407r6 1 31 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T407r7p0 : RecordPage := #[
(0x8207e, 0x3333333333333bbbb33318961fbbbb3333319185eeeeee440c1cccc6a6aeeeaeeaaaa888), (0xa207e, 0xcccccccccccceeeecccc6060eeeecccc6060eeee4434bcccc6868eeee88888a8), (0x18407e, 0x3333331f77bb31b64b04910b3331976553458feeee8a8a4422), (0x1a407e, 0x3333330a5ee3432242cccc68d8bbbba2a288a12),
(0x1c407e, 0x333333129442244cccc69d93bbba12292a2a1422), (0x1e407e, 0xcccc442224cccccc2c58989af2b7bbbbb8ab8a828a2a2242), (0x18807e, 0xccccee6d6964056646cccceeee2cc8f8a8a6466), (0x1c807e, 0x33331b946c1199933333bbb8b724808a4a8a6466),
(0x18847e, 0xcc01f31b595d6626cccceeee8a8a4ed0f6266), (0x1c847e, 0xcc02733b9b927d998b3333bbba2a293d226266)]
def T407r7 : Records := #[T407r7p0]
def testT407r7 : ℕ → Bool := testAt T407 bsT407 6 T407r6 T407r7 3 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r7c0 : checkBlock testT407r7 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r7c1 : checkBlock testT407r7 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r7c2 : checkBlock testT407r7 2 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT407r7 : LayerOK T407 7 T407r7 := by
  apply layer_of_block (bs := bsT407) (k := 6) (old := T407r6) (cw := 3) (rw := 5) (by decide +kernel) vbsT407 vT407r6
  exact @block_merge testT407r7 0 10 22 (@block_merge testT407r7 0 4 6 T407r7c0 (@block_merge testT407r7 4 4 2 T407r7c1 T407r7c2)) (show checkBlock testT407r7 22 10 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T407r8p0 : RecordPage := #[
(0x7e, 0x3333333333333bbbb3331a6d1eeeecccc686aeeee88aacccc67b37bbb9693962a0741)]
def T407r8 : Records := #[T407r8p0]
def testT407r8 : ℕ → Bool := testAt T407 bsT407 7 T407r7 T407r8 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T407r8c0 : checkBlock testT407r8 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT407r8 : LayerOK T407 8 T407r8 := by
  apply layer_of_block (bs := bsT407) (k := 7) (old := T407r7) (cw := 3) (rw := 4) (by decide +kernel) vbsT407 vT407r7
  exact @block_merge testT407r8 0 1 31 T407r8c0 (show checkBlock testT407r8 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT407 : Valid T407 := by
  apply bound_of_layers (bs := bsT407) (last := T407r8) (cw := 3) (rw := 0) (by decide +kernel) vbsT407 vT407r8 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T408 : Bound := ⟨0x55005500550055005500550055005500550055005500550055005500550055, [0x0, 0x11001100110011001100110011001100110011001100110011001100110011, 0x5000500050005000500050005000500050005000500050005000500050005, 0x5500000055000000550000005500000055000000550000005500000055, 0x550055000000000055005500000000005500550000000000550055, 0x5500550055005500000000000000000055005500550055, 0x550055005500550055005500550055], 0x100000001000000010000000500000001000000110001000100110055, 9⟩
def bsT408 : Array Bound := [T377, T378, T386, T388, T390, T391, T394].toArray
theorem vbsT408 : ∀ s ∈ bsT408, Valid s := by
  intro s hs
  simp only [bsT408,List.mem_toArray] at hs
  exact (familyCons vT377 <| familyCons vT378 <| familyCons vT386 <| familyCons vT388 <| familyCons vT390 <| familyCons vT391 <| familyCons vT394 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T408r5p0 : RecordPage := #[
(0x4a1421a407e, 0x0)]
def T408r5 : Records := #[T408r5p0]
def testT408r5 : ℕ → Bool := testAt T408 bsT408 4 (#[] : Records) T408r5 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T408r5c0 : checkBlock testT408r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT408r5 : LayerOK T408 5 T408r5 := by
  apply layer_of_block (bs := bsT408) (k := 4) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT408 (emptyOK _ _)
  exact @block_merge testT408r5 0 1 31 T408r5c0 (show checkBlock testT408r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T408r6p0 : RecordPage := #[
(0x4a18407e, 0x0), (0xca18407e, 0xa), (0x1421a407e, 0x15), (0x81e407e, 0x2),
(0xa1e407e, 0x2), (0xc1e407e, 0x0)]
def T408r6 : Records := #[T408r6p0]
def testT408r6 : ℕ → Bool := testAt T408 bsT408 5 T408r5 T408r6 3 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T408r6c0 : checkBlock testT408r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T408r6c1 : checkBlock testT408r6 2 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT408r6 : LayerOK T408 6 T408r6 := by
  apply layer_of_block (bs := bsT408) (k := 5) (old := T408r5) (cw := 3) (rw := 0) (by decide +kernel) vbsT408 vT408r5
  exact @block_merge testT408r6 0 6 26 (@block_merge testT408r6 0 4 2 T408r6c0 T408r6c1) (show checkBlock testT408r6 26 6 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T408r7p0 : RecordPage := #[
(0x18407e, 0xaacc88aa02208888aaaa31aacccc46462200), (0x1a407e, 0xaacc00208888aaaacccc46460050), (0x1c407e, 0x88aa00228888aaaacccc46465200), (0x1e407e, 0x28888880baaaaaa09cccccc07464046060020)]
def T408r7 : Records := #[T408r7p0]
def testT408r7 : ℕ → Bool := testAt T408 bsT408 6 T408r6 T408r7 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T408r7c0 : checkBlock testT408r7 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT408r7 : LayerOK T408 7 T408r7 := by
  apply layer_of_block (bs := bsT408) (k := 6) (old := T408r6) (cw := 3) (rw := 3) (by decide +kernel) vbsT408 vT408r6
  exact @block_merge testT408r7 0 4 28 T408r7c0 (show checkBlock testT408r7 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T408r8p0 : RecordPage := #[
(0x7e, 0x88888888aaaa8888aaaacccc8888aaaacccc44668888aaaaccccf594646)]
def T408r8 : Records := #[T408r8p0]
def testT408r8 : ℕ → Bool := testAt T408 bsT408 7 T408r7 T408r8 3 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T408r8c0 : checkBlock testT408r8 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT408r8 : LayerOK T408 8 T408r8 := by
  apply layer_of_block (bs := bsT408) (k := 7) (old := T408r7) (cw := 3) (rw := 2) (by decide +kernel) vbsT408 vT408r7
  exact @block_merge testT408r8 0 1 31 T408r8c0 (show checkBlock testT408r8 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT408 : Valid T408 := by
  apply bound_of_layers (bs := bsT408) (last := T408r8) (cw := 3) (rw := 0) (by decide +kernel) vbsT408 vT408r8 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def T409 : Bound := ⟨0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, [0x0, 0x55005500550055005500550055005500550055005500550055005500550055, 0x33003300330033003300330033003300330033003300330033003300330033, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f, 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff, 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff, 0xff00ff00ff00ff00ff00ff00ff00ff], 0x1000000010000000100000005000000010000001100010001001100ff, 11⟩
def bsT409 : Array Bound := [T401, T402, T403, T404, T405, T406, T407, T408].toArray
theorem vbsT409 : ∀ s ∈ bsT409, Valid s := by
  intro s hs
  simp only [bsT409,List.mem_toArray] at hs
  exact (familyCons vT401 <| familyCons vT402 <| familyCons vT403 <| familyCons vT404 <| familyCons vT405 <| familyCons vT406 <| familyCons vT407 <| familyCons vT408 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T409r7p0 : RecordPage := #[
(0x10634e1864fe, 0x8), (0x18c04a1a64fe, 0x62), (0x1cc04a1a64fe, 0x0), (0xe410e5a64fe, 0x0),
(0x4618a18c6fe, 0x8)]
def T409r7 : Records := #[T409r7p0]
def testT409r7 : ℕ → Bool := testAt T409 bsT409 6 (#[] : Records) T409r7 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T409r7c0 : checkBlock testT409r7 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T409r7c1 : checkBlock testT409r7 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT409r7 : LayerOK T409 7 T409r7 := by
  apply layer_of_block (bs := bsT409) (k := 6) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT409 (emptyOK _ _)
  exact @block_merge testT409r7 0 5 27 (@block_merge testT409r7 0 4 1 T409r7c0 T409r7c1) (show checkBlock testT409r7 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T409r8p0 : RecordPage := #[
(0x14e1864fe, 0xceee88aaee41468888aaaacccceeee4446444642), (0x10e5864fe, 0xce88aacceeee6088ccee444442aa66264444640), (0x18e5864fe, 0x41600624464), (0x14e5864fe, 0xce88aacceeee60aa4444aa66602040),
(0x4a1a64fe, 0x8888cccc8888eeee8888ccccce40408888cccceeee46468888cccceeeeee66a645438888cccceeeeaa6aaaa6), (0x14e1a64fe, 0xceee6088ccee40468888aaaacccceeee4464444640), (0x10e5a64fe, 0xceeea0ee6088ccee44aa660740), (0x14a18c4fe, 0xceee44668888aaaacccceeee4444644422),
(0x18a18c6fe, 0x62196), (0x1ca18c6fe, 0x262446)]
def T409r8 : Records := #[T409r8p0]
def testT409r8 : ℕ → Bool := testAt T409 bsT409 7 T409r7 T409r8 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T409r8c0 : checkBlock testT409r8 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T409r8c1 : checkBlock testT409r8 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T409r8c2 : checkBlock testT409r8 2 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT409r8 : LayerOK T409 8 T409r8 := by
  apply layer_of_block (bs := bsT409) (k := 7) (old := T409r7) (cw := 3) (rw := 3) (by decide +kernel) vbsT409 vT409r7
  exact @block_merge testT409r8 0 10 22 (@block_merge testT409r8 0 4 6 T409r8c0 (@block_merge testT409r8 4 4 2 T409r8c1 T409r8c2)) (show checkBlock testT409r8 22 10 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T409r9p0 : RecordPage := #[
(0x1864fe, 0x8888aaaa8888cccc8888aaaaeeee8888aaaaccccce403a14711115555559999dddc8cc8c5111111555555999999dddddccccccc08841442288888888aaaaaaaacccccccceeeeeeee666660), (0x1a64fe, 0x44445555444466664444555577774444555566666720020362222aaaaab3333bbb9191a2222aaab3333bbbbb99999981101688011111111155555409aaaacccccccceeeeeeee666660), (0x18c4fe, 0x111111111555511115555999911115555dddd99999d111155555488899999dddd11115554ccccc59999dddddc8888c891111111155555554404f2022cccccccceeeeeeee446444), (0x18c6fe, 0x111111111555511115555999911115555dddddd99999d11111155548889999999dddddd11115554c0d628f3333bbbbb9111011222222222aaaaaaa99a64cd12cccccccceeeeeeee440444),
(0x1cc6fe, 0x111111111555511115555999911115555dddddd99999d111155555488899999dddd11115554c00c07cccceeeeee444444088888888aaaaaaaa66026600cccccccceeeeeeee440444)]
def T409r9 : Records := #[T409r9p0]
def testT409r9 : ℕ → Bool := testAt T409 bsT409 8 T409r8 T409r9 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T409r9c0 : checkBlock testT409r9 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T409r9c1 : checkBlock testT409r9 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT409r9 : LayerOK T409 9 T409r9 := by
  apply layer_of_block (bs := bsT409) (k := 8) (old := T409r8) (cw := 3) (rw := 4) (by decide +kernel) vbsT409 vT409r8
  exact @block_merge testT409r9 0 5 27 (@block_merge testT409r9 0 4 1 T409r9c0 T409r9c1) (show checkBlock testT409r9 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T409r10p0 : RecordPage := #[
(0xfe, 0x8888aaaa888849478888aaaa46458888aaaa6631cccc8888aaaacccccccceeee8888aaaaeeeeeeeeeeccccce)]
def T409r10 : Records := #[T409r10p0]
def testT409r10 : ℕ → Bool := testAt T409 bsT409 9 T409r9 T409r10 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T409r10c0 : checkBlock testT409r10 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT409r10 : LayerOK T409 10 T409r10 := by
  apply layer_of_block (bs := bsT409) (k := 9) (old := T409r9) (cw := 3) (rw := 3) (by decide +kernel) vbsT409 vT409r9
  exact @block_merge testT409r10 0 1 31 T409r10c0 (show checkBlock testT409r10 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT409 : Valid T409 := by
  apply bound_of_layers (bs := bsT409) (last := T409r10) (cw := 3) (rw := 0) (by decide +kernel) vbsT409 vT409r10 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
def rootT : Bound := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, [0x0, 0x5555555555555555555555555555555555555555555555555555555555555555, 0x3333333333333333333333333333333333333333333333333333333333333333, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 0xffffffffffffffff0000000000000000ffffffffffffffff, 0xffffffffffffffffffffffffffffffff], 0x10000000100000001000000050000010100001111010101011111ffff, 12⟩
def bsrootT : Array Bound := [T409].toArray
theorem vbsrootT : ∀ s ∈ bsrootT, Valid s := by
  intro s hs
  simp only [bsrootT,List.mem_toArray] at hs
  exact (familyCons vT409 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootT : Valid rootT := by
  apply bound_of_layers (bs := bsrootT) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsrootT (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_15010.SignedCert.GraphT
open PEqualNP.CircuitLowerBounds
def columns : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def funValue (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def network : List Gate := [
  ⟨.or, [0,4]⟩,
  ⟨.or, [6,7]⟩,
  ⟨.and, [8,9]⟩,
  ⟨.or, [0,1]⟩,
  ⟨.or, [4,6]⟩,
  ⟨.or, [5,12]⟩,
  ⟨.and, [11,13]⟩,
  ⟨.and, [2,5]⟩,
  ⟨.or, [14,15]⟩,
  ⟨.or, [10,16]⟩,
  ⟨.or, [2,3]⟩,
  ⟨.and, [7,18]⟩,
  ⟨.or, [17,19]⟩]

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
  apply Source.binary_lb vrootT 0xfffffffefffffffefffffffefffffffafffffefeffffeeeefefefefeeeee0000 columns funValue (by decide +kernel) (by decide +kernel) (by rfl) _ (by decide +kernel) _ gs o legal correct
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_meta_15010.SignedCert.GraphT

theorem PEqualNP.Outside.L_meta_15010 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_15010.SignedCert.Source.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_15010.SignedCert.Source.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_15010.SignedCert.Source.isBinary, op]⟩
    have hb := PEqualNP.Outside.L_meta_15010.SignedCert.GraphT.lower gates o (fun g hg => fits g hg) computes
    have hl : PEqualNP.Outside.L_meta_15010.SignedCert.GraphT.network.length = 13 := rfl
    exact ⟨PEqualNP.Outside.L_meta_15010.SignedCert.GraphT.network, 20, PEqualNP.Outside.L_meta_15010.SignedCert.GraphT.legal_network, by omega, PEqualNP.Outside.L_meta_15010.SignedCert.GraphT.correct_network⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g,hg,h⟩).elim
