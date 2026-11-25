import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16673.SignedCert
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

abbrev W := BitVec 64

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

end PEqualNP.Outside.L_meta_16673.SignedCert

namespace PEqualNP.Outside.L_meta_16673.SignedCert

theorem norm_zero (m : W) : norm m 0 = 0 := by
  change norm m (0#64) = 0#64
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

end PEqualNP.Outside.L_meta_16673.SignedCert

namespace PEqualNP.Outside.L_meta_16673.SignedCert

abbrev Recipe := W × W × W
abbrev Bound := W × List W × W × ℕ

abbrev Bound.mask (b : Bound) : W := b.1
abbrev Bound.inputs (b : Bound) : List W := b.2.1
abbrev Bound.goal (b : Bound) : W := b.2.2.1
abbrev Bound.cost (b : Bound) : ℕ := b.2.2.2

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

end PEqualNP.Outside.L_meta_16673.SignedCert

namespace PEqualNP.Outside.L_meta_16673.SignedCert

def sep : List W → W → W → Bool
  | [], p, n => p == 0 || n == 0
  | x::r, p, n => (p == 0 || n == 0) ||
    (sep r (p &&& x) (n &&& x) && sep r (p &&& ~~~x) (n &&& ~~~x))

theorem some_bit {x : W} (hn : x ≠ 0) : ∃ i : Fin 64, x[i.val] = true := by
  by_contra! h
  apply hn
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simpa using h ⟨i,hi⟩

theorem sep_ok {ws : List W} {p n : W}
    (h : ∀ i j : Fin 64, p[i.val] = true → n[j.val] = true → ∃ w ∈ ws, w[i.val] ≠ w[j.val]) :
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

theorem op_agree {m a b z : W} {i j : Fin 64} (hm : m[i.val] = m[j.val])
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

end PEqualNP.Outside.L_meta_16673.SignedCert

namespace PEqualNP.Outside.L_meta_16673.SignedCert
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

end PEqualNP.Outside.L_meta_16673.SignedCert

namespace PEqualNP.Outside.L_meta_16673.SignedCert.Source
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
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
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

def bit (k : Fin 64) (z : W) : Bool := z[k.val]
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
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
    norm m z ∈ PEqualNP.Outside.L_meta_16673.SignedCert.ops m (norm m a) (norm m b) := by
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
    build (PEqualNP.Outside.L_meta_16673.SignedCert.ops m) (norm m t) k (bank m S) := by
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

theorem binary_lb {b : Bound} (valid : Valid b) (w : W) (raw : List W) (F : (Fin 6 → Bool) → Bool)
    (nz : w ≠ 0) (no : w ≠ ~~~0) (dim : raw.length = 6)
    (stk : bank b.mask raw.toFinset ⊆ b.inputs.toFinset) (tg : norm b.mask w = b.goal)
    (rows : ∀ k : Fin 64, F (fun i => bit k (raw.getD i.val 0)) = bit k w)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (evals : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : b.cost ≤ binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ raw, holds raw.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have eval (k : Fin 64) :
      (gs.foldl step (raw.map (bit k))).getD o false = bit k (~~~(~~~w)) := by
    let x (i : Fin 6) := bit k (raw.getD i.val 0)
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

end PEqualNP.Outside.L_meta_16673.SignedCert.Source

namespace PEqualNP.Outside.L_meta_16673.SignedCert
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
  let i := t % 64
  let j := t / 64 % 64
  (m.getLsbD i == m.getLsbD j) && (g.getLsbD i != g.getLsbD j) &&
    ws.all (fun x => x.getLsbD i == x.getLsbD j)

theorem clash_sound {m g : W} {ws : List W} {t k : ℕ}
    (yes : clash m g ws t = true) : Closed m g (k,ws) := by
  intro _ _ run
  let i : Fin 64 := ⟨t%64,Nat.mod_lt _ (by decide)⟩
  let j : Fin 64 := ⟨t/64%64,Nat.mod_lt _ (by decide)⟩
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

end PEqualNP.Outside.L_meta_16673.SignedCert

namespace PEqualNP.Outside.L_meta_16673.SignedCert

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

end PEqualNP.Outside.L_meta_16673.SignedCert

namespace PEqualNP.Outside.L_meta_16673.SignedCert

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

end PEqualNP.Outside.L_meta_16673.SignedCert

namespace PEqualNP.Outside.L_meta_16673.SignedCert

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

end PEqualNP.Outside.L_meta_16673.SignedCert

namespace PEqualNP.Outside.L_meta_16673.SignedCert

def evalWord {α : Type} (w : W) (f : W → α) : α :=
  Nat.rec (f 0) (fun j _ => f (BitVec.ofNat 64 (j+1))) w.toNat

theorem evalWord_eq {α : Type} (w : W) (f : W → α) : evalWord w f = f w := by
  unfold evalWord
  generalize h : w.toNat = t
  cases t with
  | zero =>
    change f 0 = f w
    apply congrArg f
    exact BitVec.eq_of_toNat_eq (by simpa using h.symm)
  | succ t =>
    change f (BitVec.ofNat 64 (t+1)) = f w
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
end PEqualNP.Outside.L_meta_16673.SignedCert

namespace PEqualNP.Outside.L_meta_16673.SignedCert

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
end PEqualNP.Outside.L_meta_16673.SignedCert

namespace PEqualNP.Outside.L_meta_16673.SignedCert

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
  Nat.rec (f 0) (fun j _ => f (BitVec.ofNat 64 (j+1))) w.toNat

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
  replayTail b.mask (b.cost-1-k) (p >>> 8) (initialWords b.inputs (p % 256),[])

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

end PEqualNP.Outside.L_meta_16673.SignedCert

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T64 : Bound := ⟨0xff0, [0x0, 0x550, 0x330, 0xf0], 0x530, 3⟩
def bsT64 : Array Bound := [].toArray
theorem vbsT64 : ∀ s ∈ bsT64, Valid s := by
  intro s hs
  simp only [bsT64,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T64r2p0 : RecordPage := #[
(0xe, 0x0)]
def T64r2 : Records := #[T64r2p0]
def testT64r2 : ℕ → Bool := testAt T64 bsT64 1 (#[] : Records) T64r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T64r2c0 : checkBlock testT64r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT64r2 : LayerOK T64 2 T64r2 := by
  apply layer_of_block (bs := bsT64) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT64 (emptyOK _ _)
  exact @block_merge testT64r2 0 1 31 T64r2c0 (show checkBlock testT64r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT64 : Valid T64 := by
  apply bound_of_layers (bs := bsT64) (last := T64r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT64 vT64r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T66 : Bound := ⟨0x5a5a, [0x0, 0xa0a, 0x1212, 0x5a], 0x101a, 3⟩
def bsT66 : Array Bound := [].toArray
theorem vbsT66 : ∀ s ∈ bsT66, Valid s := by
  intro s hs
  simp only [bsT66,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T66r2p0 : RecordPage := #[
(0xe, 0x0)]
def T66r2 : Records := #[T66r2p0]
def testT66r2 : ℕ → Bool := testAt T66 bsT66 1 (#[] : Records) T66r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T66r2c0 : checkBlock testT66r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT66r2 : LayerOK T66 2 T66r2 := by
  apply layer_of_block (bs := bsT66) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT66 (emptyOK _ _)
  exact @block_merge testT66r2 0 1 31 T66r2c0 (show checkBlock testT66r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT66 : Valid T66 := by
  apply bound_of_layers (bs := bsT66) (last := T66r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT66 vT66r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T67 : Bound := ⟨0x6666, [0x0, 0x2222, 0x606, 0x66], 0x426, 3⟩
def bsT67 : Array Bound := [].toArray
theorem vbsT67 : ∀ s ∈ bsT67, Valid s := by
  intro s hs
  simp only [bsT67,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T67r2p0 : RecordPage := #[
(0xe, 0x0)]
def T67r2 : Records := #[T67r2p0]
def testT67r2 : ℕ → Bool := testAt T67 bsT67 1 (#[] : Records) T67r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T67r2c0 : checkBlock testT67r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT67r2 : LayerOK T67 2 T67r2 := by
  apply layer_of_block (bs := bsT67) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT67 (emptyOK _ _)
  exact @block_merge testT67r2 0 1 31 T67r2c0 (show checkBlock testT67r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT67 : Valid T67 := by
  apply bound_of_layers (bs := bsT67) (last := T67r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT67 vT67r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T68 : Bound := ⟨0xf00f0, [0x0, 0x50050, 0x30030, 0xf0], 0x50030, 3⟩
def bsT68 : Array Bound := [].toArray
theorem vbsT68 : ∀ s ∈ bsT68, Valid s := by
  intro s hs
  simp only [bsT68,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T68r2p0 : RecordPage := #[
(0xe, 0x0)]
def T68r2 : Records := #[T68r2p0]
def testT68r2 : ℕ → Bool := testAt T68 bsT68 1 (#[] : Records) T68r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T68r2c0 : checkBlock testT68r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT68r2 : LayerOK T68 2 T68r2 := by
  apply layer_of_block (bs := bsT68) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT68 (emptyOK _ _)
  exact @block_merge testT68r2 0 1 31 T68r2c0 (show checkBlock testT68r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT68 : Valid T68 := by
  apply bound_of_layers (bs := bsT68) (last := T68r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT68 vT68r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T70 : Bound := ⟨0x5a005a, [0x0, 0xa000a, 0x120012, 0x5a], 0x10001a, 3⟩
def bsT70 : Array Bound := [].toArray
theorem vbsT70 : ∀ s ∈ bsT70, Valid s := by
  intro s hs
  simp only [bsT70,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T70r2p0 : RecordPage := #[
(0xe, 0x0)]
def T70r2 : Records := #[T70r2p0]
def testT70r2 : ℕ → Bool := testAt T70 bsT70 1 (#[] : Records) T70r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T70r2c0 : checkBlock testT70r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT70r2 : LayerOK T70 2 T70r2 := by
  apply layer_of_block (bs := bsT70) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT70 (emptyOK _ _)
  exact @block_merge testT70r2 0 1 31 T70r2c0 (show checkBlock testT70r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT70 : Valid T70 := by
  apply bound_of_layers (bs := bsT70) (last := T70r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT70 vT70r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T71 : Bound := ⟨0x660066, [0x0, 0x220022, 0x60006, 0x66], 0x40026, 3⟩
def bsT71 : Array Bound := [].toArray
theorem vbsT71 : ∀ s ∈ bsT71, Valid s := by
  intro s hs
  simp only [bsT71,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T71r2p0 : RecordPage := #[
(0xe, 0x0)]
def T71r2 : Records := #[T71r2p0]
def testT71r2 : ℕ → Bool := testAt T71 bsT71 1 (#[] : Records) T71r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T71r2c0 : checkBlock testT71r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT71r2 : LayerOK T71 2 T71r2 := by
  apply layer_of_block (bs := bsT71) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT71 (emptyOK _ _)
  exact @block_merge testT71r2 0 1 31 T71r2c0 (show checkBlock testT71r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT71 : Valid T71 := by
  apply bound_of_layers (bs := bsT71) (last := T71r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT71 vT71r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T74 : Bound := ⟨0x3c3c00000000, [0x0, 0x141400000000, 0xc0c00000000, 0x3c00000000], 0x101c00000000, 3⟩
def bsT74 : Array Bound := [].toArray
theorem vbsT74 : ∀ s ∈ bsT74, Valid s := by
  intro s hs
  simp only [bsT74,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T74r2p0 : RecordPage := #[
(0xe, 0x0)]
def T74r2 : Records := #[T74r2p0]
def testT74r2 : ℕ → Bool := testAt T74 bsT74 1 (#[] : Records) T74r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T74r2c0 : checkBlock testT74r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT74r2 : LayerOK T74 2 T74r2 := by
  apply layer_of_block (bs := bsT74) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT74 (emptyOK _ _)
  exact @block_merge testT74r2 0 1 31 T74r2c0 (show checkBlock testT74r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT74 : Valid T74 := by
  apply bound_of_layers (bs := bsT74) (last := T74r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT74 vT74r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T76 : Bound := ⟨0x55aa00000000, [0x0, 0xaa00000000, 0x112200000000, 0x50a00000000], 0x110a00000000, 3⟩
def bsT76 : Array Bound := [].toArray
theorem vbsT76 : ∀ s ∈ bsT76, Valid s := by
  intro s hs
  simp only [bsT76,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T76r2p0 : RecordPage := #[
(0xe, 0x0)]
def T76r2 : Records := #[T76r2p0]
def testT76r2 : ℕ → Bool := testAt T76 bsT76 1 (#[] : Records) T76r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T76r2c0 : checkBlock testT76r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT76r2 : LayerOK T76 2 T76r2 := by
  apply layer_of_block (bs := bsT76) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT76 (emptyOK _ _)
  exact @block_merge testT76r2 0 1 31 T76r2c0 (show checkBlock testT76r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT76 : Valid T76 := by
  apply bound_of_layers (bs := bsT76) (last := T76r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT76 vT76r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T77 : Bound := ⟨0x5a5a00000000, [0x0, 0xa0a00000000, 0x121200000000, 0x5a00000000], 0x101a00000000, 3⟩
def bsT77 : Array Bound := [].toArray
theorem vbsT77 : ∀ s ∈ bsT77, Valid s := by
  intro s hs
  simp only [bsT77,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T77r2p0 : RecordPage := #[
(0xe, 0x0)]
def T77r2 : Records := #[T77r2p0]
def testT77r2 : ℕ → Bool := testAt T77 bsT77 1 (#[] : Records) T77r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T77r2c0 : checkBlock testT77r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT77r2 : LayerOK T77 2 T77r2 := by
  apply layer_of_block (bs := bsT77) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT77 (emptyOK _ _)
  exact @block_merge testT77r2 0 1 31 T77r2c0 (show checkBlock testT77r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT77 : Valid T77 := by
  apply bound_of_layers (bs := bsT77) (last := T77r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT77 vT77r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T78 : Bound := ⟨0x3300cc00000000, [0x0, 0x11004400000000, 0xcc00000000, 0x3000c00000000], 0x11000c00000000, 3⟩
def bsT78 : Array Bound := [].toArray
theorem vbsT78 : ∀ s ∈ bsT78, Valid s := by
  intro s hs
  simp only [bsT78,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T78r2p0 : RecordPage := #[
(0xe, 0x0)]
def T78r2 : Records := #[T78r2p0]
def testT78r2 : ℕ → Bool := testAt T78 bsT78 1 (#[] : Records) T78r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T78r2c0 : checkBlock testT78r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT78r2 : LayerOK T78 2 T78r2 := by
  apply layer_of_block (bs := bsT78) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT78 (emptyOK _ _)
  exact @block_merge testT78r2 0 1 31 T78r2c0 (show checkBlock testT78r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT78 : Valid T78 := by
  apply bound_of_layers (bs := bsT78) (last := T78r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT78 vT78r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T79 : Bound := ⟨0x5a005a00000000, [0x0, 0xa000a00000000, 0x12001200000000, 0x5a00000000], 0x10001a00000000, 3⟩
def bsT79 : Array Bound := [].toArray
theorem vbsT79 : ∀ s ∈ bsT79, Valid s := by
  intro s hs
  simp only [bsT79,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T79r2p0 : RecordPage := #[
(0xe, 0x0)]
def T79r2 : Records := #[T79r2p0]
def testT79r2 : ℕ → Bool := testAt T79 bsT79 1 (#[] : Records) T79r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T79r2c0 : checkBlock testT79r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT79r2 : LayerOK T79 2 T79r2 := by
  apply layer_of_block (bs := bsT79) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT79 (emptyOK _ _)
  exact @block_merge testT79r2 0 1 31 T79r2c0 (show checkBlock testT79r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT79 : Valid T79 := by
  apply bound_of_layers (bs := bsT79) (last := T79r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT79 vT79r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T80 : Bound := ⟨0x3030c0c00000000, [0x0, 0x101040400000000, 0xc0c00000000, 0x3000c00000000], 0x101000c00000000, 3⟩
def bsT80 : Array Bound := [].toArray
theorem vbsT80 : ∀ s ∈ bsT80, Valid s := by
  intro s hs
  simp only [bsT80,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T80r2p0 : RecordPage := #[
(0xe, 0x0)]
def T80r2 : Records := #[T80r2p0]
def testT80r2 : ℕ → Bool := testAt T80 bsT80 1 (#[] : Records) T80r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T80r2c0 : checkBlock testT80r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT80r2 : LayerOK T80 2 T80r2 := by
  apply layer_of_block (bs := bsT80) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT80 (emptyOK _ _)
  exact @block_merge testT80r2 0 1 31 T80r2c0 (show checkBlock testT80r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT80 : Valid T80 := by
  apply bound_of_layers (bs := bsT80) (last := T80r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT80 vT80r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T81 : Bound := ⟨0x408040804080408, [0x0, 0x8000800080008, 0x40800000408, 0x4080408], 0x804000408, 3⟩
def bsT81 : Array Bound := [].toArray
theorem vbsT81 : ∀ s ∈ bsT81, Valid s := by
  intro s hs
  simp only [bsT81,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T81r2p0 : RecordPage := #[
(0xe, 0x0)]
def T81r2 : Records := #[T81r2p0]
def testT81r2 : ℕ → Bool := testAt T81 bsT81 1 (#[] : Records) T81r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T81r2c0 : checkBlock testT81r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT81r2 : LayerOK T81 2 T81r2 := by
  apply layer_of_block (bs := bsT81) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT81 (emptyOK _ _)
  exact @block_merge testT81r2 0 1 31 T81r2c0 (show checkBlock testT81r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT81 : Valid T81 := by
  apply bound_of_layers (bs := bsT81) (last := T81r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT81 vT81r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T82 : Bound := ⟨0x50a050a00000000, [0x0, 0xa000a00000000, 0x102010200000000, 0x50a00000000], 0x100010a00000000, 3⟩
def bsT82 : Array Bound := [].toArray
theorem vbsT82 : ∀ s ∈ bsT82, Valid s := by
  intro s hs
  simp only [bsT82,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T82r2p0 : RecordPage := #[
(0xe, 0x0)]
def T82r2 : Records := #[T82r2p0]
def testT82r2 : ℕ → Bool := testAt T82 bsT82 1 (#[] : Records) T82r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T82r2c0 : checkBlock testT82r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT82r2 : LayerOK T82 2 T82r2 := by
  apply layer_of_block (bs := bsT82) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT82 (emptyOK _ _)
  exact @block_merge testT82r2 0 1 31 T82r2c0 (show checkBlock testT82r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT82 : Valid T82 := by
  apply bound_of_layers (bs := bsT82) (last := T82r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT82 vT82r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T83 : Bound := ⟨0x1400140014001400, [0x0, 0x400040004000400, 0x140000001400, 0x14001400], 0x100004001400, 3⟩
def bsT83 : Array Bound := [].toArray
theorem vbsT83 : ∀ s ∈ bsT83, Valid s := by
  intro s hs
  simp only [bsT83,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T83r2p0 : RecordPage := #[
(0xe, 0x0)]
def T83r2 : Records := #[T83r2p0]
def testT83r2 : ℕ → Bool := testAt T83 bsT83 1 (#[] : Records) T83r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T83r2c0 : checkBlock testT83r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT83r2 : LayerOK T83 2 T83r2 := by
  apply layer_of_block (bs := bsT83) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT83 (emptyOK _ _)
  exact @block_merge testT83r2 0 1 31 T83r2c0 (show checkBlock testT83r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT83 : Valid T83 := by
  apply bound_of_layers (bs := bsT83) (last := T83r2) (cw := 1) (rw := 0) (by decide +kernel) vbsT83 vT83r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T84 : Bound := ⟨0x12121212, [0x0, 0x2020202, 0x120012, 0x1212], 0x101012, 4⟩
def bsT84 : Array Bound := [].toArray
theorem vbsT84 : ∀ s ∈ bsT84, Valid s := by
  intro s hs
  simp only [bsT84,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T84r3p0 : RecordPage := #[
(0xe, 0x0)]
def T84r3 : Records := #[T84r3p0]
def testT84r3 : ℕ → Bool := testAt T84 bsT84 2 (#[] : Records) T84r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T84r3c0 : checkBlock testT84r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT84r3 : LayerOK T84 3 T84r3 := by
  apply layer_of_block (bs := bsT84) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT84 (emptyOK _ _)
  exact @block_merge testT84r3 0 1 31 T84r3c0 (show checkBlock testT84r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT84 : Valid T84 := by
  apply bound_of_layers (bs := bsT84) (last := T84r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT84 vT84r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T85 : Bound := ⟨0x30033003, [0x0, 0x10011001, 0x30003, 0x3003], 0x11003, 4⟩
def bsT85 : Array Bound := [].toArray
theorem vbsT85 : ∀ s ∈ bsT85, Valid s := by
  intro s hs
  simp only [bsT85,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T85r3p0 : RecordPage := #[
(0xe, 0x0)]
def T85r3 : Records := #[T85r3p0]
def testT85r3 : ℕ → Bool := testAt T85 bsT85 2 (#[] : Records) T85r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T85r3c0 : checkBlock testT85r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT85r3 : LayerOK T85 3 T85r3 := by
  apply layer_of_block (bs := bsT85) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT85 (emptyOK _ _)
  exact @block_merge testT85r3 0 1 31 T85r3c0 (show checkBlock testT85r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT85 : Valid T85 := by
  apply bound_of_layers (bs := bsT85) (last := T85r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT85 vT85r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T86 : Bound := ⟨0x30300303, [0x0, 0x10100101, 0x303, 0x300003], 0x100103, 4⟩
def bsT86 : Array Bound := [].toArray
theorem vbsT86 : ∀ s ∈ bsT86, Valid s := by
  intro s hs
  simp only [bsT86,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T86r3p0 : RecordPage := #[
(0xe, 0x0)]
def T86r3 : Records := #[T86r3p0]
def testT86r3 : ℕ → Bool := testAt T86 bsT86 2 (#[] : Records) T86r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T86r3c0 : checkBlock testT86r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT86r3 : LayerOK T86 3 T86r3 := by
  apply layer_of_block (bs := bsT86) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT86 (emptyOK _ _)
  exact @block_merge testT86r3 0 1 31 T86r3c0 (show checkBlock testT86r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT86 : Valid T86 := by
  apply bound_of_layers (bs := bsT86) (last := T86r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT86 vT86r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T87 : Bound := ⟨0x30303030, [0x0, 0x10101010, 0x300030, 0x3030], 0x101030, 4⟩
def bsT87 : Array Bound := [].toArray
theorem vbsT87 : ∀ s ∈ bsT87, Valid s := by
  intro s hs
  simp only [bsT87,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T87r3p0 : RecordPage := #[
(0xe, 0x0)]
def T87r3 : Records := #[T87r3p0]
def testT87r3 : ℕ → Bool := testAt T87 bsT87 2 (#[] : Records) T87r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T87r3c0 : checkBlock testT87r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT87r3 : LayerOK T87 3 T87r3 := by
  apply layer_of_block (bs := bsT87) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT87 (emptyOK _ _)
  exact @block_merge testT87r3 0 1 31 T87r3c0 (show checkBlock testT87r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT87 : Valid T87 := by
  apply bound_of_layers (bs := bsT87) (last := T87r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT87 vT87r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T88 : Bound := ⟨0xcc003300000000, [0x0, 0x44001100000000, 0x3300000000, 0xc000300000000], 0x4001300000000, 4⟩
def bsT88 : Array Bound := [].toArray
theorem vbsT88 : ∀ s ∈ bsT88, Valid s := by
  intro s hs
  simp only [bsT88,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T88r3p0 : RecordPage := #[
(0xe, 0x0)]
def T88r3 : Records := #[T88r3p0]
def testT88r3 : ℕ → Bool := testAt T88 bsT88 2 (#[] : Records) T88r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T88r3c0 : checkBlock testT88r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT88r3 : LayerOK T88 3 T88r3 := by
  apply layer_of_block (bs := bsT88) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT88 (emptyOK _ _)
  exact @block_merge testT88r3 0 1 31 T88r3c0 (show checkBlock testT88r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT88 : Valid T88 := by
  apply bound_of_layers (bs := bsT88) (last := T88r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT88 vT88r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T89 : Bound := ⟨0x505000050500000, [0x0, 0x101000010100000, 0x50500000, 0x5000000500000], 0x105000000100000, 4⟩
def bsT89 : Array Bound := [].toArray
theorem vbsT89 : ∀ s ∈ bsT89, Valid s := by
  intro s hs
  simp only [bsT89,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T89r3p0 : RecordPage := #[
(0xe, 0x0)]
def T89r3 : Records := #[T89r3p0]
def testT89r3 : ℕ → Bool := testAt T89 bsT89 2 (#[] : Records) T89r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T89r3c0 : checkBlock testT89r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT89r3 : LayerOK T89 3 T89r3 := by
  apply layer_of_block (bs := bsT89) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT89 (emptyOK _ _)
  exact @block_merge testT89r3 0 1 31 T89r3c0 (show checkBlock testT89r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT89 : Valid T89 := by
  apply bound_of_layers (bs := bsT89) (last := T89r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT89 vT89r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T90 : Bound := ⟨0xc0c000000000c0c, [0x0, 0x404000000000404, 0xc00000000000c, 0xc0c], 0x400000000040c, 4⟩
def bsT90 : Array Bound := [].toArray
theorem vbsT90 : ∀ s ∈ bsT90, Valid s := by
  intro s hs
  simp only [bsT90,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T90r3p0 : RecordPage := #[
(0xe, 0x0)]
def T90r3 : Records := #[T90r3p0]
def testT90r3 : ℕ → Bool := testAt T90 bsT90 2 (#[] : Records) T90r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T90r3c0 : checkBlock testT90r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT90r3 : LayerOK T90 3 T90r3 := by
  apply layer_of_block (bs := bsT90) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT90 (emptyOK _ _)
  exact @block_merge testT90r3 0 1 31 T90r3c0 (show checkBlock testT90r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT90 : Valid T90 := by
  apply bound_of_layers (bs := bsT90) (last := T90r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT90 vT90r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T91 : Bound := ⟨0xc0c030300000000, [0x0, 0x404010100000000, 0x30300000000, 0xc000300000000], 0x4010300000000, 4⟩
def bsT91 : Array Bound := [].toArray
theorem vbsT91 : ∀ s ∈ bsT91, Valid s := by
  intro s hs
  simp only [bsT91,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T91r3p0 : RecordPage := #[
(0xe, 0x0)]
def T91r3 : Records := #[T91r3p0]
def testT91r3 : ℕ → Bool := testAt T91 bsT91 2 (#[] : Records) T91r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T91r3c0 : checkBlock testT91r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT91r3 : LayerOK T91 3 T91r3 := by
  apply layer_of_block (bs := bsT91) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT91 (emptyOK _ _)
  exact @block_merge testT91r3 0 1 31 T91r3c0 (show checkBlock testT91r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT91 : Valid T91 := by
  apply bound_of_layers (bs := bsT91) (last := T91r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT91 vT91r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T92 : Bound := ⟨0x1010101020202020, [0x0, 0x20202020, 0x10001000200020, 0x101000002020], 0x10101000000020, 4⟩
def bsT92 : Array Bound := [].toArray
theorem vbsT92 : ∀ s ∈ bsT92, Valid s := by
  intro s hs
  simp only [bsT92,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T92r3p0 : RecordPage := #[
(0xe, 0x0)]
def T92r3 : Records := #[T92r3p0]
def testT92r3 : ℕ → Bool := testAt T92 bsT92 2 (#[] : Records) T92r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T92r3c0 : checkBlock testT92r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT92r3 : LayerOK T92 3 T92r3 := by
  apply layer_of_block (bs := bsT92) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT92 (emptyOK _ _)
  exact @block_merge testT92r3 0 1 31 T92r3c0 (show checkBlock testT92r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT92 : Valid T92 := by
  apply bound_of_layers (bs := bsT92) (last := T92r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT92 vT92r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T93 : Bound := ⟨0x1111222200000000, [0x0, 0x222200000000, 0x101020200000000, 0x11002200000000], 0x111000200000000, 4⟩
def bsT93 : Array Bound := [].toArray
theorem vbsT93 : ∀ s ∈ bsT93, Valid s := by
  intro s hs
  simp only [bsT93,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T93r3p0 : RecordPage := #[
(0xe, 0x0)]
def T93r3 : Records := #[T93r3p0]
def testT93r3 : ℕ → Bool := testAt T93 bsT93 2 (#[] : Records) T93r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T93r3c0 : checkBlock testT93r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT93r3 : LayerOK T93 3 T93r3 := by
  apply layer_of_block (bs := bsT93) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT93 (emptyOK _ _)
  exact @block_merge testT93r3 0 1 31 T93r3c0 (show checkBlock testT93r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT93 : Valid T93 := by
  apply bound_of_layers (bs := bsT93) (last := T93r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT93 vT93r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T94 : Bound := ⟨0x1111444400000000, [0x0, 0x444400000000, 0x101040400000000, 0x11004400000000], 0x111000400000000, 4⟩
def bsT94 : Array Bound := [].toArray
theorem vbsT94 : ∀ s ∈ bsT94, Valid s := by
  intro s hs
  simp only [bsT94,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T94r3p0 : RecordPage := #[
(0xe, 0x0)]
def T94r3 : Records := #[T94r3p0]
def testT94r3 : ℕ → Bool := testAt T94 bsT94 2 (#[] : Records) T94r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T94r3c0 : checkBlock testT94r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT94r3 : LayerOK T94 3 T94r3 := by
  apply layer_of_block (bs := bsT94) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT94 (emptyOK _ _)
  exact @block_merge testT94r3 0 1 31 T94r3c0 (show checkBlock testT94r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT94 : Valid T94 := by
  apply bound_of_layers (bs := bsT94) (last := T94r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT94 vT94r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T95 : Bound := ⟨0x1122112200000000, [0x0, 0x22002200000000, 0x102010200000000, 0x112200000000], 0x100110200000000, 4⟩
def bsT95 : Array Bound := [].toArray
theorem vbsT95 : ∀ s ∈ bsT95, Valid s := by
  intro s hs
  simp only [bsT95,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T95r3p0 : RecordPage := #[
(0xe, 0x0)]
def T95r3 : Records := #[T95r3p0]
def testT95r3 : ℕ → Bool := testAt T95 bsT95 2 (#[] : Records) T95r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T95r3c0 : checkBlock testT95r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT95r3 : LayerOK T95 3 T95r3 := by
  apply layer_of_block (bs := bsT95) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT95 (emptyOK _ _)
  exact @block_merge testT95r3 0 1 31 T95r3c0 (show checkBlock testT95r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT95 : Valid T95 := by
  apply bound_of_layers (bs := bsT95) (last := T95r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT95 vT95r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T96 : Bound := ⟨0x1212121200000000, [0x0, 0x202020200000000, 0x12001200000000, 0x121200000000], 0x10101200000000, 4⟩
def bsT96 : Array Bound := [].toArray
theorem vbsT96 : ∀ s ∈ bsT96, Valid s := by
  intro s hs
  simp only [bsT96,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T96r3p0 : RecordPage := #[
(0xe, 0x0)]
def T96r3 : Records := #[T96r3p0]
def testT96r3 : ℕ → Bool := testAt T96 bsT96 2 (#[] : Records) T96r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T96r3c0 : checkBlock testT96r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT96r3 : LayerOK T96 3 T96r3 := by
  apply layer_of_block (bs := bsT96) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT96 (emptyOK _ _)
  exact @block_merge testT96r3 0 1 31 T96r3c0 (show checkBlock testT96r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT96 : Valid T96 := by
  apply bound_of_layers (bs := bsT96) (last := T96r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT96 vT96r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T97 : Bound := ⟨0x3000300000300030, [0x0, 0x1000100000100010, 0x300030, 0x300000000030], 0x100000100030, 4⟩
def bsT97 : Array Bound := [].toArray
theorem vbsT97 : ∀ s ∈ bsT97, Valid s := by
  intro s hs
  simp only [bsT97,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T97r3p0 : RecordPage := #[
(0xe, 0x0)]
def T97r3 : Records := #[T97r3p0]
def testT97r3 : ℕ → Bool := testAt T97 bsT97 2 (#[] : Records) T97r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T97r3c0 : checkBlock testT97r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT97r3 : LayerOK T97 3 T97r3 := by
  apply layer_of_block (bs := bsT97) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT97 (emptyOK _ _)
  exact @block_merge testT97r3 0 1 31 T97r3c0 (show checkBlock testT97r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT97 : Valid T97 := by
  apply bound_of_layers (bs := bsT97) (last := T97r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT97 vT97r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T98 : Bound := ⟨0x3003300300000000, [0x0, 0x1001100100000000, 0x3000300000000, 0x300300000000], 0x1100300000000, 4⟩
def bsT98 : Array Bound := [].toArray
theorem vbsT98 : ∀ s ∈ bsT98, Valid s := by
  intro s hs
  simp only [bsT98,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T98r3p0 : RecordPage := #[
(0xe, 0x0)]
def T98r3 : Records := #[T98r3p0]
def testT98r3 : ℕ → Bool := testAt T98 bsT98 2 (#[] : Records) T98r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T98r3c0 : checkBlock testT98r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT98r3 : LayerOK T98 3 T98r3 := by
  apply layer_of_block (bs := bsT98) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT98 (emptyOK _ _)
  exact @block_merge testT98r3 0 1 31 T98r3c0 (show checkBlock testT98r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT98 : Valid T98 := by
  apply bound_of_layers (bs := bsT98) (last := T98r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT98 vT98r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T99 : Bound := ⟨0x3030000000003030, [0x0, 0x1010000000001010, 0x30000000000030, 0x3030], 0x10000000001030, 4⟩
def bsT99 : Array Bound := [].toArray
theorem vbsT99 : ∀ s ∈ bsT99, Valid s := by
  intro s hs
  simp only [bsT99,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T99r3p0 : RecordPage := #[
(0xe, 0x0)]
def T99r3 : Records := #[T99r3p0]
def testT99r3 : ℕ → Bool := testAt T99 bsT99 2 (#[] : Records) T99r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T99r3c0 : checkBlock testT99r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT99r3 : LayerOK T99 3 T99r3 := by
  apply layer_of_block (bs := bsT99) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT99 (emptyOK _ _)
  exact @block_merge testT99r3 0 1 31 T99r3c0 (show checkBlock testT99r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT99 : Valid T99 := by
  apply bound_of_layers (bs := bsT99) (last := T99r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT99 vT99r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T100 : Bound := ⟨0x3030030300000000, [0x0, 0x1010010100000000, 0x30300000000, 0x30000300000000], 0x10010300000000, 4⟩
def bsT100 : Array Bound := [].toArray
theorem vbsT100 : ∀ s ∈ bsT100, Valid s := by
  intro s hs
  simp only [bsT100,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T100r3p0 : RecordPage := #[
(0xe, 0x0)]
def T100r3 : Records := #[T100r3p0]
def testT100r3 : ℕ → Bool := testAt T100 bsT100 2 (#[] : Records) T100r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T100r3c0 : checkBlock testT100r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT100r3 : LayerOK T100 3 T100r3 := by
  apply layer_of_block (bs := bsT100) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT100 (emptyOK _ _)
  exact @block_merge testT100r3 0 1 31 T100r3c0 (show checkBlock testT100r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT100 : Valid T100 := by
  apply bound_of_layers (bs := bsT100) (last := T100r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT100 vT100r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T101 : Bound := ⟨0x3300003300000000, [0x0, 0x1100001100000000, 0x300000300000000, 0x3300000000], 0x100001300000000, 4⟩
def bsT101 : Array Bound := [].toArray
theorem vbsT101 : ∀ s ∈ bsT101, Valid s := by
  intro s hs
  simp only [bsT101,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T101r3p0 : RecordPage := #[
(0xe, 0x0)]
def T101r3 : Records := #[T101r3p0]
def testT101r3 : ℕ → Bool := testAt T101 bsT101 2 (#[] : Records) T101r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T101r3c0 : checkBlock testT101r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT101r3 : LayerOK T101 3 T101r3 := by
  apply layer_of_block (bs := bsT101) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT101 (emptyOK _ _)
  exact @block_merge testT101r3 0 1 31 T101r3c0 (show checkBlock testT101r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT101 : Valid T101 := by
  apply bound_of_layers (bs := bsT101) (last := T101r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT101 vT101r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T102 : Bound := ⟨0x4444000011110000, [0x0, 0x11110000, 0x404000001010000, 0x44000000110000], 0x4000001110000, 4⟩
def bsT102 : Array Bound := [].toArray
theorem vbsT102 : ∀ s ∈ bsT102, Valid s := by
  intro s hs
  simp only [bsT102,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T102r3p0 : RecordPage := #[
(0xe, 0x0)]
def T102r3 : Records := #[T102r3p0]
def testT102r3 : ℕ → Bool := testAt T102 bsT102 2 (#[] : Records) T102r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T102r3c0 : checkBlock testT102r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT102r3 : LayerOK T102 3 T102r3 := by
  apply layer_of_block (bs := bsT102) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT102 (emptyOK _ _)
  exact @block_merge testT102r3 0 1 31 T102r3c0 (show checkBlock testT102r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT102 : Valid T102 := by
  apply bound_of_layers (bs := bsT102) (last := T102r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT102 vT102r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T103 : Bound := ⟨0x5050050500000000, [0x0, 0x1010010100000000, 0x50500000000, 0x50000500000000], 0x10010500000000, 4⟩
def bsT103 : Array Bound := [].toArray
theorem vbsT103 : ∀ s ∈ bsT103, Valid s := by
  intro s hs
  simp only [bsT103,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T103r3p0 : RecordPage := #[
(0xe, 0x0)]
def T103r3 : Records := #[T103r3p0]
def testT103r3 : ℕ → Bool := testAt T103 bsT103 2 (#[] : Records) T103r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T103r3c0 : checkBlock testT103r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT103r3 : LayerOK T103 3 T103r3 := by
  apply layer_of_block (bs := bsT103) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT103 (emptyOK _ _)
  exact @block_merge testT103r3 0 1 31 T103r3c0 (show checkBlock testT103r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT103 : Valid T103 := by
  apply bound_of_layers (bs := bsT103) (last := T103r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT103 vT103r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T104 : Bound := ⟨0x5500000000005500, [0x0, 0x1100000000001100, 0x500000000000500, 0x5500], 0x100000000001500, 4⟩
def bsT104 : Array Bound := [].toArray
theorem vbsT104 : ∀ s ∈ bsT104, Valid s := by
  intro s hs
  simp only [bsT104,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T104r3p0 : RecordPage := #[
(0xe, 0x0)]
def T104r3 : Records := #[T104r3p0]
def testT104r3 : ℕ → Bool := testAt T104 bsT104 2 (#[] : Records) T104r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T104r3c0 : checkBlock testT104r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT104r3 : LayerOK T104 3 T104r3 := by
  apply layer_of_block (bs := bsT104) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT104 (emptyOK _ _)
  exact @block_merge testT104r3 0 1 31 T104r3c0 (show checkBlock testT104r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT104 : Valid T104 := by
  apply bound_of_layers (bs := bsT104) (last := T104r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT104 vT104r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T105 : Bound := ⟨0x5500000000550000, [0x0, 0x1100000000110000, 0x500000000050000, 0x550000], 0x100000000150000, 4⟩
def bsT105 : Array Bound := [].toArray
theorem vbsT105 : ∀ s ∈ bsT105, Valid s := by
  intro s hs
  simp only [bsT105,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T105r3p0 : RecordPage := #[
(0xe, 0x0)]
def T105r3 : Records := #[T105r3p0]
def testT105r3 : ℕ → Bool := testAt T105 bsT105 2 (#[] : Records) T105r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r3c0 : checkBlock testT105r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT105r3 : LayerOK T105 3 T105r3 := by
  apply layer_of_block (bs := bsT105) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT105 (emptyOK _ _)
  exact @block_merge testT105r3 0 1 31 T105r3c0 (show checkBlock testT105r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT105 : Valid T105 := by
  apply bound_of_layers (bs := bsT105) (last := T105r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT105 vT105r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T106 : Bound := ⟨0x5500005500000000, [0x0, 0x1100001100000000, 0x500000500000000, 0x5500000000], 0x100001500000000, 4⟩
def bsT106 : Array Bound := [].toArray
theorem vbsT106 : ∀ s ∈ bsT106, Valid s := by
  intro s hs
  simp only [bsT106,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T106r3p0 : RecordPage := #[
(0xe, 0x0)]
def T106r3 : Records := #[T106r3p0]
def testT106r3 : ℕ → Bool := testAt T106 bsT106 2 (#[] : Records) T106r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T106r3c0 : checkBlock testT106r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT106r3 : LayerOK T106 3 T106r3 := by
  apply layer_of_block (bs := bsT106) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT106 (emptyOK _ _)
  exact @block_merge testT106r3 0 1 31 T106r3c0 (show checkBlock testT106r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT106 : Valid T106 := by
  apply bound_of_layers (bs := bsT106) (last := T106r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT106 vT106r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T107 : Bound := ⟨0x5555000000000000, [0x0, 0x1111000000000000, 0x505000000000000, 0x55000000000000], 0x115000000000000, 4⟩
def bsT107 : Array Bound := [].toArray
theorem vbsT107 : ∀ s ∈ bsT107, Valid s := by
  intro s hs
  simp only [bsT107,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T107r3p0 : RecordPage := #[
(0xe, 0x0)]
def T107r3 : Records := #[T107r3p0]
def testT107r3 : ℕ → Bool := testAt T107 bsT107 2 (#[] : Records) T107r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T107r3c0 : checkBlock testT107r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT107r3 : LayerOK T107 3 T107r3 := by
  apply layer_of_block (bs := bsT107) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT107 (emptyOK _ _)
  exact @block_merge testT107r3 0 1 31 T107r3c0 (show checkBlock testT107r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT107 : Valid T107 := by
  apply bound_of_layers (bs := bsT107) (last := T107r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT107 vT107r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T237 : Bound := ⟨0xf0ff0f0, [0x0, 0x5055050, 0x3033030, 0xf0f0, 0xf00f0], 0x5051030, 4⟩
def bsT237 : Array Bound := [T68].toArray
theorem vbsT237 : ∀ s ∈ bsT237, Valid s := by
  intro s hs
  simp only [bsT237,List.mem_toArray] at hs
  exact (familyCons vT68 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT237 : Valid T237 := by
  apply bound_of_layers (bs := bsT237) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT237 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T241 : Bound := ⟨0x66666666, [0x0, 0x22222222, 0x6060606, 0x660066, 0x6666], 0x4040426, 4⟩
def bsT241 : Array Bound := [T67].toArray
theorem vbsT241 : ∀ s ∈ bsT241, Valid s := by
  intro s hs
  simp only [bsT241,List.mem_toArray] at hs
  exact (familyCons vT67 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT241 : Valid T241 := by
  apply bound_of_layers (bs := bsT241) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT241 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T243 : Bound := ⟨0xcccc3333, [0x0, 0x44441111, 0x3333, 0xc0c0303, 0xcc0033], 0x4041133, 4⟩
def bsT243 : Array Bound := [].toArray
theorem vbsT243 : ∀ s ∈ bsT243, Valid s := by
  intro s hs
  simp only [bsT243,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T243r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T243r3 : Records := #[T243r3p0]
def testT243r3 : ℕ → Bool := testAt T243 bsT243 2 (#[] : Records) T243r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T243r3c0 : checkBlock testT243r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT243r3 : LayerOK T243 3 T243r3 := by
  apply layer_of_block (bs := bsT243) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT243 (emptyOK _ _)
  exact @block_merge testT243r3 0 1 31 T243r3c0 (show checkBlock testT243r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT243 : Valid T243 := by
  apply bound_of_layers (bs := bsT243) (last := T243r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT243 vT243r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T244 : Bound := ⟨0xff0000ff, [0x0, 0x55000055, 0x33000033, 0xf00000f, 0xff], 0x500003f, 4⟩
def bsT244 : Array Bound := [].toArray
theorem vbsT244 : ∀ s ∈ bsT244, Valid s := by
  intro s hs
  simp only [bsT244,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T244r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T244r3 : Records := #[T244r3p0]
def testT244r3 : ℕ → Bool := testAt T244 bsT244 2 (#[] : Records) T244r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T244r3c0 : checkBlock testT244r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT244r3 : LayerOK T244 3 T244r3 := by
  apply layer_of_block (bs := bsT244) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT244 (emptyOK _ _)
  exact @block_merge testT244r3 0 1 31 T244r3c0 (show checkBlock testT244r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT244 : Valid T244 := by
  apply bound_of_layers (bs := bsT244) (last := T244r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT244 vT244r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T247 : Bound := ⟨0xf0f0000f0f0, [0x0, 0x50500005050, 0x30300003030, 0xf0f0, 0xf000000f0], 0x10f00001030, 4⟩
def bsT247 : Array Bound := [].toArray
theorem vbsT247 : ∀ s ∈ bsT247, Valid s := by
  intro s hs
  simp only [bsT247,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T247r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T247r3 : Records := #[T247r3p0]
def testT247r3 : ℕ → Bool := testAt T247 bsT247 2 (#[] : Records) T247r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T247r3c0 : checkBlock testT247r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT247r3 : LayerOK T247 3 T247r3 := by
  apply layer_of_block (bs := bsT247) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT247 (emptyOK _ _)
  exact @block_merge testT247r3 0 1 31 T247r3c0 (show checkBlock testT247r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT247 : Valid T247 := by
  apply bound_of_layers (bs := bsT247) (last := T247r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT247 vT247r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T250 : Bound := ⟨0x55550000aaaa, [0x0, 0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa], 0x11150000002a, 4⟩
def bsT250 : Array Bound := [].toArray
theorem vbsT250 : ∀ s ∈ bsT250, Valid s := by
  intro s hs
  simp only [bsT250,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T250r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T250r3 : Records := #[T250r3p0]
def testT250r3 : ℕ → Bool := testAt T250 bsT250 2 (#[] : Records) T250r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T250r3c0 : checkBlock testT250r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT250r3 : LayerOK T250 3 T250r3 := by
  apply layer_of_block (bs := bsT250) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT250 (emptyOK _ _)
  exact @block_merge testT250r3 0 1 31 T250r3c0 (show checkBlock testT250r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT250 : Valid T250 := by
  apply bound_of_layers (bs := bsT250) (last := T250r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT250 vT250r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T252 : Bound := ⟨0xcccc00003333, [0x0, 0x444400001111, 0x3333, 0xc0c00000303, 0xcc00000033], 0xc00001133, 4⟩
def bsT252 : Array Bound := [].toArray
theorem vbsT252 : ∀ s ∈ bsT252, Valid s := by
  intro s hs
  simp only [bsT252,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T252r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T252r3 : Records := #[T252r3p0]
def testT252r3 : ℕ → Bool := testAt T252 bsT252 2 (#[] : Records) T252r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T252r3c0 : checkBlock testT252r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT252r3 : LayerOK T252 3 T252r3 := by
  apply layer_of_block (bs := bsT252) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT252 (emptyOK _ _)
  exact @block_merge testT252r3 0 1 31 T252r3c0 (show checkBlock testT252r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT252 : Valid T252 := by
  apply bound_of_layers (bs := bsT252) (last := T252r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT252 vT252r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T255 : Bound := ⟨0xff00000000ff, [0x0, 0x550000000055, 0x330000000033, 0xf000000000f, 0xff], 0x11000000003f, 4⟩
def bsT255 : Array Bound := [].toArray
theorem vbsT255 : ∀ s ∈ bsT255, Valid s := by
  intro s hs
  simp only [bsT255,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T255r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T255r3 : Records := #[T255r3p0]
def testT255r3 : ℕ → Bool := testAt T255 bsT255 2 (#[] : Records) T255r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T255r3c0 : checkBlock testT255r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT255r3 : LayerOK T255 3 T255r3 := by
  apply layer_of_block (bs := bsT255) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT255 (emptyOK _ _)
  exact @block_merge testT255r3 0 1 31 T255r3c0 (show checkBlock testT255r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT255 : Valid T255 := by
  apply bound_of_layers (bs := bsT255) (last := T255r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT255 vT255r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T257 : Bound := ⟨0xf00f0000f00f0, [0x0, 0x5005000050050, 0x3003000030030, 0xf0000000f0, 0xf00f0], 0x5001000050030, 4⟩
def bsT257 : Array Bound := [T68].toArray
theorem vbsT257 : ∀ s ∈ bsT257, Valid s := by
  intro s hs
  simp only [bsT257,List.mem_toArray] at hs
  exact (familyCons vT68 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT257 : Valid T257 := by
  apply bound_of_layers (bs := bsT257) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT257 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T259 : Bound := ⟨0x66006600660066, [0x0, 0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066], 0x4000600040026, 4⟩
def bsT259 : Array Bound := [T71].toArray
theorem vbsT259 : ∀ s ∈ bsT259, Valid s := by
  intro s hs
  simp only [bsT259,List.mem_toArray] at hs
  exact (familyCons vT71 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT259 : Valid T259 := by
  apply bound_of_layers (bs := bsT259) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT259 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T264 : Bound := ⟨0x50505050a0a0a0a, [0x0, 0xa0a0a0a, 0x101010102020202, 0x50005000a000a, 0x50500000a0a], 0x10501050000000a, 4⟩
def bsT264 : Array Bound := [].toArray
theorem vbsT264 : ∀ s ∈ bsT264, Valid s := by
  intro s hs
  simp only [bsT264,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T264r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T264r3 : Records := #[T264r3p0]
def testT264r3 : ℕ → Bool := testAt T264 bsT264 2 (#[] : Records) T264r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T264r3c0 : checkBlock testT264r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT264r3 : LayerOK T264 3 T264r3 := by
  apply layer_of_block (bs := bsT264) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT264 (emptyOK _ _)
  exact @block_merge testT264r3 0 1 31 T264r3c0 (show checkBlock testT264r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT264 : Valid T264 := by
  apply bound_of_layers (bs := bsT264) (last := T264r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT264 vT264r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T265 : Bound := ⟨0x50a050a050a050a, [0x0, 0xa000a000a000a, 0x102010201020102, 0x50a0000050a, 0x50a050a], 0x100010a0500050a, 4⟩
def bsT265 : Array Bound := [T81].toArray
theorem vbsT265 : ∀ s ∈ bsT265, Valid s := by
  intro s hs
  simp only [bsT265,List.mem_toArray] at hs
  exact (familyCons vT81 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT265 : Valid T265 := by
  apply bound_of_layers (bs := bsT265) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT265 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T266 : Bound := ⟨0x606060606060606, [0x0, 0x202020202020202, 0x6000600060006, 0x60600000606, 0x6060606], 0x4000604040406, 4⟩
def bsT266 : Array Bound := [].toArray
theorem vbsT266 : ∀ s ∈ bsT266, Valid s := by
  intro s hs
  simp only [bsT266,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T266r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T266r3 : Records := #[T266r3p0]
def testT266r3 : ℕ → Bool := testAt T266 bsT266 2 (#[] : Records) T266r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T266r3c0 : checkBlock testT266r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT266r3 : LayerOK T266 3 T266r3 := by
  apply layer_of_block (bs := bsT266) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT266 (emptyOK _ _)
  exact @block_merge testT266r3 0 1 31 T266r3c0 (show checkBlock testT266r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT266 : Valid T266 := by
  apply bound_of_layers (bs := bsT266) (last := T266r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT266 vT266r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T268 : Bound := ⟨0xc0c0c0c03030303, [0x0, 0x404040401010101, 0x3030303, 0xc000c00030003, 0xc0c00000303], 0x4000c01010103, 4⟩
def bsT268 : Array Bound := [].toArray
theorem vbsT268 : ∀ s ∈ bsT268, Valid s := by
  intro s hs
  simp only [bsT268,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T268r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T268r3 : Records := #[T268r3p0]
def testT268r3 : ℕ → Bool := testAt T268 bsT268 2 (#[] : Records) T268r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T268r3c0 : checkBlock testT268r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT268r3 : LayerOK T268 3 T268r3 := by
  apply layer_of_block (bs := bsT268) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT268 (emptyOK _ _)
  exact @block_merge testT268r3 0 1 31 T268r3c0 (show checkBlock testT268r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT268 : Valid T268 := by
  apply bound_of_layers (bs := bsT268) (last := T268r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT268 vT268r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T270 : Bound := ⟨0xf000f00000f000f, [0x0, 0x500050000050005, 0x300030000030003, 0xf000f, 0xf000000000f], 0x10001000005000f, 4⟩
def bsT270 : Array Bound := [].toArray
theorem vbsT270 : ∀ s ∈ bsT270, Valid s := by
  intro s hs
  simp only [bsT270,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T270r3p0 : RecordPage := #[
(0x1e, 0x0)]
def T270r3 : Records := #[T270r3p0]
def testT270r3 : ℕ → Bool := testAt T270 bsT270 2 (#[] : Records) T270r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T270r3c0 : checkBlock testT270r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT270r3 : LayerOK T270 3 T270r3 := by
  apply layer_of_block (bs := bsT270) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT270 (emptyOK _ _)
  exact @block_merge testT270r3 0 1 31 T270r3c0 (show checkBlock testT270r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT270 : Valid T270 := by
  apply bound_of_layers (bs := bsT270) (last := T270r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT270 vT270r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T273 : Bound := ⟨0x1414141414141414, [0x0, 0x404040404040404, 0x14001400140014, 0x141400001414, 0x14141414], 0x14101404141414, 4⟩
def bsT273 : Array Bound := [T83].toArray
theorem vbsT273 : ∀ s ∈ bsT273, Valid s := by
  intro s hs
  simp only [bsT273,List.mem_toArray] at hs
  exact (familyCons vT83 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT273 : Valid T273 := by
  apply bound_of_layers (bs := bsT273) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT273 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T276 : Bound := ⟨0x3c003c003c003c00, [0x0, 0x1400140014001400, 0xc000c000c000c00, 0x3c0000003c00, 0x3c003c00], 0x100004001400, 4⟩
def bsT276 : Array Bound := [T83].toArray
theorem vbsT276 : ∀ s ∈ bsT276, Valid s := by
  intro s hs
  simp only [bsT276,List.mem_toArray] at hs
  exact (familyCons vT83 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT276 : Valid T276 := by
  apply bound_of_layers (bs := bsT276) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT276 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T277 : Bound := ⟨0x4488448844884488, [0x0, 0x88008800880088, 0x408040804080408, 0x448800004488, 0x44884488], 0x804000408, 4⟩
def bsT277 : Array Bound := [T81].toArray
theorem vbsT277 : ∀ s ∈ bsT277, Valid s := by
  intro s hs
  simp only [bsT277,List.mem_toArray] at hs
  exact (familyCons vT81 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT277 : Valid T277 := by
  apply bound_of_layers (bs := bsT277) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT277 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T279 : Bound := ⟨0x33333333, [0x0, 0x11111111, 0x3030303, 0x330033, 0x3333], 0x1111133, 5⟩
def bsT279 : Array Bound := [T87].toArray
theorem vbsT279 : ∀ s ∈ bsT279, Valid s := by
  intro s hs
  simp only [bsT279,List.mem_toArray] at hs
  exact (familyCons vT87 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT279 : Valid T279 := by
  apply bound_of_layers (bs := bsT279) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT279 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T282 : Bound := ⟨0x3c3c3c3c, [0x0, 0x14141414, 0xc0c0c0c, 0x3c003c, 0x3c3c], 0x414143c, 5⟩
def bsT282 : Array Bound := [T87].toArray
theorem vbsT282 : ∀ s ∈ bsT282, Valid s := by
  intro s hs
  simp only [bsT282,List.mem_toArray] at hs
  exact (familyCons vT87 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT282 : Valid T282 := by
  apply bound_of_layers (bs := bsT282) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT282 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T284 : Bound := ⟨0xf0f00f0f, [0x0, 0x50500505, 0x30300303, 0xf0f, 0xf0000f], 0x10050f, 5⟩
def bsT284 : Array Bound := [T86].toArray
theorem vbsT284 : ∀ s ∈ bsT284, Valid s := by
  intro s hs
  simp only [bsT284,List.mem_toArray] at hs
  exact (familyCons vT86 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT284 : Valid T284 := by
  apply bound_of_layers (bs := bsT284) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT284 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T285 : Bound := ⟨0xf0f0f0f0, [0x0, 0x50505050, 0x30303030, 0xf000f0, 0xf0f0], 0x101030, 5⟩
def bsT285 : Array Bound := [T87].toArray
theorem vbsT285 : ∀ s ∈ bsT285, Valid s := by
  intro s hs
  simp only [bsT285,List.mem_toArray] at hs
  exact (familyCons vT87 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT285 : Valid T285 := by
  apply bound_of_layers (bs := bsT285) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT285 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T286 : Bound := ⟨0xff000000ff0, [0x0, 0x55000000550, 0x33000000330, 0xf0000000f0, 0xff0], 0x11000000530, 5⟩
def bsT286 : Array Bound := [T64].toArray
theorem vbsT286 : ∀ s ∈ bsT286, Valid s := by
  intro s hs
  simp only [bsT286,List.mem_toArray] at hs
  exact (familyCons vT64 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T286r4p0 : RecordPage := #[
(0x1e, 0x0)]
def T286r4 : Records := #[T286r4p0]
def testT286r4 : ℕ → Bool := testAt T286 bsT286 3 (#[] : Records) T286r4 0 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T286r4c0 : checkBlock testT286r4 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT286r4 : LayerOK T286 4 T286r4 := by
  apply layer_of_block (bs := bsT286) (k := 3) (old := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT286 (emptyOK _ _)
  exact @block_merge testT286r4 0 1 31 T286r4c0 (show checkBlock testT286r4 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT286 : Valid T286 := by
  apply bound_of_layers (bs := bsT286) (last := T286r4) (cw := 0) (rw := 0) (by decide +kernel) vbsT286 vT286r4 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T287 : Bound := ⟨0x3c3c00003c3c, [0x0, 0x141400001414, 0xc0c00000c0c, 0x3c0000003c, 0x3c3c], 0x101c0000143c, 5⟩
def bsT287 : Array Bound := [T74].toArray
theorem vbsT287 : ∀ s ∈ bsT287, Valid s := by
  intro s hs
  simp only [bsT287,List.mem_toArray] at hs
  exact (familyCons vT74 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T287r4p0 : RecordPage := #[
(0x1e, 0x0)]
def T287r4 : Records := #[T287r4p0]
def testT287r4 : ℕ → Bool := testAt T287 bsT287 3 (#[] : Records) T287r4 0 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T287r4c0 : checkBlock testT287r4 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT287r4 : LayerOK T287 4 T287r4 := by
  apply layer_of_block (bs := bsT287) (k := 3) (old := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT287 (emptyOK _ _)
  exact @block_merge testT287r4 0 1 31 T287r4c0 (show checkBlock testT287r4 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT287 : Valid T287 := by
  apply bound_of_layers (bs := bsT287) (last := T287r4) (cw := 0) (rw := 0) (by decide +kernel) vbsT287 vT287r4 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T289 : Bound := ⟨0x55aa000055aa, [0x0, 0xaa000000aa, 0x112200001122, 0x50a0000050a, 0x55aa], 0x110a0000152a, 5⟩
def bsT289 : Array Bound := [T76].toArray
theorem vbsT289 : ∀ s ∈ bsT289, Valid s := by
  intro s hs
  simp only [bsT289,List.mem_toArray] at hs
  exact (familyCons vT76 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T289r4p0 : RecordPage := #[
(0x1e, 0x0)]
def T289r4 : Records := #[T289r4p0]
def testT289r4 : ℕ → Bool := testAt T289 bsT289 3 (#[] : Records) T289r4 0 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T289r4c0 : checkBlock testT289r4 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT289r4 : LayerOK T289 4 T289r4 := by
  apply layer_of_block (bs := bsT289) (k := 3) (old := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT289 (emptyOK _ _)
  exact @block_merge testT289r4 0 1 31 T289r4c0 (show checkBlock testT289r4 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT289 : Valid T289 := by
  apply bound_of_layers (bs := bsT289) (last := T289r4) (cw := 0) (rw := 0) (by decide +kernel) vbsT289 vT289r4 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T290 : Bound := ⟨0x666600006666, [0x0, 0x222200002222, 0x60600000606, 0x6600000066, 0x6666], 0x600000426, 5⟩
def bsT290 : Array Bound := [T67].toArray
theorem vbsT290 : ∀ s ∈ bsT290, Valid s := by
  intro s hs
  simp only [bsT290,List.mem_toArray] at hs
  exact (familyCons vT67 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T290r4p0 : RecordPage := #[
(0x1e, 0x0)]
def T290r4 : Records := #[T290r4p0]
def testT290r4 : ℕ → Bool := testAt T290 bsT290 3 (#[] : Records) T290r4 0 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T290r4c0 : checkBlock testT290r4 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT290r4 : LayerOK T290 4 T290r4 := by
  apply layer_of_block (bs := bsT290) (k := 3) (old := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT290 (emptyOK _ _)
  exact @block_merge testT290r4 0 1 31 T290r4c0 (show checkBlock testT290r4 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT290 : Valid T290 := by
  apply bound_of_layers (bs := bsT290) (last := T290r4) (cw := 0) (rw := 0) (by decide +kernel) vbsT290 vT290r4 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T291 : Bound := ⟨0xcc003300cc0033, [0x0, 0x44001100440011, 0x3300000033, 0xc0003000c0003, 0xcc0033], 0x4001300040033, 5⟩
def bsT291 : Array Bound := [T88].toArray
theorem vbsT291 : ∀ s ∈ bsT291, Valid s := by
  intro s hs
  simp only [bsT291,List.mem_toArray] at hs
  exact (familyCons vT88 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT291 : Valid T291 := by
  apply bound_of_layers (bs := bsT291) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT291 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T292 : Bound := ⟨0x303030330303030, [0x0, 0x101010110101010, 0x30303030, 0x3000300300030, 0x30300003030], 0x101010300101030, 5⟩
def bsT292 : Array Bound := [T87].toArray
theorem vbsT292 : ∀ s ∈ bsT292, Valid s := by
  intro s hs
  simp only [bsT292,List.mem_toArray] at hs
  exact (familyCons vT87 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT292 : Valid T292 := by
  apply bound_of_layers (bs := bsT292) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT292 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T293 : Bound := ⟨0x505050550505050, [0x0, 0x101010110101010, 0x50505050, 0x5000500500050, 0x50500005050], 0x105010500101010, 5⟩
def bsT293 : Array Bound := [T89].toArray
theorem vbsT293 : ∀ s ∈ bsT293, Valid s := by
  intro s hs
  simp only [bsT293,List.mem_toArray] at hs
  exact (familyCons vT89 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT293 : Valid T293 := by
  apply bound_of_layers (bs := bsT293) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT293 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T294 : Bound := ⟨0xc0c03030c0c0303, [0x0, 0x404010104040101, 0x30300000303, 0xc0003000c0003, 0xc0c0303], 0x4010304040103, 5⟩
def bsT294 : Array Bound := [T91].toArray
theorem vbsT294 : ∀ s ∈ bsT294, Valid s := by
  intro s hs
  simp only [bsT294,List.mem_toArray] at hs
  exact (familyCons vT91 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT294 : Valid T294 := by
  apply bound_of_layers (bs := bsT294) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT294 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T295 : Bound := ⟨0xf0f000000000f0f, [0x0, 0x505000000000505, 0x303000000000303, 0xf00000000000f, 0xf0f], 0x10500000000050f, 5⟩
def bsT295 : Array Bound := [T90].toArray
theorem vbsT295 : ∀ s ∈ bsT295, Valid s := by
  intro s hs
  simp only [bsT295,List.mem_toArray] at hs
  exact (familyCons vT90 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT295 : Valid T295 := by
  apply bound_of_layers (bs := bsT295) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT295 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T296 : Bound := ⟨0xf0f0000f0f00000, [0x0, 0x505000050500000, 0x303000030300000, 0xf0f00000, 0xf000000f00000], 0x105000000100000, 5⟩
def bsT296 : Array Bound := [T89].toArray
theorem vbsT296 : ∀ s ∈ bsT296, Valid s := by
  intro s hs
  simp only [bsT296,List.mem_toArray] at hs
  exact (familyCons vT89 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT296 : Valid T296 := by
  apply bound_of_layers (bs := bsT296) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT296 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T297 : Bound := ⟨0x1111111122222222, [0x0, 0x22222222, 0x101010102020202, 0x11001100220022, 0x111100002222], 0x111111100000022, 5⟩
def bsT297 : Array Bound := [T92].toArray
theorem vbsT297 : ∀ s ∈ bsT297, Valid s := by
  intro s hs
  simp only [bsT297,List.mem_toArray] at hs
  exact (familyCons vT92 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT297 : Valid T297 := by
  apply bound_of_layers (bs := bsT297) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT297 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T298 : Bound := ⟨0x1111222211112222, [0x0, 0x222200002222, 0x101020201010202, 0x11002200110022, 0x11112222], 0x111000201110022, 5⟩
def bsT298 : Array Bound := [T93].toArray
theorem vbsT298 : ∀ s ∈ bsT298, Valid s := by
  intro s hs
  simp only [bsT298,List.mem_toArray] at hs
  exact (familyCons vT93 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT298 : Valid T298 := by
  apply bound_of_layers (bs := bsT298) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT298 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T300 : Bound := ⟨0x1122112211221122, [0x0, 0x22002200220022, 0x102010201020102, 0x112200001122, 0x11221122], 0x100110201001122, 5⟩
def bsT300 : Array Bound := [T95].toArray
theorem vbsT300 : ∀ s ∈ bsT300, Valid s := by
  intro s hs
  simp only [bsT300,List.mem_toArray] at hs
  exact (familyCons vT95 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT300 : Valid T300 := by
  apply bound_of_layers (bs := bsT300) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT300 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T301 : Bound := ⟨0x3030303030303030, [0x0, 0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030], 0x10101000101030, 5⟩
def bsT301 : Array Bound := [T87].toArray
theorem vbsT301 : ∀ s ∈ bsT301, Valid s := by
  intro s hs
  simp only [bsT301,List.mem_toArray] at hs
  exact (familyCons vT87 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT301 : Valid T301 := by
  apply bound_of_layers (bs := bsT301) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT301 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T302 : Bound := ⟨0x3300003333000033, [0x0, 0x1100001111000011, 0x300000303000003, 0x3300000033, 0x33000033], 0x100001301000033, 5⟩
def bsT302 : Array Bound := [T101].toArray
theorem vbsT302 : ∀ s ∈ bsT302, Valid s := by
  intro s hs
  simp only [bsT302,List.mem_toArray] at hs
  exact (familyCons vT101 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT302 : Valid T302 := by
  apply bound_of_layers (bs := bsT302) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT302 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T303 : Bound := ⟨0x3300330000330033, [0x0, 0x1100110000110011, 0x300030000030003, 0x330033, 0x330000000033], 0x100110000110033, 5⟩
def bsT303 : Array Bound := [T97].toArray
theorem vbsT303 : ∀ s ∈ bsT303, Valid s := by
  intro s hs
  simp only [bsT303,List.mem_toArray] at hs
  exact (familyCons vT97 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT303 : Valid T303 := by
  apply bound_of_layers (bs := bsT303) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT303 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T304 : Bound := ⟨0x3333000000003333, [0x0, 0x1111000000001111, 0x303000000000303, 0x33000000000033, 0x3333], 0x111000000001133, 5⟩
def bsT304 : Array Bound := [T99].toArray
theorem vbsT304 : ∀ s ∈ bsT304, Valid s := by
  intro s hs
  simp only [bsT304,List.mem_toArray] at hs
  exact (familyCons vT99 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT304 : Valid T304 := by
  apply bound_of_layers (bs := bsT304) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT304 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T306 : Bound := ⟨0x3c3c3c3c00000000, [0x0, 0x1414141400000000, 0xc0c0c0c00000000, 0x3c003c00000000, 0x3c3c00000000], 0x14101c00000000, 5⟩
def bsT306 : Array Bound := [T74].toArray
theorem vbsT306 : ∀ s ∈ bsT306, Valid s := by
  intro s hs
  simp only [bsT306,List.mem_toArray] at hs
  exact (familyCons vT74 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T306r4p0 : RecordPage := #[
(0x1e, 0x0)]
def T306r4 : Records := #[T306r4p0]
def testT306r4 : ℕ → Bool := testAt T306 bsT306 3 (#[] : Records) T306r4 0 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T306r4c0 : checkBlock testT306r4 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT306r4 : LayerOK T306 4 T306r4 := by
  apply layer_of_block (bs := bsT306) (k := 3) (old := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT306 (emptyOK _ _)
  exact @block_merge testT306r4 0 1 31 T306r4c0 (show checkBlock testT306r4 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT306 : Valid T306 := by
  apply bound_of_layers (bs := bsT306) (last := T306r4) (cw := 0) (rw := 0) (by decide +kernel) vbsT306 vT306r4 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T307 : Bound := ⟨0x4444444411111111, [0x0, 0x11111111, 0x404040401010101, 0x44004400110011, 0x444400001111], 0x4000401111111, 5⟩
def bsT307 : Array Bound := [T102].toArray
theorem vbsT307 : ∀ s ∈ bsT307, Valid s := by
  intro s hs
  simp only [bsT307,List.mem_toArray] at hs
  exact (familyCons vT102 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT307 : Valid T307 := by
  apply bound_of_layers (bs := bsT307) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT307 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T308 : Bound := ⟨0x5050050550500505, [0x0, 0x1010010110100101, 0x50500000505, 0x50000500500005, 0x50500505], 0x10010500100505, 5⟩
def bsT308 : Array Bound := [T103].toArray
theorem vbsT308 : ∀ s ∈ bsT308, Valid s := by
  intro s hs
  simp only [bsT308,List.mem_toArray] at hs
  exact (familyCons vT103 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT308 : Valid T308 := by
  apply bound_of_layers (bs := bsT308) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT308 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T309 : Bound := ⟨0x50505050a0a0a0a0, [0x0, 0xa0a0a0a0, 0x1010101020202020, 0x50005000a000a0, 0x50500000a0a0], 0x10101000000020, 5⟩
def bsT309 : Array Bound := [T92].toArray
theorem vbsT309 : ∀ s ∈ bsT309, Valid s := by
  intro s hs
  simp only [bsT309,List.mem_toArray] at hs
  exact (familyCons vT92 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT309 : Valid T309 := by
  apply bound_of_layers (bs := bsT309) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT309 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T310 : Bound := ⟨0x5500005555000055, [0x0, 0x1100001111000011, 0x500000505000005, 0x5500000055, 0x55000055], 0x100001505000015, 5⟩
def bsT310 : Array Bound := [T106].toArray
theorem vbsT310 : ∀ s ∈ bsT310, Valid s := by
  intro s hs
  simp only [bsT310,List.mem_toArray] at hs
  exact (familyCons vT106 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT310 : Valid T310 := by
  apply bound_of_layers (bs := bsT310) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT310 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T311 : Bound := ⟨0x5500550000550055, [0x0, 0x1100110000110011, 0x500050000050005, 0x550055, 0x550000000055], 0x100110000150015, 5⟩
def bsT311 : Array Bound := [T105].toArray
theorem vbsT311 : ∀ s ∈ bsT311, Valid s := by
  intro s hs
  simp only [bsT311,List.mem_toArray] at hs
  exact (familyCons vT105 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT311 : Valid T311 := by
  apply bound_of_layers (bs := bsT311) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT311 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T312 : Bound := ⟨0x5555000000005555, [0x0, 0x1111000000001111, 0x505000000000505, 0x55000000000055, 0x5555], 0x115000000001515, 5⟩
def bsT312 : Array Bound := [T104].toArray
theorem vbsT312 : ∀ s ∈ bsT312, Valid s := by
  intro s hs
  simp only [bsT312,List.mem_toArray] at hs
  exact (familyCons vT104 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT312 : Valid T312 := by
  apply bound_of_layers (bs := bsT312) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT312 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T313 : Bound := ⟨0x5555000055550000, [0x0, 0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000], 0x115000005150000, 5⟩
def bsT313 : Array Bound := [T107].toArray
theorem vbsT313 : ∀ s ∈ bsT313, Valid s := by
  intro s hs
  simp only [bsT313,List.mem_toArray] at hs
  exact (familyCons vT107 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT313 : Valid T313 := by
  apply bound_of_layers (bs := bsT313) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT313 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T314 : Bound := ⟨0x55550000aaaa0000, [0x0, 0xaaaa0000, 0x1111000022220000, 0x50500000a0a0000, 0x55000000aa0000], 0x115000000000000, 5⟩
def bsT314 : Array Bound := [T107].toArray
theorem vbsT314 : ∀ s ∈ bsT314, Valid s := by
  intro s hs
  simp only [bsT314,List.mem_toArray] at hs
  exact (familyCons vT107 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT314 : Valid T314 := by
  apply bound_of_layers (bs := bsT314) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT314 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T315 : Bound := ⟨0x5555555500000000, [0x0, 0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000], 0x115111500000000, 5⟩
def bsT315 : Array Bound := [T107].toArray
theorem vbsT315 : ∀ s ∈ bsT315, Valid s := by
  intro s hs
  simp only [bsT315,List.mem_toArray] at hs
  exact (familyCons vT107 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT315 : Valid T315 := by
  apply bound_of_layers (bs := bsT315) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT315 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T316 : Bound := ⟨0x5555aaaa00000000, [0x0, 0xaaaa00000000, 0x1111222200000000, 0x5050a0a00000000, 0x5500aa00000000], 0x115000a00000000, 5⟩
def bsT316 : Array Bound := [T93].toArray
theorem vbsT316 : ∀ s ∈ bsT316, Valid s := by
  intro s hs
  simp only [bsT316,List.mem_toArray] at hs
  exact (familyCons vT93 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT316 : Valid T316 := by
  apply bound_of_layers (bs := bsT316) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT316 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T317 : Bound := ⟨0xc0c0c0c030303030, [0x0, 0x4040404010101010, 0x30303030, 0xc000c000300030, 0xc0c000003030], 0x101030, 5⟩
def bsT317 : Array Bound := [T87].toArray
theorem vbsT317 : ∀ s ∈ bsT317, Valid s := by
  intro s hs
  simp only [bsT317,List.mem_toArray] at hs
  exact (familyCons vT87 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT317 : Valid T317 := by
  apply bound_of_layers (bs := bsT317) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT317 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T318 : Bound := ⟨0xcccc00000000cccc, [0x0, 0x4444000000004444, 0xc0c000000000c0c, 0xcc0000000000cc, 0xcccc], 0x400000000040c, 5⟩
def bsT318 : Array Bound := [T90].toArray
theorem vbsT318 : ∀ s ∈ bsT318, Valid s := by
  intro s hs
  simp only [bsT318,List.mem_toArray] at hs
  exact (familyCons vT90 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT318 : Valid T318 := by
  apply bound_of_layers (bs := bsT318) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT318 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T319 : Bound := ⟨0xcccc000033330000, [0x0, 0x4444000011110000, 0x33330000, 0xc0c000003030000, 0xcc000000330000], 0x4000001110000, 5⟩
def bsT319 : Array Bound := [T102].toArray
theorem vbsT319 : ∀ s ∈ bsT319, Valid s := by
  intro s hs
  simp only [bsT319,List.mem_toArray] at hs
  exact (familyCons vT102 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT319 : Valid T319 := by
  apply bound_of_layers (bs := bsT319) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT319 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T320 : Bound := ⟨0xcccc333300000000, [0x0, 0x4444111100000000, 0x333300000000, 0xc0c030300000000, 0xcc003300000000], 0x4111300000000, 5⟩
def bsT320 : Array Bound := [T88].toArray
theorem vbsT320 : ∀ s ∈ bsT320, Valid s := by
  intro s hs
  simp only [bsT320,List.mem_toArray] at hs
  exact (familyCons vT88 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT320 : Valid T320 := by
  apply bound_of_layers (bs := bsT320) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT320 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T321 : Bound := ⟨0xf000f00000f000f0, [0x0, 0x5000500000500050, 0x3000300000300030, 0xf000f0, 0xf000000000f0], 0x100000100030, 5⟩
def bsT321 : Array Bound := [T97].toArray
theorem vbsT321 : ∀ s ∈ bsT321, Valid s := by
  intro s hs
  simp only [bsT321,List.mem_toArray] at hs
  exact (familyCons vT97 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT321 : Valid T321 := by
  apply bound_of_layers (bs := bsT321) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT321 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T323 : Bound := ⟨0xf0f000000000f0f0, [0x0, 0x5050000000005050, 0x3030000000003030, 0xf00000000000f0, 0xf0f0], 0x10000000001030, 5⟩
def bsT323 : Array Bound := [T99].toArray
theorem vbsT323 : ∀ s ∈ bsT323, Valid s := by
  intro s hs
  simp only [bsT323,List.mem_toArray] at hs
  exact (familyCons vT99 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT323 : Valid T323 := by
  apply bound_of_layers (bs := bsT323) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT323 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T324 : Bound := ⟨0xf0f00f0f00000000, [0x0, 0x5050050500000000, 0x3030030300000000, 0xf0f00000000, 0xf0000f00000000], 0x10010f00000000, 5⟩
def bsT324 : Array Bound := [T100].toArray
theorem vbsT324 : ∀ s ∈ bsT324, Valid s := by
  intro s hs
  simp only [bsT324,List.mem_toArray] at hs
  exact (familyCons vT100 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT324 : Valid T324 := by
  apply bound_of_layers (bs := bsT324) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT324 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T325 : Bound := ⟨0xff0000000000ff00, [0x0, 0x5500000000005500, 0x3300000000003300, 0xf00000000000f00, 0xff00], 0x100000000001500, 5⟩
def bsT325 : Array Bound := [T104].toArray
theorem vbsT325 : ∀ s ∈ bsT325, Valid s := by
  intro s hs
  simp only [bsT325,List.mem_toArray] at hs
  exact (familyCons vT104 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT325 : Valid T325 := by
  apply bound_of_layers (bs := bsT325) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT325 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T326 : Bound := ⟨0xff00000000ff0000, [0x0, 0x5500000000550000, 0x3300000000330000, 0xf000000000f0000, 0xff0000], 0x100000000150000, 5⟩
def bsT326 : Array Bound := [T105].toArray
theorem vbsT326 : ∀ s ∈ bsT326, Valid s := by
  intro s hs
  simp only [bsT326,List.mem_toArray] at hs
  exact (familyCons vT105 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT326 : Valid T326 := by
  apply bound_of_layers (bs := bsT326) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT326 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T327 : Bound := ⟨0xff0000ff00000000, [0x0, 0x5500005500000000, 0x3300003300000000, 0xf00000f00000000, 0xff00000000], 0x100001f00000000, 5⟩
def bsT327 : Array Bound := [T101].toArray
theorem vbsT327 : ∀ s ∈ bsT327, Valid s := by
  intro s hs
  simp only [bsT327,List.mem_toArray] at hs
  exact (familyCons vT101 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT327 : Valid T327 := by
  apply bound_of_layers (bs := bsT327) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT327 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T328 : Bound := ⟨0xffff000000000000, [0x0, 0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000], 0x115000000000000, 5⟩
def bsT328 : Array Bound := [T107].toArray
theorem vbsT328 : ∀ s ∈ bsT328, Valid s := by
  intro s hs
  simp only [bsT328,List.mem_toArray] at hs
  exact (familyCons vT107 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT328 : Valid T328 := by
  apply bound_of_layers (bs := bsT328) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT328 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T329 : Bound := ⟨0x5a5a5a5a, [0x0, 0xa0a0a0a, 0x12121212, 0x5a005a, 0x5a5a], 0x10101a, 6⟩
def bsT329 : Array Bound := [T66, T70, T84].toArray
theorem vbsT329 : ∀ s ∈ bsT329, Valid s := by
  intro s hs
  simp only [bsT329,List.mem_toArray] at hs
  exact (familyCons vT66 <| familyCons vT70 <| familyCons vT84 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T329r2p0 : RecordPage := #[
(0x230a216101e, 0x0), (0x230a316101e, 0x0)]
def T329r2 : Records := #[T329r2p0]
def testT329r2 : ℕ → Bool := testAt T329 bsT329 1 (#[] : Records) T329r2 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T329r2c0 : checkBlock testT329r2 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT329r2 : LayerOK T329 2 T329r2 := by
  apply layer_of_block (bs := bsT329) (k := 1) (old := (#[] : Records)) (cw := 2) (rw := 1) (by decide +kernel) vbsT329 (emptyOK _ _)
  exact @block_merge testT329r2 0 2 30 T329r2c0 (show checkBlock testT329r2 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T329r3p0 : RecordPage := #[
(0x8216101e, 0x0), (0xa216101e, 0x1), (0x8316101e, 0x0), (0xa316101e, 0x3),
(0x230c201e, 0x0), (0x240e201e, 0x1), (0x230c301e, 0x0), (0x240e301e, 0x3)]
def T329r3 : Records := #[T329r3p0]
def testT329r3 : ℕ → Bool := testAt T329 bsT329 2 T329r2 T329r3 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T329r3c0 : checkBlock testT329r3 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T329r3c1 : checkBlock testT329r3 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT329r3 : LayerOK T329 3 T329r3 := by
  apply layer_of_block (bs := bsT329) (k := 2) (old := T329r2) (cw := 2) (rw := 1) (by decide +kernel) vbsT329 vT329r2
  exact @block_merge testT329r3 0 8 24 (@block_merge testT329r3 0 4 4 T329r3c0 T329r3c1) (show checkBlock testT329r3 24 8 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T329r4p0 : RecordPage := #[
(0x6101e, 0x1d4c64), (0xc201e, 0xc9), (0xe201e, 0x18b), (0xc301e, 0x2cd),
(0xe301e, 0x3af), (0xc321e, 0x0)]
def T329r4 : Records := #[T329r4p0]
def testT329r4 : ℕ → Bool := testAt T329 bsT329 3 T329r3 T329r4 2 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T329r4c0 : checkBlock testT329r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T329r4c1 : checkBlock testT329r4 2 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT329r4 : LayerOK T329 4 T329r4 := by
  apply layer_of_block (bs := bsT329) (k := 3) (old := T329r3) (cw := 2) (rw := 3) (by decide +kernel) vbsT329 vT329r3
  exact @block_merge testT329r4 0 6 26 (@block_merge testT329r4 0 4 2 T329r4c0 T329r4c1) (show checkBlock testT329r4 26 6 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T329r5p0 : RecordPage := #[
(0x1e, 0x85c92492090e951c9064)]
def T329r5 : Records := #[T329r5p0]
def testT329r5 : ℕ → Bool := testAt T329 bsT329 4 T329r4 T329r5 2 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T329r5c0 : checkBlock testT329r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT329r5 : LayerOK T329 5 T329r5 := by
  apply layer_of_block (bs := bsT329) (k := 4) (old := T329r4) (cw := 2) (rw := 3) (by decide +kernel) vbsT329 vT329r4
  exact @block_merge testT329r5 0 1 31 T329r5c0 (show checkBlock testT329r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT329 : Valid T329 := by
  apply bound_of_layers (bs := bsT329) (last := T329r5) (cw := 2) (rw := 0) (by decide +kernel) vbsT329 vT329r5 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T330 : Bound := ⟨0x99999999, [0x0, 0x11111111, 0x9090909, 0x990099, 0x9999], 0x1111119, 6⟩
def bsT330 : Array Bound := [].toArray
theorem vbsT330 : ∀ s ∈ bsT330, Valid s := by
  intro s hs
  simp only [bsT330,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T330r3p0 : RecordPage := #[
(0x230c101e, 0x0), (0x330c101e, 0x0), (0x240c101e, 0x0), (0x340c101e, 0x0),
(0x30f101e, 0x0), (0x130f101e, 0x0), (0x40f101e, 0x0), (0x140f101e, 0x0),
(0x230c201e, 0x0), (0x330c201e, 0x0), (0x240c201e, 0x0), (0x340c201e, 0x0),
(0x30f201e, 0x0), (0x130f201e, 0x0), (0x40f201e, 0x0), (0x140f201e, 0x0),
(0x230c301e, 0x0), (0x330c301e, 0x0), (0x240c301e, 0x0), (0x340c301e, 0x0),
(0x30f301e, 0x0), (0x130f301e, 0x0), (0x40f301e, 0x0), (0x140f301e, 0x0),
(0x321c211e, 0x0), (0x240d211e, 0x0), (0x340d211e, 0x0), (0x240e211e, 0x0),
(0x340e211e, 0x0), (0x321c311e, 0x0), (0x240d311e, 0x0), (0x340d311e, 0x0)]
def T330r3p1 : RecordPage := #[
(0x240e311e, 0x0), (0x340e311e, 0x0), (0x321c321e, 0x0), (0x240d321e, 0x0),
(0x340d321e, 0x0), (0x240e321e, 0x0), (0x340e321e, 0x0)]
def T330r3 : Records := #[T330r3p0, T330r3p1]
def testT330r3 : ℕ → Bool := testAt T330 bsT330 2 (#[] : Records) T330r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r3c0 : checkBlock testT330r3 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r3c1 : checkBlock testT330r3 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r3c2 : checkBlock testT330r3 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r3c3 : checkBlock testT330r3 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r3c4 : checkBlock testT330r3 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r3c5 : checkBlock testT330r3 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r3c6 : checkBlock testT330r3 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r3c7 : checkBlock testT330r3 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r3c8 : checkBlock testT330r3 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r3c9 : checkBlock testT330r3 3 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT330r3 : LayerOK T330 3 T330r3 := by
  apply layer_of_block (bs := bsT330) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT330 (emptyOK _ _)
  exact @block_merge testT330r3 0 39 25 (@block_merge testT330r3 0 20 19 (@block_merge testT330r3 0 8 12 (@block_merge testT330r3 0 4 4 T330r3c0 T330r3c1) (@block_merge testT330r3 8 4 8 T330r3c2 (@block_merge testT330r3 12 4 4 T330r3c3 T330r3c4))) (@block_merge testT330r3 20 8 11 (@block_merge testT330r3 20 4 4 T330r3c5 T330r3c6) (@block_merge testT330r3 28 4 7 T330r3c7 (@block_merge testT330r3 32 4 3 T330r3c8 T330r3c9)))) (show checkBlock testT330r3 25 39 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T330r4p0 : RecordPage := #[
(0xc101e, 0xe14181), (0xd101e, 0x0), (0xe101e, 0x0), (0xf101e, 0x1e34589),
(0xc201e, 0x2e54991), (0xd201e, 0x0), (0xe201e, 0x0), (0xf201e, 0x3e74d99),
(0xc301e, 0x4e951a1), (0xd301e, 0x0), (0xe301e, 0x0), (0xf301e, 0x5eb55a9),
(0xc211e, 0x31), (0xd211e, 0x1ab3), (0xe211e, 0x1cb7), (0xf211e, 0x31),
(0xc311e, 0x3b), (0xd311e, 0x1fbd), (0xe311e, 0x21c1), (0xf311e, 0x3b),
(0xc321e, 0x45), (0xd321e, 0x24c7), (0xe321e, 0x26cb), (0xf321e, 0x45)]
def T330r4 : Records := #[T330r4p0]
def testT330r4 : ℕ → Bool := testAt T330 bsT330 3 T330r3 T330r4 1 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r4c0 : checkBlock testT330r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r4c1 : checkBlock testT330r4 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r4c2 : checkBlock testT330r4 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r4c3 : checkBlock testT330r4 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r4c4 : checkBlock testT330r4 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r4c5 : checkBlock testT330r4 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT330r4 : LayerOK T330 4 T330r4 := by
  apply layer_of_block (bs := bsT330) (k := 3) (old := T330r3) (cw := 1) (rw := 6) (by decide +kernel) vbsT330 vT330r3
  exact @block_merge testT330r4 0 24 8 (@block_merge testT330r4 0 12 12 (@block_merge testT330r4 0 4 8 T330r4c0 (@block_merge testT330r4 4 4 4 T330r4c1 T330r4c2)) (@block_merge testT330r4 12 4 8 T330r4c3 (@block_merge testT330r4 16 4 4 T330r4c4 T330r4c5))) (show checkBlock testT330r4 8 24 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T330r5p0 : RecordPage := #[
(0x1e, 0xbedae99e58e17dd6d95d54d13cd2c91c50c1)]
def T330r5 : Records := #[T330r5p0]
def testT330r5 : ℕ → Bool := testAt T330 bsT330 4 T330r4 T330r5 1 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T330r5c0 : checkBlock testT330r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT330r5 : LayerOK T330 5 T330r5 := by
  apply layer_of_block (bs := bsT330) (k := 4) (old := T330r4) (cw := 1) (rw := 5) (by decide +kernel) vbsT330 vT330r4
  exact @block_merge testT330r5 0 1 31 T330r5c0 (show checkBlock testT330r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT330 : Valid T330 := by
  apply bound_of_layers (bs := bsT330) (last := T330r5) (cw := 1) (rw := 0) (by decide +kernel) vbsT330 vT330r5 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T331 : Bound := ⟨0x333333330000, [0x0, 0x111111110000, 0x30303030000, 0x3300330000, 0x33330000], 0x111301110000, 6⟩
def bsT331 : Array Bound := [].toArray
theorem vbsT331 : ∀ s ∈ bsT331, Valid s := by
  intro s hs
  simp only [bsT331,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T331r3p0 : RecordPage := #[
(0x230c101e, 0x0), (0x330c101e, 0x0), (0x240c101e, 0x0), (0x340c101e, 0x0),
(0x30f101e, 0x0), (0x130f101e, 0x0), (0x40f101e, 0x0), (0x140f101e, 0x0),
(0x230c201e, 0x0), (0x330c201e, 0x0), (0x240c201e, 0x0), (0x340c201e, 0x0),
(0x30f201e, 0x0), (0x130f201e, 0x0), (0x40f201e, 0x0), (0x140f201e, 0x0),
(0x230d301e, 0x0), (0x330d301e, 0x0), (0x240d301e, 0x0), (0x340d301e, 0x0),
(0x230e301e, 0x0), (0x330e301e, 0x0), (0x240e301e, 0x0), (0x340e301e, 0x0),
(0x321c211e, 0x0), (0x240d211e, 0x0), (0x340d211e, 0x0), (0x240e211e, 0x0),
(0x340e211e, 0x0), (0x240c311e, 0x0), (0x340c311e, 0x0), (0x221d311e, 0x0)]
def T331r3p1 : RecordPage := #[
(0x40f311e, 0x0), (0x140f311e, 0x0), (0x240c321e, 0x0), (0x340c321e, 0x0),
(0x221d321e, 0x0), (0x40f321e, 0x0), (0x140f321e, 0x0)]
def T331r3 : Records := #[T331r3p0, T331r3p1]
def testT331r3 : ℕ → Bool := testAt T331 bsT331 2 (#[] : Records) T331r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r3c0 : checkBlock testT331r3 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r3c1 : checkBlock testT331r3 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r3c2 : checkBlock testT331r3 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r3c3 : checkBlock testT331r3 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r3c4 : checkBlock testT331r3 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r3c5 : checkBlock testT331r3 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r3c6 : checkBlock testT331r3 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r3c7 : checkBlock testT331r3 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r3c8 : checkBlock testT331r3 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r3c9 : checkBlock testT331r3 3 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT331r3 : LayerOK T331 3 T331r3 := by
  apply layer_of_block (bs := bsT331) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT331 (emptyOK _ _)
  exact @block_merge testT331r3 0 39 25 (@block_merge testT331r3 0 20 19 (@block_merge testT331r3 0 8 12 (@block_merge testT331r3 0 4 4 T331r3c0 T331r3c1) (@block_merge testT331r3 8 4 8 T331r3c2 (@block_merge testT331r3 12 4 4 T331r3c3 T331r3c4))) (@block_merge testT331r3 20 8 11 (@block_merge testT331r3 20 4 4 T331r3c5 T331r3c6) (@block_merge testT331r3 28 4 7 T331r3c7 (@block_merge testT331r3 32 4 3 T331r3c8 T331r3c9)))) (show checkBlock testT331r3 25 39 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T331r4p0 : RecordPage := #[
(0xc101e, 0xe14181), (0xd101e, 0x0), (0xe101e, 0x0), (0xf101e, 0x1e34589),
(0xc201e, 0x2e54991), (0xd201e, 0x0), (0xe201e, 0x0), (0xf201e, 0x3e74d99),
(0xc301e, 0x0), (0xd301e, 0x4e951a1), (0xe301e, 0x5eb55a9), (0xf301e, 0x0),
(0xc211e, 0x31), (0xd211e, 0x1ab3), (0xe211e, 0x1cb7), (0xf211e, 0x31),
(0xc311e, 0x1ebb), (0xd311e, 0x3f), (0xe311e, 0x3f), (0xf311e, 0x21c1),
(0xc321e, 0x23c5), (0xd321e, 0x49), (0xe321e, 0x49), (0xf321e, 0x26cb)]
def T331r4 : Records := #[T331r4p0]
def testT331r4 : ℕ → Bool := testAt T331 bsT331 3 T331r3 T331r4 1 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r4c0 : checkBlock testT331r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r4c1 : checkBlock testT331r4 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r4c2 : checkBlock testT331r4 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r4c3 : checkBlock testT331r4 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r4c4 : checkBlock testT331r4 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r4c5 : checkBlock testT331r4 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT331r4 : LayerOK T331 4 T331r4 := by
  apply layer_of_block (bs := bsT331) (k := 3) (old := T331r3) (cw := 1) (rw := 6) (by decide +kernel) vbsT331 vT331r3
  exact @block_merge testT331r4 0 24 8 (@block_merge testT331r4 0 12 12 (@block_merge testT331r4 0 4 8 T331r4c0 (@block_merge testT331r4 4 4 4 T331r4c1 T331r4c2)) (@block_merge testT331r4 12 4 8 T331r4c3 (@block_merge testT331r4 16 4 4 T331r4c4 T331r4c5))) (show checkBlock testT331r4 8 24 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T331r5p0 : RecordPage := #[
(0x1e, 0xbedae99e58e17dd6d95d54d13cd2c91c50c1)]
def T331r5 : Records := #[T331r5p0]
def testT331r5 : ℕ → Bool := testAt T331 bsT331 4 T331r4 T331r5 1 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T331r5c0 : checkBlock testT331r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT331r5 : LayerOK T331 5 T331r5 := by
  apply layer_of_block (bs := bsT331) (k := 4) (old := T331r4) (cw := 1) (rw := 5) (by decide +kernel) vbsT331 vT331r4
  exact @block_merge testT331r5 0 1 31 T331r5c0 (show checkBlock testT331r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT331 : Valid T331 := by
  apply bound_of_layers (bs := bsT331) (last := T331r5) (cw := 1) (rw := 0) (by decide +kernel) vbsT331 vT331r5 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T332 : Bound := ⟨0xa5a50000a5a5, [0x0, 0x50500000505, 0x212100002121, 0xa5000000a5, 0xa5a5], 0x10500000525, 6⟩
def bsT332 : Array Bound := [].toArray
theorem vbsT332 : ∀ s ∈ bsT332, Valid s := by
  intro s hs
  simp only [bsT332,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T332r3p0 : RecordPage := #[
(0x230c101e, 0x0), (0x330c101e, 0x0), (0x240c101e, 0x0), (0x340c101e, 0x0),
(0x30f101e, 0x0), (0x130f101e, 0x0), (0x40f101e, 0x0), (0x140f101e, 0x0),
(0x230c201e, 0x0), (0x330c201e, 0x0), (0x240c201e, 0x0), (0x340c201e, 0x0),
(0x30f201e, 0x0), (0x130f201e, 0x0), (0x40f201e, 0x0), (0x140f201e, 0x0),
(0x230c301e, 0x0), (0x330c301e, 0x0), (0x240c301e, 0x0), (0x340c301e, 0x0),
(0x30f301e, 0x0), (0x130f301e, 0x0), (0x40f301e, 0x0), (0x140f301e, 0x0),
(0x321c211e, 0x0), (0x240d211e, 0x0), (0x340d211e, 0x0), (0x240e211e, 0x0),
(0x340e211e, 0x0), (0x321c311e, 0x0), (0x240d311e, 0x0), (0x340d311e, 0x0)]
def T332r3p1 : RecordPage := #[
(0x240e311e, 0x0), (0x340e311e, 0x0), (0x321c321e, 0x0), (0x240d321e, 0x0),
(0x340d321e, 0x0), (0x240e321e, 0x0), (0x340e321e, 0x0)]
def T332r3 : Records := #[T332r3p0, T332r3p1]
def testT332r3 : ℕ → Bool := testAt T332 bsT332 2 (#[] : Records) T332r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r3c0 : checkBlock testT332r3 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r3c1 : checkBlock testT332r3 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r3c2 : checkBlock testT332r3 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r3c3 : checkBlock testT332r3 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r3c4 : checkBlock testT332r3 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r3c5 : checkBlock testT332r3 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r3c6 : checkBlock testT332r3 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r3c7 : checkBlock testT332r3 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r3c8 : checkBlock testT332r3 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r3c9 : checkBlock testT332r3 3 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT332r3 : LayerOK T332 3 T332r3 := by
  apply layer_of_block (bs := bsT332) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT332 (emptyOK _ _)
  exact @block_merge testT332r3 0 39 25 (@block_merge testT332r3 0 20 19 (@block_merge testT332r3 0 8 12 (@block_merge testT332r3 0 4 4 T332r3c0 T332r3c1) (@block_merge testT332r3 8 4 8 T332r3c2 (@block_merge testT332r3 12 4 4 T332r3c3 T332r3c4))) (@block_merge testT332r3 20 8 11 (@block_merge testT332r3 20 4 4 T332r3c5 T332r3c6) (@block_merge testT332r3 28 4 7 T332r3c7 (@block_merge testT332r3 32 4 3 T332r3c8 T332r3c9)))) (show checkBlock testT332r3 25 39 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T332r4p0 : RecordPage := #[
(0xc101e, 0xe14181), (0xd101e, 0x0), (0xe101e, 0x0), (0xf101e, 0x1e34589),
(0xc201e, 0x2e54991), (0xd201e, 0x0), (0xe201e, 0x0), (0xf201e, 0x3e74d99),
(0xc301e, 0x4e951a1), (0xd301e, 0x0), (0xe301e, 0x0), (0xf301e, 0x5eb55a9),
(0xc211e, 0x31), (0xd211e, 0x1ab3), (0xe211e, 0x1cb7), (0xf211e, 0x31),
(0xc311e, 0x3b), (0xd311e, 0x1fbd), (0xe311e, 0x21c1), (0xf311e, 0x3b),
(0xc321e, 0x45), (0xd321e, 0x24c7), (0xe321e, 0x26cb), (0xf321e, 0x45)]
def T332r4 : Records := #[T332r4p0]
def testT332r4 : ℕ → Bool := testAt T332 bsT332 3 T332r3 T332r4 1 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r4c0 : checkBlock testT332r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r4c1 : checkBlock testT332r4 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r4c2 : checkBlock testT332r4 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r4c3 : checkBlock testT332r4 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r4c4 : checkBlock testT332r4 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r4c5 : checkBlock testT332r4 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT332r4 : LayerOK T332 4 T332r4 := by
  apply layer_of_block (bs := bsT332) (k := 3) (old := T332r3) (cw := 1) (rw := 6) (by decide +kernel) vbsT332 vT332r3
  exact @block_merge testT332r4 0 24 8 (@block_merge testT332r4 0 12 12 (@block_merge testT332r4 0 4 8 T332r4c0 (@block_merge testT332r4 4 4 4 T332r4c1 T332r4c2)) (@block_merge testT332r4 12 4 8 T332r4c3 (@block_merge testT332r4 16 4 4 T332r4c4 T332r4c5))) (show checkBlock testT332r4 8 24 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T332r5p0 : RecordPage := #[
(0x1e, 0xbedae99e58e17dd6d95d54d13cd2c91c50c1)]
def T332r5 : Records := #[T332r5p0]
def testT332r5 : ℕ → Bool := testAt T332 bsT332 4 T332r4 T332r5 1 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T332r5c0 : checkBlock testT332r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT332r5 : LayerOK T332 5 T332r5 := by
  apply layer_of_block (bs := bsT332) (k := 4) (old := T332r4) (cw := 1) (rw := 5) (by decide +kernel) vbsT332 vT332r4
  exact @block_merge testT332r5 0 1 31 T332r5c0 (show checkBlock testT332r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT332 : Valid T332 := by
  apply bound_of_layers (bs := bsT332) (last := T332r5) (cw := 1) (rw := 0) (by decide +kernel) vbsT332 vT332r5 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T333 : Bound := ⟨0xcc330000cc33, [0x0, 0x441100004411, 0x3300000033, 0xc0300000c03, 0xcc33], 0x1300000433, 6⟩
def bsT333 : Array Bound := [].toArray
theorem vbsT333 : ∀ s ∈ bsT333, Valid s := by
  intro s hs
  simp only [bsT333,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T333r3p0 : RecordPage := #[
(0x230c101e, 0x0), (0x330c101e, 0x0), (0x240c101e, 0x0), (0x340c101e, 0x0),
(0x30f101e, 0x0), (0x130f101e, 0x0), (0x40f101e, 0x0), (0x140f101e, 0x0),
(0x321c201e, 0x0), (0x240d201e, 0x0), (0x340d201e, 0x0), (0x240e201e, 0x0),
(0x340e201e, 0x0), (0x321c301e, 0x0), (0x240d301e, 0x0), (0x340d301e, 0x0),
(0x240e301e, 0x0), (0x340e301e, 0x0), (0x230c211e, 0x0), (0x330c211e, 0x0),
(0x240c211e, 0x0), (0x340c211e, 0x0), (0x30f211e, 0x0), (0x130f211e, 0x0),
(0x40f211e, 0x0), (0x140f211e, 0x0), (0x230c311e, 0x0), (0x330c311e, 0x0),
(0x240c311e, 0x0), (0x340c311e, 0x0), (0x30f311e, 0x0), (0x130f311e, 0x0)]
def T333r3p1 : RecordPage := #[
(0x40f311e, 0x0), (0x140f311e, 0x0), (0x321c321e, 0x0), (0x230d321e, 0x0),
(0x330d321e, 0x0), (0x230e321e, 0x0), (0x330e321e, 0x0)]
def T333r3 : Records := #[T333r3p0, T333r3p1]
def testT333r3 : ℕ → Bool := testAt T333 bsT333 2 (#[] : Records) T333r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r3c0 : checkBlock testT333r3 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r3c1 : checkBlock testT333r3 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r3c2 : checkBlock testT333r3 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r3c3 : checkBlock testT333r3 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r3c4 : checkBlock testT333r3 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r3c5 : checkBlock testT333r3 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r3c6 : checkBlock testT333r3 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r3c7 : checkBlock testT333r3 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r3c8 : checkBlock testT333r3 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r3c9 : checkBlock testT333r3 3 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT333r3 : LayerOK T333 3 T333r3 := by
  apply layer_of_block (bs := bsT333) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT333 (emptyOK _ _)
  exact @block_merge testT333r3 0 39 25 (@block_merge testT333r3 0 20 19 (@block_merge testT333r3 0 8 12 (@block_merge testT333r3 0 4 4 T333r3c0 T333r3c1) (@block_merge testT333r3 8 4 8 T333r3c2 (@block_merge testT333r3 12 4 4 T333r3c3 T333r3c4))) (@block_merge testT333r3 20 8 11 (@block_merge testT333r3 20 4 4 T333r3c5 T333r3c6) (@block_merge testT333r3 28 4 7 T333r3c7 (@block_merge testT333r3 32 4 3 T333r3c8 T333r3c9)))) (show checkBlock testT333r3 25 39 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T333r4p0 : RecordPage := #[
(0xc101e, 0xe14181), (0xd101e, 0x0), (0xe101e, 0x0), (0xf101e, 0x1e34589),
(0xc201e, 0x11), (0xd201e, 0xa93), (0xe201e, 0xc97), (0xf201e, 0x11),
(0xc301e, 0x1b), (0xd301e, 0xf9d), (0xe301e, 0x11a1), (0xf301e, 0x1b),
(0xc211e, 0x56a53a5), (0xd211e, 0x0), (0xe211e, 0x0), (0xf211e, 0x66c57ad),
(0xc311e, 0x76e5bb5), (0xd311e, 0x0), (0xe311e, 0x0), (0xf311e, 0x8705fbd),
(0xc321e, 0x45), (0xd321e, 0x24c7), (0xe321e, 0x26cb), (0xf321e, 0x45)]
def T333r4 : Records := #[T333r4p0]
def testT333r4 : ℕ → Bool := testAt T333 bsT333 3 T333r3 T333r4 1 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r4c0 : checkBlock testT333r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r4c1 : checkBlock testT333r4 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r4c2 : checkBlock testT333r4 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r4c3 : checkBlock testT333r4 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r4c4 : checkBlock testT333r4 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r4c5 : checkBlock testT333r4 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT333r4 : LayerOK T333 4 T333r4 := by
  apply layer_of_block (bs := bsT333) (k := 3) (old := T333r3) (cw := 1) (rw := 6) (by decide +kernel) vbsT333 vT333r3
  exact @block_merge testT333r4 0 24 8 (@block_merge testT333r4 0 12 12 (@block_merge testT333r4 0 4 8 T333r4c0 (@block_merge testT333r4 4 4 4 T333r4c1 T333r4c2)) (@block_merge testT333r4 12 4 8 T333r4c3 (@block_merge testT333r4 16 4 4 T333r4c4 T333r4c5))) (show checkBlock testT333r4 8 24 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T333r5p0 : RecordPage := #[
(0x1e, 0xbedae99e58e17dd6d95d54d13cd2c91c50c1)]
def T333r5 : Records := #[T333r5p0]
def testT333r5 : ℕ → Bool := testAt T333 bsT333 4 T333r4 T333r5 1 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T333r5c0 : checkBlock testT333r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT333r5 : LayerOK T333 5 T333r5 := by
  apply layer_of_block (bs := bsT333) (k := 4) (old := T333r4) (cw := 1) (rw := 5) (by decide +kernel) vbsT333 vT333r4
  exact @block_merge testT333r5 0 1 31 T333r5c0 (show checkBlock testT333r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT333 : Valid T333 := by
  apply bound_of_layers (bs := bsT333) (last := T333r5) (cw := 1) (rw := 0) (by decide +kernel) vbsT333 vT333r5 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T334 : Bound := ⟨0x33003333003300, [0x0, 0x11001111001100, 0x3000303000300, 0x33003300, 0x3300003300], 0x11001301001100, 6⟩
def bsT334 : Array Bound := [].toArray
theorem vbsT334 : ∀ s ∈ bsT334, Valid s := by
  intro s hs
  simp only [bsT334,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T334r3p0 : RecordPage := #[
(0x230c101e, 0x0), (0x330c101e, 0x0), (0x240c101e, 0x0), (0x340c101e, 0x0),
(0x30f101e, 0x0), (0x130f101e, 0x0), (0x40f101e, 0x0), (0x140f101e, 0x0),
(0x230d201e, 0x0), (0x330d201e, 0x0), (0x240d201e, 0x0), (0x340d201e, 0x0),
(0x230e201e, 0x0), (0x330e201e, 0x0), (0x240e201e, 0x0), (0x340e201e, 0x0),
(0x230c301e, 0x0), (0x330c301e, 0x0), (0x240c301e, 0x0), (0x340c301e, 0x0),
(0x30f301e, 0x0), (0x130f301e, 0x0), (0x40f301e, 0x0), (0x140f301e, 0x0),
(0x240c211e, 0x0), (0x340c211e, 0x0), (0x221d211e, 0x0), (0x40f211e, 0x0),
(0x140f211e, 0x0), (0x321c311e, 0x0), (0x240d311e, 0x0), (0x340d311e, 0x0)]
def T334r3p1 : RecordPage := #[
(0x240e311e, 0x0), (0x340e311e, 0x0), (0x240c321e, 0x0), (0x340c321e, 0x0),
(0x221d321e, 0x0), (0x40f321e, 0x0), (0x140f321e, 0x0)]
def T334r3 : Records := #[T334r3p0, T334r3p1]
def testT334r3 : ℕ → Bool := testAt T334 bsT334 2 (#[] : Records) T334r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r3c0 : checkBlock testT334r3 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r3c1 : checkBlock testT334r3 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r3c2 : checkBlock testT334r3 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r3c3 : checkBlock testT334r3 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r3c4 : checkBlock testT334r3 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r3c5 : checkBlock testT334r3 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r3c6 : checkBlock testT334r3 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r3c7 : checkBlock testT334r3 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r3c8 : checkBlock testT334r3 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r3c9 : checkBlock testT334r3 3 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT334r3 : LayerOK T334 3 T334r3 := by
  apply layer_of_block (bs := bsT334) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT334 (emptyOK _ _)
  exact @block_merge testT334r3 0 39 25 (@block_merge testT334r3 0 20 19 (@block_merge testT334r3 0 8 12 (@block_merge testT334r3 0 4 4 T334r3c0 T334r3c1) (@block_merge testT334r3 8 4 8 T334r3c2 (@block_merge testT334r3 12 4 4 T334r3c3 T334r3c4))) (@block_merge testT334r3 20 8 11 (@block_merge testT334r3 20 4 4 T334r3c5 T334r3c6) (@block_merge testT334r3 28 4 7 T334r3c7 (@block_merge testT334r3 32 4 3 T334r3c8 T334r3c9)))) (show checkBlock testT334r3 25 39 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T334r4p0 : RecordPage := #[
(0xc101e, 0xe14181), (0xd101e, 0x0), (0xe101e, 0x0), (0xf101e, 0x1e34589),
(0xc201e, 0x0), (0xd201e, 0x2e54991), (0xe201e, 0x3e74d99), (0xf201e, 0x0),
(0xc301e, 0x4e951a1), (0xd301e, 0x0), (0xe301e, 0x0), (0xf301e, 0x5eb55a9),
(0xc211e, 0x19b1), (0xd211e, 0x35), (0xe211e, 0x35), (0xf211e, 0x1cb7),
(0xc311e, 0x3b), (0xd311e, 0x1fbd), (0xe311e, 0x21c1), (0xf311e, 0x3b),
(0xc321e, 0x23c5), (0xd321e, 0x49), (0xe321e, 0x49), (0xf321e, 0x26cb)]
def T334r4 : Records := #[T334r4p0]
def testT334r4 : ℕ → Bool := testAt T334 bsT334 3 T334r3 T334r4 1 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r4c0 : checkBlock testT334r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r4c1 : checkBlock testT334r4 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r4c2 : checkBlock testT334r4 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r4c3 : checkBlock testT334r4 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r4c4 : checkBlock testT334r4 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r4c5 : checkBlock testT334r4 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT334r4 : LayerOK T334 4 T334r4 := by
  apply layer_of_block (bs := bsT334) (k := 3) (old := T334r3) (cw := 1) (rw := 6) (by decide +kernel) vbsT334 vT334r3
  exact @block_merge testT334r4 0 24 8 (@block_merge testT334r4 0 12 12 (@block_merge testT334r4 0 4 8 T334r4c0 (@block_merge testT334r4 4 4 4 T334r4c1 T334r4c2)) (@block_merge testT334r4 12 4 8 T334r4c3 (@block_merge testT334r4 16 4 4 T334r4c4 T334r4c5))) (show checkBlock testT334r4 8 24 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T334r5p0 : RecordPage := #[
(0x1e, 0xbedae99e58e17dd6d95d54d13cd2c91c50c1)]
def T334r5 : Records := #[T334r5p0]
def testT334r5 : ℕ → Bool := testAt T334 bsT334 4 T334r4 T334r5 1 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T334r5c0 : checkBlock testT334r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT334r5 : LayerOK T334 5 T334r5 := by
  apply layer_of_block (bs := bsT334) (k := 4) (old := T334r4) (cw := 1) (rw := 5) (by decide +kernel) vbsT334 vT334r4
  exact @block_merge testT334r5 0 1 31 T334r5c0 (show checkBlock testT334r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT334 : Valid T334 := by
  apply bound_of_layers (bs := bsT334) (last := T334r5) (cw := 1) (rw := 0) (by decide +kernel) vbsT334 vT334r5 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T335 : Bound := ⟨0x2222222211111111, [0x0, 0x11111111, 0x202020201010101, 0x22002200110011, 0x222200001111], 0x201111111, 6⟩
def bsT335 : Array Bound := [].toArray
theorem vbsT335 : ∀ s ∈ bsT335, Valid s := by
  intro s hs
  simp only [bsT335,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T335r3p0 : RecordPage := #[
(0x230c101e, 0x0), (0x330c101e, 0x0), (0x240c101e, 0x0), (0x340c101e, 0x0),
(0x30f101e, 0x0), (0x130f101e, 0x0), (0x40f101e, 0x0), (0x140f101e, 0x0),
(0x230c201e, 0x0), (0x330c201e, 0x0), (0x240c201e, 0x0), (0x340c201e, 0x0),
(0x30f201e, 0x0), (0x130f201e, 0x0), (0x40f201e, 0x0), (0x140f201e, 0x0),
(0x230c301e, 0x0), (0x330c301e, 0x0), (0x240c301e, 0x0), (0x340c301e, 0x0),
(0x30f301e, 0x0), (0x130f301e, 0x0), (0x40f301e, 0x0), (0x140f301e, 0x0),
(0x321c211e, 0x0), (0x240d211e, 0x0), (0x340d211e, 0x0), (0x240e211e, 0x0),
(0x340e211e, 0x0), (0x321c311e, 0x0), (0x240d311e, 0x0), (0x340d311e, 0x0)]
def T335r3p1 : RecordPage := #[
(0x240e311e, 0x0), (0x340e311e, 0x0), (0x321c321e, 0x0), (0x240d321e, 0x0),
(0x340d321e, 0x0), (0x240e321e, 0x0), (0x340e321e, 0x0)]
def T335r3 : Records := #[T335r3p0, T335r3p1]
def testT335r3 : ℕ → Bool := testAt T335 bsT335 2 (#[] : Records) T335r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r3c0 : checkBlock testT335r3 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r3c1 : checkBlock testT335r3 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r3c2 : checkBlock testT335r3 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r3c3 : checkBlock testT335r3 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r3c4 : checkBlock testT335r3 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r3c5 : checkBlock testT335r3 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r3c6 : checkBlock testT335r3 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r3c7 : checkBlock testT335r3 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r3c8 : checkBlock testT335r3 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r3c9 : checkBlock testT335r3 3 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT335r3 : LayerOK T335 3 T335r3 := by
  apply layer_of_block (bs := bsT335) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT335 (emptyOK _ _)
  exact @block_merge testT335r3 0 39 25 (@block_merge testT335r3 0 20 19 (@block_merge testT335r3 0 8 12 (@block_merge testT335r3 0 4 4 T335r3c0 T335r3c1) (@block_merge testT335r3 8 4 8 T335r3c2 (@block_merge testT335r3 12 4 4 T335r3c3 T335r3c4))) (@block_merge testT335r3 20 8 11 (@block_merge testT335r3 20 4 4 T335r3c5 T335r3c6) (@block_merge testT335r3 28 4 7 T335r3c7 (@block_merge testT335r3 32 4 3 T335r3c8 T335r3c9)))) (show checkBlock testT335r3 25 39 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T335r4p0 : RecordPage := #[
(0xc101e, 0xe14181), (0xd101e, 0x0), (0xe101e, 0x0), (0xf101e, 0x1e34589),
(0xc201e, 0x2e54991), (0xd201e, 0x0), (0xe201e, 0x0), (0xf201e, 0x3e74d99),
(0xc301e, 0x4e951a1), (0xd301e, 0x0), (0xe301e, 0x0), (0xf301e, 0x5eb55a9),
(0xc211e, 0x31), (0xd211e, 0x1ab3), (0xe211e, 0x1cb7), (0xf211e, 0x31),
(0xc311e, 0x3b), (0xd311e, 0x1fbd), (0xe311e, 0x21c1), (0xf311e, 0x3b),
(0xc321e, 0x45), (0xd321e, 0x24c7), (0xe321e, 0x26cb), (0xf321e, 0x45)]
def T335r4 : Records := #[T335r4p0]
def testT335r4 : ℕ → Bool := testAt T335 bsT335 3 T335r3 T335r4 1 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r4c0 : checkBlock testT335r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r4c1 : checkBlock testT335r4 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r4c2 : checkBlock testT335r4 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r4c3 : checkBlock testT335r4 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r4c4 : checkBlock testT335r4 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r4c5 : checkBlock testT335r4 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT335r4 : LayerOK T335 4 T335r4 := by
  apply layer_of_block (bs := bsT335) (k := 3) (old := T335r3) (cw := 1) (rw := 6) (by decide +kernel) vbsT335 vT335r3
  exact @block_merge testT335r4 0 24 8 (@block_merge testT335r4 0 12 12 (@block_merge testT335r4 0 4 8 T335r4c0 (@block_merge testT335r4 4 4 4 T335r4c1 T335r4c2)) (@block_merge testT335r4 12 4 8 T335r4c3 (@block_merge testT335r4 16 4 4 T335r4c4 T335r4c5))) (show checkBlock testT335r4 8 24 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T335r5p0 : RecordPage := #[
(0x1e, 0xbedae99e58e17dd6d95d54d13cd2c91c50c1)]
def T335r5 : Records := #[T335r5p0]
def testT335r5 : ℕ → Bool := testAt T335 bsT335 4 T335r4 T335r5 1 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T335r5c0 : checkBlock testT335r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT335r5 : LayerOK T335 5 T335r5 := by
  apply layer_of_block (bs := bsT335) (k := 4) (old := T335r4) (cw := 1) (rw := 5) (by decide +kernel) vbsT335 vT335r4
  exact @block_merge testT335r5 0 1 31 T335r5c0 (show checkBlock testT335r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT335 : Valid T335 := by
  apply bound_of_layers (bs := bsT335) (last := T335r5) (cw := 1) (rw := 0) (by decide +kernel) vbsT335 vT335r5 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T336 : Bound := ⟨0x3030303003030303, [0x0, 0x1010101001010101, 0x3030303, 0x30003000030003, 0x303000000303], 0x10101001010103, 6⟩
def bsT336 : Array Bound := [].toArray
theorem vbsT336 : ∀ s ∈ bsT336, Valid s := by
  intro s hs
  simp only [bsT336,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T336r3p0 : RecordPage := #[
(0x230c101e, 0x0), (0x330c101e, 0x0), (0x240c101e, 0x0), (0x340c101e, 0x0),
(0x30f101e, 0x0), (0x130f101e, 0x0), (0x40f101e, 0x0), (0x140f101e, 0x0),
(0x230c201e, 0x0), (0x330c201e, 0x0), (0x240c201e, 0x0), (0x340c201e, 0x0),
(0x30f201e, 0x0), (0x130f201e, 0x0), (0x40f201e, 0x0), (0x140f201e, 0x0),
(0x230c301e, 0x0), (0x330c301e, 0x0), (0x240c301e, 0x0), (0x340c301e, 0x0),
(0x30f301e, 0x0), (0x130f301e, 0x0), (0x40f301e, 0x0), (0x140f301e, 0x0),
(0x321c211e, 0x0), (0x240d211e, 0x0), (0x340d211e, 0x0), (0x240e211e, 0x0),
(0x340e211e, 0x0), (0x321c311e, 0x0), (0x240d311e, 0x0), (0x340d311e, 0x0)]
def T336r3p1 : RecordPage := #[
(0x240e311e, 0x0), (0x340e311e, 0x0), (0x321c321e, 0x0), (0x240d321e, 0x0),
(0x340d321e, 0x0), (0x240e321e, 0x0), (0x340e321e, 0x0)]
def T336r3 : Records := #[T336r3p0, T336r3p1]
def testT336r3 : ℕ → Bool := testAt T336 bsT336 2 (#[] : Records) T336r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r3c0 : checkBlock testT336r3 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r3c1 : checkBlock testT336r3 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r3c2 : checkBlock testT336r3 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r3c3 : checkBlock testT336r3 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r3c4 : checkBlock testT336r3 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r3c5 : checkBlock testT336r3 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r3c6 : checkBlock testT336r3 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r3c7 : checkBlock testT336r3 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r3c8 : checkBlock testT336r3 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r3c9 : checkBlock testT336r3 3 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT336r3 : LayerOK T336 3 T336r3 := by
  apply layer_of_block (bs := bsT336) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT336 (emptyOK _ _)
  exact @block_merge testT336r3 0 39 25 (@block_merge testT336r3 0 20 19 (@block_merge testT336r3 0 8 12 (@block_merge testT336r3 0 4 4 T336r3c0 T336r3c1) (@block_merge testT336r3 8 4 8 T336r3c2 (@block_merge testT336r3 12 4 4 T336r3c3 T336r3c4))) (@block_merge testT336r3 20 8 11 (@block_merge testT336r3 20 4 4 T336r3c5 T336r3c6) (@block_merge testT336r3 28 4 7 T336r3c7 (@block_merge testT336r3 32 4 3 T336r3c8 T336r3c9)))) (show checkBlock testT336r3 25 39 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T336r4p0 : RecordPage := #[
(0xc101e, 0xe14181), (0xd101e, 0x0), (0xe101e, 0x0), (0xf101e, 0x1e34589),
(0xc201e, 0x2e54991), (0xd201e, 0x0), (0xe201e, 0x0), (0xf201e, 0x3e74d99),
(0xc301e, 0x4e951a1), (0xd301e, 0x0), (0xe301e, 0x0), (0xf301e, 0x5eb55a9),
(0xc211e, 0x31), (0xd211e, 0x1ab3), (0xe211e, 0x1cb7), (0xf211e, 0x31),
(0xc311e, 0x3b), (0xd311e, 0x1fbd), (0xe311e, 0x21c1), (0xf311e, 0x3b),
(0xc321e, 0x45), (0xd321e, 0x24c7), (0xe321e, 0x26cb), (0xf321e, 0x45)]
def T336r4 : Records := #[T336r4p0]
def testT336r4 : ℕ → Bool := testAt T336 bsT336 3 T336r3 T336r4 1 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r4c0 : checkBlock testT336r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r4c1 : checkBlock testT336r4 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r4c2 : checkBlock testT336r4 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r4c3 : checkBlock testT336r4 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r4c4 : checkBlock testT336r4 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r4c5 : checkBlock testT336r4 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT336r4 : LayerOK T336 4 T336r4 := by
  apply layer_of_block (bs := bsT336) (k := 3) (old := T336r3) (cw := 1) (rw := 6) (by decide +kernel) vbsT336 vT336r3
  exact @block_merge testT336r4 0 24 8 (@block_merge testT336r4 0 12 12 (@block_merge testT336r4 0 4 8 T336r4c0 (@block_merge testT336r4 4 4 4 T336r4c1 T336r4c2)) (@block_merge testT336r4 12 4 8 T336r4c3 (@block_merge testT336r4 16 4 4 T336r4c4 T336r4c5))) (show checkBlock testT336r4 8 24 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T336r5p0 : RecordPage := #[
(0x1e, 0xbedae99e58e17dd6d95d54d13cd2c91c50c1)]
def T336r5 : Records := #[T336r5p0]
def testT336r5 : ℕ → Bool := testAt T336 bsT336 4 T336r4 T336r5 1 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T336r5c0 : checkBlock testT336r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT336r5 : LayerOK T336 5 T336r5 := by
  apply layer_of_block (bs := bsT336) (k := 4) (old := T336r4) (cw := 1) (rw := 5) (by decide +kernel) vbsT336 vT336r4
  exact @block_merge testT336r5 0 1 31 T336r5c0 (show checkBlock testT336r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT336 : Valid T336 := by
  apply bound_of_layers (bs := bsT336) (last := T336r5) (cw := 1) (rw := 0) (by decide +kernel) vbsT336 vT336r5 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T337 : Bound := ⟨0x3333333300000000, [0x0, 0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000], 0x111111300000000, 6⟩
def bsT337 : Array Bound := [T93, T95, T96, T98, T100, T101].toArray
theorem vbsT337 : ∀ s ∈ bsT337, Valid s := by
  intro s hs
  simp only [bsT337,List.mem_toArray] at hs
  exact (familyCons vT93 <| familyCons vT95 <| familyCons vT96 <| familyCons vT98 <| familyCons vT100 <| familyCons vT101 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T337r4p0 : RecordPage := #[
(0xd101e, 0x0), (0xe101e, 0x0), (0xd201e, 0x0), (0xe201e, 0x0),
(0xd301e, 0x0), (0xe301e, 0x0), (0xc211e, 0x6), (0xf211e, 0x6),
(0xc311e, 0x8), (0xf311e, 0x8), (0xc321e, 0xa), (0xf321e, 0xa)]
def T337r4 : Records := #[T337r4p0]
def testT337r4 : ℕ → Bool := testAt T337 bsT337 3 (#[] : Records) T337r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T337r4c0 : checkBlock testT337r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T337r4c1 : checkBlock testT337r4 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T337r4c2 : checkBlock testT337r4 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT337r4 : LayerOK T337 4 T337r4 := by
  apply layer_of_block (bs := bsT337) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT337 (emptyOK _ _)
  exact @block_merge testT337r4 0 12 20 (@block_merge testT337r4 0 4 8 T337r4c0 (@block_merge testT337r4 4 4 4 T337r4c1 T337r4c2)) (show checkBlock testT337r4 20 12 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T337r5p0 : RecordPage := #[
(0x1e, 0xbd55671117b3341690239490614)]
def T337r5 : Records := #[T337r5p0]
def testT337r5 : ℕ → Bool := testAt T337 bsT337 4 T337r4 T337r5 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T337r5c0 : checkBlock testT337r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT337r5 : LayerOK T337 5 T337r5 := by
  apply layer_of_block (bs := bsT337) (k := 4) (old := T337r4) (cw := 3) (rw := 4) (by decide +kernel) vbsT337 vT337r4
  exact @block_merge testT337r5 0 1 31 T337r5c0 (show checkBlock testT337r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT337 : Valid T337 := by
  apply bound_of_layers (bs := bsT337) (last := T337r5) (cw := 3) (rw := 0) (by decide +kernel) vbsT337 vT337r5 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T338 : Bound := ⟨0x3333cccc00000000, [0x0, 0x1111444400000000, 0xcccc00000000, 0x3030c0c00000000, 0x3300cc00000000], 0x111000c00000000, 6⟩
def bsT338 : Array Bound := [T78, T80, T94].toArray
theorem vbsT338 : ∀ s ∈ bsT338, Valid s := by
  intro s hs
  simp only [bsT338,List.mem_toArray] at hs
  exact (familyCons vT78 <| familyCons vT80 <| familyCons vT94 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T338r2p0 : RecordPage := #[
(0x230a219101e, 0x0), (0x230a319101e, 0x0)]
def T338r2 : Records := #[T338r2p0]
def testT338r2 : ℕ → Bool := testAt T338 bsT338 1 (#[] : Records) T338r2 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T338r2c0 : checkBlock testT338r2 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT338r2 : LayerOK T338 2 T338r2 := by
  apply layer_of_block (bs := bsT338) (k := 1) (old := (#[] : Records)) (cw := 2) (rw := 1) (by decide +kernel) vbsT338 (emptyOK _ _)
  exact @block_merge testT338r2 0 2 30 T338r2c0 (show checkBlock testT338r2 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T338r3p0 : RecordPage := #[
(0x8219101e, 0x0), (0xa219101e, 0x1), (0x8319101e, 0x0), (0xa319101e, 0x3),
(0x230c211e, 0x0), (0x240e211e, 0x1), (0x230c311e, 0x0), (0x240e311e, 0x3)]
def T338r3 : Records := #[T338r3p0]
def testT338r3 : ℕ → Bool := testAt T338 bsT338 2 T338r2 T338r3 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T338r3c0 : checkBlock testT338r3 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T338r3c1 : checkBlock testT338r3 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT338r3 : LayerOK T338 3 T338r3 := by
  apply layer_of_block (bs := bsT338) (k := 2) (old := T338r2) (cw := 2) (rw := 1) (by decide +kernel) vbsT338 vT338r2
  exact @block_merge testT338r3 0 8 24 (@block_merge testT338r3 0 4 4 T338r3c0 T338r3c1) (show checkBlock testT338r3 24 8 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T338r4p0 : RecordPage := #[
(0x9101e, 0x1d4c64), (0xc211e, 0xc9), (0xe211e, 0x18b), (0xc311e, 0x2cd),
(0xe311e, 0x3af), (0xc321e, 0x0)]
def T338r4 : Records := #[T338r4p0]
def testT338r4 : ℕ → Bool := testAt T338 bsT338 3 T338r3 T338r4 2 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T338r4c0 : checkBlock testT338r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T338r4c1 : checkBlock testT338r4 2 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT338r4 : LayerOK T338 4 T338r4 := by
  apply layer_of_block (bs := bsT338) (k := 3) (old := T338r3) (cw := 2) (rw := 3) (by decide +kernel) vbsT338 vT338r3
  exact @block_merge testT338r4 0 6 26 (@block_merge testT338r4 0 4 2 T338r4c0 T338r4c1) (show checkBlock testT338r4 26 6 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T338r5p0 : RecordPage := #[
(0x1e, 0x85890e951c924924920c)]
def T338r5 : Records := #[T338r5p0]
def testT338r5 : ℕ → Bool := testAt T338 bsT338 4 T338r4 T338r5 2 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T338r5c0 : checkBlock testT338r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT338r5 : LayerOK T338 5 T338r5 := by
  apply layer_of_block (bs := bsT338) (k := 4) (old := T338r4) (cw := 2) (rw := 3) (by decide +kernel) vbsT338 vT338r4
  exact @block_merge testT338r5 0 1 31 T338r5c0 (show checkBlock testT338r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT338 : Valid T338 := by
  apply bound_of_layers (bs := bsT338) (last := T338r5) (cw := 2) (rw := 0) (by decide +kernel) vbsT338 vT338r5 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T339 : Bound := ⟨0x55aa55aa00000000, [0x0, 0xaa00aa00000000, 0x1122112200000000, 0x50a050a00000000, 0x55aa00000000], 0x100110a00000000, 6⟩
def bsT339 : Array Bound := [T76, T82, T95].toArray
theorem vbsT339 : ∀ s ∈ bsT339, Valid s := by
  intro s hs
  simp only [bsT339,List.mem_toArray] at hs
  exact (familyCons vT76 <| familyCons vT82 <| familyCons vT95 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T339r2p0 : RecordPage := #[
(0x230a216101e, 0x0), (0x230a316101e, 0x0)]
def T339r2 : Records := #[T339r2p0]
def testT339r2 : ℕ → Bool := testAt T339 bsT339 1 (#[] : Records) T339r2 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T339r2c0 : checkBlock testT339r2 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT339r2 : LayerOK T339 2 T339r2 := by
  apply layer_of_block (bs := bsT339) (k := 1) (old := (#[] : Records)) (cw := 2) (rw := 1) (by decide +kernel) vbsT339 (emptyOK _ _)
  exact @block_merge testT339r2 0 2 30 T339r2c0 (show checkBlock testT339r2 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T339r3p0 : RecordPage := #[
(0x8216101e, 0x0), (0xa216101e, 0x1), (0x8316101e, 0x0), (0xa316101e, 0x3),
(0x230c201e, 0x0), (0x240e201e, 0x1), (0x230c301e, 0x0), (0x240e301e, 0x3)]
def T339r3 : Records := #[T339r3p0]
def testT339r3 : ℕ → Bool := testAt T339 bsT339 2 T339r2 T339r3 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T339r3c0 : checkBlock testT339r3 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T339r3c1 : checkBlock testT339r3 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT339r3 : LayerOK T339 3 T339r3 := by
  apply layer_of_block (bs := bsT339) (k := 2) (old := T339r2) (cw := 2) (rw := 1) (by decide +kernel) vbsT339 vT339r2
  exact @block_merge testT339r3 0 8 24 (@block_merge testT339r3 0 4 4 T339r3c0 T339r3c1) (show checkBlock testT339r3 24 8 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T339r4p0 : RecordPage := #[
(0x6101e, 0x1d4c64), (0xc201e, 0xc9), (0xe201e, 0x18b), (0xc301e, 0x2cd),
(0xe301e, 0x3af), (0xc321e, 0x0)]
def T339r4 : Records := #[T339r4p0]
def testT339r4 : ℕ → Bool := testAt T339 bsT339 3 T339r3 T339r4 2 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T339r4c0 : checkBlock testT339r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T339r4c1 : checkBlock testT339r4 2 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT339r4 : LayerOK T339 4 T339r4 := by
  apply layer_of_block (bs := bsT339) (k := 3) (old := T339r3) (cw := 2) (rw := 3) (by decide +kernel) vbsT339 vT339r3
  exact @block_merge testT339r4 0 6 26 (@block_merge testT339r4 0 4 2 T339r4c0 T339r4c1) (show checkBlock testT339r4 26 6 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T339r5p0 : RecordPage := #[
(0x1e, 0x85c92492090e951c9064)]
def T339r5 : Records := #[T339r5p0]
def testT339r5 : ℕ → Bool := testAt T339 bsT339 4 T339r4 T339r5 2 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T339r5c0 : checkBlock testT339r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT339r5 : LayerOK T339 5 T339r5 := by
  apply layer_of_block (bs := bsT339) (k := 4) (old := T339r4) (cw := 2) (rw := 3) (by decide +kernel) vbsT339 vT339r4
  exact @block_merge testT339r5 0 1 31 T339r5c0 (show checkBlock testT339r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT339 : Valid T339 := by
  apply bound_of_layers (bs := bsT339) (last := T339r5) (cw := 2) (rw := 0) (by decide +kernel) vbsT339 vT339r5 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T340 : Bound := ⟨0x5a5a5a5a00000000, [0x0, 0xa0a0a0a00000000, 0x1212121200000000, 0x5a005a00000000, 0x5a5a00000000], 0x10101a00000000, 6⟩
def bsT340 : Array Bound := [T77, T79, T96].toArray
theorem vbsT340 : ∀ s ∈ bsT340, Valid s := by
  intro s hs
  simp only [bsT340,List.mem_toArray] at hs
  exact (familyCons vT77 <| familyCons vT79 <| familyCons vT96 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T340r2p0 : RecordPage := #[
(0x230a216101e, 0x0), (0x230a316101e, 0x0)]
def T340r2 : Records := #[T340r2p0]
def testT340r2 : ℕ → Bool := testAt T340 bsT340 1 (#[] : Records) T340r2 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T340r2c0 : checkBlock testT340r2 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT340r2 : LayerOK T340 2 T340r2 := by
  apply layer_of_block (bs := bsT340) (k := 1) (old := (#[] : Records)) (cw := 2) (rw := 1) (by decide +kernel) vbsT340 (emptyOK _ _)
  exact @block_merge testT340r2 0 2 30 T340r2c0 (show checkBlock testT340r2 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T340r3p0 : RecordPage := #[
(0x8216101e, 0x0), (0xa216101e, 0x1), (0x8316101e, 0x0), (0xa316101e, 0x3),
(0x230c201e, 0x0), (0x240e201e, 0x1), (0x230c301e, 0x0), (0x240e301e, 0x3)]
def T340r3 : Records := #[T340r3p0]
def testT340r3 : ℕ → Bool := testAt T340 bsT340 2 T340r2 T340r3 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T340r3c0 : checkBlock testT340r3 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T340r3c1 : checkBlock testT340r3 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT340r3 : LayerOK T340 3 T340r3 := by
  apply layer_of_block (bs := bsT340) (k := 2) (old := T340r2) (cw := 2) (rw := 1) (by decide +kernel) vbsT340 vT340r2
  exact @block_merge testT340r3 0 8 24 (@block_merge testT340r3 0 4 4 T340r3c0 T340r3c1) (show checkBlock testT340r3 24 8 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T340r4p0 : RecordPage := #[
(0x6101e, 0x1d4c64), (0xc201e, 0xc9), (0xe201e, 0x18b), (0xc301e, 0x2cd),
(0xe301e, 0x3af), (0xc321e, 0x0)]
def T340r4 : Records := #[T340r4p0]
def testT340r4 : ℕ → Bool := testAt T340 bsT340 3 T340r3 T340r4 2 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T340r4c0 : checkBlock testT340r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T340r4c1 : checkBlock testT340r4 2 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT340r4 : LayerOK T340 4 T340r4 := by
  apply layer_of_block (bs := bsT340) (k := 3) (old := T340r3) (cw := 2) (rw := 3) (by decide +kernel) vbsT340 vT340r3
  exact @block_merge testT340r4 0 6 26 (@block_merge testT340r4 0 4 2 T340r4c0 T340r4c1) (show checkBlock testT340r4 26 6 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T340r5p0 : RecordPage := #[
(0x1e, 0x85c92492090e951c9064)]
def T340r5 : Records := #[T340r5p0]
def testT340r5 : ℕ → Bool := testAt T340 bsT340 4 T340r4 T340r5 2 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T340r5c0 : checkBlock testT340r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT340r5 : LayerOK T340 5 T340r5 := by
  apply layer_of_block (bs := bsT340) (k := 4) (old := T340r4) (cw := 2) (rw := 3) (by decide +kernel) vbsT340 vT340r4
  exact @block_merge testT340r5 0 1 31 T340r5c0 (show checkBlock testT340r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT340 : Valid T340 := by
  apply bound_of_layers (bs := bsT340) (last := T340r5) (cw := 2) (rw := 0) (by decide +kernel) vbsT340 vT340r5 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T353 : Bound := ⟨0xff00ff00ff00ff0, [0x0, 0x550055005500550, 0x330033003300330, 0xf000f000f000f0, 0xff000000ff0, 0xff00ff0], 0x110011005100530, 6⟩
def bsT353 : Array Bound := [T286].toArray
theorem vbsT353 : ∀ s ∈ bsT353, Valid s := by
  intro s hs
  simp only [bsT353,List.mem_toArray] at hs
  exact (familyCons vT286 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT353 : Valid T353 := by
  apply bound_of_layers (bs := bsT353) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT353 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T354 : Bound := ⟨0x5555555555555555, [0x0, 0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555], 0x115111505151515, 6⟩
def bsT354 : Array Bound := [T313].toArray
theorem vbsT354 : ∀ s ∈ bsT354, Valid s := by
  intro s hs
  simp only [bsT354,List.mem_toArray] at hs
  exact (familyCons vT313 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT354 : Valid T354 := by
  apply bound_of_layers (bs := bsT354) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT354 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T357 : Bound := ⟨0xf0f0f0f0f0f0f0f0, [0x0, 0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0], 0x10101000101030, 6⟩
def bsT357 : Array Bound := [T285].toArray
theorem vbsT357 : ∀ s ∈ bsT357, Valid s := by
  intro s hs
  simp only [bsT357,List.mem_toArray] at hs
  exact (familyCons vT285 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT357 : Valid T357 := by
  apply bound_of_layers (bs := bsT357) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT357 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T358 : Bound := ⟨0xffff0000ffff0000, [0x0, 0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000], 0x115000005150000, 6⟩
def bsT358 : Array Bound := [T313].toArray
theorem vbsT358 : ∀ s ∈ bsT358, Valid s := by
  intro s hs
  simp only [bsT358,List.mem_toArray] at hs
  exact (familyCons vT313 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT358 : Valid T358 := by
  apply bound_of_layers (bs := bsT358) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT358 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T359 : Bound := ⟨0xffff0000ffff, [0x0, 0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff], 0x111f0000153f, 7⟩
def bsT359 : Array Bound := [T286, T287, T289, T290, T332, T333].toArray
theorem vbsT359 : ∀ s ∈ bsT359, Valid s := by
  intro s hs
  simp only [bsT359,List.mem_toArray] at hs
  exact (familyCons vT286 <| familyCons vT287 <| familyCons vT289 <| familyCons vT290 <| familyCons vT332 <| familyCons vT333 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T359r4p0 : RecordPage := #[
(0x350c403e, 0x0), (0x30f403e, 0x0), (0x340c413e, 0x0), (0x30f413e, 0x0),
(0x340c423e, 0x0), (0x50f423e, 0x0), (0x330c433e, 0x0), (0x50f433e, 0x0)]
def T359r4 : Records := #[T359r4p0]
def testT359r4 : ℕ → Bool := testAt T359 bsT359 3 (#[] : Records) T359r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T359r4c0 : checkBlock testT359r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T359r4c1 : checkBlock testT359r4 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT359r4 : LayerOK T359 4 T359r4 := by
  apply layer_of_block (bs := bsT359) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT359 (emptyOK _ _)
  exact @block_merge testT359r4 0 8 24 (@block_merge testT359r4 0 4 4 T359r4c0 T359r4c1) (show checkBlock testT359r4 24 8 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T359r5p0 : RecordPage := #[
(0xd103e, 0x0), (0xe103e, 0x0), (0xd303e, 0x0), (0xe303e, 0x0),
(0xc403e, 0x14), (0xd403e, 0x0), (0xe403e, 0x0), (0xf403e, 0x63),
(0xd213e, 0x0), (0xe213e, 0x0), (0xc413e, 0x52), (0xd413e, 0x0),
(0xe413e, 0x0), (0xf413e, 0x67), (0xd323e, 0x0), (0xe323e, 0x0),
(0xc423e, 0x92), (0xd423e, 0x0), (0xe423e, 0x0), (0xf423e, 0xb),
(0xc433e, 0xd4), (0xd433e, 0x0), (0xe433e, 0x0), (0xf433e, 0xf)]
def T359r5 : Records := #[T359r5p0]
def testT359r5 : ℕ → Bool := testAt T359 bsT359 4 T359r4 T359r5 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T359r5c0 : checkBlock testT359r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T359r5c1 : checkBlock testT359r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T359r5c2 : checkBlock testT359r5 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T359r5c3 : checkBlock testT359r5 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T359r5c4 : checkBlock testT359r5 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T359r5c5 : checkBlock testT359r5 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT359r5 : LayerOK T359 5 T359r5 := by
  apply layer_of_block (bs := bsT359) (k := 4) (old := T359r4) (cw := 3) (rw := 3) (by decide +kernel) vbsT359 vT359r4
  exact @block_merge testT359r5 0 24 8 (@block_merge testT359r5 0 12 12 (@block_merge testT359r5 0 4 8 T359r5c0 (@block_merge testT359r5 4 4 4 T359r5c1 T359r5c2)) (@block_merge testT359r5 12 4 8 T359r5c3 (@block_merge testT359r5 16 4 4 T359r5c4 T359r5c5))) (show checkBlock testT359r5 8 24 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T359r6p0 : RecordPage := #[
(0x3e, 0xbedae99e58e107dd06d95d5aaaa24d123cd2c941c54888860c16)]
def T359r6 : Records := #[T359r6p0]
def testT359r6 : ℕ → Bool := testAt T359 bsT359 5 T359r5 T359r6 3 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T359r6c0 : checkBlock testT359r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT359r6 : LayerOK T359 6 T359r6 := by
  apply layer_of_block (bs := bsT359) (k := 5) (old := T359r5) (cw := 3) (rw := 5) (by decide +kernel) vbsT359 vT359r5
  exact @block_merge testT359r6 0 1 31 T359r6c0 (show checkBlock testT359r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT359 : Valid T359 := by
  apply bound_of_layers (bs := bsT359) (last := T359r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT359 vT359r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T360 : Bound := ⟨0xffffffff0000, [0x0, 0x555555550000, 0x333333330000, 0xf0f0f0f0000, 0xff00ff0000, 0xffff0000], 0x111f05150000, 7⟩
def bsT360 : Array Bound := [T331].toArray
theorem vbsT360 : ∀ s ∈ bsT360, Valid s := by
  intro s hs
  simp only [bsT360,List.mem_toArray] at hs
  exact (familyCons vT331 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT360 : Valid T360 := by
  apply bound_of_layers (bs := bsT360) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT360 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T361 : Bound := ⟨0xff00ffff00ff00, [0x0, 0x55005555005500, 0x33003333003300, 0xf000f0f000f00, 0xff00ff00, 0xff0000ff00], 0x15001f05001500, 7⟩
def bsT361 : Array Bound := [T334].toArray
theorem vbsT361 : ∀ s ∈ bsT361, Valid s := by
  intro s hs
  simp only [bsT361,List.mem_toArray] at hs
  exact (familyCons vT334 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT361 : Valid T361 := by
  apply bound_of_layers (bs := bsT361) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT361 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T362 : Bound := ⟨0xf0ff0f00f0ff0f0, [0x0, 0x505505005055050, 0x303303003033030, 0xf0f00000f0f0, 0xf00f0000f00f0, 0xf0ff0f0], 0x105101005051030, 7⟩
def bsT362 : Array Bound := [T68, T237, T257].toArray
theorem vbsT362 : ∀ s ∈ bsT362, Valid s := by
  intro s hs
  simp only [bsT362,List.mem_toArray] at hs
  exact (familyCons vT68 <| familyCons vT237 <| familyCons vT257 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T362r4p0 : RecordPage := #[
(0x230c103e, 0x0), (0x330c103e, 0x0), (0x240c103e, 0x0), (0x250c103e, 0x0),
(0x30f103e, 0x0), (0x130f103e, 0x0), (0x40f103e, 0x0), (0x50f103e, 0x0),
(0x240c203e, 0x0), (0x250c203e, 0x0), (0x30f203e, 0x0), (0x130f203e, 0x0),
(0x40f203e, 0x0), (0x50f203e, 0x0), (0x250c303e, 0x0), (0x250c403e, 0x0),
(0x240d213e, 0x0), (0x250d213e, 0x0), (0x230e213e, 0x0), (0x330e213e, 0x0),
(0x240e213e, 0x0), (0x250e213e, 0x0), (0x250e313e, 0x0), (0x250e413e, 0x0),
(0x240e323e, 0x0), (0x340e323e, 0x0), (0x250e323e, 0x0), (0x240e423e, 0x0),
(0x340e423e, 0x0), (0x250e423e, 0x0)]
def T362r4 : Records := #[T362r4p0]
def testT362r4 : ℕ → Bool := testAt T362 bsT362 3 (#[] : Records) T362r4 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r4c0 : checkBlock testT362r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r4c1 : checkBlock testT362r4 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r4c2 : checkBlock testT362r4 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r4c3 : checkBlock testT362r4 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r4c4 : checkBlock testT362r4 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r4c5 : checkBlock testT362r4 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r4c6 : checkBlock testT362r4 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r4c7 : checkBlock testT362r4 2 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT362r4 : LayerOK T362 4 T362r4 := by
  apply layer_of_block (bs := bsT362) (k := 3) (old := (#[] : Records)) (cw := 2) (rw := 1) (by decide +kernel) vbsT362 (emptyOK _ _)
  exact @block_merge testT362r4 0 30 2 (@block_merge testT362r4 0 16 14 (@block_merge testT362r4 0 8 8 (@block_merge testT362r4 0 4 4 T362r4c0 T362r4c1) (@block_merge testT362r4 8 4 4 T362r4c2 T362r4c3)) (@block_merge testT362r4 16 8 6 (@block_merge testT362r4 16 4 4 T362r4c4 T362r4c5) (@block_merge testT362r4 24 4 2 T362r4c6 T362r4c7))) (show checkBlock testT362r4 2 30 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T362r5p0 : RecordPage := #[
(0xc103e, 0x10f050c1), (0xd103e, 0x0), (0xe103e, 0x0), (0xf103e, 0x11f0d2c9),
(0xc203e, 0x12711), (0xd203e, 0x0), (0xe203e, 0x0), (0xf203e, 0x137195d5),
(0xc303e, 0x9d), (0xe303e, 0x0), (0xc403e, 0x11f), (0xe403e, 0x0),
(0xc213e, 0x0), (0xd213e, 0x14721), (0xe213e, 0x157299e5), (0xf213e, 0x0),
(0xc313e, 0x0), (0xe313e, 0xad), (0xc413e, 0x0), (0xe413e, 0x12f),
(0xc323e, 0x0), (0xe323e, 0xb5cf1), (0xc423e, 0x0), (0xe423e, 0x13be77)]
def T362r5 : Records := #[T362r5p0]
def testT362r5 : ℕ → Bool := testAt T362 bsT362 4 T362r4 T362r5 2 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r5c0 : checkBlock testT362r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r5c1 : checkBlock testT362r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r5c2 : checkBlock testT362r5 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r5c3 : checkBlock testT362r5 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r5c4 : checkBlock testT362r5 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r5c5 : checkBlock testT362r5 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT362r5 : LayerOK T362 5 T362r5 := by
  apply layer_of_block (bs := bsT362) (k := 4) (old := T362r4) (cw := 2) (rw := 5) (by decide +kernel) vbsT362 vT362r4
  exact @block_merge testT362r5 0 24 8 (@block_merge testT362r5 0 12 12 (@block_merge testT362r5 0 4 8 T362r5c0 (@block_merge testT362r5 4 4 4 T362r5c1 T362r5c2)) (@block_merge testT362r5 12 4 8 T362r5c3 (@block_merge testT362r5 16 4 4 T362r5c4 T362r5c5))) (show checkBlock testT362r5 8 24 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T362r6p0 : RecordPage := #[
(0x3e, 0x51057ab6572953a9647217dd6d94ba5627113cd2c91c50c1)]
def T362r6 : Records := #[T362r6p0]
def testT362r6 : ℕ → Bool := testAt T362 bsT362 5 T362r5 T362r6 2 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T362r6c0 : checkBlock testT362r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT362r6 : LayerOK T362 6 T362r6 := by
  apply layer_of_block (bs := bsT362) (k := 5) (old := T362r5) (cw := 2) (rw := 5) (by decide +kernel) vbsT362 vT362r5
  exact @block_merge testT362r6 0 1 31 T362r6c0 (show checkBlock testT362r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT362 : Valid T362 := by
  apply bound_of_layers (bs := bsT362) (last := T362r6) (cw := 2) (rw := 0) (by decide +kernel) vbsT362 vT362r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T363 : Bound := ⟨0x3333333333333333, [0x0, 0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333], 0x111111301111133, 7⟩
def bsT363 : Array Bound := [T337].toArray
theorem vbsT363 : ∀ s ∈ bsT363, Valid s := by
  intro s hs
  simp only [bsT363,List.mem_toArray] at hs
  exact (familyCons vT337 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT363 : Valid T363 := by
  apply bound_of_layers (bs := bsT363) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT363 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T364 : Bound := ⟨0x33333333cccccccc, [0x0, 0x1111111144444444, 0xcccccccc, 0x30303030c0c0c0c, 0x33003300cc00cc, 0x33330000cccc], 0x11111130404040c, 7⟩
def bsT364 : Array Bound := [T337].toArray
theorem vbsT364 : ∀ s ∈ bsT364, Valid s := by
  intro s hs
  simp only [bsT364,List.mem_toArray] at hs
  exact (familyCons vT337 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT364 : Valid T364 := by
  apply bound_of_layers (bs := bsT364) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT364 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T365 : Bound := ⟨0x3333cccc3333cccc, [0x0, 0x1111444411114444, 0xcccc0000cccc, 0x3030c0c03030c0c, 0x3300cc003300cc, 0x3333cccc], 0x111000c0111040c, 7⟩
def bsT365 : Array Bound := [T338].toArray
theorem vbsT365 : ∀ s ∈ bsT365, Valid s := by
  intro s hs
  simp only [bsT365,List.mem_toArray] at hs
  exact (familyCons vT338 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT365 : Valid T365 := by
  apply bound_of_layers (bs := bsT365) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT365 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T366 : Bound := ⟨0x5555aaaa5555aaaa, [0x0, 0xaaaa0000aaaa, 0x1111222211112222, 0x5050a0a05050a0a, 0x5500aa005500aa, 0x5555aaaa], 0x115000a0515002a, 7⟩
def bsT366 : Array Bound := [T89, T105, T298, T313, T316].toArray
theorem vbsT366 : ∀ s ∈ bsT366, Valid s := by
  intro s hs
  simp only [bsT366,List.mem_toArray] at hs
  exact (familyCons vT89 <| familyCons vT105 <| familyCons vT298 <| familyCons vT313 <| familyCons vT316 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T366r4p0 : RecordPage := #[
(0x330c323e, 0x0), (0x240c323e, 0x0), (0x130f323e, 0x0), (0x40f323e, 0x0)]
def T366r4 : Records := #[T366r4p0]
def testT366r4 : ℕ → Bool := testAt T366 bsT366 3 (#[] : Records) T366r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T366r4c0 : checkBlock testT366r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT366r4 : LayerOK T366 4 T366r4 := by
  apply layer_of_block (bs := bsT366) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT366 (emptyOK _ _)
  exact @block_merge testT366r4 0 4 28 T366r4c0 (show checkBlock testT366r4 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T366r5p0 : RecordPage := #[
(0xc323e, 0xa1196), (0xd323e, 0x0), (0xe323e, 0x0), (0xf323e, 0x213d6)]
def T366r5 : Records := #[T366r5p0]
def testT366r5 : ℕ → Bool := testAt T366 bsT366 4 T366r4 T366r5 3 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T366r5c0 : checkBlock testT366r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT366r5 : LayerOK T366 5 T366r5 := by
  apply layer_of_block (bs := bsT366) (k := 4) (old := T366r4) (cw := 3) (rw := 2) (by decide +kernel) vbsT366 vT366r4
  exact @block_merge testT366r5 0 4 28 T366r5c0 (show checkBlock testT366r5 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T366r6p0 : RecordPage := #[
(0x3e, 0x88888888f594444444444446666666666664444)]
def T366r6 : Records := #[T366r6p0]
def testT366r6 : ℕ → Bool := testAt T366 bsT366 5 T366r5 T366r6 3 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T366r6c0 : checkBlock testT366r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT366r6 : LayerOK T366 6 T366r6 := by
  apply layer_of_block (bs := bsT366) (k := 5) (old := T366r5) (cw := 3) (rw := 2) (by decide +kernel) vbsT366 vT366r5
  exact @block_merge testT366r6 0 1 31 T366r6c0 (show checkBlock testT366r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT366 : Valid T366 := by
  apply bound_of_layers (bs := bsT366) (last := T366r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT366 vT366r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T367 : Bound := ⟨0x6666666666666666, [0x0, 0x2222222222222222, 0x606060606060606, 0x66006600660066, 0x666600006666, 0x66666666], 0x4000604040426, 7⟩
def bsT367 : Array Bound := [T71, T241, T259, T266, T290].toArray
theorem vbsT367 : ∀ s ∈ bsT367, Valid s := by
  intro s hs
  simp only [bsT367,List.mem_toArray] at hs
  exact (familyCons vT71 <| familyCons vT241 <| familyCons vT259 <| familyCons vT266 <| familyCons vT290 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T367r4p0 : RecordPage := #[
(0x250c103e, 0x0), (0x41c103e, 0x0), (0x240e103e, 0x0), (0x41e103e, 0x0),
(0x40c203e, 0x0), (0x240e203e, 0x0), (0x250e203e, 0x0), (0x42e203e, 0x28),
(0xa304303e, 0x0), (0x230c403e, 0x0), (0x240e403e, 0x0), (0x250e403e, 0x0),
(0x250c213e, 0x0), (0x42c213e, 0x2), (0xa204323e, 0x8)]
def T367r4 : Records := #[T367r4p0]
def testT367r4 : ℕ → Bool := testAt T367 bsT367 3 (#[] : Records) T367r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T367r4c0 : checkBlock testT367r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T367r4c1 : checkBlock testT367r4 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T367r4c2 : checkBlock testT367r4 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T367r4c3 : checkBlock testT367r4 3 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT367r4 : LayerOK T367 4 T367r4 := by
  apply layer_of_block (bs := bsT367) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT367 (emptyOK _ _)
  exact @block_merge testT367r4 0 15 17 (@block_merge testT367r4 0 8 7 (@block_merge testT367r4 0 4 4 T367r4c0 T367r4c1) (@block_merge testT367r4 8 4 3 T367r4c2 T367r4c3)) (show checkBlock testT367r4 17 15 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T367r5p0 : RecordPage := #[
(0xc103e, 0x641), (0xe103e, 0xf05), (0xc203e, 0x109), (0xe203e, 0x3c9b0b),
(0x4303e, 0x38e2988), (0xc403e, 0x10d3), (0xe403e, 0x222e95), (0xc213e, 0x3659),
(0xc413e, 0x0), (0x4323e, 0x224da3fa988)]
def T367r5 : Records := #[T367r5p0]
def testT367r5 : ℕ → Bool := testAt T367 bsT367 4 T367r4 T367r5 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T367r5c0 : checkBlock testT367r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T367r5c1 : checkBlock testT367r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T367r5c2 : checkBlock testT367r5 2 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT367r5 : LayerOK T367 5 T367r5 := by
  apply layer_of_block (bs := bsT367) (k := 4) (old := T367r4) (cw := 3) (rw := 4) (by decide +kernel) vbsT367 vT367r4
  exact @block_merge testT367r5 0 10 22 (@block_merge testT367r5 0 4 6 T367r5c0 (@block_merge testT367r5 4 4 2 T367r5c1 T367r5c2)) (show checkBlock testT367r5 22 10 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T367r6p0 : RecordPage := #[
(0x3e, 0x2222090822222264c51888846479349711110943a1586c1)]
def T367r6 : Records := #[T367r6p0]
def testT367r6 : ℕ → Bool := testAt T367 bsT367 5 T367r5 T367r6 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T367r6c0 : checkBlock testT367r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT367r6 : LayerOK T367 6 T367r6 := by
  apply layer_of_block (bs := bsT367) (k := 5) (old := T367r5) (cw := 3) (rw := 4) (by decide +kernel) vbsT367 vT367r5
  exact @block_merge testT367r6 0 1 31 T367r6c0 (show checkBlock testT367r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT367 : Valid T367 := by
  apply bound_of_layers (bs := bsT367) (last := T367r6) (cw := 3) (rw := 0) (by decide +kernel) vbsT367 vT367r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T368 : Bound := ⟨0xa5a5a5a5a5a5a5a5, [0x0, 0x505050505050505, 0x2121212121212121, 0xa500a500a500a5, 0xa5a50000a5a5, 0xa5a5a5a5], 0x105010505050525, 7⟩
def bsT368 : Array Bound := [T332].toArray
theorem vbsT368 : ∀ s ∈ bsT368, Valid s := by
  intro s hs
  simp only [bsT368,List.mem_toArray] at hs
  exact (familyCons vT332 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT368 : Valid T368 := by
  apply bound_of_layers (bs := bsT368) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT368 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T369 : Bound := ⟨0xaaaaaaaa55555555, [0x0, 0x55555555, 0x2222222211111111, 0xa0a0a0a05050505, 0xaa00aa00550055, 0xaaaa00005555], 0xa05151515, 7⟩
def bsT369 : Array Bound := [T335].toArray
theorem vbsT369 : ∀ s ∈ bsT369, Valid s := by
  intro s hs
  simp only [bsT369,List.mem_toArray] at hs
  exact (familyCons vT335 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT369 : Valid T369 := by
  apply bound_of_layers (bs := bsT369) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT369 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T370 : Bound := ⟨0xcc33cc33cc33cc33, [0x0, 0x4411441144114411, 0x33003300330033, 0xc030c030c030c03, 0xcc330000cc33, 0xcc33cc33], 0x11001304110433, 7⟩
def bsT370 : Array Bound := [T333].toArray
theorem vbsT370 : ∀ s ∈ bsT370, Valid s := by
  intro s hs
  simp only [bsT370,List.mem_toArray] at hs
  exact (familyCons vT333 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT370 : Valid T370 := by
  apply bound_of_layers (bs := bsT370) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT370 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T371 : Bound := ⟨0xcccc3333cccc3333, [0x0, 0x4444111144441111, 0x333300003333, 0xc0c03030c0c0303, 0xcc003300cc0033, 0xcccc3333], 0x4111304041133, 7⟩
def bsT371 : Array Bound := [T243, T291, T294, T320].toArray
theorem vbsT371 : ∀ s ∈ bsT371, Valid s := by
  intro s hs
  simp only [bsT371,List.mem_toArray] at hs
  exact (familyCons vT243 <| familyCons vT291 <| familyCons vT294 <| familyCons vT320 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T371r4p0 : RecordPage := #[
(0x230c103e, 0x0), (0x240c103e, 0x0), (0x30f103e, 0x0), (0x40f103e, 0x0)]
def T371r4 : Records := #[T371r4p0]
def testT371r4 : ℕ → Bool := testAt T371 bsT371 3 (#[] : Records) T371r4 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T371r4c0 : checkBlock testT371r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT371r4 : LayerOK T371 4 T371r4 := by
  apply layer_of_block (bs := bsT371) (k := 3) (old := (#[] : Records)) (cw := 2) (rw := 1) (by decide +kernel) vbsT371 (emptyOK _ _)
  exact @block_merge testT371r4 0 4 28 T371r4c0 (show checkBlock testT371r4 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T371r5p0 : RecordPage := #[
(0xc103e, 0x64e1), (0xd103e, 0x0), (0xe103e, 0x0), (0xf103e, 0x65e5)]
def T371r5 : Records := #[T371r5p0]
def testT371r5 : ℕ → Bool := testAt T371 bsT371 4 T371r4 T371r5 2 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T371r5c0 : checkBlock testT371r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT371r5 : LayerOK T371 5 T371r5 := by
  apply layer_of_block (bs := bsT371) (k := 4) (old := T371r4) (cw := 2) (rw := 2) (by decide +kernel) vbsT371 vT371r4
  exact @block_merge testT371r5 0 4 28 T371r5c0 (show checkBlock testT371r5 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T371r6p0 : RecordPage := #[
(0x3e, 0x492924492db6492924db6492924f59)]
def T371r6 : Records := #[T371r6p0]
def testT371r6 : ℕ → Bool := testAt T371 bsT371 5 T371r5 T371r6 2 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T371r6c0 : checkBlock testT371r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT371r6 : LayerOK T371 6 T371r6 := by
  apply layer_of_block (bs := bsT371) (k := 5) (old := T371r5) (cw := 2) (rw := 2) (by decide +kernel) vbsT371 vT371r5
  exact @block_merge testT371r6 0 1 31 T371r6c0 (show checkBlock testT371r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT371 : Valid T371 := by
  apply bound_of_layers (bs := bsT371) (last := T371r6) (cw := 2) (rw := 0) (by decide +kernel) vbsT371 vT371r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T372 : Bound := ⟨0xf0f00f0ff0f00f0f, [0x0, 0x5050050550500505, 0x3030030330300303, 0xf0f00000f0f, 0xf0000f00f0000f, 0xf0f00f0f], 0x10010f0010050f, 7⟩
def bsT372 : Array Bound := [T86, T284, T308, T324].toArray
theorem vbsT372 : ∀ s ∈ bsT372, Valid s := by
  intro s hs
  simp only [bsT372,List.mem_toArray] at hs
  exact (familyCons vT86 <| familyCons vT284 <| familyCons vT308 <| familyCons vT324 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T372r4p0 : RecordPage := #[
(0x230c323e, 0x0), (0x240c323e, 0x0), (0x30f323e, 0x0), (0x40f323e, 0x0)]
def T372r4 : Records := #[T372r4p0]
def testT372r4 : ℕ → Bool := testAt T372 bsT372 3 (#[] : Records) T372r4 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T372r4c0 : checkBlock testT372r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT372r4 : LayerOK T372 4 T372r4 := by
  apply layer_of_block (bs := bsT372) (k := 3) (old := (#[] : Records)) (cw := 2) (rw := 1) (by decide +kernel) vbsT372 (emptyOK _ _)
  exact @block_merge testT372r4 0 4 28 T372r4c0 (show checkBlock testT372r4 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T372r5p0 : RecordPage := #[
(0xc323e, 0x160e1), (0xd323e, 0x16), (0xe323e, 0x16), (0xf323e, 0x161e5)]
def T372r5 : Records := #[T372r5p0]
def testT372r5 : ℕ → Bool := testAt T372 bsT372 4 T372r4 T372r5 2 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T372r5c0 : checkBlock testT372r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT372r5 : LayerOK T372 5 T372r5 := by
  apply layer_of_block (bs := bsT372) (k := 4) (old := T372r4) (cw := 2) (rw := 2) (by decide +kernel) vbsT372 vT372r4
  exact @block_merge testT372r5 0 4 28 T372r5c0 (show checkBlock testT372r5 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T372r6p0 : RecordPage := #[
(0x3e, 0x125924925bd652592000000492524924924924)]
def T372r6 : Records := #[T372r6p0]
def testT372r6 : ℕ → Bool := testAt T372 bsT372 5 T372r5 T372r6 2 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T372r6c0 : checkBlock testT372r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT372r6 : LayerOK T372 6 T372r6 := by
  apply layer_of_block (bs := bsT372) (k := 5) (old := T372r5) (cw := 2) (rw := 2) (by decide +kernel) vbsT372 vT372r5
  exact @block_merge testT372r6 0 1 31 T372r6c0 (show checkBlock testT372r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT372 : Valid T372 := by
  apply bound_of_layers (bs := bsT372) (last := T372r6) (cw := 2) (rw := 0) (by decide +kernel) vbsT372 vT372r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T373 : Bound := ⟨0xf0f0f0f00f0f0f0f, [0x0, 0x5050505005050505, 0x3030303003030303, 0xf0f0f0f, 0xf000f0000f000f, 0xf0f000000f0f], 0x1010100505050f, 7⟩
def bsT373 : Array Bound := [T336].toArray
theorem vbsT373 : ∀ s ∈ bsT373, Valid s := by
  intro s hs
  simp only [bsT373,List.mem_toArray] at hs
  exact (familyCons vT336 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT373 : Valid T373 := by
  apply bound_of_layers (bs := bsT373) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT373 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T374 : Bound := ⟨0xff0000ffff0000ff, [0x0, 0x5500005555000055, 0x3300003333000033, 0xf00000f0f00000f, 0xff000000ff, 0xff0000ff], 0x100001f0500003f, 7⟩
def bsT374 : Array Bound := [T244, T302, T310, T327].toArray
theorem vbsT374 : ∀ s ∈ bsT374, Valid s := by
  intro s hs
  simp only [bsT374,List.mem_toArray] at hs
  exact (familyCons vT244 <| familyCons vT302 <| familyCons vT310 <| familyCons vT327 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T374r4p0 : RecordPage := #[
(0x230c323e, 0x0), (0x240c323e, 0x0), (0x30f323e, 0x0), (0x40f323e, 0x0)]
def T374r4 : Records := #[T374r4p0]
def testT374r4 : ℕ → Bool := testAt T374 bsT374 3 (#[] : Records) T374r4 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T374r4c0 : checkBlock testT374r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT374r4 : LayerOK T374 4 T374r4 := by
  apply layer_of_block (bs := bsT374) (k := 3) (old := (#[] : Records)) (cw := 2) (rw := 1) (by decide +kernel) vbsT374 (emptyOK _ _)
  exact @block_merge testT374r4 0 4 28 T374r4c0 (show checkBlock testT374r4 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T374r5p0 : RecordPage := #[
(0xc323e, 0x64e1), (0xd323e, 0x0), (0xe323e, 0x0), (0xf323e, 0x65e5)]
def T374r5 : Records := #[T374r5p0]
def testT374r5 : ℕ → Bool := testAt T374 bsT374 4 T374r4 T374r5 2 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T374r5c0 : checkBlock testT374r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT374r5 : LayerOK T374 5 T374r5 := by
  apply layer_of_block (bs := bsT374) (k := 4) (old := T374r4) (cw := 2) (rw := 2) (by decide +kernel) vbsT374 vT374r4
  exact @block_merge testT374r5 0 4 28 T374r5c0 (show checkBlock testT374r5 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T374r6p0 : RecordPage := #[
(0x3e, 0xdb6db6f59492492492924924924492)]
def T374r6 : Records := #[T374r6p0]
def testT374r6 : ℕ → Bool := testAt T374 bsT374 5 T374r5 T374r6 2 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T374r6c0 : checkBlock testT374r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT374r6 : LayerOK T374 6 T374r6 := by
  apply layer_of_block (bs := bsT374) (k := 5) (old := T374r5) (cw := 2) (rw := 2) (by decide +kernel) vbsT374 vT374r5
  exact @block_merge testT374r6 0 1 31 T374r6c0 (show checkBlock testT374r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT374 : Valid T374 := by
  apply bound_of_layers (bs := bsT374) (last := T374r6) (cw := 2) (rw := 0) (by decide +kernel) vbsT374 vT374r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T375 : Bound := ⟨0xffffffff00000000, [0x0, 0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000], 0x115111f00000000, 7⟩
def bsT375 : Array Bound := [T337].toArray
theorem vbsT375 : ∀ s ∈ bsT375, Valid s := by
  intro s hs
  simp only [bsT375,List.mem_toArray] at hs
  exact (familyCons vT337 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT375 : Valid T375 := by
  apply bound_of_layers (bs := bsT375) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT375 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T376 : Bound := ⟨0xf0f0f0ff0f0f0f0, [0x0, 0x505050550505050, 0x303030330303030, 0xf0f0f0f0, 0xf000f00f000f0, 0xf0f0000f0f0], 0x105010f00101030, 8⟩
def bsT376 : Array Bound := [T87, T89, T91, T247, T285, T292, T293, T296].toArray
theorem vbsT376 : ∀ s ∈ bsT376, Valid s := by
  intro s hs
  simp only [bsT376,List.mem_toArray] at hs
  exact (familyCons vT87 <| familyCons vT89 <| familyCons vT91 <| familyCons vT247 <| familyCons vT285 <| familyCons vT292 <| familyCons vT293 <| familyCons vT296 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T376r4p0 : RecordPage := #[
(0x350841c103e, 0x0), (0x240842c103e, 0x0), (0x351610c303e, 0x0), (0x241610c313e, 0x0)]
def T376r4 : Records := #[T376r4p0]
def testT376r4 : ℕ → Bool := testAt T376 bsT376 3 (#[] : Records) T376r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T376r4c0 : checkBlock testT376r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT376r4 : LayerOK T376 4 T376r4 := by
  apply layer_of_block (bs := bsT376) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT376 (emptyOK _ _)
  exact @block_merge testT376r4 0 4 28 T376r4c0 (show checkBlock testT376r4 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T376r5p0 : RecordPage := #[
(0x840c103e, 0x4e84), (0x940c103e, 0x0), (0xa40c103e, 0x0), (0xb40c103e, 0x6e84ca),
(0x841c103e, 0x1a), (0x842c103e, 0x3c), (0xa40c203e, 0x0), (0xb40c203e, 0x6ec),
(0x610c303e, 0x58), (0xa30c303e, 0x0), (0x350c303e, 0x30e5ec), (0x750c303e, 0x5e),
(0xa30d303e, 0x84), (0x610c313e, 0x78), (0xa30c313e, 0x0), (0x240c313e, 0x29d78a),
(0x640c313e, 0x78), (0xa30d313e, 0x6e), (0xa50d413e, 0x0), (0xb50d413e, 0x84a),
(0xa30c323e, 0x0), (0xa30d323e, 0x6e), (0xa50d423e, 0x0), (0xb50d423e, 0x8e),
(0xa40d433e, 0x0), (0x840f433e, 0x84)]
def T376r5 : Records := #[T376r5p0]
def testT376r5 : ℕ → Bool := testAt T376 bsT376 4 T376r4 T376r5 3 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T376r5c0 : checkBlock testT376r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T376r5c1 : checkBlock testT376r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T376r5c2 : checkBlock testT376r5 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T376r5c3 : checkBlock testT376r5 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T376r5c4 : checkBlock testT376r5 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T376r5c5 : checkBlock testT376r5 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T376r5c6 : checkBlock testT376r5 2 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT376r5 : LayerOK T376 5 T376r5 := by
  apply layer_of_block (bs := bsT376) (k := 4) (old := T376r4) (cw := 3) (rw := 2) (by decide +kernel) vbsT376 vT376r4
  exact @block_merge testT376r5 0 26 6 (@block_merge testT376r5 0 12 14 (@block_merge testT376r5 0 4 8 T376r5c0 (@block_merge testT376r5 4 4 4 T376r5c1 T376r5c2)) (@block_merge testT376r5 12 8 6 (@block_merge testT376r5 12 4 4 T376r5c3 T376r5c4) (@block_merge testT376r5 20 4 2 T376r5c5 T376r5c6))) (show checkBlock testT376r5 6 26 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T376r6p0 : RecordPage := #[
(0xc103e, 0xaea2e830b0988aaca2e2e1c50c18080acaa), (0xc203e, 0x8e848a88c82e2e3cd44a0a08c88), (0xc303e, 0x3bb09ccc4497578b8ba121293a073311), (0xd303e, 0xeec2ccc44b8ba121299a0f3311),
(0xc313e, 0x2228baaa6db93a020217e031dc06aa9b), (0xd313e, 0x88a0aaa6db93a020323c0eaa9b), (0xd413e, 0x6e88ccaaae9e5448080c2c2aaae), (0xc323e, 0x21202122211b93a828329c48884),
(0xd323e, 0x22a2211b93a82832bc48884), (0xd423e, 0x6ecc848a888ebed44a0a0c2c2888e), (0xd433e, 0x1b9b8b9bbba1212b1a4c2c2e6ee), (0xf433e, 0x3339bba121292b3c2c2e6ee)]
def T376r6 : Records := #[T376r6p0]
def testT376r6 : ℕ → Bool := testAt T376 bsT376 5 T376r5 T376r6 3 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T376r6c0 : checkBlock testT376r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T376r6c1 : checkBlock testT376r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T376r6c2 : checkBlock testT376r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT376r6 : LayerOK T376 6 T376r6 := by
  apply layer_of_block (bs := bsT376) (k := 5) (old := T376r5) (cw := 3) (rw := 5) (by decide +kernel) vbsT376 vT376r5
  exact @block_merge testT376r6 0 12 20 (@block_merge testT376r6 0 4 8 T376r6c0 (@block_merge testT376r6 4 4 4 T376r6c1 T376r6c2)) (show checkBlock testT376r6 20 12 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T376r7p0 : RecordPage := #[
(0x3e, 0xbf57a227d1117d537aa9698a80cc2ecc39632075941)]
def T376r7 : Records := #[T376r7p0]
def testT376r7 : ℕ → Bool := testAt T376 bsT376 6 T376r6 T376r7 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T376r7c0 : checkBlock testT376r7 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT376r7 : LayerOK T376 7 T376r7 := by
  apply layer_of_block (bs := bsT376) (k := 6) (old := T376r6) (cw := 3) (rw := 4) (by decide +kernel) vbsT376 vT376r6
  exact @block_merge testT376r7 0 1 31 T376r7c0 (show checkBlock testT376r7 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT376 : Valid T376 := by
  apply bound_of_layers (bs := bsT376) (last := T376r7) (cw := 3) (rw := 0) (by decide +kernel) vbsT376 vT376r7 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T377 : Bound := ⟨0x3c3c3c3c3c3c3c3c, [0x0, 0x1414141414141414, 0xc0c0c0c0c0c0c0c, 0x3c003c003c003c, 0x3c3c00003c3c, 0x3c3c3c3c], 0x14101c0414143c, 8⟩
def bsT377 : Array Bound := [T87, T90, T273, T276, T282, T287, T301, T306].toArray
theorem vbsT377 : ∀ s ∈ bsT377, Valid s := by
  intro s hs
  simp only [bsT377,List.mem_toArray] at hs
  exact (familyCons vT87 <| familyCons vT90 <| familyCons vT273 <| familyCons vT276 <| familyCons vT282 <| familyCons vT287 <| familyCons vT301 <| familyCons vT306 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T377r4p0 : RecordPage := #[
(0x40b30d103e, 0x0), (0x240830f213e, 0x0), (0x31b40e313e, 0x0)]
def T377r4 : Records := #[T377r4p0]
def testT377r4 : ℕ → Bool := testAt T377 bsT377 3 (#[] : Records) T377r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r4c0 : checkBlock testT377r4 3 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT377r4 : LayerOK T377 4 T377r4 := by
  apply layer_of_block (bs := bsT377) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT377 (emptyOK _ _)
  exact @block_merge testT377r4 0 3 29 T377r4c0 (show checkBlock testT377r4 29 3 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T377r5p0 : RecordPage := #[
(0xb30d103e, 0x512), (0xa40d103e, 0x0), (0x930f103e, 0x0), (0x840f103e, 0x0),
(0xa10c203e, 0x0), (0x330c203e, 0x0), (0x240c203e, 0x0), (0xa40c203e, 0x0),
(0xa42c203e, 0xa), (0x840d203e, 0x0), (0xa40d203e, 0x0), (0x842d203e, 0x0),
(0xa42d203e, 0xa), (0xa40e203e, 0x0), (0x130f203e, 0x0), (0x40f203e, 0x44),
(0x840f203e, 0x0), (0xb40c303e, 0x4), (0x842c303e, 0x4), (0xb40e303e, 0x0),
(0x932e303e, 0xc), (0x942e303e, 0x6), (0xa30e213e, 0x0), (0xa40e213e, 0x0),
(0x830f213e, 0x532), (0x840f213e, 0x0), (0xa30e313e, 0xc), (0xb40e313e, 0x5c),
(0x842e313e, 0x5c), (0xa30c323e, 0x0), (0xa30e323e, 0x6)]
def T377r5 : Records := #[T377r5p0]
def testT377r5 : ℕ → Bool := testAt T377 bsT377 4 T377r4 T377r5 3 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r5c0 : checkBlock testT377r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r5c1 : checkBlock testT377r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r5c2 : checkBlock testT377r5 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r5c3 : checkBlock testT377r5 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r5c4 : checkBlock testT377r5 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r5c5 : checkBlock testT377r5 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r5c6 : checkBlock testT377r5 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r5c7 : checkBlock testT377r5 3 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT377r5 : LayerOK T377 5 T377r5 := by
  apply layer_of_block (bs := bsT377) (k := 4) (old := T377r4) (cw := 3) (rw := 2) (by decide +kernel) vbsT377 vT377r4
  exact @block_merge testT377r5 0 31 1 (@block_merge testT377r5 0 16 15 (@block_merge testT377r5 0 8 8 (@block_merge testT377r5 0 4 4 T377r5c0 T377r5c1) (@block_merge testT377r5 8 4 4 T377r5c2 T377r5c3)) (@block_merge testT377r5 16 8 7 (@block_merge testT377r5 16 4 4 T377r5c4 T377r5c5) (@block_merge testT377r5 24 4 3 T377r5c6 T377r5c7))) (show checkBlock testT377r5 1 31 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T377r6p0 : RecordPage := #[
(0xd103e, 0x882c2c2ccc808e2e8ea0e881622c2cc), (0xf103e, 0x2cc2cc8e8ea2a1c8856c2cc), (0xc203e, 0x1166446868e6e8ea6a3d8da6262f1b0b11096), (0xd203e, 0x65746468e8ea56932c2c4466),
(0xe203e, 0x119123a3a9ba42c2c6444), (0xf203e, 0x44648e848e4ea4a4a851f2c24771309444), (0xc303e, 0x2a5aa4a8e8e8d9362c2ca4aa), (0xe303e, 0x2abaa6aa923a3a76442c2ca4aa),
(0xe213e, 0x2c2ccc8e8eabe892d22ccc2), (0xf213e, 0x882c2c2ccc8e808e2ea2acc8931ccc2), (0xe313e, 0xae6a9ec2c2caaac8e8edd8893522acaa), (0xc323e, 0xae6a55daa9aa3a38b0b13b46a6aa),
(0xe323e, 0x2ab651aaa68e8e2c2c4f513a6aa)]
def T377r6 : Records := #[T377r6p0]
def testT377r6 : ℕ → Bool := testAt T377 bsT377 5 T377r5 T377r6 3 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r6c0 : checkBlock testT377r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r6c1 : checkBlock testT377r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r6c2 : checkBlock testT377r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r6c3 : checkBlock testT377r6 1 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT377r6 : LayerOK T377 6 T377r6 := by
  apply layer_of_block (bs := bsT377) (k := 5) (old := T377r5) (cw := 3) (rw := 5) (by decide +kernel) vbsT377 vT377r5
  exact @block_merge testT377r6 0 13 19 (@block_merge testT377r6 0 8 5 (@block_merge testT377r6 0 4 4 T377r6c0 T377r6c1) (@block_merge testT377r6 8 4 1 T377r6c2 T377r6c3)) (show checkBlock testT377r6 19 13 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T377r7p0 : RecordPage := #[
(0x3e, 0x1151d1d1d59abc746556b271cc8e8ea7d3569394781c)]
def T377r7 : Records := #[T377r7p0]
def testT377r7 : ℕ → Bool := testAt T377 bsT377 6 T377r6 T377r7 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T377r7c0 : checkBlock testT377r7 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT377r7 : LayerOK T377 7 T377r7 := by
  apply layer_of_block (bs := bsT377) (k := 6) (old := T377r6) (cw := 3) (rw := 4) (by decide +kernel) vbsT377 vT377r6
  exact @block_merge testT377r7 0 1 31 T377r7c0 (show checkBlock testT377r7 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT377 : Valid T377 := by
  apply bound_of_layers (bs := bsT377) (last := T377r7) (cw := 3) (rw := 0) (by decide +kernel) vbsT377 vT377r7 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T378 : Bound := ⟨0x55555555aaaaaaaa, [0x0, 0xaaaaaaaa, 0x1111111122222222, 0x50505050a0a0a0a, 0x55005500aa00aa, 0x55550000aaaa], 0x11511150000002a, 8⟩
def bsT378 : Array Bound := [T92, T94, T103, T106, T107, T250, T264, T297, T309, T314, T315].toArray
theorem vbsT378 : ∀ s ∈ bsT378, Valid s := by
  intro s hs
  simp only [bsT378,List.mem_toArray] at hs
  exact (familyCons vT92 <| familyCons vT94 <| familyCons vT103 <| familyCons vT106 <| familyCons vT107 <| familyCons vT250 <| familyCons vT264 <| familyCons vT297 <| familyCons vT309 <| familyCons vT314 <| familyCons vT315 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T378r4p0 : RecordPage := #[
(0x350a41e103e, 0x0), (0x340842e103e, 0x0), (0x351710e303e, 0x0), (0x341610c313e, 0x0)]
def T378r4 : Records := #[T378r4p0]
def testT378r4 : ℕ → Bool := testAt T378 bsT378 3 (#[] : Records) T378r4 4 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T378r4c0 : checkBlock testT378r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT378r4 : LayerOK T378 4 T378r4 := by
  apply layer_of_block (bs := bsT378) (k := 3) (old := (#[] : Records)) (cw := 4) (rw := 1) (by decide +kernel) vbsT378 (emptyOK _ _)
  exact @block_merge testT378r4 0 4 28 T378r4c0 (show checkBlock testT378r4 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T378r5p0 : RecordPage := #[
(0x840e103e, 0x34990), (0x940e103e, 0x0), (0xa40e103e, 0x0), (0xb40e103e, 0x526428e),
(0xa41e103e, 0x2e), (0x842e103e, 0x74), (0x840f203e, 0x0), (0x940f203e, 0x1254),
(0x710e303e, 0xae), (0xa30e303e, 0x0), (0x350e303e, 0xd2d254), (0x750e303e, 0xb2),
(0x830f303e, 0x190), (0x610c313e, 0xee), (0xb30c313e, 0x0), (0x340c313e, 0x1cdde0e),
(0x740c313e, 0xf0), (0xb30d313e, 0x152), (0xa50d413e, 0x0), (0xb50d413e, 0x320e),
(0xb30e323e, 0x0), (0x930f323e, 0x152), (0x850f423e, 0x0), (0x950f423e, 0x212),
(0xa40d433e, 0x0), (0x840f433e, 0x190)]
def T378r5 : Records := #[T378r5p0]
def testT378r5 : ℕ → Bool := testAt T378 bsT378 4 T378r4 T378r5 4 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T378r5c0 : checkBlock testT378r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T378r5c1 : checkBlock testT378r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T378r5c2 : checkBlock testT378r5 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T378r5c3 : checkBlock testT378r5 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T378r5c4 : checkBlock testT378r5 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T378r5c5 : checkBlock testT378r5 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T378r5c6 : checkBlock testT378r5 2 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT378r5 : LayerOK T378 5 T378r5 := by
  apply layer_of_block (bs := bsT378) (k := 4) (old := T378r4) (cw := 4) (rw := 2) (by decide +kernel) vbsT378 vT378r4
  exact @block_merge testT378r5 0 26 6 (@block_merge testT378r5 0 12 14 (@block_merge testT378r5 0 4 8 T378r5c0 (@block_merge testT378r5 4 4 4 T378r5c1 T378r5c2)) (@block_merge testT378r5 12 8 6 (@block_merge testT378r5 12 4 4 T378r5c3 T378r5c4) (@block_merge testT378r5 20 4 2 T378r5c5 T378r5c6))) (show checkBlock testT378r5 6 26 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T378r6p0 : RecordPage := #[
(0xe103e, 0x1d2716e02284d210739d4149121c50c104010751ce), (0xf203e, 0x9419073a14841122498c3cd701c085210), (0xe303e, 0x4a44d11a52885d591a469320c83937034a511), (0xf303e, 0x949144694a22469320c83837334a511),
(0xc313e, 0x420e2dce736a91a4085f8020083b4068e739b), (0xd313e, 0x841c0739cdaa4a9020084740e8e739b), (0xd413e, 0x54a10a49ce74a795460401045114739d2), (0xe323e, 0x32008320c8420a91a4e03814d1948420c),
(0xf323e, 0x39cc8420a92a4e0380ca5748420c), (0xf423e, 0x152a499073a5084146bed701c04511484212), (0xd433e, 0x2a4a91a4694a4c81a0ec5c6350d491a52), (0xf433e, 0x525234a4a8320e53b34511491a52)]
def T378r6 : Records := #[T378r6p0]
def testT378r6 : ℕ → Bool := testAt T378 bsT378 5 T378r5 T378r6 4 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T378r6c0 : checkBlock testT378r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T378r6c1 : checkBlock testT378r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T378r6c2 : checkBlock testT378r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT378r6 : LayerOK T378 6 T378r6 := by
  apply layer_of_block (bs := bsT378) (k := 5) (old := T378r5) (cw := 4) (rw := 5) (by decide +kernel) vbsT378 vT378r5
  exact @block_merge testT378r6 0 12 20 (@block_merge testT378r6 0 4 8 T378r6c0 (@block_merge testT378r6 4 4 4 T378r6c1 T378r6c2)) (show checkBlock testT378r6 20 12 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T378r7p0 : RecordPage := #[
(0x3e, 0xbcab29ca108be10739b2739697381044a92396941c290705d4)]
def T378r7 : Records := #[T378r7p0]
def testT378r7 : ℕ → Bool := testAt T378 bsT378 6 T378r6 T378r7 4 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T378r7c0 : checkBlock testT378r7 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT378r7 : LayerOK T378 7 T378r7 := by
  apply layer_of_block (bs := bsT378) (k := 6) (old := T378r6) (cw := 4) (rw := 4) (by decide +kernel) vbsT378 vT378r6
  exact @block_merge testT378r7 0 1 31 T378r7c0 (show checkBlock testT378r7 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT378 : Valid T378 := by
  apply bound_of_layers (bs := bsT378) (last := T378r7) (cw := 4) (rw := 0) (by decide +kernel) vbsT378 vT378r7 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T379 : Bound := ⟨0x55aa55aa55aa55aa, [0x0, 0xaa00aa00aa00aa, 0x1122112211221122, 0x50a050a050a050a, 0x55aa000055aa, 0x55aa55aa], 0x100110a0500152a, 8⟩
def bsT379 : Array Bound := [T104, T265, T277, T289, T300, T339].toArray
theorem vbsT379 : ∀ s ∈ bsT379, Valid s := by
  intro s hs
  simp only [bsT379,List.mem_toArray] at hs
  exact (familyCons vT104 <| familyCons vT265 <| familyCons vT277 <| familyCons vT289 <| familyCons vT300 <| familyCons vT339 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T379r4p0 : RecordPage := #[
(0x831350e103e, 0x0), (0xa31350e103e, 0x0), (0x240a20c203e, 0x0), (0x131841e203e, 0x0),
(0x40b30d213e, 0x0)]
def T379r4 : Records := #[T379r4p0]
def testT379r4 : ℕ → Bool := testAt T379 bsT379 3 (#[] : Records) T379r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r4c0 : checkBlock testT379r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r4c1 : checkBlock testT379r4 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT379r4 : LayerOK T379 4 T379r4 := by
  apply layer_of_block (bs := bsT379) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT379 (emptyOK _ _)
  exact @block_merge testT379r4 0 5 27 (@block_merge testT379r4 0 4 1 T379r4c0 T379r4c1) (show checkBlock testT379r4 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T379r5p0 : RecordPage := #[
(0xa30c103e, 0x0), (0xa40c103e, 0x0), (0xa31c103e, 0x0), (0xa30e103e, 0x0),
(0xa40e103e, 0x0), (0x350e103e, 0x848431aa), (0x831e103e, 0x18), (0xa31e103e, 0x328),
(0xa20c203e, 0x65), (0x230c203e, 0x0), (0xa40c203e, 0x0), (0x350c203e, 0x0),
(0xa41c203e, 0x0), (0xa40d203e, 0x0), (0x840e203e, 0x5), (0x240e203e, 0x0),
(0x640e203e, 0x6), (0xa40e203e, 0x0), (0x740e203e, 0x5), (0x841e203e, 0x76),
(0xa41e203e, 0x6), (0x842e203e, 0x6), (0xa42e203e, 0x76), (0x840f203e, 0x0),
(0x150f203e, 0x22), (0x842f203e, 0x0), (0xa40c303e, 0x5), (0x832c303e, 0x8),
(0x942c303e, 0x75), (0xa40e303e, 0x0), (0xb30c213e, 0x0), (0xa40c213e, 0x0)]
def T379r5p1 : RecordPage := #[
(0x350c213e, 0x8482), (0xb30d213e, 0x69), (0xa40d213e, 0x0), (0xb30c313e, 0x8),
(0xa40c313e, 0x0), (0x842c313e, 0x8), (0xb30c323e, 0x0), (0xb30e323e, 0x5)]
def T379r5 : Records := #[T379r5p0, T379r5p1]
def testT379r5 : ℕ → Bool := testAt T379 bsT379 4 T379r4 T379r5 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r5c0 : checkBlock testT379r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r5c1 : checkBlock testT379r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r5c2 : checkBlock testT379r5 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r5c3 : checkBlock testT379r5 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r5c4 : checkBlock testT379r5 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r5c5 : checkBlock testT379r5 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r5c6 : checkBlock testT379r5 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r5c7 : checkBlock testT379r5 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r5c8 : checkBlock testT379r5 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r5c9 : checkBlock testT379r5 4 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT379r5 : LayerOK T379 5 T379r5 := by
  apply layer_of_block (bs := bsT379) (k := 4) (old := T379r4) (cw := 3) (rw := 3) (by decide +kernel) vbsT379 vT379r4
  exact @block_merge testT379r5 0 40 24 (@block_merge testT379r5 0 20 20 (@block_merge testT379r5 0 8 12 (@block_merge testT379r5 0 4 4 T379r5c0 T379r5c1) (@block_merge testT379r5 8 4 8 T379r5c2 (@block_merge testT379r5 12 4 4 T379r5c3 T379r5c4))) (@block_merge testT379r5 20 8 12 (@block_merge testT379r5 20 4 4 T379r5c5 T379r5c6) (@block_merge testT379r5 28 4 8 T379r5c7 (@block_merge testT379r5 32 4 4 T379r5c8 T379r5c9)))) (show checkBlock testT379r5 24 40 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T379r6p0 : RecordPage := #[
(0xc103e, 0x1422022aaa981b0101008088), (0xe103e, 0x5542420f1b1101482eaaaa984b2107248088), (0xc203e, 0x2a8c80d02000a02f55554c5582021009c011000), (0xd203e, 0x100555531b6084802000),
(0xe203e, 0xb55d5294e3c29100555532564684fb1d84840022), (0xf203e, 0x26640415544c6aa98997c14200112), (0xc303e, 0x672cdd38330355551350084806066), (0xe303e, 0x52659982aaa89d91d84846066),
(0xc213e, 0x10911054906aaaa99fb23d0408882), (0xd213e, 0x2aa12220aaaa9a2b1430208882), (0xc313e, 0x696cdeaa12119a1aaaa8a492470406866), (0xc323e, 0x34b66ad989aaaaa1212681d06266),
(0xe323e, 0xce496b331555542414f0206266)]
def T379r6 : Records := #[T379r6p0]
def testT379r6 : ℕ → Bool := testAt T379 bsT379 5 T379r5 T379r6 3 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r6c0 : checkBlock testT379r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r6c1 : checkBlock testT379r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r6c2 : checkBlock testT379r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r6c3 : checkBlock testT379r6 1 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT379r6 : LayerOK T379 6 T379r6 := by
  apply layer_of_block (bs := bsT379) (k := 5) (old := T379r5) (cw := 3) (rw := 6) (by decide +kernel) vbsT379 vT379r5
  exact @block_merge testT379r6 0 13 19 (@block_merge testT379r6 0 8 5 (@block_merge testT379r6 0 4 4 T379r6c0 T379r6c1) (@block_merge testT379r6 8 4 1 T379r6c2 T379r6c3)) (show checkBlock testT379r6 19 13 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T379r7p0 : RecordPage := #[
(0x3e, 0x155555554d96bd555343562271aaaa67b35693960701)]
def T379r7 : Records := #[T379r7p0]
def testT379r7 : ℕ → Bool := testAt T379 bsT379 6 T379r6 T379r7 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T379r7c0 : checkBlock testT379r7 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT379r7 : LayerOK T379 7 T379r7 := by
  apply layer_of_block (bs := bsT379) (k := 6) (old := T379r6) (cw := 3) (rw := 4) (by decide +kernel) vbsT379 vT379r6
  exact @block_merge testT379r7 0 1 31 T379r7c0 (show checkBlock testT379r7 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT379 : Valid T379 := by
  apply bound_of_layers (bs := bsT379) (last := T379r7) (cw := 3) (rw := 0) (by decide +kernel) vbsT379 vT379r7 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T380 : Bound := ⟨0xcccccccc33333333, [0x0, 0x4444444411111111, 0x33333333, 0xc0c0c0c03030303, 0xcc00cc00330033, 0xcccc00003333], 0x4000c01111133, 8⟩
def bsT380 : Array Bound := [T84, T85, T86, T87, T102, T252, T268, T279, T307, T317, T319].toArray
theorem vbsT380 : ∀ s ∈ bsT380, Valid s := by
  intro s hs
  simp only [bsT380,List.mem_toArray] at hs
  exact (familyCons vT84 <| familyCons vT85 <| familyCons vT86 <| familyCons vT87 <| familyCons vT102 <| familyCons vT252 <| familyCons vT268 <| familyCons vT279 <| familyCons vT307 <| familyCons vT317 <| familyCons vT319 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T380r4p0 : RecordPage := #[
(0x350841c103e, 0x0), (0x340842c103e, 0x0), (0x351610c303e, 0x0), (0x341610c313e, 0x0)]
def T380r4 : Records := #[T380r4p0]
def testT380r4 : ℕ → Bool := testAt T380 bsT380 3 (#[] : Records) T380r4 4 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T380r4c0 : checkBlock testT380r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT380r4 : LayerOK T380 4 T380r4 := by
  apply layer_of_block (bs := bsT380) (k := 3) (old := (#[] : Records)) (cw := 4) (rw := 1) (by decide +kernel) vbsT380 (emptyOK _ _)
  exact @block_merge testT380r4 0 4 28 T380r4c0 (show checkBlock testT380r4 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T380r5p0 : RecordPage := #[
(0x840c103e, 0x55052), (0x940c103e, 0x0), (0xa40c103e, 0x0), (0xb40c103e, 0x15404a0e),
(0x841c103e, 0x2e), (0x842c103e, 0x70), (0xa40d203e, 0x0), (0xb40d203e, 0x2a90),
(0x610c303e, 0xae), (0xa30c303e, 0x0), (0x350c303e, 0x2061690), (0x750c303e, 0xb4),
(0xa30d303e, 0x192), (0x610c313e, 0xee), (0xa30c313e, 0x0), (0x340c313e, 0x1cdde4e),
(0x740c313e, 0xf2), (0xa30d313e, 0x154), (0xa50d413e, 0x0), (0xb50d413e, 0x124e),
(0xa30e323e, 0x0), (0x830f323e, 0x154), (0x850f423e, 0x0), (0x950f423e, 0x254),
(0xa40d433e, 0x0), (0x840f433e, 0x192)]
def T380r5 : Records := #[T380r5p0]
def testT380r5 : ℕ → Bool := testAt T380 bsT380 4 T380r4 T380r5 4 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T380r5c0 : checkBlock testT380r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T380r5c1 : checkBlock testT380r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T380r5c2 : checkBlock testT380r5 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T380r5c3 : checkBlock testT380r5 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T380r5c4 : checkBlock testT380r5 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T380r5c5 : checkBlock testT380r5 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T380r5c6 : checkBlock testT380r5 2 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT380r5 : LayerOK T380 5 T380r5 := by
  apply layer_of_block (bs := bsT380) (k := 4) (old := T380r4) (cw := 4) (rw := 2) (by decide +kernel) vbsT380 vT380r4
  exact @block_merge testT380r5 0 26 6 (@block_merge testT380r5 0 12 14 (@block_merge testT380r5 0 4 8 T380r5c0 (@block_merge testT380r5 4 4 4 T380r5c1 T380r5c2)) (@block_merge testT380r5 12 8 6 (@block_merge testT380r5 12 4 4 T380r5c3 T380r5c4) (@block_merge testT380r5 20 4 2 T380r5c5 T380r5c6))) (show checkBlock testT380r5 6 26 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T380r6p0 : RecordPage := #[
(0xc103e, 0x1d4716e34110261273a0e451141c50c1048d2741ce), (0xd203e, 0xa499273a1084914450f3582719c684212), (0xc303e, 0x5290261082285d5a2288a3242939370308411), (0xd303e, 0xa520884208a288a324c939970708411),
(0xc313e, 0x4a4e2dce736aa2a8685f90a42941d802e739b), (0xd313e, 0x949c6739cdaa8aa0a469423806e739b), (0xd413e, 0x55252841ce7527954a248d282208739d4), (0xe323e, 0x32429324294a4aa0a8e13850a60294a42),
(0xf323e, 0x39c294a4aa2a8e338d0642b94a42), (0xf423e, 0x1548419273a9294942bed719c68220894a54), (0xd433e, 0x2a8aa228aa528c90a4ec5ca82208a2a94), (0xf433e, 0x42145528a9324e53b382208a2a94)]
def T380r6 : Records := #[T380r6p0]
def testT380r6 : ℕ → Bool := testAt T380 bsT380 5 T380r5 T380r6 4 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T380r6c0 : checkBlock testT380r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T380r6c1 : checkBlock testT380r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T380r6c2 : checkBlock testT380r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT380r6 : LayerOK T380 6 T380r6 := by
  apply layer_of_block (bs := bsT380) (k := 5) (old := T380r5) (cw := 4) (rw := 5) (by decide +kernel) vbsT380 vT380r5
  exact @block_merge testT380r6 0 12 20 (@block_merge testT380r6 0 4 8 T380r6c0 (@block_merge testT380r6 4 4 4 T380r6c1 T380r6c2)) (show checkBlock testT380r6 20 12 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T380r7p0 : RecordPage := #[
(0x3e, 0xbd2b49d2528be52739b473969738d284114840e584072741c1)]
def T380r7 : Records := #[T380r7p0]
def testT380r7 : ℕ → Bool := testAt T380 bsT380 6 T380r6 T380r7 4 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T380r7c0 : checkBlock testT380r7 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT380r7 : LayerOK T380 7 T380r7 := by
  apply layer_of_block (bs := bsT380) (k := 6) (old := T380r6) (cw := 4) (rw := 4) (by decide +kernel) vbsT380 vT380r6
  exact @block_merge testT380r7 0 1 31 T380r7c0 (show checkBlock testT380r7 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT380 : Valid T380 := by
  apply bound_of_layers (bs := bsT380) (last := T380r7) (cw := 4) (rw := 0) (by decide +kernel) vbsT380 vT380r7 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T381 : Bound := ⟨0xff00ff0000ff00ff, [0x0, 0x5500550000550055, 0x3300330000330033, 0xf000f00000f000f, 0xff00ff, 0xff00000000ff], 0x10011000015003f, 8⟩
def bsT381 : Array Bound := [T97, T105, T255, T270, T303, T311, T321, T326].toArray
theorem vbsT381 : ∀ s ∈ bsT381, Valid s := by
  intro s hs
  simp only [bsT381,List.mem_toArray] at hs
  exact (familyCons vT97 <| familyCons vT105 <| familyCons vT255 <| familyCons vT270 <| familyCons vT303 <| familyCons vT311 <| familyCons vT321 <| familyCons vT326 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T381r4p0 : RecordPage := #[
(0x350841c103e, 0x0), (0x340842c103e, 0x0), (0x351610c303e, 0x0), (0x341610c313e, 0x0)]
def T381r4 : Records := #[T381r4p0]
def testT381r4 : ℕ → Bool := testAt T381 bsT381 3 (#[] : Records) T381r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T381r4c0 : checkBlock testT381r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT381r4 : LayerOK T381 4 T381r4 := by
  apply layer_of_block (bs := bsT381) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsT381 (emptyOK _ _)
  exact @block_merge testT381r4 0 4 28 T381r4c0 (show checkBlock testT381r4 28 4 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T381r5p0 : RecordPage := #[
(0x840c103e, 0x4e6c), (0x940c103e, 0x0), (0xa40c103e, 0x0), (0xb40c103e, 0x4e6ca8),
(0x841c103e, 0x18), (0x842c103e, 0x3a), (0xa40d203e, 0x0), (0xb40d203e, 0x4ea),
(0x610c303e, 0x58), (0xa30c303e, 0x0), (0x350c303e, 0x28d5ea), (0x750c303e, 0x5e),
(0xa30d303e, 0x6c), (0x610c313e, 0x78), (0xa30c313e, 0x0), (0x340c313e, 0x21c7c8),
(0x740c313e, 0x7c), (0xa30d313e, 0x4e), (0xa50d413e, 0x0), (0xb50d413e, 0x6c8),
(0xa30e323e, 0x0), (0x830f323e, 0x4e), (0x850f423e, 0x0), (0x950f423e, 0xce),
(0xa40d433e, 0x0), (0x840f433e, 0x6c)]
def T381r5 : Records := #[T381r5p0]
def testT381r5 : ℕ → Bool := testAt T381 bsT381 4 T381r4 T381r5 3 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T381r5c0 : checkBlock testT381r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T381r5c1 : checkBlock testT381r5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T381r5c2 : checkBlock testT381r5 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T381r5c3 : checkBlock testT381r5 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T381r5c4 : checkBlock testT381r5 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T381r5c5 : checkBlock testT381r5 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T381r5c6 : checkBlock testT381r5 2 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT381r5 : LayerOK T381 5 T381r5 := by
  apply layer_of_block (bs := bsT381) (k := 4) (old := T381r4) (cw := 3) (rw := 2) (by decide +kernel) vbsT381 vT381r4
  exact @block_merge testT381r5 0 26 6 (@block_merge testT381r5 0 12 14 (@block_merge testT381r5 0 4 8 T381r5c0 (@block_merge testT381r5 4 4 4 T381r5c1 T381r5c2)) (@block_merge testT381r5 12 8 6 (@block_merge testT381r5 12 4 4 T381r5c3 T381r5c4) (@block_merge testT381r5 20 4 2 T381r5c5 T381r5c6))) (show checkBlock testT381r5 6 26 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T381r6p0 : RecordPage := #[
(0xc103e, 0x8e82e028a89ac88a82e2e1c50c10c0c8a88), (0xd203e, 0xec6c88aaac2e2e3cd668080aaac), (0xc303e, 0x3ba89aaa4497578b8b9b1b213806aa91), (0xd303e, 0xeea2aaa44b8b9b1b21980eaa91),
(0xc313e, 0x3320b8886d3938217f030329da06221b), (0xd313e, 0xcc808886d39383032a3a0e221b), (0xd413e, 0x4eccaa888e9e5440c0ca2a2888e), (0xe323e, 0x1b031b1b331393a0202a9a6ccc6),
(0xf323e, 0x221b331393a02029aabccc6), (0xf423e, 0x4eaa6c88eccc44bed8080a2a2ccce), (0xd433e, 0x13938b93bb9b1323184a2a2e4ee), (0xf433e, 0x2ab93b931b21233a2a2e4ee)]
def T381r6 : Records := #[T381r6p0]
def testT381r6 : ℕ → Bool := testAt T381 bsT381 5 T381r5 T381r6 3 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T381r6c0 : checkBlock testT381r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T381r6c1 : checkBlock testT381r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T381r6c2 : checkBlock testT381r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT381r6 : LayerOK T381 6 T381r6 := by
  apply layer_of_block (bs := bsT381) (k := 5) (old := T381r5) (cw := 3) (rw := 5) (by decide +kernel) vbsT381 vT381r5
  exact @block_merge testT381r6 0 12 20 (@block_merge testT381r6 0 4 8 T381r6c0 (@block_merge testT381r6 4 4 4 T381r6c1 T381r6c2)) (show checkBlock testT381r6 20 12 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T381r7p0 : RecordPage := #[
(0x3e, 0xbf57a7d9917e64437a2169880caa2eaa396a8791501)]
def T381r7 : Records := #[T381r7p0]
def testT381r7 : ℕ → Bool := testAt T381 bsT381 6 T381r6 T381r7 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T381r7c0 : checkBlock testT381r7 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT381r7 : LayerOK T381 7 T381r7 := by
  apply layer_of_block (bs := bsT381) (k := 6) (old := T381r6) (cw := 3) (rw := 4) (by decide +kernel) vbsT381 vT381r6
  exact @block_merge testT381r7 0 1 31 T381r7c0 (show checkBlock testT381r7 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT381 : Valid T381 := by
  apply bound_of_layers (bs := bsT381) (last := T381r7) (cw := 3) (rw := 0) (by decide +kernel) vbsT381 vT381r7 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def T382 : Bound := ⟨0xffff00000000ffff, [0x0, 0x5555000000005555, 0x3333000000003333, 0xf0f000000000f0f, 0xff0000000000ff, 0xffff], 0x11500000000153f, 8⟩
def bsT382 : Array Bound := [T104, T107, T295, T304, T312, T318, T323, T325, T328].toArray
theorem vbsT382 : ∀ s ∈ bsT382, Valid s := by
  intro s hs
  simp only [bsT382,List.mem_toArray] at hs
  exact (familyCons vT104 <| familyCons vT107 <| familyCons vT295 <| familyCons vT304 <| familyCons vT312 <| familyCons vT318 <| familyCons vT323 <| familyCons vT325 <| familyCons vT328 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T382r6p0 : RecordPage := #[
(0xf433e, 0x842110739ce2308c328ca40100739d0)]
def T382r6 : Records := #[T382r6p0]
def testT382r6 : ℕ → Bool := testAt T382 bsT382 5 (#[] : Records) T382r6 4 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T382r6c0 : checkBlock testT382r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT382r6 : LayerOK T382 6 T382r6 := by
  apply layer_of_block (bs := bsT382) (k := 5) (old := (#[] : Records)) (cw := 4) (rw := 1) (by decide +kernel) vbsT382 (emptyOK _ _)
  exact @block_merge testT382r6 0 1 31 T382r6c0 (show checkBlock testT382r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T382r7p0 : RecordPage := #[
(0x3e, 0xc1ce2118c2118c3194a3194a2188a420504200e2208c320ca)]
def T382r7 : Records := #[T382r7p0]
def testT382r7 : ℕ → Bool := testAt T382 bsT382 6 T382r6 T382r7 4 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T382r7c0 : checkBlock testT382r7 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT382r7 : LayerOK T382 7 T382r7 := by
  apply layer_of_block (bs := bsT382) (k := 6) (old := T382r6) (cw := 4) (rw := 0) (by decide +kernel) vbsT382 vT382r6
  exact @block_merge testT382r7 0 1 31 T382r7c0 (show checkBlock testT382r7 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT382 : Valid T382 := by
  apply bound_of_layers (bs := bsT382) (last := T382r7) (cw := 4) (rw := 0) (by decide +kernel) vbsT382 vT382r7 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
def rootT : Bound := ⟨0xffffffffffffffff, [0x0, 0x5555555555555555, 0x3333333333333333, 0xf0f0f0f0f0f0f0f, 0xff00ff00ff00ff, 0xffff0000ffff, 0xffffffff], 0x115111f0515153f, 10⟩
def bsrootT : Array Bound := [T329, T330, T331, T332, T333, T334, T335, T336, T337, T339, T340, T353, T354, T357, T358, T359, T360, T361, T362, T363, T364, T365, T366, T367, T368, T369, T370, T371, T372, T373, T374, T375, T376, T377, T378, T379, T380, T381, T382].toArray
theorem vbsrootT : ∀ s ∈ bsrootT, Valid s := by
  intro s hs
  simp only [bsrootT,List.mem_toArray] at hs
  exact (familyCons vT329 <| familyCons vT330 <| familyCons vT331 <| familyCons vT332 <| familyCons vT333 <| familyCons vT334 <| familyCons vT335 <| familyCons vT336 <| familyCons vT337 <| familyCons vT339 <| familyCons vT340 <| familyCons vT353 <| familyCons vT354 <| familyCons vT357 <| familyCons vT358 <| familyCons vT359 <| familyCons vT360 <| familyCons vT361 <| familyCons vT362 <| familyCons vT363 <| familyCons vT364 <| familyCons vT365 <| familyCons vT366 <| familyCons vT367 <| familyCons vT368 <| familyCons vT369 <| familyCons vT370 <| familyCons vT371 <| familyCons vT372 <| familyCons vT373 <| familyCons vT374 <| familyCons vT375 <| familyCons vT376 <| familyCons vT377 <| familyCons vT378 <| familyCons vT379 <| familyCons vT380 <| familyCons vT381 <| familyCons vT382 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def rootTr5p0 : RecordPage := #[
(0x320843a31c107e, 0x0), (0x330841842c107e, 0x0), (0x51530b40d207e, 0x0), (0x110321c40d307e, 0x0),
(0x50b40a30c407e, 0x0), (0x110321c30d217e, 0x0), (0x110321c40d217e, 0x0), (0x320621a40d217e, 0x0),
(0x120b31a40d217e, 0x0), (0x61260c30f327e, 0x0), (0x161260c30f327e, 0x0)]
def rootTr5 : Records := #[rootTr5p0]
def testrootTr5 : ℕ → Bool := testAt rootT bsrootT 4 (#[] : Records) rootTr5 6 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr5c0 : checkBlock testrootTr5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr5c1 : checkBlock testrootTr5 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr5c2 : checkBlock testrootTr5 3 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootTr5 : LayerOK rootT 5 rootTr5 := by
  apply layer_of_block (bs := bsrootT) (k := 4) (old := (#[] : Records)) (cw := 6) (rw := 1) (by decide +kernel) vbsrootT (emptyOK _ _)
  exact @block_merge testrootTr5 0 11 21 (@block_merge testrootTr5 0 4 7 rootTr5c0 (@block_merge testrootTr5 4 4 3 rootTr5c1 rootTr5c2)) (show checkBlock testrootTr5 21 11 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def rootTr6p0 : RecordPage := #[
(0x840b30c107e, 0x9489346), (0x940b30c107e, 0x0), (0xa40b30c107e, 0x42), (0x941b30c107e, 0x1e),
(0xb41b30c107e, 0x46), (0x940b40c107e, 0x0), (0x450b40c107e, 0x1a1e), (0xa21b40c107e, 0x1e40),
(0x941b40c107e, 0x0), (0xb41b40c107e, 0x42), (0x943b40c107e, 0x0), (0xa41831c107e, 0x0),
(0xa51831c107e, 0x0), (0x843831c107e, 0x1a), (0x853831c107e, 0x1a), (0x260c31c107e, 0x2444),
(0x843a31c107e, 0x1), (0x730932c107e, 0x0), (0x840932c107e, 0x0), (0xa40932c107e, 0x22),
(0x730842c107e, 0x0), (0xb40842c107e, 0xe8042), (0x841842c107e, 0x1a1c2), (0xa41842c107e, 0x0),
(0xb40852c107e, 0xe8042), (0x330c43c107e, 0x601f26), (0x330d43c107e, 0x0), (0x260d43c107e, 0x2444),
(0x330e43c107e, 0x2), (0x130f43c107e, 0x3e), (0x40f43c107e, 0x42), (0x50f43c107e, 0x46)]
def rootTr6p1 : RecordPage := #[
(0x330e53c107e, 0x38), (0x240e53c107e, 0x42), (0x330e54c107e, 0x0), (0x250e54c107e, 0x46),
(0x840b30e107e, 0x26), (0x940b30e107e, 0x79e46), (0xa40b30e107e, 0x404479c42), (0x841b30e107e, 0x2542),
(0xa41b30e107e, 0x46), (0x851b30e107e, 0x0), (0xa51b30e107e, 0x1e), (0xb40a40e107e, 0x0),
(0x851a40e107e, 0x1e), (0xa51a40e107e, 0x0), (0xa41831e107e, 0x0), (0xa51831e107e, 0x0),
(0x330c43e107e, 0x26), (0x330d43e107e, 0x3e), (0x260d43e107e, 0x0), (0x330e43e107e, 0x0),
(0x130f43e107e, 0x0), (0x40f43e107e, 0x0), (0x330c53e107e, 0x0), (0x240e53e107e, 0x0),
(0x330e54e107e, 0x0), (0x530b40c207e, 0x46), (0xa21b40c207e, 0x40), (0xd41250c207e, 0x0),
(0xc43250c207e, 0x0), (0xd43250c207e, 0x244a), (0x720a42c207e, 0x0), (0xa50a52c207e, 0x0)]
def rootTr6p2 : RecordPage := #[
(0x330c43c207e, 0x6803e), (0x330d43c207e, 0x0), (0x350d43c207e, 0x1e), (0x330c53c207e, 0x3401f1e),
(0x330c54c207e, 0x1c00f981e), (0x330e54c207e, 0x1e), (0x350e54c207e, 0x1c), (0x840a30d207e, 0x0),
(0xa40a30d207e, 0x2522), (0x931a30d207e, 0x40), (0x530b40d207e, 0xc5), (0x450b40d207e, 0x29e),
(0xa21b40d207e, 0x1e40), (0x531b40d207e, 0x16), (0x931b40d207e, 0x0), (0x841b40d207e, 0x0),
(0xa41b40d207e, 0x42), (0xa10842d207e, 0x46), (0x841842d207e, 0x0), (0xa41842d207e, 0x0),
(0x730a42d207e, 0x0), (0x330c43d207e, 0x0), (0x330d43d207e, 0x3e), (0x350d43d207e, 0x46),
(0x840a40e207e, 0x42), (0xa40a40e207e, 0x2428), (0x330c43e207e, 0xa6), (0x350c43e207e, 0x2242),
(0x330d43e207e, 0x1f26), (0x840830f207e, 0x121146), (0xa40830f207e, 0x0), (0x931830f207e, 0x2440)]
def rootTr6p3 : RecordPage := #[
(0x841830f207e, 0x46), (0x851830f207e, 0x1e), (0xa40840f207e, 0x0), (0x931840f207e, 0x40),
(0xb31840f207e, 0x4a), (0x841840f207e, 0x42), (0xa41840f207e, 0x4a), (0x851840f207e, 0x1e),
(0xa51840f207e, 0x0), (0x230c43f207e, 0x0), (0x350c43f207e, 0x46), (0x230d43f207e, 0x0),
(0x230c53f207e, 0x0), (0x350c53f207e, 0x2a), (0x230c54f207e, 0x0), (0x230e54f207e, 0x0),
(0x230c30d307e, 0x40), (0x940a30d307e, 0x0), (0xb40a30d307e, 0x80ea142), (0x230c40d307e, 0x40),
(0x260c40d307e, 0x0), (0x321c40d307e, 0x7), (0x230d40d307e, 0x40), (0x221d40d307e, 0x7),
(0x370e40d307e, 0x0), (0x840b40d307e, 0x2428), (0x931b40d307e, 0x16), (0x230c50d307e, 0x1e40),
(0x340c50d307e, 0x2340), (0x260e42d307e, 0x0), (0xb20852d307e, 0x46), (0x330c52d307e, 0x1f46)]
def rootTr6p4 : RecordPage := #[
(0x230d43d307e, 0xf2c), (0x330d43d307e, 0x1f42), (0x230c53d307e, 0x1e26), (0x330c53d307e, 0x3e),
(0x230e54d307e, 0x1e24), (0x330e54d307e, 0x3e), (0x230d64d307e, 0x40), (0x330d64d307e, 0x0),
(0x940a30e307e, 0x2028), (0xb40a30e307e, 0x2142), (0x831a30e307e, 0x40), (0x941a30e307e, 0x2442),
(0x851a30e307e, 0x1e), (0x840b40e307e, 0x0), (0x831b40e307e, 0x0), (0xa31b40e307e, 0x40),
(0x851b40e307e, 0x0), (0xa51b40e307e, 0x1e), (0x260e42e307e, 0x0), (0x330d43e307e, 0xf1c),
(0x350c53e307e, 0x3c), (0x330c54e307e, 0x0), (0x250e54e307e, 0x46), (0x350e54e307e, 0x3c),
(0x940a30c407e, 0x0), (0xb40a30c407e, 0x80e8b26142), (0x850a30c407e, 0x0), (0xa50a30c407e, 0x2522),
(0x840b40c407e, 0x121426), (0x850b40c407e, 0x2522), (0x950b40c407e, 0x1e), (0xa50b40c407e, 0x0)]
def rootTr6p5 : RecordPage := #[
(0x950b50c407e, 0x2c), (0x851b50c407e, 0x2526), (0xa51b50c407e, 0x2c), (0xb61b50c407e, 0x44),
(0x330d43c407e, 0x0), (0x330c53c407e, 0x0), (0x330e54c407e, 0x0), (0x130f54c407e, 0x0),
(0x850a30e407e, 0x48441a146), (0xa50a30e407e, 0x0), (0x941a30e407e, 0x2442), (0x851a30e407e, 0x46),
(0xa40a50e407e, 0x0), (0x660a50e407e, 0x94a), (0x760a50e407e, 0xe22), (0x330c53e407e, 0x0),
(0x330c54e407e, 0x0), (0x330d54e407e, 0x1f1e), (0x130f65e407e, 0x4a), (0x330c54d507e, 0x40),
(0x270d54d507e, 0x0), (0x330c65d507e, 0x44), (0x340c30d217e, 0x40), (0x321c30d217e, 0xb),
(0x340d30d217e, 0x40), (0x221d30d217e, 0xb), (0xb40a30d217e, 0x452a346), (0x650a30d217e, 0x1e),
(0x260e30d217e, 0x0), (0x610840d217e, 0x40), (0xa10840d217e, 0x129142), (0x620840d217e, 0x40)]
def rootTr6p6 : RecordPage := #[
(0x730840d217e, 0x40), (0xb30840d217e, 0x101d42), (0x230c40d217e, 0x2440), (0x340c40d217e, 0x40),
(0x321c40d217e, 0xd), (0x210d40d217e, 0x0), (0x230d40d217e, 0x40), (0x340d40d217e, 0x40),
(0x221d40d217e, 0xd), (0x760a40d217e, 0x2122), (0x621a40d217e, 0xf), (0x931a40d217e, 0x40),
(0xb31a40d217e, 0x11), (0x232e40d217e, 0x0), (0x840b40d217e, 0x1944), (0x450b40d217e, 0x1e),
(0x931b40d217e, 0x16), (0x60f40d217e, 0x0), (0x230c50d217e, 0x2440), (0x340c50d217e, 0x40),
(0xa40941d217e, 0x0), (0x230e54d217e, 0x0), (0x330e54d217e, 0x0), (0x240d30c317e, 0x40),
(0x230d40c317e, 0x40), (0x240d40c317e, 0x40), (0x560b40c317e, 0x133a), (0x831b40c317e, 0x2542),
(0xa31b40c317e, 0x40), (0x851b40c317e, 0x0), (0xa51b40c317e, 0x1e), (0x42f40c317e, 0x0)]
def rootTr6p7 : RecordPage := #[
(0xb20a42c317e, 0x0), (0x330e42c317e, 0x3e), (0x260e42c317e, 0x0), (0x330c54c317e, 0x0),
(0x230e54c317e, 0x12111e), (0x330e54c317e, 0x0), (0x250e54c317e, 0x42), (0x350e54c317e, 0x0),
(0x650a30d317e, 0x1e), (0x931b40d317e, 0x1e), (0x330c42d317e, 0x1f26), (0x260e42d317e, 0x244a),
(0xb50a30c417e, 0x114a2c6a346), (0x950b40c417e, 0xf2a), (0x560b40c417e, 0x133a), (0x851b40c417e, 0x2542),
(0xa51b40c417e, 0x2a), (0x840b50c417e, 0x3c651232a), (0x950b50c417e, 0x0), (0x330d54c417e, 0x1f1e),
(0x130f54c417e, 0x0), (0xa40a20c327e, 0x2428), (0x340c52c327e, 0x0), (0xa32a30d327e, 0x0),
(0xf52250d327e, 0x0), (0x340e52d327e, 0x3c), (0x830710e327e, 0x0), (0x50f30e327e, 0x0),
(0x760a40e327e, 0x28), (0x330c50e327e, 0x40), (0x240c50e327e, 0x40), (0x340e51e327e, 0x0)]
def rootTr6p8 : RecordPage := #[
(0x650830f327e, 0x1e), (0x260c30f327e, 0x2b3), (0x71c30f327e, 0x3d3), (0x171c30f327e, 0x3d5),
(0x171c40f327e, 0x0), (0x71c50f327e, 0x0), (0x171c50f327e, 0x0), (0x921460f327e, 0x0),
(0x921560f327e, 0x0), (0x240e51f327e, 0x4a), (0x850a50c427e, 0x42), (0xa50a50c427e, 0x2428),
(0x130f65c427e, 0x0), (0xb50a30e427e, 0x452a346), (0xa50a40e427e, 0x0), (0x760a40e427e, 0x28),
(0xa50a50e427e, 0x0), (0x660a50e427e, 0x4a), (0x760a50e427e, 0x22), (0x840b50e427e, 0x3c651232c),
(0x130f65e427e, 0x4a), (0xb50a30d527e, 0x3cf2346), (0x840b50d527e, 0x79644), (0x330c65d527e, 0x40),
(0x330e65d527e, 0x0), (0x460b50c437e, 0x40), (0x560b50c437e, 0x3a), (0xb50a40e437e, 0x80ea142),
(0x850b50e437e, 0x121426)]
def rootTr6 : Records := #[rootTr6p0, rootTr6p1, rootTr6p2, rootTr6p3, rootTr6p4, rootTr6p5, rootTr6p6, rootTr6p7, rootTr6p8]
def testrootTr6 : ℕ → Bool := testAt rootT bsrootT 5 rootTr5 rootTr6 6 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c0 : checkBlock testrootTr6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c1 : checkBlock testrootTr6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c2 : checkBlock testrootTr6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c3 : checkBlock testrootTr6 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c4 : checkBlock testrootTr6 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c5 : checkBlock testrootTr6 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c6 : checkBlock testrootTr6 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c7 : checkBlock testrootTr6 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c8 : checkBlock testrootTr6 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c9 : checkBlock testrootTr6 4 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c10 : checkBlock testrootTr6 4 40 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c11 : checkBlock testrootTr6 4 44 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c12 : checkBlock testrootTr6 4 48 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c13 : checkBlock testrootTr6 4 52 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c14 : checkBlock testrootTr6 4 56 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c15 : checkBlock testrootTr6 4 60 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c16 : checkBlock testrootTr6 4 64 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c17 : checkBlock testrootTr6 4 68 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c18 : checkBlock testrootTr6 4 72 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c19 : checkBlock testrootTr6 4 76 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c20 : checkBlock testrootTr6 4 80 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c21 : checkBlock testrootTr6 4 84 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c22 : checkBlock testrootTr6 4 88 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c23 : checkBlock testrootTr6 4 92 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c24 : checkBlock testrootTr6 4 96 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c25 : checkBlock testrootTr6 4 100 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c26 : checkBlock testrootTr6 4 104 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c27 : checkBlock testrootTr6 4 108 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c28 : checkBlock testrootTr6 4 112 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c29 : checkBlock testrootTr6 4 116 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c30 : checkBlock testrootTr6 4 120 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c31 : checkBlock testrootTr6 4 124 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c32 : checkBlock testrootTr6 4 128 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c33 : checkBlock testrootTr6 4 132 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c34 : checkBlock testrootTr6 4 136 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c35 : checkBlock testrootTr6 4 140 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c36 : checkBlock testrootTr6 4 144 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c37 : checkBlock testrootTr6 4 148 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c38 : checkBlock testrootTr6 4 152 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c39 : checkBlock testrootTr6 4 156 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c40 : checkBlock testrootTr6 4 160 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c41 : checkBlock testrootTr6 4 164 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c42 : checkBlock testrootTr6 4 168 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c43 : checkBlock testrootTr6 4 172 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c44 : checkBlock testrootTr6 4 176 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c45 : checkBlock testrootTr6 4 180 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c46 : checkBlock testrootTr6 4 184 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c47 : checkBlock testrootTr6 4 188 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c48 : checkBlock testrootTr6 4 192 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c49 : checkBlock testrootTr6 4 196 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c50 : checkBlock testrootTr6 4 200 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c51 : checkBlock testrootTr6 4 204 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c52 : checkBlock testrootTr6 4 208 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c53 : checkBlock testrootTr6 4 212 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c54 : checkBlock testrootTr6 4 216 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c55 : checkBlock testrootTr6 4 220 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c56 : checkBlock testrootTr6 4 224 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c57 : checkBlock testrootTr6 4 228 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c58 : checkBlock testrootTr6 4 232 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c59 : checkBlock testrootTr6 4 236 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c60 : checkBlock testrootTr6 4 240 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c61 : checkBlock testrootTr6 4 244 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c62 : checkBlock testrootTr6 4 248 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c63 : checkBlock testrootTr6 4 252 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c64 : checkBlock testrootTr6 4 256 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c65 : checkBlock testrootTr6 4 260 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c66 : checkBlock testrootTr6 4 264 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c67 : checkBlock testrootTr6 4 268 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c68 : checkBlock testrootTr6 4 272 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c69 : checkBlock testrootTr6 4 276 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c70 : checkBlock testrootTr6 4 280 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr6c71 : checkBlock testrootTr6 1 284 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootTr6 : LayerOK rootT 6 rootTr6 := by
  apply layer_of_block (bs := bsrootT) (k := 5) (old := rootTr5) (cw := 6) (rw := 4) (by decide +kernel) vbsrootT vrootTr5
  exact @block_merge testrootTr6 0 285 3 (@block_merge testrootTr6 0 144 141 (@block_merge testrootTr6 0 72 72 (@block_merge testrootTr6 0 36 36 (@block_merge testrootTr6 0 16 20 (@block_merge testrootTr6 0 8 8 (@block_merge testrootTr6 0 4 4 rootTr6c0 rootTr6c1) (@block_merge testrootTr6 8 4 4 rootTr6c2 rootTr6c3)) (@block_merge testrootTr6 16 8 12 (@block_merge testrootTr6 16 4 4 rootTr6c4 rootTr6c5) (@block_merge testrootTr6 24 4 8 rootTr6c6 (@block_merge testrootTr6 28 4 4 rootTr6c7 rootTr6c8)))) (@block_merge testrootTr6 36 16 20 (@block_merge testrootTr6 36 8 8 (@block_merge testrootTr6 36 4 4 rootTr6c9 rootTr6c10) (@block_merge testrootTr6 44 4 4 rootTr6c11 rootTr6c12)) (@block_merge testrootTr6 52 8 12 (@block_merge testrootTr6 52 4 4 rootTr6c13 rootTr6c14) (@block_merge testrootTr6 60 4 8 rootTr6c15 (@block_merge testrootTr6 64 4 4 rootTr6c16 rootTr6c17))))) (@block_merge testrootTr6 72 36 36 (@block_merge testrootTr6 72 16 20 (@block_merge testrootTr6 72 8 8 (@block_merge testrootTr6 72 4 4 rootTr6c18 rootTr6c19) (@block_merge testrootTr6 80 4 4 rootTr6c20 rootTr6c21)) (@block_merge testrootTr6 88 8 12 (@block_merge testrootTr6 88 4 4 rootTr6c22 rootTr6c23) (@block_merge testrootTr6 96 4 8 rootTr6c24 (@block_merge testrootTr6 100 4 4 rootTr6c25 rootTr6c26)))) (@block_merge testrootTr6 108 16 20 (@block_merge testrootTr6 108 8 8 (@block_merge testrootTr6 108 4 4 rootTr6c27 rootTr6c28) (@block_merge testrootTr6 116 4 4 rootTr6c29 rootTr6c30)) (@block_merge testrootTr6 124 8 12 (@block_merge testrootTr6 124 4 4 rootTr6c31 rootTr6c32) (@block_merge testrootTr6 132 4 8 rootTr6c33 (@block_merge testrootTr6 136 4 4 rootTr6c34 rootTr6c35)))))) (@block_merge testrootTr6 144 72 69 (@block_merge testrootTr6 144 36 36 (@block_merge testrootTr6 144 16 20 (@block_merge testrootTr6 144 8 8 (@block_merge testrootTr6 144 4 4 rootTr6c36 rootTr6c37) (@block_merge testrootTr6 152 4 4 rootTr6c38 rootTr6c39)) (@block_merge testrootTr6 160 8 12 (@block_merge testrootTr6 160 4 4 rootTr6c40 rootTr6c41) (@block_merge testrootTr6 168 4 8 rootTr6c42 (@block_merge testrootTr6 172 4 4 rootTr6c43 rootTr6c44)))) (@block_merge testrootTr6 180 16 20 (@block_merge testrootTr6 180 8 8 (@block_merge testrootTr6 180 4 4 rootTr6c45 rootTr6c46) (@block_merge testrootTr6 188 4 4 rootTr6c47 rootTr6c48)) (@block_merge testrootTr6 196 8 12 (@block_merge testrootTr6 196 4 4 rootTr6c49 rootTr6c50) (@block_merge testrootTr6 204 4 8 rootTr6c51 (@block_merge testrootTr6 208 4 4 rootTr6c52 rootTr6c53))))) (@block_merge testrootTr6 216 36 33 (@block_merge testrootTr6 216 16 20 (@block_merge testrootTr6 216 8 8 (@block_merge testrootTr6 216 4 4 rootTr6c54 rootTr6c55) (@block_merge testrootTr6 224 4 4 rootTr6c56 rootTr6c57)) (@block_merge testrootTr6 232 8 12 (@block_merge testrootTr6 232 4 4 rootTr6c58 rootTr6c59) (@block_merge testrootTr6 240 4 8 rootTr6c60 (@block_merge testrootTr6 244 4 4 rootTr6c61 rootTr6c62)))) (@block_merge testrootTr6 252 16 17 (@block_merge testrootTr6 252 8 8 (@block_merge testrootTr6 252 4 4 rootTr6c63 rootTr6c64) (@block_merge testrootTr6 260 4 4 rootTr6c65 rootTr6c66)) (@block_merge testrootTr6 268 8 9 (@block_merge testrootTr6 268 4 4 rootTr6c67 rootTr6c68) (@block_merge testrootTr6 276 4 5 rootTr6c69 (@block_merge testrootTr6 280 4 1 rootTr6c70 rootTr6c71))))))) (show checkBlock testrootTr6 3 285 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def rootTr7p0 : RecordPage := #[
(0xb30c107e, 0x3c780901d34260c183080ea03a3ce0f382c0280600c24d0932684c18424d0972e), (0xb40c107e, 0x108153c78130453264cd00f8c8a5229479e1e1079e01af0b1a02cd268c99346691a3268c9972e), (0x831c107e, 0x487c981d4c0dae5c9970326817350802e60b9700009932e4d0a1425c99830), (0xc31c107e, 0x12223084b981e07d342850a142),
(0xd31c107e, 0x4888c21408909742850a100), (0xa31c107e, 0x243e4c193042b97265d08d305cc18264c998265cc0030), (0xd41c107e, 0x122201f1932e8d19346), (0xc51c107e, 0x24443cb132e3c7931e),
(0x932c107e, 0x90ba42e900aae4c98d005d0a1427ca0e2a09c250411ae5d0a14284ba142), (0x842c107e, 0x841b5cb93260bc2d5cd172e7c88e2a0ac250414ae5d1a3465cb9326), (0x852c107e, 0x181d5cb93263c70f1c3cb8f1e3ca9f2010a831540952a5478f1e3ca8f26), (0xc43c107e, 0x24440b4d4a809a10670a142),
(0xd43c107e, 0x48881780f08f06e9a106b0a142), (0xe43c107e, 0x488808c605e104a6230731a346), (0xf43c107e, 0x488809c602614095083f8c1e965c1dae), (0xc53c107e, 0x244438693420d0a142),
(0xe53c107e, 0x9110f1c06612a0c21882b9c2a), (0xc54c107e, 0x488870f2a4ca8c46111a346), (0xe54c107e, 0x9110f1c4c2388ab9e2a), (0xb30e107e, 0x134280005514c5113d342000000080ea00080e883a3ce0f382c2689624c24d093424d093426000000),
(0xa40e107e, 0x132e16c594c9a318940a522208a5223c70f1c15cd09a593464d193464d18102), (0x831e107e, 0x132e17cd0ba6800000013260401830), (0xc43e107e, 0x1a13e14a809a10c30a142), (0xd43e107e, 0x3c328c70a142),
(0xe43e107e, 0xba28c2311867042680), (0xf43e107e, 0x204a8c35c68c34c6), (0xc53e107e, 0x1a14e10db0a142), (0xe53e107e, 0x17c5584186f0c09c2a),
(0xc54e107e, 0x78e46164c461008e2a), (0xe54e107e, 0x8c2d8e31a346), (0xb40c207e, 0x4a4c98d0e668d0eb1914a440114a2928f3c3cf13344cd0b463439c6351a3308cc0000), (0x250c207e, 0x12a53e4d2243e4c987b1e603e0100d1a346a11a4d0a23e01123181de32630981f00c180000fa63e3870e1c4c7131c3c912243cb162c)]
def rootTr7p1 : RecordPage := #[
(0xd41c207e, 0x3c3b8eb198008d19846), (0xc51c207e, 0x3cb18003c7961e), (0xa42c207e, 0x1741700018301cc01c70000001f4d1a), (0xa52c207e, 0x17c1960c0f1c3c60f1e3c7800fee003800e0f24),
(0xc43c207e, 0x7879340d9030a142), (0xd43c207e, 0x3c3d9a4d0a44a21611070a142), (0xc53c207e, 0xd1e380e90f0a142), (0xc54c207e, 0xe1e38e121131a346),
(0xe54c207e, 0xf1c234d11601e24), (0xa30d207e, 0xc184224d32e90a24283ca8f2a6848b423d34201093424d0932e), (0xb40d207e, 0xf1e2849f2c4e93658998c8a5229479e1e0c79e12ef13344cd231a8c4ac62c5a3008c01830), (0xd41d207e, 0x1022133198008d18046),
(0xe32d207e, 0x10224224c0308508042), (0x842d207e, 0xc1800605394a5981a341921a34c183034519a), (0xa42d207e, 0xc180060c09b60c03380054b0611a34660c0d1a), (0xe42d207e, 0x40884ec660680468d1a346),
(0xf42d207e, 0x20442d1a04a8cc23468d18a3), (0xc43d207e, 0x8110a527e31571a346), (0xd43d207e, 0x4088539431a44a2be115ac1a2e), (0xa40e207e, 0x60c0306345a318948a5223c18f064c59a62c4b4635180460119830),
(0xc43e207e, 0x22400853422de116b0a142), (0xd43e207e, 0x112026852251730a142), (0x830f207e, 0xc00487c98c34c60c22fd302900242818a24283ca8f2a685eb42ed3425d0a1268499300), (0x840f207e, 0x180094f8d133ccd32cc931e3189402522288a5223c70f1c4c62a62ee31a8c598466118000),
(0xe32f207e, 0x422fc030850a12e), (0xe42f207e, 0x2318ec00468d1a346), (0xf42f207e, 0x118c9812a3308d1a346), (0xe52f207e, 0x1e70c00303c78f2c),
(0xc43f207e, 0x118cb84609ab0801a600bb), (0xd43f207e, 0x2319b2254635e346), (0xc53f207e, 0x1e3908c336e10036552a), (0xc54f207e, 0x3c72319e62300375c1c)]
def rootTr7p2 : RecordPage := #[
(0xe54f207e, 0x8c68c637e346), (0xc30d307e, 0x265d22201e70a6), (0xa30d307e, 0x4cd132e90a24283ca8f2a39611c70a3268d193468d1932e), (0xe30d307e, 0x99726),
(0xc40d307e, 0x75803c748ea73b0), (0xd40d307e, 0x181df0221327680), (0xe40d307e, 0x1de00f1809a130), (0xb40d307e, 0x163d583080ea03a3ce0f388471c23ce3468c5a3466119830),
(0xf40d307e, 0x607580), (0xc50d307e, 0x787961f27b9e), (0xe50d307e, 0x1e1e591a31e), (0xd60d307e, 0x228848944),
(0xf60d307e, 0x8a244), (0xc51d307e, 0xe1e587cc68c7a346), (0xd61d307e, 0x65109468912344), (0xc32d307e, 0x99702),
(0xe32d307e, 0x99a489518e18c9a346), (0xc42d307e, 0xc004a809a130), (0xd42d307e, 0xc0000), (0xe42d307e, 0x1ea68f1f718e78cc2346),
(0xf42d307e, 0x58d409518ed8d1a300), (0x852d307e, 0x11a31e3878e1e3878f1e786231fa70f3c), (0xc52d307e, 0x796463cf0ff), (0xa52d307e, 0x11a31e3078f1e791a33c8d1a3463d18f3c),
(0xe52d307e, 0x79e467918f78c7a346), (0xf62d307e, 0x45122128912244), (0xd43d307e, 0x265c81a0271ae), (0xc53d307e, 0x1c3c710741552a),
(0xc54d307e, 0xc060c19224), (0xe54d307e, 0x1c3c710b425c2c), (0xd64d307e, 0x1110f435d22), (0xa30e307e, 0x487c9919848ba6455302900a42814a24283ca8f2a44e1223093468d1a3268d19302)]
def rootTr7p3 : RecordPage := #[
(0xb40e307e, 0x1234851f47400080ea00080e8a3a3ce0f388488c246e346351a3468cc0000), (0xc32e307e, 0x26454c468c9a346), (0xe32e307e, 0x12252e), (0xc42e307e, 0x23a5a5404d08c468c02346),
(0xd42e307e, 0x23e68c468cc2346), (0xe42e307e, 0x3c9280), (0xf42e307e, 0x102530), (0xc52e307e, 0x1e3918c468c7a346),
(0xe52e307e, 0x3cf232c), (0xf62e307e, 0x112532), (0xd43e307e, 0x2645d27308880), (0xc53e307e, 0x3c6132329488102152a),
(0xc54e307e, 0x484325661224), (0xe54e307e, 0x1e3091864bd2d0c19c38), (0xd64e307e, 0x22222912244), (0xa30c407e, 0xf1c3cb0f1e4cba42890a1a26ed1354ce126308f1e3c7931e3c7932a),
(0xb40c407e, 0x1e38796424c78f306101d4074593f4f53b8498c24e4f1e3c78f1e607962c), (0xb50c407e, 0x3cb14794a2a869931e3c79e1f31914a4528b065043266899a1e8c78f46791a31e8c7962c), (0xd61c407e, 0x9910f4c8912644), (0xd43c407e, 0x1495898aa),
(0xc53c407e, 0x2971a346), (0xc54c407e, 0xa1c695013420d1a346), (0xd54c407e, 0x28b18f1c0cb0324), (0xe54c407e, 0x29b1a346),
(0xf54c407e, 0x10251e391831658a7ac), (0xd64c407e, 0x26440d3264c), (0xf65c407e, 0x132228f18f4c993094c), (0xa30e407e, 0x90f932af09553c79302900a42808a242868a9b45443420d08f1e3c78f263c7932a),
(0xa50e407e, 0x1e3878e1e5878f1c3d18c4a57652256d14a4418d062c99594ca89e3d18e463d18f463d18c18), (0xd43e407e, 0x26554f2a0c6032a), (0xc53e407e, 0x99573c715f30a8aa), (0xc54e407e, 0x6352a0268478e2c218b24)]
def rootTr7p4 : RecordPage := #[
(0xd54e407e, 0x78e2c71a346), (0xe54e407e, 0xc68f1c0c60338), (0xf54e407e, 0x204a3ce23068d18346), (0xd64e407e, 0x8880f4c2912244),
(0xf65e407e, 0x11104488b2c4), (0xc54d507e, 0x26852a02cf1a346), (0xd54d507e, 0x1e5a404024c8922), (0xe54d507e, 0x20222902040),
(0xf54d507e, 0x204a8100940), (0xc64d507e, 0x26400d3264c), (0xe64d507e, 0x3d320202902040), (0xc65d507e, 0x4a406232d71a346),
(0xe65d507e, 0x3d3264a253264c), (0xc30d217e, 0x16f5d0222da4980), (0xd30d217e, 0xb9ae25fae), (0xa30d217e, 0x30609933288ca21e0c7962eeb0f2c5d632031a1308509342850972e),
(0xe30d217e, 0x172e6b8f2f30a100), (0xf30d217e, 0x2300b7c47c9a12e), (0x840d217e, 0x1304a68d266901140447951e54023008cc1b02997f5f57b), (0xc40d217e, 0x312bdb0ec2b4),
(0xd40d217e, 0xd19181298f6358b), (0xa40d217e, 0x4c13b32cba64ccaa694c9ca444114a4478e1e38623188d08d428499342850a14262d7b), (0xe40d217e, 0xcdb22bdca7c9a134), (0xb40d217e, 0xb34299322948a51e787841e78cfbc8c80c6676142845a1424d09a34),
(0xf40d217e, 0xd1a31279a385097d), (0xc50d217e, 0x79534ed29e), (0xe50d217e, 0x7951e), (0x941d217e, 0x428468d3466d956921a486921a95cd2142850a1426909326),
(0xe42d217e, 0xd0b2f098584d2142), (0xf42d217e, 0x1666604a84c6c285098b), (0xe52d217e, 0x1e7109a5847a142), (0xc54d217e, 0x3ca93081020e2a)]
def rootTr7p5 : RecordPage := #[
(0xe54d217e, 0x1ad6ade2a), (0xd30c317e, 0xa335e8ac6), (0xe30c317e, 0x17468c99702), (0xf30c317e, 0x520a3447c9a346),
(0xd40c317e, 0x346061366d8c2), (0xe40c317e, 0x6a1424c9983), (0xb40c317e, 0x982b4d0a00e6f5bb354b76e4d36e6934280ea036b01d107479c1e7001800609a11a3509342849a12662d81), (0xf40c317e, 0xdfb46061407c6a142),
(0xc50c317e, 0x1e542041e), (0xe50c317e, 0x7951e), (0x842c317e, 0x1305a99a14a69bf3468d1a209931a4d0a1423498d1a), (0xc42c317e, 0x36f09a1a9501342850a142),
(0xd42c317e, 0xdcc284d8c2850a11a), (0xa42c317e, 0x4c17a66868d1a3499338268d1a), (0xe42c317e, 0xd0d1e715c3), (0xf42c317e, 0x812a11a),
(0xc52c317e, 0x1e38993083c7931e), (0xe52c317e, 0x1336), (0xc54c317e, 0x6ee138f0a142), (0xe54c317e, 0x37b09cf735cb725c2a),
(0xa30d317e, 0x426a53348c70a64cca232887841e58e8ac3cb180060013464d193464d1972e), (0xb40d317e, 0xf1e2bc852ce99a2c9a1407501d1e7079c0060018424d093422c5a1268499a34), (0x842d317e, 0x1a344cd0a73508d1668688264c98d266868d1a), (0xc42d317e, 0x244a686a5404d09d5),
(0xd42d317e, 0x244a84d211a), (0xa42d317e, 0xd1a266908d3434d1a0834993344d0a1426898d1a), (0xe42d317e, 0x9129d384d0d1e75d342850a142), (0xf42d317e, 0x48945a1409509a42850a11a),
(0xa30c417e, 0x78e1e3cb0f264cca23288ecc641633000c001e3c793263c7931e3c7952a), (0xb40c417e, 0x1e3878e260c600e785df36c31e3c79c268501d4077603a20e8b0876c400600181e8478f424d0a11e847952a), (0xb50c417e, 0x3c72325278f1e78f1326452914a2c69e53519058cf19e3c78f1e4c98f1e4c7952a), (0xc54c417e, 0x3bf0a5403c91342110a142)]
def rootTr7p6 : RecordPage := #[
(0xd54c417e, 0x78e3cf0a142), (0xe54c417e, 0x3c308f1c10a842a), (0xf54c417e, 0x10251e390841654f4aa), (0xa20c327e, 0x14668b1a345a0228088f383ce213d7098b01180462c58b16),
(0xc52c327e, 0x25404d08f1c3cf6963c79c1e), (0xe52c327e, 0x4a809a138), (0xf62c327e, 0x26852a040), (0xb20d327e, 0x2c58b16812a0168128b4a3ce0f3884d21348cc23303458d16),
(0xa30d327e, 0x1ef3518e700019006510a446510f2c3cb132e4cb984661198466118000), (0x250d327e, 0x4d2243e88f9698898654c1bbe32a53e4ceba671631f692c680f8d4084693423468d1a3468d1a38fa63e4c7131c3870e1c7879e3c3c91224), (0xa21d327e, 0x3469ef0058b162c58b16), (0xc52d327e, 0x3cf0f38),
(0xe52d327e, 0x1e78f99a3c79c1e), (0xf62d327e, 0x79f1450201a8102040), (0x710e327e, 0x2c58b1660fa9a2d00b40), (0xf10e327e, 0xb162d0251a),
(0xd30e327e, 0x2318e8fc6), (0xe30e327e, 0x18468cc0000), (0xf30e327e, 0x2a404688f933ef18046), (0xc40e327e, 0x1a84bfb2edcc2),
(0xa40e327e, 0x34693363098590fcc85029448507951e54097025c9a126849a13484997f), (0xe40e327e, 0x6a12ff21f42), (0xc50e327e, 0x79c3fafd9e), (0xe50e327e, 0x79c1e),
(0xf60e327e, 0x102022), (0xe51e327e, 0xf387fdfd3c79c1e), (0xc52e327e, 0x1e38fd9a3c7921e), (0xe52e327e, 0x24),
(0xf62e327e, 0x10253a), (0x830f327e, 0x3ea583061ac3d8c76b060ca232887831e5900ac3cb132e4cb8046011a3308cc1830), (0xc30f327e, 0x81e057d63303d01c6), (0xd30f327e, 0x251a330)]
def rootTr7p7 : RecordPage := #[
(0x840f327e, 0x68b2610983f4cd2131b21448507951e54097025d093424c9a131709334), (0xc40f327e, 0x104903509a42), (0xc50f327e, 0x106c1679c1e), (0x460f327e, 0xb162c58f163d05c220988462c4a05345a0f2d01f40),
(0x560f327e, 0x58b162c78b1e8361164d04c62c0207345a112d29f4a), (0xd60f327e, 0x8101f4a), (0xe51f327e, 0x10251e705a133c78f38), (0xc52f327e, 0x409479c24),
(0xe52f327e, 0x204a3cf0b1a3c78f24), (0xf62f327e, 0x812a01a8102040), (0xa50c427e, 0xf1c0c68f243c78d16948a5224d0ba6854c463118f1e3c78b1e3c79224), (0xb50c427e, 0xf1e346914a45293344cd23068c18f1e3c78f1e3479224),
(0xf65c427e, 0x13204c990ccc), (0xa30e427e, 0x78e0de219e3cb0f3060ca232890dc64263265c9971e3c796243c78f303c7962c), (0xa40e427e, 0x3c70f1c3c90f1e84d2c887e42808a2428690eb472412e04b8f423d08f423d0932a), (0xa50e427e, 0x187f94f8439b192d3c7a137f6544b2914468a5224d10a67243460d18f1e3c78f1a3c79c38),
(0xb50e427e, 0x1e3929f0873e325e78f1e78f0b3fe8a5229499a266919098d139e3c78f1e7890f1e3c59c38), (0xf65e427e, 0x40407a6408114c0), (0xa30d527e, 0x4c7d29f487d0204488c9900007961e5915c64363265c99740810223281018408101932), (0xb50d527e, 0x4c7d21f447d02022952911a3479e1e7899a2669190d8d16c08102040948a0403501122),
(0xc65d527e, 0x1e9929045f2a54a), (0xe65d527e, 0x13254633264c), (0xb50c437e, 0xf1e7eded80ea046b01d466ea108842003000c0f1e3c78f1e3479c38), (0xf61c437e, 0x9528f20),
(0xa30e437e, 0xf3c3c7961e8c7bb288ca23000c00265c9971e3d196463d18f463d1962c), (0xa40e437e, 0x78e1e7898473c7933490a24288de13570812e04b8f1e3c78f263c7932a), (0xb50e437e, 0x3c70f3c7d021260c469e3c59f380ea03a84d5c28e403000c0f1e3c78f1e3c59c38), (0xf61e437e, 0x9928f4c992a54a)]
def rootTr7 : Records := #[rootTr7p0, rootTr7p1, rootTr7p2, rootTr7p3, rootTr7p4, rootTr7p5, rootTr7p6, rootTr7p7]
def testrootTr7 : ℕ → Bool := testAt rootT bsrootT 6 rootTr6 rootTr7 6 9
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c0 : checkBlock testrootTr7 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c1 : checkBlock testrootTr7 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c2 : checkBlock testrootTr7 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c3 : checkBlock testrootTr7 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c4 : checkBlock testrootTr7 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c5 : checkBlock testrootTr7 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c6 : checkBlock testrootTr7 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c7 : checkBlock testrootTr7 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c8 : checkBlock testrootTr7 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c9 : checkBlock testrootTr7 4 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c10 : checkBlock testrootTr7 4 40 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c11 : checkBlock testrootTr7 4 44 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c12 : checkBlock testrootTr7 4 48 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c13 : checkBlock testrootTr7 4 52 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c14 : checkBlock testrootTr7 4 56 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c15 : checkBlock testrootTr7 4 60 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c16 : checkBlock testrootTr7 4 64 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c17 : checkBlock testrootTr7 4 68 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c18 : checkBlock testrootTr7 4 72 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c19 : checkBlock testrootTr7 4 76 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c20 : checkBlock testrootTr7 4 80 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c21 : checkBlock testrootTr7 4 84 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c22 : checkBlock testrootTr7 4 88 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c23 : checkBlock testrootTr7 4 92 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c24 : checkBlock testrootTr7 4 96 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c25 : checkBlock testrootTr7 4 100 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c26 : checkBlock testrootTr7 4 104 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c27 : checkBlock testrootTr7 4 108 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c28 : checkBlock testrootTr7 4 112 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c29 : checkBlock testrootTr7 4 116 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c30 : checkBlock testrootTr7 4 120 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c31 : checkBlock testrootTr7 4 124 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c32 : checkBlock testrootTr7 4 128 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c33 : checkBlock testrootTr7 4 132 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c34 : checkBlock testrootTr7 4 136 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c35 : checkBlock testrootTr7 4 140 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c36 : checkBlock testrootTr7 4 144 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c37 : checkBlock testrootTr7 4 148 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c38 : checkBlock testrootTr7 4 152 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c39 : checkBlock testrootTr7 4 156 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c40 : checkBlock testrootTr7 4 160 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c41 : checkBlock testrootTr7 4 164 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c42 : checkBlock testrootTr7 4 168 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c43 : checkBlock testrootTr7 4 172 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c44 : checkBlock testrootTr7 4 176 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c45 : checkBlock testrootTr7 4 180 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c46 : checkBlock testrootTr7 4 184 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c47 : checkBlock testrootTr7 4 188 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c48 : checkBlock testrootTr7 4 192 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c49 : checkBlock testrootTr7 4 196 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c50 : checkBlock testrootTr7 4 200 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c51 : checkBlock testrootTr7 4 204 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c52 : checkBlock testrootTr7 4 208 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c53 : checkBlock testrootTr7 4 212 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c54 : checkBlock testrootTr7 4 216 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c55 : checkBlock testrootTr7 4 220 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c56 : checkBlock testrootTr7 4 224 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c57 : checkBlock testrootTr7 4 228 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c58 : checkBlock testrootTr7 4 232 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c59 : checkBlock testrootTr7 4 236 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c60 : checkBlock testrootTr7 4 240 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c61 : checkBlock testrootTr7 4 244 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr7c62 : checkBlock testrootTr7 4 248 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootTr7 : LayerOK rootT 7 rootTr7 := by
  apply layer_of_block (bs := bsrootT) (k := 6) (old := rootTr6) (cw := 6) (rw := 9) (by decide +kernel) vbsrootT vrootTr6
  exact @block_merge testrootTr7 0 252 4 (@block_merge testrootTr7 0 124 128 (@block_merge testrootTr7 0 60 64 (@block_merge testrootTr7 0 28 32 (@block_merge testrootTr7 0 12 16 (@block_merge testrootTr7 0 4 8 rootTr7c0 (@block_merge testrootTr7 4 4 4 rootTr7c1 rootTr7c2)) (@block_merge testrootTr7 12 8 8 (@block_merge testrootTr7 12 4 4 rootTr7c3 rootTr7c4) (@block_merge testrootTr7 20 4 4 rootTr7c5 rootTr7c6))) (@block_merge testrootTr7 28 16 16 (@block_merge testrootTr7 28 8 8 (@block_merge testrootTr7 28 4 4 rootTr7c7 rootTr7c8) (@block_merge testrootTr7 36 4 4 rootTr7c9 rootTr7c10)) (@block_merge testrootTr7 44 8 8 (@block_merge testrootTr7 44 4 4 rootTr7c11 rootTr7c12) (@block_merge testrootTr7 52 4 4 rootTr7c13 rootTr7c14)))) (@block_merge testrootTr7 60 32 32 (@block_merge testrootTr7 60 16 16 (@block_merge testrootTr7 60 8 8 (@block_merge testrootTr7 60 4 4 rootTr7c15 rootTr7c16) (@block_merge testrootTr7 68 4 4 rootTr7c17 rootTr7c18)) (@block_merge testrootTr7 76 8 8 (@block_merge testrootTr7 76 4 4 rootTr7c19 rootTr7c20) (@block_merge testrootTr7 84 4 4 rootTr7c21 rootTr7c22))) (@block_merge testrootTr7 92 16 16 (@block_merge testrootTr7 92 8 8 (@block_merge testrootTr7 92 4 4 rootTr7c23 rootTr7c24) (@block_merge testrootTr7 100 4 4 rootTr7c25 rootTr7c26)) (@block_merge testrootTr7 108 8 8 (@block_merge testrootTr7 108 4 4 rootTr7c27 rootTr7c28) (@block_merge testrootTr7 116 4 4 rootTr7c29 rootTr7c30))))) (@block_merge testrootTr7 124 64 64 (@block_merge testrootTr7 124 32 32 (@block_merge testrootTr7 124 16 16 (@block_merge testrootTr7 124 8 8 (@block_merge testrootTr7 124 4 4 rootTr7c31 rootTr7c32) (@block_merge testrootTr7 132 4 4 rootTr7c33 rootTr7c34)) (@block_merge testrootTr7 140 8 8 (@block_merge testrootTr7 140 4 4 rootTr7c35 rootTr7c36) (@block_merge testrootTr7 148 4 4 rootTr7c37 rootTr7c38))) (@block_merge testrootTr7 156 16 16 (@block_merge testrootTr7 156 8 8 (@block_merge testrootTr7 156 4 4 rootTr7c39 rootTr7c40) (@block_merge testrootTr7 164 4 4 rootTr7c41 rootTr7c42)) (@block_merge testrootTr7 172 8 8 (@block_merge testrootTr7 172 4 4 rootTr7c43 rootTr7c44) (@block_merge testrootTr7 180 4 4 rootTr7c45 rootTr7c46)))) (@block_merge testrootTr7 188 32 32 (@block_merge testrootTr7 188 16 16 (@block_merge testrootTr7 188 8 8 (@block_merge testrootTr7 188 4 4 rootTr7c47 rootTr7c48) (@block_merge testrootTr7 196 4 4 rootTr7c49 rootTr7c50)) (@block_merge testrootTr7 204 8 8 (@block_merge testrootTr7 204 4 4 rootTr7c51 rootTr7c52) (@block_merge testrootTr7 212 4 4 rootTr7c53 rootTr7c54))) (@block_merge testrootTr7 220 16 16 (@block_merge testrootTr7 220 8 8 (@block_merge testrootTr7 220 4 4 rootTr7c55 rootTr7c56) (@block_merge testrootTr7 228 4 4 rootTr7c57 rootTr7c58)) (@block_merge testrootTr7 236 8 8 (@block_merge testrootTr7 236 4 4 rootTr7c59 rootTr7c60) (@block_merge testrootTr7 244 4 4 rootTr7c61 rootTr7c62)))))) (show checkBlock testrootTr7 4 252 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def rootTr8p0 : RecordPage := #[
(0xc107e, 0x1e9931f029529f1e129e11c07c0a01e109e0f87436190ba691224267c793263c982a993264c98270a1264c118511f028878c1e07c6300d8c60c02c120702a64c9932e4c997485d217445d124488910f1e5c70f1e5ca9700d7465cba3465c015d0972e85093265c99326), (0xe107e, 0x1e9931f029529f1e1d9e1cc07c0a01e1b9e1a8cc622f16a6912131e4c793264c993424c9a1447c0a21e3078c4630623183060c1815a64c993264cb81447cfa2447ca0f1e0470f1e04a814604298d181020427050810085093265c99326), (0xc207e, 0x7a64c7c0254a7c78a2789e9a4487c7931e26a64c4b24c07c0201e34473c68d1a34453468d42349a1447c0221e30788718c106326302b4c070280000183060c00007d000328100f1e007801c003f3c78024003d01180008d193260109326850983060c1830), (0xd207e, 0x7a64c7c0254a7c7831e0c9a4487c7931e0c993194c701f0080783063c183184be5d3468b708b29a1447c0221e0c7834630578c98c2604b060c183060c1840610184461120408910f1e6018f1e60b1815584660c23464d09814e14260b980060c0030),
(0xe207e, 0x7a64c7c0254a7c7831e0c9a4487c7931e0c9931acd301f00807831e0c68d1a3508d268511f00887831e0d18c188c98c184c6016c183060c18306111844610184089120403c798063c798246119819e34660c132660998426109326850980060c0030), (0xf207e, 0x7a64c7c0254a7c790278fe9a4487c7931e3ea64c7b3cc07c0201e3b9e3475399a3508e29a1447c0221e3078c4630623263098c3060c180000020407cc80407cf8f1e00e0f1e00723460000046006f85080004d0801b583060c1830), (0xd307e, 0x1e9931f407cbd80797679729a4487c7931e5bc24cb584b39529f1e58abcf2b556a953a95469942993f11f27621e30793660c15c8298c2606c68d1a3468d193201f444ba28910f1e4a9c3c7926b1228f469a45b044804c990e854c9906ba3468d1a346), (0xe307e, 0x1e9931f407cdd8079b679b29a4487c7931e6bc24cd584d39529f1e689e67b3596c963a662a661c47c6221e3078c183060c263098c468d1a3468d18c447cfa2447c88f1e3070f1e3060c304c1a3000c304c98c2fd326300a3468d1a346),
(0xc407e, 0x3d654a7d01f3ce03c5deed75a69121f264c21d309339e11e9930f1e3c78f1e3878f1e3c78f1e3d11f396246309b8c6030621a630981e78f1e3cb0f1e5931644993224458e3591962c8d19638560658b16244c99637d32658a8f1e5878f1e), (0xe407e, 0x1099529f407d07810581c05fe9a4487c993087ec24cfb847a64c3c78f1e3c70f1e3c78f1c3c78f1e3c78e447c6224630623180c18c263098c1e3c78f1e3cb0c447cfa2447c80c4630f98d18c180c18c1a30e03244c98c3dd32630a8f1e5878f1e), (0xd507e, 0x1e8c9e8b9e8a9e89c461f0d859e4c786264c306424c3211e993263e7cfa54a94f9f4080f9f3e809a44890f9f1e3079cb18c2763000000026049814489122448910f1e6530f1e993191265199228d19940646a04064c9326652132691222448912244), (0xd217e, 0x1e9931f0a9529f1ea09e9fc47c3221e7d9e73c66aad63407c3a01e9e9e353b9c9a34712c9a3499348912131e4c793264c9934dd3264c9932608c2850a14285087407cfa0407ca0f1e9a9c3c7a66aa632f96cae52d24f25919890c7e3a0236ba142850a142),
(0xc317e, 0x7a64c7d01f0e807ace7acb11f0c8879fa79d2793498c922a54a7c7ac67ac35faed6eb357aac64fb0e326912131e4c793424c9a1264c9932609a64c993264cd05487cfa4487c88f1ea99c3c7aa2aa9f4da5c2a4c96142a398a2c6a1828d193264c99334), (0xd317e, 0x7a64c7d01f0e807841e1111f0c887841e107b35994962a54a7c7841e1177badcee36fb6c650b16326912131e4c79342849934de1264c993264c993264cd1a486921a4a692a4489528f1e6820f1e68a9a5ada4268d21426919a5a634668b93264c99334), (0xc417e, 0xa9529f407c3a06170781bfc47c322466bade31f4306269e9930f1e3c78f1e3878f1e3c78e1e3c78f1c3c9a4484c993264d0932684993264c982a78f1e3c98f1e552153e9121520557d542152a54a955ed54254aa142546155e552a54a8f1e4c78f1e), (0xc327e, 0x7a64c7c9a4487c7931ebfc47d0b8879fe79d6985a982f8d9529f1ec59ec4a6b7db5355eab1946c78d01f1a8078d1e3508d268468d16cd1a3458b163468d1a3528d4a7d00d40952a0403c78d1c3c78b244c98d263508d424c9a1423460d462cc234635873468d1a),
(0xd327e, 0x1e9931f269121f1e4c7b0311f43621e809e76a617a60ce6e54a7c7b327b2e9aeb734d5dadc653b2e3407c6a01e3478d42349a11a3468d1a346b2a68d1a3401f40348a0403c78d1e3470d64cf1e349132635093268508d4635918d18d00358f3468d1a), (0xe327e, 0x1e9931f269121f1e4c7b0711f43e21e819e77a618a60dee654a7c7b6e7b6a9ae29ab3194ac98d01f1a807b6678d429ca684732f974d1a22e7f3a6b2a68d1ad8c07cfa0407c88f1ed79c3c7b5ae1342d5ea6142d3c974a63471b42023463468d67f1f9d), (0xf327e, 0x7a64c7c9a4487c7931ec2c47d11887a0a79e29866983bd39529f1ee89ee7a6bba6afc654b363407c6a01ee69e350a769a11d4c268d67f3a68d162c5a040952b97039301f4ae3ca3c78b383c7b8a721422cd1342e1f063462cc37f1b7bbb3468d67f0f9d), (0xc427e, 0x1d99529f269121f264c22cb11f44e2466cae63261aa60f9e9930f1e3c78f1e3c78f1e3878f1e3d01f1a8068d1a3508d2684683060c68d1e3c78f243c7924c490264c8101275d275522448912264909224850921848192244890f1e4878f1e),
(0xe427e, 0x1e39529f269121f264c22cf11f4562466daee3261ba6109e9930f1e3c78f1e3878f1e3c78f1e3c70f407c6a07376668d429ea684770c1831a239e3c78f1e3c91c4070fa0407081c785c77dc3870e134271dd8509c2a7019c76dc3870b0f1e4878f1e), (0xd527e, 0x1ef59ef49e4c787264c3871e839e79c66eaf6326049811e993263e7cfa54a94f9f26912243e7d1223e7cfa21e3478d1a3468d421c9a100000004081020408100f1e7530f1e9931d79dd4a748a54a4c99d424c9a1427511d79624474ca0408102040), (0xc437e, 0x101f7a60269121f424d3f8511f45e21fc30627a61ca6119e9930f1e3c78f1c3c78f1e3c78e1e3c78f1e39ef9529f73f2fb5c4a6109ac3195aab67c68c78f1e3cf0f1e3929f3e9529f2039ed3868e383891326102132638a8e183918e188d18f1e7878f1e), (0xe437e, 0x101f7ae0269121f424d418511f466220430628a61da6129e9930f1e3c78f1e3c78f1e3c78f1c3df79529f74733b7c5a6109ac71962af68c68c78f1e3c78f3c7931e4a993254a79f57869e38789132679f34c99e2a7919e7c634678b0f1e7878f1e),
(0xf537e, 0x1ef19eec9e4c785424c2a11e849e7a800000026049811e993263e7d0203e7cfa026912243e7d1223e7cfa21efb9ef7f4f37b9c6a6149854659b4e34a952a54a9528f1e9930f1e453204044891404469122912112645222444489144444a54a952a54a)]
def rootTr8 : Records := #[rootTr8p0]
def testrootTr8 : ℕ → Bool := testAt rootT bsrootT 7 rootTr7 rootTr8 6 8
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr8c0 : checkBlock testrootTr8 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr8c1 : checkBlock testrootTr8 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr8c2 : checkBlock testrootTr8 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr8c3 : checkBlock testrootTr8 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr8c4 : checkBlock testrootTr8 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr8c5 : checkBlock testrootTr8 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr8c6 : checkBlock testrootTr8 1 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootTr8 : LayerOK rootT 8 rootTr8 := by
  apply layer_of_block (bs := bsrootT) (k := 7) (old := rootTr7) (cw := 6) (rw := 8) (by decide +kernel) vbsrootT vrootTr7
  exact @block_merge testrootTr8 0 25 7 (@block_merge testrootTr8 0 12 13 (@block_merge testrootTr8 0 4 8 rootTr8c0 (@block_merge testrootTr8 4 4 4 rootTr8c1 rootTr8c2)) (@block_merge testrootTr8 12 8 5 (@block_merge testrootTr8 12 4 4 rootTr8c3 rootTr8c4) (@block_merge testrootTr8 20 4 1 rootTr8c5 rootTr8c6))) (show checkBlock testrootTr8 7 25 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def rootTr9p0 : RecordPage := #[
(0x7e, 0x1e9931f632a53e3d79eb603eae01ea4f4f2c70be9a4487c7931e753266d9849978511f2b10f267918c79b18b24715306981)]
def rootTr9 : Records := #[rootTr9p0]
def testrootTr9 : ℕ → Bool := testAt rootT bsrootT 8 rootTr8 rootTr9 6 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootTr9c0 : checkBlock testrootTr9 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootTr9 : LayerOK rootT 9 rootTr9 := by
  apply layer_of_block (bs := bsrootT) (k := 8) (old := rootTr8) (cw := 6) (rw := 5) (by decide +kernel) vbsrootT vrootTr8
  exact @block_merge testrootTr9 0 1 31 rootTr9c0 (show checkBlock testrootTr9 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootT : Valid rootT := by
  apply bound_of_layers (bs := bsrootT) (last := rootTr9) (cw := 6) (rw := 0) (by decide +kernel) vbsrootT vrootTr9 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_16673.SignedCert.GraphT
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def columns : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def funValue : (Fin 6 → Bool) → Bool := (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209699520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))
def witness : Circuit := ⟨[
  ⟨.or, [0,1]⟩,
  ⟨.or, [0,2]⟩,
  ⟨.or, [1,3]⟩,
  ⟨.or, [2,3]⟩,
  ⟨.and, [7,8]⟩,
  ⟨.or, [0,10]⟩,
  ⟨.and, [6,9]⟩,
  ⟨.and, [11,4]⟩,
  ⟨.or, [10,5]⟩,
  ⟨.and, [12,14]⟩,
  ⟨.or, [13,15]⟩],16⟩

theorem size_witness : witness.size = 11 := rfl
theorem legal_witness : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 9000 in
set_option maxHeartbeats 4000000 in
theorem computes_witness : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = funValue x := by
  decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 4000000 in
theorem binary_bound (C : Circuit) (feasible : FanInTwo C)
    (correct : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = funValue x) : 10 ≤ Source.binaryCost C.gates := by
  have legal : ∀ g ∈ C.gates, Source.legal g := by
    intro g hg
    have h := feasible g hg
    rcases h with ⟨hop,arity⟩
    exact ⟨hop,arity⟩
  apply Source.binary_lb vrootT 0xfeeaeee0faeaeac0 columns funValue (by decide +kernel) (by decide +kernel) (by rfl) _ (by decide +kernel) _ C.gates C.output legal correct
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_meta_16673.SignedCert.GraphT

theorem PEqualNP.Outside.L_meta_16673 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209699520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4209699520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  obtain ⟨C,legal,lim,satisfies⟩ := h
  by_cases used : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g,hg,ng⟩ := used
    have fewer : PEqualNP.Outside.L_meta_16673.SignedCert.Source.binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_16673.SignedCert.Source.isBinary)).mpr
        ⟨g,hg,by simp [PEqualNP.Outside.L_meta_16673.SignedCert.Source.isBinary,ng]⟩
    have bound := PEqualNP.Outside.L_meta_16673.SignedCert.GraphT.binary_bound C legal satisfies
    have cnt := PEqualNP.Outside.L_meta_16673.SignedCert.GraphT.size_witness
    change C.gates.length ≤ s at lim
    exact ⟨PEqualNP.Outside.L_meta_16673.SignedCert.GraphT.witness,PEqualNP.Outside.L_meta_16673.SignedCert.GraphT.legal_witness,by omega,PEqualNP.Outside.L_meta_16673.SignedCert.GraphT.computes_witness⟩
  · refine ⟨C,?_,lim,satisfies⟩
    intro g hg
    obtain ⟨ops,arity⟩ := legal g hg
    refine ⟨?_,arity⟩
    rcases ops with yes|yes|no
    · exact Or.inl yes
    · exact Or.inr yes
    · exact (used ⟨g,hg,no⟩).elim
