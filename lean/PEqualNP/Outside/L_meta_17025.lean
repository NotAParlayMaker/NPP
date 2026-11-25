import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17025.SignedCert
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

abbrev W := BitVec 128

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

end PEqualNP.Outside.L_meta_17025.SignedCert

namespace PEqualNP.Outside.L_meta_17025.SignedCert

theorem norm_zero (m : W) : norm m 0 = 0 := by
  change norm m (0#128) = 0#128
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

end PEqualNP.Outside.L_meta_17025.SignedCert

namespace PEqualNP.Outside.L_meta_17025.SignedCert

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

end PEqualNP.Outside.L_meta_17025.SignedCert

namespace PEqualNP.Outside.L_meta_17025.SignedCert

def sep : List W → W → W → Bool
  | [], p, n => p == 0 || n == 0
  | x::r, p, n => (p == 0 || n == 0) ||
    (sep r (p &&& x) (n &&& x) && sep r (p &&& ~~~x) (n &&& ~~~x))

theorem some_bit {x : W} (hn : x ≠ 0) : ∃ i : Fin 128, x[i.val] = true := by
  by_contra! h
  apply hn
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simpa using h ⟨i,hi⟩

theorem sep_ok {ws : List W} {p n : W}
    (h : ∀ i j : Fin 128, p[i.val] = true → n[j.val] = true → ∃ w ∈ ws, w[i.val] ≠ w[j.val]) :
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

theorem op_agree {m a b z : W} {i j : Fin 128} (hm : m[i.val] = m[j.val])
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

end PEqualNP.Outside.L_meta_17025.SignedCert

namespace PEqualNP.Outside.L_meta_17025.SignedCert
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

end PEqualNP.Outside.L_meta_17025.SignedCert

namespace PEqualNP.Outside.L_meta_17025.SignedCert.Source
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
  · change reachable av (BitVec.allOnes 128 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 128)
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

def bit (k : Fin 128) (z : W) : Bool := z[k.val]
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 128) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#128)[k.val] = false; simp
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
    norm m z ∈ PEqualNP.Outside.L_meta_17025.SignedCert.ops m (norm m a) (norm m b) := by
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
    build (PEqualNP.Outside.L_meta_17025.SignedCert.ops m) (norm m t) k (bank m S) := by
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
    (rows : ∀ k : Fin 128, F (fun i => bit k (raw.getD i.val 0)) = bit k w)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (evals : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : b.cost ≤ binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ raw, holds raw.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have eval (k : Fin 128) :
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

end PEqualNP.Outside.L_meta_17025.SignedCert.Source

namespace PEqualNP.Outside.L_meta_17025.SignedCert
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
  let i := t % 128
  let j := t / 128 % 128
  (m.getLsbD i == m.getLsbD j) && (g.getLsbD i != g.getLsbD j) &&
    ws.all (fun x => x.getLsbD i == x.getLsbD j)

theorem clash_sound {m g : W} {ws : List W} {t k : ℕ}
    (yes : clash m g ws t = true) : Closed m g (k,ws) := by
  intro _ _ run
  let i : Fin 128 := ⟨t%128,Nat.mod_lt _ (by decide)⟩
  let j : Fin 128 := ⟨t/128%128,Nat.mod_lt _ (by decide)⟩
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

end PEqualNP.Outside.L_meta_17025.SignedCert

namespace PEqualNP.Outside.L_meta_17025.SignedCert

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

end PEqualNP.Outside.L_meta_17025.SignedCert

namespace PEqualNP.Outside.L_meta_17025.SignedCert

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

end PEqualNP.Outside.L_meta_17025.SignedCert

namespace PEqualNP.Outside.L_meta_17025.SignedCert

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

end PEqualNP.Outside.L_meta_17025.SignedCert

namespace PEqualNP.Outside.L_meta_17025.SignedCert

def evalWord {α : Type} (w : W) (f : W → α) : α :=
  Nat.rec (f 0) (fun j _ => f (BitVec.ofNat 128 (j+1))) w.toNat

theorem evalWord_eq {α : Type} (w : W) (f : W → α) : evalWord w f = f w := by
  unfold evalWord
  generalize h : w.toNat = t
  cases t with
  | zero =>
    change f 0 = f w
    apply congrArg f
    exact BitVec.eq_of_toNat_eq (by simpa using h.symm)
  | succ t =>
    change f (BitVec.ofNat 128 (t+1)) = f w
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
end PEqualNP.Outside.L_meta_17025.SignedCert

namespace PEqualNP.Outside.L_meta_17025.SignedCert

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
end PEqualNP.Outside.L_meta_17025.SignedCert

namespace PEqualNP.Outside.L_meta_17025.SignedCert

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
  Nat.rec (f 0) (fun j _ => f (BitVec.ofNat 128 (j+1))) w.toNat

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

end PEqualNP.Outside.L_meta_17025.SignedCert

namespace PEqualNP.Outside.L_meta_17025.SignedCert.GraphT
def T54 : Bound := ⟨0xff, [0x0, 0x55, 0x33, 0xf], 0x17, 4⟩
def bsT54 : Array Bound := [].toArray
theorem vbsT54 : ∀ s ∈ bsT54, Valid s := by
  intro s hs
  simp only [bsT54,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T54r3p0 : RecordPage := #[
(0xe, 0x0)]
def T54r3 : Records := #[T54r3p0]
def testT54r3 : ℕ → Bool := testAt T54 bsT54 2 (#[] : Records) T54r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T54r3c0 : checkBlock testT54r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT54r3 : LayerOK T54 3 T54r3 := by
  apply layer_of_block (bs := bsT54) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT54 (emptyOK _ _)
  exact @block_merge testT54r3 0 1 31 T54r3c0 (show checkBlock testT54r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT54 : Valid T54 := by
  apply bound_of_layers (bs := bsT54) (last := T54r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT54 vT54r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_17025.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_17025.SignedCert.GraphT
def T55 : Bound := ⟨0x3333, [0x0, 0x1111, 0x303, 0x33], 0x113, 4⟩
def bsT55 : Array Bound := [].toArray
theorem vbsT55 : ∀ s ∈ bsT55, Valid s := by
  intro s hs
  simp only [bsT55,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T55r3p0 : RecordPage := #[
(0xe, 0x0)]
def T55r3 : Records := #[T55r3p0]
def testT55r3 : ℕ → Bool := testAt T55 bsT55 2 (#[] : Records) T55r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T55r3c0 : checkBlock testT55r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT55r3 : LayerOK T55 3 T55r3 := by
  apply layer_of_block (bs := bsT55) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT55 (emptyOK _ _)
  exact @block_merge testT55r3 0 1 31 T55r3c0 (show checkBlock testT55r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT55 : Valid T55 := by
  apply bound_of_layers (bs := bsT55) (last := T55r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT55 vT55r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_17025.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_17025.SignedCert.GraphT
def T57 : Bound := ⟨0x555500000000, [0x0, 0x111100000000, 0x50500000000, 0x5500000000], 0x11500000000, 4⟩
def bsT57 : Array Bound := [].toArray
theorem vbsT57 : ∀ s ∈ bsT57, Valid s := by
  intro s hs
  simp only [bsT57,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T57r3p0 : RecordPage := #[
(0xe, 0x0)]
def T57r3 : Records := #[T57r3p0]
def testT57r3 : ℕ → Bool := testAt T57 bsT57 2 (#[] : Records) T57r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T57r3c0 : checkBlock testT57r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT57r3 : LayerOK T57 3 T57r3 := by
  apply layer_of_block (bs := bsT57) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT57 (emptyOK _ _)
  exact @block_merge testT57r3 0 1 31 T57r3c0 (show checkBlock testT57r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT57 : Valid T57 := by
  apply bound_of_layers (bs := bsT57) (last := T57r3) (cw := 1) (rw := 0) (by decide +kernel) vbsT57 vT57r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_17025.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_17025.SignedCert.GraphT
def T96 : Bound := ⟨0xffff, [0x0, 0x5555, 0x3333, 0xf0f, 0xff], 0x517, 5⟩
def bsT96 : Array Bound := [T54].toArray
theorem vbsT96 : ∀ s ∈ bsT96, Valid s := by
  intro s hs
  simp only [bsT96,List.mem_toArray] at hs
  exact (familyCons vT54 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT96 : Valid T96 := by
  apply bound_of_layers (bs := bsT96) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT96 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_17025.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_17025.SignedCert.GraphT
def T99 : Bound := ⟨0xff000000ff, [0x0, 0x5500000055, 0x3300000033, 0xf0000000f, 0xff], 0x1500000017, 5⟩
def bsT99 : Array Bound := [T54].toArray
theorem vbsT99 : ∀ s ∈ bsT99, Valid s := by
  intro s hs
  simp only [bsT99,List.mem_toArray] at hs
  exact (familyCons vT54 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT99 : Valid T99 := by
  apply bound_of_layers (bs := bsT99) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT99 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_17025.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_17025.SignedCert.GraphT
def T100 : Bound := ⟨0x333300003333, [0x0, 0x111100001111, 0x30300000303, 0x3300000033, 0x3333], 0x11100000113, 5⟩
def bsT100 : Array Bound := [T55].toArray
theorem vbsT100 : ∀ s ∈ bsT100, Valid s := by
  intro s hs
  simp only [bsT100,List.mem_toArray] at hs
  exact (familyCons vT55 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT100 : Valid T100 := by
  apply bound_of_layers (bs := bsT100) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT100 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_17025.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_17025.SignedCert.GraphT
def T101 : Bound := ⟨0x555500005555, [0x0, 0x111100001111, 0x50500000505, 0x5500000055, 0x5555], 0x11500000515, 5⟩
def bsT101 : Array Bound := [T57].toArray
theorem vbsT101 : ∀ s ∈ bsT101, Valid s := by
  intro s hs
  simp only [bsT101,List.mem_toArray] at hs
  exact (familyCons vT57 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT101 : Valid T101 := by
  apply bound_of_layers (bs := bsT101) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT101 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_17025.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_17025.SignedCert.GraphT
def T102 : Bound := ⟨0xffff00000000, [0x0, 0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000], 0x11500000000, 5⟩
def bsT102 : Array Bound := [T57].toArray
theorem vbsT102 : ∀ s ∈ bsT102, Valid s := by
  intro s hs
  simp only [bsT102,List.mem_toArray] at hs
  exact (familyCons vT57 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT102 : Valid T102 := by
  apply bound_of_layers (bs := bsT102) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsT102 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_17025.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_17025.SignedCert.GraphT
def T105 : Bound := ⟨0xf0f00000f0f, [0x0, 0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f], 0x10500000507, 6⟩
def bsT105 : Array Bound := [].toArray
theorem vbsT105 : ∀ s ∈ bsT105, Valid s := by
  intro s hs
  simp only [bsT105,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T105r3p0 : RecordPage := #[
(0x230c101e, 0x0), (0x330c101e, 0x0), (0x240c101e, 0x0), (0x340c101e, 0x0),
(0x30f101e, 0x0), (0x130f101e, 0x0), (0x40f101e, 0x0), (0x140f101e, 0x0),
(0x230c201e, 0x0), (0x330c201e, 0x0), (0x240c201e, 0x0), (0x340c201e, 0x0),
(0x30f201e, 0x0), (0x130f201e, 0x0), (0x40f201e, 0x0), (0x140f201e, 0x0),
(0x230c301e, 0x0), (0x330c301e, 0x0), (0x240c301e, 0x0), (0x340c301e, 0x0),
(0x30f301e, 0x0), (0x130f301e, 0x0), (0x40f301e, 0x0), (0x140f301e, 0x0),
(0x321c211e, 0x0), (0x240d211e, 0x0), (0x340d211e, 0x0), (0x240e211e, 0x0),
(0x340e211e, 0x0), (0x321c311e, 0x0), (0x240d311e, 0x0), (0x340d311e, 0x0)]
def T105r3p1 : RecordPage := #[
(0x240e311e, 0x0), (0x340e311e, 0x0), (0x321c321e, 0x0), (0x240d321e, 0x0),
(0x340d321e, 0x0), (0x240e321e, 0x0), (0x340e321e, 0x0)]
def T105r3 : Records := #[T105r3p0, T105r3p1]
def testT105r3 : ℕ → Bool := testAt T105 bsT105 2 (#[] : Records) T105r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r3c0 : checkBlock testT105r3 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r3c1 : checkBlock testT105r3 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r3c2 : checkBlock testT105r3 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r3c3 : checkBlock testT105r3 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r3c4 : checkBlock testT105r3 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r3c5 : checkBlock testT105r3 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r3c6 : checkBlock testT105r3 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r3c7 : checkBlock testT105r3 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r3c8 : checkBlock testT105r3 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r3c9 : checkBlock testT105r3 3 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT105r3 : LayerOK T105 3 T105r3 := by
  apply layer_of_block (bs := bsT105) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsT105 (emptyOK _ _)
  exact @block_merge testT105r3 0 39 25 (@block_merge testT105r3 0 20 19 (@block_merge testT105r3 0 8 12 (@block_merge testT105r3 0 4 4 T105r3c0 T105r3c1) (@block_merge testT105r3 8 4 8 T105r3c2 (@block_merge testT105r3 12 4 4 T105r3c3 T105r3c4))) (@block_merge testT105r3 20 8 11 (@block_merge testT105r3 20 4 4 T105r3c5 T105r3c6) (@block_merge testT105r3 28 4 7 T105r3c7 (@block_merge testT105r3 32 4 3 T105r3c8 T105r3c9)))) (show checkBlock testT105r3 25 39 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T105r4p0 : RecordPage := #[
(0xc101e, 0xe14181), (0xd101e, 0x0), (0xe101e, 0x0), (0xf101e, 0x1e34589),
(0xc201e, 0x2e54991), (0xd201e, 0x0), (0xe201e, 0x0), (0xf201e, 0x3e74d99),
(0xc301e, 0x4e951a1), (0xd301e, 0x0), (0xe301e, 0x0), (0xf301e, 0x5eb55a9),
(0xc211e, 0x31), (0xd211e, 0x1ab3), (0xe211e, 0x1cb7), (0xf211e, 0x31),
(0xc311e, 0x3b), (0xd311e, 0x1fbd), (0xe311e, 0x21c1), (0xf311e, 0x3b),
(0xc321e, 0x45), (0xd321e, 0x24c7), (0xe321e, 0x26cb), (0xf321e, 0x45)]
def T105r4 : Records := #[T105r4p0]
def testT105r4 : ℕ → Bool := testAt T105 bsT105 3 T105r3 T105r4 1 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r4c0 : checkBlock testT105r4 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r4c1 : checkBlock testT105r4 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r4c2 : checkBlock testT105r4 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r4c3 : checkBlock testT105r4 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r4c4 : checkBlock testT105r4 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r4c5 : checkBlock testT105r4 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT105r4 : LayerOK T105 4 T105r4 := by
  apply layer_of_block (bs := bsT105) (k := 3) (old := T105r3) (cw := 1) (rw := 6) (by decide +kernel) vbsT105 vT105r3
  exact @block_merge testT105r4 0 24 8 (@block_merge testT105r4 0 12 12 (@block_merge testT105r4 0 4 8 T105r4c0 (@block_merge testT105r4 4 4 4 T105r4c1 T105r4c2)) (@block_merge testT105r4 12 4 8 T105r4c3 (@block_merge testT105r4 16 4 4 T105r4c4 T105r4c5))) (show checkBlock testT105r4 8 24 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T105r5p0 : RecordPage := #[
(0x1e, 0xbedae99e58e17dd6d95d54d13cd2c91c50c1)]
def T105r5 : Records := #[T105r5p0]
def testT105r5 : ℕ → Bool := testAt T105 bsT105 4 T105r4 T105r5 1 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T105r5c0 : checkBlock testT105r5 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT105r5 : LayerOK T105 5 T105r5 := by
  apply layer_of_block (bs := bsT105) (k := 4) (old := T105r4) (cw := 1) (rw := 5) (by decide +kernel) vbsT105 vT105r4
  exact @block_merge testT105r5 0 1 31 T105r5c0 (show checkBlock testT105r5 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT105 : Valid T105 := by
  apply bound_of_layers (bs := bsT105) (last := T105r5) (cw := 1) (rw := 0) (by decide +kernel) vbsT105 vT105r5 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_17025.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_17025.SignedCert.GraphT
def T117 : Bound := ⟨0xffff0000ffff, [0x0, 0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff], 0x11500000517, 8⟩
def bsT117 : Array Bound := [T54, T55, T57, T96, T99, T100, T101, T102, T105].toArray
theorem vbsT117 : ∀ s ∈ bsT117, Valid s := by
  intro s hs
  simp only [bsT117,List.mem_toArray] at hs
  exact (familyCons vT54 <| familyCons vT55 <| familyCons vT57 <| familyCons vT96 <| familyCons vT99 <| familyCons vT100 <| familyCons vT101 <| familyCons vT102 <| familyCons vT105 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T117r4p0 : RecordPage := #[
(0x240840c103e, 0x0)]
def T117r4 : Records := #[T117r4p0]
def testT117r4 : ℕ → Bool := testAt T117 bsT117 3 (#[] : Records) T117r4 4 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T117r4c0 : checkBlock testT117r4 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT117r4 : LayerOK T117 4 T117r4 := by
  apply layer_of_block (bs := bsT117) (k := 3) (old := (#[] : Records)) (cw := 4) (rw := 1) (by decide +kernel) vbsT117 (emptyOK _ _)
  exact @block_merge testT117r4 0 1 31 T117r4c0 (show checkBlock testT117r4 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T117r5p0 : RecordPage := #[
(0x840c103e, 0x33a1), (0xa40c103e, 0x0), (0x842c103e, 0x1908), (0xa30c303e, 0x0),
(0x832c303e, 0x194a), (0xa30c313e, 0x0)]
def T117r5 : Records := #[T117r5p0]
def testT117r5 : ℕ → Bool := testAt T117 bsT117 4 T117r4 T117r5 4 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T117r5c0 : checkBlock testT117r5 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T117r5c1 : checkBlock testT117r5 2 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT117r5 : LayerOK T117 5 T117r5 := by
  apply layer_of_block (bs := bsT117) (k := 4) (old := T117r4) (cw := 4) (rw := 0) (by decide +kernel) vbsT117 vT117r4
  exact @block_merge testT117r5 0 6 26 (@block_merge testT117r5 0 4 2 T117r5c0 T117r5c1) (show checkBlock testT117r5 26 6 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T117r6p0 : RecordPage := #[
(0xc103e, 0x420a7296108414a628c23388e3390681842105314a), (0xc303e, 0x420874208984108620c03388e33a108414ea143108), (0xc313e, 0x420634208931a1052a108520ce33a1084196c142908)]
def T117r6 : Records := #[T117r6p0]
def testT117r6 : ℕ → Bool := testAt T117 bsT117 5 T117r5 T117r6 4 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T117r6c0 : checkBlock testT117r6 3 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT117r6 : LayerOK T117 6 T117r6 := by
  apply layer_of_block (bs := bsT117) (k := 5) (old := T117r5) (cw := 4) (rw := 3) (by decide +kernel) vbsT117 vT117r5
  exact @block_merge testT117r6 0 3 29 T117r6c0 (show checkBlock testT117r6 29 3 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def T117r7p0 : RecordPage := #[
(0x3e, 0x320ce8421084210840ca3390a4584210330ce4310e108414c51)]
def T117r7 : Records := #[T117r7p0]
def testT117r7 : ℕ → Bool := testAt T117 bsT117 6 T117r6 T117r7 4 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem T117r7c0 : checkBlock testT117r7 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT117r7 : LayerOK T117 7 T117r7 := by
  apply layer_of_block (bs := bsT117) (k := 6) (old := T117r6) (cw := 4) (rw := 2) (by decide +kernel) vbsT117 vT117r6
  exact @block_merge testT117r7 0 1 31 T117r7c0 (show checkBlock testT117r7 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vT117 : Valid T117 := by
  apply bound_of_layers (bs := bsT117) (last := T117r7) (cw := 4) (rw := 0) (by decide +kernel) vbsT117 vT117r7 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_17025.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_17025.SignedCert.GraphT
def rootT : Bound := ⟨0xffffffffffffffff, [0x0, 0x5555555555555555, 0x3333333333333333, 0xf0f0f0f0f0f0f0f, 0xff00ff00ff00ff, 0xffff0000ffff, 0xffffffff], 0x111011501130517, 9⟩
def bsrootT : Array Bound := [T117].toArray
theorem vbsrootT : ∀ s ∈ bsrootT, Valid s := by
  intro s hs
  simp only [bsrootT,List.mem_toArray] at hs
  exact (familyCons vT117 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootT : Valid rootT := by
  apply bound_of_layers (bs := bsrootT) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsrootT (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_17025.SignedCert.GraphT

namespace PEqualNP.Outside.L_meta_17025.SignedCert.GraphT
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def columns : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000]
def funValue : (Fin 6 → Bool) → Bool := (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276943592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))
def witness : Circuit := ⟨[
  ⟨.or, [0,1]⟩,
  ⟨.or, [0,2]⟩,
  ⟨.or, [7,4]⟩,
  ⟨.or, [2,5]⟩,
  ⟨.and, [6,9]⟩,
  ⟨.or, [10,1]⟩,
  ⟨.or, [10,7]⟩,
  ⟨.and, [12,3]⟩,
  ⟨.and, [11,8]⟩,
  ⟨.or, [14,13]⟩],15⟩

theorem size_witness : witness.size = 10 := rfl
theorem legal_witness : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 9000 in
set_option maxHeartbeats 4000000 in
theorem computes_witness : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = funValue x := by
  decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 4000000 in
theorem binary_bound (C : Circuit) (feasible : FanInTwo C)
    (correct : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = funValue x) : 9 ≤ Source.binaryCost C.gates := by
  have legal : ∀ g ∈ C.gates, Source.legal g := by
    intro g hg
    have h := feasible g hg
    rcases h with ⟨hop,arity⟩
    exact ⟨hop,arity⟩
  apply Source.binary_lb vrootT 0xfeeefeeafeecfae8feeefeeafeecfae8 columns funValue (by decide +kernel) (by decide +kernel) (by rfl) _ (by decide +kernel) _ C.gates C.output legal correct
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_meta_17025.SignedCert.GraphT

theorem PEqualNP.Outside.L_meta_17025 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276943592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276943592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  obtain ⟨C,legal,lim,satisfies⟩ := h
  by_cases used : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g,hg,ng⟩ := used
    have fewer : PEqualNP.Outside.L_meta_17025.SignedCert.Source.binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_17025.SignedCert.Source.isBinary)).mpr
        ⟨g,hg,by simp [PEqualNP.Outside.L_meta_17025.SignedCert.Source.isBinary,ng]⟩
    have bound := PEqualNP.Outside.L_meta_17025.SignedCert.GraphT.binary_bound C legal satisfies
    have cnt := PEqualNP.Outside.L_meta_17025.SignedCert.GraphT.size_witness
    change C.gates.length ≤ s at lim
    exact ⟨PEqualNP.Outside.L_meta_17025.SignedCert.GraphT.witness,PEqualNP.Outside.L_meta_17025.SignedCert.GraphT.legal_witness,by omega,PEqualNP.Outside.L_meta_17025.SignedCert.GraphT.computes_witness⟩
  · refine ⟨C,?_,lim,satisfies⟩
    intro g hg
    obtain ⟨ops,arity⟩ := legal g hg
    refine ⟨?_,arity⟩
    rcases ops with yes|yes|no
    · exact Or.inl yes
    · exact Or.inr yes
    · exact (used ⟨g,hg,no⟩).elim
