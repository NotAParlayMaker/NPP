import PEqualNP.Defs

-- Truth tables represent all 128 assignments to the seven inputs.
-- The lower bound allows a wire to be complemented at no cost.
-- Projecting a live circuit onto a restriction saves a binary gate for each
-- live wire that becomes constant. The recorded states enumerate the remaining
-- gate choices. The last theorem combines the bound with a 13-gate AND/OR circuit.

-- The live-set compression proof is adapted from L-meta-9136 and its credited sources.
namespace PEqualNP.Outside.L_meta_10714.SignedCert
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

end PEqualNP.Outside.L_meta_10714.SignedCert

namespace PEqualNP.Outside.L_meta_10714.SignedCert

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

end PEqualNP.Outside.L_meta_10714.SignedCert

namespace PEqualNP.Outside.L_meta_10714.SignedCert

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

end PEqualNP.Outside.L_meta_10714.SignedCert

namespace PEqualNP.Outside.L_meta_10714.SignedCert

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

end PEqualNP.Outside.L_meta_10714.SignedCert

namespace PEqualNP.Outside.L_meta_10714.SignedCert
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

end PEqualNP.Outside.L_meta_10714.SignedCert

namespace PEqualNP.Outside.L_meta_10714.SignedCert.Source
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
    norm m z ∈ PEqualNP.Outside.L_meta_10714.SignedCert.ops m (norm m a) (norm m b) := by
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
    build (PEqualNP.Outside.L_meta_10714.SignedCert.ops m) (norm m t) k (bank m S) := by
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

theorem binary_lb {b : Bound} (valid : Valid b) (w : W) (raw : List W) (F : (Fin 7 → Bool) → Bool)
    (nz : w ≠ 0) (no : w ≠ ~~~0) (dim : raw.length = 7)
    (stk : bank b.mask raw.toFinset ⊆ b.inputs.toFinset) (tg : norm b.mask w = b.goal)
    (rows : ∀ k : Fin 128, F (fun i => bit k (raw.getD i.val 0)) = bit k w)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (evals : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : b.cost ≤ binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ raw, holds raw.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have eval (k : Fin 128) :
      (gs.foldl step (raw.map (bit k))).getD o false = bit k (~~~(~~~w)) := by
    let x (i : Fin 7) := bit k (raw.getD i.val 0)
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

end PEqualNP.Outside.L_meta_10714.SignedCert.Source

namespace PEqualNP.Outside.L_meta_10714.SignedCert
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

end PEqualNP.Outside.L_meta_10714.SignedCert

namespace PEqualNP.Outside.L_meta_10714.SignedCert

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


end PEqualNP.Outside.L_meta_10714.SignedCert

namespace PEqualNP.Outside.L_meta_10714.SignedCert

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

end PEqualNP.Outside.L_meta_10714.SignedCert

namespace PEqualNP.Outside.L_meta_10714.SignedCert

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

end PEqualNP.Outside.L_meta_10714.SignedCert

namespace PEqualNP.Outside.L_meta_10714.SignedCert

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
end PEqualNP.Outside.L_meta_10714.SignedCert

namespace PEqualNP.Outside.L_meta_10714.SignedCert

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
end PEqualNP.Outside.L_meta_10714.SignedCert

namespace PEqualNP.Outside.L_meta_10714.SignedCert

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

end PEqualNP.Outside.L_meta_10714.SignedCert

namespace PEqualNP.Outside.L_meta_10714.SignedCert

def shifted (p : ℕ) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 128 => w.getLsbD ((p >>> (7*i.val)) % 128)))).cast List.length_ofFn

theorem shifted_bit (p : ℕ) (w : W) {i : ℕ} (hi : i < 128) :
    (shifted p w).getLsbD i = w.getLsbD ((p >>> (7*i)) % 128) := by
  simp only [shifted,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,↓reduceDIte,Option.getD_some]

theorem shifted_and (p : ℕ) (x y : W) : shifted p (x &&& y) = shifted p x &&& shifted p y := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  change (shifted p (x &&& y)).getLsbD i = (shifted p x &&& shifted p y).getLsbD i
  simp only [BitVec.getLsbD_and,shifted_bit _ _ hi]

theorem shifted_neg (p : ℕ) (x : W) : shifted p (~~~x) = ~~~(shifted p x) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  change (shifted p (~~~x)).getLsbD i = (~~~(shifted p x)).getLsbD i
  rw [shifted_bit _ _ hi,BitVec.getLsbD_not,BitVec.getLsbD_not,shifted_bit _ _ hi]
  simp only [hi,decide_true,Nat.mod_lt _ (by decide : 0 < 128),Bool.true_and]

theorem shifted_phase (p : ℕ) (s : Bool) (x : W) : shifted p (phase s x) = phase s (shifted p x) := by
  cases s <;> simp [phase,shifted_neg]

theorem shifted_norm {p : ℕ} {m q : W} (sub : q &&& shifted p m = q) (x : W) :
    norm q (shifted p (norm m x)) = norm q (shifted p x) := by
  obtain ⟨s,e⟩ := norm_cases m x
  rw [e,shifted_and,shifted_phase]
  have cut : q &&& (shifted p m &&& phase s (shifted p x)) = q &&& phase s (shifted p x) := by
    rw [← BitVec.and_assoc,sub]
  rw [norm_of_mask cut]
  cases s <;> simp [phase,norm_neg]

theorem shifted_op {p : ℕ} {m q a b z : W} (sub : q &&& shifted p m = q)
    (hz : z ∈ ops m a b) : norm q (shifted p z) ∈ ops q (norm q (shifted p a)) (norm q (shifted p b)) := by
  obtain ⟨s,t,rfl⟩ := op_cases hz
  rw [shifted_norm sub,shifted_and,shifted_phase,shifted_phase]
  exact norm_gate .. 

theorem shifted_build {p : ℕ} {m q g : W} {k : ℕ} {S A : Finset W}
    (sub : q &&& shifted p m = q) (run : build (ops m) g k S) (zero : (0 : W) ∈ A)
    (stock : ∀ w ∈ S, norm q (shifted p w) ∈ A) : build (ops q) (norm q (shifted p g)) k A := by
  induction k generalizing S A with
  | zero => exact stock g run
  | succ k ih =>
    rcases run with skip | ⟨a,ha,b,hb,_,z,hz,tail⟩
    · exact Or.inl (ih skip zero stock)
    have hA := stock a ha
    have hB := stock b hb
    have hZ := shifted_op sub hz
    by_cases e : norm q (shifted p a) = norm q (shifted p b)
    · rw [e] at hZ
      have hzA : norm q (shifted p z) ∈ A := by
        rcases op_same hZ with h | h
        · rwa [h]
        · rwa [h,norm_idem]
      apply Or.inl (ih tail zero ?_)
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hzA
      · exact stock _ hw
    · refine Or.inr ⟨_,hA,_,hB,e,_,hZ,ih tail (Finset.mem_insert_of_mem zero) ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Finset.mem_insert_self ..
      · exact Finset.mem_insert_of_mem (stock _ hw)

theorem transfer {src dest : Bound} (v : Valid src) (p : ℕ) (le : dest.cost ≤ src.cost)
    (sub : src.mask &&& shifted p dest.mask = src.mask)
    (eq : norm src.mask (shifted p dest.goal) = src.goal)
    (zero : (0 : W) ∈ src.inputs)
    (stock : dest.inputs.all (fun w => src.inputs.contains (norm src.mask (shifted p w))) = true) :
    Valid dest := by
  intro k hk run
  have moved := shifted_build sub run (List.mem_toFinset.mpr zero)
    (fun w hw => List.mem_toFinset.mpr (List.contains_iff_mem.mp
      (List.all_eq_true.mp stock w (List.mem_toFinset.mp hw))))
  rw [eq] at moved
  exact v _ (lt_of_lt_of_le hk le) moved

end PEqualNP.Outside.L_meta_10714.SignedCert

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
open Source PEqualNP.CircuitLowerBounds
def rootA : Bound := ⟨0xffffffffffffffffffffffffffffffff, [0x0, 0x55555555555555555555555555555555, 0x33333333333333333333333333333333, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0xff00ff00ff00ff00ff00ff00ff00ff, 0xffff0000ffff0000ffff0000ffff, 0xffffffff00000000ffffffff, 0xffffffffffffffff], 0x100010011010355ff, 12⟩
def cols : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
def graph (x : Fin 7 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem edge_eq : ∀ x : Fin 7 → Bool, decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = graph x := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem size_lb (h : Valid rootA) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, Source.legal g) (ev : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = graph x) :
    12 ≤ binaryCost gs := by
  apply binary_lb h 0xfffffffffffffffefffeffeefefcaa00 cols graph (by decide +kernel) (by decide +kernel) (by rfl) _ (by decide +kernel) _ gs o hg ev
  · decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A0 : Bound := ⟨0x3300330000, [0x0, 0x1100110000, 0x300030000, 0x330000], 0x1100030000, 3⟩
def bsA0 : Array Bound := [].toArray
theorem vbsA0 : ∀ s ∈ bsA0, Valid s := by
  intro s hs
  simp only [bsA0,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A0r2p0 : RecordPage := #[
(0xe, 0x0)]
def A0r2 : Records := #[A0r2p0]
def testA0r2 : ℕ → Bool := testAt A0 bsA0 1 (#[] : Records) A0r2 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A0r2c0 : checkBlock testA0r2 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA0r2 : LayerOK A0 2 A0r2 := by
  apply layer_of_block (bs := bsA0) (k := 1) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsA0 (emptyOK _ _)
  exact @block_merge testA0r2 0 1 31 A0r2c0 (show checkBlock testA0r2 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA0 : Valid A0 := by
  apply bound_of_layers (bs := bsA0) (last := A0r2) (cw := 1) (rw := 0) (by decide +kernel) vbsA0 vA0r2 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A7 : Bound := ⟨0x12001200120012, [0x0, 0x2000200020002, 0x1200000012, 0x120012], 0x1000020012, 3⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA7 : Valid A7 := by
  apply transfer vA0 0x1a240000a040000000000000000018a100008810000000000000000000000000000 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A8 : Bound := ⟨0x30300000303, [0x0, 0x10100000101, 0x300000003, 0x303], 0x100000103, 4⟩
def bsA8 : Array Bound := [].toArray
theorem vbsA8 : ∀ s ∈ bsA8, Valid s := by
  intro s hs
  simp only [bsA8,List.mem_toArray] at hs
  exact (familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A8r3p0 : RecordPage := #[
(0xe, 0x0)]
def A8r3 : Records := #[A8r3p0]
def testA8r3 : ℕ → Bool := testAt A8 bsA8 2 (#[] : Records) A8r3 1 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A8r3c0 : checkBlock testA8r3 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA8r3 : LayerOK A8 3 A8r3 := by
  apply layer_of_block (bs := bsA8) (k := 2) (old := (#[] : Records)) (cw := 1) (rw := 1) (by decide +kernel) vbsA8 (emptyOK _ _)
  exact @block_merge testA8r3 0 1 31 A8r3c0 (show checkBlock testA8r3 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA8 : Valid A8 := by
  apply bound_of_layers (bs := bsA8) (last := A8r3) (cw := 1) (rw := 0) (by decide +kernel) vbsA8 vA8r3 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A10 : Bound := ⟨0xa0005000a0005, [0x0, 0x500000005, 0x2000100020001, 0xa0005], 0x100020005, 4⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA10 : Valid A10 := by
  apply transfer vA8 0x19b10000000000112000000000000000000000000000000000000000099100000000000100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A12 : Bound := ⟨0x303000003030000, [0x0, 0x101000001010000, 0x3000000030000, 0x3030000], 0x1000001030000, 4⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA12 : Valid A12 := by
  apply transfer vA8 0x1cb8000000000018b0000000000000000000000000000000000000000c9800000000000890 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A13 : Bound := ⟨0x3030000000000000303, [0x0, 0x1010000000000000101, 0x30000000000000003, 0x303], 0x10000000000000103, 4⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA13 : Valid A13 := by
  apply transfer vA8 0x24c8000000000020c000000000000000000000000000000000000000048800000000000080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A14 : Bound := ⟨0x500050000000000050005, [0x0, 0x100010000000000010001, 0x50000000000000005, 0x50005], 0x10000000000010005, 4⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA14 : Valid A14 := by
  apply transfer vA8 0x29500000000000214000000000000000000000000000000000000000091000000000000100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A15 : Bound := ⟨0x5000500000000000a000a, [0x0, 0xa000a, 0x100010000000000020002, 0x5000000000000000a], 0x1000000000002000a, 4⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA15 : Valid A15 := by
  apply transfer vA8 0x29500000000000214000000000000000000000000000000000000000099100000000000181 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A16 : Bound := ⟨0x900090000000000090009, [0x0, 0x100010000000000010001, 0x90000000000000009, 0x90009], 0x10000000000010009, 4⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA16 : Valid A16 := by
  apply transfer vA8 0x29d0000000000021c000000000000000000000000000000000000000099000000000000180 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A17 : Bound := ⟨0xa000500000000000a0005, [0x0, 0x50000000000000005, 0x200010000000000020001, 0xa0005], 0x10000000000020005, 4⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA17 : Valid A17 := by
  apply transfer vA8 0x29d10000000000214000000000000000000000000000000000000000099100000000000100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A24 : Bound := ⟨0x3000000030000000300000003, [0x0, 0x1000000010000000100000001, 0x30000000000000003, 0x300000003], 0x10000000100000003, 4⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA24 : Valid A24 := by
  apply transfer vA8 0x30e0000000000020c00000000000000000000000000000000000000010a000000000000080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A34 : Bound := ⟨0x101000001010000010100000101, [0x0, 0x1000000010000000100000001, 0x1010000000000000101, 0x10100000101], 0x10000000100000101, 4⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA34 : Valid A34 := by
  apply transfer vA8 0x34600000000000244000000000000000000000000000000000000000142000000000000400 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A229 : Bound := ⟨0xf000f000f000f, [0x0, 0x5000500050005, 0x3000300030003, 0xf0000000f, 0xf000f], 0x100010003000f, 4⟩
def bsA229 : Array Bound := [A10].toArray
theorem vbsA229 : ∀ s ∈ bsA229, Valid s := by
  intro s hs
  simp only [bsA229,List.mem_toArray] at hs
  exact (familyCons vA10 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA229 : Valid A229 := by
  apply bound_of_layers (bs := bsA229) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA229 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A240 : Bound := ⟨0x505050505050505, [0x0, 0x101010101010101, 0x5000500050005, 0x50500000505, 0x5050505], 0x1000101010505, 4⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA240 : Valid A240 := by
  apply transfer vA229 0x74c9c3000000000000000000000054894200000000000000000000003448c100000000000000000000001408400 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A249 : Bound := ⟨0xf0f00000f0f, [0x0, 0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f], 0x10000050f, 5⟩
def bsA249 : Array Bound := [A8].toArray
theorem vbsA249 : ∀ s ∈ bsA249, Valid s := by
  intro s hs
  simp only [bsA249,List.mem_toArray] at hs
  exact (familyCons vA8 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA249 : Valid A249 := by
  apply bound_of_layers (bs := bsA249) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA249 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A251 : Bound := ⟨0x5a005a005a005a, [0x0, 0xa000a000a000a, 0x12001200120012, 0x5a0000005a, 0x5a005a], 0x100002005a, 5⟩
def bsA251 : Array Bound := [A7].toArray
theorem vbsA251 : ∀ s ∈ bsA251, Valid s := by
  intro s hs
  simp only [bsA251,List.mem_toArray] at hs
  exact (familyCons vA7 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A251r4p0 : RecordPage := #[
(0x1e, 0x0)]
def A251r4 : Records := #[A251r4p0]
def testA251r4 : ℕ → Bool := testAt A251 bsA251 3 (#[] : Records) A251r4 0 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A251r4c0 : checkBlock testA251r4 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA251r4 : LayerOK A251 4 A251r4 := by
  apply layer_of_block (bs := bsA251) (k := 3) (old := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA251 (emptyOK _ _)
  exact @block_merge testA251r4 0 1 31 A251r4c0 (show checkBlock testA251r4 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA251 : Valid A251 := by
  apply bound_of_layers (bs := bsA251) (last := A251r4) (cw := 0) (rw := 0) (by decide +kernel) vbsA251 vA251r4 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A254 : Bound := ⟨0xf0f00000f0f0000, [0x0, 0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000], 0x1000001030000, 5⟩
def bsA254 : Array Bound := [A12].toArray
theorem vbsA254 : ∀ s ∈ bsA254, Valid s := by
  intro s hs
  simp only [bsA254,List.mem_toArray] at hs
  exact (familyCons vA12 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA254 : Valid A254 := by
  apply bound_of_layers (bs := bsA254) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA254 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A257 : Bound := ⟨0xf0f0000000000000f0f, [0x0, 0x5050000000000000505, 0x3030000000000000303, 0xf000000000000000f, 0xf0f], 0x1000000000000050f, 5⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA257 : Valid A257 := by
  apply transfer vA249 0x972a4c80000000870a0c000000000000000000000000000000000000162848800000000608080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A259 : Bound := ⟨0xf000f00000000000f000f, [0x0, 0x500050000000000050005, 0x300030000000000030003, 0xf000000000000000f, 0xf000f], 0x1000000000003000f, 5⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA259 : Valid A259 := by
  apply transfer vA249 0xa7469500000000870614000000000000000000000000000000000000264491000000000604100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A262 : Bound := ⟨0x5500550000000000550055, [0x0, 0x1100110000000000110011, 0x500050000000000050005, 0x550000000000000055, 0x550055], 0x10000000000010055, 5⟩
def bsA262 : Array Bound := [A14].toArray
theorem vbsA262 : ∀ s ∈ bsA262, Valid s := by
  intro s hs
  simp only [bsA262,List.mem_toArray] at hs
  exact (familyCons vA14 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA262 : Valid A262 := by
  apply bound_of_layers (bs := bsA262) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA262 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A269 : Bound := ⟨0x30303030000000003030303, [0x0, 0x10101010000000001010101, 0x300030000000000030003, 0x3030000000000000303, 0x3030303], 0x10000000001030103, 5⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA269 : Valid A269 := by
  apply transfer vA249 0xb3624c80000000a3420c000000000000000000000000000000000000326048800000002240080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A270 : Bound := ⟨0x50505050000000005050505, [0x0, 0x10101010000000001010101, 0x500050000000000050005, 0x5050000000000000505, 0x5050505], 0x10000000001010505, 5⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA270 : Valid A270 := by
  apply transfer vA249 0xb5629500000000952214000000000000000000000000000000000000346091000000001420100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A273 : Bound := ⟨0xf0000000f000000f0000000f0, [0x0, 0x5000000050000005000000050, 0x3000000030000003000000030, 0xf0000000f0, 0xf00000000000000f0], 0x100000010000000f0, 5⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA273 : Valid A273 := by
  apply transfer vA262 0x18c062018406000000000000000010c04201040400000000000000000000000000000000000000000000000000000000000000000000000009c026009402400000000000000001c0060014004 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A293 : Bound := ⟨0xf00000000000f000f00000000000f, [0x0, 0x50000000000050005000000000005, 0x30000000000030003000000000003, 0xf000000000000000f, 0xf00000000000f], 0x1000100000000000f, 5⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA293 : Valid A293 := by
  apply transfer vA262 0x1cc07201c407000000000000000010c0420104040000000000000000000000000000000000000000000000000000000000000000000000000cc03200c403000000000000000000c0020004000 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A308 : Bound := ⟨0x303000003030000030300000303, [0x0, 0x101000001010000010100000101, 0x3000000030000000300000003, 0x3030000000000000303, 0x30300000303], 0x10000000100000103, 7⟩
def bsA308 : Array Bound := [A8, A13, A24, A34].toArray
theorem vbsA308 : ∀ s ∈ bsA308, Valid s := by
  intro s hs
  simp only [bsA308,List.mem_toArray] at hs
  exact (familyCons vA8 <| familyCons vA13 <| familyCons vA24 <| familyCons vA34 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A308r3p0 : RecordPage := #[
(0x240830c101e, 0x0), (0x240840c101e, 0x0), (0x31831c101e, 0x94), (0x31841c101e, 0x4),
(0x240840c201e, 0x0), (0x31841c201e, 0x2), (0x240840c211e, 0x0), (0x31841c211e, 0x2)]
def A308r3 : Records := #[A308r3p0]
def testA308r3 : ℕ → Bool := testAt A308 bsA308 2 (#[] : Records) A308r3 2 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A308r3c0 : checkBlock testA308r3 8 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA308r3 : LayerOK A308 3 A308r3 := by
  apply layer_of_block (bs := bsA308) (k := 2) (old := (#[] : Records)) (cw := 2) (rw := 1) (by decide +kernel) vbsA308 (emptyOK _ _)
  exact @block_merge testA308r3 0 8 24 A308r3c0 (show checkBlock testA308r3 24 8 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A308r4p0 : RecordPage := #[
(0x830c101e, 0x1), (0xa30c101e, 0x0), (0x840c101e, 0x23), (0xa40c101e, 0x0),
(0x831c101e, 0xaa2), (0x841c101e, 0xe20), (0x832c101e, 0xab2), (0x842c101e, 0xe30),
(0xa30c201e, 0x0), (0x840c201e, 0x49), (0xa40c201e, 0x0), (0x841c201e, 0x1610),
(0x832c201e, 0xb34), (0x842c201e, 0x1630), (0xa30c301e, 0x0), (0xa40c301e, 0x0),
(0x832c301e, 0xf34), (0x842c301e, 0x16b2), (0xa30c211e, 0x0), (0x840c211e, 0x6d),
(0xa40c211e, 0x0), (0x841c211e, 0x1e10), (0x842c211e, 0x1e20), (0xa30c311e, 0x0),
(0xa40c311e, 0x0), (0x842c311e, 0x1ea2), (0xa30c321e, 0x0), (0xa40c321e, 0x0)]
def A308r4 : Records := #[A308r4p0]
def testA308r4 : ℕ → Bool := testAt A308 bsA308 3 A308r3 A308r4 2 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A308r4c0 : checkBlock testA308r4 8 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A308r4c8 : checkBlock testA308r4 8 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A308r4c16 : checkBlock testA308r4 8 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A308r4c24 : checkBlock testA308r4 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA308r4 : LayerOK A308 4 A308r4 := by
  apply layer_of_block (bs := bsA308) (k := 3) (old := A308r3) (cw := 2) (rw := 3) (by decide +kernel) vbsA308 vA308r3
  exact @block_merge testA308r4 0 28 4 (@block_merge testA308r4 0 16 12 (@block_merge testA308r4 0 8 8 A308r4c0 A308r4c8) (@block_merge testA308r4 16 8 4 A308r4c16 A308r4c24)) (show checkBlock testA308r4 4 28 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A308r5p0 : RecordPage := #[
(0xc101e, 0x43e1b8bc4c9340381506819a4), (0xc201e, 0x26d3397c4a4b20a84e2301592), (0xc301e, 0x8c4397c580304fa4e3b05180), (0xc211e, 0x2b5332b86a4a21489f4b81512),
(0xc311e, 0xcc432b87802058a9f5f85100), (0xc321e, 0xcc46ad4d80109bc9f6b93080)]
def A308r5 : Records := #[A308r5p0]
def testA308r5 : ℕ → Bool := testAt A308 bsA308 4 A308r4 A308r5 2 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A308r5c0 : checkBlock testA308r5 6 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA308r5 : LayerOK A308 5 A308r5 := by
  apply layer_of_block (bs := bsA308) (k := 4) (old := A308r4) (cw := 2) (rw := 5) (by decide +kernel) vbsA308 vA308r4
  exact @block_merge testA308r5 0 6 26 A308r5c0 (show checkBlock testA308r5 26 6 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A308r6p0 : RecordPage := #[
(0x1e, 0x2162095138c15647341)]
def A308r6 : Records := #[A308r6p0]
def testA308r6 : ℕ → Bool := testAt A308 bsA308 5 A308r5 A308r6 2 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A308r6c0 : checkBlock testA308r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA308r6 : LayerOK A308 6 A308r6 := by
  apply layer_of_block (bs := bsA308) (k := 5) (old := A308r5) (cw := 2) (rw := 3) (by decide +kernel) vbsA308 vA308r5
  exact @block_merge testA308r6 0 1 31 A308r6c0 (show checkBlock testA308r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA308 : Valid A308 := by
  apply bound_of_layers (bs := bsA308) (last := A308r6) (cw := 2) (rw := 0) (by decide +kernel) vbsA308 vA308r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A309 : Bound := ⟨0xa0005000a0005000a0005000a0005, [0x0, 0x5000000050000000500000005, 0x20001000200010002000100020001, 0xa000500000000000a0005, 0xa0005000a0005], 0x10000000100020005, 7⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA309 : Valid A309 := by
  apply transfer vA308 0x39f1000000000031600000000000000000000000000000000000000029d1000000000021400000000000000000000000000000000000000019b10000000000112000000000000000000000000000000000000000099100000000000100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A310 : Bound := ⟨0x500050000500050050005000050005, [0x0, 0x100010000100010010001000010001, 0x500050000000000050005, 0x50000000050000005000000005, 0x50005000050005], 0x10000001000010005, 7⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA310 : Valid A310 := by
  apply transfer vA308 0x3b740000000000336400000000000000000000000000000000000000295000000000002140000000000000000000000000000000000000001b340000000000132400000000000000000000000000000000000000091000000000000100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A373 : Bound := ⟨0xffff0000ffff0000, [0x0, 0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000], 0x1000001030000, 6⟩
def bsA373 : Array Bound := [A254].toArray
theorem vbsA373 : ∀ s ∈ bsA373, Valid s := by
  intro s hs
  simp only [bsA373,List.mem_toArray] at hs
  exact (familyCons vA254 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA373 : Valid A373 := by
  apply bound_of_layers (bs := bsA373) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA373 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A375 : Bound := ⟨0xff00ff0000000000ff00ff, [0x0, 0x5500550000000000550055, 0x3300330000000000330033, 0xf000f00000000000f000f, 0xff00000000000000ff, 0xff00ff], 0x100000000000300ff, 6⟩
def bsA375 : Array Bound := [A259].toArray
theorem vbsA375 : ∀ s ∈ bsA375, Valid s := by
  intro s hs
  simp only [bsA375,List.mem_toArray] at hs
  exact (familyCons vA259 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA375 : Valid A375 := by
  apply bound_of_layers (bs := bsA375) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA375 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A376 : Bound := ⟨0xff00ff00ff00ff00000000, [0x0, 0x5500550055005500000000, 0x3300330033003300000000, 0xf000f000f000f00000000, 0xff000000ff00000000, 0xff00ff00000000], 0x10001001100000000, 6⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA376 : Valid A376 := by
  apply transfer vA373 0xaf4eb52ab46a508f0e3428b0624000000000000000000000000000006ecdb326ac5a304e8d3224a852200000000000000000000000000000 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A378 : Bound := ⟨0xff000000ff000000ff000000ff, [0x0, 0x55000000550000005500000055, 0x33000000330000003300000033, 0xf0000000f0000000f0000000f, 0xff00000000000000ff, 0xff000000ff], 0x100000011000000ff, 6⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA378 : Valid A378 := by
  apply transfer vA375 0xcf8f362cb87260000000000000008f0e3428b0624000000000000000000000000000000000000000000000000000000000000000000000004e8d3224a85220000000000000000e0c3020a04200 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A379 : Bound := ⟨0xff000000ff00ff000000ff0000, [0x0, 0x55000000550055000000550000, 0x33000000330033000000330000, 0xf0000000f000f0000000f0000, 0xff000000ff0000, 0xff0000000000ff0000], 0x10001000000030000, 6⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA379 : Valid A379 := by
  apply transfer vA373 0xcf9b2e4c78b0e08f1a2c4870a0c000000000000000000000000000006ed9ab466c98b02e58a9426488900000000000000000000000000000 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A382 : Bound := ⟨0xf000f000f000f00f000f000f000f0, [0x0, 0x50005000500050050005000500050, 0x30003000300030030003000300030, 0xf000f000f000f0, 0xf0000000f000000f0000000f0, 0xf000f0000000000f000f0], 0x100000010000000f0, 6⟩
def bsA382 : Array Bound := [A273].toArray
theorem vbsA382 : ∀ s ∈ bsA382, Valid s := by
  intro s hs
  simp only [bsA382,List.mem_toArray] at hs
  exact (familyCons vA273 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA382 : Valid A382 := by
  apply bound_of_layers (bs := bsA382) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA382 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A383 : Bound := ⟨0x5500550055005500aa00aa00aa00aa, [0x0, 0xaa00aa00aa00aa, 0x110011001100110022002200220022, 0x5000500050005000a000a000a000a, 0x5500000055000000aa000000aa, 0x5500550000000000aa00aa], 0x100000000000200aa, 6⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA383 : Valid A383 := by
  apply transfer vA382 0xedd3970000000000000000000000ad52950000000000000000000000cd931600000000000000000000008d12140000000000000006ed59b10000000000000000000002e549910000000000000000000004e951a10000000000000000000000e141810000000 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A384 : Bound := ⟨0x5a005a005a005a005a005a005a005a, [0x0, 0xa000a000a000a000a000a000a000a, 0x120012001200120012001200120012, 0x5a0000005a0000005a0000005a, 0x5a005a00000000005a005a, 0x5a005a005a005a], 0x100002005a, 6⟩
def bsA384 : Array Bound := [A251].toArray
theorem vbsA384 : ∀ s ∈ bsA384, Valid s := by
  intro s hs
  simp only [bsA384,List.mem_toArray] at hs
  exact (familyCons vA251 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA384 : Valid A384 := by
  apply bound_of_layers (bs := bsA384) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA384 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A386 : Bound := ⟨0xaa00aa0055005500aa00aa00550055, [0x0, 0x5500550000000000550055, 0x220022001100110022002200110011, 0xa000a00050005000a000a00050005, 0xaa00000055000000aa00000055, 0xaa00aa00550055], 0x10000000000010055, 6⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA386 : Valid A386 := by
  apply transfer vA382 0xefd79f1000000000000000000000ad52950000000000000000000000cf971e10000000000000000000008d12140000000000000006ed59b10000000000000000000002c509100000000000000000000004e951a10000000000000000000000c101000000000 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A389 : Bound := ⟨0xf0000f00f0000f00f0000f00f0000f, [0x0, 0x500005005000050050000500500005, 0x300003003000030030000300300003, 0xf0000000f0000000f0000000f, 0xf0000f0000000000f0000f, 0xf0000f00f0000f], 0x1000000010000000f, 6⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA389 : Valid A389 := by
  apply transfer vA382 0xefdbaf4000000000000000000000c78b0e0000000000000000000000af5aad4000000000000000000000870a0c0000000000000006ed9ab400000000000000000000046890a00000000000000000000002e58a9400000000000000000000006080800000000 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A390 : Bound := ⟨0xff0000000000ff00ff0000000000ff, [0x0, 0x550000000000550055000000000055, 0x330000000000330033000000000033, 0xf00000000000f000f00000000000f, 0xff00000000000000ff, 0xff0000000000ff], 0x100010000000000ff, 6⟩
def bsA390 : Array Bound := [A293].toArray
theorem vbsA390 : ∀ s ∈ bsA390, Valid s := by
  intro s hs
  simp only [bsA390,List.mem_toArray] at hs
  exact (familyCons vA293 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA390 : Valid A390 := by
  apply bound_of_layers (bs := bsA390) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA390 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A394 : Bound := ⟨0xf0f0f0f0f0f0f0f, [0x0, 0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f], 0x100010103050f, 7⟩
def bsA394 : Array Bound := [A8, A10, A240, A249, A254].toArray
theorem vbsA394 : ∀ s ∈ bsA394, Valid s := by
  intro s hs
  simp only [bsA394,List.mem_toArray] at hs
  exact (familyCons vA8 <| familyCons vA10 <| familyCons vA240 <| familyCons vA249 <| familyCons vA254 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A394r4p0 : RecordPage := #[
(0x240c403e, 0x0), (0x230c423e, 0x0)]
def A394r4 : Records := #[A394r4p0]
def testA394r4 : ℕ → Bool := testAt A394 bsA394 3 (#[] : Records) A394r4 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A394r4c0 : checkBlock testA394r4 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA394r4 : LayerOK A394 4 A394r4 := by
  apply layer_of_block (bs := bsA394) (k := 3) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsA394 (emptyOK _ _)
  exact @block_merge testA394r4 0 2 30 A394r4c0 (show checkBlock testA394r4 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A394r5p0 : RecordPage := #[
(0xc203e, 0x2), (0xc403e, 0x9), (0xd403e, 0x68), (0xc423e, 0x13),
(0xd423e, 0x68)]
def A394r5 : Records := #[A394r5p0]
def testA394r5 : ℕ → Bool := testAt A394 bsA394 4 A394r4 A394r5 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A394r5c0 : checkBlock testA394r5 5 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA394r5 : LayerOK A394 5 A394r5 := by
  apply layer_of_block (bs := bsA394) (k := 4) (old := A394r4) (cw := 3) (rw := 1) (by decide +kernel) vbsA394 vA394r4
  exact @block_merge testA394r5 0 5 27 A394r5c0 (show checkBlock testA394r5 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A394r6p0 : RecordPage := #[
(0x3e, 0x66666822976666000066686600004453666624210000)]
def A394r6 : Records := #[A394r6p0]
def testA394r6 : ℕ → Bool := testAt A394 bsA394 5 A394r5 A394r6 3 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A394r6c0 : checkBlock testA394r6 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA394r6 : LayerOK A394 6 A394r6 := by
  apply layer_of_block (bs := bsA394) (k := 5) (old := A394r5) (cw := 3) (rw := 3) (by decide +kernel) vbsA394 vA394r5
  exact @block_merge testA394r6 0 1 31 A394r6c0 (show checkBlock testA394r6 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA394 : Valid A394 := by
  apply bound_of_layers (bs := bsA394) (last := A394r6) (cw := 3) (rw := 0) (by decide +kernel) vbsA394 vA394r6 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A395 : Bound := ⟨0xf000f000f000f000f000f000f000f, [0x0, 0x50005000500050005000500050005, 0x30003000300030003000300030003, 0xf0000000f0000000f0000000f, 0xf000f00000000000f000f, 0xf000f000f000f], 0x1000100010003000f, 7⟩
def bsA395 : Array Bound := [A309].toArray
theorem vbsA395 : ∀ s ∈ bsA395, Valid s := by
  intro s hs
  simp only [bsA395,List.mem_toArray] at hs
  exact (familyCons vA309 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA395 : Valid A395 := by
  apply bound_of_layers (bs := bsA395) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA395 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A399 : Bound := ⟨0x5050505050505050505050505050505, [0x0, 0x1010101010101010101010101010101, 0x50005000500050005000500050005, 0x505000005050000050500000505, 0x50505050000000005050505, 0x505050505050505], 0x10001000101010505, 7⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA399 : Valid A399 := by
  apply transfer vA395 0xf5cbc70000000000000000000000d58b460000000000000000000000b54ac50000000000000000000000950a44000000000000000000000074c9c3000000000000000000000054894200000000000000000000003448c100000000000000000000001408400 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A400 : Bound := ⟨0xf0f0f0f000000000f0f0f0f, [0x0, 0x50505050000000005050505, 0x30303030000000003030303, 0xf000f00000000000f000f, 0xf0f0000000000000f0f, 0xf0f0f0f], 0x1000000000103050f, 8⟩
def bsA400 : Array Bound := [A13, A14, A15, A16, A17, A257, A259, A269, A270].toArray
theorem vbsA400 : ∀ s ∈ bsA400, Valid s := by
  intro s hs
  simp only [bsA400,List.mem_toArray] at hs
  exact (familyCons vA13 <| familyCons vA14 <| familyCons vA15 <| familyCons vA16 <| familyCons vA17 <| familyCons vA257 <| familyCons vA259 <| familyCons vA269 <| familyCons vA270 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A400r4p0 : RecordPage := #[
(0x40b50c103e, 0x0), (0x50b50c103e, 0x0), (0x40b50c303e, 0x0), (0x50b50c303e, 0x0),
(0x250a30d403e, 0x0), (0x240a50d403e, 0x0), (0x250850c213e, 0x0), (0x50b50c213e, 0x0),
(0x240a30d413e, 0x0), (0x240a40d413e, 0x0), (0x250850c323e, 0x0), (0x50b50c323e, 0x0),
(0x250a40d423e, 0x0), (0x250a50d423e, 0x0), (0x250a30d433e, 0x0), (0x240a50d433e, 0x0)]
def A400r4 : Records := #[A400r4p0]
def testA400r4 : ℕ → Bool := testAt A400 bsA400 3 (#[] : Records) A400r4 4 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A400r4c0 : checkBlock testA400r4 8 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A400r4c8 : checkBlock testA400r4 8 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA400r4 : LayerOK A400 4 A400r4 := by
  apply layer_of_block (bs := bsA400) (k := 3) (old := (#[] : Records)) (cw := 4) (rw := 1) (by decide +kernel) vbsA400 (emptyOK _ _)
  exact @block_merge testA400r4 0 16 16 (@block_merge testA400r4 0 8 8 A400r4c0 A400r4c8) (show checkBlock testA400r4 16 16 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A400r5p0 : RecordPage := #[
(0x950c103e, 0x0), (0xa50c103e, 0x0), (0xb50c103e, 0x1436060e), (0x851c103e, 0x18e),
(0x852c103e, 0x150), (0x950c303e, 0x0), (0xa50c303e, 0x0), (0xb50c303e, 0x1877160a),
(0x851c303e, 0x18a), (0x852c303e, 0x1d0), (0xa30c403e, 0x0), (0x240c403e, 0x0),
(0xa50c403e, 0x0), (0xa30d403e, 0x149), (0xa50d403e, 0x1cb), (0x850c213e, 0x53604),
(0x950c213e, 0x0), (0xa50c213e, 0x0), (0xb50c213e, 0x14f819cc), (0x851c213e, 0x14c),
(0x852c213e, 0x20e), (0x610c413e, 0xa), (0xa30c413e, 0x0), (0xa40c413e, 0x0),
(0x250c413e, 0x0), (0x650c413e, 0xa), (0xa30d413e, 0x191), (0xa40d413e, 0x213),
(0x850c323e, 0x75604), (0x950c323e, 0x0), (0xa50c323e, 0x0), (0xb50c323e, 0x1d78218a)]
def A400r5p1 : RecordPage := #[
(0x851c323e, 0x20a), (0x852c323e, 0x1cc), (0x610c423e, 0x4a), (0x230c423e, 0x0),
(0x630c423e, 0x10), (0xa40c423e, 0x0), (0xa50c423e, 0x0), (0xa40d423e, 0x159),
(0xa50d423e, 0x1db), (0x610c433e, 0xa), (0xa30c433e, 0x0), (0x240c433e, 0x0),
(0x640c433e, 0xe), (0xa50c433e, 0x0), (0xa30d433e, 0x19d), (0xa50d433e, 0x21f)]
def A400r5 : Records := #[A400r5p0, A400r5p1]
def testA400r5 : ℕ → Bool := testAt A400 bsA400 4 A400r4 A400r5 4 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A400r5c0 : checkBlock testA400r5 8 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A400r5c8 : checkBlock testA400r5 8 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A400r5c16 : checkBlock testA400r5 8 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A400r5c24 : checkBlock testA400r5 8 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A400r5c32 : checkBlock testA400r5 8 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A400r5c40 : checkBlock testA400r5 8 40 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA400r5 : LayerOK A400 5 A400r5 := by
  apply layer_of_block (bs := bsA400) (k := 4) (old := A400r4) (cw := 4) (rw := 4) (by decide +kernel) vbsA400 vA400r4
  exact @block_merge testA400r5 0 48 16 (@block_merge testA400r5 0 24 24 (@block_merge testA400r5 0 8 16 A400r5c0 (@block_merge testA400r5 8 8 8 A400r5c8 A400r5c16)) (@block_merge testA400r5 24 8 16 A400r5c24 (@block_merge testA400r5 32 8 8 A400r5c32 A400r5c40))) (show checkBlock testA400r5 16 48 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A400r6p0 : RecordPage := #[
(0xc103e, 0x1c254a70a01e00631ce8382830245014060982741ce), (0xc303e, 0x144d4253a0458c8014a82878d16460982701c05414a), (0xc403e, 0x4281180a01e108114654460982217609c55c484204), (0xd403e, 0x1098c8420451d50b6098271b70184204),
(0xc213e, 0x62960190727529c2631cc4a8d09f5014080a026398c), (0xc413e, 0x701c9dc25ce72b5014066c54062f61f82d811ce72b), (0xd413e, 0x14a739cad405018dd8860d6005ce72b), (0xc323e, 0x54353942641601905298a7ef5db9701c080a025314a),
(0xc423e, 0x1099058a5826319155354e5d2dc7e0280a4c78098c645), (0xd423e, 0x109906319155454edd3dc86028098c645), (0xc433e, 0x54350144d4a55365b639701c0b35dc08558114a553), (0xd433e, 0x14e52954d97d8edc070217602d4a553)]
def A400r6 : Records := #[A400r6p0]
def testA400r6 : ℕ → Bool := testAt A400 bsA400 5 A400r5 A400r6 4 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A400r6c0 : checkBlock testA400r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A400r6c4 : checkBlock testA400r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A400r6c8 : checkBlock testA400r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA400r6 : LayerOK A400 6 A400r6 := by
  apply layer_of_block (bs := bsA400) (k := 5) (old := A400r5) (cw := 4) (rw := 6) (by decide +kernel) vbsA400 vA400r5
  exact @block_merge testA400r6 0 12 20 (@block_merge testA400r6 0 4 8 A400r6c0 (@block_merge testA400r6 4 4 4 A400r6c4 A400r6c8)) (show checkBlock testA400r6 20 12 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A400r7p0 : RecordPage := #[
(0x3e, 0x52af5632715314f739ab5394063989840e55414364182741c1)]
def A400r7 : Records := #[A400r7p0]
def testA400r7 : ℕ → Bool := testAt A400 bsA400 6 A400r6 A400r7 4 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A400r7c0 : checkBlock testA400r7 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA400r7 : LayerOK A400 7 A400r7 := by
  apply layer_of_block (bs := bsA400) (k := 6) (old := A400r6) (cw := 4) (rw := 4) (by decide +kernel) vbsA400 vA400r6
  exact @block_merge testA400r7 0 1 31 A400r7c0 (show checkBlock testA400r7 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA400 : Valid A400 := by
  apply bound_of_layers (bs := bsA400) (last := A400r7) (cw := 4) (rw := 0) (by decide +kernel) vbsA400 vA400r7 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A401 : Bound := ⟨0x333333330000000033333333, [0x0, 0x111111110000000011111111, 0x30303030000000003030303, 0x3300330000000000330033, 0x33330000000000003333, 0x33333333], 0x10000000001031133, 8⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA401 : Valid A401 := by
  apply transfer vA400 0xbb72cd80000000ab528d000000009b324c800000008b120c00000000000000000000000000000000000000000000000000000000000000003a70c9800000002a5089000000001a3048800000000a10080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A402 : Bound := ⟨0xf0f00000f0f00000f0f00000f0f, [0x0, 0x505000005050000050500000505, 0x303000003030000030300000303, 0xf0000000f0000000f0000000f, 0xf0f0000000000000f0f, 0xf0f00000f0f], 0x1000000010000050f, 8⟩
def bsA402 : Array Bound := [A308].toArray
theorem vbsA402 : ∀ s ∈ bsA402, Valid s := by
  intro s hs
  simp only [bsA402,List.mem_toArray] at hs
  exact (familyCons vA308 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA402 : Valid A402 := by
  apply bound_of_layers (bs := bsA402) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA402 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A403 : Bound := ⟨0x3333000033330000333300003333, [0x0, 0x1111000011110000111100001111, 0x303000003030000030300000303, 0x33000000330000003300000033, 0x33330000000000003333, 0x333300003333], 0x10000001100001133, 8⟩
def bsA403 : Array Bound := [A308].toArray
theorem vbsA403 : ∀ s ∈ bsA403, Valid s := by
  intro s hs
  simp only [bsA403,List.mem_toArray] at hs
  exact (familyCons vA308 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA403 : Valid A403 := by
  apply bound_of_layers (bs := bsA403) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA403 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A404 : Bound := ⟨0x330033003300330033003300330033, [0x0, 0x110011001100110011001100110011, 0x30003000300030003000300030003, 0x33000000330000003300000033, 0x3300330000000000330033, 0x33003300330033], 0x10001001100030033, 8⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA404 : Valid A404 := by
  apply transfer vA400 0xebd38f00000000ab528d00000000cb930e000000008b120c00000000000000000000000000000000000000000000000000000000000000006ad18b000000002a5089000000004a910a000000000a10080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A405 : Bound := ⟨0xaa005500aa005500aa005500aa0055, [0x0, 0x55000000550000005500000055, 0x220011002200110022001100220011, 0xa0005000a0005000a0005000a0005, 0xaa00550000000000aa0055, 0xaa005500aa0055], 0x10000001100020055, 8⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA405 : Valid A405 := by
  apply transfer vA402 0xefd79f10000000af569d100000000000000000000000000000000000cd9316000000008d12140000000000000000000000000000000000006ed59b100000002e54991000000000000000000000000000000000004c9112000000000c10100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A406 : Bound := ⟨0xf000f0000f000f00f000f0000f000f, [0x0, 0x500050000500050050005000050005, 0x300030000300030030003000030003, 0xf000f00000000000f000f, 0xf00000000f000000f00000000f, 0xf000f0000f000f], 0x1000000100003000f, 8⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA406 : Valid A406 := by
  apply transfer vA402 0xefd7b740000000cf9736400000000000000000000000000000000000a74695000000008706140000000000000000000000000000000000006ed5b3400000004e9532400000000000000000000000000000000000264491000000000604100 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A407 : Bound := ⟨0x3030303030303030303030303030303, [0x0, 0x1010101010101010101010101010101, 0x30003000300030003000300030003, 0x303000003030000030300000303, 0x30303030000000003030303, 0x303030303030303], 0x10001000101030103, 8⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA407 : Valid A407 := by
  apply transfer vA403 0x3cf800034e800038f000030e000000000000000000000000000000002cd800024c800028d000020c000000000000000000000000000000001cb800014a800018b000010a000000000000000000000000000000000c98000048800008900000080 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A408 : Bound := ⟨0x11111111111111111111111111111111, [0x0, 0x1010101010101010101010101010101, 0x110011001100110011001100110011, 0x1111000011110000111100001111, 0x111111110000000011111111, 0x1111111111111111], 0x10001001101011111, 8⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA408 : Valid A408 := by
  apply transfer vA400 0xf9e3a700000000d9a32600000000b962a500000000992224000000000000000000000000000000000000000000000000000000000000000078e1a30000000058a122000000003860a1000000001820200 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A416 : Bound := ⟨0xffffffffffffffff, [0x0, 0x5555555555555555, 0x3333333333333333, 0xf0f0f0f0f0f0f0f, 0xff00ff00ff00ff, 0xffff0000ffff, 0xffffffff], 0x10011010355ff, 8⟩
def bsA416 : Array Bound := [A394].toArray
theorem vbsA416 : ∀ s ∈ bsA416, Valid s := by
  intro s hs
  simp only [bsA416,List.mem_toArray] at hs
  exact (familyCons vA394 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA416 : Valid A416 := by
  apply bound_of_layers (bs := bsA416) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA416 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A417 : Bound := ⟨0xffffffff00000000ffffffff, [0x0, 0x555555550000000055555555, 0x333333330000000033333333, 0xf0f0f0f000000000f0f0f0f, 0xff00ff0000000000ff00ff, 0xffff000000000000ffff, 0xffffffff], 0x100000000010355ff, 9⟩
def bsA417 : Array Bound := [A400].toArray
theorem vbsA417 : ∀ s ∈ bsA417, Valid s := by
  intro s hs
  simp only [bsA417,List.mem_toArray] at hs
  exact (familyCons vA400 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA417 : Valid A417 := by
  apply bound_of_layers (bs := bsA417) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA417 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A418 : Bound := ⟨0xffff0000ffff0000ffff0000ffff, [0x0, 0x5555000055550000555500005555, 0x3333000033330000333300003333, 0xf0f00000f0f00000f0f00000f0f, 0xff000000ff000000ff000000ff, 0xffff000000000000ffff, 0xffff0000ffff], 0x100000011000055ff, 9⟩
def bsA418 : Array Bound := [A402].toArray
theorem vbsA418 : ∀ s ∈ bsA418, Valid s := by
  intro s hs
  simp only [bsA418,List.mem_toArray] at hs
  exact (familyCons vA402 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA418 : Valid A418 := by
  apply bound_of_layers (bs := bsA418) (last := (#[] : Records)) (cw := 0) (rw := 1) (by decide +kernel) vbsA418 (emptyOK _ _) (by decide +kernel) (canon_checked (by decide +kernel)) 0x0
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A419 : Bound := ⟨0xff00ff00ff00ff00ff00ff00ff00ff, [0x0, 0x550055005500550055005500550055, 0x330033003300330033003300330033, 0xf000f000f000f000f000f000f000f, 0xff000000ff000000ff000000ff, 0xff00ff0000000000ff00ff, 0xff00ff00ff00ff], 0x100010011000300ff, 10⟩
def bsA419 : Array Bound := [A309, A310, A375, A376, A378, A379, A382, A383, A384, A386, A389, A390, A404, A405, A406].toArray
theorem vbsA419 : ∀ s ∈ bsA419, Valid s := by
  intro s hs
  simp only [bsA419,List.mem_toArray] at hs
  exact (familyCons vA309 <| familyCons vA310 <| familyCons vA375 <| familyCons vA376 <| familyCons vA378 <| familyCons vA379 <| familyCons vA382 <| familyCons vA383 <| familyCons vA384 <| familyCons vA386 <| familyCons vA389 <| familyCons vA390 <| familyCons vA404 <| familyCons vA405 <| familyCons vA406 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A419r3p0 : RecordPage := #[
(0x31320520050750c537e, 0x0), (0x31320520040730c547e, 0x0)]
def A419r3 : Records := #[A419r3p0]
def testA419r3 : ℕ → Bool := testAt A419 bsA419 2 (#[] : Records) A419r3 4 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r3c0 : checkBlock testA419r3 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA419r3 : LayerOK A419 3 A419r3 := by
  apply layer_of_block (bs := bsA419) (k := 2) (old := (#[] : Records)) (cw := 4) (rw := 1) (by decide +kernel) vbsA419 (emptyOK _ _)
  exact @block_merge testA419r3 0 2 30 A419r3c0 (show checkBlock testA419r3 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A419r4p0 : RecordPage := #[
(0x31420040b60c207e, 0x0), (0x41050b60850c307e, 0x0), (0x41060b60850c307e, 0x0), (0x41420040b60c307e, 0x0),
(0x41420040b60c407e, 0x4), (0x30321a60610c507e, 0x0), (0x21050b60850c327e, 0x0), (0x21060b60850c327e, 0x0),
(0x41420050b60c327e, 0x8), (0x41420050b60c427e, 0x0), (0x40321a50610c527e, 0x0), (0x51440250860c437e, 0x0),
(0x31421040b60c437e, 0x0), (0x51440050b60c437e, 0x0), (0x31421050b60c437e, 0x0), (0x31421060b60c437e, 0x0),
(0x50361720861c437e, 0x0), (0x50361630861c437e, 0x0), (0x40341720862c437e, 0x0), (0x40341630862c437e, 0x0),
(0x50330270c61d437e, 0x0), (0x40330250c62e437e, 0x0), (0x41510050750c537e, 0x0), (0x31420050750c537e, 0x0),
(0x320520050750c537e, 0x1), (0x41520050750c537e, 0x1), (0x41430050750c537e, 0x18), (0x620041430040f537e, 0x0),
(0x210541430040f537e, 0x0), (0x250a51430040f537e, 0x0), (0x50b51440040f537e, 0x0), (0x41510040730c547e, 0x0)]
def A419r4p1 : RecordPage := #[
(0x31420040730c547e, 0x0), (0x320520040730c547e, 0x3), (0x41520040730c547e, 0x3), (0x41430040730c547e, 0x18),
(0x42620430040f547e, 0x0), (0x210541430040f547e, 0x0), (0x50b51430040f547e, 0x0), (0x250a51440040f547e, 0x0)]
def A419r4 : Records := #[A419r4p0, A419r4p1]
def testA419r4 : ℕ → Bool := testAt A419 bsA419 3 A419r3 A419r4 4 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r4c0 : checkBlock testA419r4 8 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r4c8 : checkBlock testA419r4 8 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r4c16 : checkBlock testA419r4 8 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r4c24 : checkBlock testA419r4 8 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r4c32 : checkBlock testA419r4 8 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA419r4 : LayerOK A419 4 A419r4 := by
  apply layer_of_block (bs := bsA419) (k := 3) (old := A419r3) (cw := 4) (rw := 1) (by decide +kernel) vbsA419 vA419r3
  exact @block_merge testA419r4 0 40 24 (@block_merge testA419r4 0 16 24 (@block_merge testA419r4 0 8 8 A419r4c0 A419r4c8) (@block_merge testA419r4 16 8 16 A419r4c16 (@block_merge testA419r4 24 8 8 A419r4c24 A419r4c32))) (show checkBlock testA419r4 24 40 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A419r5p0 : RecordPage := #[
(0x40b10960c207e, 0x0), (0x240a50960c207e, 0x0), (0x230a60960c207e, 0x0), (0x420040b60c207e, 0x1),
(0x430040b60c207e, 0x1), (0x421040b60c207e, 0x0), (0x431040b60c207e, 0x0), (0x952040b60c207e, 0x0),
(0x943040b60c207e, 0x0), (0x151440b60c207e, 0x0), (0x161440b60c207e, 0x0), (0x161550b60c207e, 0x0),
(0x220421b60c207e, 0x0), (0x220431b60c207e, 0x0), (0x320953951c207e, 0x0), (0x20b60850c307e, 0x0),
(0x30b60850c307e, 0x0), (0x40b60850c307e, 0x0), (0x50b60850c307e, 0x3), (0x60b60850c307e, 0x5),
(0x41b60850c307e, 0x283), (0x31861850c307e, 0x0), (0x110321c50c307e, 0x0), (0x250960a50c307e, 0x0),
(0x260960a50c307e, 0x0), (0x320862a50c307e, 0x0), (0x310232e50c307e, 0x0), (0x110321c60c307e, 0x0),
(0x40b10960c307e, 0x0), (0x50b10960c307e, 0x0), (0x230a60960c307e, 0x0), (0x320531960c307e, 0x0)]
def A419r5p1 : RecordPage := #[
(0x41530b60c307e, 0x0), (0x51530b60c307e, 0x0), (0x61530b60c307e, 0x0), (0x420040b60c307e, 0x7),
(0x440040b60c307e, 0x7), (0x421040b60c307e, 0x1a), (0x431040b60c307e, 0x1a), (0x831040b60c307e, 0x0),
(0xa31040b60c307e, 0x0), (0x952040b60c307e, 0x0), (0x51440b60c307e, 0x0), (0x61440b60c307e, 0x0),
(0x161440b60c307e, 0x0), (0x421050b60c307e, 0x1a), (0x431050b60c307e, 0x1a), (0x831050b60c307e, 0x0),
(0xa31050b60c307e, 0x0), (0x952050b60c307e, 0x0), (0x161450b60c307e, 0x0), (0x620060b60c307e, 0x0),
(0x421060b60c307e, 0x1a), (0x431060b60c307e, 0x1a), (0x231860b60c307e, 0x0), (0x220421b60c307e, 0x0),
(0x220962b60c307e, 0x0), (0x42050f60c307e, 0x0), (0x42060f60c307e, 0x0), (0x32070f60c307e, 0x0),
(0x330861951c307e, 0x0), (0x41861861c307e, 0x2), (0x320a63861c307e, 0x0), (0x50750a50c407e, 0x0)]
def A419r5p2 : RecordPage := #[
(0x250960a50c407e, 0x0), (0x41862a50c407e, 0x2), (0x321230c60c407e, 0x0), (0x110321c60c407e, 0x0),
(0x40b10960c407e, 0x0), (0x260a60960c407e, 0x0), (0x31421960c407e, 0x0), (0x320531960c407e, 0x0),
(0x41420b60c407e, 0x0), (0x151420b60c407e, 0x0), (0x61420b60c407e, 0x0), (0x161420b60c407e, 0x0),
(0x41530b60c407e, 0x0), (0x61530b60c407e, 0x0), (0x420040b60c407e, 0x124), (0x440040b60c407e, 0x9),
(0x540040b60c407e, 0x0), (0x421040b60c407e, 0x0), (0x431040b60c407e, 0x0), (0x831040b60c407e, 0x0),
(0xa31040b60c407e, 0x0), (0x151440b60c407e, 0x0), (0x61440b60c407e, 0x0), (0x161440b60c407e, 0x0),
(0x61550b60c407e, 0x0), (0x161550b60c407e, 0x0), (0x421060b60c407e, 0x0), (0x431060b60c407e, 0x0),
(0x220421b60c407e, 0x0), (0x42050f60c407e, 0x0), (0x210531861c407e, 0x0), (0x50b60a50d407e, 0x0)]
def A419r5p3 : RecordPage := #[
(0x60b60a50d407e, 0x0), (0x260860b60d407e, 0x0), (0x260a60961d407e, 0x0), (0x720031961d407e, 0x0),
(0x231720862d407e, 0x0), (0x250a50610c507e, 0x0), (0x321a60610c507e, 0xb), (0x131a60610c507e, 0x0),
(0x40b61610c507e, 0xb), (0x260a60a60c507e, 0x0), (0x42050f60c507e, 0x0), (0x42070f60c507e, 0x0),
(0x240a61862c507e, 0x0), (0x60340c50d507e, 0x0), (0x50750a50d507e, 0x0), (0x250860a50d507e, 0x0),
(0x260860a50d507e, 0x0), (0x40b31a50d507e, 0x0), (0x50b31a50d507e, 0x0), (0x60b31a50d507e, 0x0),
(0x32230c60d507e, 0x0), (0x110321c60d507e, 0x0), (0x221230d60d507e, 0x0), (0x221250d60d507e, 0x0),
(0x221270d60d507e, 0x0), (0x40b31a60d507e, 0x0), (0x60b31a60d507e, 0x0), (0x50330d52d507e, 0x0),
(0x231720862d507e, 0x0), (0x240861862d507e, 0x0), (0x250230c65d507e, 0x0), (0x20b60850c327e, 0x0)]
def A419r5p4 : RecordPage := #[
(0x30b60850c327e, 0x0), (0x40b60850c327e, 0x0), (0x50b60850c327e, 0xd), (0x60b60850c327e, 0xf),
(0x21b60850c327e, 0x78d), (0x41862850c327e, 0x0), (0x50740a50c327e, 0x0), (0x260960a50c327e, 0x0),
(0x41862a50c327e, 0x0), (0x321230c60c327e, 0x0), (0x110321c60c327e, 0x0), (0x50b10960c327e, 0x0),
(0x250a60960c327e, 0x0), (0x31421960c327e, 0x0), (0x320531960c327e, 0x0), (0x141420b60c327e, 0x0),
(0x51420b60c327e, 0x0), (0x61420b60c327e, 0x0), (0x161420b60c327e, 0x0), (0x51530b60c327e, 0x0),
(0x61530b60c327e, 0x0), (0x51540b60c327e, 0x0), (0x61540b60c327e, 0x0), (0x161540b60c327e, 0x0),
(0x420050b60c327e, 0x228), (0x440050b60c327e, 0x11), (0x540050b60c327e, 0x0), (0x421050b60c327e, 0x0),
(0x431050b60c327e, 0x0), (0x831050b60c327e, 0x0), (0xa31050b60c327e, 0x0), (0x61450b60c327e, 0x0)]
def A419r5p5 : RecordPage := #[
(0x161450b60c327e, 0x0), (0x421060b60c327e, 0x0), (0x431060b60c327e, 0x0), (0x220421b60c327e, 0x0),
(0x42060f60c327e, 0x0), (0x210531861c327e, 0x0), (0x230230d65c327e, 0x0), (0x50b60a50d327e, 0x0),
(0x60b60a50d327e, 0x0), (0x250860b60d327e, 0x0), (0x330630851d327e, 0x0), (0x130b60851d327e, 0x0),
(0x40b60851d327e, 0x0), (0x50b60851d327e, 0x0), (0x60b60851d327e, 0x0), (0x320863851d327e, 0x0),
(0x250a60961d327e, 0x0), (0x720031961d327e, 0x0), (0x231720862d327e, 0x0), (0x110321c50c427e, 0x0),
(0x250960a50c427e, 0x0), (0x260960a50c427e, 0x0), (0x320862a50c427e, 0x0), (0x110321c60c427e, 0x0),
(0x40b10960c427e, 0x0), (0x50b10960c427e, 0x0), (0x320531960c427e, 0x0), (0x41530b60c427e, 0x0),
(0x51530b60c427e, 0x0), (0x61530b60c427e, 0x0), (0x421040b60c427e, 0x1c), (0x431040b60c427e, 0x1c)]
def A419r5p6 : RecordPage := #[
(0x831040b60c427e, 0x0), (0xa31040b60c427e, 0x0), (0x51440b60c427e, 0x0), (0x161440b60c427e, 0x0),
(0x420050b60c427e, 0x13), (0x440050b60c427e, 0x13), (0x421050b60c427e, 0x1c), (0x431050b60c427e, 0x1c),
(0x831050b60c427e, 0x0), (0xa31050b60c427e, 0x0), (0x61450b60c427e, 0x0), (0x161450b60c427e, 0x0),
(0x620060b60c427e, 0x0), (0x421060b60c427e, 0x1c), (0x431060b60c427e, 0x1c), (0x220421b60c427e, 0x0),
(0x42050f60c427e, 0x0), (0x42060f60c427e, 0x0), (0x32070f60c427e, 0x0), (0x41861861c427e, 0x0),
(0x320a63861c427e, 0x0), (0x321a50610c527e, 0x15), (0x131a50610c527e, 0x0), (0x240a60610c527e, 0x0),
(0x50b51610c527e, 0x15), (0x250a60a50c527e, 0x0), (0x42060f50c527e, 0x0), (0x42070f50c527e, 0x0),
(0x240a61852c527e, 0x0), (0x32230c50d527e, 0x0), (0x110321c50d527e, 0x0), (0x221230d50d527e, 0x0)]
def A419r5p7 : RecordPage := #[
(0x221260d50d527e, 0x0), (0x221270d50d527e, 0x0), (0x250860a50d527e, 0x0), (0x260860a50d527e, 0x0),
(0x50b31a50d527e, 0x0), (0x60b31a50d527e, 0x0), (0x60340c60d527e, 0x0), (0x50740a60d527e, 0x0),
(0x40b31a60d527e, 0x0), (0x50b31a60d527e, 0x0), (0x60b31a60d527e, 0x0), (0x231720852d527e, 0x0),
(0x240861852d527e, 0x0), (0x40330d62d527e, 0x0), (0x260230c65d527e, 0x0), (0x440250860c437e, 0x17),
(0x540250860c437e, 0x0), (0x450250860c437e, 0x17), (0x550250860c437e, 0x0), (0x110321c60c437e, 0x0),
(0x50321c60c437e, 0x0), (0x50710960c437e, 0x0), (0x50b10960c437e, 0x0), (0x320521960c437e, 0x0),
(0x320531960c437e, 0x0), (0x41420b60c437e, 0x0), (0x141420b60c437e, 0x0), (0x51420b60c437e, 0x0),
(0x61420b60c437e, 0x0), (0x161420b60c437e, 0x0), (0x41520b60c437e, 0x0), (0x51520b60c437e, 0x0)]
def A419r5p8 : RecordPage := #[
(0x61520b60c437e, 0x0), (0x41430b60c437e, 0x0), (0x141430b60c437e, 0x0), (0x51430b60c437e, 0x0),
(0x61430b60c437e, 0x0), (0x161430b60c437e, 0x0), (0x41530b60c437e, 0x0), (0x51530b60c437e, 0x0),
(0x61530b60c437e, 0x0), (0x421040b60c437e, 0x19), (0x431040b60c437e, 0x19), (0x831040b60c437e, 0x0),
(0xa31040b60c437e, 0x0), (0x51440b60c437e, 0x0), (0x61440b60c437e, 0x0), (0x161440b60c437e, 0x0),
(0x51540b60c437e, 0x0), (0x61540b60c437e, 0x0), (0x161540b60c437e, 0x0), (0x440050b60c437e, 0x1b),
(0x540050b60c437e, 0x0), (0x450050b60c437e, 0x1b), (0x550050b60c437e, 0x0), (0x421050b60c437e, 0x1d),
(0x821050b60c437e, 0x0), (0xa21050b60c437e, 0x0), (0x431050b60c437e, 0x1d), (0x831050b60c437e, 0x0),
(0xa31050b60c437e, 0x0), (0x61450b60c437e, 0x0), (0x161450b60c437e, 0x0), (0x421060b60c437e, 0x1f)]
def A419r5p9 : RecordPage := #[
(0x821060b60c437e, 0x0), (0xa21060b60c437e, 0x0), (0x431060b60c437e, 0x1f), (0x31421b60c437e, 0x7ce99),
(0x42050f60c437e, 0x0), (0x32060f60c437e, 0x0), (0x42060f60c437e, 0x0), (0x32070f60c437e, 0x0),
(0x261720861c437e, 0x0), (0x361720861c437e, 0x21), (0x361630861c437e, 0x23), (0x60760861c437e, 0x11a1),
(0x241720862c437e, 0x0), (0x341720862c437e, 0x25), (0x341630862c437e, 0x27), (0x50740862c437e, 0x13a5),
(0x50b60a30d437e, 0x0), (0x330270c61d437e, 0x29), (0x50740862d437e, 0x1c), (0x60b60a50e437e, 0x0),
(0x60760861e437e, 0x1a), (0x330250c62e437e, 0x2b), (0x240a60610c537e, 0x0), (0x50361e10c537e, 0x0),
(0x50361e30c537e, 0x0), (0x250e50250c537e, 0x0), (0x260e50250c537e, 0x0), (0x250c52250c537e, 0x0),
(0x50f52250c537e, 0x0), (0x60f52250c537e, 0x0), (0x250a60a50c537e, 0x0), (0x260a60a50c537e, 0x0)]
def A419r5p10 : RecordPage := #[
(0x510050750c537e, 0x2d), (0x420050750c537e, 0x5f8), (0x520050750c537e, 0x19b1), (0x430050750c537e, 0x355f8),
(0x530050750c537e, 0x0), (0x440050750c537e, 0x1ab3c2d), (0x540050750c537e, 0x0), (0xa51050750c537e, 0x468),
(0xb51050750c537e, 0x421), (0x60130f62c537e, 0x0), (0x110321c60d537e, 0x0), (0x221230d60d537e, 0x0),
(0x221250d60d537e, 0x0), (0x221260d60d537e, 0x0), (0xa32240a60d537e, 0x0), (0x50740a60d537e, 0x0),
(0x40b31a60d537e, 0x0), (0x50b31a60d537e, 0x0), (0x40330d62d537e, 0x0), (0x230d20040f537e, 0x0),
(0x41430040f537e, 0x42148437), (0x441430040f537e, 0x0), (0x841430040f537e, 0x8), (0x541430040f537e, 0x39),
(0xa41430040f537e, 0x39), (0x851430040f537e, 0x0), (0xa51430040f537e, 0x3b), (0x51c30040f537e, 0x0),
(0xa10530040f537e, 0x39), (0x441530040f537e, 0x39), (0x541530040f537e, 0x0), (0x250e30040f537e, 0x0)]
def A419r5p11 : RecordPage := #[
(0x51e30040f537e, 0x39), (0x620440040f537e, 0x37), (0x951440040f537e, 0x0), (0xb51440040f537e, 0xf718),
(0x230c40040f537e, 0x0), (0xa10540040f537e, 0x39), (0x250e40040f537e, 0x0), (0x250e50040f537e, 0x0),
(0x260e50040f537e, 0x3b), (0x140f50040f537e, 0x0), (0x50f50040f537e, 0x3d), (0x250c52040f537e, 0x0),
(0x240e52040f537e, 0x0), (0x130f52040f537e, 0x0), (0x40f52040f537e, 0x0), (0x50f52040f537e, 0x0),
(0x260e50050f537e, 0x0), (0x250c52050f537e, 0x0), (0x240e52050f537e, 0x0), (0x130f52050f537e, 0x0),
(0x40f52050f537e, 0x0), (0x50f52050f537e, 0x0), (0x60f52050f537e, 0x0), (0x260a60850f537e, 0x0),
(0x230d20060f537e, 0x0), (0x40b31860f537e, 0x0), (0x50b31860f537e, 0x0), (0x230050f62f537e, 0x0),
(0x230060f62f537e, 0x0), (0x260a60610c547e, 0x0), (0x40341e10c547e, 0x0), (0x250e50230c547e, 0x0)]
def A419r5p12 : RecordPage := #[
(0x260e50230c547e, 0x0), (0x250a60a30c547e, 0x0), (0x260a60a30c547e, 0x0), (0x510040730c547e, 0x3f),
(0x420040730c547e, 0x838), (0x520040730c547e, 0x22c3), (0x430040730c547e, 0x47838), (0x530040730c547e, 0x0),
(0x440040730c547e, 0x23c5c3f), (0x540040730c547e, 0x0), (0xa41040730c547e, 0x0), (0xa51040730c547e, 0x4e4),
(0xb51040730c547e, 0x225), (0x110321c60d547e, 0x0), (0x221260d60d547e, 0x0), (0x221270d60d547e, 0x0),
(0xa32260a60d547e, 0x0), (0x60760a60d547e, 0x0), (0x250e50030f547e, 0x0), (0x250a60830f547e, 0x0),
(0x230d20040f547e, 0x0), (0x620430040f547e, 0x49), (0x41430040f547e, 0x210c4249), (0x441430040f547e, 0x0),
(0x841430040f547e, 0x0), (0x541430040f547e, 0x4b), (0xa41430040f547e, 0x4b), (0x951430040f547e, 0x0),
(0xb51430040f547e, 0x13718), (0x230c30040f547e, 0x0), (0x51c30040f547e, 0x4), (0xa10530040f547e, 0x4b)]
def A419r5p13 : RecordPage := #[
(0x441530040f547e, 0x4b), (0x541530040f547e, 0x0), (0x250e30040f547e, 0x0), (0x51e30040f547e, 0x4b),
(0x851440040f547e, 0x0), (0xa51440040f547e, 0x4f), (0xa10540040f547e, 0x4b), (0x250e40040f547e, 0x0),
(0x250e50040f547e, 0x4f), (0x260e50040f547e, 0x0), (0x140f50040f547e, 0x0), (0x60f50040f547e, 0x4d)]
def A419r5 : Records := #[A419r5p0, A419r5p1, A419r5p2, A419r5p3, A419r5p4, A419r5p5, A419r5p6, A419r5p7, A419r5p8, A419r5p9, A419r5p10, A419r5p11, A419r5p12, A419r5p13]
def testA419r5 : ℕ → Bool := testAt A419 bsA419 4 A419r4 A419r5 4 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c0 : checkBlock testA419r5 8 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c8 : checkBlock testA419r5 8 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c16 : checkBlock testA419r5 8 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c24 : checkBlock testA419r5 8 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c32 : checkBlock testA419r5 8 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c40 : checkBlock testA419r5 8 40 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c48 : checkBlock testA419r5 8 48 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c56 : checkBlock testA419r5 8 56 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c64 : checkBlock testA419r5 8 64 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c72 : checkBlock testA419r5 8 72 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c80 : checkBlock testA419r5 8 80 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c88 : checkBlock testA419r5 8 88 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c96 : checkBlock testA419r5 8 96 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c104 : checkBlock testA419r5 8 104 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c112 : checkBlock testA419r5 8 112 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c120 : checkBlock testA419r5 8 120 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c128 : checkBlock testA419r5 8 128 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c136 : checkBlock testA419r5 8 136 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c144 : checkBlock testA419r5 8 144 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c152 : checkBlock testA419r5 8 152 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c160 : checkBlock testA419r5 8 160 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c168 : checkBlock testA419r5 8 168 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c176 : checkBlock testA419r5 8 176 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c184 : checkBlock testA419r5 8 184 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c192 : checkBlock testA419r5 8 192 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c200 : checkBlock testA419r5 8 200 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c208 : checkBlock testA419r5 8 208 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c216 : checkBlock testA419r5 8 216 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c224 : checkBlock testA419r5 8 224 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c232 : checkBlock testA419r5 8 232 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c240 : checkBlock testA419r5 8 240 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c248 : checkBlock testA419r5 8 248 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c256 : checkBlock testA419r5 8 256 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c264 : checkBlock testA419r5 8 264 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c272 : checkBlock testA419r5 8 272 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c280 : checkBlock testA419r5 8 280 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c288 : checkBlock testA419r5 8 288 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c296 : checkBlock testA419r5 8 296 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c304 : checkBlock testA419r5 8 304 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c312 : checkBlock testA419r5 8 312 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c320 : checkBlock testA419r5 8 320 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c328 : checkBlock testA419r5 8 328 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c336 : checkBlock testA419r5 8 336 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c344 : checkBlock testA419r5 8 344 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c352 : checkBlock testA419r5 8 352 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c360 : checkBlock testA419r5 8 360 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c368 : checkBlock testA419r5 8 368 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c376 : checkBlock testA419r5 8 376 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c384 : checkBlock testA419r5 8 384 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c392 : checkBlock testA419r5 8 392 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c400 : checkBlock testA419r5 8 400 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c408 : checkBlock testA419r5 8 408 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c416 : checkBlock testA419r5 8 416 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r5c424 : checkBlock testA419r5 4 424 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA419r5 : LayerOK A419 5 A419r5 := by
  apply layer_of_block (bs := bsA419) (k := 4) (old := A419r4) (cw := 4) (rw := 6) (by decide +kernel) vbsA419 vA419r4
  exact @block_merge testA419r5 0 428 20 (@block_merge testA419r5 0 216 212 (@block_merge testA419r5 0 104 112 (@block_merge testA419r5 0 48 56 (@block_merge testA419r5 0 24 24 (@block_merge testA419r5 0 8 16 A419r5c0 (@block_merge testA419r5 8 8 8 A419r5c8 A419r5c16)) (@block_merge testA419r5 24 8 16 A419r5c24 (@block_merge testA419r5 32 8 8 A419r5c32 A419r5c40))) (@block_merge testA419r5 48 24 32 (@block_merge testA419r5 48 8 16 A419r5c48 (@block_merge testA419r5 56 8 8 A419r5c56 A419r5c64)) (@block_merge testA419r5 72 16 16 (@block_merge testA419r5 72 8 8 A419r5c72 A419r5c80) (@block_merge testA419r5 88 8 8 A419r5c88 A419r5c96)))) (@block_merge testA419r5 104 56 56 (@block_merge testA419r5 104 24 32 (@block_merge testA419r5 104 8 16 A419r5c104 (@block_merge testA419r5 112 8 8 A419r5c112 A419r5c120)) (@block_merge testA419r5 128 16 16 (@block_merge testA419r5 128 8 8 A419r5c128 A419r5c136) (@block_merge testA419r5 144 8 8 A419r5c144 A419r5c152))) (@block_merge testA419r5 160 24 32 (@block_merge testA419r5 160 8 16 A419r5c160 (@block_merge testA419r5 168 8 8 A419r5c168 A419r5c176)) (@block_merge testA419r5 184 16 16 (@block_merge testA419r5 184 8 8 A419r5c184 A419r5c192) (@block_merge testA419r5 200 8 8 A419r5c200 A419r5c208))))) (@block_merge testA419r5 216 104 108 (@block_merge testA419r5 216 48 56 (@block_merge testA419r5 216 24 24 (@block_merge testA419r5 216 8 16 A419r5c216 (@block_merge testA419r5 224 8 8 A419r5c224 A419r5c232)) (@block_merge testA419r5 240 8 16 A419r5c240 (@block_merge testA419r5 248 8 8 A419r5c248 A419r5c256))) (@block_merge testA419r5 264 24 32 (@block_merge testA419r5 264 8 16 A419r5c264 (@block_merge testA419r5 272 8 8 A419r5c272 A419r5c280)) (@block_merge testA419r5 288 16 16 (@block_merge testA419r5 288 8 8 A419r5c288 A419r5c296) (@block_merge testA419r5 304 8 8 A419r5c304 A419r5c312)))) (@block_merge testA419r5 320 56 52 (@block_merge testA419r5 320 24 32 (@block_merge testA419r5 320 8 16 A419r5c320 (@block_merge testA419r5 328 8 8 A419r5c328 A419r5c336)) (@block_merge testA419r5 344 16 16 (@block_merge testA419r5 344 8 8 A419r5c344 A419r5c352) (@block_merge testA419r5 360 8 8 A419r5c360 A419r5c368))) (@block_merge testA419r5 376 24 28 (@block_merge testA419r5 376 8 16 A419r5c376 (@block_merge testA419r5 384 8 8 A419r5c384 A419r5c392)) (@block_merge testA419r5 400 16 12 (@block_merge testA419r5 400 8 8 A419r5c400 A419r5c408) (@block_merge testA419r5 416 8 4 A419r5c416 A419r5c424)))))) (show checkBlock testA419r5 20 428 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A419r6p0 : RecordPage := #[
(0xa10860c207e, 0x0), (0xa50860c207e, 0x0), (0xa60860c207e, 0x0), (0xb10960c207e, 0x41201800440),
(0xa50960c207e, 0x3), (0xa60960c207e, 0x5), (0x421960c207e, 0x0), (0x431960c207e, 0x2),
(0x962960c207e, 0x5), (0x953960c207e, 0x3), (0x32e60c207e, 0x0), (0x42e60c207e, 0x0),
(0x40b60c207e, 0x8880f001a202c0048807), (0x440b60c207e, 0x2a204c0010818), (0x550b60c207e, 0xb8b0098800), (0x560b60c207e, 0xb8300a8802),
(0x421b60c207e, 0x80058819), (0x431b60c207e, 0x8006801b), (0x962b60c207e, 0x78842), (0x953b60c207e, 0x4088000),
(0x50f60c207e, 0x0), (0x160f60c207e, 0x0), (0x170f60c207e, 0x0), (0x32f60c207e, 0x2),
(0x42f60c207e, 0x0), (0xa50951c207e, 0x0), (0xa60951c207e, 0x0), (0x861951c207e, 0x2),
(0x953951c207e, 0xe681d), (0x863951c207e, 0x382), (0x630861c207e, 0x0), (0xa50861c207e, 0x0)]
def A419r6p1 : RecordPage := #[
(0x431861c207e, 0x2), (0x861861c207e, 0x842), (0xa61861c207e, 0x0), (0x953861c207e, 0x1a),
(0xa50942c207e, 0x0), (0xa60942c207e, 0x0), (0x861942c207e, 0x0), (0x630862c207e, 0x0),
(0xa60862c207e, 0x2), (0x851862c207e, 0x0), (0xa51862c207e, 0x0), (0x240c54c207e, 0x1c),
(0x250c54c207e, 0x1a), (0x130f54c207e, 0x0), (0x250c64c207e, 0x1a), (0x240d64c207e, 0x0),
(0x250d64c207e, 0x1a), (0x330e64c207e, 0x48), (0x130f64c207e, 0x0), (0x50f64c207e, 0x1a),
(0x60f64c207e, 0x0), (0x70f64c207e, 0x0), (0x170f64c207e, 0x0), (0x240c65c207e, 0x1c),
(0x240d65c207e, 0x1c), (0x250d65c207e, 0x2), (0x330e65c207e, 0x4), (0x130f65c207e, 0x0),
(0x40f65c207e, 0x1c), (0x60f65c207e, 0x0), (0x70f65c207e, 0x0), (0x170f65c207e, 0x0)]
def A419r6p2 : RecordPage := #[
(0x610850c307e, 0x18), (0xa10850c307e, 0x1a), (0x620850c307e, 0x18), (0x630850c307e, 0x18),
(0xa30850c307e, 0x2), (0x960850c307e, 0x0), (0xa60850c307e, 0x0), (0xb60850c307e, 0x29004f8094230841f),
(0x861850c307e, 0xac1f), (0xa61850c307e, 0x0), (0x862850c307e, 0xac21), (0x863850c307e, 0xa423),
(0xa63850c307e, 0x0), (0x230c50c307e, 0x18), (0x240c50c307e, 0x58), (0x321c50c307e, 0x2d),
(0x210d50c307e, 0x0), (0x230d50c307e, 0x358), (0x240d50c307e, 0x58), (0x221d50c307e, 0x2d),
(0x960a50c307e, 0x3818e02fd681f), (0xa60a50c307e, 0x0), (0xb60a50c307e, 0x82), (0x831a50c307e, 0x18),
(0xa31a50c307e, 0x0), (0x862a50c307e, 0x33), (0x863a50c307e, 0x1a), (0xa63a50c307e, 0x1a),
(0x232e50c307e, 0x35), (0x42e50c307e, 0x2), (0x42f50c307e, 0x1a), (0xa10860c307e, 0x0)]
def A419r6p3 : RecordPage := #[
(0xa30860c307e, 0x0), (0x250860c307e, 0xc6318), (0xa60860c307e, 0x0), (0x863860c307e, 0x4),
(0xa63860c307e, 0x0), (0x210c60c307e, 0x0), (0x230c60c307e, 0x18), (0x240c60c307e, 0x18),
(0x260c60c307e, 0x0), (0x321c60c307e, 0x37), (0x710960c307e, 0x18), (0xb10960c307e, 0x101f007780e75a),
(0x620960c307e, 0x18), (0x630960c307e, 0x18), (0xa30960c307e, 0x3), (0xa60960c307e, 0x3d),
(0x421960c307e, 0x1a), (0x431960c307e, 0x1a), (0x531960c307e, 0x3f), (0x962960c307e, 0x3d),
(0x230d60c307e, 0x18), (0x240d60c307e, 0x18), (0x221d60c307e, 0x37), (0xa60a60c307e, 0x0),
(0xa31a60c307e, 0x0), (0x863a60c307e, 0x0), (0xa63a60c307e, 0x0), (0x32e60c307e, 0x0),
(0x42e60c307e, 0x0), (0x530b60c307e, 0x114431075a), (0x40b60c307e, 0x10a6288822789a212c0248847), (0x440b60c307e, 0x2c8ae015441d0b58)]
def A419r6p4 : RecordPage := #[
(0x50b60c307e, 0x431e30308862f8ba216f18), (0x450b60c307e, 0x1945815443d0b40), (0x60b60c307e, 0xc63181146b1084348867), (0x460b60c307e, 0x5815c45d0b44),
(0x860b60c307e, 0x10da2), (0x560b60c307e, 0x32e059d681f), (0x421b60c307e, 0x6916c4bd686f), (0x431b60c307e, 0x6b1744dd683f),
(0x831b60c307e, 0x17c4f), (0xa31b60c307e, 0x308a38), (0x962b60c307e, 0x318a7a1b471), (0x50f60c307e, 0x73),
(0x60f60c307e, 0x75), (0x70f60c307e, 0x77), (0x170f60c307e, 0x0), (0x32f60c307e, 0x77),
(0x42f60c307e, 0x1d473), (0xa60951c307e, 0x0), (0x861951c307e, 0x79), (0x863951c307e, 0x35a),
(0xa63951c307e, 0x1a), (0x630861c307e, 0x0), (0x531861c307e, 0x1a), (0x861861c307e, 0x3d8562),
(0xa61861c307e, 0x0), (0x863861c307e, 0xf64), (0xa63861c307e, 0x7d), (0x630852c307e, 0x2),
(0x860852c307e, 0x1a), (0xa60852c307e, 0x0), (0x861852c307e, 0xf62), (0xa61852c307e, 0x2)]
def A419r6p5 : RecordPage := #[
(0x210d52c307e, 0x5a), (0xb20a52c307e, 0x1a), (0xa60a52c307e, 0x2), (0x630862c307e, 0x0),
(0x650862c307e, 0x1a), (0xa60862c307e, 0x2), (0x260c62c307e, 0x0), (0x210d62c307e, 0x1a),
(0xb20a62c307e, 0x0), (0xa60a62c307e, 0x2), (0x230c65c307e, 0x0), (0x330c65c307e, 0x79d681f),
(0x240c65c307e, 0x1a), (0x230d65c307e, 0x10), (0x330d65c307e, 0x0), (0x240d65c307e, 0x1a),
(0x250d65c307e, 0x1a), (0x230e65c307e, 0x0), (0x330e65c307e, 0x344), (0x250e65c307e, 0x1a),
(0x30f65c307e, 0x0), (0x130f65c307e, 0x35a), (0x40f65c307e, 0x1a), (0x50f65c307e, 0x1a),
(0x60f65c307e, 0x0), (0x230c50c407e, 0x18), (0x240c50c407e, 0x18), (0x750a50c407e, 0xfe2),
(0x960a50c407e, 0x16081d1023), (0xa60a50c407e, 0x0), (0xb60a50c407e, 0x82), (0x831a50c407e, 0x58)]
def A419r6p6 : RecordPage := #[
(0xa31a50c407e, 0x1a), (0x862a50c407e, 0x883), (0x863a50c407e, 0x883), (0xa63a50c407e, 0x2),
(0xa10860c407e, 0x0), (0x220860c407e, 0xc6318), (0xa30860c407e, 0x0), (0xa50860c407e, 0x0),
(0xa60860c407e, 0x0), (0x210c60c407e, 0x0), (0x230c60c407e, 0x10b8), (0x240c60c407e, 0x18),
(0x321c60c407e, 0x21487), (0x710960c407e, 0x18), (0xb10960c407e, 0x1011805822444), (0x620960c407e, 0x18),
(0x630960c407e, 0x18), (0xa30960c407e, 0x4), (0xa50960c407e, 0x0), (0xa60960c407e, 0x8b),
(0x421960c407e, 0x11a4), (0x431960c407e, 0x11a2), (0x531960c407e, 0x8f), (0x230d60c407e, 0x18),
(0x240d60c407e, 0x18), (0x221d60c407e, 0x87), (0xa60a60c407e, 0x0), (0xa31a60c407e, 0x0),
(0x32e60c407e, 0x2), (0x42e60c407e, 0x4), (0x420b60c407e, 0x25c9524c5824482), (0x530b60c407e, 0x136226482)]
def A419r6p7 : RecordPage := #[
(0x40b60c407e, 0x110a9264a72944519424f889d), (0x440b60c407e, 0xaf2b4ab1132211238), (0x550b60c407e, 0x16658e0ab11262), (0x60b60c407e, 0x18c630221365b88b5),
(0x460b60c407e, 0x588b0569362112a8), (0x860b60c407e, 0x0), (0x560b60c407e, 0x1662c15e225c23), (0x421b60c407e, 0x2d445188b9),
(0x431b60c407e, 0x2dc452908f), (0x831b60c407e, 0x539085), (0xa31b60c407e, 0x2a498), (0x50f60c407e, 0x1764),
(0x70f60c407e, 0x4), (0x170f60c407e, 0x0), (0x32f60c407e, 0x2), (0x42f60c407e, 0x1764),
(0x720861c407e, 0x6), (0x630861c407e, 0x2), (0x730861c407e, 0x2), (0x31861c407e, 0x31820c2b10b18c608623482111a210882),
(0x431861c407e, 0x211a2), (0x831861c407e, 0x1082), (0x531861c407e, 0x10bd), (0xa31861c407e, 0x10bd),
(0x630862c407e, 0x44), (0x210d62c407e, 0x17a2), (0xb20a62c407e, 0x0), (0x230c64c407e, 0x0),
(0x230d64c407e, 0x5), (0x240d64c407e, 0x1c), (0x250d64c407e, 0x2), (0x230c65c407e, 0x0)]
def A419r6p8 : RecordPage := #[
(0x330c65c407e, 0x23), (0x270c65c407e, 0x0), (0x230d65c407e, 0x3d), (0x330d65c407e, 0x0),
(0x240d65c407e, 0x4), (0x250d65c407e, 0x1a), (0x330e65c407e, 0x48), (0x130f65c407e, 0x42),
(0x50f65c407e, 0x1a), (0x60f65c407e, 0x0), (0x70f65c407e, 0x0), (0xa50a50d407e, 0x1c),
(0x960a50d407e, 0x1a), (0xa60a50d407e, 0x0), (0xb60a50d407e, 0xc1c17e810424), (0x861a50d407e, 0x4),
(0xa61a50d407e, 0x0), (0x863a50d407e, 0x2), (0x620a60d407e, 0x0), (0xa50a60d407e, 0x0),
(0xa60a60d407e, 0x0), (0x621a60d407e, 0xe), (0x850b60d407e, 0x0), (0x860b60d407e, 0xc3),
(0x720961d407e, 0x0), (0x630961d407e, 0x2), (0xa50961d407e, 0x0), (0xa60961d407e, 0xc5),
(0x31961d407e, 0x6318c630431e52), (0x431961d407e, 0x12), (0x720862d407e, 0x31cc9), (0x630862d407e, 0x32442)]
def A419r6p9 : RecordPage := #[
(0x330d54d407e, 0x1d), (0x330c64d407e, 0x0), (0x240c64d407e, 0x1c), (0x330d64d407e, 0x5),
(0x250d64d407e, 0x2), (0x330c65d407e, 0x0), (0x240c65d407e, 0x6), (0x270c65d407e, 0x0),
(0x330d65d407e, 0x3d), (0x250d65d407e, 0x2), (0x330e65d407e, 0x0), (0x130f65d407e, 0x42),
(0x50f65d407e, 0x0), (0x60f65d407e, 0x0), (0x70f65d407e, 0x0), (0xa40610c507e, 0x0),
(0xa50610c507e, 0xcb), (0xa60610c507e, 0x6799a2), (0xb61610c507e, 0xcd34442), (0x862610c507e, 0x11a2),
(0xa62610c507e, 0xcf), (0x850a40c507e, 0x0), (0xa60a40c507e, 0x7005), (0x951a40c507e, 0x1a),
(0xa50a50c507e, 0x0), (0x860a50c507e, 0x0), (0xa60a50c507e, 0x83d), (0xa31a50c507e, 0x0),
(0xa50a60c507e, 0x0), (0xa60a60c507e, 0xd3), (0xa31a60c507e, 0x0), (0x861a60c507e, 0x1a)]
def A419r6p10 : RecordPage := #[
(0xa61a60c507e, 0x0), (0x42e60c507e, 0x8d), (0x140f60c507e, 0x0), (0x50f60c507e, 0x354d1),
(0x70f60c507e, 0xd7), (0x170f60c507e, 0x0), (0x42f60c507e, 0xd7e1aa6), (0x330e42c507e, 0x0),
(0x260c52c507e, 0x0), (0x130f52c507e, 0x2), (0x50f52c507e, 0x0), (0x60f52c507e, 0x0),
(0x70f52c507e, 0x0), (0x170f52c507e, 0x0), (0x610862c507e, 0x8d), (0x630862c507e, 0x88d),
(0x861862c507e, 0x21ec2b), (0xa61862c507e, 0x170d9), (0x210d62c507e, 0x17a2), (0x720a62c507e, 0x4),
(0xb20a62c507e, 0x0), (0x430a62c507e, 0x4690cf), (0x330e62c507e, 0x4), (0x130f62c507e, 0x2),
(0x50f62c507e, 0x6), (0x70f62c507e, 0x6), (0x170f62c507e, 0x0), (0x330d54c507e, 0x0),
(0x330c65c507e, 0x424), (0x330d65c507e, 0x0), (0x240d65c507e, 0x1b24), (0x250d65c507e, 0x1a)]
def A419r6p11 : RecordPage := #[
(0x350d65c507e, 0x0), (0x330e65c507e, 0x1f444), (0x130f65c507e, 0x0), (0x50f65c507e, 0x1a),
(0x150f65c507e, 0x0), (0x230c40d507e, 0x18), (0x340c40d507e, 0x58), (0x850a40d507e, 0x3),
(0xa60a40d507e, 0x1c), (0x931a40d507e, 0x18), (0x851a40d507e, 0x1a), (0x230c50d507e, 0x18),
(0x340c50d507e, 0x1b78), (0x250a50d507e, 0x23171810318), (0x650a50d507e, 0x0), (0xa50a50d507e, 0x0),
(0x750a50d507e, 0x37403), (0x860a50d507e, 0x70e1c1be6), (0xa60a50d507e, 0x2), (0x931a50d507e, 0x18),
(0xb31a50d507e, 0x739ca71e83f), (0x851a50d507e, 0x0), (0xa51a50d507e, 0x0), (0x861a50d507e, 0x44),
(0xa61a50d507e, 0x1a), (0x260e50d507e, 0xcb), (0x230c60d507e, 0x1d38), (0x340c60d507e, 0x58),
(0x321c60d507e, 0xeb), (0x42c60d507e, 0x469d22), (0x230d60d507e, 0x621db8), (0x340d60d507e, 0x18)]
def A419r6p12 : RecordPage := #[
(0x250d60d507e, 0x310ef), (0x270d60d507e, 0x310f1), (0x221d60d507e, 0x78f0ef3b4eb), (0x620a60d507e, 0x0),
(0xa50a60d507e, 0x0), (0xa60a60d507e, 0x0), (0x931a60d507e, 0x19f8), (0xb31a60d507e, 0x7af0f33b48f),
(0x861a60d507e, 0x1a), (0xa61a60d507e, 0x1c), (0x142e60d507e, 0xcf), (0x40f60d507e, 0x82),
(0x142f60d507e, 0x6), (0x330c42d507e, 0x2), (0x260c52d507e, 0x0), (0x330d52d507e, 0x1ee2),
(0x50f52d507e, 0x68e3), (0x60f52d507e, 0x68e5), (0x70f52d507e, 0x68e7), (0x170f52d507e, 0x0),
(0x610862d507e, 0xe9), (0xa10862d507e, 0x2), (0x720862d507e, 0x48f9), (0xb20862d507e, 0x4842),
(0x630862d507e, 0x3e442), (0x861862d507e, 0x8fb), (0xa61862d507e, 0x5c), (0x330c62d507e, 0x4842),
(0x330d62d507e, 0x1082), (0x630a62d507e, 0xe9), (0x50f62d507e, 0x21e66), (0x70f62d507e, 0x21ea6)]
def A419r6p13 : RecordPage := #[
(0x170f62d507e, 0x0), (0x330d54d507e, 0x3), (0x230c65d507e, 0x860fd08744), (0x330c65d507e, 0x0),
(0x240c65d507e, 0x1f66), (0x230d65d507e, 0x1a), (0x330d65d507e, 0x0), (0x250d65d507e, 0x0),
(0x350d65d507e, 0x1a), (0x330e65d507e, 0x2), (0x130f65d507e, 0x0), (0x50f65d507e, 0x0),
(0x150f65d507e, 0x1a), (0x610850c327e, 0x18), (0xa10850c327e, 0x40), (0x620850c327e, 0x18),
(0x630850c327e, 0x18), (0xa30850c327e, 0x1c), (0x960850c327e, 0x0), (0xa60850c327e, 0x0),
(0xb60850c327e, 0x109c20e241503404ff), (0x861850c327e, 0x424ff), (0xa61850c327e, 0x0), (0x862850c327e, 0x42d01),
(0x863850c327e, 0x42d03), (0xa63850c327e, 0x0), (0x230c50c327e, 0x18), (0x240c50c327e, 0x18),
(0xa10a50c327e, 0x0), (0x740a50c327e, 0x21a0), (0x960a50c327e, 0x1843c40e20ff), (0xa60a50c327e, 0x0)]
def A419r6p14 : RecordPage := #[
(0xb60a50c327e, 0x80), (0x831a50c327e, 0x818), (0xa31a50c327e, 0x5c), (0x862a50c327e, 0x111),
(0x863a50c327e, 0x111), (0xa63a50c327e, 0x0), (0xa10860c327e, 0x0), (0x220860c327e, 0xc6318),
(0xa30860c327e, 0x0), (0xa40860c327e, 0x0), (0xa60860c327e, 0x0), (0x210c60c327e, 0x0),
(0x230c60c327e, 0x2278), (0x240c60c327e, 0x18), (0x321c60c327e, 0x44d15), (0x710960c327e, 0x18),
(0xb10960c327e, 0x87fe11710008), (0x620960c327e, 0x18), (0x630960c327e, 0x18), (0xa30960c327e, 0x8),
(0xa40960c327e, 0x0), (0xa60960c327e, 0x919), (0x421960c327e, 0x2368), (0x431960c327e, 0x2360),
(0x531960c327e, 0x11d), (0x230d60c327e, 0x18), (0x240d60c327e, 0x18), (0x221d60c327e, 0x115),
(0xa60a60c327e, 0x0), (0xa31a60c327e, 0x0), (0x32e60c327e, 0x0), (0x42e60c327e, 0x8)]
def A419r6p15 : RecordPage := #[
(0x420b60c327e, 0x49523c2428f8100), (0x530b60c327e, 0x252938100), (0x540b60c327e, 0x25e96e12b023e0), (0x50b60c327e, 0x213d49d3b4e409ba6a998131),
(0x450b60c327e, 0x1414fd2b024e002438), (0x60b60c327e, 0x18c63004252a28143), (0x460b60c327e, 0x184fd2d0252002464), (0x860b60c327e, 0x0),
(0x560b60c327e, 0x61414bc00494ff), (0x421b60c327e, 0x50d3700147), (0x431b60c327e, 0x515390211d), (0x831b60c327e, 0x9da113),
(0xa31b60c327e, 0x4f518), (0x60f60c327e, 0x2928), (0x70f60c327e, 0x8), (0x170f60c327e, 0x0),
(0x32f60c327e, 0x0), (0x42f60c327e, 0x2928), (0x720861c327e, 0xa), (0x630861c327e, 0x0),
(0x730861c327e, 0x0), (0x31861c327e, 0x3184450bc6000c610a46d000236000100), (0x431861c327e, 0x42360), (0x831861c327e, 0x2100),
(0x531861c327e, 0x214b), (0xa31861c327e, 0x214b), (0x630862c327e, 0x8), (0x210d62c327e, 0x2960),
(0xb20a62c327e, 0x0), (0x230c65c327e, 0x0), (0x330c65c327e, 0xff), (0x260c65c327e, 0x0)]
def A419r6p16 : RecordPage := #[
(0x230d65c327e, 0x14d), (0x330d65c327e, 0x0), (0x240d65c327e, 0x8), (0x250d65c327e, 0x1c),
(0x330e65c327e, 0x804), (0x130f65c327e, 0x0), (0x50f65c327e, 0x1c), (0x60f65c327e, 0x0),
(0x70f65c327e, 0x0), (0xa40a50d327e, 0x1a), (0x960a50d327e, 0x1c), (0xa60a50d327e, 0x0),
(0xb60a50d327e, 0x6151129e402028), (0x861a50d327e, 0x48), (0xa61a50d327e, 0x0), (0x863a50d327e, 0x0),
(0x620a60d327e, 0x0), (0xa40a60d327e, 0x0), (0xa60a60d327e, 0x0), (0x621a60d327e, 0xc),
(0x862a60d327e, 0x0), (0x840b60d327e, 0x0), (0x860b60d327e, 0x953), (0x630851d327e, 0x155),
(0x960851d327e, 0x14d), (0xb60851d327e, 0xaeab6acaafc), (0x861851d327e, 0x39c), (0xa61851d327e, 0x1c),
(0x863851d327e, 0x15f), (0x720961d327e, 0x0), (0x630961d327e, 0x0), (0xa40961d327e, 0x0)]
def A419r6p17 : RecordPage := #[
(0xa60961d327e, 0x161), (0x31961d327e, 0x6318c630858e94), (0x431961d327e, 0x14), (0x720862d327e, 0x58d65),
(0x630862d327e, 0x59400), (0x330c65d327e, 0x0), (0x240c65d327e, 0x6), (0x260c65d327e, 0x0),
(0x330d65d327e, 0x14d), (0x250d65d327e, 0x0), (0x330e65d327e, 0x0), (0x130f65d327e, 0x0),
(0x50f65d327e, 0x0), (0x60f65d327e, 0x0), (0x70f65d327e, 0x0), (0x230c50c427e, 0x18),
(0x240c50c427e, 0x18), (0x321c50c427e, 0x167), (0x230d50c427e, 0x398), (0x240d50c427e, 0x18),
(0x221d50c427e, 0x167), (0x960a50c427e, 0x30b5e969e7103), (0xa60a50c427e, 0x0), (0xb60a50c427e, 0x80),
(0x831a50c427e, 0x18), (0xa31a50c427e, 0x0), (0x862a50c427e, 0x16d), (0x863a50c427e, 0x1c),
(0xa63a50c427e, 0x1c), (0x42e50c427e, 0x0), (0x42f50c427e, 0x1c), (0xa10860c427e, 0x0)]
def A419r6p18 : RecordPage := #[
(0xa30860c427e, 0x0), (0x240860c427e, 0xc6318), (0xa60860c427e, 0x0), (0x863860c427e, 0x48),
(0xa63860c427e, 0x2), (0x210c60c427e, 0x0), (0x230c60c427e, 0x18), (0x240c60c427e, 0x18),
(0x250c60c427e, 0x0), (0x321c60c427e, 0x16f), (0x710960c427e, 0x18), (0xb10960c427e, 0x2103c2e625c79c),
(0x620960c427e, 0x18), (0x630960c427e, 0x18), (0xa30960c427e, 0x805), (0xa60960c427e, 0x14d),
(0x421960c427e, 0x1c), (0x431960c427e, 0x1c), (0x531960c427e, 0x175), (0x230d60c427e, 0x18),
(0x240d60c427e, 0x18), (0x221d60c427e, 0x16f), (0xa60a60c427e, 0x0), (0xa31a60c427e, 0x0),
(0x863a60c427e, 0x0), (0xa63a60c427e, 0x0), (0x32e60c427e, 0x0), (0x42e60c427e, 0x0),
(0x530b60c427e, 0x5ed795df9c), (0x40b60c427e, 0xade30c1aeec0afe05f718), (0x440b60c427e, 0x61c1861577e0382), (0x50b60c427e, 0x2bac9af2c8b1e06344c58189)]
def A419r6p19 : RecordPage := #[
(0x450b60c427e, 0xcbb2a261579e0398), (0x60b60c427e, 0xc63185ed9d0000cd8199), (0x460b60c427e, 0x61951017be0388), (0x860b60c427e, 0x2b20),
(0x560b60c427e, 0x30cb8187e7103), (0x421b60c427e, 0x19b6357de719f), (0x431b60c427e, 0x19d63d7fe7175), (0x831b60c427e, 0x64581),
(0xa31b60c427e, 0xc9b078), (0x50f60c427e, 0x1a1), (0x60f60c427e, 0x1a3), (0x70f60c427e, 0x1a5),
(0x170f60c427e, 0x0), (0x32f60c427e, 0x1a5), (0x42f60c427e, 0x68da1), (0x630861c427e, 0x0),
(0x531861c427e, 0x1c), (0x861861c427e, 0xd3a160), (0xa61861c427e, 0x0), (0x863861c427e, 0x34e8),
(0xa63861c427e, 0x1a9), (0x630852c427e, 0x0), (0x860852c427e, 0x1c), (0xa60852c427e, 0x0),
(0x861852c427e, 0x34e0), (0xa61852c427e, 0x0), (0x210d52c427e, 0x1c), (0xb20a52c427e, 0x1c),
(0xa60a52c427e, 0x0), (0x630862c427e, 0x0), (0x640862c427e, 0x1c), (0xa60862c427e, 0x0)]
def A419r6p20 : RecordPage := #[
(0x250c62c427e, 0x0), (0x210d62c427e, 0x1c), (0xb20a62c427e, 0x0), (0xa60a62c427e, 0x0),
(0x230c65c427e, 0x0), (0x330c65c427e, 0x15fe7103), (0x240c65c427e, 0x1c), (0x230d65c427e, 0x50),
(0x330d65c427e, 0x0), (0x240d65c427e, 0x1c), (0x250d65c427e, 0x1c), (0x230e65c427e, 0x0),
(0x330e65c427e, 0x388), (0x250e65c427e, 0x1c), (0x30f65c427e, 0x0), (0x130f65c427e, 0x39c),
(0x40f65c427e, 0x1c), (0x50f65c427e, 0x1c), (0x70f65c427e, 0x0), (0xa30610c527e, 0x0),
(0xa50610c527e, 0xd6b560), (0xa60610c527e, 0x1af), (0xb51610c527e, 0x1ab6c400), (0x852610c527e, 0x2360),
(0xa52610c527e, 0x1ad), (0xa50a30c527e, 0x6803), (0xa40a50c527e, 0x0), (0x860a50c527e, 0x0),
(0xa60a50c527e, 0x9b3), (0xa31a50c527e, 0x0), (0x861a50c527e, 0x1c), (0xa61a50c527e, 0x0)]
def A419r6p21 : RecordPage := #[
(0x42e50c527e, 0x11b), (0x140f50c527e, 0x0), (0x60f50c527e, 0x6d5b1), (0x70f50c527e, 0x1b7),
(0x170f50c527e, 0x0), (0x42f50c527e, 0x1b76d74a), (0xa40a60c527e, 0x0), (0xa60a60c527e, 0x14d),
(0xa31a60c527e, 0x0), (0x610852c527e, 0x11b), (0x630852c527e, 0x11b), (0x861852c527e, 0x69d0b),
(0xa61852c527e, 0x69b9), (0x210d52c527e, 0x2960), (0x720a52c527e, 0x8), (0xb20a52c527e, 0x0),
(0x430a52c527e, 0x8da1ad), (0x330e52c527e, 0x8), (0x130f52c527e, 0x0), (0x60f52c527e, 0xa),
(0x70f52c527e, 0xa), (0x170f52c527e, 0x0), (0x250c62c527e, 0x0), (0x130f62c527e, 0x0),
(0x50f62c527e, 0x0), (0x60f62c527e, 0x0), (0x70f62c527e, 0x0), (0x170f62c527e, 0x0),
(0x330c65c527e, 0x2028), (0x330d65c527e, 0x6a404), (0x330e65c527e, 0x0), (0x240e65c527e, 0x3728)]
def A419r6p22 : RecordPage := #[
(0x250e65c527e, 0x1c), (0x350e65c527e, 0x0), (0x130f65c527e, 0x0), (0x50f65c527e, 0x1c),
(0x150f65c527e, 0x0), (0x340c30d527e, 0x18), (0xa50a30d527e, 0x1a), (0x230c50d527e, 0x3778),
(0x340c50d527e, 0x18), (0x321c50d527e, 0x1bd), (0x42c50d527e, 0x8db760), (0x230d50d527e, 0xa437f8),
(0x340d50d527e, 0x18), (0x260d50d527e, 0x521c1), (0x270d50d527e, 0x521c3), (0x221d50d527e, 0xe1b83a6fdbd),
(0x620a50d527e, 0x0), (0xa40a50d527e, 0x0), (0x860a50d527e, 0x61c7d38a6), (0xa60a50d527e, 0x0),
(0x931a50d527e, 0x35b8), (0xb31a50d527e, 0xe5b93a6fd1d), (0x861a50d527e, 0x1c), (0xa61a50d527e, 0x1a),
(0x142e50d527e, 0x1ad), (0x40f50d527e, 0x100), (0x142f50d527e, 0xa), (0x230c60d527e, 0x18),
(0x340c60d527e, 0x39b8), (0x240a60d527e, 0x5871800b18), (0x640a60d527e, 0x2), (0xa40a60d527e, 0x0)]
def A419r6p23 : RecordPage := #[
(0x740a60d527e, 0x73c05), (0xa60a60d527e, 0x0), (0x931a60d527e, 0x18), (0xb31a60d527e, 0xeaba6e8f175),
(0x861a60d527e, 0x808), (0xa61a60d527e, 0x5c), (0x250e60d527e, 0x1af), (0x610852d527e, 0x1bb),
(0xa10852d527e, 0x0), (0x720852d527e, 0x51d7), (0xb20852d527e, 0x5000), (0x630852d527e, 0x75c00),
(0x861852d527e, 0x1d9), (0xa61852d527e, 0x1a), (0x330c52d527e, 0x5000), (0x330d52d527e, 0x2100),
(0x630a52d527e, 0x1bb), (0x60f52d527e, 0x4392a), (0x70f52d527e, 0x4396a), (0x170f52d527e, 0x0),
(0x250c62d527e, 0x0), (0x330d62d527e, 0x13b60), (0x50f62d527e, 0x71d1), (0x60f62d527e, 0x71d3),
(0x70f62d527e, 0x71d5), (0x170f62d527e, 0x0), (0x230c65d527e, 0x18774504051c), (0x330c65d527e, 0x0),
(0x240c65d527e, 0x3b26), (0x330d65d527e, 0x0), (0x230e65d527e, 0x1c), (0x330e65d527e, 0x0)]
def A419r6p24 : RecordPage := #[
(0x250e65d527e, 0x0), (0x350e65d527e, 0x1c), (0x130f65d527e, 0x0), (0x50f65d527e, 0x0),
(0x150f65d527e, 0x1c), (0xa60a30c437e, 0x6), (0xb60a30c437e, 0x42), (0x862a30c437e, 0x1a),
(0xa62a30c437e, 0x1a), (0x863a30c437e, 0x1f62), (0xa63a30c437e, 0x2), (0xa60a50c437e, 0x6),
(0xb60a50c437e, 0x0), (0x862a50c437e, 0x3b20), (0xa62a50c437e, 0x0), (0x863a50c437e, 0x1c),
(0xa63a50c437e, 0x1c), (0xa10860c437e, 0x0), (0xa20860c437e, 0x0), (0xa30860c437e, 0x0),
(0x240860c437e, 0xc6318), (0xa40860c437e, 0x0), (0x250860c437e, 0x795e3785df), (0x260860c437e, 0xc6318),
(0xa60860c437e, 0x0), (0x210c60c437e, 0x0), (0x230c60c437e, 0x18), (0x240c60c437e, 0x18),
(0x250c60c437e, 0x0), (0x260c60c437e, 0x0), (0x270c60c437e, 0x0), (0x321c60c437e, 0x7a5e7)]
def A419r6p25 : RecordPage := #[
(0x710960c437e, 0x3d78), (0xb10960c437e, 0x101c3da208504), (0x620960c437e, 0x18), (0xa20960c437e, 0x14d),
(0x630960c437e, 0x18), (0xa30960c437e, 0x83d), (0xa40960c437e, 0x0), (0xa60960c437e, 0x0),
(0x421960c437e, 0x4), (0x521960c437e, 0x1ef), (0x431960c437e, 0x8), (0x531960c437e, 0x1f1),
(0x230d60c437e, 0x18), (0x240d60c437e, 0x58), (0x221d60c437e, 0x1e7), (0xa40a60c437e, 0x0),
(0xa60a60c437e, 0x0), (0xa21a60c437e, 0x0), (0xa31a60c437e, 0x0), (0x32e60c437e, 0x0),
(0x42e60c437e, 0x0), (0x420b60c437e, 0xfdbf387ddf57cc96), (0x520b60c437e, 0x805ff7f504), (0x430b60c437e, 0x105c13881e0580d16),
(0x530b60c437e, 0x8460f83488), (0x40b60c437e, 0xc621983617855fd84f18), (0x440b60c437e, 0x87e1dc43706c06febe62), (0x840b60c437e, 0x0),
(0x540b60c437e, 0x112c478886057d421), (0x50b60c437e, 0x8e60f8de358cdff8c62f8b62b8a627), (0x450b60c437e, 0x47b1dc430dc1f03bfefbbd78), (0x60b60c437e, 0xc621191643806418ff18)]
def A419r6p26 : RecordPage := #[
(0x460b60c437e, 0xc47711c3b08c1300bf20), (0x860b60c437e, 0x0), (0x560b60c437e, 0x188f62587e0b7ed01), (0x421b60c437e, 0x47f17c26891def),
(0x821b60c437e, 0x90631), (0xa21b60c437e, 0x121c678), (0x431b60c437e, 0x48b1ac2a491df1), (0x831b60c437e, 0x8de17),
(0xa31b60c437e, 0x11cc338), (0x50f60c437e, 0x249), (0x60f60c437e, 0x9364b7ade9), (0x70f60c437e, 0x24f),
(0x32f60c437e, 0x93e4b), (0x42f60c437e, 0x93649), (0x720861c437e, 0x94e51), (0x630861c437e, 0x255),
(0x730861c437e, 0x0), (0xa40861c437e, 0x4), (0x660861c437e, 0x4a20), (0x760861c437e, 0x25594e57),
(0x431861c437e, 0x491c48), (0x531861c437e, 0x4), (0x270c61c437e, 0x0), (0x210d61c437e, 0x4),
(0xb20a61c437e, 0x0), (0x431a61c437e, 0x48), (0x531a61c437e, 0x0), (0x720862c437e, 0x96e59),
(0x630862c437e, 0x25d), (0x730862c437e, 0x0), (0x640862c437e, 0x4b22), (0x740862c437e, 0x25d96e5f)]
def A419r6p27 : RecordPage := #[
(0xa60862c437e, 0x8), (0x250c62c437e, 0x0), (0x210d62c437e, 0x48), (0xb20a62c437e, 0x2),
(0xa30a10d437e, 0x1a), (0xa50a10d437e, 0x1c), (0xa60a30d437e, 0x0), (0xb60a30d437e, 0x2c4c2210464),
(0x863a30d437e, 0x1b22), (0xa40a60d437e, 0x0), (0xa60a60d437e, 0x0), (0xa21a60d437e, 0x0),
(0x840b60d437e, 0x0), (0x860b60d437e, 0x0), (0xa60b60d437e, 0x1c), (0x821b60d437e, 0x0),
(0xa21b60d437e, 0x18), (0x240c61d437e, 0x0), (0x270c61d437e, 0x4c7c), (0x240d61d437e, 0x382),
(0x720862d437e, 0x0), (0x640862d437e, 0x382), (0x740862d437e, 0x7265), (0xa60862d437e, 0x0),
(0xa60a50e437e, 0x0), (0xb60a50e437e, 0x313388003fc08), (0x862a50e437e, 0x3720), (0xa40a60e437e, 0x0),
(0xa60a60e437e, 0x0), (0xa31a60e437e, 0x0), (0x840b60e437e, 0x0), (0xa40b60e437e, 0x1a)]
def A419r6p28 : RecordPage := #[
(0x860b60e437e, 0x0), (0x831b60e437e, 0x0), (0xa31b60e437e, 0x18), (0x720861e437e, 0x0),
(0xa40861e437e, 0x0), (0x660861e437e, 0x340), (0x760861e437e, 0x6a69), (0x240c62e437e, 0x0),
(0x250c62e437e, 0x4d7a), (0x240d62e437e, 0x340), (0xa40860f437e, 0x0), (0xa60860f437e, 0x0),
(0x840960f437e, 0x0), (0xa40960f437e, 0x0), (0x860960f437e, 0x0), (0xa60960f437e, 0x0),
(0xa30610c537e, 0x0), (0xa50610c537e, 0x1bb), (0xa60610c537e, 0x26d), (0xa30a10c537e, 0x0),
(0xa50a10c537e, 0x0), (0x261e10c537e, 0x0), (0x361e10c537e, 0x26f), (0xa50a30c537e, 0x0),
(0xa60a30c537e, 0x6), (0x261e30c537e, 0x0), (0x361e30c537e, 0x271), (0xc10250c537e, 0x113),
(0xc30250c537e, 0x0), (0xe30250c537e, 0x0), (0xc50250c537e, 0x0), (0xe50250c537e, 0x313a8273)]
def A419r6p29 : RecordPage := #[
(0xf50250c537e, 0x0), (0xc52250c537e, 0xa77), (0xd52250c537e, 0x0), (0xe52250c537e, 0x0),
(0xf52250c537e, 0x627b14f289441c), (0x420650c537e, 0x100), (0xa61650c537e, 0x0), (0xb61650c537e, 0x251),
(0xa60a50c537e, 0x627f04fa6), (0x50750c537e, 0x4d32be80a421548d1ea50271d01089bd546d1744d0f42d078c5038), (0xa61750c537e, 0x147caa8), (0xb61750c537e, 0x148a253),
(0xa40a60c537e, 0x0), (0xa60a60c537e, 0x1c), (0xa31a60c537e, 0x0), (0x250c62c537e, 0x277),
(0x330e62c537e, 0x4), (0x130f62c537e, 0x5264), (0x50f62c537e, 0x279), (0x60f62c537e, 0x27b),
(0xa30a10d537e, 0x0), (0xa50a10d537e, 0x0), (0xa50a30d537e, 0x0), (0xa60a30d537e, 0x0),
(0xa32a30d537e, 0x0), (0xa60a50d537e, 0x0), (0xa32a50d537e, 0x0), (0x230c60d537e, 0x18),
(0x321c60d537e, 0x295), (0x230d60d537e, 0x252f8), (0x250d60d537e, 0x1299), (0x260d60d537e, 0x129b)]
def A419r6p30 : RecordPage := #[
(0x221d60d537e, 0x1ca6e99a5e95), (0x240a60d537e, 0xc629d9b718), (0x640a60d537e, 0x2), (0xa40a60d537e, 0x0),
(0x740a60d537e, 0xa7c3d), (0xa60a60d537e, 0x1c), (0x931a60d537e, 0x18), (0xb31a60d537e, 0x1ca8ea1a5df1),
(0xa32a60d537e, 0x29d), (0x250e60d537e, 0x26d), (0x330c62d537e, 0x8), (0x250c62d537e, 0x0),
(0x330d62d537e, 0x154a4), (0x50f62d537e, 0x12a1), (0x60f62d537e, 0x12a3), (0xa60a50e537e, 0x40),
(0x840a60e537e, 0x0), (0xa40a60e537e, 0x1a), (0xa60a60e537e, 0x1c), (0xa31a60e537e, 0x0),
(0x240c62e537e, 0x0), (0x250c62e537e, 0x0), (0x240d62e537e, 0x0), (0x40f62e537e, 0x0),
(0x50f62e537e, 0x0), (0x60f62e537e, 0x0), (0xd20040f537e, 0x2aa7), (0x430040f537e, 0x42148ad6b3ac6afab6abaa718c2042),
(0xc30040f537e, 0x56e2), (0x530040f537e, 0x210a457b5dd722), (0xe30040f537e, 0x5820afeb9), (0x440040f537e, 0x210a458f62d835dd6f55d538c6308b0c00)]
def A419r6p31 : RecordPage := #[
(0xc40040f537e, 0x2ad022c9), (0x540040f537e, 0x210a457b57d960), (0xe40040f537e, 0x5622b36cb), (0xc50040f537e, 0x2b3),
(0xd50040f537e, 0x2c5), (0xe50040f537e, 0xad79688acf), (0xf50040f537e, 0xb1c1c15ab69e118), (0xc52040f537e, 0xad7),
(0xd52040f537e, 0x0), (0xe52040f537e, 0x22d9), (0xf52040f537e, 0x7056fa2ddb6ded), (0xd20050f537e, 0x29bf),
(0xc30050f537e, 0x0), (0xc50050f537e, 0x0), (0xe50050f537e, 0x18b8440), (0xf50050f537e, 0x0),
(0xc52050f537e, 0xae3), (0xd52050f537e, 0x0), (0xe52050f537e, 0x22e5), (0xf52050f537e, 0xc5da2bad174dcfc),
(0xa60850f537e, 0x31778808), (0xd20060f537e, 0x2f1), (0xe20060f537e, 0x0), (0xc30060f537e, 0x0),
(0xe30060f537e, 0x0), (0xc50060f537e, 0x0), (0xe50060f537e, 0x11c), (0x840860f537e, 0x0),
(0xa40860f537e, 0x1a), (0xa60860f537e, 0x380), (0x931860f537e, 0x45e38), (0xb31860f537e, 0x1cc5ea2bcd16)]
def A419r6p32 : RecordPage := #[
(0x250c62f537e, 0x2e3c5ae49645a), (0x240e62f537e, 0x172db3abc5ef), (0x40f62f537e, 0x174e2dd16896), (0x50f62f537e, 0x5d78b7c979defa),
(0x60f62f537e, 0x5da2d12f5be5ed), (0xa30610c547e, 0xe9), (0xa50610c547e, 0x0), (0xa60610c547e, 0x2fb),
(0xa30a10c547e, 0x0), (0xa50a10c547e, 0x0), (0x241e10c547e, 0x0), (0x341e10c547e, 0x2fd),
(0xc10230c547e, 0x85), (0xc40230c547e, 0x0), (0xe40230c547e, 0x0), (0xc50230c547e, 0x0),
(0xe50230c547e, 0x180e2ff), (0xf50230c547e, 0x0), (0x420630c547e, 0x82), (0xa51630c547e, 0x0),
(0xa61630c547e, 0x0), (0xb61630c547e, 0x259), (0xa60a30c547e, 0x305c6066), (0x40730c547e, 0x4cb2ff046210d8ce2e630315e0884bf4d89e2387e1b85e138c60f8),
(0xa51730c547e, 0x315), (0xa61730c547e, 0x18bcba4), (0xb61730c547e, 0x18c925b), (0xa40a50c547e, 0x0),
(0xa60a50c547e, 0x6), (0xa40a60c547e, 0x1a), (0xa60a60c547e, 0x0), (0xa30a10d547e, 0x0)]
def A419r6p33 : RecordPage := #[
(0xa50a10d547e, 0x0), (0xa60a30d547e, 0x0), (0xa32a30d547e, 0x0), (0xa40a50d547e, 0x0),
(0xa60a50d547e, 0x0), (0xa32a50d547e, 0x0), (0x321c60d547e, 0x31b), (0x260d60d547e, 0x231d),
(0x270d60d547e, 0x231f), (0x221d60d547e, 0x18fe3babc71b), (0xa40a60d547e, 0x1a), (0x260a60d547e, 0xc6321bef18),
(0x660a60d547e, 0x0), (0xa60a60d547e, 0x0), (0x760a60d547e, 0xc8d4d), (0xa32a60d547e, 0x321),
(0x270e60d547e, 0x2fb), (0xa60a30e547e, 0x2), (0xa40a60e547e, 0x1a), (0x860a60e547e, 0x0),
(0xa60a60e547e, 0x1c), (0xd20030f547e, 0x18ed), (0xc40030f547e, 0x0), (0xc50030f547e, 0x0),
(0xe50030f547e, 0x16325), (0xf50030f547e, 0x0), (0xa60830f547e, 0x2c64e4), (0xd20040f547e, 0x1b29),
(0x430040f547e, 0x108626739be6b99e6397e5b8c6304cac42), (0xc30040f547e, 0x33d1133b), (0x530040f547e, 0x10862687a0e7e2), (0xe30040f547e, 0x68e0d173f)]
def A419r6p34 : RecordPage := #[
(0x440040f547e, 0x210c4d2f49d1f41cf72fcb718c1000), (0xc40040f547e, 0x6620), (0x540040f547e, 0x1086268799e9a0), (0xe40040f547e, 0x66a2d3f4d),
(0xc50040f547e, 0x349), (0xd50040f547e, 0x337), (0xe50040f547e, 0xd2c1a9eb51), (0xf50040f547e, 0xce41ab8b5aae098),
(0xd20060f547e, 0x297), (0xc30060f547e, 0x0), (0xe30060f547e, 0x9a), (0xc50060f547e, 0x0),
(0xe50060f547e, 0x0), (0xa40860f547e, 0x342), (0x860860f547e, 0x0), (0xa60860f547e, 0x1c)]
def A419r6 : Records := #[A419r6p0, A419r6p1, A419r6p2, A419r6p3, A419r6p4, A419r6p5, A419r6p6, A419r6p7, A419r6p8, A419r6p9, A419r6p10, A419r6p11, A419r6p12, A419r6p13, A419r6p14, A419r6p15, A419r6p16, A419r6p17, A419r6p18, A419r6p19, A419r6p20, A419r6p21, A419r6p22, A419r6p23, A419r6p24, A419r6p25, A419r6p26, A419r6p27, A419r6p28, A419r6p29, A419r6p30, A419r6p31, A419r6p32, A419r6p33, A419r6p34]
def testA419r6 : ℕ → Bool := testAt A419 bsA419 5 A419r5 A419r6 4 9
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c0 : checkBlock testA419r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c4 : checkBlock testA419r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c8 : checkBlock testA419r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c12 : checkBlock testA419r6 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c16 : checkBlock testA419r6 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c20 : checkBlock testA419r6 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c24 : checkBlock testA419r6 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c28 : checkBlock testA419r6 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c32 : checkBlock testA419r6 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c36 : checkBlock testA419r6 4 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c40 : checkBlock testA419r6 4 40 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c44 : checkBlock testA419r6 4 44 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c48 : checkBlock testA419r6 4 48 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c52 : checkBlock testA419r6 4 52 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c56 : checkBlock testA419r6 4 56 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c60 : checkBlock testA419r6 4 60 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c64 : checkBlock testA419r6 4 64 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c68 : checkBlock testA419r6 4 68 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c72 : checkBlock testA419r6 4 72 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c76 : checkBlock testA419r6 4 76 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c80 : checkBlock testA419r6 4 80 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c84 : checkBlock testA419r6 4 84 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c88 : checkBlock testA419r6 4 88 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c92 : checkBlock testA419r6 4 92 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c96 : checkBlock testA419r6 4 96 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c100 : checkBlock testA419r6 4 100 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c104 : checkBlock testA419r6 4 104 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c108 : checkBlock testA419r6 4 108 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c112 : checkBlock testA419r6 4 112 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c116 : checkBlock testA419r6 4 116 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c120 : checkBlock testA419r6 4 120 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c124 : checkBlock testA419r6 4 124 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c128 : checkBlock testA419r6 4 128 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c132 : checkBlock testA419r6 4 132 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c136 : checkBlock testA419r6 4 136 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c140 : checkBlock testA419r6 4 140 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c144 : checkBlock testA419r6 4 144 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c148 : checkBlock testA419r6 4 148 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c152 : checkBlock testA419r6 4 152 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c156 : checkBlock testA419r6 4 156 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c160 : checkBlock testA419r6 4 160 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c164 : checkBlock testA419r6 4 164 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c168 : checkBlock testA419r6 4 168 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c172 : checkBlock testA419r6 4 172 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c176 : checkBlock testA419r6 4 176 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c180 : checkBlock testA419r6 4 180 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c184 : checkBlock testA419r6 4 184 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c188 : checkBlock testA419r6 4 188 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c192 : checkBlock testA419r6 4 192 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c196 : checkBlock testA419r6 4 196 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c200 : checkBlock testA419r6 4 200 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c204 : checkBlock testA419r6 4 204 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c208 : checkBlock testA419r6 4 208 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c212 : checkBlock testA419r6 4 212 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c216 : checkBlock testA419r6 4 216 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c220 : checkBlock testA419r6 4 220 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c224 : checkBlock testA419r6 4 224 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c228 : checkBlock testA419r6 4 228 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c232 : checkBlock testA419r6 4 232 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c236 : checkBlock testA419r6 4 236 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c240 : checkBlock testA419r6 4 240 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c244 : checkBlock testA419r6 4 244 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c248 : checkBlock testA419r6 4 248 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c252 : checkBlock testA419r6 4 252 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c256 : checkBlock testA419r6 4 256 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c260 : checkBlock testA419r6 4 260 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c264 : checkBlock testA419r6 4 264 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c268 : checkBlock testA419r6 4 268 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c272 : checkBlock testA419r6 4 272 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c276 : checkBlock testA419r6 4 276 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c280 : checkBlock testA419r6 4 280 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c284 : checkBlock testA419r6 4 284 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c288 : checkBlock testA419r6 4 288 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c292 : checkBlock testA419r6 4 292 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c296 : checkBlock testA419r6 4 296 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c300 : checkBlock testA419r6 4 300 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c304 : checkBlock testA419r6 4 304 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c308 : checkBlock testA419r6 4 308 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c312 : checkBlock testA419r6 4 312 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c316 : checkBlock testA419r6 4 316 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c320 : checkBlock testA419r6 4 320 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c324 : checkBlock testA419r6 4 324 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c328 : checkBlock testA419r6 4 328 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c332 : checkBlock testA419r6 4 332 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c336 : checkBlock testA419r6 4 336 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c340 : checkBlock testA419r6 4 340 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c344 : checkBlock testA419r6 4 344 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c348 : checkBlock testA419r6 4 348 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c352 : checkBlock testA419r6 4 352 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c356 : checkBlock testA419r6 4 356 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c360 : checkBlock testA419r6 4 360 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c364 : checkBlock testA419r6 4 364 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c368 : checkBlock testA419r6 4 368 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c372 : checkBlock testA419r6 4 372 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c376 : checkBlock testA419r6 4 376 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c380 : checkBlock testA419r6 4 380 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c384 : checkBlock testA419r6 4 384 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c388 : checkBlock testA419r6 4 388 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c392 : checkBlock testA419r6 4 392 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c396 : checkBlock testA419r6 4 396 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c400 : checkBlock testA419r6 4 400 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c404 : checkBlock testA419r6 4 404 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c408 : checkBlock testA419r6 4 408 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c412 : checkBlock testA419r6 4 412 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c416 : checkBlock testA419r6 4 416 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c420 : checkBlock testA419r6 4 420 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c424 : checkBlock testA419r6 4 424 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c428 : checkBlock testA419r6 4 428 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c432 : checkBlock testA419r6 4 432 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c436 : checkBlock testA419r6 4 436 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c440 : checkBlock testA419r6 4 440 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c444 : checkBlock testA419r6 4 444 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c448 : checkBlock testA419r6 4 448 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c452 : checkBlock testA419r6 4 452 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c456 : checkBlock testA419r6 4 456 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c460 : checkBlock testA419r6 4 460 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c464 : checkBlock testA419r6 4 464 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c468 : checkBlock testA419r6 4 468 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c472 : checkBlock testA419r6 4 472 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c476 : checkBlock testA419r6 4 476 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c480 : checkBlock testA419r6 4 480 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c484 : checkBlock testA419r6 4 484 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c488 : checkBlock testA419r6 4 488 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c492 : checkBlock testA419r6 4 492 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c496 : checkBlock testA419r6 4 496 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c500 : checkBlock testA419r6 4 500 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c504 : checkBlock testA419r6 4 504 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c508 : checkBlock testA419r6 4 508 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c512 : checkBlock testA419r6 4 512 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c516 : checkBlock testA419r6 4 516 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c520 : checkBlock testA419r6 4 520 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c524 : checkBlock testA419r6 4 524 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c528 : checkBlock testA419r6 4 528 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c532 : checkBlock testA419r6 4 532 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c536 : checkBlock testA419r6 4 536 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c540 : checkBlock testA419r6 4 540 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c544 : checkBlock testA419r6 4 544 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c548 : checkBlock testA419r6 4 548 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c552 : checkBlock testA419r6 4 552 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c556 : checkBlock testA419r6 4 556 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c560 : checkBlock testA419r6 4 560 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c564 : checkBlock testA419r6 4 564 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c568 : checkBlock testA419r6 4 568 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c572 : checkBlock testA419r6 4 572 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c576 : checkBlock testA419r6 4 576 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c580 : checkBlock testA419r6 4 580 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c584 : checkBlock testA419r6 4 584 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c588 : checkBlock testA419r6 4 588 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c592 : checkBlock testA419r6 4 592 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c596 : checkBlock testA419r6 4 596 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c600 : checkBlock testA419r6 4 600 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c604 : checkBlock testA419r6 4 604 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c608 : checkBlock testA419r6 4 608 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c612 : checkBlock testA419r6 4 612 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c616 : checkBlock testA419r6 4 616 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c620 : checkBlock testA419r6 4 620 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c624 : checkBlock testA419r6 4 624 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c628 : checkBlock testA419r6 4 628 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c632 : checkBlock testA419r6 4 632 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c636 : checkBlock testA419r6 4 636 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c640 : checkBlock testA419r6 4 640 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c644 : checkBlock testA419r6 4 644 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c648 : checkBlock testA419r6 4 648 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c652 : checkBlock testA419r6 4 652 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c656 : checkBlock testA419r6 4 656 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c660 : checkBlock testA419r6 4 660 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c664 : checkBlock testA419r6 4 664 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c668 : checkBlock testA419r6 4 668 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c672 : checkBlock testA419r6 4 672 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c676 : checkBlock testA419r6 4 676 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c680 : checkBlock testA419r6 4 680 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c684 : checkBlock testA419r6 4 684 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c688 : checkBlock testA419r6 4 688 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c692 : checkBlock testA419r6 4 692 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c696 : checkBlock testA419r6 4 696 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c700 : checkBlock testA419r6 4 700 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c704 : checkBlock testA419r6 4 704 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c708 : checkBlock testA419r6 4 708 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c712 : checkBlock testA419r6 4 712 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c716 : checkBlock testA419r6 4 716 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c720 : checkBlock testA419r6 4 720 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c724 : checkBlock testA419r6 4 724 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c728 : checkBlock testA419r6 4 728 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c732 : checkBlock testA419r6 4 732 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c736 : checkBlock testA419r6 4 736 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c740 : checkBlock testA419r6 4 740 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c744 : checkBlock testA419r6 4 744 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c748 : checkBlock testA419r6 4 748 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c752 : checkBlock testA419r6 4 752 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c756 : checkBlock testA419r6 4 756 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c760 : checkBlock testA419r6 4 760 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c764 : checkBlock testA419r6 4 764 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c768 : checkBlock testA419r6 4 768 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c772 : checkBlock testA419r6 4 772 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c776 : checkBlock testA419r6 4 776 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c780 : checkBlock testA419r6 4 780 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c784 : checkBlock testA419r6 4 784 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c788 : checkBlock testA419r6 4 788 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c792 : checkBlock testA419r6 4 792 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c796 : checkBlock testA419r6 4 796 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c800 : checkBlock testA419r6 4 800 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c804 : checkBlock testA419r6 4 804 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c808 : checkBlock testA419r6 4 808 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c812 : checkBlock testA419r6 4 812 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c816 : checkBlock testA419r6 4 816 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c820 : checkBlock testA419r6 4 820 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c824 : checkBlock testA419r6 4 824 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c828 : checkBlock testA419r6 4 828 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c832 : checkBlock testA419r6 4 832 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c836 : checkBlock testA419r6 4 836 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c840 : checkBlock testA419r6 4 840 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c844 : checkBlock testA419r6 4 844 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c848 : checkBlock testA419r6 4 848 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c852 : checkBlock testA419r6 4 852 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c856 : checkBlock testA419r6 4 856 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c860 : checkBlock testA419r6 4 860 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c864 : checkBlock testA419r6 4 864 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c868 : checkBlock testA419r6 4 868 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c872 : checkBlock testA419r6 4 872 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c876 : checkBlock testA419r6 4 876 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c880 : checkBlock testA419r6 4 880 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c884 : checkBlock testA419r6 4 884 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c888 : checkBlock testA419r6 4 888 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c892 : checkBlock testA419r6 4 892 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c896 : checkBlock testA419r6 4 896 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c900 : checkBlock testA419r6 4 900 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c904 : checkBlock testA419r6 4 904 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c908 : checkBlock testA419r6 4 908 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c912 : checkBlock testA419r6 4 912 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c916 : checkBlock testA419r6 4 916 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c920 : checkBlock testA419r6 4 920 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c924 : checkBlock testA419r6 4 924 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c928 : checkBlock testA419r6 4 928 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c932 : checkBlock testA419r6 4 932 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c936 : checkBlock testA419r6 4 936 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c940 : checkBlock testA419r6 4 940 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c944 : checkBlock testA419r6 4 944 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c948 : checkBlock testA419r6 4 948 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c952 : checkBlock testA419r6 4 952 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c956 : checkBlock testA419r6 4 956 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c960 : checkBlock testA419r6 4 960 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c964 : checkBlock testA419r6 4 964 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c968 : checkBlock testA419r6 4 968 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c972 : checkBlock testA419r6 4 972 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c976 : checkBlock testA419r6 4 976 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c980 : checkBlock testA419r6 4 980 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c984 : checkBlock testA419r6 4 984 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c988 : checkBlock testA419r6 4 988 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c992 : checkBlock testA419r6 4 992 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c996 : checkBlock testA419r6 4 996 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1000 : checkBlock testA419r6 4 1000 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1004 : checkBlock testA419r6 4 1004 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1008 : checkBlock testA419r6 4 1008 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1012 : checkBlock testA419r6 4 1012 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1016 : checkBlock testA419r6 4 1016 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1020 : checkBlock testA419r6 4 1020 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1024 : checkBlock testA419r6 4 1024 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1028 : checkBlock testA419r6 4 1028 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1032 : checkBlock testA419r6 4 1032 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1036 : checkBlock testA419r6 4 1036 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1040 : checkBlock testA419r6 4 1040 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1044 : checkBlock testA419r6 4 1044 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1048 : checkBlock testA419r6 4 1048 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1052 : checkBlock testA419r6 4 1052 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1056 : checkBlock testA419r6 4 1056 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1060 : checkBlock testA419r6 4 1060 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1064 : checkBlock testA419r6 4 1064 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1068 : checkBlock testA419r6 4 1068 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1072 : checkBlock testA419r6 4 1072 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1076 : checkBlock testA419r6 4 1076 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1080 : checkBlock testA419r6 4 1080 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1084 : checkBlock testA419r6 4 1084 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1088 : checkBlock testA419r6 4 1088 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1092 : checkBlock testA419r6 4 1092 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1096 : checkBlock testA419r6 4 1096 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r6c1100 : checkBlock testA419r6 4 1100 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA419r6 : LayerOK A419 6 A419r6 := by
  apply layer_of_block (bs := bsA419) (k := 5) (old := A419r5) (cw := 4) (rw := 9) (by decide +kernel) vbsA419 vA419r5
  exact @block_merge testA419r6 0 1104 16 (@block_merge testA419r6 0 552 552 (@block_merge testA419r6 0 276 276 (@block_merge testA419r6 0 136 140 (@block_merge testA419r6 0 68 68 (@block_merge testA419r6 0 32 36 (@block_merge testA419r6 0 16 16 (@block_merge testA419r6 0 8 8 (@block_merge testA419r6 0 4 4 A419r6c0 A419r6c4) (@block_merge testA419r6 8 4 4 A419r6c8 A419r6c12)) (@block_merge testA419r6 16 8 8 (@block_merge testA419r6 16 4 4 A419r6c16 A419r6c20) (@block_merge testA419r6 24 4 4 A419r6c24 A419r6c28))) (@block_merge testA419r6 32 16 20 (@block_merge testA419r6 32 8 8 (@block_merge testA419r6 32 4 4 A419r6c32 A419r6c36) (@block_merge testA419r6 40 4 4 A419r6c40 A419r6c44)) (@block_merge testA419r6 48 8 12 (@block_merge testA419r6 48 4 4 A419r6c48 A419r6c52) (@block_merge testA419r6 56 4 8 A419r6c56 (@block_merge testA419r6 60 4 4 A419r6c60 A419r6c64))))) (@block_merge testA419r6 68 32 36 (@block_merge testA419r6 68 16 16 (@block_merge testA419r6 68 8 8 (@block_merge testA419r6 68 4 4 A419r6c68 A419r6c72) (@block_merge testA419r6 76 4 4 A419r6c76 A419r6c80)) (@block_merge testA419r6 84 8 8 (@block_merge testA419r6 84 4 4 A419r6c84 A419r6c88) (@block_merge testA419r6 92 4 4 A419r6c92 A419r6c96))) (@block_merge testA419r6 100 16 20 (@block_merge testA419r6 100 8 8 (@block_merge testA419r6 100 4 4 A419r6c100 A419r6c104) (@block_merge testA419r6 108 4 4 A419r6c108 A419r6c112)) (@block_merge testA419r6 116 8 12 (@block_merge testA419r6 116 4 4 A419r6c116 A419r6c120) (@block_merge testA419r6 124 4 8 A419r6c124 (@block_merge testA419r6 128 4 4 A419r6c128 A419r6c132)))))) (@block_merge testA419r6 136 68 72 (@block_merge testA419r6 136 32 36 (@block_merge testA419r6 136 16 16 (@block_merge testA419r6 136 8 8 (@block_merge testA419r6 136 4 4 A419r6c136 A419r6c140) (@block_merge testA419r6 144 4 4 A419r6c144 A419r6c148)) (@block_merge testA419r6 152 8 8 (@block_merge testA419r6 152 4 4 A419r6c152 A419r6c156) (@block_merge testA419r6 160 4 4 A419r6c160 A419r6c164))) (@block_merge testA419r6 168 16 20 (@block_merge testA419r6 168 8 8 (@block_merge testA419r6 168 4 4 A419r6c168 A419r6c172) (@block_merge testA419r6 176 4 4 A419r6c176 A419r6c180)) (@block_merge testA419r6 184 8 12 (@block_merge testA419r6 184 4 4 A419r6c184 A419r6c188) (@block_merge testA419r6 192 4 8 A419r6c192 (@block_merge testA419r6 196 4 4 A419r6c196 A419r6c200))))) (@block_merge testA419r6 204 36 36 (@block_merge testA419r6 204 16 20 (@block_merge testA419r6 204 8 8 (@block_merge testA419r6 204 4 4 A419r6c204 A419r6c208) (@block_merge testA419r6 212 4 4 A419r6c212 A419r6c216)) (@block_merge testA419r6 220 8 12 (@block_merge testA419r6 220 4 4 A419r6c220 A419r6c224) (@block_merge testA419r6 228 4 8 A419r6c228 (@block_merge testA419r6 232 4 4 A419r6c232 A419r6c236)))) (@block_merge testA419r6 240 16 20 (@block_merge testA419r6 240 8 8 (@block_merge testA419r6 240 4 4 A419r6c240 A419r6c244) (@block_merge testA419r6 248 4 4 A419r6c248 A419r6c252)) (@block_merge testA419r6 256 8 12 (@block_merge testA419r6 256 4 4 A419r6c256 A419r6c260) (@block_merge testA419r6 264 4 8 A419r6c264 (@block_merge testA419r6 268 4 4 A419r6c268 A419r6c272))))))) (@block_merge testA419r6 276 136 140 (@block_merge testA419r6 276 68 68 (@block_merge testA419r6 276 32 36 (@block_merge testA419r6 276 16 16 (@block_merge testA419r6 276 8 8 (@block_merge testA419r6 276 4 4 A419r6c276 A419r6c280) (@block_merge testA419r6 284 4 4 A419r6c284 A419r6c288)) (@block_merge testA419r6 292 8 8 (@block_merge testA419r6 292 4 4 A419r6c292 A419r6c296) (@block_merge testA419r6 300 4 4 A419r6c300 A419r6c304))) (@block_merge testA419r6 308 16 20 (@block_merge testA419r6 308 8 8 (@block_merge testA419r6 308 4 4 A419r6c308 A419r6c312) (@block_merge testA419r6 316 4 4 A419r6c316 A419r6c320)) (@block_merge testA419r6 324 8 12 (@block_merge testA419r6 324 4 4 A419r6c324 A419r6c328) (@block_merge testA419r6 332 4 8 A419r6c332 (@block_merge testA419r6 336 4 4 A419r6c336 A419r6c340))))) (@block_merge testA419r6 344 32 36 (@block_merge testA419r6 344 16 16 (@block_merge testA419r6 344 8 8 (@block_merge testA419r6 344 4 4 A419r6c344 A419r6c348) (@block_merge testA419r6 352 4 4 A419r6c352 A419r6c356)) (@block_merge testA419r6 360 8 8 (@block_merge testA419r6 360 4 4 A419r6c360 A419r6c364) (@block_merge testA419r6 368 4 4 A419r6c368 A419r6c372))) (@block_merge testA419r6 376 16 20 (@block_merge testA419r6 376 8 8 (@block_merge testA419r6 376 4 4 A419r6c376 A419r6c380) (@block_merge testA419r6 384 4 4 A419r6c384 A419r6c388)) (@block_merge testA419r6 392 8 12 (@block_merge testA419r6 392 4 4 A419r6c392 A419r6c396) (@block_merge testA419r6 400 4 8 A419r6c400 (@block_merge testA419r6 404 4 4 A419r6c404 A419r6c408)))))) (@block_merge testA419r6 412 68 72 (@block_merge testA419r6 412 32 36 (@block_merge testA419r6 412 16 16 (@block_merge testA419r6 412 8 8 (@block_merge testA419r6 412 4 4 A419r6c412 A419r6c416) (@block_merge testA419r6 420 4 4 A419r6c420 A419r6c424)) (@block_merge testA419r6 428 8 8 (@block_merge testA419r6 428 4 4 A419r6c428 A419r6c432) (@block_merge testA419r6 436 4 4 A419r6c436 A419r6c440))) (@block_merge testA419r6 444 16 20 (@block_merge testA419r6 444 8 8 (@block_merge testA419r6 444 4 4 A419r6c444 A419r6c448) (@block_merge testA419r6 452 4 4 A419r6c452 A419r6c456)) (@block_merge testA419r6 460 8 12 (@block_merge testA419r6 460 4 4 A419r6c460 A419r6c464) (@block_merge testA419r6 468 4 8 A419r6c468 (@block_merge testA419r6 472 4 4 A419r6c472 A419r6c476))))) (@block_merge testA419r6 480 36 36 (@block_merge testA419r6 480 16 20 (@block_merge testA419r6 480 8 8 (@block_merge testA419r6 480 4 4 A419r6c480 A419r6c484) (@block_merge testA419r6 488 4 4 A419r6c488 A419r6c492)) (@block_merge testA419r6 496 8 12 (@block_merge testA419r6 496 4 4 A419r6c496 A419r6c500) (@block_merge testA419r6 504 4 8 A419r6c504 (@block_merge testA419r6 508 4 4 A419r6c508 A419r6c512)))) (@block_merge testA419r6 516 16 20 (@block_merge testA419r6 516 8 8 (@block_merge testA419r6 516 4 4 A419r6c516 A419r6c520) (@block_merge testA419r6 524 4 4 A419r6c524 A419r6c528)) (@block_merge testA419r6 532 8 12 (@block_merge testA419r6 532 4 4 A419r6c532 A419r6c536) (@block_merge testA419r6 540 4 8 A419r6c540 (@block_merge testA419r6 544 4 4 A419r6c544 A419r6c548)))))))) (@block_merge testA419r6 552 276 276 (@block_merge testA419r6 552 136 140 (@block_merge testA419r6 552 68 68 (@block_merge testA419r6 552 32 36 (@block_merge testA419r6 552 16 16 (@block_merge testA419r6 552 8 8 (@block_merge testA419r6 552 4 4 A419r6c552 A419r6c556) (@block_merge testA419r6 560 4 4 A419r6c560 A419r6c564)) (@block_merge testA419r6 568 8 8 (@block_merge testA419r6 568 4 4 A419r6c568 A419r6c572) (@block_merge testA419r6 576 4 4 A419r6c576 A419r6c580))) (@block_merge testA419r6 584 16 20 (@block_merge testA419r6 584 8 8 (@block_merge testA419r6 584 4 4 A419r6c584 A419r6c588) (@block_merge testA419r6 592 4 4 A419r6c592 A419r6c596)) (@block_merge testA419r6 600 8 12 (@block_merge testA419r6 600 4 4 A419r6c600 A419r6c604) (@block_merge testA419r6 608 4 8 A419r6c608 (@block_merge testA419r6 612 4 4 A419r6c612 A419r6c616))))) (@block_merge testA419r6 620 32 36 (@block_merge testA419r6 620 16 16 (@block_merge testA419r6 620 8 8 (@block_merge testA419r6 620 4 4 A419r6c620 A419r6c624) (@block_merge testA419r6 628 4 4 A419r6c628 A419r6c632)) (@block_merge testA419r6 636 8 8 (@block_merge testA419r6 636 4 4 A419r6c636 A419r6c640) (@block_merge testA419r6 644 4 4 A419r6c644 A419r6c648))) (@block_merge testA419r6 652 16 20 (@block_merge testA419r6 652 8 8 (@block_merge testA419r6 652 4 4 A419r6c652 A419r6c656) (@block_merge testA419r6 660 4 4 A419r6c660 A419r6c664)) (@block_merge testA419r6 668 8 12 (@block_merge testA419r6 668 4 4 A419r6c668 A419r6c672) (@block_merge testA419r6 676 4 8 A419r6c676 (@block_merge testA419r6 680 4 4 A419r6c680 A419r6c684)))))) (@block_merge testA419r6 688 68 72 (@block_merge testA419r6 688 32 36 (@block_merge testA419r6 688 16 16 (@block_merge testA419r6 688 8 8 (@block_merge testA419r6 688 4 4 A419r6c688 A419r6c692) (@block_merge testA419r6 696 4 4 A419r6c696 A419r6c700)) (@block_merge testA419r6 704 8 8 (@block_merge testA419r6 704 4 4 A419r6c704 A419r6c708) (@block_merge testA419r6 712 4 4 A419r6c712 A419r6c716))) (@block_merge testA419r6 720 16 20 (@block_merge testA419r6 720 8 8 (@block_merge testA419r6 720 4 4 A419r6c720 A419r6c724) (@block_merge testA419r6 728 4 4 A419r6c728 A419r6c732)) (@block_merge testA419r6 736 8 12 (@block_merge testA419r6 736 4 4 A419r6c736 A419r6c740) (@block_merge testA419r6 744 4 8 A419r6c744 (@block_merge testA419r6 748 4 4 A419r6c748 A419r6c752))))) (@block_merge testA419r6 756 36 36 (@block_merge testA419r6 756 16 20 (@block_merge testA419r6 756 8 8 (@block_merge testA419r6 756 4 4 A419r6c756 A419r6c760) (@block_merge testA419r6 764 4 4 A419r6c764 A419r6c768)) (@block_merge testA419r6 772 8 12 (@block_merge testA419r6 772 4 4 A419r6c772 A419r6c776) (@block_merge testA419r6 780 4 8 A419r6c780 (@block_merge testA419r6 784 4 4 A419r6c784 A419r6c788)))) (@block_merge testA419r6 792 16 20 (@block_merge testA419r6 792 8 8 (@block_merge testA419r6 792 4 4 A419r6c792 A419r6c796) (@block_merge testA419r6 800 4 4 A419r6c800 A419r6c804)) (@block_merge testA419r6 808 8 12 (@block_merge testA419r6 808 4 4 A419r6c808 A419r6c812) (@block_merge testA419r6 816 4 8 A419r6c816 (@block_merge testA419r6 820 4 4 A419r6c820 A419r6c824))))))) (@block_merge testA419r6 828 136 140 (@block_merge testA419r6 828 68 68 (@block_merge testA419r6 828 32 36 (@block_merge testA419r6 828 16 16 (@block_merge testA419r6 828 8 8 (@block_merge testA419r6 828 4 4 A419r6c828 A419r6c832) (@block_merge testA419r6 836 4 4 A419r6c836 A419r6c840)) (@block_merge testA419r6 844 8 8 (@block_merge testA419r6 844 4 4 A419r6c844 A419r6c848) (@block_merge testA419r6 852 4 4 A419r6c852 A419r6c856))) (@block_merge testA419r6 860 16 20 (@block_merge testA419r6 860 8 8 (@block_merge testA419r6 860 4 4 A419r6c860 A419r6c864) (@block_merge testA419r6 868 4 4 A419r6c868 A419r6c872)) (@block_merge testA419r6 876 8 12 (@block_merge testA419r6 876 4 4 A419r6c876 A419r6c880) (@block_merge testA419r6 884 4 8 A419r6c884 (@block_merge testA419r6 888 4 4 A419r6c888 A419r6c892))))) (@block_merge testA419r6 896 32 36 (@block_merge testA419r6 896 16 16 (@block_merge testA419r6 896 8 8 (@block_merge testA419r6 896 4 4 A419r6c896 A419r6c900) (@block_merge testA419r6 904 4 4 A419r6c904 A419r6c908)) (@block_merge testA419r6 912 8 8 (@block_merge testA419r6 912 4 4 A419r6c912 A419r6c916) (@block_merge testA419r6 920 4 4 A419r6c920 A419r6c924))) (@block_merge testA419r6 928 16 20 (@block_merge testA419r6 928 8 8 (@block_merge testA419r6 928 4 4 A419r6c928 A419r6c932) (@block_merge testA419r6 936 4 4 A419r6c936 A419r6c940)) (@block_merge testA419r6 944 8 12 (@block_merge testA419r6 944 4 4 A419r6c944 A419r6c948) (@block_merge testA419r6 952 4 8 A419r6c952 (@block_merge testA419r6 956 4 4 A419r6c956 A419r6c960)))))) (@block_merge testA419r6 964 68 72 (@block_merge testA419r6 964 32 36 (@block_merge testA419r6 964 16 16 (@block_merge testA419r6 964 8 8 (@block_merge testA419r6 964 4 4 A419r6c964 A419r6c968) (@block_merge testA419r6 972 4 4 A419r6c972 A419r6c976)) (@block_merge testA419r6 980 8 8 (@block_merge testA419r6 980 4 4 A419r6c980 A419r6c984) (@block_merge testA419r6 988 4 4 A419r6c988 A419r6c992))) (@block_merge testA419r6 996 16 20 (@block_merge testA419r6 996 8 8 (@block_merge testA419r6 996 4 4 A419r6c996 A419r6c1000) (@block_merge testA419r6 1004 4 4 A419r6c1004 A419r6c1008)) (@block_merge testA419r6 1012 8 12 (@block_merge testA419r6 1012 4 4 A419r6c1012 A419r6c1016) (@block_merge testA419r6 1020 4 8 A419r6c1020 (@block_merge testA419r6 1024 4 4 A419r6c1024 A419r6c1028))))) (@block_merge testA419r6 1032 36 36 (@block_merge testA419r6 1032 16 20 (@block_merge testA419r6 1032 8 8 (@block_merge testA419r6 1032 4 4 A419r6c1032 A419r6c1036) (@block_merge testA419r6 1040 4 4 A419r6c1040 A419r6c1044)) (@block_merge testA419r6 1048 8 12 (@block_merge testA419r6 1048 4 4 A419r6c1048 A419r6c1052) (@block_merge testA419r6 1056 4 8 A419r6c1056 (@block_merge testA419r6 1060 4 4 A419r6c1060 A419r6c1064)))) (@block_merge testA419r6 1068 16 20 (@block_merge testA419r6 1068 8 8 (@block_merge testA419r6 1068 4 4 A419r6c1068 A419r6c1072) (@block_merge testA419r6 1076 4 4 A419r6c1076 A419r6c1080)) (@block_merge testA419r6 1084 8 12 (@block_merge testA419r6 1084 4 4 A419r6c1084 A419r6c1088) (@block_merge testA419r6 1092 4 8 A419r6c1092 (@block_merge testA419r6 1096 4 4 A419r6c1096 A419r6c1100))))))))) (show checkBlock testA419r6 16 1104 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A419r7p0 : RecordPage := #[
(0x860c207e, 0x7058c6818c7001782d001e818c63006098002c), (0x960c207e, 0x4f181008e30000f1006f002f82d004e818c630080a000f0), (0xa60c207e, 0x382c6340c6000108821090000318c6000000400018c), (0xe60c207e, 0x5c0560c00800007),
(0xb60c207e, 0x13e302025c600000118842021108803e4108400200750000318c631801b01900000008400084000210), (0xf60c207e, 0x6205f08016880ac1802900840001), (0x951c207e, 0x1d800e71802501100318008806fc10842101a900cc18c00020739c10042), (0x861c207e, 0xe08008f8c0840063001022821801040bc0840340548403f06300001e800000068042),
(0x942c207e, 0x1023880e71802701310b18001009ba000000025a012458c000006b5a00000), (0x862c207e, 0x101de818c084006300002a829881040c408c03c05c14448463021027884210078800), (0xc54c207e, 0x42e0800d0380b3a05704000), (0xd54c207e, 0x10b82073400739c),
(0xe54c207e, 0x340e085a16b5a), (0xf54c207e, 0x382d6b40b7a), (0xc64c207e, 0x14c1341a0001774004000), (0xd64c207e, 0x15400c3a05f04000),
(0xe64c207e, 0x201a00102d031eb5a), (0xf64c207e, 0x36835e01a400ce2d6b40cba), (0xc65c207e, 0x10c406fc1704206f14042), (0xd65c207e, 0x11780e6207114042),
(0xe65c207e, 0x89c10382203af39c), (0xf65c207e, 0x3f83ee01ec1c103cf380efc), (0x850c307e, 0x63013212e2095c6024c2444220823c23422cdc07018c63011210e2085083081), (0xc50c307e, 0x413e10213a1364),
(0xd50c307e, 0x11029c1c0a50a30a1), (0xa50c307e, 0x18c05b85a882cf180b10af108820ad0ab0a93701c06318c135ad085ad6b5a0a1081), (0xe50c307e, 0x17617214e103ad0b44), (0xf50c307e, 0x2f48409f46b5a083),
(0x860c307e, 0xc6032431c00c60818a43000002830c00c63180c1509417ea), (0xc60c307e, 0x34d400d10cf0cd0cb), (0x960c307e, 0x18c0839f180e50e310709037c8116000018c6301ba1b620d90d70d5), (0xd60c307e, 0x1aa1da1d61d2a)]
def A419r7p1 : RecordPage := #[
(0xa60c307e, 0x3180f50f3003180f1508440ef2180000318c611ad685ad694a), (0xe60c307e, 0x1f21ee1daad6b5a0d7), (0xb60c307e, 0xc60422b8c08987d888887884210d20549042c821220e20a0000000081880e318c6301fe1fbad203ef5ad6b4216b5a0cb0d5), (0xf60c307e, 0x48447c35434c47446c023381174685a0bf),
(0x951c307e, 0x3181291271150e700318d68824a42102e48412327398c6b44d6b5a26842), (0x861c307e, 0xc604d44cc2cc25400c635a13112f12dd08f88687087b90800631ad095eb5ad070e842), (0x852c307e, 0x31810998018c0798638018c6b427e27bc06302108820bd2102ec4ec4e75a137d6b5a26908), (0xc52c307e, 0x22057e91a09bd135a),
(0xd52c307e, 0x1102c41cd051e82875a141), (0xa52c307e, 0x18c084d400c603d432400c635a1108414540842d6850d02828), (0x862c307e, 0x18c0849c00c602d425c00c635a0031816848443c38c3e452c4e40293ad0a3eb5ad071e908), (0xc62c307e, 0x222ad690014dd066e832f5a),
(0xd62c307e, 0x2261e3a0e9d2b5a14f), (0xa62c307e, 0x18c084a400c602dc26400c635ad09687d8728a9a05ad68545029e8), (0xc65c307e, 0x25e27a24a4091409c8856455c554c6), (0xd65c307e, 0x4c502c2215f15d15b0a908b),
(0xe65c307e, 0x9f908126816711059458c84), (0xf65c307e, 0x39817140b7885b48416b169), (0xc50c407e, 0x113410e2ea2e7a), (0xa50c407e, 0x63030e30a2183c60421686045ff4217d17b1795005dc0210802c63182685ad0b420a1087),
(0xe50c407e, 0x44d043805a), (0xf50c407e, 0x35a089), (0x860c407e, 0x318c634323a37063f82c631818d308c3163126), (0xc60c407e, 0x3326197195193),
(0x960c407e, 0x18c630220d68d5886a7434fa08be0d2f058c630346342219f19d19b), (0xd60c407e, 0x833636636235e6), (0xa60c407e, 0xc63181b7308481b54280200b18c608210842108c6), (0xe60c407e, 0x37637236661084419d),
(0xb60c407e, 0x18c630220ea8df8e98e888421cf40bca0735039639238e01007140210b18c63181c31c1108837e210842108437a419319b), (0xf60c407e, 0x1df1dd20cd8cc8ed8ec80581d720844189), (0x861c407e, 0x18c0c184a8858c0843de3da3d63d23ce3ba39e3523738c1079478c841e120d49042), (0xc52c407e, 0xd0bf885a173d6b5a)]
def A419r7p2 : RecordPage := #[
(0xd52c407e, 0x686045ad6b5a), (0x862c407e, 0xc631818509110b181131810843d23ce3be3a2356376210f8884210d58884), (0xc62c407e, 0x3d63a661108410ca8864c42), (0xd62c407e, 0x3de3aa36e21af118421f3),
(0xa62c407e, 0x18c63030e1262163022087b46fc6b4421107d483e64), (0xc54c407e, 0x40), (0xd54c407e, 0x38216b5a), (0xc64c407e, 0x1c1087dc42),
(0xd64c407e, 0x1c1fd10fd887e442), (0xc65c407e, 0xd04b8080c8047fd46), (0xd65c407e, 0x8417a20920720517908b), (0xe65c407e, 0xd04c906eb5a),
(0xf65c407e, 0x10ae084c84222d6b441fa), (0xa50d407e, 0x3182111880cf1810888487c00c6084d0887486c8654021700b18c6344d0b42d0884), (0xa60d407e, 0xc6342462035c6044c60841088ac48229428044e016318c08821084222518b10884), (0xb60d407e, 0x318c6318210861090432822f008045b8c6302108422184210884),
(0x961d407e, 0x318c6042210847647242115908dc39c8d4047182108cc8423118b21042), (0x862d407e, 0x18c68494406f8c111939cc6044c604223b239118842084223f1108f484), (0xc54d407e, 0x3400739c), (0xd54d407e, 0x1c8380d120eb5a),
(0xc64d407e, 0xec1c1122921f39c), (0xd64d407e, 0x1c2491008923f39c), (0xc65d407e, 0x49f443e024fd1269259144), (0xd65d407e, 0x2129e839c94484324),
(0xe65d407e, 0x4a744422d12aeb5a), (0xf65d407e, 0x12ee096c84b22d6b44afa), (0x610c507e, 0x3182692672657630211318d493087092f806e30216318), (0xa40c507e, 0x6818c009bf1803002e136f0400009af18c6000008000080c),
(0xe40c507e, 0x3d030001a0), (0xa50c507e, 0x318101fe304eead0884ea42730138809af18c611a16b42d094a), (0xe50c507e, 0x12bd2b41c3a), (0xf50c507e, 0x1ad6b5a0c1)]
def A419r7p3 : RecordPage := #[
(0xa60c507e, 0xc631828127fc609f4c21209ed04e7c279e0b18c608210842108c6), (0xe60c507e, 0xa0c78dc610843524), (0xf60c507e, 0x1468f293291c5165120e60a1ca14421e118d), (0xc42c507e, 0x410304e00040),
(0xe42c507e, 0x200d28f), (0xc52c507e, 0x35a500a474ed6b5a), (0xd52c507e, 0x96e89dc5ad6b5a), (0xe52c507e, 0x341c3a),
(0xf52c507e, 0x29b299014be0a545a293), (0x862c507e, 0x318d0978810f18c6044ce546543c163021087ac79ca3484283108a7c421088228529d), (0xc62c507e, 0x7a486113398a744e11042), (0xd62c507e, 0xf6909f44e118422a5),
(0xa62c507e, 0x631a1311022e318c089a443de4208422ab2a92a72a529d), (0xe62c507e, 0x44d253a21a92ad), (0xf62c507e, 0x62b52b3073056221e12af285), (0xc54c507e, 0x1a00004d60),
(0xd54c507e, 0x11c04de0d15beb5a), (0xc65c507e, 0xa844427f133d063e8254ae5c4e66), (0xd65c507e, 0x2a3110a041c2c12bfd15e95db884), (0xe65c507e, 0x4d741922d161eb5a),
(0xf65c507e, 0x59258e2d6b458ba), (0xc40d507e, 0x682059a5960), (0xa40d507e, 0x111ae30225fe0805ab8c00b4c02e168f040000b3f18c60001000000810), (0xe40d507e, 0x12f8200),
(0xc50d507e, 0x38741b65b25afa), (0xa50d507e, 0xc60446f8c0b45e25de5da5d78c174973e8442e5217180b8405be5ba5b602cfc6318d2342d0b420cb0db), (0xe50d507e, 0x130e836c05e7a), (0xf50d507e, 0x35a0dd),
(0xc60d507e, 0x5f63525f23425ee5ea4), (0xd60d507e, 0xc4305d18183983012ff2fd193), (0xa60d507e, 0x6318c0898cc4cc4782c60c3cc3442209061682e3e184f058c630220842108c1c62c421931a1), (0xe60d507e, 0x3152332633051a110844624)]
def A419r7p4 : RecordPage := #[
(0xf60d507e, 0x6324217c88c5c441a3), (0xc42d507e, 0xf31b), (0xe42d507e, 0x5a622cb00040), (0xc52d507e, 0x6838c063ba),
(0xd52d507e, 0x1a0e531f), (0xe52d507e, 0x345cfa2d7d6b5a), (0xf52d507e, 0x1a2e93273250191e0c845ad6b5a), (0x862d507e, 0x318c6318113399a999f058c0844239110c42fb1084662232f32d32b329),
(0xc62d507e, 0x11d906ac99cc6522231337), (0xd62d507e, 0x2106b444339317), (0xa62d507e, 0x6318c6302269110c6484315108cec4210882317329), (0xe62d507e, 0x861a4d265222f511042),
(0xf62d507e, 0x430f31a099f839833d117e884219332b), (0xc54d507e, 0x1a2eb016a80059e0), (0xd54d507e, 0x1a2ed00099a1eb5a), (0xc65d507e, 0x333110c4745dfa3493473452e308b),
(0xd65d507e, 0xcd444313070d44d3cd34d2c84), (0xe65d507e, 0x345e22d1a9eb5a), (0xf65d507e, 0x1ac9abeb46aba), (0x850c327e, 0x6306e66e2036fc6000020db4dacda4d9cd94d8c631a16806c66c2035f35d35b),
(0xc50c327e, 0x2386b66ee6ebc), (0xa50c327e, 0x6307167120387c6000070e14e0f8038137f37d36318c08dec40000002701ce038037935b), (0xe50c327e, 0x8e1ad881c), (0xf50c327e, 0x39c35d),
(0x860c327e, 0x318c63872bc36318c68e4f40391501471e71aa), (0xc60c327e, 0x73aa39b399397), (0x960c327e, 0x18c630041d89d780eb78757c365c6318d1d4e8074e74a03a33a139f), (0xd60c327e, 0x1073e76e76a766a),
(0xa60c327e, 0xc63183bb500043b921b18c604000100000000014a), (0xe60c327e, 0x77e77a76ea000083a1), (0xb60c327e, 0x18c630041ec9e19eb9ea80003d321be90f44879e79a7978c6318c1e49e380023c51000000107860000000000782839739f), (0xf60c327e, 0x3e33e141cf9ce9ef9eee0f6c404000838d)]
def A419r7p5 : RecordPage := #[
(0x861c327e, 0x18c1c39b7e30000007e67e27de7da7d67c27a675a77b8c20fa4f9d083e541d6a000), (0xc52c327e, 0xe1c1801c375e739c), (0xd52c327e, 0x70e141ce739c), (0x862c327e, 0xc6318389371c60000231800007da7d67c67aa75e77e001fa800001d78108),
(0xc62c327e, 0x7de7aea0210801cc80e5c00), (0xd62c327e, 0x7e67b277603b3028003f7), (0xa62c327e, 0x18c6307166e78c0000400fc4f0cec400020fe507ee8), (0xc65c327e, 0xe1b588ffcff4fecc6),
(0xd65c327e, 0x1080fc40540340137d365), (0xe65c327e, 0xe1b6a04f39c), (0xf65c327e, 0xc2088903d081a0e738817c), (0xa50d327e, 0x318420fe30004900107506f1810908e0106505d054d8c630041300384e0380e0108),
(0xa60d327e, 0xc6388538c0012c08c610800109c0442521b18c6008460001000000042138f00108), (0xb60d327e, 0x318c63184210a000882a442dc631800008560000004280000108), (0x851d327e, 0x318421ca14a318d68004374354239ce210cd0c7181090842f4739ce239c), (0x961d327e, 0x318c6000421088a88684213a11050c71843f0134210f50843b38f42000),
(0x862d327e, 0x18c710e7180026a0fa318d6808c6000445443029084000044902111d08), (0xc65d327e, 0x10d78836244fe226a25a0c6), (0xd65d327e, 0x4229f10c5145082a8), (0xe65d327e, 0x10df883a0e22af39c),
(0xf65d327e, 0xc22e8916d08b20e7388afc), (0xc50c427e, 0x8c66c28c28be8), (0xd50c427e, 0x211a45a467465379), (0xa50c427e, 0x18c23ca3b811d7184734710010046f46d46b56318c685a0139ce001ce739c379361),
(0xe50c427e, 0x8f685e8d26c3ce0388), (0xf50c427e, 0x11f5084632739c363), (0x860c427e, 0xc6122521f18009090a636318c084211920c42481300c8fe6), (0xc60c427e, 0x124cc249148f48d48b),
(0x960c427e, 0x18c010c7184a54a30250a127d06cb8c6302108493a9360499497495), (0xd60c427e, 0x92a95695294e6), (0xa60c427e, 0x3184b34b1c60024af300084ad42b18c60421089ce701ce70c6), (0xe60c427e, 0x96e96a9566e739c497)]
def A419r7p6 : RecordPage := #[
(0xb60c427e, 0xc6008678c268a5ca67a6680004cb4235a1325098e98a9878c6318c260a5f8842108497a977ce112e79ce73800739c48b495), (0xf60c427e, 0x137536d25524d36535f09aa24d32701c47f), (0x861c427e, 0xc613a539d1d4dbf1810b9c4e54e34e1e26da65a50a5aa118c085ce26ff39ce250f000), (0x852c427e, 0x3180273e3001258a43e30217389e69e38c68000010047d4211ed3bd3b79c4ebe739c47084),
(0xc52c427e, 0x4238f09c45fe239c), (0xd52c427e, 0x211cc5ae232f0de79c4f5), (0xa52c427e, 0x18c013a7180092cd2271810b9c021084f920000e713dc89ea4), (0x862c427e, 0x18c010d7180091dcdaf1810b9cc604207137533528d2dd3fd3b449fbce27df39ce251f084),
(0xc62c427e, 0x99e6e7082501e246f122f9c), (0xd62c427e, 0x9a295fc4a7e1b9c503), (0xa62c427e, 0x18c010df180091e4db71810b9ce270a5ca52a83901ce714148a064), (0xc65c427e, 0x9c69e2872837122768143542d42546),
(0xd65c427e, 0x13948a2a051351150f46b365), (0xe65c427e, 0x279a106e6451b02146545d06), (0xf65c427e, 0x614945a2291814850851f51d), (0x610c527e, 0x31853152f52d663000295a50a949d6e30a4e01e006318),
(0xa30c527e, 0x7058c08917181380010843efa533d0318c6040000000004c), (0xe30c527e, 0x4f130001e2), (0xa50c527e, 0xc631853f53dc614ed400114e48a6f8c631a535d0100000000014a), (0xe50c527e, 0x1504f9d8a000075a8),
(0xf50c527e, 0x2a59f4a96a18a92a8f854516950c003e5391), (0xa60c527e, 0x318c6000a2aa26e010a9e8537c631812a6887dc9c07380e00c6), (0xe60c527e, 0x4dfe1b8943c), (0xf60c527e, 0x1ce739c481),
(0x852c527e, 0x318e271e300053c600a5eab2aaf8c6800000fbcfad52d085410015540000100543553), (0xc52c527e, 0xfb50a0297a954c0c02000), (0xd52c527e, 0x1f8a14ec0c0280055b), (0xa52c527e, 0x631c4e5c6000ab8c014c407e684000056155f55d55b553),
(0xe52c527e, 0xa62aa603ad563), (0xf52c527e, 0xa56b569c2b38b403e5565543), (0xc62c527e, 0x39c3095b78ce739c), (0xd62c527e, 0x270f15441ce739c)]
def A419r7p7 : RecordPage := #[
(0xe62c527e, 0x38943c), (0xf62c527e, 0x577575c2b9895c41c56f), (0xc65c527e, 0x139f890eaae0429ef0dbd5e58a6e6), (0xd65c527e, 0x13a789120e2bdf39c),
(0xe65c527e, 0x5590214fc5a583581e2bfabeb106), (0xf65c527e, 0xb12b0e0e738b0bc), (0xc30d527e, 0x78a0b165a62), (0xa30d527e, 0x21fe30052710fde818c08b2c0010843f3a58dd0318c60020000000050),
(0xe30d527e, 0x2938a02), (0xc50d527e, 0xb2a75ab2674ab22b1e8), (0xd50d527e, 0x14859fe2cee166c5a599597397), (0xa50d527e, 0x6318c014a56bd6b718d016ad6a4004008b4e45a5c6318d2d1e80040000001684e3c003973a5),
(0xe50d527e, 0x5b143d52959f3a500008768), (0xf50d527e, 0xb6a842c9816cc083a7), (0xc60d527e, 0x12878936b72b6fc), (0xa60d527e, 0xc6008838c038b96b938c1248feae3ae2f0085c342d2e318c097044b7eb7ab7621f9e1380e038048b49b),
(0xe60d527e, 0x295f126c4b9bc), (0xf60d527e, 0x39c49d), (0x852d527e, 0x318c63180297aedaece31a00008443021485950000bae05d55d35d15cf), (0xc52d527e, 0x222a0ebd4bd4b9e043b5dd),
(0xd52d527e, 0x420ec4085df5b3), (0xa52d527e, 0x6318c63005310216d5085b100178400001005b35cf), (0xe52d527e, 0x10b52a62b9e058f02000), (0xf52d527e, 0x85ab52f3af2e178c5a02cb80003975d1),
(0xc62d527e, 0x7128c4bd3c), (0xd62d527e, 0x1c4a55eb), (0xe62d527e, 0x38b8bc5b7e739c), (0xf62d527e, 0x1c5c75f35f1c2f7897b41ce739c),
(0xc65d527e, 0xe2e4aec810b5bc5f95f75f55a5365), (0xd65d527e, 0x38b960e2fdf39c), (0xe65d527e, 0x176c085af16980d8057fd7f508), (0xf65d527e, 0x304b03f38c0bc)]
def A419r7p8 : RecordPage := #[
(0xc30c437e, 0xb410a15e2ffa), (0xa30c437e, 0x630c2ac26c22c1e2349102be3021085cf4136c1ac1668ae00810c631810b42d0b5a16882085), (0xe30c437e, 0x84df410a2d689a), (0xc50c437e, 0x386be7068e3c),
(0xa50c437e, 0x630c42c3ec3ac3605f9c6000b3c45f00006eac32c2ebeacc631800010e038800380e038035f), (0xe50c437e, 0x2758386bfc4039c), (0x860c437e, 0x318c6389db8c631a139c6386e318998bf86c63183316e31a3698accc53a331399894cc466), (0xc60c437e, 0x63f3718f70c77a639637635633),
(0x960c437e, 0x318c6318657655653651e327f0d9718c634c9ba08b64b649647645643641), (0xd60c437e, 0xc82cbacb6cb26), (0xa60c437e, 0xc6318e277e318c684ed994ccc6a03308198c630265f1388821904410c6), (0xe60c437e, 0xcd2ccecba622104643),
(0xb60c437e, 0x318c61a459c5a3da35a2d9b5a25a1c0bea06850341b40b3fe318c630cfacf62345133c899dd9d59cc882338a19bd082219b48cd64633641), (0xf60c437e, 0x34db4cb20b1f81a5f0d2a269322104623), (0x861c437e, 0x6318c713c71810986cdc71860f09742176555f186ab6a9699687651667035381a9418c35186391a85a7c8469d23289108), (0xc61c437e, 0xd12a421006ad231b918cc86),
(0xd61c437e, 0x68b663232d90c46336af), (0xa61c437e, 0x18c631c4f3c604261d373c61844265086b56b366d65300318d6884421ac50d5e8), (0x862c437e, 0x6318c0018c684f587cdaf18613091213183332a16b36a969b68d6556696c1487c604d7e26bd121aedae5086b7432aa084), (0xc62c437e, 0xd1e6210826c3431aa18ccc6),
(0xd62c437e, 0x691665432ca0c86336c5), (0xa62c437e, 0x18c63000631a13f62136dc6185424c846b56ab671657e731810904211b1c8d8a4), (0xa10d437e, 0x18c63046c5e27ae302121abc00c63428242208c86c46c666e365f0de718c634d93a0a122084), (0xa30d437e, 0x318236893422bdc60421134146d9ed9a696e00802c6318d0b421685a16828444),
(0xa60d437e, 0x18c631c4f9c6084c60d3cafc846d7501b540cc6318136989c42108862541884), (0xb60d437e, 0x18c6318c1a896090843370b6f81b740db78c630234b136c9084210864319a191c84), (0xc61d437e, 0x71b7d4d5e06e52371b2390c4), (0xd61d437e, 0xe370b6b91b9d8948c664),
(0x862d437e, 0x6318c1384e73186d1236293183352a3311bbd22718137689bac48411ba484), (0xa50e437e, 0x318437aa38057fc6388ca00010de6de2bfacc631800040e0386f3c07000e0008), (0xa60e437e, 0x18c6318c6851508601581c61becc8401be40cc6318137b89c462721888220c6), (0xb60e437e, 0x18c630c06b078c382b81a1085017f40e038c63026ff137e918cc8c9644110442908)]
def A419r7p9 : RecordPage := #[
(0x861e437e, 0x6318c37aa3184691ad357a176d567185200e1a070b0630e121924221c1d08), (0xc62e437e, 0x169c0ccd8a27114387b25a0c6), (0xd62e437e, 0x2d382b7da1c4d89ccc668), (0x860f437e, 0x318c608422181d61f183572c721108038b8198c6302715138842110832084),
(0x960f437e, 0xc6318609589c60d64b24844200e3e071dc6318138d89c64842110842084), (0x610c537e, 0x18c630b9eaa78c29484392b28b919d7e30e421c6846318), (0xa10c537e, 0xc63185d1543c61084288c964633039480e5f18c634e4fa0cb4210a), (0xe10c537e, 0x421cb5cad08),
(0xa30c537e, 0x3187096a31126e3027683348e6241ff03978218c6302d0b5a16832c4a), (0xe30c537e, 0x147735733d2b41c7a), (0x250c537e, 0x6318c08449e4078c6318c3a4ba3ba2ba1e318c08c74452284372b56e318c0b5a14d421cad4e82e7fc73dc6318c600e7627390210a1da00b428737), (0x650c537e, 0x18c630e16d4b8c6852548429d3dd354ac63181399e9484395ab185d74224ba58000),
(0xa50c537e, 0x18c039c50dc631800040ba0021db00041ccf1d478a138c63000020000100000e5c0a), (0xe50c537e, 0x2ebaaaa249fa800a020075e0), (0x750c537e, 0x318c61c35a9f18d0148429d5dd554ac6318039ae8084396a800c6300753000000014038f), (0xa60c537e, 0x318c6318c634296eba66e3637e3adf142718c604eb221ff220862323918ccc6),
(0xe60c537e, 0x69f75574d5190ca24), (0xf60c537e, 0x350babba7914869d627), (0xc62c537e, 0xe86d524309d7d0a210c6), (0xd62c537e, 0x3a2b5591d750a41884),
(0xe62c537e, 0xe8e8651761), (0xf62c537e, 0xe920e61d9c4eca869d763), (0xa10d537e, 0x6318c2d9aade3086af41fbe31a14f4210a231390c0501dad471e056318c69da74a4210a), (0xc30d537e, 0x38f41b22265cfa),
(0xa30d537e, 0x630ee3a11048817f18116be83a48ede420503b68218c631a1685a169420d9), (0xe30d537e, 0x1c8741b3a), (0xc50d537e, 0x1584ebc07467b2b520), (0xa50d537e, 0x630eeae47c513c6000c2058f01d9f1dcf8a1f8c63000020002000001403a3),
(0xe50d537e, 0x5e172301d1a000), (0xc60d537e, 0xca2ef2c92d16eee4), (0xd60d537e, 0x47810730effa77d6e177b633), (0xa60d537e, 0x18c6318c3c8b92f14571825320b78f78d6e765be3c5f143f18c604f1227877857831102a08821189486633649)]
def A419r7p10 : RecordPage := #[
(0xe60d537e, 0x1c95e059244f264), (0xf60d537e, 0x477964b), (0xa21d537e, 0x18c630f22ca6eea7638c3b8872a10a42948), (0xc62d537e, 0x8caa2797795),
(0xd62d537e, 0x4657799), (0xe62d537e, 0x478d43bb9088633), (0xf62d537e, 0x478f0730f3a279b43bd9088633), (0xa50e537e, 0x3184231803008e3cff145f18c6000100000280040008),
(0xa60e537e, 0xc6318c6342a7c51bc60427a73211c7a5e28be318c09e8c4f42462321904410c6), (0xc62e537e, 0x6b32184f5687a9210c6), (0xd62e537e, 0xd6a47a743d6b119884), (0xe62e537e, 0x8653763),
(0xf62e537e, 0xe61ecc4f6287af761), (0x40f537e, 0x39c52510896c84c020034beabe9be8be78178c0ace2321114aa1084010040b5a461084210a43e6be5be4be381f140f86f82f7e27bd13ddbdcbdbe30f6b8c6118), (0x50f537e, 0x18c6302112e90ae318c630fcefcafc6fc38c6302323114ba10846318c0b5a421084210a43efbeef1f6f18c63181004fb278207d73e540108), (0x850f537e, 0x18c210a4039c521c631800040ce002cb9f28008471fa78a3b8c63000080001cb800040008),
(0x60f537e, 0x18c6318c004006bc6318c600bca0569c6318119288a640802318c605ad21084210a03faf1fcf18c604fe227ef66f7ed7eb6b742108), (0x860f537e, 0x6318c2140e7148f18c6044b222117ff7ed7fd6b742108e3fdf147718c604ff227f76432319910431108), (0x160f537e, 0x6318c63001001b718c631802f3815af18c60464e229b02008c631816b48421080101cc6318110442108421084), (0xc62f537e, 0xfc387cf1688d6e2801799),
(0xd62f537e, 0x7e3c3e88b447ed795), (0xe62f537e, 0x7e5c3e98b447fd44019088633), (0xf62f537e, 0x7e7c3ea8b447ff0731012280744029088643), (0x610c547e, 0x18c6318c19494e98c42407b2ac06a51e31016356426318),
(0xa10c547e, 0xc6318c60caca14842190c8e8633e409f122f18c605022219321086), (0xe10c547e, 0x21205e05484), (0x230c547e, 0x89e7ff8c6318c6318c400bcbbd5baf817a40adb8c63042388b61839c501c6318212054d047043a81f040e8206f18c6318111291890460e4819), (0x630c547e, 0x18c630dd6d7bc4fdc60c421a0ae0a4c60413f0d8c6304240a9b18331211fc128842),
(0xa30c547e, 0x18c0b5a15900800df8c63021118b84220caea0b742aa010218c63021088210864c46), (0xe30c547e, 0x19894f91f8f8884611043562), (0x730c547e, 0x318c61bb5aff82c60c421a0d60ccc60418f058c6304240b984210b18c0a0bc42108c218b), (0xa50c547e, 0x3186ef6c10226e300671235107283fbc6318141b8a00e039c07122c06)]
def A419r7p11 : RecordPage := #[
(0xe50c547e, 0x4fb831827e1b8947c), (0xa60c547e, 0x318c6318e27fe30f52a70f635041e80fef18c635077a155411042325918ccc6), (0xe60c547e, 0x6b98338293188caa8), (0xf60c547e, 0x35dc1ac1598c46b7625),
(0xa10d547e, 0x6318c63062e54a46c5e281e3041f321086431298dc841e1b18c6046141f9862c4621086), (0xc30d547e, 0xaac6ac433e3aa61a2), (0xa30d547e, 0x63108b017a15f1038e3022f510d7ea10f42b6010218c630211042108c219f), (0xe30d547e, 0x33b80b10cf9042),
(0xc50d547e, 0x128f89329a2b8bc), (0xa50d547e, 0x631097c0202e30007302dbf129d10928401c631814238a1c0701c070c0499), (0xe50d547e, 0x20378933c), (0xc60d547e, 0xcab09ac8ad22f1a8),
(0xd60d547e, 0x8853e428e213c5a7057fd633), (0xa60d547e, 0x18c6318c42fc07a29a03e31a161803777713659042e8216e16615c08038c631a855d0ad910441189c86633645), (0xe60d547e, 0x203e14d91410c28), (0xf60d547e, 0x884d647),
(0xa21d547e, 0x18c6310becaf09694b8c4228d69086218c4), (0xa30e547e, 0x3182131813844d431e858c0200b18c60421184220844), (0xa60e547e, 0xc6318e283e3000631a1677ad510808690433e318c6a19742c686234188421084), (0x30f547e, 0x22da07e318c6318c63100ef36f62eca05ed02b8e318c10842039c26318c1084210862439c38ea1bc020436e318c63037a286b1e120884),
(0x830f547e, 0x18c108620b5a16d00800f38c6302117e8f0884426a1d742d2010058c630210c9884220844), (0x40f547e, 0x8ba8222d685c402003dc04bcebd9bb3817bc0ae6233d115890842039c2088226084210862447c46c45c448221c110b107102287f143ec3dc3ce310ef8c6098), (0x60f547e, 0x18c6318c004007dc6318c600be20575c6318119f88acc1ce1318c60441108421086044c8225f18c60512ba89366b7af89169d21084), (0x860f547e, 0x6318c10c04590206e318c0b5a16f8057af77b69d21084044f8227718c635137a1696434319a08421084),
(0x160f547e, 0x6318c63001001ff18c631802f9815df18c60468222b507384c6318110442108402008c63181205a4210821084)]
def A419r7 : Records := #[A419r7p0, A419r7p1, A419r7p2, A419r7p3, A419r7p4, A419r7p5, A419r7p6, A419r7p7, A419r7p8, A419r7p9, A419r7p10, A419r7p11]
def testA419r7 : ℕ → Bool := testAt A419 bsA419 6 A419r6 A419r7 4 11
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c0 : checkBlock testA419r7 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c4 : checkBlock testA419r7 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c8 : checkBlock testA419r7 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c12 : checkBlock testA419r7 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c16 : checkBlock testA419r7 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c20 : checkBlock testA419r7 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c24 : checkBlock testA419r7 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c28 : checkBlock testA419r7 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c32 : checkBlock testA419r7 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c36 : checkBlock testA419r7 4 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c40 : checkBlock testA419r7 4 40 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c44 : checkBlock testA419r7 4 44 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c48 : checkBlock testA419r7 4 48 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c52 : checkBlock testA419r7 4 52 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c56 : checkBlock testA419r7 4 56 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c60 : checkBlock testA419r7 4 60 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c64 : checkBlock testA419r7 4 64 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c68 : checkBlock testA419r7 4 68 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c72 : checkBlock testA419r7 4 72 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c76 : checkBlock testA419r7 4 76 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c80 : checkBlock testA419r7 4 80 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c84 : checkBlock testA419r7 4 84 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c88 : checkBlock testA419r7 4 88 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c92 : checkBlock testA419r7 4 92 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c96 : checkBlock testA419r7 4 96 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c100 : checkBlock testA419r7 4 100 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c104 : checkBlock testA419r7 4 104 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c108 : checkBlock testA419r7 4 108 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c112 : checkBlock testA419r7 4 112 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c116 : checkBlock testA419r7 4 116 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c120 : checkBlock testA419r7 4 120 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c124 : checkBlock testA419r7 4 124 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c128 : checkBlock testA419r7 4 128 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c132 : checkBlock testA419r7 4 132 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c136 : checkBlock testA419r7 4 136 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c140 : checkBlock testA419r7 4 140 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c144 : checkBlock testA419r7 4 144 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c148 : checkBlock testA419r7 4 148 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c152 : checkBlock testA419r7 4 152 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c156 : checkBlock testA419r7 4 156 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c160 : checkBlock testA419r7 4 160 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c164 : checkBlock testA419r7 4 164 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c168 : checkBlock testA419r7 4 168 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c172 : checkBlock testA419r7 4 172 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c176 : checkBlock testA419r7 4 176 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c180 : checkBlock testA419r7 4 180 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c184 : checkBlock testA419r7 4 184 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c188 : checkBlock testA419r7 4 188 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c192 : checkBlock testA419r7 4 192 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c196 : checkBlock testA419r7 4 196 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c200 : checkBlock testA419r7 4 200 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c204 : checkBlock testA419r7 4 204 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c208 : checkBlock testA419r7 4 208 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c212 : checkBlock testA419r7 4 212 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c216 : checkBlock testA419r7 4 216 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c220 : checkBlock testA419r7 4 220 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c224 : checkBlock testA419r7 4 224 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c228 : checkBlock testA419r7 4 228 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c232 : checkBlock testA419r7 4 232 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c236 : checkBlock testA419r7 4 236 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c240 : checkBlock testA419r7 4 240 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c244 : checkBlock testA419r7 4 244 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c248 : checkBlock testA419r7 4 248 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c252 : checkBlock testA419r7 4 252 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c256 : checkBlock testA419r7 4 256 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c260 : checkBlock testA419r7 4 260 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c264 : checkBlock testA419r7 4 264 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c268 : checkBlock testA419r7 4 268 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c272 : checkBlock testA419r7 4 272 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c276 : checkBlock testA419r7 4 276 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c280 : checkBlock testA419r7 4 280 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c284 : checkBlock testA419r7 4 284 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c288 : checkBlock testA419r7 4 288 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c292 : checkBlock testA419r7 4 292 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c296 : checkBlock testA419r7 4 296 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c300 : checkBlock testA419r7 4 300 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c304 : checkBlock testA419r7 4 304 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c308 : checkBlock testA419r7 4 308 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c312 : checkBlock testA419r7 4 312 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c316 : checkBlock testA419r7 4 316 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c320 : checkBlock testA419r7 4 320 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c324 : checkBlock testA419r7 4 324 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c328 : checkBlock testA419r7 4 328 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c332 : checkBlock testA419r7 4 332 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c336 : checkBlock testA419r7 4 336 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c340 : checkBlock testA419r7 4 340 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c344 : checkBlock testA419r7 4 344 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c348 : checkBlock testA419r7 4 348 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c352 : checkBlock testA419r7 4 352 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c356 : checkBlock testA419r7 4 356 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c360 : checkBlock testA419r7 4 360 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c364 : checkBlock testA419r7 4 364 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c368 : checkBlock testA419r7 4 368 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c372 : checkBlock testA419r7 4 372 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r7c376 : checkBlock testA419r7 1 376 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA419r7 : LayerOK A419 7 A419r7 := by
  apply layer_of_block (bs := bsA419) (k := 6) (old := A419r6) (cw := 4) (rw := 11) (by decide +kernel) vbsA419 vA419r6
  exact @block_merge testA419r7 0 377 7 (@block_merge testA419r7 0 188 189 (@block_merge testA419r7 0 92 96 (@block_merge testA419r7 0 44 48 (@block_merge testA419r7 0 20 24 (@block_merge testA419r7 0 8 12 (@block_merge testA419r7 0 4 4 A419r7c0 A419r7c4) (@block_merge testA419r7 8 4 8 A419r7c8 (@block_merge testA419r7 12 4 4 A419r7c12 A419r7c16))) (@block_merge testA419r7 20 12 12 (@block_merge testA419r7 20 4 8 A419r7c20 (@block_merge testA419r7 24 4 4 A419r7c24 A419r7c28)) (@block_merge testA419r7 32 4 8 A419r7c32 (@block_merge testA419r7 36 4 4 A419r7c36 A419r7c40)))) (@block_merge testA419r7 44 24 24 (@block_merge testA419r7 44 12 12 (@block_merge testA419r7 44 4 8 A419r7c44 (@block_merge testA419r7 48 4 4 A419r7c48 A419r7c52)) (@block_merge testA419r7 56 4 8 A419r7c56 (@block_merge testA419r7 60 4 4 A419r7c60 A419r7c64))) (@block_merge testA419r7 68 12 12 (@block_merge testA419r7 68 4 8 A419r7c68 (@block_merge testA419r7 72 4 4 A419r7c72 A419r7c76)) (@block_merge testA419r7 80 4 8 A419r7c80 (@block_merge testA419r7 84 4 4 A419r7c84 A419r7c88))))) (@block_merge testA419r7 92 48 48 (@block_merge testA419r7 92 24 24 (@block_merge testA419r7 92 12 12 (@block_merge testA419r7 92 4 8 A419r7c92 (@block_merge testA419r7 96 4 4 A419r7c96 A419r7c100)) (@block_merge testA419r7 104 4 8 A419r7c104 (@block_merge testA419r7 108 4 4 A419r7c108 A419r7c112))) (@block_merge testA419r7 116 12 12 (@block_merge testA419r7 116 4 8 A419r7c116 (@block_merge testA419r7 120 4 4 A419r7c120 A419r7c124)) (@block_merge testA419r7 128 4 8 A419r7c128 (@block_merge testA419r7 132 4 4 A419r7c132 A419r7c136)))) (@block_merge testA419r7 140 24 24 (@block_merge testA419r7 140 12 12 (@block_merge testA419r7 140 4 8 A419r7c140 (@block_merge testA419r7 144 4 4 A419r7c144 A419r7c148)) (@block_merge testA419r7 152 4 8 A419r7c152 (@block_merge testA419r7 156 4 4 A419r7c156 A419r7c160))) (@block_merge testA419r7 164 12 12 (@block_merge testA419r7 164 4 8 A419r7c164 (@block_merge testA419r7 168 4 4 A419r7c168 A419r7c172)) (@block_merge testA419r7 176 4 8 A419r7c176 (@block_merge testA419r7 180 4 4 A419r7c180 A419r7c184)))))) (@block_merge testA419r7 188 96 93 (@block_merge testA419r7 188 48 48 (@block_merge testA419r7 188 24 24 (@block_merge testA419r7 188 12 12 (@block_merge testA419r7 188 4 8 A419r7c188 (@block_merge testA419r7 192 4 4 A419r7c192 A419r7c196)) (@block_merge testA419r7 200 4 8 A419r7c200 (@block_merge testA419r7 204 4 4 A419r7c204 A419r7c208))) (@block_merge testA419r7 212 12 12 (@block_merge testA419r7 212 4 8 A419r7c212 (@block_merge testA419r7 216 4 4 A419r7c216 A419r7c220)) (@block_merge testA419r7 224 4 8 A419r7c224 (@block_merge testA419r7 228 4 4 A419r7c228 A419r7c232)))) (@block_merge testA419r7 236 24 24 (@block_merge testA419r7 236 12 12 (@block_merge testA419r7 236 4 8 A419r7c236 (@block_merge testA419r7 240 4 4 A419r7c240 A419r7c244)) (@block_merge testA419r7 248 4 8 A419r7c248 (@block_merge testA419r7 252 4 4 A419r7c252 A419r7c256))) (@block_merge testA419r7 260 12 12 (@block_merge testA419r7 260 4 8 A419r7c260 (@block_merge testA419r7 264 4 4 A419r7c264 A419r7c268)) (@block_merge testA419r7 272 4 8 A419r7c272 (@block_merge testA419r7 276 4 4 A419r7c276 A419r7c280))))) (@block_merge testA419r7 284 48 45 (@block_merge testA419r7 284 24 24 (@block_merge testA419r7 284 12 12 (@block_merge testA419r7 284 4 8 A419r7c284 (@block_merge testA419r7 288 4 4 A419r7c288 A419r7c292)) (@block_merge testA419r7 296 4 8 A419r7c296 (@block_merge testA419r7 300 4 4 A419r7c300 A419r7c304))) (@block_merge testA419r7 308 12 12 (@block_merge testA419r7 308 4 8 A419r7c308 (@block_merge testA419r7 312 4 4 A419r7c312 A419r7c316)) (@block_merge testA419r7 320 4 8 A419r7c320 (@block_merge testA419r7 324 4 4 A419r7c324 A419r7c328)))) (@block_merge testA419r7 332 24 21 (@block_merge testA419r7 332 12 12 (@block_merge testA419r7 332 4 8 A419r7c332 (@block_merge testA419r7 336 4 4 A419r7c336 A419r7c340)) (@block_merge testA419r7 344 4 8 A419r7c344 (@block_merge testA419r7 348 4 4 A419r7c348 A419r7c352))) (@block_merge testA419r7 356 12 9 (@block_merge testA419r7 356 4 8 A419r7c356 (@block_merge testA419r7 360 4 4 A419r7c360 A419r7c364)) (@block_merge testA419r7 368 4 5 A419r7c368 (@block_merge testA419r7 372 4 1 A419r7c372 A419r7c376))))))) (show checkBlock testA419r7 7 377 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A419r8p0 : RecordPage := #[
(0xc207e, 0x561484e128461083e0e8360c82e0ae318c6318c6318c0000000130739c008000001106318c63021084203c421080d1035ad0018c6318c00000080002c0901c05800700045c10b9c1081a0035a00318c6318c600010000), (0xc307e, 0xc6308be2e80000039c06318c6318c6318c630840b62c8ae2aa10298a22789a000018c63021084212c42108491000000018c6318c6b5ad6b5a11c4510c410fc3d0ec390dc81a86618902f0b4000000000318c6318c635ad6b5a), (0xc407e, 0x4c92e4a9260012247800469178c6318c6318c6318c1084490e42906421023f839c16318c08421087d16b4200802c6318c60421084220f63c8ee3a8e6388de368d7a1a467d68650b41c10b9c10b18c6318c604210844), (0xd407e, 0x2ccb12bcad000ab2a40029ca5c6318c6318c6318c608421085190842039c16318c08421142216b5a109201080203718c6318108421088427c84e90842134426f5a2100017000e7318c6318c604210844),
(0xc507e, 0x1d2739ca71839c1000709bf8c6318c6318c6318c1ba6d9b26b9aa699a26799a6580c9018f8c6302108421f45ad6842580420080fc6318c6042108422d4c5218660b88e1b4bfd17a5deb4e0e4002e4b7001c00e318c6318c0842108b5), (0xd507e, 0x92a4690a3e0e7040023a8de318c6318c6318c6308ca2e8aa2688a1e86a1684a0e0414081e318c08421142216b4200802c6318c6042108422d50121fe7e9f643e4713df47a9e7ad1e21e800779da001d601e318c6318c0842108b5), (0xc327e, 0xaaaa6a8a9f8c6318c630212366f884529178c6318c210a6a96a4a8e8428aa1e318c035a000000014107380c6318c60000000000000427e9ea769ca6e9aa6698a5fc4b52be712949f18c6318c601a0035a0000000008), (0xd327e, 0x5a56759563c6318c63181091d3844229c8dc6318c61084210b0a10846318c035a0000002be00739c02bb8c6318c000000011000000010856d0aca1084238855f9c42318c6318c600006800d680000008),
(0xc427e, 0x33acdb32cbe318c6318c08421035a06318c6304232ac9b22c7908c6b16c4b0f8c63021084000000614000015d06318c6300000001739ce739c60d815fd7d5ed795dd755cd0b8adeb6a16b49f18c6318c60421084210b9ce739c), (0xc527e, 0x396e4b8ee2e318c6318c0845491e0d6818c6318c386e0b7edeb76dcb6edab66d8e318c0903118e0e7380614000000a0e318c63000000004c000000067dafe35ad5f38c5d5a9434ed2b10c4c718c6318c604268da110980080000019f), (0xd527e, 0xffbfafdbf38c6318c6302115648835a06318c630fbbeaf9be2f7bdaf5bd2f3bcb8c6302414464839c0000002be0c6318c6000000000000067de3e3c2eff38eeaf2eda1d975dd543a69ae318c6318c084e8b9e2139a0180000019f), (0xc437e, 0x1f971718c6318c63181091f38c02002b8c6318c10915c5313c4a0e738c4b0f8c6318c08441087f422238861f874004000a1e318c6302d6b42789a4221082121b86617856138460f8341c82e09e720749f18c6318c605a81603d6a010b50841084),
(0xd437e, 0x1fb71f18c6318c63181092139402002f8c6318c1084212390739c231b8c6318c084410888446f1a810051718c605ad0a2421088210919923121084000802709c0039cc6318c6318168917eb4421084245a4), (0xe437e, 0x1fd72718c6318c63181092339c0200338c6318c10922c860e718bc6318110440a108422410010002318c631816b5a40a642108842111fa23d4210807111df38846318c6318c084812348d085ad222d41084), (0xf437e, 0x1ff72f18c6318c6318109253a40200378c6318c10842039c26318c0882221084010046318c0b5a4108421088210842492491c00e700027318c6318c6042d68422688421104), (0xc537e, 0x1ce32f8c6318c6318c0845692601001dc6318c626b9a6679940f3bca06cdb1c6318c6048388cb422418d61f874085840a4a8f8c6318c0b5ad0ae2aa1484224f92e6324c32fa88a8340097412dcb32bcaa002931c6318c631816a539475a507284224f9364b),
(0xd537e, 0x39c66718c6318c6318108af25402003f8c6318c51b45d134381ed7ac0dcb6f8c6318c090b119e8446f10810052f18c605ad0b2842285449f25d064a067f9f493dc22004f33b8013aa6b8c6318c6302d4e738eb53787a84224f9b64b), (0xe537e, 0x738cde318c6318c630211624b804008718c6318a6697a569303d206d718c6048488cd42108444604200853718c631816b5a40b6842285421082229141108001147800846318c6318c0848d085ad226d42108), (0xf537e, 0x738cee318c6318c630211664c804008f18c6318ab6abaa6a703de06ef18c6048688d14210802008c631816b48421084290822108222a545468a84004200040114fa29dc6318c6318c6114d885ad084812348d224d42108), (0xc547e, 0x58d4fc6318c6318c605ad0ba010025c6318c62a7a1e939940f881bdc6318c60488a1e2354d32123990e278941ce719163f18c6318110a3110a4190c4212b3abec7458b6199068341cb06bfe70cbae318c6318c0855e8abbae6b7ad44230da4212b3ac6af),
(0xd547e, 0xb2aa38c6318c6318c0b5a17c02004f8c6318c55745d2f3481f503838c6318c091745446d9b24248b14839c64f18c6044110e4212e1256757dbe8b76dbb6516bc220e5ab69f3968af38c6318c6302159f66885658e24212b3b26af), (0xe547e, 0x16754f18c6318c631816b43080400a718c6318aa689a566703e606ff18c6048988d72108424560e738465718c63181108221124212e121084412e5210840009c0039cc6318c63181089718844212c921084), (0xf547e, 0x16955718c6318c631816b43180400af18c6318ab68da666b03ee070f18c6048c88dd2108407384c631811044210842188421084412f125de4bb400e70002009c27318c6318c631825d621108211044ba497392b121084)]
def A419r8 : Records := #[A419r8p0]
def testA419r8 : ℕ → Bool := testAt A419 bsA419 7 A419r7 A419r8 4 9
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r8c0 : checkBlock testA419r8 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r8c2 : checkBlock testA419r8 2 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r8c4 : checkBlock testA419r8 2 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r8c6 : checkBlock testA419r8 2 6 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r8c8 : checkBlock testA419r8 2 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r8c10 : checkBlock testA419r8 2 10 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r8c12 : checkBlock testA419r8 2 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r8c14 : checkBlock testA419r8 2 14 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r8c16 : checkBlock testA419r8 2 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r8c18 : checkBlock testA419r8 2 18 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r8c20 : checkBlock testA419r8 2 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r8c22 : checkBlock testA419r8 1 22 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA419r8 : LayerOK A419 8 A419r8 := by
  apply layer_of_block (bs := bsA419) (k := 7) (old := A419r7) (cw := 4) (rw := 9) (by decide +kernel) vbsA419 vA419r7
  exact @block_merge testA419r8 0 23 9 (@block_merge testA419r8 0 12 11 (@block_merge testA419r8 0 6 6 (@block_merge testA419r8 0 2 4 A419r8c0 (@block_merge testA419r8 2 2 2 A419r8c2 A419r8c4)) (@block_merge testA419r8 6 2 4 A419r8c6 (@block_merge testA419r8 8 2 2 A419r8c8 A419r8c10))) (@block_merge testA419r8 12 6 5 (@block_merge testA419r8 12 2 4 A419r8c12 (@block_merge testA419r8 14 2 2 A419r8c14 A419r8c16)) (@block_merge testA419r8 18 2 3 A419r8c18 (@block_merge testA419r8 20 2 1 A419r8c20 A419r8c22)))) (show checkBlock testA419r8 9 23 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A419r9p0 : RecordPage := #[
(0x7e, 0x5b5d33cb1c2fbadb2b800aa60e711000f3718c6318c6318c6318c6318108b24421c516b4180400718c6318)]
def A419r9 : Records := #[A419r9p0]
def testA419r9 : ℕ → Bool := testAt A419 bsA419 8 A419r8 A419r9 4 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A419r9c0 : checkBlock testA419r9 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA419r9 : LayerOK A419 9 A419r9 := by
  apply layer_of_block (bs := bsA419) (k := 8) (old := A419r8) (cw := 4) (rw := 5) (by decide +kernel) vbsA419 vA419r8
  exact @block_merge testA419r9 0 1 31 A419r9c0 (show checkBlock testA419r9 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA419 : Valid A419 := by
  apply bound_of_layers (bs := bsA419) (last := A419r9) (cw := 4) (rw := 0) (by decide +kernel) vbsA419 vA419r9 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A420 : Bound := ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, [0x0, 0x5050505050505050505050505050505, 0x3030303030303030303030303030303, 0xf000f000f000f000f000f000f000f, 0xf0f00000f0f00000f0f00000f0f, 0xf0f0f0f000000000f0f0f0f, 0xf0f0f0f0f0f0f0f], 0x1000100010103050f, 10⟩
def bsA420 : Array Bound := [A309, A394, A399, A400, A402, A407].toArray
theorem vbsA420 : ∀ s ∈ bsA420, Valid s := by
  intro s hs
  simp only [bsA420,List.mem_toArray] at hs
  exact (familyCons vA309 <| familyCons vA394 <| familyCons vA399 <| familyCons vA400 <| familyCons vA402 <| familyCons vA407 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A420r6p0 : RecordPage := #[
(0x610860c207e, 0x6), (0x620860c207e, 0x6), (0x630860c207e, 0x6), (0x230c60c207e, 0x6),
(0x240c60c207e, 0x6), (0x32e60c207e, 0x4), (0x42e60c207e, 0x0), (0x630861c207e, 0x40),
(0x31861c207e, 0x666688aa66002066222400004), (0x630862c207e, 0x4), (0x230c40c507e, 0x6), (0x240c40c507e, 0x6),
(0x42e40c507e, 0x2), (0x630842c507e, 0x2), (0x230c30c527e, 0x6), (0x240c30c527e, 0x6)]
def A420r6 : Records := #[A420r6p0]
def testA420r6 : ℕ → Bool := testAt A420 bsA420 5 (#[] : Records) A420r6 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A420r6c0 : checkBlock testA420r6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A420r6c4 : checkBlock testA420r6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A420r6c8 : checkBlock testA420r6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A420r6c12 : checkBlock testA420r6 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA420r6 : LayerOK A420 6 A420r6 := by
  apply layer_of_block (bs := bsA420) (k := 5) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsA420 (emptyOK _ _)
  exact @block_merge testA420r6 0 16 16 (@block_merge testA420r6 0 8 8 (@block_merge testA420r6 0 4 4 A420r6c0 A420r6c4) (@block_merge testA420r6 8 4 4 A420r6c8 A420r6c12)) (show checkBlock testA420r6 16 16 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A420r7p0 : RecordPage := #[
(0x860c207e, 0x333333333333444455550150641), (0xc60c207e, 0x105272), (0xa60c207e, 0xcccccc0048cccd111155540000400041), (0xe60c207e, 0x3564104002),
(0x861c207e, 0x333333445502330001448896cc000f00002024), (0x862c207e, 0x33333344550033112144889acc889342222400), (0xc40c507e, 0x16f50), (0xa40c507e, 0xcccccccd540408cccd111155540004000405),
(0xe40c507e, 0x65e0504020), (0x842c507e, 0x3333445533113344550020440032cc89b40000402), (0xc30c527e, 0x20ffd4), (0xa30c527e, 0xcccccccd544400cccd111155544000000083),
(0xe30c527e, 0x6e68300024)]
def A420r7 : Records := #[A420r7p0]
def testA420r7 : ℕ → Bool := testAt A420 bsA420 6 A420r6 A420r7 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A420r7c0 : checkBlock testA420r7 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A420r7c4 : checkBlock testA420r7 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A420r7c8 : checkBlock testA420r7 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A420r7c12 : checkBlock testA420r7 1 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA420r7 : LayerOK A420 7 A420r7 := by
  apply layer_of_block (bs := bsA420) (k := 6) (old := A420r6) (cw := 3) (rw := 4) (by decide +kernel) vbsA420 vA420r6
  exact @block_merge testA420r7 0 13 19 (@block_merge testA420r7 0 8 5 (@block_merge testA420r7 0 4 4 A420r7c0 A420r7c4) (@block_merge testA420r7 8 4 1 A420r7c8 A420r7c12)) (show checkBlock testA420r7 19 13 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A420r8p0 : RecordPage := #[
(0xc207e, 0x1999a222199999aaaa9999a2220000016cccccd111155544884896666668888aaaa000004002239488616666666688888888aaaaaaaa004000), (0xc507e, 0x1999999999a2221999a2222aaa999999a22200880a75554cccccd111110088089aaaaaa22224226666666688888888008bc01a1aaaaaaaa224222), (0xc527e, 0x1999999999a2221999a2222aaa999999a2222aaa88888a6cccccd11111155555400000b00000026666666688888888aaaaaaaa44cdd12a1000002)]
def A420r8 : Records := #[A420r8p0]
def testA420r8 : ℕ → Bool := testAt A420 bsA420 7 A420r7 A420r8 3 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A420r8c0 : checkBlock testA420r8 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A420r8c2 : checkBlock testA420r8 1 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA420r8 : LayerOK A420 8 A420r8 := by
  apply layer_of_block (bs := bsA420) (k := 7) (old := A420r7) (cw := 3) (rw := 4) (by decide +kernel) vbsA420 vA420r7
  exact @block_merge testA420r8 0 3 29 (@block_merge testA420r8 0 2 1 A420r8c0 A420r8c2) (show checkBlock testA420r8 29 3 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A420r9p0 : RecordPage := #[
(0x7e, 0xcccd1110cccccc0055999a2222aaa9999a2222aaa8909b33344440201aaaa)]
def A420r9 : Records := #[A420r9p0]
def testA420r9 : ℕ → Bool := testAt A420 bsA420 8 A420r8 A420r9 3 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A420r9c0 : checkBlock testA420r9 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA420r9 : LayerOK A420 9 A420r9 := by
  apply layer_of_block (bs := bsA420) (k := 8) (old := A420r8) (cw := 3) (rw := 2) (by decide +kernel) vbsA420 vA420r8
  exact @block_merge testA420r9 0 1 31 A420r9c0 (show checkBlock testA420r9 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA420 : Valid A420 := by
  apply bound_of_layers (bs := bsA420) (last := A420r9) (cw := 3) (rw := 0) (by decide +kernel) vbsA420 vA420r9 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A421 : Bound := ⟨0x33333333333333333333333333333333, [0x0, 0x11111111111111111111111111111111, 0x3030303030303030303030303030303, 0x330033003300330033003300330033, 0x3333000033330000333300003333, 0x333333330000000033333333, 0x3333333333333333], 0x10001001101031133, 10⟩
def bsA421 : Array Bound := [A401, A403, A404, A407, A408].toArray
theorem vbsA421 : ∀ s ∈ bsA421, Valid s := by
  intro s hs
  simp only [bsA421,List.mem_toArray] at hs
  exact (familyCons vA401 <| familyCons vA403 <| familyCons vA404 <| familyCons vA407 <| familyCons vA408 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def A421r9p0 : RecordPage := #[
(0x7e, 0x22220000444400002222666600002222444488880000222244446666)]
def A421r9 : Records := #[A421r9p0]
def testA421r9 : ℕ → Bool := testAt A421 bsA421 8 (#[] : Records) A421r9 3 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem A421r9c0 : checkBlock testA421r9 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA421r9 : LayerOK A421 9 A421r9 := by
  apply layer_of_block (bs := bsA421) (k := 8) (old := (#[] : Records)) (cw := 3) (rw := 1) (by decide +kernel) vbsA421 (emptyOK _ _)
  exact @block_merge testA421r9 0 1 31 A421r9c0 (show checkBlock testA421r9 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA421 : Valid A421 := by
  apply bound_of_layers (bs := bsA421) (last := A421r9) (cw := 3) (rw := 0) (by decide +kernel) vbsA421 vA421r9 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def A422 : Bound := ⟨0x55555555555555555555555555555555, [0x0, 0x11111111111111111111111111111111, 0x5050505050505050505050505050505, 0x550055005500550055005500550055, 0x5555000055550000555500005555, 0x555555550000000055555555, 0x5555555555555555], 0x10001001101015555, 10⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vA422 : Valid A422 := by
  apply transfer vA419 0xfdebe78edcba7000000000000000bd6ae58ad4aa5000000000000000ddab668cd8b260000000000000009d2a6488d0a240000000000000007ce9e386cc9a30000000000000003c68e182c48a10000000000000005ca96284c89220000000000000001c286080c08200 <;> decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.SignedCert.GraphA
def bsrootA : Array Bound := [A400, A401, A402, A403, A407, A416, A417, A418, A419, A420, A421, A422].toArray
theorem vbsrootA : ∀ s ∈ bsrootA, Valid s := by
  intro s hs
  simp only [bsrootA,List.mem_toArray] at hs
  exact (familyCons vA400 <| familyCons vA401 <| familyCons vA402 <| familyCons vA403 <| familyCons vA407 <| familyCons vA416 <| familyCons vA417 <| familyCons vA418 <| familyCons vA419 <| familyCons vA420 <| familyCons vA421 <| familyCons vA422 <| familyNil) s hs
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def rootAr5p0 : RecordPage := #[
(0x32061510060f70c54fe, 0x0), (0x42061510060f70c54fe, 0x0)]
def rootAr5 : Records := #[rootAr5p0]
def testrootAr5 : ℕ → Bool := testAt rootA bsrootA 4 (#[] : Records) rootAr5 4 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr5c0 : checkBlock testrootAr5 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootAr5 : LayerOK rootA 5 rootAr5 := by
  apply layer_of_block (bs := bsrootA) (k := 4) (old := (#[] : Records)) (cw := 4) (rw := 1) (by decide +kernel) vbsrootA (emptyOK _ _)
  exact @block_merge testrootAr5 0 2 30 rootAr5c0 (show checkBlock testrootAr5 30 2 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def rootAr6p0 : RecordPage := #[
(0x61c10250870c54fe, 0x0), (0x31420650870c54fe, 0x0), (0x41420650870c54fe, 0x0), (0x61420650870c54fe, 0x14),
(0x61430650870c54fe, 0x288), (0x50721230c70c54fe, 0x0), (0x50332630c70c54fe, 0x0), (0x50721240c70c54fe, 0x0),
(0x50332640c70c54fe, 0x0), (0x61430260c70c54fe, 0x14), (0x10332660c70c54fe, 0x0), (0x120332660c70c54fe, 0x0),
(0x120332670c70c54fe, 0x0), (0x60332670c70c54fe, 0x0), (0x440110321c70c54fe, 0x0), (0x450110321c70c54fe, 0x0),
(0x450050321c70c54fe, 0x182), (0x450250210d70c54fe, 0x0), (0x261650210d70c54fe, 0x0), (0x220510050f70c54fe, 0x0),
(0x42510050f70c54fe, 0x0), (0x43430050f70c54fe, 0x0), (0x630042050f70c54fe, 0x0), (0x220510060f70c54fe, 0x0),
(0x61510060f70c54fe, 0xd), (0x32510060f70c54fe, 0x1), (0x42510060f70c54fe, 0x3), (0x43460060f70c54fe, 0x31),
(0x53460060f70c54fe, 0xb), (0x630032060f70c54fe, 0x12), (0x650032060f70c54fe, 0x0), (0x630042060f70c54fe, 0x0)]
def rootAr6p1 : RecordPage := #[
(0x220510070f70c54fe, 0x0), (0x32510070f70c54fe, 0x0), (0x610032070f70c54fe, 0x0), (0x630032070f70c54fe, 0x12),
(0x220510080f70c54fe, 0x0), (0x42510080f70c54fe, 0x0), (0x43430080f70c54fe, 0x0), (0x630042080f70c54fe, 0x0),
(0x41430260c70c64fe, 0x0), (0x61430260c70c64fe, 0x0), (0x61440260c70c64fe, 0x0), (0x41430270c70c64fe, 0x0),
(0x41430260c70c65fe, 0x0), (0x61440260c70c65fe, 0x14)]
def rootAr6 : Records := #[rootAr6p0, rootAr6p1]
def testrootAr6 : ℕ → Bool := testAt rootA bsrootA 5 rootAr5 rootAr6 4 1
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr6c0 : checkBlock testrootAr6 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr6c4 : checkBlock testrootAr6 4 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr6c8 : checkBlock testrootAr6 4 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr6c12 : checkBlock testrootAr6 4 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr6c16 : checkBlock testrootAr6 4 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr6c20 : checkBlock testrootAr6 4 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr6c24 : checkBlock testrootAr6 4 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr6c28 : checkBlock testrootAr6 4 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr6c32 : checkBlock testrootAr6 4 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr6c36 : checkBlock testrootAr6 4 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr6c40 : checkBlock testrootAr6 4 40 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr6c44 : checkBlock testrootAr6 2 44 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootAr6 : LayerOK rootA 6 rootAr6 := by
  apply layer_of_block (bs := bsrootA) (k := 5) (old := rootAr5) (cw := 4) (rw := 1) (by decide +kernel) vbsrootA vrootAr5
  exact @block_merge testrootAr6 0 46 18 (@block_merge testrootAr6 0 24 22 (@block_merge testrootAr6 0 12 12 (@block_merge testrootAr6 0 4 8 rootAr6c0 (@block_merge testrootAr6 4 4 4 rootAr6c4 rootAr6c8)) (@block_merge testrootAr6 12 4 8 rootAr6c12 (@block_merge testrootAr6 16 4 4 rootAr6c16 rootAr6c20))) (@block_merge testrootAr6 24 12 10 (@block_merge testrootAr6 24 4 8 rootAr6c24 (@block_merge testrootAr6 28 4 4 rootAr6c28 rootAr6c32)) (@block_merge testrootAr6 36 4 6 rootAr6c36 (@block_merge testrootAr6 40 4 2 rootAr6c40 rootAr6c44)))) (show checkBlock testrootAr6 18 46 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def rootAr7p0 : RecordPage := #[
(0x621610870c54fe, 0x0), (0x631610870c54fe, 0x0), (0x651610870c54fe, 0x10), (0x661610870c54fe, 0x10),
(0x610a10870c54fe, 0x10), (0x231e10870c54fe, 0x0), (0x241e10870c54fe, 0x0), (0x261e10870c54fe, 0x0),
(0x271e10870c54fe, 0x0), (0x631620870c54fe, 0x0), (0x651620870c54fe, 0x10), (0x661620870c54fe, 0x10),
(0x651630870c54fe, 0x10), (0x661630870c54fe, 0x10), (0xc10250870c54fe, 0x1), (0x450250870c54fe, 0x210b5a94a3a80652),
(0x420650870c54fe, 0x385074), (0x430650870c54fe, 0x9074), (0x440650870c54fe, 0xb4), (0x460650870c54fe, 0x14121e88),
(0x261650870c54fe, 0x252), (0x661650870c54fe, 0x292), (0xc10260870c54fe, 0x1cc), (0x440660870c54fe, 0x12),
(0x231620c70c54fe, 0x0), (0x241620c70c54fe, 0x0), (0x31a20c70c54fe, 0x0), (0x41a20c70c54fe, 0x0),
(0x721230c70c54fe, 0xb), (0x241630c70c54fe, 0x0), (0x261630c70c54fe, 0x10), (0x271630c70c54fe, 0x10)]
def rootAr7p1 : RecordPage := #[
(0x332630c70c54fe, 0xd), (0x721240c70c54fe, 0xf), (0x261640c70c54fe, 0x10), (0x271640c70c54fe, 0x10),
(0x332640c70c54fe, 0x11), (0x430260c70c54fe, 0x274), (0x440260c70c54fe, 0x14), (0x460260c70c54fe, 0x284e94),
(0x271660c70c54fe, 0x0), (0x332660c70c54fe, 0xb95), (0x440270c70c54fe, 0x252), (0x332670c70c54fe, 0xd99),
(0x110321c70c54fe, 0x25491fa1d), (0x910321c70c54fe, 0x48cd0b95), (0x50321c70c54fe, 0x91b61170d921619c2a15), (0x120721c70c54fe, 0x0),
(0x60721c70c54fe, 0xf16a), (0x620210d70c54fe, 0x10), (0x630210d70c54fe, 0x10), (0x250210d70c54fe, 0x923),
(0x650210d70c54fe, 0x124b4), (0x260210d70c54fe, 0x294), (0x660210d70c54fe, 0x144b2), (0x230a10d70c54fe, 0x10),
(0x240a10d70c54fe, 0x10), (0x260a10d70c54fe, 0x0), (0x270a10d70c54fe, 0x0), (0x660230d70c54fe, 0x212),
(0x621230d70c54fe, 0x0), (0x621240d70c54fe, 0x0), (0x710221d70c54fe, 0x0), (0x630032e70c54fe, 0x24c)]
def rootAr7p2 : RecordPage := #[
(0x660032e70c54fe, 0x0), (0x41432e70c54fe, 0x5498e), (0x630042e70c54fe, 0xe), (0x510050f70c54fe, 0x14a7),
(0x430050f70c54fe, 0x576), (0x42050f70c54fe, 0x25484252a521094a94631cad4d9cb5ca), (0x510060f70c54fe, 0x6acd8af), (0x460060f70c54fe, 0x72dd48582a31),
(0x32060f70c54fe, 0x2529498e9376199d24f58ed8a), (0x42060f70c54fe, 0x21094ad684252b598c939709ad1cfdca), (0x510070f70c54fe, 0x43641), (0x32070f70c54fe, 0xa529463a946121c991d8a945),
(0x510080f70c54fe, 0x25c9), (0x430080f70c54fe, 0x9b0), (0x42080f70c54fe, 0x25494a94b5a52a52d6631d365c1d3dca), (0x610032f70c54fe, 0x645),
(0x630032f70c54fe, 0x47772), (0x660032f70c54fe, 0x1ec5), (0x610042f70c54fe, 0xe), (0x630042f70c54fe, 0x13dfad),
(0x661630871c54fe, 0x12), (0x440660871c54fe, 0x3a40), (0x442660871c54fe, 0x6494e), (0x620c60250c64fe, 0x10),
(0x842c60250c64fe, 0x12), (0xa40e60250c64fe, 0x0), (0x260e60250c64fe, 0x842d693a5263194), (0x660e60250c64fe, 0x194),
(0x32c70650c64fe, 0x12), (0x240e70650c64fe, 0x1d2), (0x250e70650c64fe, 0x12), (0x270e70650c64fe, 0x3a52)]
def rootAr7p3 : RecordPage := #[
(0x132e70650c64fe, 0x10), (0x610871650c64fe, 0x10), (0x630871650c64fe, 0x10), (0x640871650c64fe, 0x10),
(0xa40871650c64fe, 0x0), (0x260871650c64fe, 0x14), (0x660871650c64fe, 0x14), (0x240c71650c64fe, 0x10),
(0x250c71650c64fe, 0x10), (0x270c71650c64fe, 0x12), (0x841a71650c64fe, 0x10), (0x231620c70c64fe, 0x0),
(0x241620c70c64fe, 0x0), (0x241630c70c64fe, 0x0), (0x261630c70c64fe, 0x10), (0x271630c70c64fe, 0x10),
(0x261640c70c64fe, 0x10), (0x271640c70c64fe, 0x10), (0x430260c70c64fe, 0x53a34), (0x440260c70c64fe, 0x55a34),
(0x460260c70c64fe, 0x2ad3a310c), (0x271660c70c64fe, 0x252), (0x430270c70c64fe, 0xaf2), (0x440270c70c64fe, 0xaf2),
(0x630831a70c64fe, 0x0), (0x241620c70c65fe, 0x0), (0x241630c70c65fe, 0x0), (0x261630c70c65fe, 0x10),
(0x271630c70c65fe, 0x10), (0x261640c70c65fe, 0x10), (0x271640c70c65fe, 0x10), (0x430260c70c65fe, 0xb34)]
def rootAr7p4 : RecordPage := #[
(0x440260c70c65fe, 0x5bb34), (0x460260c70c65fe, 0x2dd294), (0x271660c70c65fe, 0x0), (0x430270c70c65fe, 0x12)]
def rootAr7 : Records := #[rootAr7p0, rootAr7p1, rootAr7p2, rootAr7p3, rootAr7p4]
def testrootAr7 : ℕ → Bool := testAt rootA bsrootA 6 rootAr6 rootAr7 4 6
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c0 : checkBlock testrootAr7 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c2 : checkBlock testrootAr7 2 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c4 : checkBlock testrootAr7 2 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c6 : checkBlock testrootAr7 2 6 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c8 : checkBlock testrootAr7 2 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c10 : checkBlock testrootAr7 2 10 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c12 : checkBlock testrootAr7 2 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c14 : checkBlock testrootAr7 2 14 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c16 : checkBlock testrootAr7 2 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c18 : checkBlock testrootAr7 2 18 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c20 : checkBlock testrootAr7 2 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c22 : checkBlock testrootAr7 2 22 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c24 : checkBlock testrootAr7 2 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c26 : checkBlock testrootAr7 2 26 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c28 : checkBlock testrootAr7 2 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c30 : checkBlock testrootAr7 2 30 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c32 : checkBlock testrootAr7 2 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c34 : checkBlock testrootAr7 2 34 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c36 : checkBlock testrootAr7 2 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c38 : checkBlock testrootAr7 2 38 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c40 : checkBlock testrootAr7 2 40 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c42 : checkBlock testrootAr7 2 42 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c44 : checkBlock testrootAr7 2 44 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c46 : checkBlock testrootAr7 2 46 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c48 : checkBlock testrootAr7 2 48 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c50 : checkBlock testrootAr7 2 50 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c52 : checkBlock testrootAr7 2 52 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c54 : checkBlock testrootAr7 2 54 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c56 : checkBlock testrootAr7 2 56 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c58 : checkBlock testrootAr7 2 58 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c60 : checkBlock testrootAr7 2 60 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c62 : checkBlock testrootAr7 2 62 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c64 : checkBlock testrootAr7 2 64 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c66 : checkBlock testrootAr7 2 66 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c68 : checkBlock testrootAr7 2 68 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c70 : checkBlock testrootAr7 2 70 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c72 : checkBlock testrootAr7 2 72 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c74 : checkBlock testrootAr7 2 74 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c76 : checkBlock testrootAr7 2 76 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c78 : checkBlock testrootAr7 2 78 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c80 : checkBlock testrootAr7 2 80 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c82 : checkBlock testrootAr7 2 82 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c84 : checkBlock testrootAr7 2 84 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c86 : checkBlock testrootAr7 2 86 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c88 : checkBlock testrootAr7 2 88 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c90 : checkBlock testrootAr7 2 90 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c92 : checkBlock testrootAr7 2 92 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c94 : checkBlock testrootAr7 2 94 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c96 : checkBlock testrootAr7 2 96 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c98 : checkBlock testrootAr7 2 98 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c100 : checkBlock testrootAr7 2 100 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c102 : checkBlock testrootAr7 2 102 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c104 : checkBlock testrootAr7 2 104 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c106 : checkBlock testrootAr7 2 106 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c108 : checkBlock testrootAr7 2 108 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c110 : checkBlock testrootAr7 2 110 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c112 : checkBlock testrootAr7 2 112 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c114 : checkBlock testrootAr7 2 114 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c116 : checkBlock testrootAr7 2 116 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c118 : checkBlock testrootAr7 2 118 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c120 : checkBlock testrootAr7 2 120 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c122 : checkBlock testrootAr7 2 122 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c124 : checkBlock testrootAr7 2 124 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c126 : checkBlock testrootAr7 2 126 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c128 : checkBlock testrootAr7 2 128 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr7c130 : checkBlock testrootAr7 2 130 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootAr7 : LayerOK rootA 7 rootAr7 := by
  apply layer_of_block (bs := bsrootA) (k := 6) (old := rootAr6) (cw := 4) (rw := 6) (by decide +kernel) vbsrootA vrootAr6
  exact @block_merge testrootAr7 0 132 28 (@block_merge testrootAr7 0 66 66 (@block_merge testrootAr7 0 32 34 (@block_merge testrootAr7 0 16 16 (@block_merge testrootAr7 0 8 8 (@block_merge testrootAr7 0 4 4 (@block_merge testrootAr7 0 2 2 rootAr7c0 rootAr7c2) (@block_merge testrootAr7 4 2 2 rootAr7c4 rootAr7c6)) (@block_merge testrootAr7 8 4 4 (@block_merge testrootAr7 8 2 2 rootAr7c8 rootAr7c10) (@block_merge testrootAr7 12 2 2 rootAr7c12 rootAr7c14))) (@block_merge testrootAr7 16 8 8 (@block_merge testrootAr7 16 4 4 (@block_merge testrootAr7 16 2 2 rootAr7c16 rootAr7c18) (@block_merge testrootAr7 20 2 2 rootAr7c20 rootAr7c22)) (@block_merge testrootAr7 24 4 4 (@block_merge testrootAr7 24 2 2 rootAr7c24 rootAr7c26) (@block_merge testrootAr7 28 2 2 rootAr7c28 rootAr7c30)))) (@block_merge testrootAr7 32 16 18 (@block_merge testrootAr7 32 8 8 (@block_merge testrootAr7 32 4 4 (@block_merge testrootAr7 32 2 2 rootAr7c32 rootAr7c34) (@block_merge testrootAr7 36 2 2 rootAr7c36 rootAr7c38)) (@block_merge testrootAr7 40 4 4 (@block_merge testrootAr7 40 2 2 rootAr7c40 rootAr7c42) (@block_merge testrootAr7 44 2 2 rootAr7c44 rootAr7c46))) (@block_merge testrootAr7 48 8 10 (@block_merge testrootAr7 48 4 4 (@block_merge testrootAr7 48 2 2 rootAr7c48 rootAr7c50) (@block_merge testrootAr7 52 2 2 rootAr7c52 rootAr7c54)) (@block_merge testrootAr7 56 4 6 (@block_merge testrootAr7 56 2 2 rootAr7c56 rootAr7c58) (@block_merge testrootAr7 60 2 4 rootAr7c60 (@block_merge testrootAr7 62 2 2 rootAr7c62 rootAr7c64)))))) (@block_merge testrootAr7 66 32 34 (@block_merge testrootAr7 66 16 16 (@block_merge testrootAr7 66 8 8 (@block_merge testrootAr7 66 4 4 (@block_merge testrootAr7 66 2 2 rootAr7c66 rootAr7c68) (@block_merge testrootAr7 70 2 2 rootAr7c70 rootAr7c72)) (@block_merge testrootAr7 74 4 4 (@block_merge testrootAr7 74 2 2 rootAr7c74 rootAr7c76) (@block_merge testrootAr7 78 2 2 rootAr7c78 rootAr7c80))) (@block_merge testrootAr7 82 8 8 (@block_merge testrootAr7 82 4 4 (@block_merge testrootAr7 82 2 2 rootAr7c82 rootAr7c84) (@block_merge testrootAr7 86 2 2 rootAr7c86 rootAr7c88)) (@block_merge testrootAr7 90 4 4 (@block_merge testrootAr7 90 2 2 rootAr7c90 rootAr7c92) (@block_merge testrootAr7 94 2 2 rootAr7c94 rootAr7c96)))) (@block_merge testrootAr7 98 16 18 (@block_merge testrootAr7 98 8 8 (@block_merge testrootAr7 98 4 4 (@block_merge testrootAr7 98 2 2 rootAr7c98 rootAr7c100) (@block_merge testrootAr7 102 2 2 rootAr7c102 rootAr7c104)) (@block_merge testrootAr7 106 4 4 (@block_merge testrootAr7 106 2 2 rootAr7c106 rootAr7c108) (@block_merge testrootAr7 110 2 2 rootAr7c110 rootAr7c112))) (@block_merge testrootAr7 114 8 10 (@block_merge testrootAr7 114 4 4 (@block_merge testrootAr7 114 2 2 rootAr7c114 rootAr7c116) (@block_merge testrootAr7 118 2 2 rootAr7c118 rootAr7c120)) (@block_merge testrootAr7 122 4 6 (@block_merge testrootAr7 122 2 2 rootAr7c122 rootAr7c124) (@block_merge testrootAr7 126 2 4 rootAr7c126 (@block_merge testrootAr7 128 2 2 rootAr7c128 rootAr7c130))))))) (show checkBlock testrootAr7 28 132 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def rootAr8p0 : RecordPage := #[
(0x610870c54fe, 0x12a4a54a4214a5ad203d00ac01b8034a4210), (0xa10870c54fe, 0x25494a9484294b598c73a108425294a94a52d6b598c631cc631409), (0xe10870c54fe, 0x2411a03c1a0b), (0x620870c54fe, 0x12a4a54a52920bd02ac0982c03085296b4210),
(0x630870c54fe, 0x12a4214a5ad4a483740cb8260d01ca54a4210), (0x250870c54fe, 0x210842108425294a108425294ad6b5a108425294ad6b598c632108425294ad6b598c631ce73a108425294a41fb5ad6a528ca528ea5281d), (0x650870c54fe, 0x4a5085ad08421294a42b14ca56b5acc0cb82a0f02c84f412d047410d294), (0x260870c54fe, 0x2108421084294a521084294a52d6b5a1084294a52d6b598c6321084294a52d6b598c631ce73a1084294a5294b5ad694a4c94a4e94a42d),
(0x660870c54fe, 0x529085296b529084214a5282b14d296b5acc0db82e1103d29217ca52), (0x620c70c54fe, 0x3318a950), (0xa20c70c54fe, 0x371aa812c7318a), (0x230c70c54fe, 0x4a9295294a31cc70e416317421295296b318e63190841cc),
(0x630c70c54fe, 0x820190fe83d1d8c610), (0x240c70c54fe, 0x4a9084a54a5ad4a398c610c1a3364a54a318c631d08418c), (0x640c70c54fe, 0x9203911e8451d8ce10), (0x260c70c54fe, 0x25284252b598c7318670a108425294ad6b598e63140f55244fa13684ba528a),
(0x660c70c54fe, 0x29816451228f554), (0x270c70c54fe, 0x29484294b598c731847021084294a52d6b598e63141154a9491565294a4a), (0x670c70c54fe, 0x2b81e851238fd52), (0x321c70c54fe, 0x95294a52457a14d84971060a92a94a28bb6531ce616d459),
(0x721c70c54fe, 0x86395184be09), (0x210d70c54fe, 0x95252a5210a52d6a521084252948da6b94a94a50d267a52d6b59865718d409), (0xa10d70c54fe, 0xa04c8eb4399c4dea), (0x230d70c54fe, 0x25494a94a518a84252a52d66394a3cba1094a47795296b318e63990841cc),
(0x240d70c54fe, 0x4a9084a54a5ad4a395084a54a5acc62947b64a54a318c631908418c), (0x221d70c54fe, 0x4a8c53954a28fa59), (0x621d70c54fe, 0x7b3c824bea), (0x32e70c54fe, 0x95252a521094a94b598e94a946394a920587f62a0c),
(0x432e70c54fe, 0x31ca620d4a9318c), (0x42e70c54fe, 0x9521094a94b5a1094a94b598c84294b598c529c8572a0c), (0x442e70c54fe, 0x18c53106a5398c), (0x50f70c54fe, 0x12a4a54a42129528c6398c63148b72a108425294a94a518e632ca529c89b590f6)]
def rootAr8p1 : RecordPage := #[
(0x60f70c54fe, 0x94a1094ad6631cc6318a49b9ce5246108425294ad6b598e6328a5294a3097648f619c2a511b4), (0x70f70c54fe, 0x14a4214a5acc6398c539ce525e1084294a52d6b598e6324a52a94611c09492b2), (0x80f70c54fe, 0x12a4a54a4a54a5acc6398c63149d72a5294a94a52d6b598e6320a529c9b841330), (0x32f70c54fe, 0x25494a9494a9463a0a94a4a4bd2945246ca6386aa928d8a162949f),
(0x42f70c54fe, 0x4a9084a54a5ad084a54a5acc6421052764aa528a49dad6522dcc1ba98a76294a5), (0x630871c54fe, 0x12a4a54a284ff084a5254ca94b598c73a52a520c6398c), (0x660871c54fe, 0x29484294b598ea518ad51a948184294b598c54b18c6298e7528c55815274a52), (0x431871c54fe, 0x9521094a94b5a1094a4ad95296b318c5321094a94b594a52906e74a54a39ce5398c6398c),
(0x630872c54fe, 0x95210a52d653a1652a51ce6321094a94b5a0c631ce), (0xc60250c64fe, 0x18b163a10a52d693a526315ec84210a5294b5ad6039ce739ce62bd8c), (0xe60250c64fe, 0xa5210a52d693a526318af84210a52945bad694b5ad692ce5293a5262bd8c), (0xc62250c64fe, 0x29484294b598e62c610a52d66314c84210a5294b5ad6739ce039ce6298c),
(0xc70650c64fe, 0xab62e5d293940), (0xe70650c64fe, 0x3182e94a8bf92f64bb93252), (0x871650c64fe, 0x529085296b5294a3173084214a528cd65d296b5acc963b98a00018c3), (0xc71650c64fe, 0x12630e8d368b3c0c),
(0xa71650c64fe, 0x29484294b5a9463558e63061084294a52d6b598c6398c63a4c9498c3), (0xe71650c64fe, 0x2a64c61b14c), (0xc73650c64fe, 0x24ad6355ccf631cc), (0x620c70c64fe, 0x4986d96bb190),
(0x230c70c64fe, 0x12a4a54a4a54a499ee7318d76421295296b39cc631908418c), (0x630c70c64fe, 0x9315813937e8dd6db5e10), (0x240c70c64fe, 0x12a421295296b4a54a319268b94c6365929528e731908418c), (0x640c70c64fe, 0x931d803938e8e16db6610),
(0xa40c70c64fe, 0x4992c06b94e6318c), (0x260c70c64fe, 0x94a1094ad6739ca6321084252949a6cb94ad6b59ce7298c6524e9a39e8e5a528c), (0x660c70c64fe, 0x24cd60664eb70b7594), (0x270c70c64fe, 0xa5210a52d6739ca6321084294a52d6b59ce7298c64a9493be4ed94a5294a4c),
(0x670c70c64fe, 0x181ba3adc6df64a52), (0x831a70c64fe, 0x4a9085296b421295296b31d085296b318c639cf1642106318c), (0x842e70c64fe, 0x93554c6bb190), (0x640c72c64fe, 0x1e2e6414e)]
def rootAr8p2 : RecordPage := #[
(0x620c70c65fe, 0xf378b9d0), (0x630c70c65fe, 0x1c1393e68f77abc610), (0x240c70c65fe, 0x4a9084a54a5ad085296b31cc539cf374214a5acc63990841cc), (0x640c70c65fe, 0x1c0193f68fb7abce10),
(0xa40c70c65fe, 0xe05b14c7398c), (0x260c70c65fe, 0x210b5a1094ad66318a63a108425294ad6b598c629ce752503a4068ffa528e), (0x660c70c65fe, 0x70565057dbddd4), (0x270c70c65fe, 0x210a52d684294b598c6298e84210a5294b5ad66318a739d2a5250794a4e),
(0x670c70c65fe, 0x705e9057ebe5d2), (0x260a70d65fe, 0x8421084210a529484210a5294b5ad684210a5294b5ad66318c62a1084294a52d6b59ce7398c6321084294a5294b5ad6039ce6318c94a4e), (0x660a70d65fe, 0x528c54214a5ace5319084214a5296b5acc7318c6318e5529254a52)]
def rootAr8 : Records := #[rootAr8p0, rootAr8p1, rootAr8p2]
def testrootAr8 : ℕ → Bool := testAt rootA bsrootA 7 rootAr7 rootAr8 4 8
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c0 : checkBlock testrootAr8 2 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c2 : checkBlock testrootAr8 2 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c4 : checkBlock testrootAr8 2 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c6 : checkBlock testrootAr8 2 6 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c8 : checkBlock testrootAr8 2 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c10 : checkBlock testrootAr8 2 10 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c12 : checkBlock testrootAr8 2 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c14 : checkBlock testrootAr8 2 14 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c16 : checkBlock testrootAr8 2 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c18 : checkBlock testrootAr8 2 18 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c20 : checkBlock testrootAr8 2 20 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c22 : checkBlock testrootAr8 2 22 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c24 : checkBlock testrootAr8 2 24 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c26 : checkBlock testrootAr8 2 26 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c28 : checkBlock testrootAr8 2 28 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c30 : checkBlock testrootAr8 2 30 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c32 : checkBlock testrootAr8 2 32 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c34 : checkBlock testrootAr8 2 34 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c36 : checkBlock testrootAr8 2 36 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c38 : checkBlock testrootAr8 2 38 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c40 : checkBlock testrootAr8 2 40 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c42 : checkBlock testrootAr8 2 42 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c44 : checkBlock testrootAr8 2 44 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c46 : checkBlock testrootAr8 2 46 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c48 : checkBlock testrootAr8 2 48 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c50 : checkBlock testrootAr8 2 50 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c52 : checkBlock testrootAr8 2 52 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c54 : checkBlock testrootAr8 2 54 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c56 : checkBlock testrootAr8 2 56 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c58 : checkBlock testrootAr8 2 58 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c60 : checkBlock testrootAr8 2 60 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c62 : checkBlock testrootAr8 2 62 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c64 : checkBlock testrootAr8 2 64 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c66 : checkBlock testrootAr8 2 66 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c68 : checkBlock testrootAr8 2 68 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c70 : checkBlock testrootAr8 2 70 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c72 : checkBlock testrootAr8 2 72 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr8c74 : checkBlock testrootAr8 1 74 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootAr8 : LayerOK rootA 8 rootAr8 := by
  apply layer_of_block (bs := bsrootA) (k := 7) (old := rootAr7) (cw := 4) (rw := 8) (by decide +kernel) vbsrootA vrootAr7
  exact @block_merge testrootAr8 0 75 21 (@block_merge testrootAr8 0 38 37 (@block_merge testrootAr8 0 18 20 (@block_merge testrootAr8 0 8 10 (@block_merge testrootAr8 0 4 4 (@block_merge testrootAr8 0 2 2 rootAr8c0 rootAr8c2) (@block_merge testrootAr8 4 2 2 rootAr8c4 rootAr8c6)) (@block_merge testrootAr8 8 4 6 (@block_merge testrootAr8 8 2 2 rootAr8c8 rootAr8c10) (@block_merge testrootAr8 12 2 4 rootAr8c12 (@block_merge testrootAr8 14 2 2 rootAr8c14 rootAr8c16)))) (@block_merge testrootAr8 18 10 10 (@block_merge testrootAr8 18 4 6 (@block_merge testrootAr8 18 2 2 rootAr8c18 rootAr8c20) (@block_merge testrootAr8 22 2 4 rootAr8c22 (@block_merge testrootAr8 24 2 2 rootAr8c24 rootAr8c26))) (@block_merge testrootAr8 28 4 6 (@block_merge testrootAr8 28 2 2 rootAr8c28 rootAr8c30) (@block_merge testrootAr8 32 2 4 rootAr8c32 (@block_merge testrootAr8 34 2 2 rootAr8c34 rootAr8c36))))) (@block_merge testrootAr8 38 18 19 (@block_merge testrootAr8 38 8 10 (@block_merge testrootAr8 38 4 4 (@block_merge testrootAr8 38 2 2 rootAr8c38 rootAr8c40) (@block_merge testrootAr8 42 2 2 rootAr8c42 rootAr8c44)) (@block_merge testrootAr8 46 4 6 (@block_merge testrootAr8 46 2 2 rootAr8c46 rootAr8c48) (@block_merge testrootAr8 50 2 4 rootAr8c50 (@block_merge testrootAr8 52 2 2 rootAr8c52 rootAr8c54)))) (@block_merge testrootAr8 56 10 9 (@block_merge testrootAr8 56 4 6 (@block_merge testrootAr8 56 2 2 rootAr8c56 rootAr8c58) (@block_merge testrootAr8 60 2 4 rootAr8c60 (@block_merge testrootAr8 62 2 2 rootAr8c62 rootAr8c64))) (@block_merge testrootAr8 66 4 5 (@block_merge testrootAr8 66 2 2 rootAr8c66 rootAr8c68) (@block_merge testrootAr8 70 2 3 rootAr8c70 (@block_merge testrootAr8 72 2 1 rootAr8c72 rootAr8c74)))))) (show checkBlock testrootAr8 21 75 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def rootAr9p0 : RecordPage := #[
(0x870c54fe, 0x210842108425294a548421094a52a52948421094a5294a94a5294b5ad6842108425294a94a5294b5ad6b598c632108425294a94a5294b5ad66318c739cc842108421094a52948443e5294a94a52940d0ba5294b5ad6b5ad663025ce07050301), (0xc70c54fe, 0x4a929529084a54a5acc63994a31ce6421084a5295294a5ad6b31cc628a49c144c05508421294a44a47295294a108fd296b5acc1d1b70c8b8a89a94a), (0xd70c54fe, 0x95252a521094a94b598c73294629ca8421094a52a5294b5ad66398c5294a35335421084a5295294a5ad6b31462e517a945aa2b), (0xa70c54fe, 0x842108421094a52952108425294a94a52108425294a52a5294a52d6b5a108421094a52a5294a52d6b5ad66318c8421094a52a5294b5ad66318c631ce731ce842108421094a5294a52a5294a5294b5ad6b5ad66318c6318c7398c6318c052b01),
(0xe70c54fe, 0x12a4a54a421295296b318e6318c3d3b731c726f08421294a54a5296b5acc7318a51a99828980c21084a5295294a5ad6b318c6318e7398c6318c61689a94a), (0xf70c54fe, 0x25494a9484252a52d6631cc6318a49739ca478421094a52a5294b5ad66398c5294a51493c2108420a4594a529494874a5294a2906d6b5ad651fb18c6318e7318e7398c62942aa03), (0x871c54fe, 0x842108421094a52952108425294a94a52108425294a52a5294a52d6b5a108421094a5294a94a5294b5ad6b598c7421084a5294a54a5294a5ad6b318c6313d48ea528e4dd908421084a52949365295294a5296b5ad6b318c625b18c6318c5298c639ce), (0x872c54fe, 0x842108421094a52952108425294a94a52108421094a5294a94a5294b5ad6b5a108421094a5294a94a5294b5ad6b598c642108421294a54a5294a5ad6b5ace739ce4f524a94a3d3b7421084a5294a54a5294a5ad6b39ce728b9ce739ce529ce7318c),
(0x250c64fe, 0x421085294a421085ad6b421085294a314c5784210a5294b5ad66398e84210a5294b5ad6739d262ab14e1084294a5294b5ad694a4e94a4e), (0x650c64fe, 0x1084214a529084216b5ad084214a528c531961084294a5294b5ad6639cc726c21084214a5294a5ad6b5ace739ce7298c63616317d76108421084294a5294a52d6b5ad6b59ce739ca62db1661084294a5294b5ad694a5273a52949ca94a52), (0xc70c64fe, 0x95252a521094a94b59ce72a52a518c8421094a525f5d94a94a52d6b59ce7298c6319c25908421294a4f2ef295294a3ab9d296b5ace2dedae6b69633b18c), (0xa70c64fe, 0x42108421084a5294a908421294a54a52908421294a54a5294a5ad6b42108421294a54a5294a5ad6b5ace739908421294a54a5296b5acc6318c7b6318c63a10842108425294a5294a94a5294a52d6b5ad6b598c6318c7398c6318c7398c09),
(0xe70c64fe, 0x25494a9484252a52d6739ca63eb18e625c21084a52931b0ca54a5296b5ace7394c6318c67098421094a52a5294b5ad66318e6318c6394a633b18c), (0xc72c64fe, 0x9521094a94b5a1084252949955e52a5294b5ad672a1094a94b598c7313d8c631f58f6c84252a52d67394e7398c532108425294a94a52d6b59ce739fda5cc6318c631ce7318c6298c), (0xa70d64fe, 0x10842108421294a52a421084a5295294a421084a5295294a5296b5ad08421294a54a5296b5ace7398e542108421294a5295294a5296b5ad6b318c6298c6318c742108421084a5294a5295294a5294a5ad6b5ad6b318c639cc6318c6318e7318a), (0xc70c65fe, 0x25484294b5a1094a94b598c62a10a52d663a108425294a94a52d6b598c629ce73a041dd08421294a5231f295294a46c5d296b5ad130f0ac837b740b9ce),
(0xa70c65fe, 0x10842108421294a52a421084a5295294a421084a5295294a5296b5ad08421294a5295294a5296b5acc631908421294a54a5296b5ace7398e696318c63210842108425294a5294a94a5294a52d6b5ad6b59ce6318c6318c6318c631ce07), (0xe70c65fe, 0x25484294b5a1094a94b598c629cfec631ca308421294a54a5296b5acc6314e739ce81078421094a52a5294b5ad67318c6318c6314a740b9ce), (0xa70d65fe, 0x42108421084a5294a908421294a54a52908421294a54a5294a5ad6b421084a5295294a5ad6b318c631508421084a5294a54a5294a5ad6b5ace739ca6318c63190842108421294a5294ac9ca5295294a5294a5ad6b5ad6b318e7318c6318c6318c639ca)]
def rootAr9 : Records := #[rootAr9p0]
def testrootAr9 : ℕ → Bool := testAt rootA bsrootA 8 rootAr8 rootAr9 4 7
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c0 : checkBlock testrootAr9 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c1 : checkBlock testrootAr9 1 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c2 : checkBlock testrootAr9 1 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c3 : checkBlock testrootAr9 1 3 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c4 : checkBlock testrootAr9 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c5 : checkBlock testrootAr9 1 5 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c6 : checkBlock testrootAr9 1 6 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c7 : checkBlock testrootAr9 1 7 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c8 : checkBlock testrootAr9 1 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c9 : checkBlock testrootAr9 1 9 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c10 : checkBlock testrootAr9 1 10 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c11 : checkBlock testrootAr9 1 11 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c12 : checkBlock testrootAr9 1 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c13 : checkBlock testrootAr9 1 13 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c14 : checkBlock testrootAr9 1 14 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c15 : checkBlock testrootAr9 1 15 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c16 : checkBlock testrootAr9 1 16 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c17 : checkBlock testrootAr9 1 17 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr9c18 : checkBlock testrootAr9 1 18 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootAr9 : LayerOK rootA 9 rootAr9 := by
  apply layer_of_block (bs := bsrootA) (k := 8) (old := rootAr8) (cw := 4) (rw := 7) (by decide +kernel) vbsrootA vrootAr8
  exact @block_merge testrootAr9 0 19 13 (@block_merge testrootAr9 0 9 10 (@block_merge testrootAr9 0 4 5 (@block_merge testrootAr9 0 2 2 (@block_merge testrootAr9 0 1 1 rootAr9c0 rootAr9c1) (@block_merge testrootAr9 2 1 1 rootAr9c2 rootAr9c3)) (@block_merge testrootAr9 4 2 3 (@block_merge testrootAr9 4 1 1 rootAr9c4 rootAr9c5) (@block_merge testrootAr9 6 1 2 rootAr9c6 (@block_merge testrootAr9 7 1 1 rootAr9c7 rootAr9c8)))) (@block_merge testrootAr9 9 5 5 (@block_merge testrootAr9 9 2 3 (@block_merge testrootAr9 9 1 1 rootAr9c9 rootAr9c10) (@block_merge testrootAr9 11 1 2 rootAr9c11 (@block_merge testrootAr9 12 1 1 rootAr9c12 rootAr9c13))) (@block_merge testrootAr9 14 2 3 (@block_merge testrootAr9 14 1 1 rootAr9c14 rootAr9c15) (@block_merge testrootAr9 16 1 2 rootAr9c16 (@block_merge testrootAr9 17 1 1 rootAr9c17 rootAr9c18))))) (show checkBlock testrootAr9 13 19 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def rootAr10p0 : RecordPage := #[
(0xc54fe, 0x421084a529421085294a421084a5294a96b5ad08421294a54a528c6318c3e108425294a52a5294a52d6b59ce739c6c2108421294a5295294a5296b5ad6b318c6398c2d448e2a830610842108425294a5294a94a5294a52d6b5ad6b598c7318c), (0xc64fe, 0x108421294a5084214a52908421294a52a5ad6b421084a5295294a314c6e108425294a52a5294a52d6b598e731c6c2108421294a5295294a5296b5ad6b39ce739ca63195d8c541842108421094a529493465294a94a5294a52d6b5ad6b59ce739ca), (0xd64fe, 0x8421094a5284210a52948421094a52952d6b5a108425294a94a518a62a108425294a52a5294a52d6b598e63a108425294a94a52d6b59ce739ce5318a758c52a10842108425294a5294a94a5294a52d6b5ad6b59ce739ca), (0xc65fe, 0x108421294a5084214a52908421294a52a5ad6b421084a5295294a394e6e108421094a52a5294a52d6b5ad66318c61f08421084a5294a54a5294a5ad6b5acc6318c629ce8e1739f0610842108425294a5294a94a5294a52d6b5ad6b598c6318a),
(0xd65fe, 0x2108425294a1084294a52108425294a54b5ad68421094a52a5294729ca842108425294a94a5294b5ad6b598c632108425294a94a52d6b598c6318c539ca95ce52a10842108425294a5294a94a5294a52d6b5ad6b598c6318a)]
def rootAr10 : Records := #[rootAr10p0]
def testrootAr10 : ℕ → Bool := testAt rootA bsrootA 9 rootAr9 rootAr10 4 5
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr10c0 : checkBlock testrootAr10 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr10c1 : checkBlock testrootAr10 1 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr10c2 : checkBlock testrootAr10 1 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr10c3 : checkBlock testrootAr10 1 3 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr10c4 : checkBlock testrootAr10 1 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootAr10 : LayerOK rootA 10 rootAr10 := by
  apply layer_of_block (bs := bsrootA) (k := 9) (old := rootAr9) (cw := 4) (rw := 5) (by decide +kernel) vbsrootA vrootAr9
  exact @block_merge testrootAr10 0 5 27 (@block_merge testrootAr10 0 2 3 (@block_merge testrootAr10 0 1 1 rootAr10c0 rootAr10c1) (@block_merge testrootAr10 2 1 2 rootAr10c2 (@block_merge testrootAr10 3 1 1 rootAr10c3 rootAr10c4))) (show checkBlock testrootAr10 27 5 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
def rootAr11p0 : RecordPage := #[
(0xfe, 0xc64bb9ca6c73061084210842108425294a5294a5294a1084294a5294a5294a52108425294a54b5ad6b5ad6b5ad68421094a52a5294)]
def rootAr11 : Records := #[rootAr11p0]
def testrootAr11 : ℕ → Bool := testAt rootA bsrootA 10 rootAr10 rootAr11 4 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem rootAr11c0 : checkBlock testrootAr11 1 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootAr11 : LayerOK rootA 11 rootAr11 := by
  apply layer_of_block (bs := bsrootA) (k := 10) (old := rootAr10) (cw := 4) (rw := 3) (by decide +kernel) vbsrootA vrootAr10
  exact @block_merge testrootAr11 0 1 31 rootAr11c0 (show checkBlock testrootAr11 31 1 = true by decide +kernel)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vrootA : Valid rootA := by
  apply bound_of_layers (bs := bsrootA) (last := rootAr11) (cw := 4) (rw := 0) (by decide +kernel) vbsrootA vrootAr11 (by decide +kernel) (canon_checked (by decide +kernel)) 0x1
  decide +kernel
end PEqualNP.Outside.L_meta_10714.SignedCert.GraphA

namespace PEqualNP.Outside.L_meta_10714.CircuitWitness
open PEqualNP.CircuitLowerBounds

def gates : List Gate := [
  ⟨.or, [4, 5]⟩,
  ⟨.and, [6, 7]⟩,
  ⟨.or, [0, 3]⟩,
  ⟨.or, [1, 9]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.and, [10, 11]⟩,
  ⟨.and, [0, 3]⟩,
  ⟨.or, [12, 13]⟩,
  ⟨.or, [8, 14]⟩,
  ⟨.or, [1, 2]⟩,
  ⟨.or, [4, 6]⟩,
  ⟨.and, [16, 17]⟩,
  ⟨.or, [15, 18]⟩]

theorem size : gates.length = 13 := rfl

theorem legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem computes : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, 19⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_10714.CircuitWitness

theorem PEqualNP.Outside.L_meta_10714 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_10714.SignedCert.Source.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_10714.SignedCert.Source.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_10714.SignedCert.Source.isBinary, op]⟩
    have hb := PEqualNP.Outside.L_meta_10714.SignedCert.GraphA.size_lb PEqualNP.Outside.L_meta_10714.SignedCert.GraphA.vrootA gates o (fun g hg => fits g hg) (fun x => (computes x).trans (PEqualNP.Outside.L_meta_10714.SignedCert.GraphA.edge_eq x))
    have hl : PEqualNP.Outside.L_meta_10714.CircuitWitness.gates.length = 13 := rfl
    exact ⟨PEqualNP.Outside.L_meta_10714.CircuitWitness.gates, 19, PEqualNP.Outside.L_meta_10714.CircuitWitness.legal, by omega, PEqualNP.Outside.L_meta_10714.CircuitWitness.computes⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
