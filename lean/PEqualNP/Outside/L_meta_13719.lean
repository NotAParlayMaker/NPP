import PEqualNP.Defs

-- A seven-gate monotone circuit realizes the table. Five binary gates would
-- have to discard both first-gate inputs. For each possible gate, two
-- rows with different target values then agree on all remaining wires.

namespace PEqualNP.Outside.L_meta_13719

-- The build and live relations are those used in the upstream signed-wire bounds.
-- The original relations and their compression proof appear in L_meta_9136.
def build {α : Type*} [DecidableEq α] (ops : α → α → Finset α) (goal : α) :
    ℕ → Finset α → Prop
  | 0, s => goal ∈ s
  | k+1, s => build ops goal k s ∨ ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z s)

def live {α : Type*} [DecidableEq α] (ops : α → α → Finset α) (goal : α) :
    ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨ ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧
      ∃ z ∈ ops a b, z ∉ s ∧ ∃ rest, s = insert a (insert b rest) ∧
        live ops goal k (insert z rest)

theorem build_subset {α : Type*} [DecidableEq α] {ops : α → α → Finset α} {g : α}
    {k : ℕ} {s t : Finset α} (h : build ops g k s) (sub : s ⊆ t) : build ops g k t := by
  induction k generalizing s t with
  | zero => exact sub h
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih h sub)
    · exact Or.inr ⟨a, sub ha, b, sub hb, hab, z, hz, ih tail (Finset.insert_subset_insert _ sub)⟩

def zeroCount {α β : Type*} [DecidableEq α] [DecidableEq β] (p : α → β) (zero : β)
    (s : Finset α) := (s.filter fun a => p a = zero).card

def project {α β : Type*} [DecidableEq α] [DecidableEq β] (p : α → β) (zero : β)
    (s : Finset α) := (s.image p).erase zero

theorem zero_insert {α β : Type*} [DecidableEq α] [DecidableEq β] (p : α → β) (zero : β)
    (a : α) (s : Finset α) : zeroCount p zero (insert a s) ≤
    zeroCount p zero s + (if p a = zero then 1 else 0) := by
  by_cases h : p a = zero
  · simp only [zeroCount, Finset.filter_insert, h, if_true]
    exact Finset.card_insert_le _ _
  · simp [zeroCount, Finset.filter_insert, h]

theorem zero_insert_new {α β : Type*} [DecidableEq α] [DecidableEq β] (p : α → β) (zero : β)
    (a : α) (s : Finset α) (hn : a ∉ s) : zeroCount p zero (insert a s) =
    zeroCount p zero s + (if p a = zero then 1 else 0) := by
  by_cases h : p a = zero
  · have h' : a ∉ s.filter (fun u => p u = zero) := fun m => hn (Finset.mem_filter.mp m).1
    simp [zeroCount, Finset.filter_insert, h, Finset.card_insert_of_notMem h']
  · simp [zeroCount, Finset.filter_insert, h]

theorem project_subset {α β : Type*} [DecidableEq α] [DecidableEq β] (p : α → β) (zero : β)
    {s t : Finset α} (h : s ⊆ t) : project p zero s ⊆ project p zero t := by
  exact Finset.erase_subset_erase _ (Finset.image_mono p h)

-- A binary gate collapses when it reads a constant or two copies of one wire.
-- A surviving gate is a legal operation on the two projected inputs.
theorem project_live {α β : Type*} [DecidableEq α] [DecidableEq β]
    (ops : α → α → Finset α) (ops' : β → β → Finset β) (p : α → β) (zero : β)
    (collapse : ∀ a b z, z ∈ ops a b → (p a = zero ∨ p b = zero ∨ p a = p b) →
      p z = zero ∨ p z = p a ∨ p z = p b)
    (preserve : ∀ a b z, z ∈ ops a b → p z ∈ ops' (p a) (p b))
    {g : α} (ng : p g ≠ zero) {k : ℕ} {s : Finset α} (h : live ops g k s) :
    ∃ l, l + zeroCount p zero s ≤ k ∧ build ops' (p g) l (project p zero s) := by
  induction k generalizing s with
  | zero =>
    change s = {g} at h
    subst s
    refine ⟨0, by simp [zeroCount, ng], ?_⟩
    change p g ∈ (Finset.image p {g}).erase zero
    simp [ng]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, _, z, hop, hz, r, hs, tail⟩
    · obtain ⟨l, bound, run⟩ := ih skip
      exact ⟨l, by omega, run⟩
    · obtain ⟨l, bound, run⟩ := ih tail
      have hr : r ⊆ s := by rw [hs]; exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
      have hzr : z ∉ r := fun hmem => hz (hr hmem)
      rw [zero_insert_new p zero z r hzr] at bound
      have cntA := zero_insert p zero a (insert b r)
      have cntB := zero_insert p zero b r
      have pbase : project p zero r ⊆ project p zero s := project_subset p zero hr
      have available {w : α} (hw : w ∈ s) (nw : p w ≠ zero) : p w ∈ project p zero s :=
        Finset.mem_erase.mpr ⟨nw, Finset.mem_image_of_mem p hw⟩
      have skipz (simple : p z = zero ∨ p z = p a ∨ p z = p b) :
          build ops' (p g) l (project p zero s) := by
        apply build_subset run
        intro v hv
        obtain ⟨nz, mem⟩ := Finset.mem_erase.mp hv
        rw [Finset.image_insert] at mem
        rcases Finset.mem_insert.mp mem with rfl | old
        · rcases simple with h0 | hA | hB
          · exact (nz h0).elim
          · rw [hA] at nz ⊢
            exact available ha nz
          · rw [hB] at nz ⊢
            exact available hb nz
        · exact pbase (Finset.mem_erase.mpr ⟨nz, old⟩)
      by_cases trivial : p a = zero ∨ p b = zero ∨ p a = p b
      · have simple := collapse a b z hop trivial
        have both (a0 : p a = zero) (b0 : p b = zero) : p z = zero := by
          rcases simple with e | e | e <;> simp_all
        refine ⟨l, ?_, skipz simple⟩
        rw [hs]
        by_cases a0 : p a = zero <;> by_cases b0 : p b = zero <;> by_cases z0 : p z = zero <;>
          first | exact False.elim (z0 (both a0 b0)) | (simp [a0, b0, z0] at cntA cntB bound; omega)
      · have na : p a ≠ zero := fun e => trivial (Or.inl e)
        have nb : p b ≠ zero := fun e => trivial (Or.inr (Or.inl e))
        have ne : p a ≠ p b := fun e => trivial (Or.inr (Or.inr e))
        refine ⟨l+1, ?_, Or.inr ⟨p a, available ha na, p b, available hb nb, ne,
          p z, preserve a b z hop, build_subset run ?_⟩⟩
        · rw [hs]
          simp only [if_neg na, if_neg nb, Nat.add_zero] at cntA cntB
          omega
        · intro v hv
          obtain ⟨nz, m⟩ := Finset.mem_erase.mp hv
          rw [Finset.image_insert] at m
          rcases Finset.mem_insert.mp m with rfl | old
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (pbase (Finset.mem_erase.mpr ⟨nz, old⟩))

end PEqualNP.Outside.L_meta_13719

namespace PEqualNP.Outside.L_meta_13719

-- Generic live-wire lemmas from L_meta_9136 under Apache-2.0.
variable {α : Type*} [DecidableEq α]

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

abbrev W := BitVec 64

def words (a b : W) : List W := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
def raw (a b : W) : Finset W := (words a b).toFinset
def clean (a b : W) : Finset W := (raw a b).erase 0

theorem raw_simple {a b z : W} (h : z ∈ raw a b) (e : a = 0 ∨ b = 0 ∨ a = b) :
    z = 0 ∨ z = a ∨ z = b := by
  simp only [raw, words, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases e with rfl | rfl | rfl <;> rcases h with rfl | rfl | rfl | rfl <;> simp
  · exact Or.inr (BitVec.and_allOnes (x := b))
  · exact Or.inr (Or.inl (BitVec.and_allOnes (x := a)))

theorem raw_mask {a b z : W} (h : z ∈ raw a b) (m : W) :
    z &&& m ∈ raw (a &&& m) (b &&& m) := by
  simp only [raw, words, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl
  · left; ext i; simp; cases a[i] <;> cases b[i] <;> cases m[i] <;> rfl
  · right; left; ext i; simp; cases a[i] <;> cases b[i] <;> cases m[i] <;> rfl
  · right; right; left; ext i; simp; cases a[i] <;> cases b[i] <;> cases m[i] <;> rfl
  · right; right; right; ext i; simp; cases a[i] <;> cases b[i] <;> cases m[i] <;> rfl

theorem raw_to_clean {g : W} (ng : g ≠ 0) {k : ℕ} {s : Finset W}
    (h : build raw g k s) : build clean g k (s.erase 0) := by
  induction k generalizing s with
  | zero => exact Finset.mem_erase.mpr ⟨ng, h⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, ne, z, hz, tail⟩
    · exact Or.inl (ih skip)
    · have run := ih tail
      by_cases bad : a = 0 ∨ b = 0 ∨ z = 0
      · have simpz : z = 0 ∨ z ∈ s := by
          rcases bad with h0 | h0 | h0
          · rcases raw_simple hz (.inl h0) with h | rfl | rfl
            · exact .inl h
            · exact .inr ha
            · exact .inr hb
          · rcases raw_simple hz (.inr (.inl h0)) with h | rfl | rfl
            · exact .inl h
            · exact .inr ha
            · exact .inr hb
          · exact .inl h0
        apply Or.inl
        apply build_subset run
        intro w hw
        obtain ⟨nz, mem⟩ := Finset.mem_erase.mp hw
        refine Finset.mem_erase.mpr ⟨nz, ?_⟩
        rcases Finset.mem_insert.mp mem with rfl | m
        · exact simpz.resolve_left nz
        · exact m
      · have na : a ≠ 0 := fun h => bad (.inl h)
        have nb : b ≠ 0 := fun h => bad (.inr (.inl h))
        have nz : z ≠ 0 := fun h => bad (.inr (.inr h))
        refine Or.inr ⟨a, Finset.mem_erase.mpr ⟨na,ha⟩, b, Finset.mem_erase.mpr ⟨nb,hb⟩, ne,
          z, Finset.mem_erase.mpr ⟨nz,hz⟩, build_subset run ?_⟩
        intro w hw
        obtain ⟨n0, mem⟩ := Finset.mem_erase.mp hw
        rcases Finset.mem_insert.mp mem with rfl | ms
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨n0,ms⟩)

def maskBank (m : W) (s : Finset W) := project (fun x : W => x &&& m) 0 s
def Hard (y m : W) (req : ℕ) (s : Finset W) : Prop :=
  ∀ t, build raw (y &&& m) t (maskBank m s) → req ≤ t

theorem fits {y m : W} {req k : ℕ} {s : Finset W} (hy : y &&& m ≠ 0)
    (hard : Hard y m req s) (h : live clean y k s) :
    req + zeroCount (fun x : W => x &&& m) 0 s ≤ k := by
  obtain ⟨l, pay, run⟩ := project_live clean raw (fun x : W => x &&& m) 0
    (fun a b z hop => raw_simple (raw_mask (Finset.mem_erase.mp hop).2 m))
    (fun a b z hop => raw_mask (Finset.mem_erase.mp hop).2 m) hy h
  have := hard l run
  omega

def freeAt (m z : W) (ws : List W) : Bool :=
  ((z &&& m) == 0) || ws.any fun w => (w &&& m) == (z &&& m)

theorem nextHard {y m a b z : W} {req : ℕ} {ws kept : List W}
    (old : Hard y m req ws.toFinset) (ha : a ∈ ws) (hb : b ∈ ws) (hop : z ∈ raw a b)
    (sub : kept.toFinset ⊆ ws.toFinset) :
    Hard y m (if freeAt m z ws then req else req-1) (insert z kept.toFinset) := by
  let p : W → W := fun u => u &&& m
  have haveOld {u : W} (hu : u ∈ ws) (hn : p u ≠ 0) : p u ∈ maskBank m ws.toFinset :=
    Finset.mem_erase.mpr ⟨hn, Finset.mem_image_of_mem p (List.mem_toFinset.mpr hu)⟩
  intro t run
  by_cases hf : freeAt m z ws = true
  · rw [if_pos hf]
    apply old t
    apply build_subset run
    intro u hu
    obtain ⟨nz, mem⟩ := Finset.mem_erase.mp hu
    rw [Finset.image_insert] at mem
    rcases Finset.mem_insert.mp mem with rfl | prev
    · simp only [freeAt, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hf
      rcases hf with zero | ⟨w, hw, eq⟩
      · exact (nz zero).elim
      · change p w = p z at eq
        change p z ≠ 0 at nz
        change p z ∈ maskBank m ws.toFinset
        rw [← eq] at nz ⊢
        exact haveOld hw nz
    · exact (project_subset p 0 sub) (Finset.mem_erase.mpr ⟨nz,prev⟩)
  · rw [if_neg hf]
    have new : p z ≠ 0 ∧ ∀ w ∈ ws, p w ≠ p z := by
      simpa [freeAt, p] using hf
    have hz := raw_mask hop m
    have neither : ¬ (p a = 0 ∨ p b = 0 ∨ p a = p b) := by
      intro hh
      rcases raw_simple hz hh with e | e | e
      · exact new.1 e
      · exact new.2 a ha e.symm
      · exact new.2 b hb e.symm
    have run' : build raw (y &&& m) (t+1) (maskBank m ws.toFinset) := by
      refine Or.inr ⟨p a, haveOld ha (fun e => neither (.inl e)), p b,
        haveOld hb (fun e => neither (.inr (.inl e))), fun e => neither (.inr (.inr e)),
        p z, hz, build_subset run ?_⟩
      intro w hw
      obtain ⟨nz, mem⟩ := Finset.mem_erase.mp hw
      rw [Finset.image_insert] at mem
      rcases Finset.mem_insert.mp mem with rfl | prev
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem ((project_subset p 0 sub) (Finset.mem_erase.mpr ⟨nz,prev⟩))
    have := old (t+1) run'
    omega

end PEqualNP.Outside.L_meta_13719

namespace PEqualNP.Outside.L_meta_13719

def atRow (w : W) (i : Fin 64) : Bool := w[i.val]

def fromRows (f : Fin 64 → Bool) : W := (BitVec.ofBoolListLE (List.ofFn f)).setWidth 64

theorem read_fromRows (f : Fin 64 → Bool) (i : Fin 64) : atRow (fromRows f) i = f i := by
  change (fromRows f).getLsbD i.val = _
  rw [fromRows, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]
  have hi : i.val < (List.ofFn f).length := by simpa only [List.length_ofFn] using i.isLt
  simp only [i.isLt, decide_true, Bool.true_and, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_ofFn]

theorem rows_ext {u v : W} (h : ∀ i : Fin 64, atRow u i = atRow v i) : u = v := by
  ext i hi
  exact h ⟨i,hi⟩

def act (p : Fin 64 → Fin 64) (w : W) : W := fromRows fun i => atRow w (p i)

theorem act_at (p : Fin 64 → Fin 64) (w : W) (i : Fin 64) :
    atRow (act p w) i = atRow w (p i) := read_fromRows _ _

theorem act_inv {p q : Fin 64 → Fin 64} (hp : Function.LeftInverse p q) (w : W) :
    act q (act p w) = w := by
  apply rows_ext; intro i
  simp only [act_at, hp i]

theorem act_zero (p : Fin 64 → Fin 64) : act p 0 = 0 := by
  apply rows_ext; intro i; rw [act_at]; simp [atRow]

theorem act_and (p : Fin 64 → Fin 64) (a b : W) : act p (a &&& b) = act p a &&& act p b := by
  apply rows_ext; intro i; rw [act_at]
  change (a &&& b)[(p i).val] = (act p a &&& act p b)[i.val]
  simp only [BitVec.getElem_and]
  exact congrArg₂ (· && ·) (act_at p a i).symm (act_at p b i).symm

theorem act_op (p : Fin 64 → Fin 64) {a b z : W} (h : z ∈ raw a b) :
    act p z ∈ raw (act p a) (act p b) := by
  simp only [raw, words, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl
  · exact .inl (act_and p a b)
  · right; left; apply rows_ext; intro i; rw [act_at]
    change (a ||| b)[(p i).val] = (act p a ||| act p b)[i.val]
    simp only [BitVec.getElem_or]
    exact congrArg₂ (· || ·) (act_at p a i).symm (act_at p b i).symm
  · right; right; left; apply rows_ext; intro i; rw [act_at]
    change (a &&& ~~~b)[(p i).val] = (act p a &&& ~~~act p b)[i.val]
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    exact congrArg₂ (fun x y : Bool => x && !y) (act_at p a i).symm (act_at p b i).symm
  · right; right; right; apply rows_ext; intro i; rw [act_at]
    change (b &&& ~~~a)[(p i).val] = (act p b &&& ~~~act p a)[i.val]
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    exact congrArg₂ (fun x y : Bool => x && !y) (act_at p b i).symm (act_at p a i).symm

theorem map_build {α β : Type*} [DecidableEq α] [DecidableEq β]
    {ops : α → α → Finset α} {ops' : β → β → Finset β} (f : α → β) (inj : Function.Injective f)
    (hom : ∀ a b z, z ∈ ops a b → f z ∈ ops' (f a) (f b))
    {g : α} {k : ℕ} {s : Finset α} (h : build ops g k s) :
    build ops' (f g) k (s.image f) := by
  induction k generalizing s with
  | zero => exact Finset.mem_image_of_mem f h
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,ne,z,hz,tail⟩
    · exact Or.inl (ih skip)
    · exact Or.inr ⟨f a,Finset.mem_image_of_mem f ha,f b,Finset.mem_image_of_mem f hb,
        fun eq => ne (inj eq), f z, hom a b z hz, by simpa using ih tail⟩

theorem map_live {α β : Type*} [DecidableEq α] [DecidableEq β]
    {ops : α → α → Finset α} {ops' : β → β → Finset β} (f : α → β) (inj : Function.Injective f)
    (hom : ∀ a b z, z ∈ ops a b → f z ∈ ops' (f a) (f b))
    {g : α} {k : ℕ} {s : Finset α} (h : live ops g k s) :
    live ops' (f g) k (s.image f) := by
  induction k generalizing s with
  | zero =>
    change s = {g} at h
    change s.image f = {f g}
    simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,ne,z,hz,hnew,r,hs,tail⟩
    · exact Or.inl (ih skip)
    · refine Or.inr ⟨f a, Finset.mem_image_of_mem f ha, f b, Finset.mem_image_of_mem f hb,
        fun eq => ne (inj eq), f z, hom a b z hz, ?_, r.image f, by simp [hs], by simpa using ih tail⟩
      rintro hm
      obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp hm
      exact hnew (inj eq ▸ hu)

def matching (ws : List W) (j : Fin 64) (p : W) : W :=
  ws.foldl (fun v w => if atRow w j then v &&& w else v &&& ~~~w) p

theorem matching_spec (ws : List W) (i j : Fin 64) (p : W) :
    atRow (matching ws j p) i = true ↔ atRow p i = true ∧
      ∀ w ∈ ws, atRow w i = atRow w j := by
  induction ws generalizing p with
  | nil => simp [matching]
  | cons w ws ih =>
    change atRow (matching ws j (if atRow w j then p &&& w else p &&& ~~~w)) i = true ↔ _
    rw [ih]
    by_cases hj : atRow w j = true
    · rw [if_pos hj]
      unfold atRow at hj ⊢
      simp [hj, List.forall_mem_cons, and_assoc]
    · rw [if_neg hj]
      unfold atRow at hj ⊢
      have jf := Bool.eq_false_iff.mpr hj
      simp [jf, List.forall_mem_cons, and_assoc]

def cutOK (y : W) (neg : List (Fin 64)) (ws : List W) : Bool :=
  neg.all fun j => atRow y j || (matching ws j y == 0)

theorem unequal_predecessor (i j : Fin 64) {a b z : W} (h : z ∈ clean a b)
    (hd : atRow z i ≠ atRow z j) : atRow a i ≠ atRow a j ∨ atRow b i ≠ atRow b j := by
  have hz := (Finset.mem_erase.mp h).2
  simp only [raw, words, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! eq
  rcases eq with ⟨ha,hb⟩
  unfold atRow at *
  rcases hz with rfl | rfl | rfl | rfl <;> simp [ha,hb] at hd

theorem cut_forced {y : W} {k : ℕ} {ws : List W} (h : live clean y k ws.toFinset)
    (neg : List (Fin 64)) : cutOK y neg ws = true := by
  apply List.all_eq_true.mpr
  intro j _
  by_cases hneg : atRow y j = true
  · simp [hneg]
  · have z : matching ws j y = 0 := by
      apply rows_ext; intro i
      by_cases on : atRow (matching ws j y) i = true
      · obtain ⟨hp, same⟩ := (matching_spec ws i j y).mp on
        have opp : atRow y i ≠ atRow y j := fun eq => hneg (eq ▸ hp)
        obtain ⟨u, hu, diff⟩ := live_separates (fun w => atRow w i ≠ atRow w j) opp
          (fun _ _ _ h => unequal_predecessor i j h) h
        exact (diff (same u (List.mem_toFinset.mp hu))).elim
      · simp [atRow] at *
        simpa using on
    simp [hneg,z]

end PEqualNP.Outside.L_meta_13719

namespace PEqualNP.Outside.L_meta_13719

abbrev Debts := List (W × ℕ)

def Feasible (y : W) (k : ℕ) (ws : List W) (ds : Debts) : Prop :=
  ws.Nodup ∧ live clean y k ws.toFinset ∧ ∀ d ∈ ds, Hard y d.1 d.2 ws.toFinset

def debtsAfter (z : W) (ws : List W) (ds : Debts) : Debts := ds.map fun d =>
  (d.1, if freeAt d.1 z ws then d.2 else d.2-1)

theorem after_ok {y a b z : W} {ds : Debts} {ws kept : List W}
    (hard : ∀ d ∈ ds, Hard y d.1 d.2 ws.toFinset)
    (ha : a ∈ ws) (hb : b ∈ ws) (hop : z ∈ clean a b)
    (sub : kept.toFinset ⊆ ws.toFinset) :
    ∀ d ∈ debtsAfter z ws ds, Hard y d.1 d.2 (insert z kept.toFinset) := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  exact nextHard (hard c hc) ha hb (Finset.mem_erase.mp hop).2 sub

def debtOK (y : W) (k : ℕ) (ws : List W) (ds : Debts) : Bool :=
  ds.all fun d => ((y &&& d.1) == 0) ||
    decide (d.2 + (ws.filter fun w => (w &&& d.1) == 0).length ≤ k)

theorem valid_debts {y : W} {k : ℕ} {ws : List W} {ds : Debts}
    (f : Feasible y k ws ds) : debtOK y k ws ds = true := by
  obtain ⟨nd, run, hard⟩ := f
  apply List.all_eq_true.mpr
  intro d hd
  by_cases zero : y &&& d.1 = 0
  · simp [zero]
  · have bound := fits zero (hard d hd) run
    have eq : zeroCount (fun w : W => w &&& d.1) 0 ws.toFinset =
        (ws.filter fun w => (w &&& d.1) == 0).length := by
      unfold zeroCount
      rw [← List.toFinset_card_of_nodup (nd.filter _)]
      congr 1
      ext w
      simp only [Finset.mem_filter,List.mem_toFinset,List.mem_filter,beq_iff_eq]
    rw [eq] at bound
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    exact Or.inr bound

theorem present_nonempty {y : W} {k : ℕ} {ws : List W} {ds : Debts} (f : Feasible y k ws ds) :
    ws.length ≤ k+1 := by
  have h := live_card f.2.1
  simpa only [List.toFinset_card_of_nodup f.1] using h

def rotIndex (d : ℕ) (i : Fin 64) : Fin 64 :=
  if h : i.val < 64 - (d % 64) then ⟨d % 64 + i.val, by omega⟩
  else ⟨i.val - (64 - d % 64), by omega⟩

def swapIndex (d l h : ℕ) (i : Fin 64) : Fin 64 :=
  if atRow (BitVec.ofNat 64 l) i then rotIndex d i else
  if atRow (BitVec.ofNat 64 h) i then rotIndex (64-d%64) i else i

def swapBits (d l h : ℕ) (w : W) : W :=
  let lo := BitVec.ofNat 64 l
  let hi := BitVec.ofNat 64 h
  ((w.rotateRight d) &&& lo) ||| ((w.rotateRight (64-d%64)) &&& ~~~lo &&& hi) |||
    (w &&& ~~~(lo ||| hi))

theorem at_rotate (w : W) (d : ℕ) (i : Fin 64) :
    atRow (w.rotateRight d) i = atRow w (rotIndex d i) := by
  unfold atRow rotIndex
  rw [BitVec.getElem_rotateRight]
  split <;> rfl

theorem at_swap (d l h : ℕ) (w : W) (i : Fin 64) :
    atRow (swapBits d l h w) i = atRow w (swapIndex d l h i) := by
  unfold swapBits swapIndex
  by_cases lo : atRow (BitVec.ofNat 64 l) i = true <;>
    by_cases hi : atRow (BitVec.ofNat 64 h) i = true <;>
    simp only [lo,hi,ite_true,ite_false] <;> unfold atRow at * <;>
    simp [lo,hi,← at_rotate,atRow]
  all_goals unfold rotIndex; split <;> rfl

def permRow : List ℕ → Fin 64 → Fin 64
  | d :: l :: h :: rest, i => permRow rest (swapIndex d l h i)
  | _, i => i

def reorderWord (p : List ℕ) (w : W) : W := act (permRow p) w

def fastPerm : List ℕ → W → W
  | d :: l :: h :: rest, w => swapBits d l h (fastPerm rest w)
  | _, w => w

theorem fastPerm_at : ∀ (p : List ℕ) (w : W) (i : Fin 64),
    atRow (fastPerm p w) i = atRow w (permRow p i)
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | [_,_], _, _ => rfl
  | d :: l :: h :: rest, w, i => (at_swap d l h _ i).trans (fastPerm_at rest w _)

def Symmetry (y : W) (p q : List ℕ) : Prop :=
  (∀ i : Fin 64, permRow p (permRow q i) = i ∧ permRow q (permRow p i) = i) ∧
    reorderWord p y = y ∧ reorderWord q y = y

set_option maxHeartbeats 2000000 in
theorem feasible_transport {y : W} {p q : List ℕ} {k : ℕ} {s t : List W} {d e : Debts}
    (ok : Symmetry y p q)
    (nd : t.Nodup) (bank : t.toFinset = s.toFinset.image (reorderWord p))
    (cost : ∀ c ∈ e, (reorderWord q c.1,c.2) ∈ d)
    (f : Feasible y k s d) : Feasible y k t e := by
  obtain ⟨_, run, old⟩ := f
  have inv : Function.LeftInverse (reorderWord q) (reorderWord p) :=
    act_inv (p := permRow p) (q := permRow q) (fun i => (ok.1 i).1)
  have inv' : Function.LeftInverse (reorderWord p) (reorderWord q) :=
    act_inv (p := permRow q) (q := permRow p) (fun i => (ok.1 i).2)
  have co (a b z : W) (hz : z ∈ clean a b) : reorderWord p z ∈ clean (reorderWord p a) (reorderWord p b) := by
    obtain ⟨nz,hop⟩ := Finset.mem_erase.mp hz
    refine Finset.mem_erase.mpr ⟨?_, act_op (permRow p) hop⟩
    intro eq; apply nz
    apply inv.injective
    exact eq.trans (act_zero (permRow p)).symm
  refine ⟨nd, ?_, ?_⟩
  · have live' := map_live (reorderWord p) inv.injective co run
    rw [ok.2.1] at live'
    simpa only [bank] using live'
  · intro c hc l hl
    have prev := old _ (cost c hc)
    apply prev l
    have run' := map_build (ops := raw) (ops' := raw) (reorderWord q) inv'.injective
      (fun _ _ _ h => act_op (permRow q) h) hl
    have out : reorderWord q (y &&& c.1) = y &&& reorderWord q c.1 := by
      rw [reorderWord, act_and]
      change reorderWord q y &&& reorderWord q c.1 = _
      rw [ok.2.2]
    rw [out] at run'
    apply build_subset run'
    rintro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨nz,mem⟩ := Finset.mem_erase.mp hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp mem
    rw [bank] at hu
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    have nz' : reorderWord q (reorderWord p a &&& c.1) ≠ 0 :=
      fun h => nz (inv'.injective (h.trans (act_zero (permRow q)).symm))
    refine Finset.mem_erase.mpr ⟨nz', Finset.mem_image.mpr ⟨a,ha,?_⟩⟩
    change _ = act (permRow q) (reorderWord p a &&& c.1)
    rw [act_and]
    change _ = reorderWord q (reorderWord p a) &&& reorderWord q c.1
    rw [inv a]

end PEqualNP.Outside.L_meta_13719

namespace PEqualNP.Outside.L_meta_13719

-- Pair and liveness choices from the upstream signed-wire checker in L_meta_9136.
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

abbrev Entry := ℕ × ℕ × ℕ × ℕ
abbrev Sym := List ℕ × List ℕ
abbrev Level := Array Entry
abbrev Catalogue := ℕ × ℕ × ℕ × ℕ
abbrev Hint := ℕ × ℕ

def rowAt (c : Catalogue) (i : ℕ) (h : Hint) : Entry :=
  ((c.2.2.1 >>> (c.2.1*i)) % (2^c.2.1), (c.2.2.2 >>> (32*i)) % (2^32),h.1,h.2)

def parts (bits word : ℕ) : List ℕ :=
  if word = 0 then [] else (List.range (word.log2 / bits + 1)).map fun i =>
    (word >>> (bits * i)) % (2^bits)

def entryBank (dict : ℕ) (e : Entry) : List W :=
  (parts 10 e.1).map fun i => BitVec.ofNat 64 (dict >>> (64*(i-1)))

def entryDebts (masks : List W) (e : Entry) : Debts :=
  masks.zipIdx.map fun mi => (mi.1, (e.2.1 >>> (4*mi.2)) % 16)

def Banned (y : W) (dict : ℕ) (masks : List W) (c : Catalogue) (k n : ℕ) : Prop :=
  ∀ j, j < n → ¬ Feasible y k (entryBank dict (rowAt c j (0,0))) (entryDebts masks (rowAt c j (0,0)))

def findArc (hints : List ℕ) (tag : ℕ) : Option (ℕ × ℕ) :=
  (hints.find? fun v => v % 1024 == tag).map fun v => ((v >>> 10) % 2048, v >>> 21)

def applyRow (p : List ℕ) (w : W) : W := fastPerm p w

theorem applyRow_eq (p : List ℕ) (w : W) : applyRow p w = reorderWord p w := by
  apply rows_ext; intro i
  exact (fastPerm_at p w i).trans (act_at (permRow p) w i).symm

def routeOK (s : List W) (ds : Debts) (t : List W) (dt : Debts) (q : List ℕ) : Bool :=
  decide ((t.map (applyRow q)).Perm s) &&
    dt.all fun c => ds.contains (applyRow q c.1, c.2)

set_option maxHeartbeats 1000000 in
theorem route_ok {y : W} {k : ℕ} {s t : List W} {ds dt : Debts} {p q : List ℕ}
    (sym : Symmetry y p q) (pass : routeOK s ds t dt q = true)
    (h : Feasible y k s ds) : Feasible y k t dt := by
  simp only [routeOK,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.contains_iff_mem] at pass
  have funEq : applyRow q = reorderWord q := funext (applyRow_eq q)
  have perm : (t.map (reorderWord q)).Perm s := funEq ▸ pass.1
  have ok := sym
  have left : Function.LeftInverse (reorderWord q) (reorderWord p) :=
    act_inv (p := permRow p) (q := permRow q) (fun i => (ok.1 i).1)
  have right : Function.LeftInverse (reorderWord p) (reorderWord q) :=
    act_inv (p := permRow q) (q := permRow p) (fun i => (ok.1 i).2)
  apply feasible_transport sym _ _ _ h
  · exact (perm.nodup_iff.mpr h.1).of_map _
  · ext v
    simp only [List.mem_toFinset,Finset.mem_image]
    constructor
    · intro ht
      exact ⟨reorderWord q v, perm.mem_iff.mp (List.mem_map_of_mem ht), right v⟩
    · rintro ⟨a,ha,rfl⟩
      obtain ⟨u,hu,eu⟩ := List.mem_map.mp (perm.mem_iff.mpr ha)
      rw [← eu,right u]
      exact hu
  · intro c hc
    simpa only [applyRow_eq] using pass.2 c hc

def obstruction (y : W) (neg : List (Fin 64)) (which k : ℕ) (s : List W) (ds : Debts) : Bool :=
  match neg[which]? with
  | some j => !(atRow y j || matching s j y == 0)
  | none =>
      match ds[which-neg.length]? with
      | some d => !(((y &&& d.1) == 0) ||
          decide (d.2 + (s.filter fun w => (w &&& d.1) == 0).length ≤ k))
      | none => false

theorem no_obstruction {y : W} {neg : List (Fin 64)} {which k : ℕ} {s : List W} {ds : Debts}
    (f : Feasible y k s ds) : obstruction y neg which k s ds = false := by
  unfold obstruction
  split
  · rename_i j hj
    have hc := cut_forced f.2.1 [j]
    change (((atRow y j || matching s j y == 0) && true) = true) at hc
    simpa only [Bool.and_true,Bool.not_eq_false'] using hc
  · split
    · rename_i d hd
      have h := List.all_eq_true.mp (valid_debts f) d (List.mem_of_getElem? hd)
      simpa only [Bool.not_eq_false'] using h
    · rfl

def checkChild (y : W) (neg : List (Fin 64)) (dict : ℕ) (masks : List W)
    (syms : Array Sym) (prev : Catalogue) (hints : List ℕ) (tag which k : ℕ) (s : List W) (ds : Debts) : Bool :=
  decide (k+1 < s.length) || obstruction y neg which k s ds ||
    match findArc hints tag with
    | none => false
    | some (j,g) =>
        match syms[g]? with
        | some sigma => decide (j < prev.1) &&
            routeOK s ds (entryBank dict (rowAt prev j (0,0))) (entryDebts masks (rowAt prev j (0,0))) sigma.2
        | none => false

theorem child_refuted {y : W} {neg : List (Fin 64)} {dict : ℕ} {masks : List W}
    {syms : Array Sym} {prev : Catalogue} {hints : List ℕ} {tag which k : ℕ} {s : List W} {ds : Debts}
    (symGood : ∀ v ∈ syms, Symmetry y v.1 v.2)
    (smaller : Banned y dict masks prev k prev.1)
    (ok : checkChild y neg dict masks syms prev hints tag which k s ds = true) :
    ¬ Feasible y k s ds := by
  intro f
  have size := present_nonempty f
  simp only [checkChild, Nat.not_lt_of_ge size, decide_false, Bool.false_or, no_obstruction f] at ok
  split at ok
  · contradiction
  · split at ok
    · rename_i v hv
      simp only [Bool.and_eq_true] at ok
      obtain ⟨bound, link⟩ := ok
      exact smaller _ (of_decide_eq_true bound)
        (route_ok (p := v.1) (q := v.2) (symGood v (Array.mem_of_getElem? hv)) link f)
    · contradiction

def patternFor (book groups pair : ℕ) : ℕ :=
  let ix := (groups >>> (11*pair)) % 2048
  (book >>> (80*ix)) % (2^80)

def eachAt {α : Type} (test : ℕ → α → Bool) (start : ℕ) : List α → Bool
  | [] => true
  | x :: xs => test start x && eachAt test (start+1) xs

theorem each_witness {α : Type} {test : ℕ → α → Bool} {start : ℕ} {xs : List α} {x : α}
    (h : eachAt test start xs = true) (mem : x ∈ xs) : ∃ i, test i x = true := by
  induction xs generalizing start with
  | nil => simp at mem
  | cons y ys ih =>
    simp only [eachAt,Bool.and_eq_true] at h
    rcases List.mem_cons.mp mem with rfl | rest
    · exact ⟨start,h.1⟩
    · exact ih h.2 rest

def testPair (y : W) (neg : List (Fin 64)) (dict : ℕ) (masks : List W)
    (syms : Array Sym) (prev : Catalogue) (hints : List ℕ) (book groups k : ℕ) (ws : List W) (ds : Debts)
    (pair : ℕ) (ab : W × W × List W) : Bool :=
  let (a,b,r) := ab
  let pattern := patternFor book groups pair
  eachAt (fun op z => (z == 0) || ws.contains z ||
    eachAt (fun slot kept =>
      let why := (pattern >>> (5*(4*op + slot))) % 32
      checkChild y neg dict masks syms prev hints (1 + 16*pair + 4*op + slot) why
        k (z :: kept) (debtsAfter z ws ds)) 0 (keepChoices a b r)) 0 (words a b)

def checkEntry (y : W) (neg : List (Fin 64)) (dict : ℕ) (masks : List W)
    (syms : Array Sym) (book : ℕ) (prev : Catalogue) (k : ℕ) (e : Entry) : Bool :=
  let ws := entryBank dict e
  let ds := entryDebts masks e
  !ws.contains y && eachAt
    (testPair y neg dict masks syms prev (parts 26 e.2.2.1) book e.2.2.2 k ws ds) 0 (pairs ws)

theorem clean_swap (a b : W) : clean a b = clean b a := by
  have same : raw a b = raw b a := by
    ext z
    simp only [raw,words,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    rw [BitVec.and_comm a b,BitVec.or_comm a b]; tauto
  simp only [clean,same]

set_option maxHeartbeats 1000000 in
theorem entry_refuted {y : W} {neg : List (Fin 64)} {dict : ℕ} {masks : List W}
    {syms : Array Sym} {book : ℕ} {prev : Catalogue} {k : ℕ} {e : Entry}
    (symGood : ∀ v ∈ syms, Symmetry y v.1 v.2)
    (smaller : Banned y dict masks prev k prev.1)
    (ok : checkEntry y neg dict masks syms book prev k e = true) :
    ¬ Feasible y (k+1) (entryBank dict e) (entryDebts masks e) := by
  let ws := entryBank dict e
  let ds := entryDebts masks e
  change (!ws.contains y && eachAt (testPair y neg dict masks syms prev (parts 26 e.2.2.1) book e.2.2.2 k ws ds) 0 (pairs ws)) = true at ok
  simp only [Bool.and_eq_true] at ok
  obtain ⟨no, all⟩ := ok
  change ¬ Feasible y (k+1) ws ds
  rintro ⟨nd,run,hard⟩
  rcases first_live run with terminal | ⟨a,ha,b,hb,ne,z,hop,hn,needed,hs,tail⟩
  · have mem : y ∈ ws.toFinset := terminal ▸ Finset.mem_singleton_self _
    have yc := List.contains_iff_mem.mpr (List.mem_toFinset.mp mem)
    rw [yc] at no
    contradiction
  · obtain ⟨r, found, perm⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) ne
    have go {a b : W} (found : (a,b,r) ∈ pairs ws) (perm : ws.Perm (a :: b :: r))
        (hs : ws.toFinset = insert a (insert b needed)) (hop : z ∈ clean a b) : False := by
      obtain ⟨kept, hk, nk, setk⟩ := recover_kept perm nd hs
      have subset : kept.toFinset ⊆ ws.toFinset := by
        rw [setk,hs]
        exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
      have lack : z ∉ ws := fun h => hn (List.mem_toFinset.mpr h)
      have hzt : (z :: kept).Nodup := List.nodup_cons.mpr
        ⟨fun mem => hn (subset (List.mem_toFinset.mpr mem)),nk⟩
      have fa : a ∈ ws := perm.mem_iff.mpr (by simp)
      have fb : b ∈ ws := perm.mem_iff.mpr (by simp)
      have cf : Feasible y k (z :: kept) (debtsAfter z ws ds) := by
        refine ⟨hzt, ?_, ?_⟩
        · simpa only [List.toFinset_cons,setk] using tail
        · simpa only [List.toFinset_cons] using after_ok hard fa fb hop subset
      obtain ⟨_,selected⟩ := each_witness all found
      change eachAt _ 0 (words a b) = true at selected
      obtain ⟨_,op⟩ := each_witness selected (List.mem_toFinset.mp (Finset.mem_erase.mp hop).2)
      have nz := (Finset.mem_erase.mp hop).1
      have zs : ws.contains z = false := Bool.eq_false_iff.mpr (fun h => lack (List.contains_iff_mem.mp h))
      simp only [beq_eq_false_iff_ne.mpr nz,zs,Bool.false_or] at op
      obtain ⟨_,link⟩ := each_witness op hk
      exact child_refuted symGood smaller link cf
    rcases found with direct | swapped
    · exact go direct perm hs hop
    · apply go swapped (perm.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm])
      rwa [← clean_swap]

end PEqualNP.Outside.L_meta_13719

namespace PEqualNP.Outside.L_meta_13719

theorem build_extend {α : Type*} [DecidableEq α] {o : α → α → Finset α} {y : α}
    {s : Finset α} {a b : ℕ} (le : a ≤ b) (h : build o y a s) : build o y b s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

def indispensable (y : W) (neg : List (Fin 64)) (base : List W) : Bool :=
  base.sublists.all fun ws => (ws == base) || !cutOK y neg ws

theorem cert_lower {y : W} {neg : List (Fin 64)} {base : List W} {ds : Debts} {budget : ℕ}
    (nz : y ≠ 0) (nd : base.Nodup) (full : indispensable y neg base = true)
    (hard : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset)
    (denied : ¬ Feasible y budget base ds)
    {k : ℕ} (run : build raw y k base.toFinset) : budget < k := by
  by_contra! small
  have refined := raw_to_clean nz (build_extend small run)
  obtain ⟨s,sub,hr⟩ := compress refined
  classical
  let ws := base.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (Finset.mem_erase.mp (sub hw)).2
  have hrun : live clean y budget ws.toFinset := eq.symm ▸ hr
  have check := List.all_eq_true.mp full ws (List.mem_sublists.mpr (List.filter_sublist ..))
  have cut := cut_forced hrun neg
  have entire : ws = base := by
    simpa only [cut,Bool.not_true,Bool.or_false,beq_iff_eq] using check
  apply denied
  exact ⟨nd,entire ▸ hrun,hard⟩

theorem lower_by_sample {y target : W} {s t : Finset W} {k : ℕ}
    (p : Fin 64 → Fin 64) (out : act p y = target) (nz : target ≠ 0)
    (avail : project (act p) 0 s ⊆ t)
    (lower : ∀ m, build raw target m t → k ≤ m)
    {l : ℕ} (run : build raw y l s) : k ≤ l := by
  obtain ⟨small,sub,hr⟩ := compress run
  have nonzero : act p y ≠ 0 := out ▸ nz
  obtain ⟨m,pay,projected⟩ := project_live raw raw (act p) 0
    (fun _ _ _ op => raw_simple (act_op p op))
    (fun _ _ _ op => act_op p op) nonzero hr
  rw [out] at projected
  have bound := lower m (build_subset projected ((project_subset _ _ sub).trans avail))
  omega

def auditRows (test : Entry → Bool) (c : Catalogue) (start : ℕ) : List Hint → Bool
  | [] => true
  | h :: rest => test (rowAt c start h) && auditRows test c (start+1) rest

theorem extend_rows {y : W} {neg : List (Fin 64)} {dict : ℕ} {masks : List W}
    {syms : Array Sym} {book : ℕ} {prev cur : Catalogue} {k start : ℕ} {rows : List Hint}
    (symGood : ∀ v ∈ syms, Symmetry y v.1 v.2)
    (smaller : Banned y dict masks prev k prev.1)
    (doneRows : Banned y dict masks cur (k+1) start)
    (ok : auditRows (checkEntry y neg dict masks syms book prev k) cur start rows = true) :
    Banned y dict masks cur (k+1) (start+rows.length) := by
  induction rows generalizing start with
  | nil => simpa using doneRows
  | cons h rs ih =>
    simp only [auditRows,Bool.and_eq_true] at ok
    obtain ⟨pass,tail⟩ := ok
    have denied := entry_refuted symGood smaller pass
    have next : Banned y dict masks cur (k+1) (start+1) := by
      intro j hj
      by_cases lt : j < start
      · exact doneRows j lt
      · have eq : j = start := by omega
        subst j
        exact denied
    have rest := ih next tail
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using rest

end PEqualNP.Outside.L_meta_13719

namespace PEqualNP.Outside.L_meta_13719.Forksix

def y : W := 0xfeeefaaafcccf080

def base : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]

def neg : List (Fin 64) := [0,1,2,3,4,5,6,8,9,10,11,16,17,20,21,24,25,32,34,36,38,40,42,48,52,56]

def dict : ℕ := 0xffffffff00000000ffff0000ffff0000ff00ff00ff00ff00f0f0f0f0f0f0f0f0ccccccccccccccccaaaaaaaaaaaaaaaa

def masks : List W := []

def ds : Debts := []

def syms : Array Sym := #[([],[]),([0x8,0xff000000ff00,0xff000000ff0000,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030],[0x8,0xff000000ff00,0xff000000ff0000,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030]),([0x10,0xffff0000,0xffff00000000,0x1,0x2222222222222222,0x4444444444444444],[0x10,0xffff0000,0xffff00000000,0x1,0x2222222222222222,0x4444444444444444]),([0x10,0xffff0000,0xffff00000000,0x8,0xff000000ff00,0xff000000ff0000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444],[0x18,0xff00ff00,0xff00ff00000000,0x8,0xff000000ff00,0xff000000ff0000,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444]),([0x18,0xff00ff00,0xff00ff00000000,0x8,0xff000000ff00,0xff000000ff0000,0x2,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x1,0x2222222222222222,0x4444444444444444],[0x10,0xffff0000,0xffff00000000,0x8,0xff000000ff00,0xff000000ff0000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050,0x1,0x2222222222222222,0x4444444444444444]),([0x18,0xff00ff00,0xff00ff00000000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x18,0xff00ff00,0xff00ff00000000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050])]

def book : ℕ := 0x8421084210842c084210842108421084280842110842108421084910842084210842108425084211084210842108461084218c6318c6318c6418c6308421084210842308421294a5294a5294a2294a521084210842108621084318c6318c6318c1318c6108421084210843108422108421084210852108439ce739ce739ce339ce75ad6b5ad6b5ad655ad6b00000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (0,1,0x0,0x0)

def c3 : Catalogue := (0,1,0x0,0x0)

def c4 : Catalogue := (0,1,0x0,0x0)

def c5 : Catalogue := (1,53,0x18050100300801,0x0)

def r5_0 : List Hint := [(0,0x380680c0160280480800e0180100500800c01001)]

end PEqualNP.Outside.L_meta_13719.Forksix

namespace PEqualNP.Outside.L_meta_13719.Forksix



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem symGood : ∀ v ∈ syms, Symmetry y v.1 v.2 := by
  have h : ∀ i : Fin syms.size,
      (∀ j : Fin 64, permRow syms[i.val].1 (permRow syms[i.val].2 j) = j ∧
        permRow syms[i.val].2 (permRow syms[i.val].1 j) = j) ∧
      applyRow syms[i.val].1 y = y ∧ applyRow syms[i.val].2 y = y := by decide +kernel
  intro v hv
  obtain ⟨i,hi,rfl⟩ := Array.mem_iff_getElem.mp hv
  simpa only [Symmetry,← applyRow_eq] using h ⟨i,hi⟩

abbrev ban (c : Catalogue) (k n : ℕ) := Banned y dict masks c k n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem empty (c : Catalogue) (k : ℕ) : ban c k 0 := fun j h => (Nat.not_lt_zero j h).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem more {c p : Catalogue} {k start : ℕ} {rows : List Hint}
    (prior : ban p k p.1) (doneRows : ban c (k+1) start) (ok : ck p c k start rows = true) :
    ban c (k+1) (start+rows.length) := extend_rows symGood prior doneRows ok

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0 : ban c0 0 c0.1 := empty c0 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b1 : ban c1 1 c1.1 := empty c1 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b2 : ban c2 2 c2.1 := empty c2 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b3 : ban c3 3 c3.1 := empty c3 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4 : ban c4 4 c4.1 := empty c4 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_0 : ck c4 c5 4 0 r5_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b5 : ban c5 5 c5.1 := by
  have p0 := empty c5 5
  have p1 : ban c5 5 1 := more b4 p0 ok5_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (run : build raw y k base.toFinset) : 6 ≤ k := by
  have denial := b5 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c5 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c5 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    (by simp [ds]) denial run

end PEqualNP.Outside.L_meta_13719.Forksix

namespace PEqualNP.Outside.L_meta_13719

namespace Table

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def ops (a b : W) : List W := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
def basicOps (a b : W) : Finset W := (ops a b).toFinset
def inputs : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def truth : W := 0xfeeefaaafcccf080
def goal : W := ~~~truth
def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277074602 * 2 ^ 32 + 4241289344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def circuit : List Gate := [⟨.and,[1,0]⟩,⟨.and,[4,1]⟩,⟨.and,[5,0]⟩,⟨.or,[6,3]⟩,⟨.or,[8,7]⟩,⟨.and,[9,2]⟩,⟨.or,[11,10]⟩]
theorem monotoneUpper : Monotone2 ⟨circuit,12⟩ ∧
    ∀ x : Fin 6 → Bool, Circuit.eval ⟨circuit,12⟩ (List.ofFn x) = target x := by
  refine ⟨?_, ?_⟩
  · intro g hg
    change g ∈ circuit at hg
    change (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
    simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with h | h | h | h | h | h | h <;> subst g <;> simp
  · decide +kernel
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

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
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
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
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
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
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

theorem source_zero {a b z : W} (h : z ∈ basicOps a b) (one : z[0] = true) :
    a[0] = true ∨ b[0] = true := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp at one <;> tauto


theorem binary_lower
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs,legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    6 ≤ binaryCost gs := by
  have width : inputs.length = 6 := rfl
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have sample : ∀ j : Fin 64, target (fun i => (inputs.getD i.val 0)[j.val]) = bit j (~~~goal) := by
    decide +kernel
  have evaluate (k : Fin 64) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi _
        have hlt : i < inputs.length := by simpa only [width, List.length_ofFn] using hi
        simp only [List.getElem_ofFn,List.getElem_map,x,List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt,Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same,he]
    exact sample k
  obtain ⟨u,hu,run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  rcases hu with rfl | rfl
  · obtain ⟨s,sub,hr⟩ := compress run
    obtain ⟨w,hw,on⟩ := live_separates (fun w : W => w[0] = true)
      (by decide +kernel : goal[0] = true) (fun _ _ _ h => source_zero h) hr
    have none : inputs.all (fun w => !w[0]) = true := by decide +kernel
    have no := List.all_eq_true.mp none w (List.mem_toFinset.mp (sub hw))
    simp [on] at no

  · apply Forksix.lower
    have sameOps : basicOps = raw := rfl
    rw [sameOps] at run
    simpa only [goal,BitVec.not_not,truth,inputs,Forksix.y,Forksix.base] using run

theorem compare
    (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := h
  by_cases has : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g,hm,op⟩ := has
    have less : (C.gates.filter isBinary).length < C.gates.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g,hm,by simp [isBinary,op]⟩
    have count := binary_lower C.gates C.output (fun g hg => fits g hg) computes
    change 6 ≤ (C.gates.filter isBinary).length at count
    obtain ⟨ok,correct⟩ := monotoneUpper
    refine ⟨⟨circuit,12⟩,ok,?_,correct⟩
    change C.gates.length ≤ s at size
    change 7 ≤ s
    omega
  · refine ⟨C,?_,size,computes⟩
    intro g hm
    obtain ⟨ops',ar⟩ := fits g hm
    refine ⟨?_,ar⟩
    change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at ops'
    change g.op = GateOp.and ∨ g.op = GateOp.or
    rcases ops' with a | b | n
    · exact .inl a
    · exact .inr b
    · exact (has ⟨g,hm,n⟩).elim

end Table
end PEqualNP.Outside.L_meta_13719


theorem PEqualNP.Outside.L_meta_13719 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074602 * 2 ^ 32 + 4241289344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074602 * 2 ^ 32 + 4241289344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_13719.Table.compare
