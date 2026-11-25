import PEqualNP.Defs

-- Deleting vertex 3 leaves a seven-vertex graph with an eleven-gate lower bound.
-- Its lower bound uses certificates on induced subgraphs. The extra vertex is
-- essential, so fixing it saves another binary gate. A thirteen-gate monotone
-- witness handles every circuit with a negation. The signed compilation comes
-- from L_meta_9136 and the finite certificate verifier from L_meta_10590.

namespace PEqualNP.Outside.L_meta_14162

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

end PEqualNP.Outside.L_meta_14162

namespace PEqualNP.Outside.L_meta_14162

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

abbrev W := BitVec 128

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

end PEqualNP.Outside.L_meta_14162

namespace PEqualNP.Outside.L_meta_14162

def atRow (w : W) (i : Fin 128) : Bool := w[i.val]

def fromRows (f : Fin 128 → Bool) : W := (BitVec.ofBoolListLE (List.ofFn f)).setWidth 128

theorem read_fromRows (f : Fin 128 → Bool) (i : Fin 128) : atRow (fromRows f) i = f i := by
  change (fromRows f).getLsbD i.val = _
  rw [fromRows, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]
  have hi : i.val < (List.ofFn f).length := by simpa only [List.length_ofFn] using i.isLt
  simp only [i.isLt, decide_true, Bool.true_and, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_ofFn]

theorem rows_ext {u v : W} (h : ∀ i : Fin 128, atRow u i = atRow v i) : u = v := by
  ext i hi
  exact h ⟨i,hi⟩

def act (p : Fin 128 → Fin 128) (w : W) : W := fromRows fun i => atRow w (p i)

theorem act_at (p : Fin 128 → Fin 128) (w : W) (i : Fin 128) :
    atRow (act p w) i = atRow w (p i) := read_fromRows _ _

theorem act_inv {p q : Fin 128 → Fin 128} (hp : Function.LeftInverse p q) (w : W) :
    act q (act p w) = w := by
  apply rows_ext; intro i
  simp only [act_at, hp i]

theorem act_zero (p : Fin 128 → Fin 128) : act p 0 = 0 := by
  apply rows_ext; intro i; rw [act_at]; simp [atRow]

theorem act_and (p : Fin 128 → Fin 128) (a b : W) : act p (a &&& b) = act p a &&& act p b := by
  apply rows_ext; intro i; rw [act_at]
  change (a &&& b)[(p i).val] = (act p a &&& act p b)[i.val]
  simp only [BitVec.getElem_and]
  exact congrArg₂ (· && ·) (act_at p a i).symm (act_at p b i).symm

theorem act_op (p : Fin 128 → Fin 128) {a b z : W} (h : z ∈ raw a b) :
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

def matching (ws : List W) (j : Fin 128) (p : W) : W :=
  ws.foldl (fun v w => if atRow w j then v &&& w else v &&& ~~~w) p

theorem matching_spec (ws : List W) (i j : Fin 128) (p : W) :
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

def cutOK (y : W) (neg : List (Fin 128)) (ws : List W) : Bool :=
  neg.all fun j => atRow y j || (matching ws j y == 0)

theorem unequal_predecessor (i j : Fin 128) {a b z : W} (h : z ∈ clean a b)
    (hd : atRow z i ≠ atRow z j) : atRow a i ≠ atRow a j ∨ atRow b i ≠ atRow b j := by
  have hz := (Finset.mem_erase.mp h).2
  simp only [raw, words, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! eq
  rcases eq with ⟨ha,hb⟩
  unfold atRow at *
  rcases hz with rfl | rfl | rfl | rfl <;> simp [ha,hb] at hd

theorem cut_forced {y : W} {k : ℕ} {ws : List W} (h : live clean y k ws.toFinset)
    (neg : List (Fin 128)) : cutOK y neg ws = true := by
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

end PEqualNP.Outside.L_meta_14162

namespace PEqualNP.Outside.L_meta_14162

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

def rotIndex (d : ℕ) (i : Fin 128) : Fin 128 :=
  if h : i.val < 128 - (d % 128) then ⟨d % 128 + i.val, by omega⟩
  else ⟨i.val - (128 - d % 128), by omega⟩

def swapIndex (d l h : ℕ) (i : Fin 128) : Fin 128 :=
  if atRow (BitVec.ofNat 128 l) i then rotIndex d i else
  if atRow (BitVec.ofNat 128 h) i then rotIndex (128-d%128) i else i

def swapBits (d l h : ℕ) (w : W) : W :=
  let lo := BitVec.ofNat 128 l
  let hi := BitVec.ofNat 128 h
  ((w.rotateRight d) &&& lo) ||| ((w.rotateRight (128-d%128)) &&& ~~~lo &&& hi) |||
    (w &&& ~~~(lo ||| hi))

theorem at_rotate (w : W) (d : ℕ) (i : Fin 128) :
    atRow (w.rotateRight d) i = atRow w (rotIndex d i) := by
  unfold atRow rotIndex
  rw [BitVec.getElem_rotateRight]
  split <;> rfl

theorem at_swap (d l h : ℕ) (w : W) (i : Fin 128) :
    atRow (swapBits d l h w) i = atRow w (swapIndex d l h i) := by
  unfold swapBits swapIndex
  by_cases lo : atRow (BitVec.ofNat 128 l) i = true <;>
    by_cases hi : atRow (BitVec.ofNat 128 h) i = true <;>
    simp only [lo,hi,ite_true,ite_false] <;> unfold atRow at * <;>
    simp [lo,hi,← at_rotate,atRow]
  all_goals unfold rotIndex; split <;> rfl

def permRow : List ℕ → Fin 128 → Fin 128
  | d :: l :: h :: rest, i => permRow rest (swapIndex d l h i)
  | _, i => i

def reorderWord (p : List ℕ) (w : W) : W := act (permRow p) w

def fastPerm : List ℕ → W → W
  | d :: l :: h :: rest, w => swapBits d l h (fastPerm rest w)
  | _, w => w

theorem fastPerm_at : ∀ (p : List ℕ) (w : W) (i : Fin 128),
    atRow (fastPerm p w) i = atRow w (permRow p i)
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | [_,_], _, _ => rfl
  | d :: l :: h :: rest, w, i => (at_swap d l h _ i).trans (fastPerm_at rest w _)

def Symmetry (y : W) (p q : List ℕ) : Prop :=
  (∀ i : Fin 128, permRow p (permRow q i) = i ∧ permRow q (permRow p i) = i) ∧
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

end PEqualNP.Outside.L_meta_14162

namespace PEqualNP.Outside.L_meta_14162

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
  ((c.2.2.1 >>> (c.2.1*i)) % (2^c.2.1), (c.2.2.2 >>> (64*i)) % (2^64),h.1,h.2)

def parts (bits word : ℕ) : List ℕ :=
  if word = 0 then [] else (List.range (word.log2 / bits + 1)).map fun i =>
    (word >>> (bits * i)) % (2^bits)

def entryBank (dict : ℕ) (e : Entry) : List W :=
  (parts 10 e.1).map fun i => BitVec.ofNat 128 (dict >>> (128*(i-1)))

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

def obstruction (y : W) (neg : List (Fin 128)) (which k : ℕ) (s : List W) (ds : Debts) : Bool :=
  match neg[which]? with
  | some j => !(atRow y j || matching s j y == 0)
  | none =>
      match ds[which-neg.length]? with
      | some d => !(((y &&& d.1) == 0) ||
          decide (d.2 + (s.filter fun w => (w &&& d.1) == 0).length ≤ k))
      | none => false

theorem no_obstruction {y : W} {neg : List (Fin 128)} {which k : ℕ} {s : List W} {ds : Debts}
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

def checkChild (y : W) (neg : List (Fin 128)) (dict : ℕ) (masks : List W)
    (syms : Array Sym) (prev : Catalogue) (hints : List ℕ) (tag which k : ℕ) (s : List W) (ds : Debts) : Bool :=
  decide (k+1 < s.length) || obstruction y neg which k s ds ||
    match findArc hints tag with
    | none => false
    | some (j,g) =>
        match syms[g]? with
        | some sigma => decide (j < prev.1) &&
            routeOK s ds (entryBank dict (rowAt prev j (0,0))) (entryDebts masks (rowAt prev j (0,0))) sigma.2
        | none => false

theorem child_refuted {y : W} {neg : List (Fin 128)} {dict : ℕ} {masks : List W}
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

def testPair (y : W) (neg : List (Fin 128)) (dict : ℕ) (masks : List W)
    (syms : Array Sym) (prev : Catalogue) (hints : List ℕ) (book groups k : ℕ) (ws : List W) (ds : Debts)
    (pair : ℕ) (ab : W × W × List W) : Bool :=
  let (a,b,r) := ab
  let pattern := patternFor book groups pair
  eachAt (fun op z => (z == 0) || ws.contains z ||
    eachAt (fun slot kept =>
      let why := (pattern >>> (5*(4*op + slot))) % 32
      checkChild y neg dict masks syms prev hints (1 + 16*pair + 4*op + slot) why
        k (z :: kept) (debtsAfter z ws ds)) 0 (keepChoices a b r)) 0 (words a b)

def checkEntry (y : W) (neg : List (Fin 128)) (dict : ℕ) (masks : List W)
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
theorem entry_refuted {y : W} {neg : List (Fin 128)} {dict : ℕ} {masks : List W}
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

end PEqualNP.Outside.L_meta_14162

namespace PEqualNP.Outside.L_meta_14162

theorem build_extend {α : Type*} [DecidableEq α] {o : α → α → Finset α} {y : α}
    {s : Finset α} {a b : ℕ} (le : a ≤ b) (h : build o y a s) : build o y b s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

def indispensable (y : W) (neg : List (Fin 128)) (base : List W) : Bool :=
  base.sublists.all fun ws => (ws == base) || !cutOK y neg ws

theorem cert_lower {y : W} {neg : List (Fin 128)} {base : List W} {ds : Debts} {budget : ℕ}
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
    (p : Fin 128 → Fin 128) (out : act p y = target) (nz : target ≠ 0)
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

theorem extend_rows {y : W} {neg : List (Fin 128)} {dict : ℕ} {masks : List W}
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

end PEqualNP.Outside.L_meta_14162

namespace PEqualNP.Outside.L_meta_14162

def sampleRow (code : ℕ) (i : Fin 128) : Fin 128 := ⟨(code >>> (7*i.val)) % 128, Nat.mod_lt _ (by decide)⟩

theorem essential_sample {y target v : W} {s t : List W} {need : ℕ}
    (p : Fin 128 → Fin 128) (i j : Fin 128) (diff : atRow y i ≠ atRow y j)
    (sing : s.all (fun w => (atRow w i == atRow w j) || (w == v)) = true)
    (free : act p v = 0) (out : act p y = target) (nz : target ≠ 0)
    (avail : project (act p) 0 s.toFinset ⊆ t.toFinset)
    (bound : ∀ k, build raw target k t.toFinset → need ≤ k)
    (l : ℕ) (run : build raw y l s.toFinset) : need+1 ≤ l := by
  have hn : y ≠ 0 := by rintro rfl; exact diff (by simp [atRow])
  obtain ⟨bank,sub,live'⟩ := compress (raw_to_clean hn run)
  obtain ⟨u,hu,ev⟩ := live_separates (fun w => atRow w i ≠ atRow w j) diff
    (fun _ _ _ hop => unequal_predecessor i j hop) live'
  have chk := List.all_eq_true.mp sing u (List.mem_toFinset.mp (Finset.mem_erase.mp (sub hu)).2)
  simp only [Bool.or_eq_true,beq_iff_eq] at chk
  have hv : v ∈ bank := chk.resolve_left ev ▸ hu
  have cost : 0 < zeroCount (act p) 0 bank :=
    Finset.card_pos.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,free⟩⟩
  obtain ⟨m,pay,rb⟩ := project_live clean raw (act p) 0
    (fun _ _ _ h => raw_simple (act_op p (Finset.mem_erase.mp h).2))
    (fun _ _ _ h => act_op p (Finset.mem_erase.mp h).2) (out ▸ nz) live'
  rw [out] at rb
  have sub' : bank ⊆ s.toFinset := sub.trans (Finset.erase_subset _ _)
  have lower := bound m (build_subset rb ((project_subset _ _ sub').trans avail))
  omega
end PEqualNP.Outside.L_meta_14162

namespace PEqualNP.Outside.L_meta_14162.G41

def y : W := 0xe8

def base : List W := [0xaa,0xcc,0xf0]

def neg : List (Fin 128) := [0,1,2,4]

def dict : ℕ := 0xf0000000000000000000000000000000cc000000000000000000000000000000aa

def masks : List W := []

def ds : Debts := []

def syms : Array Sym := #[([],[]),([0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030],[0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030]),([0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444],[0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444]),([0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444],[0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444]),([0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444],[0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444]),([0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050],[0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050])]

def book : ℕ := 0x844108c2108c42084211082210c4210c211084218c23188631882118c6300000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (0,1,0x0,0x0)

def c3 : Catalogue := (1,22,0x300801,0x0)

def r3_0 : List Hint := [(0,0xc01001)]

end PEqualNP.Outside.L_meta_14162.G41

namespace PEqualNP.Outside.L_meta_14162.G41



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem symGood : ∀ v ∈ syms, Symmetry y v.1 v.2 := by
  have h : ∀ i : Fin syms.size,
      (∀ j : Fin 128, permRow syms[i.val].1 (permRow syms[i.val].2 j) = j ∧
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
theorem ok3_0 : ck c2 c3 2 0 r3_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b3 : ban c3 3 c3.1 := by
  have p0 := empty c3 3
  have p1 : ban c3 3 1 := more b2 p0 ok3_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (run : build raw y k base.toFinset) : 4 ≤ k := by
  have denial := b3 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c3 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c3 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    (by simp [ds]) denial run

end PEqualNP.Outside.L_meta_14162.G41

namespace PEqualNP.Outside.L_meta_14162.G29

def y : W := 0xeea0

def base : List W := [0xaaaa,0xcccc,0xf0f0,0xff00]

def neg : List (Fin 128) := [0,1,2,3,4,6,8,12]

def dict : ℕ := 0xff000000000000000000000000000000f0f00000000000000000000000000000cccc0000000000000000000000000000aaaa

def masks : List W := []

def ds : Debts := []

def syms : Array Sym := #[([],[]),([0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0x7,0xaa00aa00aa00aa00aa00aa00aa00aa,0x55005500550055005500550055005500],[0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0x7,0xaa00aa00aa00aa00aa00aa00aa00aa,0x55005500550055005500550055005500])]

def book : ℕ := 0x8421084210842508421084210842108422084210842108421084230842110842108421084110842318c6318c6318c1318c62108421084210852108400000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (0,1,0x0,0x0)

def c3 : Catalogue := (1,33,0x100300801,0x0)

def r3_0 : List Hint := [(0,0x300500800c01001)]

end PEqualNP.Outside.L_meta_14162.G29

namespace PEqualNP.Outside.L_meta_14162.G29



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem symGood : ∀ v ∈ syms, Symmetry y v.1 v.2 := by
  have h : ∀ i : Fin syms.size,
      (∀ j : Fin 128, permRow syms[i.val].1 (permRow syms[i.val].2 j) = j ∧
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
theorem ok3_0 : ck c2 c3 2 0 r3_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b3 : ban c3 3 c3.1 := by
  have p0 := empty c3 3
  have p1 : ban c3 3 1 := more b2 p0 ok3_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (run : build raw y k base.toFinset) : 4 ≤ k := by
  have denial := b3 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c3 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c3 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    (by simp [ds]) denial run

end PEqualNP.Outside.L_meta_14162.G29

namespace PEqualNP.Outside.L_meta_14162.G57

def y : W := 0xeea8
def base : List W := [0xaaaa,0xcccc,0xf0f0,0xff00]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (run : build raw y k base.toFinset) : 5 ≤ k := by
  apply essential_sample (v := 0xf0f0) (sampleRow 0x16284880608080)
    1 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G41.lower k run

end PEqualNP.Outside.L_meta_14162.G57

namespace PEqualNP.Outside.L_meta_14162.G61

def y : W := 0xfefaeea0

def base : List W := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def neg : List (Fin 128) := [0,1,2,3,4,6,8,12,16,18,24]

def dict : ℕ := 0xfffff0f0000000000000000000000000ffff0000000000000000000000000000ff00ff00000000000000000000000000fafafafa000000000000000000000000f0f0f0f0000000000000000000000000f0f0a0a0000000000000000000000000eeeeeeee000000000000000000000000cccceeee000000000000000000000000cccccccc000000000000000000000000aaaaaaaa00000000000000000000000000ee00ee0000000000000000000000000000fafa0000000000000000000000000000aaaa

def masks : List W := [0xffff,0x330033,0xf0f0f0f,0x33333333]

def ds : Debts := [(0xffff,4),(0x330033,4),(0xf0f0f0f,4),(0x33333333,5)]

def syms : Array Sym := #[([],[]),([0xc,0xf0f00000f0f00000f0f00000f0f0,0xf0f00000f0f00000f0f00000f0f0000],[0xc,0xf0f00000f0f00000f0f00000f0f0,0xf0f00000f0f00000f0f00000f0f0000])]

def book : ℕ := 0x584816a0210a08458421619836318c629836318c63181631816318263181619836318c61d836318c590242208422021590846a02841108410216a1086318c630c5631856318c08421084250842508421210842108421087210845ad6b5ad685ad6b5ad6b421084210842105421084210842108421074210821086210842108421086421084210842104421081084210842108471084200000000000000400001210842108421088210844210842108421094210808421084280842108428318cc318c6318c6318c621084210842108421084084210842108421084210842108422084210842242108421084210842108318c6318c7318c7318c6318c6318c6318c6318c639ce139ce739ce739ce721084210842108521084605816318c625896318c084810a0210a084084216318c63021630a56318c39c273a8e73a82139ce76318c63180630216318c5282a51d4a51c215294a294252a4a52a421294a56318c63042630216318c4a42949529494214a52908421084210842708421084210842108425084210000000000000010000c2108421084210812108442108421084210142108318c6318c6318c5318c6000000000000005000000000000000000020000008421084220842108421084210842008421084210842108423084210842121084210802108421084084210842108429084210842108421084280842108421084210842a08421084210842108422084210842108421084230842110842108421084110842318c6318c6318c1318c6318c6318c6318c9318c60842108421084240842100000000000000100000294a5294a5294a1294a54a5294a5294a5214a52908421084240842108421084210842508421084216318c6318c6318c6318c00000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (0,1,0x0,0x0)

def c3 : Catalogue := (0,1,0x0,0x0)

def c4 : Catalogue := (4,44,0xc02c0901804b0240501002c02c0801404c0240701003,0x4233000000000000332300000000000033230000000000004242)

def r4_0 : List Hint := [(0,0x380600c0140200000600800801),
  (0,0x780e01a02c0600b01202804808),
  (0,0xa80c0280180301402604808810),
  (0,0xd80703400c0c80903004c0b816)]

def c5 : Catalogue := (4,54,0xd0300b0240501300b0240501001c02c0a0240501000c02c0901c04,0x4434000000000000433400000000000044330000000000005343)

def r5_0 : List Hint := [(0x5a,0x120230440841001f03c0740e001),
  (0x23642004d1,0x6c1582a00e0681480b0180a00581803009c13025),
  (0xc15,0xc81881a04a0300583002e05c1782b0540b81682c),
  (0,0xac1c8380560dc1b02804a0301a83406002819825)]

def c6 : Catalogue := (1,44,0xc02c0901404,0x5444)

def r6_0 : List Hint := [(0x322000083c08010e020081c0001060000006,0x120400440fc1f03d0780741d83a)]

end PEqualNP.Outside.L_meta_14162.G61

namespace PEqualNP.Outside.L_meta_14162.G61



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem symGood : ∀ v ∈ syms, Symmetry y v.1 v.2 := by
  have h : ∀ i : Fin syms.size,
      (∀ j : Fin 128, permRow syms[i.val].1 (permRow syms[i.val].2 j) = j ∧
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
theorem ok4_0 : ck c3 c4 3 0 r4_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4 : ban c4 4 c4.1 := by
  have p0 := empty c4 4
  have p1 : ban c4 4 4 := more b3 p0 ok4_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_0 : ck c4 c5 4 0 r5_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b5 : ban c5 5 c5.1 := by
  have p0 := empty c5 5
  have p1 : ban c5 5 4 := more b4 p0 ok5_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_0 : ck c5 c6 5 0 r6_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b6 : ban c6 6 c6.1 := by
  have p0 := empty c6 6
  have p1 : ban c6 6 1 := more b5 p0 ok6_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem withDebts (hard : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset) (k : ℕ) (run : build raw y k base.toFinset) : 7 ≤ k := by
  have denial := b6 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c6 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c6 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    hard denial run

end PEqualNP.Outside.L_meta_14162.G61

namespace PEqualNP.Outside.L_meta_14162.G61

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain0 : Hard y 0xffff 4 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x1e3868c16284880e182840608080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G29.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain1 : Hard y 0x330033 4 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x2a508900a10080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G41.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain2 : Hard y 0xf0f0f0f 4 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x3668c98162848826488900608080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G29.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain3 : Hard y 0x33333333 5 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x3a70c982a508901a304880a10080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G57.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem initial : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset := by
  intro d hd
  simp only [ds,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact domain0
  · exact domain1
  · exact domain2
  · exact domain3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (h : build raw y k base.toFinset) : 7 ≤ k := withDebts initial k h

end PEqualNP.Outside.L_meta_14162.G61

namespace PEqualNP.Outside.L_meta_14162.G107

def y : W := 0xffecfea0

def base : List W := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def neg : List (Fin 128) := [0,1,2,3,4,6,8,16,17,20]

def dict : ℕ := 0xffffff00000000000000000000000000ffffee00000000000000000000000000ffffaaaa000000000000000000000000ffff0000000000000000000000000000ffeeffee000000000000000000000000ffccffcc000000000000000000000000ffaaffaa000000000000000000000000ff00ff00000000000000000000000000f0f0f0f0000000000000000000000000eeeeeeee000000000000000000000000ee00ee00000000000000000000000000cccccccc000000000000000000000000aaaaffaa000000000000000000000000aaaaaaaa00000000000000000000000000ee00ee0000000000000000000000000000ffee0000000000000000000000000000ffcc0000000000000000000000000000ffaa0000000000000000000000000000ff000000000000000000000000000000cfcc00000000000000000000000000000f00

def masks : List W := [0x3333,0xffff,0x5050505,0xf0f0f0f,0x33333333,0x55555555]

def ds : Debts := [(0x3333,4),(0xffff,5),(0x5050505,4),(0xf0f0f0f,5),(0x33333333,5),(0x55555555,5)]

def syms : Array Sym := #[([],[]),([0xe,0xcccc0000cccc0000cccc0000cccc,0x33330000333300003333000033330000],[0xe,0xcccc0000cccc0000cccc0000cccc,0x33330000333300003333000033330000]),([0xc,0xf0f00000f0f00000f0f00000f0f0,0xf0f00000f0f00000f0f00000f0f0000,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444],[0xc,0xf0f00000f0f00000f0f00000f0f0,0xf0f00000f0f00000f0f00000f0f0000,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444]),([0xf,0xaaaa0000aaaa0000aaaa0000aaaa,0x55550000555500005555000055550000,0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444],[0xc,0xf0f00000f0f00000f0f00000f0f0,0xf0f00000f0f00000f0f00000f0f0000,0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444]),([0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050],[0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050]),([0xe,0xcccc0000cccc0000cccc0000cccc,0x33330000333300003333000033330000,0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050],[0xe,0xcccc0000cccc0000cccc0000cccc,0x33330000333300003333000033330000,0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050]),([0xc,0xf0f00000f0f00000f0f00000f0f0,0xf0f00000f0f00000f0f00000f0f0000,0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444],[0xf,0xaaaa0000aaaa0000aaaa0000aaaa,0x55550000555500005555000055550000,0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444]),([0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0xf,0xaaaa0000aaaa0000aaaa0000aaaa,0x55550000555500005555000055550000],[0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0xf,0xaaaa0000aaaa0000aaaa0000aaaa,0x55550000555500005555000055550000])]

def book : ℕ := 0x508c211c4211cc65084250ca3620631a0a550c63084816182109884604215184651cc651c42518c639c47518e73984251ce761866524c632463518c651465624a52a463514a52102461884218216108461826610c661021618c651906614c631505518c65294a5294a529475294a5294a52842528a55294a421284190841926421085294052940529425294651d475294a519465294a519435294a525435294a5294a52842528635294a4a50949929499064a5295294a528c5529055294a318c6318c6328c6318c60b0c608421084c60b0215294a528e7528c65294a230c621084210c6230841286310842108631284218cc31a0631a0c618c63605816318c621886318c6318c6318c605816318c3184631cc631c42318c631cc731946318c631d47420684190841863421086318c63021630636318c619836318c631836318c21184210842108421084631816318c6318c6318c63186631866318163186619866318c631886318c5294a52842528c65294a5294a5298c529855294a605816318c619866318c5294a528c6528425294a084210848408421084846318c630c6630216318c52941529415294252946521425294a529425294a5314c5294a531435294a6318c6318c6318c6318c5294a5298c529835294a615816318c631816318c631816318663181631865294a5298c5294a5294a084210842108427084216318c6318c631836318c08421084230842308421318c6318c6318c3318c621084210852108521084318c6318c6318c5318c6318c6318c2318c6318c608481098210988408421501405294a519465294a501405294a511445294a2102421884218212108431826310c631021318c65294a52800528215294a18c63194211946318c235294a52800528c65294a294a528c8328ca529485108421084210845108421084210842108491084218c6318c6618c6318c63318c6318c6318c8318c618c6318c6318c6318c635294a529425294a5294a084210842808421084285294a529445294a5294a0000000000000020000a5294a5294a5294a5294a42108421084210842108318c6318c1318c6318c6318c6318c7318c6318c6318c6318c4318c6318c61084210842108471084208421084210842408421318c6318c6318c6318c6318c6318c7318c6318c72108621084210862108410842108461084210846631876318c6318c6318c529445294a5294a5294a1084210842108421084a0842108421084210842c39ce739ce739ce739ce710842108421084110842294a6294a5294a5294a5210842108421086210841084a1084210842108420842c084210842108421000000000000002000066318c631866318c6318c5294a529465294a5294a631826318c6318c6318c084210842108421084214a5264a5294a5294a529084210842108426084210842108421084230842a318c6318c6318c7318c639ce739ce739ce639ce718c6318c6918c6318c63210842108421084210840842108426084210842639ce739ce739ce839ce7084210842108422084211084210841108421084200000000000000400000000000000000002000000000000000000030000000000000000000100000318c6318c6318c1318c6000000000000005000000842108420084210842108421084250842108421318c6318c0318c6318c610842108431084210842108421084210846108420842108421084250842139ce739ce739ce439ce7318c6318c6318c2318c639ce739ce739ce539ce7084210842108423084211084210842108431084221084210842108821084000000000000001000062108421084210852108400000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (0,1,0x0,0x0)

def c3 : Catalogue := (0,1,0x0,0x0)

def c4 : Catalogue := (3,45,0x380d02808009c068140400d40380d02808,0x23323300000000003322330000000000332233)

def r4_0 : List Hint := [(0,0x500901001c0300500800c01001),
  (0,0xa0130240440800f01c0340600b),
  (0,0xa0130240440101102c0540600b)]

def c5 : Catalogue := (10,55,0x240701a0501204400e0340a02005001c068140400b20380d02808012a0701a0501001c80e0340a02001901c068140400f20440e0340a02240701a058140454130380d02808,0x433343000000000034324400000000003432440000000000433343000000000033325400000000003343430000000000443333000000000044333300000000004433330000000000433354)

def r5_0 : List Hint := [(0,0x841001f03c0400d81d03806c0281a03205c0c017),
  (0x2d4400095,0x9c0480804c0801282400c0141180400600811001),
  (0x13a44004ad,0xb00f0190120ac04807054058028040320a408028),
  (0,0x9c0480800e09c0280404e0401402f0400601702d),
  (0,0xd0048330480040280404e008008320400c818830),
  (0,0x481b07406c02804036040008390700dc1b035),
  (0,0xd02101e048014028410800401f83e07a0f01883b),
  (0,0x2584a0921202384607211422043),
  (0,0x280420001002784e008040268390720542600b),
  (0x400869,0x1480481e0480140285107a0ac1884f0800401f819)]

def c6 : Catalogue := (3,55,0x120380d0280800e40781c0681404480e0340c02808,0x44435400000000005444430000000000554444)

def r6_0 : List Hint := [(0x28042bc000cab000229c0004a308001dcc00037,0x1802f85e0ba1702d85a0b21602b8560aa1501c853),
  (0x63ac2008e710082bc401cad08061f8000876380011cc0143f30050bcc00007,0x1b4360570d61a82f0690d019c330650c818c31061),
  (0x539800144600040ac802427200402c002407,0x1e83c8780ee1d83a8740e611c390710721c03786e)]

def c7 : Catalogue := (1,45,0x120380d02808,0x555454)

def r7_0 : List Hint := [(0x2270600498280022040088020011e0200860100116080004808000e0c0083000010a0000008,0x420831042044007f0fc1f43e07b)]

end PEqualNP.Outside.L_meta_14162.G107

namespace PEqualNP.Outside.L_meta_14162.G107



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem symGood : ∀ v ∈ syms, Symmetry y v.1 v.2 := by
  have h : ∀ i : Fin syms.size,
      (∀ j : Fin 128, permRow syms[i.val].1 (permRow syms[i.val].2 j) = j ∧
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
theorem ok4_0 : ck c3 c4 3 0 r4_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4 : ban c4 4 c4.1 := by
  have p0 := empty c4 4
  have p1 : ban c4 4 3 := more b3 p0 ok4_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_0 : ck c4 c5 4 0 r5_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b5 : ban c5 5 c5.1 := by
  have p0 := empty c5 5
  have p1 : ban c5 5 10 := more b4 p0 ok5_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_0 : ck c5 c6 5 0 r6_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b6 : ban c6 6 c6.1 := by
  have p0 := empty c6 6
  have p1 : ban c6 6 3 := more b5 p0 ok6_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_0 : ck c6 c7 6 0 r7_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b7 : ban c7 7 c7.1 := by
  have p0 := empty c7 7
  have p1 : ban c7 7 1 := more b6 p0 ok7_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem withDebts (hard : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset) (k : ℕ) (run : build raw y k base.toFinset) : 8 ≤ k := by
  have denial := b7 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c7 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c7 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    hard denial run

end PEqualNP.Outside.L_meta_14162.G107

namespace PEqualNP.Outside.L_meta_14162.G107

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain0 : Hard y 0x3333 4 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x1a304880a10080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G41.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain1 : Hard y 0xffff 5 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x1e1c7061a14604160c5021204400)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G57.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain2 : Hard y 0x5050505 4 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x34609101420100)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G41.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain3 : Hard y 0xf0f0f0f 5 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x364cc913448c10160c4811408400)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G57.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain4 : Hard y 0x33333333 5 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x3a54e141a146043244c101204400)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G57.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain5 : Hard y 0x55555555 5 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x3c58e143448c101c186041408400)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G57.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem initial : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset := by
  intro d hd
  simp only [ds,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact domain0
  · exact domain1
  · exact domain2
  · exact domain3
  · exact domain4
  · exact domain5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (h : build raw y k base.toFinset) : 8 ≤ k := withDebts initial k h

end PEqualNP.Outside.L_meta_14162.G107

namespace PEqualNP.Outside.L_meta_14162.G117

def y : W := 0xffeceae0

def base : List W := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def neg : List (Fin 128) := [0,1,2,3,4,8,10,12,16,17,20]

def dict : ℕ := 0xffff0000000000000000000000000000ff00ff00000000000000000000000000fafafafa000000000000000000000000f0f0f0f0000000000000000000000000eeeeeeee000000000000000000000000cccccccc000000000000000000000000aaaaaaaa000000000000000000000000aaa0aaa00000000000000000000000000000ffcc

def masks : List W := [0xffff,0xff00ff,0xf0f0f0f,0x33333333,0x55555555]

def ds : Debts := [(0xffff,4),(0xff00ff,4),(0xf0f0f0f,4),(0x33333333,4),(0x55555555,4)]

def syms : Array Sym := #[([],[]),([0x4,0xf000f000f000f000f000f000f000f0,0xf000f000f000f000f000f000f000f00,0xe,0xcccc0000cccc0000cccc0000cccc,0x33330000333300003333000033330000],[0x4,0xf000f000f000f000f000f000f000f0,0xf000f000f000f000f000f000f000f00,0xe,0xcccc0000cccc0000cccc0000cccc,0x33330000333300003333000033330000]),([0x8,0xff000000ff000000ff000000ff00,0xff000000ff000000ff000000ff0000,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444],[0x8,0xff000000ff000000ff000000ff00,0xff000000ff000000ff000000ff0000,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444]),([0x4,0xf000f000f000f000f000f000f000f0,0xf000f000f000f000f000f000f000f00,0xf,0xaaaa0000aaaa0000aaaa0000aaaa,0x55550000555500005555000055550000,0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444],[0xc,0xf0f00000f0f00000f0f00000f0f0,0xf0f00000f0f00000f0f00000f0f0000,0x6,0xcc00cc00cc00cc00cc00cc00cc00cc,0x33003300330033003300330033003300,0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444]),([0x6,0xcc00cc00cc00cc00cc00cc00cc00cc,0x33003300330033003300330033003300,0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050],[0x6,0xcc00cc00cc00cc00cc00cc00cc00cc,0x33003300330033003300330033003300,0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050]),([0x8,0xff000000ff000000ff000000ff00,0xff000000ff000000ff000000ff0000,0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0x7,0xaa00aa00aa00aa00aa00aa00aa00aa,0x55005500550055005500550055005500,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444],[0xe,0xcccc0000cccc0000cccc0000cccc,0x33330000333300003333000033330000,0x6,0xcc00cc00cc00cc00cc00cc00cc00cc,0x33003300330033003300330033003300,0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444]),([0xc,0xf0f00000f0f00000f0f00000f0f0,0xf0f00000f0f00000f0f00000f0f0000,0x7,0xaa00aa00aa00aa00aa00aa00aa00aa,0x55005500550055005500550055005500],[0xc,0xf0f00000f0f00000f0f00000f0f0,0xf0f00000f0f00000f0f00000f0f0000,0x7,0xaa00aa00aa00aa00aa00aa00aa00aa,0x55005500550055005500550055005500]),([0xe,0xcccc0000cccc0000cccc0000cccc,0x33330000333300003333000033330000,0x6,0xcc00cc00cc00cc00cc00cc00cc00cc,0x33003300330033003300330033003300,0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444],[0x8,0xff000000ff000000ff000000ff00,0xff000000ff000000ff000000ff0000,0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0x7,0xaa00aa00aa00aa00aa00aa00aa00aa,0x55005500550055005500550055005500,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444]),([0xc,0xf0f00000f0f00000f0f00000f0f0,0xf0f00000f0f00000f0f00000f0f0000,0x6,0xcc00cc00cc00cc00cc00cc00cc00cc,0x33003300330033003300330033003300,0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444],[0x4,0xf000f000f000f000f000f000f000f0,0xf000f000f000f000f000f000f000f00,0xf,0xaaaa0000aaaa0000aaaa0000aaaa,0x55550000555500005555000055550000,0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050,0x1,0x22222222222222222222222222222222,0x44444444444444444444444444444444]),([0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0xf,0xaaaa0000aaaa0000aaaa0000aaaa,0x55550000555500005555000055550000],[0x2,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x30303030303030303030303030303030,0xf,0xaaaa0000aaaa0000aaaa0000aaaa,0x55550000555500005555000055550000])]

def book : ℕ := 0x58ca3620631a0a558c63588e26a442124e7588426054169821099466042159c47720e73a04259ce76206871d0841c63621086a44971129490426a529594657a8a52a863594a56282a7954a514216294a69826790c631021698c6711247988421926710841084310842108431084208421084210842a0842110842108421084210842210882108421084210882108421084210832108421084210842108121084294a5294a5294a5294a518c6318c6418c6318c632108421084210892108408421084210842508421084210842108427084210842108421084260842110842108451084210845084210842108421084210842108421084220842508421084210842308421108421084210843108420842108428084210842821084210842108421084318c9318c6318c6318c6000000000000004000000000000000000030000000000000000000200000108421084210841108420000000000000010000008421084210842208421108421084110842108421084210843108421084210842108421084510842108421084210847108421084210842108461084221084210842108221084210842108421087210844210842108421024210821084210842108a2108421084210842108521084108421084210844108422108421084210862108400000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (0,1,0x0,0x0)

def c3 : Catalogue := (0,1,0x0,0x0)

def c4 : Catalogue := (2,44,0x80180400c0190200601002,0x232330000000000032332)

def r4_0 : List Hint := [(0,0x500901001c0300500800c01001),
  (0,0x90110200380780e01a0300380b)]

def c5 : Catalogue := (2,54,0x9020070180400e4080180501003,0x434330000000000044333)

def r5_0 : List Hint := [(0x1801264800091,0x740e01b0340540c81802e0340a01602a03c0a013),
  (0,0x74130150380941200702e08c0b8220420800f81e)]

def c6 : Catalogue := (1,44,0x90200601003,0x44444)

def r6_0 : List Hint := [(0x1801260e0008820001e1000468300016040044808000e02004280001060000008,0x1802f05c0b41602b0540a414027)]

end PEqualNP.Outside.L_meta_14162.G117

namespace PEqualNP.Outside.L_meta_14162.G117



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem symGood : ∀ v ∈ syms, Symmetry y v.1 v.2 := by
  have h : ∀ i : Fin syms.size,
      (∀ j : Fin 128, permRow syms[i.val].1 (permRow syms[i.val].2 j) = j ∧
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
theorem ok4_0 : ck c3 c4 3 0 r4_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4 : ban c4 4 c4.1 := by
  have p0 := empty c4 4
  have p1 : ban c4 4 2 := more b3 p0 ok4_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_0 : ck c4 c5 4 0 r5_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b5 : ban c5 5 c5.1 := by
  have p0 := empty c5 5
  have p1 : ban c5 5 2 := more b4 p0 ok5_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_0 : ck c5 c6 5 0 r6_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b6 : ban c6 6 c6.1 := by
  have p0 := empty c6 6
  have p1 : ban c6 6 1 := more b5 p0 ok6_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem withDebts (hard : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset) (k : ℕ) (run : build raw y k base.toFinset) : 7 ≤ k := by
  have denial := b6 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c6 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c6 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    hard denial run

end PEqualNP.Outside.L_meta_14162.G117

namespace PEqualNP.Outside.L_meta_14162.G117

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain0 : Hard y 0xffff 4 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x1e3868c0e1828416284880608080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G29.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain1 : Hard y 0xff00ff 4 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x2e54b140e1430426449100604100)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G29.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain2 : Hard y 0xf0f0f0f 4 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x364cc913448c10160c4811408400)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G29.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain3 : Hard y 0x33333333 4 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x3a7068c32604882a502842240080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G29.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain4 : Hard y 0x55555555 4 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x3c70b1434609101c303041420100)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G29.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem initial : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset := by
  intro d hd
  simp only [ds,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · exact domain0
  · exact domain1
  · exact domain2
  · exact domain3
  · exact domain4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (h : build raw y k base.toFinset) : 7 ≤ k := withDebts initial k h

end PEqualNP.Outside.L_meta_14162.G117

namespace PEqualNP.Outside.L_meta_14162.G63

def y : W := 0xfffeffeefefeaa00
def base : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (run : build raw y k base.toFinset) : 8 ≤ k := by
  apply essential_sample (v := 0xcccccccccccccccc) (sampleRow 0x7af1cb86ad18b05ab14a84a910a03a70c982a508901a304880a10080)
    16 18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G61.lower k run

end PEqualNP.Outside.L_meta_14162.G63

namespace PEqualNP.Outside.L_meta_14162.G111

def y : W := 0xfffffefcffeeaa00
def base : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (run : build raw y k base.toFinset) : 9 ≤ k := by
  apply essential_sample (v := 0xf0f0f0f0f0f0f0f0) (sampleRow 0x76e9cb866c98b056a94a846890a03668c98264889016284880608080)
    32 36 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G107.lower k run

end PEqualNP.Outside.L_meta_14162.G111

namespace PEqualNP.Outside.L_meta_14162.G103

def y : W := 0xfffcee00
def base : List W := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (run : build raw y k base.toFinset) : 6 ≤ k := by
  apply essential_sample (v := 0xf0f0f0f0) (sampleRow 0x364cc913448c10160c4811408400)
    16 20 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G57.lower k run

end PEqualNP.Outside.L_meta_14162.G103

namespace PEqualNP.Outside.L_meta_14162.G115

def y : W := 0xffeceee0
def base : List W := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (run : build raw y k base.toFinset) : 6 ≤ k := by
  apply essential_sample (v := 0xf0f0f0f0) (sampleRow 0x364cc913448c10160c4811408400)
    1 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G57.lower k run

end PEqualNP.Outside.L_meta_14162.G115

namespace PEqualNP.Outside.L_meta_14162.G119

def y : W := 0xfffffefcfeeefe00

def base : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]

def neg : List (Fin 128) := [0,1,2,3,4,5,6,7,8,16,20,24,32,33,40]

def dict : ℕ := 0xffffffffffffff000000000000000000ffffffffffffaaaa0000000000000000ffffffffffff00000000000000000000ffffffffff00ff000000000000000000fffffffff0f0f0f00000000000000000ffffffffaaaaaaaa0000000000000000ffffffff000000000000000000000000ffffff00ffffff000000000000000000ffffff00ffaaff000000000000000000ffffff00ff00ff000000000000000000fffffcfcfcfcfcfc0000000000000000fffff0f0fffff0f00000000000000000fffff0f0fafaf0f00000000000000000fffff0f0f0f0f0f00000000000000000ffffeeeeeeeeeeee0000000000000000ffffcccceeeecccc0000000000000000ffffcccccccccccc0000000000000000ffffaaaaffffaaaa0000000000000000ffffaaaaaaaaaaaa0000000000000000ffff5555ffff00000000000000000000ffff0f0fffff00000000000000000000ffff00ffffff00000000000000000000ffff0000ffff00000000000000000000ffff0000ff0000000000000000000000ffff0000f0f000000000000000000000ffff0000aaaa00000000000000000000ffff0000000000000000000000000000ff0fff00ff0fff000000000000000000ff0fff00ff00ff000000000000000000ff00ff00ffffff000000000000000000ff00ff00ff0fff000000000000000000ff00ff00ff00ff000000000000000000ff000000ffff00000000000000000000f5f5f0f0f0f0f0f00000000000000000f0fff0f0f0fff0f00000000000000000f0fff0f0f0f0f0f00000000000000000f0f0f0f0f0fff0f00000000000000000f0f0f0f0f0f0f0f00000000000000000cfcfcccccccccccc0000000000000000ccffcccccccccccc0000000000000000cccccccccccccccc0000000000000000aaaaffffaaaaaaaa0000000000000000aaaaffff000000000000000000000000aaaaaaaaffffaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaa0000ffff00000000000000000000333333333333330000000000000000000f0f0f0f0f0f0f0000000000000000000f0f0f0f0f0f000000000000000000000f0f0f0f0f000f0000000000000000000f0f0f0f0000000000000000000000000f0f00000f0f000000000000000000000f0f00000000000000000000000000000f000f0f0f000f00000000000000000000ff00ff00ff0000000000000000000000ff00ff00000000000000000000000000ff000000ff0000000000000000000000ff00000000000000000000000000000000ffffffff000000000000000000000000ffff0000000000000000000000000000ff00ff00ff0000000000000000000000aaaaaaaaaaaa00000000000000000000222222222222000000000000000000000000ffffff00000000000000000000000000fffff0f0000000000000000000000000ffffaaaa000000000000000000000000ffff0000000000000000000000000000555500000000000000000000000000000f0f000000000000000000000000000000ff0000

def masks : List W := [0x5000500050005,0xf000f000f000f,0x55005500550055,0xff00ff00ff00ff,0x505050505050505,0xf0f0f0f0f0f0f0f,0x3333333333333333,0x5555555555555555]

def ds : Debts := [(0x5000500050005,4),(0xf000f000f000f,5),(0x55005500550055,5),(0xff00ff00ff00ff,6),(0x505050505050505,5),(0xf0f0f0f0f0f0f0f,6),(0x3333333333333333,7),(0x5555555555555555,6)]

def syms : Array Sym := #[([],[]),([0x10,0xffff000000000000ffff0000,0xffff000000000000ffff00000000,0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050],[0x10,0xffff000000000000ffff0000,0xffff000000000000ffff00000000,0x3,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x50505050505050505050505050505050])]

def book : ℕ := 0x109627b4421356b78842085c17a8210a9ca784215ac8b7b16b5b0847ad6b630ac7ad8c62ca57b18c7b48d7a1ad7a0847b5ad4a4697b9294b8637a5297382e7a5ce724217b9ce7a82a7a14a7a0217a94a7a1a87a9087a9aa7a10810842108421304c108420bd4a084210854a0bc2143d6b421084216b43d0843d29421084212943d085294a5314c5294a5294a084210a9ea0a82a085e15296a5354a5356b5294a6b5cd6a9ad6a9ca6b5ad4210842deb42d0b421e85ad4b5b16b5b14a5ad6b6318c62d8c62d8b6318caa2a8ad6b5ab2acad6b542108425e942509421e84a5294b9294b92e4a529739ae725ce725a9739ce08421085e108421085e1aa2a8ad6b5ad6b5ad6b542108421e842108421e87bdef7bdef7bdee7bdef5294a5294a53d4a5294a7bdef7bd087bdef7bdef109291384213929108427a9ea7bdef7bdeb7bdef085e10842108421084217bdee7bdef7bdef7bdef7b1ec7bdef7a1e87bdef7bdec7bde87bde87bdecab2acad6b5aa2a8ad6b57bdef7beb57bea87bdef7bdef7bdef7a1e87bdef7bde97bde97bde87bde97bdef7bdef7bde57bdef109291084210929108427bdef7bc217bdef7bdef5ad6b5ad6b5bd6b5ad6bad6b5ad508ad529ad6b57bdef7bd087bd297bdef1088410842108841084229525294a529529294a5785e17bdef791e47bdef7ade47bdef7bde47bdef7bde57bdef7bdef7bdef7bde47bde17bde47bde1295452b0a52b14a294a57bdef7bdef7bde47bdefaa2a6ad6b5ab2a6ad6b57a1e57bdef7b9e57bdef0858c084210858c084217bdef7bc217bdad7bdef6318c6318c63d8c6318cad6b5ad508ad58cad6b57bdef7bd087bdce7bdef1086310842108631084218d231b4631b52918c63789e27bdef785e17bdef7a1e87bdef7adeb7bdefaa2a3ad6b5aa6a3ad6b57a5e37bdef7bde37bdef421e84210842108421087bde97bde97bde17bde97bde97bde97bdea7bde95294a5294a5294b5294a5294e5294a5294a5294a7bdef7bdef7bde17bdef739ce739ce739c1739ce7bdef7bdef7bde37bdef4a5294a5294a5234a5294a5294a5214a5294a5294a5284a5294a5294a5297d5f57bdef7d5e27bdef5ad6b5ad625ad6b5ad6b739ce739c1739ce739ce4210c42108421084210c10962134421356b1084210962138421396b10842085410b8210b94a08421738ae72dce72ca5739ce5ac6b5b96b5b8635ad6b7382e725ce72421739cead6b5ad6b5ad6b5ad6b5aa042ad6b5ad6b5ad6b5ad6b5a8902ad6b5ad6b55290a5094a509025294a42148421084214a421080a0a10ac210aca50a0216b48d6a1ad6a0846b5ad12062138421386312042421a842108421ad4210810922130421312910842785e17bdef7a9ea7bdef7a1e57bdef7ade57bdef7bde17bde17bde47bde17bde37bdef7bdef7bdef7bdef7bde17bdef7bdef421084210d4210d42108108431084210843108426b5ad6b5a26b5ad6b5ad4210d421084210d421081208213042130841204210942108421094a108420856109501095650850110842134421344d108426b50d691ad691046b5ad084210a8210a82a08421aa2a8ad6b5aaaaaad6b5aa6a2ad6b5aa2a2ad6b55286a5394a538635294a421a842908429aa42108120221244212421120425282a5214a520215294aad6b5ad508ad5adad6b55294a529415294a5294a6b5ad6b5ad6b5ae6b5ad7bdef7bdec7bdef7bdef6b5ad6b5ad6b5aa6b5ad785e17bdef7b5ed7bdef785e17bdef7a5e97bdef5ac8b5b16b5b0845ad6b7bdef7bc217bc847bdefaa2a8ad6b5aa6a9ad6b57bde27bde27bde17bde27a1e87bdef7a5e97bdef10842108421084b1084208421084210842e0842108421084210842a0842d421084210c421084210c421084210e421084210e5294a529485294a5294a5294c5294a5294a5294a421084210842108421154210842108421084210f084210842a08421084215ad6b5ad6b5ad6b5ad6d5ad6b5ad685ad6b5ad6b5ad6b5ad6f5ad6b5ad6b6b5ab6b5ad6b5ad6b5ad5294a5294e5294a5294a4210942108421084210f4a5294a5294a5284a5294210c42108421084210f4210f421084210942108084210842c0842c084215ad6b5ad6d5ad6b5ad6b42108421084210c421086318c6318c631886318c42108421084210e42108085210b0210b12908421781e07bdef7b5ed7bdef781e07bdef7a5e97bdefaa2a2ad6b5aa6a2ad6b57bdef7beb57bea27bdef7a1e17bdef7b9e17bdef7a1e17bdef7a5e17bdef7bde07bde07bde17bde06318c62c2162d8c6302c7bdef7bc007bdad7bdefad6b5ad529ad508ad6b57bdef7bd297bd087bdef6b5a86b5ad6b5ad6b5ad6318c6318c6318e6318c739ce739ce739c9739ce7bdef7bdef7bde97bdef5294a529435294a5294a10849108421084910842739ce739ce739ce739ce295252b8a52b929294a5109221344213529108427a1e47bdef7b1e47bdef7b1e47bdef7a1e47bdefaa2a2ad6b5ab2a2ad6b5aa2a6ad6b5aa6a6ad6b5aaaa2ad6b5aa2a2ad6b57bdef7beb57beaa7bdef7a1e37bdef7b9e37bdef7a1e57bdef7a5e57bdef7a9e17bdef7a1e17bdef7bde87bde87bdea7bde87d5f57bdef7d5ed7bdef294a5294ab294a5294a52108421084210842108442108421084210b4210c084210842f0842108421421084210f4210842108421084211542108421081084810842108431084221084210822108421084084240842108424084217bde27bdef7bdef7bdef5294a5294c5294a5294a18c6318c6e18c6318c636318c6318c6318d6318c210842108421089210844a5294a5224a5294a5290842f0842108429084214a5294a5294a52b4a5297bdef7bdef7bdec7bdef0842d084210842d084214210c421084210c421084a5294a5294a52e4a529421084210e4210e4210808421084210842c084210842a084210842a084217bdef7bde27bdef7bdef6b5a96b5ad6b5ad6b5ad21084210842108b210846318c6318c6318a6318c421084210842104421086318c6318c6318b6318c421154210842108421084210f4210842108421080842f0842108421084215ad6b5ad6b5ad6b5ad6b10842108421084c1084210842108421084d1084210842108421084e1084218c6318c6318c6318c637bde17bdef7bdef7bdef084210842208421084224210b421084210b42108421094210842109421084210842108421094210e08422084210842108422421084210b4210b4210818c6318c6318c6518c6342108421094210942108294a5294a5294a3294a50842108421084230842118c6318c6918c6318c634a5294a5294a5214a5294a5294a5294a52d4a5297bde97bdef7bdef7bdef294a5294a5294a5294a5084210842a0842a0842108428084210842508421421084210b4210842108421084210a4210a4210842108421084210b42108318c6318cc318c6318c6294ab294a5294a5294a5084210842408424084216318c6318c631846318c4a5294a5294a52a4a5296318c6318c631896318c21084210842108a2108421084210842108d21084210842108421086210847bdef7bdef7bdef7bdef318c6318c6318c6318c66318c631816318c6318c6318c631886318c6318c42108421014210842108000000000000008000004a5294a5284a5294a529529415294a5294a5294a5ad685ad6b5ad6b5ad6b529485294a5294a5294a210842108421085210842108421084210812108418c6118c6318c6318c6310841108421084210842108421084210842108425ad6b5ad6b5ad6a5ad6b5294a5294a5294d5294a4a5294a5294a52c4a5295294a5294a5294c5294a421084210842109421080000000000000040000021084210842108821084421084210d42108421080000000000000090000000000000000000b0000000000000000000a0000000000000000000200000000000000000001000001084210842108481084208421084210842808421421084210a4210842108421084210c4210842108421084210942108421086b5ad6b5ad6b5ad6b5ad4210c421084210842108421094210842108421095294a5294a5294a5294a08421084210842108421739ce739c9739ce739ce421094210842108421084a5294a5294a5294a5296318c6318c6318c6318c421084210842108421084210842108421034210810842108421084510842294a5294a5294a2294a5318c6318c6318c3318c61084210842108461084208421084210842b08421108421084210849108420842108421084290842142108421084210542108294a5294a5294a6294a5318c6318c6318c5318c608421084210842408421421084210842102421081084210844108421084210842108421084a108424210842108421014210808421084210842d084211084010842108421084208421084210842a0842110842108421084410842084210842108425084212108421084210822108408421084210842208421108421084210843108421084210842108411084242108421084210a4210842108421084210d4210800000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (0,1,0x0,0x0)

def c3 : Catalogue := (0,1,0x0,0x0)

def c4 : Catalogue := (3,47,0x1003c0e03009e187e1b0420d430fc390781a,0x3433222200000000242143320000000023324343)

def r4_0 : List Hint := [(0,0x480800e0180280200800c01001),
  (0,0x480600a0200380200800c00802),
  (0,0x780e0040340280c01601405009)]

def c5 : Catalogue := (44,57,0x80180420f03405400f4300841e06a006c1804e10835003009c2107809801c8601383c0d400c0270781a045804e1083c0d019003009c210781a801b0601083405400f4360c02106a006c138420d00910360c0270841a801b0601384204400f0360c02706a007a180420f01300360c02708409801c8600f03405400f4390c01e06a00721b0601383500390c02707809801c8681804e0f400e4270781a01220801c84e0f035003909c1e0680e801b04e1083407400d0270841e03a0060138420f835003009c230781a801804e1103c0d400c0270841a06200601383c0d02f0c390c0270781a861b060138420d400fc3909c1e06a007a180420f0350c3f0b0210781a801f0601083c0d400e83009c1e06a006e1804e1083500300a8210781a801804e108400d400c0270941e06a0060140420f03500390c0270781a,0x343243320000000034324332000000003532322100000000443333220000000034433232000000003443434300000000343232210000000034323221000000003532433200000000353243320000000035323221000000003532322100000000453333220000000035433232000000004433443300000000453333220000000034434343000000003443434300000000354332320000000044443333000000004444333300000000344332320000000034433232000000003443434300000000353243320000000044334433000000003532433200000000344343430000000034434343000000003532433200000000344343430000000034434343000000003532433200000000344343430000000034325443000000003432544300000000443344330000000044443333000000004533332200000000344343430000000035433232000000004444333300000000344343430000000034543243)

def r5_0 : List Hint := [(0,0x2006807016040048060040140280400400c01801),
  (0,0x540a00901004c080060240140100402200c01001),
  (0,0x240580901001c0800600a0140100400600c01001),
  (0,0x340580901001c0800600a0140100400600c01001),
  (0,0x340b00901001c0800600a0140100400600c01001),
  (0,0x180680f0160140680800405c0800400201001801),
  (0,0x200681a016040068060040640280400406001801),
  (0,0x58068090100400b80600a03c0100400606c00801),
  (0x950001194200025,0x240f01d01001c0e00600a0700100400607001001),
  (0,0x58068090100400380600a0140100400600c01001),
  (0xb5,0x34040070440841000600a0080f8040060080f801),
  (0x495,0x18068050420981280800401c1200400200c11802),
  (0x95,0x200680704209c128060040140f80400400c11801),
  (0,0xbc1702d0580141602b0060ac0082a0520a414028),
  (0,0xbc1702d0640c81902b0560ac010310520a414030),
  (0,0x540b01401004c080060240141980402200c19801),
  (0,0x340b00901001c0800600a0140100400600c01001),
  (0,0x340b00901001c0800600a0140100400600c01001),
  (0,0x1005803010008080060020140100900608803805),
  (0,0x18058050100080800400200c0100d00a08803803),
  (0,0x200581000c0080280400400c0080d00e08802803),
  (0,0xe0038370120d80800506a0080280306800801801),
  (0,0x200581000c0080280400400c0082200e02402803),
  (0,0x200200201a01c0180b02000c0480600400402805)]

def r5_1 : List Hint := [(0,0x2006807016040048060040140280400400c01801),
  (0,0x200300201a01c0280b0200140480400400401803),
  (0,0x2c0401001a0240380600a0080280400600801801),
  (0,0x200680700c0080280400400c0080b02002402803),
  (0,0x18068050160140480800401c0800400200c01802),
  (0,0x58068090100400380600a0140100400600c01001),
  (0x825,0x3c0701c01a0141d00b00a0e40480400408801803),
  (0,0x180680f0160180480800401c0803c04a0301d802),
  (0,0x18108400120141f8080040f8080040020f401802),
  (0,0x18058050100080800400200c0102200a02403803),
  (0,0x2c0300501a024028080200080380400600401802),
  (0,0x18068050100080380400200c0100b00a02408003),
  (0,0x500b00901001c0800600a0140100400600c01001),
  (0,0x104190100580140102b0060080081402802003004),
  (0,0xbc1702f0580141602b0060ac0082a0840a413026),
  (0,0x2006807016040048060040140280400400c01801),
  (0,0x540b00901001c0800600a0140100400600c01001),
  (0,0x18068050160140480800401c0800400200c01802),
  (0,0x58068090100400380600a0140100400600c01001),
  (0,0x500400700c014010040060080081601204002803)]

def c6 : Catalogue := (62,67,0x1804e1083c0d01602441003009c210781a8018058138420f03500300a4270841e06a0060138420f03a0d400c0270841e06c1a881804e1083c0d009003009c210781a0420060138420f0340b440c02c09c210781a801804e1083c0d009002c09c210781a0120060160420f0340500100300841e0680a801e860160420f035003d0c0270841e06800801e8601083c0d400d8300b0270841a002006c1804e1083500300b0270841e02400801804e1083c04c00e4300b0270781a801a060138420f03400400e43009c1e069804e1083c0d01e02400b0270841e0680e801804e130420f03500310c0270841e06a0060138420f03406c00c0270901e0680e0020060138480f035003009c210781a0060060138420f03403c61003009c210781a801805e138420f0350c3009c210781a01218601604e1083c0d431003f0c0210781a801f8601083c0d01d0c400c0270781a05400801804e0f0340ac009c210781a04c04882004e1083c0d027003009c210781a06600661804e1083c0d400c02b0841e068130020060158420f035003009c210781a01a00601684e1083c0d400ec270841e068048820860138420f035003b0c0270781a04e0060138420f0380d400c0270841e068038019060138420f035003009c210781a04a0060138420f03401400c0270841e068058a20060138420f03500300b8270841e06a10801d8601383c0d421003009c1e06814,0x454343320000000045434332000000004543433200000000454354430000000055444433000000005544443300000000454343320000000045435443000000004554434300000000454343320000000045434332000000004543433200000000454354430000000045435443000000004543544300000000454354430000000045435443000000004643433200000000464343320000000055444433000000005544443300000000455443430000000055444433000000004554434300000000454354430000000045435443000000004543544300000000454354430000000045435443000000004554545400000000455454540000000045435443000000004543544300000000454354430000000045435443000000004543544300000000454354430000000045436554000000004543655400000000455454540000000045545454000000004554434300000000455443430000000055444433000000005544443300000000455454540000000045545454000000004554434300000000554444330000000045544343000000005544443300000000456543540000000055444433000000005544443300000000455443430000000045544343000000004554434300000000554444330000000055444433000000004554434300000000456543540000000045654354)

def r6_0 : List Hint := [(0,0xe124080480120082380500a0081e0030060042304508811021843),
  (0x131,0x380a013c270490421342404c09212c2384a0240142583c09404401801),
  (0xc5,0xd0ac154058090a8020298520200180285100a008020030a200c01001),
  (0,0x380700502f8160121782e8070201702d85a00a0080e0590b216025857),
  (0,0x680ce024040070200182d0050041982c85809615c328640c618830860),
  (0x435,0xd0161240401302001809005004010088030040040f0210d41a430861),
  (0x40d40000250003054200805,0xd0160240400702001802805004010018030040040f01d0d40003606b),
  (0,0x720e2084380540de1b82f06d02011c2e04a00a0081e05c09400c01001),
  (0,0x74016024040070200182d005004010060030020040f0380e61883081e),
  (0,0x150f4024258070200d4028050040e03c8780ee1dc3b00300600800875),
  (0,0x80fa0840b0100920181981200a010198110060043e0460aa1ec20040),
  (0,0x81042200048580de1742586d02016c1a84a00a0083f81c0fc18c3f07e),
  (0,0x80161304181c10401825005096010250030960040f02109213809011),
  (0x73d40018c50005214200035,0xd0ac0840580d10e0200b8860200180788500a0080208404c00c00801),
  (0,0x680161243408a09803c09005096010088030960044486410422030861),
  (0,0x25c4b04612a2384a0931242444808f11c2344608b),
  (0,0x7d0281180401302001809005004010088030040044c89808c07830861),
  (0,0x721340840b0540de1742f06d02016c2e04a00a0080d85c09400c01001),
  (0,0x680161bc0406d020018250050040104e0030040044d8210e618830861),
  (0,0x380921e80989e0200481a8050040443b0030040041087113a1a42504a),
  (0,0xb01004003005004010018020021a04e8690941280f04902604808864),
  (0,0x2a8548a812629c530a514828c458461442845009f),
  (0,0x15e2bc000ae13a08c5680515808c558030460042304608410c13026),
  (0,0x14132084040100a001802833004010018330040043e0460442c020040)]

def r6_1 : List Hint := [(0x94c4002101,0x380122d45a0500422cc568ac0a02c8568ac066008590ab1620cc01001),
  (0x84140030c5000b214202835,0xd03c0701082516c020038690480180286903e008020030d208c01001),
  (0,0x2a04209c040500480181981f004010198230040044d8211702dc5b8b7),
  (0x24f5,0xd0ac0740b0091720200385e0200180285e00a008020030bc00c01001),
  (0x34ed000e2b420345d,0x380422f41087a1782e8010501582ec568331640085d0ab0662c801001),
  (0,0x680ce2f004050158018198b2004010198b20040040f0641802fc5f8be),
  (0x3c25,0xc202c3040405002001819805004010198030040040f0210441ac30861),
  (0,0x25c648c818e118630931242986288f11c3106188b),
  (0,0x9902c3040404602001819805066010198030660044c85503c11830861),
  (0x90d40040250011054204005,0xd02c0240400702001802805004010018030040040f01d0001ac3606b),
  (0,0x721000840b0540de0082f06d0202b42e04a00a0085585c09400c01001),
  (0,0xc202c3284d8210e6020368100bc018250050b80080204a00617001001),
  (0x51050013354004895,0x1c016330040980200184c0050040104c003004004068cb04401c02803),
  (0,0x290a0040198050040cc018020021a01280800c010108cd16e2dc5b81e),
  (0x1636c0054d708122f80030b60014278002896,0x3686c8d81ae3586a8931a829c698d21a2340678ce),
  (0,0xe001237c0585f0120206f0070200186f00500a0086e81c1b818c6d8db),
  (0x163f4006cb9001a2d400647500180a4005c25,0x801a01c1104600002c080090420180100510a0140200200607001801),
  (0,0x390648e312a3887089314e2984808f1483104608b),
  (0x1d3d40060c5001c214200035,0xd03c0740580910e020038860200180288500a0080200300000c01001),
  (0x8213780084db082035c0080d608132f8002cb60013278202c96081f1ec007877001f0ec207837,0x3b0068eb1ae3a86a8da1d23a0738e61ca340678d1),
  (0x8214740084fd00232e40088b5081c1e4006475001c0a4206425,0x601a014000ed00002c02809042020010070380400200100607001802),
  (0,0x3cc790f118e39c780931a629c6a0ef19e3b8688ce),
  (0,0x5601a32c7b0211ea0207a0071e8018118050460080202300608c01001),
  (0x2074b9001a2d4008875001d0a4206825,0xb01a02434846130020080070380180280510a0080200300607001001)]

def r6_2 : List Hint := [(0,0x3904a8e212629c4808f148230458c91c63847b8c4),
  (0x1b3d4008cc5081b214002435,0xd03c0740400710c01802885004010018860040040580900004002803),
  (0x59050021354009045,0x162740401d0200180e8050040103f0030040041100001201c02803),
  (0,0x680161bc0406d02001825005004010250030040040f0210e618830861),
  (0x953d0020214205435,0x210000740483f0f40201f04b0200187c01e00a0080203d03c00c01001),
  (0,0x7d0e01243701302011c090050040f008803004004390df0f01a430861),
  (0,0xbd02c304010500202b4198050042ac19803004004390df0441dc30861),
  (0x905d,0x121bc0406d0200182500500401025003004004000221f210020040),
  (0,0x74016024040070200182d0050043ec320630c41847d0590b012c2b81c),
  (0,0x1402c0242e80702016c028050042047e8630ee1dc2c8fc0c61f83f01c),
  (0x20983d,0xc21361907f8fe042020280f41e8018198f4164008020331742c801001),
  (0xacf9002a3d420a0c9002731400a48500280e4209c35,0xd03c074058090420200381c0200180288500a0080200303800c01001),
  (0,0x380422002a07a0de1782586d0201701a84a00a0082e07609400c01001),
  (0x9405,0x41064040160050040ac018020020740580800c010108f908010020000)]

def c7 : Catalogue := (9,67,0x400c0270841e068048820060138420f03500300b0270841e06a0060138420f03407400fc3009c210781a801804e1083c0d027003b0c0270841e06a0060138420f0340a400d43009c210781a,0x5654544300000000565454430000000056545443000000005654655400000000565465540000000056655454000000005665545400000000566554540000000066555544)

def r7_0 : List Hint := [(0x20154f000452c000d47080250c200457080013c20003f,0x10820e118649061c6254828e21c224c6290414c240819020c84048008b),
  (0x45c20244f080812c001c47000610c000026,0x11119238c880e21c243c538a6120438520c411822c2310d21842c85109),
  (0x20214f000e52c200d47080d50c00313b080b4dc0004e7000a37c0028cf,0x11722c118649151c64508111322424c6289214c240478c311c3108008b),
  (0x1452c004d47000a41c20485f000516c204457000614c004036000f0d4002826,0x11619238c4a91d1c224c490a612023c470c411822c8e0462364688c918),
  (0x20794f001d52c007147081b50c20693f08194cc006117001743c005cff081613c20544d,0x11c24e118931252482549190524424c908c52402404791f1864784608b),
  (0x82553c009143001749c208c5f001e16c208857002114c005c360020098007c25,0x1271924a84a9051c224c628a612023c618c411822c8e0462524a08c918),
  (0x83253800c94b083451c00d14608334fc20c93e00334bc00c92e0824478006516002443820650600213f800c4fb00303e400bcf7002e3d800b4f5000633820a8cb082932400a0c708273180098c5002c21c00ac8508060f800a83b00290e420a03700270d8209835,0xd03c0746b8d525a3687412b1ce24c5392c1a6350730d025633c688ce),
  (0x3753c00cd4e08374fc20cd3e08374bc00dd2a083448c00d122003647800711600353b8200ce60013338202cc60835178000c560813138002c46,0x380424e09b93626a4d0999321ce314988c51a63509812f25c33c688ce),
  (0x83d53c00f54e003751800c94300254f80069360014438003106003c15c00dc56003b13c00c84e001e0ec00e83700050ac20e427000802c00e007,0x13c1ae4d46d1321ce24c628d31a8398970cf1a23380f0212764e88c939)]

def c8 : Catalogue := (1,57,0x1003009c210781a,0x67656554)

def r8_0 : List Hint := [(0x8083c00020ec00073a00018e408053802010d800053400010c800013002000b800032c00008a808031402008480801100000038,0x390a2944286508a089314e34c6a14027e4f89e8ce)]

end PEqualNP.Outside.L_meta_14162.G119

namespace PEqualNP.Outside.L_meta_14162.G119



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem symGood : ∀ v ∈ syms, Symmetry y v.1 v.2 := by
  have h : ∀ i : Fin syms.size,
      (∀ j : Fin 128, permRow syms[i.val].1 (permRow syms[i.val].2 j) = j ∧
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
theorem ok4_0 : ck c3 c4 3 0 r4_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4 : ban c4 4 c4.1 := by
  have p0 := empty c4 4
  have p1 : ban c4 4 3 := more b3 p0 ok4_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_0 : ck c4 c5 4 0 r5_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_1 : ck c4 c5 4 24 r5_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b5 : ban c5 5 c5.1 := by
  have p0 := empty c5 5
  have p1 : ban c5 5 24 := more b4 p0 ok5_0
  have p2 : ban c5 5 44 := more b4 p1 ok5_1
  exact p2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_0 : ck c5 c6 5 0 r6_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_1 : ck c5 c6 5 24 r6_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_2 : ck c5 c6 5 48 r6_2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b6 : ban c6 6 c6.1 := by
  have p0 := empty c6 6
  have p1 : ban c6 6 24 := more b5 p0 ok6_0
  have p2 : ban c6 6 48 := more b5 p1 ok6_1
  have p3 : ban c6 6 62 := more b5 p2 ok6_2
  exact p3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_0 : ck c6 c7 6 0 r7_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b7 : ban c7 7 c7.1 := by
  have p0 := empty c7 7
  have p1 : ban c7 7 9 := more b6 p0 ok7_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8_0 : ck c7 c8 7 0 r8_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b8 : ban c8 8 c8.1 := by
  have p0 := empty c8 8
  have p1 : ban c8 8 1 := more b7 p0 ok8_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem withDebts (hard : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset) (k : ℕ) (run : build raw y k base.toFinset) : 9 ≤ k := by
  have denial := b8 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c8 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c8 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    hard denial run

end PEqualNP.Outside.L_meta_14162.G119

namespace PEqualNP.Outside.L_meta_14162.G119

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain0 : Hard y 0x5000500050005 4 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x64c11202440100)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G41.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain1 : Hard y 0xf000f000f000f 5 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x668d8a16489820260c8812408800)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G57.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain2 : Hard y 0x55005500550055 5 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x6c59a1464498104c192044409000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G57.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain3 : Hard y 0xff00ff00ff00ff 6 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x6ed9ab466c98b04e992a446890a02e58a9426488900e182840608080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G103.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain4 : Hard y 0x505050505050505 5 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x74e152864c112034605082440100)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G57.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain5 : Hard y 0xf0f0f0f0f0f0f0f 6 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x76e9cb866c98b056a94a846890a03668c98264889016284880608080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G115.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain6 : Hard y 0x3333333333333333 7 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x7af1cb86ad18b05ab14a84a910a03a70c982a508901a304880a10080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G117.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain7 : Hard y 0x5555555555555555 6 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x7ce9e386cc9a303c68e182c48a105ca96284c892201c286080c08200)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G115.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem initial : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset := by
  intro d hd
  simp only [ds,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact domain0
  · exact domain1
  · exact domain2
  · exact domain3
  · exact domain4
  · exact domain5
  · exact domain6
  · exact domain7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (h : build raw y k base.toFinset) : 9 ≤ k := withDebts initial k h

end PEqualNP.Outside.L_meta_14162.G119

namespace PEqualNP.Outside.L_meta_14162.G123

def y : W := 0xffffeeecfefeeea0
def base : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (run : build raw y k base.toFinset) : 9 ≤ k := by
  apply essential_sample (v := 0xff00ff00ff00ff00) (sampleRow 0x6ed9ab466c98b04e992a446890a02e58a9426488900e182840608080)
    1 9 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G107.lower k run

end PEqualNP.Outside.L_meta_14162.G123

namespace PEqualNP.Outside.L_meta_14162.G125

def y : W := 0xffffeeecfefaeea0

def base : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]

def neg : List (Fin 128) := [0,1,2,3,4,6,8,12,16,18,24,32,33,36,40,44]

def dict : ℕ := 0xffffffffaaaa00000000000000000000ffffffff222222220000000000000000ffffffff222200000000000000000000ffffffff000022220000000000000000ffffffff000000000000000000000000ffffeeeeffffeeee0000000000000000ffffccccffffcccc0000000000000000ffffaaaaffffaaaa0000000000000000ffff0000ffff00000000000000000000ffaaff00ffaaff000000000000000000ff00ff00ff00ff000000000000000000fafaf0f0fafaf0f00000000000000000f2f2f0f0f2f2f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000eeeeeeeeeeeeeeee0000000000000000eeeecccceeeecccc0000000000000000cccceeeecccceeee0000000000000000cccccccccccccccc0000000000000000bbbbaaaabbbbaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaa8888aaaa88880000000000000000aaaa0000aaaa000000000000000000008888aaaa8888aaaa00000000000000005555aaaa5555aaaa0000000000000000555500005555000000000000000000004444cccc4444cccc00000000000000003333222233332222000000000000000022222222222222220000000000000000222200002222000000000000000000000f0f0e0e0f0f0e0e00000000000000000f0f0a0a0f0f0a0a00000000000000000000eeee0000eeee00000000000000000000aaaa0000aaaa00000000000000000000222200002222000000000000000000000000ffffeeee000000000000000000000000ffffcccc000000000000000000000000ddddcccc

def masks : List W := [0x330033,0x33333333,0xffffffff,0x33003300330033,0xff00ff00ff00ff,0xf0f0f0f0f0f0f0f,0x3333333333333333]

def ds : Debts := [(0x330033,4),(0x33333333,5),(0xffffffff,7),(0x33003300330033,5),(0xff00ff00ff00ff,7),(0xf0f0f0f0f0f0f0f,7),(0x3333333333333333,6)]

def syms : Array Sym := #[([],[]),([0x18,0xff00ff0000000000ff00ff00,0xff00ff0000000000ff00ff00000000,0xf,0xaaaa0000aaaa0000aaaa0000aaaa,0x55550000555500005555000055550000],[0x18,0xff00ff0000000000ff00ff00,0xff00ff0000000000ff00ff00000000,0xf,0xaaaa0000aaaa0000aaaa0000aaaa,0x55550000555500005555000055550000])]

def book : ℕ := 0x39c67828e73a86381ce781986314c631585818c6210842108422088210843418c318c63198c340c6a0a82a5294a0681a5294ad6b5ad6b5a86a1ad6b5318c632a0a328ca31a066306c6298c628636318c528215294a5294a5294a5298a5254a525895294a94a529484294a5294a52a5294a5021a5294a5294ad6b5ad421ad6b5ad6b5340c6318c6318c6340c681a038421082a03842108420b8420b842028420b842108421084205842108421084042842108421008421084630842108463ad6b5ad463ad421ad6b56318c6318c6418c6318c842108410884042842100842108484084210848484210842108402184210842018420184202842088320384210842038421031a06318c6318c6318c6084210842108422084286318c6318c631836318c08422084210842108422318c6318ca318ca318c64210842101421084210831846328c632842318c60002002000020210000031986308c630982318c6ad6b5aa000ad6b5ad6b55294a50cc350d4a528caad6b5a8400ad6b5ad6b5108481084210848108428421084203842108421008421084210842c0842194a5292c4294a5294a52a0681a5294a328ca5294a86a1ad6b5ab2acad6b55284a52d4a52c425294a94a529344294a5294a5221184210842118c21084ad6b5ad6b5ad6b5ad6b594a5294842948a594a52a8481ad6b5ad6b5ad6b5a5294a5021a50a5a529439ca73a8e73a8a539ce75286a51d4a51c635294aad6b5a9104ad6b5ad6b58421084042841088421084201842018420a84201842108404284063842108420684206842028420681a058421082a058421081a05842108320584210842108420584210842104a5244a5294a5294a5291085210842108421084218c6318c6318c6318c63084340842108421084214a5294a5294a5294a52994a52948429490894a5294a5294a9494a8a94a52a0681a5294a2689a529494a5294ab594aa594a52a5294a52b5a52a5a529494a52949089484294a5239c673a8e73a86339ce7a5294a5021a5042a529494a52948429486394a5221064224842246321084a5294a5042a5021a529431986314c631585318c642108421084210a42108421084210842109421086b5ad6b5ad6b5ad6b5ad18d03184631850118c6380a02842108060184210a8ea3ad6b5a86a1ad6b594a5294a529044194a52806018421082a0a8421084201842018420284201294252a4a52a421294a584210840c684021842105294a5294a529495294a8421084210842018421084210842048421084210318cc318c6318cc318c6529415294a5294a5294a42108421084210c421080843008421084210842108435084210842108421421084210842108421081085010842108421084208421084220842108422084210842308421084236318c6318c6318c6318c2108421084210872108421084210842108821084108421084810842108480842108429084210842908421084280842108428318c6318c6318cc318ca8420484210842108421010842108421084210850084210842108421084300842108421084290842108421084210842108435318c6318c6318c6318c6294a8294a5294a5294a518c6318c6418c6318c635ad6b5ad6b5ad625ad6b318c6318c6318c3318c6318c6318c6318c5318c6108431084210843108428420184210842108421008423084210842308421318cc318c6318c6318c6084210842208422084210842108423084230842118c6318c6a18c6318c63084220842108422084214210842108421034210821084210852108521084421084210842105421084210842102421084210880601842108260984210a86a1ad6b5aa2a8ad6b584210842b5842a584210802008421082a0a8421084200842008420284200856158421085603842102102422084220212108484210840428402184210ad6b5ad508ad421ad6b58421084000840218421084210840218404284210ad6b5ad421ad463ad6b594a529080094a5294a52294a528c8328ca52948508421084210842208430084210842108421084211084210842108491084218c6318c6318c6518c6342108421084210242108318c6318c6318ca318c6294a5294aa294a5294a508421084280842108430294ac294a5294a5294a5294a5294a5294a3294a5294a5294a5294a1294a54a5294a5294a5214a5290843008422084210842184210842108421084210294a5294a5294a5294a51084210840108421084210842108411084210842084210842208421084215ad6b5ad6b5ad615ad6b2108421084210842108418c6318c6218c6318c63084210842808421084215294a5294a5294c5294a21084210842108a210845ad6b5ad6b5ad645ad6b5294a5294a5294a5294a084210842108428084212108421084210812108408420084210842108421084210842108427084210842108421084240842142108421084210142108084210842408421084210000000000000040000000000000000000200000084210842a08421084211084210843108421084200000000000000800000000000000000006000000000000000000030000000000000000000100000000000000000005000000842108420084210842108421084250842108421084210842308421084211084210842108481084208421084210842a084211084210842108471084218c6318c6318c6418c6308421084210842508421318c6318c6318c2318c60842108421084220842108421084210842308421108421084210843108422108421084210832108410842108421084110842318c6318c6318c1318c62108421084210852108400000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (0,1,0x0,0x0)

def c3 : Catalogue := (0,1,0x0,0x0)

def c4 : Catalogue := (0,1,0x0,0x0)

def c5 : Catalogue := (24,56,0x841d06c1404807741b0601404801941d06c1805012841d06c1a05012841d06c180480c841d06c1805812841b060140480e941d0701805012841e0701805012941d06c1a05012841e06c1a05012941d06c180480c841d06c1a0480c941d06c1805812841d06c1a05812941d06c1805005841d06c1a05005841d06c18050128c1d06c1805012841d06c1905012881d06c1805012741b0601404803841d06c1404808841d06c1805812,0x354242100000000044435430000000003442532000000000354242100000000044434320000000004443432000000000344242100000000034535330000000003453422000000000354253200000000035424210000000004443543000000000454343200000000044435430000000004543432000000000344253200000000035424210000000003442421000000000444354300000000045434320000000004443543000000000444354300000000045434320000000005444443)

def r5_0 : List Hint := [(0,0x340600b0120280480800801c0300500800c01001),
  (0,0x540601401004c038130240480880f02003c07002),
  (0,0x500c809026060098120060080881002e03c01016),
  (0,0x780181d0060700480200c01c0300502000c0d81a),
  (0,0x340600b0120700480800801c0300500800c01001),
  (0,0x340600b0120280480800801c0300500800c01001),
  (0,0x800601d0120700480800c01c0300503e00c01001),
  (0,0x340600b0120880480800201c0300504200c01001),
  (0,0x340600b0120880480800201c0300504200c01001),
  (0,0x340600b0120280480800201c0300504600c01001),
  (0,0x340600b0120880480800201c0300504600c01001),
  (0,0x340600b0120700480504600c0100800201c03001),
  (0,0x340600b0120880480504600c0100800201c03001),
  (0,0x14060030120a00480800201c0302604e09812824),
  (0,0x340600b0120880480800201c0300504600c01001),
  (0,0x14060030120a00480800201c0302604e09812824),
  (0,0x340600b0120880480800201c0300504600c01001),
  (0,0x300480901001c030120240480c0100520400701f),
  (0,0x340600b0120280480800801c0300500800c01001),
  (0,0x800601d0120700480503e00c0100800801c03001),
  (0,0x340600b0120700480800201c0300504600c01001),
  (0,0x340600b0120880480800201c0300504600c01001),
  (0,0x500c809026060098120060080902b0540a804016),
  (0,0x5406014010060038130240480c0290200a407002)]

def c6 : Catalogue := (33,66,0x2106c180501203405841e0741b0601404a10741b0601505012841d06c180501204210781d06c140480700210741b0501201e10741b060140480b841e06c180501201610781b0601404810941d06c180501204000941d06c1805012841d06c1a0501204000841d06c1a05012841d06c180481003000841d06c180480c841d06c180581404a10741b060160481000210741b0601604a10741b0601404805841d06c180501001640741b060140480a00240741b0601404a10741b060140480f841d06c180501304a10741b0601404809841d06c180501201210741b060140480684200741b0601404a10741b06014048117c1d06c180501200800741b0601404802841f0741b0601704a10741b060170480a,0x455353200000000045535320000000005554543000000000455353200000000046535320000000004653532000000000555454300000000045535320000000004553532000000000455364300000000045536430000000004653532000000000465353200000000055545430000000005554543000000000555454300000000055545430000000005554543000000000455353200000000045535320000000005554654000000000555465400000000055545430000000005554543000000000555454300000000055545430000000005554543000000000555454300000000055545430000000005554654000000000555465400000000065555540000000006555554)

def r6_0 : List Hint := [(0,0x200180740481c0120200f8280040141800305e09c1700e0520381682c),
  (0x91,0x3a01a0e406007070024030370120d81a83406606c0283206200c17827),
  (0,0x1202384608a110218420821001f82d07c0f41e03b),
  (0,0xa00e0278370120002704d09812c188030041281682d0540a824816),
  (0x15,0xd01802c0480a0120202c0570ac0100201f0041542a0530a41482882c),
  (0x94908024340004dd,0x5e04009c0605d0b80242d8090120d82d00600e0180282706000c0d859),
  (0,0x64018194048220120d81180700c01432003036164318390c41843005f),
  (0xc55,0xd01802c0480a0120202c0570ac01402003036154348390d019c33027),
  (0x51542014350004094000015,0xd01802c0480a0120200200700c01402003004004348390d81ac0006a),
  (0,0x20018170048090120200300700c150380680c41bc2606e03606c36827),
  (0,0xd01802c0480a0120200200700c1300201b0361c82a0710d018437827),
  (0,0x1e83c8480f011c230770ec1d42182d0e810420073),
  (0,0x30060740181c012020020570ac0b41800305e154168670d019c1c87b),
  (0x20a500071d4001805,0xd01802c048220120200080700c1a80007d0d41f00282100600800800),
  (0,0xd01802c048220120200080700c1303201b0361f02a0390d018437827),
  (0,0x2244408710c11c428841062081e8811001fc2007e),
  (0x2855080a0d4002425,0xd01802c048220120200080700c014118030040044688c1161ac1688a),
  (0,0xd01802c0480a01218c2984d0a418c2c04d0a4168028040060084788e),
  (0,0x2544a04808c11c23093084104200921221d421890),
  (0xc294203085000b1d4000005,0xd01802c04822012014118030041a41c86c0d61a80400100e01800800),
  (0x8070f8001c3b080d0dc003436,0x224440871362684c8841302084b8810461fc4b07e),
  (0xe154201c4d080e0d4002c1d0009054001c0d,0xd01802c048220120200080700c01411803004004468001162702d000),
  (0x80ec203c37,0x2885088714011c4289f1302081e89e13a1fc2007e),
  (0x4035000e09400301d000a05400200d,0xd01802c048220120200080700c01411803004004168661161ac2d000)]

def r6_1 : List Hint := [(0x444d000f0d4003425,0x501800c048280120200080700c0981382604a090518000720e40306a),
  (0x184d,0x501800c048280120200080700c1300001b0361f01480005209407021),
  (0,0x20018170048090120202b0570ac01418003036154528a40d019c10870),
  (0,0x224440871082ac410811541fc548811501fc538a6),
  (0,0x54040000060ae0b80205680600e1300006e0361f01489c04a0a4070ac),
  (0x545508150d40050250013074004815,0xd01802c048220120200080700c01411803004004468391161ac2d06a),
  (0x2058c9,0xd01802c0480a01218c3885d0c22c05780700c1680280400606c38059),
  (0x5cdd,0x5404009c060ae0b80242d8200120205680600e018260270dc06c0d87c),
  (0x4405,0xc0120240400700c04c09012030034058220021a81482904a03813800)]

def c7 : Catalogue := (5,66,0x210741b0601404805841e0741b0601404a10741b0601404810841d06c180501202a10741b0601705012,0x56646430000000005664643000000000566464300000000066656540000000006665654)

def r7_0 : List Hint := [(0x201cdf000636c0014d7080434c200cca080232400049700001bc00000a,0x951281202304708c2d85a8b40802cc590750862c4498740821001688f),
  (0x198003056000b15420284f000712c202447000810c000016,0x951281202304708c2485e8bc08624c3a0410802ec5d0b90822e05b82d),
  (0x80d27800349b081825c0060960017158005855080e13c20344e08170d82058350015098005025001307800481d000806c0044170010058003c15000e03c00340e,0x8911021c4304710a2104c08207a2041187f0801f8608391802fc5f06a),
  (0x194bc00392e001c37c006cdd001a278001496081913c20384e08190fc00643a08180cc006032,0x8111209c440c710e2186304710a210628c41040f4408271861fc200c2),
  (0x82027c00809e0019258003493001f11c006446000706c007817001d03c00340e,0x8911021c4304710a2104c08207a2046487f080308408390fe10064027)]

def c8 : Catalogue := (1,56,0x841d06c1805012,0x6775754)

def r8_0 : List Hint := [(0x801200200078080410000103c00030e00008340001030000008,0x2244408710c11c428841962081e8810841fc200ca)]

end PEqualNP.Outside.L_meta_14162.G125

namespace PEqualNP.Outside.L_meta_14162.G125



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem symGood : ∀ v ∈ syms, Symmetry y v.1 v.2 := by
  have h : ∀ i : Fin syms.size,
      (∀ j : Fin 128, permRow syms[i.val].1 (permRow syms[i.val].2 j) = j ∧
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
  have p1 : ban c5 5 24 := more b4 p0 ok5_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_0 : ck c5 c6 5 0 r6_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_1 : ck c5 c6 5 24 r6_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b6 : ban c6 6 c6.1 := by
  have p0 := empty c6 6
  have p1 : ban c6 6 24 := more b5 p0 ok6_0
  have p2 : ban c6 6 33 := more b5 p1 ok6_1
  exact p2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_0 : ck c6 c7 6 0 r7_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b7 : ban c7 7 c7.1 := by
  have p0 := empty c7 7
  have p1 : ban c7 7 5 := more b6 p0 ok7_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8_0 : ck c7 c8 7 0 r8_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b8 : ban c8 8 c8.1 := by
  have p0 := empty c8 8
  have p1 : ban c8 8 1 := more b7 p0 ok8_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem withDebts (hard : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset) (k : ℕ) (run : build raw y k base.toFinset) : 9 ≤ k := by
  have denial := b8 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c8 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c8 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    hard denial run

end PEqualNP.Outside.L_meta_14162.G125

namespace PEqualNP.Outside.L_meta_14162.G125

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain0 : Hard y 0x330033 4 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x2a508900a10080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G41.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain1 : Hard y 0x33333333 5 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x3a70c982a508901a304880a10080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G57.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain2 : Hard y 0xffffffff 7 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x3e78e9c3668c982e58a9426488901e3868c16284880e182840608080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G61.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain3 : Hard y 0x33003300330033 5 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x6a95a242a14a0462858202204800)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G57.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain4 : Hard y 0xff00ff00ff00ff 7 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x6e9daa56c99a242e1ca852c18a04668d8a16489820260c8812408800)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G61.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain5 : Hard y 0xf0f0f0f0f0f0f0f 7 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x76e9cb866c98b056a94a846890a03668c98264889016284880608080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G117.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain6 : Hard y 0x3333333333333333 6 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x7ad5cb13a54c9178d1c303850c105a954a11a1448158914201810400)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G103.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem initial : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset := by
  intro d hd
  simp only [ds,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact domain0
  · exact domain1
  · exact domain2
  · exact domain3
  · exact domain4
  · exact domain5
  · exact domain6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (h : build raw y k base.toFinset) : 9 ≤ k := withDebts initial k h

end PEqualNP.Outside.L_meta_14162.G125

namespace PEqualNP.Outside.L_meta_14162.G127

def y : W := 0xfffffffffefefefcfffeffeefefeaa00

def base : List W := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]

def neg : List (Fin 128) := [0,1,2,3,4,5,6,7,8,10,12,14,16,24,32,36,48,64,65,72,80,88]

def dict : ℕ := 0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffff00000000ffffffffffffffffffffaaaaffff0000ffffffffffffffffffaaffaaff00ff00fffffffffffffffffafafafaf0f0f0f0ffffffffffffffffeeeeeeeeccccccccffffffffffffffffeeeeeeee00000000ffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaa00000000ffffffffffffffff5555555500000000ffffffffffffffff00ff00ff00aa00aaffffffffffffffff00000000aaaaaaaaffffffffffffffff0000000000000000ffffffffffff5555ffffaaaaffff0000ffffffffffff0000ffffaaaaffff0000ffffffffff55ff55ffaaffaaff00ff00ffffffffff00ff00ffaaffaaff00ff00fffffffffcfcfcfcfefefefefcfcfcfcfffffffff0f0f0f0fffffffffafafafafffffffff0f0f0f0fafafafaf0f0f0f0ffffffffccccccccffffffffeeeeeeeeffffffffcccccccceeeeeeeeccccccccffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaa55555555aaaaaaaaffffffffaaaaaaaa5555555500000000ffffffffaaaaaaaa00000000aaaaaaaaffffffffaa00aa00ffffffffaa00aa00ffffffff55555555aaaaaaaa00000000ffffffff22222222ffffffff22222222ffffffff0a0a0a0affffffff0a0a0a0affffffff00aa00aaffffffff00aa00aaffffffff0000aaaaffffffff0000aaaaffffffff00000000ffffffffaaaaaaaaffffffff00000000ffffffff00000000ffffffff00000000aaaaaaaa00000000ffffffff0000000055555555aaaaaaaaffffffff000000005555555500000000ffffccccffff0000ffffeeeeffff0000ffffaaaaffff0000ffffaaaaffff0000ffffaaaaffff000055550000ffff0000ffff0f0fffff0000ffff0505ffff0000ffff0505ffff0000ffff0505ffff0000ffff0000ffff0000ffffaaaaffff0000ffff0000ffff0000ffff0000ffff0000ffccffccff00ff00ffeeffeeff00ff00ffaaffaaff00ff00ffaaffaaff00ff00ffaaffaaff00ff0055005500ff00ff00ffaaffaaaaaaaaaaffaaffaaaaaaaaaaffaaffaa00000000ffaaffaa00000000ff00ff00ff55ff55ff00ff00aa00aa00ff00ff00ff00ff00ffaaffaaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00fefefefefcfcfcfcfefefefefcfcfcfcfcfcfcfcfcfcfcfcfefefefefefefefefcfcfcfcfcfcfcfcfefefefefcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfefefefefcfcfcfcfcfcfcfc5454545454545454fcfcfcfcf0f0f0f0fefefefef0f0f0f0fafafafaf0f0f0f0fafafafafafafafafafafafaf0f0f0f0fafafafaf0f0f0f0fafafafaf0f0f0f050505050f0f0f0f0fafafafaf0f0f0f05050505050505050f0f0f5f5f0f0f0f0f0f0f5f5f0f0f0f0f0f0f0f0fcfcfcfcf0f0f0f0fefefefef0f0f0f0f0f0f0f0fefefefefcfcfcfcf0f0f0f0f0f0f0f0fafafafafafafafaf0f0f0f0f0f0f0f0fafafafaf0f0f0f0f0f0f0f0f0f0f0f0fafafafa50505050f0f0f0f0f0f0f0f0f0f0f0f0fafafafaf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f050505050fafafafaf0f0f0f000000000fafafafa00000000eeeeeeeecccccccceeeeeeeeccccccccccccccccfcfcfcfcccccccccfefefefecccccccccccccccceeeeeeeeeeeeeeeecccccccccccccccceeeeeeeecccccccccccccccccccccccceeeeeeee44444444cccccccccccccccccccccccceeeeeeeecccccccccccccccccccccccccccccccccccccccccccccccc44444444eeeeeeeecccccccc00000000eeeeeeee00000000bbbbbbbbaaaaaaaabbbbbbbbaaaaaaaaafafafafaaaaaaaaafafafafaaaaaaaaaaffaaffaaaaaaaaaaffaaffaaaaaaaaaaaaffffaaaaaaaaaaaaffffaaaaaaaaaaaaaaaaffffffffaaaaaaaa00000000aaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaaaaaaaaaa55555555aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaaaaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaa00000000aaaaaaaa0000000055555555ffffffff555555550000000055555555ffffffff00000000aaaaaaaa55555555ffffffff000000000000000055555555aaaaaaaa55555555aaaaaaaa555555555555555555555555aaaaaaaa55555555555555555555555500000000555555555555555500000000aaaaaaaa5555555500000000ffffffffaaaaaaaa5555555500000000555555550000000054545454fcfcfcfc54545454fcfcfcfc50505050f0f0f0f050505050fafafafa44444444cccccccc44444444eeeeeeee3333333300000000111111110000000022222222aaaaaaaa00000000aaaaaaaa111111110000000011111111000000000f0f0f0f0f0f0f0f0f0f0a0a0f0f00000f0f0f0f0000000005050505000000000505050500000000050505050000000000ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00aa00aa00aa00aa00ff00ff00aa00aa0055005500aa00aa0055005500aa00aa005500550000000000550055000000000000555500000000000055550000000000000000ffffffff55555555aaaaaaaa00000000ffffffff555555550000000000000000ffffffff00000000aaaaaaaa00000000f0f0f0f000000000fafafafa00000000cccccccc00000000eeeeeeee00000000aaaaaaaaffffffffaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa55555555aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000222222220000000022222222000000000a0a0a0a000000000a0a0a0a0000000000aa00aa00ff00ff00aa00aa0000000000aa00aa0000000000aa00aa000000000000aaaa000000000000aaaa0000000000000000ffffffffaaaaaaaa0000000000000000ffffffff000000000000000000000000ffffaaaaffff00000000000000000000ffaaffaaff00ff000000000000000000fafafafaf0f0f0f00000000000000000eeeeeeeecccccccc0000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaa0000000000000000000000005555555500000000000000000000000000ff00ff00aa00aa000000000000000000000000aaaaaaaa

def masks : List W := [0x3333333333333333,0xffffffffffffffff,0xf0f00000f0f00000f0f00000f0f,0x3333000033330000333300003333,0xffff0000ffff0000ffff0000ffff,0x330033003300330033003300330033,0xff00ff00ff00ff00ff00ff00ff00ff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0x33333333333333333333333333333333]

def ds : Debts := [(0x3333333333333333,7),(0xffffffffffffffff,8),(0xf0f00000f0f00000f0f00000f0f,8),(0x3333000033330000333300003333,7),(0xffff0000ffff0000ffff0000ffff,9),(0x330033003300330033003300330033,7),(0xff00ff00ff00ff00ff00ff00ff00ff,9),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,9),(0x33333333333333333333333333333333,9)]

def syms : Array Sym := #[([],[])]

def book : ℕ := 0x421ce42108421ce42108421084390e4390e4210808822084210842108822b59ce10842109ceb5842b58631084210863b5842b0dc31c8631c9ceb0c63b386e739ce73863b39ceb58421084210842b5842b5ad6b5ad6b5ad2b5ad610a421384213a4e10842b5ad6b5ad6b5a52b5ad6739d2739ce739ce739d1e739ce739ce7021e739c18c631ba2e1b86318e234a4694b9294b8634a529739ce73908739ce7390eb5ad1b5ad6b5ad6b5ad642028422284202142228b5a31b5ad6b5ad6b5ad6421084210e421084210842108421114211242108b5ad6b5842b5ac3b5ad6b5a52b5ad6b5ad6b5ad6c6318c6021c6252c6318e739ce7021e7252e739c4202842108420214210808421084220842e0842108421084210842108433e4b92e739ce0781e739cb4ed3b5ad6b5ad6b5ad61cc631b86e1b8631cc635282a53d4a53c215294ac6318b5ad6b5ad6b5ad608421084210d8210842108421084420842108442b5ad6b5884b5821b5ad614c42138421384e14c42c6318c618cc6231c6318b5ad6b598cb5a31b5ad6b5a73b5ad6b5ad6b5ad61084210843108421084210853108421084210842b5ad6b5842b5ad6b5ad6c0701c6318c6318c6318c330cc6318c6318c6318b32ccb5ad6b5ad6b5ad618c631b86e1b86318c637bdef7c5f17c5ef7bdef18c631cc731cc6318c639ce539ce739ce529ce73109c210442105c11084218c6318c4218c6318c43b5ad6b5983b5ac3b5ad6739ce739ce759ce739ceb5ad6b5ad1b59ceb5ad6b5ad6b5b18b5b0fb5ad6b5aceb5aceb5ad1b5aceb5ad6b5ad6b4ed3b5ad6b5ad6b59ceb5ad3b5ad69cc339ce739cc219ce7310842138421384e10842b5ad6b5ad6b5ad1b5ad6b5ad6b5ad6b46d1b5ad6b5ad6b5863b5ad1b5ad69ce539ba739ba4e9ce73b5ad6b5842b5ad3b5ad6b5ad6b5a31b5ad6b5ad6e739ce7252e7021e739cb5ad6b598cb59ceb5ad6b5ad6b5a73b5ad6b5ad6b5ad6b5863b59ceb5ad6e739ce739ce0781e739cb5ad6b59ceb5863b5ad69cc339ba739b8219ce73b5ad6b598cb5a52b5ad6739ce739ce739ce739d694a4e94a5294a5294a52f33ccf7bdef3bcef7bde18c631b86e18c6318c63e739ce3b8ee739ce739ce739ce0781e739ce739cb08621444214463b08420002003800e739c00000b0c631c8421c863b0c4318c6318c631d86318c6318c631ba4e1b86318e4318c6318c6318c6318c76b5ad6b5ad3b5863b5ad618dce18c6318dc318c63b5ad6b5863b5ad2b5ad6e3b8ee739ce0781e739ce7391e739ce0781e739cb5ad6b5b18b5b05b5ad6c330cc6318c4310c6318b5ac5b5ac5b5ac3b5ac5b32ccb5ad6b3aceb5ad6b32c3b5ad6b3ac3b5ad6739ce73842739ce7384ec6318c6185c6245c6318739d6739ce739ce739ce18c7618c6318c6318c63b5ad6b598cb5ad6b5ad610ac2108421084210842b5ad6b46d1b5ad6b5ad6b5ad6b5ad1b5ad1b5ad6b5ad6b5b9cb5b92b5ad6c330cc6318c4711c6318b5ad6b5b18b5b11b5ad6b32ccb5ad6b46d1b5ad6b5accb5ad1b5ad1b5accb5ad6b4ed3b5ad6b5ad6b5ad6b5ad3b5ad3b5ad6b09c214442145ce10842b24694cd294cc634a52942108421084202142108159ce10842109ce15842c6318c618cc6210c6318f7bdef798cf79cef7bde18c631c8631c87218c63c6318c6185c6305c6318f7bdef7983f7bc3f7bdeb0a021484214a10b0842421084410844110c2108b0d231c8631c929b0c63421084210842103e2108b40908461084484b4210420a843d0843ca5c210815842108421084215842c6318c6021c6318c6318c6318c618cc6318c6318b09c214442145ceb0842b384e745ce74442b39ceb24694cd294cc63b2529420684210842063f21087386e739ce73863739ce10842108421384e1084215863108421086315842c6318c618cc6252c6318f7bdef798cf7a52f7bdec6318c6021c6310c6318e739ce7021e739ce739cf7bdef798cf7bdef7bde94a5294a4e94a5294a52b5ad6b5842b5ad1b5ad6084210b8000b82108401c6318c6301c6318c63187bdf27bdef7bdef7bdef5294a5294e5294e5294a4a5294a52e4a52e4a5297bdef7bdef7bdf17bdef8c6318c6288c6318c63118c6318c6318c7018c63c6318c6302c6318c6318e739ce738ee739ce739cc6318c630cc6318c6318b5ad6b5ad6b5acfb5ad60842108430084210842cc6318c6318c6301c6318318c6318d0318c6318c66b5ad6b5ad6b5a66b5adc6318c6318c630fc6318c6318c630fc6318c63180842e084220842108421084210842e084210842c5ad6b5ad6b5ad6b5ad6b6b42d6b9ad6b8216b5ad5ac2b5ad6b5ac215ad6bb6318b5ad6b5ad6b5ad6f7bdef7bdef7bc1f7bde08421084240842108424084240842108421084244a5294a52e4a5294a529b5ad3b5ad6b5ad6b5ad6b5ad6b59ceb5821b5ad66b42d6c1ad6c0216b5adc6318c6252c6021c6318f7bdef7bdef5821f7bde4a5294bd084bd294a5094a4294a5294a4214a529e739ce7381e739ce739c8c6318c6218c6318c631108421085410854108421084210853108531084210850108421084210842b5ad6b5842b5a10b5ad6c6318c3421c6318c63184a4294b1294b0214a529b5ad6b5842b5929b5ad6e739ce2021e739ce739cc0701c6318c2709c63186302c621cc62021631cc1084f108421084210842b5ad6b5842b5884b5ad6b5ad6b5842b59efb5ad6c6318c1585c6318c6318c0701c6318c1304c6318e0781e739ce1785e739c6324c6298c62a4a6318cb5ad6b5884b5842b5ad6b5ad6b5842b5acfb5ad6b5ad6b0982b5ad6b5ad6b5ad6b5b18b5b12b5ad6c0701c6318c0b02c6318e0781e739ce0f83e739cc330cc6318c630fc63188c6318c6228c6318c6318c6318c62e8c6318c6318c6318c6318c6348c6318c6318c6318c6338c631739ce739ce739d6739ce8c6318c6328c6318c631a5294a5281a5294a52948c6318c62c8c6318c6317bdef7bde87bdef7bdefa5294a5294a5292a52940842e0842108421084220843208421084210842118c6518c6318c6318c63294a3294a5294a5294a51084210842108421084ec6318c6318c6310c63181084e1084210842108420842108421084340842108421084210843308421b5ad6b5acab5ad6b5ad66b44d6b9ad6b8426b5adb4e52b5ad6b5ad6b5ad61084210842108421084318c6318c6318c7318c639ce619ce739ce739ce73a5281a5294a5294a52948c62c8c6318c6318c63108432084210842108432c6318c6318c4421c6318c6318c6318c4021c6318b5ac1b5ac1b5ac2b5ac15282a5394a538215294ab5ad6b598bb5a4bb5ad6b5ad6b5ad6b3821b5ad64a4294b9294b8214a529c6318c618bc624bc631810843108421084210842b5ac1b5ad6b5ad6b5ad6b5ad6b5ad6b5ac3b5ad6f7bdef7983f79c3f7bdeb5ad6b5ac1b5ad6b5ad694a4294a5294a5294a52b5ad6b5aceb5ad6b5ad61084210842108431084e00020038000382100000b5ad6b5982b5a42b5ad6e739ce4842e739ce739ce739ce3800e739ce739cb5ad6b5983b59c3b5ad6e739ce0400e739ce739c10842108421084e108436318c63192631926318c7bdef7bdef7bdef7bdf1739ce739c8739ce739ce8c62e8c6318c6318c631000000000e0000e00000739ce739d2739ce739ce94a5294a5294a5294a420000e000000000e00000e7380e739ce739ce739c18c6318c7218c6318c6394a5294a4294a5294a5294a5294a4c94a5294a52739ce739c0739ce739ce00001000000000100000a5294a5294a528ea52945294a5294a5294a5294a18c6318c6f18c6318c63b5ad6b5842b5821b5ad6b5ad6b5821b59ceb5ad6e7382e739ce0781e739cc330bc6318c430bc6318f7bdef7bdef4421f7bdeb3129b5ad6b5ad6b5ad69483293a529382194a52c6318c6084c6021c631818c6318c6318c6318c730000000001000010000018c6318c6518c6318c63294a5294a3294a5294a59ce739ce619ce739ce73b5ad6b5ac0b5ad6b5ad68c6238c6318c6318c63118c6e18c6318c6318c63739ce739ce739ce739c17bdef7bdf27bdef7bdef739c1739ce739ce739ce0842108432084210842110842108421084e108560843608421084210842110842108421084310856631916318c631916318cb5ac8b5ad6b5ad6b5ad6000000000000003000030842208422084210842142108421084210e4210ec3304c6318c4304c631842208441084421042108c6318c618ac620ac6318f7bdef7989f79c9f7bde18c6318c6318c6318c6ec6318c6184c6244c6318f7bdef7982f7a42f7bdee739ce7380e7021e739cc6318c6185c6205c63181086210c4210c631084218c6318c6318c7218c63b5adbb5ad6b5ad6b5ad6b5ad8b5ad6b5ad6b5ad610856108421084210842b5ad6b4442b5ad6b5ad6b32c2b5ad6b46c2b5ad6b5ad6b4c42b5ad6b5ad6c6318c6318c4a10c631842248441084425042108e739ce739ce4929e739c42248421084225242108c6318c6318c4484c6318b5ad6b5842b59ceb5ad6b5ad6b5b18b5b10b5ad6b5ad6b5b9cb5b89b5ad6b5ad6b5b18b5b04b5ad6f7bdef7bdef4442f7bdeb5ad6b5842b5863b5ad694a4394a5294a5294a5208421084380842108421084210843c08421084216318c631986318c6318c6318c631966318c6318cb5ad2b5ad6b5ad6b5ad6084320842108432084219ce739ce739ce739ce7394a5294a5294a4f94a5294a5294a5294a4e94a5208421084210843108421b5ad6b5ad6b5aceb5ad6739ce739ce739d3739ceb3ac2b5ad6b32c2b5ad642108441084411042108c6318c6318c4250c6318b5ad6b5ad0b5ad6b5ad642110421084211042108c6301c6318c6318c631842108421104211042108842108421084213842109ce739ce739ce709ce73c630dc6318c6318c6318084300842108430084216318c631916318c631916318c6318e6318c6318e108421084d1084d10842842108421284210842100842108430084300842194a5294a5294a5094a526318c6318c6318c631986318e6318c6318c6318e6318c6318c631916318c8c6318c6318c62c8c631421084210c4210c421086318c6318c631936318c9ce739ce739ce6c9ce736b5ad6b5ad6b5ae6b5ada5294a5294a528da5294c6318c6318c35edc6318e739ce7021e71cee739cc6302c6318c6318c6318c09a2c6318c6318c6318c6318c4042c6318c63186318c6318c631906318cb32c3b5ad6b36c3b5ad6b62d8b5ad6b62cfb5ad6e739ce739ce2649e739cb5ad6b5ad2b5ad6b5ad6e5ad6e739ce739ce739cc6318c6f7bc6318c6318e7381e739ce739ce739c084290842108429084216318d6318c6318d6318ce7388e739ce739ce739c10842108481084810842084210842908429084214a5294a5324a5294a52994a5294a5294a4994a524a5294a5294a52a4a5296318c6318d6318d6318c5294a5294a529495294a8c6318c6318c62d8c6314210c42108421084210c42108421084211342108a5294a5294a5288a529442108421084210e4210842108421084210d42108e738ee739ce739ce739cc6318c6021c61efc6318e739ce739ce21c8e739cc6318c6186c6206c6318f7bdef7982f79c2f7bdee0781e739ce739ce739cf33c9f7bdef3bc9f7bdef33c3f7bdef3bc3f7bde10862144421446310842e7108e739ce739ce739c18c631c8421c86318c43e739ce71cee739ce739cc6318c6187c6247c6318f7bdef7983f7a43f7bdec30a5c6318c6318c6318b32c2b5ad6b3ac2b5ad6b62d8b5ad6b62c2b5ad6b72dcb5ad6b72c3b5ad6b32ccb5ad6b3ecfb5ad6420a843d0843ca542108b5ad6b5989b5a49b5ad6c6318c6318c1224c6318b5ac4b5ac4b5ac2b5ac4b5ad6b5ac5b5ad6b5ad6b5ad6b5ad1b5ad6b5ad6b5ad6b5acfb5ad6b5ad6c5ad6c6318c6318c6318f3bc2f7bdef33c2f7bdec6f7bc6318c6318c6318f33ccf7bdef3fcff7bde4210f421084210f42108421084210f4210f421087bdef7bdef7bdf37bdef9ce739ce739ce6f9ce73c6305c6318c6318c631808424084210842408421084250842108425084216318f6318c6318f6318cc630ac6318c6318c631808421084240842408421210842108421092210840842108425084250842121084210842108a210848c6318c6318c6248c6318c6318c6318c6258c6316318c6318f6318f6318c421084210a4210a421088c6318c6318c62a8c63121084210842108f2108410842108451084510842294a5294a5294b1294a59ce739ce739ce659ce736318e6318c6318e6318c294a5294a5294af294a5294a5294a5294ae294a5c630cc6318c6318c631894a5294a5294a4594a52294a5294a5294a7294a539ce739cef39ce739ce76318c6318c631856318c08421084250842108425b3042b5ad6b5ad6b5ad6b5ad6b2589b5ad6b5ad6b0ac2b5ad6b3aceb5ad6b62d8b5ad6b62d0b5ad6b72dcb5ad6b72c9b5ad6b62d8b5ad6b62c4b5ad6f7bdef7bdef0a22f7bdeb0ac2b5ad6b0ec3b5ad6b5ad6b5ac3b5ad6b5ad610842108511085110842b5ad6b5ad3b5ad6b5ad6f5ad6f7bdef7bdef7bde10a021484214a1010842c05a1c6318c6318c6318e0781e739ce4390e739cc4704c6318c3304c6318c6318c3042c6318c6318def7bdef7bdef7bdef7be739ce5ad6e739ce739ce739ce21c8e739ce739c39ce739ce739ce739ce784090846108448484210c30c6c6318c6318c6318c6318c6021c6084c6318e739ce7021e70a5e739cc6318c5ad6c6318c6318420e842108420e742108c6318c298ac6318c6318f7bdef2589f7bdef7bde7bdef7bdf17bdef7bdef084210842f0842f08421084210842e0842e084219ce739ce739ce729ce7321084210842109121084b5ac2b5ad6b5ad6b5ad60842208421084220842108423084210842308421b5ad6b5ac2b5ad6b5ad60842108422084220842108421084230842308421318c6318d1318c6318c68c6318c6318c6238c631b5ad6b5ac9b5ad6b5ad6840508461084442842106b44d6c1ad6c0426b5ad7bc4f7bdef7bc427bdeff7842f7bdef7bdef7bde420684210842063421086324c6258c626496318cf7bdef25e9f7bdef7bdeb5ad6b5accb5ad6b5ad610842108431084310842b5accb5ad6b5ad6b5ad69ce739ce739ce639ce734a5294a5294a5234a5291084e108421084e108420842f084210842f084210842e084210842e08421631906318c631906318cf7bccf7bdef7bdef7bde94a5294a5294a4394a5218dc31c8631c9ce18c63c0b02c6318c0701c6318e7380e739ce0781e739cc330ac6318c430ac6318c3307c6318c4307c6318f3129f7bdef7bdef7bdef3063f7bdef7bdef7bde108451084210845108420842108423084210842394a5294a5294a5294a528421084210842038421084210842108421284210e739ce739ce739ce739c7bdef7bdef7bde37bdef318c6318c6318cf318c67bdef7bdef7bdf27bdef294a5294a5294a5294a5f7bdef7bdef7bdef7bde631966318c6318c6318cb5ad6b5ad6b5ac1b5ad618c6318c6318c7118c630842e08421084210842eb5ad6b5ac8b5ad6b5ad6084220842108421084220842108421084210843c6318c63190631906318c6318c6318e6318e6318c18c6318c6e18c6318c638c6228c6318c6318c631084210843208432084216318c63191631916318cb5ad6b5ad6b5ad3b5ad6421084211342113421088c6318c6318c6318c6318421084210842108421018d231c8631c92918c63e0501e739ce739ce739cc6318c6021c6129c6318c3305c6318c3705c6318f33c3f7bdef37c3f7bdee739ce739ce2021e739cc3306c6318c4306c63187384e745ce74442739cef3042f7bdef7bdef7bdec6318c6021c6042c6318e739ce7021e7063e739cc6318c618cc630fc6318f7bdef7bdef2649f7bde739ce739ce739d0739ce084380842108421084210843c084210842108421631986318c6318c6318c6319e6318c6318c6318c1084310842108431084208421084220842108422084210842e084210842e631926318c631926318c109c214442145ce10842c0701c6318c4b12c6318c0701c6318c3f0fc6318e0781e739ce4b92e739ce0781e739ce3b8ee739cc6318c639cc6389c6318c3304c6318c4704c6318c3305c6318c4305c6318c6301c6301c6304c6301c731cc6318c7305c6318f33c2f7bdef47c2f7bdef33c2f7bdef3bc2f7bdec6318c63dec63c2c6318e739ce73dee73c3e739cc6318c63dec63cfc63184a4694cd294cc634a52942028439084382142108c6318c6042c6021c6318e739ce71cee7021e739cc6318c618ac624ac6318f7bdef7989f7a49f7bde8c6318c6318c62f8c6318c6318c6318c6308c6318c6318c6318c62e8c6317bde07bdef7bdef7bdef7bdef7bdef7bdef7bde184210842108420b842107bdef7bdef7bdeb7bdef18c6318c6418c6318c6384210842108420a842107bdef7bdef7bdea7bdef8c6318c6318c6228c631108421084210853108426b5ad6b5ad6b5a96b5ad21084210842108d21084294a5294a5294a8294a5421084210842105421085294a5294a529455294a294a5294a6294a5294a57bdef7bde97bdef7bdef7bdef7bdef7bdf67bdef739ce739ce739d1739ce84210842108420f842109ce739ce739ce619ce738c6318c6318c6328c631739cc739ce739ce739ce7bde17bdef7bdef7bdef8420c8421084210842107bde87bdef7bdef7bdefb5acab5ad6b5ad6b5ad66b5ad6b5ad6b5b06b5ad42108421084211142108294a0294a5294a5294a518c6318c6318c6318c62739ce739ce739cb739ce739ce739ce739c9739ce7bdef7bdef7bde97bdef6318c6318c631926318c739ce739ce739c3739ce739ce739ce739cf739ce739ce739ce739d2739ce739ce739c2739ce739ce739ce739cc739ce739ce0000000000000110000021084210842108621084084210843008421084218c6318c6318c62b8c631a5294a5294a5294a5294739ce739c1739ce739ce8c6318c6318c6298c63194a5294a5294a4194a52b5ac9b5ad6b5ad6b5ad6084210843208421084320842e08421084210842118c6318c7318c6318c6318c6718c6318c6318c6318c6318c6318c6f18c6308421084210842f084214a5294a5294a5294a52900000000000000f00000084210842108421084200000000000000100000000000000000000d0000010842108421084c108426318c631826318c6318c08421084210842c084216318c631816318c6318c6318c6318e6318c6318c6318c631886318c6318c318c6318c6318ca318c65294a5294a529465294a6318c6318c6318e6318c5294a5294a529475294a6318c6318c631836318c08422084210842108421084210842c084210842118c6218c6318c6318c6318c6318c6318c6d18c63108421084210850108425294a5294a529435294a4a5294a5294a5214a529739ce739ce739ce739ce0842108421084210842e842108420184210842100842008421084210842118c6318c6318c6418c632108421084210832108418c6318c6018c6318c63294a5294a0294a5294a5294a5294a5294aa294a5294a5294a5294a6294a5318c6318c6318c5318c618c6318c6318c6518c63294a5294a5294a3294a56318c6318c6318d6318c294a5294a2294a5294a50842108424084210842118c6318c6818c6318c635294a5294a529415294a4a5294a5214a5294a52910844108421084210842b5ad6b5ad6b5ad6b5ad6084210842108432084211084210840108421084221084210842108e2108408421084210842a084216318c6318c631846318c21084210842108521084210842108421084210844a5244a5294a5294a52910842108421085110842108411084210842108421084210842108521084218c6118c6318c6318c63a5282a5294a5294a529410842108421084f10842108421084210849108427bdef7bde27bdef7bdef7bdef7bde17bdef7bdef842108420c84210842107bdef7bdef7bdef7bdef842038421084210842104a5294a5284a5294a529f7bc3f7bdef7bdef7bde4210842108421014210808421084280842108421084210842108421084216318c6318c6318a6318c5294a5294a5294b5294a21084210842108121084739ce739ce739c1739ce4a5294a5294a52b4a5290000000000000030000000000000000000100000084210842008421084210842108425084210842108421084230842108421c6318c6318c6318c63186318c6318c631826318c108421084410842108424a5294a5244a5294a5291084210841108421084218c6318c6118c6318c636318c6318c6318c6318c18c6318c6318c6318c634a5284a5294a5294a52900000000000000e0000000000000000000c000000000000000000080000000000000000000400000000000000000002000001084210842108421084218c6318c6318c6e18c6318c6318c6318c6718c63842018421084210842104210842108421084210818c6318c6218c6318c63084210842e084210842118c6318c6718c6318c63842108421084201842104210842108421034210810842108421084510842294a5294a5294a2294a5318c6318c6318c3318c610842108421084e108421084210842108481084210842108421084410842108421084210846108420842108421084240842108421084210842508421210842108421082210844210842108421024210808421084210842208421084210842108423084216318c6318c6318f6318c108421084210843108421084210842108411084242108421084210a4210808421084210842d084218c6318c6318c6288c631a5294a5294a5281a529408421084210842e084210842108421084300842110842108421084d108420842108421084280842108421084210842908421421084210842109421088c6318c6318c6218c6316318c6318c631816318c4a5294a5294a5324a529084210842208421084217bdef7bdef7bde17bdef6318c6318c631896318c00000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (0,1,0x0,0x0)

def c3 : Catalogue := (0,1,0x0,0x0)

def c4 : Catalogue := (0,1,0x0,0x0)

def c5 : Catalogue := (3,58,0x2246d18c5b16437831b46916c590de0c6d18c6216437,0x55434345500000005543545440000000555443444)

def r5_0 : List Hint := [(0,0x300580a0100240400500e0180280300800c01001),
  (0,0x300580f0100380400500e0180280300800c06801),
  (0,0x300580a0100380400500e0180280300800c06801)]

def c6 : Catalogue := (333,68,0x831f06316c400dc0a831e86316c490dc0a831b46316c4910035831b4631704910038831b46316c4910c388e1b463124400dc1d831b46316c491002d831b463124400dc1e831ac6316c4910037831b86416c4910037831b8631704910037831b46316c4b10037831b46316c4d10437831b46416c4d10037831b4631704d10037831b46316c4810037831b46316c4d10c37831b46616c4d10037831b46316c4d1003c831b46316c4d11437831b46316c5611037831b46316c4a11037831b46316c4910837831b46416c4911037831b4631704911037831b46316c4c11037831b46316c490fc37831b46316c4911034831b46316c491103d831b46316c4f11037891b46316c4911037831b46916c4911037831b4631884911037831b46316c5511037831b46316c4911024831b46316c590dc25831b46316c590f837831b46816c4910037831b4631844910037831b46316c5310037831b46316c49118378318c5b124400dc19832047f1b44910037832047c1b45b10037831fc7c1b46310037832047a1b45b12437831fc7a1b46312437831f07a1b46316c37831f87a1b46316c378e2207c18c5b100378e2207a18c5b124376d18c5b124400dc188e1fc6d18c49100378e1e86d18c5b124376d18c5b124400dc2b832045b124400dc29831fc63124400dc29832046d16c4910037831fc6d18c4910037831f06d18c5b10037831e86d18c5b12437831b463124400dc1d831b463124400dc0e831b86316c4911011831b46316c4d11011831b46316c5911011832086d16c4910037832006d18c4910037831fc6d18c4910011831e86d18c5b12411832006d18c4910011831b46312440070118318c49100370a41c881b86316c4910011831b46316c4a10437831b46316c5710437831b463124400dc1f831e46d18c5b12444831b46416c4910037831b4631704910037831b46316c4c10037831b46316c4910c37871b46816c4910037871b4631844910037831b4681844910037871b46316c5310037831b46816c5310037831b4631845310037871b46316c4911837831b46816c4911837831b4631844911837831b46316c5311837831b46316c5a11837831b4631744910037831d063124400dc1e831e4631244006c0d831b46317c491001e831b463124400cc1e8318c5e124400dc1e831b463134400dc1e831b463124440dc1e831e46d18c5b13444831e46d18c491101e831e46d18c5b16444832047916c4910037831fc7918c49100378820c811e45b124408820c7f1e46312440831fc791b46312440831e8791b46316c49831e06d18c5b12440831e46316c4911011831b46316c4910012831b46316c400dc27831b46316c490dc26831b463124400b81e831b463124400b81c8318c49100370b81e8318c49100370b81c6d18c5b124400bc2e6316c49100370bc2e6d18c49100370bc1e6d1a05b124400dc2f6d18c61124400dc2f6d18c5b14c400dc2f6d18c5b124460dc2f871b46316c4910037831dc6d18c5b12440871e46d18c5b12440831a86416c4910037831a8631704910037831b4641704910037831e46d18c5c12440831b46416c4c10037831b4631704c10037831b46416c4910c37831b4631704910c37831b46316c4c10c37831b46316c5810c37831e46d18c5b12443831b4631704910034831b46316c4910c34831b46316c4910037871b46416c4910037871b4631704910037871b46316c4c10037871b46316c4910c37871b46316c4910034871b46316c4910038871b86316c4910037871b46316c4d10037871b46316c4911037871b46316c491002e8718c5b124400dc2e871b46316c4910038872046d16c4910037871fc6d18c4910037871f06d18c5b10037871e86d18c5b12437871b86316c4910037871b46316c4a10037871b46316c4910437871b463124400dc1e871e46d18c491001e831b46816c491002e831a05b124400dc2e791a05b124400dc2f871b46816c4910037831b46716c4910037831b4681704910037831b46816c4c10037831b46816c4910c37871e46d1a05b12440871e46816c49100376816c49100370bc29871a05b124400dc29831b46816c400dc22831b46816c5010037831b46816c491003a831a86816c4910037831b86816c4910037831b46816c4d10037831b46816c4911037831b468124400dc1e831e468124400dc1e831e46816c4910029831a05b124400dc29831bc6816c4910037831b463184491002e8318c61124400dc2e791b463184491002f7918c61124400dc2f871b4631844910037831b4641844910037831b4631804910037831b4631844c10037831b4631844910c37871e46d18c6112440871e46318449100376318449100370bc298718c61124400dc296d1a061124400dc2f871b4681844910037831a061124400dc29831e46d1a06112440831e4681844910037831b4631844910034831b4631844910038831b463184491003b831a8631844910037831b8631844910037831b4631844d10037831b4631844911037831b463124400dc1c831e46d18c491001c831e463184491001b831e463124400dc1c831e46318449100298318c61124400dc29831e463184491000d831c0631844910037831b46316c531002e8318c5b14c400dc2e871b46316c5310037831b46416c5310037831b4631705310037831b46316c5210037831b46316c5310c37871e46d18c5b14c40871e46316c53100378718c5b14c400dc296d1a05b14c400dc2f871b46816c5310037831a05b14c400dc29831e46d1a05b14c40831e46816c53100376d18c6114c400dc2f871b4631845310037831b46818453100378318c6114c400dc29831e46d18c6114c40831e4631845310037831b46516c5310037831b46316c531003c831b46316c5110037831b46316c5410037831b46316c5311037831b46314c400dc1e831c46316c5310037831b46316c460dc28831b46316c491182e8318c5b124460dc2e6d18c5b168460dc2f791b46316c491182f871b46316c4911837831b46416c4911837831b4631704911837831b46316c4c11837871b46316c5a11837871e46d18c5b12446871e46316c49118378718c5b124460dc296d1a05b124460dc2f871b46816c4911837831b46816c5a11837831a05b124460dc29831e46d1a05b12446831e46816c49118376d18c61124460dc2f871b4631844911837831b4681844911837831b4631845a118378318c61124460dc29831e46d18c6112446831e46318449118376d18c5b14c460dc2f871b46316c5311837831b46816c5311837831b4631845311837831e46d18c5b14c46831b46316c4911834831b46316c4911838831b46316c4e11837831b46316c491183d831b46316c5a0dc068a20c6d18c5b16837831b46316c5a0dc23831b46316c4d11837831b463124460dc1e831e46d18c491181e831e46d18c5b16846831c86316c4911837831e46816c4910037831e4631844910037831b46316c49110118318c5b124400dc2e831b46316c4a10037831b46316c4910437831b463124400dc1e871b46316c4910011831b4631844910011831b46316c4911811831b46316c4910037871b46316c4910011831b4631704910011831b46316c4910c11831b46316c4910013871b46816c49100116d18c61124400bc11871b4631844910011831b4681844910011871b46316c5310011831b46816c5310011831b46318453100116d18c5b124460bc11871b46316c4911811831b46816c4911811831b4631844911811831b46316c5311811831b46316c5a11811871e46d18c5b12440831b46316c491002e831e46d18c6112440831e46d18c5b12446871e46316c4910011831e4631844910011831e46316c49118116d18c5b124400dc2f871b46316c4910037831b46816c4910037831b4631844910037831b46316c5310037831b46316c4911837,0x56535355400000006554544550000000555353454000000055645345400000006554544550000000556453465000000055535345400000005564534540000000555353454000000055536455400000005564534540000000565353554000000066545455500000005653646540000000566453554000000056535355400000006654545550000000565364654000000056535355400000006654545550000000665454555000000066545455500000006554544550000000655465555000000065655445500000006654545550000000655454455000000065545445500000006554544550000000665454555000000065545446600000006554655550000000656554455000000066545455500000006554544550000000665454555000000066545455500000005553645540000000556453454000000056535355400000006554544550000000555353454000000055646455400000005653646540000000566453554000000065546555500000006565544550000000665454555000000066545455500000005653535650000000655454466000000055535346500000005564534650000000655454466000000055535346500000005553645540000000556453454000000055536455400000005564534540000000565353554000000065545445500000005564534540000000556453454000000065545445500000006654545550000000665454555000000055536455400000005564534540000000556453454000000065545445500000005564534540000000556453443000000055645344300000005553534650000000665454555000000066545455500000005564534540000000655454455000000055536455400000005564534540000000565353554000000065545445500000005553645540000000556453454000000055646454300000005653535540000000565364643000000056645354300000006554544550000000655465544000000065655444400000006654545440000000665454544000000055645345400000005564534430000000556453443000000055645344300000005564534430000000556453443000000056645355400000006565544550000000665454555000000065655445500000006654545550000000555364554000000055645345400000005553645540000000556453454000000055645345400000006554544550000000555353454000000065545445500000005553534540000000565353554000000065545445500000005564534430000000556453443000000055645344300000005564534430000000555353454000000055535345400000005564534540000000555364554000000055645345400000005653535540000000655454455000000055535346500000005553534540000000555353465000000055536455400000005564534540000000556464554000000055645345400000005653646540000000566453554000000065546555500000006565544550000000665454555000000066545455500000006554544550000000556453454000000065545445500000005553534540000000555364565000000055645346500000005653535650000000655454466000000055535346500000005553534650000000555353465000000056535356500000006554544660000000555353454000000055535345400000005553534540000000555364565000000055645346500000005653535650000000655454466000000055535345400000005653535540000000655454455000000055645345400000005564534540000000555364543000000055536454300000005553645540000000555364565000000055536455400000005564645540000000565364654000000065546555500000005553645540000000555364554000000055536455400000005553645540000000565364654000000056536464300000005553645430000000555364554000000055536455400000005653646540000000655465555000000055646454300000005564645430000000555364543000000055536454300000005553645430000000556453443000000055645344300000005564534540000000556453454000000055645346500000005564645540000000556453454000000056645355400000006565544550000000556453454000000055645345400000005564534540000000556453454000000055646455400000005564645540000000556464543000000055646454300000005564645430000000556453454000000055645345400000005564534430000000556453454000000055645345400000005664535540000000656554455000000055645344300000005564534430000000556453443000000055645344300000005564534430000000556453443000000055645344300000005564534430000000565353543000000056535354300000005653535650000000565364654000000056645355400000005653535540000000665454555000000056535355400000005653535540000000565353554000000056536465400000005653646540000000565364643000000056536464300000005653646430000000566453554000000056645355400000005664646430000000566453543000000056645354300000005664535430000000565364643000000056535354300000005653535540000000565353554000000066545455500000005664535430000000565353543000000066545454400000006554544440000000655454444000000066545455500000006554544550000000655454466000000065546555500000006565544550000000665454555000000066545455500000006554544550000000655454455000000065545445500000006554655550000000655465555000000066546564400000006554655440000000655465544000000065546554400000006565544550000000656554455000000065656554400000006665545440000000656554444000000065655444400000006565544440000000665454555000000066545455500000006654656440000000666554544000000066545454400000006554544550000000655454455000000066545455500000006554544440000000665454555000000066545455500000006654545440000000665454555000000065655444400000006565544440000000665454544000000065545444400000005553645430000000556453443000000065545445500000005553534430000000565353554000000065545445500000005564534430000000555353454000000055645344300000006554544440000000555353443000000055535346500000005564534540000000655454455000000055535345400000005553645540000000556453454000000055645345400000005564645430000000565353554000000056536464300000005664535430000000655454455000000065545445500000006554655440000000656554444000000066545454400000006654545440000000555353454000000055535344300000005564534430000000655454444000000055535345400000005564534430000000655454444000000055535345400000005553534540000000555364543000000055645344300000005653535430000000655454444)

def r6_0 : List Hint := [(0,0x1d0160280401c01006c0d01903005c0b01502804c0901202201408007),
  (0,0x1d0160280401c01006c1001903005c0f81502804c0901e02201408007),
  (0,0x1d0160280400901006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d01603c0401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0xf0120200c0190300540a8140260440880502001c0e80b01006c0b812),
  (0,0x120160440401101006c0d01903005c0b01502804c1282604a09011822),
  (0,0x120160440401101006c0d01903005c0b01502804c1282604a09011822),
  (0,0x120160440401101006c0d01903005c0b01502804c1282604a09011822),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0x2f0160b80402d01006c1601903005c1581502804c0901102201408007),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0x1d0160280401c0100dc0b0150280d81a8340660c80903102201403830),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0xa0380200d0190300580a8140260740580803605c1881100a04003812),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0x1d0160280401c01006c0d03803005c0b01502804c0903102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007)]

def r6_1 : List Hint := [(0,0xa0380200d0190300580a8140260740580803605c1881100a04003812),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0x1d01603c0400901006c0c01903005c0a81502804c0901102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0xc01603c0400901006c0c01903005c0a81502804c0901102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0903102201408007),
  (0,0x2f0160b80d82c03205c158150260f41e03c0580ac0183b0060e81c805),
  (0,0xc01603c040090100640c0190301001d84000a04c0183b0060fc1f001),
  (0,0xc01603c040090100440181100a0540a81502804c018110060fc21041),
  (0,0xb0100200d81903005c0a8140260f01e03c07a0f01d80307600c1d811),
  (0,0x1d0160280401c0100640d0190301000b04000a04c018430060341f001),
  (0,0x120160440401101006c0d01903005c0b01502804c1282604a09011822),
  (0,0x120160440401101006c0d01903005c0b01502804c1282604a09011822),
  (0,0x200160440401101006c0d019030054228150280600881202200c1f044),
  (0,0x120520a8058110520200280c0100dc0384802a0501b04708c0d019832),
  (0,0x3d0520000583c05206c1602803205c1582702a04c0183204800c1d039),
  (0,0x2f0160b80d82c03205c158150260f41e83c0580ac018120060e81c805),
  (0,0x1d0160280401c0100440901100a0540b01502804c0182500603421041),
  (0,0x1d0161380404d0100dc1b8150280480901100a01c2602609612c25049),
  (0,0x550a814c290510141402681c01004c2781602a0501801202404402807)]

def r6_2 : List Hint := [(0,0x590160282c01c01015c0b0150281580901100a01c150350680cc19047),
  (0,0x1d0160740400801006c0d01903005c1b81502804c0901202201408007),
  (0,0x1d0160280401c0101680b0150281681a83406604c0901202201403830),
  (0,0x4e0b60a40400c01006c1401903005c1381502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d03803005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0xa0380200d0190300580a8140260780880502001c0e80b01006c0b812),
  (0,0x120160440401101006c0d01903005c0b01502804c1282604a09011822),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0xb0100200d81903005c0a8140260480880502001c0e80a0380680b031),
  (0,0x1d0160280401c0100dc0b0150280d81a8340660c80902102201403830),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0xa0380200d0190300580a8140260840880502001c0e80b01006c0b812),
  (0,0x120160440401101006c0d01903005c0b01502804c1282604a09011822),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0xb0100200d81903005c0a8140260480880502001c0e80a0380680b031),
  (0,0x1d0160280401c0100dc0b0150280d81a8340660c80902102201403830),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0xa0380200d0190300580a8140260840880502001c0e80b01006c0b812),
  (0,0xb0100200d81903005c0a8140260480880502001c0e80a0380680b031)]

def r6_3 : List Hint := [(0,0x120160440401101006c0d01903005c0b01502804c1282604a09011822),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0x1d0160280401c0100dc0b0150280d81a8340660c80902102201403830),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0901e02201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d0190301700b01502804c0902102201408007),
  (0,0x2a0220a40280c0100401401903001c1381502804c090290160200d817),
  (0,0xa0380200b0150280d41a0330640480880500e0c00e80b0100dc2e812),
  (0,0xb0100200d81903005c0a814026044088030240140901102204822812),
  (0,0x1d0160740400801006c0d01903005c1b81502804c0901202201408007),
  (0,0x1d0160280401c0100d82f0340660481081100a0c01b81602a05009807),
  (0,0x12016044040110100640881903005c0f8150280501281e04a1843005f),
  (0,0x2f0160b80d82c03205c158150260f41e83c0580ac018200060e81c805),
  (0,0x1d0160280401c010064100190301000b04000a04c018620060341f05c),
  (0,0xc01603c040090100440881100a0540a81502804c0182500600821041),
  (0,0x1d01603c0400901006c0d01b0c605c0a81502804c0901102201421007),
  (0,0x290160a40405801006c3281903005c3201502804c0901e02201408007),
  (0,0x590180e00406801006c1c03803005c3381502804c0906602201408007),
  (0,0x120160440401101006c0d01903005c0b01502804c1282604a09011822),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0xb0100200d81903005c0a8140260480880502001c0e80a0380680b031),
  (0,0x1d0160280401c01006c0d03803005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007)]

def r6_4 : List Hint := [(0,0xa0380200d0190300580a8140260840880502001c0e80b01006c0b812),
  (0,0x120160440401101006c0d03803005c0b01502804c1282604a09011822),
  (0,0x120520a8058110520200280c01006c080280700600b80704e0540a013),
  (0,0xb0100200d83803005c0a8140260480880502001c0e80a0380680b031),
  (0,0x1d0160280401c01006c0d03803005c0b01502804c0902102201408007),
  (0,0xa0380200d0380300580a8140260840880502001c0e80b01006c0b812),
  (0,0xb0100200d81903005c0a8140260480880502001c0e80a0380680b031),
  (0,0x120160440401101006c0d01903005c0b01502804c1282604a09011822),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0901e02201408007),
  (0,0x1d01603c0400901006c1001903005c0a81502804c0901102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0xb0100200d81903005c0a814026094128610d4100090110220443481e),
  (0,0x290160a40405801006c3601903005c3581502804c0901e02201408007),
  (0,0x120160440406d01006c0d01903005c0b01502804c1282104a0ec11845),
  (0,0x120160442681c09a06c0d0190c605c0b0150c604c1283204a10c11822),
  (0,0xb0100200d81903005c0a8140260480880502001c0e80a0380680b031),
  (0,0x120160440400501006c0801903005c0381502804c1482a0520301406e),
  (0,0x3d0160f00d82c03205c15815026094000250460880182a0060e81c86f),
  (0,0x120160440400501006c0801903005c0381502804c1482a0521c01406e),
  (0,0x3d0520000583c05206c1602803205c1582702a04c0183204800c1d039),
  (0,0x2f0160b80d82c03205c158150260f41e83c0580ac0183b0060e81c805)]

def r6_5 : List Hint := [(0,0x1d016028040090100640d0190301000b04000a04c018710060341f05c),
  (0,0x1d016028040090100440d01100a0540b01502804c0187200600821041),
  (0,0x120e60440401101006c0d01903005c0b01502804c0882104a09011822),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x290161d00400901006c1401903005c1081502804c0902102201408007),
  (0,0x4e0b60a40400c01006c1401903005c1381502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x120160440401101006c0d01903005c0b01502804c1282604a09011822),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0xb0100200d81903005c0a8140260480880502001c0e80a0380680b031),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0xa0380200d0190300580a8140260840880502001c0e80b01006c0b812),
  (0,0xb0100200d81903005c0a8140260480880502001c0e80a0380680b031),
  (0,0x80320600a8140260440281000e02c0401b02e0480501c0340581881d),
  (0,0x120160440401101006c0d01903005c0b01502804c1282604a09011822),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d01603c0400901006c0c01903005c0a81502804c0901102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x110220200d0190300580a814026098128240460880900b01006c0b875),
  (0,0x2a0220a40280c0100401401903001c1381502804c090290160200d817),
  (0,0xb0100200d81903005c0a8140260941283b046114090110760680b021)]

def r6_6 : List Hint := [(0,0x290161d00400901006c1401903005c1081502804c0902102201408007),
  (0,0x120161dc0401101006c0d01903005c0b01502804c128210221d811805),
  (0,0xb0100200d81903005c0a8140260480880502001c0e80a0380680b031),
  (0,0x120160440400501006c0801903005c0381502804c1482a0520301406e),
  (0,0x3d0160f00d82c03205c15815026094000250460880182a0060e81c86f),
  (0,0x2f0160b80d82c03205c158150260f41e83c0580ac0181d0060e81c805),
  (0,0x1d01603c0401c0100640d0190301000b04000a04c018710060341f05c),
  (0,0x1d01603c0401c0100440d01100a0540b01502804c0187200603421041),
  (0,0x120160442681101006c0d01903005c0b01502804c0882104a09011822),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x2901603c0400f01006c1401903005c3c01502804c0902102201408007),
  (0,0x590160e00407c01006c1c03803005c3d8150281e80907902201408007),
  (0,0x2f10820c1681c05a0ac0b02b0280f01083c00a01c410811001fc3f07d),
  (0,0xb0100200d81903005c0a8140260480880502001c0e80a0380680b031),
  (0,0x80320600a8140260440281000e02c0401b02e0480501c0340581881d),
  (0,0x120160440401101006c0d01903005c0b01502804c1282604a09011822),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d01603c0400901006c0c01903005c0a81502804c0901102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x110220200d0190300580a814026098128240460880900b01006c0b875),
  (0,0xb0100200d81903005c0a81402609408876046014090030220680b021)]

def r6_7 : List Hint := [(0,0x290162080400f01006c1401903005c3c01502804c0902102201408007),
  (0,0x3d0520000583c05206c1602803205c1582702a04c0183204800c1d039),
  (0,0x2f0160b80d82c03205c158150260f41e83c0580ac0181d0060e81c805),
  (0,0xc0160280401c0100640d0190301000b04000a04c018710060341f001),
  (0,0xc0160280401c0100440d01100a0540b01502804c0187200603421041),
  (0,0x11016044040110100640d0190300540b01502804c0182104a09011822),
  (0,0x5c09c0582d8150140200a01c01006c0981a0320600900704204402810),
  (0,0x1b09c0682d8190140200c01c01005c0981602a0500901004204402807),
  (0,0x809c0702d80801406c0c01a03205c0a01602a04c0900504204408007),
  (0,0xb09c0280400803806c0c81a03005c0a81602804c0901104201408007),
  (0,0x1d0160a40400c01006c1401903005c1381502804c0902102201408007),
  (0,0xb0100200d81903005c0a81402604412824046088088110220680b021),
  (0,0x1d0160a40400c01006c1401903005c1381502804c0902102201408007),
  (0,0xc0160280401c0100640d0190301000b04000a04c018710060341f05c),
  (0,0xc0160280401c0100440d01100a0540b01502804c0187200603421041),
  (0,0x11016044040110100640d0190300540b01502804c0182104a09011822),
  (0,0x1d0160a40400c01006c1401903005c1381502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d0190301700b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0xc01603c0400901006c0c01903005c0a81502804c0901102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007)]

def r6_8 : List Hint := [(0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0x1d0160280401c0100dc0b0150280d81a8340660c80901202201403830),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0901e02201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d03803005c0b01502804c0902102201408007),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x120520a8058110520200280c01006c080280320600b80704e0540a013),
  (0,0x1203a0440581105c0200282d01006c0802c0320600b8070560540a013),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0xa0380200d0190300580a8140260480880502001c0e80b01006c0b812),
  (0,0xa0380201001903007c0a8140260780880502001c0e80b01006c0b812),
  (0,0xa0120200d0190300580a8140260840880502001c0e80b01006c0b812),
  (0,0xf0380200d0190300580a8140260840880502001c0e80b01006c0b812),
  (0,0x2e058064158150260f01e02c0560bc0581b02e0f41d8030740e402803),
  (0,0x80320600a8140260f01e03d07802c0401b02e0440183b0060ec08812),
  (0,0x2e05a020160190300ac0a8140260740580803605c0881100a04003812),
  (0,0xb0360640b8150260f01e03d0780f41e02c0560f4018030740e442843),
  (0,0xb0360640b8150260f01e03d0780f01e03c0780f0018030740e41e085)]

def r6_9 : List Hint := [(0,0x2f0160b80d82c03205c158150260f41e83c0580ac0183b0060e81c832),
  (0,0x2f0160b80d82c03205c158150260f41e03c0580ac0183c0060e81c805),
  (0,0x1d0160280401c0100640d01903000c2280307e0f82004508001409801),
  (0,0x1d0160280401c0100540b01502800c0900307e1040881102201409842),
  (0,0x860b60b80402d01006c1601903005c1581502804c0901102201408007),
  (0,0x11016044040110100640d0190301000b04000a04c018870060901d022),
  (0,0x121100442d81101e0200280901006c080180320600b80702a0540a013),
  (0,0x1702401c4486e05416c0a8110520200a0050180200d8130200a00c818),
  (0,0x80240144480c05416c0401105206c0c0100500640b81400e09c0a813),
  (0,0x2a11816c1088b0221d42d80802222832818034064110640280580a813),
  (0,0x2a0ea16c1088b0222302d808022228328190340601106402a0580a013),
  (0,0x80240442d80802206c0c01a03205c0a01602a04c1282404c09411822),
  (0,0xb0240440400802206c0c81a03005c0a81602804c1282504c09011822),
  (0,0x30180a8058771100200680c0100144808f00c0143088e11a0d801032),
  (0,0x11018000058111100640d0180321001b82708004c0189204800c1d091),
  (0,0x30180a8058771100200680c0100ec498940220141d89311e10002813),
  (0,0x2f0160b80c82c0321001e0400260441d8110341700183b0060e84880d),
  (0,0x2f0160b80883c02205415815026044350400ae2540183b0062441c84b),
  (0,0xb12c0b80d81905805c0a82b0260f01e03c07a0f01d80307600c1d811),
  (0,0x2f0160b80d82c03205c158150262581782e0580ac090110221e83d005),
  (0,0xc0162201e83c07806c0c01905805c0a01505604c018030060141d039),
  (0,0x3d0160f00d82c03205c158150262601509112e25c018320060e81c831),
  (0,0x2f0160b80d82c03205c1581502626c1e03f1342644c03b13025c4b897),
  (0,0xc0162202d80c0161940c0190301900a81502804c3c0110220140989c)]

def r6_10 : List Hint := [(0,0x1d0160280401c0100dc0b0150280d81a8340660c80901202201403830),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0901e02201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d03803005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0901202201408007),
  (0,0x1d0160280401c01006c1001903005c0f81502804c0901e02201408007),
  (0,0x1d0160280400901006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d01603c0401c01006c0d01903005c0b01502804c0902102201408007),
  (0,0x30180a8058771100200680c0100641f0180320602000104e10002813),
  (0,0x2f0160b80d82c03205c158150260f41e03c0580ac0183b0060e81c805),
  (0,0xc01603c040090100142280600a184308360040c80183b0060fc4f09d),
  (0,0xc01603c040090100ec0181100a0ec1d84000a04c0183b0060fc4f89f),
  (0,0x120221dc0886d01006c0881903005c5081502804c150a00060901d039),
  (0,0xb0360640b8150260f41e02c0560bc1702c0560c4018030740e40281d),
  (0,0x2f0160b80d82c03205c1581502600c0e8030740e41e8310780b015805),
  (0,0x81440702d8080141940c01a0321900a01602a04c1080506204408007),
  (0,0x1709c0582d8150140200a01c01006c0981a0320600900706204402810)]

def r6_11 : List Hint := [(0,0x809c0702d80801406c0c01a03205c0a01602a04c0900506204408007),
  (0,0x81440242d8080141940c01a0321900a01602a04c1080504204408007),
  (0,0xb14603c2d8080381940c81a0301900a81602804c1081104201408007),
  (0,0x1d0160280401c0100140b00600a1841a8360040c801843006034480a4),
  (0,0x1d0160280401c0100ec0d01100a0ec0b04000a04c0184300603449893),
  (0,0x110e60442681101006c0d01903005c0b04000a04c018710060901d022),
  (0,0x960b60b80d82c03205c158150260f41e03c0580ac0183b0060e81c805),
  (0,0x960b60b80d82c03205c158150260f41e03c0580ac0183b0060e81c805),
  (0,0x1709c0582d8150140200a01c01006c0981a0320600900702404402810),
  (0,0x1b09c0802d8190140200c01c01005c0981f02a0500901003c04402807),
  (0,0x809c0242d80801406c0c01a03205c0a01602a04c0900504204408007),
  (0,0xb09c03c0400803806c0c81a03005c0a81602804c0901104201408007),
  (0,0x80b60200d81803205c0a0150260480281102001c2701c0140680b031),
  (0,0xb0100200d81903005c0a8140260480880502001c2700a0380680b031),
  (0,0xa0380200d0190300580a814026044088110221000880300604420012),
  (0,0x1705425c4401514e0200a0a701006c098a60320600900714a04402810),
  (0,0x805412c4400814e06c0c0a603205c0a0a802a04c0900514a04408007),
  (0,0x2e05a020160190300ac0a8140260f00880502001c0e80c01006c0b812),
  (0,0x1203e2b00780202a0240101401008055813032060128261522a8068a9),
  (0,0x120402ac078020320240101801007c5601302a050128261522a8068a9),
  (0,0x3706c0c8270160a816c0a8520140200a0500380200900706004808805),
  (0,0x1b02e04c2701a02c16c0c8150140200c0140380200901000e07808805),
  (0,0x802e0502701c02c16c0401501406c0c0130340640900500e08408810),
  (0,0x5b02e0542700a02c0200401403806c0c8130340600901100e08402810)]

def r6_12 : List Hint := [(0,0x80360602701c03416c0401901405c0a01302c0540900502008408807),
  (0,0x5b0360e02700a0340200401803805c0a81302c0500901102008402807),
  (0,0x5b0100202700a03806c0c81803405c0a81402c04c0901100a08408007),
  (0,0x2e05a020160190300ac0a8140260f41e03c07a0f01d80307600c1d811),
  (0,0x1d0160280401c01006c0d01903005c0b01502804c0901202201408007),
  (0,0x1d0160280401c01006c1001903005c0f81502804c0901e02201408007),
  (0,0x1d0160280400901006c0d01903005c0b01502804c0902102201408007),
  (0,0x1d01603c0401c01006c0d01903005c0b01502804c0902102201408007),
  (0x8a50001214000075,0xc0160280400e0100140380600a124218490921c001804006034008ad),
  (0,0xc016220040080100140280600a00c0180301a0042582609612c250ae),
  (0,0x1d0160280401c0100640d0190301000b04000a04c018710060341f001),
  (0,0x590162cc040b2010064588190301005804000a04c018af0060341f05c),
  (0x65,0x590162cc04009010064080190301000384000a0c8018040060341f05c),
  (0x465,0x5901603c0400e010064080190301000084000a0c8018a90060341f05c),
  (0x865,0xc0162cc0400e010064080190301005a04000a0c8018a90060341f05c),
  (0,0xc01603c040090100142200600a1842283607e04c018030060344805c),
  (0,0xc016220040080100640c0190301000284000a04c018030060341f001),
  (0,0xc0160280401c0100640d0190301000b04000a04c018710060341f001),
  (0,0xc0160280401c0100640d0190301002284000a04c018450060fc1f001),
  (0,0xc0160280401c010064100190301000b04000a04c018620060341f05c),
  (0,0xc016028040090100640d0190301000b04000a04c018710060341f05c),
  (0,0xc01603c0401c0100640d0190301000b04000a04c018710060341f05c),
  (0,0x1d0160280401c01006c0d01903005c0b0170c604c1007308001408001),
  (0,0xc01603c040090100ec0181100a0ec2284000a04c018030060344985c)]

def r6_13 : List Hint := [(0,0x1d0e603c268090100dc0b0b60c60d81a83600404c5a8061540344805c),
  (0,0xc01603c0400901000c0881107e0141d83f00a04c018030060085c0b7),
  (0,0xc016220040580100441281100a0540a01502804c0182500600821041),
  (0,0xc01803c040580100440281100a0540a01502804c018b900600821041),
  (0,0xc0160280401c0100440901100a0540b01502804c0182500603421041),
  (0,0xc0160280401c0100440881100a0540b01502804c018120060fc21041),
  (0,0xc016028040090100440d01100a0540b01502804c0187200600821041),
  (0,0xc01603c0401c0100440d01100a0540b01502804c0187200603421041),
  (0,0xc01603c040090100ec0881100a0ec1d84000a04c018030060085d8ba),
  (0,0x1d0160280401c01006c0d01b0c605c0b01502804c0901e02201421007),
  (0,0x11016044040110100640d0190300540b01502804c0182104a09011822),
  (0,0x11016044040110100640d0190300540b01502804c0182104a09011822),
  (0,0x3b0161dc0406d0100643b8190300543681502804c018110780f01e83c),
  (0,0x2f0160b80d82c03205c158150260f41e03c0580ac0183b0060e81c805),
  (0,0x2f1040b80e02d01006c1601903005c1581502804c0901102201408007),
  (0,0x1103000d8bf03205c5f0150260f45e83c0580ac018bc0060e81c805),
  (0,0x1d0160a40400c01006c1401903005c1381502804c0902102201408007),
  (0,0x1d0160a40400c01006c1401903005c1381502804c0902102201408007),
  (0,0x2f0160b80402d01006c1601903005c1581502804c0901102201408007),
  (0,0x170b60540401401006c098190300480381100a040248160140700d012),
  (0,0x1b0b60640401801005c098150280480801100a01c248200140700f81e)]

def c7 : Catalogue := (402,78,0x831b46316c491003400e0c6c18c5b124400dc0a831b463124400dc1d02a0c6d18c49100380dc1d0020c6d18c49100370760c6d18c5b124400e004831a86316c491003702a0c6d1905b124400dc0a831b463170491003702a0c6d18c5b130400dc0a831b46316c4910c3702a386d18c5b124400e037831b46316c491002c00638831b86316c49100378e20c6d18c5b128400de38831b46316c49104378e20c6316c491003705e38831b463124400dc1f8f20c6d18c5b124400da0c791b46316c4910037831a86316c49100370060c6d18c5b128400dc05831b46316c49104370160c6d18c5b124400d805831b46316c49100370a60c6e18c5b124400dc04831b46416c49100370160c6d18c5c124400dc05831b46316c4c100370160c6d18c5b124430dc05831b46316c49100340160c6d1a86316c4d10037831b46316c4d100370060c6e1b46316c4d10037831b46316c4d100370120c6d18c5b134400dc21831b46316c4d1003705a0c7d1b46316c4d10037831b46316c4d11c400de0c6d18c5b164440dc05831b46a18c5b124440de0c6d18c5b124440dc01831b86d18c5b124440de0c6d18c5b124440dc04831b46316c4d1103701400831b46316c4d11037831b46316c49110370960c6d18c5b124440dc15831ec6d18c5b124440de0c6d18c5b124440f8370020c6d18c5b164440de0c6d18c5b124400dc328318c5b124400dc1700e20831b46316c49100388820c6d18c491003707e20831b46316c491002c8f20c6c18c5b124400de20832046d16c49100378820c7f1b463124400de20831f06d18c5b100378820c7a1b46316c490de0c811b46c16c49100370020c811b45b124400de0c7f1b46c18c49100370020c7f1b463124400de0c7c1b46c18c5b100370020c7c1b46316c400de0c7a1b46c18c5b124370020c7a1b46316c490de0c6d18c5b124400dc118e2206316c491003705e38881b06316c49100378e1b46c18c5b124400de38881b46316c491002c8e2206d18c5b124400da206d18c5b124400dc36881b86d18c5b124400de206d18c5b134400dc05881b46316c49110370160c6d18c5b124400d029831b46316c49100390de0c6d18c5b134400dc29831b46316c49110370a60c6d18c5b124400dc2a8318c5b124400dc2905e0c6c18c5b124400dc29831b46316c49100380a6386d18c5b124400dc03831b46c18c5b124400de0c6c18c5b124400dc03831b46316c49100380de0c6d18c5b124400e003861b46316c491003700e186d18c5b124400dc0a882186d18c5b124400de0c6d18c5b124400dc14831b46316c491002c0460c6a18c5b124400dc11831b46316c4d100370460c6d18c5b124440dc11831b46a18c5b124400460c6a18c5b1244004405831b86316c49100110160c6d18c5b1344004405831b46316c491101101400831b46316c4911011831cc6d18c5b124400de206d18c5b1244004405831b46c18c5b1244004638881b46316c49100118820c731b46316c491020c731b46316c4910011831b46316c491001100e18831b46316c4910011831b46316c491002e0a60c6d18c5b124400b8118318c5b124400dc2e0a60c6316c49100370b811881b46316c49100110060c6e18c5b124400dc11831b46316c4a100370460c6d18c5b124410dc11831b46316c4910036046206d18c5b124400dc01831b86d18c5b124400de0c6e18c5b124400dc01831b46316c4a1003700400831b46316c4a10037831b46316c491043700400831b46316c4910437831b46316c49100370da0c6d18c5b124400d801841b46316c4910011016106d18c5b124400dc018e2106d18c5b124400de106d18c5b124400dc05831b46316c491003702e3c831b46316c4910037831e46d18c491003707800831b463124400dc1e831e46d18c5b1244001620831e46d18c5b12440001b46316c49100370be0c6d18c5b124400dc048720c6d18c5b124400de1c6d18c5b124400dc320021c6d18c5b124400de0c6d1a05b124400dc320020c6d1a05b124400de0c6d18c61124400dc320020c6d18c61124400de0c6d18c5b14c400dc320020c6d18c5b14c400de0c6d18c5b124460dc320020c6d18c5b124460de0c791b463124400dc1f8f1b46316c491003702e3c8318c5b124400dc17831b46316c491003705e3c831b463124400dc1f0020c6d18c491003707e3c831b46316c491002c831b46316c49100370b20c751b46316c49100378e1b46316c491003702e0c791b46316c491002c831e46d18c5b124400da0c6d18c49100370780b8f20c6d18c491003707a0c7918c49100370780d831e46d18c491001e06e0c6d18c49100370780a8e20c6d18c491003707a0c6d18c4910037078028520c6d18c491003707a0c6d18c49100370780d831b463124400dc1e06e0c6d18c491003707805831d86d18c5b124400de0c791b46316c4d10037831e46d18c5b124440de0c791b4631244007805831e4761b46316c491020c761b46316c4910005831e46d1a86316c491020c791b46316c4d10005831e46d18c5b1244401400831e46d18c5b12444881b46316c491003702e0c7918c5b124400dc17831e46c18c5b124400de20831b463124400dc1e881e46d18c5b1244001620791b46316c491000b8820c7918c5b1244005e20831e46c18c5b12440831e46d1b06316c4910238881e46d18c5b124408820c791b4631244007a0c6d18c49100370a41e831e46d18c491002907a0c791b46316c49100038620c791b46316c491020c6d18c491003707811831e463124400dc1e0460c7918c5b12440044058820c7918c5b124400460c7918c5b124400a411831b46316c49100380ca0c6d18c5b124400dc31831b86316c49100370ca0c6d18c5b134400dc32831b46316c49110370ca0c6d18c5b124400dc30831b463124400dc3207a0c6d18c5b124400dc2e831e46d18c491003207a0c791b46316c491002e831b46316c49100320b800831b46316c491002e831e463124400dc3207a0c7918c5b124400dc2e8318c5b124400dc320b8008318c5b124400dc2e791b46316c49100320bde46316c49100370c82f791b46316c49100370bdb46316c49100370c82f831a86316c49100370ca0c6d1905b124400dc32831b46317049100370ca0c6d18c5b130400dc32831b46316c4910c370ca0c6d18c5b124400d032831e46d18c5b1244001000871b46316c4910037831b46a18c5b124400de0c6a18c5b124400dc04831b46416c491003701000831b46416c4910037831b463170491003701000831b4631704910037831b46316c4c1003701000831b46316c4c10037831b46316c4910c3701000831b46316c4910c37831b46316c49100370d20c6d18c5b124400d004871b46316c49100370121c6d18c5b124400dc0a871b46316c49100370161c831e46d18c5b12440871e46d18c5b124400ca1c7918c5b124400dc32871b46316c491003700e38871b46316c4910037871b46c18c5b124400de1c6d18c5b124400dc018821c6d18c5b124400de1c6d18c5b124400dc36871e46d18c5b124400dc00871e46d18c5b12440871b46316c49100370c9b46316c49100370bc29871b46316c49100370a60c6d18c5b124400dc038620c6d18c5b124400de0c6316c49100370c829831e46d18c5b124400a58c5b124400dc320bc298718c5b124400dc320a60c7918c5b124400c829831b46316c49100370a60c791b46816c4910032831e46816c49100370c9b46816c49100370c82f001b46816c49100370be0c6d1a05b124400dc048720c6d1a05b124400de1c6d1a05b124400dc320021c6d1a05b124400de0c6816c49100370c829831b46816c491003702a38831b46816c4910037831b46816c491003702634831b46816c4910037831b46816c491003706a0c6d1a05b124400dc058820c6d1a05b124400de0c6d1a05b124400dc290020c6816c49100370a60c791b46816c49100370020c791a05b124400de0c6d1a05b124400dc0c831e46d18c61124400ca0c7918c61124400dc326d18c61124400dc320bc006d18c61124400dc2f831b46318449100370121c831b4631844910037871b46318449100370c800871b46318449100378318c61124400dc320a60c6d1a061124400dc320020c6d1a061124400de0c6d18c61124400dc0a8e20c6d18c61124400de0c6d18c61124400dc088c20c6d18c61124400de0c6d18c61124400dc1b831b463184491003701620831b4631844910037831b46318449100370a4008318c61124400dc29831e46d18c61124400dc00831e46d18c61124400020c7918c61124400de0c6d18c61124400dc0d831e46d18c5b14c400ca0c7918c5b14c400dc326d18c5b14c400dc320bc006d18c5b14c400dc2f831b46316c53100370121c831b46316c5310037871b46316c53100370c800871b46316c53100378318c5b14c400dc320a60c6d1a05b14c400dc320020c6d1a05b14c400de0c6d18c6114c400dc320020c6d18c6114c400de0c6d18c5b14c400dc0a8e20c6d18c5b14c400de0c6d18c5b14c400dc078b20c6d18c5b14c400de0c6d18c5b14c400dc20831b46316c531003701620831b46316c5310037831b46316c53100370a60c791b46316c5310037831b46316c531003703e0c6d18c5b168460dc32831e46d18c5b124460ca0c7918c5b124460dc326d18c5b124460dc320bc006d18c5b124460dc2f831b46316c49118370121c831b46316c4911837871b46316c49118370c800871b46316c49118378318c5b124460dc320a60c6d1a05b124460dc320020c6d1a05b124460de0c6d18c61124460dc320020c6d18c61124460de0c6d18c5b14c460dc320020c6d18c5b14c460de0c6d18c5b124460dc0a8e20c6d18c5b124460de0c6d18c5b124460dc068a20c6d18c5b124460de0c6d18c5b124460dc230020c6d18c5b168460de0c6d18c5b124460dc058820c6d18c5b124460de0c6d18c5b124460dc29831e46d18c5b124460dc00831e46d18c5b12446831b46316c4911837041b46316c49100370bc11871b46316c49100370460c6d1a05b124400dc11831b46318449100370460c6d18c5b14c400dc11831b46316c49118370460c7918c5b124400dc32831b46316c491001101620831b46316c49100118318c5b124400dc290460c6d18c5b124400dc018420c6d18c5b124400de0c791b46316c4910037831e46316c49100370460c6d18c5b124400c8116d18c5b124400c82f0460c6d18c5b12440044048720c6d18c5b124400461c6d18c5b124400c8110021c6d18c5b124400460c6d18c5b124400a4118318c5b124400c8290460c6d1a05b124400c811831b463184491003204400831b4631844910011831b46316c53100320460c6d18c5b124460c8110020c6d18c5b124460460c791b46316c4910032831e46316c49100320460c6d18c5b124400dc32831b46316c491003704400831b46316c4910037,0x66646456500000006664645650000000667564565000000066756456500000006675645650000000666464565000000066646456500000006664756650000000667564565000000067646466500000007665655660000000666464576000000066646456500000006664645650000000676464665000000076656556600000006664645650000000667564565000000066646456500000006664645650000000666464565000000067646466500000007665655660000000666464565000000066646456500000006664645650000000666475665000000066756456500000006764646650000000766565566000000066646456500000006764646650000000676464665000000067646466500000006764646650000000676464665000000067646466500000006764646650000000676464665000000077656566600000007665655660000000766565566000000076656556600000007665655660000000776565666000000077656566600000007665655660000000766565566000000076656556600000007665655660000000776565666000000066646456500000006664645650000000666464565000000066756456500000006664645650000000666464565000000066647566500000006675645650000000676464665000000076656556600000006664756650000000666475665000000066756456500000006675645650000000676464665000000067646466500000007665655660000000766565566000000066646456500000006664645760000000666464576000000066646457600000006664645760000000666464576000000066646457600000006664645760000000676464676000000076656557700000006664645650000000666464565000000067646466500000007665655660000000666464565000000066646456500000006664645650000000666464565000000066646457600000006664645650000000666464565000000066646456500000006664645650000000666464576000000066646457600000006664645760000000666464565000000066646456500000006664645650000000676464665000000076656556600000006664645650000000666464565000000066646456500000006764646650000000766565566000000076656556600000006664645650000000666464576000000066646456500000006664645760000000666464565000000066646456500000006664645650000000666464565000000066646455400000006664645540000000666464554000000066646455400000006664645760000000666464565000000067646466500000007665655660000000666464565000000066646457600000006664645650000000666464565000000067646466500000006764646650000000766565566000000076656556600000006664645650000000666464565000000066646457600000006664645760000000666464576000000066646457600000006664645650000000666464565000000066756455400000006675645540000000666464565000000066646456500000006664645650000000666464565000000066646456500000006664645650000000666464565000000066647565400000006664756540000000667564554000000066756455400000006764646540000000676464654000000076656555500000007665655550000000667564565000000066646457600000006664645650000000666464565000000066756456500000006675645650000000666464565000000066646456500000006664645650000000666464576000000066646456500000006664645650000000667564565000000066756456500000006675645540000000667564554000000066756456500000006675645650000000667564565000000066756456500000006675645540000000667564554000000066756456500000006664645650000000676464665000000076656556600000006675645650000000666464565000000066646456500000006664645650000000676464665000000076656556600000007665655660000000666464576000000066646456500000006664645650000000667564565000000066646457600000006664645760000000666464565000000066646456500000006664645650000000666464576000000066756456500000006675645540000000667564554000000066646456500000006664645650000000667564554000000066756455400000006664645650000000666464565000000066646455400000006664645650000000666464565000000066646456500000006764646650000000766565566000000066646456500000006675645540000000666464554000000066756455400000006664645540000000666464554000000066646455400000006675645540000000666464554000000066646455400000006664645540000000666464565000000066646456500000006664645650000000666464565000000066646456500000006664756650000000667564565000000067646466500000007665655660000000666464565000000066646456500000006664645760000000666464565000000066646456500000006664756650000000666475665000000066756456500000006675645650000000676464665000000067646466500000007665655660000000766565566000000066646456500000006664645650000000666464576000000066646457600000006664645760000000666464565000000066646456500000006664645650000000666464565000000066646457600000006664645760000000666464565000000066646457600000006664645760000000666464565000000066646456500000006664645760000000666464565000000066646456500000006664645650000000666464565000000066646455400000006664645540000000666464565000000066646456500000006664645540000000666464554000000066647565400000006664756540000000666475665000000066647566500000006664756650000000666475665000000066647566500000006664756650000000666475654000000066647566500000006664756650000000666475665000000066647566500000006664756540000000666475665000000066647566500000006664756540000000666475654000000066647565400000006664756540000000666475654000000066756455400000006675645540000000667564565000000066756456500000006675645650000000667564565000000066756456500000006675645650000000667564554000000066757565400000006675756540000000667564565000000066756456500000006675645650000000667564565000000066756455400000006675645650000000667564565000000066756455400000006675645540000000667564554000000066756455400000006675645540000000667564554000000067646465400000006764646540000000676464665000000067646466500000006764646650000000676464665000000067646466500000006764646650000000676464654000000067647575400000006764757540000000677564654000000067756465400000006764646650000000676464665000000067646466500000006764646650000000676464654000000067646466500000006764646650000000676464654000000067646465400000006764646540000000776565655000000076656555500000007665655550000000766565566000000076656556600000007665655660000000766565566000000076656556600000007665655660000000766565555000000076657665500000007665766550000000767665555000000076766555500000007765656550000000776565655000000076656556600000007665655660000000766565566000000076656556600000007665655550000000776565655000000076656556600000007665655660000000766565555000000076656555500000007665655550000000766565555000000066646456500000006664645650000000666475654000000066756455400000006764646540000000766565555000000066646455400000006664645650000000666464565000000066646455400000006664645650000000666464565000000066646455400000006664645540000000666464554000000066646456500000006664645650000000666464565000000066646456500000006664645650000000666464554000000066646455400000006664756540000000667564554000000066756455400000006764646540000000766565555000000076656555500000006664645540000000666464554000000066646455400000006664645540000000666464554)

def r7_0 : List Hint := [(0,0xd51a834c690d11a033c670cd19832c650c919031c630c518830c610c1),
  (0,0x3a02c050080380200d81a0320600b81602a0500989b03a0fc1f89a132364218d81ae3586b026),
  (0x51b400106500031140008350001094000015,0x3a02c050080380200d81a0320600b81602a050098120420440281000e0a8218dd1b836c6d070),
  (0x20c50007254001875,0x2402c088080220200d81a0320600b81602a050098700003783809a0e00941302504808c11043),
  (0xc194002c5d000a094002405,0x240a41500b0220a4040050180200d8100500640c01700e09c0a8140261c0000431bc1c04d070),
  (0x3466000911c001846,0xd51a834c690d11a033c728cd198390718e21c23806303118830c610df),
  (0x123340044c50010294003c95000e214000005,0x3a02c050080380200d81a0320600b81602a0500982a0543746e0db0e00481881100a04003800),
  (0x54c50014294004c95000e1d4000405,0x3a02c050080380200d81a0320600b81602a050098490aa124248700920481881100a04003800),
  (0xa11c001c46,0xd51a834c758ea1d233c728cd1d032c650c91ce31c63031188398610c1),
  (0x18334005cc50016294004c85000f1d4000805,0x3a02c050080380200d81a0320600b81602a0500982a04c374380db1b40481881100a04003800),
  (0x64c5001625400508500101d4000c05,0x3a02c050080380200d81a0320600b81602a050098ec0641c0760ec1d80481881100a04003800),
  (0,0x160200401b0320600b81502804c4b02e05a0b01581d0140700d0160e00480880502001c21831),
  (0x2c05,0x5e02c1700805a0200d82c0320600b82b02a050098980542444889712e0482181100a04003800),
  (0xc11c002046,0xd51a834c690d11a033c728cd19832c650c919031c6303118830c610c1),
  (0x64a5001725400548500111d4001005,0x3a02c050080380200d81a0320600b81602a050098701da3746e0db1b40481881100a04003800),
  (0,0x54074790de1e20284c8f10380204d0f00340640c0ac1e00580a8140263bc7703102201408007),
  (0x1d194007035001b054006805,0x3a02c050080380200d81a0320600b81602a050098120620440281000e000000de0e026838000),
  (0x183d40048d5001d1d4001415,0x140700401a0320600b01502804c000de0e02683801d0160200d8170000c40880502001c00012),
  (0x21314008095001f1d4007805,0x3a02c050080380200d81a0320600b81602a050098700003783809a0e00481881100a04003800),
  (0x785d,0x2402c088080220200d81a0320600b81602a0500989b0000fc1f89a13200c000030480e81c831),
  (0x894d,0x1b20301500b1ee220040f60180200d8f50300640c0171e80500a81402626c130f307e0fc4d099),
  (0,0x543ec7d0f70b60287c85b038020780650340640c0f00c80580a8140263e04581d07e0fc4d099),
  (0x24094008c15,0x3a1cc0504d0380200d81a0320600b81602a050098b503a0fc1f89a1320c4218d81ae36c7e026),
  (0x9405,0x160200401b0320600b81502804c1e83c0780b01581d0140700d0160e000c018240740e413000)]

def r7_1 : List Hint := [(0,0x540747903f0b60281f85b0380204d0650340640c0ac0c80580a81402609845843154034548a9),
  (0x9815,0x3a1cc0504d0380200d81a0320600b81602a050098b50862a8068a91520c40e83f07e268380f8),
  (0x945d0028114009c35,0x2402c088080220200d81a0320600b81602a0500982504c0941202304416c000430860600a070),
  (0x18b5,0x3a02c050080380200d81a0320600b81602a050098d90543606b8d61fa364188d81ae3587e826),
  (0,0x3a02c050080380200d81a0320600b81602a05009901200008010381fe3647f0d81ae0e06b026),
  (0x72d4009c55,0x3a02c050080380200d81a0320600b81602a050098d904c360810d61ac364000d82043586b026),
  (0xa055,0x3a02c050080380200d81a0320600b81602a050099041460e011103206364000381ae3586b026),
  (0x20b5,0x3a02c050080380200d81a0320600b81602a0500989b1da3606b8d61ac364828d81ae3586b026),
  (0,0x140700401a0320600b01502804c0e83f07e2684c81d0160200d81713610c6c0d71ac358130d9),
  (0xa455,0x3a02c050080380200d81a0320600b81602e1e0098120240446b83e1fa41c000d820c35882826),
  (0x64bc007d2e002b37c00a806,0xc621c0a86a10d1a6348860d11a033c8590a19a33072109210388708e0),
  (0x2c534001849,0x1b20a41500b1ee224040f60520200d8f50500640c01722043c0a814026364130311b035c6b099),
  (0x2405,0x5202c448080520200d8280320600b8fd02a0500981222a0440281000e450151132244447e800),
  (0,0x544607d0f70b60287c85b038020780650340640c1170c80580a81402609845916154034548a9),
  (0xb425,0x3a1cc0504d0380200d81a0320600b81602a050098b522c2a8068a91520c46c8d81ae36c8c826),
  (0xc0ab002f29c00b89f000d12c00a847,0xd51a834c690d11a04808f8e21c24788e8e21c20e06311c18830c8d91a),
  (0x2e35400c405,0x3a02c2700809a0200d81a0320600b8fd02a050190120240440281000e4501311322444438000),
  (0xbc75,0xaa498299250a20289204d0380207801a0340640c0322462d85b1221da4840901202201408090),
  (0x3035400c825,0xb202c050580380202b81a032060950b616c48876856024044028101200a89492824e36c1908e),
  (0,0x540a89712d1bc3009609917c0207a89a17e0640c1171582f80a8140263b87712b02201408007),
  (0x3403400cc05,0xa616c6000817c0200d8bf0320600b8be02a050098122560440281000e1c0151132244448c826),
  (0xe12c00d447,0xd51a834c690d11a04d89a934266390718e21c24c86313118830c9812f),
  (0xe46d003819400dc4500360d400380d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e0a89b8dd1b80e02e000),
  (0xf466003c138003c4b003b11c00e846,0xd51a834c758ea1d233c728cd1d0390718e2272380630211884e06112f)]

def r7_2 : List Hint := [(0x401b400fc65003c17400f8450036094003c0d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e0a8000dd27436c2e000),
  (0x11066004313800404b004211c010446,0xd527e4f8690d127a33c7293c198390719321c23806302127630c6112f),
  (0x461b4011465004317400f835003709400400d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e0a8000381b836c2e000),
  (0x47314010cb5003c294000005,0x160200401b0320600b81502804c0901100a040038310620c4140430540740501c03405818800),
  (0x12866004713800444b004911c012046,0xd51a834c690d11a033c728cd198500718e21c23806302118830c6112f),
  (0x11c5d004511400fc35003809400440d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e170000dd1b836c2e000),
  (0,0x5450ca10f11e2028788f1038020780f00340640c05c1e00580a8140265047702102201408007),
  (0x13865004d114013035004b09400d00d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e000188dd1b836c2e000),
  (0x140b600122ac013ca7,0xd31a2340728cd19852c710e11c0470620c3184528a494828e518a2944),
  (0x118b5004029400e49500121f4013805,0x140700401a0320600b01502804c1081100a040038311ba3706d85c0000740580803605c09000),
  (0x120650051174010445003a0d400180d,0x2402c088080220200d81a0320600b81602a0500982504c094120230440c4000310620a021800),
  (0x4f1b40124650052174010835003b09400d415,0x240a41500b0220a4040050180200d8100500640c01700e09c0a8140260a8000311ba3706d870),
  (0x501b4012865004411400f43500530b400340d,0x3a02c050080380201b81602a0501b0350680cc19012042044028070600a8188dd1b80002e000),
  (0x15055,0x3a02c050080380200d8200365340b81f02a0500986b0cc10001038082364000d82984146b026),
  (0x1554d,0x1b25481500b1ee54c040f62a40200d9512a00640c0171e853c0a8140264041314e004008558ff),
  (0,0x2a402ca98082a40200d8380320600b94f02a050098121600440281000e450151132240e0aa049),
  (0,0x5455cab0f70b60287c85b038020a88650400640c0f00c807c0a81402609845955154034548a9),
  (0x1602d0057094015815,0x3a1cc0504d0380200d8200320600b81f02a050098b52aa2a8068a91520c4838d81ae0c87e026),
  (0x5a114016405,0xb202cac0080d00200d8380320600b86702a050098120cc0440281000e450150dd2243b0aa000),
  (0,0x5455cac1612c0028af95e038020191232b8574ae15b12a07c0a8141805682b01e022014ac807),
  (0,0x3a02c050080380202995c2ba5701b81f02a0506001203c0440295900e154b31652c80c8b1962),
  (0,0x540a89712d1bc3009609917c020a889a17e0640c0f41582f80a8140265a4b416702201408007),
  (0,0xa616c6000817c0200d8bf0320600b8be02a050098122ce0440281000e1c015113224444aa16a),
  (0x5d138004c4b005c11c016c46,0xd51a834c758ea1d24d89a9342d832c650c91ce5ac630211884e0980c1)]

def r7_3 : List Hint := [(0x601b4017c65005d1740178450036054004c0d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e0a8000dd2740e06d000),
  (0x6313800504b006211c018446,0xd527e4f8690d127a4d89a83826632c6516d1905ac6302127630c980c1),
  (0x651b40190650063174017835003705400500d,0x3a02c050080380200d81a0700600b81602a050098120420440281000e0a8000381b80e06d000),
  (0x66314018cb5005d294000405,0x160200401b0320600b81502804c0901100a040038fe1fc3f82194f0aa0740501c03405818800),
  (0x6613800544b006811c019c46,0xd51a834c690d11a05b89a93426632c650c91905ac6302118830c980c1),
  (0x1985d0064114017c35003805400540d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e170000dd1b80e06d000),
  (0,0x545c4a10f11e2028788f1038020b80f00340640c0f01e00580a8140265bc7702102201408007),
  (0x1b465006c11401ac35006a0b401a415,0x3a02c050080380200d81a0320600b81602a050098120420440281000e0007f0dd1b80007e049),
  (0,0xd31a2340bd1342665e4bc1772ec5d4620c32605d0a494828e5ccb9144),
  (0x652d40180a5003921401b405,0x140700401a0320600b01502804c1081100a040038fe1ba3701c0fc0920740580803605c09000),
  (0x6719401b85d0061114016c35,0x2402c088080220200d81a0320600b81602a0500982504c094120230443f8000fe1fc10ca7849),
  (0x1a065006f174018835005c09400d405,0x240a41500b0220a4040050180200d8100500640c01700e09c0a814026124000fe09212438049),
  (0x712d401c055,0x3a02c0504d0381340d81a03218c0b81602a18c0982104c1148101000e364000d80863586b032),
  (0x7443c01cc4f007213801c42b,0x1801a84347597f1d233c728cd1d032c650c91ce31cbf0261885f4be17b),
  (0x74bc00812e007637c01d4ce,0xc621c0a86a10d1a63acbf9831d233c8590a19a3a065982302324738c7),
  (0x1dd4d0073134001c49,0x1b24501500b1ee4b4041020180200d8f51ea0640c0171e83d00a814026364130311b00fc6b0d6),
  (0x2701c01cc06,0xd41d63a4678cd1d032c648e718e318621381843046a98730c614c2031),
  (0x732d4002805,0x22802c968082040200d8f50320600b8f402a0500981204c0440281000e45015113204444aa000),
  (0,0x54508a10f70b6028c405b012020780650340640c0f00c80580a8140260984592b154034548a9),
  (0x7b17401e855007909401e015,0x3a1cc0504d0120200d81a0320600b81602a050098b52562a8068a91520c4150d81ae36c7e026),
  (0x752d401f005,0x31402cc48082040200d8100320600b80702a0500981204c0440281000e450151130e0444aa000),
  (0,0x54654511940080282199301c648c8191034064c719031e0580a98e026634c602102262c08007),
  (0,0x3a02c0505101c6480d81a0326380b81602a63809812042044c581000e21ccb19808665ccb996),
  (0,0x540a89712d1bc300cc89917c0207a89a17e0640c0f41582f80a8140263b87712b02201408007)]

def r7_4 : List Hint := [(0x7e03401f405,0xa616c6000817c0200d8bf0320600b8be02a050098122560440281000e1c015113224444aa026),
  (0x8113800584b008011c01fc46,0xd527e4f8758ea33433c7293c1d032c6516d1ce31c630212764e0610c1),
  (0x831b40208650081174017825003e05400580d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e0a80003827436c6d000),
  (0x853340210c500812d4017495003c214000805,0x160200401b0320600b81502804c0901100a0400382a1ba10c6d8da04c0740501c03405818800),
  (0x84138005c4b008711c021846,0xd51a834ccd8ea1d233c728cd1d032c650c91ce31c630211884e0610c1),
  (0x2105d0082114017c25003f054005c0d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e170000dd27436c6d000),
  (0,0x545c0a10f11e2028ce0f1038020780f00340640c0f01e00580a8140265047702102201408007),
  (0x23065007b174022c45008a0f4022425008805401f80d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e000000dd00036c7e000),
  (0x852b80060ab008e29c0234a6,0xd31d43a4728cd1d05e4bc19f33c084621381845d0a494833a518b9144),
  (0x85334020cb5006025401008500181f4023005,0x140700401a0320600b01502804c1081100a040038001ba4e86d8fc0000740580803605c09000),
  (0x2346d0086194023c5d007f114016c25003a054001c0d,0x2402c088080220200d81a0320600b81602a0500982504c094120230440a8000dd08636c6d000),
  (0x2386d008719402405d0073134020035005c05400ec05,0x240a41500b0220a4040050180200d8100500640c01700e09c0a8140260a8000001ba1c06d8da),
  (0x24455,0x3a1cc050080381340d81a0360600b81602e050098783400e00289c138364000431ae3586b026),
  (0x2510f009313c02484e,0x18027e6886910c27a33c7293c19832c6516d19031cbf02634230cbe17b),
  (0x95534024c4d,0x1b24501500b346220040f62580200d8f51ea0640c0171e83d00a814026410130ec00408881903),
  (0x2801c024c06,0x13f1a44f46793c19832cb68c818e3189d8c31843046a9a5348614c2031),
  (0x24cb5,0x22802c1c0082580200d8f50320600b8f402a050098120640440281000e45015038224444aa0ec),
  (0,0x54508a11a30b603c7c85b038020780650340640c0f00c80580a8140260984592b154034548a9),
  (0x991740260550097094025815,0x3a1cc0784d0380200d81a0320600b81602a050098b52562a8068a91520c4150d81ae36c7e026),
  (0x9b094026805,0x34e02c1c00834c0200d9a00320600b87a02a050098123400440281000e4501504922436caa000),
  (0x2711d,0x546c851843362638d81030386bcd71ac0346ac0c1ad358058d58140266a8d482135001408007),
  (0,0x3a144c70080386bc0d81a3560600b816356050098120426a00281000e3b0db04336a6d0d9951),
  (0,0x540a8971ba1bc3009609917c0207a89a17e0640c0f41582f80a8140266e4dc1b702201408007),
  (0,0xa616c6000817c0200d8bf0320600b8be02a0500981236e0440281000e1c015113224444aa1bb)]

def r7_5 : List Hint := [(0x9e3340274c50081294018c950043214000c05,0x160200401b0320600b81502804c0901100a0400382a0863706d8da0640740501c03405818800),
  (0x9d13800644b00a011c027c46,0xd52dc4f8690d127a33c7293c19832c6516d19031c6302127630c610c1),
  (0x2745d00820d4019025004505400640d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e170000381b836c6d000),
  (0,0x545c0a119c1e2028788f1038020780f00340640c0f01e00580a8140266f07702102201408007),
  (0xa519402645d00a4134028c3500a2094028415,0x3a02c050080380200d81a0320600b81602a050098120420440281000e000000001b836c7e0ec),
  (0x9e2b80298a6,0x13e1a24f47293c1985e4df97733c6f89d8c31845d0a49bd28e518b9144),
  (0x278cd00832940194950046214029405,0x140700401a0320600b01502804c1081100a040038000703706d8fc1d80740580803605c09000),
  (0xa61b4027c6500a717401fc350061094010415,0x2402c088080220200d81a0320600b81602a0500982504c094120230440a8000431b836c6d0ec),
  (0xa019402a05d00931340200250062054010805,0x240a41500b0220a4040050180200d8100500640c01700e09c0a8140263b0000000e03b0760ec),
  (0,0x1802c440080180200d8180320600b81402a0500981208a0440281000e45015113224444aa070),
  (0x9329401cc95,0x2402c0880800a0200d8100320600b80702a0500985b00010c218180280a4150290180a037070),
  (0x274b500842940198950047214001005,0x160200401b0320600b81502804c0901100a0400384320a414829051da0740501c03405818800),
  (0x279150085414001415,0x100640c01502804c0880502001c218430300500000b01006c0b81220a0280e01a02c0c40001d),
  (0x785d,0x240300000b022220040050180200d8100300640c01700e0500a814026260000311222444b897),
  (0x248b50072294007805,0x160200401b0320600b81502804c0901100a0400385b08610c0c0140000740501c03405818800),
  (0,0x544989712d1bc220960990180207a89a0300640c0f41580500a814026704e004502201408007),
  (0,0x38416c440080180200d8180320600b81402a0500981208a0440281000e1c015113224444aa070),
  (0x3005,0x5202ce20083860200d9af0320600b9c302a050098122560440281000e45015113224444aa000),
  (0,0x110030040180320600a01502804c2281100a040038290160200d8170240a88991222255038114),
  (0x29445008c0d401b425004e05400740d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e170828dd1b836c7e000),
  (0x212f00214b802a4df,0xc621c0a86a10d1a6348860d11a033c8590a19a33065982302324640c7),
  (0xaa534002049,0x1b20a41500b1ee710040f63860200d8f535e0640c0171e870c0a81402626c131051b035c6b0d6),
  (0,0x3a1cc0504d0380200d81a0320600b81602a050099150420440281000e0c4e39c638c3586b1c5),
  (0,0x545087d0f70b60287c85b038020780650340640c0f00c80580a814026098458a9154034548a9)]

def r7_6 : List Hint := [(0x2b45500ac09402ac15,0x3a1cc0504d0380200d81a0320600b81602a050098b51522a8068a91520c4000d81ae36c6d026),
  (0x2c56500b04d402bcf500ae294007449,0x9c1c07685b01472c0401c3940200d81a3920640c01702c7200a8140260481085c02201408007),
  (0,0x540a89712d1bc3009609917c0207a89a17e0640c0f41582f80a8140263b8e00a902201408007),
  (0x2c805,0xa616c6000817c0200d8bf0320600b8be02a050098121520440281000e1c015113224444aa000),
  (0xb3174027c4500860d4019c25004805400200d,0x2402c088080220200d81a0320600b81602a0500982504c0941202304410c0010520a41482800),
  (0x2d05d00a00d4021c250068054012405,0x240a41500b0220a4040050180200d8100500640c01700e09c0a8140261c0001051ba3706d8da),
  (0,0x54504770293980a86f0f10220a44c8f100a0300409a1e0040140190302b07800704e0540a013),
  (0x2dc5500b609402d415,0x3a1cc0504d0380200d81a0320600b81602a050098b51522a8068a9152498828d81ae36c7e026),
  (0xb903402e005,0xa616c6000817c0200d8bf0320600b8be02a050098121520440281000e49815113224444aa026),
  (0x2f44500bc0d402ec2500ba05402e40d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e170828dd1b836c7e000),
  (0xb919403003500bf05402f805,0x3a02c050080380200d81a0320600b81602a050098120420440281000e000000de0e026838000),
  (0,0x3a02c050080380200d81a0320600b81602a0500989b03a0fc1f89a1323647d8d81ae3586b026),
  (0x30866001b12c030447,0x1d23a234ce80d11a073c728cd198738a58e21c2380e691c18830c6114a),
  (0x2e86500c511403103500c309402fc0d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e000188dd1b836c2e000),
  (0,0x1d23a234ce80d11a074cbd1342665c8bc9782ee5d8e697518830c98174),
  (0xbb194031c4500c60d4030c15,0x3a02c050080380200d81a0320600b81602a050098120420440281000e0007f0dd1b80e07e049),
  (0x1c12c032047,0x1d23a234cea8ea1d273c728cd1d05c8bc97833e678e69d41884e061174),
  (0xbc19403285d00c911403182500c405403000d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e000000dd27436c7e000),
  (0,0x1d23ae4f8e80d127a73c7293c1985c8bc9bf2ee678e69d627630c61174),
  (0x2f46500cb17403243500c7094031415,0x3a02c050080380200d81a0320600b81602a050098120420440281000e000000381b836c7e0ec),
  (0x2f85500cb114032835,0x3a02c050080380200d81a0320600b81602a050098120420440281000e414000430860600a000),
  (0,0x524501500b1104b40400c2580200d8181ea0640c0170283d00a814026048229c102201408007),
  (0x1d12c033047,0x1da1a834c690d11a033c728cd198764bc9782ee678ec1d418830c61174),
  (0xcc19403345d00c8094030405,0x240a41500b0220a4040050180200d8100500640c01700e09c0a814026000000431bc1c04d070)]

def r7_7 : List Hint := [(0xb919401f835003405402f805,0x3a02c050080380200d81a0320600b81602a050098120420440281000e1c0000de0e02683805c),
  (0x2e86500a11140220350069094006c0d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e76c188dd1b836c2e000),
  (0xbb19402884500890d4012c15,0x3a02c050080380200d81a0320600b81602a050098120420440281000e76c7f0dd1b87707e049),
  (0x2f06500a311401ac25004c05400700d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e76c828dd3ba36c7e000),
  (0xbd194022c35006c094013415,0x3a02c050080380200d81a0320600b81602a050098120420440281000e76c829dc1b836c7e0ec),
  (0x2f855009911401ec35,0x3a02c050080380200d81a0320600b81602a050098120420440281000e7782e0430860600a000),
  (0x348b500d129403409500cf214033805,0x140700401a0320600b01502804c1081100a040038431ba3706d8fc0e00740580803605c09000),
  (0x34d8d,0x543dc440f60180207a8180320607a01402a050098261e60fc1f89a1324601480b01006c0b89b),
  (0x350cd00a62d40234a5,0x220440401a0320600b01502804c1302504808c1100008610c0c0140e00480580803605c3a905),
  (0xd5334023895004f1d4033005,0x5404414805018020080280320600382702a050098000863783809a0e00481480b01006c0b800),
  (0x3583a,0xd41a4340678cd19832c648c818e600620c33c6788c00c43c2780c21df),
  (0xd433402ccc500a72d4023ca5006e254014485,0x160200401b0320600b81502804c1282504808c1102a1ba3706d8da0000480881103405810843),
  (0xd75f401d039,0x1b202c7b8081ec0200d8f50320600b8f402a050098250000941202304400c150030860e81c9e4),
  (0x35cbd009429401d009,0x7a02c1e01b0580640b82b02a04c1280004a08c1105b00010c0c0140e000c150030740e437843),
  (0x3602a,0xd51a834c690d11a033cf40cd19832c650c919031c631e7188784f31e5),
  (0xd533402d0c500a8294024095006f214014875,0x5202c148080180200d8280320600b82702a0500982a0003746e0db1b40481081100a04003870),
  (0xd953401d829,0x1b20a40000b1ee0a4040f60180200d8f50500640c0171e809c0a814026260130f31301c04b897),
  (0xa93140364bd002b1d401d809,0x7a0a40000b0780a40d82c0500640b82b04e0540987000010c6f09a0e000c190240060e81c870),
  (0x1dc39,0x22802c968082580200d8f50320600b8f402a050098d93d63606b8d61ac364f50d81ec444aa1e9),
  (0xd333402a8c50095294015495002c21401dc09,0x5e02c1701b0580640b82b02a04c1e83d0780b01582a0863746d8da0e000c0e8030740e402902),
  (0,0x28416c0505b0380203281a0320603201602a050098f303a0fc1f89a1327b87d8d81ae7b4f69ec),
  (0xb519402584500780d401582500da07400980d,0x3a02c050080380200c81a03206020016080014098030e200c0683e0b87bc218dd1b836c2e000),
  (0x2d865009711401e43500db0b400b415,0x3a02c050080380200881a0220140a81602a050098030e400c068420827bc218dd1b81707e049),
  (0x2dc65009811401e835,0x241cc0884d0220200d81a0320600b81602a050098110420941202304410c828430860600a070)]

def r7_8 : List Hint := [(0,0x18378440990180204d0180320605601402a050098ee08a0440281000e7c094913224444aa1c1),
  (0xb819401f435003305403700d,0x9c16c148080180200d8280320600b82702a050098120420440281000e1c0218de0e026838000),
  (0,0x7a02c1e0080780200d82c0320600b82b02a050098980542444889712e00c130030480e81c831),
  (0,0x540747903f0b60441f85b0220204d0650340640c0ac0c80580a8140260c4f89c50060901d039),
  (0x37415,0x3a1cc0884d0220200d81a0320600b81602a050098ff38a00c1203a0720c40003f07e268381e4),
  (0x885d,0x7a02c1e01b0580640b82b02a04c4d80007e2684c80305400c1d03912200c000030740e41886f),
  (0,0x5e02c1701b0580640b82b02a04c4d82f07e2684c80320400c1d039122364218d81ac35800102),
  (0,0x54504770293e6000f90de022220f909900a030040a81340400c0190302a0560070280540a013),
  (0x3785d,0x2416c0005b022220040050180200d8100300640c01700e0500a8140261c0000311222444b897),
  (0x88bd,0x7a0300000b0782200d82c0300640b82b028054098980000c44889712e00c190240060e81c9f4),
  (0,0x1802c4401b0300640b81402a04c1e83c0780b01591400044c889540e000c120030740e481102),
  (0,0x547dcfb1f50b60001f85b00c2204d06517e0600c8ac0c82f80a015026244f889204800c1d039),
  (0x331b1,0x2422c7c0433e63b44403f1547100603f01a70c040651342fcd7819030190560be3860540a013),
  (0xcc61403717d00e0394037c35,0x242241507000010c2d811052378040050181c00401b0200a04d01903005c038270e00540a013),
  (0xe24940384e5,0x54084458700b63b43a85b02210c4605b02210c0408a0ca0680c019030088320160280540a013),
  (0,0xe00744583f0b60441f85b0220204d0650340640c0ac0c80580a8140260c4f89f80060901d039),
  (0,0x3a7d4768111542200880d0180200d8bf0300640c01717c0500a814026260189f10067c4fd1f9),
  (0,0x3a12c150111542200880d0180200d8bf0300640c01717c0500a8140261c0189f1006090fd1f9),
  (0,0x547ece10f70b60b87806505806478064056054098003ec018030a91523e4f883b0060e81c80d),
  (0xe4594038d35,0x2416c7685b02210c040110860200d81a0300640c01702c0500a814026094130f304a09011822),
  (0x2f85d,0x2402c0885b0220203281a0320603201602a0500989b0000fc1f89a13200c2e0030480e81c9e4),
  (0,0x22044440110180200d8180320600b81402a0500982a00c2a8068a9152498018033e27e8fc9fc),
  (0xdd4bc00992e00e637c039406,0x2044060a8e890d1a6741010d11a073d008ce19a331001ff3fc7f4618e0),
  (0x39c15,0x3a130150731542202680d0180200d8bf0300640c01717c23c2000502610c439f11b035c6d870)]

def r7_9 : List Hint := [(0x39c05,0x3a130150731542202680d0180200d8bf11e0440281717c0500a81402610d0320500400838049),
  (0x697d,0x240a4000980000c4058111107c8040050187c80401b0200605401903005c038141500540a013),
  (0,0x3a130958732ce22026a070180200d8bf0300640c01717c0500a8140260c43804502201408007),
  (0,0x22a260e284c0000a4398113e4220268053e40300401b0202a00c01903005c038a80280540a013),
  (0x39815,0x3a1300007300c2200d8bf0300640b8be028054098981240900183a0720c4000f307e268381f2),
  (0xe8534037449,0x1b00301500b1ee220040f60180200c8f50300640c04022e23c200050260fc438431b035c6b05c),
  (0x3a54d,0x1b00301500b1ee220040f60180200895111e044028151e80500a8140260fd03205004008558ff),
  (0,0x2283c49307325a2202692c0180200d8f50300640c0171e80500a814026454e084502201408007),
  (0xe90d403a025,0x5e1cc1701b0580640b82b02a04c2980600c2a45489807600c1d03901a0c5040d81b63f000199),
  (0x3a85d,0x5e02c1701b0580640b82b02a04c1e83c0780b01580307600c1d0392044500011322255038070),
  (0x3ac1d,0x5e02c1701b0580640b82b02a04c1e82f0780b0158982042604b897412364218d81ac35800043),
  (0,0x54834060f70160b87a8650580647a06405605409a0d1360f01e02c05610d0600641682905207),
  (0,0x12c1441701b0580640b82b02a04c4b03c0780b015a0f00c82d0520a40e0c5040d822255107043),
  (0,0x540010912d1bc3007a89a17e0647a0ac17c05409a111582f81e02c0564b1080be0060e81c805),
  (0,0xa616c6001b17e0640b8be02a04c1e8be0780b01580317c00c1d03900a1c00011322255107188),
  (0xed2a403b05d,0x7a0300000b0782200d82c0300640b82b0280540980306410c0183a0722600003112225c4b870),
  (0xed1e403b85d,0x7a02c1e01b0580640b82b02a04c4d80007e2684c8980542604b8970e000c000030740e418843),
  (0x3bc6d,0x54000060f70162207a8650300647a064028054098001363cc1f89a132000f88240060e81c891),
  (0,0xa61444401b0300640b81402a04c298f307e2684c8f104800c1d0391220c4fb8d8222550fb99c),
  (0x33065,0x22a0a4150730220a4268050180200d8100500640c01700e09c0a8140261c0e28291bc2644d099),
  (0x2f85d,0x420300000b0222202d805018020328100300640c06400e0500a8140262602e0291222444b897),
  (0,0x1386004d17c0200d8bf0320600b8be02a0500981d17c0fc1f89a1324990a09842025c4ba13),
  (0,0x1b21387d85b1ee028040f90380200da150340640c01742a0580a8140263647c01d07e0fc4d099),
  (0,0x1802c4405b018020328180320603201402a0500982108a0440281000e85894913224444aa070)]

def r7_10 : List Hint := [(0x2f86d,0x54000060110162200285b018020080650300640c0070c80500a814026000148291222444b897),
  (0,0x1d23a234ce79e819a5c8bc97833c7350e0c43c686d0d2191887810c217),
  (0,0x54000060f70162207a8650300647a064028054098001e63cc1f89a1324e8f88240060e81c891),
  (0,0x3a02c0505b0380203281a0320603201602a050098f303a0fc1f89a132874218d81ae7b4f69ec),
  (0x2f86d,0x44058110b60200d0650320600b06402a050098001e60fc1f89a132000120030480e81c9e4),
  (0,0x44440110180200d8180320600b81402a0500982a1e60fc1f89a132170120033e27e8fc9e4),
  (0,0x1b20300000b1ee2200d8f50300640b8f40280540989b0003cc1f89a13200cee8240060e81c891),
  (0x3c066001f12c002447,0xd51a834c690d11a033c728cd198390718e21c23806311c18830c6112f),
  (0xcf1b403d06500f311403c83500f1094007c0d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e0a8188dd1b836c2e000),
  (0,0xd51a834c690d11a04d8bd13426632c650c91905ac6317518830c980c1),
  (0x3406d00f719403d84500f50d403c415,0x3a02c050080380200d81a0320600b81602a050098120420440281000e0a87f0dd1b80e06d049),
  (0x7213800804b000a11c009c46,0xd51a834c758ea1d233c728cd1d032c650c91ce31c630211884e0610c1),
  (0x3446d00f919401c85d00f811403d42500f205400800d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e0a8000dd27436c6d000),
  (0x9213800a046,0xd527e4f8690d127a33c7293c19832c6516d19031c631be27630c610c1),
  (0xd21b403e865009217403e03500f609403cc15,0x3a02c050080380200d81a0320600b81602a050098120420440281000e0a8000381b836c6d0ec),
  (0x2112c003047,0xd51a834c690d11a033c728cd19832c650c919031c631d418830c610c1),
  (0x3e84500f90d403dc2500f405400840d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e170828dd1b836c6d000),
  (0,0x548810f8f11e2028788f1038020780f00340640c0f01e00580a8140268787702102201408007),
  (0x3386500fe11403f43500fc09403ec15,0x3a02c050080380200d81a0320600b81602a050098120420440281000e000218dd1b836c7e070),
  (0,0xd31a2340670cd1985e4bc17733c314620c31845d0a494828e518b9144),
  (0,0x543e0459f50b60a81f85b1542201f85b01a0300409a0ca2fc0c0190302b0320be0280540a013),
  (0x3fc05,0x3a130150731542202680d0180200d8bf0300640c01717c0500a8140260c4130f307e0fc4d070),
  (0,0xd51a834c679e819a32c650c918e6010e0c43c6788bf21918878110a17),
  (0,0x1b20300000b1ee2200d8f50300640b8f40280540989b0003cc1f89a13200c9d0240060e81c891)]

def r7_11 : List Hint := [(0x4015d,0x540a8060f70162207b05b0180207a8650300640c0f40c80500a814026098798f307e0fc4d099),
  (0,0xa61444404d0180200d8180320600b81402a050098b51e60fc1f89a1320c4930d811a444aa0f8),
  (0,0x22044050110380200d81a0320600b81602a050098b51522a8068a9152498128030487e8fc831),
  (0,0x44410c9708807e3000603f17c0203289a17e0640c0641582f80a8140263cce00be07e0fc4d099),
  (0,0x3a044050110380200d81a0320600b81602a050098b503a0fc1f89a132170218030487e8fc831),
  (0,0x3a044050110380200d81a0320600b81602a0500982a20a2a8068a915226c0e8030487e8fc9e4),
  (0x2f805,0x3a1cc0504d0380200d81a0320600b81602a050098b503a3784c89a1320c41881100a04003800),
  (0x33865,0x3a1cc0504d0380200d81a0320600b81602a050099150420440281000e891119c638c3586b070),
  (0x40466,0x2033a234ce80d11a073c670cd198801139fd1863810222618830d1294a),
  (0x40825,0x3a1cc0504d0380200d81a0320600b816080014098b503a0fc1f89a13210c218d81ae36c2e087),
  (0,0x2033a234ce80d11a08b1158c41868a8bc9782ee5d90222918830c98228),
  (0x40815,0x3a1cc0504d0380200d81a0220140b81602a050098b503a0fc1f89a13210c218d81ae0e07e206),
  (0x2f85d,0x3a1cc0884d0220200d81a0320600b81602a050098b503a0fc1f89a13210c000030480e81c831),
  (0,0x228030150731ee22026a2d0180200d8f50300640c0171e80500a8140262d4f60f307e0fc4d099),
  (0x3386d,0x3a044050110380200d81a0320600b81602a0500982a1522a8068a9152000218030487e8fc831),
  (0x1d31402f805,0x3a1cc0504d0380200d81a0320600b81602a0500987003a3784c89a1324541881100a0400385c),
  (0,0x3a02c050080380200c81a032060200160800140983f03a0fc1f89a132360218d81ae3582e087),
  (0,0x3a02c050080380200881a0220140a81602a0500983f03a0fc1f89a132360218d81ae71c6b206),
  (0x10331402f85d,0x241cc0884d0220200d81a0320600b81602a0500987003a0fc1f89a13200c2e0030480e81c831),
  (0x1d1b4040c55,0x3a044050110380200d81a0320600b81602a0500982a20a2a8068a9152000000030487e8fc831),
  (0,0x160200401b0320600b81502804c1e83c0780b0158120220440d01603a3646c0d71ac35818843),
  (0x410a9,0x160200401b0320600b81502804c1e83c0780b01580300610c1d03908a450899122225501882a),
  (0x41499,0x5e02c1700805a0200d82c0320600b82b02a0500989803a2603809712e364188d81ae3586b026),
  (0,0x5e02c1700805a0200d82c0320600b82b02a0500981208a0440281000e45018913224444aa070)]

def r7_12 : List Hint := [(0,0x54074971f21bc0b8f909905a0205409a0580640c0a81580ac0a8140263bc7704302201408007),
  (0x37005,0x12c16c1700805a0200d82c0320600b82b02a050098120860440281000e1c01509112225c4b800),
  (0x1d6d4041945,0xe03c80e85b1bc0282d8700380203289a0340640c0641580580a814026084e283102201408007),
  (0,0x541c1188211e48c00885b4600280285b45e070040100ca8b80d01903001c3222e02c0540a013),
  (0x75b1,0x240a89708807e3000603f17c0203289a17e0640c0641582f80a81402622c13105154034548a9),
  (0x1d6940421350107294037845,0x9c1c00005b0143780401c0e00200d81a1340640c01702c1c00a8140260481880002201408007),
  (0x40c55,0x3a044050110380200d81a0320600b81602a0500982a0862a8068a91521c0768030487e8fc9fc),
  (0x339b5010a5d4042545,0x4645091005b3960282d9ca038020328f00340640c0641e00580a8140260850f02102201408007),
  (0x42c6600ff11c037446,0x2033a234ce80d11a073c728cd1988011a1fd1863810204318830d12a33),
  (0x10d154043025,0x3a1cc0504d0380200d81a0320600b816080014098b50862a8068a915210c150d81ae36c38121),
  (0x43015,0x3a1cc0504d0380200d81a0220140b81602a050098b50862a8068a915210c800020041c024a35),
  (0x103194043415,0x3a1cc0884d0220200d81a0320600b81602a050098b515400c1203a0720000003f07e268381e4),
  (0,0x3a1cc0504d0380200d81a0320600b81602a050098b520a00c1203a0720c43803c0780b015845),
  (0x33445,0x3a2601500b05c7c80402d3e40200d82c1500640c0170562a00a8140260482180002201408007),
  (0x374b5,0x3a02c050080380200c81a032060200160800140983f0543606b8d60b8360218d81ae358e3887),
  (0,0x3a02c050080380200881a0220140a81602a0500983f200008010ab1fe360218d81ae71c6b206),
  (0,0x3a02c050080380200d81a0320600b81602a0500981203a0f01e02c056094828030480e81c826),
  (0,0x5e02c1705b05a0203282c0320603202b02a0500989803a2444889712e0842181100a040039c5),
  (0x43839,0xa616c440080180200d8180320600b81402a050098d91e60fc1f89a132364930d81ec444aa0f8),
  (0,0x44412ce103f1102201f80c0180204d0650300640c0ac0c80500a81402609845806154034548a9),
  (0,0xa62206000817c0200d8bf0320600b8be02a050098121520440281000e4982189112225c4ba13),
  (0,0x384220440080180200d8180320600b81402a0500981208a0440281000e1702489112225c4b870),
  (0x2f80d,0x38416c440080180200d8180320600b81402a0500981208a0440281000e1c01889112225c4b800),
  (0x43c99,0x38416c440080180200d8180320600b81402a050098d924c3607b1112a826c7983f07e2684c826)]

def r7_13 : List Hint := [(0x2f855,0x38416d1b80846c0200d8180320600b81402a0500981208a0440281000e1240000a0380680b031),
  (0x339a5011359404493501113d40440a5,0x9c8e02185b01472c0401c3940200d81a3920640c01702c7200a81402604810a1e02201408007),
  (0x3386d,0x2206000817c0200d8bf0320600b8be02a050098121520440281000e0002489112225c4b870),
  (0x2f80d,0xb616c440080180200d8180320600b81402a0500981208a0440281000e2601889112225c4b85c),
  (0x4559501145d402f855,0xb616c218080860200d8180320600b81402a0500981208a0440281000e1382e00a0380680b031),
  (0,0x1616c040650320603201502804c1e83c0780b01581d0140700d0160e000c018240740e4228ed),
  (0,0x1e21cc4404d0180200d8180320600b81402a050098b51e60fc1f89a132450930d811a444aa0f8),
  (0x3fc05,0x1802c440080180200c8180320602008f080014098030e200c0683e0b844815113224444e0800),
  (0,0x1802c440080180200888f0220140a81402a050098030be00c06842082448151132248e4aa049),
  (0x338c5,0x3a378050990380204d01a0320605601602a05009a3a446718e31ed3da3b81081100a04003a1e),
  (0x33405,0x3a02c1700805a0200d82c0320600b82b02a0500981208a0440281000e2601509112225c4b800),
  (0,0x22044078110120200d8180320602e0450800140982a00c2a8068a90b8170018030480e87f043),
  (0,0x22044078110120200d8110220140b81502a0500982a00c2a8068a9152170018030480c41c843),
  (0x40c49,0x24c8f8150110ee22008a3d0180200da3c0300640c0174760500a8140260a8fe043154034548a9),
  (0x4586d,0x3a044050110380200d81a0320600b81602a0500982604a094799fa3f2000ef05b0b6194321c5),
  (0,0x22a10d200890223001480517c0203281017e0640c06400e2f80a8140260c4380a92568fc548a9),
  (0,0x4210d200880223000600517c0203281017e0640c06400e2f80a8140260c509a433f090920a41),
  (0x465ad01184d4045ca5,0x540007688814e378040a70e00200d8a61340640c0171501c00a81402604852a4402201408007),
  (0x11b3d40468a5,0x2410c3800f0049180480248a020100ab1da0640c01f1583b40a814026094130a9154034548a9),
  (0,0x2403c1f80907e0201009a0320600f8ac02a050098250e02a8068a915209424a4848e90520a43),
  (0,0x3a02c050080380200d81a0320600b81602a0500989b03a0fc1f89a132364218d81ae3586b026),
  (0x1174d804709701070ec037c37,0x24f49c9352624b1a6741250d11a073d248e519a330e694a238310618c2),
  (0x2b985011f4940478e5011d254041c39,0x2e1380b1db0b80c42d81501472c040140387280401b026068e4819030048038210b804402810),
  (0,0x2554a894d262521a6741288d11a05c8bb1792f05dce6a502ea31061974)]

def r7_14 : List Hint := [(0xaf6140485250120394047495,0x361380d2560703f82d81901472c0401803872804017026058e4015028048080212de04402807),
  (0x4613601140f804203b00e00dc038c36,0x25a49c965262581a673c740e519a5c8cf9792f0678e6a5704231061174),
  (0x2c18501224940480e5011e254042039,0x101380e1db2747142d80801472c0d8180347240c817028058e4015026048028210b804408007),
  (0x1150f8039036,0x25d4ba970e813d1a273c9e0e51985c8df9792ee678e6a5b37c30c61174),
  (0xb16140489250121394047c95,0xb61380525e070248040080387280d8190347240c01702a058e40140260480882137801408007),
  (0x46975,0x5445c321180620587b85b02a0287c85b028070040f00ca04c0d019030098458a91b22a8068a9),
  (0x46d75,0x54544329571fc0807b85b0320287c85b030070040f00c804c0f815028098458a920e2a8068a9),
  (0x38435,0x546202da5f4be0247b85b010028780650300680c8f00c80500b0150260984580d38a2a8548a9),
  (0x38835,0x5468c2da604c003c7c85b010070780650320680c0f00c80540b014026098458aa124034548a9),
  (0x48dad,0x54000e10110b68dc089c246c0200d0650300640c0160c80500a814026099028f304a09011822),
  (0,0x54114e10110b62200285b018020080650300640c0070c80500a81402670518a613f090920a41),
  (0,0x547ece10f70b60b8780650580647806405605409800116018550a9152988f883b0060e81ca42),
  (0,0x547d4e103f0b62201f85b0180204d0650300640c0ac0c80500a8140263e0458061540345f8be),
  (0x48c05,0x5c0b40402c0320601581502804c1e83c0780b01583b0060901d03908a1c00501c03405838000),
  (0x3386501271140498350125094049015,0x3a02c050080380200d81a0320600b81602a050098120420440281000e76c218dd1b836c7e070),
  (0x12927c04a093010b12c039447,0x2033a234ce80d11a09a133a66186995321fd1860e10226318830d1985c),
  (0x12835404b8c5012d29404b095012b21404a809,0xb202c5980801c0200c810032060200b4080014190fd0863746e0db0e000c5480301a0f82e05c),
  (0,0x4d80301300b4d62200422d0100200c8f50300640c03f0649a81f83f13400d348030060341f05c),
  (0x4bc25,0xb202c5980801c0200c8100320601f98a07e0fc4d00315200c0683e0b89b421a6c1ae36c1908e),
  (0x12935404c005,0x1802c440080100200c818032060200050800141900300600c0683e0b8448131132244443805c),
  (0x10c12c039c47,0x2033a234ce80d11a08b1338c4186801381fd1869b90226f18830d3705c),
  (0,0x3a1cc0784d0120200d8110220140b845080014098b500c2a8068a90b810c6c0d81ae0e02e271),
  (0xb519404d44501340d404cc25013207404c40d,0x1802c050080380200c81a03206020016080014098030e200c0683e0b8000218dd1b836c00000),
  (0x43449,0x4e6030150731ee22026a2d0180200d8f50300640c01722e9c8200050262d4470431540345485c)]

def r7_15 : List Hint := [(0x13709404d81d,0x3a1cc0504d0380200d81a0320600b816080014098b50a22a8068a90b810c218d81ae36c00087),
  (0x3fc45,0x184481500b1104b40400c2580200c8181ea0640c0404e47042000502600c3885c0060341f05c),
  (0x4e02d,0x3a1cc0784d0120201b84500c0141b03506c008190b500c2a8068a90b810c6c0d81ae0002e087),
  (0,0x3a02c0500803802008a760220153a84322644c7601502c0540a0132b600c600030041093a041),
  (0,0x1b00301500b1ee2200422d0b00201f8324ee3601f8151e80500a81413400d348b90060085c041),
  (0x4e415,0x3a02c050080380201f8731b00fc0a81602a0504d00318000c010b80829e0218d81ae0c87e162),
  (0x13b11404e805,0x1802c440080b0020088050220140a81402a0500980317200c01042082448150dd2243b0aa05c),
  (0x2d865013f11404f835013d0b404f015,0x1802c050080380200881a0220140a81602a050098030e400c06842082000218dd1b80007e049),
  (0,0x4e6030150731ee22026a2d0180200d9514f2044028171e80500a8140262d452205004008558ff),
  (0x1410b4050015,0x3a1cc0504d0380200d81a0220140b81602a050098b5200008010ab1fe10c218d81ae0007e206),
  (0,0x184481500b1104b40400c25802008a79472044028150283d00a81402600c2fa7a00603421041),
  (0x4c415,0x3a1cc0504d0380200d81a0320600b81602a050098b500c2a8068a91520c40e83f07e268380f8),
  (0x4f025,0x3a1cc0504d0380200d81a0320600b81602a050098b52442a8068a91520c46c8d81ae36c8c826),
  (0x4cc15,0x3a1cc0504d0380200d8200320600b81f02a050098b52b82a8068a91520c4838d81ae9ec7e026),
  (0xca174050855013e09404d015,0x3a1cc0504d0120200d81a0320600b81602a050098b51522a8068a91520c4150d84f836c7e026),
  (0xcb174050c55013f09404d415,0x3a1cc0784d0380200d81a0320600b81602a050098b51522a8068a91520c41527d1ae36c7e026),
  (0xb719405105d0143114050835,0x2202c088080220200c81a0320600a81602a0500980304209412023044000000430860600a070),
  (0,0x1802c440080180200d8180320600b81402a0500981208a0440281000e45015113224444aa070),
  (0,0x3a1cc0504d0380200d81a0320600b81602a050098b51524ad1f8a91520c41081100a04003a1e),
  (0x50025,0x3a1cc0784d0120200d8180320600b83b080014098b500c2a8068a915210c6c0d81ae36c8c887),
  (0x4dc15,0x3a1cc0784d0120200d8030220140b81502a050098b500c2a8068a915210c6c0d81ae9ec7e206),
  (0x51055,0x3a1cc0504d0380200d81a0320600b81602a0500985303a0f01e02c0560c4000030480e81c826),
  (0x5154d,0x1b20301500b1ee220040f60180200d8f50300640c0171e80500a81402626c130f307e0fc4d099),
  (0x5186d,0x540a8148114fc0a4028fa018020080650500640c0070c809c0a814026001188291bc2644d099)]

def r7_16 : List Hint := [(0,0x540009712d1bc3007a89a17e0647a0ac17c05409a113802f81e02c0569f1082470060e81c805),
  (0,0x286f01c1320200d09a0320600b0ac02a0500981d3800fc1f89a1323ed4024848e90520a7f),
  (0,0x8610c9712d1bc3009609917c0207a89a17e0640c1c11582f820005026a04e00be0060fc1f001),
  (0,0x8610c9712d1bc3009609917c0211c89a17e044028f41582f80a814026a08e00be0060fc21041),
  (0,0x86498970881bc0180609900c0200c09a17e0640c0141582f80a8140263cce00be07e0fc4d099),
  (0x51805,0x5e2081701c05a0200d82c0320600b82b02a0500981d03a2444889712e0c42181100a04003800),
  (0x51c99,0x2206000817c0200d8bf0320600b8be02a050099264282603809712e3654183f07e2684c826),
  (0xbf034052005,0xa616c6000817c0200d8bf0320600b8be02a050098121520440281000e1c0151132244448c826),
  (0,0xa616c6000817c0200d8bf0320600b8be02a050098121800440281000e1c0151132249ecaa16a),
  (0xc0034052405,0xa616c6000817c0200d8bf0320600b8be02a050098121520440281000e1c0151134c4444aa026),
  (0,0xa616c6000817c0200d8bf0320600b8be02a0500981217e0440281000e1c015284224444aa1bb),
  (0,0xa616c6000817c0200d8bf0320600b8be02a0500981217c0440281000e1c0930880180600a045),
  (0xb8194052435014805405280d,0x3a02c148080180200d8280320600b82702a050098120420440281000e000218de0e026838000),
  (0x51d46,0x28649834ce79e819a5c8bc97833c7350e0c43c686ce6a851887810c217),
  (0,0x38416c4401b0300640b81402a04c6c9f71b0444aa09b1e60fc4d09900000c120030740e49d091),
  (0x51c65,0xa616c6001b17e0640b8be02a04c1e8be0780b01580350e00c1d03900a0000011322255107188),
  (0x14c514052d05,0xa616d2300848a0200d8ed0320600b8ed02a050098121520440281000e1251000a0380680b021),
  (0x52805,0x12c16c1700805a0200d82c0320600b82b02a0500981208a0440281000e1c01509112225c4b800)]

def c8 : Catalogue := (99,88,0x831b46316c49100370d00a0020c6d18c5b124400dc34831b46316c491003702803831b46316c49100380dc0a0020c6d18c5b124400e037831b46316c491003702804002386d18c5b124400dc0a8e20c6d18c5b124400dc2c0020c6d18c5b124400dc2c8e20c6d18c5b124400dc018f238831b46316c49100378e20c6d18c5b124400dc360020c6d18c5b124400dc36831b46a18c5b124400dc050020c6d1a86316c4910037831b46316c491003701401831b86d18c5b124400dc050020c6e1b46316c4910037831b46316c4910037014040020c6d18c5b134400dc0500000831b46316c4d100370020c6d18c5b124440dc0500000831b46316c49110378820c6d18c5b124400dc170020c6d18c5b124400dc178820c6d18c5b124400dc038f220831b46316c49100378820c6d1b06316c49100370020c6d1b06316c491003700238881b46316c4910037002206d18c5b124400dc05831b46316c49100370a40a8e20c6d18c5b124400dc29831b46316c49100370a4058820c6d18c5b124400dc29831b46316c49100370a4030020c6d18c5b124400dc038620c6d18c5b124400dc2900218831b46316c4910037831b46316c49100370440a8e20c6d18c5b124400dc11831b46316c4910037044050020c6d18c5b12440044058820c6d18c5b124400dc1100220831b46316c4910011831b46316c49100370a4110020c6d18c5b124400a4110020c6316c49100370a411831b46316c4910037044010020c6d18c5b124400dc018420c6d18c5b124400dc1100210831b46316c49100370020c791b46316c49100370020c6d18c5b124400dc32831e46d18c5b124400dc0b0020c6d18c5b124400dc0b8f20c791b46316c49100370023c831b46316c4910037831e46d18c5b124400dc0a8e20c791b46316c49100370020c791b463124400dc1e00000831b463124400dc1e831e46d18c5b124400dc050020c791b46316c49100058820c791b46316c491003700220831e46d18c5b12440831e46d18c5b124400dc290020c791b46316c4910029831e46d18c5b124400dc110020c7918c5b124400dc11831b46316c49100370c80a8e20c6d18c5b124400dc32831b46316c49100370c8058820c6d18c5b124400dc32831e46d18c5b124400dc320020c791b46316c49100320020c7918c5b124400dc32001b46316c49100370c82f000006d18c5b124400dc2f831b46316c49100370c8040020c6d18c5b124400dc048720c6d18c5b124400dc320021c831b46316c49100370021c6d18c5b124400dc3200000871b46316c4910037831b46316c49100370c8290020c6d18c5b124400dc290020c6316c49100370c8290020c6d1a05b124400dc3200000831b46816c49100370020c6d18c61124400dc3200000831b46318449100370020c6d18c5b14c400dc3200000831b46316c53100370020c6d18c5b124460dc3200000831b46316c4911837831b46316c49100370c8110020c6d18c5b124400dc110020c6d18c5b124400c811,0x77757567600000007775756760000000777575676000000077757567600000007775756760000000777575676000000077757568700000007775756760000000777575676000000077757567600000007775756760000000777575676000000077757567600000007775756760000000777575676000000077757567600000007775756760000000777575676000000077757567600000007875757760000000787575776000000087767667700000008776766770000000777575676000000077757567600000007775756760000000777575676000000077757567600000007775756760000000777575687000000077757568700000007775756760000000777575676000000077757567600000007775756760000000777575676000000077757567600000007775756760000000777575676000000077757567600000007775756760000000777575676000000077757567600000007775756760000000777575676000000077757566500000007775756650000000777575665000000077757567600000007775756760000000777575676000000077757567600000007775756650000000777575665000000077757567600000007775756760000000777575676000000077757567600000007775756760000000777575676000000077867566500000007786756650000000777575676000000077757567600000007775756760000000777575676000000077757566500000007775756650000000777575665000000077757566500000007775756760000000777575676000000077757567600000007775756760000000777575665000000077757566500000007775756650000000777575676000000077757567600000007775756760000000777575676000000077757567600000007775756760000000777575676000000077757567600000007775756650000000777575665000000077757566500000007775867650000000777586765000000077867566500000007786756650000000787575765000000078757576500000008776766660000000877676666000000077757566500000007775756650000000777575665)

def r8_0 : List Hint := [(0x113380040cb000f31c0038c6000d3140030bf000b2f80028a60009258002095000721800187600051d400105700031580008070001018000005,0x1aa350698d21a2340678e519a330658ca19232063870000a29448e0510318188c418630860800),
  (0x1932c0060c7000c2fc005cbe00132d80048b300161ac005467001415c004c56000203c00480e,0x1aa350698d21a2340678e519a330658ca19232063a8f51c31061a8c516a34218c4186a3145826),
  (0xb4f4000d3500203b4007ce500173740078c5001d2d40070a5001b254006865,0x3a02c050080380200d81a0320600b81602a050098d90003606b8d61ac0a8000dd1b836c6d0001b20006c0d71ac35800000),
  (0x2c53000ad48002a2b000a4a80028280009c6600261700094580024140006c4c000512c008c48002211c00840c,0x2931a834c690d11a033c728cd198a48718e21c238148a9018830c6112f),
  (0x3c35800ccbe00062ec00ecb7003a2d800e46e00381b400dc6b003619c00d466003419400905f003317800c846003111400c036002f0d400b826002d094006c0f000603800140d,0x1aa350698d21a2340678e519a330720e31c4384700c6042310618c225ea5818a95512a502e000),
  (0x1194c00455200110ec00433a00108e00041170010058003f14000704c003e12000f41c,0x2931a834c690d11a0a60bd13426632c650c91905ad48a9718830c980c1),
  (0x4b2f8001cbb00532dc0148b600511b801406d004f1ac013867004d198013065003f17c012c5e004a11801244500480d8011c35002e05800b415001c03c001c0e,0x1aa350698d21a23409b1352684cc658ca192320b58c604231061930182a587f2955120e144049),
  (0x1814c005f52001791c005d460017110005b170016858005914001604e001d13000204b0057120015847005511801502c,0x2931a834d4d0ea1d233c728cd1d032c650c91ce31d48a991884e0610c1),
  (0x632f80024bb006b2dc01a8b600691b801a06d00671ac0198670065198019065005917c018c5e00581740188460061114012026004709400c016002f05400740f000903800200d,0x1aa350698eb1d43a4678e519a3a0658ca19239c638c60423109c0c2182a5800295274a5144000),
  (0x1dd4c007652001d53c00744e001cd30007217001c458007014001bc4e001e13001b848006d11801b03c,0x2935384f8690d127a33c7293c19832c6516d19031d48a9b27630c610c1),
  (0x1e0be000a2ec0200b7007f2d801f86e007d1b401f06b007b19c01e866007919401c05f007817801bc5d00620d8018435004a098012425003205800c415001e03c00280e,0x1aa4fc9f0d21a24f4678e5278330658ca2da320638c60424ec618c2182a5800038512a51440ec),
  (0x210ce008331801e0b6006f2d4018ca60058294012c960033218005c7f000b1f800681700820580008070081018000005,0x1a8348680cf19a330658c919031c630c418630860a9f52aa254f29d000354c39a430a61018800),
  (0xc2ec005cba00852dc0218b200881ac021c67000217c02185e001401c021406,0x21c350698d21a2340678ce19a33065981192320638c6546310618c2182a8815187348a8550070),
  (0xb4e4020935008a3b40224e500703140164b5003f294009095000c234001015,0x22802c968082580200d8f50320600b8f402a050098120000440281000e0a8000dd1b836c6d0002280008991222255000000),
  (0x93530024948009151002405c008f1600238540089140007c4c000d12c023448008c11c022c44,0x2a51a834c690d11a033c728cd19832c650c919031d521d418830c610c1),
  (0x20cbe000e2ec0254b700942d802245f008317801e846007911401943600640d4013426004c09400d4160034054007c0f000e03800340d,0x1aa350698d21a2340678e519a330658ca192320638c6042310618c218217082a95512a5144000),
  (0x265bf00886a802619a009265800586a0097168023c56000f12c025847,0x55eab9568d449834c692ac1a234155aaa1ca334662a95505e4bc17733ca9d531d418830c61174),
  (0x991a401ec4500660d40138250036054003c0d,0x545c0a10f11e2028788f1038020780f00340640c0f01e00580a81402650477021022014080070b8170828dd1b836c7e000),
  (0x102ec029cb7009919802986500a517c02905e00a311802884500a10d8028035009f098027825009d058027015009b03c02680e,0x3a4744699d01a2340e78e519a330b91792f05dccf1cd3a8310618c22e817021a95512a5158070),
  (0x264e5007c314019cb5004f29400dc950010234022c7500ad1b402b05500ab11402a83500a909402a01d,0x3a02c050080380200d81a0320600b81602a050098120420440281000e170828dd1b836c7e0000000006e8dc1b63f00005c),
  (0x8a2c00080ac00af2a002b8a4,0xd31a2340670cd1985e4bc17733c314620c31845d0a494828e518b9144),
  (0x8447800451b00b145c02c116008a33c0210ce007e2d801f4b5006929801a0a50051258014095003921800e08500201fc00447e008b01c029805,0x1a6344680e519a330bc9782ee678108c4186308ba04352aa254a2b00e0524a414728c5c8a205c),
  (0xb55fc0208bf00862f802c06e009419802d05f00b317802c85d007f11801b445006a0d8015435005209800e816001303c000c0e,0x300350868d2218340678e519a330658ca1923206397e04c3106197c2f6a7c00295512a794e870),
  (0xd9f001267802e54f00b11b8029c6b009619c025466008c19402e05f00b717802d85d008513c02084e00800d801ac260056094014c16003b018008805,0x18c438150d421a34c6910c1a23406790b214334660cb304604648c818e1c000043514a2470288)]

def r8_1 : List Hint := [(0xbb7340208cd000332402bc7d008d1d402e86d006e114015c35003e094008c15,0x1b24501500b1ee4b4040f62580200d8f51ea0640c0171e83d00a814026364130001b035c6b0d6054000218dd1b836c6d070),
  (0x2f07d008f19401c445005a0d4010025002505400600d,0x54508a10f70b60287c85b038020780650340640c0f00c80580a8140260984592b154034548a9000ac4218dd1b836c7e000),
  (0x25ce50072314016cb50041294009895001923402b46d00bf19402f83500bd094005809,0x3a1cc0504d0380200d81a0320600b81602a050098b52562a8068a915276c218dd1b836c7e0000620a86c0d71b63f01305c),
  (0xc01f40248650076114017c35004509400ac15,0x540a89712d1bc3009609917c0207a89a17e0640c0f41582f80a8140263b87712b02201408007000ac8828dd1b836c7e070),
  (0x9839401dcc500602d40118a5002c25402a01d00c1054022009,0xa616c6000817c0200d8bf0320600b8be02a050098122560440281000e76c828dd1b836c7e0700e00a8899122225501305c),
  (0xc55fc0310cb00c331c0308bf00172f800505f000117800005d001a03c000c0e,0x300350868d2218340678e519a330658ca19232063a8f00031061a8c5165f8000c4186accbd831),
  (0x319cd000c3740308cd000330400100d,0x1b24500000b1ee4b4040f62580200d8f51ea0640c0171e83d00a81402626c0000007e0fc4d0991b2000000d81ae3586b000),
  (0xc267c00319e00c953c03206b00c719c00505f008117800005d000413c02084e,0x18c438000d421a34c6910c1a23406790b19c334660cb304604648c818ead00003130e69150aa0),
  (0x5e1d00ca7340308c9008230400685d,0x1b20300000b1ee220040f60180200d8f50300640c0171e80500a814026364000001b035c6b0d622800000113224444aa000),
  (0x345bf00c86a803419a00cf63c03218a00ce60c03358200cc5d8030d6f00185b8032cff,0x55ea9d5f2bd5780a886a4c21a34d5daac574344682ab572ae0670cd198aa55bab656a5e0bb99e),
  (0x2222900d586403520d00d380403497d00d11a4030c49,0x541715f8430b60a87b85b1ee2207c85b1ec030040f00ca3d40c0190303c0320f40280540a0130e0170e29051b035c6b0d6),
  (0x3119f001967803714f00d1198036c5f00da17803644f00a710c03601600d7018035805,0x3a4748151d121a34ce82ba1a2340e7ab819c3346617256cad4bc17733cb04132c018830c702b0),
  (0xe07340344e500c4324037c6d00de094037415,0x2283c4150731ee220268f60180200d8f50300640c0171e80500a8140261c0e29051b035c6b0d6062000468d81ae36c7e070),
  (0x3994c00e55200380ac00d22a00328a000c627002ec9400e4170038c5800e213003840c,0x2931a834c679e819a32c650c918eb11618c43c67896121918878110a17),
  (0xea6ec03a5b700c567c03199e00dc32c032cc700c92fc0328be00c92bc0314aa00b928c02d4a200e8128039c0a,0x51a438000d421a34c67ab819c33465ac830232463a8f000b1c6228c5165f89d2c618878110ac5),
  (0x168a403b61900e55f403b07d00eb1c4033065,0x54171650435923b4968de1ee710960991ec70c040f51343d4d78190303d0560f43860540a0130e01c01328707e0fc4d099),
  (0xe673403b86d00c8024029c01,0x1b27787685b1ee710040f63860200d8f535e0640c0171e870c0a8140263641328707e0fc4d0990e000021913224444aa070),
  (0x3d5bf00f46bc03cdae00f257c03c55d00f01bc03bc6e,0x55e0a96790d3a234d672ac1a23415c2b919c334662b656ead4bc17733c09966acc18830d462cb),
  (0x3d61900d483403d99d00e95f403b07d,0x541702e0000183b47b80b1ee2207b05b1ec030040f50ca3d40c0190303d0320f40280540a01300026ce28f307e0fc4d099),
  (0x3b5b600d531803d466001616c02200b,0x50c930699d01a2340e78ce19a330b92b52f05dccf2d459831061a8c596b05698c45a4a8568ad0),
  (0xf58d403a9cd00d0394032009,0xb83c4768511ee220268f60180200d8f50300640c0171e80500a8140268e0e28f307e0fc4d099062170ce0d811a444aa05c),
  (0x862f80048bb00042dc0068b600ae1b8040c6d01021ac040467010019803fc65008117c02185e00fe11803f44500fc0d803ec3500fa09803e42500f805803dc15000103c00480e,0x1aa350698d21a2340678e519a330658ca192320638c6042310618c2182a5821a95512a5144070),
  (0x1096ec0421b7001367c00059e010753c04194d01051ac041067008517c02045e008513c004c4a000410c006842,0x51a438150d421a34c692ce1a234067ab819c334660cb590604648c818ea3c132c718830d4628b),
  (0x431bf0108698042d9601021a804285a,0x55eb5d6b10d49834d5daac1a234155ab91ca334662a956e5e4bc17733ca9d5f2d518830d462cb)]

def r8_2 : List Hint := [(0x40e9010d364043069,0x54b60a10f70b60287c85b038020780650340640c0f00c80580a814026170f201d07e0fc4d0990b8170828d81ae3586b1c5),
  (0x116318043066011515c04505601130980448250111058044015010f03c04380e,0x3a4744699d01a2340e78e519a330b91792f05dccf2d45aa31061a8c596b04218c4186a5158026),
  (0x11b5140430e5011a1940464350118094045c1d,0x3a1cc0504d0380200d81a0320600b81602a0500987003a0fc1f89a132170828d81ae3586b1c50620006c0d71b63f00005c),
  (0x4c7700c21d802181f000b078047407011c01802c805,0x1a8348680cf19a330658c919031cc00c418678cf10d530e690c29840e05f8620c35665ec13000),
  (0x484cb012031c0048bf000b2f802145700c2158047c07011e01802d805,0x1aa350698d21a2340679e819a330658ca19232063ab405461cd22a1540318218c418630860800),
  (0x30935000b4c402e805,0x22802c968082580200d8f50320600b8f402a050098d90003606b8d61ac45015113224444aa0701b210c6c0d71ac35813000),
  (0x499bf01216a80495a20124658048c6f01221b8046c5a010411c030c46,0x55e3556b10d49834d5daac1a234155ab91ca334662a956e5e4bc17733c0995f04318830d462cb),
  (0x126364030cc501271f4045869,0x54508a10f70b60287c85b038020780650340640c0f00c80580a8140261c02e0ed1b035c6b0d6000afc218d81ae3586b1c5),
  (0x10d3180414b700c42d8049866012d17c04b05e012b158004053012a09804a416012805400400b,0x3a4744699d01a2340e78e519a330b91792f05dccf2d408631061a8c596b056c8c4186381582d0),
  (0x126514031135010a39404c06d011a19404bc35012e094040809,0x3a1cc0504d0380200d81a0320600b81602a050098701da3606b8d61ac76c218d81ae3586b1c50620a86c0d71b63f03805c),
  (0x4c4ed01173840490d501081d4042c65,0x540a89712d1bc3009609917c0207a89a17e0640c0f41582f80a8140261c0380be07e0fc4d0990b8ac8828d81ae3586b026),
  (0x48419001004404c805,0xa616c6000817c0200d8bf0320600b8be02a050098d917c0fc1f89a132364828d81ae3586b0260e00a88991222255038000),
  (0x4d5bf01026a804d19a010819804cc56012012c031c47,0x55eab96f8d33a234c68aac1a23415c2de19c334662b65baad4bc17733cb716dada18830c61174),
  (0x1351a4031c05,0x546707892d1bc220960990180207a89a0300640c0f41580500a8140263bc77045022014080070b817076913224444aa000),
  (0x13a6d80484bb00c82dc04d466013917c04e05e013701c04d806,0x50c930699d01a2340e78ce19a330b92b52f05dccf1cd5b4310618c22e8b8015187348a8568870),
  (0x135394032085013c1b404ec15,0xb616c440080180200d8180320600b81402a0500981208a0440281000e17076913224444aa0000e0000899122225500005c),
  (0x4f62d013c8840420750133194041005,0x5410c2d8f70b62207c85b018020780650300640c0f00c80500a814026098458aa154034548a90b8ac415113224444aa000),
  (0x105214050035013f09404f805,0x1e21cc4404d0180200d8180320600b81402a050098b51542a8068a915245015113224444aa0000622346c0d71b63f013000),
  (0x1411f404e869,0x5410d6492d1bc710960993860207a89a35e0640c0f415870c0a8140263b87712b02201408007000b2876913224444aa070),
  (0x13439405081d013b054040809,0x3bc16ce20083860200d9af0320600b9c302a050098122560440281000e76c76913224444aa0700e010c899122225501305c),
  (0x1262ec0344b7011616c0514570144098050c16,0x5c643469abb1a2340678ce19a330ec9792f05dccf05c5b431061a8c596171710c4186a797085c),
  (0x4e9bf01166e80249b3008f6c80299b1014b67c04e99a014a64c05259201481bc04586a014718c051862012412c033047,0x5ce171730d321a34c68abb1a2340672ab570334662b5552ad8bc17733cb942e2e418830d462cb),
  (0x525b600916980299a5008867c04e19e015459c054d6501524dc05453501503dc053cf5014e29c0534a5013c17804945b00cd15c034c56012512c05304a,0x49cbac21a4c1a6ba8e80d1306340e78e55d2334661722f2ba0bc17733c73410a1e18830c61174),
  (0x4e2290159894052a1500f3834023df50158694055d6501564540554b500ce154006049,0x540a97680056210c7b85b01472c7c85b038728040f00ca068e48190303c0320163900540a01304c22d7605c154034548a9)]

def r8_3 : List Hint := [(0x888f403562d00f47f40565f1015b67405687d,0x3802a0867087b8f70b62207b0f90b6030040f51e01940c0190303d0780640280540a0130001c045806154034548a9),
  (0x5762d01388840420750133194057005,0x5410ce10f70b62207c85b018020780650300640c0f00c80500a81402609845806154034548a900000015113224444aa000),
  (0x4f4be00d42d804205700f415805780f,0x59e74469aac1a23415c8e519a3315b9792f05dccf2cd5e231061a8c596b34218c4186bc177aee),
  (0x15d8a403d225014b854033cc501391f4045869,0xe00a9768f70b60287c85b038020780650340640c0f00c80580a8140261c045aec154034548a9000afc218d81ae7b4f6a69),
  (0x58ca001622700584980160250057c66013f14004b84c012812c03744800d611c02f444,0x2033a234ce80d11a073c670cd198bc9381fd1863810226318830d1285c),
  (0x5a8d6014331804a4bb00d72dc050c66016917c05a05b016715c0598530165098059025,0x3a4744699d01a2340e78ce19a330e72703fa30c700ef5b431061a8c0b8bd1798c4186a502e05c),
  (0x16e38005b4dc016c36005acd4014014004bc4c00de12002f844,0x2033a234ce80d11a0811338c41868a8bc9782ee5d9022f618830d7aa28),
  (0x14431804a8bb00d82dc051066017217c05c45b017015c05bc530165058059015,0x3a4744699d01a2340e9a6718830cb91792f05dcbb0ef5b431061a6e596bd1798c41860e15805c),
  (0x290dd017835405bca50166254025c75017715405d84501750d405d025017307400580d,0x3a1cc0504d0380200d81a0320600b81602a050098b51522a8068a91520c4150d81ae36c7e02600010c6e8dc1b63f000000),
  (0x11467c00599e014519805e45e011a12802fc42,0x3a4748151d121a34ce82f91a2340e7ab819c3346617256cad4bc17733cb517c2f718830d462cb),
  (0x4acc901451d402946d011416405e0510170094059c15,0x228bec150731ee22026a2d0180200d8f50300640c0171e80500a8140262d534afa154034548a9000000218d81ae36c7e070),
  (0x11639405f4dd011435405c4a50168254042875017c0d405ec25017a07404080d,0x3a1cc0504d0380200d81a0320600b81602a050098b51522a8068a9152000150d81ae36c7e07000010c6c0d71b63f000000),
  (0x10267c02919e012d16c04c05a00d915c02b45200d911c05f846,0x3a4748151d11a634ce80d11a2340e78ce5703346617256aad8bc17733c7357e1c118830c61174),
  (0x4b0d9010531405f46900a4184045455017209405a415,0x5f6450150731104b42680c2580200d8181ea0640c0170283d00a8140262d57d05c154034548a906210c000d81ae36c7e026),
  (0x146318045cbb00eb2dc02386600a619405e45f001603c04380e,0x3a4744699d01a2340e78e519a330b91792f05dccf3003a8310618c22e8bad7fafe5faa3165870),
  (0x438e9017f394051cd500ef1f4024865,0x540a89712d1bc3009609917c0207a89a17e0640c0f41582f80a8140260998130102201408007000ac8e39c638c3586b070),
  (0x168f403b62d018183406019d00f01b405fc61,0x188000864b87b92d1bc3007b12c1322f8040f51ea2685f8190303d07a0ac17c0540a01304c1c0e00be07e0fc4d099),
  (0x614ed010e384042075010b1940610550183094060815,0x540a89712d1bc3009609917c0207a89a17e0640c0f41582f80a8140261c0e00be07e0fc4d099000000000d81ae36c7e026),
  (0x4c4bb00ec2dc05785f010801c03c006,0x59e74469aac1a23415c8ce19a3315bab52f05dccf2cd608310618c22e8b3d81987348a8568870),
  (0x614e900f03940520d5010f1f404e869,0x6210c9712d1bc3009609917c0207a89a17e0640c0f41582f80a8140260998130102201408007000b2982913224444aa070),
  (0x13a02c061807,0xb834c698d11a2340f42b819a330bcab62f05dccf3075aa310618c22e81702e187348a8568b06),
  (0x2688d018c214026075018b1b40628550189114062035018709402200d,0xa616c6000817c0200d8bf0320600b8be02a050098121520440281000e1c015113224444aa0260000006e8dc1b63f038000),
  (0x1866d80530bb018e268063499013b17c030453013603c02200e,0x50c930699d01a2340e78ce19a330b92b52f05dccf1cd5a631184aa15a2735840c4186a3165826),
  (0x63d1901861d4026c1d0136024063001,0xa616c6000817c0200d8bf0320600b8be02a050098d92e03607b1112a83658503f07e2684c82600010c8991222255000070)]

def r8_4 : List Hint := [(0x13a39406448d013621404d07501901b404080d,0xa616c6000817c0200d8bf0320600b8be02a050098121520440281000e00021913224444aa0260000008991222255038000),
  (0x508bf00a82cc05f857010203c02680e,0x3a4744699d01a2340e78e519a330b91792f05dccf1cd61831061a8c596735858c4186a3165826),
  (0x64419009a04404dc05,0xa616c6000817c0200d8bf0320600b8be02a050098d96140fc1f89a132365868d81ae3586b0260e00a88991222255038000)]

def c9 : Catalogue := (8,78,0x831b46316c491003702a38831b46316c4910037831b46316c491003701620831b46316c4910037831b46316c49100370a60c6d18c5b124400dc11831e46d18c5b124400de0c6d18c5b124400dc32,0x8886867870000000888686787000000088868678700000008886867870000000888686776000000088868677600000008886867760000000888686776)

def r9_0 : List Hint := [(0x71bc001b6e00068cc00193200034c0000b2f80008bc00002ec0060b800172dc0058b600151b800506d00131b000486b00111a0004067000f198003865000d18000305f000b178002846000911400203600070d400182600050940010160003054000810000103c00000e,0x526350698d21a2340678e519a330658ca19232063a91042310618c2182c3821a95512a5144070),
  (0xb1bc002b6ec00a9b800296dc00a1ac00276a00079a0001d67c00059e002653c00954d00241b0008c6b00221a00084670020180007c5f000c178008050001f13c00784c001d128006044001710c005842,0x622c40150d421a34c692ce1a234067ab819c334660cb590604648c818ec3c132c718830d4628b),
  (0xedbc003a6e000e4cc003832c00dcc8003631c00d4c000342fc00ccbe001e2e00074b600022d00000b300321b000c46b00301a000bc67001e16000b857001d158000810002d03c00000e,0x526350698d21a2340678e519a330658ca19232063b0f51c31061a8c516c44218c4186a3145826),
  (0x10dbc00426e00104cc004032000d4bc00342ec00ccba00202e0007cb7000d2d0002cb2003f1b000f86b003d1a000f067000d18000b45f000b178008008002e01c007c06,0x620350698d21a2340678ce19a3306598119232063a91546310618c2182c4815187348a8550070),
  (0x111bf004b6c00129ae00496b000f9aa00486a000a5a600476900119a2004565801105a004014000dc4c003612c008848002111c006444,0x252c4d6b10d49834d5daac1a234155ab919c334662a956e5e4bc17733c170a0ada18830d462cb),
  (0x443180104c000392f000e0bb00242e0008cb7001a2d0011066005518001505f005317000c45b00521600144570050150004853004f098013825004d058013015,0x3a4744699d01a2340e78ce19a330b91792f05dccf0ef5b431061a8c596889798c4186a515805c),
  (0x171bf005c668016c70005a1b801646c00311a80160680029198015c640056188011456004214000e84c0027120006c44,0x252170b80d33a234c68aac1a23415c2de570334662b65baad8bc17733cc516dad518830c61174),
  (0x5c6d8010cc0003b2f000a0b8001c2d0017066006204001840f006003000f80b005f020017807005d010004803,0x5b0930699d01a2340e7ab819a330b92b62f05dccf1cd5aa310618c22e87042e187348a8568b15)]

def c10 : Catalogue := (1,68,0x831b46316c4910037,0x999797887)

def r10_0 : List Hint := [(0x75300019480005170001058000314000084c0001120000044,0x2931a834c690d11a033c670cd19832c650c919031d488c518830c610c1)]

end PEqualNP.Outside.L_meta_14162.G127

namespace PEqualNP.Outside.L_meta_14162.G127



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem symGood : ∀ v ∈ syms, Symmetry y v.1 v.2 := by
  have h : ∀ i : Fin syms.size,
      (∀ j : Fin 128, permRow syms[i.val].1 (permRow syms[i.val].2 j) = j ∧
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
  have p1 : ban c5 5 3 := more b4 p0 ok5_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_0 : ck c5 c6 5 0 r6_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_1 : ck c5 c6 5 24 r6_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_2 : ck c5 c6 5 48 r6_2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_3 : ck c5 c6 5 72 r6_3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_4 : ck c5 c6 5 96 r6_4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_5 : ck c5 c6 5 120 r6_5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_6 : ck c5 c6 5 144 r6_6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_7 : ck c5 c6 5 168 r6_7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_8 : ck c5 c6 5 192 r6_8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_9 : ck c5 c6 5 216 r6_9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_10 : ck c5 c6 5 240 r6_10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_11 : ck c5 c6 5 264 r6_11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_12 : ck c5 c6 5 288 r6_12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_13 : ck c5 c6 5 312 r6_13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b6 : ban c6 6 c6.1 := by
  have p0 := empty c6 6
  have p1 : ban c6 6 24 := more b5 p0 ok6_0
  have p2 : ban c6 6 48 := more b5 p1 ok6_1
  have p3 : ban c6 6 72 := more b5 p2 ok6_2
  have p4 : ban c6 6 96 := more b5 p3 ok6_3
  have p5 : ban c6 6 120 := more b5 p4 ok6_4
  have p6 : ban c6 6 144 := more b5 p5 ok6_5
  have p7 : ban c6 6 168 := more b5 p6 ok6_6
  have p8 : ban c6 6 192 := more b5 p7 ok6_7
  have p9 : ban c6 6 216 := more b5 p8 ok6_8
  have p10 : ban c6 6 240 := more b5 p9 ok6_9
  have p11 : ban c6 6 264 := more b5 p10 ok6_10
  have p12 : ban c6 6 288 := more b5 p11 ok6_11
  have p13 : ban c6 6 312 := more b5 p12 ok6_12
  have p14 : ban c6 6 333 := more b5 p13 ok6_13
  exact p14

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_0 : ck c6 c7 6 0 r7_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_1 : ck c6 c7 6 24 r7_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_2 : ck c6 c7 6 48 r7_2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_3 : ck c6 c7 6 72 r7_3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_4 : ck c6 c7 6 96 r7_4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_5 : ck c6 c7 6 120 r7_5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_6 : ck c6 c7 6 144 r7_6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_7 : ck c6 c7 6 168 r7_7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_8 : ck c6 c7 6 192 r7_8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_9 : ck c6 c7 6 216 r7_9 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_10 : ck c6 c7 6 240 r7_10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_11 : ck c6 c7 6 264 r7_11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_12 : ck c6 c7 6 288 r7_12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_13 : ck c6 c7 6 312 r7_13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_14 : ck c6 c7 6 336 r7_14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_15 : ck c6 c7 6 360 r7_15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7_16 : ck c6 c7 6 384 r7_16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b7 : ban c7 7 c7.1 := by
  have p0 := empty c7 7
  have p1 : ban c7 7 24 := more b6 p0 ok7_0
  have p2 : ban c7 7 48 := more b6 p1 ok7_1
  have p3 : ban c7 7 72 := more b6 p2 ok7_2
  have p4 : ban c7 7 96 := more b6 p3 ok7_3
  have p5 : ban c7 7 120 := more b6 p4 ok7_4
  have p6 : ban c7 7 144 := more b6 p5 ok7_5
  have p7 : ban c7 7 168 := more b6 p6 ok7_6
  have p8 : ban c7 7 192 := more b6 p7 ok7_7
  have p9 : ban c7 7 216 := more b6 p8 ok7_8
  have p10 : ban c7 7 240 := more b6 p9 ok7_9
  have p11 : ban c7 7 264 := more b6 p10 ok7_10
  have p12 : ban c7 7 288 := more b6 p11 ok7_11
  have p13 : ban c7 7 312 := more b6 p12 ok7_12
  have p14 : ban c7 7 336 := more b6 p13 ok7_13
  have p15 : ban c7 7 360 := more b6 p14 ok7_14
  have p16 : ban c7 7 384 := more b6 p15 ok7_15
  have p17 : ban c7 7 402 := more b6 p16 ok7_16
  exact p17

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8_0 : ck c7 c8 7 0 r8_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8_1 : ck c7 c8 7 24 r8_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8_2 : ck c7 c8 7 48 r8_2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8_3 : ck c7 c8 7 72 r8_3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8_4 : ck c7 c8 7 96 r8_4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b8 : ban c8 8 c8.1 := by
  have p0 := empty c8 8
  have p1 : ban c8 8 24 := more b7 p0 ok8_0
  have p2 : ban c8 8 48 := more b7 p1 ok8_1
  have p3 : ban c8 8 72 := more b7 p2 ok8_2
  have p4 : ban c8 8 96 := more b7 p3 ok8_3
  have p5 : ban c8 8 99 := more b7 p4 ok8_4
  exact p5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok9_0 : ck c8 c9 8 0 r9_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b9 : ban c9 9 c9.1 := by
  have p0 := empty c9 9
  have p1 : ban c9 9 8 := more b8 p0 ok9_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok10_0 : ck c9 c10 9 0 r10_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b10 : ban c10 10 c10.1 := by
  have p0 := empty c10 10
  have p1 : ban c10 10 1 := more b9 p0 ok10_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem withDebts (hard : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset) (k : ℕ) (run : build raw y k base.toFinset) : 11 ≤ k := by
  have denial := b10 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c10 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c10 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    hard denial run

end PEqualNP.Outside.L_meta_14162.G127

namespace PEqualNP.Outside.L_meta_14162.G127

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain0 : Hard y 0x3333333333333333 7 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x7af1cb86ad18b05ab14a84a910a03a70c982a508901a304880a10080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G61.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain1 : Hard y 0xffffffffffffffff 8 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x7ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G63.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain2 : Hard y 0xf0f00000f0f00000f0f00000f0f 8 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xd7ab4e8c78b0e0972a4c8870a0c056a94a846890a016284880608080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G107.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain3 : Hard y 0x3333000033330000333300003333 7 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xdb374c9d9334485a354895831408cb170c1c9130404a150814811000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G61.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain4 : Hard y 0xffff0000ffff0000ffff0000ffff 9 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xdfbb6ecd7ab4e8cf9b2e4c78b0e09f3a6cc972a4c88f1a2c4870a0c05eb96ac56a94a84e992a446890a01e3868c16284880e182840608080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G111.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain5 : Hard y 0x330033003300330033003300330033 7 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xebd38f0cb930e0ab528d08b120c06ad18b04a910a02a508900a10080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G117.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain6 : Hard y 0xff00ff00ff00ff00ff00ff00ff00ff 9 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xefdbaf4e7cb8f0cf9b2e4c78b0e0af5aad4a74a8d08f1a2c4870a0c06ed9ab466c98b04e992a446890a02e58a9426488900e182840608080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G119.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain7 : Hard y 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f 9 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xf7ebcf8e7cb8f0d7ab4e8c78b0e0b76acd8a74a8d0972a4c8870a0c076e9cb866c98b056a94a846890a03668c98264889016284880608080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G123.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem domain8 : Hard y 0x33333333333333333333333333333333 9 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xfbf3cf8ebd38f0dbb34e8cb930e0bb72cd8ab528d09b324c88b120c07af1cb86ad18b05ab14a84a910a03a70c982a508901a304880a10080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) G125.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem initial : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset := by
  intro d hd
  simp only [ds,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact domain0
  · exact domain1
  · exact domain2
  · exact domain3
  · exact domain4
  · exact domain5
  · exact domain6
  · exact domain7
  · exact domain8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (k : ℕ) (h : build raw y k base.toFinset) : 11 ≤ k := withDebts initial k h

end PEqualNP.Outside.L_meta_14162.G127

namespace PEqualNP.Outside.L_meta_14162.Graph

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev V := BitVec 130
def ops (a b : V) : List V := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
abbrev basicOps (a b : V) : Finset V := (ops a b).toFinset
def inputs : List V := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x200000000000000000000000000000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0x3ffffffffffffffff0000000000000000]
def truth : V := 0x2fffffffffefefefcfffeffeefefeaa00
def goal : V := ~~~truth
def extra : V := 0x200000000000000000000000000000000
def es : List ℕ := [0,4,0,5,1,5,2,5,0,6,1,6,4,6,1,7,2,7,3,7,6,7]
def target (x : Fin 8 → Bool) : Bool := decide (∃ i < es.length / 2,
  (List.ofFn x).getD (es.getD (2 * i) 0) false = true ∧
  (List.ofFn x).getD (es.getD (2 * i + 1) 0) false = true)

def circuit : List Gate := [⟨.or,[0,1]⟩,⟨.or,[2,3]⟩,⟨.or,[8,2]⟩,⟨.or,[1,9]⟩,⟨.or,[8,7]⟩,⟨.or,[4,12]⟩,⟨.and,[0,4]⟩,⟨.and,[10,5]⟩,⟨.and,[11,7]⟩,⟨.and,[6,13]⟩,⟨.or,[14,15]⟩,⟨.or,[16,17]⟩,⟨.or,[18,19]⟩]
theorem monotoneUpper : circuit.length = 13 ∧
    (∀ g ∈ circuit, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    ∀ x : Fin 8 → Bool, Circuit.eval ⟨circuit, 20⟩ (List.ofFn x) = target x := by
  refine ⟨rfl, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide +kernel


def holds (av : Finset V) (z : V) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset V} {z a : V} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset V} {z : V} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset V) (z : V) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset V} {z : V} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset V} {x y : V} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : V) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : V) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 130 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : V) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 130)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : V) (hw : w ∈ basicOps a b) (z : V) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset V} {x y : V} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 130) (z : V) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List V) (i : ℕ) (k : Fin 130) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List V) (g : Gate) : V := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 100000 in
theorem action_spec (w : List V) (g : Gate) (hg : legal g) (k : Fin 130) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : V)[k.val] = false := by change (0#130)[k.val] = false; simp
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
theorem available_read {av : Finset V} {w : List V} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List V) (av : Finset V) (hw : ∀ u ∈ w, holds av u)
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
    show ∀ x : V, x ||| (0 : V) = x from fun x => BitVec.or_zero,
    show ∀ x : V, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
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
    (w : List V) (av : Finset V) (hw : ∀ u ∈ w, holds av u)
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
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : V => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset V) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
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


def trunc (v : V) : W := v.setWidth 128

theorem trunc_op {a b z : V} (h : z ∈ basicOps a b) : trunc z ∈ raw (trunc a) (trunc b) := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  simp only [raw,words,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  rcases h with rfl | rfl | rfl | rfl
  · left; ext i hi; simp [trunc,hi]
  · right; left; ext i hi; simp [trunc,hi]
  · right; right; left; ext i hi; simp [trunc,hi]
  · right; right; right; ext i hi; simp [trunc,hi]

theorem diff130 (i j : Fin 130) {a b z : V} (h : z ∈ basicOps a b)
    (diff : z[i.val] ≠ z[j.val]) : a[i.val] ≠ a[j.val] ∨ b[i.val] ≠ b[j.val] := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  rcases h with rfl | rfl | rfl | rfl <;> simp [ha,hb] at diff

theorem source_zero {a b z : V} (h : z ∈ basicOps a b) (one : z[0] = true) :
    a[0] = true ∨ b[0] = true := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp at one <;> tauto

theorem project_core {k : ℕ}
    (run : build basicOps truth k inputs.toFinset) : 12 ≤ k := by
  obtain ⟨s,sub,live'⟩ := compress run
  have difference : truth[128] ≠ truth[129] := by decide +kernel
  obtain ⟨v,hv,ev⟩ := live_separates (fun w : V => w[128] ≠ w[129]) difference
    (fun _ _ _ hop => diff130 128 129 hop) live'
  have classify : inputs.all (fun w => (w[128] == w[129]) || (w == extra)) = true := by decide +kernel
  have cls := List.all_eq_true.mp classify v (List.mem_toFinset.mp (sub hv))
  simp only [Bool.or_eq_true,beq_iff_eq] at cls
  have extraIn : extra ∈ s := cls.resolve_left ev ▸ hv
  have positive : 0 < zeroCount trunc 0 s := Finset.card_pos.mpr
    ⟨extra,Finset.mem_filter.mpr ⟨extraIn,by decide +kernel⟩⟩
  have eq : trunc truth = G127.y := by decide +kernel
  obtain ⟨l,pay,smaller⟩ := project_live basicOps raw trunc 0
    (fun _ _ _ hop => raw_simple (trunc_op hop)) (fun _ _ _ hop => trunc_op hop)
    (by decide +kernel : trunc truth ≠ 0) live'
  rw [eq] at smaller
  have permitted : project trunc 0 inputs.toFinset ⊆ G127.base.toFinset := by decide +kernel
  have bound := G127.lower l (build_subset smaller ((project_subset trunc 0 sub).trans permitted))
  omega

theorem binary_lower
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs,legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    12 ≤ binaryCost gs := by
  have width : inputs.length = 8 := rfl
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have sample : ∀ j : Fin 130, target (fun i => (inputs.getD i.val 0)[j.val]) = bit j (~~~goal) := by
    decide +kernel
  have evaluate (k : Fin 130) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 8) : Bool := bit k (inputs.getD i.val 0)
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
    obtain ⟨w,hw,on⟩ := live_separates (fun w : V => w[0] = true)
      (by decide +kernel : goal[0] = true) (fun _ _ _ h => source_zero h) hr
    have none : inputs.all (fun w => !w[0]) = true := by decide +kernel
    have no := List.all_eq_true.mp none w (List.mem_toFinset.mp (sub hw))
    simp [on] at no
  · apply project_core
    simpa only [goal,BitVec.not_not] using run

theorem comparison
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs,legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    ∃ (ms : List Gate) (mo : ℕ),
      (∀ g ∈ ms, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ms.length ≤ gs.length ∧ ∀ x : Fin 8 → Bool, Circuit.eval ⟨ms,mo⟩ (List.ofFn x) = target x := by
  by_cases has : ∃ g ∈ gs, g.op = GateOp.not
  · obtain ⟨g,hm,op⟩ := has
    have less : (gs.filter isBinary).length < gs.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g,hm,by simp [isBinary,op]⟩
    have count := binary_lower gs o hg he
    change 12 ≤ (gs.filter isBinary).length at count
    obtain ⟨len,legal',correct⟩ := monotoneUpper
    exact ⟨circuit,20,legal',by omega,correct⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hm
    obtain ⟨ops',size⟩ := hg g hm
    exact ⟨by rcases ops' with a | b | n; exact .inl a; exact .inr b; exact (has ⟨g,hm,n⟩).elim,size⟩

end PEqualNP.Outside.L_meta_14162.Graph

theorem PEqualNP.Outside.L_meta_14162 :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  exact PEqualNP.Outside.L_meta_14162.Graph.comparison gates o legal computes
