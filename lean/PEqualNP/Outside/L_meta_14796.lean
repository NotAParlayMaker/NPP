import PEqualNP.Defs

-- The induced graph on 0,1,3,4,6,7 consists of two triangles joined by an edge.
-- Its ten-gate signed lower bound uses two smaller induced graphs and a live-wire
-- certificate. Restricting the two other essential vertices saves two gates.
-- The signed compilation and live relations derive from L_meta_9136, with the
-- finite certificate checker from L_meta_10590. Both are in the project sources.

namespace PEqualNP.Outside.L_meta_14796

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

end PEqualNP.Outside.L_meta_14796

namespace PEqualNP.Outside.L_meta_14796

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

end PEqualNP.Outside.L_meta_14796

namespace PEqualNP.Outside.L_meta_14796

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

end PEqualNP.Outside.L_meta_14796

namespace PEqualNP.Outside.L_meta_14796

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

end PEqualNP.Outside.L_meta_14796

namespace PEqualNP.Outside.L_meta_14796

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

end PEqualNP.Outside.L_meta_14796

namespace PEqualNP.Outside.L_meta_14796

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

end PEqualNP.Outside.L_meta_14796

namespace PEqualNP.Outside.L_meta_14796.Bridgepaw

def y : W := 0xfeeefaa0

def base : List W := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def neg : List (Fin 64) := [0,1,2,3,4,6,8,10,16,20,24]

def dict : ℕ := 0xfffff0f000000000fffff00000000000ffffcccc00000000ffffaaaa00000000ffffa0a000000000ffff303000000000ffff000000000000fff0fff000000000ffeeff0000000000ffccff0000000000ffaaff0000000000ffa0ffa000000000ff0fff0000000000ff00ff0000000000fefef0f000000000fcfcfcfc00000000fcfcf0f000000000fcccfccc00000000fafafafa00000000faaafaaa00000000f0f0f0f000000000f0f0000000000000f0a0f0a000000000f000f0f000000000f000f00000000000eeeeeeee00000000eeeecccc00000000eeeeaaaa00000000eeee000000000000ecececec00000000ccff000000000000cceeccee00000000ccee000000000000ccccfcfc00000000cccceeee00000000cccccccc00000000ccccc0c000000000cccc888800000000cccc444400000000cccc00cc00000000cccc000000000000c4c4c4c400000000c0c0c0c000000000bbbbaaaa00000000bbbb000000000000aaaaaaaa00000000aaaa000000000000a0a0a0a000000000888888880000000055ff000000000000555500000000000050f050f0000000005050f0f000000000505050500000000044cc44cc000000004444cccc00000000444444440000000044440000000000003333303000000000333322220000000033330000000000003030f0f00000000030303030000000002222aaaa00000000222222220000000011110000000000001010f0f0000000000fff0000000000000ccc0ccc000000000aaa0aaa0000000000ff00000000000000fa00fa0000000000f000f00000000000cc00cc0000000000aa00aa000000000000f0f0000000000000eeee000000000000cccc000000000000aaaa

def masks : List W := []

def ds : Debts := []

def syms : Array Sym := #[([],[]),([0x4,0xf000f000f000f0,0xf000f000f000f00],[0x4,0xf000f000f000f0,0xf000f000f000f00])]

def book : ℕ := 0x84410a0210a042084214a4694a9294a8634a5295286a5254a524635294a294252a0a52a021294a542108415084150542108318c6318c6318c8318c6421084210a421084210a08421084240842408421294a5294aa294a5294a542108421084210442108210842108921089210842108421086210842108621084210842108721084210842108621084210842108821084210842108821088210842108821084084c10a4210a4c608421084810a8210a884084214a5294a8214a9294a4295294a524215254a5282a42108420844210842088084210842308423084214a5294a9294a92a4a5295294a5254a525495294a210842108521084210852108521084210852108418c6318c6918c6318c63210862108421084210865294a5294a529435294a18c6318c6318c6318c6321084210852108521084084290842108429084210842a084210842a0842110842108421084810842084240842108421084240842608421084210842618c6318c6818c6318c63421094210842109421082108421084210862108442108421094210942108084220842108422084210842508421084250842121024220442202121044084420a0210a042084214a4a94a9294a8a54a529528ea5254a524e75294a0842108422084210842208421084230842108423084e10a4210a4e708421084a10a8210a8a508421084210a0280a021084214a4294a9294a8214a5295282a5254a524215294a29425294a529421294a52942529ca529c21294a539c27394e73942139ce7084230842108423084214210842108421034210839ce739ce739ce339ce7318c6318c6318c4318c621084210812108421084210842108521084210840000100000000010000042108421064210842108084270842108427084210842108421084280842121084210842108a2108421088210842108421084421084210442108421085294a5294a5294a5294a0842108424084210842408421084260842108426084210a4210a42908421084210a8210a82a08421210242208422021210842108121084210842108421082210842108421084421084210842105421082108421084210882108418c6318c6018c6318c63294a5294a5294a3294a50000000000000030000310842108421084310842084210842308421084212108421080210842108400000000000000400001318c6318c6318c9318c62108421084210832108418c6318c6318c6418c63318c6318c6318c3318c6318c6318c6318c5318c64210442108421084210800000000000000300000000000000000005000000842108420084210842110842108401084210842421084210142108421080842108425084210842108421084210842108422318c6318c6318ca318c642108421084210a421084210842108421094210821084210842108921084084210842208421084210848109821098840842108421098210982608421084210902109024084212102421884218212108431826310c631021318c62102421084210212108410842108421084710842108421084210845108420000000000000020000010842108421084210842294a5294a5294a1294a539ce739ce739ce139ce74a5214a5294a5294a529294a5294a1294a5294a539ce739ce139ce739ce7421084210842108421080842108421084270842100000000000000200001318c6318c6318c7318c6294a5294a5294a5294a5084210842108425084211084210842108411084242108421084210142108084210842108422084210842108421084230842121084210842108521084084210842108426084214a5294a5294a5294a529084240842108424084212108621084210842108408421084240842108421084210842608421084210000000000000010000021084210842108421084318c6318c6318c6318c60000000000000060000000000000000000400000084210842108421084210842108421084290842108421084210842a084210842108421084240842121084210842108121084318c6318c6318c1318c600000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (3,27,0x10c3b0d2388211470ec34,0x0)

def r2_0 : List Hint := [(0,0xc01001),
  (0,0xc01001),
  (0,0xc01001)]

def c3 : Catalogue := (16,37,0x922407816430ec2708a488c1f84524420d01292230761a420ec3402678841d869083b0d0018a1d84e11420ec2f08a10761984508330880d8e1d86611420ec340ce10761980324420ec34,0x0)

def r3_0 : List Hint := [(0,0x280400600801001),
  (0,0x180800e00800806),
  (0x94200015,0x180200201803000),
  (0x10d4000005,0x180001200800809),
  (0,0x400201600c05001),
  (0,0x180800e0080080b),
  (0,0x180800e0080080b),
  (0,0x180800e00800802),
  (0,0x180b0160340600a),
  (0,0x180601e0040100e),
  (0x200815,0x180200204003002),
  (0,0x280400600801001),
  (0,0x280200401001801),
  (0,0x280400600801001),
  (0x805,0x18110060080080a),
  (0,0xb81602a05009812)]

def c4 : Catalogue := (65,47,0x49108380b02292218761604524420ec2808a48841d85c11491083b0881592210761584524480dc2c08a107616044064e1083b0b02292210761101724420f83b08a48841d85805491083c0ec2c92210761204524420ec2708a48841604409491183b0b02292210761602124420ec340b210761384404cf1083b09c22922107611027083b09c2204e48841384409491183b09c2292210761382124420ec3409e48841d8681100124420ec34841d8621604528420ec2c08a10761384400c91083b0a42292210761684524420ec2205248841d85411420ec270882192210581103724450ec2c08a48841d8440c491083b0d42292210761304524420ec3008a4876160440449108390b022841d8581103d2c420ec2c08a4884160440e491103b0b02292210761103324420ec3208a48841d84611491083b0881692210761b045083b0b02200e10761985811491083b0880e841d86c1100724420ec3308a10761b06611001083b0cc2292210761b00330491083b0da48841d86c0bc91083b08817,0x0)

def r4_0 : List Hint := [(0,0xd817006008010010340480c818),
  (0,0xd817006008010010280780e81c),
  (0x31,0x1102100a0800200302407c01001),
  (0x461,0x1282400608c0100100c0841000a),
  (0x804138000c4600040f8200c36000102c000807,0x1582a0520a013826),
  (0,0x180200206c0b8000420800502c),
  (0x10e4000005,0x168300060001782e05a0080081c),
  (0x141d,0x180b0160841000001a0c800031),
  (0x143d,0x400700602c010010000cc1981c),
  (0,0x181b02e04c098140040040b012),
  (0,0x183706e02c0583601a0c81a834),
  (0x1461,0xd81700602c010010580841000a),
  (0x5,0x2804006008010010000bc17000),
  (0,0x40070060181983300400800838),
  (0,0xd8240760500983a02c0841d039),
  (0,0xd817006058010010280f009812),
  (0,0xd8240060500981902c0081e819),
  (0,0xd8140260580101202e00c09801),
  (0,0xd81707c0500981902c0541e819),
  (0,0x18130260080081203605c0a016),
  (0,0xd8040220500981302c05400819),
  (0,0x1b01404602c058230580d42003f),
  (0x1861,0xd81700602c0680105800800839),
  (0,0xd8170060680901b00400800812)]

def r4_1 : List Hint := [(0x1461,0x1282400608c0981308200800812),
  (0,0xd8170060080100108404c09812),
  (0x1c61,0xd82400608c0981308600800812),
  (0,0xd8140260580101202e00c09801),
  (0x1c350807094001415,0x180800e0080080200c01803000),
  (0x5,0x280400604c098130880080080a),
  (0,0x400700602c0100106a10020045),
  (0,0xd8170060d40100106a08410046),
  (0,0xd8170060500901902c00800846),
  (0x2045,0x180800e02c0580001a0300300a),
  (0,0x18170760500984802c00823812),
  (0,0x181b02e04c098140040040b012),
  (0xa178202456080a13800244600080a8000822,0x2584a05612414027),
  (0x5184002039,0x280400602c0a81500c1342600a),
  (0x80c0b4002c25000c074202c15,0x28040060080100100c0180301c),
  (0x5,0x28040060001782e00400800800),
  (0xd114002c05,0x28040060240e04e0040080084e),
  (0x3045,0x280005e0080101c00800c08001),
  (0,0x180800e0080080b00a0100e002),
  (0,0x400700602c0100100c0cc1984f),
  (0x2405,0x180601e000288500020080700a),
  (0xa114203825,0x181107a0080080902001829002),
  (0,0x28040060080100102604c09812),
  (0,0xd8170061080981300400800812)]

def r4_2 : List Hint := [(0,0xd80400614c0981300400800812),
  (0,0xd8140260580101202e00c09801),
  (0x5,0x28040060001782e0040080081c),
  (0,0x40070061542785403e0540a80a),
  (0x3c55,0xd81600405c0300102804c09013),
  (0,0xd8170060500981302c00800812),
  (0,0xd81402605c0b81302c08409020),
  (0,0xd8170060580100102804c09812),
  (0,0xd81700a0500981302c0540a812),
  (0,0x18130260080081203605c0a016),
  (0x3c15,0xb82d0000500981202c05405012),
  (0,0x281700605c0900500400800812),
  (0,0x403600602c0100100615c29056),
  (0,0xd8030760500985a02c0082c858),
  (0,0x28170060502d01302c00800812),
  (0x3861,0xd8170060480981308a00800812),
  (0,0xd8170060500981302c00800812)]

def c5 : Catalogue := (31,57,0x491083b0b02202648841d858110093c491083b0b02292210761d05811491083b0b02201e4890210761604524420ec370b0229221076160440980124420ec2204e48841d8581100534491083b0b02292210761604e1100124420ec2708a48841d8581102324420ec2c0880692210801d85811491083b0b02508a48841d8581103b24420ec2c0880198248841d85811491083b0b02208648841d8581103524420ec2c08805922107a1d85811491083b0b02208248841d8581102e00491083b0881792210761604407c91083b0d82c0880092210761b04524420ec2c0881f,0x0)

def r5_0 : List Hint := [(0x1d,0x6c0b8030340f01d0020040042305b0b616c00018),
  (0x206f00071a8001863000518800106100030ec000837000103c00000e,0x318620561843005f0bc1742e00a),
  (0x28b900092c400040d,0x6c0b80300c1342601402604c0e01604208005018),
  (0x2c15,0x6c0b8030340f01d016042080230650c81900000a),
  (0xd0fc003033000b01c000406,0x318620561a4140270d019c33018),
  (0x455,0x6c0b80302804c098020040040506b0d414c0e018),
  (0x81313400484508110f4004035080f074003815,0x6c1203e02804c0c81602a0f40c80600c0180e00a),
  (0x153242050c1,0x6c3280602e00c048140261b0098020040240f812),
  (0x817074005815,0x940b83e028048098010da0040c86500c1300e00a),
  (0,0x6c0b80302804c0981602a0040c86a01e0243700a),
  (0x70b1081b0f4006835001b0b42068250019074006015,0x941200304604c098430040040900600c0180e01c),
  (0x788d001d204000805,0x88388050e00100181c02604c0980a0de0540a81c),
  (0x212c4000c550020074007c15,0x941200304604c0987202a0540e00609a1300e00a),
  (0x8064003011,0x140200302604c09802004004090220e81cc0e01c),
  (0,0x6c0b80302804c3b86a0d41d8080160040041c875),
  (0,0x6c3585b0480ec0306b0780703c8160041e02c812),
  (0,0x6c0b8030d60101d0160040041c86b0ec16c0e07a),
  (0x823134008845,0x6c1203b02804c2d0160041641c80601e0180807b),
  (0xb49e082c25820b48e002c21800ac6f002a1b820a45e002815800a44e082811800843a001c0c800300e002702c0098070025018009005,0x2584a0560003e87c0920a01381c),
  (0xa8bd08311f400c07500311b420c065002f02400b805,0x140200302604c0982200c0180e0020040040900a),
  (0xac8d,0x183f0250fc090018000de1682d07508200800846),
  (0xc81d,0x14020030a41682d002004004230220b616c0007a),
  (0x320fc00a83e000802c00cc07,0x418820561241402700c2044007f),
  (0xa8b1,0x941200304604c09841004004090060e81cc0e084)]

def r5_1 : List Hint := [(0xe8c500392f400e0b5003716400d855003506400d015,0x6c0b80600c0280481402604c0e01602a05405012),
  (0xe891,0x1a843806072018430140d80480c81610a1b42c012),
  (0,0x6c1c81102804c0c81602a1600906a01401837088),
  (0,0x6c0b8030301d02701402604c3601600400444812),
  (0xf08d003b20400b071,0x184602d00c22c0781c02404c1707808a00845012),
  (0x83e07400f415,0x6c0200f02804c170160042280901801e0180e088),
  (0xb4b100400b420fc25,0x6c1800303204c0988e0040040900602001846884)]

def c6 : Catalogue := (1,47,0x491083b0b022,0x0)

def r6_0 : List Hint := [(0x1e28020749c081c260206c94081e24000748c001c220006c84081a20000687c00191e000607400171c000586f00151b00050680013190004863081118000405c080f160203854001114020404c000f120003844000d10000303c000b0e000283408090c000202c08070a0201824000908020201c0007060001814000504000100e00030300008080001018000004,0x3186205624c490911200a01388f)]

end PEqualNP.Outside.L_meta_14796.Bridgepaw

namespace PEqualNP.Outside.L_meta_14796.Bridgepaw



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
theorem ok2_0 : ck c1 c2 1 0 r2_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b2 : ban c2 2 c2.1 := by
  have p0 := empty c2 2
  have p1 : ban c2 2 3 := more b1 p0 ok2_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3_0 : ck c2 c3 2 0 r3_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b3 : ban c3 3 c3.1 := by
  have p0 := empty c3 3
  have p1 : ban c3 3 16 := more b2 p0 ok3_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4_0 : ck c3 c4 3 0 r4_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4_1 : ck c3 c4 3 24 r4_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4_2 : ck c3 c4 3 48 r4_2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4 : ban c4 4 c4.1 := by
  have p0 := empty c4 4
  have p1 : ban c4 4 24 := more b3 p0 ok4_0
  have p2 : ban c4 4 48 := more b3 p1 ok4_1
  have p3 : ban c4 4 65 := more b3 p2 ok4_2
  exact p3

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
  have p2 : ban c5 5 31 := more b4 p1 ok5_1
  exact p2

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
theorem lower (k : ℕ) (run : build raw y k base.toFinset) : 7 ≤ k := by
  have denial := b6 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c6 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c6 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    (by simp [ds]) denial run

end PEqualNP.Outside.L_meta_14796.Bridgepaw

namespace PEqualNP.Outside.L_meta_14796.Bridgedis

def y : W := 0xffececa0

def base : List W := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def neg : List (Fin 64) := [0,1,2,3,4,6,8,9,12,16,17,20]

def dict : ℕ := 0xffffa0a000000000ffff000000000000ffa0ffa000000000ff00ff0000000000f0f0f0f000000000cccccccc00000000aaaaaaaa00000000a0a0a0a0000000004c4c4c4c000000000a0a0a0a

def masks : List W := []

def ds : Debts := []

def syms : Array Sym := #[([],[]),([0x8,0xff000000ff00,0xff000000ff0000],[0x8,0xff000000ff00,0xff000000ff0000]),([0x6,0xcc00cc00cc00cc,0x3300330033003300],[0x6,0xcc00cc00cc00cc,0x3300330033003300]),([0xe,0xcccc0000cccc,0x3333000033330000,0x6,0xcc00cc00cc00cc,0x3300330033003300],[0x8,0xff000000ff00,0xff000000ff0000,0x6,0xcc00cc00cc00cc,0x3300330033003300]),([0x8,0xff000000ff00,0xff000000ff0000,0x6,0xcc00cc00cc00cc,0x3300330033003300],[0xe,0xcccc0000cccc,0x3333000033330000,0x6,0xcc00cc00cc00cc,0x3300330033003300]),([0xe,0xcccc0000cccc,0x3333000033330000],[0xe,0xcccc0000cccc,0x3333000033330000]),([0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x8,0xff000000ff00,0xff000000ff0000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x8,0xff000000ff00,0xff000000ff0000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0xe,0xcccc0000cccc,0x3333000033330000,0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x8,0xff000000ff00,0xff000000ff0000,0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x8,0xff000000ff00,0xff000000ff0000,0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0xe,0xcccc0000cccc,0x3333000033330000,0x6,0xcc00cc00cc00cc,0x3300330033003300,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0xe,0xcccc0000cccc,0x3333000033330000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0xe,0xcccc0000cccc,0x3333000033330000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050])]

def book : ℕ := 0x18ca31a8631a8a518c6318ca319c6319ca518c6339c673a0e73a06339ce7294652aca52ac63294a5294652a0a52a063294a508421090240902108421420e841508414e54210800000000000000300000084210842208421084210842108423084210842110842108421084310842318c6318c6318c7318c608421084210842a084210842108421084270842108421084210842308421108c212442124c61084231846324c632442318c64a44949929498424a5291084212442124491084210842118421184610842318c6308c6308c2318c6000000000000002000000000000000000090000000000000000000600000108421084210842108424a5294a5294a5294a52910842108421084610842318c6318c6318c2318c64a5294a5294a5224a52900000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (1,24,0xa02005,0x0)

def r2_0 : List Hint := [(0,0xc01001)]

def c3 : Catalogue := (3,34,0x240701403901c0300a80701403,0x0)

def r3_0 : List Hint := [(0x54400005,0x180200200002004),
  (0,0x180700c00800805),
  (0,0x180200201c03008)]

def c4 : Catalogue := (3,44,0x901c0501001901c050100300240701403,0x0)

def r4_0 : List Hint := [(0x18010b800002610010782000160001038800006,0x700d01802c05009),
  (0,0x180200204c0981202204007800),
  (0x80d,0x18020020580b00802a0540a000)]

def c5 : Catalogue := (1,44,0x901c0601404,0x0)

def r5_0 : List Hint := [(0xc0081f0002068c004130001048000011,0x701d0380340601b0340640c017)]

end PEqualNP.Outside.L_meta_14796.Bridgedis

namespace PEqualNP.Outside.L_meta_14796.Bridgedis



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
theorem ok2_0 : ck c1 c2 1 0 r2_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b2 : ban c2 2 c2.1 := by
  have p0 := empty c2 2
  have p1 : ban c2 2 1 := more b1 p0 ok2_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3_0 : ck c2 c3 2 0 r3_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b3 : ban c3 3 c3.1 := by
  have p0 := empty c3 3
  have p1 : ban c3 3 3 := more b2 p0 ok3_0
  exact p1

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

end PEqualNP.Outside.L_meta_14796.Bridgedis

namespace PEqualNP.Outside.L_meta_14796.Bridge

def y : W := 0xfffefefeffececa0

def base : List W := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]

def neg : List (Fin 64) := [0,1,2,3,4,6,8,9,12,16,17,20,32,40,48]

def dict : ℕ := 0xffffffffffffff00fffffffffffff0f0ffffffffffffccccffffffffffffaaaaffffffffffff0000fffffffffff0fff0ffffffffffeeffeeffffffffffccffccffffffffffcccc00ffffffffffaaffaaffffffffff00ff00fffffffffefefefefffffffffcfcfcfcfffffffffafafafafffffffff0f0f0f0ffffffffeeeeeeeeffffffffccccccccffffffffcccccc00ffffffffcccc0000ffffffffaaaaaaaaffffffff0c0c0c0cffffffff0c0c0c00ffffffff05050500ffffffff00cc00ccffffffff0000ffccffffffff0000ccccffffffff00000000fffffffafffffffaffffffeeffffffeeffffffccffffffccffffffccffffff00ffffffccccccccccffffffaaffffffaaffffff00ffffff00fffffefeffffa0a0fffffefeffff0000fffffafafffffafafffffafaffff0000fffff4f4ffff0000fffff0f0fffff0f0ffffeeeeffffeeeeffffeeeeffffaaaaffffeeeeffff0000ffffccffffffccccffffccffffff0000ffffcccfffff0000ffffccccffffccccffffccccffffcc00ffffccccffff0000ffffcc0cffffcc00ffffaeaeffff0000ffffaaffffffaaaaffffaaffffff0000ffffaaeeffff0000ffffaabbffff0000ffffaaafffff0000ffffaaaaffffaaaaffff3333ffff0000ffff3232ffff0000ffff0f0fffff0000ffff0e0effff0000ffff0c0cffff0c0cffff0c0cffff0c00ffff0c0cffff0000ffff00ffffff0000ffff00faffff0000ffff00eeffff0000ffff00ccffff00ccffff00ccffff0000ffff00bbffff0000ffff0055ffff0000ffff0033ffff0022ffff0033ffff0000ffff003300000000ffff0032ffff0032ffff000fffff0000ffff0005ffff0000ffff0003ffff0000ffff0000ffffccccffff0000ffff0000fffefffefffefffefffefffeffa0ffa0fffefffeff00ff00fffcfcfcfffcfcf0fffcf0f0ffeca0a0fffafffafffafffafff0fff0fff0fff0ffeeffeeffeeffeeffeeffeeffaaffaaffeeffeeccccccccffcfffcfffccffccffccffffffccffccffccffccffccffccffccffccffccff00ffccffccff88ff88ffccffccff00ff00ffccffccaa88aa88ffccffcc00000000ffccff88ffccff88ffccff0cffccff00ffccccccffcccc00ffcccc0cffcccc00ffcc3300ffcc3300ffcc0000ffcc00ccffcc0000ffcc0000ffc8ffc8ffc8ffc8ffaaffffffaaffaaffaaffeeffaaffeeffaaffaaffeeffeeffaaffaaffaaffaaffaaffaacc88cc88ffaaf0a0ffaaf0a0ffaacc88ffaacc88ff88ff88ffccffccff00ffffff00ff00ff00ffccff00ff00ff00ff00ffccffccff00ff00ff00ff00ff00ff00ff00cc00ff00ee22ff00ee22ff00ee00ff00ee00ff00cc00ff00cc00ff000000ff00ff00fefefefefefefefefefefefefafafafafefefefef0f0f0f0fefefefeccccccccfefefefeaaaaaaaafefefefea0a0a0a0fefefefe00000000fcfcfcfcfcfcfcfcfcfcfcfcfcfcfcf0fcfcfcfcf0f0f0f0fcfcfcfca8a8a8a8fcfcfcfc00000000fbfbfbfbfafafafafbfbfbfbaaaaaaaafafafffffafafafafafafefefafafefefafafafafefefefefafafafafafafafafafafafac8c8c8c8fafafafa00000000fafafa00fafafa00fac8fac8fac8fac8f4f4f4f4f4f4f4f4f3f3f3f3f0f0f0f0f0f0fcfcf0f0fcfcf0f0fcfc00000000f0f0f0f0fcfcfcfcf0f0f0f0f0f0f0f0f0f0f0f0e4e4e4e4f0f0f0f0e0e0e0e0f0f0f0f0a0a0a0a0efefefefeeeeeeeeeeeeffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaeeaaeeeeeeeeee00ee00eeeeeeeeeaeaeaeaeeeeeeeee0e0e0e0eeeeeeeeaaaaaaaaeeeeeeaaeeeeeeaaeeeeee00eeeeee00eeeaeeeaeeeaeeeaeee0eee0eee0eee0eeaaeeaaeeeeeeeeeaeaeaeaeeeeeeeecfcfcfcfcfcccfcccfcfcfcfcececececfcfcfcfcccccccccfcfcfcccfcfcfcccfcecfcecfcecfcecdcdcdcdccccccccccccffffccccffccccccffffcccceeeeccccffffccccccccccccffeeccccffeeccccfefeccccfefecccccfcfccccccccccccccffccccccccccccccccffffffccccccccccffeeffeeccccccccff00ff00ccccccccfefefefecccccccccccccccccccccccccccccc88cccccccccccccc00cccccccccc88cc88cccccccccc00cc00ccccccccc8c8c8c8ccccccccc0c0c0c0cccccccc88888888cccccccc04040404cccccccc00000c0ccccccccc000000cccccccccc00000000cccccc88cccccc88cccccc0ccccccc00cccccc04cccccc04cccccc00ffffff00cccccc00cccccccccccccc00cccccc00ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0cc88cc88ffaaffaacc88cc88cccccccccc88cc88cc88cc88cc0ccc0ccc00cc00cc00cccccc00cc00c8c8c8c8fafafafac8c8c8c8ccccccccc8c8c8c8c8c8c8c8bbbbbbff00000000bbbbbbbbbbaabbaabbbbbbbbbb00bb00bbbbbbbbbababababbbbbbbbb0b0b0b0bbbbbbbbaaaaaaaabbbbbbbb88888888bbbbbbbb00000000bbbbbbaabbbbbbaabbbbbb00bbbbbb00bbbabbbabbbabbbabbb0bbb0bbb0bbb0b8b8b8b8b8b8b8b8afafafafafaaafaaafafafafaeaeaeaeafafafafaaaaaaaaafafafaaafafafaaafaeafaeafaeafaeaeaeaeaeaeaeaeaeaeaeaeae00000000ababababaaaaaaaaababababa0a0a0a0abababab00000000aaaaffffaaaaffaaaaaaffffaaaafafaaaaaffffaaaaeeeeaaaaffffaaaaaaaaaaaafffaaaaafffaaaaaffeeaaaaffeeaaaafefeaaaafefeaaaaeeeeaaaaeeeeaaaaeeee00000000aaaabbbbaaaaaaaaaaaabbbb00000000aaaaafafaaaaaaaaaaaaafaf00000000aaaaaeaeaaaaaeaeaaaaaaffaaaaaaaaaaaaaaff00000000aaaaaaeeaaaaaaeeaaaaaaaaffffffaaaaaaaaaafffafffaaaaaaaaaffeeffeeaaaaaaaafefefefeaaaaaaaaf0f0f0f0aaaaaaaaeeeeeeeeaaaaaaaaaeaeaeaeaaaaaaaaaaaaeeeeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaaaaaaaaaa8aaa8aaaaaaaaaaa2aaa2aaaaaaaaaaa0aaa0aaaaaaaaa8a8a8a8aaaaaaaaa2a2a2a2aaaaaaaaa0a0a8a8aaaaaaaaa0a0a2a2aaaaaaaaa0a0a0aaaaaaaaaaa0a0a0a0aaaaaaaa222222aaaaaaaaa2aaaaaaa2aaaaaa00ffffff00aaa2aaa2aaa2aaa2aaa2aaa2aaa0aaa0aaa2aaa2a0a0a0a0aaa0aaa0fff0fff0aa88aa88ffccffccaa22aa22aa22aaaaaa02aa02aaaaaaaaa8a8a8a8fcfcfcfca2a2aaaaa2a2a2a2a2a2a2aaa2a2a2aaa2a2a2a2a2a2aaaaa2a2a2a2a2a2a2a2a2a2a2a2a2a0a2a0a2a2a2a2a0a0a0a08c8c8c8c888888888888cccc8888888888888c8c88888c8c888888cc888888cc88888888cccccccc888888888c8c8c8c888888888888cccc5555555550505050333333333333000033333333330033003333333330303030333333332222222233223322ffaaffaa32323232fafafafa22222222aaaaaaaa22222222aaa2aaa20f0fcfcf0000cccc0f0f0f0f0a0a0a0a0f0f0f0f000000000f0c0f0c0f0c0f0c0f000c00ff00ff000f000a00ff00ff000f000300ff00ff000e0e0e0e0e0e0e0e0c0cffff0c0c0c0c0c0c0c0c0c0c0c0c0b000b00ff00ff000a020a02aaaaaaaa05050505fafafafa050505050000000005000500ff00ff0004040404cccccccc03030303fcfcfcfc03030303f0f0f0f003000300ff00ff0002020202aaaaaaaa01000100ff00ff0000ff00ff00cc00cc00ff00ff0000000000ccffff00cc00cc00550055000000000033ffff0000ffcc0022ffee0022ffee00222222002222aa0000ffff0000ffee0000ffff0000ffcc0000ffff0000ffaa0000ffff0000ff000000ffff0000fafa0000ffff0000eeee0000ffff0000cccc0000ffff0000aaaa0000ffff00000c0c0000ffff000000cc0000ffff000000000000fffe0000fffe0000fffa0000fffa0000ffee0000ffee0000ffcf0000ffcc0000ffcc0000ffcc0000ffcc0000ff000000ffcc000000000000ffaa0000ffee0000ffaa0000ffaa0000ffaa000000000000ff880000ffcc0000ff330000ff000000ff33000000000000ff0f0000ff000000ff0c0000ff0c0000ff000000ffee0000ff000000ffcc0000fefe0000fefe0000fafa0000fafa0000fafa000000000000eeee0000eeee0000eeee0000aaaa0000eeee000000000000cfcf0000cccc0000ccff0000cccc0000cccc0000cccc0000cccc0000cc000000cccc000088880000cc880000cc880000cc000000cccc0000c8c80000c8c80000bbbb0000aaaa0000bbbb000000000000afaf0000aaaa0000aeae0000aeae0000aaff0000aaaa0000aaee0000aaee0000aaaa0000eeee000088880000cccc00003333ffffcccc00003300000033cc00000f0ffffff0f000000f0f00000c0c00000f0c00000f0c00000f0a00000f0a00000e0e00000e0e00000c0ccccccccc00000c0c00000c0c000000ffffffff00000000ff000000cc000000ff000000aa000000ff00000000000000fa000000fa000000ee000000ee000000cccccccccc000000cc000000cc0000000f000000000000000c0000000c00000000ffffffcc00000000ffffffaa00000000ffffff0000000000fffefffe00000000fffafffa00000000ffeeffee00000000ffccffcc00000000ffaaffaa00000000ff0cff0c00000000ff00ffcc00000000fefefefe00000000fafafefe00000000fafafafa00000000eeeeeeee00000000cccccccc00000000cccccc0000000000cc88cc8800000000c8c8c8c800000000aeaeaeae00000000aaaaeeee000000004c4c4c4c00000000332233220000000032323232000000000f0f0f00000000000f0c0f0c000000000f0a0f0a000000000e0e0e0e000000000c0c0c0c0000000004040404000000000000ffcc000000000000ffaa000000000000fafa000000000000eeee000000000000cccc0000000000000c0c00000000000000cc

def masks : List W := [0x5555555555555555,0x3333333333333333,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff,0xffff0000ffff,0xffffffff]

def ds : Debts := [(0x5555555555555555,7),(0x3333333333333333,6),(0xf0f0f0f0f0f0f0f,7),(0xff00ff00ff00ff,7),(0xffff0000ffff,7),(0xffffffff,6)]

def syms : Array Sym := #[([],[]),([0x8,0xff000000ff00,0xff000000ff0000],[0x8,0xff000000ff00,0xff000000ff0000]),([0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x8,0xff000000ff00,0xff000000ff0000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x8,0xff000000ff00,0xff000000ff0000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0xc,0xf0f00000f0f0,0xf0f00000f0f0000,0x1e,0xcccccccc,0x3333333300000000,0x7,0xaa00aa00aa00aa,0x5500550055005500],[0xc,0xf0f00000f0f0,0xf0f00000f0f0000,0x1e,0xcccccccc,0x3333333300000000,0x7,0xaa00aa00aa00aa,0x5500550055005500]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x1e,0xcccccccc,0x3333333300000000,0xf,0xaaaa0000aaaa,0x5555000055550000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0xc,0xf0f00000f0f0,0xf0f00000f0f0000,0x1e,0xcccccccc,0x3333333300000000,0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0xc,0xf0f00000f0f0,0xf0f00000f0f0000,0x1e,0xcccccccc,0x3333333300000000,0x7,0xaa00aa00aa00aa,0x5500550055005500,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x1e,0xcccccccc,0x3333333300000000,0xf,0xaaaa0000aaaa,0x5555000055550000,0x3,0xa0a0a0a0a0a0a0a,0x5050505050505050]),([0x4,0xf000f000f000f0,0xf000f000f000f00,0x1e,0xcccccccc,0x3333333300000000,0xf,0xaaaa0000aaaa,0x5555000055550000],[0x4,0xf000f000f000f0,0xf000f000f000f00,0x1e,0xcccccccc,0x3333333300000000,0xf,0xaaaa0000aaaa,0x5555000055550000])]

def book : ℕ := 0xa1d479b4e73b54a99ce7a28ea9394a538e79294aa04818b0210b0848842185200842108320c84210a10247b08423021790841184698a621084299a66a08429b4421344d988421244990a421084292649a0842938421384e90842a0ca38b0631b0a588c63a50638320c84210852039b44d839ad6b842835ad9384e835ce73442839ce8b06c8318c630638318ca14657b0a52b063794a58318c7958c615857b18ca5282a5294a5294a529484a10842108421084210826028421083a02842109ce739ce739ce099ce7382602842108420284210842108421084e02842109cc4210842108429cc4290a4294a5294a4694a520842188e2308c238862139c47834e73b44281ce799846818c631842818c689c67820e73a06381ce7994657aca52ac63794a521084795e521485791e4820e879508414e57a1080b02c88621084218b22c7a1e37bdef7bde37bdef7c9f27bdef7bdef7bdef9cc6310842108639cc4294863108421086394842318c631cc731cc7318c67c5f17bdef7bdef7bdef9ce739ce739d26a9ce73a5294a514aa528ea5294a5294a514aa516ba5294a5294a514aa528ca5294a5294a516ba514aa52949ce739ce739ce8d9ce73a4a94a5294a5294a52949cc42108c6108429ccc6948421092910842949298c4210858c084218c58c39c4781ce739c4281ce799c47828e73a84281ce79284a81d4a51c428294a89c6781ce739c6381ce77c1e77bdef7bdef7bdef85214842108421084210a5294a5021a50a5a52940c42108421084210c4217bdef7bdef7bce77bdef81e038421083203842107bdef7bdef7bc217bdef318cc318c6318ce318c699a669ce739ce6a9ce7318ca31b0631b0a518c635284a5314a530425294a4a4494b5294b4424a529294652b0a52b063294a598ca38a8631a8a588c637bdef7c2107bdef7bdef7c5e17bdef7bde17bdef108c292442124c69084290ca389c6319ca588c63914657a0a52a063794a5832028421083a0284210832028421083602842107bdef7bdef7d0637bdef8c6318c2108c6318c6318c6318c5e08c4218c63198e639ce739b66d9ce739ce739cc639ccc69ce739ce739cc639cd089ce7381e028421083a028421084e138421084e0384210826028421081e028421081e038421082e0384210295452b4a52b54a294a5294e52b8a52b8e7294a582205842108320584210822028421082e028421082e028421082202842108421084105842058421084e02842108420284210089410b4210b54a08821098210b0210b02c0982131846338c633842318c614c42109ad1084214dad94a52949ce9484294a529529494a5294a5294a526318c6318f6318c6318c81a038421084203842107d0637bdef7bdef7bdef7c1f07bdef7c1ef7bdef108421085210842108429ce6a9ce739ce6a9ce739ce739ce2a9ce6a9ce739ce739ce099ce699ce739ce739cdeb9ce6b9ce7323ca521084210a523c8494a5294a0694a5294a5294a5294a109484294a52084818b0210b0848842108441830210b0428042188461810210906380421210247b08423021790848102479484214217908488c63194211946388c239ce7394a5294a5294a52794a528c8328ca57948510842116651144510a62295652b4a52b56b294a510842116451144510a42295052b8a52b908294a58d2248c6318c6318c631318c6320c8320c8318c6420a843108430a542108891e48c6318c6318c631a09629b4421356b98842a09029384213908908428d2248c6318b2248c631a20484310843042a210899846324c632442998c6924494992949842925299ce739ce529ccc69ce736320c6318c6318c6318c81a058421081e058421018d43194631954518c632956528ca528d63294a58c6248c6318b2248c6317bde17bdef7b1e17bdef7b1e37bdef7b9e37bdef7c5f17bdef7c5ef7bdef6318f6318c6318c6318c1084c108421084e10842085610b0210b16b0842139c673b0e73b06339ce77ade17bdef7b1e17bdef7ade37bdef7b5e37bdef7b1e17bdef7ade17bdef294a8294a5294a8294a518c6318c6a18c6a18c635294e5294a5294a5294e4210d42108421084210d10843108421084a108421084810842108421084294a52949299486394a527a1e17bdef7b5e17bdef7b5e17bdef7a1e17bdef18c6a18c6318c6318c6a084210842108426084234210f42108421084210818c6318c6318c6318c72421084210f421084210842108421094210a4210810848108421084d1084294a4894a5294a5294a521048213042130841044294a529486394a4794a525ac4b5b16b5b0425ad6b7a1e87bdef7b1ec7bdef7a1e37bdef7b9e37bdef7b1e17bdef7a1e17bdef7a1e77bdef7bde77bdef93def94a5294a5294a5242108421084210842110996659ce739b66d9ce739ce739cca59ccc69ce738ce338c6318ce258c631822028421083a028421084e138421084e0584210826028421082202842109ce739cca59cce79ce738421084105841458421018c6318c631c60318c6383e1084210842108421018c6318c6a18c6318c6a4210842109421084210894a5294a4f94a5294a5290e4394a5293a4e94a5290e4394a529264994a5294a52948639496b94a52826028421083202842108320284210826028421084a128421084a03842107ca527bdef7bdef7bdef94a5293def94a5294a5218c8318c6318c8418c6329425294a529421294a518ce319463194e518c632950528ca528d03294a58aa248c6318ba248c6318c6258c6318aa258c6318aa258c6318c6258c631420a841d0841ca5421088c6318c5488c6288c6317ade17bdef7b9e17bdef7c5f17bdef7c5ea7bdef81a0284210836028421084a128421084a068421084202842108420284210108421084214a021084210842134421344d1084210842138421384e1084231846330c633042318c6084420842108442084210842108e2308c2308621318cc318c6318c6318c64a52c4a5294a5294a5299ce729ce739ce739ce7310844108421084b1084298a629ce739b66d9ce73886218c6318ba2e8c6318ce338c6318ce2a8c631791e17bdef7b9e17bdef18c6318c631cc6318c638bdef8c6318c6318c6310842108442084210844214c63108421086314c4290e4394a5294a4794a5290e4394a5292a4a94a5210a42108421084210842886218c6318b62d8c631324c9318c6318c6324c994a529494a9486394a52791e17bdef7b5e17bdef6318c631906318c6318c4a5294a52a4a52a4a52908426084210842d0842108429084210842e084219264994a5293a4e94a52098410b0210b042098219ca529ce739ce739ce73318c63198c318c63198ca5281a5294a5294a52949ce739ce739ce939ce7394a5294a5294a9294a52a528ca5294a528ca5294a3e8ca5294a528ca5294318c6318d0318c6318c68420384210842038421084e0384210842038421084a038421084203842107c6317bdef7bdef7bdef842078421084210842108c6318bdef8c6318c6317384273a0e7384e73a0e94a529492994a5294a5299a669ce7398a629ce735294a5094a509425294aa0a82a5294a5294a5294a0a82a5294a1685a5294a428ca5294a0a82a5294a0a82a5294a0e83a52944a52e4a5294a52e4a52984214842108421084210318c6318cd318cd318c6421084210d4210d4210818c7218c6318c6318c634210d421084210d421085294a5294a5294a52954529545294a5294a5294a4211042108421084210884210842148421084210109429b4421354a98842108e293842138e790842988c292442124c69084281e028421084202842108461184210846038421014c42108a51084214ca514842108a510842148a57bdef7bdef7c4217bdef7c2107bdef7bdef7bdef7bde17bdef7bde17bdef7cde37bdef7bde37bdef7c9e37bdef7bde37bdef7c1f07bdef7c1e77bdef94a529ce7394a5294a5218ca38a8631a8a588c6389c673a0e73a06389ce7294657aca52ac63794a58b02c7918c610217b18c420e879508414e57a108a5294a5042a528da529485214842108520284210a4e8da5294a528da5294a4a8ea5294a528ea5294a468ca5294a528ca52947bdef7bdef7c28c7bdef7d1f47bdef7d1ec7bdef0c46308421084630c4216304c6352c634426312c21084215e521485211e49d2749ce739d26a9ce739ce739cc429ccc69ce73a5294a5021a516ba5294a5294a5021a5063a52947bdef7bdef7cc637bdef148631084210863148420c421085ce084210c5ce318e7318c6318e7318c67cdf37bdef7cde37bdef7b1e37bdef7b5e37bdef7b1e17bdef7bde17bdef7b1e77bdef7bde77bdef5294a5294b5294a5294b294a5294ab294aa294a5294af294a5294a5294a5294a5294af294a5294a5294a5294a6294a7294a5294a5294a9294aa294a54a5294a52e4a52e4a52939ce939ce739cee39ce739ce739ced39ce739ced39cea39ce739ce739cea294a5294ab294a5294ab4a5294a5294a5294a53082609842108320c8421084e138421084e098421082602842108360284210108421084214e021084284a028421084202842108460384210842038421083e0584210842058421021087210842108421084294a5294b0294a5294af42168435084356b421085ad0b5b96b5b9085ad6b084810b22c0b08c0862121c84230842308c21c84795e57bdef7b1ec7bdef0c4210858c084210c58c7bdef7bd8c7bca57bdef1184610a621084211a661244910a42108421264908421086210842108621084a10b0210b0a50842139c6739ce739c6339ce7795e17bdef7b1e17bdef795e37bdef7b9e37bdef795e37bdef7b5e37bdef7b1e17bdef795e17bdef7b1ec7bdef795e57bdef4a5294a5304a5294a5294a5294a52e4a5294a52994e4694a529264694a52826098421084203842109520294a5294a5294a5284e10842108421084210846108421084210842108420684210842108421084210841f08421084210318c7318c6318ca318c69ce739ce709ce739ce739ce739ce409ccc69ce7339c473b8e73b84239ce74a44949d2949c424a52939c673ace73ac6339ce7795e17bdef7b9e17bdef7cdf37bdef7cdeb7bdef7b9e17bdef795e17bdef7adeb7bdef795e57bdef108421084214c42108420c4210854a084210c54a7ce737bdef7bdef7bdef0842108484084210848414c42108421084214c4290a4294a5294a4794a5290a4294a5292a4a94a524a6494a5294a5294a5290b02c08621084210b22c31846328c632842318c694a529494a9484294a52795e17bdef7b5e17bdef211e42108421084210847b5e17bdef795e17bdef7a1e87bdef795e57bdef10853108421084e1084294a4794a5294a5294a5298a629ce739ce6a9ce7394e5394a5294e4994a5239d073b0e73b10839ce79ce739ce609cc429ce73420e843108430e742108318c6318c634cc6318c69ce739d2949ce739ce730c4e708421084e70c421318c631929318c63192923d08210842110823c8414c42108c61084214cc614842109291084214929886218c6318c6248c6316322c6318c6318c6318c39c4739ce739c4239ce739c473a8e73a84239ce75284a51d4a51c425294a791e17bdef7bde17bdef631ec6318c6318c6318c6318c6318c6318c63190739d2739ce739ce739ce528ea5394a538e75294a250242308423021250846302c6318c630216318c795e17bdef7bde17bdef795e37bdef7bde37bdef7c5e17bdef795e17bdef108421084210a021084281e028421082a028421082a028421081e028421081e0384210842038421031a06318c6318c6318c67bdef7be107be057bdef1084211842118461084239ce7388e7388e239ce794e4694a5293a4694a5218c631b20c1b06318e0394a52949cd94a4d94a5298a629ce7399a669ce739ce739cc429cca59ce739ce739ccc69cc429ce739ce739cc429cc639ce73086810842108421084216b5ad6b5ad6ce8d6b5ad94a5294a9494a8794a52a1e87a5294a2288a5294a1e87a5294a528ca5294a2288a5294a1e87a52947bdf17bdef7bdef7bdef18c6318c7018c6318c63294a5294a5294a5294af294b0294a5294a5294a59ce6a9ce739b66a9ce7394a4794a5293a4794a5294e5394a5294e4d94a5239d073a8e73a90839ce75296a51d4a51d675294a9ce739cdaa9ce6a9ce7394a52949c794a4794a5239ce73a4e73a4e939ce75294a5194a519465294a9ce739cda99ce699ce7394a52949c694a4694a52420e842d0842ce7421085ad4b5a16b5a1485ad6b9ce739cdab9ce6b9ce7394a52949c894a4894a52150421360d13442108425514a5354d5354a5514a10842124421244910842109ad10a42109a210a426b5ad68dad68da36b5ad10842126091244210a024a4494a5294a4424a5295286a52d4a52c635294a5ad4b5b16b5b14a5ad6b6b5ad695ad695a56b5ad7d2947bdef7bdef7bdef5d16b5b56d5b56b5d16b18ce31a4631a4e718c635294a5394a5394e5294a109a210e4310da310a4218c631a8631a86a18c635296a5314a5316b5294a6b5ad685ad685a16b5ad39c673a4e73a46339ce75294a5314a5314c5294a6b5ad69dad69da76b5ad7bde37bdef7ade37bdef7adea7bdef7b9ea7bdef7ade37bdef7bde37bdef7b9e17bdef7ade17bdef7ade77bdef7bde77bdef94a5294a4094a5294a5280200842108320c84210802008421081204842108421084000840218421094a5294a52934e794a52808428421084210842108c6318c6318c6288c631a5294a5042a516ba5294a5294a5042a5108a52948b2258c6318ba258c6318b2258c6318b6258c631a5294a5084a5042a52948c6318c5888c6288c6318d2948c6318c6318c631a4631a5294a5294a52948c6318c631895e58c631739c0739ce739ce739ce7bdf47bdef7bdef7bdef18c6318c6318c6318c7194a5494a5294a5294a52318c6318c6318c6318d094a5294a5294a4c94a520000000000000060000339ce739ce439ce739ce7108e213842138e710842791e47bdef7a1e87bdefa5294a5042a50a5a5294a5294a50e7a5042a5294a5294a5042a5063a52942108421084210842108f084230842108421084210000000000000030000c10852108421084210842000000000c0000000000084210842d0842d0842194a5294a4c94a5294a52108421084d1084d10842000000000c0000c000006b5ad6b5ad6b5ad6b5a10001200000000000000094a4d94a5294a5294a52294a5294a5294a5294a14210842100421084210808422084210842d0842110842108501084210852000000000000004000118c6318c6318c6258c6316318c631836318c6318c6318c6318c631946318c00000000020000200000631826318c6318c6318c210912108421084210845294a529435294a5294a631916318c6318c6318c5294a529445294a5294a210842108d2108d210846b5ad6b5a36b5ad6b5ad108421084410842108448c6318c6208c6318c631084220842108425084219ce739ce6e9ce739ce73084280842108428084218c6238c6318c6318c6317bdef7bde57bdef7bdef318c6318c8318c8318c621085210842108421084084230842c08421084210842d084210842d08421318cd318c6318cd318c694a4c94a5294a5294a527bdef7bdef7bded7bdef6b5a16b5ad6b5ad6b5ad9ce649ce739ce739ce7394a5294a4494a5294a52318c6318c6318cd318c984210842048421084210739c6739ce739ce739ce210842108421086210847bdef7bdef7bde47bdef108431084210842108422108d210842108d2108494a5294a4594a5294a520000000000000010000200000000000000100006084210842c084210843194a4f94a5294a5294a5210853108451084210842084310842108423084217bde97bdef7bdef7bdef084210842308421084230842208424084210842194a4594a5294a5294a5210942134421354a10842886218c6318b22c8c63181a0284210832028421081a0284210826028421084a128421084a0284210846118421084608842107c1f07bdef7c1e57bdef10842108421084310845a5294a5084a50a5a5294a5294a5084a50e7a529410844108421084410842000000000000003000020842108421084220842410842108421084310853294a5294a2294a5294a56b5ad6b5ad6b5a76b5ad94a4394a5294a5294a529ce639ce739ce739ce737bdef7bde77bdef7bdef7bde77bdef7bdef7bdef08431084210842108421210842108f210842108410842108431084210843918c694a5294a5294a5218c6318c6318c6918c636b5ad6b5a26b5ad6b5ad18c6318c6318c6818c636b5ad6b5ad6b5ae6b5ad739ce739ce739cd739ce7bdef7bc847bca57bdef084210842108422084348420284210832028421084e138421084e0e8421084a128421084a0d8421083203842108420384210842108418584205842107bdef7be527be437bdef39ce739cec39ce739ce7a5294a5042a514aa5294a5294a5042a528ea52948d2348c6318d2258c631a5294a514aa5042a52947d1f47bdef7d1e37bdef8c6318c6288c6318c6318c6318c62b8c6318c6318c62c8c6318c6318c631084210842c0842c08421084210842108422084299ce6b9ce739ce739ce737bde37bdef7bdef7bdef8c6258c6318c6318c631318c6318c8318c6318c618c6318c6618c6318c6618c6318c6918c6318c691084210842108431084618c6318c6318c6318c642108421084210882108c318c6318c3318c6318c608423084220842108421000000000100003000000000400000000010000010842108431084510842084340842108427084210842108421084210842208421084210842308422318c6318c7318c6318c60842108421084210843408421084220842108434108431084610842108429ce669ce739ce739ce73000000000100001000006318c6318d6318d6318c21084210842108c210887bdef7bde37bdef7bdef8c6318c6258c6318c63110853108461084210842108521084910842108421084a108421084a108421084210842108431084d1084210842108431084e94a5294a4294a5294a5294a5294e7394a5294a529ce739ce739a4c69ce73a5294a50e7a5108a5294a5294a50e7a528ca5294a5294a5108a50e7a529408434084210842208421084210842d084210842d00000000070000700000084220842108421084220000000000000020000c94a5294a5294a4694a526b5ad6b5ad6b5a56b5ad18c6318c7018c6318c701084910842108421084e8420c8421084210842104a5294a5294a5334a52910842108501084210842108e210842108e71084239c473b4e73b44239ce794a529421094a5294a525284a5394a538425294a94e7394a5294a5294a5208421084210842208426084210842108427084226b5a36b5ad6b5ad6b5ad631846318c6318c6318c94a5294a4694a5294a5200000000000000d0000000012000000000c000000000d000000000d00000108481084210848108421084b108421084b108427bdef7bdef7bde87bdef2108521084210842108f084240842108424084216b5ad6b5ad6b5a46b5ad5294a529425294a5294a5294a529495294a5294a5ad6b5ad695ad6b5ad6b84210842108420284210a5294a5294a5283a52948c6318c6268c6318c631318cc318c6318cc318c6318cc318c6318c6318cc7bdef7bdef7bdef7bdef842108420c842108421084204842108421084210a5294a5294a5282a52945294a529475294a5294aa5286a5294a5294a52941084c1084210842108525ad6b5ad685ad6b5ad6b7bdef7bde27bdef7bdef39d47388e73894239ce794a5294842948a594a526b44d6b1ad6b0426b5ad6306c6318c630636318c94a52948429486394a526318c6158c615856318c94a5294a5294a5294a5294a5294a4794a5294a521084210842108421085239cf439ce739ce739ce71085310842108421084294a5294a4894a5294a520842d08421084210842d39ce739ce739ce739cf439cf039ce739ce739ce71084c108421084c108420842108421084210843110842108421084210853318c6318c6318cc318c85294a5294a5294c5294a0842e08421084210842e294a5294a5294a9294a5000000000000005000060842c084210842c084212108c210842108c2108494a5294a5294a4394a52a5285a5294a5294a5294739c2739ce739ce739ce39ce739ce839ce739ce8294a5294a8294a7294a5842108420184210842108421084202842108421039cee39ce739ce739ce71084510842108421084510847108421084710842210842108621087210842108421089210882108421084210882108421084318c4318c6318c6318c694a5294a5294a4194a524a52a4a5294a52a4a52939ce739ce739cea39ce739ce739cef39ce739ce7a5294a5281a5294a52948c6318c6248c6318c6319ce739ce739ce629ce738c6218c6318c6318c6310842108421084210842c318c6318cc318c8318c67bdef7bde87bdef7bdef294b1294a5294a5294b12108421084210852108f39cef39ce739ce739ce76b5ad6b5ad6b5ad6b5aa6b5ad6b5a16b5ad6b5ad6b5ad6b5a46b5ad6b5ad08425084210842508421108451084210845108428c6228c6318c6318c63139ce739ce739ceb39ce76b5ad6b5aa6b5ad6b5ad6b5ad6b5a96b5ad6b5ad842108421084203842107bdef7bdef7bde77bdef00000000000000a00000084210842108429084214a5294a5224a5294a5294a5294a5214a5294a5294a5294a5244a5294a52900000000000000200009084210842208421084227bdef7bdef7bde67bdef0000000006000060000094a5294a5294a4294a5208421084210842a084229024094a5293a4e94a52084410b0210b042084210846109021090630842194a52948009482194a52210242148421421210841084213421134421082218c63194211946318c23294a528c8328ca52948588e238c6318b22c8c63188e238c6318ba2e8c63188e238c6318b62d8c631420484310843042421088c6318c58c8c4638c631791e37bdef7b1e37bdef7c5f17bdef7c5e37bdef108421084d1084210842a5294a5289a5294a5294108421084a1084210842318c6318c6318ce318c6a5294a5284a5294a52942108c21084210842108c2108a210842108a21084886218c63189e278c6317d1f47bdef7d1e17bdef0842c084210842108431318c6318c7318c7318c618c6318c6f18c6318c6339d473b4e73b54a39ce794a4694a529264694a52826098421083a0e8421084e0284210826028421084a128421084a1084210826038421082e038421084210841258414584210a5294a5021a514aa52948d2348c6318d2248c631886218c6318aa2a8c631a5294a5021a5042a52948c6318c4218c4638c631a5294a5042a5021a52948c6318c58c8c4218c6319525494a529524794a528c6318c6528c6458c6319264994a5290a4294a5290a4294a5290e4394a527bdef7bde67bdef7bdefa5294a5084a514aa5294a5294a5084a5108a5294a5294a514aa5084a5294a5294a5084a5285a529439c673a0e73a06339ce77d1f47bdef7d1ea7bdef791e37bdef7ade37bdef791e37bdef7a1e37bdef7b9e17bdef791e17bdef8c6318c6218c6318c631108421084810842108488c6318c6298c6318c6310000000000000010000c084210842708421084277bdec7bdef7bdef7bdef210842108421085210888c6318c6228c6318c6317bdef7bdef7bde17bdef318c6318c8318c6318c8084210842b084210842b7bdef7bdef7bde27bdef9ce739ce6c9ce739ce730000200000000020000039ce739ce739ce739cf17bdf27bdef7bdef7bdef21084210842108e21084108421084d108421084d108421084e108421084e2108421084210852108c10842108421084310849000000000000009000020000000000000090000621084210842108b210859024094a529324c94a5294a52948009488494a522104423084230422108439c67390e73906339ce7791e17bdef7b1e17bdef7c9f27bdef7c9e37bdef7b1e17bdef791e17bdef1084213484134421088294a52948009484294a5218c63195451946318d43318c630800308c6318067bdef7bc837bca37bdef0842c08421084210842c294a6294a5294a5294a51084210845108451084290a4294a5293a4e94a5290a4294a529264994a5289e248c6318b2248c63189e258c6318ba258c6318ca328c6318ca258c63139c473b0e73b04239ce794a52949299484294a528c6318c4e78c6288c631791e47bdef7b1ec7bdef791e47bdef7adeb7bdef7c9f27bdef7c9e87bdef7c5f17bdef7c5e47bdef791e47bdef795e57bdef108421084710842108429ce739ce649ce739ce730842108428084210842118c6318c6318c6318c6618c6318c6318c6318c6b1084e108421084e108427bdef7bdef7bdec7bdef210842108c2108c21084294a5294a0294a5294a52108f2108421084210849ce739ce619ce739ce739ce739ce699ce739ce73108421084510842108452108c2108421084210847bdef7bdef7bde37bdef084210842e084210842e318c6318c9318c6318c9318c6318c6318c6318d394a5294a5294a4794a5239ce739ce739ce739cee084230842108423084212108521084210852108400000000000000c0000100000000000000c00007318c6318c6318c7318cc210842108c210842108c10842108461084210846882208c6318a6298c631882208c63189a268c6318c6318c4008c4638c6317c5f17bdef7c5e17bdef781e07bdef795e57bdef10842128c612842108c21084211d2711c42109228c6318c4008c4218c63139ce738800388e739c077bdef7bc007bc847bdef318d3318c6318c6318c64a5324a5294a5294a5290842208421084210842110842108421084210846084210842708427084212108421088210882108499a669ce739b66d9ce739264794a5293a4794a5294e5394a5294e4694a529ce739ccc69cd089ce7394a52949279496794a5239ce73b0e73b0ec39ce79ce739ccc69ce699ce7394a529492694a4694a5239ce73a0e73a0e839ce79ce739ccc69cce79ce7394a52949289494894a52420e842108420e742108318c6318c6318cb318c69ce739ce6a9ce739ce739ce739ce6b9ce739ce7339ce739ce739ce739ce908421084210842d0842108421084210842e0842194a4294a5294a5294a529ce629ce739ce739ce7308427084210842708421318c6318cc318c6318cc21088210842108821084318c6318ca318c6318c66318c631826318c6318c10846108421084210846108491084210842108496318c6318c631896318c000000000000001000046318c6318c631906318c318c6318c6318c8318c7084210842f084210842f1084210842108431084f39ce939ce739ce739ce7421044210842108421080000000000000030000118c6318c6318c6318c6c18c6318c6318c6e18c6318c6318c6318c6c18c63000000000000006000029ce739ce669ce739ce73084210842108422084271084210842108531084218c6c18c6318c6318c6308421084210842608422108421084910842108496318c6318e6318c6318c5ad6b5ad6b5ad675ad6b294ac294a5294a5294a539ce739cea39ce739ce7294a5294ac294a5294a5294a5294ae294a5294a5084210842408421084240000100000000010000010842108461084610842421084210e4210842108108461084210846108426318c6318c6318c63191318c6318c6318c8318d1318c9318c6318c6318c98c6248c6318c6318c63142108421084210c421087bdf07bdef7bdef7bdef7bdf37bdef7bdef7bdef6318c6318a6318c6318c6318c631866318c6318c0000000000000040000100000000000000c0000439cec39ce739ce739ce7318c6318c6318c7318c80842108421084220843318c6618c6318c6318c635ad6b5ad625ad6b5ad6b421054210842108421080842108421084220842a39cf239ce739ce739ce70000000000000020000694a5394a5294a5294a525294a5294a5294d5294a9ce739ce629ce739ce735294a5294a5294a5294a9ce739ce6d9ce739ce736318c631816318c6318c6318c631896318c6318c6318c631846318c6318c000000000000004000072108421091210842108439ce739ce539ce739ce77bde67bdef7bdef7bdef1084d108421084d1084210842108491084910842084210842a0842a08421318c6318c9318c9318c66b5ad6b5ad6b5a96b5ad210842108b2108b210846318c6318c6318b6318c0842a084210842a0842108421084230842308421210842108521085210849d2949ce739ce739ce73a5294a5021a50e7a5294a5294a5021a5084a5294852148421085203842109ce739c2109ce739ce73826028421081a028421081a03842108220384210a5294a5084a5021a529484210840c5840e584210108421084c108421084208422084210842208421210842108c210842108610842108421084210849318c6318d2318c6318d2108421084a108421084a10842108471084210847631876318c6318c6318c318c6318cd318c6318c6631946318c6318c6318c10962134421356b1084210902138421390810842150421304c13042150426b44d6b9ad6b8426b5ad7384e735ce73442739ce420484210842042421084204842d0842c42421085ac4b5a16b5a0425ad6b8c6318c6318c6318c631889e28c6318c6318c631789e27bdef7adeb7bdef789e27bdef7a1e87bdef7b1ec7bdef789e27bdef791e47bdef789e27bdef294a5294a1294a5294a5084210842c08421084210842108423084210842118d431b4631b54a18c635286a5394a538635294a14c42124491244214c4218ca31a8631a8a518c635296a50d4a50d635294a90a0294a5294a5294a5280a028421084210842100020000000000000000080a02842108160584210294652aca52ac63294a55ad4b5956b595455ad6b84210840428406384210210842108c2108421094842018421084210842108420284210842108421018c6318c6e18c6318c63739ce739ce739c2739ce739ce739ce739c5739ce39ce739cee39ce739ce700000000000000600013108421085010842108507bde17bdef7bdef7bdef210842108c210842108418c6318c6c18c6318c634210c421084210842108294a5294a5294a1294a5318c6318c2318c6318c639ce739ce839ce739ce7318c6318c9318c6318c6421084210742108421085ad625ad6b5ad6b5ad6b421084210242108421086318c6318c6318d631925294a5294a529475294a6318c6318c631866318c210842108421086210852108421084210852108b421084210842101421081084210844108421084818c6318c6318c6318c63084210842a084210842a6b5aa6b5ad6b5ad6b5ad4a5294a5294a52c4a5292108421081210842108439ce539ce739ce739ce71084210842108431084c10842108431084310842739ce739ce739ce739ce4210342108421084210894a4494a5294a5294a525ad6b5ad6d5ad6b5ad6b1084c108421084210842294a5294a3294a5294a57bde27bdef7bdef7bdef18c6318c6718c6318c6318c6318c6b18c6318c63739ce739ce739ca739ce421084210a42108421085ad6b5ad6b5ad6b5ad6b18c6318c6818c6318c63739ce739ce739c4739ce108461084210842108426318c6318c631886318c84210842108421084210318c6318c6318c6318c0318c6318c6318c6318cc4a5294a5294a5284a52918c6318c6318c6318c6100000000000000800000294a5294a4294a5294a5294a5294a5294a5294a54a5294a5294a5214a529108421084510842108426b5ad6b5ad6b5a36b5ad18c6318c6318c6718c6318c6518c6318c6318c6318c6318c6518c6318c63294a5294a5294a8294a5739ce739ce739c3739ce42108421084210342108294a5294a5294a6294a55ad6b5ad6b5ad655ad6b318c1318c6318c6318c642108421084210a4210839ce739ce339ce739ce721084210832108421084210842108021084210846318c6318c631856318c9ce699ce739ce739ce731084110842108421084218c6318c6918c6318c639ce739ce739ce669ce734a5294a5294a5274a52908421084210842b084215ad6b5ad6b5ad615ad6b318c6318c6318c1318c618c6318c6218c6318c6339ce739ce639ce739ce7421084210642108421086b5ad6b5ad6b5ad6b5ad18c6318c6318c6218c63294a5294a5294a2294a539ce739ce739cec39ce76318c6318c631876318c6318c6318c6318a6318c294a5294a5294aa294a539ce739ce239ce739ce7739ce739ce739c7739ce318c9318c6318c6318c6739ce739ce739c8739ce00000000000000e000006318c631806318c6318c318c6318d2318c6318c639ce739ce739ce439ce739ce739ce039ce739ce7318c6318c6318c9318c64a5294a5294a52d4a5294a5294a5294a52b4a5294a5294a5294a52a4a52939ce739ce739ce739ce742108421084210b421085ad6b5ad6b5ad685ad6b4210842108421084210818c6318c6318c6618c6318c6318c6418c6318c63084210842a08421084219ce739ce609ce739ce73318c6318c4318c6318c60000000000000020001418c6318c6618c6318c636b5ad6b5ad6b5a26b5ad294a4294a5294a5294a5000000000000006000126318c6318c6318e6318c6318c6318c6318d6318c210842108421082210846b5ad6b5ad6b5a16b5ad294a5294a6294a5294a5294a5294a9294a5294a5294a7294a5294a5294a5084210842c084210842c0842108424084210842108421084250842108421631806318c6318c6318c000000000000002000134a5294a5294a5294a5290000000000000020001239ce739ce739ce339ce7318c6318c6318c4318c6318c6318c1318c6318c610842108401084210842318c6318c0318c6318c68c6208c6318c6318c63139ce739ce139ce739ce7318c6318cc318c6318c6421084210442108421085294a5294a529425294a084210842608421084210842108427084210842108421084200842108421a5294a5294a5294a529408421084220842108421108401084210842108425294a5294d5294a5294a108421084210849108424a5294a5294a52e4a52918c6318c6318c6a18c635294a5294a5294b5294a294a5294a5294ab294a55ad6b5ad6b5ad6a5ad6b9ce739ce739ce739ce73108c212442124c610842a0280a5294a2689a5294a0280a5294a1a86a529431846324c632442318c64a44949929498424a5298c6318d0008c6318c631781e07bdef7a5e97bdef781e07bdef799e67bdef7d1f47bdef7d1ef7bdef781e07bdef789e27bdef7bde07bdef7bdef7bdef084210842f084210842110843108421084310842318c7318c6318c7318c639c673b4e73b46339ce718ce31b8631b8e718c63108c610a42108c21084239d0738ce738d0339ce718ca319c6319ca518c63420e841508414e542108294652a0a52a063294a500000000000000500000210842108221084210842108421085210842108421084210842108b210840000000000000040001421084210842108c210848c6268c6318c6318c6316b5a26b5ad6b5ad6b5ad10842108421084c108420000000000000070000018c6318c6118c6318c6318c6318c6018c6318c6310842108461084210842318c6318c6318ca318c6108421084910842108425294a529465294a5294a39ce739ce939ce739ce794a4694a5294a5294a524a5294a5294a5234a52939ce039ce739ce739ce71084210842108441084218c6318c6318c6418c635294a5294a529435294a210842108421083210844a5294a5294a5244a5294210242108421084210810842108421084e108425ad6b5ad6b5ad635ad6b10842108421084a108425294a5294a529445294a4210842108421054210821084210842108a21084739ce739ce739c1739ce10842108421084b1084239ce739ce739ce239ce739ce239ce739ce739ce7108421084410842108425ad6b5ad6b5ad625ad6b318c6318c6318c6318c6294a5294a5294a7294a539ce739ce739ce539ce7294a5294a7294a5294a5294a5294aa294a5294a55294a5294a529455294a94a4194a5294a5294a52318c6318c6318c5318c64a5294a5294a5254a5294a5294a5294a5264a5294210842108421024210818c6818c6318c6318c631084210842108481084218c6318c6a18c6318c635294a5294a529485294a6318c6318c631836318c6318c6318c631846318c08421084210842c08421084210842108426084216318c6318c631826318c10842108421084110842318c6318c6318c3318c61084210842108471084218c6318c6318c6518c63294a5294a5294a3294a5084210842108422084211084410842108421084208421084210842a0842108421084210842808421210842108421087210840000000000000010000f318c6318c6318cc318c639ce739ce739ce839ce74210842108421074210810842108421084d1084210842108421084510842318c6318c6318cd318c6318c6318c6318c8318c621084210842108821084318c6318c6318c7318c6084210b0210b02c08421084810b0210b084084210848108421084840842121024230842302121084210242108421021210846302c6118c610216318c000000000000003000001084210841108421084210842108431084210842000000000000002000000842108421084270842194a4094a5294a5294a52084210842108423084210842108421084250842121084210842108521084108421084210843108420000000000000090000000000000000000600000108421084210842108426318c6318c6318c6318c084210842108421084212108421084210842108400000000000000c00000000000000000004000000000000000000010000008421084210842408421210842108421081210846318c6318c631816318c10842108421084610842318c6318c6318c2318c64a5294a5294a5224a52900000000000000000000

def ck (p c : Catalogue) (k start : ℕ) (hs : List Hint) : Bool :=
  auditRows (checkEntry y neg dict masks syms book p k) c start hs

def c0 : Catalogue := (0,1,0x0,0x0)

def c1 : Catalogue := (0,1,0x0,0x0)

def c2 : Catalogue := (2,29,0x35cb196394594fd,0x12212000211202)

def r2_0 : List Hint := [(0,0xc01001),
  (0,0x1802804)]

def c3 : Catalogue := (6,39,0x338a8a4058d9d414d810d72a4901639c549201ab38b1aa458e7152480b1,0x2332310031132300233131001331320013323100132131)

def r3_0 : List Hint := [(0,0x480601001403804),
  (0x1114800005,0x300a0000140200a),
  (0,0x480601001405804),
  (0x10d4400415,0x601801406004),
  (0,0x180f01c0080080d),
  (0,0x480601001403804)]

def c4 : Catalogue := (16,49,0xb3a82911fa53e718854d202c738b12827e9639c62159480b1ce316aca4058e9976505252c738c3ab2901639350538480b1c9ac8901fa58eb19c549202c738ad2a4901639c56552480b100338a924058e715a480b10db38a7a405888b9c62159480b1,0x332433003433420024342300344242003342420043334300244242004323330043332300244242002442420024424200244242002342420024423200244242)

def r4_0 : List Hint := [(0,0x98150280180981200a04408004),
  (0,0xb00602c0140380402c0580b007),
  (0x20002d,0xc806032014038040300000c017),
  (0x2004178000c5610020ec000437000206c400417,0xf81e03a0700d81a),
  (0,0xa8230000180a82200a08410004),
  (0,0x98250000180982400a04408004),
  (0,0x580e0500541380804209803804),
  (0,0x18120240080081302004014811),
  (0,0x18020020480901302004008829),
  (0,0x160150280181581500a0a810804),
  (0,0x100100604c1702e05a04008004),
  (0,0x190310280c00981205e04408004),
  (0,0x98150280180981200a04408004),
  (0,0x1b01506a0b8170340660cc08020),
  (0x1471,0x981502c0180981200a04408004),
  (0x801415,0x180f01c0080081601e03800016)]

def c5 : Catalogue := (185,59,0x59d414c8fd2c418ce282901fa588a99c59d41480fd28738b7282901fa58e718c505203f4b1ce2ce901fa588ff9c60541480fd2c738b3a82901fa3d67185505203f4b1ce282901fa588d19c59d41480fd2b338a0a407e9622767141480fd2c45ace282901fa588b567505203f4b10df38a0a407e96236671675051f3f4b1ce286901fa588b59c59d41484fd29f38b3a828f9fa58d9d41474fd2c417ce27a901fa588c79c505203f4b11b338b3a82909fa53e713d480fd2c463ce2a0a0a40588b59c505203f4b116f38b3a82901fa5567167505233f4a7ce2cead240731639c504fd2c48416b38a0a407e94e2d671674f5203f4a7ce2ce901fa589039c60141480fd2c738b3a82901fa54e716f505203f4b1ce282901fa588b59c59d3f480fd2c738a0a407e96235e713d480fd2c44ace2ce901fa589019c5fd41480fd2c738a0a407e9622be7167505203f4a2ce282901fa588b99c59d41480fd21b38c4a82901fa58e7141480fd2c45cce2cea0a407e95b67505203f4b10d738c7afcb02927ee7141480fd2c45ace314a0a407e9639c505203b0b116acea0a407e9623ce7167505203f49ace2eaa0a407e96367505203f4e12c742b3a82901fa58e7167505203bcb1d02cea0a407e9639c60941480fd2c738b3a82901fa52e716a505203f4b1ce282901fa5889d6750538480b105acea0a407e9620d61941480fd2c418b3a82991fa5883167505203f4b106738b3a82901e058e7167505203f4a6ce2f8a0a407e9639c59d41480fd2a338b6282901fa58d9d41480fd2c41ace2cea0a407d96376505203f4b108b4cbb282901fa58d9d41480fd2c42ece310ad240588459c59d3c480fd26338b3a407e9623de7184505203f4b1ce30ea0a407e9639d5d941480fd2c738b3ab4901ca58e7576505203f4b1ce288901fa588d19c59d5b480e52c748bb282901fa58e7187511203f4b1ce2ce929fa588f79c64141494fd2c6eca0a407e9620c69967505252c45fce2eca0a407e9319c5d941494fd2c738a0a407e9622767141480fd2c468d12eca0a407e9639c59d41480fd26f38b8a82901fa58e956750520468b1d6322a0a407e9639c59d414d0fd25b38a0a407e9623467167505203f4acce282901fa5889f9c59d41480fd25ecea0a3c7e9620be7140480fd2c463b3a82982407e95967505203f4b11d738aca407e9622ce7167505203f499ce2e8a0a407e9639c59d41480fd27738bc282901fa58e7177505203f4b1ce2cea0a407e95d9c5a541480fd2c738a0a407e96234e7167505203f4afce282901fa588b99c4f9203f4b112b38b7282901fa58e7141480fd2c468ce2e4a0a407e9639c59d41480fd27b38bd282901fa58e716b505203f4b1ce2cea0a407d9639c505203f4b11a338b3a407e96238e7193505203f4b1b3a82901fa58835a559d41480fb2c738c3a82901f658d9d35480fd2c471ce2cea0a667d96367505203f4b108738b3a82901f858e7141480fd2c45ece2cea0a407e9619c505203ecb119b38a0a407e9623467167505203f4acce2cea0a687e92d6750535480b105b4cc6282901fa58e9567505203f4b1d3318a0a408d163a65d9414811a2c7389ea407e9622567167504fd330b1ce2cead240588899c61d41480fd2c738c4282901f658e716750534374b1ce2ae901fa588b59c59d414c8fd29f58a72407e9620f59d414751a3f417b3a829a2607e94fb267188565202c738ad2407c9622d6a167505303f4a7002cea0a607e94fa859d414dcfd2c400ce310aca4058ea167504fd2c474ce2cea0a685382da6671675053429f38ad240588cc22ea167505313f4b1db338c42b490163b26b188569202c738b3a829a1ac58e7191505203f4b1ce318a0a407e9639c59d414d0fd2b764d631eb01fa58ec9a663d414d0b1,0x53344400444344004344440045434300453344004444430044434400434444004444430044433300333444003543330045433300354333005433330044433300333434004453430033354400333544004334340035433300354333004335440035434300254353004444330034344400343544004354430034443400344434003444340044443300444334003434340034433400254433002443340025433400254334004444240044442400344344004344340025434400334444004444330024434400434424005434230025552500254343004543330025434300533424002444440044442400344344003444430024443400344424004543240024444400444424003543430053344400433444005434440053354400343444004444330034434400443434003444240024443400333444004443330055432300554333005443230035534300444444004344440044344400454343005543430044534300544343004543330044434300554343004543430043444400443444005444240044345400444444004444440045434300454333005444430044344400444344003443540054442400433534003443430043343400344334003344340043343400354333004334340053343300354343003434440044433400434434003444430045344300334444004444330034433400334434002543340025433400454333003543430045434300344344004434340045442300344343003543330043443400443434004334340044434300354343004344340034444300334434003443340024443400344424003543330044434300433444004335440043344400543344004443430054334400544344002543440033353400345343003543430035434300333554004453430043354400445333004334350043353400354353003453430043353400433534005335340035435300533533004335440043354400355343004335340035534300455343002345540045342400453334003345340045552300453543)

def r5_0 : List Hint := [(0,0xf41203c0760041203a0720e0008100220e008037),
  (0,0x118228440861082084007e0881f02a0420dc1b811),
  (0,0x130188030960082504907a120238310620ec1a02d),
  (0,0x144108030a00480904f0040040984e02004026811),
  (0,0x14429803084048090020040040985202004026811),
  (0,0xb01880305c0082d0590b01602b8330201582a854),
  (0,0xc40105e0ba0042e0240480c82d8100201001f804),
  (0x8003440000b1,0x2c308600be1742e02404e0c82d81004c1001f804),
  (0x800015,0x48090030261582b063004004088620ac1580504f),
  (0x47d,0x1900301900a01c0203502c090080180180600b861),
  (0,0x281e82509014c018670cc0080082d0ca1301d834),
  (0,0x1a8108030d2008008680980ec1a00d07a12023849),
  (0xc00809,0x1b43680302c008008070200400880b0d81b03580a),
  (0x8021fc20147300041c8000c71,0x3a0730e4078388700381bc3701a),
  (0,0x48090030f01582b013004004088770ec1d805075),
  (0x800c15,0x410811001fc3f07d0f81ec3d079),
  (0xc01415,0x90120030001a810822004004088000d408405011),
  (0x819,0x640301904a0001200500e0100801810606006817),
  (0x201891,0x2c1188a1122200b08710c04c0908510804408004),
  (0xc01815,0xc010010980ec0003d09011c2480f01c0580688b),
  (0,0xc0780e02c0580384b1220b80009011e2384688c),
  (0,0xd40302405c008190330200102001812625049892),
  (0,0x1a81080312a09012011004004110680d40841b811),
  (0,0x1900300806c0580c80500e0100389812e0604b017)]

def r5_1 : List Hint := [(0,0x1301d803004008008590b01604d0560200404c854),
  (0x65,0x4c0a89b00c04c090530000341200502204002010),
  (0x200065,0xb00a80300c0480a85b0042700980502008402011),
  (0x200035,0xb00989d00c048098050200440202500000012010),
  (0xc0044d,0x3c0700302c008008360580540980c0200401009e),
  (0,0x240300802c0580c833032010368a012e27c02017),
  (0,0x8008030260480902614828c020a20200405080a),
  (0,0x298530030260480904f14828c528a20200405080a),
  (0,0xb00a8a900c0ac0a82e15029c0983305408402011),
  (0,0x298530030ae0480904715828c55811020040268aa),
  (0,0xc0780e0240480401002001c1480200203409811),
  (0,0x1301d80315a0080084907a120238650980ec1a02d),
  (0,0x1301d8030b209012062004004560100200401c011),
  (0,0x1900300802c0580c83300e0100382e12e0604b017),
  (0,0x190030080120380400500e0100383515e2604b0ae),
  (0,0x144188030b2090120a6004004110310620ec1b811),
  (0,0x1900306d02c0580c833032010368b012e27c4b017),
  (0,0xb00a8b200c0ac0a81306416c098621622c40202a),
  (0,0xc3686d02c0580c81903201c368b011e23847097),
  (0x2008214801c05,0xb00a8a900c0ac0a80a16a2d023805054084020b3),
  (0,0xb0090060040b8098100660a40880316c04800810),
  (0x2465,0xb00a8a900c0ac0a8880002705c005054084020b7),
  (0x2008154c02005,0xb00a8a900c0ac0a80015029c060050540840200c),
  (0,0xc3686d02c0580c81903201c3689011e23847097)]

def r5_2 : List Hint := [(0,0x1444400310c048090b90040040988402004026811),
  (0,0xb00301205c008098330200100883100604800810),
  (0,0x1900300802c0580c83300e0100382e12e0604b017),
  (0,0xb00a8a900c0ac0a8361740f81100505408402020),
  (0,0x1441880300c048090110040040982a02004002011),
  (0,0x1441080300c048090110040040984e02004002011),
  (0,0xb00a80300c048090a6004004098050ac04002011),
  (0,0xb00a80300c048090320040040980502004002011),
  (0,0x1900300802c0580c83300e0100382e12e0604b017),
  (0,0x14418803048048090020040040981002004002011),
  (0,0x1900300802c0580c833032010368a012e27c5d817),
  (0,0x1900300802c0580c833032010368a012e27c4b017),
  (0,0x130188030b209012062004004560100200401c011),
  (0,0x1900300802c0580c833032010368a012e27c4b017),
  (0,0x1441880300c048090a60040040981002004002011),
  (0,0xb00a80300c0480902e004004158330540ec02011),
  (0,0xb00a80300c048090560040040980502004002011),
  (0,0xb00a80300c048090560040fc0980502008402011),
  (0,0xb00a80300c048090a60040040980502004002011),
  (0,0x14418803178048090400040040982a02004052811),
  (0,0xb00a80300c048090a6004004098050ac04002011),
  (0,0x190030080640580980500e0100889801a2605e8ae),
  (0,0xc3686d02c0580c81002001c0382e05c0b817097),
  (0,0xc2603b0480902c8620c4188560190320400c8a6)]

def r5_3 : List Hint := [(0,0x2fc0300802c0580c83300e0100382e12e0605f017),
  (0,0xc3686d02c0580c81903201c3689011e23847097),
  (0,0x130188030b2090120a60040041102a0540841b811),
  (0,0x1905e0080120580c82a0320103684912e27c4b017),
  (0,0x1301d8030b209012062004004560100200401c011),
  (0,0x1900300802c0580c83300e0100382e12e0604b017),
  (0,0x1301d80315a0080084907a120238650980ec1a02d),
  (0,0xc068c3084048610010043040985202030026811),
  (0,0xb00a8a900c0ac0a80518c3140208c08c3105080a),
  (0,0x14418803048048090020040040982f02004002011),
  (0,0xb00a80300c0480902e0040041583305408402011),
  (0,0x32064003134048090c71622c41582602004002011),
  (0,0x1900300802c0580c83300e0100382e12e0604b017),
  (0,0x190030080120580c80500e0100381812e0604b017),
  (0x2885,0x1441880304e0b8170b6096244098260200400202d),
  (0,0x1441880304e048090280040041582605408402011),
  (0x202825,0x8008030260b81702d0200400200b19403464810),
  (0,0xc0901200400409810020338088cd19a330660cb),
  (0,0xb00a8031a00b817013096244098cf0200402682d),
  (0,0xb01702e05c12c09833020010168150060b848810),
  (0x202c65,0x1446880304e0480a8880042700982602008402011),
  (0,0x180188d204e0ac090280500d00982605404002011),
  (0x202c75,0x1442d89d0600480986501a0001202f02004402010),
  (0,0x190030080120580c80500e0100381812e0604b017)]

def r5_4 : List Hint := [(0,0x35000803134048090c70c434c2d84f0200400203f),
  (0x203075,0xb00989d00c0480982501a0001200502004402010),
  (0,0x35000803134048090c70c434c2d84f0200400203f),
  (0x203065,0xb00a80300c0480a85b0042700980502008402011),
  (0,0x144108030a0048090110040040984e02004026811),
  (0,0xb00301205c008098330200100881500604800810),
  (0,0xb01880300c048090a60040041580505408402011),
  (0,0xb81705c00c0c82d8330800fc020b60b835412010),
  (0,0xd40300605c0b8098330660100883502a01817033),
  (0,0x8008031340480904715834c1c04f020040020d6),
  (0,0xd40300605c0b8098330660100880306225049892),
  (0,0xb00a8a900c0ac0a8361740f81100505408402020),
  (0,0xc3686d02c0580c81903201c3689011e23847097),
  (0,0xcc0a83300c0cc0302e19c0b809833020230528a0),
  (0,0x3401580300c0480902e004004098330ac15802011),
  (0,0x14429803048048090020040040981002004026811),
  (0,0xb00a80300c0480902e004004098330ac15802011),
  (0,0xb00a8a900c0ac0a8361740f81100505408402020),
  (0,0x2c83686d0320580c81903201c3689011e23847097),
  (0,0xc3686d0040040b01903201c5308c1182386c0d7),
  (0,0xc3686d0040041701903201c5308c1182386c8d7),
  (0,0xc3686d02c0580c81903201c3689011e23847097),
  (0,0xc0b0160240480c81002001c148610be11c0c017),
  (0,0x190030080120580c80500e0100381812e0604b017)]

def r5_5 : List Hint := [(0,0xb00a80300c048090130040040980502004002011),
  (0,0xb00a80300c048090a6004004158050620ec02011),
  (0,0x1441d80307204809028004004098da02004002011),
  (0,0xd40a8b200c0480902e06436c098330ac15867011),
  (0,0xb00a80300c0ac0a802004004110050620ec02020),
  (0,0xb00a8dd00c0480902e09e3700983305408402011),
  (0,0xc090120040040982c02a0181701002001008833),
  (0,0x1441880308a04809002004004098de02004052811),
  (0,0xb00a80300c0480902e004004098330ac15802011),
  (0,0xc3686d0040040b01903201c0388c11823847033),
  (0,0x38030080120380403300e0100382e06804c4b011),
  (0,0x1446880304e048090c70040040982602004002011),
  (0,0x1900300802c0580c83300e0100381812e0604b017),
  (0,0x18028e400c38c710051c23806f82e0641002d83f),
  (0,0xd43686d05c0040b03302001c0880600c01817033),
  (0,0x130188030b2090120a6004004110310540ec1b811),
  (0,0x1900300802c0580c833032010368a012e27c4b017),
  (0,0x1441500300c048090450040040982a02004002011),
  (0,0xb00a80300c048090a6004004158050540ec02011),
  (0,0x1900300802c0580c833032010368a012e27c4b017),
  (0,0x130188030b2090120a60040041102a0540ec1b811),
  (0,0x190030080320580c805032010368a012e27c4b017),
  (0,0x1441d8030a0048090110040040984e02004002011),
  (0,0xb00301205c008098330200100881500604800810)]

def r5_6 : List Hint := [(0,0x240300802c0580c833032010368a012e27c02017),
  (0,0x1900300802c0580c8330322943684912e3944b017),
  (0,0xb01983300c0481982e05c39809833118040268a0),
  (0,0x1900300802c0580c83300e0100381812e0604b017),
  (0,0xcc0a8330240cc0902e19c0b809833020230020a0),
  (0,0x3400a80300c0480902e0040041583305408402011),
  (0,0x1441d803048048090020040040982f02004002011),
  (0,0xb00301205c008098330200100883100604800810),
  (0x603425,0x130298890b2090120a60680045c0650d439c1b811),
  (0,0x3a42c80802c058040650420dc0884912e3944b0e8),
  (0,0x380b01600e01c0388e11c2385f09712e2584b8ea),
  (0x280f304203875,0xb00981600c0480982501a0001200502004402010),
  (0x3cb1,0x1301d80302c18400849004004758650980ec1a02d),
  (0,0x1301d8030b209012062004004560100ac0401c011),
  (0,0x1900300802c0580c83300e2940382e12e0604b017),
  (0,0x38188ee00c0201203300e0400202e1da3b009811),
  (0,0x2fc0300802c0580c83300e0100382e12e0605f017),
  (0,0x1301d80312e0080089707a120778650980ec1a02d),
  (0,0x1901200802c0580c81000e0100381812e0604b017),
  (0,0x2fc0300802c0580c83300e0100382e12e0605f017),
  (0,0xc0780e02c0580c81903201c3209011e23847097),
  (0,0xb00a80305c0b81702e09624409833020040020f0),
  (0,0x1301d80312e0080089707a120778650980ec1a02d),
  (0,0x190030080120580c80500e0100381812e0604b017)]

def r5_7 : List Hint := [(0,0xb00a80305c0b81702e09624409833020040020f0),
  (0,0x1901200802c0580c81000e0100381812e0604b017),
  (0,0xd40301202c0580b0330200100382e05c0b817097),
  (0,0x1900300802c0580c83300e0100381812e0604b017),
  (0,0x1900300802c0580c83300e0100381812e0604b017),
  (0,0x190030080120580c80500e0100381812e0604b017),
  (0,0x1301d8030b209012062004004560100200401c011),
  (0,0x1900300802c0580c83300e0100382e12e0604b017),
  (0x203865,0xb00a80300c0480a8560042700980502008402011),
  (0,0xb00a80300c048090a60040040980502004002011),
  (0,0x1441d8030a0048090400040040984e02004026811),
  (0,0xb00301205c008098330200100881500604800810),
  (0,0x144108030a00480904f0040040984e02004026811),
  (0,0x14418803048048090020040040981002004002011),
  (0,0x1301d8030b2090120a6004004110680d40841b811),
  (0,0x190030080320580c80500e0100381812e0604b017),
  (0,0xc3686d0040040b01903201c5308c1182386c0d7)]

def c6 : Catalogue := (488,69,0xce2cea0a407e96231e7167505203f4b10ff38b3a82901fa5889d9c50941480fd2c44e00338a0a407e962276716750524480fd25800ce2cea0a407e92d9c59d41480fd2c439ce2cea0a407e96229e7167505203f4d32c738b3a82901fa64163a659d41480fd2c417d3338a0a407e962346999c59d41480fd2b34cb3a82901fa5883d9c59d41480fd2c449ce2cea0a407e9622ce716755d203f4b116738cc30ca0a407e9639c59d41481153f449ce31ac3282901fa58e7167505203f4b121738b3a8aa0a407e9639c59d414810f3f4b1ce2cea0a407e96223e7167505203f4b118338b3a82901fa5887b9c59d41480fd2c452ce2cea0a407e9620de7167505203f4b125738b3a82901fa588719c59d41480fd2c411ce2cea0a407e98458e7167505203f4b10eb38b3a82901fa588a3a868967505203f4b1ce310bea82901fa58ea19c59d41480fd2af38b72b4a0a407e9639c59d41481063f4b1ce2cea0a407e982588019c59d41480fd2af38b3a82901fa59962006716e505203f4b1ce2cea0a405891604e9d9c59d41480fd2c738b3a82901fa6f1639c59d41480fd2dcb1ce2b4a0a407e962346a19c59d41480fd2b338c4282901fa588c7a359d41480fd2c417d3b38b3a82901ec58e716756141480fd2c738b3a829022e7e9639c59d41480fd2c490ce2cea0a40869fa58e7167505203f4b116338b3a82901fa629639c59d41480fd23809ce282901fa588b40f6bd9c505203f4b116b38aaa82901fa588b59c5b541480fd2c45ace282901fa588b403e799c505203f4b116b38a0a407e9622d0b19c505203f4b116833ce282901fa629622d67188505203f4b116b46b3a82901fa588319c53941480fd2c41ece2cea0a407e94e04ea99c59d41480fd29f38b3a82901fa7b94f9c56941480fd2c45ace2cea09fa589080b67167505203f4a705b38b3a82901624502d9c6217d505203f4b1d32cea0a407e9620f6999c59d41480f62c74cce282901fa588b5a667167505203f4a7ce310a0a407e96231ea167505203f4b52c738c4282901fa588b59c6215a505202c45ace2cea09fa5890822e7167505203f4a711738b3a82901fa5893f9c59d5c505203f4b1ce310bda82901fa58e716755941480fd2c746ce282901fa588b59c59d5a505203f4a7ce282901fa589042d671675051d3f4b118b38b3a82901fa681639c59d41480fd324b1ce2cea0a407e98058e7167505203f4b103338b3a829020e7e9639c59d41480fd2c443ce2b4a0a407e9622e6a19c59d41480fd2b738afa82901fa588b5b167167505203f4a7ce310a0a407e9622568d67505203f4b107738b3a8ea0a407e9639c59d41480fd2c493ce2cea0a40851fa58e7167505203f4b115738b3a82901fa588659c59d41480fd318b1ce2cea0a407e97c58e716750520414fd2c738b3a82901fa588859c5f941480fd2c44cce2fca0a407e9622b67167505203f4e92c738b3a94a0a407e9639c5f97d505203f4b1ce2cea0a407e9621a6716752141480fd2c738b3a82901fa589139c59d5e505203f4b1ce2ceb0282901fa43e718652541480fd2c738c32fca0a407e9639c505203f4b115845ce2cea0a407e962506716752d41480fd2c738bf2f6a0a407e9639c59d41480fd2c433ce2cea3282901fa58e717e505203f4b116b38b3a82901fa6b9639c59d41480fd2c40bce2cea0a407e97058e7167505203f4f42c738b3a82901fa5881f9c59d41481003f4b1ce2cea0a407e9620a59d41480fd2c46d07738b3abea0a407e9639c63d79505203f4b1ce31ebda82901fa58e716758141480fd28f38b8292a0a407e9639c59d41480fd3a0b1ce2cea0a40819fa58e7167505203f4bf2c400ce2cea0a407e9479c59d41480fd2f4b100338b5a82901fa58e7149505203f4b117338b3ac0a0a407e95b9c5f941480fd2c44ace2fca0a407e962316716757d41480e72c738b3a82901fa588619c59d5d505203f4b1ce2ceaa282901fa58e716750520448fd2c738b3ac0901fa5883b9c5f949505203f456ce31ebf2c0a09fa58e716750527480fd2c738caae6a0a407e9639c59d41480fd38cb1ce2cea0a40849fa58e7167505203f4ba2c6cea0a407e9623c0319c66567505203f4b1ce2cea0a407e9b258e7167505203f4f52c738b3a82901fc7e9639c59d41480fd2c413ce32aa0a407e9622d67167505203f4b102338b3a82901fa588499c59d41480fd3e0b1ce332a0a407e9622d0019c505203f4b116b52b3a82901fa588319c59d41480fd2c465ce332b3a82901d858e71675052a480b11db4acaacea0a407e9639c59d41480fd2c418ce2ce952407e9623be71915052a480fd2c738b3a82901fa588ec0067167505202c476ce2cea0a70901fa58801a559d41480fd2c400ce2ce901fa588ef9c59d41481143f4b100338c8a82901fa58e7167505203f4b124b38b3a82902167e9639c59d41480fd2c44bce2cea0a407e9621567167505203f4d12c738b3a82901fa5d9639c59d41481043f4b1ce2cea0a407e9622067195505203f4b115b38b3a82901fa5884b9c59d41480fd2c420ce2cea0a407e9e258e7167505203f4b117738cdacea0a407e9639c64941480fd2c44cce2cea0a407e96211e7167505203f4b109b38b3a82901fa759639c65941480fd2c456ce2cea0a407e9c858e71675052f480fd2c738caad0a0a407e96367505203f4b106016b3a82942407e9620b67167505203f4ee2c738b3a8295a407e9639c59d41480fd2c42dce2cea0a52901fa58d9d41480fd3c8b106338caacea0a407e90f9c619414a9203f4b1ce2cea0a407e96244671675053a480fd2c738cab0ca0a407e9639c59d41480fd2c4a4ce2cea0a58901fa58e71414a9203f4b116b38caacea0a407e94f9c59d41480fd2c42cce2cea0a4c901fa58e7167505203f4f32c738b3a82901fa5881d9c59d41481013f4b1ce2cea0a407e9620ae7167505203f4b103738b3a82901fa5c96367505203f4b10ac22ce2cea0a76901fa58e71955d941480fd2c74cb3a82901fa588560067176505203f4b1ce2cea0a407e9da58e716750520408fd2c738b3a82901fa5e163675052a480fd2c41ace32ab3a82901f658e7195505203f4b119b38b3a829da40711639c59d41480fd2c428ce32eb3a82901fa58e716753541480fd2c738c4282901fa588459c6555a480fd2c45ad42cea0a547e9620c6719562141480ec2c738cab10ad2407e96200671956215a480b1b3a82901fa588e02fe999c59d41480db2c73eb3a82901fa588bf9c59d41480fd2c46ece282901fa588be2d67167505203f4dd2c738b3a82901fa6b16367505203f4b117c18ce2cea0a407e9b058e9967505202c47c17f38b3a82901fa588fb9c59d41480fd2605fce32ab3a82901fa4c6999c59d41480cf2c738b3a82901fa588839c59d41480fd2c412ce2cea0a407e99c58e7167505203f4b10f338bb282901fa5888b9c62176505203f4b1ce2fcbb282901fa58801a65d941480fd2c738b3a82901fa678259c5d941480fd2c441ce316bb282901fa58e7167511203f4e52c738b3a82901fa678799c60d76505203f4b1ce2eca0a54901fa58e7167505253f4b117f38b3a82902207e9639c59d414b9203f4b1ce2cea0a407e962236716756d41480fd2c738b3a82901fa588c3a259d41480fd2c45fce2cea0a407e9621de716753141480fd2c738b3a82901fa588a19c59d414b5203f4b1ce2cea0a407e9621f67167505203f4b107338b3a82901fa589299c65579505203f4b1d6338b3a82901fa4c6717650520468fd2c738b3a82901fa6f9639c59d414811b3f4b1d62cea0a407e9b458eb1a259d41480fd2c764ce2f2a0a407e9639c59d41481183f4b1ce2cea0a407e96202e71675052044cfd2c758b3a82901fa588319c59d414811a3b0b1ce2cea0a407e9624e6716750520470fd2c738b3a829a24058923ac67567505203f4b1d9338b9a82901fa58e7167505203f4b101f38b3a829022c7e9639c59d414811a2c409d9338a0a407e9622d67167505203f4b101b38b3a82902227e963b267141480fd2c456d933ab3a82901fa58ec99c5a141480fd2c738b3a82902187e9639c59d41480fd334b1ce2cea0a407e96458e7167505202c48d00f4ece2cea0a407e9639c59d41480fd380b1ce2cea0a407e96c58eb19c505203f4b11a338b3a829a2407e959ac59d41480fd2c41ed9338a0a407e96231e9d67505203f4b105f38b3a82901fa588c9af67141480fd2c468ce2cea0a407e962340019c505203f4b11a354ce2cea0a407e9580067167505203f4acd7acea0a407e9620f67167505203f4b107b68ce282901fa588c7af67167505203e4b1ce2cea0a407e9620be716750520468b105b38b3a829a2407e8e59c59d414e51a3f4b1ce2ce9a2407e96239e718c50520468fd2c400ce2cea0a407e8e59c59d414dd203f4b100338c3a82901fa588019c59d203f4b11cf38b3a82902327e962006718c505203f4b1ce2cea0a407e96247e7167505203f4b101338b3a829021c7e9639c59d41480fd2c448ce2cea0a407e96214e7167505203f4d42c738b3a82901fa621639c50520468fd2c45cd6338b3a82901fa56eb167505203f4b107764ce282901fa588c59c59d41480fd2c402ce2cea0a407e9620fec19c59d41480fd2c738b3a82901fa7d1639c59d41480fd2c45cce2bea0a407e9622e0019c505203f4b117338cd2cea0a407e963b167167505203f4ad00338b3a82901fa56e718e505203f4b112b38b3a82901fa588cfad59d41480fd2c41dce2cea0a407e9620eecd9c505203f4b118b38a0a407e9623308b9c59d41480fd32cb1ce2cea0a407e962056716750520420fd2c738b3a82901fa588899c59d41480fd2c431ce2cea0a407e99458d9d414811a3f4b106b58ce2cea0a407d963ac59d41480fd2c422d9338a0a407e9623367167505203f4b100738b3a82901fa58835675053b480fd2c41a002cea0a407e9620d6ad9c59d41480fd2c738b3a82901fa7d963b667167505203ecb100338b3a82901f658e7167505203f4b113738b3acca0a407e963b659d41480fd2c422ce2cea0a407e962116d99c505203f4b119b38b3a82901624602da767167505203f4b1d9338b4282901fa58e7167505202c47e05b38b3a829da405882dac69967505203f4b1ce2cea0a689016858eb167505203fcfd2c74cb3a82901fa5882fa667167505203e4b1d9338a0a407e96231e9967505203f4b119b6cd32cea0a407e963ac59d41480fd2c463d934ca0a407e96231e996750520468b105f58d32cea0a407c963a659d414811a2c45fd634cb3a829023458e71414811a3f4b116b58ce2cea0a407e94f9c62141480fd2c44ad9338a0a407e9623167167505202c47c05f5eb3a82901fa588bf9c59d414d120354b1d62cea0a40831fa58ec99c505203f4b119b64d6282901fa588cd9c59d414d1202c417da358b3a82901fa58ec99c61941480fd2c738c430ca0a407e9620067186505203f4b1d62cead2407e9620f6a19c59d414d0f72c738b3ab4901fa588cdb667188505203f4b1d62cead2407e9622fec9ac62141480fd2c758ce2b4901fa588b5a867167505343f4a700338b3a829a1fa53e8d6750520468fd05f58ce2cead2407c9620067167569203e4b1d4338b3a829a1620b6c9a662141480fd2c758ce2cead2405888ba868d67505343f4b1ce2cea0a408d1fa316b167525203f4b107738b3ac0a0a6875163ac59d49480fd2c45fd9358bf282901fa58e716752541480fd12b6ace2fca0a407e9639c59d414811a3f456d9338c9282901fa58e7167581414d0b105b64d32fca0a407e9639c59d414811a3f41dd9338c7282901fa58e717e50520468fd12b38c7afca0a687e963b26718f505343f4b1,0x55445400554445004554540045545400455454005445450054454500454455005554440044454500454445005444450045544400444545005454440055445500555454005554540055545400554455005544550055455400545455005445550055454400455454005545350045545400455454005445450055444500454455004544550035545500555534005445540056444400444555005554440055445400554445004445550044455500555444004445540044445500444545004454450045544400444545004644440054444500444455004454550044455500444545004445450045544400355445004445450045544400455444004554440045544400455444004554440045544400355544003554450036544400544535004554440044454500444545004445450036544400544545005445450054445500564454005454540054445500455454005445450046445400644535003654540036545400454545004545450054544500545544005645440044544500455445004455450035554400454535003455450045453500454445004455440045444500454445003554450044553500355445004455350036444500545435003555350035454500345545004554350035553500355535004545350035544500355445003645350036543500545445004454550056444500454544004454450054545500545455005455550055545500564455003654450054553500355455005645350035554400355445003654450034554500445535004455350045454400445445004454450044544500545435003454550036455400564534003455550055543500545445005545440055453500345555003545550055553400355445004455350036444500464435003454550055454400545445003554550034555500446535003654360036563500355535003654540054454500544545003554550054453500355454003554450044454500444545004445450036544400444545004554440044454500365444003654440054453500454535003554540054454500455454005445350054553500554535005445450054454500544545004554540054553500355455005545350035544500355544004545350035553500355535004554350035454500354545003654350035554400445535003554450035553500355535003645350045543500455534003455450036543500544545005445450046545400544545005445450055544400444555004554440044454500544545005554550055455500544555005445550056545400555435003545550035554500455535004554350034554500455444004445450045544400455444004555340045543500555434003445550056543400555444005654340055544400555444005554350044454500455444004654340034455500555444005554440034555500465444003664440054463500365454003664540036645400555444004444650055545400555454004654440044455500345555005545350035545500554554005545540045455500355555004445650055544400444555004445550035455500565444005654440056543500655444004445550055544400555444005554440035455500555435005555350045455500545455005445550055544400555444004545540055455400555435005554350035555400554535004544550044555400554445003655540044555500555445004454550055444500545455005455540046455400445445004545350035544500545535003554550054454500544545005445550055545400465454004554440044454500444555004654440045543500345545004654350055445400464454005445540054454500454455004544540054444500445445004445450045544400444545005454440046444400544445004544450045544400455444004554440044454500444545005454440054544400464444004454540054444500544455005445450054454500545544005544450054454500544545004554540054554400445455005544450045444500454445004455440045444500355445004455350035454500355445004455350054543500464435004545440044544500445445004454450035544500355445003554450035544500445535004455350036444500455435005454350054543500464435004654440044454500444545004554440045544400354545004554350044454500455444005554340046543400455444004445450044454500444545004445450045544400455444004554440035454500345545005554340055543400465434005454540054445500564454004445550044455500645454004445650064544400544455005454540056444400555444005554440055544400564444005444550054545400554455005454550035545500545535003644550056443500444555005554440034456500655444005654340056543400444555005554440056445400564454005644540054644400444654004564440046544400556444005654440045644400444645004446450054444600446454004464540054465400564454004564540054464500454446005464350034565400556435005654350035544600464535003554460046453500445654005644450044544600464445003644460036464500464644)

def r6_0 : List Hint := [(0x95,0xb060228700880483d0430e400213c798f209011c3508407004078811),
  (0x800405,0x600a3e00a82405e2444d0f40022987b84f09011c678f601416c7a8f3),
  (0,0x3302a040030ce02433c2000109a0b852091026270500f91ee2c05b0d9),
  (0x34c48008f1,0xb0c23ec188881f40484300402412c4404700204c08084014040268a2),
  (0,0x4c0a62c82c81202a298010fd0081242585702611c0581005e2847e0a2),
  (0x400005,0x4b0203ec188011fe0482b8040243dc238a80680e06688401416c268fe),
  (0,0x2c204090150dd01a01801038202014081000420dc0683d1e437023811),
  (0x1131,0xb020410718881fe0484300c024268818c600204c5888401815826811),
  (0,0x5102a2240302402a420838fd14a0b82185702611c1990605e4147e0a2),
  (0,0xb1f01381802105e02c5184307e2680884f0023ac7b08401416c7a8d1),
  (0,0x4e0664280a8f401a0181104d02a0b85d0440ae04c8400d2123f452826),
  (0x400425,0xe31bc3ec6c80d21a0ac8600418c0c81f0c621604c790840143f8268d1),
  (0xa0143d,0x30a44380a81200816c0110b0263c81900a14a080058ca16609c14026),
  (0,0x2c0b2160150dd20c0b801057202044279061b811c1981021e0842a811),
  (0,0x30201d8030120082980110b0263341900c14a0806691316644888910),
  (0,0x5102a00c6802402433c0100100804c5209102611c8a106020414848a2),
  (0x20d12007054801805,0x1180241580905600604c8b83406818c0883d09011c8b00a0700e006115),
  (0x253d,0xb08e08c0091b2340901382b0b60401302a07e0108c82301a03019040),
  (0x8028f1,0x12023e228448011f40902b8380244784e00c23a37c080dc1ac0400211c),
  (0x2ca1,0xb0481a81202100648090834068040340100200dc790e707a12023811),
  (0x11328a040c2280f304a03877080d1d4a0306f,0x4b49612b03c4a89492824e4989281c24848c0d122),
  (0x28133c4204885,0xb00608c4411b02c38c13812026034118470180887002602004402020),
  (0x5111,0x1002000c038120240441a0340083a0258910260309809011e4bc4692e),
  (0x4050ba00132c8003cb1000b22c002887,0x4f89e8822784ec9d1392704dc9b1352684cc99131)]

def r6_1 : List Hint := [(0x58e10010344c054ad,0xd0481a8120210064fc8b8340682cc0883d09011c068680d40841b811),
  (0x174c40044e1,0xb02c5041202707018411800064040130d60081003094010606089817),
  (0x1875,0x310962286180d21a0908603818c508440471fc16c080b41ac3bc0203f),
  (0xa0603d,0x312246c1201207050c0109c064040080d6008100058ca16c09c11826),
  (0x69310019284001c75,0xb0c21800685d288090138321a217c4404713816c080260803ac0203f),
  (0x24d9281c0f4006c11,0x510ba274138120b608c0689c0640980803f0081001884728a09078010),
  (0,0xb0b01a82c021006268a30020024180884f1b80302a0680200404c811),
  (0x5521,0x3505c5200301207051c0100c0640cc080d60081000c14016c250a0092),
  (0,0x544a808229e4a83814e29a530a594a2481b80d149),
  (0x817434805901,0x1540a211c0a80d112018a98240242202391f00216c029520200400203f),
  (0,0xb01a228ad0882b4564430c50245604415700204cab0842aa04002011),
  (0,0x4108e1448d80d2b62681202418c11c6983414e16c278100203bc0203f),
  (0,0x6a04200caf84b122578120240161a0080102ba4000583d0905707e84f),
  (0,0x311862700910c18c0081f10b0260405a0ef008044619642c6588b0960),
  (0,0xb112220090861a25a08183e026040420eb008044b39662ca588b0960),
  (0,0x301a30c1201218c5a8259691340e81a0a707011c080101de010278d6),
  (0,0x2c02a00c010020021641202408e4088716c16c3b8028560ac0dc7e96b),
  (0,0x16e13800c2b8120482705603406437008010008100058ca062090b6810),
  (0,0x6a04200cb90120241a0080102ba5c42589120c5c00583d0902842796f),
  (0,0xb00622012086024008818010261304205b008344ba9660ec5d0b9960),
  (0x7521,0xa602a05803032024004000010b60cc2001009a0fc249760be3948e817),
  (0x8074ed,0xd2fc08c0697d2f85ecbd02414e5e414002216088bc1770d43bc1b811),
  (0,0x6400c020c017f1420b8170130000cc198a101427c0c0970301704a017),
  (0x600025,0x91006008069832f80900981218c6081303414e010080a20206045080a)]

def r6_2 : List Hint := [(0x207835,0x200200c098120246145203400828808010142028058ca01a090c2010),
  (0x201f194c07c05,0x571640088305d2f80c00981218c034238a814e030178110203bc0200c),
  (0,0xa614c00c098120240a81a03400828808010142030618610be39473817),
  (0,0x2006004090570242b04e0340700406e0100083583096430e588c3160),
  (0,0x18801a46c1202b18c34c5d0a70b6040150ef0080fcb500d2d22686384f),
  (0x8141,0x2e01a1800685d2880904d0221a2458238a814e0e00804f0403ac020d6),
  (0,0x18b0ba2244d0121a211c8f0a707013c080eb00835820847314090c4810),
  (0,0xb31a220158860242e8818010b60a8420100080fcc616630e588b9960),
  (0x2021194c08405,0xb2d06384418f31a04c1801202a11cc70a814e0300882f0200840200c),
  (0,0xa614c00cc88120240001a03407004408010008358bb0610be394c8017),
  (0,0x350165f00301218c0348988d12815c010c102664c028101de010c9011),
  (0,0x2c02a00c0984b122160120240164201e8482b83f48a010020574ca00a),
  (0,0x1200060080691b2f80904d01218c4582383414e0e00804f0203bc020d6),
  (0x8911,0x2c02a00c0383406801809012018280080100186540684b12211c09811),
  (0,0x2c02a00cb904007e2800801006e6601a03401665c0684b12265808867),
  (0x808cf1,0xb23e228448881f4090430380244648199900216c080841ac0400203f),
  (0x20253b44090e1,0xa3360b0cd01500602c0901202411c1704b12204c05033020040020a2),
  (0,0xf0c800c0401204801c080100080d4ce19c2c45800696800204c08847),
  (0x98e1,0xb000174090271a20581403e026040130eb0080444199d318260888ae),
  (0,0x1a4346510030221a20b85d03e0260cc100eb0080445b1a2342680cf99e),
  (0,0xb016510030221a20b85d03e0260cc100eb0080444699d34a25049892),
  (0x2a4e480a53100284a4a09d21,0x2c0160340a8031380180900c0240b80109c12204c1981001804052811),
  (0,0x6002a634030600240b85d0010260ccd401009a0448280d30e69cc61a6),
  (0x202223800b886002d1d820b466302c17800ac56202c02c40ac07,0x6d0d99b203c6c4d81af35c6b4d601c3566a80d1a9)]

def r6_3 : List Hint := [(0x993d082647480bcad,0xb0001800005d2886d8138221a2000140ba07c088da8260403ac02020),
  (0x20223b40064d508193140080a5001a25420688530311f480c0752031024c0c005,0x2c02a2a40302b02a04cdd1b90266e0db94501611c0282a0420100880a),
  (0xbd4d20323b4c0c85d,0x3360b0cd0150060000301202411c1704b12204c0003302004002011),
  (0,0x208e21c30fe1f8e107c0f6704e01bf37c6f4de1bb),
  (0x80cc3d,0x338a61c0901200012c488000260400800032a0444808f00028046018),
  (0,0x2311000ce4812024720258910265c408010008044059c530e284e39c6),
  (0xcc1d,0x2c02a2a40302b02a0d85d03e064014150210081000680d01a72c001ca),
  (0,0xb112220090861a25a08183e026040420eb008044b39662ca588b0960),
  (0,0x350165100302218c0b85d10b0260cc100ef008044e691339825049892),
  (0x993d,0xb39c08c4e11b2886d81382b18c354140ba216088da8260543bc02020),
  (0,0x30da1b4e29872fe12c488130000400817f0002884808f11c5e046018),
  (0,0x2c02a0c41581202a04c2585b026594e89653a073c560de1e40101000a),
  (0xc0d005,0x4e02a374280a407e0b8200011d60cc3501006e044c000d3a602cae1d2),
  (0x6cc5001a11420dc3518360b480d4250836034c0d405,0x2c02a00c0301202a16c0109c02601408021008044d100028a02c2380a),
  (0xe0d9,0x5106222412012048754db9d43962b00103406427008010020010a9040),
  (0xc0e405,0x6a04200ceb84007e044258911de1a00801006e044059d33a602cae1d6),
  (0,0x4c07600c2c8120242980100102602cad9da3b27642b010020010089d8),
  (0x941400e005,0x6400c0205f8000320140380400e0d45789812c2b80c09703011c0b861),
  (0,0xd020054198d0024008098010260346985b008344418b019a2c06c9db),
  (0,0x4c0a62c82c81202a29801057026194190f2008080058761f0284e78fc),
  (0,0x1001a2c81981202a29801057026000190f20080804688c11e774971dc),
  (0,0x5102a2241582402a04cb405b0262b0260f2008080b29062ca414e79de),
  (0xe921,0x502a058030ce0240b8000010260cc0501009a288500833be27c61817),
  (0x856,0x4f8f61eb3d47a4f41e70fe798f29e43c6788f09e0)]

def r6_4 : List Hint := [(0x203a3b4c0ec5d,0xd3da1a80682a1ba000520400885e4088021b80880002a0540841b811),
  (0x3b4b420ed0d,0x1800580000a800006018f78120240b80600200204c1980a020040529ee),
  (0,0x7ec0f1fa3f27ccfc1f73ec7d4f01f43e67c8f89f0),
  (0,0x18002a000031ef0240b8000910260cc0501014a7b8500830c227c89817),
  (0,0x4e02a7f8030c50240b8fe8010260ccfe01014a7b8c000d3a8414ea1de),
  (0xc00c05,0x2c02a2c80301202a148b405b0b672c3b1ff39611c310561620106e06b),
  (0x3d4f4a0f131203d3b440f0e1,0xa01a0b04e01500602c090120242701700212204c05033020040021ee),
  (0,0x6a40600cb90120241a0010910261a0080100087b805a02402284cfa00),
  (0x83f034c0f805,0x2c02a3740301202404820001056014150100080440680d3a64182380a),
  (0,0xb00622012086024008818010261304205b008344ba9660ec5d0b9960),
  (0,0x301a5f02c81218c2980110b0260ec190ef0080810211339844888892),
  (0x80e8ed,0xd2fc08c0691b2f88141382418c5e414002216088bc0260543bc1b811),
  (0,0x6400c020c02061420b8488130000cc080a10142885009713e17061817),
  (0,0x2c02a2c80302c0240b8190010268250418740e63019856020740088f3),
  (0,0x2c02a2c80301202404c010570268303b20c416828588321c20101000a),
  (0,0x4e0542a4030221a20b85d03e0260cc100eb14a7b8c000d01a83d0720d),
  (0x3114c1103d08430d461082d2041094c10005,0x5104200c2801202413c010010261380801009a0440580001a02d071d2),
  (0,0x4c06200c0301202484d092113962c4010340642cc08010020840a9040),
  (0,0x4e042634280220241a05d001026138d40100082880580d30e414ae109),
  (0,0x2c02a2c80302b024158190010b60142b0100083710420830e72c239ca),
  (0x8486,0x8710d8824344a8382190fe1f90c21742c8550a1e0),
  (0,0x2c02a2c80301202a6003b1ff14204c2585b026874588761a62840505d),
  (0,0x8a113a2644a1fd1222324888837a213d68810fa1e),
  (0x84533c203465,0x8bcd9a2e03c4a8d822d4588ad1501c2486a80d229)]

def r6_5 : List Hint := [(0x38e5,0x2c02a00c8c0760ec02c0901246404c0100146204d180760ec028ca875),
  (0,0x8a0a808244e8991a2250fe1f91223342c854e09e0),
  (0x7ca5,0x5104200c280120248d4e29871425902589102611d1a810020284050a2),
  (0,0x2c28e7142c8240162981e8471e40cc082362000440a80333409024010),
  (0xc04855,0x6a04200c03012024728e29871427282589102611c73810020284050a2),
  (0,0x2c02a00ca39c530e164120240162981e84808e3c8028100208d880011),
  (0,0x2c02a00c030120240141a034008280080101420280684b12204c23844),
  (0,0x6a04200cb90120241a0258910261a008010008288059c530e284ae237),
  (0x28474c4a118ad,0xb02c6384e0e300604c180121c6000c72382160880882f02038002020),
  (0x12131,0xb02c14c09824024000698010b6044080100080fc41a390be060ce017),
  (0,0x2c34600c030120480d8010340640140801000810006a0247472c2e1ca),
  (0,0x2e01600c09812048000010340640140801000810046a3b3be060ee017),
  (0,0x4f89e8824849052023f0fe1f91f23d42c8551e1e0),
  (0x41254d20483b4c0c85d,0x336130cd03b0060002c82404811c5883d0903c8000100200401c011),
  (0,0x9280f1fa4927cd2401c48e069232453e6910f8a43),
  (0,0x24b0627f81202c0482b0fe80106404035010008100ea80d3a872cea1ca),
  (0,0xb0000c4a9824048000560340645480801000810041a3b0c206089817),
  (0,0x6002a634090220240b85d0010260ccd4010008288ef00d30e414c61de),
  (0x12511,0xa614c00c0381202400025891026000080100082884689011e27c46018),
  (0,0xb31a220158860242e8818010b60a8420100080fcc616630e588b9960),
  (0,0x350165f00301218c0d40110b064014080ef0081012614039825088892),
  (0x1049464011d11,0x4c07600c069c530e164120240182981e84808e3c8080100208d880011),
  (0,0xb00046cdb02718c9341410b0326d4130ef00801cbf1402fc0604b017),
  (0,0x2c02a00c1b01202404c2589102682ce298714271c028100202840880c)]

def r6_6 : List Hint := [(0x204b1e4412871,0x2c02a00c090120240b82580102693c3b076016938840321fa0101300a),
  (0x204d3b44130e1,0xa3360b0cd01500602c0901202411c1704b12204c05033020040020a2),
  (0x811805,0x25501c0380400802401c038100089505d2534a49440680d4a004c08800),
  (0,0x2c02a2c80302b02404c1900102682d041871425708a02f0202845100a),
  (0,0x2c02a00c030120240b8010010264603b076416959278380700106300a),
  (0,0x4c07600c03012024480e29874ae2c41a03407011c08010020840a90d6),
  (0x8138f1,0xb23e228448881f4090430380244648199900216c080841ac0400203f),
  (0,0x12001a228448012b40902b8c502434c8199900216c080dc2aa0400203f),
  (0x40d05d,0xb11240c1208602a5a08185b026130420f2008080081661f09652c0ef),
  (0,0x2c0543745e0400889752e25b0820b82583f4b487419810188359000a2),
  (0,0x510a62242c82402a2981a05b026144260f2008080059061f0414e78fc),
  (0xe45d,0xb3fc40c160860487f4818010641a8420100081011da603a897c85a5e),
  (0,0x2c02a00c030120240141e848008280080102ba0280684b12241823a61),
  (0x201a2d4402055,0x6a04200ceb84007e99d2e25c4cc728010014ca9907381002098d311ee),
  (0,0x2c3467f80302c0480d8cc801064014350100081000680d30e72c2e1ca),
  (0,0xb23e228448884d00904303802a4645c95707c0c8080841ac08402040),
  (0,0x1200060080691b2880904d02b18c458638ba14e16c0804f0543bc0203f),
  (0,0x2c02a00cc8834068160120240160140801006e4001e83d09011c79011),
  (0x80e0b9,0x2c02a00c030120249a4e29874cc0b82589102611c19810020010050a2),
  (0,0x2c02a00cc70240486441e8481e401408010070045041c530e9a8339c6),
  (0x50294813c75,0x2c02a2a40302b02a0143aa6d0082d93610c16c11c460461882840526b),
  (0,0x301a5f0018121b6004010c102600c2b26f19c045370c3398330660cb),
  (0xc01015,0x4e0542a4030221a2680d11a13400b93610c02687419a724e201138011),
  (0,0x510a600c260510240080100102614426056008044059060ec4603a978)]

def r6_7 : List Hint := [(0x803314c00c15,0x6a0546345e0121a210539945340114258d10268741501016884138011),
  (0,0xb23e228448884e814443038024464441570020ac080842aa04002011),
  (0,0x1200060080691b2f80c44d01218c3c86383d1de0ac080260203bc02011),
  (0,0x301a5f01201218c004010c102602c11a7504e31c178101de01008826),
  (0,0x2c02a00c09012024778e29873a00b82589102611c19810020010050a2),
  (0,0x2506200c1201204812c258010269dcbe2763409381781005e010089b5),
  (0x78a5,0x5106200c138120249e4e29871422d82589102611d3c010020284050a2),
  (0,0xb2fc08c0691b2f86d81381218c5e4140022160acda8260543bc02011),
  (0,0x3100447c6880d288018188321a22993d0ba1d60ac198100403ac02011),
  (0,0x2c02a00c03012024378010010641882b05600813c7c1d10ec72c5b27b),
  (0,0x2c34600c030120620480103405601408010008044069d323e9f02e19e),
  (0x30520f4214435,0x510a600c12012024008010010260bc08010008044058ca01a9f8eca7d),
  (0,0x2c02a00cb28760ec018090121fc04c0100146204c588560ac3f802011),
  (0,0x2c062a00030120622993f8010560cc35010008044a380d23e9f02e19e),
  (0,0x2c2ca1d80a8b201a0ac0928102a04c011790ae04c560320143c802020),
  (0,0x5102a00c1582402404c010010263c82605b0083448c1063a24143a9de),
  (0x214c35,0xc800200c2b812024a085884805621008010008044058ca01a194c4810),
  (0,0xc40a63742601202434c20001056040150100080449000d3a69f941a7d),
  (0x15129,0x513aaa1018803138090091530482b00109c0680c8080102a404002040),
  (0,0x600626341202b0243dc5d0010b6040150100080fcc580d30e72cc61ca),
  (0x8154bd,0x2c02a00c8c0760ec0480901250a0b80100146204d27838070028020c6),
  (0,0x2c02a00c03012024600e298714204c258910268748a010020284050a2),
  (0x58394815c3d08560d4814c15,0x5111000c4302e05c59025891026210080100080b4058ca01a9f943a86),
  (0x16519,0x5106200d440760ec09c090120180a00100146204c130560ac0308c011)]

def r6_8 : List Hint := [(0,0x28a10e034188ff1c609d4482c0240a11889a00204cc280a1ec16c020d1),
  (0,0x4e02a374030400240b82789105c33c4280109a614c000d3a64153c80a),
  (0x178c5085d294017095385b1f4a16875285b024e16805,0x511a26341381202a220b409c026a314580d01611c130100420100880a),
  (0x85f434217881,0x28e0a211c18a8d11209ca982402440c2385f00216c131520200400203f),
  (0x18055,0x600626341382b02440c5d0010b6098150100080fd4780d30e72c239ca),
  (0,0x6a04200cb90120240442589105c1a01a034008318059d33a62853c80a),
  (0x205816c4078573058038007806,0xa550f9eb0e24a94a08d5267994906f248a440d290),
  (0,0x29710ea58188ff1c609c0202c0240a06309a00204cc280a1ec16c268d1),
  (0x218481,0x29a0a2a6418a9811209c1c0240242202385f00216c130d60200400203f),
  (0x18855,0x600623481382b02440c5d0010b6098150100080fd4629b30e72c239ca),
  (0,0x4e02a374030a40240b8200010260cc4281009a448c000d3a682cae29c),
  (0x1865274019095106523421908520631d4818455,0x6a04200cb90120240440100102602c0680d53c8380501002084008a9d),
  (0,0x6a04200ceb812024044258910261a008010008448059d33a682cae29c),
  (0,0x2c02a6340302b0240d85d0010b6014150100080fd2600d30e72c239ca),
  (0,0xb0960944885300604c1801202457033034068010890100200405080a),
  (0,0x1a00c00346880d0b8018db0221a22994f8ba07c0ac029b50403ac02011),
  (0x660f4215c35,0x5111000c4301202440c0100105621015021008044058ca01a9f95027d),
  (0,0x510a600c260120240e81e84805604008010008044902a33a6a8950a7d),
  (0x1058194a16035,0x200200c158120240440801000811c7083420c030058ca01a97c080e2),
  (0,0x5106200c030240480b8258910266813b2763409381982f05e010089b5),
  (0x216495,0x3024048010010260402b0e60223280686500419466aa654a1795200b),
  (0x14b5,0x2c06200c2c8240480b82580116caa0be2764ee938198100aca9c15236),
  (0x60b5,0x4c07600c2c8240480080100108e9dd562ab4eeaa82b0100200dc152a9),
  (0x15005,0xbf00c021578160320140380400e02d5716255a5800c0970302580ba3b)]

def r6_9 : List Hint := [(0,0x510a66341201202a0e80103e06404008021008100902a353672d581ca),
  (0x218835,0x200200c2b81202aa085603e06437008021008100058ca01a090c4810),
  (0,0x4094008530060c8120120242d87719c33858827ab20ac158022b1),
  (0,0x18d0240545603e06404010804080ad006857504370652b30485b408041),
  (0x673ac001ce7,0xae55c2b756c5355a81e0e01c49481c0dc1bc9181a),
  (0,0x3100447c0091f0b8018120320b651d5d04713872c198100800fc02152),
  (0,0xe305caf06880d33e018718131a2220068475762e0198e00223ac020b7),
  (0,0x1202400c198380700b80100118c93c2b0560180444606c0d839c3595e),
  (0,0x150022bc030120b60083309c0640cc0803f0081004c0611062605e8ae),
  (0x19cc5,0x2e346510030321a218c2389c0b60cc200eb0080fc5b05c1120915e810),
  (0,0x2c3961d8718b201a01809153060008012b057c0c8028562a438402040),
  (0,0x1470a266c1899a006018a9812024198238ab0cc39019952020040022bf),
  (0,0x2c02a00c0301202412c5591d1c80cc08010008afca39c530e72c239ca),
  (0x81a07d,0x2c02a00c670020020180300601804c4d05700004c4600500a03061811),
  (0,0x311a2000138121a20a16083e026098080eb0080444c2c0318260888ae),
  (0,0x1a00c0a3c688830b8018db0221a20d94f8ba07c088029b50403ac02020),
  (0,0x30ec1d8090120000580b2c30261582b0002300444808f58428047102),
  (0,0x2c02a00c1581202404c01001026460e89d15881d4790380700106300a),
  (0,0x5106200c1201202462ce29873963dc1a03407011c08010020010a90d6),
  (0,0x2c02a00c030120240d8e2987070b14e298739611c028100200106b152),
  (0x1a486,0xb2910ac95904a94a2c70fe7990c2c6248a440d06f),
  (0x6911421a435,0x200200c4d01202411c560d307013c0801000835805800000090c4810),
  (0x1a949,0x1640c0b2c6880d1a409c630221a20a0858ba07c04c130ef0403ac02011),
  (0x6c46481ad11,0x2c02a00c059c530e018090120180b82589108e04c19810020030ca811)]

def r6_10 : List Hint := [(0x1a8a5086a25401a005,0x3500c0181702e0260cc198040220000000605c0cc0183112824c49000),
  (0,0x2c02a2c80302b02a0b81905b02682d66acc14267c840ac1e42841000a),
  (0x6e034c1b405,0xd0056374030120240b82003f0260cc150210080445b1a23422d90500a),
  (0x805510700b481bc250070034c1bc05,0x2c02a2a40302b02a0b8540a70260cc15021008044001a234202c2380a),
  (0,0x1a434600c0302404851d012013960080100106403019810020010a9040),
  (0,0x250a600c12012024188010010640400801000810005a7359c4605b178),
  (0,0x2c02a2a40302b02a12c5d03e06451d682cf3960301982a04201020152),
  (0,0x2c06200ce58760ec018090305a40080100151c2680285605eb440204f),
  (0,0x5106200c1582404804c010010262b01883b0080808c10620c83d502d3),
  (0,0x2ac3500347580d0b81656a0221702994f8ba07c088329b516a2d01b811),
  (0,0x6449e5fc030060180580b2d50260140280c2300140c0971fe18c4b0f9),
  (0x7246481c511,0x2c02a2c805ad730e018090120180b8190015ac04c19856020030ca811),
  (0,0x51062510030221a20b85d03e0260cc100eb0080452b1a2342680cf99e),
  (0x81cc9d,0x1a00c047c6880d288018db0221a22687f0ba07c04c029b50403ac02011),
  (0,0x2c02a00d6c0760ec0180901201804c0100146204c588560ac030ca811),
  (0,0x2c02a00c03012024008010010260cc2b05632a045278760ec4603aa9d),
  (0x1d119,0x2c02a00d6c8760ec018090120182680100146204c028560ac0308c011),
  (0,0x1a00c00346880d0b8018db0221a22994f8ba07c04c029b50403ac02011),
  (0x7439421d0d5007331441cc65,0x30da1b40100105c0340680d0000640c80714c0344608c11c364830d7),
  (0x808075,0x250a600d6d8760ec0c0090125a4188010015b472c178560acb4414952),
  (0,0x601a22a41202b02a2b05d03e06404015021008100c580d01a72d501ca),
  (0x1d519,0x2c02a00d6e1c530e0180901201804c2589138e04c02810020030ca811),
  (0,0x1a4346510030221a20b85d03e026b74d11a134067c198201d6010089b5),
  (0x1d8c5,0x30580540901200c0580b00b5c004008005052b7c3085f20c72c23ade)]

def r6_11 : List Hint := [(0x1d405,0x30da1b40b0160320640c8070da2304608e11c35c3085f12e11c4b9b8),
  (0,0x3100447c6880d288018120321a20d88c8ba17216c028100803ac0203f),
  (0x20772f4c1dc2d,0x2c02a00d278760ec018090120000b80100146204c028560ac00002011),
  (0,0x250a600c1801202400801001026b843b0762301d4178560ac01008a69),
  (0,0x3302a0000303302a0b81a05b026420068f214a08046083158775711dc),
  (0,0x2c02a2c8030120240041a05b07072c3b1ff39611c028561620106b152),
  (0x3411420d035,0x5106200c03012024044010010260a80801014a044058000000315027d),
  (0,0x250a62c82c82b02a2981905b026194560f200808005acd598284cfae3),
  (0,0x3302a0400300d0240b8010010260140685609a0444608319a27c6cae4),
  (0,0x24f0580340a80d164018060120240b94f8320b604c0280c1622c452811),
  (0,0x5102a224030510240b81a05b026014260b114a045279062ca69ce79a6),
  (0xc01005,0x2c02a2c80302b02a29973ae607072d729ff39611c028b11620106b06b),
  (0,0x250a62c832812024004010570261942b0b100804405876598284e79c6),
  (0x79034c1e005,0x2c02a374030120242982003f0560cc15021008044a380d01a4180600a),
  (0,0x311a2000030241a20b81a03e0264201d8eb14a08089a04408ba0888ae),
  (0,0x2c02a00c0302b024008010010b6014188560080fce59060ecba85b2e9),
  (0,0x5102a00c03024024414e298734e0b825aec02611c1981002013575811),
  (0x7a25421e885,0x4c07600d768120240a00100102602d4f29e4fca80bb810020010089d8),
  (0,0x2c02a2c8030120240b81905b02693d0620c416829278e11c22941000a),
  (0x7c07481ec15,0x5106200c0303b0620b8010010260141883b14a0452790620c46023978),
  (0x104520800f421fc35287e07481f415,0x510a600c21012024008010010261480801009a0440580001a83823aee),
  (0,0x5106200c0301202451d782ef396008010010642cc19810020010a9040),
  (0,0x2c02a2c80302b02a0081905b0640cc2b05600813ca3a0841072c5b1ca),
  (0x13cd6,0xbd57a0825e68991a2f20fe1f9122f142c854e09e0)]

def r6_12 : List Hint := [(0,0x2c02a2c80302b02a93d729ff1420b84d057026875278ac1a6284052f6),
  (0,0x8a113a2644a1fd1223342c704f02213d68810faf7),
  (0x81d88f105015c014006,0x6d0d99b203c6c4d82fc5f6be97c81c3566a80d2f8),
  (0x1d8a9,0x250a600d7e9c530e090090122a6418e298708e72c0801002054814952),
  (0,0x8a0a808244e8991a23342c854e0a250fe1f9122fe),
  (0,0x2c02a00c030120240b8e298707001408010008358a39c530e72c239ca),
  (0,0x510a600d670760ec218090121fc0080100146204c420560ac3f88c011),
  (0,0x2c49e1d8030120180b8012310260142b00c230044188031fe04800856),
  (0,0x250a600c32812024008010010261942b056008044058760ec4603a978),
  (0,0x1a00c0a3c688830b8018db0221a20b96a3005fe04c199b50403ac02011),
  (0,0x2c02a00d278760ec018090120180142b056018460010020028c409811),
  (0x2092d088243482049d,0x2e6060005900060401809b011c608c000ba07c0881981108c38002020),
  (0,0x5102a00c0305102404c010010262c426056008044b29060ec69c3a9a6),
  (0,0x1002000c00012024008010010260002b0560080444688c118280972e4),
  (0,0x7ec0f1fa4927cd2401c48e0692324529a91182243),
  (0,0x2e06200003013048008000010640cc088100081000c0830c206089817),
  (0,0x2c02a00c0301202472c0100139672c3b0763962d8310560ac010a9152),
  (0,0x1a434600c030240480d8010010640140801000810006a0240272ccf9ca),
  (0x2039094c0e405,0x2c02a00c0301202404c258910261882b05600804406b0560a00023800),
  (0x208d1,0x151a2000030151a20080703e0640cc108eb0081004c24c318260888ae),
  (0,0x2c02a00c030120240b8010010700cc2b056008358830760ecba85b2e9),
  (0x1d4e9,0x250a600c120120246e0e298714212c2589102611c080100200111b011),
  (0x20831d4c20c05,0x2c02a00c0301202412c2589102651d82b0560e11c198560ac01008b06),
  (0,0x2c02a00c030120240b82589102693c3b076142938840321fa2941300a)]

def r6_13 : List Hint := [(0x844b422110d,0x1470a200018800006018a9824048008060020020c81995202004002040),
  (0x20405,0x30da1b40100102c0640c80702c0942980c0040304608c11c4b86b800),
  (0,0x2c02a2c80302b02a0b81905b02660104208142c201982f05e2845100a),
  (0,0x2c02a00c0301202451ce29873961981a03407011c198100200a4a90d6),
  (0,0x2c02a00c030120246441a03407072ce298739611c028100200106b152),
  (0,0x3100447c6880d1a4018120321a20093d0ba07c0c8198100803ac02040),
  (0,0x5106200cd030b614018228426120b80100146204c198de0a4bc002011),
  (0x21415,0x600a390280e30860a8510e001a0b81904f07c370678f60143d4798d1),
  (0,0x3319e0ec0a83c1380181984d02a0b80103e0ae04c4610e20c3dc580d9),
  (0,0x4c0b20c18684001629801057044194190f26180800582f1f02886e0e0),
  (0,0x2c02a2c80301202493c3b1ff1420b82585b0268748a02f1c2284050a2),
  (0,0x2c396c38718b201a018159531c6298192b057c0c8028b136a3c802040),
  (0,0x4c61e7141d803334164091530242c4558470cc390080102a404052abf),
  (0,0x2c02a00c030120242985591d0700cc08010008470a39c530e72c239ca),
  (0xe2188d,0x2c00a0d01a803138018090e602a04c190000ae04c4611401438553046),
  (0,0x3302a0406803302404c0100102633c0685b09a344461d119a2c06c9db),
  (0,0x502ac40030ce0240b81000102633c0505b09a344502081ee2c06c9db),
  (0,0x4c622970150dd01a2f02000c088298011791b80881882a46c08553811),
  (0,0x24f02a000031ef02a05926857032420050f214a080500ff15827c4b2e2),
  (0,0x871109eb44e898f43130fe79912312248a451106f),
  (0,0x2c02a2c8030120240b819001026601041d341657019b140202848900a),
  (0,0xc6cf61eb634898f4319630c5d8b1f73c6788e0b15),
  (0,0x2c02a00c0301202404c01001026460e88764161d4588380700106300a),
  (0,0x5107600c03012024c3ce29873962c41a03407011c08010020134a90d6)]

def r6_14 : List Hint := [(0,0x2c02a00c030120241581a11d07072ce298739611c028100200106b152),
  (0,0x2c4121d80a8b201a0ac091ef02a04c011790ae04c840320143c852820),
  (0,0x2c550970150dd01a2f02000b088298011791b80880282a46c08553811),
  (0,0x8a09c830109ed1c01400584307e0447784f0023ac270370d404078811),
  (0,0x5914c47c0a8241901400584307e2993d04f0023ac198100d404078811),
  (0x884a4a21d21,0x2c3000340a803138018091ef0240b80109c12204c19810014040529ee),
  (0x621805,0x3024018010a60260640c80702c1307f05914c0304608c3ba4b802800),
  (0,0x2c02a2c80301202a0b81a05b0b60cc2b0b1008370830761f072c23b1c),
  (0,0x4c0a600c2c812024c75012011420080109102627008010020011001ee),
  (0,0x4c0a600c2c8120241881a0010b6040080100080fc0597c63ec78238fc),
  (0x88a024c22405,0x2c02a374030120240f42000105651d909d364011c1982a0200100880a),
  (0,0x2c02a2c81b0120240b80105702682c3b2cc14273c028561622840880c),
  (0,0x4c0762c82c8241ac298010571d61942b0b106e044058761f002d05322),
  (0,0x2c02a00c030120240b82580102693c3b076646938028560ac294150e7),
  (0,0x502ac94030040240b99202e02633c0508c09a24031a080c618c4a1db),
  (0,0x513961d80a88752c0181215302a2981a18c0ae16c0287664c2c4020d6),
  (0,0x2c06238003012024298278010560cc35010008044a380d3a64182e327),
  (0,0x10410ea58108ff1c60185282c0240446309a00204c4200a1ec16c268d1),
  (0x22d29,0x2c300ca00a803138018159ef0240b8190d512204c1982f014040529ee),
  (0,0x2c062374328400880b8010dc0440cc0802106e04594a5c4b6104e79c6),
  (0x22c05,0x6400c0200b0190320140c8044aa2307c1dd12cca80c09703011c24817),
  (0,0x2c3003e00a8e31fe018161ef0242684d32b00204c678f601416c268d1),
  (0,0x2c3001d80a8b201a018091ef02a268011790ae04c840320143c852820),
  (0,0x2c550970150dd01a2f02000b088298011791b80880281046c08553811)]

def r6_15 : List Hint := [(0,0x2c3001d80a8b201a018091ef02a04c011790ae04c588320143c852820),
  (0,0x2c02a2c80301202a298010570260cc190f214a081278761f0284e7b2c),
  (0,0x4c5b61d9808b252c1640915302a1881a32d0b616c2b05664c2c4528dc),
  (0,0x4e076374030120242c4200010560401501009a0458780d3a641941a7d),
  (0,0x16c10ea58298ff1c60900202c0240098609a00204c2900a1ec16c268d1),
  (0x8d4a4a23121,0x2c3000340a803138018091ef02404c0129f12204c8a010014040529ee),
  (0,0x4c31e2c82c81202a29801057026b843b0f814273c2b0321e40101032e),
  (0,0x3302a0400303302a0b81a05b02633c0685b09a344461d119a2c06c9db),
  (0,0x3302a040030330240b80100102633c0685b09a344461d119a2c06c9db),
  (0,0x2c02a00c0301202a2980105b0b6014188b10080fce59061f072c23b1c),
  (0x22cd9,0x5102a22403024024600db9d420a0b80133002627019810020295979ee),
  (0x108f234223885,0x4c04200cb90120240440100102602d9880d3b2a8034010020010089d8),
  (0,0x2c02a0c40302c0240b82585b02693ce896540e73c02856162294088f3),
  (0,0x5102a0ec2c82407e0b81e85b1d6014260b106e045279061f002d05332),
  (0,0x5107600c2c812024298010010261580801014a044058ca408cd199b32),
  (0,0x2c02a00c2c8240486010921166a0b8010910642cc198100200e0bc040),
  (0xc0d005,0x2c02a2c803012024298190010b60cc2b01000813ca3a083a674423b36),
  (0,0x51674ce40a83b670164121d50840b81eb371223ac198de65c04077820),
  (0,0x100202c81981202a298010570260001c0380083190588c1184bc97190),
  (0x24121,0xa602a05803032024004000010b60cc2001009a0fc249750be3948e817),
  (0x20903b4c2445d,0xd3da1a8068211ba000520403045e4088021b8088000680d40841b811),
  (0x22484d,0x18002a000031ef0240b80002e0260cc0508c14a27c0c0000300604c017),
  (0xe24c5d,0xd3da1a8f68210062d8c10d61accdc088020023bd478680540ec1b811),
  (0,0x14706200003153048008000660640cca9010008100501750c227c89817)]

def r6_16 : List Hint := [(0xc10005,0x2c02a00c03012024378010010641881885600813c7c1060ec72c5b336),
  (0,0x5102a00c09024024778e298720a0b82583402611c19810020011978a2),
  (0x895034c25005,0x2c05600c030120240480104805601408010008044069d33a64182e00a),
  (0x1097234225885,0x4c0a600c120120240080100102602d9880d4fc76417810020010089d8),
  (0,0x2c02a00c0302c02404c01001026594e88766761d4588560ac010088f3),
  (0,0x2c02a00c030120240b801091026600e9ad1416bc0198100202941000a),
  (0,0x5102a00c1b15902a04c0100102634c2985b0083448c1060ec69c3ab3b),
  (0,0x3100c018530a600c0cc0800402251d9e90667ac9c0c04967844c0bae9),
  (0x994a4226121,0x4c67c0341d803138164122d40480080109c0cc0883286a2a43801b84f),
  (0x9a474426511,0xd5aa05405836010b54098160320288b0040080107f86312e0604b33f),
  (0,0x2c1f01d8718031fe018091530482680128e0020c831056680148020dc),
  (0x209c404226c81,0x3410a2a64108fa112018720240240fc2385f00216c270d60200402683f),
  (0x9e4a4a27521,0x4c42603418803138018091530482c40109c0680c8080102a404052840),
  (0,0x2c1c600c0301204815801034064014080100081010420247472c2e1ca),
  (0x27025,0x6a0766342c8220480045d0011701943502106e3719f00d30ed08239ca),
  (0,0xf01c634008ba00201c320190022384808c6862f90300d30e11d031cb),
  (0,0x2e00205018b021380180985b0480cc0883f0200100c1131fcae80c017),
  (0,0x2e06226c03013048004000010b60cc088100080fc0c2a30be0608e817),
  (0xc27c5d,0x2404800c000d61ac008010011de02c3606c11a1ac08010020d10089d2),
  (0x28121,0x20a605812013024004000010b6040088100080fc0c2a30be0608e817),
  (0x20a03b4002865,0xa336094cd0530065ec1202404811cc1034068030bc0650d40841b8d6),
  (0,0xb68c194a9824010001a2834070548080070083582e23b12e0601a017),
  (0,0xb0046380098e0060c8180120242d8668380700e0278cd0ac15802347),
  (0,0x2e05c00c098120480001a0340700140801000835951a3b0be060c8017)]

def r6_17 : List Hint := [(0x828501,0x8a0a29d8298fa1120901c02402400423a7a00216c080d60200400203f),
  (0,0xf01c00c0401202401c08010008238ce19c690580068020020c8200b6),
  (0xb2d4028425,0x6a04200da50240481a01a0340181a03502106e358069c530ed0823b49),
  (0,0xf01c00c0483406801c0c8190682384608c6902f8069c530e11d031d1),
  (0,0x14706200003153048008000660640cca90100081000c0830c206089817),
  (0x5875,0x6a04200ceb84007e728010014ca96d2e25c6842cc3406a0420dca9152),
  (0x42914d20a33b4c2885d,0x336130cd03b0060002c82404811c5303d090454000650d40841b811),
  (0xa6094429405,0x6a04200ceb84007e0441e8481de1a03502106e044069d33a600023800),
  (0x5535,0x34c01600c030240480d8010340640140801000810006a0269672c2e1ca),
  (0,0x1002000c19812024008010010260001c0380083190588c1184bc97190),
  (0,0x2e06226c03013048004000010b60cc088100080fc0c1670be0608e817),
  (0,0x6400c0200b016032600bf8a12fe0cc198a519c028318620c62ec068f9),
  (0,0x6400c0200b0160100cc0380400e4c0ebb4e69a3a0a3a0620c1719380d),
  (0x29c45,0x900c020048160320140380400e0604b81812c05c06b50668d3d938ca),
  (0,0xb68c0c4a9824010934010160325480800700801c06a3b40c97c85a5e),
  (0,0x900c020048160320140380400ed450325f21697806a06396170e500d),
  (0,0xb062d48122ed010009a9016032040ec00700801d1d8ca12e0604b017),
  (0x5d25,0xd06cd58033550100d9aa016032015a000700801da635312e0604b017),
  (0x82a05d,0xb0000c4a982404800001034064548080100081000023b0c206089817),
  (0,0x3600c0901b03406401408004080d303081822605c06ac1396050e5202),
  (0xc2a405,0xf01c00c0406d0da1b41e8481d235c3606c17c1ac069d33a603423800),
  (0,0x2c02a38c0302c0240b84d001026601041d41427501982f020294f700a),
  (0x20dc35,0x2c1a200c0301202416c0100102601408010008044068ca6aecd199327),
  (0x8150b9,0x2c02a00c2c8240489a4e29876b20b82589113411c19810020d60bc15d)]

def r6_18 : List Hint := [(0xc0e405,0x2c02a00c030120241581e8480700140801000813d041d33a674423b36),
  (0,0x2c02a00c030120246003b07614204c01001026c245882f05e284050a2),
  (0,0x2c3961d8718b201a018091531c60c8012b05640c83105636a3c802040),
  (0xc2a8ad,0xa0040b000815006338090120240000989a0ae04c050cd22845061846),
  (0x29111,0x560ac00c038120240a8258910260001c0380083190589011e4bc97190),
  (0x28d21,0x20a605812013024004000010b6040088100080fc0c1650be0608e817),
  (0xc2ac5d,0xd3da1a8f6821006418c10d61accdc088020023bdad0680200401b811),
  (0x2b041,0x14706200003153048008000660640cca90100081001728b0c206089817),
  (0,0x2c02a00c0301202404c0109102682d0120114267c8a010020284f700a),
  (0x82b479,0x2c02a00c030120240b80100102693c3b07650a958028560ac010150e7),
  (0x20af3b442b8e1,0xa3360b0cd01500602c0901202411c1704b12204c05033020040020a2),
  (0x82a805,0xf01c00c0401202401c0801019c0188716c0561ac0680200241810000),
  (0,0xbd5109eb6ba4a94a35c0fe7990c35b248a440d06f),
  (0,0x2c02a00c0301202404c2589102682ce99d3416570c00100202848900a),
  (0,0xc6daf8826348991a3196305318b1f73c6d78e0b15),
  (0,0x2c02a00c090120240b801001026460e88763a0959278380700106300a),
  (0,0x510a600c12012024481519873960e81a03407011c08010020010a90d6),
  (0x2b129,0x51286a1018803138090091530480080109c0cc0c8080102a404002040),
  (0xc2b05d,0xb3da1a8f682100602cc10d61accdc088020023bdad0680540841b811),
  (0x829901,0x8a0a29a0298fa1120901c02402400423a7a00216c080d60200400203f),
  (0,0x120048298120a600602cc10d61ac3c80883d0903bc080680200401b811),
  (0,0x516c0224030121a2044b403e0260a8080eb14a044208472ca734e799e),
  (0,0x4e02ad840302202a0b85d05b0260ccd402f09a288c000d4104158429c),
  (0xb425442cc8d08b221462c47d20b01d4826c55,0x4c04200cb901202413c0100102602d4f00d0168380501002084008a9d)]

def r6_19 : List Hint := [(0,0x6a0422c8b902b0241a0190010261a01781000828805a0830e284ae29c),
  (0,0x2c02a6340302b0241585d0010b6014150100080fd0400d30e72c239ca),
  (0,0x2c02a00c03012024158010010641882b05600813c7c0760ec7445b27b),
  (0,0x2c34600c0302b0480d85d0340640141501000810006a4c23e72c2e1ca),
  (0x22d435,0x510a600c120120240040100102604008010008044058ca6ae9f9b127d),
  (0,0x5102a00c0302402404c010010262c42605b0083448c1060ec82c3a9de),
  (0,0x600a62a41202b02a34c5d03e064040150210081009000d59e72d501ca),
  (0,0x4e0766340302b0242c45d0010b60401501009a0fd8780d30e72cc61ca),
  (0,0x2c02a00c03012024600e298714204c258910268748a010020284050a2),
  (0xb74a4a2d921,0x2c3960341880313801809153048158012b02320c8028102a404002040),
  (0,0x4c0766340302b0242c45d0010b6040150104200fc9029b30e95cc61ca),
  (0,0x1800580340a8ff1c6018f782c0242691889a00204c6780a1ec16c268d1),
  (0,0x4e02a00c0302402433c2605b09a04c01001026344c01060ec41405075),
  (0x82e09d,0x1a00c00346880d0b8018db0221a2269b18ba07c04c029b50403ac02011),
  (0,0x2c1a2224030121a20c8b403e026014080eb008044d004701a680e799e),
  (0,0x2c1a2224030121a20c8b403e026014080eb008044d104723e6802e19e),
  (0,0x5102a00c0302402404c010010262c42605b09a3448c1060ec4158429c),
  (0,0x2e05c00c098120480001a03407001408010008359b223b0be060c8017),
  (0x8120ed,0xa336094cd053006d941202404811c8b0340680e0bc0100200401c0d6),
  (0,0xb68c14ca98240100008b034070548080070083582e23b12e060ce017),
  (0,0xa614c00cc88120240001a03407004408010008359b30610be394c8017),
  (0,0x2c02a2c80902b0240b819001026779041873a06301982f0200105100a),
  (0,0x2c02a00c030120240b8258910269a4e99d3416a84198100200108900a),
  (0,0x51186224120121a2009b383e026040080eb008044208472ca6816019e)]

def r6_20 : List Hint := [(0,0x4e02a6340302202404c5d001026450d401009a2890580d30e414ae29c),
  (0x8c56,0xdc1b788244edb9b6b6c0fe1f9b5b6a3c6d79b4b68),
  (0xc1dc2d,0x4c07600cbc25c4b8c446b0d611a298010016e23bc3406a0420001b811),
  (0,0x7ec0f1fa6ecc5dba81c48e069ba3736e491182243),
  (0,0x1cd062000031530480d9bb919064014a90100081004c0830c206089817),
  (0,0x2c0627f80302c0480d8cc801064014350100081012600d23e72c2e1ca),
  (0,0x5102a00c090240240b80100102633c2605b0083448c1060ec4152b1de),
  (0,0x600a66341202b02434c5d0010b6040150100080fc9000d30e72cc61ca)]

def c7 : Catalogue := (126,79,0xd3338b3a82901fa588019c59d41480fd370b100338b3a82901fa5a163a667167505203f4b118c00ce2cea0a407e96231e9da667167505203f4b100000ce2cea0a407e90e006716750520454fd2c40000338c3282901fa58e7167505203f4b120c4500338b3a82901fa58922006716750520430fd2c400ce2cea0a407e9a4588019c59d41480fd30cb1d4338b3a82901fa588120067167505203f4b102738b3ab4a0a407e9620f0019c59d41480fd2c41ed7b38b3ab4a0a407e963a367167505203f4f62c400ce2cea0a407e9ec58e716756941480fd2c45a00338b3a82901fa588b4006715a505203f4b11680000338a0a407e9622d6719959d5a505203f4b100350ce2cea0a407e94e000019c59d41480fd29f46ce2cea0a407e9620b6999c59d5a505203f4b100338b3ab4a0a405888b9c6216756941480fd2c400d4346b3a82901fa58e8d9c59d41480fd2c445d1b38b3ab4a0a407e963a367167505203f4b118800ce2cea0a407e962316716757d5a505203f4b1ce31eb3a92a0a407e9639c59d49505203f4b115800ce2cea0a407e9622b6716758549505203f4b1ce2cea4a82901fa5882da66716752541480fd2c738b3a92a0a407e9e458e716752541480fd2c445ce310b3a92a0a407e9639c59d49505203f4b107400ce2cea0a407e9620ee718f59d41480fd2c42f00338b3a82901fa5885f9c59d5f52541480fd2c738b3a92a0a407e9ce588019c59d41480fd39cb100338c7afca0a407e9639c655675052a480fd2c738caacea0a407e962138019c59d41480fd2c427ce2cea0a54901fa588300067167505203f4b106352ce2cea0a54901fa588019c66567505203f4b1ce32ab3a82901fa761620067167505203f4ec2c738b3a82952407e962260019c59d41480fd2c44cce2ceb0a82952407e962006716758541480fd2c738caacea0a407e9620b671675052a480fd2c416d3338b3a82952407e9639c59d414a9203f4f22c738b3a82952407e96222e7167569414a9203f4b1ce32ab3a82901fa588440067167505203f4b108b38caacea0a407e962158019c59d41480fd2c42bce2cea0a76952407e9639c59d414a9203f4e22c400ce2cea0a407e9c4588019c65588505203f4b10034cb3a82901fa588bf9c59d41480fd2c46f11738b3ab4a0a407e9622fe716752541480fd2c45fce2cea0a54901fa588bf9c59d41480fd2c47c17c0000338b3a82901fa4c0019c59d41480fd33cb100000ce2eca0a407e9620067167505203f4da2c400ce2cea0a40831fa588019c59d41480fd31cb1ce2cea0a408d1fa588bfac6716750520468fd2c738caacea0a408d1fa58eb19c59d41480fd2c445d4338b3a82902347e9639c59d6050520468fd2c764ce2cea0a407e962018019c59d41480fd2c403ce2cea0a408d1fa5882e0067167505203f4b105f4ece2cea0a408d1fa58801a767167505203f4b1d6338b3a82901fa7c9620067167505203f4f92c738b3a82902347e962250019c59d41480fd2c44ace2ceafa82902347e962006716757d41480fd2c758ce2cea0a407e962330019c59d41480fd2c466ce2cea0a76902347e96200671675053b480fd2c758ce2cea0a407e9620b0019c59d414811a2c416d3338b3a82902347e962006b1a659d41480fd2c738b3ab4a0a408d1fa58801ac59d41480fd2c45fce2cea0a68902347e962006c9ac59d41480fd2c400d9338c4282901fa58801b26717e505203f4b1,0x6555650065555600555566005655550056555500555556006555660065556600665565005656550065555600655655006556460046556600555655005556550055655500556555005565550055555600555556004665550046655500466555004665550046655500555646005556460065555600556565004665650046656500655646005655560055655600565546005655460045655600466646004665460046654600456646005565560055655600556556004665560046655600556546005565460046565500465655004565560045655600456556004756460046664600466555004665550055564600555646005556460046655500466555004665550046564600465646004566460045664600566555005556560055565600555656004656560045665600566545005665450056654500566545004556560045565600455656004765550066555500566555005665550056654600565646005656550045566600455666006665450055556600665555006655460056555600556556004665560056655500555656004566560056555500565555005555560055555600555556005555560055655500556555004655560046555600456556004565560056654500566545004556560045565600656555005555660055556600656555004565660066654500455666006665450057555500575546)

def r7_0 : List Hint := [(0x20392a200d48820310e000b418a028ee0009398a020ce000731880189e0005258a0108e0003218e0085f300109c400007,0x8370ee19c2b84706e09c0b800e0dfdbf37d0fc861be37b106de9bcb78),
  (0x893300214c8008131081f4a8807922081d478007116081b43800690608193fc8060f320173c4a03cce1003318a058af081528c2050a1201327800489608111ec804077380f0f8000c36,0x83722e41c7b8471c4a9c0b8d0e0e31c2083716e28923897101b80d123),
  (0x254bc20951f100b318602cb628242b8008ca62024278208c96001a218206876000b0d8202c26,0x2b511ae81cf88d73ce75ce39b734e65cc39772c861cab94726e480d06f),
  (0x2026364c0983d,0x580540194738a61c2c82404802cc01c530ee91b294738a61c5b3a31660cc08010744650053a1),
  (0x4030f6202a3b800a4e6001b318003086282817c009c17,0x3ae11a6c9ce3ad734e61d6396430e51d5b920341bdd53a9750e9dd33a5),
  (0x2e664a0b591082c3a4c0ac4d,0x5851c06831006270030122a6090c01c5408a345084b0965908f89a08e0cc083a20202840515d),
  (0x364f800d53600344b8008d26083343c6014b620322bc00c4a308121d880c06b102f19c201426303003800bc06,0x2b7766ec846b9f7621c03892a734ec04693b75ea483706f248e480d290),
  (0xe5092038404c0dc6d,0x1666c1299a0a600ca9824024049b300d38a61c508b6746714c39cb018e880801002028405176),
  (0x3e2ec00f4b7101329c601897100621c80f057103b09c80e81f,0x22f77e2080f12a0e0ef89d93a77aef1ddbbb7743b9dcbb876eed9dabb4),
  (0x41474810065003c15420fc35,0x165f81180d2365f0db027024319e08c706829c1c1b504c040778041aca3c001c578072c239ca),
  (0x204e47c01351b004c468012d19004a45c8125132048448811d11004642c21150708463ec0114f7201c39c8108bf003d2ac80d4a720441fc810c7e301c15cc1082f,0x31b6be20805bca792f211323478ef19e2bc408e891e1a1642af08e09e0),
  (0x1498920516048108d92050274c13c3d,0x580540180b38a61c03012024030c01c530e4d89b02e096244000131660cc08010000654050a2),
  (0x2651c80f8ee00363980164da001d31801084620540ac414c27285807c815c1b005605c015413305402c014c07,0x3d4366f4de93ad3606bde89ad430f41d59aa0341bd5abcf79cf35e63cb),
  (0x42694009595,0x2c820cef89c236f58db027024318bc8282d042c099b504c0407780402220dea847676680e799e),
  (0x38684fc019d3b00664dc81953300644ac018d2a00624a40185272860488a17d21080345c2178ff205d3380114c6205c23c816c8e380911cc1683f,0x31b7c4f85f03df7bc078953dd528ae1ee09c7b6861ed3bb7b27d9ec3d7),
  (0x1b199286b6442178e9206a2b4c1a44d,0x5860006815006270030123de048c01c551ea3c5082e0960004881308e0cc08000020284598a2),
  (0xb0d6000a21ce1cc5f007216c81c457007014c017846006f0ec81b83700540ac41b427,0x1b46befb40f1b10e0fb0d73eb7d4fa5f43bb7cef99f13e5792f91f194d),
  (0x5e5140008b5,0x9c054c6806044048c008330e284173ef12204c4e033148040508f31446000698720a20d843ee),
  (0x3839c0050c52879274a1e097007725420808538761f441d47720741d4a1d8090075018c1d005,0x22f366fd80f12a360fd51622b454fd1f9a2b7e4fc40e12435406914bf0),
  (0x8045400c505001539481fccd207e2f4a1f4ad207c294208895387b23481e885287b024c1e805,0x165f81189c2365f0db027024319fc1932d0fdc0980051e035e000b08e6d4130101de0100880a),
  (0x2294f007f53802253e08664d822251e00664588220ef20873b88218ed004a3984214e31084384820caf20822b880a46b302319cc2045f,0xa804c6e00b5f105001ff92a0e011cf3bc5788ff9ecbfd7f8fedfd3f9),
  (0x208e574423551008a424820101208c334c22c6d,0x1466c1619a02a00c058120240484680b38a61c5080005c12c4881301800019810020284060a2),
  (0x20413b800e4e6002a2ec0090b7009115c022856007212ca2404708720ec82403700570ac423c27,0x40981020a0392a0e1019e2bc47fd015fe3fb7f4fe405bca793011c3c03),
  (0x309257402295500324540058c5,0xd408401972024048051c530e2860584b12204c063360200405080c14402ce29871422358440a)]

def r7_1 : List Hint := [(0x209515c825037109309c024c07,0x1b477efb40f1b10e104a08c10454070d586e0348a5dcc0f81d035f8c0c),
  (0x92474a244650097154025845,0x1611c4515a110568ac88618a04a099033320042d9561085540800407e0000000030e72c239ca),
  (0xc268fd08543e40114f500993c4802c853098134600435,0x58aa12e02a1ba0345e040016110c01c50010520b02e0970560a0b608e0cc083a21ce98c050a2),
  (0x309e474015d19004a454027511201c3540270c92023314806885309b1b4404055,0x167b4351ed04200c059821ac358001ca38a61da10b639412c48af608ee887381002098c050a2),
  (0x165ad0011394a28c6d20a2194a2845d00a0154227c35,0x167381180d236510db02705631a0c4171743f82d9b504c0a87780407e3b85b00d78072c239ca),
  (0xc29d0d006f42401850500a64048294bd00a42c4c01c55,0x340180068d101a170031b6044344c00000ea9b45082e16c9b08601308e0ce0dc1a832284050a2),
  (0x307247421c919006645402a111080339400bcb53003194600035,0x165f81180d2365f0db0270243180027938af0050c1516c12e0a81308f06d3c010302284050a2),
  (0x3045482bc4d08ae114a2b42d00ac094a2ac1d20aa054c2a405,0xa22200188602404a0f1c530e284b204b12204c23c1d0200405080a14402c6500d4fc2345b41c),
  (0x8b722c02d88720b51ec02d07738b31bc82c86b00ac19c02c46330b009cc2a417,0x42a2a10a6143ad0e109dd607e430f8e1342584908d19c228430820f88d),
  (0x9d3608bb32c02e8c720b92ec42b0b720b81ecc2a87730b907802b01630b803882a806,0x42a5e90a5aebad0e0535d63c985abc9d642c524235adbab0dc06a15a90),
  (0x22ad4600ab4d8a2f49720bd21c42f077,0x4345e8209ae92a0e10cd8c14c2963ba194318610bd78a1642a7d58ac2e),
  (0x28c12c04300a800c6218a3148000c41f0030c7808c21d082f85c10ae160e3044000c00e002fc1830be04002b808,0x10e9109eb5910e54a2c70fe79a1c2c686ea461b435),
  (0x338e730cd2bc0330ab20ba29c032ca300ca26ca2d89708ca22c82d88730c917cc3205738c711cc31c37,0x31b6be2098d226469111dc3b7886f8a214418810fe1f43d8787061d8ee),
  (0x340f008af3a02340e000af360033cc8,0x111e234456348991a3196305318b1f73c6d78e0b15),
  (0xd255402e0c500d01f442f87520d0134a2f84520b8094034405,0xa2220018860240487983d0900ac4201002001008c4a3a674c8304701402c6500d4fd1253ec48),
  (0x3518920cf13422fc4528d30f402d03520b0094c2c005,0xa222001c4b0ec1d843012024030818020028c4098840ac1580611802202c6500d11ac1d501d6),
  (0xc614a3544d00b6114231c35,0xa30783b164164034430123de054818022f215c09c4e064028790a504002c6508d89a9f95044c),
  (0x29694035d99001b614a3584d00ba114232035,0xa312942239006270430122a609227802138198190840205480800408002c6508d6ae9f999a7d),
  (0x324b508d9194236005,0x460c4c682705604a0b8ba00216c1302a0200101f80b3743f93f4514faa300698739611ce5450),
  (0x36d3e00294d80348bb10302dc43486e0030198a3685f20ce0dc231835,0x4578ad0a494bad0e0235d613a52448dd586e034a41d53a98ab15229c52),
  (0x3854b001c51c2380ff20df27c03789300dd1d8037075,0x2b9570adcd988345c07838071360ada2c8838b0e280e06e0de6a80d123),
  (0x20e42bc838ca708e225c038887,0x31b6be2098d226468c658c14c88717e2f45d8b916cfba1642a7058ac5a),
  (0xe5394810c9d,0x5805401a4f0ec1d80301202403001002003180e59cb0ec1d8002ea16c0142b056018460a92d1),
  (0xe8624839d8120e63b481108d00e5204c3983d,0x580540180b38a61d278760ec3b8030120240014f02e096244238b60260142b0560004d88c011)]

def r7_2 : List Hint := [(0x3b4e600ec11423b03510e909c03ac1f00ea05c03a407,0x42a4426c9643ad528b1dd61e6430b19d5a910341be32c648c70c231461),
  (0xf06e483bc5500ee11423b835,0x510180068d101a170139b60443441429f1740f80982636a0807580402202c000000009f95027d),
  (0xe13582384c620ef15c01105600f20ac43c42700f607c83d41b00f405c03cc1310f202c03c407,0x1b48d26c80f1b13611a0d71ad430070d59aa0341bc5b2b58cef36333cb),
  (0xf06f40111b5,0x171ad47c6a106170031b60443441729f1740f80983336a080758040222d84685c1aa680cf99e),
  (0xfa664a3e59120f84f4a3c93900454d403dd31,0x5851c06831006271278760001d8030122a60c006002004270332311340142b15205e0308c04f),
  (0x28fc0f403ec35,0x58054c6a4f0ea1d80302b024030008ba0031b02b805054158061181b851c069871dc72c239ca),
  (0x4098929012f40400b521012b42400a500ff27403f89520fd214c3f405,0x5805401ad90ec1d8030120240304d0020028c40980d01a034773070180142b05601846008b06),
  (0x210457403d559004a554040d5120ed22480d485,0x1666c1299a0a600c000760ec1d8a98300240480604722c0d01a00c396548178560ac0308c152),
  (0x42189010760400f4e521060f4041435,0x580540180b0ec1d8030120240301b0340691b4e58050ac158061182a4034e29871dc72c239ca),
  (0x210b1748428550109114242435,0x340180068d101a170031b60443441b2d4600bfc1c00536a080758041ac034771ba37272c239ca),
  (0x29154fc04513b20614dc844d3301124ac044527080745c2440ff210c33c843c8e290e228011486010d208c4303f,0x31b8ed1d63a4738e51c5133c73d079c3fc708de892372167847d8e09e0),
  (0x24412921163f4c4584d,0x5893c3b0151640352787651ea3c030120000486502e0045e42ba310260142b0000ac3288c011),
  (0xa4785f00a716c847457011c14c044046011b0ec846837291907c83c81b011805c045c13,0x47c6bf0a63dc7a46879dd607e4491e5f42153827823b47884b17211c77),
  (0x44175,0xa205401a4f1061d8031590243f8170020028c4098058fa1587f11802293c830761064603a978),
  (0x841cef10a42dc8494af21242b4848ca70122294c4847d11201dc847c7500a40588484090120018c47c05,0x1b43666c80f1b1360bf17dafa5f23b95ac677e4fc40e1ab3540697c3f0),
  (0x12b4140378f508de39484a8cd012931484a0bd31272348498852127024c49805,0x340181478d1106170031b60443441746d9011fc0980b00059e3f00b08e0ccda8201d60100880a),
  (0x213253c04c54b204a51c84c143012f4bc04b92d092f43c24b90d212c3784184d6212d27c84a09e312c138018446,0x4828f820cf628f36407a40bad528ae0063ac3cc8600e42b756a440d06f),
  (0x12d52484ad412133474c4cc6d,0x1a3fc160ff02a00c4680b0ec1d8000060240480623102600800a31026000028560ac0308c011),
  (0xd453822954608d44f802953601083a80408e2213815c04b45600a712ca4dc4708a70ec84dc37013607c03d41b013505c04d013,0x4859082098d22646920c3f87e4487910b21538278005c7584b17211c77),
  (0x13963404b58500df554437cc5,0x4a14c0180d0ec1d846012024030010020028c40982d0ac1580611802202c3b07611a4603a978),
  (0x213c17c84ec57113a09c04e807,0x1b43666c80f1b136122608c88296070d59aa03452643c0f90d0355e40c),
  (0x213943404e055013d11424f435,0x340181478d1106170031b6044344013631740f81903336a0807580408051c0000000072c061ca),
  (0x211b534046d49011151404f941,0x340180068d101a171278000ea9b4031b604e4300602e53e2e81f231026014da8261680308c011),
  (0x194152c00254709414ec402537294033c04fcb70001198e5004f113f09c400407,0x494927171afc9292324041c8f91c79d0c48d0fd23245b7c106dea45378)]

def r7_3 : List Hint := [(0x39452bc8510a7094325c450877,0x31b93926c0f12a9352664c49745517e2f49681afc4fba163ec7d58ac95),
  (0x518f5205b2b4403415,0x5893c3b015164270030123de054530347f127c2d9cb0ec001751cb08e4201900a1e42964f49d),
  (0x14a664a5259109484f481709d0146244c51c4d,0x5860006a4f0ec3b80a8b2000034030123de7bc0a82e00427023857026420190001ce3c852820),
  (0x395017c853c57214e0dc25340d014c01cc52c05,0x4a96bf2a18d4a746929a52ca462c0725186e44528a43c0f81d285f8ca0),
  (0x39564346554550154114854c250952034e54405,0x550138238153da3802800b0860fc534aa09e0047583346c1a8080f102251c000003a60002380a),
  (0x1413d8001067215515c017056009a12ca57447015c0ac456c27195a07c05641b015805c055c13,0x13e9391ce5912a9632c03fc6f4312be571f695b2b005c7592d011e64ab),
  (0x559ad005c694003985,0x980343b3281643f82c8123de054530022f215c09cb4064030790a504002c3b08d5d4284e7cb3),
  (0x19605f485717900615d4057d71095e534c02455,0x28e14423a4f0001d80acb710e034031530487bc0a80108e9ea360570b64225b0760143c852cb5),
  (0x164664a58c4d0162114c58405,0x5893ce70159720340302b3de054008ba8d815c2d908040028790a596a51c068ee93e72c23cb8),
  (0x29672f40598b501692b405a0a50965254459c8d2166214c59405,0x586003b015164034030123de0544d0022f215c0980d01a3ba2680b0184201900a1e4294104b6),
  (0x196b634056589006661405a9810805514c01405,0x1666c128000ec1da5d106164034a98240247bc0a84722c0d16a49f0711383b0320143c8528ca),
  (0x10061d485b84d016d114c5b005,0x586003b015164034030123de0541b0345a927c1c108064028790a5194034e28ee93e72c23cb8),
  (0x25c13d210c3b4c5bc4d,0x5893c3b24f0ec4d80a8b200039c030120184d80a82e0045e4bc857026420190000143c852820),
  (0x9851c0590da000819ce5e05f009a16c85dc57017614c04304601750ac45d027397307c85701b017205c05c413,0x3d4938f4c0f3ad93479de8cbd4312f1f41f69772b23b47892cf91e64ab),
  (0x10c6540500b5,0xa293c4181597e270030243de054170342f215c0990897c3cc790a504093c830835d4414e7cb3),
  (0x19755f405d57901115d405e571093f35444fc45,0x55013806a4f00130c0acc29840342800b087304b202e66e13cbc8571d6422600b30143ca60020),
  (0x5fd99297e64405f579297c5c425ed3d217a2b4c1683d,0x586000694701aa7818803000590030123de54c12002004000b20660640cc0800a53c04052840),
  (0xad47000f19c01684600f80ec86143721600ac461027398307c86081b018105c060013,0x3d40e70a6643ad0e131dd607e431319f44c5988de1f1c7884af9211bce),
  (0x169a52187574061951,0x1e620caa0ff02a00c0583604804918813004004098f322d3241c00418c20c8c1060ec4143ab3b),
  (0x2982634460989006661406298101895a4a621612189474462111,0x1a3fc160003960347f8e30062700583602454c122311340084e0660640288b0385a81d80230c),
  (0x63d5d118e544a6346d218c194c62c05,0x1a8c4160ff02a6340583605604a360571740042d80a22c3181c0041ea3b8e580d30e72c23cca),
  (0x8640df0010198c6405f20dc054404007,0x45c9a133e494911042366736e6da8624687f0fcdae6688d99908665c1f),
  (0x645690991534037535,0x28e144239472cea1018a8d01a2700315304854c1214708e47c4e11f3960cca90102a404002152),
  (0x1145ca6483f,0x1b456d34df01b21dc078d8929528070d592352206a44c0f9a4c5ca5cd1)]

def r7_4 : List Hint := [(0x1975e486597101955a4a651610993574204945,0x1666c12b6401a0354680d006270a982402454c120470cc2ac060661c8548080102a4040022bf),
  (0x19b5744669510199474404c750040194c66005,0x143fc160ff02a00c05836024049e08360680d01c00a2300e01c004018a78831c530e72c23cca),
  (0x82d3a000b4d800f932006688c019422006387c09881e026386c01881a0005c56,0x13666c4459aedb9b6cd69ab351b59e43c6d78f09e0),
  (0x46193e097c4d866191e017c458c680ae019f2a80678a6019d288006066319c17cc4b85d,0x1369c33826fcde1042366eb6e6db3726d87f0fcdad4f4da3c6d78f09e0),
  (0x19c67404bd6909a25348684bd,0x28e1440014710620c188000062700315304854c120020000084e0660640cca90102a404002040),
  (0x863ce01189360866cc001952e040b898318f24006248800fa1a000b85801a8140069c4c01a612006944401a40b0468c2811a4030068c08,0x7ee749fa9d07ce73ce648f0da72a453e739271ce2),
  (0xa6b14f01ab52c06a94701a950c006537018743845f506118727805f496,0x4827c03b80f481528ae147ceb43007215a910341bd228839d491182243),
  (0xd753c026d47115e4180644d6015e258a6c05f009e16c86bc5701ae14c04bc4601600ac46b427116002c06b407,0x4f03d8f4c0f4ef528ae2771e643007276a910341be413e529b0b55acec),
  (0x4bd9500e05d4064105,0x5851c418319e22700302c2a6090010bd138198190330d45480800408051c068837dc72c2e1ca),
  (0x658e709b225c06c88711b11dcc08005,0x12d0e62080f12a0e13d18c14c2973ce2f45d81b16cfba1642a7d58acf2),
  (0x21a957446755101b34548208cd101e054c08405,0x143fc160ff02a00c0583602404a301cb004004190005d41d83b1cb16c0288b038070012404f5),
  (0x1b76b4a6d9a100835e486cd7101aa5a4a6796109b557486d0cd,0x160341288d01a034000310063f8a982402454c1200000400806066064548080102a404002040),
  (0x21993b8065ce621ba15c020c56009e12ca6e44701820ac46e027118202c06e007,0x4fb3d87b00f12a5293ea7ccf7430070922910341bc06cf89ef0b67b4ec),
  (0xa6edad008369406ad9901a0644007d85,0x5802c069b80063f8030122a60923580201819819005020548080040800350108d69672c2e1ca),
  (0x2706621c015ca6fc4721bf0dc06f80d01bd01cc6f005,0x502a022098d2264694027fcfe62c0709206e4453f5dccfc81d285f8ca0),
  (0x1bb47406b0cd019f30446e86501c4154870c2501c2034c70405,0x167b4351ed04200c059821ac35a5501107a1207780a0d004008037022000001d33a60002380a),
  (0x39c92bc0720ab218c29c071ca309c622c05888721c51ec03ec77318b15cc58437,0x5096bf4200f5070e141a82d04a06f8a133c98090fdde422776ee98a8ee),
  (0x7349b296225c27348b216221cc7306f21cb1ac02886701ca18cc27c17,0x2282a020913a2646909c3f87e4491723ac2588108d19ccc8427060f88d),
  (0x1cf36c2630d709cf32c0630c731ce07802881630d9038828006,0x3706de20913a2646942de53c9448db09d93a448235ad9240dd42a15a90),
  (0xa12dc27444701d10dc474027,0x2282a0208a792a0e053a8750d5f28cd0b2153eac56864fc81d03446bb4),
  (0x74805,0xd4084c68060560486e0ba00216c3402a0208401f80b666768064514fa7280698739611ce5450),
  (0x2758d001d5320a750b011d32a045989839d4100074c3801660a0040018,0x8a0a851129f0e68814e630530a594a86f43e1b149),
  (0x760db096835c2760cb016831c875cbb00fe2dce5944731650dcc3f427,0x2282a0208a792a0e0e1e3ac258085398c14c29744d19c3d8794487743b),
  (0x404c809672a0059c98,0x8a0a844529f45288433630530a5a3342c854fab15)]

def r7_5 : List Hint := [(0x771ad21db47447691121d9334c2045d,0x53c0000599b336094cd19a0a600c059530480480900016c4581a0340700294f010020040020d6),
  (0xdd4708db4f800d136019335802044601040ec877837016b0ac477427116b02c077407,0x519908fb68c1b10e145cd7516715454d586e03448ca6be57930b5e74ec),
  (0x8169400cd95,0x2c820c7819a0a6634a98240560484e116a340d01c1520200a8080041ac20df700d30e72d9d9ca),
  (0xecb7004029c07809b096d25c27808b016d21c877c7b01051dcc66057396c11cc5b037,0x12d0e62080f12a0e1471dc3b776d46de53c98090fdde3bb776ee98a8ee),
  (0x7989b296d25c27988b216d21c87947b21e41e8878c79010a1dc47887211e11c4010067310909cc0fc17,0x2282a020a8f92a0e08943f87e4310fe3ac25a3d47519ccc8430820f88d),
  (0x1e74f8a10136083c498279d1e204045800f10621e73b84100e6303c19cc79c5e004015880f006,0xee8050d200af4105205ae92a0e02369050ea1abe615b5b2481b80d2f8)]

def c8 : Catalogue := (9,69,0x19c59d41480fd2c416d3338b3a82901fa58e7167505203f4f22c738b3a82901fa5888b9c59d5a505203f4b1ce2cea4a82901fa58e71675052a480fd2c738b3a82901fa588bf9c59d414811a3f4b1,0x6666660066666600666666005766660056766600567657005667570067665600566667)

def r8_0 : List Hint := [(0x7d50081e520207d40001e4e0007528201c480006d18081a4200068f830193c0c060ef00173b00058eb00153a00050e720133908048e300113700040db080f3602038d708113302040cb000f3200038c7200d2f08030bb000b2e00028b720092c00020ab00072a08018a7080526000148820041ec000c7820021dcc00457380011cc00037,0x44788d11674d14a20f8a94527a4d49692523a44a79de3bb776ee877521),
  (0x44d840a0f8002b39820a8cc00293200098bc101f2e000a08800271e0409870001f1a080943d20240dc208c35102009ca0881f002105c008007,0x52fa5d0a696bada214b1d64d48714add5d0f86d0d441d2aa530c231461),
  (0x9d50281d520209d40201d4e0011928204548081111f004347001091b0041460810117203f45080f913003d43000f10b083b42020e907083d3f020f0fb003b3e000e8f7202c39c80e4b000382b000dca8003629000d49c083426020d48c003422080cc8020321f880c47c20301e800bc78000a1d800b874002d1c8c0b057,0x44788d1163b533a64f211323453c79e6acd4a62891e1a1642a4da981e0),
  (0xa150281a520e13140384b4fc01393c004d4ec812938200e4dc81253420484cc01592c00554ac815128203a49c20011720503c0813ce800573608158d020553380150c8003a318211cb620532c0014cac00522a00144a40050270013c98204e24081348e184c230612c8a004a220003886004921001208220281b0406868304711cc00007,0x4478ed4ce3a47353d3a68a53696279e6ac708df0e25e53551f4d25dcac),
  (0x29540a06d48286f500a1b93f006d4f001b13b006b4e0805137206a4d081a53300684b0019d2b00664a801952900644a00101272863488a18921080145c20b107205c3c0416ce8184f3608168d020593384160c8100e3188184b000602a0017c9b005e26081749710051a0c17060005b160213c48305a100c1643e00580e00038360034060001408,0x4479054fdf053e1dd3a68a53d5294f29da8f9d74ea73539a70a461b537),
  (0xa940001c4e001d120105c4604140f8005f31c41d0b0005c2a001408800351e0a1cc5f207215c81c437107009c01c007,0x1b488cfb6749b1a2150ea1541455398d5d0f86c8a643d4081d03441c0c),
  (0x20364a061450810513e0a1dc9d287625c01d495207723481d887087521441dc7d10761dc81d475085112001443800360a001dc090076018c1d405,0x2282a1114a7d14a205398c14c297515f9d447e4af0a5539a1f0d8a4bf0),
  (0x7a50001e53e28784e0a05136002b4b8a01d28080649821e920087947881e118201445820ad0e200742000190620373e081e8f020793b841e0e81014398c180d818523204148b80860220018078202b1ac401c68300619cc1e860307917801e058001415881804808520e00148280037060c0ac0e0007020801806,0xeeaa153ea754d88b4f6a6514a20236a5d4aa935229c547a7343e1b546),
  (0x20254800094e000e5281061460614d0810533e04020b700612a0214c98005322000e078000819801f457287c11c81f037107b09c01ec07,0x555aa9116a9d14a2154a8750d5f35469cd0f86cbe151cfc81d03446c0c)]

def c9 : Catalogue := (1,59,0x67167505203f4b1,0x677767)

def r9_0 : List Hint := [(0x13c0a000e808013808000d820023208014c030042e0600ca810032608020900008230001c88000621000147c08041e020146c00041a080045c1000160c014502004120200c3800030a00008183001040000008,0x111e234459d3452881e79ab3521c4e6a7343e1b435)]

end PEqualNP.Outside.L_meta_14796.Bridge

namespace PEqualNP.Outside.L_meta_14796.Bridge



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
theorem ok2_0 : ck c1 c2 1 0 r2_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b2 : ban c2 2 c2.1 := by
  have p0 := empty c2 2
  have p1 : ban c2 2 2 := more b1 p0 ok2_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3_0 : ck c2 c3 2 0 r3_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b3 : ban c3 3 c3.1 := by
  have p0 := empty c3 3
  have p1 : ban c3 3 6 := more b2 p0 ok3_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4_0 : ck c3 c4 3 0 r4_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4 : ban c4 4 c4.1 := by
  have p0 := empty c4 4
  have p1 : ban c4 4 16 := more b3 p0 ok4_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_0 : ck c4 c5 4 0 r5_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_1 : ck c4 c5 4 24 r5_1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_2 : ck c4 c5 4 48 r5_2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_3 : ck c4 c5 4 72 r5_3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_4 : ck c4 c5 4 96 r5_4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_5 : ck c4 c5 4 120 r5_5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_6 : ck c4 c5 4 144 r5_6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5_7 : ck c4 c5 4 168 r5_7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b5 : ban c5 5 c5.1 := by
  have p0 := empty c5 5
  have p1 : ban c5 5 24 := more b4 p0 ok5_0
  have p2 : ban c5 5 48 := more b4 p1 ok5_1
  have p3 : ban c5 5 72 := more b4 p2 ok5_2
  have p4 : ban c5 5 96 := more b4 p3 ok5_3
  have p5 : ban c5 5 120 := more b4 p4 ok5_4
  have p6 : ban c5 5 144 := more b4 p5 ok5_5
  have p7 : ban c5 5 168 := more b4 p6 ok5_6
  have p8 : ban c5 5 185 := more b4 p7 ok5_7
  exact p8

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
theorem ok6_14 : ck c5 c6 5 336 r6_14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_15 : ck c5 c6 5 360 r6_15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_16 : ck c5 c6 5 384 r6_16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_17 : ck c5 c6 5 408 r6_17 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_18 : ck c5 c6 5 432 r6_18 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_19 : ck c5 c6 5 456 r6_19 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6_20 : ck c5 c6 5 480 r6_20 = true := by decide +kernel

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
  have p14 : ban c6 6 336 := more b5 p13 ok6_13
  have p15 : ban c6 6 360 := more b5 p14 ok6_14
  have p16 : ban c6 6 384 := more b5 p15 ok6_15
  have p17 : ban c6 6 408 := more b5 p16 ok6_16
  have p18 : ban c6 6 432 := more b5 p17 ok6_17
  have p19 : ban c6 6 456 := more b5 p18 ok6_18
  have p20 : ban c6 6 480 := more b5 p19 ok6_19
  have p21 : ban c6 6 488 := more b5 p20 ok6_20
  exact p21

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
theorem b7 : ban c7 7 c7.1 := by
  have p0 := empty c7 7
  have p1 : ban c7 7 24 := more b6 p0 ok7_0
  have p2 : ban c7 7 48 := more b6 p1 ok7_1
  have p3 : ban c7 7 72 := more b6 p2 ok7_2
  have p4 : ban c7 7 96 := more b6 p3 ok7_3
  have p5 : ban c7 7 120 := more b6 p4 ok7_4
  have p6 : ban c7 7 126 := more b6 p5 ok7_5
  exact p6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8_0 : ck c7 c8 7 0 r8_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b8 : ban c8 8 c8.1 := by
  have p0 := empty c8 8
  have p1 : ban c8 8 9 := more b7 p0 ok8_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok9_0 : ck c8 c9 8 0 r9_0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b9 : ban c9 9 c9.1 := by
  have p0 := empty c9 9
  have p1 : ban c9 9 1 := more b8 p0 ok9_0
  exact p1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (hard : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset) (k : ℕ) (run : build raw y k base.toFinset) : 10 ≤ k := by
  have denial := b9 0 (by decide +kernel)
  have eqBank : entryBank dict (rowAt c9 0 (0,0)) = base := by decide +kernel
  have eqDebts : entryDebts masks (rowAt c9 0 (0,0)) = ds := by decide +kernel
  rw [eqBank, eqDebts] at denial
  exact cert_lower (by decide +kernel) (by decide +kernel) (neg := neg) (by decide +kernel)
    hard denial run

end PEqualNP.Outside.L_meta_14796.Bridge

namespace PEqualNP.Outside.L_meta_14796.Bridge

def sampleRow (code : ℕ) (i : Fin 64) : Fin 64 := ⟨(code >>> (6*i.val)) % 64, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h0 : Hard y 0x5555555555555555 7 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xfbceb8db4cb0bacaa89a48a079c69859449038c288184080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) Bridgepaw.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h1 : Hard y 0x3333333333333333 6 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xf75f34b65b24e71e30a61a20755714345304651610241200)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) Bridgedis.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h2 : Hard y 0xf0f0f0f0f0f0f0f 7 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xef9eb8cf1cb0ae9aa88e18a06d96984d14902c92880c1080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) Bridgepaw.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h3 : Hard y 0xff00ff00ff00ff 7 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xdd79c7d96986cd38c3c92882d55945d14904c51841c10800)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) Bridgepaw.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h4 : Hard y 0xffff0000ffff 7 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0xbcf9c7b8e986acb8c3a8a882b4d945b0c904a49841a08800)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) Bridgepaw.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem h5 : Hard y 0xffffffff 6 base.toFinset := by
  intro l run
  exact lower_by_sample (sampleRow 0x7de75c6da6585d65544d24503ce34c2ca2481c61440c2040)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) Bridgedis.lower run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem startDebts : ∀ d ∈ ds, Hard y d.1 d.2 base.toFinset := by
  intro d hd
  simp only [ds,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end PEqualNP.Outside.L_meta_14796.Bridge

namespace PEqualNP.Outside.L_meta_14796.Graph

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev V := BitVec 68
def ops (a b : V) : List V := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
abbrev basicOps (a b : V) : Finset V := (ops a b).toFinset
def inputs : List V := [0xcaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0x20000000000000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xb0000000000000000,0xffff0000ffff0000,0xffffffff00000000]
def truth : V := 0xafffefefeffececa0
def goal : V := ~~~truth
def es : List ℕ := [0,3,1,4,0,5,2,5,3,5,1,6,2,6,4,6,0,7,1,7,2,7,3,7]
def target (x : Fin 8 → Bool) : Bool := decide (∃ i < es.length / 2,
  (List.ofFn x).getD (es.getD (2 * i) 0) false = true ∧
  (List.ofFn x).getD (es.getD (2 * i + 1) 0) false = true)

def circuit : List Gate := [⟨.or,[0,2]⟩,⟨.or,[2,4]⟩,⟨.or,[4,7]⟩,⟨.or,[5,7]⟩,⟨.or,[0,11]⟩,⟨.or,[6,10]⟩,⟨.and,[1,13]⟩,⟨.and,[8,11]⟩,⟨.and,[3,12]⟩,⟨.and,[9,6]⟩,⟨.or,[14,15]⟩,⟨.or,[16,17]⟩,⟨.or,[18,19]⟩]
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
  · change reachable av (BitVec.allOnes 68 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : V) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 68)
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

private def bit (k : Fin 68) (z : V) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List V) (i : ℕ) (k : Fin 68) :
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
theorem action_spec (w : List V) (g : Gate) (hg : legal g) (k : Fin 68) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : V)[k.val] = false := by change (0#68)[k.val] = false; simp
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


def trunc (v : V) : W := v.setWidth 64

theorem trunc_op {a b z : V} (h : z ∈ basicOps a b) : trunc z ∈ raw (trunc a) (trunc b) := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  simp only [raw,words,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  rcases h with rfl | rfl | rfl | rfl
  · left; ext i hi; simp [trunc,hi]
  · right; left; ext i hi; simp [trunc,hi]
  · right; right; left; ext i hi; simp [trunc,hi]
  · right; right; right; ext i hi; simp [trunc,hi]

theorem diff68 (i j : Fin 68) {a b z : V} (h : z ∈ basicOps a b)
    (diff : z[i.val] ≠ z[j.val]) : a[i.val] ≠ a[j.val] ∨ b[i.val] ≠ b[j.val] := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  rcases h with rfl | rfl | rfl | rfl <;> simp [ha,hb] at diff

theorem source_zero {a b z : V} (h : z ∈ basicOps a b) (one : z[0] = true) :
    a[0] = true ∨ b[0] = true := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp at one <;> tauto

theorem forced {s : Finset V} {k : ℕ} (sub : s ⊆ inputs.toFinset) (h : live basicOps truth k s)
    (u : V) (i j : Fin 68) (d : truth[i.val] ≠ truth[j.val])
    (only : inputs.all (fun w => (w[i.val] == w[j.val]) || (w == u)) = true) : u ∈ s := by
  obtain ⟨w,hw,neq⟩ := live_separates (fun v : V => v[i.val] ≠ v[j.val]) d
    (fun _ _ _ m => diff68 i j m) h
  have hit := List.all_eq_true.mp only w (List.mem_toFinset.mp (sub hw))
  simp only [Bool.or_eq_true,beq_iff_eq] at hit
  exact hit.resolve_left neq ▸ hw
def removed : Finset V := ([0x20000000000000000,0xb0000000000000000] : List V).toFinset
theorem project_bridge {k : ℕ} (run : build basicOps truth k inputs.toFinset) : 12 ≤ k := by
  obtain ⟨s,sub,lv⟩ := compress run
  have included : removed ⊆ s.filter (fun w => trunc w = 0) := by
    intro w hw
    simp only [removed,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl

    · exact Finset.mem_filter.mpr ⟨forced sub lv _ 64 65 (by decide +kernel) (by decide +kernel),by decide +kernel⟩
    · exact Finset.mem_filter.mpr ⟨forced sub lv _ 66 67 (by decide +kernel) (by decide +kernel),by decide +kernel⟩
  have paid := Finset.card_le_card included
  have count : removed.card = 2 := by decide +kernel
  change removed.card ≤ zeroCount trunc 0 s at paid
  have eq : trunc truth = Bridge.y := by decide +kernel
  obtain ⟨l,bound,small⟩ := project_live basicOps raw trunc 0
    (fun _ _ _ hop => raw_simple (trunc_op hop)) (fun _ _ _ hop => trunc_op hop)
    (by decide +kernel : trunc truth ≠ 0) lv
  rw [eq] at small
  have cover : project trunc 0 inputs.toFinset ⊆ Bridge.base.toFinset := by decide +kernel
  have need := Bridge.lower Bridge.startDebts l (build_subset small ((project_subset trunc 0 sub).trans cover))
  omega
set_option maxRecDepth 100000 in
theorem binary_lower
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs,legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    12 ≤ binaryCost gs := by
  have width : inputs.length = 8 := rfl
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have sample : ∀ j : Fin 68, target (fun i => (inputs.getD i.val 0)[j.val]) = bit j (~~~goal) := by
    decide +kernel
  have evaluate (k : Fin 68) :
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
  · apply project_bridge
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

end PEqualNP.Outside.L_meta_14796.Graph

theorem PEqualNP.Outside.L_meta_14796 :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  exact PEqualNP.Outside.L_meta_14796.Graph.comparison gates o fits computes
