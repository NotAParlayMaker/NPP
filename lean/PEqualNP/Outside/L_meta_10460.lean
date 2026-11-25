import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10460.Evidence

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

theorem build_mono_k {ops : α → α → Finset α} {goal : α} {k₁ k₂ : ℕ} {av : Finset α}
    (hle : k₁ ≤ k₂) (h : build ops goal k₁ av) : build ops goal k₂ av := by
  induction hle with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem build_mono_av {ops : α → α → Finset α} {goal : α} {k : ℕ} {av₁ av₂ : Finset α}
    (hsub : av₁ ⊆ av₂) (h : build ops goal k av₁) : build ops goal k av₂ := by
  induction k generalizing av₁ av₂ with
  | zero => exact hsub h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih hsub skip)
    · exact Or.inr ⟨a, hsub ha, b, hsub hb, hab, z, hz, ih (Finset.insert_subset_insert z hsub) tail⟩

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn; apply sub; intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := fun hh => sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := fun u hu =>
          (Finset.mem_insert.mp (ht (Finset.mem_erase.mp hu).2)).resolve_left (Finset.mem_erase.mp hu).1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

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

theorem live_map {α β : Type} [DecidableEq α] [DecidableEq β]
    {ops1 : α → α → Finset α} {ops2 : β → β → Finset β}
    {g1 : α} {g2 : β} (f : α → β)
    (hinj : Function.Injective f) (hgoal : f g1 = g2)
    (hops : ∀ a b z, z ∈ ops1 a b → f z ∈ ops2 (f a) (f b))
    {k : ℕ} {s : Finset α} (h : live ops1 g1 k s) :
    live ops2 g2 k (s.image f) := by
  induction k generalizing s with
  | zero => change s = {g1} at h; subst h; simp [live, hgoal]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact Or.inl (ih skip)
    · refine Or.inr ⟨f a, Finset.mem_image_of_mem f ha, f b, Finset.mem_image_of_mem f hb,
        fun he => hab (hinj he), f z, hops a b z hz, ?_, rest.image f, ?_, ?_⟩
      · intro hm
        obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hm
        exact hout (hinj he ▸ hu)
      · simp [Finset.image_insert]
      · simpa [Finset.image_insert] using ih tail

end Live

def ops (n : ℕ) (x y : BitVec n) : List (BitVec n) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
abbrev basicOps (n : ℕ) (a b : BitVec n) : Finset (BitVec n) :=
  ((ops n a b).filter (fun z => z != 0 && z != BitVec.allOnes n)).toFinset
def nrm (n : ℕ) (u : BitVec n) : BitVec n := if u.getLsbD 0 then ~~~u else u

theorem ops_swap (n : ℕ) (a b : BitVec n) : basicOps n a b = basicOps n b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

theorem ops_diff_ij {n : ℕ} (i j : ℕ) (hi : i < n) (hj : j < n) (a b z : BitVec n)
    (hz : z ∈ basicOps n a b) (hd : z.getLsbD i ≠ z.getLsbD j) :
    a.getLsbD i ≠ a.getLsbD j ∨ b.getLsbD i ≠ b.getLsbD j := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail; obtain ⟨ha, hb⟩ := fail; apply hd
  rcases hz.1 with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
      decide_eq_true hi, decide_eq_true hj, Bool.true_and, ha, hb]

def dif (n : ℕ) (w : BitVec n) (d : ℕ) : BitVec n := (w ^^^ (w >>> d)) &&& (BitVec.allOnes n >>> d)
def unionDif (n : ℕ) (ws : List (BitVec n)) (d : ℕ) : BitVec n := ws.foldr (fun w s => dif n w d ||| s) 0
def cover (n : ℕ) (jumps : List ℕ) (t : BitVec n) (ws : List (BitVec n)) : Bool :=
  jumps.all fun d => (dif n t d &&& unionDif n ws d) == dif n t d

theorem bit_dif {n : ℕ} {w : BitVec n} {d i : ℕ} (hi : i < n) :
    (dif n w d).getLsbD i = true ↔ i + d < n ∧ w.getLsbD i ≠ w.getLsbD (i + d) := by
  simp only [dif, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, Bool.and_eq_true, decide_eq_true_eq, Nat.add_comm d i]
  cases w.getLsbD i <;> cases w.getLsbD (i + d) <;> simp

theorem bit_union (n : ℕ) (ws : List (BitVec n)) (d i : ℕ) :
    (unionDif n ws d).getLsbD i = true ↔ ∃ w ∈ ws, (dif n w d).getLsbD i = true := by
  induction ws with
  | nil => simp [unionDif]
  | cons w ws ih =>
    change (dif n w d ||| unionDif n ws d).getLsbD i = true ↔ _
    simp [ih]

theorem live_cover {n k : ℕ} {jumps : List ℕ} {goal : BitVec n} {ws : List (BitVec n)}
    (h : live (basicOps n) goal k ws.toFinset) : cover n jumps goal ws = true := by
  apply List.all_eq_true.mpr; intro d _
  apply beq_iff_eq.mpr; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_and]
  cases hd : (dif n goal d).getLsbD i with
  | false => rfl
  | true =>
    obtain ⟨hj, hne⟩ := (bit_dif hi).mp hd
    obtain ⟨w, hw, hdw⟩ := live_separates (fun u : BitVec n => u.getLsbD i ≠ u.getLsbD (i + d))
      hne (ops_diff_ij i (i + d) hi hj) h
    rw [(bit_union n ws d i).mpr ⟨w, List.mem_toFinset.mp hw, (bit_dif hi).mpr ⟨hj, hdw⟩⟩]; rfl

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

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

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧ ws.Perm (a :: b :: rest) := by
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

def keepChoices {α : Type} (a b : α) (r : List α) : List (List α) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {α : Type} [DecidableEq α] {ws r : List α} {a b : α} {needed : Finset α}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩; ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩; ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

def sameSet {α : Type} [BEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => ys.contains x) && ys.all (fun y => xs.contains y)

theorem sameSet_sound {α : Type} [DecidableEq α] {xs ys : List α} (h : sameSet xs ys = true) :
    xs.toFinset = ys.toFinset := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  ext a; simp only [List.mem_toFinset]; exact ⟨h.1 a, h.2 a⟩

def actN : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p2 :: ps, n => Nat.bit (Nat.beq (Nat.mod (Nat.div n p2) 2) 1) (actN ps n)

def actB (n : ℕ) (ps : List ℕ) (x : BitVec n) : BitVec n := BitVec.ofNat n (actN ps x.toNat)

theorem mod_div_two_pow_eq_testBit (n p : ℕ) :
    Nat.beq (Nat.mod (Nat.div n (2 ^ p)) 2) 1 = n.testBit p := by
  change Nat.beq (n / 2 ^ p % 2) 1 = n.testBit p
  rw [Nat.testBit_eq_decide_div_mod_eq]
  cases h : n / 2 ^ p % 2 with
  | zero => rfl
  | succ k =>
    have hlt : n / 2 ^ p % 2 < 2 := Nat.mod_lt _ (by decide)
    have hk : k = 0 := by omega
    subst hk; rfl

theorem actN_testBit : ∀ (pi ps : List ℕ) (n k : ℕ),
    ps = pi.map (fun p => 2 ^ p) →
    (actN ps n).testBit k = (pi[k]?.map n.testBit).getD false
  | [], _, _, _, rfl => by simp [actN]
  | p :: pi, _, n, 0, rfl => by simp [actN, mod_div_two_pow_eq_testBit]
  | p :: pi, _, n, k + 1, rfl => by
    simp [actN, Nat.testBit_bit_succ, actN_testBit pi (pi.map (fun q => 2 ^ q)) n k rfl]

theorem actB_getLsbD (n : ℕ) (pi : List ℕ) (x : BitVec n) (k : ℕ) (hk : k < n) :
    (actB n (pi.map (fun p => 2 ^ p)) x).getLsbD k = (pi[k]?.map x.getLsbD).getD false := by
  unfold actB
  rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and, actN_testBit pi _ x.toNat k rfl]
  cases pi[k]? <;> rfl

def symValid (n gsize : ℕ) (G_idx G_pow : Array (List ℕ)) (G_inv : Array ℕ) (goal : BitVec n) (g : ℕ) : Bool :=
  let pi := G_idx[g]?.getD []
  let inv := G_idx[G_inv[g]?.getD 0]?.getD []
  let ps := G_pow[g]?.getD []
  Nat.blt (G_inv[g]?.getD 0) gsize &&
  Nat.beq (G_inv[G_inv[g]?.getD 0]?.getD 0) g &&
  Nat.beq pi.length n &&
  Nat.beq inv.length n &&
  (ps == pi.map (fun p => 2 ^ p)) &&
  (actB n ps goal == goal) &&
  (List.range n).all (fun k => match pi[k]? with
    | some p => Nat.blt p n && (inv[p]? == some k)
    | none => false)

theorem actB_spec {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) :
    G_inv[g]?.getD 0 < gsize ∧
    G_inv[G_inv[g]?.getD 0]?.getD 0 = g ∧
    G_pow[g]?.getD [] = (G_idx[g]?.getD []).map (fun p => 2 ^ p) ∧
    actB n (G_pow[g]?.getD []) goal = goal ∧
    (∀ k < n, ∃ p < n, (G_idx[g]?.getD [])[k]? = some p ∧ (G_idx[G_inv[g]?.getD 0]?.getD [])[p]? = some k) := by
  have hv := List.all_eq_true.mp hvalid g (List.mem_range.mpr hg)
  unfold symValid at hv
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, List.all_eq_true, List.mem_range] at hv
  refine ⟨hv.1.1.1.1.1.1, Nat.eq_of_beq_eq_true hv.1.1.1.1.1.2, hv.1.1.2, hv.1.2, fun k hk => ?_⟩
  have h1 := hv.2 k hk
  cases hp : (G_idx[g]?.getD [])[k]? with
  | none => simp [hp] at h1
  | some p =>
    simp only [hp, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h1
    exact ⟨p, h1.1, rfl, h1.2⟩

theorem actB_inv_left {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (x : BitVec n) :
    actB n (G_pow[G_inv[g]?.getD 0]?.getD []) (actB n (G_pow[g]?.getD []) x) = x := by
  obtain ⟨hinv_lt, hinv2, hpow, _, _⟩ := actB_spec hv g hg
  obtain ⟨_, _, hpow', _, hpi'⟩ := actB_spec hv (G_inv[g]?.getD 0) hinv_lt
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow', actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, hpk⟩ := hpi' k hk
  rw [hinv2] at hpk
  rw [hkp]; simp only [Option.map_some, Option.getD_some]
  rw [hpow, actB_getLsbD n _ _ p hp, hpk]; simp

theorem actB_inj {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : Function.Injective (actB n (G_pow[g]?.getD [])) :=
  Function.LeftInverse.injective (actB_inv_left hv g hg)

theorem actB_and {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b : BitVec n) :
    actB n (G_pow[g]?.getD []) (a &&& b) = actB n (G_pow[g]?.getD []) a &&& actB n (G_pow[g]?.getD []) b := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_and, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp, BitVec.getLsbD_and]

theorem actB_or {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b : BitVec n) :
    actB n (G_pow[g]?.getD []) (a ||| b) = actB n (G_pow[g]?.getD []) a ||| actB n (G_pow[g]?.getD []) b := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_or, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp, BitVec.getLsbD_or]

theorem actB_not {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a : BitVec n) :
    actB n (G_pow[g]?.getD []) (~~~a) = ~~~actB n (G_pow[g]?.getD []) a := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_not, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, _⟩ := hpi k hk
  simp [hkp, hk, hp]

theorem actB_zero {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : actB n (G_pow[g]?.getD []) 0 = 0 := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp]

theorem actB_allOnes {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : actB n (G_pow[g]?.getD []) (BitVec.allOnes n) = BitVec.allOnes n := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow, actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, _⟩ := hpi k hk
  rw [hkp]
  simp only [Option.map_some, Option.getD_some, BitVec.getLsbD_allOnes, hk, hp, decide_true]

theorem actB_ops {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b z : BitVec n) (hz : z ∈ basicOps n a b) :
    actB n (G_pow[g]?.getD []) z ∈ basicOps n (actB n (G_pow[g]?.getD []) a) (actB n (G_pow[g]?.getD []) b) := by
  simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hz ⊢
  refine ⟨?_, fun e => hz.2.1 (actB_inj hv g hg (e.trans (actB_zero hv g hg).symm)),
               fun e => hz.2.2 (actB_inj hv g hg (e.trans (actB_allOnes hv g hg).symm))⟩
  have hz' := hz.1
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz' ⊢
  rcases hz' with rfl | rfl | rfl | rfl
  · left; exact actB_and hv g hg a b
  · right; left; exact actB_or hv g hg a b
  · right; right; left; rw [actB_and hv g hg, actB_not hv g hg]
  · right; right; right; rw [actB_and hv g hg, actB_not hv g hg]

def checkChildP (n k : ℕ) (targets : List (List (BitVec n))) (nxt : List (BitVec n)) : Bool :=
  decide (nxt.length > k) || targets.any (fun t => sameSet nxt t)

def checkStepP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (k extra : ℕ)
    (targets : List (List (BitVec n))) (a b : BitVec n) (r : List (BitVec n)) : Bool :=
  (ops n a b).all fun w =>
    (w == 0 || w == BitVec.allOnes n || w == a || w == b || r.contains w) ||
    (!cover n jumps goal (w :: r) || checkChildP n k targets (w :: r)) &&
    ((extra == 0) ||
      ((!cover n jumps goal (w :: a :: r) || checkChildP n k targets (w :: a :: r)) &&
       (!cover n jumps goal (w :: b :: r) || checkChildP n k targets (w :: b :: r)))) &&
    ((extra < 2) || !cover n jumps goal (w :: a :: b :: r) || checkChildP n k targets (w :: a :: b :: r))

def checkNodeP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (gsize : ℕ) (G_pow : Array (List ℕ))
    (k : ℕ) (cur prev : Array (List (BitVec n) × List (ℕ × ℕ))) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hs) =>
    decide ws.Nodup && !(ws.contains goal) && decide (ws.length ≤ k + 1) &&
    hs.all (fun p => Nat.blt p.1 gsize && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [])).1.map (actB n (G_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepP n jumps goal k extra targets a b r)

def checkBlockP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (gsize : ℕ) (G_pow : Array (List ℕ))
    (k : ℕ) (cur prev : Array (List (BitVec n) × List (ℕ × ℕ))) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeP n jumps goal gsize G_pow k cur prev (start + m) &&
      checkBlockP n jumps goal gsize G_pow k cur prev start m

theorem checkBlockP_at {n gsize k start m : ℕ} {jumps : List ℕ} {goal : BitVec n} {G_pow : Array (List ℕ)}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (h : checkBlockP n jumps goal gsize G_pow k cur prev start m = true) (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeP n jumps goal gsize G_pow k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockP, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem checkBlockP_merge {n gsize k start a b : ℕ} {jumps : List ℕ} {goal : BitVec n} {G_pow : Array (List ℕ)}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (h1 : checkBlockP n jumps goal gsize G_pow k cur prev start a = true)
    (h2 : checkBlockP n jumps goal gsize G_pow k cur prev (start + a) b = true) :
    checkBlockP n jumps goal gsize G_pow k cur prev start (a + b) = true := by
  induction b with
  | zero => simpa using h1
  | succ b ih =>
    simp only [checkBlockP, Bool.and_eq_true] at h2 ⊢
    exact ⟨by simpa [Nat.add_assoc] using h2.1, ih h2.2⟩

theorem node_sound_P {n gsize k i : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (hk : 0 < k) (hi : i < cur.size)
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hprev : ∀ j < prev.size, ¬ live (basicOps n) goal (k - 1) (prev[j]?.getD ([], [])).1.toFinset)
    (hchk : checkNodeP n jumps goal gsize G_pow k cur prev i = true) :
    ¬ live (basicOps n) goal k (cur[i]?.getD ([], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hs⟩
  have hget : cur[i]? = some (ws, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeP at hchk
  rw [hget] at hchk ⊢
  dsimp only at hchk ⊢
  simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [])).1.map (actB n (G_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps n) goal (k - 1) t.toFinset := by
    intro t ht
    obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hg, hc⟩ := hhs (g, c) hmem
    intro hlive
    have hinv_lt := (actB_spec hvalid g hg).1
    have hinv_g := (actB_spec hvalid (G_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB n (G_pow[G_inv[g]?.getD 0]?.getD [])) (actB_inj hvalid _ hinv_lt)
      hinv_g (actB_ops hvalid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [])).1.map (actB n (G_pow[g]?.getD []))).toFinset.image
        (actB n (G_pow[G_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left hvalid g hg v]
      · intro hu; exact ⟨actB n (G_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left hvalid g hg u⟩
    rw [hset] at himg
    exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · have hmem : goal ∈ ws.toFinset := done.symm ▸ Finset.mem_singleton_self _
    exact hng (List.mem_toFinset.mp hmem)
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec n} (hpair : (a, b, r) ∈ pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed))
        (hop : z ∈ basicOps n a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps n) goal (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail
      rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover n jumps goal (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair
      unfold checkStepP at hstep
      dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes n || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw
      simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq
      simp only [List.length_cons] at plen
      have close (hc : checkChildP n k targets (z :: kept) = true) : False := by
        unfold checkChildP at hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with hgt | ⟨t, ht, hss⟩
        · omega
        · rw [sameSet_sound hss] at htail
          exact htargets t ht htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept
        have h1 := hw.1.1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.2
        have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap n a b ▸ hz)

theorem level_sound_P {n gsize k : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (hk : 0 < k)
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hprev : ∀ j < prev.size, ¬ live (basicOps n) goal (k - 1) (prev[j]?.getD ([], [])).1.toFinset)
    (hblk : checkBlockP n jumps goal gsize G_pow k cur prev 0 cur.size = true) :
    ∀ i < cur.size, ¬ live (basicOps n) goal k (cur[i]?.getD ([], [])).1.toFinset :=
  fun i hi => node_sound_P hk hi hvalid hprev (checkBlockP_at hblk i (Nat.zero_le _) (by simpa using hi))

theorem no_build_of_root {n gsize k rg : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {rows root_ws : List (BitVec n)}
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hrg : rg < gsize)
    (hsub : rows.sublists.filter (fun ws => cover n jumps goal ws) = [rows])
    (hmatch : sameSet (rows.map (actB n (G_pow[rg]?.getD []))) root_ws = true)
    (hdead : ¬ live (basicOps n) goal k root_ws.toFinset) :
    ¬ build (basicOps n) goal k rows.toFinset := by
  intro hb
  obtain ⟨s, hs, hl⟩ := compress hb
  let ws := rows.filter (· ∈ s)
  have hsubl : ws.Sublist rows := List.filter_sublist
  have heq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hcov : cover n jumps goal ws = true := live_cover (heq.symm ▸ hl)
  have hmem : ws ∈ rows.sublists.filter (fun zs => cover n jumps goal zs) :=
    List.mem_filter.mpr ⟨List.mem_sublists.mpr hsubl, hcov⟩
  rw [hsub, List.mem_singleton] at hmem
  have hs_eq : s = rows.toFinset := by rw [← heq, hmem]
  have hl_rows : live (basicOps n) goal k rows.toFinset := hs_eq ▸ hl
  have hrg_g := (actB_spec hvalid rg hrg).2.2.2.1
  have hrot := live_map (actB n (G_pow[rg]?.getD [])) (actB_inj hvalid rg hrg) hrg_g (actB_ops hvalid rg hrg) hl_rows
  have himg : rows.toFinset.image (actB n (G_pow[rg]?.getD [])) =
      (rows.map (actB n (G_pow[rg]?.getD []))).toFinset := by
    ext u; simp [List.mem_map]
  rw [himg, sameSet_sound hmatch] at hrot
  exact hdead hrot

def jumps5 : List ℕ := [1, 2, 4, 8, 16]
def jumps6 : List ℕ := [1, 2, 4, 8, 16, 32]

def p4h_goal : BitVec 32 := 0xfffeeea0
def p4h_rows : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def p4h_s0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def p4h_p0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648]
def p4h_s1 : List ℕ := [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15, 16, 24, 20, 28, 18, 26, 22, 30, 17, 25, 21, 29, 19, 27, 23, 31]
def p4h_p1 : List ℕ := [1, 256, 16, 4096, 4, 1024, 64, 16384, 2, 512, 32, 8192, 8, 2048, 128, 32768, 65536, 16777216, 1048576, 268435456, 262144, 67108864, 4194304, 1073741824, 131072, 33554432, 2097152, 536870912, 524288, 134217728, 8388608, 2147483648]
def p4h_idx : Array (List ℕ) := Array.mk [p4h_s0, p4h_s1]
def p4h_pow : Array (List ℕ) := Array.mk [p4h_p0, p4h_p1]
def p4h_inv : Array ℕ := Array.mk [0, 1]
theorem p4h_G_valid : (List.range 2).all (symValid 32 2 p4h_idx p4h_pow p4h_inv p4h_goal) = true := by decide +kernel
def p4h_L2 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xeeaeeeae,0xfff0fff0,0xffff0000],[]),
  ([0xeeeeeeaa,0xfff0fff0,0xffff0000],[])
]
def p4h_L3 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xeeeeeeee,0xffaaffaa,0xfff0fff0,0xffff0000],[]),
  ([0xcccccccc,0xeeaaeeaa,0xfff0fff0,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xffffcc00],[]),
  ([0xaaaaaaaa,0xcc0ccc0c,0xfff0fff0,0xffff0000],[(0,0)]),
  ([0xaaaaaaaa,0xcccccc00,0xfff0fff0,0xffff0000],[(0,1)]),
  ([0xf000f0,0xeeaeeeae,0xff00ff00,0xffff0000],[(0,0)]),
  ([0x44f444f4,0xaaaaaaaa,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xffb0ffb0,0xffff0000],[(1,0)]),
  ([0xaaaaaaaa,0xf0f0f0f0,0xffccffcc,0xffffcc00],[]),
  ([0x33cc33cc,0xaaaaaaaa,0xf0f0f0f0,0xffff0000],[]),
  ([0xcccccccc,0xf0f0f0f0,0xffaaffaa,0xffffaa00],[]),
  ([0x55aa55aa,0xcccccccc,0xf0f0f0f0,0xffff0000],[]),
  ([0xaaaaaaaa,0xf0f0f0f0,0xffcccccc,0xffffff00],[]),
  ([0xcccccccc,0xf0f0f0f0,0xffaaaaaa,0xffffff00],[]),
  ([0xffff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0],[]),
  ([0xaaaaaaaa,0xcccccccc,0xfff0ffa0,0xffff0000],[(1,1)]),
  ([0xaaaaaaaa,0xf0f0f0f0,0xffccff00,0xffffcccc],[]),
  ([0xf0ff0f0,0xaaaaaaaa,0xcccccccc,0xff00ff00],[])
]
def p4h_L4 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xf000f0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xeeeeeeee,0xff00ff00,0xfff0fff0,0xffff0000],[(0,0)]),
  ([0xf000f0,0xaaaaaaaa,0xeeeeeeee,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xffaaffaa,0xfff0fff0,0xffff0000],[(0,0)]),
  ([0xaa00aa,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xa0a0a0a0,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000],[(1,1),(1,2)]),
  ([0xcc00cc,0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xffff0000],[]),
  ([0xf000f0,0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xffff0000],[(0,3)]),
  ([0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xffff0000,0xffffff00],[(0,4)]),
  ([0xaaaa,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xff00ff00,0xfff0fff0,0xffff0000],[]),
  ([0xf000f0,0xf000f00,0xaaaaaaaa,0xcccccccc,0xffff0000],[]),
  ([0xf000f0,0xaaaaaaaa,0xccfcccfc,0xff00ff00,0xffff0000],[]),
  ([0xf000f0,0xaaaaaaaa,0xcc0ccc0c,0xff00ff00,0xffff0000],[(0,3),(0,5)]),
  ([0xf000f0,0x44444444,0xaaaaaaaa,0xff00ff00,0xffff0000],[(0,6)]),
  ([0xaaaaaaaa,0xcccccccc,0xf4f4f4f4,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xb0b0b0b0,0xcccccccc,0xff00ff00,0xffff0000],[(0,7),(1,3)]),
  ([0xaaaaaaaa,0xcccccccc,0xfcf0fcf0,0xff00ff00,0xffff0000],[]),
  ([0x30f030f0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffa0ffa0,0xffff0000],[(1,1)]),
  ([0x22aa22aa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffa0a0],[(1,2),(1,8)]),
  ([0x33ff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[]),
  ([0xa0a0a0a0,0xcccccccc,0xfafafafa,0xff00ff00,0xffff0000],[(1,8),(1,9)]),
  ([0xaaaaaaaa,0xcccccccc,0xf3f0f3f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xc0f0c0f0,0xcccccccc,0xff00ff00,0xffff0000],[]),
  ([0xcc00cc,0x33003300,0xaaaaaaaa,0xf0f0f0f0,0xffff0000],[(0,9)]),
  ([0xaaaaaaaa,0xcccccccc,0xfaf0faf0,0xff00ff00,0xffff0000],[]),
  ([0x44cc44cc,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaa00],[(0,10)]),
  ([0x55ff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[]),
  ([0xaa00aa00,0xcccccccc,0xf0f0f0f0,0xffaaffaa,0xffff0000],[(0,10),(0,11)]),
  ([0xaaaaaaaa,0xcccccccc,0xf5f0f5f0,0xff00ff00,0xffff0000],[]),
  ([0xa0f0a0f0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[]),
  ([0xaa00aa,0x55005500,0xcccccccc,0xf0f0f0f0,0xffff0000],[(0,11)]),
  ([0xaaaaaaaa,0xcccccccc,0xff00ff00,0xfff0f0f0,0xffff0000],[]),
  ([0xf0f0f0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xfafaf0f0,0xff00ff00,0xffff0000],[(1,12)]),
  ([0xcccccc,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffaaff00,0xffff0000],[(1,13)]),
  ([0xaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaa0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaaaa],[(1,12),(1,13),(1,14)]),
  ([0xaaaaaaaa,0xcccccc00,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,4),(1,15)]),
  ([0xf0f0a0a,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0fff0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccc4444,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaa,0x55550000,0xcccccccc,0xf0f0f0f0,0xff00ff00],[(1,14)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff30ff30,0xffff0000],[]),
  ([0xa2a2a2a2,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xc0c0c0c,0x30303030,0xaaaaaaaa,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfff0ff00,0xffff0000],[]),
  ([0xf00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xfcfcf0f0,0xff00ff00,0xffff0000],[]),
  ([0xc0ccccc,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffccff00,0xffff0000],[(0,16)]),
  ([0xa0aaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccc0000,0xf0f0f0f0,0xff00ff00,0xffffcccc],[(0,16),(1,17)]),
  ([0xcccc,0x33330000,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00],[(1,17)])
]
def p4h_L5 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(1,0)]),
  ([0xaaaaaaaa,0xcccccccc,0xff00ff00,0xfff0fff0,0xffff0000],[(0,0),(0,1),(0,3),(0,6),(0,7),(0,8),(1,2),(1,4),(1,5),(1,9)]),
  ([0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000],[(1,7)]),
  ([0xf000f00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,10),(0,11)]),
  ([0xf000f0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000],[(0,2),(0,7),(0,10),(0,12),(0,13),(0,14)]),
  ([0xf000f0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,7),(0,11),(1,15),(1,16)]),
  ([0xa0a0a0a0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,5),(0,19),(0,21),(0,23),(1,17),(1,18),(1,20),(1,22)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfafafafa,0xff00ff00,0xffff0000],[(0,23)]),
  ([0xa0a0a0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(1,24),(1,25),(1,26)]),
  ([0xcc00cc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,6),(0,26)]),
  ([0xaa00aa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,27),(0,28),(0,29),(0,30),(0,31),(1,27),(1,28)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffaaffaa,0xffff0000],[(0,3),(0,31),(1,3)]),
  ([0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,4),(0,34),(1,32),(1,33)]),
  ([0xaaaa0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,37),(0,39),(0,41),(1,35),(1,36),(1,38),(1,40)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xffffaaaa],[(0,41),(0,43),(1,8),(1,42)]),
  ([0xaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,9),(0,45),(0,46),(1,44)]),
  ([0xff0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(1,46)]),
  ([0xaaaaaaaa,0xc0c0c0c0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfcfcfcfc,0xff00ff00,0xffff0000],[]),
  ([0xc0c0c0c,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,48),(0,49),(1,47)]),
  ([0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,52),(0,54),(0,56),(1,50),(1,51),(1,53),(1,55)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xffffcccc],[(0,56)]),
  ([0xcccc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,57)]),
  ([0xf0f0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(1,57)])
]
def p4h_L6 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(0,19),(0,20),(0,21),(0,22),(0,23),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,12),(1,13),(1,14),(1,15),(1,16),(1,19),(1,20),(1,21),(1,22),(1,23)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4h_chk_2_0 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 2 p4h_L2 (Array.mk []) 0 2 = true := by decide +kernel
theorem p4h_chk_2 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 2 p4h_L2 (Array.mk []) 0 2 = true := p4h_chk_2_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4h_chk_3_0 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 3 p4h_L3 p4h_L2 0 18 = true := by decide +kernel
theorem p4h_chk_3 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 3 p4h_L3 p4h_L2 0 18 = true := p4h_chk_3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4h_chk_4_0 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 4 p4h_L4 p4h_L3 0 40 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4h_chk_4_40 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 4 p4h_L4 p4h_L3 40 18 = true := by decide +kernel
theorem p4h_chk_4 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 4 p4h_L4 p4h_L3 0 58 = true := (checkBlockP_merge p4h_chk_4_0 p4h_chk_4_40)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4h_chk_5_0 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 5 p4h_L5 p4h_L4 0 24 = true := by decide +kernel
theorem p4h_chk_5 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 5 p4h_L5 p4h_L4 0 24 = true := p4h_chk_5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4h_chk_6_0 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 6 p4h_L6 p4h_L5 0 1 = true := by decide +kernel
theorem p4h_chk_6 : checkBlockP 32 jumps5 p4h_goal 2 p4h_pow 6 p4h_L6 p4h_L5 0 1 = true := p4h_chk_6_0
theorem p4h_L2_sound : ∀ i < p4h_L2.size, ¬ live (basicOps 32) p4h_goal 2 (p4h_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) p4h_G_valid (fun j hj => by simp at hj) p4h_chk_2
theorem p4h_L3_sound : ∀ i < p4h_L3.size, ¬ live (basicOps 32) p4h_goal 3 (p4h_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) p4h_G_valid p4h_L2_sound p4h_chk_3
theorem p4h_L4_sound : ∀ i < p4h_L4.size, ¬ live (basicOps 32) p4h_goal 4 (p4h_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) p4h_G_valid p4h_L3_sound p4h_chk_4
theorem p4h_L5_sound : ∀ i < p4h_L5.size, ¬ live (basicOps 32) p4h_goal 5 (p4h_L5[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) p4h_G_valid p4h_L4_sound p4h_chk_5
theorem p4h_L6_sound : ∀ i < p4h_L6.size, ¬ live (basicOps 32) p4h_goal 6 (p4h_L6[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) p4h_G_valid p4h_L5_sound p4h_chk_6
theorem p4h_sublists : p4h_rows.sublists.filter (fun ws => cover 32 jumps5 p4h_goal ws) = [p4h_rows] := by decide +kernel
theorem p4h_top_match : sameSet (p4h_rows.map (actB 32 (p4h_pow[0]?.getD []))) (p4h_L6[0]?.getD ([], [])).1 = true := by decide +kernel
theorem p4h_no_build : ¬ build (basicOps 32) p4h_goal 6 p4h_rows.toFinset :=
  no_build_of_root p4h_G_valid (by decide) p4h_sublists p4h_top_match (p4h_L6_sound 0 (by decide))

def c5_goal : BitVec 32 := 0xfefceea0
def c5_rows : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def c5_s0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def c5_p0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648]
def c5_s1 : List ℕ := [0, 1, 16, 17, 8, 9, 24, 25, 4, 5, 20, 21, 12, 13, 28, 29, 2, 3, 18, 19, 10, 11, 26, 27, 6, 7, 22, 23, 14, 15, 30, 31]
def c5_p1 : List ℕ := [1, 2, 65536, 131072, 256, 512, 16777216, 33554432, 16, 32, 1048576, 2097152, 4096, 8192, 268435456, 536870912, 4, 8, 262144, 524288, 1024, 2048, 67108864, 134217728, 64, 128, 4194304, 8388608, 16384, 32768, 1073741824, 2147483648]
def c5_s2 : List ℕ := [0, 2, 1, 3, 16, 18, 17, 19, 8, 10, 9, 11, 24, 26, 25, 27, 4, 6, 5, 7, 20, 22, 21, 23, 12, 14, 13, 15, 28, 30, 29, 31]
def c5_p2 : List ℕ := [1, 4, 2, 8, 65536, 262144, 131072, 524288, 256, 1024, 512, 2048, 16777216, 67108864, 33554432, 134217728, 16, 64, 32, 128, 1048576, 4194304, 2097152, 8388608, 4096, 16384, 8192, 32768, 268435456, 1073741824, 536870912, 2147483648]
def c5_s3 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31]
def c5_p3 : List ℕ := [1, 4, 16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576, 4194304, 16777216, 67108864, 268435456, 1073741824, 2, 8, 32, 128, 512, 2048, 8192, 32768, 131072, 524288, 2097152, 8388608, 33554432, 134217728, 536870912, 2147483648]
def c5_s4 : List ℕ := [0, 4, 2, 6, 1, 5, 3, 7, 16, 20, 18, 22, 17, 21, 19, 23, 8, 12, 10, 14, 9, 13, 11, 15, 24, 28, 26, 30, 25, 29, 27, 31]
def c5_p4 : List ℕ := [1, 16, 4, 64, 2, 32, 8, 128, 65536, 1048576, 262144, 4194304, 131072, 2097152, 524288, 8388608, 256, 4096, 1024, 16384, 512, 8192, 2048, 32768, 16777216, 268435456, 67108864, 1073741824, 33554432, 536870912, 134217728, 2147483648]
def c5_s5 : List ℕ := [0, 4, 8, 12, 16, 20, 24, 28, 1, 5, 9, 13, 17, 21, 25, 29, 2, 6, 10, 14, 18, 22, 26, 30, 3, 7, 11, 15, 19, 23, 27, 31]
def c5_p5 : List ℕ := [1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 2, 32, 512, 8192, 131072, 2097152, 33554432, 536870912, 4, 64, 1024, 16384, 262144, 4194304, 67108864, 1073741824, 8, 128, 2048, 32768, 524288, 8388608, 134217728, 2147483648]
def c5_s6 : List ℕ := [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15, 16, 24, 20, 28, 18, 26, 22, 30, 17, 25, 21, 29, 19, 27, 23, 31]
def c5_p6 : List ℕ := [1, 256, 16, 4096, 4, 1024, 64, 16384, 2, 512, 32, 8192, 8, 2048, 128, 32768, 65536, 16777216, 1048576, 268435456, 262144, 67108864, 4194304, 1073741824, 131072, 33554432, 2097152, 536870912, 524288, 134217728, 8388608, 2147483648]
def c5_s7 : List ℕ := [0, 8, 16, 24, 1, 9, 17, 25, 2, 10, 18, 26, 3, 11, 19, 27, 4, 12, 20, 28, 5, 13, 21, 29, 6, 14, 22, 30, 7, 15, 23, 31]
def c5_p7 : List ℕ := [1, 256, 65536, 16777216, 2, 512, 131072, 33554432, 4, 1024, 262144, 67108864, 8, 2048, 524288, 134217728, 16, 4096, 1048576, 268435456, 32, 8192, 2097152, 536870912, 64, 16384, 4194304, 1073741824, 128, 32768, 8388608, 2147483648]
def c5_s8 : List ℕ := [0, 16, 1, 17, 2, 18, 3, 19, 4, 20, 5, 21, 6, 22, 7, 23, 8, 24, 9, 25, 10, 26, 11, 27, 12, 28, 13, 29, 14, 30, 15, 31]
def c5_p8 : List ℕ := [1, 65536, 2, 131072, 4, 262144, 8, 524288, 16, 1048576, 32, 2097152, 64, 4194304, 128, 8388608, 256, 16777216, 512, 33554432, 1024, 67108864, 2048, 134217728, 4096, 268435456, 8192, 536870912, 16384, 1073741824, 32768, 2147483648]
def c5_s9 : List ℕ := [0, 16, 8, 24, 4, 20, 12, 28, 2, 18, 10, 26, 6, 22, 14, 30, 1, 17, 9, 25, 5, 21, 13, 29, 3, 19, 11, 27, 7, 23, 15, 31]
def c5_p9 : List ℕ := [1, 65536, 256, 16777216, 16, 1048576, 4096, 268435456, 4, 262144, 1024, 67108864, 64, 4194304, 16384, 1073741824, 2, 131072, 512, 33554432, 32, 2097152, 8192, 536870912, 8, 524288, 2048, 134217728, 128, 8388608, 32768, 2147483648]
def c5_idx : Array (List ℕ) := Array.mk [c5_s0, c5_s1, c5_s2, c5_s3, c5_s4, c5_s5, c5_s6, c5_s7, c5_s8, c5_s9]
def c5_pow : Array (List ℕ) := Array.mk [c5_p0, c5_p1, c5_p2, c5_p3, c5_p4, c5_p5, c5_p6, c5_p7, c5_p8, c5_p9]
def c5_inv : Array ℕ := Array.mk [0, 1, 2, 8, 4, 7, 6, 5, 3, 9]
theorem c5_G_valid : (List.range 10).all (symValid 32 10 c5_idx c5_pow c5_inv c5_goal) = true := by decide +kernel
def c5_L3 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xffff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0],[]),
  ([0xf0ff0f0,0xaaaaaaaa,0xcccccccc,0xff00ff00],[])
]
def c5_L4 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaa0aaa0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xfcfc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0f00],[]),
  ([0xa2a2a2a2,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaa,0x55550000,0xcccccccc,0xf0f0f0f0,0xff00ff00],[(8,0)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaa00],[]),
  ([0xf00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffa0a0],[]),
  ([0xa0aaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xa0a0a0a0,0xcccccccc,0xfafafafa,0xff00ff00,0xffff0000],[(5,1)]),
  ([0xcccc,0x33330000,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00],[(7,1)])
]
def c5_L5 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[]),
  ([0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000],[(4,1),(6,0)]),
  ([0xaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,4),(2,3),(7,2)]),
  ([0xa0a0a0a0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,7),(0,9),(1,5),(4,7),(5,6),(5,8),(9,8)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfafafafa,0xff00ff00,0xffff0000],[(0,9)]),
  ([0xcccc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,10)])
]
def c5_L6 : Array (List (BitVec 32) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5),(4,2),(4,5),(5,0),(5,1),(5,2),(5,5),(6,2),(6,5),(7,0),(7,1),(7,2),(7,3),(7,4),(7,5),(8,0),(8,1),(8,2),(8,3),(8,4),(8,5),(9,2),(9,5)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_chk_3_0 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 3 c5_L3 (Array.mk []) 0 2 = true := by decide +kernel
theorem c5_chk_3 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 3 c5_L3 (Array.mk []) 0 2 = true := c5_chk_3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_chk_4_0 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 4 c5_L4 c5_L3 0 11 = true := by decide +kernel
theorem c5_chk_4 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 4 c5_L4 c5_L3 0 11 = true := c5_chk_4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_chk_5_0 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 5 c5_L5 c5_L4 0 6 = true := by decide +kernel
theorem c5_chk_5 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 5 c5_L5 c5_L4 0 6 = true := c5_chk_5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_chk_6_0 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 6 c5_L6 c5_L5 0 1 = true := by decide +kernel
theorem c5_chk_6 : checkBlockP 32 jumps5 c5_goal 10 c5_pow 6 c5_L6 c5_L5 0 1 = true := c5_chk_6_0
theorem c5_L3_sound : ∀ i < c5_L3.size, ¬ live (basicOps 32) c5_goal 3 (c5_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) c5_G_valid (fun j hj => by simp at hj) c5_chk_3
theorem c5_L4_sound : ∀ i < c5_L4.size, ¬ live (basicOps 32) c5_goal 4 (c5_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) c5_G_valid c5_L3_sound c5_chk_4
theorem c5_L5_sound : ∀ i < c5_L5.size, ¬ live (basicOps 32) c5_goal 5 (c5_L5[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) c5_G_valid c5_L4_sound c5_chk_5
theorem c5_L6_sound : ∀ i < c5_L6.size, ¬ live (basicOps 32) c5_goal 6 (c5_L6[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) c5_G_valid c5_L5_sound c5_chk_6
theorem c5_sublists : c5_rows.sublists.filter (fun ws => cover 32 jumps5 c5_goal ws) = [c5_rows] := by decide +kernel
theorem c5_top_match : sameSet (c5_rows.map (actB 32 (c5_pow[0]?.getD []))) (c5_L6[0]?.getD ([], [])).1 = true := by decide +kernel
theorem c5_no_build : ¬ build (basicOps 32) c5_goal 6 c5_rows.toFinset :=
  no_build_of_root c5_G_valid (by decide) c5_sublists c5_top_match (c5_L6_sound 0 (by decide))

def projN {m : ℕ} : List ℕ → BitVec m → ℕ
  | [], _ => 0
  | idx :: idxs, w => Nat.bit (w.getLsbD idx) (projN idxs w)

theorem projN_testBit {m : ℕ} : ∀ (idxs : List ℕ) (w : BitVec m) (k : ℕ),
    (projN idxs w).testBit k = (idxs[k]?.map w.getLsbD).getD false
  | [], _, _ => by simp [projN]
  | idx :: idxs, w, 0 => by simp [projN]
  | idx :: idxs, w, k + 1 => by simp [projN, Nat.testBit_bit_succ, projN_testBit idxs w k]

def projB (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) : BitVec n := BitVec.ofNat n (projN idxs w)
def projS (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) : BitVec n := nrm n (projB n idxs w)

theorem projB_getLsbD (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) (k : ℕ) (hk : k < n) :
    (projB n idxs w).getLsbD k = (idxs[k]?.map w.getLsbD).getD false := by
  unfold projB; rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and, projN_testBit]

theorem projB_and (n : ℕ) {m : ℕ} (idxs : List ℕ) (a b : BitVec m) :
    projB n idxs (a &&& b) = projB n idxs a &&& projB n idxs b := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_and, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases idxs[k]? <;> simp [BitVec.getLsbD_and]

theorem projB_or (n : ℕ) {m : ℕ} (idxs : List ℕ) (a b : BitVec m) :
    projB n idxs (a ||| b) = projB n idxs a ||| projB n idxs b := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_or, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases idxs[k]? <;> simp [BitVec.getLsbD_or]

theorem projB_not (n : ℕ) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n) (hlt : ∀ idx ∈ idxs, idx < m) (a : BitVec m) :
    projB n idxs (~~~a) = ~~~projB n idxs a := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_not, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  have hk' : k < idxs.length := by omega
  rw [List.getElem?_eq_getElem hk']
  have hmem := hlt idxs[k] (List.getElem_mem hk')
  simp [hk, hmem]

theorem projB_zero (n : ℕ) {m : ℕ} (idxs : List ℕ) : projB n idxs (0 : BitVec m) = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [projB_getLsbD n _ _ k hk]; cases idxs[k]? <;> simp

theorem projB_mask (n : ℕ) {m : ℕ} (idxs : List ℕ) (mask : BitVec m)
    (hm : ∀ idx ∈ idxs, mask.getLsbD idx = true) (w : BitVec m) :
    projB n idxs (w &&& mask) = projB n idxs w := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases h : idxs[k]? with
  | none => rfl
  | some idx =>
    have hmem : idx ∈ idxs := List.mem_of_getElem? h
    simp [BitVec.getLsbD_and, hm idx hmem]

theorem nrm_bit0 (n : ℕ) (hn : 0 < n) (u : BitVec n) : (nrm n u).getLsbD 0 = false := by
  unfold nrm
  cases h : u.getLsbD 0
  · simp only [Bool.false_eq_true, ite_false, h]
  · simp only [ite_true, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_true]

theorem projS_ne_allOnes (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (w : BitVec m) :
    projS n idxs w ≠ BitVec.allOnes n := by
  intro h
  have := nrm_bit0 n hn (projB n idxs w)
  change (projS n idxs w).getLsbD 0 = false at this
  rw [h, BitVec.getLsbD_allOnes, decide_eq_true hn] at this
  exact Bool.noConfusion this

theorem nrm_zero (n : ℕ) : nrm n 0 = 0 := by
  unfold nrm; simp

theorem projS_zero (n : ℕ) {m : ℕ} (idxs : List ℕ) : projS n idxs (0 : BitVec m) = 0 := by
  unfold projS; rw [projB_zero, nrm_zero]

theorem projS_mask (n : ℕ) {m : ℕ} (idxs : List ℕ) (mask : BitVec m)
    (hm : ∀ idx ∈ idxs, mask.getLsbD idx = true) (w : BitVec m) :
    projS n idxs (w &&& mask) = projS n idxs w := by
  unfold projS; rw [projB_mask n idxs mask hm w]

theorem nrm_neg (n : ℕ) (hn : 0 < n) (u : BitVec n) : nrm n (~~~u) = nrm n u := by
  unfold nrm
  cases h : u.getLsbD 0
  · have h1 : (~~~u).getLsbD 0 = true := by
      simp only [BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_false]
    rw [h1]; simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.not_not]
  · have h1 : (~~~u).getLsbD 0 = false := by
      simp only [BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_true]
    rw [h1]; simp only [ite_true, ite_false, Bool.false_eq_true]

theorem projS_not (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) (w : BitVec m) :
    projS n idxs (~~~w) = projS n idxs w := by
  unfold projS; rw [projB_not n idxs hlen hlt w, nrm_neg n hn]

theorem nrm_ops (n : ℕ) (hn : 0 < n) (x y z : BitVec n) (hx : x.getLsbD 0 = false) (hy : y.getLsbD 0 = false)
    (hz : z ∈ ops n x y ∨ z ∈ ops n (~~~x) y ∨ z ∈ ops n x (~~~y) ∨ z ∈ ops n (~~~x) (~~~y)) :
    nrm n z ∈ ops n x y := by
  have nrm_f (u : BitVec n) (hu : u.getLsbD 0 = false) : nrm n u = u := by
    unfold nrm; simp only [hu, Bool.false_eq_true, ite_false]
  have nrm_t (u : BitVec n) (hu : u.getLsbD 0 = true) : nrm n u = ~~~u := by
    unfold nrm; simp only [hu, ite_true]
  have b_eq (u v : BitVec n) (h : ∀ i < n, u.getLsbD i = v.getLsbD i) : u = v := BitVec.eq_of_getLsbD_eq h
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · left; exact nrm_f _ (by simp only [BitVec.getLsbD_and, hx, hy, Bool.and_false])
  · right; left; exact nrm_f _ (by simp only [BitVec.getLsbD_or, hx, hy, Bool.or_false])
  · right; right; left; exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right; exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.and_false])]
    exact BitVec.and_comm ..
  · right; right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.true_or])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; left
    exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.or_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.true_or])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; right
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.not_true, Bool.and_false])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.not_true, Bool.and_false])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

theorem projS_ops (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) (a b z : BitVec m) (hz : z ∈ ops m a b) :
    projS n idxs z ∈ ops n (projS n idxs a) (projS n idxs b) := by
  have hrest : projB n idxs z ∈ ops n (projB n idxs a) (projB n idxs b) := by
    simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
    rcases hz with rfl | rfl | rfl | rfl
    · left; exact projB_and n idxs a b
    · right; left; exact projB_or n idxs a b
    · right; right; left; rw [projB_and, projB_not n idxs hlen hlt]
    · right; right; right; rw [projB_and, projB_not n idxs hlen hlt]
  apply nrm_ops n hn (projS n idxs a) (projS n idxs b) (projB n idxs z) (nrm_bit0 n hn _) (nrm_bit0 n hn _)
  unfold projS nrm
  cases ha : (projB n idxs a).getLsbD 0 <;> cases hb : (projB n idxs b).getLsbD 0 <;>
    simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.not_not]
  · exact Or.inl hrest
  · exact Or.inr (Or.inr (Or.inl hrest))
  · exact Or.inr (Or.inl hrest)
  · exact Or.inr (Or.inr (Or.inr hrest))

theorem ops_zero_left (n : ℕ) (y : BitVec n) : ∀ w ∈ ops n 0 y, w = 0 ∨ w = y := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · left; exact BitVec.zero_and
  · right; exact BitVec.zero_or
  · left; exact BitVec.zero_and
  · right; rw [show ~~~(0 : BitVec n) = BitVec.allOnes n from BitVec.eq_of_getLsbD_eq fun i hi => by simp [hi], BitVec.and_allOnes]

theorem ops_zero_right (n : ℕ) (x : BitVec n) : ∀ w ∈ ops n x 0, w = 0 ∨ w = x := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · left; exact BitVec.and_zero
  · right; exact BitVec.or_zero
  · right; rw [show ~~~(0 : BitVec n) = BitVec.allOnes n from BitVec.eq_of_getLsbD_eq fun i hi => by simp [hi], BitVec.and_allOnes]
  · left; exact BitVec.zero_and

theorem ops_self (n : ℕ) (x : BitVec n) : ∀ w ∈ ops n x x, w = 0 ∨ w = x := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · right; exact BitVec.and_self
  · right; exact BitVec.or_self
  · left; exact BitVec.and_not_self x
  · left; exact BitVec.and_not_self x

def zCount {m n : ℕ} (f : BitVec m → BitVec n) (s : Finset (BitVec m)) : ℕ :=
  (s.filter (fun w => f w = 0)).card
def nonZeroImg {m n : ℕ} (f : BitVec m → BitVec n) (s : Finset (BitVec m)) : Finset (BitVec n) :=
  (s.image f).erase 0

set_option maxRecDepth 100000 in
theorem live_restrict {m n : ℕ} (hn : 0 < n) (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) {opsM : BitVec m → BitVec m → Finset (BitVec m)}
    (hopsM : ∀ a b z, z ∈ opsM a b → z ∈ ops m a b)
    {g : BitVec m} {goalN : BitVec n} (hg : projS n idxs g = goalN) (hgnz : goalN ≠ 0)
    {k : ℕ} {s : Finset (BitVec m)} (h : live opsM g k s) :
    build (basicOps n) goalN (k - zCount (projS n idxs) s) (nonZeroImg (projS n idxs) s) := by
  let f : BitVec m → BitVec n := projS n idxs
  change build (basicOps n) goalN (k - zCount f s) (nonZeroImg f s)
  induction k generalizing s with
  | zero =>
    change s = {g} at h; subst h
    have hzc : zCount f {g} = 0 := by
      unfold zCount; rw [Finset.filter_singleton, if_neg (by change projS n idxs g ≠ 0; rw [hg]; exact hgnz)]; rfl
    rw [hzc]; change goalN ∈ nonZeroImg f {g}
    exact Finset.mem_erase.mpr ⟨hgnz, Finset.mem_image.mpr ⟨g, Finset.mem_singleton_self g, hg⟩⟩
  | succ k ih =>
    have hsc := live_card h
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, hs_eq, tail⟩
    · exact build_mono_k (by omega) (ih skip)
    · have htail := ih tail
      have hz_ops : f z ∈ ops n (f a) (f b) := projS_ops n hn idxs hlen hlt a b z (hopsM a b z hz)
      have hsub_rest : nonZeroImg f rest ⊆ nonZeroImg f s := by
        intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hu ⊢
        obtain ⟨hne, v, hv, rfl⟩ := hu; exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
      have hcard_rest : zCount f rest ≤ zCount f (insert z rest) := by
        unfold zCount; exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert z rest))
      by_cases hza : f a = 0
      · have hzb_or := ops_zero_left n (f b) (f z) (hza ▸ hz_ops)
        have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
          intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
          obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
          · rcases hzb_or with h0 | h1; exact (hne h0).elim; exact ⟨hne, b, hb, h1.symm⟩
          · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
        have hm : zCount f s ≤ zCount f (insert z rest) + 1 := by
          by_cases hzb : f b = 0
          · have hzz : f z = 0 := by rcases hzb_or with h0 | h1; exact h0; exact h1.trans hzb
            have hz_nr : z ∉ rest := fun hm => hout (by rw [hs_eq]; simp [hm])
            have h1 : zCount f (insert z rest) = zCount f rest + 1 := by
              unfold zCount; rw [Finset.filter_insert, if_pos hzz, Finset.card_insert_of_notMem (by simp [hz_nr])]
            have h2 : zCount f s ≤ zCount f rest + 2 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_pos hzb, if_pos hza]
              have hc1 := Finset.card_insert_le a (insert b (rest.filter (fun w => f w = 0)))
              have hc2 := Finset.card_insert_le b (rest.filter (fun w => f w = 0))
              omega
            omega
          · have h2 : zCount f s ≤ zCount f rest + 1 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_neg hzb, if_pos hza]
              exact Finset.card_insert_le a (rest.filter (fun w => f w = 0))
            omega
        exact build_mono_k (by omega) (build_mono_av hsub htail)
      · by_cases hzb : f b = 0
        · have hza_or := ops_zero_right n (f a) (f z) (hzb ▸ hz_ops)
          have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
            intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
            obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
            · rcases hza_or with h0 | h1; exact (hne h0).elim; exact ⟨hne, a, ha, h1.symm⟩
            · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
          have hm : zCount f s ≤ zCount f (insert z rest) + 1 := by
            have h2 : zCount f s ≤ zCount f rest + 1 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_pos hzb, if_neg hza]
              exact Finset.card_insert_le b (rest.filter (fun w => f w = 0))
            omega
          exact build_mono_k (by omega) (build_mono_av hsub htail)
        · have hzc_eq : zCount f s = zCount f rest := by
            unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_neg hzb, if_neg hza]
          have hzc_le : zCount f s ≤ k := by
            have hsubf : insert a (insert b (s.filter (fun w => f w = 0))) ⊆ s := by
              intro u hu
              rcases Finset.mem_insert.mp hu with rfl | hu
              · exact ha
              · rcases Finset.mem_insert.mp hu with rfl | hu
                · exact hb
                · exact (Finset.mem_filter.mp hu).1
            have han : a ∉ insert b (s.filter (fun w => f w = 0)) := by
              simp only [Finset.mem_insert, Finset.mem_filter, not_or]; exact ⟨hab, fun h => hza h.2⟩
            have hbn : b ∉ s.filter (fun w => f w = 0) := by
              simp only [Finset.mem_filter]; exact fun h => hzb h.2
            have hle := Finset.card_le_card hsubf
            rw [Finset.card_insert_of_notMem han, Finset.card_insert_of_notMem hbn] at hle
            unfold zCount; omega
          by_cases hzz : f z = 0
          · have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
              intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
              obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
              · exact (hne hzz).elim
              · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
            exact build_mono_k (by omega) (build_mono_av hsub htail)
          · by_cases heqab : f a = f b
            · have hsame := ops_self n (f a) (f z) (heqab ▸ hz_ops)
              have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
                intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
                obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
                · rcases hsame with h0 | h1; exact (hne h0).elim; exact ⟨hne, a, ha, h1.symm⟩
                · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
              exact build_mono_k (by omega) (build_mono_av hsub htail)
            · have hstep : build (basicOps n) goalN ((k - zCount f (insert z rest)) + 1) (nonZeroImg f s) := by
                refine Or.inr ⟨f a, ?_, f b, ?_, heqab, f z, ?_, ?_⟩
                · exact Finset.mem_erase.mpr ⟨hza, Finset.mem_image_of_mem f ha⟩
                · exact Finset.mem_erase.mpr ⟨hzb, Finset.mem_image_of_mem f hb⟩
                · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
                  exact ⟨hz_ops, hzz, projS_ne_allOnes n hn idxs z⟩
                · apply build_mono_av _ htail
                  intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu
                  obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
                  · exact Finset.mem_insert_self _ _
                  · exact Finset.mem_insert_of_mem (hsub_rest (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f hv⟩))
              exact build_mono_k (by omega) hstep

abbrev W5Node := List (BitVec 64) × List (BitVec 64 × BitVec 64 × BitVec 64) × List ℕ × List (ℕ × ℕ)

def checkReplay (m : BitVec 64) (bank : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → Bool
  | [], targets => targets.all (fun t => (t &&& m) == 0 || bank.contains (t &&& m))
  | (v, a, b) :: rest, targets =>
    bank.contains a && bank.contains b && (ops 64 a b).contains v &&
    checkReplay m (v :: bank) rest targets

theorem checkReplay_sound (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (g : BitVec 32)
    (steps : List (BitVec 64 × BitVec 64 × BitVec 64)) (targets : List (BitVec 64)) :
    ∀ (bank : List (BitVec 64)) (k : ℕ),
      checkReplay m bank steps targets = true →
      build (basicOps 32) g k (nonZeroImg (projS 32 idxs) targets.toFinset) →
      build (basicOps 32) g (k + steps.length) (nonZeroImg (projS 32 idxs) bank.toFinset) := by
  let f : BitVec 64 → BitVec 32 := projS 32 idxs
  have hn : 0 < 32 := by decide
  induction steps with
  | nil =>
    intro bank k hchk hb
    simp only [checkReplay, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hchk
    simp only [List.length_nil, Nat.add_zero]
    apply build_mono_av _ hb
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu ⊢
    obtain ⟨hne, t, ht, rfl⟩ := hu
    rcases hchk t ht with h0 | hmem
    · exfalso; apply hne
      rw [← projS_mask 32 idxs m hm t, h0, projS_zero]
    · exact ⟨hne, t &&& m, hmem, projS_mask 32 idxs m hm t⟩
  | cons s rest ih =>
    obtain ⟨v, a, b⟩ := s
    intro bank k hchk hb
    simp only [checkReplay, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨ha, hb_mem⟩, hv⟩, hrest⟩ := hchk
    have hb' := ih (v :: bank) k hrest hb
    simp only [List.length_cons, show k + (rest.length + 1) = (k + rest.length) + 1 by omega]
    have hfv : f v ∈ ops 32 (f a) (f b) := projS_ops 32 hn idxs hlen hlt a b v hv
    have hsub_ins (hmem_v : f v = 0 ∨ f v ∈ nonZeroImg f bank.toFinset) :
        nonZeroImg f (v :: bank).toFinset ⊆ nonZeroImg f bank.toFinset := by
      intro u hu
      simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu ⊢
      obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
      · rcases hmem_v with h0 | hm'
        · exact (hne h0).elim
        · exact Finset.mem_erase.mp hm' |>.imp_right (fun hi => by simpa [List.mem_toFinset] using hi)
      · exact ⟨hne, w, hw, rfl⟩
    by_cases hv0 : f v = 0
    · exact Or.inl (build_mono_av (hsub_ins (Or.inl hv0)) hb')
    · by_cases ha0 : f a = 0
      · rcases ops_zero_left 32 (f b) (f v) (ha0 ▸ hfv) with h0 | h1
        · exact (hv0 h0).elim
        · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb_mem, h1.symm⟩⟩))) hb')
      · by_cases hb0 : f b = 0
        · rcases ops_zero_right 32 (f a) (f v) (hb0 ▸ hfv) with h0 | h1
          · exact (hv0 h0).elim
          · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
        · by_cases hab : f a = f b
          · rcases ops_self 32 (f a) (f v) (hab ▸ hfv) with h0 | h1
            · exact (hv0 h0).elim
            · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
          · refine Or.inr ⟨f a, Finset.mem_erase.mpr ⟨ha0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr ha)⟩,
              f b, Finset.mem_erase.mpr ⟨hb0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hb_mem)⟩,
              hab, f v, ?_, ?_⟩
            · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
              exact ⟨hfv, hv0, projS_ne_allOnes 32 hn idxs v⟩
            · apply build_mono_av _ hb'
              intro u hu
              simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu
              obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hw)⟩)

def addNeed (stock needed : List (BitVec 64)) (u : BitVec 64) : List (BitVec 64) :=
  if u == 0 || stock.contains u || needed.contains u then needed else u :: needed

def buildNeeded (m : BitVec 64) (stock : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], needed => needed
  | (w, a, b) :: rest, needed =>
    let pw := w &&& m
    let needed' := if needed.contains pw then addNeed stock (addNeed stock needed (a &&& m)) (b &&& m) else needed
    buildNeeded m stock rest needed'

def buildSteps (m : BitVec 64) (needed : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → List (BitVec 64 × BitVec 64 × BitVec 64)
  | [], _ => []
  | (w, a, b) :: rest, bank =>
    let pw := w &&& m
    let pa := a &&& m
    let pb := b &&& m
    if needed.contains pw && pw != 0 && !bank.contains pw &&
       bank.contains pa && bank.contains pb && (ops 64 pa pb).contains pw then
      (pw, pa, pb) :: buildSteps m needed rest (pw :: bank)
    else
      buildSteps m needed rest bank

def checkCofClose (fuel : ℕ) (m : BitVec 64) (stock : List (BitVec 64))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) : Bool :=
  let flat := (nxt.filter (fun u => (u &&& m) == 0)).length
  let rem := fuel - flat
  if Nat.blt rem 7 then
    let start := nxt.foldl (fun acc u => addNeed stock acc (u &&& m)) []
    if Nat.blt (start.length + rem) 7 then
      let needed := buildNeeded m stock hist.reverse start
      if Nat.blt (needed.length + rem) 7 then
        let steps := buildSteps m needed hist stock
        Nat.blt (steps.length + rem) 7 && checkReplay m stock steps nxt
      else false
    else false
  else false

def w5_goal : BitVec 64 := 0xfffffffefefceea0
def w5_rows : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def w5_s0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
def w5_p0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648, 4294967296, 8589934592, 17179869184, 34359738368, 68719476736, 137438953472, 274877906944, 549755813888, 1099511627776, 2199023255552, 4398046511104, 8796093022208, 17592186044416, 35184372088832, 70368744177664, 140737488355328, 281474976710656, 562949953421312, 1125899906842624, 2251799813685248, 4503599627370496, 9007199254740992, 18014398509481984, 36028797018963968, 72057594037927936, 144115188075855872, 288230376151711744, 576460752303423488, 1152921504606846976, 2305843009213693952, 4611686018427387904, 9223372036854775808]
def w5_s1 : List ℕ := [0, 1, 16, 17, 8, 9, 24, 25, 4, 5, 20, 21, 12, 13, 28, 29, 2, 3, 18, 19, 10, 11, 26, 27, 6, 7, 22, 23, 14, 15, 30, 31, 32, 33, 48, 49, 40, 41, 56, 57, 36, 37, 52, 53, 44, 45, 60, 61, 34, 35, 50, 51, 42, 43, 58, 59, 38, 39, 54, 55, 46, 47, 62, 63]
def w5_p1 : List ℕ := [1, 2, 65536, 131072, 256, 512, 16777216, 33554432, 16, 32, 1048576, 2097152, 4096, 8192, 268435456, 536870912, 4, 8, 262144, 524288, 1024, 2048, 67108864, 134217728, 64, 128, 4194304, 8388608, 16384, 32768, 1073741824, 2147483648, 4294967296, 8589934592, 281474976710656, 562949953421312, 1099511627776, 2199023255552, 72057594037927936, 144115188075855872, 68719476736, 137438953472, 4503599627370496, 9007199254740992, 17592186044416, 35184372088832, 1152921504606846976, 2305843009213693952, 17179869184, 34359738368, 1125899906842624, 2251799813685248, 4398046511104, 8796093022208, 288230376151711744, 576460752303423488, 274877906944, 549755813888, 18014398509481984, 36028797018963968, 70368744177664, 140737488355328, 4611686018427387904, 9223372036854775808]
def w5_s2 : List ℕ := [0, 2, 1, 3, 16, 18, 17, 19, 8, 10, 9, 11, 24, 26, 25, 27, 4, 6, 5, 7, 20, 22, 21, 23, 12, 14, 13, 15, 28, 30, 29, 31, 32, 34, 33, 35, 48, 50, 49, 51, 40, 42, 41, 43, 56, 58, 57, 59, 36, 38, 37, 39, 52, 54, 53, 55, 44, 46, 45, 47, 60, 62, 61, 63]
def w5_p2 : List ℕ := [1, 4, 2, 8, 65536, 262144, 131072, 524288, 256, 1024, 512, 2048, 16777216, 67108864, 33554432, 134217728, 16, 64, 32, 128, 1048576, 4194304, 2097152, 8388608, 4096, 16384, 8192, 32768, 268435456, 1073741824, 536870912, 2147483648, 4294967296, 17179869184, 8589934592, 34359738368, 281474976710656, 1125899906842624, 562949953421312, 2251799813685248, 1099511627776, 4398046511104, 2199023255552, 8796093022208, 72057594037927936, 288230376151711744, 144115188075855872, 576460752303423488, 68719476736, 274877906944, 137438953472, 549755813888, 4503599627370496, 18014398509481984, 9007199254740992, 36028797018963968, 17592186044416, 70368744177664, 35184372088832, 140737488355328, 1152921504606846976, 4611686018427387904, 2305843009213693952, 9223372036854775808]
def w5_s3 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63]
def w5_p3 : List ℕ := [1, 4, 16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576, 4194304, 16777216, 67108864, 268435456, 1073741824, 2, 8, 32, 128, 512, 2048, 8192, 32768, 131072, 524288, 2097152, 8388608, 33554432, 134217728, 536870912, 2147483648, 4294967296, 17179869184, 68719476736, 274877906944, 1099511627776, 4398046511104, 17592186044416, 70368744177664, 281474976710656, 1125899906842624, 4503599627370496, 18014398509481984, 72057594037927936, 288230376151711744, 1152921504606846976, 4611686018427387904, 8589934592, 34359738368, 137438953472, 549755813888, 2199023255552, 8796093022208, 35184372088832, 140737488355328, 562949953421312, 2251799813685248, 9007199254740992, 36028797018963968, 144115188075855872, 576460752303423488, 2305843009213693952, 9223372036854775808]
def w5_s4 : List ℕ := [0, 4, 2, 6, 1, 5, 3, 7, 16, 20, 18, 22, 17, 21, 19, 23, 8, 12, 10, 14, 9, 13, 11, 15, 24, 28, 26, 30, 25, 29, 27, 31, 32, 36, 34, 38, 33, 37, 35, 39, 48, 52, 50, 54, 49, 53, 51, 55, 40, 44, 42, 46, 41, 45, 43, 47, 56, 60, 58, 62, 57, 61, 59, 63]
def w5_p4 : List ℕ := [1, 16, 4, 64, 2, 32, 8, 128, 65536, 1048576, 262144, 4194304, 131072, 2097152, 524288, 8388608, 256, 4096, 1024, 16384, 512, 8192, 2048, 32768, 16777216, 268435456, 67108864, 1073741824, 33554432, 536870912, 134217728, 2147483648, 4294967296, 68719476736, 17179869184, 274877906944, 8589934592, 137438953472, 34359738368, 549755813888, 281474976710656, 4503599627370496, 1125899906842624, 18014398509481984, 562949953421312, 9007199254740992, 2251799813685248, 36028797018963968, 1099511627776, 17592186044416, 4398046511104, 70368744177664, 2199023255552, 35184372088832, 8796093022208, 140737488355328, 72057594037927936, 1152921504606846976, 288230376151711744, 4611686018427387904, 144115188075855872, 2305843009213693952, 576460752303423488, 9223372036854775808]
def w5_s5 : List ℕ := [0, 4, 8, 12, 16, 20, 24, 28, 1, 5, 9, 13, 17, 21, 25, 29, 2, 6, 10, 14, 18, 22, 26, 30, 3, 7, 11, 15, 19, 23, 27, 31, 32, 36, 40, 44, 48, 52, 56, 60, 33, 37, 41, 45, 49, 53, 57, 61, 34, 38, 42, 46, 50, 54, 58, 62, 35, 39, 43, 47, 51, 55, 59, 63]
def w5_p5 : List ℕ := [1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 2, 32, 512, 8192, 131072, 2097152, 33554432, 536870912, 4, 64, 1024, 16384, 262144, 4194304, 67108864, 1073741824, 8, 128, 2048, 32768, 524288, 8388608, 134217728, 2147483648, 4294967296, 68719476736, 1099511627776, 17592186044416, 281474976710656, 4503599627370496, 72057594037927936, 1152921504606846976, 8589934592, 137438953472, 2199023255552, 35184372088832, 562949953421312, 9007199254740992, 144115188075855872, 2305843009213693952, 17179869184, 274877906944, 4398046511104, 70368744177664, 1125899906842624, 18014398509481984, 288230376151711744, 4611686018427387904, 34359738368, 549755813888, 8796093022208, 140737488355328, 2251799813685248, 36028797018963968, 576460752303423488, 9223372036854775808]
def w5_s6 : List ℕ := [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15, 16, 24, 20, 28, 18, 26, 22, 30, 17, 25, 21, 29, 19, 27, 23, 31, 32, 40, 36, 44, 34, 42, 38, 46, 33, 41, 37, 45, 35, 43, 39, 47, 48, 56, 52, 60, 50, 58, 54, 62, 49, 57, 53, 61, 51, 59, 55, 63]
def w5_p6 : List ℕ := [1, 256, 16, 4096, 4, 1024, 64, 16384, 2, 512, 32, 8192, 8, 2048, 128, 32768, 65536, 16777216, 1048576, 268435456, 262144, 67108864, 4194304, 1073741824, 131072, 33554432, 2097152, 536870912, 524288, 134217728, 8388608, 2147483648, 4294967296, 1099511627776, 68719476736, 17592186044416, 17179869184, 4398046511104, 274877906944, 70368744177664, 8589934592, 2199023255552, 137438953472, 35184372088832, 34359738368, 8796093022208, 549755813888, 140737488355328, 281474976710656, 72057594037927936, 4503599627370496, 1152921504606846976, 1125899906842624, 288230376151711744, 18014398509481984, 4611686018427387904, 562949953421312, 144115188075855872, 9007199254740992, 2305843009213693952, 2251799813685248, 576460752303423488, 36028797018963968, 9223372036854775808]
def w5_s7 : List ℕ := [0, 8, 16, 24, 1, 9, 17, 25, 2, 10, 18, 26, 3, 11, 19, 27, 4, 12, 20, 28, 5, 13, 21, 29, 6, 14, 22, 30, 7, 15, 23, 31, 32, 40, 48, 56, 33, 41, 49, 57, 34, 42, 50, 58, 35, 43, 51, 59, 36, 44, 52, 60, 37, 45, 53, 61, 38, 46, 54, 62, 39, 47, 55, 63]
def w5_p7 : List ℕ := [1, 256, 65536, 16777216, 2, 512, 131072, 33554432, 4, 1024, 262144, 67108864, 8, 2048, 524288, 134217728, 16, 4096, 1048576, 268435456, 32, 8192, 2097152, 536870912, 64, 16384, 4194304, 1073741824, 128, 32768, 8388608, 2147483648, 4294967296, 1099511627776, 281474976710656, 72057594037927936, 8589934592, 2199023255552, 562949953421312, 144115188075855872, 17179869184, 4398046511104, 1125899906842624, 288230376151711744, 34359738368, 8796093022208, 2251799813685248, 576460752303423488, 68719476736, 17592186044416, 4503599627370496, 1152921504606846976, 137438953472, 35184372088832, 9007199254740992, 2305843009213693952, 274877906944, 70368744177664, 18014398509481984, 4611686018427387904, 549755813888, 140737488355328, 36028797018963968, 9223372036854775808]
def w5_s8 : List ℕ := [0, 16, 1, 17, 2, 18, 3, 19, 4, 20, 5, 21, 6, 22, 7, 23, 8, 24, 9, 25, 10, 26, 11, 27, 12, 28, 13, 29, 14, 30, 15, 31, 32, 48, 33, 49, 34, 50, 35, 51, 36, 52, 37, 53, 38, 54, 39, 55, 40, 56, 41, 57, 42, 58, 43, 59, 44, 60, 45, 61, 46, 62, 47, 63]
def w5_p8 : List ℕ := [1, 65536, 2, 131072, 4, 262144, 8, 524288, 16, 1048576, 32, 2097152, 64, 4194304, 128, 8388608, 256, 16777216, 512, 33554432, 1024, 67108864, 2048, 134217728, 4096, 268435456, 8192, 536870912, 16384, 1073741824, 32768, 2147483648, 4294967296, 281474976710656, 8589934592, 562949953421312, 17179869184, 1125899906842624, 34359738368, 2251799813685248, 68719476736, 4503599627370496, 137438953472, 9007199254740992, 274877906944, 18014398509481984, 549755813888, 36028797018963968, 1099511627776, 72057594037927936, 2199023255552, 144115188075855872, 4398046511104, 288230376151711744, 8796093022208, 576460752303423488, 17592186044416, 1152921504606846976, 35184372088832, 2305843009213693952, 70368744177664, 4611686018427387904, 140737488355328, 9223372036854775808]
def w5_s9 : List ℕ := [0, 16, 8, 24, 4, 20, 12, 28, 2, 18, 10, 26, 6, 22, 14, 30, 1, 17, 9, 25, 5, 21, 13, 29, 3, 19, 11, 27, 7, 23, 15, 31, 32, 48, 40, 56, 36, 52, 44, 60, 34, 50, 42, 58, 38, 54, 46, 62, 33, 49, 41, 57, 37, 53, 45, 61, 35, 51, 43, 59, 39, 55, 47, 63]
def w5_p9 : List ℕ := [1, 65536, 256, 16777216, 16, 1048576, 4096, 268435456, 4, 262144, 1024, 67108864, 64, 4194304, 16384, 1073741824, 2, 131072, 512, 33554432, 32, 2097152, 8192, 536870912, 8, 524288, 2048, 134217728, 128, 8388608, 32768, 2147483648, 4294967296, 281474976710656, 1099511627776, 72057594037927936, 68719476736, 4503599627370496, 17592186044416, 1152921504606846976, 17179869184, 1125899906842624, 4398046511104, 288230376151711744, 274877906944, 18014398509481984, 70368744177664, 4611686018427387904, 8589934592, 562949953421312, 2199023255552, 144115188075855872, 137438953472, 9007199254740992, 35184372088832, 2305843009213693952, 34359738368, 2251799813685248, 8796093022208, 576460752303423488, 549755813888, 36028797018963968, 140737488355328, 9223372036854775808]
def w5_idx : Array (List ℕ) := Array.mk [w5_s0, w5_s1, w5_s2, w5_s3, w5_s4, w5_s5, w5_s6, w5_s7, w5_s8, w5_s9]
def w5_pow : Array (List ℕ) := Array.mk [w5_p0, w5_p1, w5_p2, w5_p3, w5_p4, w5_p5, w5_p6, w5_p7, w5_p8, w5_p9]
def w5_inv : Array ℕ := Array.mk [0, 1, 2, 8, 4, 7, 6, 5, 3, 9]
theorem w5_G_valid : (List.range 10).all (symValid 64 10 w5_idx w5_pow w5_inv w5_goal) = true := by decide +kernel
def cfMask0 : BitVec 64 := 0x5555555555555555
def cfStock0 : List (BitVec 64) := [0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]
def cfIdx0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62]
def cfMask1 : BitVec 64 := 0x3333333333333333
def cfStock1 : List (BitVec 64) := [0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]
def cfIdx1 : List ℕ := [0, 1, 16, 17, 8, 9, 24, 25, 4, 5, 20, 21, 12, 13, 28, 29, 32, 33, 48, 49, 40, 41, 56, 57, 36, 37, 52, 53, 44, 45, 60, 61]
def cfMask2 : BitVec 64 := 0xf0f0f0f0f0f0f0f
def cfStock2 : List (BitVec 64) := [0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000]
def cfIdx2 : List ℕ := [0, 2, 1, 3, 16, 18, 17, 19, 8, 10, 9, 11, 24, 26, 25, 27, 32, 34, 33, 35, 48, 50, 49, 51, 40, 42, 41, 43, 56, 58, 57, 59]
def cfMask3 : BitVec 64 := 0xff00ff00ff00ff
def cfStock3 : List (BitVec 64) := [0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]
def cfIdx3 : List ℕ := [0, 4, 2, 6, 1, 5, 3, 7, 16, 20, 18, 22, 17, 21, 19, 23, 32, 36, 34, 38, 33, 37, 35, 39, 48, 52, 50, 54, 49, 53, 51, 55]
def cfMask4 : BitVec 64 := 0xffff0000ffff
def cfStock4 : List (BitVec 64) := [0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000]
def cfIdx4 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]
def cfMask5 : BitVec 64 := 0xffffffff
def cfStock5 : List (BitVec 64) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def cfIdx5 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def cfMasks : Array (BitVec 64) := Array.mk [cfMask0, cfMask1, cfMask2, cfMask3, cfMask4, cfMask5]
def cfStocks : Array (List (BitVec 64)) := Array.mk [cfStock0, cfStock1, cfStock2, cfStock3, cfStock4, cfStock5]

theorem cf_specs :
    (cfIdx0.length = 32 ∧ (∀ idx ∈ cfIdx0, idx < 64) ∧ (∀ idx ∈ cfIdx0, cfMask0.getLsbD idx = true) ∧ projS 32 cfIdx0 w5_goal = p4h_goal ∧ cfStock0.all (fun w => p4h_rows.contains (projS 32 cfIdx0 w)) = true) ∧
    (cfIdx1.length = 32 ∧ (∀ idx ∈ cfIdx1, idx < 64) ∧ (∀ idx ∈ cfIdx1, cfMask1.getLsbD idx = true) ∧ projS 32 cfIdx1 w5_goal = p4h_goal ∧ cfStock1.all (fun w => p4h_rows.contains (projS 32 cfIdx1 w)) = true) ∧
    (cfIdx2.length = 32 ∧ (∀ idx ∈ cfIdx2, idx < 64) ∧ (∀ idx ∈ cfIdx2, cfMask2.getLsbD idx = true) ∧ projS 32 cfIdx2 w5_goal = p4h_goal ∧ cfStock2.all (fun w => p4h_rows.contains (projS 32 cfIdx2 w)) = true) ∧
    (cfIdx3.length = 32 ∧ (∀ idx ∈ cfIdx3, idx < 64) ∧ (∀ idx ∈ cfIdx3, cfMask3.getLsbD idx = true) ∧ projS 32 cfIdx3 w5_goal = p4h_goal ∧ cfStock3.all (fun w => p4h_rows.contains (projS 32 cfIdx3 w)) = true) ∧
    (cfIdx4.length = 32 ∧ (∀ idx ∈ cfIdx4, idx < 64) ∧ (∀ idx ∈ cfIdx4, cfMask4.getLsbD idx = true) ∧ projS 32 cfIdx4 w5_goal = p4h_goal ∧ cfStock4.all (fun w => p4h_rows.contains (projS 32 cfIdx4 w)) = true) ∧
    (cfIdx5.length = 32 ∧ (∀ idx ∈ cfIdx5, idx < 64) ∧ (∀ idx ∈ cfIdx5, cfMask5.getLsbD idx = true) ∧ projS 32 cfIdx5 w5_goal = c5_goal  ∧ cfStock5.all (fun w => c5_rows.contains  (projS 32 cfIdx5 w)) = true) := by
  decide +kernel

theorem checkCofClose_sound_aux (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true)
    (stock : List (BitVec 64)) (g : BitVec 32) (hgnz : g ≠ 0) (rows : List (BitVec 32))
    (hg : projS 32 idxs w5_goal = g)
    (hstock : stock.all (fun w => rows.contains (projS 32 idxs w)) = true)
    (hnobuild : ¬ build (basicOps 32) g 6 rows.toFinset)
    (fuel : ℕ) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64))
    (hnd : nxt.Nodup) (hchk : checkCofClose fuel m stock hist nxt = true) :
    ¬ live (basicOps 64) w5_goal fuel nxt.toFinset := by
  intro hlive
  unfold checkCofClose at hchk
  dsimp only at hchk
  split at hchk
  · split at hchk
    · split at hchk
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
        have hops64 : ∀ a b z : BitVec 64, z ∈ basicOps 64 a b → z ∈ ops 64 a b := fun a b z hz =>
          (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
        have hres := live_restrict (by decide : 0 < 32) idxs hlen hlt hops64 hg hgnz hlive
        have hflat_le : (nxt.filter (fun u => (u &&& m) == 0)).length ≤ zCount (projS 32 idxs) nxt.toFinset := by
          have hndf : (nxt.filter (fun u => (u &&& m) == 0)).Nodup := hnd.filter _
          rw [← List.toFinset_card_of_nodup hndf]
          apply Finset.card_le_card
          intro u hu
          simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu.1, ?_⟩
          rw [← projS_mask 32 idxs m hm u, hu.2, projS_zero]
        have hrep := checkReplay_sound idxs hlen hlt m hm g _ nxt stock _ hchk.2 hres
        have hsub : nonZeroImg (projS 32 idxs) stock.toFinset ⊆ rows.toFinset := by
          intro u hu
          simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu
          obtain ⟨_, v, hv, rfl⟩ := hu
          have h1 := List.all_eq_true.mp hstock v hv
          simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
          exact List.mem_toFinset.mpr h1
        exact hnobuild (build_mono_k (by omega) (build_mono_av hsub hrep))
      · cases hchk
    · cases hchk
  · cases hchk

theorem checkCofClose_sound (c fuel : ℕ) (hc : c < 6)
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64))
    (hnd : nxt.Nodup)
    (hchk : checkCofClose fuel (cfMasks[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true) :
    ¬ live (basicOps 64) w5_goal fuel nxt.toFinset := by
  have hp4_nz : p4h_goal ≠ 0 := by decide
  have hc5_nz : c5_goal ≠ 0 := by decide
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := cf_specs
  match c with
  | 0 => exact checkCofClose_sound_aux cfIdx0 h0.1 h0.2.1 cfMask0 h0.2.2.1 cfStock0 p4h_goal hp4_nz p4h_rows h0.2.2.2.1 h0.2.2.2.2 p4h_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose_sound_aux cfIdx1 h1.1 h1.2.1 cfMask1 h1.2.2.1 cfStock1 p4h_goal hp4_nz p4h_rows h1.2.2.2.1 h1.2.2.2.2 p4h_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose_sound_aux cfIdx2 h2.1 h2.2.1 cfMask2 h2.2.2.1 cfStock2 p4h_goal hp4_nz p4h_rows h2.2.2.2.1 h2.2.2.2.2 p4h_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose_sound_aux cfIdx3 h3.1 h3.2.1 cfMask3 h3.2.2.1 cfStock3 p4h_goal hp4_nz p4h_rows h3.2.2.2.1 h3.2.2.2.2 p4h_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose_sound_aux cfIdx4 h4.1 h4.2.1 cfMask4 h4.2.2.1 cfStock4 p4h_goal hp4_nz p4h_rows h4.2.2.2.1 h4.2.2.2.2 p4h_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose_sound_aux cfIdx5 h5.1 h5.2.1 cfMask5 h5.2.2.1 cfStock5 c5_goal  hc5_nz c5_rows  h5.2.2.2.1 h5.2.2.2.2 c5_no_build  fuel hist nxt hnd hchk
  | c + 6 => omega

def checkChildW5 (k : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 64)))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) : Bool :=
  decide (nxt.length > k) ||
  cfs.any (fun c => checkCofClose (k - 1) (cfMasks[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt) ||
  targets.any (fun t => sameSet nxt t)

def checkStepW5 (k extra : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 64)))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (a b : BitVec 64) (r : List (BitVec 64)) : Bool :=
  (ops 64 a b).all fun w =>
    (w == 0 || w == BitVec.allOnes 64 || w == a || w == b || r.contains w) ||
    let h' := hist ++ [(w, a, b)]
    (!cover 64 jumps6 w5_goal (w :: r) || checkChildW5 k cfs targets h' (w :: r)) &&
    ((extra == 0) ||
      ((!cover 64 jumps6 w5_goal (w :: a :: r) || checkChildW5 k cfs targets h' (w :: a :: r)) &&
       (!cover 64 jumps6 w5_goal (w :: b :: r) || checkChildW5 k cfs targets h' (w :: b :: r)))) &&
    ((extra < 2) || !cover 64 jumps6 w5_goal (w :: a :: b :: r) || checkChildW5 k cfs targets h' (w :: a :: b :: r))

def checkNodeW5 (k : ℕ) (cur prev : Array W5Node) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hist, cfs, hs) =>
    decide ws.Nodup && !(ws.contains w5_goal) && decide (ws.length ≤ k + 1) &&
    cfs.all (fun c => Nat.blt c 6) &&
    hs.all (fun p => Nat.blt p.1 10 && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 64 (w5_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepW5 k extra cfs targets hist a b r)

def checkBlockW5 (k : ℕ) (cur prev : Array W5Node) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeW5 k cur prev (start + m) && checkBlockW5 k cur prev start m

theorem checkBlockW5_at {k start m : ℕ} {cur prev : Array W5Node}
    (h : checkBlockW5 k cur prev start m = true) (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeW5 k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockW5, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem checkBlockW5_merge {k start a b : ℕ} {cur prev : Array W5Node}
    (h1 : checkBlockW5 k cur prev start a = true)
    (h2 : checkBlockW5 k cur prev (start + a) b = true) :
    checkBlockW5 k cur prev start (a + b) = true := by
  induction b with
  | zero => simpa using h1
  | succ b ih =>
    simp only [checkBlockW5, Bool.and_eq_true] at h2 ⊢
    exact ⟨by simpa [Nat.add_assoc] using h2.1, ih h2.2⟩

theorem node_sound_W5 {k i : ℕ} {cur prev : Array W5Node}
    (hk : 0 < k) (hi : i < cur.size)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 64) w5_goal (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hchk : checkNodeW5 k cur prev i = true) :
    ¬ live (basicOps 64) w5_goal k (cur[i]?.getD ([], [], [], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hist, cfs, hs⟩
  have hget : cur[i]? = some (ws, hist, cfs, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeW5 at hchk
  rw [hget] at hchk ⊢
  dsimp only at hchk ⊢
  simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hcfs⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 64 (w5_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps 64) w5_goal (k - 1) t.toFinset := by
    intro t ht
    obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hg, hc⟩ := hhs (g, c) hmem
    intro hlive
    have hinv_lt := (actB_spec w5_G_valid g hg).1
    have hinv_g := (actB_spec w5_G_valid (w5_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB 64 (w5_pow[w5_inv[g]?.getD 0]?.getD [])) (actB_inj w5_G_valid _ hinv_lt)
      hinv_g (actB_ops w5_G_valid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [], [], [])).1.map (actB 64 (w5_pow[g]?.getD []))).toFinset.image
        (actB 64 (w5_pow[w5_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [], [], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left w5_G_valid g hg v]
      · intro hu; exact ⟨actB 64 (w5_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left w5_G_valid g hg u⟩
    rw [hset] at himg
    exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · have hmem : w5_goal ∈ ws.toFinset := done.symm ▸ Finset.mem_singleton_self _
    exact hng (List.mem_toFinset.mp hmem)
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec 64} (hpair : (a, b, r) ∈ pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed))
        (hop : z ∈ basicOps 64 a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps 64) w5_goal (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail
      rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover 64 jumps6 w5_goal (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair
      unfold checkStepW5 at hstep
      dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes 64 || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw
      simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq
      simp only [List.length_cons] at plen
      have close (hc : checkChildW5 k cfs targets (hist ++ [(z, a, b)]) (z :: kept) = true) : False := by
        unfold checkChildW5 at hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with (hgt | ⟨c, hcm, hcf⟩) | ⟨t, ht, hss⟩
        · omega
        · exact checkCofClose_sound c (k - 1) (hcfs c hcm) (hist ++ [(z, a, b)]) (z :: kept) hndc hcf htail
        · rw [sameSet_sound hss] at htail
          exact htargets t ht htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept
        have h1 := hw.1.1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.2
        have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap 64 a b ▸ hz)

theorem level_sound_W5 {k : ℕ} {cur prev : Array W5Node}
    (hk : 0 < k)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 64) w5_goal (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeW5 k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps 64) w5_goal k (cur[i]?.getD ([], [], [], [])).1.toFinset :=
  fun i hi => node_sound_W5 hk hi hprev (hblk i hi)

def w5_L4 : Array W5Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xfcfcfc00fcfcfc00,0xfff0fff0fff0fff0,0xffffccccffffcccc,0xffffffff00000000],[(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00),(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfcfc00fcfcfc00,0xfcfcfcfcfcfcfcfc,0xffffff00ffffff00)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffffff00cccccc00,0xffffffffffff0000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xffccffccffccffcc,0xff00ff00ff00ff00,0xcccccccccccccccc),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffffff00cccccc00,0xffffff00ffffff00,0xffffffffcccccccc),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfffffff0fcfcfcf0,0xffffffffffff0000],[(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffffff00cccccc00,0xffffff00ffffff00,0xffffffffcccccccc),(0xfffffff0fcfcfcf0,0xffffff00cccccc00,0xf0f0f0f0f0f0f0f0),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[])
]
def w5_L5 : Array W5Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xfcfcfcfcfcfcfcfc,0xfff0fff0fff0fff0,0xffffccccffffcccc,0xffffff00ffffff00,0xffffffff00000000],[(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00),(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc)],[1, 2],[(0,0)]),
  ([0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffffff00ffffff00,0xffffffffcccccccc,0xffffffffffff0000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xffccffccffccffcc,0xff00ff00ff00ff00,0xcccccccccccccccc),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfca8a8fcfca8a8,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0),(0xfcfcfcfcfcfcfcfc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0),(0xfcfca8a8fcfca8a8,0xfcfcfcfcfcfcfcfc,0xffffaaaaffffaaaa)],[],[(6,0)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xfffffffff0f0f0f0,0xffffffffffffaaaa],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffffffffffffaaaa,0xffffaaaaffffaaaa,0xffffffff00000000)],[2],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfc0000,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xfcfcfcfcfcfc0000,0xfcfcfcfcfcfcfcfc,0xffffffffffff0000)],[4],[(1,1)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0aaa0fff0aaa0,0xffffff00ffffff00,0xffffffff00000000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfff0aaa0fff0aaa0,0xfff0fff0fff0fff0,0xffffaaaaffffaaaa)],[],[(2,0)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfff0fff0fff0fff0,0xffffff00ffffff00,0xfffffffff0f0f0f0,0xffffffffffff0000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[2],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfffffff0fffffff0,0xfffffffff0f0f0f0,0xffffffffffff0000],[(0xfff0fff0fff0fff0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xfffffff0fffffff0,0xffff0000ffff0000,0xfff0fff0fff0fff0),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2, 5],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfffffafafffffafa,0xfffffffff0f0f0f0,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xfffffafafffffafa,0xf0f0f0f0f0f0f0f0,0xffffaaaaffffaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[5],[]),
  ([0xeeee0000eeee,0x5555444455554444,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffeeeeffffeeee,0xffffaaaaffffaaaa,0xcccccccccccccccc),(0xeeee0000eeee,0xffff0000ffff0000,0xffffeeeeffffeeee),(0x5555444455554444,0xaaaaaaaaaaaaaaaa,0xffffeeeeffffeeee)],[],[]),
  ([0xeeee0000eeee,0x3333222233332222,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffeeeeffffeeee,0xffffaaaaffffaaaa,0xcccccccccccccccc),(0xeeee0000eeee,0xffff0000ffff0000,0xffffeeeeffffeeee),(0x3333222233332222,0xcccccccccccccccc,0xffffeeeeffffeeee)],[1],[]),
  ([0xffff0000fefe,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfefefefefefefefe,0xfcfcfcfcfcfcfcfc,0xaaaaaaaaaaaaaaaa),(0xfffffffffefefefe,0xfefefefefefefefe,0xffffffff00000000),(0xffff0000fefe,0xffff0000ffff0000,0xfffffffffefefefe)],[],[]),
  ([0xfafa0000fafa,0x5555505055555050,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffffafafffffafa,0xffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0),(0xfafa0000fafa,0xffff0000ffff0000,0xfffffafafffffafa),(0x5555505055555050,0xaaaaaaaaaaaaaaaa,0xfffffafafffffafa)],[],[]),
  ([0xfafa0000fafa,0xf0f0a0a0f0f0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffffafafffffafa,0xffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0),(0xfafa0000fafa,0xffff0000ffff0000,0xfffffafafffffafa),(0xf0f0a0a0f0f0a0a,0xf0f0f0f0f0f0f0f0,0xfffffafafffffafa)],[],[]),
  ([0xffff0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffcfcfffffcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xfffffffffffffcfc,0xfffffcfcfffffcfc,0xffffffff00000000),(0xffff0000fcfc,0xffff0000ffff0000,0xfffffffffffffcfc)],[],[]),
  ([0xfcfc0000fcfc,0xf0f0a0a0f0f0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000),(0xf0f0a0a0f0f0a0a,0xf0f0f0f0f0f0f0f0,0xffffaaaaffffaaaa)],[],[]),
  ([0xffff0000aaaa,0x5555555555550000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffffaaaa,0xffffaaaaffffaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffffffaaaa),(0x5555555555550000,0xaaaaaaaaaaaaaaaa,0xffffffffffffaaaa)],[],[]),
  ([0xeeeeeeee,0x3333333322222222,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffffffffeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000),(0x3333333322222222,0xcccccccccccccccc,0xffffffffeeeeeeee),(0xeeeeeeee,0xffffffff00000000,0xffffffffeeeeeeee)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccaa88ffccaa88,0xffffff00ffffff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffccaa88ffccaa88,0xffffaaaaffffaaaa,0xffccffccffccffcc),(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0302ffff0302,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00),(0x302030203020302,0xfcfcfcfcfcfcfcfc,0xffaaffaaffaaffaa),(0xffff0302ffff0302,0x302030203020302,0xffff0000ffff0000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaacccc8888,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffffaaaacccc8888,0xffffaaaaffffaaaa,0xffffffffcccccccc),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaf0f0a0a0,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffffaaaaf0f0a0a0,0xffffaaaaffffaaaa,0xfffffffff0f0f0f0),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffeeeeffffee00,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xeeeeeeeeee00ee00,0xeeeeeeeeeeeeeeee,0xffffffffff00ff00),(0xffffeeeeffffee00,0xeeeeeeeeee00ee00,0xffff0000ffff0000)],[],[(7,2)]),
  ([0xffaa0000ffaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffffaaaaaaaa,0xffffffffff00ff00],[(0xffaaffaaffaaffaa,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000)],[0],[]),
  ([0xfafa0000fafa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa,0xfffffffff0f0f0f0],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xfafa0000fafa,0xffff0000ffff0000,0xfafafafafafafafa)],[],[]),
  ([0xffff0000aaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f0f0f0],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa)],[],[]),
  ([0xffff0000cccc,0x3333333333330000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffffffffffcccc,0xffffccccffffcccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffffffcccc),(0x3333333333330000,0xcccccccccccccccc,0xffffffffffffcccc)],[],[]),
  ([0xfafafafa,0xf0f0f0f0a0a0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfffffffffafafafa,0xfafafafafafafafa,0xffffffff00000000),(0xf0f0f0f0a0a0a0a,0xf0f0f0f0f0f0f0f0,0xfffffffffafafafa),(0xfafafafa,0xffffffff00000000,0xfffffffffafafafa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccf0f0c0c0,0xffffffffffff0000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffffccccf0f0c0c0,0xffffccccffffcccc,0xfffffffff0f0f0f0),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[]),
  ([0xdddd0000dcdc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0x5555555550505050,0xaaaaaaaaaaaaaaaa,0xfffffffff0f0f0f0),(0xdddddddddcdcdcdc,0x5555555550505050,0xcccccccccccccccc),(0xdddd0000dcdc,0xdddddddddcdcdcdc,0xffff0000ffff0000)],[],[])
]
def w5_L6 : Array W5Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffffaaaaffffaaaa,0xffffff00ffffff00,0xffffffff00000000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xffccffccffccffcc,0xff00ff00ff00ff00,0xcccccccccccccccc),(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa)],[0, 1],[(4,0)]),
  ([0xfafa0000fafa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000),(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfafa0000fafa,0xffff0000ffff0000,0xfafafafafafafafa)],[4],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffffff00ffffff00,0xffffffff00000000,0xffffffffffff0000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xffccffccffccffcc,0xff00ff00ff00ff00,0xcccccccccccccccc),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[(0,1)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0),(0xfcfcfcfcfcfcfcfc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0)],[0, 1],[(0,2),(6,0)]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xfcfc0000fcfc,0xffff0000ffff0000,0xfcfcfcfcfcfcfcfc)],[4],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xffffffff00000000,0xffffffffffff0000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[(0,4),(1,1),(2,3)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xfffffff0fffffff0,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0),(0xfffffff0fffffff0,0xff00ff00ff00ff00,0xfffff0f0fffff0f0)],[0, 2],[]),
  ([0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xffaaffaaffaaffaa,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa)],[0, 2],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000,0xffffffffffffff00],[(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00),(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffffffffffff00,0xffffff00ffffff00,0xffffffff00000000)],[1],[(6,3)]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[3],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000,0xfffffffffffff0f0],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0),(0xfffffffffffff0f0,0xfffff0f0fffff0f0,0xffffffff00000000)],[0],[]),
  ([0xfafafafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[(0xfff0fff0fff0fff0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00),(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfafafafa,0xfafafafafafafafa,0xffffffff00000000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0,0xffffaaaaffffaaaa,0xffffff00ffffff00,0xffffffff00000000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa)],[0, 2],[(0,5),(2,0)]),
  ([0xeeee0000eeee,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000),(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xeeee0000eeee,0xffff0000ffff0000,0xeeeeeeeeeeeeeeee)],[1, 4],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0,0xffffff00ffffff00,0xffffffff00000000,0xffffffffffff0000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2],[(0,6)]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xfcfcfcfcfcfcfcfc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0),(0xeeee0000eeee,0xffff0000ffff0000,0xeeeeeeeeeeeeeeee)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000,0xffffffffffffff00],[(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00),(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffffff00,0xffffff00ffffff00,0xffffffff00000000)],[0, 1],[]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xfcfcfcfcfcfcfcfc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0),(0xeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[],[]),
  ([0xffff0000aaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000,0xffffffffaaaaaaaa],[(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa)],[4],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffeeeeffffeeee,0xffffffff00000000,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffeeeeffffeeee,0xcccccccccccccccc,0xffffaaaaffffaaaa)],[1, 5],[(7,7)]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffcccccccc],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xeeee0000eeee,0xffff0000ffff0000,0xeeeeeeeeeeeeeeee)],[5],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffffcccccccc,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000)],[1],[(7,6),(7,7)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffffafafffffafa,0xffffffff00000000,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xfffffafafffffafa,0xf0f0f0f0f0f0f0f0,0xffffaaaaffffaaaa)],[5],[(0,8)]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xfcfc0000fcfc,0xffff0000ffff0000,0xfcfcfcfcfcfcfcfc)],[5],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xfffffffff0f0f0f0,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[],[(0,8),(6,1)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc)],[2],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffaaffffffaa,0xffffffff00000000,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffffaaffffffaa,0xff00ff00ff00ff00,0xffffaaaaffffaaaa)],[0, 5],[]),
  ([0xeeee0000eeee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xeeee0000eeee,0xffff0000ffff0000,0xeeeeeeeeeeeeeeee)],[0, 4],[]),
  ([0xffff0000aaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa)],[1],[]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcccccccc],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[5],[]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffeeeeffffeeee,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffeeeeffffeeee,0xffffaaaaffffaaaa,0xcccccccccccccccc),(0xeeee0000eeee,0xffff0000ffff0000,0xffffeeeeffffeeee)],[0, 1],[(0,9),(0,10)]),
  ([0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffaaffffffaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000),(0xffffffaaffffffaa,0xffffaaaaffffaaaa,0xff00ff00ff00ff00),(0xffaa0000ffaa,0xffff0000ffff0000,0xffffffaaffffffaa)],[0],[(3,9),(9,9)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffefffefffefffe,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfefefefefefefefe,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0),(0xfffefffefffefffe,0xfefefefefefefefe,0xff00ff00ff00ff00)],[],[]),
  ([0xfefe0000fefe,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfefefefefefefefe,0xfcfcfcfcfcfcfcfc,0xaaaaaaaaaaaaaaaa),(0xfefe0000fefe,0xfefefefefefefefe,0xffff0000ffff0000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffffefefefe],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfefefefefefefefe,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0),(0xfffffffffefefefe,0xfefefefefefefefe,0xffffffff00000000)],[3, 4],[(0,11),(4,11)]),
  ([0xfefefefe,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfefefefefefefefe,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0),(0xfefefefe,0xfefefefefefefefe,0xffffffff00000000)],[],[]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffeeeeffffeeee,0xffffaaaaffffaaaa,0xcccccccccccccccc),(0xeeee0000eeee,0xffff0000ffff0000,0xffffeeeeffffeeee)],[0],[(0,10)]),
  ([0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000),(0xffffffaaffffffaa,0xffffaaaaffffaaaa,0xff00ff00ff00ff00),(0xffaa0000ffaa,0xffff0000ffff0000,0xffffffaaffffffaa)],[0],[(3,9)]),
  ([0xaaaaaaaaaaaaaaaa,0xaafeaafeaafeaafe,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0),(0xfc00fc00fc00fc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00),(0xaafeaafeaafeaafe,0xfc00fc00fc00fc,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xe0e00000e0e,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xeeee0000eeee,0xeeeeeeeeeeeeeeee,0xffff0000ffff0000),(0xe0e00000e0e,0xeeee0000eeee,0xf0f0f0f0f0f0f0f0)],[0, 1],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaafffaaaaafffa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfff0fff0fff0fff0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00),(0xfff00000fff0,0xfff0fff0fff0fff0,0xffff0000ffff0000),(0xaaaafffaaaaafffa,0xfff00000fff0,0xaaaaaaaaaaaaaaaa)],[3],[]),
  ([0xee000000ee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xeeee0000eeee,0xeeeeeeeeeeeeeeee,0xffff0000ffff0000),(0xee000000ee,0xeeee0000eeee,0xff00ff00ff00ff00)],[0],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffff0000eeee],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xeeee0000eeee,0xeeeeeeeeeeeeeeee,0xffff0000ffff0000),(0xffffffff0000eeee,0xeeee0000eeee,0xffffffff00000000)],[],[]),
  ([0xeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xeeee0000eeee,0xeeeeeeeeeeeeeeee,0xffff0000ffff0000),(0xeeee,0xeeee0000eeee,0xffffffff00000000)],[0],[]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffffafafffffafa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffffafafffffafa,0xffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0),(0xfafa0000fafa,0xffff0000ffff0000,0xfffffafafffffafa)],[0],[(0,12),(0,13)]),
  ([0xffee0000ffee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffeeffeeffeeffee,0xeeeeeeeeeeeeeeee,0xff00ff00ff00ff00),(0xffee0000ffee,0xffff0000ffff0000,0xffeeffeeffeeffee)],[],[]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffffcfcfffffcfc,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffcfcfffffcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xfcfc0000fcfc,0xffff0000ffff0000,0xfffffcfcfffffcfc)],[0],[(2,13),(7,13)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffffcfcfffffcfc,0xffffffff00000000,0xffffffffffff0000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffcfcfffffcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[5],[(2,8),(7,8)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffffeeffee],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffeeffeeffeeffee,0xeeeeeeeeeeeeeeee,0xff00ff00ff00ff00),(0xffffffffffeeffee,0xffeeffeeffeeffee,0xffffffff00000000)],[],[(4,14)]),
  ([0xffeeffee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffeeffeeffeeffee,0xeeeeeeeeeeeeeeee,0xff00ff00ff00ff00),(0xffeeffee,0xffeeffeeffeeffee,0xffffffff00000000)],[],[]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffffafafffffafa,0xffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0),(0xfafa0000fafa,0xffff0000ffff0000,0xfffffafafffffafa)],[0],[(0,13)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaafefeaaaafefe,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xaaaafefeaaaafefe,0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffff0000fcfc],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xffffffff0000fcfc,0xfcfc0000fcfc,0xffffffff00000000)],[5],[]),
  ([0xfcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xfcfc,0xfcfc0000fcfc,0xffffffff00000000)],[],[]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000),(0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000)],[0],[(0,15)]),
  ([0xffff0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffffaaaa],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffffaaaa,0xffffaaaaffffaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffffffaaaa)],[0],[(0,16),(1,17)]),
  ([0xffff0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xffffffffeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000),(0xffff0000eeee,0xffff0000ffff0000,0xffffffffeeeeeeee)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa,0xfffffffffff0fff0],[(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xfffffffffff0fff0,0xfff0fff0fff0fff0,0xffffffff00000000),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000)],[0],[(4,3),(5,3)]),
  ([0xaaaaaaaaaaa0aaa0,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffffff0fff0],[(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xfffffffffff0fff0,0xfff0fff0fff0fff0,0xffffffff00000000),(0xaaaaaaaaaaa0aaa0,0xaaaaaaaaaaaaaaaa,0xfffffffffff0fff0)],[],[(8,14)]),
  ([0xffff0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffffffcfcfcfc,0xfcfcfcfcfcfcfcfc,0xffffffff00000000),(0xffff0000fcfc,0xffff0000ffff0000,0xfffffffffcfcfcfc)],[],[]),
  ([0xffff0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffffffcfcfcfc,0xfcfcfcfcfcfcfcfc,0xffffffff00000000),(0xffff0000fcfc,0xffff0000ffff0000,0xfffffffffcfcfcfc)],[],[]),
  ([0xffff0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xfffffffffcfcfcfc],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffffffcfcfcfc,0xfcfcfcfcfcfcfcfc,0xffffffff00000000),(0xffff0000fcfc,0xffff0000ffff0000,0xfffffffffcfcfcfc)],[4],[]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffeeeeeeee],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000),(0xeeeeeeee,0xffffffff00000000,0xffffffffeeeeeeee)],[0],[(0,17),(2,17)]),
  ([0xffff0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffffaaaa,0xffffaaaaffffaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffffffaaaa)],[0],[(1,17)]),
  ([0xffff0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfffffffffcfcfcfc,0xfcfcfcfcfcfcfcfc,0xffffffff00000000),(0xffff0000fcfc,0xffff0000ffff0000,0xfffffffffcfcfcfc)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaaaaafefefefe,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfcfcfc,0xfcfcfcfcfcfcfcfc,0xffffffff00000000),(0xaaaaaaaafefefefe,0xfcfcfcfc,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaaaaafffafffa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfff0fff0fff0fff0,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0),(0xfff0fff0,0xfff0fff0fff0fff0,0xffffffff00000000),(0xaaaaaaaafffafffa,0xfff0fff0,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeee0eee0eee0eee0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfff0fff0fff0fff0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00),(0xeee0eee0eee0eee0,0xeeeeeeeeeeeeeeee,0xfff0fff0fff0fff0)],[0, 3],[(1,5),(8,2)]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffffff00,0xffffffff00000000],[(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00),(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfafa0000fafa,0xffff0000ffff0000,0xfafafafafafafafa)],[3],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeee0e0eeeee0e0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xeeeee0e0eeeee0e0,0xeeeeeeeeeeeeeeee,0xfffff0f0fffff0f0)],[],[(8,18)]),
  ([0xfa000000fa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfa000000fa,0xffffff00ffffff00,0xfafafafafafafafa)],[1],[(1,19)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc)],[0],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeee0e0e0e0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xeeeeeeeee0e0e0e0,0xeeeeeeeeeeeeeeee,0xfffffffff0f0f0f0)],[0, 5],[(8,20)]),
  ([0xff000000aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xff000000aa,0xffffff00ffffff00,0xffffffffaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeee00ee00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xeeeeeeeeee00ee00,0xeeeeeeeeeeeeeeee,0xffffffffff00ff00)],[0, 1, 2, 3, 4, 5],[(0,22),(1,21),(2,22),(3,4),(4,4),(8,21)]),
  ([0xff000000cc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffff00ffffff00,0xff00ff00ff00ff00,0xffff0000ffff0000),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xff000000cc,0xffffff00ffffff00,0xffffffffcccccccc)],[],[]),
  ([0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[(0xffaaffaaffaaffaa,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa)],[0],[(0,23)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xfffffffff0f0f0f0,0xffffffffffff0000],[(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2, 4, 5],[(0,3),(0,7),(0,8),(2,3),(2,8),(4,23),(7,24),(7,25),(9,24),(9,25)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000,0xffffffffcccccccc],[(0xffffccccffffcccc,0xcccccccccccccccc,0xffff0000ffff0000),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc)],[1, 4],[]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xfafa0000fafa,0xffff0000ffff0000,0xfafafafafafafafa)],[5],[(0,24)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xfffffffff0f0f0f0,0xffffffffffff0000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[],[(2,8),(5,1),(7,3)]),
  ([0xfafa0000fafa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xfafa0000fafa,0xffff0000ffff0000,0xfafafafafafafafa)],[],[(0,24)]),
  ([0xffff0000aaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa)],[],[(0,25)]),
  ([0xfafafafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f0f0f0],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xfafafafa,0xfafafafafafafafa,0xffffffff00000000)],[2, 5],[]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffeeeeffffeeee,0xaaaaaaaaaaaaaaaa,0xffffccccffffcccc),(0xeeee0000eeee,0xffff0000ffff0000,0xffffeeeeffffeeee)],[0, 1, 4],[(0,9)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaffaafaaaffaafa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0),(0xff00f000ff00f0,0xff00ff00ff00ff00,0xfffff0f0fffff0f0),(0xaaffaafaaaffaafa,0xff00f000ff00f0,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xf0a00000f0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffaaffaaffaaffaa,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa),(0xf0a00000f0a,0xffaa0000ffaa,0xf0f0f0f0f0f0f0f0)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffff0000ffaa],[(0xffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa),(0xffffffff0000ffaa,0xffaa0000ffaa,0xffffffff00000000)],[],[]),
  ([0xffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa),(0xffaa,0xffaa0000ffaa,0xffffffff00000000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfac8fac8fac8fac8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xfac8fac8fac8fac8,0xfafafafafafafafa,0xffccffccffccffcc)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafac8c8c8c8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xfafafafac8c8c8c8,0xfafafafafafafafa,0xffffffffcccccccc)],[5],[]),
  ([0xf0f00000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xf0f00000f00,0xfffff0f0fffff0f0,0xffffffffff00ff00)],[],[]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xfffffcfcfffffcfc,0xffffccccffffcccc,0xf0f0f0f0f0f0f0f0),(0xfcfc0000fcfc,0xffff0000ffff0000,0xfffffcfcfffffcfc)],[0, 1],[(2,13)]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xfffffafafffffafa,0xfffff0f0fffff0f0,0xaaaaaaaaaaaaaaaa),(0xfafa0000fafa,0xffff0000ffff0000,0xfffffafafffffafa)],[0, 2],[(0,12)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaffaaeeaaffaaee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffccccffffcccc,0xcccccccccccccccc,0xffff0000ffff0000),(0xff00cc00ff00cc,0xffffccccffffcccc,0xff00ff00ff00ff00),(0xaaffaaeeaaffaaee,0xff00cc00ff00cc,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaffeeaaaaffee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffcc0000ffcc,0xffccffccffccffcc,0xffff0000ffff0000),(0xaaaaffeeaaaaffee,0xffcc0000ffcc,0xaaaaaaaaaaaaaaaa)],[3],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffff0000fafa],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfafa0000fafa,0xfafafafafafafafa,0xffff0000ffff0000),(0xffffffff0000fafa,0xfafa0000fafa,0xffffffff00000000)],[],[]),
  ([0xfafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfafa0000fafa,0xfafafafafafafafa,0xffff0000ffff0000),(0xfafa,0xfafa0000fafa,0xffffffff00000000)],[],[]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffffcccc],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffffffffffcccc,0xffffccccffffcccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffffffcccc)],[0],[(0,26),(2,27)]),
  ([0xffff0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00),(0xffffffffffaaffaa,0xffaaffaaffaaffaa,0xffffffff00000000),(0xffff0000ffaa,0xffff0000ffff0000,0xffffffffffaaffaa)],[],[]),
  ([0xffff0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfffffffffafafafa,0xfafafafafafafafa,0xffffffff00000000),(0xffff0000fafa,0xffff0000ffff0000,0xfffffffffafafafa)],[],[]),
  ([0xfafafafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffffafafafa],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfffffffffafafafa,0xfafafafafafafafa,0xffffffff00000000),(0xfafafafa,0xffffffff00000000,0xfffffffffafafafa)],[0],[(0,27),(4,27)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffffffffffcccc,0xffffccccffffcccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffffffcccc)],[0, 1],[(2,27)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaaaaaffffeeee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffccccffffcccc,0xcccccccccccccccc,0xffff0000ffff0000),(0xffffcccc,0xffffccccffffcccc,0xffffffff00000000),(0xaaaaaaaaffffeeee,0xffffcccc,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaaaaaffeeffee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffccffccffccffcc,0xff00ff00ff00ff00,0xcccccccccccccccc),(0xffccffcc,0xffccffccffccffcc,0xffffffff00000000),(0xaaaaaaaaffeeffee,0xffccffcc,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafa00fa00,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xfafafafafa00fa00,0xfafafafafafafafa,0xffffffffff00ff00)],[0, 5],[(8,28)]),
  ([0xf0f00000a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000),(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xf0f00000a0a,0xfffff0f0fffff0f0,0xffffffffaaaaaaaa)],[],[]),
  ([0xffff0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffffffffffaaaa,0xaaaaaaaaaaaaaaaa,0xffffffffffff0000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffffffaaaa)],[0],[(0,16)]),
  ([0xffff0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffcccccccc],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xfffffffffcfcfcfc,0xf0f0f0f0f0f0f0f0,0xffffffffcccccccc),(0xffff0000fcfc,0xffff0000ffff0000,0xfffffffffcfcfcfc)],[1],[]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffffffffeeeeeeee,0xcccccccccccccccc,0xffffffffaaaaaaaa),(0xeeeeeeee,0xffffffff00000000,0xffffffffeeeeeeee)],[0],[(0,17)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaffaaffaaffaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xff00ff00ff0000,0xff00ff00ff00ff00,0xffffffffffff0000),(0xaaffaaffaaffaaaa,0xff00ff00ff0000,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaffaaffaafaaafa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xff00ff00f000f0,0xff00ff00ff00ff00,0xfffffffff0f0f0f0),(0xaaffaaffaafaaafa,0xff00ff00f000f0,0xaaaaaaaaaaaaaaaa)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaffffaaaaffaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xffff0000ff00,0xffff0000ffff0000,0xffffffffff00ff00),(0xaaaaffffaaaaffaa,0xffff0000ff00,0xaaaaaaaaaaaaaaaa)],[3],[]),
  ([0xffff0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f0f0f0],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[2],[(0,25)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffffcccccccc,0xffffffffffff0000],[(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc)],[5],[]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000),(0xffffffffffffcccc,0xcccccccccccccccc,0xffffffffffff0000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffffffcccc)],[0],[(0,26)]),
  ([0xfafafafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xfffffffffafafafa,0xf0f0f0f0f0f0f0f0,0xffffffffaaaaaaaa),(0xfafafafa,0xffffffff00000000,0xfffffffffafafafa)],[0],[(0,27)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaffffaaaaeeee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc),(0xaaaaffffaaaaeeee,0xffff0000cccc,0xaaaaaaaaaaaaaaaa)],[3],[(3,29)]),
  ([0xaaaaaaaaaaaaaaaa,0xaaffaaffaaeeaaee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xff00ff00cc00cc,0xff00ff00ff00ff00,0xffffffffcccccccc),(0xaaffaaffaaeeaaee,0xff00ff00cc00cc,0xaaaaaaaaaaaaaaaa)],[0],[]),
  ([0xaaaaaaaaaaaaaaaa,0xaaaaffffaaaafafa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000),(0xffff0000f0f0,0xffff0000ffff0000,0xfffffffff0f0f0f0),(0xaaaaffffaaaafafa,0xffff0000f0f0,0xaaaaaaaaaaaaaaaa)],[],[])
]
def w5_L7 : Array W5Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xfffff0f0fffff0f0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0)],[0, 1, 2, 3, 4],[(0,3),(0,6),(0,10),(1,9),(2,4),(2,5),(4,7),(6,8),(7,11),(8,0),(8,2),(9,1)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffff00ffffff00,0xffffffff00000000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffff00ffffff00,0xffff0000ffff0000,0xff00ff00ff00ff00)],[0, 1, 2, 3, 4],[(0,0),(0,6),(0,12),(0,16),(1,15),(1,17),(3,13),(4,14),(5,15),(5,17),(6,0),(6,6),(6,16),(8,12),(8,14),(9,13)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000,0xffffffffffff0000],[(0xffffaaaaffffaaaa,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[0, 1, 3, 4, 5],[(0,10),(0,16),(0,19),(0,21),(0,22),(0,24),(0,26),(1,20),(1,29),(2,23),(3,27),(3,28),(5,25),(6,2),(6,14),(9,18)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfefefefefefefefe,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfefefefefefefefe,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0)],[0, 1, 2, 3, 4, 5],[(0,32),(0,33),(0,34),(0,35),(1,26),(1,31),(2,19),(2,30),(4,32),(4,33),(5,6),(8,19),(8,30),(9,6)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xfefefefefefefefe,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfefefefefefefefe,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0)],[0, 2],[(1,37),(2,30),(8,36)]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xeeee0000eeee,0xeeeeeeeeeeeeeeee,0xffff0000ffff0000)],[0, 1, 2, 3, 4, 5],[(0,15),(0,20),(0,27),(0,30),(0,39),(0,41),(0,42),(0,43),(4,38),(6,40)]),
  ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa),(0xeeee0000eeee,0xeeeeeeeeeeeeeeee,0xffff0000ffff0000)],[0, 1, 4],[(0,13),(0,30)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffeeffeeffeeffee,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffeeffeeffeeffee,0xeeeeeeeeeeeeeeee,0xff00ff00ff00ff00)],[0, 1, 2, 3, 4, 5],[(0,32),(0,45),(0,48),(0,49),(1,22),(1,44),(2,32),(2,45),(4,46),(4,47),(8,22),(8,44)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffeeffeeffeeffee,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffeeffeeffeeffee,0xeeeeeeeeeeeeeeee,0xff00ff00ff00ff00)],[3],[(1,50),(4,46),(8,50)]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000)],[0, 1, 2, 3, 4, 5],[(0,23),(0,46),(0,51),(0,52),(0,53),(0,54),(4,41),(6,23),(6,51),(6,54),(8,41)]),
  ([0xfcfc0000fcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfcfcfcfcfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccc),(0xfcfc0000fcfc,0xfcfcfcfcfcfcfcfc,0xffff0000ffff0000)],[1, 2, 4],[(0,4),(0,46),(6,4)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffeeeeeeee],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[0, 1, 2, 3, 4, 5],[(0,34),(0,48),(0,56),(0,62),(1,55),(2,34),(2,56),(4,59),(4,60),(4,61),(6,57),(6,58),(7,8),(7,16),(8,55),(9,8),(9,16)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffeeeeeeee],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[3, 5],[(0,62),(1,63),(4,64),(8,63)]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[0, 1, 2, 3, 4, 5],[(0,9),(0,17),(0,43),(0,62),(2,9),(2,17),(2,43),(3,65),(4,53),(4,65),(6,66)]),
  ([0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xeeeeeeee,0xeeeeeeeeeeeeeeee,0xffffffff00000000)],[0, 1, 5],[(0,29),(0,62),(2,29)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfff0fff0fff0fff0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00)],[0, 1, 2, 3],[(0,32),(0,67),(1,6),(1,12),(2,41),(4,54),(5,6),(7,41),(8,3),(8,54)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffff0f0fffff0f0,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000)],[0, 1, 2],[(0,39),(0,69),(1,0),(4,32),(7,68),(7,70),(8,0),(9,68)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[0, 1, 2],[(0,34),(0,72),(1,16),(2,19),(2,43),(5,14),(7,73),(8,21),(8,71)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[0, 1, 3, 5],[(0,48),(0,74),(1,10),(1,24),(3,5),(4,5),(4,47),(4,53),(6,57),(7,75),(8,10),(8,24)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000,0xffffffffffff0000],[(0xffffccccffffcccc,0xffff0000ffff0000,0xcccccccccccccccc),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[1, 4, 5],[(0,8),(0,19),(0,47),(0,80),(1,78),(2,79),(2,83),(3,81),(3,82),(6,5),(6,22),(7,77),(8,76)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xfefefefefefefefe,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfefefefefefefefe,0xcccccccccccccccc,0xfafafafafafafafa)],[0, 1, 2],[(1,31),(2,84),(8,84)]),
  ([0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa)],[0, 1, 2, 3, 4, 5],[(0,7),(0,31),(0,76),(0,86),(0,87),(0,88),(4,85),(6,7),(6,76),(6,86),(8,85)]),
  ([0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000],[(0xffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00),(0xffaa0000ffaa,0xffff0000ffff0000,0xffaaffaaffaaffaa)],[0, 3, 4],[(0,31)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00)],[0, 1],[(0,32),(0,89),(1,86),(5,86)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffcccccccc],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000)],[0, 1],[(0,34),(0,90),(1,26),(1,88),(5,91)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xfffafffafffafffa,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfffafffafffafffa,0xfafafafafafafafa,0xff00ff00ff00ff00)],[0, 3],[(4,44),(5,93),(8,92)]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfafa0000fafa,0xfafafafafafafafa,0xffff0000ffff0000)],[0, 1, 2, 3, 4, 5],[(0,44),(0,68),(0,70),(0,79),(0,81),(0,96),(0,97),(6,95),(7,86),(8,94)]),
  ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa),(0xfafa0000fafa,0xfafafafafafafafa,0xffff0000ffff0000)],[0, 2, 4],[(0,1),(0,44)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffffafafafa],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfffffffffafafafa,0xfafafafafafafafa,0xffffffff00000000)],[0, 1, 2, 3, 4, 5],[(0,34),(0,100),(0,101),(1,48),(1,99),(2,98),(4,100),(5,10),(7,48),(8,98),(9,10)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffffafafafa],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfffffffffafafafa,0xfafafafafafafafa,0xffffffff00000000)],[0, 5],[(0,101),(2,102),(8,102)]),
  ([0xfafafafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfafafafa,0xfafafafafafafafa,0xffffffff00000000)],[0, 1, 2, 3, 4, 5],[(0,11),(0,97),(0,101),(1,88),(2,103),(3,104),(4,11),(4,97),(6,104)]),
  ([0xfafafafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xfafafafa,0xfafafafafafafafa,0xffffffff00000000)],[0, 2, 5],[(0,83),(0,101),(4,83)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[0, 2, 3],[(0,105),(2,8),(3,2),(4,22),(4,97),(5,106),(7,48),(8,80)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa,0xffffffffeeeeeeee],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffffffffeeeeeeee,0xcccccccccccccccc,0xffffffffaaaaaaaa)],[0, 1, 3],[(0,109),(1,55),(3,108),(8,107)]),
  ([0xffff0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa)],[0, 1, 2, 3, 4, 5],[(0,28),(0,55),(0,73),(0,82),(0,106),(0,113),(4,111),(6,112),(7,91),(8,110)]),
  ([0xffff0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xffff0000aaaa,0xffff0000ffff0000,0xffffffffaaaaaaaa)],[0, 4, 5],[(0,18),(0,55)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa,0xfffffffff0f0f0f0],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xfffffffff0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000)],[0, 2, 5],[(0,57),(0,113),(2,21),(2,114),(4,57),(4,113),(5,24),(5,77),(5,80),(8,21),(8,114),(9,24),(9,80)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa,0xfffffffffafafafa],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000),(0xfffffffffafafafa,0xf0f0f0f0f0f0f0f0,0xffffffffaaaaaaaa)],[0, 2],[(0,116),(2,98),(8,115)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc)],[0, 1, 2, 3, 4, 5],[(0,25),(0,71),(0,75),(0,98),(0,117),(2,106),(4,118),(6,119),(8,73)]),
  ([0xffff0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffcccccccc],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000cccc,0xffff0000ffff0000,0xffffffffcccccccc)],[1, 4, 5],[(0,78),(0,98),(0,114)])
]
def w5_L8 : Array W5Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xeeeeeeeeeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc)],[0, 1, 2, 3, 4, 5],[(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(1,0),(1,1),(1,2),(2,3),(2,4),(2,5),(2,6),(2,15),(2,17),(4,9),(4,10),(8,0),(8,1),(8,2)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xfafafafafafafafa,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0)],[0, 1, 2, 3, 4, 5],[(0,3),(0,20),(0,23),(0,24),(0,25),(0,26),(0,27),(0,28),(0,29),(0,30),(0,31),(0,32),(1,7),(1,21),(1,22),(2,19),(4,23),(4,25),(4,26),(4,27),(4,32),(5,0),(5,16),(7,7),(8,19),(9,0)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa],[(0xffffffffaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xffffffff00000000)],[0, 1, 2, 3, 4, 5],[(0,11),(0,28),(0,33),(0,34),(0,35),(0,36),(0,37),(1,11),(1,28),(1,33),(1,34),(1,35),(1,36),(1,37),(2,24),(2,38),(2,39),(3,38),(3,39),(4,17),(5,17),(6,32),(7,18),(7,32),(8,2),(8,19),(9,2),(9,19)])
]
def w5_L9 : Array W5Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[],[0, 1, 2, 3, 4, 5],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,0),(6,2),(7,0),(7,1),(8,0),(8,1)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_4_0 : checkBlockW5 4 w5_L4 (Array.mk []) 0 3 = true := by decide +kernel
theorem w5_chk_4 : ∀ i < w5_L4.size, checkNodeW5 4 w5_L4 (Array.mk []) i = true :=
  fun i hi => checkBlockW5_at w5_chk_4_0 i (Nat.zero_le _) (by simpa [w5_L4] using hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_5_0 : checkBlockW5 5 w5_L5 w5_L4 0 30 = true := by decide +kernel
theorem w5_chk_5 : ∀ i < w5_L5.size, checkNodeW5 5 w5_L5 w5_L4 i = true :=
  fun i hi => checkBlockW5_at w5_chk_5_0 i (Nat.zero_le _) (by simpa [w5_L5] using hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_6_0 : checkBlockW5 6 w5_L6 w5_L5 0 30 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_6_30 : checkBlockW5 6 w5_L6 w5_L5 30 30 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_6_60 : checkBlockW5 6 w5_L6 w5_L5 60 30 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_6_90 : checkBlockW5 6 w5_L6 w5_L5 90 30 = true := by decide +kernel
theorem w5_chk_6 : ∀ i < w5_L6.size, checkNodeW5 6 w5_L6 w5_L5 i = true := by
  intro i hi
  have hsz : i < 120 := by simpa [w5_L6] using hi
  by_cases h0 : i < 30
  · exact checkBlockW5_at w5_chk_6_0 i (by omega) (by omega)
  ·
    by_cases h1 : i < 60
    · exact checkBlockW5_at w5_chk_6_30 i (by omega) (by omega)
    ·
      by_cases h2 : i < 90
      · exact checkBlockW5_at w5_chk_6_60 i (by omega) (by omega)
      ·
        exact checkBlockW5_at w5_chk_6_90 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_7_0 : checkBlockW5 7 w5_L7 w5_L6 0 30 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_7_30 : checkBlockW5 7 w5_L7 w5_L6 30 10 = true := by decide +kernel
theorem w5_chk_7 : ∀ i < w5_L7.size, checkNodeW5 7 w5_L7 w5_L6 i = true := by
  intro i hi
  have hsz : i < 40 := by simpa [w5_L7] using hi
  by_cases h0 : i < 30
  · exact checkBlockW5_at w5_chk_7_0 i (by omega) (by omega)
  ·
    exact checkBlockW5_at w5_chk_7_30 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_8_0 : checkBlockW5 8 w5_L8 w5_L7 0 3 = true := by decide +kernel
theorem w5_chk_8 : ∀ i < w5_L8.size, checkNodeW5 8 w5_L8 w5_L7 i = true :=
  fun i hi => checkBlockW5_at w5_chk_8_0 i (Nat.zero_le _) (by simpa [w5_L8] using hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w5_chk_9_0 : checkBlockW5 9 w5_L9 w5_L8 0 1 = true := by decide +kernel
theorem w5_chk_9 : ∀ i < w5_L9.size, checkNodeW5 9 w5_L9 w5_L8 i = true :=
  fun i hi => checkBlockW5_at w5_chk_9_0 i (Nat.zero_le _) (by simpa [w5_L9] using hi)

theorem w5_L4_sound : ∀ i < w5_L4.size, ¬ live (basicOps 64) w5_goal 4 (w5_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) (fun j hj => by simp at hj) w5_chk_4
theorem w5_L5_sound : ∀ i < w5_L5.size, ¬ live (basicOps 64) w5_goal 5 (w5_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) w5_L4_sound w5_chk_5
theorem w5_L6_sound : ∀ i < w5_L6.size, ¬ live (basicOps 64) w5_goal 6 (w5_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) w5_L5_sound w5_chk_6
theorem w5_L7_sound : ∀ i < w5_L7.size, ¬ live (basicOps 64) w5_goal 7 (w5_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) w5_L6_sound w5_chk_7
theorem w5_L8_sound : ∀ i < w5_L8.size, ¬ live (basicOps 64) w5_goal 8 (w5_L8[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) w5_L7_sound w5_chk_8
theorem w5_L9_sound : ∀ i < w5_L9.size, ¬ live (basicOps 64) w5_goal 9 (w5_L9[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) w5_L8_sound w5_chk_9

theorem w5_sublists : w5_rows.sublists.filter (fun ws => cover 64 jumps6 w5_goal ws) = [w5_rows] := by decide +kernel
theorem w5_top_match : sameSet (w5_rows.map (actB 64 (w5_pow[0]?.getD []))) (w5_L9[0]?.getD ([], [], [], [])).1 = true := by decide +kernel

theorem w5_no_build : ¬ build (basicOps 64) w5_goal 9 w5_rows.toFinset :=
  no_build_of_root w5_G_valid (by decide) w5_sublists w5_top_match (w5_L9_sound 0 (by decide))

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev W7 := BitVec 128
abbrev basicOps7 (a b : W7) : Finset W7 := (ops 128 a b).toFinset

def holds (av : Finset W7) (z : W7) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W7} {z a : W7} (h : holds av z) : holds (insert a av) z := by
  rcases h with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_not {av : Finset W7} {z : W7} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W7) (z : W7) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps7 a b, holds (insert w av) z

theorem reachable_not {av : Finset W7} {z : W7} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

theorem and_reach {av : Finset W7} {x y : W7} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W7) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W7) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 128 &&& y); rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W7) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 128); rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W7) (hw : w ∈ basicOps7 a b) (z : W7) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps7, ops] : a &&& b ∈ basicOps7 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps7, ops] : a &&& ~~~b ∈ basicOps7 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps7, ops] : b &&& ~~~a ∈ basicOps7 a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps7, ops] : a ||| b ∈ basicOps7 a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W7} {x y : W7} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit7 (k : Fin 128) (z : W7) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit7 (w : List W7) (i : ℕ) (k : Fin 128) :
    (w.map (bit7 k)).getD i false = bit7 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt h), bit7]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W7) (g : Gate) : W7 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem action_spec (w : List W7) (g : Gate) (hg : legal g) (k : Fin 128) :
    step (w.map (bit7 k)) g = (w ++ [action w g]).map (bit7 k) := by
  obtain ⟨op, args⟩ := g; obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop; change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W7)[k.val] = false := by simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit7, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit7, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W7} {w : List W7} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]; exact .inl rfl

theorem gate_reach (w : List W7) (av : Finset W7) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op, args⟩ := g; obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop; change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : W7, x ||| (0 : W7) = x from fun x => BitVec.or_zero,
    show ∀ x : W7, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

def goal7 : W7 := 0xfffffffffffffffefffffffefefceea0
def rows7 : List W7 := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]

theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W7) (av : Finset W7) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit7 k))).getD out false = bit7 k goal7) :
    ∃ t, (t = goal7 ∨ t = ~~~goal7) ∧ build basicOps7 t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal7 := by
      apply BitVec.eq_of_getElem_eq; intro i hi
      simpa only [List.foldl_nil, read_bit7, bit7] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim ((by decide : goal7 ≠ 0) zero)
    · exact False.elim ((by decide : goal7 ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W7 => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit7 k))).getD out false = bit7 k goal7 := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W7) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

def F (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)

theorem sample7_ok : ∀ k : Fin 128, F (fun i => (rows7.getD i.val 0)[k.val]) = goal7[k.val] := by decide +kernel
theorem bridge : ∀ x : Fin 7 → Bool, decide (∃ i < ([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = F x := by
  decide +kernel

def gw (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def upperW : List Gate := [⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [14, 15]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩]

theorem legalUpper : ∀ g ∈ upperW, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [upperW]

set_option maxHeartbeats 2200000 in
theorem correctUpper : ∀ x : Fin 7 → Bool, Circuit.eval ⟨upperW,20⟩ (List.ofFn x) = gw x := by
  decide +kernel

end PEqualNP.Outside.L_meta_10460.Evidence

namespace PEqualNP.Outside.L_meta_10460.Signed
open PEqualNP.Outside.L_meta_10460.Evidence

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def branch {n : Nat} (k : Nat) (ws : List (BitVec n))
    (f : BitVec n → BitVec n → BitVec n → List (BitVec n) → Bool) : Bool :=
  (pairs ws).any fun (a,b,r) =>
    (ops n a b).any fun z =>
      z != 0 && z != BitVec.allOnes n && !(ws.contains z) &&
        (keepChoices a b r).any fun kept =>
          decide ((z :: kept).length ≤ k + 1) && f z a b (z :: kept)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem branch_or_done {n k : Nat} {ws : List (BitVec n)} {g : BitVec n}
    (hn : ws.Nodup) (h : live (basicOps n) g (k + 1) ws.toFinset)
    (f : BitVec n → BitVec n → BitVec n → List (BitVec n) → Bool)
    (hf : ∀ z a b ys, ys.Nodup → live (basicOps n) g k ys.toFinset → f z a b ys = true) :
    ws.contains g = true ∨ branch k ws f = true := by
  rcases first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hznot,t,hs,ht⟩
  · left
    apply List.contains_iff_mem.2
    exact List.mem_toFinset.1 (done.symm ▸ Finset.mem_singleton_self g)
  · right
    obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.1 ha) (List.mem_toFinset.1 hb) hab
    have pick {u v : BitVec n} (hm' : (u,v,r) ∈ pairs ws) (hp' : ws.Perm (u :: v :: r))
        (hs' : ws.toFinset = insert u (insert v t)) (hz' : z ∈ basicOps n u v) :
        branch k ws f = true := by
      obtain ⟨kept,hkept,hnd,hset⟩ := recover_kept hp' hn hs'
      have hnew : z ∉ kept := by
        intro hz
        apply hznot
        rw [hs']
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hset ▸ List.mem_toFinset.2 hz))
      have hn' := List.nodup_cons.2 ⟨hnew,hnd⟩
      have ht' : live (basicOps n) g k (z :: kept).toFinset := by simpa [hset] using ht
      have hl := live_card ht'
      rw [List.toFinset_card_of_nodup hn'] at hl
      have hzw : ws.contains z = false := by simpa using hznot
      have ho := List.mem_filter.1 (List.mem_toFinset.1 hz')
      unfold branch
      apply List.any_eq_true.2 ⟨(u,v,r), hm', ?_⟩
      apply List.any_eq_true.2 ⟨z, ho.1, ?_⟩
      simp only [ho.2, hzw, Bool.not_false, Bool.true_and]
      exact List.any_eq_true.2 ⟨kept, hkept, Bool.and_eq_true_iff.2 ⟨decide_eq_true hl, hf _ _ _ _ hn' ht'⟩⟩
    rcases hm with fwd | rev
    · exact pick fwd hp hs hz
    · exact pick rev (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap n a b ▸ hz)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def pairReject {n : Nat} (g : BitVec n) (ws : List (BitVec n)) (code : Nat) : Bool :=
  let u := (code >>> 8) &&& 255
  let v := (code >>> 16) &&& 255
  decide (u < n) && decide (v < n) && (g.getLsbD u != g.getLsbD v) &&
    ws.all (fun w => w.getLsbD u == w.getLsbD v)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem pairReject_no {n k : Nat} {g : BitVec n} {ws code}
    (h : pairReject g ws code = true) : ¬ live (basicOps n) g k ws.toFinset := by
  let u := (code >>> 8) &&& 255
  let v := (code >>> 16) &&& 255
  change (decide (u < n) && decide (v < n) && (g.getLsbD u != g.getLsbD v) &&
    ws.all (fun w => w.getLsbD u == w.getLsbD v)) = true at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, beq_iff_eq] at h
  intro hl
  obtain ⟨w,hw,hd⟩ := live_separates (fun z : BitVec n => z.getLsbD u ≠ z.getLsbD v)
    h.1.2 (ops_diff_ij u v h.1.1.1 h.1.1.2) hl
  exact hd (h.2 w (List.mem_toFinset.1 hw))

end PEqualNP.Outside.L_meta_10460.Signed

namespace PEqualNP.Outside.L_meta_10460.Signed
open PEqualNP.Outside.L_meta_10460.Evidence
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def replay {M : Nat} (m : BitVec M) (bank : List (BitVec M)) :
    List (BitVec M × BitVec M × BitVec M) → List (BitVec M) → Bool
  | [], targets => targets.all (fun t => (t &&& m) == 0 || bank.contains (t &&& m))
  | (v, a, b) :: rest, targets =>
    bank.contains a && bank.contains b && (ops M a b).contains v &&
    replay m (v :: bank) rest targets

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem replay_ok {M N : Nat} (hn : 0 < N) (idxs : List ℕ) (hlen : idxs.length = N) (hlt : ∀ idx ∈ idxs, idx < M)
    (m : BitVec M) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (g : BitVec N)
    (steps : List (BitVec M × BitVec M × BitVec M)) (targets : List (BitVec M)) :
    ∀ (bank : List (BitVec M)) (k : ℕ),
      replay m bank steps targets = true →
      build (basicOps N) g k (nonZeroImg (projS N idxs) targets.toFinset) →
      build (basicOps N) g (k + steps.length) (nonZeroImg (projS N idxs) bank.toFinset) := by
  let f : BitVec M → BitVec N := projS N idxs
  induction steps with
  | nil =>
    intro bank k hchk hb
    simp only [replay, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hchk
    simp only [List.length_nil, Nat.add_zero]
    apply build_mono_av _ hb
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu ⊢
    obtain ⟨hne, t, ht, rfl⟩ := hu
    rcases hchk t ht with h0 | hmem
    · exfalso; apply hne
      rw [← projS_mask N idxs m hm t, h0, projS_zero]
    · exact ⟨hne, t &&& m, hmem, projS_mask N idxs m hm t⟩
  | cons s rest ih =>
    obtain ⟨v, a, b⟩ := s
    intro bank k hchk hb
    simp only [replay, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨ha, hb_mem⟩, hv⟩, hrest⟩ := hchk
    have hb' := ih (v :: bank) k hrest hb
    simp only [List.length_cons, show k + (rest.length + 1) = (k + rest.length) + 1 by omega]
    have hfv : f v ∈ ops N (f a) (f b) := projS_ops N hn idxs hlen hlt a b v hv
    have hsub_ins (hmem_v : f v = 0 ∨ f v ∈ nonZeroImg f bank.toFinset) :
        nonZeroImg f (v :: bank).toFinset ⊆ nonZeroImg f bank.toFinset := by
      intro u hu
      simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu ⊢
      obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
      · rcases hmem_v with h0 | hm'
        · exact (hne h0).elim
        · exact Finset.mem_erase.mp hm' |>.imp_right (fun hi => by simpa [List.mem_toFinset] using hi)
      · exact ⟨hne, w, hw, rfl⟩
    by_cases hv0 : f v = 0
    · exact Or.inl (build_mono_av (hsub_ins (Or.inl hv0)) hb')
    · by_cases ha0 : f a = 0
      · rcases ops_zero_left N (f b) (f v) (ha0 ▸ hfv) with h0 | h1
        · exact (hv0 h0).elim
        · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb_mem, h1.symm⟩⟩))) hb')
      · by_cases hb0 : f b = 0
        · rcases ops_zero_right N (f a) (f v) (hb0 ▸ hfv) with h0 | h1
          · exact (hv0 h0).elim
          · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
        · by_cases hab : f a = f b
          · rcases ops_self N (f a) (f v) (hab ▸ hfv) with h0 | h1
            · exact (hv0 h0).elim
            · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
          · refine Or.inr ⟨f a, Finset.mem_erase.mpr ⟨ha0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr ha)⟩,
              f b, Finset.mem_erase.mpr ⟨hb0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hb_mem)⟩,
              hab, f v, ?_, ?_⟩
            · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
              exact ⟨hfv, hv0, projS_ne_allOnes N hn idxs v⟩
            · apply build_mono_av _ hb'
              intro u hu
              simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu
              obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hw)⟩)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def stepsFor {M : Nat} (bank : List (BitVec M)) : Nat → Nat → List (BitVec M × BitVec M × BitVec M)
  | 0, _ => []
  | p + 1, bits =>
    let op := bits &&& 3
    let a := bank.getD ((bits >>> 2) &&& 15) 0
    let b := bank.getD ((bits >>> 6) &&& 15) 0
    let w := (ops M a b).getD op 0
    (w,a,b) :: stepsFor (bank ++ [w]) p (bits >>> 10)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem stepsFor_length {M} (bank : List (BitVec M)) (p bits : Nat) :
    (stepsFor bank p bits).length = p := by
  induction p generalizing bank bits with
  | zero => rfl
  | succ p ih => simp [stepsFor, ih]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def cut {M} (lb fuel : Nat) (mask : BitVec M) (stock ws : List (BitVec M)) (hint : Nat) : Bool :=
  let flat := (ws.filter (fun u => u &&& mask == 0)).length
  let p := (hint >>> 8) &&& 15
  decide (fuel - flat + p < lb) && replay mask stock (stepsFor stock p (hint >>> 12)) ws

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem cut_no {M N : Nat} (hn : 0 < N) (idxs : List Nat)
    (hlen : idxs.length = N) (hlt : ∀ i ∈ idxs, i < M)
    (mask : BitVec M) (hm : ∀ i ∈ idxs, mask.getLsbD i = true)
    (stock : List (BitVec M)) (goal : BitVec M) (g : BitVec N) (hnz : g ≠ 0)
    (rows : List (BitVec N)) (hg : projS N idxs goal = g)
    (hst : stock.all (fun w => rows.contains (projS N idxs w)) = true)
    {lb k : Nat} (low : ¬build (basicOps N) g (lb-1) rows.toFinset)
    {ws : List (BitVec M)} (hnd : ws.Nodup) (hint : Nat)
    (hc : cut lb k mask stock ws hint = true) : ¬live (basicOps M) goal k ws.toFinset := by
  intro h
  have hopp : ∀ a b z : BitVec M, z ∈ basicOps M a b → z ∈ ops M a b :=
    fun _ _ _ hh => (List.mem_filter.1 (List.mem_toFinset.1 hh)).1
  have ih := live_restrict hn idxs hlen hlt hopp hg hnz h
  have hflat : (ws.filter (fun w => w &&& mask == 0)).length ≤ zCount (projS N idxs) ws.toFinset := by
    have hnf : (ws.filter (fun w => w &&& mask == 0)).Nodup := hnd.filter _
    rw [← List.toFinset_card_of_nodup hnf]
    apply Finset.card_le_card
    intro w hw
    simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hw
    exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 hw.1, by rw [← projS_mask N idxs mask hm w, hw.2, projS_zero]⟩
  simp only [cut, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hre := replay_ok hn idxs hlen hlt mask hm g _ ws stock _ hc.2 ih
  have hsub : nonZeroImg (projS N idxs) stock.toFinset ⊆ rows.toFinset := by
    intro w hw
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hw
    obtain ⟨_,v,hv,rfl⟩ := hw
    exact List.mem_toFinset.2 (List.contains_iff_mem.1 (List.all_eq_true.1 hst v hv))
  apply low
  apply build_mono_k _ (build_mono_av hsub hre)
  rw [stepsFor_length]
  have hi := hc.1
  omega

end PEqualNP.Outside.L_meta_10460.Signed

namespace PEqualNP.Outside.L_meta_10460.Signed
open PEqualNP.Outside.L_meta_10460.Evidence
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def addNeedS {M : Nat} (stock needed : List (BitVec M)) (u : BitVec M) : List (BitVec M) :=
  if u == 0 || stock.contains u || needed.contains u then needed else u :: needed

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def buildNeededS {M : Nat} (m : BitVec M) (stock : List (BitVec M)) :
    List (BitVec M × BitVec M × BitVec M) → List (BitVec M) → List (BitVec M)
  | [], needed => needed
  | (w, a, b) :: rest, needed =>
    let pw := w &&& m
    let needed' := if needed.contains pw then addNeedS stock (addNeedS stock needed (a &&& m)) (b &&& m) else needed
    buildNeededS m stock rest needed'

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def buildStepsS {M : Nat} (m : BitVec M) (needed : List (BitVec M)) :
    List (BitVec M × BitVec M × BitVec M) → List (BitVec M) → List (BitVec M × BitVec M × BitVec M)
  | [], _ => []
  | (w, a, b) :: rest, bank =>
    let pw := w &&& m
    let pa := a &&& m
    let pb := b &&& m
    if needed.contains pw && pw != 0 && !bank.contains pw &&
       bank.contains pa && bank.contains pb && (ops M pa pb).contains pw then
      (pw, pa, pb) :: buildStepsS m needed rest (pw :: bank)
    else
      buildStepsS m needed rest bank

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def autoCut {M : Nat} (lb fuel : ℕ) (m : BitVec M) (stock : List (BitVec M))
    (hist : List (BitVec M × BitVec M × BitVec M)) (nxt : List (BitVec M)) : Bool :=
  let flat := (nxt.filter (fun u => (u &&& m) == 0)).length
  let rem := fuel - flat
  if Nat.blt rem lb then
    let start := nxt.foldl (fun acc u => addNeedS stock acc (u &&& m)) []
    if Nat.blt (start.length + rem) lb then
      let needed := buildNeededS m stock hist.reverse start
      if Nat.blt (needed.length + rem) lb then
        let steps := buildStepsS m needed hist stock
        Nat.blt (steps.length + rem) lb && replay m stock steps nxt
      else false
    else false
  else false

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem autoCut_no {M N lb : Nat} (hn : 0 < N) (target : BitVec M) (idxs : List ℕ) (hlen : idxs.length = N) (hlt : ∀ idx ∈ idxs, idx < M)
    (m : BitVec M) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true)
    (stock : List (BitVec M)) (g : BitVec N) (hgnz : g ≠ 0) (rows : List (BitVec N))
    (hg : projS N idxs target = g)
    (hstock : stock.all (fun w => rows.contains (projS N idxs w)) = true)
    (hnobuild : ¬ build (basicOps N) g (lb - 1) rows.toFinset)
    (fuel : ℕ) (hist : List (BitVec M × BitVec M × BitVec M)) (nxt : List (BitVec M))
    (hnd : nxt.Nodup) (hchk : autoCut lb fuel m stock hist nxt = true) :
    ¬ live (basicOps M) target fuel nxt.toFinset := by
  intro hlive
  unfold autoCut at hchk
  dsimp only at hchk
  split at hchk
  · split at hchk
    · split at hchk
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
        have hops64 : ∀ a b z : BitVec M, z ∈ basicOps M a b → z ∈ ops M a b := fun a b z hz =>
          (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
        have hres := live_restrict hn idxs hlen hlt hops64 hg hgnz hlive
        have hflat_le : (nxt.filter (fun u => (u &&& m) == 0)).length ≤ zCount (projS N idxs) nxt.toFinset := by
          have hndf : (nxt.filter (fun u => (u &&& m) == 0)).Nodup := hnd.filter _
          rw [← List.toFinset_card_of_nodup hndf]
          apply Finset.card_le_card
          intro u hu
          simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu.1, ?_⟩
          rw [← projS_mask N idxs m hm u, hu.2, projS_zero]
        have hrep := replay_ok hn idxs hlen hlt m hm g _ nxt stock _ hchk.2 hres
        have hsub : nonZeroImg (projS N idxs) stock.toFinset ⊆ rows.toFinset := by
          intro u hu
          simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu
          obtain ⟨_, v, hv, rfl⟩ := hu
          have h1 := List.all_eq_true.mp hstock v hv
          simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
          exact List.mem_toFinset.mpr h1
        exact hnobuild (build_mono_k (by omega) (build_mono_av hsub hrep))
      · cases hchk
    · cases hchk
  · cases hchk

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def misses {n} (g : BitVec n) (zeros : List Nat) (ws : List (BitVec n)) : Bool :=
  zeros.any fun u =>
    let diffs := ws.foldl (fun a w => a ||| (if w.getLsbD u then ~~~w else w)) 0
    let left := (g &&& ~~~diffs).toNat
    if left == 0 then false else pairReject g ws ((u <<< 8) ||| (left.log2 <<< 16))

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem misses_no {n k} {g : BitVec n} {zeros ws} (h : misses g zeros ws = true) :
    ¬ live (basicOps n) g k ws.toFinset := by
  obtain ⟨u, _, hu⟩ := List.any_eq_true.1 h
  dsimp only at hu
  split at hu
  · contradiction
  · exact pairReject_no hu

end PEqualNP.Outside.L_meta_10460.Signed

namespace PEqualNP.Outside.L_meta_10460.Signed
open PEqualNP.Outside.L_meta_10460.Evidence

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem root_no {n k} {g : BitVec n} {roots : List (BitVec n)} (jumps : List Nat)
    (hsub : roots.sublists.filter (fun ws => cover n jumps g ws) = [roots])
    (hn : ¬ live (basicOps n) g k roots.toFinset) : ¬build (basicOps n) g k roots.toFinset := by
  intro h
  obtain ⟨s, hs, hl⟩ := compress h
  let ws := roots.filter (· ∈ s)
  have hsubl : ws.Sublist roots := List.filter_sublist
  have heq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hcov : cover n jumps g ws = true := live_cover (heq.symm ▸ hl)
  have hmem : ws ∈ roots.sublists.filter (fun zs => cover n jumps g zs) :=
    List.mem_filter.mpr ⟨List.mem_sublists.mpr hsubl, hcov⟩
  rw [hsub, List.mem_singleton] at hmem
  rw [hmem] at heq
  exact hn (heq.symm ▸ hl)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
abbrev Hist (n : Nat) := List (BitVec n × BitVec n × BitVec n)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def explore {n} (g : BitVec n) (zeros : List Nat)
    (test : Nat → Hist n → List (BitVec n) → Bool) :
    Nat → Hist n → List (BitVec n) → Bool
  | 0, _, ws => ws.contains g
  | k + 1, hs, ws => ws.contains g ||
    branch k ws (fun z a b ys =>
      let hs' := hs ++ [(z,a,b)]
      !(misses g zeros ys) && !(test k hs' ys) && explore g zeros test k hs' ys)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem explore_ok {n} {g : BitVec n} {zeros test}
    (H : ∀ k hs ys, ys.Nodup → test k hs ys = true → ¬live (basicOps n) g k ys.toFinset) :
    ∀ k hist ys, ys.Nodup → live (basicOps n) g k ys.toFinset →
      explore g zeros test k hist ys = true := by
  intro k
  induction k with
  | zero =>
    intro hist ys _ hl
    change ys.toFinset = {g} at hl
    exact List.contains_iff_mem.2 (List.mem_toFinset.1 (hl.symm ▸ Finset.mem_singleton_self g))
  | succ k ih =>
    intro hist ws hnd hl
    simp only [explore, Bool.or_eq_true]
    apply branch_or_done hnd hl
    intro z a b ys hn h
    have hm : misses g zeros ys = false := Bool.eq_false_iff.2 (fun hb => misses_no hb h)
    have ht : test k (hist ++ [(z,a,b)]) ys = false := Bool.eq_false_iff.2 (fun hb => H _ _ _ hn hb h)
    simp [hm, ht, ih _ _ hn h]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def nodeCheck {n} (g : BitVec n) (zeros : List Nat) (k : Nat) (ws : List (BitVec n))
    (hs : Hist n) (close : Hist n → List (BitVec n) → Bool) (targets : List (List (BitVec n))) : Bool :=
  !(ws.contains g) && !branch k ws (fun z a b ys =>
    !(misses g zeros ys) && !(close (hs ++ [(z,a,b)]) ys) && !(targets.any (sameSet ys)))

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem node_no {n k} {g : BitVec n} {zeros ws hist close targets}
    (hn : List.Nodup ws)
    (hc : ∀ hs ys, ys.Nodup → close hs ys = true → ¬live (basicOps n) g k ys.toFinset)
    (ht : ∀ t ∈ targets, ¬live (basicOps n) g k t.toFinset)
    (hchk : nodeCheck g zeros k ws hist close targets = true) :
    ¬ live (basicOps n) g (k+1) ws.toFinset := by
  intro h
  have hgo := branch_or_done hn h (fun z a b ys =>
    !(misses g zeros ys) && !(close (hist ++ [(z,a,b)]) ys) && !(targets.any (sameSet ys))) (by
      intro z a b ys hy hh
      have hm : misses g zeros ys = false := Bool.eq_false_iff.2 (fun hp => misses_no hp hh)
      have hc' : close (hist ++ [(z,a,b)]) ys = false := Bool.eq_false_iff.2 (fun hp => hc _ _ hy hp hh)
      have ht' : targets.any (sameSet ys) = false := by
        apply List.any_eq_false.2
        intro t ht' he
        apply ht _ ht'
        rw [← sameSet_sound he]
        exact hh
      simp [hm,hc',ht'])
  simp only [nodeCheck, Bool.and_eq_true, Bool.not_eq_true'] at hchk
  rcases hgo with hp | hp
  · exact Bool.noConfusion (hchk.1.symm.trans hp)
  · exact Bool.noConfusion (hchk.2.symm.trans hp)

end PEqualNP.Outside.L_meta_10460.Signed

namespace PEqualNP.Outside.L_meta_10460.Shapes
open PEqualNP.Outside.L_meta_10460.Evidence PEqualNP.Outside.L_meta_10460.Signed

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def trG : BitVec 8 := 0xe8

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def trR : List (BitVec 8) := [170, 204, 240]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def trTest := explore trG [0, 1, 2, 4] (fun _ _ _ => false) 3 [] trR

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem trClosed : trTest = false := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem trLow : ¬build (basicOps 8) trG 3 trR.toFinset := by
  apply root_no [1, 2, 4] (by decide +kernel)
  intro h
  have ha : trTest = true := explore_ok (by simp) 3 [] trR (by decide +kernel) h
  rw [trClosed] at ha
  contradiction

end PEqualNP.Outside.L_meta_10460.Shapes

namespace PEqualNP.Outside.L_meta_10460.Shapes
open PEqualNP.Outside.L_meta_10460.Evidence PEqualNP.Outside.L_meta_10460.Signed

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clG : BitVec 16 := 0xfee8

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clR : List (BitVec 16) := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clSub0D : BitVec 16 := 0x5555

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clSub0S : List (BitVec 16) := [0x4444, 0x5050, 0x5500]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clSub0I : List Nat := [0, 2, 4, 6, 8, 10, 12, 14]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clSub1D : BitVec 16 := 0x3333

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clSub1S : List (BitVec 16) := [0x2222, 0x3030, 0x3300]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clSub1I : List Nat := [0, 1, 4, 5, 8, 9, 12, 13]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clSub2D : BitVec 16 := 0xf0f

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clSub2S : List (BitVec 16) := [0xa0a, 0xc0c, 0xf00]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clSub2I : List Nat := [0, 1, 2, 3, 8, 9, 10, 11]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clSub3D : BitVec 16 := 0xff

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clSub3S : List (BitVec 16) := [170, 204, 240]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clSub3I : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def cutsCl (k : Nat) (h : Hist 16) (ws : List (BitVec 16)) := autoCut 4 k clSub0D clSub0S h ws || autoCut 4 k clSub1D clSub1S h ws || autoCut 4 k clSub2D clSub2S h ws || autoCut 4 k clSub3D clSub3S h ws

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem cutsCl_ok (k : Nat) (h : Hist 16) (ws : List (BitVec 16)) (hn : ws.Nodup) (hc : cutsCl k h ws = true) : ¬live (basicOps 16) clG k ws.toFinset := by
  simp only [cutsCl, Bool.or_eq_true] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · exact autoCut_no (lb := 4) (by decide +kernel) clG clSub0I (by decide +kernel) (by decide +kernel) clSub0D (by decide +kernel) clSub0S trG (by decide +kernel) trR (by decide +kernel) (by decide +kernel) trLow k h ws hn hc
  · exact autoCut_no (lb := 4) (by decide +kernel) clG clSub1I (by decide +kernel) (by decide +kernel) clSub1D (by decide +kernel) clSub1S trG (by decide +kernel) trR (by decide +kernel) (by decide +kernel) trLow k h ws hn hc
  · exact autoCut_no (lb := 4) (by decide +kernel) clG clSub2I (by decide +kernel) (by decide +kernel) clSub2D (by decide +kernel) clSub2S trG (by decide +kernel) trR (by decide +kernel) (by decide +kernel) trLow k h ws hn hc
  · exact autoCut_no (lb := 4) (by decide +kernel) clG clSub3I (by decide +kernel) (by decide +kernel) clSub3D (by decide +kernel) clSub3S trG (by decide +kernel) trR (by decide +kernel) (by decide +kernel) trLow k h ws hn hc

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def clTest := explore clG [0, 1, 2, 4, 8] cutsCl 6 [] clR

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem clClosed : clTest = false := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem clLow : ¬build (basicOps 16) clG 6 clR.toFinset := by
  apply root_no [1, 2, 4, 8] (by decide +kernel)
  intro h
  have ha : clTest = true := explore_ok cutsCl_ok 6 [] clR (by decide +kernel) h
  rw [clClosed] at ha
  contradiction

end PEqualNP.Outside.L_meta_10460.Shapes

namespace PEqualNP.Outside.L_meta_10460.Shapes
open PEqualNP.Outside.L_meta_10460.Evidence PEqualNP.Outside.L_meta_10460.Signed

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new4G : BitVec 32 := 0xfffefea0

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new4R : List (BitVec 32) := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new4SubD : BitVec 32 := 0x33333333

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new4SubS : List (BitVec 32) := [0x22222222, 0x30303030, 0x33003300, 0x33330000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new4SubI : List Nat := [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem new4Low : ¬build (basicOps 32) new4G 7 new4R.toFinset :=
  root_no [1, 2, 4, 8, 16] (by decide +kernel) (cut_no (lb := 7) (by decide +kernel) new4SubI (by decide +kernel) (by decide +kernel) new4SubD (by decide +kernel) new4SubS new4G clG (by decide +kernel) clR (by decide +kernel) (by decide +kernel) clLow (by decide +kernel) 0 (by decide +kernel))

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new5G : BitVec 32 := 0xfffefee0

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new5R : List (BitVec 32) := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new5SubD : BitVec 32 := 0x33333333

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new5SubS : List (BitVec 32) := [0x22222222, 0x30303030, 0x33003300, 0x33330000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new5SubI : List Nat := [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem new5Low : ¬build (basicOps 32) new5G 7 new5R.toFinset :=
  root_no [1, 2, 4, 8, 16] (by decide +kernel) (cut_no (lb := 7) (by decide +kernel) new5SubI (by decide +kernel) (by decide +kernel) new5SubD (by decide +kernel) new5SubS new5G clG (by decide +kernel) clR (by decide +kernel) (by decide +kernel) clLow (by decide +kernel) 0 (by decide +kernel))

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new6G : BitVec 16 := 0xfea0

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new6R : List (BitVec 16) := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new6SubD : BitVec 16 := 0x3333

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new6SubS : List (BitVec 16) := [0x2222, 0x3030, 0x3300]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new6SubI : List Nat := [0, 1, 4, 5, 8, 9, 12, 13]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem new6Low : ¬build (basicOps 16) new6G 4 new6R.toFinset :=
  root_no [1, 2, 4, 8] (by decide +kernel) (cut_no (lb := 4) (by decide +kernel) new6SubI (by decide +kernel) (by decide +kernel) new6SubD (by decide +kernel) new6SubS new6G trG (by decide +kernel) trR (by decide +kernel) (by decide +kernel) trLow (by decide +kernel) 0 (by decide +kernel))

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new7G : BitVec 16 := 0xfea8

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new7R : List (BitVec 16) := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new7SubD : BitVec 16 := 0xf0f

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new7SubS : List (BitVec 16) := [0xa0a, 0xc0c, 0xf00]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def new7SubI : List Nat := [0, 1, 2, 3, 8, 9, 10, 11]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem new7Low : ¬build (basicOps 16) new7G 4 new7R.toFinset :=
  root_no [1, 2, 4, 8] (by decide +kernel) (cut_no (lb := 4) (by decide +kernel) new7SubI (by decide +kernel) (by decide +kernel) new7SubD (by decide +kernel) new7SubS new7G trG (by decide +kernel) trR (by decide +kernel) (by decide +kernel) trLow (by decide +kernel) 0 (by decide +kernel))

end PEqualNP.Outside.L_meta_10460.Shapes

namespace PEqualNP.Outside.L_meta_10460.Shapes
open PEqualNP.Outside.L_meta_10460.Evidence PEqualNP.Outside.L_meta_10460.Signed

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band0D : BitVec 128 := 0xffffffff00000000ffffffff

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band0S : List (BitVec 128) := [0xaaaaaaaa00000000aaaaaaaa, 0xcccccccc00000000cccccccc, 0xf0f0f0f000000000f0f0f0f0, 0xff00ff0000000000ff00ff00, 0xffff000000000000ffff0000, 0xffffffff0000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band0I : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band1D : BitVec 128 := 0xffffffffffffffff

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band1S : List (BitVec 128) := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band1I : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band2D : BitVec 128 := 0x5555000055550000555500005555

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band2S : List (BitVec 128) := [0x4444000044440000444400004444, 0x5050000050500000505000005050, 0x5500000055000000550000005500, 0x5555000000000000555500000000, 0x5555000055550000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band2I : List Nat := [0, 2, 4, 6, 8, 10, 12, 14, 32, 34, 36, 38, 40, 42, 44, 46, 64, 66, 68, 70, 72, 74, 76, 78, 96, 98, 100, 102, 104, 106, 108, 110]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band3D : BitVec 128 := 0xff000000ff000000ff000000ff

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band3S : List (BitVec 128) := [0xaa000000aa000000aa000000aa, 0xcc000000cc000000cc000000cc, 0xf0000000f0000000f0000000f0, 0xff00000000000000ff00000000, 0xff000000ff0000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band3I : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 64, 65, 66, 67, 68, 69, 70, 71, 96, 97, 98, 99, 100, 101, 102, 103]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band4D : BitVec 128 := 0xf0f00000f0f00000f0f00000f0f

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band4S : List (BitVec 128) := [0xa0a00000a0a00000a0a00000a0a, 0xc0c00000c0c00000c0c00000c0c, 0xf0000000f0000000f0000000f00, 0xf0f0000000000000f0f00000000, 0xf0f00000f0f0000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band4I : List Nat := [0, 1, 2, 3, 8, 9, 10, 11, 32, 33, 34, 35, 40, 41, 42, 43, 64, 65, 66, 67, 72, 73, 74, 75, 96, 97, 98, 99, 104, 105, 106, 107]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band5D : BitVec 128 := 0x3333000033330000333300003333

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band5S : List (BitVec 128) := [0x2222000022220000222200002222, 0x3030000030300000303000003030, 0x3300000033000000330000003300, 0x3333000000000000333300000000, 0x3333000033330000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band5I : List Nat := [0, 4, 8, 12, 1, 5, 9, 13, 32, 36, 40, 44, 33, 37, 41, 45, 64, 68, 72, 76, 65, 69, 73, 77, 96, 100, 104, 108, 97, 101, 105, 109]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band6D : BitVec 128 := 0xf000f000f000f000f000f000f000f

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band6S : List (BitVec 128) := [0xa000a000a000a000a000a000a000a, 0xc000c000c000c000c000c000c000c, 0xf0000000f0000000f0000000f0000, 0xf000f00000000000f000f00000000, 0xf000f000f000f0000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band6I : List Nat := [0, 2, 1, 3, 16, 18, 17, 19, 32, 34, 33, 35, 48, 50, 49, 51, 64, 66, 65, 67, 80, 82, 81, 83, 96, 98, 97, 99, 112, 114, 113, 115]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band7D : BitVec 128 := 0x330033003300330033003300330033

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band7S : List (BitVec 128) := [0x220022002200220022002200220022, 0x300030003000300030003000300030, 0x330000003300000033000000330000, 0x330033000000000033003300000000, 0x330033003300330000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band7I : List Nat := [0, 1, 16, 17, 4, 5, 20, 21, 32, 33, 48, 49, 36, 37, 52, 53, 64, 65, 80, 81, 68, 69, 84, 85, 96, 97, 112, 113, 100, 101, 116, 117]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band8D : BitVec 128 := 0x550055005500550055005500550055

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band8S : List (BitVec 128) := [0x440044004400440044004400440044, 0x500050005000500050005000500050, 0x550000005500000055000000550000, 0x550055000000000055005500000000, 0x550055005500550000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band8I : List Nat := [0, 2, 4, 6, 16, 18, 20, 22, 32, 34, 36, 38, 48, 50, 52, 54, 64, 66, 68, 70, 80, 82, 84, 86, 96, 98, 100, 102, 112, 114, 116, 118]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band9D : BitVec 128 := 0x11111111111111111111111111111111

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band9S : List (BitVec 128) := [0x10101010101010101010101010101010, 0x11001100110011001100110011001100, 0x11110000111100001111000011110000, 0x11111111000000001111111100000000, 0x11111111111111110000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band9I : List Nat := [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96, 100, 104, 108, 112, 116, 120, 124]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band10D : BitVec 128 := 0x3030303030303030303030303030303

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band10S : List (BitVec 128) := [0x2020202020202020202020202020202, 0x3000300030003000300030003000300, 0x3030000030300000303000003030000, 0x3030303000000000303030300000000, 0x3030303030303030000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band10I : List Nat := [0, 1, 16, 17, 8, 9, 24, 25, 32, 33, 48, 49, 40, 41, 56, 57, 64, 65, 80, 81, 72, 73, 88, 89, 96, 97, 112, 113, 104, 105, 120, 121]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band11D : BitVec 128 := 0x5050505050505050505050505050505

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band11S : List (BitVec 128) := [0x4040404040404040404040404040404, 0x5000500050005000500050005000500, 0x5050000050500000505000005050000, 0x5050505000000000505050500000000, 0x5050505050505050000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band11I : List Nat := [0, 8, 16, 24, 2, 10, 18, 26, 32, 40, 48, 56, 34, 42, 50, 58, 64, 72, 80, 88, 66, 74, 82, 90, 96, 104, 112, 120, 98, 106, 114, 122]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band12D : BitVec 128 := 0xffff0000ffff

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band12S : List (BitVec 128) := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band12I : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band14D : BitVec 128 := 0xf0f0f0f0f0f0f0f

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band14S : List (BitVec 128) := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band14I : List Nat := [0, 2, 1, 3, 16, 18, 17, 19, 8, 10, 9, 11, 24, 26, 25, 27, 32, 34, 33, 35, 48, 50, 49, 51, 40, 42, 41, 43, 56, 58, 57, 59]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band15D : BitVec 128 := 0x3333333333333333

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band15S : List (BitVec 128) := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band15I : List Nat := [0, 1, 16, 17, 8, 9, 24, 25, 4, 5, 20, 21, 12, 13, 28, 29, 32, 33, 48, 49, 40, 41, 56, 57, 36, 37, 52, 53, 44, 45, 60, 61]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band16D : BitVec 128 := 0xffffffff

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band16S : List (BitVec 128) := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band16I : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band17D : BitVec 128 := 0x5555555555555555

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band17S : List (BitVec 128) := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band17I : List Nat := [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band18D : BitVec 128 := 0xffff000000000000ffff

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band18S : List (BitVec 128) := [0xaaaa000000000000aaaa, 0xcccc000000000000cccc, 0xf0f0000000000000f0f0, 0xff00000000000000ff00, 0xffff0000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band18I : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band20D : BitVec 128 := 0xf0f0f0f000000000f0f0f0f

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band20S : List (BitVec 128) := [0xa0a0a0a000000000a0a0a0a, 0xc0c0c0c000000000c0c0c0c, 0xf000f00000000000f000f00, 0xf0f0000000000000f0f0000, 0xf0f0f0f0000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band20I : List Nat := [0, 2, 1, 3, 16, 18, 17, 19, 8, 10, 9, 11, 24, 26, 25, 27, 64, 66, 65, 67, 80, 82, 81, 83, 72, 74, 73, 75, 88, 90, 89, 91]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band21D : BitVec 128 := 0x333333330000000033333333

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band21S : List (BitVec 128) := [0x222222220000000022222222, 0x303030300000000030303030, 0x330033000000000033003300, 0x333300000000000033330000, 0x333333330000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band21I : List Nat := [0, 1, 16, 17, 8, 9, 24, 25, 4, 5, 20, 21, 12, 13, 28, 29, 64, 65, 80, 81, 72, 73, 88, 89, 68, 69, 84, 85, 76, 77, 92, 93]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band22D : BitVec 128 := 0x555555550000000055555555

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band22S : List (BitVec 128) := [0x444444440000000044444444, 0x505050500000000050505050, 0x550055000000000055005500, 0x555500000000000055550000, 0x555555550000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band22I : List Nat := [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band23D : BitVec 128 := 0x303000003030000030300000303

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band23S : List (BitVec 128) := [0x202000002020000020200000202, 0x300000003000000030000000300, 0x303000000000000030300000000, 0x303000003030000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band23I : List Nat := [0, 1, 8, 9, 32, 33, 40, 41, 64, 65, 72, 73, 96, 97, 104, 105]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band24D : BitVec 128 := 0x33000000330000003300000033

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band24S : List (BitVec 128) := [0x22000000220000002200000022, 0x30000000300000003000000030, 0x33000000000000003300000000, 0x33000000330000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band24I : List Nat := [0, 1, 4, 5, 32, 33, 36, 37, 64, 65, 68, 69, 96, 97, 100, 101]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band25D : BitVec 128 := 0x50005000500050005000500050005

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band25S : List (BitVec 128) := [0x40004000400040004000400040004, 0x50000000500000005000000050000, 0x50005000000000005000500000000, 0x50005000500050000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band25I : List Nat := [0, 2, 16, 18, 32, 34, 48, 50, 64, 66, 80, 82, 96, 98, 112, 114]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band26D : BitVec 128 := 0x505000005050000050500000505

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band26S : List (BitVec 128) := [0x404000004040000040400000404, 0x500000005000000050000000500, 0x505000000000000050500000000, 0x505000005050000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band26I : List Nat := [0, 2, 8, 10, 32, 34, 40, 42, 64, 66, 72, 74, 96, 98, 104, 106]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band27D : BitVec 128 := 0x110011001100110011001100110011

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band27S : List (BitVec 128) := [0x100010001000100010001000100010, 0x110000001100000011000000110000, 0x110011000000000011001100000000, 0x110011001100110000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band27I : List Nat := [0, 4, 16, 20, 32, 36, 48, 52, 64, 68, 80, 84, 96, 100, 112, 116]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band28D : BitVec 128 := 0x1111111111111111

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band28S : List (BitVec 128) := [0x1010101010101010, 0x1100110011001100, 0x1111000011110000, 0x1111111100000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band28I : List Nat := [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band30D : BitVec 128 := 0x333300003333

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band30S : List (BitVec 128) := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band30I : List Nat := [0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band32D : BitVec 128 := 0x555500005555

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band32S : List (BitVec 128) := [0x444400004444, 0x505000005050, 0x550000005500, 0x555500000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band32I : List Nat := [0, 2, 4, 6, 8, 10, 12, 14, 32, 34, 36, 38, 40, 42, 44, 46]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band33D : BitVec 128 := 0x1111000011110000111100001111

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band33S : List (BitVec 128) := [0x1010000010100000101000001010, 0x1100000011000000110000001100, 0x1111000000000000111100000000, 0x1111000011110000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band33I : List Nat := [0, 32, 4, 36, 8, 40, 12, 44, 64, 96, 68, 100, 72, 104, 76, 108]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band34D : BitVec 128 := 0x33330000000000003333

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band34S : List (BitVec 128) := [0x22220000000000002222, 0x30300000000000003030, 0x33000000000000003300, 0x33330000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band34I : List Nat := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band36D : BitVec 128 := 0x505050505050505

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band36S : List (BitVec 128) := [0x404040404040404, 0x500050005000500, 0x505000005050000, 0x505050500000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band36I : List Nat := [0, 2, 8, 10, 16, 18, 24, 26, 32, 34, 40, 42, 48, 50, 56, 58]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band37D : BitVec 128 := 0x303030303030303

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band37S : List (BitVec 128) := [0x202020202020202, 0x300030003000300, 0x303000003030000, 0x303030300000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band37I : List Nat := [0, 1, 16, 17, 8, 9, 24, 25, 32, 33, 48, 49, 40, 41, 56, 57]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band42D : BitVec 128 := 0x1010101010101010101010101010101

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band42S : List (BitVec 128) := [0x1000100010001000100010001000100, 0x1010000010100000101000001010000, 0x1010101000000000101010100000000, 0x1010101010101010000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band42I : List Nat := [0, 32, 8, 40, 16, 48, 24, 56, 64, 96, 72, 104, 80, 112, 88, 120]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band44D : BitVec 128 := 0x111111110000000011111111

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band44S : List (BitVec 128) := [0x101010100000000010101010, 0x110011000000000011001100, 0x111100000000000011110000, 0x111111110000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band44I : List Nat := [0, 4, 8, 12, 16, 20, 24, 28, 64, 68, 72, 76, 80, 84, 88, 92]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band46D : BitVec 128 := 0x50505050000000005050505

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band46S : List (BitVec 128) := [0x40404040000000004040404, 0x50005000000000005000500, 0x50500000000000005050000, 0x50505050000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band46I : List Nat := [0, 2, 8, 10, 16, 18, 24, 26, 64, 66, 72, 74, 80, 82, 88, 90]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band47D : BitVec 128 := 0x30303030000000003030303

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band47S : List (BitVec 128) := [0x20202020000000002020202, 0x30003000000000003000300, 0x30300000000000003030000, 0x30303030000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band47I : List Nat := [0, 1, 16, 17, 8, 9, 24, 25, 64, 65, 80, 81, 72, 73, 88, 89]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band52D : BitVec 128 := 0x55550000000000005555

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band52S : List (BitVec 128) := [0x44440000000000004444, 0x50500000000000005050, 0x55000000000000005500, 0x55550000000000000000]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band52I : List Nat := [0, 2, 4, 6, 8, 10, 12, 14, 64, 66, 68, 70, 72, 74, 76, 78]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def band : Nat → Nat → Hist 128 → List (BitVec 128) → Bool
  | 0, k, h, ws => autoCut 10 k band0D band0S h ws
  | 1, k, h, ws => autoCut 10 k band1D band1S h ws
  | 2, k, h, ws => autoCut 8 k band2D band2S h ws
  | 3, k, h, ws => autoCut 8 k band3D band3S h ws
  | 4, k, h, ws => autoCut 8 k band4D band4S h ws
  | 5, k, h, ws => autoCut 8 k band5D band5S h ws
  | 6, k, h, ws => autoCut 8 k band6D band6S h ws
  | 7, k, h, ws => autoCut 8 k band7D band7S h ws
  | 8, k, h, ws => autoCut 8 k band8D band8S h ws
  | 9, k, h, ws => autoCut 8 k band9D band9S h ws
  | 10, k, h, ws => autoCut 8 k band10D band10S h ws
  | 11, k, h, ws => autoCut 8 k band11D band11S h ws
  | 12, k, h, ws => autoCut 7 k band12D band12S h ws
  | 13, k, h, ws => autoCut 7 k band14D band14S h ws
  | 14, k, h, ws => autoCut 7 k band15D band15S h ws
  | 15, k, h, ws => autoCut 7 k band16D band16S h ws
  | 16, k, h, ws => autoCut 7 k band17D band17S h ws
  | 17, k, h, ws => autoCut 7 k band18D band18S h ws
  | 18, k, h, ws => autoCut 7 k band20D band20S h ws
  | 19, k, h, ws => autoCut 7 k band21D band21S h ws
  | 20, k, h, ws => autoCut 7 k band22D band22S h ws
  | 21, k, h, ws => autoCut 7 k band23D band23S h ws
  | 22, k, h, ws => autoCut 7 k band24D band24S h ws
  | 23, k, h, ws => autoCut 7 k band25D band25S h ws
  | 24, k, h, ws => autoCut 7 k band26D band26S h ws
  | 25, k, h, ws => autoCut 7 k band27D band27S h ws
  | 26, k, h, ws => autoCut 5 k band28D band28S h ws
  | 27, k, h, ws => autoCut 5 k band30D band30S h ws
  | 28, k, h, ws => autoCut 5 k band32D band32S h ws
  | 29, k, h, ws => autoCut 5 k band33D band33S h ws
  | 30, k, h, ws => autoCut 5 k band34D band34S h ws
  | 31, k, h, ws => autoCut 5 k band36D band36S h ws
  | 32, k, h, ws => autoCut 5 k band37D band37S h ws
  | 33, k, h, ws => autoCut 5 k band42D band42S h ws
  | 34, k, h, ws => autoCut 5 k band44D band44S h ws
  | 35, k, h, ws => autoCut 5 k band46D band46S h ws
  | 36, k, h, ws => autoCut 5 k band47D band47S h ws
  | 37, k, h, ws => autoCut 5 k band52D band52S h ws
  | _, _, _, _ => false

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem band_no (i k : Nat) (h : Hist 128) (ws : List (BitVec 128)) (hn : ws.Nodup)
    (hc : band i k h ws = true) : ¬live (basicOps 128) goal7 k ws.toFinset := by
  by_cases hi : i < 38
  · interval_cases i
    · exact autoCut_no (lb := 10) (by decide +kernel) goal7 band0I (by decide +kernel) (by decide +kernel) band0D (by decide +kernel) band0S w5_goal (by decide +kernel) w5_rows (by decide +kernel) (by decide +kernel) w5_no_build k h ws hn hc
    · exact autoCut_no (lb := 10) (by decide +kernel) goal7 band1I (by decide +kernel) (by decide +kernel) band1D (by decide +kernel) band1S w5_goal (by decide +kernel) w5_rows (by decide +kernel) (by decide +kernel) w5_no_build k h ws hn hc
    · exact autoCut_no (lb := 8) (by decide +kernel) goal7 band2I (by decide +kernel) (by decide +kernel) band2D (by decide +kernel) band2S new4G (by decide +kernel) new4R (by decide +kernel) (by decide +kernel) new4Low k h ws hn hc
    · exact autoCut_no (lb := 8) (by decide +kernel) goal7 band3I (by decide +kernel) (by decide +kernel) band3D (by decide +kernel) band3S new4G (by decide +kernel) new4R (by decide +kernel) (by decide +kernel) new4Low k h ws hn hc
    · exact autoCut_no (lb := 8) (by decide +kernel) goal7 band4I (by decide +kernel) (by decide +kernel) band4D (by decide +kernel) band4S new5G (by decide +kernel) new5R (by decide +kernel) (by decide +kernel) new5Low k h ws hn hc
    · exact autoCut_no (lb := 8) (by decide +kernel) goal7 band5I (by decide +kernel) (by decide +kernel) band5D (by decide +kernel) band5S new5G (by decide +kernel) new5R (by decide +kernel) (by decide +kernel) new5Low k h ws hn hc
    · exact autoCut_no (lb := 8) (by decide +kernel) goal7 band6I (by decide +kernel) (by decide +kernel) band6D (by decide +kernel) band6S new4G (by decide +kernel) new4R (by decide +kernel) (by decide +kernel) new4Low k h ws hn hc
    · exact autoCut_no (lb := 8) (by decide +kernel) goal7 band7I (by decide +kernel) (by decide +kernel) band7D (by decide +kernel) band7S new5G (by decide +kernel) new5R (by decide +kernel) (by decide +kernel) new5Low k h ws hn hc
    · exact autoCut_no (lb := 8) (by decide +kernel) goal7 band8I (by decide +kernel) (by decide +kernel) band8D (by decide +kernel) band8S new5G (by decide +kernel) new5R (by decide +kernel) (by decide +kernel) new5Low k h ws hn hc
    · exact autoCut_no (lb := 8) (by decide +kernel) goal7 band9I (by decide +kernel) (by decide +kernel) band9D (by decide +kernel) band9S new4G (by decide +kernel) new4R (by decide +kernel) (by decide +kernel) new4Low k h ws hn hc
    · exact autoCut_no (lb := 8) (by decide +kernel) goal7 band10I (by decide +kernel) (by decide +kernel) band10D (by decide +kernel) band10S new4G (by decide +kernel) new4R (by decide +kernel) (by decide +kernel) new4Low k h ws hn hc
    · exact autoCut_no (lb := 8) (by decide +kernel) goal7 band11I (by decide +kernel) (by decide +kernel) band11D (by decide +kernel) band11S new5G (by decide +kernel) new5R (by decide +kernel) (by decide +kernel) new5Low k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band12I (by decide +kernel) (by decide +kernel) band12D (by decide +kernel) band12S p4h_goal (by decide +kernel) p4h_rows (by decide +kernel) (by decide +kernel) p4h_no_build k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band14I (by decide +kernel) (by decide +kernel) band14D (by decide +kernel) band14S p4h_goal (by decide +kernel) p4h_rows (by decide +kernel) (by decide +kernel) p4h_no_build k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band15I (by decide +kernel) (by decide +kernel) band15D (by decide +kernel) band15S p4h_goal (by decide +kernel) p4h_rows (by decide +kernel) (by decide +kernel) p4h_no_build k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band16I (by decide +kernel) (by decide +kernel) band16D (by decide +kernel) band16S c5_goal (by decide +kernel) c5_rows (by decide +kernel) (by decide +kernel) c5_no_build k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band17I (by decide +kernel) (by decide +kernel) band17D (by decide +kernel) band17S p4h_goal (by decide +kernel) p4h_rows (by decide +kernel) (by decide +kernel) p4h_no_build k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band18I (by decide +kernel) (by decide +kernel) band18D (by decide +kernel) band18S p4h_goal (by decide +kernel) p4h_rows (by decide +kernel) (by decide +kernel) p4h_no_build k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band20I (by decide +kernel) (by decide +kernel) band20D (by decide +kernel) band20S p4h_goal (by decide +kernel) p4h_rows (by decide +kernel) (by decide +kernel) p4h_no_build k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band21I (by decide +kernel) (by decide +kernel) band21D (by decide +kernel) band21S p4h_goal (by decide +kernel) p4h_rows (by decide +kernel) (by decide +kernel) p4h_no_build k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band22I (by decide +kernel) (by decide +kernel) band22D (by decide +kernel) band22S p4h_goal (by decide +kernel) p4h_rows (by decide +kernel) (by decide +kernel) p4h_no_build k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band23I (by decide +kernel) (by decide +kernel) band23D (by decide +kernel) band23S clG (by decide +kernel) clR (by decide +kernel) (by decide +kernel) clLow k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band24I (by decide +kernel) (by decide +kernel) band24D (by decide +kernel) band24S clG (by decide +kernel) clR (by decide +kernel) (by decide +kernel) clLow k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band25I (by decide +kernel) (by decide +kernel) band25D (by decide +kernel) band25S clG (by decide +kernel) clR (by decide +kernel) (by decide +kernel) clLow k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band26I (by decide +kernel) (by decide +kernel) band26D (by decide +kernel) band26S clG (by decide +kernel) clR (by decide +kernel) (by decide +kernel) clLow k h ws hn hc
    · exact autoCut_no (lb := 7) (by decide +kernel) goal7 band27I (by decide +kernel) (by decide +kernel) band27D (by decide +kernel) band27S clG (by decide +kernel) clR (by decide +kernel) (by decide +kernel) clLow k h ws hn hc
    · exact autoCut_no (lb := 5) (by decide +kernel) goal7 band28I (by decide +kernel) (by decide +kernel) band28D (by decide +kernel) band28S new6G (by decide +kernel) new6R (by decide +kernel) (by decide +kernel) new6Low k h ws hn hc
    · exact autoCut_no (lb := 5) (by decide +kernel) goal7 band30I (by decide +kernel) (by decide +kernel) band30D (by decide +kernel) band30S new7G (by decide +kernel) new7R (by decide +kernel) (by decide +kernel) new7Low k h ws hn hc
    · exact autoCut_no (lb := 5) (by decide +kernel) goal7 band32I (by decide +kernel) (by decide +kernel) band32D (by decide +kernel) band32S new6G (by decide +kernel) new6R (by decide +kernel) (by decide +kernel) new6Low k h ws hn hc
    · exact autoCut_no (lb := 5) (by decide +kernel) goal7 band33I (by decide +kernel) (by decide +kernel) band33D (by decide +kernel) band33S new7G (by decide +kernel) new7R (by decide +kernel) (by decide +kernel) new7Low k h ws hn hc
    · exact autoCut_no (lb := 5) (by decide +kernel) goal7 band34I (by decide +kernel) (by decide +kernel) band34D (by decide +kernel) band34S new7G (by decide +kernel) new7R (by decide +kernel) (by decide +kernel) new7Low k h ws hn hc
    · exact autoCut_no (lb := 5) (by decide +kernel) goal7 band36I (by decide +kernel) (by decide +kernel) band36D (by decide +kernel) band36S new7G (by decide +kernel) new7R (by decide +kernel) (by decide +kernel) new7Low k h ws hn hc
    · exact autoCut_no (lb := 5) (by decide +kernel) goal7 band37I (by decide +kernel) (by decide +kernel) band37D (by decide +kernel) band37S new6G (by decide +kernel) new6R (by decide +kernel) (by decide +kernel) new6Low k h ws hn hc
    · exact autoCut_no (lb := 5) (by decide +kernel) goal7 band42I (by decide +kernel) (by decide +kernel) band42D (by decide +kernel) band42S new7G (by decide +kernel) new7R (by decide +kernel) (by decide +kernel) new7Low k h ws hn hc
    · exact autoCut_no (lb := 5) (by decide +kernel) goal7 band44I (by decide +kernel) (by decide +kernel) band44D (by decide +kernel) band44S new6G (by decide +kernel) new6R (by decide +kernel) (by decide +kernel) new6Low k h ws hn hc
    · exact autoCut_no (lb := 5) (by decide +kernel) goal7 band46I (by decide +kernel) (by decide +kernel) band46D (by decide +kernel) band46S new7G (by decide +kernel) new7R (by decide +kernel) (by decide +kernel) new7Low k h ws hn hc
    · exact autoCut_no (lb := 5) (by decide +kernel) goal7 band47I (by decide +kernel) (by decide +kernel) band47D (by decide +kernel) band47S new6G (by decide +kernel) new6R (by decide +kernel) (by decide +kernel) new6Low k h ws hn hc
    · exact autoCut_no (lb := 5) (by decide +kernel) goal7 band52I (by decide +kernel) (by decide +kernel) band52D (by decide +kernel) band52S new6G (by decide +kernel) new6R (by decide +kernel) (by decide +kernel) new6Low k h ws hn hc
  · have hz : band i k h ws = false := by unfold band; split <;> first | omega | rfl
    rw [hz] at hc
    contradiction

end PEqualNP.Outside.L_meta_10460.Shapes

namespace PEqualNP.Outside.L_meta_10460.Big
open PEqualNP.Outside.L_meta_10460.Evidence PEqualNP.Outside.L_meta_10460.Signed PEqualNP.Outside.L_meta_10460.Shapes

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def inv7 : Array Nat := #[0, 1, 2, 3, 4, 5, 18, 19, 8, 9, 14, 15, 12, 13, 10, 11, 16, 17, 6, 7]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def row7 : Array (List Nat) := #[[0, 1, 16, 17, 8, 9, 24, 25, 4, 5, 20, 21, 12, 13, 28, 29, 2, 3, 18, 19, 10, 11, 26, 27, 6, 7, 22, 23, 14, 15, 30, 31, 32, 33, 48, 49, 40, 41, 56, 57, 36, 37, 52, 53, 44, 45, 60, 61, 34, 35, 50, 51, 42, 43, 58, 59, 38, 39, 54, 55, 46, 47, 62, 63, 64, 65, 80, 81, 72, 73, 88, 89, 68, 69, 84, 85, 76, 77, 92, 93, 66, 67, 82, 83, 74, 75, 90, 91, 70, 71, 86, 87, 78, 79, 94, 95, 96, 97, 112, 113, 104, 105, 120, 121, 100, 101, 116, 117, 108, 109, 124, 125, 98, 99, 114, 115, 106, 107, 122, 123, 102, 103, 118, 119, 110, 111, 126, 127],
  [0, 1, 16, 17, 8, 9, 24, 25, 4, 5, 20, 21, 12, 13, 28, 29, 2, 3, 18, 19, 10, 11, 26, 27, 6, 7, 22, 23, 14, 15, 30, 31, 64, 65, 80, 81, 72, 73, 88, 89, 68, 69, 84, 85, 76, 77, 92, 93, 66, 67, 82, 83, 74, 75, 90, 91, 70, 71, 86, 87, 78, 79, 94, 95, 32, 33, 48, 49, 40, 41, 56, 57, 36, 37, 52, 53, 44, 45, 60, 61, 34, 35, 50, 51, 42, 43, 58, 59, 38, 39, 54, 55, 46, 47, 62, 63, 96, 97, 112, 113, 104, 105, 120, 121, 100, 101, 116, 117, 108, 109, 124, 125, 98, 99, 114, 115, 106, 107, 122, 123, 102, 103, 118, 119, 110, 111, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127],
  [0, 4, 2, 6, 1, 5, 3, 7, 16, 20, 18, 22, 17, 21, 19, 23, 8, 12, 10, 14, 9, 13, 11, 15, 24, 28, 26, 30, 25, 29, 27, 31, 32, 36, 34, 38, 33, 37, 35, 39, 48, 52, 50, 54, 49, 53, 51, 55, 40, 44, 42, 46, 41, 45, 43, 47, 56, 60, 58, 62, 57, 61, 59, 63, 64, 68, 66, 70, 65, 69, 67, 71, 80, 84, 82, 86, 81, 85, 83, 87, 72, 76, 74, 78, 73, 77, 75, 79, 88, 92, 90, 94, 89, 93, 91, 95, 96, 100, 98, 102, 97, 101, 99, 103, 112, 116, 114, 118, 113, 117, 115, 119, 104, 108, 106, 110, 105, 109, 107, 111, 120, 124, 122, 126, 121, 125, 123, 127],
  [0, 4, 2, 6, 1, 5, 3, 7, 16, 20, 18, 22, 17, 21, 19, 23, 8, 12, 10, 14, 9, 13, 11, 15, 24, 28, 26, 30, 25, 29, 27, 31, 64, 68, 66, 70, 65, 69, 67, 71, 80, 84, 82, 86, 81, 85, 83, 87, 72, 76, 74, 78, 73, 77, 75, 79, 88, 92, 90, 94, 89, 93, 91, 95, 32, 36, 34, 38, 33, 37, 35, 39, 48, 52, 50, 54, 49, 53, 51, 55, 40, 44, 42, 46, 41, 45, 43, 47, 56, 60, 58, 62, 57, 61, 59, 63, 96, 100, 98, 102, 97, 101, 99, 103, 112, 116, 114, 118, 113, 117, 115, 119, 104, 108, 106, 110, 105, 109, 107, 111, 120, 124, 122, 126, 121, 125, 123, 127],
  [0, 8, 16, 24, 1, 9, 17, 25, 2, 10, 18, 26, 3, 11, 19, 27, 4, 12, 20, 28, 5, 13, 21, 29, 6, 14, 22, 30, 7, 15, 23, 31, 32, 40, 48, 56, 33, 41, 49, 57, 34, 42, 50, 58, 35, 43, 51, 59, 36, 44, 52, 60, 37, 45, 53, 61, 38, 46, 54, 62, 39, 47, 55, 63, 64, 72, 80, 88, 65, 73, 81, 89, 66, 74, 82, 90, 67, 75, 83, 91, 68, 76, 84, 92, 69, 77, 85, 93, 70, 78, 86, 94, 71, 79, 87, 95, 96, 104, 112, 120, 97, 105, 113, 121, 98, 106, 114, 122, 99, 107, 115, 123, 100, 108, 116, 124, 101, 109, 117, 125, 102, 110, 118, 126, 103, 111, 119, 127],
  [0, 8, 16, 24, 1, 9, 17, 25, 2, 10, 18, 26, 3, 11, 19, 27, 4, 12, 20, 28, 5, 13, 21, 29, 6, 14, 22, 30, 7, 15, 23, 31, 64, 72, 80, 88, 65, 73, 81, 89, 66, 74, 82, 90, 67, 75, 83, 91, 68, 76, 84, 92, 69, 77, 85, 93, 70, 78, 86, 94, 71, 79, 87, 95, 32, 40, 48, 56, 33, 41, 49, 57, 34, 42, 50, 58, 35, 43, 51, 59, 36, 44, 52, 60, 37, 45, 53, 61, 38, 46, 54, 62, 39, 47, 55, 63, 96, 104, 112, 120, 97, 105, 113, 121, 98, 106, 114, 122, 99, 107, 115, 123, 100, 108, 116, 124, 101, 109, 117, 125, 102, 110, 118, 126, 103, 111, 119, 127],
  [0, 16, 8, 24, 4, 20, 12, 28, 2, 18, 10, 26, 6, 22, 14, 30, 1, 17, 9, 25, 5, 21, 13, 29, 3, 19, 11, 27, 7, 23, 15, 31, 32, 48, 40, 56, 36, 52, 44, 60, 34, 50, 42, 58, 38, 54, 46, 62, 33, 49, 41, 57, 37, 53, 45, 61, 35, 51, 43, 59, 39, 55, 47, 63, 64, 80, 72, 88, 68, 84, 76, 92, 66, 82, 74, 90, 70, 86, 78, 94, 65, 81, 73, 89, 69, 85, 77, 93, 67, 83, 75, 91, 71, 87, 79, 95, 96, 112, 104, 120, 100, 116, 108, 124, 98, 114, 106, 122, 102, 118, 110, 126, 97, 113, 105, 121, 101, 117, 109, 125, 99, 115, 107, 123, 103, 119, 111, 127],
  [0, 16, 8, 24, 4, 20, 12, 28, 2, 18, 10, 26, 6, 22, 14, 30, 1, 17, 9, 25, 5, 21, 13, 29, 3, 19, 11, 27, 7, 23, 15, 31, 64, 80, 72, 88, 68, 84, 76, 92, 66, 82, 74, 90, 70, 86, 78, 94, 65, 81, 73, 89, 69, 85, 77, 93, 67, 83, 75, 91, 71, 87, 79, 95, 32, 48, 40, 56, 36, 52, 44, 60, 34, 50, 42, 58, 38, 54, 46, 62, 33, 49, 41, 57, 37, 53, 45, 61, 35, 51, 43, 59, 39, 55, 47, 63, 96, 112, 104, 120, 100, 116, 108, 124, 98, 114, 106, 122, 102, 118, 110, 126, 97, 113, 105, 121, 101, 117, 109, 125, 99, 115, 107, 123, 103, 119, 111, 127],
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 65, 67, 69, 71, 73, 75, 77, 79, 81, 83, 85, 87, 89, 91, 93, 95, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 119, 121, 123, 125, 127],
  [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 65, 67, 69, 71, 73, 75, 77, 79, 81, 83, 85, 87, 89, 91, 93, 95, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 119, 121, 123, 125, 127],
  [0, 2, 1, 3, 16, 18, 17, 19, 8, 10, 9, 11, 24, 26, 25, 27, 4, 6, 5, 7, 20, 22, 21, 23, 12, 14, 13, 15, 28, 30, 29, 31, 32, 34, 33, 35, 48, 50, 49, 51, 40, 42, 41, 43, 56, 58, 57, 59, 36, 38, 37, 39, 52, 54, 53, 55, 44, 46, 45, 47, 60, 62, 61, 63, 64, 66, 65, 67, 80, 82, 81, 83, 72, 74, 73, 75, 88, 90, 89, 91, 68, 70, 69, 71, 84, 86, 85, 87, 76, 78, 77, 79, 92, 94, 93, 95, 96, 98, 97, 99, 112, 114, 113, 115, 104, 106, 105, 107, 120, 122, 121, 123, 100, 102, 101, 103, 116, 118, 117, 119, 108, 110, 109, 111, 124, 126, 125, 127],
  [0, 2, 1, 3, 16, 18, 17, 19, 8, 10, 9, 11, 24, 26, 25, 27, 4, 6, 5, 7, 20, 22, 21, 23, 12, 14, 13, 15, 28, 30, 29, 31, 64, 66, 65, 67, 80, 82, 81, 83, 72, 74, 73, 75, 88, 90, 89, 91, 68, 70, 69, 71, 84, 86, 85, 87, 76, 78, 77, 79, 92, 94, 93, 95, 32, 34, 33, 35, 48, 50, 49, 51, 40, 42, 41, 43, 56, 58, 57, 59, 36, 38, 37, 39, 52, 54, 53, 55, 44, 46, 45, 47, 60, 62, 61, 63, 96, 98, 97, 99, 112, 114, 113, 115, 104, 106, 105, 107, 120, 122, 121, 123, 100, 102, 101, 103, 116, 118, 117, 119, 108, 110, 109, 111, 124, 126, 125, 127],
  [0, 16, 1, 17, 2, 18, 3, 19, 4, 20, 5, 21, 6, 22, 7, 23, 8, 24, 9, 25, 10, 26, 11, 27, 12, 28, 13, 29, 14, 30, 15, 31, 32, 48, 33, 49, 34, 50, 35, 51, 36, 52, 37, 53, 38, 54, 39, 55, 40, 56, 41, 57, 42, 58, 43, 59, 44, 60, 45, 61, 46, 62, 47, 63, 64, 80, 65, 81, 66, 82, 67, 83, 68, 84, 69, 85, 70, 86, 71, 87, 72, 88, 73, 89, 74, 90, 75, 91, 76, 92, 77, 93, 78, 94, 79, 95, 96, 112, 97, 113, 98, 114, 99, 115, 100, 116, 101, 117, 102, 118, 103, 119, 104, 120, 105, 121, 106, 122, 107, 123, 108, 124, 109, 125, 110, 126, 111, 127],
  [0, 16, 1, 17, 2, 18, 3, 19, 4, 20, 5, 21, 6, 22, 7, 23, 8, 24, 9, 25, 10, 26, 11, 27, 12, 28, 13, 29, 14, 30, 15, 31, 64, 80, 65, 81, 66, 82, 67, 83, 68, 84, 69, 85, 70, 86, 71, 87, 72, 88, 73, 89, 74, 90, 75, 91, 76, 92, 77, 93, 78, 94, 79, 95, 32, 48, 33, 49, 34, 50, 35, 51, 36, 52, 37, 53, 38, 54, 39, 55, 40, 56, 41, 57, 42, 58, 43, 59, 44, 60, 45, 61, 46, 62, 47, 63, 96, 112, 97, 113, 98, 114, 99, 115, 100, 116, 101, 117, 102, 118, 103, 119, 104, 120, 105, 121, 106, 122, 107, 123, 108, 124, 109, 125, 110, 126, 111, 127],
  [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15, 16, 24, 20, 28, 18, 26, 22, 30, 17, 25, 21, 29, 19, 27, 23, 31, 32, 40, 36, 44, 34, 42, 38, 46, 33, 41, 37, 45, 35, 43, 39, 47, 48, 56, 52, 60, 50, 58, 54, 62, 49, 57, 53, 61, 51, 59, 55, 63, 64, 72, 68, 76, 66, 74, 70, 78, 65, 73, 69, 77, 67, 75, 71, 79, 80, 88, 84, 92, 82, 90, 86, 94, 81, 89, 85, 93, 83, 91, 87, 95, 96, 104, 100, 108, 98, 106, 102, 110, 97, 105, 101, 109, 99, 107, 103, 111, 112, 120, 116, 124, 114, 122, 118, 126, 113, 121, 117, 125, 115, 123, 119, 127],
  [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15, 16, 24, 20, 28, 18, 26, 22, 30, 17, 25, 21, 29, 19, 27, 23, 31, 64, 72, 68, 76, 66, 74, 70, 78, 65, 73, 69, 77, 67, 75, 71, 79, 80, 88, 84, 92, 82, 90, 86, 94, 81, 89, 85, 93, 83, 91, 87, 95, 32, 40, 36, 44, 34, 42, 38, 46, 33, 41, 37, 45, 35, 43, 39, 47, 48, 56, 52, 60, 50, 58, 54, 62, 49, 57, 53, 61, 51, 59, 55, 63, 96, 104, 100, 108, 98, 106, 102, 110, 97, 105, 101, 109, 99, 107, 103, 111, 112, 120, 116, 124, 114, 122, 118, 126, 113, 121, 117, 125, 115, 123, 119, 127],
  [0, 4, 8, 12, 16, 20, 24, 28, 1, 5, 9, 13, 17, 21, 25, 29, 2, 6, 10, 14, 18, 22, 26, 30, 3, 7, 11, 15, 19, 23, 27, 31, 32, 36, 40, 44, 48, 52, 56, 60, 33, 37, 41, 45, 49, 53, 57, 61, 34, 38, 42, 46, 50, 54, 58, 62, 35, 39, 43, 47, 51, 55, 59, 63, 64, 68, 72, 76, 80, 84, 88, 92, 65, 69, 73, 77, 81, 85, 89, 93, 66, 70, 74, 78, 82, 86, 90, 94, 67, 71, 75, 79, 83, 87, 91, 95, 96, 100, 104, 108, 112, 116, 120, 124, 97, 101, 105, 109, 113, 117, 121, 125, 98, 102, 106, 110, 114, 118, 122, 126, 99, 103, 107, 111, 115, 119, 123, 127],
  [0, 4, 8, 12, 16, 20, 24, 28, 1, 5, 9, 13, 17, 21, 25, 29, 2, 6, 10, 14, 18, 22, 26, 30, 3, 7, 11, 15, 19, 23, 27, 31, 64, 68, 72, 76, 80, 84, 88, 92, 65, 69, 73, 77, 81, 85, 89, 93, 66, 70, 74, 78, 82, 86, 90, 94, 67, 71, 75, 79, 83, 87, 91, 95, 32, 36, 40, 44, 48, 52, 56, 60, 33, 37, 41, 45, 49, 53, 57, 61, 34, 38, 42, 46, 50, 54, 58, 62, 35, 39, 43, 47, 51, 55, 59, 63, 96, 100, 104, 108, 112, 116, 120, 124, 97, 101, 105, 109, 113, 117, 121, 125, 98, 102, 106, 110, 114, 118, 122, 126, 99, 103, 107, 111, 115, 119, 123, 127]]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def pow7 : Array (List Nat) := row7.map (fun rs => rs.map (fun r => 2 ^ r))

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem sym7valid : (List.range 20).all (symValid 128 20 row7 pow7 inv7 goal7) = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
abbrev Raw := Nat × Nat × Nat

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def records6 : Array Raw := #[

  (0xb8e5954545404411ccc, 0x0, 0x0),
  (0xb8e59545454044116cc, 0x0, 0x0),
  (0x7669165545404411f0c, 0xa01, 0x0),
  (0xb2ea5525855044115d8, 0x0, 0x0),
  (0xb26a6525855044115d8, 0x0, 0x0),
  (0xb259572585504411f18, 0x1201, 0x0),
  (0xb7e896558550441171c, 0x0, 0x0),
  (0x8658991549504411e98, 0x0, 0x0),
  (0xb1e1962549504411e98, 0x0, 0x0),
  (0xb2e85965495044115d8, 0x0, 0x0),
  (0xb159572589504411f18, 0x79602, 0x0),
  (0xb2e8565589504411798, 0x0, 0x0),
  (0xa2685655c9504411b58, 0x1201, 0x0),
  (0xa4685655d1504411b4c, 0x11202, 0x0),
  (0x7668794595504411b1c, 0x0, 0x0),
  (0x6568562603524411e98, 0x6b402, 0x0),
  (0xb159562603524411e98, 0x0, 0x0),
  (0xa168165589524411b98, 0x401, 0x0),
  (0xb3e9d65589524411713, 0x1, 0x0),
  (0xb2e45905955244115d8, 0x0, 0x0),
  (0xa4e8f985d9524411867, 0x0, 0x0),
  (0xb3ea5989d9524411077, 0x0, 0x0),
  (0xa4e4f9261d654411867, 0x0, 0x0),
  (0xb4e8993e1d654411467, 0x0, 0x0),
  (0xb3e61525855048115d2, 0x0, 0x0),
  (0xb7e615258550481155a, 0x0, 0x0),
  (0xb76635258550481155a, 0x0, 0x0),
  (0xba663525855048111da, 0x0, 0x0),
  (0xb3e85865495048116d2, 0x0, 0x0),
  (0xb7e858654950481165a, 0x0, 0x0),
  (0xb7e856558950481171a, 0x0, 0x0),
  (0xa268165585514811b98, 0x1, 0x0),
  (0x6568584dc5605411a9c, 0x201, 0x0),
  (0xb2e859654960541159a, 0x0, 0x0),
  (0xb4e859654960541158e, 0x0, 0x0),
  (0xb0e8592dd952541135a, 0x0, 0x0),
  (0xb3e8592dd9525411353, 0x0, 0x0),
  (0xb0e8592dd95254111da, 0x0, 0x0),
  (0xb3e8592dd95254111d3, 0x0, 0x0),
  (0xb4e8590e1d6254110ee, 0x0, 0x0),
  (0xb4e8590e096554111ce, 0x0, 0x0),
  (0xb2e1193e05765411473, 0x0, 0x0),
  (0xb4e8590e0976541116e, 0x0, 0x0)]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def records7 : Array Raw := #[

  (0x1d954545404410f4c, 0xaac084d122a208, 0x0),
  (0x25954545404410dcc, 0x2a4ac08472607, 0x401),
  (0x25954545404410fcc, 0x2611c03, 0x4401),
  (0x25b54545404410dcc, 0xa929ac10229808, 0x0),
  (0x19564545404410f8c, 0xa92b0462606, 0x0),
  (0x29564545404410fcc, 0x2229803, 0x0),
  (0x29165545404410fcc, 0x88a02, 0x8401),
  (0x1d965545404410f1c, 0x2a13472c98081209, 0x8401),
  (0x21965545404410e9c, 0x2a112b209b807, 0x0),
  (0x2a165545404410edc, 0x928a03, 0x0),
  (0x29396545404410dec, 0x1c12603, 0x0),
  (0x2a396545404410cfc, 0x0, 0x1800402),
  (0x29396545404410bec, 0x70402, 0x0),
  (0x2a396545404410afc, 0x0, 0x4401),
  (0x25191595404410dec, 0x402, 0x0),
  (0x21591595404410edc, 0x12602, 0x8201),
  (0x26191595404410cfc, 0x810a03, 0x0),
  (0x21975595404410e1e, 0xaac2a812062608, 0x0),
  (0x28797595404410d7c, 0x0, 0x0),
  (0x28f97595404410d76, 0x10602, 0x0),
  (0x29397595404410d6e, 0x2c01, 0x0),
  (0x2a397595404410c7e, 0x401, 0x0),
  (0x287965d5404410b7c, 0x0, 0x0),
  (0x28f965d5404410b76, 0x401, 0x0),
  (0x293965d5404410b6e, 0x0, 0x0),
  (0x2a3965d5404410a7e, 0x401, 0x0),
  (0x1c952585504410f58, 0x2e0aa50b0842005920b, 0x0),
  (0x24952585504410fd8, 0x1401, 0x0),
  (0x2a552585504410ddc, 0x10802, 0xc401),
  (0x2a652585504410ddc, 0x20402, 0x10401),
  (0x19572585504410f1c, 0x14aaea1309e07, 0x14401),
  (0x19582585504410f9c, 0x1474603, 0x0),
  (0x19592585504410f9c, 0x1ca4003, 0x0),
  (0x19592d85504410d9c, 0x52a72e4a806, 0x0),
  (0x28965585504410f9c, 0x1211a03, 0x61014402),
  (0x28f98585504410bf4, 0x1201, 0x0),
  (0x18991549504410fd8, 0x94899210806, 0x1c401),
  (0x1d991549504410f5c, 0x2692003, 0x0),
  (0x21991549504410edc, 0x98802, 0x1c401),
  (0x25991549504410ddc, 0x4811203, 0x0),
  (0x28562549504410fd8, 0x51a02, 0x1c601),
  (0x21962549504410e9a, 0x44a8baa51e22009, 0x20407181c403),
  (0x21962549504410f9a, 0x4a800804, 0x0),
  (0x29d62549504410b5a, 0x12faab8308103409, 0x0),
  (0x29d62549504410f5a, 0x4201a03, 0x0),
  (0x21972549504410e5a, 0x92a16baa50881e0a, 0x0),
  (0x21972549504410f5a, 0x2810022051e07, 0x0),
  (0x29972549504410f5a, 0xf8308103406, 0x0),
  (0x21b72549504410e5a, 0x2692a1702ea8009, 0x0),
  (0x29b72549504410b5a, 0x120aea9509e07, 0x0),
  (0x28976549504410f5a, 0xfc203404, 0x0),
  (0x28786549504410edc, 0x1401, 0x81001802),
  (0x28b86549504410eda, 0xa1e02, 0x1801),
  (0x28786549504410bdc, 0x401, 0x5801),
  (0x28b86549504410bda, 0x1e01, 0x5801),
  (0x28596549504410ddc, 0x521203, 0x24401),
  (0x29f96549504410d5e, 0x1e01, 0x1c01),
  (0x29f96549504410b5e, 0x1e01, 0x5c01),
  (0x19591589504410f9c, 0x71a02, 0x0),
  (0x25591589504410ddc, 0x401, 0x0),
  (0x19572589504410f1a, 0x4a85aea9b09e08, 0x28401),
  (0x25572589504410f5a, 0x2411a03, 0x0),
  (0x19582589504410f9a, 0x11a400204, 0x0),
  (0x21982589504410eba, 0x118802, 0x0),
  (0x28565589504410f9c, 0x46a603, 0xb1028402),
  (0x25d65589504410d1e, 0x12f94aaed0104209, 0x0),
  (0x25d65589504410f1e, 0x3401a03, 0x0),
  (0x25d95589504410d5e, 0x10002, 0x0),
  (0x29797589504410d5e, 0xd4202, 0x0),
  (0x287985895044109fc, 0x0, 0x0),
  (0x29f9858950441097e, 0x1, 0x0),
  (0x28598d895044109fc, 0x0, 0x0),
  (0x29598d895044109de, 0x0, 0x0),
  (0x29d98d8950441097e, 0x1, 0x0),
  (0x285655c9504410f5c, 0x2679603, 0xc1028402),
  (0x289655c9504410f5a, 0x1291e03, 0xc1014402),
  (0x259655c9504410f1e, 0xfb404204, 0x0),
  (0x28b865c9504410e7a, 0x82802, 0x0),
  (0x28b865c9504410b7a, 0x2001, 0x0),
  (0x297965c9504410b5e, 0x3401, 0x0),
  (0x1d965609504410f1e, 0x50072404, 0x0),
  (0x19591d91504410d9c, 0x2a62c12805, 0x0),
  (0x19584591504410f8e, 0x2928088205, 0x0),
  (0x28565591504410f9c, 0x479203, 0x55808202),
  (0x25d65591504410d1e, 0x2a2b8b04d00dba09, 0x0),
  (0x25d65591504410f1e, 0x298d0004, 0x0),
  (0x29797591504410d5e, 0xe8002, 0x0),
  (0x287985915044109fc, 0x0, 0x0),
  (0x28b985915044109fa, 0x1, 0x0),
  (0x29f9859150441097e, 0x1, 0x0),
  (0x29398591504410aee, 0x0, 0xda01),
  (0x29198991504410aee, 0x0, 0x11a01),
  (0x29998991504410abe, 0x401, 0x0),
  (0x2a5989915044108fe, 0x20a02, 0x0),
  (0x28598d915044109fc, 0x0, 0x0),
  (0x29598d915044109de, 0x0, 0x0),
  (0x29d98d9150441097e, 0x1, 0x0),
  (0x285655d1504410f5c, 0x2678403, 0xd1015602),
  (0x259655d1504410f1e, 0xe3403a04, 0x0),
  (0x297965d1504410b5e, 0x1, 0x0),
  (0x1d965611504410f1e, 0xa0072204, 0x0),
  (0x28786611504410afc, 0x0, 0x0),
  (0x28565613504410edc, 0x9b602, 0x0),
  (0x1d965613504410e1e, 0xaaca0a804d0008, 0x0),
  (0x28596613504410cfc, 0x110a02, 0x0),
  (0x24991595504410ddc, 0x11202, 0xc1024402),
  (0x28b91595504410bdc, 0x2601, 0xb1024402),
  (0x25191595504410ddc, 0x48402, 0x34401),
  (0x1d992595504410f1e, 0x401a4a405, 0x9801),
  (0x29f92595504410b5e, 0x2401, 0x18401),
  (0x28794595504410bdc, 0x2201, 0x38401),
  (0x1d994595504410f1e, 0x2a201204, 0x38401),
  (0x29f94595504410b5e, 0x2201, 0x19a01),
  (0x28976595504410f1e, 0xf94d0104206, 0x0),
  (0x28b76595504410b1e, 0x1252ad2e91e07, 0x0),
  (0x29176595504410f1e, 0xe04d00dba06, 0x0),
  (0x29376595504410b1e, 0xa8a884d2c49e08, 0x0),
  (0x297925d9504410b5e, 0x4201, 0x0),
  (0x297945d9504410b5e, 0x3a01, 0x0),
  (0x28991e19504410afc, 0x1201, 0x0),
  (0x25191e19504410cfc, 0x1401, 0x0),
  (0x25391e19504410cfc, 0x401, 0x0),
  (0x28792619504410afc, 0x1401, 0x0),
  (0x29f92619504410a7e, 0xa01, 0x0),
  (0x28794619504410afc, 0x0, 0x0),
  (0x28b94619504410afa, 0xa01, 0x0),
  (0x29f94619504410a7e, 0xa01, 0x0),
  (0x28594e19504410cfc, 0xa01, 0x0),
  (0x28594e19504410afc, 0x28402, 0x0),
  (0x28991e195044109fc, 0x1201, 0x0),
  (0x28594e195044109fc, 0x401, 0x0),
  (0x28562603524410ef8, 0x146b403, 0x3c401),
  (0x19562603524410e9a, 0x4ba44aa01a07, 0x10103c402),
  (0x28565603524410edc, 0x2601, 0x40401),
  (0x28596603524410cfc, 0x14802, 0x0),
  (0x19562605524410f99, 0x4a410099406, 0xf181c402),
  (0x1d965605524410f1d, 0x2692003, 0x0),
  (0x28386605524410afc, 0x1201, 0x0),
  (0x28165589524410f9a, 0x48a78008806, 0x444027809c03),
  (0x28565589524410f99, 0x11c02604, 0x444101840403),
  (0x21d65589524410f1b, 0x4a400314206, 0x0),
  (0x29d65589524410f1b, 0x6008d4405, 0x48401),
  (0x29b87589524410b3b, 0x4201, 0x0),
  (0x24590595524410ddc, 0x10802, 0x4c4111030803),
  (0x28b91595524410bd9, 0x2601, 0x13102c602),
  (0x28976595524410f1b, 0x103e03404, 0x0),
  (0x29b87595524410e1f, 0x124710204, 0x0),
  (0x29b87595524410b1f, 0x110202, 0x0),
  (0x28b97595524410b5b, 0x4401, 0x0),
  (0x28f97595524410b57, 0x201, 0x48401),
  (0x283985d9524410c7e, 0xb8002, 0x0),
  (0x287985d9524410c7d, 0x1, 0x0),
  (0x28f985d9524410877, 0x0, 0x0),
  (0x28f985d9524410c77, 0xa8602, 0x50401),
  (0x297985d9524410c5f, 0x1, 0x0),
  (0x28b985d952441097b, 0x1, 0x0),
  (0x28f985d9524410977, 0x0, 0x0),
  (0x293985d952441096f, 0x0, 0x0),
  (0x297985d952441095f, 0x1, 0x0),
  (0x283985d9524410a7e, 0x1, 0x0),
  (0x287985d9524410a7d, 0x1, 0x0),
  (0x28f985d9524410a77, 0x0, 0x0),
  (0x293985d9524410a6f, 0x0, 0x0),
  (0x29b985d9524410a3f, 0x1, 0x0),
  (0x281989d9524410a7e, 0x1, 0x0),
  (0x285989d9524410a7d, 0x1, 0x0),
  (0x299989d9524410a3f, 0x1, 0x0),
  (0x2a5989d952441087f, 0x18402, 0x152054402),
  (0x28998dd952441097b, 0x1, 0x0),
  (0x29598dd952441095f, 0x1, 0x0),
  (0x28590e19524410cfc, 0x401, 0x0),
  (0x29d90e19524410c7e, 0x18a02, 0x0),
  (0x24590e19524410cfc, 0x11202, 0x0),
  (0x28b91619524410af9, 0x0, 0x91824402),
  (0x28b97619524410a7b, 0x1, 0x0),
  (0x28f97619524410a77, 0x0, 0x0),
  (0x29397619524410a6f, 0x0, 0x0),
  (0x29797619524410a5f, 0x1, 0x0),
  (0x28197e19524410c7e, 0x1, 0x0),
  (0x28597e19524410c7d, 0x1, 0x0),
  (0x21d90e19524410c7e, 0xa01, 0x0),
  (0x2839661d524410a7e, 0x1, 0x0),
  (0x2879661d524410a7d, 0x1, 0x0),
  (0x28f9661d524410a77, 0x0, 0x0),
  (0x2979661d524410a5f, 0x1, 0x0),
  (0x24590595724410d7c, 0x51602, 0xc2830802),
  (0x24990595724410d7a, 0x51203, 0xd6835802),
  (0x21985595724410e1f, 0x8002, 0x0),
  (0x2839859572441097e, 0x1, 0x0),
  (0x2879859572441097d, 0x1, 0x0),
  (0x28f98595724410977, 0x0, 0x0),
  (0x28f98595724410a77, 0x1, 0x0),
  (0x29798595724410a5f, 0x1, 0x0),
  (0x29598995724410a5f, 0x1, 0x0),
  (0x28198d9572441097e, 0x1, 0x0),
  (0x28598d9572441097d, 0x1, 0x0),
  (0x28b81601654410afc, 0x1601, 0x13184c402),
  (0x28784601654410afc, 0x0, 0x0),
  (0x1d590e09654410d5e, 0x2401, 0x39a01),
  (0x21d90e09654410c7e, 0x18a02, 0x0),
  (0x28f87609654410a77, 0x0, 0x0),
  (0x2879060b654410cfc, 0x0, 0x0),
  (0x2839160b654410cfc, 0x801, 0x0),
  (0x2839760b654410c7e, 0x1, 0x0),
  (0x2879760b654410c7d, 0x1, 0x0),
  (0x28f9760b654410877, 0x202, 0x0),
  (0x28f9760b654410c77, 0x601, 0x0),
  (0x29b925d5654410b1f, 0x4918203, 0x0),
  (0x24790e1d654410e7c, 0x0, 0x0),
  (0x24f90e1d654410e76, 0x1, 0x0),
  (0x29190e1d654410a7e, 0x0, 0x0),
  (0x2839261d654410a7e, 0xb8002, 0x0),
  (0x2879261d654410a7d, 0x1, 0x0),
  (0x24f9261d654410c77, 0x10c02, 0x58401),
  (0x28f9261d654410a77, 0x50602, 0x0),
  (0x2939261d654410a6f, 0x2e01, 0x58401),
  (0x2979261d654410a5f, 0x1, 0x0),
  (0x24f92e1d654410c77, 0x0, 0x0),
  (0x28993e1d654410c77, 0x401, 0x5c401),
  (0x28b93e1d654410c77, 0x0, 0x0),
  (0x28393e1d654410e76, 0x3510e03, 0x0),
  (0x28f86609754410a77, 0x0, 0x0),
  (0x29190e1975441097e, 0x0, 0x0),
  (0x24790e19754410d7c, 0x0, 0x0),
  (0x24f90e19754410d76, 0x1, 0x0),
  (0x28393e19754410d76, 0xd0e02, 0x0),
  (0x14981585504810fd8, 0x98409204, 0x0),
  (0x19581585504810f9c, 0x1510098205, 0x0),
  (0x25d52585504810f5a, 0x3f09603, 0x0),
  (0x26152585504810dda, 0x18813404, 0x191060402),
  (0x26352585504810dda, 0x801, 0x1b1068402),
  (0x28965585504810f9a, 0x10002, 0x14401),
  (0x25d65585504810f1e, 0xf8002, 0x0),
  (0x28b985855048109fa, 0x3401, 0x0),
  (0x28f985855048109f6, 0x1, 0x60401),
  (0x29f9858550481097e, 0x1, 0x64401),
  (0x28998d855048109fa, 0x0, 0x6c401),
  (0x29598d855048109de, 0x0, 0x6c401),
  (0x29d98d8550481097e, 0x1, 0x68401),
  (0x1d952605504810f5a, 0x6a602, 0x0),
  (0x21952605504810eda, 0x310803, 0x0),
  (0x29952605504810bda, 0x11202, 0x0),
  (0x19562605504810f9a, 0x286c403, 0x0),
  (0x21962605504810eba, 0x110802, 0x0),
  (0x1d965605504810f1e, 0x6a603, 0x0),
  (0x28576549504810f5a, 0x4bf0806c083408, 0x0),
  (0x28776549504810b5a, 0x24beaae9a407, 0x0),
  (0x28586549504810eda, 0xd10853405, 0x1d1070402),
  (0x28786549504810eda, 0x51e02, 0x0),
  (0x28786549504810bda, 0x51e10204, 0x0),
  (0x28565589504810f9a, 0x1601, 0x1e1028402),
  (0x24991595504810dda, 0x0, 0x1d2030402),
  (0x1d991595504810f1e, 0x5a603, 0x0),
  (0x29f91595504810b5e, 0x2601, 0x1e1074802),
  (0x28576595504810f1e, 0x4be83401b04208, 0x0),
  (0x28776595504810b1e, 0x53ea92ba659e08, 0x0),
  (0x297915d9504810b5e, 0xd4202, 0x0),
  (0x28b91619504810afa, 0xd4402, 0x0),
  (0x28f91619504810af6, 0x1401, 0x1c1870402),
  (0x29f91619504810a7e, 0x801, 0x1d1874402),
  (0x28165585514810f9c, 0x20002, 0x7c401),
  (0x21d65585514810f1d, 0x31c204, 0x0),
  (0x29d65585514810f1d, 0xafc604, 0x0),
  (0x29b87585514810b3d, 0x4201, 0x0),
  (0x24990595514810dda, 0x201, 0x1f1035802),
  (0x28576595514810f1d, 0x6c083403e06, 0x0),
  (0x29b87595514810b1f, 0x118202, 0x0),
  (0x28797595514810b5d, 0x4601, 0x0),
  (0x287985d951481097d, 0x1, 0x0),
  (0x28f985d9514810977, 0x0, 0x0),
  (0x297985d951481095f, 0x1, 0x0),
  (0x283985d9514810a7e, 0x1, 0x0),
  (0x28f985d9514810a77, 0x0, 0x0),
  (0x29b985d9514810a3f, 0x1, 0x0),
  (0x281989d9514810a7e, 0x1, 0x0),
  (0x299989d9514810a3f, 0x1, 0x0),
  (0x28598dd951481097d, 0x1, 0x0),
  (0x29598dd951481095f, 0x1, 0x0),
  (0x28797619514810a7d, 0x1, 0x0),
  (0x28f97619514810a77, 0x0, 0x0),
  (0x29797619514810a5f, 0x1, 0x0),
  (0x28197e19514810c7e, 0x1, 0x0),
  (0x28b90607654810cfa, 0x0, 0x0),
  (0x28397607654810c7e, 0x1, 0x0),
  (0x29b915d5654810b1f, 0x4910203, 0x0),
  (0x24790e1d654810c7e, 0x0, 0x0),
  (0x24b90e1d654810e7a, 0x0, 0x0),
  (0x2839161d654810a7e, 0x1, 0x0),
  (0x28f9161d654810a77, 0x0, 0x0),
  (0x2979161d654810a5f, 0x1, 0x0),
  (0x24b90e19754810d7a, 0x0, 0x0),
  (0x189525c5605410f9a, 0x6c402, 0x0),
  (0x299525c5605410b9e, 0x1201, 0x1c801),
  (0x1c9625c5605410f3a, 0x464c403, 0x0),
  (0x195725c5605410f1e, 0xb14690809207, 0x0),
  (0x19582dc5605410e9e, 0x240c403, 0x3ca01),
  (0x195745c5605410f1e, 0xb14a10205, 0x0),
  (0x28584dc5605410afc, 0x48202, 0x80401),
  (0x19584dc5605410e9e, 0x280bc03, 0x80401),
  (0x28b655c5605410b9e, 0xc202, 0x0),
  (0x249625c7605410d3a, 0x12baa74690208, 0x0),
  (0x195825c7605410f1e, 0x14f8003, 0x0),
  (0x195925c7605410d1e, 0x12a2e52a74691609, 0x0),
  (0x195945c7605410d1e, 0xa11caaca1e07, 0x80201),
  (0x19584dc7605410e1e, 0x2a8aac80406, 0x0),
  (0x289655c7605410f1e, 0x1244c004, 0x0),
  (0x291655c7605410f1e, 0x13602, 0x0),
  (0x25991549605410d9e, 0x4801, 0x0),
  (0x29d62549605410f9a, 0x6a482804, 0x0),
  (0x25982549605410f9a, 0x10002, 0x0),
  (0x28596549605410d9e, 0x504803, 0x221084402),
  (0x28796549605410d9e, 0x21e02, 0x20801),
  (0x28b98549605410bda, 0x16a0003, 0x0),
  (0x195915cb605410d1e, 0x52ab92a1a06, 0x0),
  (0x285655cb605410f1e, 0x4c002, 0x40801),
  (0x24991595605410d9e, 0x811203, 0x211044802),
  (0x28b91595605410b9e, 0x59c99205, 0x84401),
  (0x25191595605410d9e, 0x402, 0x7d801),
  (0x29391595605410b9e, 0x472604, 0xe0838002),
  (0x28792595605410b9e, 0x126a404, 0x0),
  (0x19571601615410f9c, 0x202, 0x0),
  (0x20952601615410eda, 0x1201, 0x0),
  (0x19582601615410e9e, 0xd0101204, 0x0),
  (0x19584601615410e9e, 0x18d0403605, 0x0),
  (0x19574e01615410f1e, 0x81c02, 0x0),
  (0x28387549615410ade, 0x0, 0x19100c802),
  (0x28b87549615410adb, 0x0, 0x64401),
  (0x28f87549615410ad7, 0x401, 0x60401),
  (0x28187d49615410ade, 0x0, 0x1a1010802),
  (0x28987d49615410adb, 0x0, 0x68401),
  (0x2a587d496154108df, 0x401, 0x6c401),
  (0x28f875c9615410a77, 0x0, 0x0),
  (0x28f87609615410a77, 0x0, 0x0),
  (0x28587a09615410a7d, 0x801, 0x0),
  (0x29987a09615410a3f, 0x801, 0x0),
  (0x195915cb615410d1d, 0x2a512a2e09a07, 0x0),
  (0x287985cb615410c7d, 0x1, 0x0),
  (0x28f985cb615410877, 0x1, 0x0),
  (0x28f985cb615410c77, 0x601, 0x0),
  (0x287985cb61541097d, 0x1, 0x0),
  (0x28f985cb615410977, 0x0, 0x0),
  (0x1959060b615410c9e, 0x494aae00271e08, 0x0),
  (0x2839760b615410c7e, 0x1, 0x0),
  (0x2839760b6154108fe, 0x1, 0x0),
  (0x28392595615410b9e, 0x2401, 0xe6818402),
  (0x28792595615410b9d, 0x1a01, 0x18401),
  (0x28990e1d6154108fe, 0x0, 0x0),
  (0x29190e1d6154108fe, 0x0, 0x0),
  (0x24790e1d615410cfc, 0x0, 0x0),
  (0x24f90e1d615410cf6, 0x1, 0x0),
  (0x28393e1d615410cf6, 0xd0002, 0x0),
  (0x2939661e61541093f, 0x0, 0x0),
  (0x2839861e615410c7e, 0x1, 0x0),
  (0x28b9861e61541087f, 0x0, 0x0),
  (0x28f9861e615410877, 0x0, 0x0),
  (0x28f9861e615410c77, 0x601, 0x0),
  (0x19572589715410f1b, 0x2519310205, 0x0),
  (0x2839758971541097e, 0xa01, 0x0),
  (0x1958258971d410e1b, 0x4a8aa4b8259c08, 0x0),
  (0x28b8658971d410e3b, 0x0, 0x0),
  (0x2839858971d410c7e, 0x401, 0x0),
  (0x28b9858971d410c7b, 0x1, 0x0),
  (0x28b9858971d410a7b, 0x1, 0x0),
  (0x2839259571d410b5e, 0x2401, 0x0),
  (0x2839261971d410a7e, 0x0, 0x0),
  (0x283915d9525410b5e, 0x0, 0x8481d1024803),
  (0x28b915d9525410b5b, 0x4401, 0x74401),
  (0x28f915d9525410b57, 0x1401, 0x222070402),
  (0x28592dd9525410b5b, 0x4401, 0x24108c402),
  (0x28592dd95254109db, 0x0, 0x261094402),
  (0x19572601625410f9a, 0x202, 0x0),
  (0x21572601625410eda, 0x1600203, 0x0),
  (0x28391595625410b9e, 0x2601, 0x1e102ca02),
  (0x28590e1d6254108fe, 0x0, 0x9c401),
  (0x24b90e1d625410cfa, 0x0, 0x0),
  (0x2839861e625410c7e, 0x1, 0x0),
  (0x2879861e62541087f, 0x0, 0x0),
  (0x28f9161972d410a77, 0x0, 0x0),
  (0x20990e05655410cde, 0x0, 0x1d204c802),
  (0x28990e056554109de, 0x7c802, 0x0),
  (0x29190e056554109de, 0x3c01, 0x0),
  (0x28590e096554109de, 0x4801, 0xa0401),
  (0x20790e05765410d7c, 0x0, 0x0),
  (0x28990e0576541097e, 0x0, 0x0),
  (0x29190e0576541097e, 0x0, 0x0),
  (0x24f90e05765410d76, 0x1, 0x0),
  (0x24f82605765410c77, 0x0, 0x0),
  (0x24f82e05765410c77, 0x0, 0x0),
  (0x28393e05765410d76, 0x3510e03, 0x0),
  (0x21193e05765410c77, 0x1401, 0xa4401),
  (0x21393e05765410c77, 0x0, 0x0),
  (0x28392607765410c7e, 0x401, 0x0),
  (0x28392607765410a7e, 0x0, 0x0),
  (0x28592e07765410a7d, 0x1, 0x0),
  (0x28594e07765410a7d, 0x1, 0x0),
  (0x28382607765410a7e, 0x0, 0x0),
  (0x2839260776541097e, 0xa01, 0x0),
  (0x20b92607765410c7b, 0x1, 0x0),
  (0x2839460776541097e, 0xa01, 0x0),
  (0x28590e0976541097e, 0x0, 0xa8401),
  (0x20b90e09765410d7a, 0x0, 0x0),
  (0x28f9160b765410877, 0x202, 0x0),
  (0x28f9160b765410c77, 0x601, 0x0),
  (0x28f9160b765410a77, 0x0, 0x0),
  (0x2839160b76541097e, 0x801, 0x23188c402),
  (0x28f9160b765410977, 0x0, 0x241890402),
  (0x283926077654108fe, 0x1, 0x0),
  (0x283946077654108fe, 0x1, 0x0),
  (0x2839160b7654108fe, 0x1, 0x94401),
  (0x28f9160b7654108f7, 0x0, 0x98401),
  (0x28f9160b7059508f7, 0x50002, 0xa882828a0803),
  (0x2879260570d950a7d, 0x1, 0x0),
  (0x2939260570d950a6f, 0x0, 0x0),
  (0x28192e0570d950c7e, 0x401, 0x0),
  (0x28192e0570d950a7e, 0x0, 0x0),
  (0x2879460570d950a7d, 0x1, 0x0),
  (0x28b9160970d950a7b, 0x1, 0x0),
  (0x2939160970d950a6f, 0x0, 0x0)]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def records8 : Array Raw := #[

  (0x545454044107cc, 0x608812a4a688ab000b, 0x3100c002100800110040001000008),
  (0x645454044107ec, 0x2a092b0010a62609, 0x1440508104011804005),
  (0x655454044107dc, 0x4a88092b2600a09, 0x9102040710184041004006),
  (0x7654540441077c, 0x2a13472c00298a4a00b, 0x71000402),
  (0x865454044106fc, 0x882a1024ac00a9b80b, 0x81000002),
  (0x965454044105fc, 0x11ca884ac00298a0a, 0xb10284011804404),
  (0x965454044107fc, 0x472603, 0xd10304050808404),
  (0x96d454044105fc, 0x4a884a6b0008a09, 0xc401),
  (0x915954044107fc, 0x470098a05, 0x10103c60f10384060818006),
  (0x7559540441075e, 0x12ab0b102a120260a, 0x11103c008081c604),
  (0x9759540441057e, 0x4d2ab0b10600209, 0x1510504131048404),
  (0x9759540441077e, 0x184d0111206, 0x400090824003),
  (0x865d540441067e, 0x2ab022a84840206260b, 0x44401),
  (0x965d540441077e, 0x184d4404, 0x1910604171058404),
  (0x96dd540441057e, 0x12ab0b10218008, 0x0),
  (0x525855044107dc, 0x214aae092a0010a0a, 0x7441c106c41a1001c05),
  (0x7258550441077c, 0x214aae002a121422960c, 0x1e1068402),
  (0x825855044107fc, 0x1458874605, 0x7c401),
  (0x925855044107fc, 0x714a4004, 0x20106c402),
  (0x92d855044105fc, 0x852a09c100b92a0a0b, 0x84401),
  (0x6558550441079c, 0x2cac7aea94a1270438a0e, 0x2268884216884420688041f687c41e6878408602060c),
  (0x985855044107fc, 0xe4a8d1d11e07, 0x8c401),
  (0x915495044107dc, 0x852ab92a009c894610a0d, 0x9c42610944241070405),
  (0x625495044107da, 0x112a2e09aaa42000a, 0xb042b10a842910a04241001c07),
  (0x7254950441075a, 0x42baa58c0284a438210a2140f, 0x3110c083010bc42e20b842d20b442b106840a),
  (0x7654950441075e, 0x12a14aae802004d240b, 0x3210ac4251001804),
  (0x865495044106de, 0x44a852ab8222001e0b, 0x3410cc42d10a44261005806),
  (0x865495044107de, 0x12a0a50880078409, 0xd843510b842a1009805),
  (0x965495044105de, 0x44a852ab8269e9000b, 0x3810dc42d2005c04),
  (0x965495044107de, 0x48a7826a420408, 0xe442e209c41c1009c05),
  (0x86d495044106de, 0x44a852ab826c62000b, 0x30100d802),
  (0x96d495044105de, 0x112a14aae0a40200a, 0x30200dc02),
  (0x915895044107fc, 0x21c01468a06, 0x3b10e84281098604),
  (0x7258950441077a, 0x2692a16baa5050880c, 0xf4a3d10f042d20b4605),
  (0x825895044107fa, 0x4691602820207, 0x3f10f8402),
  (0x6558950441079e, 0x112a14aae09a7800a, 0x42110444010f843c10e84086011808),
  (0x955895044107de, 0x49e91a10006, 0x4310f443b1015804),
  (0x865895044107be, 0x4a852020006, 0x3f10f4a2a1015e04),
  (0x9758950441057e, 0x4be52abb41030c00b, 0x11044110ac403),
  (0x9758950441077e, 0x3404269205, 0x10c44210b0403),
  (0x985895044105fe, 0x2be01a04, 0x461114402),
  (0x98d895044105fe, 0xaa0003, 0x124448111c403),
  (0x655c950441075e, 0x12a02594aae00509e0b, 0x13044b112844110f042d2078407),
  (0x865c950441067e, 0x92a1622052ab9e0b, 0x13442d18b4403),
  (0x865c950441077e, 0x50882801e06, 0x13843d28b8403),
  (0x965c950441077e, 0xfb40420c006, 0x13c44c10bc403),
  (0x86dc950441067e, 0x24a85c0214aae0a, 0xc0401),
  (0x96dc950441057e, 0x482b94a8509e09, 0xc4401),
  (0x656095044107de, 0x2c69140a801608, 0x14043e107c403),
  (0x7660950441077e, 0x1458072405, 0x140401),
  (0x866095044106fe, 0x2c620204, 0xfc401),
  (0x91d915044105fc, 0x22a018b04092a0a0a, 0x144401),
  (0x845915044107ee, 0xa4a00488206, 0x52106da02),
  (0x6559150441079e, 0x10aaaca126027800a, 0x154454114c452114441e581c207),
  (0x9759150441057e, 0xa802b8b04d02eb60a, 0x561150402),
  (0x9759150441077e, 0x298d00e9206, 0x154401),
  (0x985915044105fe, 0xaa08e0005, 0x164458115c403),
  (0x985915044106fe, 0x2846092a806, 0x5a1071a02),
  (0x989915044106fe, 0xa11803, 0x5d117045b1075a04),
  (0x98d915044105fe, 0x28002, 0x60117c45e1174404),
  (0x655d150441075e, 0x12a282b12a007ba0a, 0x621184461015041e6879606),
  (0x865d150441067e, 0x12a0022ac4a881e0a, 0x0),
  (0x865d150441077e, 0x82829e05, 0x0),
  (0x965d150441077e, 0xe3403a0b606, 0x631188402),
  (0x86dd150441067e, 0x4a8008ab12a3609, 0x0),
  (0x96dd150441057e, 0xa8028212ce9e08, 0x0),
  (0x656115044107de, 0xa8a928008407, 0x1904521081a03),
  (0x7661150441077e, 0x2811c02205, 0x190401),
  (0x866115044106fe, 0xb28203, 0x651058002),
  (0x656135044106de, 0x12ab0a0a848008, 0x19c4661085a03),
  (0x7661350441067e, 0xaac02848a8021340a, 0x19c401),
  (0x966135044104fe, 0x42aab000884a809, 0x1a0401),
  (0x915955044107dc, 0xb24a878470098a0a, 0x6b11a84691198461114c44a110040f102580a),
  (0x925955044107de, 0x122947a411a07, 0x1b446c11a444b10884096019807),
  (0x92d955044105de, 0x112a14aae09e0160a, 0x0),
  (0x945955044107de, 0x2a211204, 0x7011bc46e11ac4610089a06),
  (0x7659550441071e, 0x7aea948003b2a12d042ac09c10, 0x1d047311c847111bc46c119c46411504501104411181d80d),
  (0x925d950441077e, 0xf94d010c006, 0x1d447110c8403),
  (0x92dd950441057e, 0x12014a82d04ba409, 0x1c8401),
  (0x945d950441077e, 0xe04d00eb606, 0x7611cc402),
  (0x94dd950441057e, 0xa8a880134b0208, 0x1d0401),
  (0x91e195044106fc, 0x14002c8482848a09, 0x7911e047710cc633102d806),
  (0x926195044106fe, 0x294fc648806, 0x7b11e8402),
  (0x92e195044106fe, 0x2808080a849e08, 0x13443418d040b6029805),
  (0x946195044106fe, 0x294e4a04, 0x1f847d11f04781048005),
  (0x94e195044104fe, 0x10aaac00221208, 0x7f1048002),
  (0x94e195044106fe, 0x29e02, 0x2004791048003),
  (0x91e195044105fc, 0x500c82a1210a08, 0x8111944351035804),
  (0x91e195044107fc, 0x82808a04, 0x0),
  (0x92e195044105fe, 0xa02021278207, 0x4e10d840d6031804),
  (0x94e195044105fe, 0xaa0078205, 0x821058002),
  (0x9461b5044104fe, 0x10aaac04a0884a80a, 0x0),
  (0x626035244106fa, 0x4b8009a912a8809, 0x84120c402),
  (0x656035244106de, 0x114aae48290008, 0x2144841145a03),
  (0x966035244104fe, 0x4294aae0024a409, 0x218401),
  (0x626055244107f9, 0x1291522610007, 0x87120c6281890404),
  (0x656055244107dd, 0x125249c808407, 0x88121c43a1898404),
  (0x7660552441077d, 0x265242a005, 0x881094402),
  (0x866055244106fd, 0x11521208a06, 0x8910ec6271065c04),
  (0x6558952441079b, 0x10a4aeaa468219e0080c, 0x8d123068c122c48a121c68712106841104a4120a4407781dc0e),
  (0x8758952441077b, 0x4a508204406, 0x23848c10b0603),
  (0x905955244107de, 0x12a1421e08a07, 0x8f1228453692c80f6019c06),
  (0x915955244107dd, 0x140a611c05, 0x90123c48b121444a2100606),
  (0x7659552441071f, 0x12baa51cd2001e0a40b, 0x24448811048116821c05),
  (0x8759552441065f, 0xa94483246bc40420a, 0x921151e412904604),
  (0x8759552441075f, 0x129440c205, 0x9312304556908604),
  (0x9759552441075f, 0x818313405, 0x95125048d1025c04),
  (0x925d952441077b, 0x103f0b400806, 0x9110c8402),
  (0x985d952441047f, 0xa944ae18400208, 0x26869a12648991260898125c4962258409),
  (0x985d952441057f, 0x613403, 0x9e127449c126c404),
  (0x985d952441067f, 0x612403, 0x28c4a212844a0127c405),
  (0x989d952441067f, 0x0, 0xa712984a51290404),
  (0x98dd952441057f, 0x0, 0x2a44a8129c403),
  (0x90e195244104fe, 0x4294aae00248609, 0xab12a8402),
  (0x90e195244106fe, 0x4886a428406, 0xac12ac44d2029c04),
  (0x916195244106fd, 0x49414120a06, 0x2b44ac10dc6371055c05),
  (0x9761952441067f, 0x1218403, 0xb11ac44b012bc4ae12ac406),
  (0x97e1952441047f, 0x9252a22e18409, 0xb312c8402),
  (0x97e1952441067f, 0x1221e03, 0x3818e0415702dc04),
  (0x90e195244105fe, 0x1211a08a05, 0xb4122444e2031c04),
  (0x8761952441067f, 0x409203, 0x2d04b1190c603),
  (0x97e1952441057f, 0x48878204, 0xe44197035c03),
  (0x9161b5244104fd, 0x8112baa50008b2240b, 0x0),
  (0x9761b52441047f, 0xa94093246b861000a, 0x0),
  (0x9661d52441067f, 0xc10203, 0x2e04b722dc4b612d48b51268607),
  (0x96e1d52441047f, 0xaa512b8610008, 0x268601),
  (0x96e1d52441067f, 0xc91c404206, 0x2686921159a442910605),
  (0x96e1d52441057f, 0x310109205, 0x2c46931238403),
  (0x9059572441077e, 0x12a1402078407, 0xba12e4461698584b292c806),
  (0x9159572441077d, 0x49401c99e58a08, 0xb922e444a292884a1928406),
  (0x8559572441075f, 0x124710308006, 0xbb1189a4c2930604),
  (0x9859572441057f, 0x678403, 0x2f88be12f44bc22f0405),
  (0x9859572441067f, 0x1c210004, 0xc01b004bf22fc404),
  (0x9899572441067f, 0x1, 0x3046c1129c403),
  (0x98d9572441057f, 0x0, 0xc313088c2129c404),
  (0x8661572441067f, 0x202, 0x2ec4b81ae0403),
  (0x96e1572441057f, 0x324710005, 0xb8198da4f293c604),
  (0x9661772441047f, 0xa944ae1c210209, 0x0),
  (0x816016544106fc, 0x220002c92a0472629e0c, 0xc463104b962e448f6a3d88f1a3c410604040a),
  (0x91e016544107fc, 0x82848405, 0x0),
  (0x826016544106fe, 0x28801204, 0xba11ec46b69ad8106039c06),
  (0x846016544106fe, 0xa11203, 0xc512e54ad61f846969a5806),
  (0x94e016544105fe, 0xa10082805, 0xc462b58906a4186a69a9806),
  (0x90e096544105fe, 0x4806a428806, 0xc713186c6131586e69b9806),
  (0x7560965441075f, 0x409a91205, 0xc611bda6c183dc04),
  (0x8760965441067f, 0x10819204, 0xc8131c4ae1041c04),
  (0x97e0965441057f, 0x48068290806, 0x7e61ec47069c186d19b4406),
  (0x9060b6544104fe, 0x429252ab8009e09, 0x324401),
  (0x9160b6544104fd, 0x2044aea9400229e0a, 0x328401),
  (0x9760b65441047f, 0x2ea9448800218409, 0xce13344cc132c404),
  (0x925d565441075f, 0x12465440c206, 0xcf124467369c4604),
  (0x92dd565441055f, 0x4aa5026c4b8008, 0x7469c8602),
  (0x90e1d65441067e, 0xc82480d4406, 0x3484d113404151049805),
  (0x9261d65441067f, 0x14b8e10805, 0xd81b604d713584d513504d31258808),
  (0x92e1d65441047f, 0x44aa5080021ae09, 0x258801),
  (0x92e1d65441067f, 0x294b8804, 0xd912588156051804),
  (0x93e1d654410477, 0x400248a52a07, 0xdb636c4da6368404),
  (0x93e1d654410677, 0x12504d000c418e09, 0xdc63704d963644d563544d16344413604c40a),
  (0x90e1d65441077e, 0x3511204, 0x0),
  (0x92e1d65441057f, 0x140340c448807, 0x2b84941a50403),
  (0x93e1d654410577, 0x13448008b11478e0a, 0xc863204956a558951a54406),
  (0x93e1d654410777, 0xd4448605, 0x0),
  (0x8660975441067f, 0x830203, 0x3744d81ad4803),
  (0x96e0975441057f, 0xc918108806, 0xd81b3c47669d4604),
  (0x9660b75441047f, 0x112a94202006bc40a, 0x0),
  (0x90e1975441057e, 0xc824a804406, 0x3784191059803),
  (0x90e1975441077e, 0x320b510005, 0xe0137c402),
  (0x92e1975441057f, 0x850203, 0x2d48196061803),
  (0x93e19754410577, 0x4a80a654413400e0a, 0xe163844dd6374417605c406),
  (0x93e19754410777, 0xd0310604, 0xe06380402),
  (0x9261b75441047f, 0x2a944af10610009, 0x0),
  (0x815855048107fc, 0x54448098206, 0xe31388402),
  (0x525855048107da, 0xaea92a162861002240c, 0x3988e613948e513904e2238842b1068409),
  (0x6558550481079e, 0x4a852ab9609e1000a, 0x3a04e7138c4411078405),
  (0x9758550481077e, 0xfc201604, 0xe81390402),
  (0x985855048105fe, 0x14206d0005, 0xeb13a84e91394404),
  (0x98d855048105fe, 0x20002, 0xee13b44ec1398404),
  (0x526055048107da, 0x80460aa1161aea1310a5260f, 0x3c44f013bc4e51388405),
  (0x626055048107fa, 0x4a86c404, 0x3cc4f213c4403),
  (0x656055048107de, 0x509102a1202608, 0xf413c84f1138c404),
  (0x7660550481077e, 0x4806a604, 0xf413bc402),
  (0x866055048106fe, 0x910203, 0xf313c0402),
  (0x7654950481075a, 0x8580c24faaba848210c6a00f, 0x3d84f513bc8ef10ac405),
  (0x865495048106da, 0x788030916aaea120843200e, 0xf813dc4f120b4404),
  (0x865495048107da, 0x200c040ae7863162a84a00e, 0xf913c04e510b8404),
  (0x86d495048106da, 0xc102692a2ea971a4c000d, 0xc0401),
  (0x6558950481079a, 0xc112a2ea966827b00080d, 0xfa13c8af210f0404),
  (0x955895048107da, 0x12a1668232e13000891e0d, 0xf328f4402),
  (0x985895048107fa, 0x5bf19e6a806, 0x0),
  (0x915955048107de, 0x99602, 0x3f44fc13ec4fa1128405),
  (0x925955048107da, 0x12a0269678cb84c009080d, 0x3ec4e7112c403),
  (0x7659550481071e, 0x5807aefaa52848432023009a10, 0x3fc4fe13f04f41104405),
  (0x915d950481077e, 0x4be8340426c008, 0x4004fe13d4403),
  (0x91dd950481057e, 0x14faa092b8012609, 0xff13d8402),
  (0x916195048106fe, 0x1420cd4405, 0x40c50214044f71bdc405),
  (0x91e195048106fe, 0x51e02, 0xf81be0402),
  (0x92e195048106fa, 0x16b80c02808a0409, 0x134401),
  (0x91e195048105fe, 0x50078204, 0x3e4401),
  (0x92e195048105fa, 0x16b80c2808480809, 0x138401),
  (0x92e195048107fa, 0x8080a804, 0x0),
  (0x6558551481079d, 0x80996786b9252a21c10a0e, 0x4185051c1450424104547951c07),
  (0x8758551481077d, 0x420a604605, 0x1071414402),
  (0x905955148107de, 0x2a0803, 0x10814104e72985804),
  (0x7659551481071f, 0x12a94f9a0ae01e8260b, 0x1091151c02),
  (0x8759551481075f, 0x11829c204, 0x10a14144e82ba0604),
  (0x9759551481075f, 0x2831be04, 0x10b1418402),
  (0x915d951481077d, 0x6c0834042f8a08, 0x424401),
  (0x985d951481057f, 0x613e03, 0x10e143490d1430404),
  (0x985d951481067f, 0x612603, 0x444510244050f243c405),
  (0x989d951481067f, 0x0, 0x1131448912129c404),
  (0x98dd951481057f, 0x0, 0x454514129c403),
  (0x9761951481067f, 0x611603, 0x460718145c9171458405),
  (0x97e1951481047f, 0x92294a86b8409, 0x1192464402),
  (0x97e1951481067f, 0xa79603, 0x0),
  (0x8761951481067f, 0x9602, 0x460601),
  (0x97e1951481057f, 0x29e09604, 0x0),
  (0x9761b51481047f, 0xa9409322f1061000a, 0x0),
  (0x96e1d51481057f, 0x318109605, 0x46070a141c403),
  (0x816016548106fe, 0x21602, 0x10313ecafb22e4404),
  (0x826016548106fa, 0x3009a5ae808a2411e0c, 0x42070812e8403),
  (0x92e016548107fa, 0x82858405, 0x0),
  (0x7560565481075f, 0xa659c04, 0xfc2bf0602),
  (0x8760565481067f, 0xa49603, 0x458401),
  (0x97e0565481057f, 0x49401c0a658a08, 0x103240c4fd2bf48fd1bf4406),
  (0x906076548104fe, 0x248852ab8459e0a, 0x468401),
  (0x9760765481047f, 0x2a5122800ae18409, 0x11b246c402),
  (0x915d565481075f, 0x947212a440c208, 0x11c14246fe2bf8604),
  (0x91dd565481055f, 0x12a940c6b8059c09, 0xff2bfc602),
  (0x90e1d65481067e, 0xb9633003e0c608, 0x47851d12ac403),
  (0x9161d65481067f, 0x48c10a04, 0x4847211480920147c91f12ac8ab125c409),
  (0x91e1d65481047f, 0x44aa500088b8609, 0x25c401),
  (0x91e1d65481067f, 0x48a02, 0x47491d125c403),
  (0x90e1d65481077e, 0x3f19604, 0x0),
  (0x91e1d65481057f, 0x1203e0c629607, 0x45850b1c2c403),
  (0x8660575481067f, 0x28202, 0x1211ad84b422d0404),
  (0x96e0575481057f, 0xc910a04206, 0x1211c705002c00604),
  (0x9660775481047f, 0x112a9408022e1c60a, 0x0),
  (0x90e1975481057e, 0x11ae096a0cc0008, 0x2d0401),
  (0x90e1975481077e, 0xf8318004, 0x488401),
  (0x91e1975481057f, 0x1208a03, 0x2d8401),
  (0x9161b75481047f, 0x2a944c6b8610009, 0x0),
  (0x525c56054107de, 0x9102a1212607, 0x124148c4ef1090804),
  (0x625c56054107be, 0x4a85086c406, 0x494524148c42c28a0a05),
  (0x725c560541077e, 0xb14690809207, 0x1261494402),
  (0x82dc56054106fe, 0x4a40c404, 0x127120ca02),
  (0x745c560541077e, 0xb14a10205, 0x4a0401),
  (0x84dc56054106fe, 0xa120bc04, 0x12a14a4402),
  (0x655c560541079e, 0x12a0b13209420e1840260d, 0x4ac52a14a0527149852414158f41230887219000b),
  (0x625c760541073e, 0x12a0052aba009a11c0b, 0x4b0401),
  (0x825c760541077e, 0x53e58004, 0x4b4401),
  (0x925c760541057e, 0x12a00b94a8211d1a40b, 0x12e14b0402),
  (0x945c760541057e, 0x28011ca82b2808, 0x12f14a4202),
  (0x84dc760541067e, 0xaa2a0ac80408, 0x4c0401),
  (0x655c760541071e, 0x32b1e82ea943a848429c0e, 0x13214c453014bc52e14b452a099c008),
  (0x915496054107de, 0x2722003, 0x133148c8ef2094404),
  (0x6254960541079a, 0x580c026a482aba84843080e, 0x4d05232c8c9231c8c405),
  (0x825496054107da, 0x91603011a0ae33e8284880e, 0x4d452518b0803),
  (0x9654960541059e, 0x780c16baa5284843202026a410, 0x4dc536149072410a4805),
  (0x9654960541079e, 0x6a020431e030ba45a84820e, 0x4d453310a8803),
  (0x985496054107de, 0x171a46a006, 0x13814d0402),
  (0x655c960541079e, 0x80c0418cb885c62a84a40e, 0x12d1c9848c2140404),
  (0x915cb60541057e, 0x52ab82692a001440a, 0x4e4401),
  (0x655cb60541071e, 0x30796baa52848432021a0e, 0x13a14e45271a10804),
  (0x9159560541079e, 0xa4b209e18811c0260b, 0x13e14f453c14ec53a1ce85320cc810664118fc1bf048d222c86f09bc010),
  (0x9259560541079e, 0x68210c030b8819e58a4a40e, 0x13f14ec5311cc448d222886c19b0408),
  (0x92d9560541059e, 0x3059ebaa5284843202020e, 0x12b1cac402),
  (0x656111094106ce, 0x282112a0e0144160a, 0x0),
  (0x7661110941066e, 0xa002112a0e5105a00b, 0x0),
  (0x8659510941069e, 0xa10248e0144265a00b, 0x0),
  (0x98dd910941067e, 0x4a858009012008, 0x0),
  (0x8659520941069e, 0x2203044900960240a, 0x0),
  (0x98dd920941067e, 0x12a1600231012009, 0x0),
  (0x716016154107fc, 0x1200203, 0x500401),
  (0x526016154107de, 0x81448404, 0x5044e4106c803),
  (0x826016154106fe, 0xd040284c006, 0x1421504402),
  (0x646016154107be, 0x20d0401205, 0xe26895602),
  (0x846016154106fe, 0x634100a3606, 0x50c401),
  (0x74e0161541077e, 0x81270404, 0x510401),
  (0x6560161541079e, 0x12a320a079473410e00a0d, 0x510543150854013a04e36a216550149e09),
  (0x875496154106df, 0x20613404, 0x51c54615144e51070805),
  (0x87d496154106df, 0x20402, 0x52854915204e61074805),
  (0x655c961541079f, 0x25192a0a51c07, 0x1436955e50107c404),
  (0x875c961541067f, 0x20651c04, 0x14b143ca02),
  (0x87dc961541067f, 0x21402, 0x1122a9c402),
  (0x6560961541079f, 0x12a0471a54007, 0x14213a04646880404),
  (0x8760961541067f, 0x20652804, 0x14c127c802),
  (0x87a0961541067f, 0x21402, 0x14e15344a71290804),
  (0x915cb61541057d, 0x2a5024a802e2c409, 0x53c401),
  (0x655cb61541071f, 0x4a8a9402e09a79c0a, 0x14f1145e02),
  (0x985cb61541047f, 0x12a512b880060c40a, 0x5485511540403),
  (0x985cb61541057f, 0x712803, 0x154154c402),
  (0x9060b6154104fe, 0x494a82b84d1c09, 0x554401),
  (0x6560b61541069f, 0x12a14aae70078209, 0x1551511a676884404),
  (0x9760b61541047f, 0x494aae2020061340a, 0x558401),
  (0x9760b6154104ff, 0xd1c02, 0x55c401),
  (0x9259561541079f, 0x471e29a02407, 0x564558139c46f69b04537888407),
  (0x90e1d6154104fe, 0x3209200405, 0x15b156854513ac45a7964006),
  (0x90e1d6154106fe, 0xcb510004, 0x15d1570402),
  (0x91e1d6154106fd, 0x3470003, 0x570401),
  (0x92e1d6154104ff, 0x13471400806, 0x146143caeb13a4404),
  (0x93e1d6154104f7, 0x4a80b213470a50e0b, 0x15e1531b4b151c4ea1160006),
  (0x93e1d6154106f7, 0x3470603, 0x574401),
  (0x94e1d6154104ff, 0x11c02, 0x27d659015c003),
  (0x90e1d6154105fe, 0x2792a0005, 0x0),
  (0x93e1d6154105f7, 0x4a809c05, 0x8c401),
  (0x9161e61541057d, 0x3209274428007, 0x5345486bb9a60796c005),
  (0x9261e61541057f, 0x21402, 0xa712908607979e04),
  (0x9461e61541057f, 0x10202, 0x14a6d25b1253b9aec6a9d406),
  (0x9661e61541053f, 0x12c8201c05, 0x15f153854a6bb5a5f7970006),
  (0x9861e61541047f, 0xc8248818013408, 0x58c562158596115804a7529c45d7174009),
  (0x7654971541075f, 0x910203, 0x4cc8f0109c803),
  (0x965497154105df, 0x2611203, 0x4904f11098803),
  (0x7258971541077b, 0x2519a09310807, 0x1641494402),
  (0x6558971541079f, 0x264a85086c407, 0x16413d04f2122084228e8a06),
  (0x7658971541073f, 0x86c403, 0x13323cc44328eca04),
  (0x9758971541057f, 0xa49a03, 0x1651280602),
  (0x97d8971541057f, 0x29202, 0xa71294602),
  (0x655c971541075f, 0x2518b10809207, 0x5905436c98403),
  (0x655d171541075f, 0xb14a10205, 0x509b425ca0403),
  (0x92d957154105df, 0x260c203, 0x4ac401),
  (0x91dd971541077d, 0x110a08004, 0x0),
  (0x92dd971541057f, 0x28809404, 0x2d08892065803),
  (0x94dd971541057f, 0x408a03, 0x194001),
  (0x8258971d41067b, 0x12a2a0a5180b8809, 0x16614b0402),
  (0x6558971d41071f, 0x4a8baa50009a79c0a, 0x598401),
  (0x8658971d41063f, 0x4a8baa50020208, 0x59c401),
  (0x9858971d41047f, 0x112a94280b860c60a, 0x16915a0402),
  (0x9858971d41067f, 0x51a803, 0x5a8401),
  (0x6560971d41065f, 0x12a2a502946b8059c0b, 0x16614b8402),
  (0x6561171d41065f, 0x11c08aaaca1f2800a, 0x1555cbc402),
  (0x9259571d41075f, 0x40a44c005, 0x16b14c4402),
  (0x9459571d41075f, 0xa213604, 0x1321198002),
  (0x9261971d41067f, 0x11518804, 0x16c15a4402),
  (0x92e1971d41047f, 0x112a940801ae08, 0x5a4401),
  (0x92e1971d41067f, 0x502a0804, 0x169159c402),
  (0x9461971d41067f, 0x14a02, 0x15659a0002),
  (0x94e1971d41047f, 0x10200a22a1ac08, 0x559601),
  (0x94e1971d41067f, 0x401, 0x559601),
  (0x915d952541075f, 0x834453405, 0x16f15b856d14d88f710dc806),
  (0x91dd952541075f, 0x11e21404, 0x13723e043820cc404),
  (0x92dd952541075b, 0x5aec00782a0808, 0x5c043820d0403),
  (0x91dd95254105df, 0x11e20204, 0x3e443920d4403),
  (0x92dd95254105db, 0x16bb000291ea0809, 0x5c443920d8403),
  (0x92dd95254107db, 0x782a0804, 0x0),
  (0x726016254107fa, 0x1600203, 0x5ccb7315c8403),
  (0x6560162541079e, 0x10c7a0030bbe09a5a84880e, 0x1721590a4210f8a04),
  (0x856016254106de, 0x5be09abb000881e9040c, 0x5cc44310fca03),
  (0x766016254107be, 0x80858004, 0x1732cd4802),
  (0x9159562541079f, 0x47086a605, 0x5d0b7413f0afc13e84402900407),
  (0x90e156254107de, 0x1e90003, 0x0),
  (0x90e1d6254104fe, 0xa2e58203030408, 0x5d45651118403),
  (0x90e1d6254106fe, 0x3f18003, 0x5d8401),
  (0x91e1d6254104ff, 0x11229a04, 0x2806461114403),
  (0x92e1d6254106fb, 0x3e68003, 0x5d8401),
  (0x90e1d6254105fe, 0x9e58092806, 0x4e0801),
  (0x9161e62541057f, 0x1220a03, 0xa71294849291ca04),
  (0x9261e62541057b, 0xc005826c6b8808, 0x124a01),
  (0x9661e62541053f, 0x5b00026ae06, 0x120a01),
  (0x9861e62541047f, 0x300162ae08613e09, 0x5e0577129c403),
  (0x91dd972541057f, 0x9402, 0x0),
  (0x92dd972541077b, 0x46a0220005, 0x0),
  (0x6560572d41065f, 0x2a512a026af10009, 0x14f14e4402),
  (0x9159572d41075f, 0xa64c004, 0x13a1214802),
  (0x9161972d41067f, 0x48d10a04, 0x5e45501218803),
  (0x91e1972d41047f, 0x112a940021ae08, 0x540401),
  (0x91e1972d41067f, 0x48a02, 0x540401),
  (0x90e056554105de, 0xc82012a1e98408, 0x17c15ec57a15d05595bf449021c0008),
  (0x90e056554107de, 0x1e98403, 0x0),
  (0x826056554106df, 0x421203, 0x17a15b493b13ec48f21a4406),
  (0x92e056554105df, 0x11c0a659206, 0x5d0b6d24f04fd11a8405),
  (0x846056554106df, 0x8402, 0x13d142146b11ac004),
  (0x94e056554105df, 0x11c0a604, 0x56173e131947001b8005),
  (0x90e096554105de, 0x2b80c167a890409, 0x5f456b15604c611b4405),
  (0x90e096554107de, 0x59e90404, 0x0),
  (0x91e096554105df, 0x409a91205, 0x56453f11b4403),
  (0x90e0576541057e, 0x4a8c8202006, 0x18015fc57e15b476d140c4ad21f8008),
  (0x90e0576541077e, 0x12cb510005, 0x60457e1340403),
  (0x81e0576541077d, 0xd4428004, 0x5f8401),
  (0x8260576541067f, 0x28831204, 0x182147c8d4131c404),
  (0x82e0576541067f, 0x28831404, 0x18312b08ab2055804),
  (0x92e0576541057f, 0x4d1400310a48809, 0x5b876e147c9031404405),
  (0x93e05765410577, 0x4a878b10050213480e0c, 0x6185851610583160856f1dbc50211f4009),
  (0x93e05765410777, 0x12d4428605, 0x1811345802),
  (0x8460576541067f, 0x29418404, 0x18516140d3634d404),
  (0x84e0576541067f, 0x418a03, 0x18611e0002),
  (0x94e0576541057f, 0x10a02, 0x34d47e01f0003),
  (0x9260776541047f, 0x44aa508002b8609, 0x18712c8802),
  (0x9260776541067f, 0x450803, 0x6204d262c8803),
  (0x92e0776541067f, 0x50802, 0x6244b22055803),
  (0x9460776541047f, 0x10a00222a1ac08, 0x465401),
  (0x9460776541067f, 0x401, 0x11951fc002),
  (0x94e0776541067f, 0x401, 0x18a1465402),
  (0x8260776541067f, 0x1401, 0x62c401),
  (0x9260776541057f, 0x449428805, 0x18d16304d261dc404),
  (0x82e0776541067f, 0xa21203, 0x18d1624402),
  (0x9460776541057f, 0x10a02, 0x63858a0200003),
  (0x84e0776541067f, 0x10a02, 0x18a162807911e4004),
  (0x90e0976541057e, 0x5ae03008c82808, 0x64058f162c4c711ec405),
  (0x90e0976541077e, 0x5bf18004, 0x1901478402),
  (0x91e0976541057f, 0x449428805, 0x11d235047b11e8404),
  (0x82e0976541077b, 0xfc620004, 0x640401),
  (0x9160b76541047f, 0x4a944ae20008609, 0x64859112cc803),
  (0x9160b76541067f, 0x48830a04, 0x19312cc8ab22a8804),
  (0x91e0b76541067f, 0x48a02, 0x18d12cc802),
  (0x9160b76541057f, 0x4d121800c428809, 0x65459416245701dc0405),
  (0x90e057654105fe, 0x12a2008005, 0x570401),
  (0x93e057654105f7, 0x7a00a804, 0x0),
  (0x926077654104ff, 0x11229a04, 0x6584de6204403),
  (0x946077654104ff, 0x429803, 0x1971208002),
  (0x90e097654105fe, 0x16802a0005, 0x5d8401),
  (0x9160b7654104ff, 0x4d1c18050807, 0x66459815c4403),
  (0x9059574442076e, 0xa4a80025163901200b, 0x0),
  (0x97e0165442077e, 0x20a0404, 0x0),
  (0x97e0165482077e, 0x20a0404, 0x0),
  (0x90dc570595077e, 0x79210004, 0x5f9801),
  (0x82dc570595067f, 0xa21250405, 0x31c8c571f9c03),
  (0x92dc570595057f, 0x10009258a06, 0x17a2de89031310404),
  (0x90e057059505fe, 0x82848405, 0x0),
  (0x93e057059505f7, 0x4a878080406, 0x0),
  (0x7260770595067f, 0x10849404, 0x18b11ec802),
  (0x926077059504ff, 0x11203e0c629608, 0x60197c6df1803),
  (0x946077059504ff, 0xa11e04ae0207, 0x5fd97b6ded803),
  (0x90dc970595077e, 0x78058404, 0x640801),
  (0x90e097059505fe, 0x82858405, 0x0),
  (0x9160b7059504ff, 0x5060340c448808, 0x19a163c97d2df4804),
  (0x9260570d95067f, 0x1410803, 0x67059b132c803),
  (0x92e0570d95047f, 0x4480088a941ae09, 0x19d132c802),
  (0x92e0570d95067f, 0x429e50805, 0x6784cb2328803),
  (0x9460570d95067f, 0x401, 0x19f146d402),
  (0x94e0570d95047f, 0x4002a942881ac09, 0x46d401),
  (0x94e0570d95067f, 0x11e02, 0x11b5469802),
  (0x9160970d95067f, 0x1210a03, 0x6845a01330803),
  (0x91e0970d95047f, 0x4002494a88b8609, 0x330801),
  (0x91e0970d95067f, 0x48878a04, 0xcc2324802)]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def records9 : Array Raw := #[

  (0x1d565440035f, 0x10228e52607, 0x0),
  (0x21d65440027f, 0x470228e2141a60a, 0x0),
  (0x21d65440037f, 0x11c28009420e1a60a, 0x0),
  (0x19571480037d, 0x10220c19207, 0x0),
  (0x19571880037d, 0x10228818c07, 0x0),
  (0x195734800377, 0x400248830a07, 0x0),
  (0x195738800377, 0x400220628e07, 0x0),
  (0x1d565480035f, 0x400248830a1a409, 0x0),
  (0x21d65480027f, 0x10009a48830a1a40a, 0x0),
  (0x21d65480037f, 0x11220009a28c1a40a, 0x0),
  (0x21975480035f, 0x409220030a1a409, 0x0),
  (0x1454044103fc, 0x18400222a4a6b0a0a, 0x71018405101040310084011000408),
  (0x1954044103fe, 0x42aab0008848609, 0xb102c00a1028009182440908240081020005101400218084020808010),
  (0x1d540441037e, 0x2061000aa2c4b284a60c, 0x3840d103040a1024404080c607),
  (0x1855044103fc, 0xb2ea942284b208070438a0e, 0x151050413684c41268484116844410684040f683c404601060e),
  (0x1495044103de, 0x8284092a14aae3a400c0d, 0x1f107841d107041b10684191060417105840f100180c),
  (0x1895044103fe, 0x10a4a852ab8009a2060c, 0xa4428109c4261094424108c4221084420107041a185c404600580f),
  (0x1c950441037e, 0xbaa51630ea1208010a2420e, 0x2f10b842d10b042b10a84261084418104040a),
  (0x2095044103fe, 0x96189180baa52848a1240e, 0x3210c443010a04221044406),
  (0x1915044103fe, 0x42aab000a84982060b, 0xec43a10e443810dc43610d443410cc410583da0a000c20d),
  (0x1d150441037e, 0x81840022aaa12b3a0b, 0x10444010fc43e10f443c10d84106841609),
  (0x2115044103fe, 0x10a8aab012a84881820c, 0x44110c44210e04341049a06),
  (0x2135044102fe, 0x20610008aaaca120a, 0x471118445104da04),
  (0x1955044103de, 0xa102c92a0e014aae7ac0d, 0x4c112c44a1124448111444210f043510c042a108c41c10504090009810),
  (0x1d950441037e, 0x2ea9480ea12c8203410ab1c0f, 0x14044f113844d1130446110c43610c4426106440c180d80d),
  (0x2195044102fe, 0x2cbaa52020e4b208010aa1e0f, 0x561154454114c452114443d10ac41a186840a001580c),
  (0x2195044103fe, 0x44a82b208050880e19e0d, 0x1684591160457111043e10e043210b0428109441b101980d),
  (0x21b5044102fe, 0xa1000b24a838852abac0d, 0x16c44010b841e101d805),
  (0x2035244102fe, 0x20a100094a92b8e90c0c, 0x5e117445c10cda04),
  (0x2055244103fd, 0x8484baa5002a52263020d, 0x188461118045f10e5a201858407),
  (0x1895244103fb, 0x4292baa0026a41880b, 0x190664118c45f197c45c19704262898817185c403780dc0d),
  (0x1955244103df, 0x10a212baa5029007860c, 0x1a846911a04671198465118c460117443568a882318684097009c0f),
  (0x1d952441037f, 0x90608880a014aae49c1340e, 0x7011bc46e11b446c11ac4671184426206440c7011c0c),
  (0x2195244102ff, 0x42884aea9400269e1a40d, 0x7611d447411cc47211c446c10ac81c187040a7015c0c),
  (0x2195244103ff, 0x1211490a21e68209, 0x7911e047711b446210e5a2c209061d1019c0a),
  (0x21b5244102ff, 0x42884aea940029060b, 0x1ec47a10b881f101dc05),
  (0x21d52441027f, 0x2f18e3082ab2104820045441c211, 0x7e11f447c11b046810d9a262898608),
  (0x21d52441037f, 0x308bc42c91a4014a8448708210, 0x1fc47811b44691190437689c607),
  (0x19572441037f, 0x422a512002296b867c20d, 0x218485121048312086821204480220046c11a066810f5c3c68f182b20ac42a28a882a18a8415),
  (0x21572441037f, 0x6344bc65c848052a2050820f, 0x220487120c48210fda2d28b4607),
  (0x21772441027f, 0x1ae38c20a52a4120801420e, 0x891105e2f28bc604),
  (0x2016544103fe, 0x10a4a8c8201e50880e0c, 0x23848d123048b1228481620046669998651994448692180b002180f),
  (0x2096544103ff, 0x11250a21e01a0a40a, 0x2484911240690123c48d6230484120084b692d849192440b7021c0f),
  (0x20b6544102ff, 0x4288baa5120027860b, 0x254494124c44a1928405),
  (0x1d565441035f, 0xbaa50e2a6428480c8211f12c10, 0x97625c4966258490624046861a0467699c64c6930609602440e),
  (0x21d65441027f, 0x1aea9420e2904b208012cd4410, 0x9d127049b626c49a62684996264498626046c51b040a602840e),
  (0x21d65441037f, 0x4d3209200b11421e18e0d, 0xa1128049f627c49e62784916244484521046a69a986a19a840b602c410),
  (0x20975441037f, 0x6344247226a1252ab8508210, 0x28c4a2125846e19ac64f6934607),
  (0x20b75441027f, 0x18e30910a52a41208012e0e, 0xa4125c4506938604),
  (0x21975441037f, 0x32092a2650910e1801340d, 0xa912a04a7629c4a662984a562944a2628846e69b860d603440e),
  (0x21b75441027f, 0x2ea9420f10a412c820041ac0f, 0xaa62a840e6038404),
  (0x1855048103fe, 0x94aae012a162881060c, 0xb012bc4ae12b44ac12ac4261040408),
  (0x2055048103fe, 0x96184008baa5284c42a60e, 0x2d44b412cc4b212c44af12ac407),
  (0x1495048103da, 0x304092a2ea969300080c, 0x2e48b912e08b812dc8b712d84b122c44ac106040b),
  (0x1895048103fa, 0x30403009a4a8baa5880c, 0x2f04bb2aec4ba12dc8b71ac8ab21084409),
  (0x1955048103de, 0x8304092a14aae59e0300d, 0xbf12f84bd12e84b722cc4ad10a8408),
  (0x1d950481037e, 0x16bbea94a1208010c808c1a0f, 0xc113004bf12d84b41098406),
  (0x2195048102fe, 0x5aea94a120b000432021e0e, 0xc4130c4c212dc6b710ac406),
  (0x2195048103fe, 0x18c102c00ba02162a849e0e, 0xc713184c512ecab812d44af10b0408),
  (0x21b5048102fe, 0x20c100c024a852ab960c, 0xb910b8402),
  (0x1855148103fd, 0x4708a940024ae1962a60d, 0x3246c9132043668d9805),
  (0x1955148103df, 0x4212a9408ab9601e1a60d, 0xcd13304cb13288ca13204ad2ab466810f180a),
  (0x1d951481037f, 0x161a022e28268052a4849be0f, 0xd213444d0133c4ce132c46c10d9808),
  (0x2195148102ff, 0x19e5ae282014a9221c1260e, 0x3544d4134c46c10f5c05),
  (0x2195148103ff, 0x29e70299606, 0xd713584cf10f9804),
  (0x21b5148102ff, 0x1084aa50008ab961a60c, 0xd81101c02),
  (0x21d51481037f, 0x63091c42ae04852a4849c209611, 0x3644d6133c4cc13244ae2ab8607),
  (0x2016548103fe, 0x4a803009678882e10c0c, 0xdc136c4da13286ca12f8abe2200408),
  (0x2056548103ff, 0x1229e50070299609, 0xdf13784dd1b744da23684bd2af48bd1af4484120440c),
  (0x2076548102ff, 0x108a9400249e18ab960c, 0x3844e02380403),
  (0x1d565481035f, 0xbaa524308590c0048211f1a810, 0x38c4e213744cb1afcabf19a0407),
  (0x21d65481027f, 0xbaa50a308590482c00106fc610, 0xe713984e513908e411b0406),
  (0x21d65481037f, 0xf8cb8819e2920960301460e, 0x3a44e823a04de13346cd1210407),
  (0x20575481037f, 0x418cbc42c91a4a1252a01708211, 0x3ac4ea13884d01b386c02b00607),
  (0x20775481027f, 0xbc638c20a52a4120801060e, 0xec138c4c12b04604),
  (0x21975481037f, 0x10632e2a84c6916080c3e0e, 0x3bc4ee23b84ed23b44ea1340607),
  (0x21b75481027f, 0x2ea9428c2164120b00051860f, 0x3c0401),
  (0x1c56054103fe, 0x106380808502cc42a84a60e, 0xf713d84f513d04f313c84f113258b4119085f210c00c),
  (0x1c760541037e, 0xb20baa50ea12c8200429c0e, 0xfd13f04fb13e84f913e04f60918008),
  (0x1496054103de, 0xc245aea94a120843202000e, 0x103140850114004ff13f84f81bc86f112d8419105c80c),
  (0x1c96054103fe, 0x418cc000ae2171a02a84a40f, 0x10414006f91bcc46420c4406),
  (0x1cb60541037e, 0x5aea94a120b000432021a0e, 0x10614144f41970804),
  (0x19560541039e, 0x4a8404c825a07aec000c, 0x4245090420508041c5070418706141830604107041410304040450103f46fd13f42fd03dc6f713dc2f703218bf1afc4bf0afc063918c84c193044c0930023),
  (0x19560541039f, 0x449640009e07, 0x0),
  (0x2111094102ee, 0x2800844a83944160a, 0x10b1428402),
  (0x1951094103de, 0x284092a0e01442659e0c, 0x10c1428402),
  (0x1d910941037e, 0x2840024a83888144160c, 0x10d142c402),
  (0x2191094102fe, 0x2840024a83944265a00c, 0x430401),
  (0x1952094103de, 0x8304092a1058091e0b, 0x438401),
  (0x1d920941037e, 0x2203040024a84160a, 0x43c401),
  (0x2192094102fe, 0x880c100092a105a40b, 0x438401),
  (0x2016154103fe, 0xb2012a0a81473410e0c, 0x1161454514144c512144451012b84ab698563700d1e0c),
  (0x1496154103df, 0x112a14aae08090a2060c, 0x460918145c917144df136c4491112b0419206440f203c40d),
  (0x1c96154103ff, 0x11c9464a82945880a, 0x11b14685191451a6d20dde311044408),
  (0x2096154103ff, 0x12a0470a69500809, 0x47851d147051214448cf1ab84436848409),
  (0x1cb61541037f, 0x11c012a2a5022ae2060c, 0x488521148051f10cde05),
  (0x20b6154102ff, 0x4712a14aae08a2060c, 0x49852514905231455a46684c407),
  (0x19561541039f, 0x2ea9478038a402ca848472c0f, 0x49db271491b241481b201471b1c1465b191459b16132d4cb1ab5aad119d6672131a4c10d5e350050417),
  (0x21d6154102ff, 0x18e21511c2b4102ca84800e, 0x4b852d14b052b14a852914a051d6c68517133d8af11b483978e000f),
  (0x21d6154103ff, 0x12a023b474408, 0x13014bdb2f1054404),
  (0x21e61541037f, 0x11c012a3208a5083860c, 0x4d453414cc53214c451e146db186ac1a3b78e800b),
  (0x1497154103df, 0x62442a49aea940284840c60f, 0x13714d8517144dafe23c44b11058808),
  (0x1897154103ff, 0x4992a0b11420009a0b, 0x13c14ec53a14e453814dc4fe23c84b412c846d21848272880a0e),
  (0x1c971541037f, 0x62442c6926a1252ab8458210, 0x13d14ec53814685146bcc406),
  (0x1d171541037f, 0x1884a910a8a612caca0020e, 0x13e1475b1d5c49b125bd4406),
  (0x1957154103df, 0x38854429e982c80a121060e, 0x4fc53e14f453914dc51c5c59af713318b311a4860210800d),
  (0x1d971541037f, 0xc824a81267862c42200d, 0x508541150053b14e853614756d662d44a561e0862211000d),
  (0x18971d41037f, 0x44a8baa50268a2060c, 0x1471518545151054313e0406),
  (0x20971d41027f, 0xb8e90c20a52a4120801281c610, 0x148151854313e8404),
  (0x21171d41027f, 0x1012822062aab280a, 0x14914957235bec404),
  (0x19571d41035f, 0x1ebaa50e290a12032084b1c0f, 0x14b1528549152054414916fd1114008),
  (0x21971d41027f, 0x6baa50838a412c82004b280f, 0x151154054f153854d15305461514525591c00a),
  (0x1d952541035f, 0xa9478c200c10b96482124a2010, 0x154154c55214dc90122dc41c2068408),
  (0x1d95254103df, 0xc20aa127a4080c2e5841a00f, 0x55c5561554536145c50222e041d206c409),
  (0x1db52541035f, 0x11aa50c210b964b000212891a10, 0x2e441f2078403),
  (0x2016254103fe, 0x12a16682faec002203040d, 0x15b156855915605382c008271088a08),
  (0x19562541039f, 0x2a51e308080c10b92584a1a0f, 0x15c1564b591510b4414e4b3912fcabf12e8467219c623288c40e),
  (0x2156254103df, 0x45aec0009a4a821e3240d, 0x15d156cb5a14e8b021aec4252890408),
  (0x21d6254102ff, 0x3e18c20aa12102b96c0119a0f, 0x584560157c55e14ec46d20a0407),
  (0x21d6254103ff, 0x5826bf1a807, 0x588b62140c9031af0405),
  (0x21e62541037f, 0x4030582692a0ab883060d, 0x1661594564158c53c28a4a06),
  (0x1957254103df, 0x82a849f1a40aec005843060f, 0x1592cf4519141046920c0406),
  (0x1d972541037f, 0xa082867c68240845aec000e, 0x5a05671568b1a13b487820c8407),
  (0x20572d41027f, 0xeb8c20a52a4284820041c40f, 0x169148451f1414404),
  (0x19572d41035f, 0x2ea94308416a12c0008479a0f, 0x5a856914805061174805),
  (0x21972d41027f, 0x2ea9428c2105920b00041a80f, 0x5b456c15ac5211178805),
  (0x2056554103df, 0x11c4a8c8201e18a2260c, 0x17315c857115c056f15b856a157054b049d70713744cd53298bd124146a219884b0120414),
  (0x2096554103df, 0xc20aa1219e080c2e11691a0f, 0x17615d457415c054a149c50812f849011a8865212440c),
  (0x20b6554102df, 0xa9478c200c10b925821280e, 0x4fc5091128403),
  (0x20576541037f, 0x11038080850a19e0b24b4a4410, 0x60458015fc57e15f457c15ec57a15e457815dc5521d484d3630849861d08732150013),
  (0x20776541027f, 0x1aea9420e2904b208012c0e, 0x1871618585161058316084d46261875215400a),
  (0x20776541037f, 0x44a8c8278628050880e0d, 0x63058b1628589162058005e45531d4c4d5530c49861d8856014440f),
  (0x20976541037f, 0x10c0a118829219e030b96fa810, 0x64058f163858d162057a13908742148409),
  (0x20b76541027f, 0xbaa50a308416482c001060e, 0x1931648591139087521c4806),
  (0x20b76541037f, 0x30280829219e030b961280e, 0x650590162857b155075413908c411d8872214c40b),
  (0x2057654103ff, 0x792a1083470310a0a, 0x65859514a8403),
  (0x2077654102ff, 0x44a8c8278629420e0c, 0x198165c567155454204a84d753144a561e485a015c40c),
  (0x2077654103ff, 0x4792a2008a07, 0x50052a1160403),
  (0x2097654103ff, 0x1e5a023e09aa4609, 0x1991584402),
  (0x20b7654102ff, 0x3082a8486782b961300200e, 0x668561155854113b48c611e48772164409),
  (0x20b7654103ff, 0x11e5808080a808, 0x5a05611574b57131c405),
  (0x20576d41027f, 0xbaa50838a4284b20801441ac10, 0xd861ec87a216c004),
  (0x20976d41027f, 0xbaa50a308416482c00146a0610, 0x1ec801),
  (0x19574442036f, 0x40022923885105860b, 0x19b142c50a1c28404),
  (0x19574842036f, 0x10008818a06, 0x0),
  (0x2016544203fe, 0xa4a810009422058e41e0d, 0x19c166c402),
  (0x1d565442035f, 0x102010292a0e5160a, 0x430601),
  (0x21d65442027f, 0x400240a4a83888145860d, 0x0),
  (0x21d65442037f, 0x440008a4a85088163860d, 0x0),
  (0x2016548203fe, 0x12a0008422058c41e0b, 0x674401),
  (0x1d565482035f, 0x408020c4a841609, 0x438601),
  (0x21d65482027f, 0x10008880c292a105860c, 0x0),
  (0x21d65482037f, 0x100092a0a22058c1900c, 0x0),
  (0x1c570595037f, 0x4712a3209e18a2200260d, 0x6819a0167d99f167999e15dd97715c177055c0b7023798de13698da12454912235c8d0228415),
  (0x2057059503ff, 0x4a8790020d0510a0a, 0x6885a11279803),
  (0x2077059502ff, 0x44a8c8200a78650880e0d, 0x6945a4168c5a055dd9762dd89715dc556e6db98df6279892223800f),
  (0x2077059503ff, 0x4a811e02008a08, 0x67996f6dbd89e622c405),
  (0x1c970595037f, 0xa2020a19e682030b961240e, 0x6989a6168c9a3163498d15c9b72636c491224448c223040d),
  (0x2097059503ff, 0x16780808fa918409, 0x1a713a0802),
  (0x20b7059502ff, 0xb8c80819e292080c161280e, 0x1a8167c58d25d0b7425cdb7363a0892223c80a),
  (0x20b7059503ff, 0x5847808080a808, 0x6989752dd48e82370405),
  (0x2157099502df, 0x408049641e07, 0x0),
  (0x21d70995027f, 0x1000925907862880a, 0x0),
  (0x20570d95027f, 0x2ea9421e38a412c820041ac0f, 0x1ae16b45ac16ac5aa16a44e16381895225080a),
  (0x20970d95027f, 0x2ea9428c2105920b00047860f, 0x6c45b016bc495224c805)]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def records10 : Array Raw := #[

  (0x6544001ff, 0x400228e21419e09, 0x210044001800404),
  (0x75440017f, 0x10228e2141a609, 0x11000402),
  (0x71480017d, 0x10008831206, 0xc401),
  (0x71880017d, 0x10008a20c06, 0x10401),
  (0x734800177, 0x10009220c06, 0x14401),
  (0x738800177, 0x10008818e06, 0x18401),
  (0x6548001ff, 0x400248830a19e09, 0x91020407181c40620184052014404100c40a),
  (0x75480015f, 0x409220032407, 0x28401),
  (0x75480017f, 0x400248830a1a409, 0x8101c402),
  (0x4044101fe, 0x8184002a8ab1209, 0x3460d103420d003040b182c40b082c009),
  (0x5044101fe, 0xa1000b24a838852abac0d, 0x1b10684191060417105841510504131048411104040f103840d002d810),
  (0x5244101ff, 0x3a4314a90b9208020a1060e, 0x2510904231088421108041f107841d10704136844810183c40d702dc10),
  (0x72441017f, 0x2e58e30a52a4120802041c20f, 0xa0628109c6271098424189041468518112844811184440d),
  (0x6544101ff, 0x1eb883aa510c820122841ac0f, 0x2e10b442c18b042b60ac42a60a842960a44266098421608441f687d81f187c4196064417685d817185c40c703041a),
  (0x75441017f, 0x2e50838a990a12c82004ac41ac11, 0x3210c443060c042f60bc42d10b042460904206880618686060d6034410),
  (0x5048101fe, 0x20c100c024a852ab960c, 0x3b10e843910e043710d843510d0433104440a),
  (0x5148101ff, 0x163ae30a52a4120802041a60f, 0x108441110043f10f843d10f043328cc624105180b),
  (0x6548101ff, 0x2ea9428c590482c002047860f, 0x48111c44619184451110443210c43f10f463d10e483910dca3720dc6371098412),
  (0x75481017f, 0x2e50a90c2164120b0004ac6a0611, 0x4c112c44a1124447111843e18e0a38189040a),
  (0x6054101fe, 0x12a10100c02c9682e0b, 0x521144651114425101406501140250013c64f113c24f013864e113824e013464d113424d00f183818e043808e001e907881818604180860020),
  (0x6054101ff, 0x40024a85902888060b, 0x14c401),
  (0x1094101fe, 0x2840024a83885109960c, 0x5711584551150404),
  (0x2094101fe, 0x20c100092a105a40a, 0x1684591160403),
  (0x6094101fe, 0x1240400259e07, 0x0),
  (0x6154101ff, 0xbaa50838a4284b208011c1ac10, 0x6469904631189a621184460698045f697c45e697845d697445c697045b696c43e60f863368cc42d10816202061a18104de13003841e),
  (0x7154101ff, 0x2e21438a990a12c82004ac41ac11, 0x1a846911a04671198465118845e596da4d1109834109481d205400f),
  (0x71d41017f, 0x2ea9420e290a12c820041ac0f, 0x6f11b846d11b046b118164e1058008),
  (0x5254101df, 0xa9490c200c10b925821280e, 0x7221c847121c447021c0465219445c113c84f10d440f203c40e),
  (0x6254101ff, 0xa9428c210b96482c0012868610, 0x7829e047711d8a7611d4a7511d047329cc47021c066b29ac466299844f213c64710e0a3810d84202080610284041a),
  (0x7254101ff, 0x142a4308590b920b0004aa918611, 0x1e847911d8473299c45d11404252048409),
  (0x72d41017f, 0x2ea9428c2105920b0004a060f, 0x7d11f047b117c4511070806),
  (0x6554101df, 0x40b2792a16400c2e0b, 0x20048001fc47f01f847e01f047c01e447901d047401c247021b846e01a4469018446101604580154455014c452111844600f583710dc02c10b001f907c817105c025),
  (0x76541017f, 0x2e20a19e4164b20b00048280f, 0x21848602144850210484020c4830208482020448101c067011c027001644590158456011c44700fd83910e402d10b40219084819106401f),
  (0x7654101ff, 0x2e20a7905a84b20b00041a00f, 0x23048c022c48b022848a02244890220488021c48701e847a01d847601d667529c447101a846a0188462010183a10e8022908881a106801f),
  (0x76d41017f, 0x40300b24a8590288b860d, 0x23848e023448d01c8472010583b10ec023908c81b106c00d),
  (0x74442016f, 0x400229239059409, 0x23c4541950403),
  (0x74842016f, 0x10008818a06, 0x240401),
  (0x6544201ff, 0x10009029448e21619e0c, 0x94124c4921a48491124048f1158455195440a),
  (0x75442017f, 0x100090292a0e2145860c, 0x24c492115c603),
  (0x6548201ff, 0x400220c29241619e0b, 0x98125c4961a5849511644581960408),
  (0x75482017f, 0x400220c292a105860b, 0x25c4961168603),
  (0x76542017f, 0x400249640a20609, 0x0),
  (0x7059501ff, 0x2e20a4164867b20b00048280f, 0x2804a0027c49f027849e027449d027049c026c49b026849a02644990254495024449101fe67f91fca7f21f9a7e61f967e51204480111443110c02e10b802a90a882910a4027),
  (0x7099501ff, 0x1000925907862880a, 0x2884a11a84403),
  (0x70d95017f, 0x40300b249641e18a22e0d, 0xa412900a3128c0a212026809200a80211582b90ac80c)]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def records11 : Array Raw := #[

  (0x4000ff, 0x10008a39420608, 0x46011000403),
  (0x8000ff, 0x10009220c28608, 0x20608101c607101840520144042010403100840b),
  (0x4100ff, 0x1ae20ea9443208048a12c0e, 0x3860e103440c603040b682d80b182c40a682980a1828409702440f),
  (0x8100ff, 0xbaa50a3164120b00081060e, 0x1218484111040610103ca0f203c60f103040a),
  (0x14100ff, 0x40300b24a8590288b860d, 0x221084420107c41e107801d107401c107001b106c01a1068019106401810600171058416005441500504131048412004180f103c00e103800b902c80a1028024),
  (0x4200ff, 0x400240a5123962060b, 0x986261094424108c4151854407),
  (0x8200ff, 0x10008831240a5860a, 0xa0628109c4161858405),
  (0x14200ff, 0x400249640a20609, 0x29105c602),
  (0x19500ff, 0x8478628807, 0x2c80b182c50b0c2c10ae02b60ad42b30ac42a90a9c2a40a882a109e427809dc27609d427409cc27209c42700964258095c2560954254094c25209442500824207081020208041f887e01f687d81f587d41f387cc1f187c411704581140444110035c0d4034c0d1034006701980640184060001c004000c001000046)]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def records12 : Array Raw := #[

  (0x7f, 0x202, 0x20407981e407781dc07481d007281c807181c406901a0067019806501900630188061018005901600570158055015005301480510140048812004681180458114043810c041810403700d803400c4030009c024008c021008001700580140044010001c004000c00100003d)]

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def layer : Nat → Array Raw
  | 6 => records6
  | 7 => records7
  | 8 => records8
  | 9 => records9
  | 10 => records10
  | 11 => records11
  | 12 => records12
  | _ => #[]

end PEqualNP.Outside.L_meta_10460.Big

namespace PEqualNP.Outside.L_meta_10460.Big
open PEqualNP.Outside.L_meta_10460.Evidence PEqualNP.Outside.L_meta_10460.Signed PEqualNP.Outside.L_meta_10460.Shapes

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def unpackWords (width : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | t+1, z => (z &&& (2^width-1)) :: unpackWords width t (z >>> width)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def unpackSeq (width z : Nat) : List Nat := unpackWords width (z &&& 511) (z >>> 9)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def path (bank : List (BitVec 128)) : Nat → Nat → List (BitVec 128) × Hist 128
  | 0, _ => (bank,[])
  | t+1, bits =>
    let op := bits &&& 3
    let a := bank.getD ((bits >>> 2) &&& 15) 0
    let b := bank.getD ((bits >>> 6) &&& 15) 0
    let w := (ops 128 a b).getD op 0
    let r := path (bank ++ [w]) t (bits >>> 10)
    (r.1, (w,a,b) :: r.2)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def record (k i : Nat) : Raw := (layer k)[i]?.getD (0,0,0)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def inputs (t : Nat) (ws : List (BitVec 128)) := ws.zipIdx.filterMap fun (w,i) =>
  if t.testBit i then some w else none
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def state (k i : Nat) : List (BitVec 128) × Hist 128 :=
  let t := (record k i).1
  let build := path rows7 (12-k) (t >>> 16)
  (inputs (t &&& 65535) build.1, build.2)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def req (k i : Nat) := unpackSeq 6 (record k i).2.1
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def links (k i : Nat) := unpackSeq 14 (record k i).2.2
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def coords (code : Nat) : Nat × Nat := (code &&& 31, code >>> 5)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def targets (k : Nat) (links : List Nat) := links.map fun code =>
  ((state k (coords code).2).1).map (actB 128 (pow7[(coords code).1]?.getD []))
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def zeros7 : List Nat := [0,1,2,3,4,6,8,12,16,17,24,32,64]
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def audit (k i : Nat) : Bool :=
  let ws := (state k i).1
  let hist := (state k i).2
  let refs := links k i
  let cuts := req k i
  decide ws.Nodup && refs.all (fun c => decide ((coords c).1 < 20) && decide ((coords c).2 < (layer (k-1)).size)) &&
    nodeCheck goal7 zeros7 (k-1) ws hist (fun h ys => cuts.any (fun c => band c (k-1) h ys)) (targets (k-1) refs)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem mirror_no {k : Nat} {ws : List (BitVec 128)} (g : Nat) (hg : g < 20)
    (h : ¬live (basicOps 128) goal7 k ws.toFinset) :
    ¬ live (basicOps 128) goal7 k (ws.map (actB 128 (pow7[g]?.getD []))).toFinset := by
  intro hlive
  have hinv := (actB_spec sym7valid g hg).1
  have hg' := (actB_spec sym7valid (inv7[g]?.getD 0) hinv).2.2.2.1
  have hi := live_map (actB 128 (pow7[inv7[g]?.getD 0]?.getD [])) (actB_inj sym7valid _ hinv)
    hg' (actB_ops sym7valid _ hinv) hlive
  have hset : ((ws.map (actB 128 (pow7[g]?.getD []))).toFinset.image
      (actB 128 (pow7[inv7[g]?.getD 0]?.getD []))) = ws.toFinset := by
    ext u
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_,⟨v,hv,rfl⟩,rfl⟩
      rwa [actB_inv_left sym7valid g hg v]
    · intro hu
      exact ⟨_, ⟨u,hu,rfl⟩, actB_inv_left sym7valid g hg u⟩
  rw [hset] at hi
  exact h hi

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem audited_no {k i} (chk : audit (k+1) i = true)
    (pr : ∀ j < (layer k).size, ¬live (basicOps 128) goal7 k (state k j).1.toFinset) :
    ¬live (basicOps 128) goal7 (k+1) (state (k+1) i).1.toFinset := by
  simp only [audit, Nat.add_sub_cancel, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at chk
  apply node_no chk.1.1 _ _ chk.2
  · intro h ys hn hc
    obtain ⟨c,_,ht⟩ := List.any_eq_true.1 hc
    exact band_no c k h ys hn ht
  · intro ws hw
    obtain ⟨c,cm,rfl⟩ := List.mem_map.1 hw
    obtain ⟨hg,hi⟩ := chk.1.2 c cm
    exact mirror_no (coords c).1 hg (pr (coords c).2 hi)

end PEqualNP.Outside.L_meta_10460.Big

namespace PEqualNP.Outside.L_meta_10460.Finish
open PEqualNP.Outside.L_meta_10460.Evidence PEqualNP.CircuitLowerBounds

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem actualBuild (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    ∃ t, (t = goal7 ∨ t = ~~~goal7) ∧ build basicOps7 t (binaryCost gs) rows7.toFinset := by
  apply compile gs o hg rows7 rows7.toFinset
  · exact fun u hu => .inr (.inr ⟨u,List.mem_toFinset.2 hu,.inl rfl⟩)
  · intro k
    let x (i : Fin 7) : Bool := (rows7.getD i.val 0)[k.val]
    have same : List.ofFn x = rows7.map (fun w => w[k.val]) := by
      apply List.ext_getElem
      · simp [rows7]
      · intro i hi hj
        have hlt : i < rows7.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (rows7.map (fun w => w[k.val])) = goal7[k.val]
    rw [← same, he]
    exact sample7_ok k

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def idRows := List.range 128
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem rootsProject : rows7.all (fun w => rows7.contains (projS 128 idRows w)) = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem thirteenBinary (no : ¬build (basicOps 128) goal7 12 rows7.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (spec : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = gw x) : 12 < binaryCost gs := by
  by_contra! h
  obtain ⟨t,ht,hb⟩ := actualBuild gs o hg (fun x => (spec x).trans (bridge x))
  obtain ⟨s,hs,hl⟩ := compress (build_mono_k h hb)
  have hpr : projS 128 idRows t = goal7 := by
    rcases ht with rfl | rfl <;> decide +kernel
  have hc := live_restrict (by decide : 0 < 128) idRows (by decide) (by simp [idRows])
    (fun _ _ _ hz => List.mem_toFinset.1 hz) hpr (by decide : goal7 ≠ 0) hl
  apply no (build_mono_k (Nat.sub_le _ _) (build_mono_av _ hc))
  intro w hw
  simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hw
  obtain ⟨_,v,hv,rfl⟩ := hw
  exact List.mem_toFinset.2 (List.contains_iff_mem.1 (List.all_eq_true.1 rootsProject v (List.mem_toFinset.1 (hs hv))))

end PEqualNP.Outside.L_meta_10460.Finish

namespace PEqualNP.Outside.L_meta_10460.Completion
open PEqualNP.Outside.L_meta_10460.Evidence PEqualNP.Outside.L_meta_10460.Signed PEqualNP.Outside.L_meta_10460.Big

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
def block (k off : Nat) : Nat → Bool
  | 0 => true
  | n+1 => audit k (off+n) && block k off n

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem joinBlock {k off a b} (ha : block k off a = true) (hb : block k (off+a) b = true) :
    block k off (a+b) = true := by
  induction b with
  | zero => simpa using ha
  | succ b ih =>
    simp only [block, Bool.and_eq_true] at hb
    exact Bool.and_eq_true_iff.2 ⟨by simpa [Nat.add_assoc] using hb.1, ih hb.2⟩

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem atBlock {k off n} (hb : block k off n = true) (i : Nat) (lo : off ≤ i) (hi : i < off+n) : audit k i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block, Bool.and_eq_true] at hb
    by_cases eq : i = off+n
    · exact eq ▸ hb.1
    · exact ih hb.2 (by omega)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem signedBound (checked : ∀ s i, i < (layer s).size → audit s i = true) :
    ¬build (basicOps 128) goal7 12 rows7.toFinset := by
  have hlev : ∀ s i, i < (layer s).size → ¬live (basicOps 128) goal7 s (state s i).1.toFinset := by
    intro s
    induction s with
    | zero =>
      intro i hi
      change i < 0 at hi
      omega
    | succ s ih =>
      intro i hi
      exact audited_no (checked _ _ hi) ih
  apply root_no [1,2,4,8,16,32,64] (by decide +kernel)
  have h := hlev 12 0 (by decide)
  have hroot : (state 12 0).1 = rows7 := by decide +kernel
  rwa [hroot] at h

end PEqualNP.Outside.L_meta_10460.Completion

namespace PEqualNP.Outside.L_meta_10460.Finish
open PEqualNP.Outside.L_meta_10460.Evidence PEqualNP.Outside.L_meta_10460.Signed PEqualNP.Outside.L_meta_10460.Big PEqualNP.Outside.L_meta_10460.Completion PEqualNP.CircuitLowerBounds

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem fromSigned (no : ¬build (basicOps 128) goal7 12 rows7.toFinset) : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o legal _ spec
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · have lo := thirteenBinary no gs o legal spec
    obtain ⟨g, hm, hop⟩ := hn
    have lt : binaryCost gs < gs.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, hm, by simp [isBinary, hop]⟩
    refine ⟨upperW, 20, legalUpper, ?_, correctUpper⟩
    change 14 ≤ gs.length
    omega
  · refine ⟨gs, o, ?_, Nat.le_refl _, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases hop with ha | ho | hnot
    · exact Or.inl ha
    · exact Or.inr ho
    · exact False.elim (hn ⟨g, hg, hnot⟩)

end PEqualNP.Outside.L_meta_10460.Finish

namespace PEqualNP.Outside.L_meta_10460.Completion
open PEqualNP.Outside.L_meta_10460.Big

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked6_0 : block 6 0 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked6_8 : block 6 8 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked6_16 : block 6 16 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked6_24 : block 6 24 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked6_32 : block 6 32 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked6_40 : block 6 40 3 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem checked6 : block 6 0 43 = true := (joinBlock (joinBlock checked6_0 (joinBlock checked6_8 checked6_16)) (joinBlock checked6_24 (joinBlock checked6_32 checked6_40)))

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_0 : block 7 0 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_8 : block 7 8 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_16 : block 7 16 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_24 : block 7 24 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_32 : block 7 32 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_40 : block 7 40 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_48 : block 7 48 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_56 : block 7 56 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_64 : block 7 64 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_72 : block 7 72 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_80 : block 7 80 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_88 : block 7 88 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_96 : block 7 96 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_104 : block 7 104 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_112 : block 7 112 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_120 : block 7 120 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_128 : block 7 128 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_136 : block 7 136 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_144 : block 7 144 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_152 : block 7 152 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_160 : block 7 160 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_168 : block 7 168 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_176 : block 7 176 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_184 : block 7 184 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_192 : block 7 192 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_200 : block 7 200 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_208 : block 7 208 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_216 : block 7 216 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_224 : block 7 224 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_232 : block 7 232 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_240 : block 7 240 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_248 : block 7 248 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_256 : block 7 256 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_264 : block 7 264 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_272 : block 7 272 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_280 : block 7 280 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_288 : block 7 288 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_296 : block 7 296 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_304 : block 7 304 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_312 : block 7 312 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_320 : block 7 320 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_328 : block 7 328 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_336 : block 7 336 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_344 : block 7 344 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_352 : block 7 352 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_360 : block 7 360 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_368 : block 7 368 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_376 : block 7 376 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_384 : block 7 384 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_392 : block 7 392 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_400 : block 7 400 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_408 : block 7 408 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked7_416 : block 7 416 2 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem checked7 : block 7 0 418 = true := (joinBlock (joinBlock (joinBlock (joinBlock (joinBlock checked7_0 (joinBlock checked7_8 checked7_16)) (joinBlock checked7_24 (joinBlock checked7_32 checked7_40))) (joinBlock (joinBlock checked7_48 (joinBlock checked7_56 checked7_64)) (joinBlock (joinBlock checked7_72 checked7_80) (joinBlock checked7_88 checked7_96)))) (joinBlock (joinBlock (joinBlock checked7_104 (joinBlock checked7_112 checked7_120)) (joinBlock checked7_128 (joinBlock checked7_136 checked7_144))) (joinBlock (joinBlock checked7_152 (joinBlock checked7_160 checked7_168)) (joinBlock (joinBlock checked7_176 checked7_184) (joinBlock checked7_192 checked7_200))))) (joinBlock (joinBlock (joinBlock (joinBlock checked7_208 (joinBlock checked7_216 checked7_224)) (joinBlock checked7_232 (joinBlock checked7_240 checked7_248))) (joinBlock (joinBlock checked7_256 (joinBlock checked7_264 checked7_272)) (joinBlock (joinBlock checked7_280 checked7_288) (joinBlock checked7_296 checked7_304)))) (joinBlock (joinBlock (joinBlock checked7_312 (joinBlock checked7_320 checked7_328)) (joinBlock (joinBlock checked7_336 checked7_344) (joinBlock checked7_352 checked7_360))) (joinBlock (joinBlock checked7_368 (joinBlock checked7_376 checked7_384)) (joinBlock (joinBlock checked7_392 checked7_400) (joinBlock checked7_408 checked7_416))))))

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_0 : block 8 0 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_8 : block 8 8 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_16 : block 8 16 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_24 : block 8 24 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_32 : block 8 32 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_40 : block 8 40 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_48 : block 8 48 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_56 : block 8 56 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_64 : block 8 64 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_72 : block 8 72 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_80 : block 8 80 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_88 : block 8 88 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_96 : block 8 96 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_104 : block 8 104 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_112 : block 8 112 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_120 : block 8 120 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_128 : block 8 128 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_136 : block 8 136 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_144 : block 8 144 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_152 : block 8 152 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_160 : block 8 160 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_168 : block 8 168 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_176 : block 8 176 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_184 : block 8 184 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_192 : block 8 192 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_200 : block 8 200 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_208 : block 8 208 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_216 : block 8 216 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_224 : block 8 224 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_232 : block 8 232 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_240 : block 8 240 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_248 : block 8 248 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_256 : block 8 256 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_264 : block 8 264 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_272 : block 8 272 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_280 : block 8 280 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_288 : block 8 288 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_296 : block 8 296 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_304 : block 8 304 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_312 : block 8 312 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_320 : block 8 320 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_328 : block 8 328 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_336 : block 8 336 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_344 : block 8 344 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_352 : block 8 352 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_360 : block 8 360 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_368 : block 8 368 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_376 : block 8 376 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_384 : block 8 384 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_392 : block 8 392 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_400 : block 8 400 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_408 : block 8 408 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_416 : block 8 416 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_424 : block 8 424 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked8_432 : block 8 432 2 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem checked8 : block 8 0 434 = true := (joinBlock (joinBlock (joinBlock (joinBlock (joinBlock checked8_0 (joinBlock checked8_8 checked8_16)) (joinBlock checked8_24 (joinBlock checked8_32 checked8_40))) (joinBlock (joinBlock checked8_48 (joinBlock checked8_56 checked8_64)) (joinBlock (joinBlock checked8_72 checked8_80) (joinBlock checked8_88 checked8_96)))) (joinBlock (joinBlock (joinBlock checked8_104 (joinBlock checked8_112 checked8_120)) (joinBlock (joinBlock checked8_128 checked8_136) (joinBlock checked8_144 checked8_152))) (joinBlock (joinBlock checked8_160 (joinBlock checked8_168 checked8_176)) (joinBlock (joinBlock checked8_184 checked8_192) (joinBlock checked8_200 checked8_208))))) (joinBlock (joinBlock (joinBlock (joinBlock checked8_216 (joinBlock checked8_224 checked8_232)) (joinBlock (joinBlock checked8_240 checked8_248) (joinBlock checked8_256 checked8_264))) (joinBlock (joinBlock checked8_272 (joinBlock checked8_280 checked8_288)) (joinBlock (joinBlock checked8_296 checked8_304) (joinBlock checked8_312 checked8_320)))) (joinBlock (joinBlock (joinBlock checked8_328 (joinBlock checked8_336 checked8_344)) (joinBlock (joinBlock checked8_352 checked8_360) (joinBlock checked8_368 checked8_376))) (joinBlock (joinBlock checked8_384 (joinBlock checked8_392 checked8_400)) (joinBlock (joinBlock checked8_408 checked8_416) (joinBlock checked8_424 checked8_432))))))

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_0 : block 9 0 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_8 : block 9 8 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_16 : block 9 16 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_24 : block 9 24 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_32 : block 9 32 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_40 : block 9 40 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_48 : block 9 48 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_56 : block 9 56 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_64 : block 9 64 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_72 : block 9 72 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_80 : block 9 80 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_88 : block 9 88 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_96 : block 9 96 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_104 : block 9 104 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_112 : block 9 112 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_120 : block 9 120 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_128 : block 9 128 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_136 : block 9 136 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_144 : block 9 144 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_152 : block 9 152 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked9_160 : block 9 160 5 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem checked9 : block 9 0 165 = true := (joinBlock (joinBlock (joinBlock (joinBlock checked9_0 checked9_8) (joinBlock checked9_16 (joinBlock checked9_24 checked9_32))) (joinBlock (joinBlock checked9_40 checked9_48) (joinBlock checked9_56 (joinBlock checked9_64 checked9_72)))) (joinBlock (joinBlock (joinBlock checked9_80 checked9_88) (joinBlock checked9_96 (joinBlock checked9_104 checked9_112))) (joinBlock (joinBlock checked9_120 (joinBlock checked9_128 checked9_136)) (joinBlock checked9_144 (joinBlock checked9_152 checked9_160)))))

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked10_0 : block 10 0 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked10_8 : block 10 8 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked10_16 : block 10 16 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked10_24 : block 10 24 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked10_32 : block 10 32 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked10_40 : block 10 40 5 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem checked10 : block 10 0 45 = true := (joinBlock (joinBlock checked10_0 (joinBlock checked10_8 checked10_16)) (joinBlock checked10_24 (joinBlock checked10_32 checked10_40)))

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked11_0 : block 11 0 8 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked11_8 : block 11 8 1 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem checked11 : block 11 0 9 = true := (joinBlock checked11_0 checked11_8)

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem checked12_0 : block 12 0 1 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem checked12 : block 12 0 1 = true := checked12_0

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem checkedAll (k i : Nat) (hi : i < (layer k).size) : audit k i = true := by
  by_cases hk : k ≤ 12
  · interval_cases k
    · change i < 0 at hi; omega
    · change i < 0 at hi; omega
    · change i < 0 at hi; omega
    · change i < 0 at hi; omega
    · change i < 0 at hi; omega
    · change i < 0 at hi; omega
    · apply atBlock checked6 i (Nat.zero_le i)
      change i < 43 at hi
      omega
    · apply atBlock checked7 i (Nat.zero_le i)
      change i < 418 at hi
      omega
    · apply atBlock checked8 i (Nat.zero_le i)
      change i < 434 at hi
      omega
    · apply atBlock checked9 i (Nat.zero_le i)
      change i < 165 at hi
      omega
    · apply atBlock checked10 i (Nat.zero_le i)
      change i < 45 at hi
      omega
    · apply atBlock checked11 i (Nat.zero_le i)
      change i < 9 at hi
      omega
    · apply atBlock checked12 i (Nat.zero_le i)
      change i < 1 at hi
      omega
  · have he : layer k = #[] := by unfold layer; split <;> first | omega | rfl
    rw [he] at hi
    change i < 0 at hi
    omega

end PEqualNP.Outside.L_meta_10460.Completion

theorem PEqualNP.Outside.L_meta_10460 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  exact PEqualNP.Outside.L_meta_10460.Finish.fromSigned (PEqualNP.Outside.L_meta_10460.Completion.signedBound PEqualNP.Outside.L_meta_10460.Completion.checkedAll)
