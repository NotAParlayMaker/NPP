import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12074

-- Adapted from the signed live-wire search and gate-elimination framework in L-meta-8724
-- and L-meta-8463, Apache-2.0.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := fun hh => sub ((Finset.insert_eq_of_mem hh) ▸ ht)
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

theorem live_image {ops : α → α → Finset α} {f : α → α}
    (hm : ∀ a b z, z ∈ ops a b → f z ∈ ops (f a) (f b))
    (hinj : Function.Injective f) {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : live ops (f goal) k (s.image f) := by
  induction k generalizing s with
  | zero =>
    change s = {goal} at h
    subst h; simp [live]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact Or.inl (ih skip)
    · refine Or.inr ⟨f a, Finset.mem_image_of_mem f ha, f b, Finset.mem_image_of_mem f hb,
        fun e => hab (hinj e), f z, hm a b z hz, ?_, rest.image f, ?_, ?_⟩
      · intro hm'
        obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hm'
        exact hout (hinj heq ▸ hu)
      · simp [Finset.image_insert]
      · simpa [Finset.image_insert] using ih tail

end Live

abbrev W := BitVec 482

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 241 := ((x >>> 241) ^^^ x).setWidth 241
def cuts (ws : List W) : BitVec 241 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 241) ++ (0 : BitVec 241)

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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 241) (w : W) : Prop :=
  w.getLsbD (241 + i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 241) (a b z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 241 + i.val < 482 := by omega
  have hi' : i.val < 482 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 241) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 241)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
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

theorem singleton_list {g : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {g}) : ws = [g] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

-- Fast Nat-based search engine (native kernel Nat.land/lor/xor/shiftRight primitives)
def MASKN : ℕ := 2 ^ 241 - 1
def FULLN : ℕ := 2 ^ 482 - 1
def GOALN : ℕ := goal.toNat
def NGOALN : ℕ := (~~~goal).toNat

def opsN (a b : ℕ) : List ℕ :=
  [Nat.land a b, Nat.lor a b, Nat.land a (FULLN - b), Nat.land b (FULLN - a)]

def sepN (w : ℕ) : ℕ :=
  Nat.land (Nat.xor (Nat.shiftRight w 241) w) MASKN

def cutsN : List ℕ → ℕ
  | [] => 0
  | w :: ws => Nat.lor (sepN w) (cutsN ws)

def memN (x : ℕ) : List ℕ → Bool
  | [] => false
  | y :: ys => Nat.beq x y || memN x ys

def dispatchN (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) : Bool :=
  let base := cutsN r
  let sa := sepN a
  let sb := sepN b
  (opsN a b).any fun w =>
    if Nat.beq w a || Nat.beq w b || memN w r then false
    else
      let v := Nat.lor (sepN w) base
      (Nat.beq v MASKN && next extra (w :: r)) ||
      (Nat.ble 1 extra && ((Nat.beq (Nat.lor v sa) MASKN && next (extra - 1) (w :: a :: r)) ||
                           (Nat.beq (Nat.lor v sb) MASKN && next (extra - 1) (w :: b :: r)))) ||
      (Nat.ble 2 extra && Nat.beq (Nat.lor (Nat.lor v sa) sb) MASKN && next (extra - 2) (w :: a :: b :: r))

def optN : ℕ → ℕ → List ℕ → Bool
  | 0, _, ws => match ws with | [w] => Nat.beq w GOALN || Nat.beq w NGOALN | _ => false
  | 1, _, ws => match ws with
      | [w] => Nat.beq w GOALN || Nat.beq w NGOALN
      | [a, b] => (opsN a b).any fun w => Nat.beq w GOALN || Nat.beq w NGOALN
      | _ => false
  | k + 1, extra, ws =>
      (match ws with | [w] => Nat.beq w GOALN || Nat.beq w NGOALN | _ => false) ||
      (pairs ws).any (fun (a, b, r) => dispatchN extra (optN k) a b r)

def searchN (n : ℕ) (inputs : List ℕ) : Bool :=
  inputs.sublists.any fun ws =>
    Nat.ble ws.length (n + 1) && Nat.beq (cutsN ws) MASKN && optN n (n + 1 - ws.length) ws

def checkFirstN (n : ℕ) (z : ℕ) (inputs : List ℕ) : Bool :=
  inputs.sublists.any fun ws =>
    let ys := z :: ws
    Nat.ble ys.length (n + 1) && Nat.beq (cutsN ys) MASKN && optN n (n + 1 - ys.length) ys

theorem opsN_map (a b : W) : (ops a b).map BitVec.toNat = opsN a.toNat b.toNat := by
  simp only [ops, opsN, List.map_cons, List.map_nil, BitVec.toNat_and, BitVec.toNat_or,
    BitVec.toNat_not, FULLN]
  rfl

theorem sepN_toNat (w : W) : sepN w.toNat = (sep w).toNat := by
  simp only [sepN, sep, MASKN, BitVec.toNat_setWidth, BitVec.toNat_xor, BitVec.toNat_ushiftRight]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem cutsN_map (ws : List W) : cutsN (ws.map BitVec.toNat) = (cuts ws).toNat := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, cutsN, cuts, List.foldr_cons, BitVec.toNat_or, sepN_toNat, ih]
    rfl

theorem memN_false {w : W} {ws : List W} (h : w ∉ ws) : memN w.toNat (ws.map BitVec.toNat) = false := by
  induction ws with
  | nil => rfl
  | cons u us ih =>
    have hne : w ≠ u := fun e => h (e ▸ List.mem_cons_self)
    have htl : w ∉ us := fun hm => h (List.mem_cons_of_mem _ hm)
    simp only [List.map_cons, memN, ih htl, Bool.or_false]
    cases hb : Nat.beq w.toNat u.toNat
    · rfl
    · exact absurd (BitVec.toNat_inj.mp (Nat.eq_of_beq_eq_true hb)) hne

theorem pairs_map {α β : Type} (f : α → β) (ws : List α) :
    pairs (ws.map f) = (pairs ws).map (fun (a, b, r) => (f a, f b, r.map f)) := by
  have singles_map : ∀ l : List α,
      singles (l.map f) = (singles l).map (fun (b, bs) => (f b, bs.map f)) := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, singles, ih, List.map_map]
      rfl
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, pairs, singles_map, ih, List.map_append, List.map_map]
    rfl

theorem maskN_eq : (-1 : BitVec 241).toNat = MASKN := by
  change (BitVec.allOnes 241).toNat = 2 ^ 241 - 1
  exact BitVec.toNat_allOnes

theorem dispatchN_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List ℕ → Bool)
    (hz : z ∈ basicOps a b) (hzout : z ≠ a ∧ z ≠ b ∧ z ∉ r)
    (hk : kept ∈ keepChoices a b r) (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1)
    (ht : next (k - kept.length) ((z :: kept).map BitVec.toNat) = true) :
    dispatchN extra next a.toNat b.toNat (r.map BitVec.toNat) = true := by
  apply List.any_eq_true.mpr
  refine ⟨z.toNat, ?_, ?_⟩
  · rw [← opsN_map]; exact List.mem_map.mpr ⟨z, List.mem_toFinset.mp hz, rfl⟩
  · have hna : Nat.beq z.toNat a.toNat = false := by
      cases hb : Nat.beq z.toNat a.toNat
      · rfl
      · exact absurd (BitVec.toNat_inj.mp (Nat.eq_of_beq_eq_true hb)) hzout.1
    have hnb : Nat.beq z.toNat b.toNat = false := by
      cases hb : Nat.beq z.toNat b.toNat
      · rfl
      · exact absurd (BitVec.toNat_inj.mp (Nat.eq_of_beq_eq_true hb)) hzout.2.1
    have hnr : memN z.toNat (r.map BitVec.toNat) = false := memN_false hzout.2.2
    simp only [hna, hnb, hnr, Bool.or_false, Bool.false_eq_true, ite_false]
    have hcN : cutsN ((z :: kept).map BitVec.toNat) = MASKN := by
      rw [cutsN_map, hc, maskN_eq]
    simp [keepChoices] at hk
    rcases hk with rfl | rfl | rfl | rfl <;>
      simp only [List.map_cons, cutsN] at hcN ht ⊢ <;>
      (try simp only [List.length_cons] at *) <;>
      simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq]
    · left; left; exact ⟨hcN, by convert ht using 2; omega⟩
    · left; right; refine ⟨by omega, .inl ⟨?_, by convert ht using 2; omega⟩⟩
      change (sepN z.toNat ||| cutsN (r.map BitVec.toNat)) ||| sepN a.toNat = MASKN
      change sepN z.toNat ||| (sepN a.toNat ||| cutsN (r.map BitVec.toNat)) = MASKN at hcN
      rw [← hcN]; ac_rfl
    · left; right; refine ⟨by omega, .inr ⟨?_, by convert ht using 2; omega⟩⟩
      change (sepN z.toNat ||| cutsN (r.map BitVec.toNat)) ||| sepN b.toNat = MASKN
      change sepN z.toNat ||| (sepN b.toNat ||| cutsN (r.map BitVec.toNat)) = MASKN at hcN
      rw [← hcN]; ac_rfl
    · right; refine ⟨⟨by omega, ?_⟩, by convert ht using 2; omega⟩
      change ((sepN z.toNat ||| cutsN (r.map BitVec.toNat)) ||| sepN a.toNat) ||| sepN b.toNat = MASKN
      change sepN z.toNat ||| (sepN a.toNat ||| (sepN b.toNat ||| cutsN (r.map BitVec.toNat))) = MASKN at hcN
      rw [← hcN]; ac_rfl

theorem optN_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ)
    (hn : ws.Nodup) (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optN n extra (ws.map BitVec.toNat) = true := by
  have hgN : (Nat.beq g.toNat GOALN || Nat.beq g.toNat NGOALN) = true := by
    rcases hg with rfl | rfl <;> simp [GOALN, NGOALN]
  induction n generalizing ws extra with
  | zero =>
    rw [singleton_list hn h]
    simpa [optN] using hgN
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rw [singleton_list hn done]
      cases k with
      | zero => simpa [optN] using hgN
      | succ k' =>
        change ((Nat.beq g.toNat GOALN || Nat.beq g.toNat NGOALN) || _) = true
        simp [hgN]
    · cases k with
      | zero =>
        change insert z needed = {g} at tail
        have hzg : z = g := Finset.mem_singleton.mp (tail ▸ Finset.mem_insert_self z needed)
        have hcard := live_card h
        rw [List.toFinset_card_of_nodup hn] at hcard
        obtain ⟨r, _, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
        have hlen := hp.length_eq
        have hrnil : r = [] := by
          cases r with
          | nil => rfl
          | cons => simp at hlen; omega
        subst hrnil
        have hws2 : ws = [a, b] ∨ ws = [b, a] := by
          cases ws with
          | nil => simp at hlen
          | cons u ws' =>
            cases ws' with
            | nil => simp at hlen
            | cons v ws'' =>
              cases ws'' with
              | nil =>
                have hu : u = a ∨ u = b := by
                  have := hp.mem_iff.mp (List.mem_cons_self)
                  simpa using this
                have hv : v = a ∨ v = b := by
                  have := hp.mem_iff.mp (List.mem_cons_of_mem _ List.mem_cons_self)
                  simpa using this
                have huv : u ≠ v := (List.nodup_cons.mp hn).1 ∘ (by intro e; simp [e])
                rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
                · exact absurd rfl huv
                · exact .inl rfl
                · exact .inr rfl
                · exact absurd rfl huv
              | cons => simp at hlen
        rcases hws2 with rfl | rfl
        · change (opsN a.toNat b.toNat).any (fun w => Nat.beq w GOALN || Nat.beq w NGOALN) = true
          rw [List.any_eq_true]
          exact ⟨g.toNat, by rw [← opsN_map, ← hzg]; exact List.mem_map.mpr ⟨z, List.mem_toFinset.mp hz, rfl⟩, hgN⟩
        · change (opsN b.toNat a.toNat).any (fun w => Nat.beq w GOALN || Nat.beq w NGOALN) = true
          rw [List.any_eq_true]
          have hz' : z ∈ basicOps b a := ops_swap a b ▸ hz
          exact ⟨g.toNat, by rw [← opsN_map, ← hzg]; exact List.mem_map.mpr ⟨z, List.mem_toFinset.mp hz', rfl⟩, hgN⟩
      | succ k' =>
        obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
        have go {a b : W} (perm : ws.Perm (a :: b :: r))
            (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
            dispatchN extra (optN (k' + 1)) a.toNat b.toNat (r.map BitVec.toNat) = true := by
          obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
          have hzout' : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
            have hnot : z ∉ a :: b :: r := fun hm' => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm'))
            simp only [List.mem_cons, not_or] at hnot
            exact hnot
          have hznew : z ∉ kept := by
            intro hu
            apply hout
            rw [hset]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
          have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
          have hl : live basicOps g (k' + 1) (z :: kept).toFinset := by simpa [hfin] using tail
          have hc := live_card hl
          rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
          have len := perm.length_eq
          simp only [List.length_cons] at len
          apply dispatchN_complete (k := k' + 1) (extra := extra) (optN (k' + 1)) hop hzout' hk (by omega) (by omega) (cuts_full hg hl)
          apply ih _ _ hnd _ hl
          simp; omega
        change ((match ws.map BitVec.toNat with | [w] => Nat.beq w GOALN || Nat.beq w NGOALN | _ => false) ||
          (pairs (ws.map BitVec.toNat)).any (fun (a, b, r) => dispatchN extra (optN (k' + 1)) a b r)) = true
        rw [Bool.or_eq_true, List.any_eq_true]
        right
        rw [pairs_map]
        rcases hm with direct | swap
        · exact ⟨(a.toNat, b.toNat, r.map BitVec.toNat),
            List.mem_map.mpr ⟨(a, b, r), direct, rfl⟩, go hp hs hz⟩
        · exact ⟨(b.toNat, a.toNat, r.map BitVec.toNat),
            List.mem_map.mpr ⟨(b, a, r), swap, rfl⟩,
            go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

theorem searchN_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) :
    searchN n (inputs.map BitVec.toNat) = true := by
  classical
  obtain ⟨s, hs, hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hmem : ws.map BitVec.toNat ∈ (inputs.map BitVec.toNat).sublists :=
    List.mem_sublists.mpr ((List.filter_sublist ..).map BitVec.toNat)
  refine List.any_eq_true.mpr ⟨ws.map BitVec.toNat, hmem, ?_⟩
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, List.length_map]
  refine ⟨⟨sz, by rw [cutsN_map, cuts_full hg hl', maskN_eq]⟩, ?_⟩
  exact optN_complete hg n ws (n + 1 - ws.length) hnd (by omega) hl'

theorem checkFirstN_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (z : W) (inputs : List W)
    (hn : inputs.Nodup) {rest : Finset W} (hsub : rest ⊆ inputs.toFinset)
    (h : live basicOps g n (insert z rest)) :
    checkFirstN n z.toNat (inputs.map BitVec.toNat) = true := by
  classical
  let ws := inputs.filter (fun w => w ∈ rest ∧ w ≠ z)
  have hzw : z ∉ ws := by simp [ws]
  have hnd : (z :: ws).Nodup := List.nodup_cons.mpr ⟨hzw, hn.filter _⟩
  have heq : (z :: ws).toFinset = insert z rest := by
    ext w
    simp only [ws, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · rintro (rfl | ⟨_, hr, _⟩)
      · exact Or.inl rfl
      · exact Or.inr hr
    · rintro (rfl | hr)
      · exact Or.inl rfl
      · by_cases hwz : w = z
        · exact Or.inl hwz
        · exact Or.inr ⟨List.mem_toFinset.mp (hsub hr), hr, hwz⟩
  have hl' : live basicOps g n (z :: ws).toFinset := heq.symm ▸ h
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hmem : ws.map BitVec.toNat ∈ (inputs.map BitVec.toNat).sublists :=
    List.mem_sublists.mpr ((List.filter_sublist ..).map BitVec.toNat)
  refine List.any_eq_true.mpr ⟨ws.map BitVec.toNat, hmem, ?_⟩
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, List.length_cons, List.length_map]
  have hys : z.toNat :: ws.map BitVec.toNat = (z :: ws).map BitVec.toNat := rfl
  rw [hys]
  refine ⟨⟨by simpa using sz, by rw [cutsN_map, cuts_full hg hl', maskN_eq]⟩, ?_⟩
  exact optN_complete hg n (z :: ws) (n + 1 - (ws.length + 1)) hnd (by simp at sz ⊢; omega) hl'

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a, ha, e⟩ => ⟨a, sub ha, e⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 482 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 482)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps, ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps, ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 482) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 482) :
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

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 482) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#482)[k.val] = false; simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
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

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
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
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

def SignedBuild (k : ℕ) (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {av : Finset W} {z : W} (h : holds av z) : SignedBuild 0 av z := by
  rcases h with h | h | ⟨a, ha, rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not, build] using ha)))

theorem sb_wait {av : Finset W} {z : W} {k : ℕ} (h : SignedBuild k av z) :
    SignedBuild (k + 1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

theorem sb_le {av : Finset W} {z : W} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild k av z) :
    SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {av : Finset W} {t a b z : W} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps a b) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k + 1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩) (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩)))

theorem sb_advance {av : Finset W} {z t : W} {k : ℕ} (hz : reachable av z)
    (next : ∀ av' : Finset W, av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k + 1) av t := by
  rcases hz with h | ⟨a, ha, b, hb, hn, w, hw, ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem mem_ops_reach {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

set_option maxRecDepth 5000 in
theorem mem_ops_const {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hconst : (x = 0 ∨ x = ~~~0) ∨ (y = 0 ∨ y = ~~~0)) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have h0 : holds av (0 : W) := .inl rfl
  have h1 : holds av (~~~(0 : W)) := .inr (.inl rfl)
  have a0l (u : W) : (0 : W) &&& u = 0 := BitVec.zero_and
  have a0r (u : W) : u &&& (0 : W) = 0 := BitVec.and_zero
  have o0l (u : W) : (0 : W) ||| u = u := BitVec.zero_or
  have o0r (u : W) : u ||| (0 : W) = u := BitVec.or_zero
  have a1l (u : W) : ~~~(0 : W) &&& u = u := BitVec.allOnes_and
  have a1r (u : W) : u &&& ~~~(0 : W) = u := BitVec.and_allOnes
  have o1l (u : W) : ~~~(0 : W) ||| u = ~~~0 := BitVec.allOnes_or
  have o1r (u : W) : u ||| ~~~(0 : W) = ~~~0 := BitVec.or_allOnes
  have n1 : ~~~(~~~(0 : W)) = 0 := BitVec.not_not
  rcases hconst with (rfl | rfl) | (rfl | rfl) <;> rcases hz with rfl | rfl | rfl | rfl
  all_goals first
    | rw [a0l]; exact h0
    | rw [a0r]; exact h0
    | rw [o0l]; exact hy
    | rw [o0r]; exact hx
    | rw [a1l]; exact hy
    | rw [a1r]; exact hx
    | rw [a1r]; exact hy
    | rw [o1l]; exact h1
    | rw [o1r]; exact h1
    | rw [n1, a0r]; exact h0
    | rw [a1l]; exact holds_not hy
    | rw [a1l]; exact holds_not hx

theorem live_transport {f : W → W} (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero => change s = {g} at run; exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · exact sb_wait (ih skip hav)
    · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
      intro av' sub ok
      apply ih tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hr
      · exact ok
      · exact holds_mono sub (hav u (by simp [he, hr]))

theorem live_transport_save {f : W → W}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hp : p ∈ s) (hpg : p ≠ g) (hconst : f p = 0 ∨ f p = ~~~0)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild (k - 1) av (f g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    exact False.elim (hpg (by simpa [run] using hp))
  | succ k ih =>
    simp only [Nat.add_sub_cancel] at *
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · exact sb_le (Nat.sub_le _ _) (ih skip hp hav)
    · have mapped := hm a b z hz
      have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he, hu])
      by_cases touches : p = a ∨ p = b
      · have cc : (f a = 0 ∨ f a = ~~~0) ∨ (f b = 0 ∨ f b = ~~~0) :=
          touches.elim (fun h => .inl (h ▸ hconst)) (fun h => .inr (h ▸ hconst))
        have collapsed := mem_ops_const (hav a ha) (hav b hb) cc mapped
        apply live_transport hm tail
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact collapsed
        · exact inOld u hr
      · have pr : p ∈ r := by
          rw [he] at hp
          simpa [Finset.mem_insert, touches, (not_or.mp touches).1, (not_or.mp touches).2] using hp
        have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
        have pos : 0 < k := by
          by_contra! hk
          have eq : k = 0 := by omega
          subst k
          change insert z r = {g} at tail
          exact hpg (by simpa [tail] using pt)
        have cost : (k - 1) + 1 = k := by omega
        rw [← cost]
        apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) mapped)
        intro av' sub ok
        apply ih tail pt
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact ok
        · exact holds_mono sub (inOld u hr)

def selectRows (m : Fin 482 → Fin 482) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 482 => w[(m k).val]))).cast List.length_ofFn

theorem selectRows_bit (m : Fin 482 → Fin 482) (w : W) (j : ℕ) (hj : j < 482) :
    (selectRows m w)[j] = w[(m ⟨j, hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [selectRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem selectRows_eq (m : Fin 482 → Fin 482) (u v : W)
    (h : ∀ j : Fin 482, u[(m j).val] = v[j.val]) : selectRows m u = v := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [selectRows_bit m u j hj]
  exact h ⟨j, hj⟩

theorem selectRows_not (m : Fin 482 → Fin 482) (u : W) :
    selectRows m (~~~u) = ~~~selectRows m u := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  simp only [selectRows_bit _ _ j hj, BitVec.getElem_not]

theorem selectRows_and (m : Fin 482 → Fin 482) (u v : W) :
    selectRows m (u &&& v) = selectRows m u &&& selectRows m v := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  simp only [selectRows_bit _ _ j hj, BitVec.getElem_and]

theorem selectRows_or (m : Fin 482 → Fin 482) (u v : W) :
    selectRows m (u ||| v) = selectRows m u ||| selectRows m v := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  simp only [selectRows_bit _ _ j hj, BitVec.getElem_or]

theorem selectRows_ops (m : Fin 482 → Fin 482) (a b z : W) (hz : z ∈ basicOps a b) :
    selectRows m z ∈ basicOps (selectRows m a) (selectRows m b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl
  · exact Or.inl (selectRows_and m a b)
  · exact Or.inr (Or.inl (selectRows_or m a b))
  · exact Or.inr (Or.inr (Or.inl (by rw [selectRows_and, selectRows_not])))
  · exact Or.inr (Or.inr (Or.inr (by rw [selectRows_and, selectRows_not])))

theorem selectRows_invol (m : Fin 482 → Fin 482) (hm : ∀ k, m (m k) = k) :
    Function.Injective (selectRows m) := by
  have hinv : ∀ w : W, selectRows m (selectRows m w) = w := by
    intro w
    apply BitVec.eq_of_getElem_eq
    intro j hj
    rw [selectRows_bit m _ j hj, selectRows_bit m _ (m ⟨j, hj⟩).val (m ⟨j, hj⟩).isLt]
    simp [hm ⟨j, hj⟩]
  intro a b h
  rw [← hinv a, ← hinv b, h]

theorem restrict_goal_signs {f : W → W} (hneg : ∀ u, f (~~~u) = ~~~f u)
    (hfg : f goal = goal) {t : W} (ht : t = goal ∨ t = ~~~goal) :
    f t = goal ∨ f t = ~~~goal := by
  rcases ht with rfl | rfl
  · exact Or.inl hfg
  · exact Or.inr (by rw [hneg, hfg])

theorem impossible_of_searchN {k : ℕ} {ins : List W} (hrej : searchN k (ins.map BitVec.toNat) = false)
    (hnd : ins.Nodup) {u : W} (hu : u = goal ∨ u = ~~~goal)
    (hsb : SignedBuild k ins.toFinset u) : False := by
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  have no {v : W} (hv : v = goal ∨ v = ~~~goal) (run : build basicOps v k ins.toFinset) : False :=
    Bool.noConfusion (hrej.symm.trans (searchN_complete hv k ins hnd run))
  rcases hsb with c | c | run | run
  · rcases hu with rfl | rfl
    · exact ne.1 c
    · exact ne.2.2.1 c
  · rcases hu with rfl | rfl
    · exact ne.2.1 c
    · exact ne.2.2.2 c
  · exact no hu run
  · exact no (hu.elim (fun h => Or.inr (by rw [h])) (fun h => Or.inl (by rw [h, BitVec.not_not]))) run

def table (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4269860864 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def ins6 : List W := [0x3ffffc00003ffffc00003ffffc00003ffffffffffffff800007fffffffffe5455454554545545455454554545545455454554a8aa8a8aa8a8aa8a8aa9, 0x3fffffffffc0000000003fffffffffc00003ffffffffffffff800007ffffe989989899898998989989899898998989989899931331313313133131331, 0x3fffffffffffffffffffc000000000000003fffffffffffffffffff800004e11e0e11e0e11e0e11e0e11e0e11e0e11e0e11e1c23c1c23c1c23c1c23c0, 0x3ffffffffffffffffffffffffffffffffffc00007fffffffffffffffffffb01e0101e0101e0101e0101e0101e0101e0101e0203c0203c0203c0203c01, 0x3fffffffffffffffffffffffffffffffffffffff800000000000000000005fe001fe001fe001fe001fe001fe001fe001fe003fc003fc003fc003fc000, 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe]

def v6 (i : Fin 6) : W := ins6.getD i.val 0

theorem spec_table : ∀ j : Fin 482,
    Nat.testBit (4269860864 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if (ins6.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val] := by
  decide +kernel

def ix5 : List ℕ := [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]

def map5 (j : Fin 482) : Fin 482 :=
  ⟨((if j.val < 241 then 0 else 241) + ix5.getD (j.val % 241) 0) % 482,
    Nat.mod_lt _ (by decide)⟩

def restrict5 (w : W) : W := selectRows map5 w

def ins5 : List W := [0x3ffffc00003ffffc00003ffffc00003ffffffffffffff800007fffffffffe5455454554545545455454554545545455454554a8aa8a8aa8a8aa8a8aa8, 0x3fffffffffc0000000003fffffffffc00003ffffffffffffff800007ffffe989989899898998989989899898998989989899931331313313133131330, 0x3fffffffffffffffffffc000000000000003fffffffffffffffffff800006e11e0e11e0e11e0e11e0e11e0e11e0e11e0e11e1c23c1c23c1c23c1c23c0, 0x3ffffffffffffffffffffffffffffffffffc00007fffffffffffffffffff901e0101e0101e0101e0101e0101e0101e0101e0203c0203c0203c0203c00, 0x3fffffffffffffffffffffffffffffffffffffff800000000000000000007fe001fe001fe001fe001fe001fe001fe001fe003fc003fc003fc003fc000]

def v5 (i : Fin 5) : W := ins5.getD i.val 0

theorem ins5_nd : ins5.Nodup := by decide +kernel

theorem restrict5_v5 : restrict5 (v6 5) = ~~~0 := selectRows_eq map5 _ _ (by decide +kernel)

theorem restrict5_goal : restrict5 goal = goal := selectRows_eq map5 _ _ (by decide +kernel)

theorem restrict5_avail (k : Fin 6) : holds ins5.toFinset (restrict5 (v6 k)) := by
  have h : ∀ i : Fin 5, restrict5 (v6 i.castSucc) = v5 i :=
    fun i => selectRows_eq map5 _ _ (by revert i; decide +kernel)
  fin_cases k
  · exact .inr (.inr ⟨v5 0, by simp [ins5, v5], .inl (h 0)⟩)
  · exact .inr (.inr ⟨v5 1, by simp [ins5, v5], .inl (h 1)⟩)
  · exact .inr (.inr ⟨v5 2, by simp [ins5, v5], .inl (h 2)⟩)
  · exact .inr (.inr ⟨v5 3, by simp [ins5, v5], .inl (h 3)⟩)
  · exact .inr (.inr ⟨v5 4, by simp [ins5, v5], .inl (h 4)⟩)
  · exact .inr (.inl restrict5_v5)

def changes (w : W) (r : Fin 241) : Bool :=
  w.getLsbD (241 + r.val) != w.getLsbD r.val

theorem unchanged (w : W) (r : Fin 241) (h : changes w r = false) : ¬ differs r w := by
  simpa [changes, differs] using h

theorem goal_changes : ∀ k : Fin 241, differs k goal ∧ differs k (~~~goal) := by
  unfold differs; decide +kernel

set_option maxRecDepth 8000 in
theorem input6_index : ∀ w ∈ ins6, ∃ i : Fin 6, v6 i = w := by
  intro w hw
  simp only [ins6, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩

theorem input6_not_goal : ∀ i : Fin 6, v6 i ≠ goal ∧ v6 i ≠ ~~~goal := by decide +kernel

theorem pair0_only_x5 : ∀ q : Fin 6, q ≠ 5 → changes (v6 q) ⟨0, by decide⟩ = false := by decide +kernel

set_option maxRecDepth 8000 in
theorem input5_index : ∀ w ∈ ins5, ∃ i : Fin 5, v5 i = w := by
  intro w hw
  simp only [ins5, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩

theorem input5_not_goal : ∀ i : Fin 5, v5 i ≠ goal ∧ v5 i ≠ ~~~goal := by decide +kernel

theorem index_of_op (a b z : W) (hz : z ∈ basicOps a b) :
    ∃ o : Fin 4, (ops a b).getD o.val 0 = z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩

def ix3 : List ℕ := [10, 11, 12, 13, 21, 30, 31, 32, 33, 41, 50, 51, 52, 53, 61, 70, 71, 72, 73, 81, 109, 110, 111, 112, 120, 129, 130, 131, 132, 140, 149, 150, 151, 152, 160, 169, 170, 171, 172, 180, 189, 190, 191, 192, 200, 209, 210, 211, 212, 220, 229, 230, 231, 232, 240]

def map3 (j : Fin 482) : Fin 482 :=
  ⟨((if j.val < 241 then 0 else 241) + ix3.getD (j.val % 241 % 55) 0) % 482,
    Nat.mod_lt _ (by decide)⟩

def restrict3 (w : W) : W := selectRows map3 w

def ins4_3 : List W := [0x3f07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83fff83e0f83ff07fe108421084210842108421084210842108421084210842108421084210842, 0x1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1fffc00ffc1ff83e210842108421084210842108421084210842108421084210842108421084, 0x1fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe0fffff0001fffc0421084210842108421084210842108421084210842108421084210842108, 0x200001ffffffffc00003ffffffff800007ffffffff00000ffffffffe00000842108421084210842108421084210842108421084210842108421084210]

theorem ins4_3_nd : ins4_3.Nodup := by decide +kernel

theorem restrict3_v3 : restrict3 (v5 3) = ~~~0 := selectRows_eq map3 _ _ (by decide +kernel)

theorem restrict3_goal : restrict3 goal = goal := selectRows_eq map3 _ _ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject3 : searchN 6 (ins4_3.map BitVec.toNat) = false := by decide +kernel

theorem restrict3_avail (k : Fin 5) : holds ins4_3.toFinset (restrict3 (v5 k)) := by
  have h0 : restrict3 (v5 0) = ins4_3.getD 0 0 := selectRows_eq map3 _ _ (by decide +kernel)
  have h1 : restrict3 (v5 1) = ins4_3.getD 1 0 := selectRows_eq map3 _ _ (by decide +kernel)
  have h2 : restrict3 (v5 2) = ins4_3.getD 2 0 := selectRows_eq map3 _ _ (by decide +kernel)
  have h4 : restrict3 (v5 4) = ins4_3.getD 3 0 := selectRows_eq map3 _ _ (by decide +kernel)
  fin_cases k
  · exact .inr (.inr ⟨_, by simp [ins4_3], .inl h0⟩)
  · exact .inr (.inr ⟨_, by simp [ins4_3], .inl h1⟩)
  · exact .inr (.inr ⟨_, by simp [ins4_3], .inl h2⟩)
  · exact .inr (.inl restrict3_v3)
  · exact .inr (.inr ⟨_, by simp [ins4_3], .inl h4⟩)

def row3Tbl : List ℕ := [48, 5, 5, 48, 27, 5, 5, 27, 5, 27, 27, 5, 0, 0, 0, 0, 5, 114, 114, 5]

def row3 (j : Fin 5) (op : Fin 4) : Fin 241 :=
  ⟨row3Tbl.getD (4 * j.val + op.val) 0 % 241, Nat.mod_lt _ (by decide)⟩

theorem sep_pair_3 : ∀ j : Fin 5, j ≠ 3 → ∀ op : Fin 4,
    changes ((ops (v5 3) (v5 j)).getD op.val 0) (row3 j op) = false ∧
    ∀ q : Fin 5, q ≠ 3 → changes (v5 q) (row3 j op) = false := by decide +kernel

theorem kill_case_3 {t : W} (ht : t = goal ∨ t = ~~~goal) (j : Fin 5) (hj : j ≠ 3)
    {z : W} (hz : z ∈ basicOps (v5 3) (v5 j)) (rest : Finset W)
    (hsub : rest ⊆ ins5.toFinset) (tail : live basicOps t 7 (insert z rest)) : False := by
  obtain ⟨o, ho⟩ := index_of_op _ _ _ hz
  obtain ⟨hrz, hrq⟩ := sep_pair_3 j hj o
  let r := row3 j o
  rw [ho] at hrz
  have hd : differs r t := ht.elim (fun h => h ▸ (goal_changes r).1) (fun h => h ▸ (goal_changes r).2)
  obtain ⟨w, hw, hdw⟩ := live_separates (differs r) hd (ops_differs r) tail
  have hkeep : v5 3 ∈ rest := by
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact False.elim (unchanged _ _ hrz hdw)
    · obtain ⟨q, rfl⟩ := input5_index _ (List.mem_toFinset.mp (hsub hw))
      by_contra hn
      exact unchanged _ _ (hrq q (fun eq => hn (eq ▸ hw))) hdw
  have pg : v5 3 ≠ t := ht.elim (fun h => h ▸ (input5_not_goal 3).1) (fun h => h ▸ (input5_not_goal 3).2)
  have hsb : SignedBuild 6 ins4_3.toFinset (restrict3 t) := by
    apply live_transport_save (selectRows_ops map3) tail (Finset.mem_insert_of_mem hkeep) pg (Or.inr restrict3_v3)
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact mem_ops_const (restrict3_avail 3) (restrict3_avail j) (Or.inl (Or.inr restrict3_v3))
        (selectRows_ops map3 _ _ _ hz)
    · obtain ⟨q, rfl⟩ := input5_index _ (List.mem_toFinset.mp (hsub hu))
      exact restrict3_avail q
  exact impossible_of_searchN reject3 ins4_3_nd (restrict_goal_signs (selectRows_not map3) restrict3_goal ht) hsb

def ixSw01 : List ℕ := [0, 1, 2, 4, 3, 5, 6, 8, 7, 9, 10, 12, 11, 13, 14, 16, 15, 17, 18, 20, 19, 21, 42, 44, 43, 45, 46, 48, 47, 49, 50, 52, 51, 53, 54, 56, 55, 57, 58, 60, 59, 61, 22, 24, 23, 25, 26, 28, 27, 29, 30, 32, 31, 33, 34, 36, 35, 37, 38, 40, 39, 41, 62, 64, 63, 65, 66, 68, 67, 69, 70, 72, 71, 73, 74, 76, 75, 77, 78, 80, 79, 81, 83, 82, 84, 85, 87, 86, 88, 89, 91, 90, 92, 93, 95, 94, 96, 97, 99, 98, 100, 121, 123, 122, 124, 125, 127, 126, 128, 129, 131, 130, 132, 133, 135, 134, 136, 137, 139, 138, 140, 101, 103, 102, 104, 105, 107, 106, 108, 109, 111, 110, 112, 113, 115, 114, 116, 117, 119, 118, 120, 141, 143, 142, 144, 145, 147, 146, 148, 149, 151, 150, 152, 153, 155, 154, 156, 157, 159, 158, 160, 161, 163, 162, 164, 165, 167, 166, 168, 169, 171, 170, 172, 173, 175, 174, 176, 177, 179, 178, 180, 201, 203, 202, 204, 205, 207, 206, 208, 209, 211, 210, 212, 213, 215, 214, 216, 217, 219, 218, 220, 181, 183, 182, 184, 185, 187, 186, 188, 189, 191, 190, 192, 193, 195, 194, 196, 197, 199, 198, 200, 221, 223, 222, 224, 225, 227, 226, 228, 229, 231, 230, 232, 233, 235, 234, 236, 237, 239, 238, 240]
def mapSw01 (j : Fin 482) : Fin 482 :=
  ⟨((if j.val < 241 then 0 else 241) + ixSw01.getD (j.val % 241) 0) % 482, Nat.mod_lt _ (by decide)⟩
def sw01 (w : W) : W := selectRows mapSw01 w
theorem sw01_invol : ∀ k : Fin 482, mapSw01 (mapSw01 k) = k := by decide +kernel
theorem sw01_goal : sw01 goal = goal := selectRows_eq mapSw01 _ _ (by decide +kernel)
theorem sw01_v0 : sw01 (v5 0) = v5 1 := selectRows_eq mapSw01 _ _ (by decide +kernel)
theorem sw01_v1 : sw01 (v5 1) = v5 0 := selectRows_eq mapSw01 _ _ (by decide +kernel)
theorem sw01_v2 : sw01 (v5 2) = v5 2 := selectRows_eq mapSw01 _ _ (by decide +kernel)
theorem sw01_v3 : sw01 (v5 3) = v5 3 := selectRows_eq mapSw01 _ _ (by decide +kernel)
theorem sw01_v4 : sw01 (v5 4) = v5 4 := selectRows_eq mapSw01 _ _ (by decide +kernel)
theorem sw01_ins5 : ∀ w ∈ ins5, sw01 w ∈ ins5 := by
  intro w hw; obtain ⟨i, rfl⟩ := input5_index w hw
  fin_cases i
  · change sw01 (v5 0) ∈ ins5; rw [sw01_v0]; simp [ins5, v5]
  · change sw01 (v5 1) ∈ ins5; rw [sw01_v1]; simp [ins5, v5]
  · change sw01 (v5 2) ∈ ins5; rw [sw01_v2]; simp [ins5, v5]
  · change sw01 (v5 3) ∈ ins5; rw [sw01_v3]; simp [ins5, v5]
  · change sw01 (v5 4) ∈ ins5; rw [sw01_v4]; simp [ins5, v5]

def ixSw02 : List ℕ := [0, 1, 42, 46, 44, 48, 43, 47, 45, 49, 50, 53, 52, 51, 54, 58, 56, 60, 55, 59, 57, 61, 22, 26, 24, 28, 23, 27, 25, 29, 30, 33, 32, 31, 34, 38, 36, 40, 35, 39, 37, 41, 2, 6, 4, 8, 3, 7, 5, 9, 10, 13, 12, 11, 14, 18, 16, 20, 15, 19, 17, 21, 62, 66, 64, 68, 63, 67, 65, 69, 70, 73, 72, 71, 74, 78, 76, 80, 75, 79, 77, 81, 85, 83, 87, 82, 86, 84, 88, 89, 92, 91, 90, 93, 97, 95, 99, 94, 98, 96, 100, 161, 165, 163, 167, 162, 166, 164, 168, 169, 172, 171, 170, 173, 177, 175, 179, 174, 178, 176, 180, 121, 125, 123, 127, 122, 126, 124, 128, 129, 132, 131, 130, 133, 137, 135, 139, 134, 138, 136, 140, 201, 205, 203, 207, 202, 206, 204, 208, 209, 212, 211, 210, 213, 217, 215, 219, 214, 218, 216, 220, 101, 105, 103, 107, 102, 106, 104, 108, 109, 112, 111, 110, 113, 117, 115, 119, 114, 118, 116, 120, 181, 185, 183, 187, 182, 186, 184, 188, 189, 192, 191, 190, 193, 197, 195, 199, 194, 198, 196, 200, 141, 145, 143, 147, 142, 146, 144, 148, 149, 152, 151, 150, 153, 157, 155, 159, 154, 158, 156, 160, 221, 225, 223, 227, 222, 226, 224, 228, 229, 232, 231, 230, 233, 237, 235, 239, 234, 238, 236, 240]
def mapSw02 (j : Fin 482) : Fin 482 :=
  ⟨((if j.val < 241 then 0 else 241) + ixSw02.getD (j.val % 241) 0) % 482, Nat.mod_lt _ (by decide)⟩
def sw02 (w : W) : W := selectRows mapSw02 w
theorem sw02_invol : ∀ k : Fin 482, mapSw02 (mapSw02 k) = k := by decide +kernel
theorem sw02_goal : sw02 goal = goal := selectRows_eq mapSw02 _ _ (by decide +kernel)
theorem sw02_v0 : sw02 (v5 0) = v5 2 := selectRows_eq mapSw02 _ _ (by decide +kernel)
theorem sw02_v1 : sw02 (v5 1) = v5 1 := selectRows_eq mapSw02 _ _ (by decide +kernel)
theorem sw02_v2 : sw02 (v5 2) = v5 0 := selectRows_eq mapSw02 _ _ (by decide +kernel)
theorem sw02_v3 : sw02 (v5 3) = v5 3 := selectRows_eq mapSw02 _ _ (by decide +kernel)
theorem sw02_v4 : sw02 (v5 4) = v5 4 := selectRows_eq mapSw02 _ _ (by decide +kernel)
theorem sw02_ins5 : ∀ w ∈ ins5, sw02 w ∈ ins5 := by
  intro w hw; obtain ⟨i, rfl⟩ := input5_index w hw
  fin_cases i
  · change sw02 (v5 0) ∈ ins5; rw [sw02_v0]; simp [ins5, v5]
  · change sw02 (v5 1) ∈ ins5; rw [sw02_v1]; simp [ins5, v5]
  · change sw02 (v5 2) ∈ ins5; rw [sw02_v2]; simp [ins5, v5]
  · change sw02 (v5 3) ∈ ins5; rw [sw02_v3]; simp [ins5, v5]
  · change sw02 (v5 4) ∈ ins5; rw [sw02_v4]; simp [ins5, v5]

def ixSw12 : List ℕ := [0, 1, 22, 23, 26, 27, 24, 25, 28, 29, 30, 31, 33, 32, 34, 35, 38, 39, 36, 37, 40, 41, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11, 13, 12, 14, 15, 18, 19, 16, 17, 20, 21, 42, 43, 46, 47, 44, 45, 48, 49, 50, 51, 53, 52, 54, 55, 58, 59, 56, 57, 60, 61, 62, 63, 66, 67, 64, 65, 68, 69, 70, 71, 73, 72, 74, 75, 78, 79, 76, 77, 80, 81, 82, 85, 86, 83, 84, 87, 88, 89, 90, 92, 91, 93, 94, 97, 98, 95, 96, 99, 100, 101, 102, 105, 106, 103, 104, 107, 108, 109, 110, 112, 111, 113, 114, 117, 118, 115, 116, 119, 120, 161, 162, 165, 166, 163, 164, 167, 168, 169, 170, 172, 171, 173, 174, 177, 178, 175, 176, 179, 180, 181, 182, 185, 186, 183, 184, 187, 188, 189, 190, 192, 191, 193, 194, 197, 198, 195, 196, 199, 200, 121, 122, 125, 126, 123, 124, 127, 128, 129, 130, 132, 131, 133, 134, 137, 138, 135, 136, 139, 140, 141, 142, 145, 146, 143, 144, 147, 148, 149, 150, 152, 151, 153, 154, 157, 158, 155, 156, 159, 160, 201, 202, 205, 206, 203, 204, 207, 208, 209, 210, 212, 211, 213, 214, 217, 218, 215, 216, 219, 220, 221, 222, 225, 226, 223, 224, 227, 228, 229, 230, 232, 231, 233, 234, 237, 238, 235, 236, 239, 240]
def mapSw12 (j : Fin 482) : Fin 482 :=
  ⟨((if j.val < 241 then 0 else 241) + ixSw12.getD (j.val % 241) 0) % 482, Nat.mod_lt _ (by decide)⟩
def sw12 (w : W) : W := selectRows mapSw12 w
theorem sw12_invol : ∀ k : Fin 482, mapSw12 (mapSw12 k) = k := by decide +kernel
theorem sw12_goal : sw12 goal = goal := selectRows_eq mapSw12 _ _ (by decide +kernel)
theorem sw12_v0 : sw12 (v5 0) = v5 0 := selectRows_eq mapSw12 _ _ (by decide +kernel)
theorem sw12_v1 : sw12 (v5 1) = v5 2 := selectRows_eq mapSw12 _ _ (by decide +kernel)
theorem sw12_v2 : sw12 (v5 2) = v5 1 := selectRows_eq mapSw12 _ _ (by decide +kernel)
theorem sw12_v3 : sw12 (v5 3) = v5 3 := selectRows_eq mapSw12 _ _ (by decide +kernel)
theorem sw12_v4 : sw12 (v5 4) = v5 4 := selectRows_eq mapSw12 _ _ (by decide +kernel)
theorem sw12_ins5 : ∀ w ∈ ins5, sw12 w ∈ ins5 := by
  intro w hw; obtain ⟨i, rfl⟩ := input5_index w hw
  fin_cases i
  · change sw12 (v5 0) ∈ ins5; rw [sw12_v0]; simp [ins5, v5]
  · change sw12 (v5 1) ∈ ins5; rw [sw12_v1]; simp [ins5, v5]
  · change sw12 (v5 2) ∈ ins5; rw [sw12_v2]; simp [ins5, v5]
  · change sw12 (v5 3) ∈ ins5; rw [sw12_v3]; simp [ins5, v5]
  · change sw12 (v5 4) ∈ ins5; rw [sw12_v4]; simp [ins5, v5]

def ixSw04 : List ℕ := [0, 1, 121, 133, 123, 135, 125, 137, 127, 139, 129, 140, 131, 132, 122, 134, 124, 136, 126, 138, 128, 130, 161, 173, 163, 175, 165, 177, 167, 179, 169, 180, 171, 172, 162, 174, 164, 176, 166, 178, 168, 170, 42, 54, 44, 56, 46, 58, 48, 60, 50, 61, 52, 53, 43, 55, 45, 57, 47, 59, 49, 51, 201, 213, 203, 215, 205, 217, 207, 219, 209, 220, 211, 212, 202, 214, 204, 216, 206, 218, 208, 210, 93, 83, 95, 85, 97, 87, 99, 89, 100, 91, 92, 82, 94, 84, 96, 86, 98, 88, 90, 101, 113, 103, 115, 105, 117, 107, 119, 109, 120, 111, 112, 102, 114, 104, 116, 106, 118, 108, 110, 2, 14, 4, 16, 6, 18, 8, 20, 10, 21, 12, 13, 3, 15, 5, 17, 7, 19, 9, 11, 141, 153, 143, 155, 145, 157, 147, 159, 149, 160, 151, 152, 142, 154, 144, 156, 146, 158, 148, 150, 22, 34, 24, 36, 26, 38, 28, 40, 30, 41, 32, 33, 23, 35, 25, 37, 27, 39, 29, 31, 181, 193, 183, 195, 185, 197, 187, 199, 189, 200, 191, 192, 182, 194, 184, 196, 186, 198, 188, 190, 62, 74, 64, 76, 66, 78, 68, 80, 70, 81, 72, 73, 63, 75, 65, 77, 67, 79, 69, 71, 221, 233, 223, 235, 225, 237, 227, 239, 229, 240, 231, 232, 222, 234, 224, 236, 226, 238, 228, 230]
def mapSw04 (j : Fin 482) : Fin 482 :=
  ⟨((if j.val < 241 then 0 else 241) + ixSw04.getD (j.val % 241) 0) % 482, Nat.mod_lt _ (by decide)⟩
def sw04 (w : W) : W := selectRows mapSw04 w
theorem sw04_invol : ∀ k : Fin 482, mapSw04 (mapSw04 k) = k := by decide +kernel
theorem sw04_goal : sw04 goal = goal := selectRows_eq mapSw04 _ _ (by decide +kernel)
theorem sw04_v0 : sw04 (v5 0) = v5 4 := selectRows_eq mapSw04 _ _ (by decide +kernel)
theorem sw04_v1 : sw04 (v5 1) = v5 1 := selectRows_eq mapSw04 _ _ (by decide +kernel)
theorem sw04_v2 : sw04 (v5 2) = v5 2 := selectRows_eq mapSw04 _ _ (by decide +kernel)
theorem sw04_v3 : sw04 (v5 3) = v5 3 := selectRows_eq mapSw04 _ _ (by decide +kernel)
theorem sw04_v4 : sw04 (v5 4) = v5 0 := selectRows_eq mapSw04 _ _ (by decide +kernel)
theorem sw04_ins5 : ∀ w ∈ ins5, sw04 w ∈ ins5 := by
  intro w hw; obtain ⟨i, rfl⟩ := input5_index w hw
  fin_cases i
  · change sw04 (v5 0) ∈ ins5; rw [sw04_v0]; simp [ins5, v5]
  · change sw04 (v5 1) ∈ ins5; rw [sw04_v1]; simp [ins5, v5]
  · change sw04 (v5 2) ∈ ins5; rw [sw04_v2]; simp [ins5, v5]
  · change sw04 (v5 3) ∈ ins5; rw [sw04_v3]; simp [ins5, v5]
  · change sw04 (v5 4) ∈ ins5; rw [sw04_v4]; simp [ins5, v5]

def ixSw14 : List ℕ := [0, 1, 101, 102, 113, 114, 105, 106, 117, 118, 109, 110, 120, 112, 103, 104, 115, 116, 107, 108, 119, 111, 22, 23, 34, 35, 26, 27, 38, 39, 30, 31, 41, 33, 24, 25, 36, 37, 28, 29, 40, 32, 161, 162, 173, 174, 165, 166, 177, 178, 169, 170, 180, 172, 163, 164, 175, 176, 167, 168, 179, 171, 181, 182, 193, 194, 185, 186, 197, 198, 189, 190, 200, 192, 183, 184, 195, 196, 187, 188, 199, 191, 82, 93, 94, 85, 86, 97, 98, 89, 90, 100, 92, 83, 84, 95, 96, 87, 88, 99, 91, 2, 3, 14, 15, 6, 7, 18, 19, 10, 11, 21, 13, 4, 5, 16, 17, 8, 9, 20, 12, 121, 122, 133, 134, 125, 126, 137, 138, 129, 130, 140, 132, 123, 124, 135, 136, 127, 128, 139, 131, 141, 142, 153, 154, 145, 146, 157, 158, 149, 150, 160, 152, 143, 144, 155, 156, 147, 148, 159, 151, 42, 43, 54, 55, 46, 47, 58, 59, 50, 51, 61, 53, 44, 45, 56, 57, 48, 49, 60, 52, 62, 63, 74, 75, 66, 67, 78, 79, 70, 71, 81, 73, 64, 65, 76, 77, 68, 69, 80, 72, 201, 202, 213, 214, 205, 206, 217, 218, 209, 210, 220, 212, 203, 204, 215, 216, 207, 208, 219, 211, 221, 222, 233, 234, 225, 226, 237, 238, 229, 230, 240, 232, 223, 224, 235, 236, 227, 228, 239, 231]
def mapSw14 (j : Fin 482) : Fin 482 :=
  ⟨((if j.val < 241 then 0 else 241) + ixSw14.getD (j.val % 241) 0) % 482, Nat.mod_lt _ (by decide)⟩
def sw14 (w : W) : W := selectRows mapSw14 w
theorem sw14_invol : ∀ k : Fin 482, mapSw14 (mapSw14 k) = k := by decide +kernel
theorem sw14_goal : sw14 goal = goal := selectRows_eq mapSw14 _ _ (by decide +kernel)
theorem sw14_v0 : sw14 (v5 0) = v5 0 := selectRows_eq mapSw14 _ _ (by decide +kernel)
theorem sw14_v1 : sw14 (v5 1) = v5 4 := selectRows_eq mapSw14 _ _ (by decide +kernel)
theorem sw14_v2 : sw14 (v5 2) = v5 2 := selectRows_eq mapSw14 _ _ (by decide +kernel)
theorem sw14_v3 : sw14 (v5 3) = v5 3 := selectRows_eq mapSw14 _ _ (by decide +kernel)
theorem sw14_v4 : sw14 (v5 4) = v5 1 := selectRows_eq mapSw14 _ _ (by decide +kernel)
theorem sw14_ins5 : ∀ w ∈ ins5, sw14 w ∈ ins5 := by
  intro w hw; obtain ⟨i, rfl⟩ := input5_index w hw
  fin_cases i
  · change sw14 (v5 0) ∈ ins5; rw [sw14_v0]; simp [ins5, v5]
  · change sw14 (v5 1) ∈ ins5; rw [sw14_v1]; simp [ins5, v5]
  · change sw14 (v5 2) ∈ ins5; rw [sw14_v2]; simp [ins5, v5]
  · change sw14 (v5 3) ∈ ins5; rw [sw14_v3]; simp [ins5, v5]
  · change sw14 (v5 4) ∈ ins5; rw [sw14_v4]; simp [ins5, v5]

def ixSw0214 : List ℕ := [0, 1, 161, 165, 173, 177, 162, 166, 174, 178, 169, 172, 180, 170, 163, 167, 175, 179, 164, 168, 176, 171, 22, 26, 34, 38, 23, 27, 35, 39, 30, 33, 41, 31, 24, 28, 36, 40, 25, 29, 37, 32, 101, 105, 113, 117, 102, 106, 114, 118, 109, 112, 120, 110, 103, 107, 115, 119, 104, 108, 116, 111, 181, 185, 193, 197, 182, 186, 194, 198, 189, 192, 200, 190, 183, 187, 195, 199, 184, 188, 196, 191, 85, 93, 97, 82, 86, 94, 98, 89, 92, 100, 90, 83, 87, 95, 99, 84, 88, 96, 91, 42, 46, 54, 58, 43, 47, 55, 59, 50, 53, 61, 51, 44, 48, 56, 60, 45, 49, 57, 52, 121, 125, 133, 137, 122, 126, 134, 138, 129, 132, 140, 130, 123, 127, 135, 139, 124, 128, 136, 131, 201, 205, 213, 217, 202, 206, 214, 218, 209, 212, 220, 210, 203, 207, 215, 219, 204, 208, 216, 211, 2, 6, 14, 18, 3, 7, 15, 19, 10, 13, 21, 11, 4, 8, 16, 20, 5, 9, 17, 12, 62, 66, 74, 78, 63, 67, 75, 79, 70, 73, 81, 71, 64, 68, 76, 80, 65, 69, 77, 72, 141, 145, 153, 157, 142, 146, 154, 158, 149, 152, 160, 150, 143, 147, 155, 159, 144, 148, 156, 151, 221, 225, 233, 237, 222, 226, 234, 238, 229, 232, 240, 230, 223, 227, 235, 239, 224, 228, 236, 231]
def mapSw0214 (j : Fin 482) : Fin 482 :=
  ⟨((if j.val < 241 then 0 else 241) + ixSw0214.getD (j.val % 241) 0) % 482, Nat.mod_lt _ (by decide)⟩
def sw0214 (w : W) : W := selectRows mapSw0214 w
theorem sw0214_invol : ∀ k : Fin 482, mapSw0214 (mapSw0214 k) = k := by decide +kernel
theorem sw0214_goal : sw0214 goal = goal := selectRows_eq mapSw0214 _ _ (by decide +kernel)
theorem sw0214_v0 : sw0214 (v5 0) = v5 2 := selectRows_eq mapSw0214 _ _ (by decide +kernel)
theorem sw0214_v1 : sw0214 (v5 1) = v5 4 := selectRows_eq mapSw0214 _ _ (by decide +kernel)
theorem sw0214_v2 : sw0214 (v5 2) = v5 0 := selectRows_eq mapSw0214 _ _ (by decide +kernel)
theorem sw0214_v3 : sw0214 (v5 3) = v5 3 := selectRows_eq mapSw0214 _ _ (by decide +kernel)
theorem sw0214_v4 : sw0214 (v5 4) = v5 1 := selectRows_eq mapSw0214 _ _ (by decide +kernel)
theorem sw0214_ins5 : ∀ w ∈ ins5, sw0214 w ∈ ins5 := by
  intro w hw; obtain ⟨i, rfl⟩ := input5_index w hw
  fin_cases i
  · change sw0214 (v5 0) ∈ ins5; rw [sw0214_v0]; simp [ins5, v5]
  · change sw0214 (v5 1) ∈ ins5; rw [sw0214_v1]; simp [ins5, v5]
  · change sw0214 (v5 2) ∈ ins5; rw [sw0214_v2]; simp [ins5, v5]
  · change sw0214 (v5 3) ∈ ins5; rw [sw0214_v3]; simp [ins5, v5]
  · change sw0214 (v5 4) ∈ ins5; rw [sw0214_v4]; simp [ins5, v5]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_01_0 : checkFirstN 7 ((ops (v5 0) (v5 1)).getD 0 0).toNat (ins5.map BitVec.toNat) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_01_1 : checkFirstN 7 ((ops (v5 0) (v5 1)).getD 1 0).toNat (ins5.map BitVec.toNat) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_01_2 : checkFirstN 7 ((ops (v5 0) (v5 1)).getD 2 0).toNat (ins5.map BitVec.toNat) = false := by decide +kernel

theorem kill_01 {t : W} (ht : t = goal ∨ t = ~~~goal) {z : W} (hz : z ∈ basicOps (v5 0) (v5 1))
    (rest : Finset W) (hsub : rest ⊆ ins5.toFinset) (tail : live basicOps t 7 (insert z rest)) : False := by
  obtain ⟨o, ho⟩ := index_of_op _ _ _ hz
  rw [← ho] at tail
  fin_cases o
  · exact Bool.noConfusion (reject_01_0.symm.trans (checkFirstN_complete ht 7 _ ins5 ins5_nd hsub tail))
  · exact Bool.noConfusion (reject_01_1.symm.trans (checkFirstN_complete ht 7 _ ins5 ins5_nd hsub tail))
  · exact Bool.noConfusion (reject_01_2.symm.trans (checkFirstN_complete ht 7 _ ins5 ins5_nd hsub tail))
  · have htl := live_image (selectRows_ops mapSw01) (selectRows_invol mapSw01 sw01_invol) tail
    rw [Finset.image_insert] at htl
    have hzw : sw01 ((ops (v5 0) (v5 1)).getD 3 0) = (ops (v5 0) (v5 1)).getD 2 0 := by
      change selectRows mapSw01 (v5 1 &&& ~~~v5 0) = v5 0 &&& ~~~v5 1
      rw [selectRows_and, selectRows_not]
      exact congrArg₂ (fun a b => a &&& ~~~b) sw01_v1 sw01_v0
    change live basicOps (sw01 t) 7 (insert (sw01 ((ops (v5 0) (v5 1)).getD 3 0)) (rest.image sw01)) at htl
    rw [hzw] at htl
    have hsub' : rest.image sw01 ⊆ ins5.toFinset := by
      intro w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      exact List.mem_toFinset.mpr (sw01_ins5 u (List.mem_toFinset.mp (hsub hu)))
    have hft := restrict_goal_signs (selectRows_not mapSw01) sw01_goal ht
    exact Bool.noConfusion (reject_01_2.symm.trans (checkFirstN_complete hft 7 _ ins5 ins5_nd hsub' htl))

set_option maxRecDepth 8000 in
theorem kill_01_via (m : Fin 482 → Fin 482) (hm : ∀ k, m (m k) = k)
    (hfg : selectRows m goal = goal) (hfins : ∀ w ∈ ins5, selectRows m w ∈ ins5)
    {a b : W} (ha : selectRows m a = v5 0) (hb : selectRows m b = v5 1)
    {t : W} (ht : t = goal ∨ t = ~~~goal) {z : W} (hz : z ∈ basicOps a b)
    (rest : Finset W) (hsub : rest ⊆ ins5.toFinset)
    (tail : live basicOps t 7 (insert z rest)) : False := by
  have hfz : selectRows m z ∈ basicOps (v5 0) (v5 1) := ha ▸ hb ▸ selectRows_ops m a b z hz
  have htl : live basicOps (selectRows m t) 7 (insert (selectRows m z) (rest.image (selectRows m))) := by
    have h1 := live_image (selectRows_ops m) (selectRows_invol m hm) tail
    rwa [Finset.image_insert] at h1
  have hsub' : rest.image (selectRows m) ⊆ ins5.toFinset := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact List.mem_toFinset.mpr (hfins u (List.mem_toFinset.mp (hsub hu)))
  exact kill_01 (restrict_goal_signs (selectRows_not m) hfg ht) hfz (rest.image (selectRows m)) hsub' htl

theorem no_eight_ins5 (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 8 ins5.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 7) hl with endcase | ⟨a, ha, b, hb, hab, z, hz, _, rest, he, tail⟩
  · have tx : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := input5_index _ (List.mem_toFinset.mp (hs tx))
    rcases ht with rfl | rfl
    · exact (input5_not_goal i).1 hi
    · exact (input5_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := input5_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := input5_index _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg v5 eq)
    have sub : rest ⊆ ins5.toFinset := fun u hu =>
      hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    by_cases hi3 : i = 3
    · subst hi3; exact kill_case_3 ht j (Ne.symm hij) hz rest sub tail
    by_cases hj3 : j = 3
    · subst hj3; exact kill_case_3 ht i hij (ops_swap _ _ ▸ hz) rest sub tail
    fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
    all_goals try exact absurd rfl hi3
    all_goals try exact absurd rfl hj3
    · exact kill_01 ht hz rest sub tail
    · exact kill_01_via mapSw12 sw12_invol sw12_goal sw12_ins5 sw12_v0 sw12_v2 ht hz rest sub tail
    · exact kill_01_via mapSw14 sw14_invol sw14_goal sw14_ins5 sw14_v0 sw14_v4 ht hz rest sub tail
    · exact kill_01 ht (ops_swap _ _ ▸ hz) rest sub tail
    · exact kill_01_via mapSw02 sw02_invol sw02_goal sw02_ins5 sw02_v2 sw02_v1 ht (ops_swap _ _ ▸ hz) rest sub tail
    · exact kill_01_via mapSw04 sw04_invol sw04_goal sw04_ins5 sw04_v4 sw04_v1 ht (ops_swap _ _ ▸ hz) rest sub tail
    · exact kill_01_via mapSw12 sw12_invol sw12_goal sw12_ins5 sw12_v0 sw12_v2 ht (ops_swap _ _ ▸ hz) rest sub tail
    · exact kill_01_via mapSw02 sw02_invol sw02_goal sw02_ins5 sw02_v2 sw02_v1 ht hz rest sub tail
    · exact kill_01_via mapSw0214 sw0214_invol sw0214_goal sw0214_ins5 sw0214_v2 sw0214_v4 ht hz rest sub tail
    · exact kill_01_via mapSw14 sw14_invol sw14_goal sw14_ins5 sw14_v0 sw14_v4 ht (ops_swap _ _ ▸ hz) rest sub tail
    · exact kill_01_via mapSw04 sw04_invol sw04_goal sw04_ins5 sw04_v4 sw04_v1 ht hz rest sub tail
    · exact kill_01_via mapSw0214 sw0214_invol sw0214_goal sw0214_ins5 sw0214_v2 sw0214_v4 ht (ops_swap _ _ ▸ hz) rest sub tail

theorem no_nine_binary (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 9 ins6.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  have hd : differs ⟨0, by decide⟩ t :=
    ht.elim (fun h => h ▸ (goal_changes ⟨0, by decide⟩).1) (fun h => h ▸ (goal_changes ⟨0, by decide⟩).2)
  obtain ⟨w, hw, hdw⟩ := live_separates (differs ⟨0, by decide⟩) hd (ops_differs ⟨0, by decide⟩) hl
  obtain ⟨q, rfl⟩ := input6_index _ (List.mem_toFinset.mp (hs hw))
  have hq5 : q = 5 := by
    by_contra hne
    exact unchanged _ _ (pair0_only_x5 q hne) hdw
  subst hq5
  have pg : v6 5 ≠ t := ht.elim (fun h => h ▸ (input6_not_goal 5).1) (fun h => h ▸ (input6_not_goal 5).2)
  have hsb : SignedBuild 8 ins5.toFinset (restrict5 t) := by
    apply live_transport_save (selectRows_ops map5) hl hw pg (Or.inr restrict5_v5)
    intro u hu
    obtain ⟨k, rfl⟩ := input6_index _ (List.mem_toFinset.mp (hs hu))
    exact restrict5_avail k
  have signs : restrict5 t = goal ∨ restrict5 t = ~~~goal :=
    restrict_goal_signs (selectRows_not map5) restrict5_goal ht
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  rcases hsb with c | c | run5 | run5
  · rcases signs with h | h
    · exact ne.1 (h.symm.trans c)
    · exact ne.2.2.1 (h.symm.trans c)
  · rcases signs with h | h
    · exact ne.2.1 (h.symm.trans c)
    · exact ne.2.2.2 (h.symm.trans c)
  · exact no_eight_ins5 _ signs run5
  · exact no_eight_ins5 _ (signs.elim (fun h => Or.inr (by rw [h])) (fun h => Or.inl (by rw [h, BitVec.not_not]))) run5

theorem ten_binary (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = table x) :
    9 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins6, holds ins6.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 482) :
      (gs.foldl step (ins6.map (bit k))).getD o false = bit k goal := by
    have same : List.ofFn (fun i : Fin 6 => bit k (ins6.getD i.val 0)) =
        ins6.map (bit k) := by
      apply List.ext_getElem (by simp [ins6])
      intro i hi hj
      have hlt : i < ins6.length := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (ins6.map (bit k)) = bit k goal
    rw [← same, he]
    exact spec_table k
  obtain ⟨t, ht, run⟩ := compile gs o hg ins6 ins6.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins6.toFinset) :
      build basicOps t b ins6.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_nine_binary t ht (lift low run)

def witness : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [4, 10]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [11, 14]⟩, ⟨.and, [13, 15]⟩], 16⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

set_option maxRecDepth 8000 in
theorem witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = table x := by
  decide +kernel

theorem monotone_replacement (s : ℕ) (C : Circuit) (hC : FanInTwo C) (hs : C.size ≤ s)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = table x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧ ∀ x : Fin 6 → Bool, D.eval (List.ofFn x) = table x := by
  by_cases present : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hm, hn⟩ := present
    have cut : binaryCost C.gates < C.size :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, hm, by simp [isBinary, hn]⟩
    have ten := ten_binary C.gates C.output hC he
    exact ⟨witness, witness_mono, by change 11 ≤ s; omega, witness_eval⟩
  · exact ⟨C, fun g hg => ⟨(hC g hg).1.imp_right (·.resolve_right fun h => present ⟨g, hg, h⟩),
      (hC g hg).2⟩, hs, he⟩

end PEqualNP.Outside.L_meta_12074

theorem PEqualNP.Outside.L_meta_12074 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860864 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, hC, hs, he⟩
  exact PEqualNP.Outside.L_meta_12074.monotone_replacement s C hC hs he
