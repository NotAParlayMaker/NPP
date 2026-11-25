import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17160

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

section MonotoneLive

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

end MonotoneLive

abbrev W := BitVec 64

def mOps (x y : W) : List W := [x &&& y, x ||| y]
def sepM (x : W) : BitVec 32 := (x &&& ~~~(x >>> 32)).setWidth 32
def cutsM (ws : List W) : BitVec 32 := ws.foldr (fun w v => sepM w ||| v) 0
def mGoal : W := (0 : BitVec 32) ++ (-1 : BitVec 32)

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

abbrev monoOps (a b : W) : Finset W := (mOps a b).toFinset

def posSep (i : Fin 32) (w : W) : Prop :=
  w.getLsbD i.val = true ∧ w.getLsbD (32 + i.val) = false

theorem ops_posSep (i : Fin 32) (a b z : W) (hz : z ∈ monoOps a b)
    (hd : posSep i z) : posSep i a ∨ posSep i b := by
  simp only [monoOps, mOps, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  obtain ⟨h1, h2⟩ := hd
  rcases hz with rfl | rfl
  · simp only [BitVec.getLsbD_and, Bool.and_eq_true, Bool.and_eq_false_iff] at h1 h2
    rcases h2 with h2 | h2
    · exact Or.inl ⟨h1.1, h2⟩
    · exact Or.inr ⟨h1.2, h2⟩
  · simp only [BitVec.getLsbD_or, Bool.or_eq_true, Bool.or_eq_false_iff] at h1 h2
    rcases h1 with h1 | h1
    · exact Or.inl ⟨h1, h2.1⟩
    · exact Or.inr ⟨h1, h2.2⟩

theorem cutsM_spec (ws : List W) (i : Fin 32) :
    (cutsM ws).getLsbD i.val = true ↔ ∃ w ∈ ws, posSep i w := by
  induction ws with
  | nil => simp [cutsM]
  | cons a rest ih =>
    change (sepM a ||| cutsM rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 32 := i.isLt
    have hi2 : i.val < 64 := by omega
    have hi3 : 32 + i.val < 64 := by omega
    simp [sepM, posSep, hi, hi2, hi3, Nat.add_comm]

theorem cutsM_full {k : ℕ} {ws : List W} (h : live monoOps mGoal k ws.toFinset) :
    cutsM ws = -1 := by
  have hd : ∀ i : Fin 32, posSep i mGoal := by unfold posSep mGoal; decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (posSep ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops_posSep ⟨j, hj⟩) h
  have hbit := (cutsM_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cutsM ws)[j] = (BitVec.allOnes 32)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem monoOps_swap (a b : W) : monoOps a b = monoOps b a := by
  ext z
  simp only [monoOps, mOps, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]

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

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatchM (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cutsM r
  (mOps a b).any fun w =>
    let v := sepM w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sepM a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sepM b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sepM a ||| sepM b == -1) && next (extra - 2) (w :: a :: b :: r))

def optM : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [mGoal]
  | k + 1, extra, ws => (ws == [mGoal]) ||
    (pairs ws).any (fun (a, b, r) => dispatchM extra (optM k) a b r)

theorem dispatchM_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ monoOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cutsM (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatchM extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cutsM, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optM_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live monoOps mGoal n ws.toFinset) :
    optM n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optM, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optM, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ monoOps a b) :
          dispatchM extra (optM k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu; apply hout; rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live monoOps mGoal k (z :: kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatchM_complete (k := k) (extra := extra) (optM k) hop hk (by omega) (by omega) (cutsM_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optM, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (monoOps_swap a b ▸ hz)⟩

def searchM (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (cutsM ws == -1) && optM n (n + 1 - ws.length) ws

theorem searchM_complete (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build monoOps mGoal n inputs.toFinset) : searchM n inputs = true := by
  classical
  obtain ⟨s, hs, hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live monoOps mGoal n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws, List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cutsM_full hl', optM_complete n ws _ hnd (by omega : n + 1 - ws.length + ws.length = n + 1) hl']⟩

def c6Rows : List W :=
  [0xca5294a5c00003ff, 0xd294a529000ffc00, 0xe318c6313ff00000,
   0x0c6318c601f07c00, 0x14a5294afe00001f, 0x25294a52000f83e0]

theorem c6_reject : searchM 7 c6Rows = false := by
  decide +kernel

theorem c6_rows_nodup : c6Rows.Nodup := by
  decide +kernel

theorem c6_sample_ok : ∀ k : Fin 64,
    decide (∃ i j : Fin 3, i ≠ j ∧
      (c6Rows.getD i.val 0)[k.val] = true ∧ (c6Rows.getD (3 + j.val) 0)[k.val] = true) =
    mGoal[k.val] := by
  decide +kernel

def mHolds (av : Finset W) (z : W) : Prop := z = 0 ∨ z ∈ av

theorem mHolds_insert {av : Finset W} {z a : W} (h : mHolds av z) : mHolds (insert a av) z :=
  h.imp id (Finset.mem_insert_of_mem)

def mReach (av : Finset W) (z : W) : Prop :=
  mHolds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ monoOps a b, mHolds (insert w av) z

theorem mAnd_reach {av : Finset W} {x y : W} (hx : mHolds av x) (hy : mHolds av y) :
    mReach av (x &&& y) := by
  rcases hx with rfl | hx
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl (.inl rfl)
  rcases hy with rfl | hy
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl (.inl rfl)
  by_cases h : x = y
  · subst y; rw [BitVec.and_self]; exact .inl (.inr hx)
  · exact .inr ⟨x, hx, y, hy, h, x &&& y, by simp [monoOps, mOps], .inr (Finset.mem_insert_self ..)⟩

theorem mOr_reach {av : Finset W} {x y : W} (hx : mHolds av x) (hy : mHolds av y) :
    mReach av (x ||| y) := by
  rcases hx with rfl | hx
  · rw [show (0 : W) ||| y = y from BitVec.zero_or]; exact .inl hy
  rcases hy with rfl | hy
  · rw [show x ||| (0 : W) = x from BitVec.or_zero]; exact .inl (.inr hx)
  by_cases h : x = y
  · subst y; rw [BitVec.or_self]; exact .inl (.inr hx)
  · exact .inr ⟨x, hx, y, hy, h, x ||| y, by simp [monoOps, mOps], .inr (Finset.mem_insert_self ..)⟩

def bit (k : Fin 64) (z : W) : Bool := z[k.val]
def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def mAction (w : List W) (g : Gate) : W :=
  match g.op, g.inputs with
  | .and, [a, b] => w.getD a 0 &&& w.getD b 0
  | .or, [a, b] => w.getD a 0 ||| w.getD b 0
  | _, _ => 0

theorem mAction_spec (w : List W) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length = 2) (k : Fin 64) :
    stepB (w.map (bit k)) g = (w ++ [mAction w g]).map (bit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  rcases hop with rfl | rfl <;>
    simp only [stepB, mAction, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      List.any_cons, List.any_nil, Bool.and_true, Bool.or_false, List.map_append,
      read_bit, bit, BitVec.getElem_and, BitVec.getElem_or, id_eq]

theorem mCompile (gs : List Gate) (out : ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, mHolds av u)
    (he : ∀ k : Fin 64, (gs.foldl stepB (w.map (bit k))).getD out false = bit k mGoal) :
    build monoOps mGoal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = mGoal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hread : mHolds av (w.getD out 0) := by
      by_cases h : out < w.length
      · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]; exact .inl rfl
    rw [hv] at hread
    rcases hread with h0 | hm
    · exact False.elim ((by decide : mGoal ≠ 0) h0)
    · exact hm
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    let z := mAction w g
    have stepOK := mAction_spec w g hop hlen
    have nextEval : ∀ k, (gs.foldl stepB ((w ++ [z]).map (bit k))).getD out false = bit k mGoal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have hread : ∀ i, mHolds av (w.getD i 0) := fun i => by
      by_cases h : i < w.length
      · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]; exact .inl rfl
    have hreach : mReach av z := by
      cases g with | mk op args =>
      simp only at hop hab
      subst hab
      rcases hop with rfl | rfl
      · exact mAnd_reach (hread a) (hread b)
      · exact mOr_reach (hread a) (hread b)
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    rcases hreach with hex | ⟨u, hu, v, hv, hne, nw, hnw, hhold⟩
    · apply Or.inl
      exact tail av (fun t ht => (List.mem_append.mp ht).elim (hw t) (fun hs => (List.mem_singleton.mp hs) ▸ hex)) nextEval
    · refine Or.inr ⟨u, hu, v, hv, hne, nw, hnw, ?_⟩
      exact tail (insert nw av)
        (fun t ht => (List.mem_append.mp ht).elim (fun h => mHolds_insert (hw t h)) (fun hs => (List.mem_singleton.mp hs) ▸ hhold))
        nextEval

theorem lift_build {ops : W → W → Finset W} {g : W} {a b : ℕ} {av : Finset W}
    (h : a ≤ b) (hb : build ops g a av) : build ops g b av := by
  induction h with
  | refl => exact hb
  | step _ ih => exact Or.inl ih

theorem c6_base (m : ℕ) (core : Fin 3 → Fin m) (hInj : Function.Injective core)
    (E : Finset (Fin 3 × Fin m))
    (hE : ∀ p : Fin 3, ∀ q : Fin m, (p, q) ∈ E ↔ ∃ i : Fin 3, q = core i ∧ p ≠ i)
    (C : Circuit) (hAO : IsAO2 (3 + m) C)
    (hFun : ∀ x : Fin (3 + m) → Bool, circuitFun (3 + m) C x =
      decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd 3 e.2) = true)) :
    8 ≤ C.size := by
  classical
  by_contra! hlt
  have hle7 : C.gates.length ≤ 7 := by delta Circuit.size at hlt; omega
  let inpW : List W := List.ofFn fun u : Fin (3 + m) =>
    if h : u.val < 3 then c6Rows.getD u.val 0
    else if h0 : (⟨u.val - 3, by omega⟩ : Fin m) = core 0 then c6Rows.getD 3 0
    else if h1 : (⟨u.val - 3, by omega⟩ : Fin m) = core 1 then c6Rows.getD 4 0
    else if h2 : (⟨u.val - 3, by omega⟩ : Fin m) = core 2 then c6Rows.getD 5 0
    else 0
  have hmem : ∀ w ∈ inpW, mHolds c6Rows.toFinset w := by
    intro w hw
    simp only [inpW, List.mem_ofFn, Set.mem_range] at hw
    obtain ⟨u, rfl⟩ := hw
    have hc : ∀ idx < 6, c6Rows.getD idx 0 ∈ c6Rows.toFinset := fun idx hidx => by
      rw [List.mem_toFinset, List.getD_eq_getElem _ _ (by simp [c6Rows]; omega)]
      exact List.getElem_mem _
    split_ifs
    · exact .inr (hc _ (by omega))
    · exact .inr (hc 3 (by omega))
    · exact .inr (hc 4 (by omega))
    · exact .inr (hc 5 (by omega))
    · exact .inl rfl
  have heval : ∀ k : Fin 64,
      (C.gates.foldl stepB (inpW.map (bit k))).getD C.output false = bit k mGoal := by
    intro k
    let x : Fin (3 + m) → Bool := fun u => bit k (inpW.getD u.val 0)
    have hmap : inpW.map (bit k) = List.ofFn x := by
      apply List.ext_getElem
      · simp [inpW]
      · intro i hi hj
        have hi' : i < inpW.length := by simpa using hi
        simp only [List.getElem_map, List.getElem_ofFn, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hi', Option.getD_some]
    change Circuit.eval C (inpW.map (bit k)) = mGoal[k.val]
    rw [hmap]
    change circuitFun (3 + m) C x = mGoal[k.val]
    rw [hFun x, ← c6_sample_ok k]
    congr 1
    apply propext
    have hLeft : ∀ p : Fin 3, x (Fin.castAdd m p) = (c6Rows.getD p.val 0)[k.val] := by
      intro p
      simp [x, inpW, bit, List.getD_eq_getElem?_getD, p.isLt]
    have hRight : ∀ i : Fin 3, x (Fin.natAdd 3 (core i)) = (c6Rows.getD (3 + i.val) 0)[k.val] := by
      intro i
      have hne : ¬ (3 + (core i).val < 3) := by omega
      have hsub : (⟨3 + (core i).val - 3, by omega⟩ : Fin m) = core i := by ext; simp
      fin_cases i
      · simp [x, inpW, bit, List.getD_eq_getElem?_getD, hne, hsub]
      · have h10 : core 1 ≠ core 0 := fun h => by have := hInj h; cases this
        simp [x, inpW, bit, List.getD_eq_getElem?_getD, hne, hsub, h10]
      · have h20 : core 2 ≠ core 0 := fun h => by have := hInj h; cases this
        have h21 : core 2 ≠ core 1 := fun h => by have := hInj h; cases this
        simp [x, inpW, bit, List.getD_eq_getElem?_getD, hne, hsub, h20, h21]
    constructor
    · rintro ⟨⟨p, q⟩, he, hp, hq⟩
      obtain ⟨i, rfl, hpi⟩ := (hE p q).mp he
      exact ⟨p, i, hpi, hLeft p ▸ hp, hRight i ▸ hq⟩
    · rintro ⟨p, i, hpi, hp, hq⟩
      exact ⟨(p, core i), (hE p (core i)).mpr ⟨i, rfl, hpi⟩,
        (hLeft p).symm ▸ hp, (hRight i).symm ▸ hq⟩
  have hbuild := mCompile C.gates C.output
    (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩) inpW c6Rows.toFinset hmem heval
  have htrue := searchM_complete 7 c6Rows c6_rows_nodup (lift_build hle7 hbuild)
  rw [c6_reject] at htrue
  cases htrue

def restrictStep (n : ℕ) (st : List Gate × List (Option ℕ)) (g : Gate) :
    List Gate × List (Option ℕ) :=
  let (gs', mp) := st
  match g.op, g.inputs with
  | .and, [a, b] =>
    match mp.getD a none, mp.getD b none with
    | some a', some b' => (gs' ++ [⟨.and, [a', b']⟩], mp ++ [some (n + gs'.length)])
    | _, _ => (gs', mp ++ [none])
  | .or, [a, b] =>
    match mp.getD a none, mp.getD b none with
    | none, mb => (gs', mp ++ [mb])
    | ma, none => (gs', mp ++ [ma])
    | some a', some b' => (gs' ++ [⟨.or, [a', b']⟩], mp ++ [some (n + gs'.length)])
  | _, _ => (gs', mp ++ [none])

def initMap (n w0 : ℕ) : List (Option ℕ) :=
  List.ofFn fun i : Fin n => if i.val = w0 then none else some i.val

def restrictCircuit (n w0 : ℕ) (C : Circuit) : Circuit :=
  let res := C.gates.foldl (restrictStep n) ([], initMap n w0)
  ⟨res.1, (res.2.getD C.output none).getD (n + res.1.length)⟩

def valC (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem foldl_stepB_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepB w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepB]; omega

theorem foldl_stepB_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepB w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepB w g) (by simp [stepB]; omega)]
    simp [stepB, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def GoodState (n : ℕ) (x x' : List Bool) (w : List Bool) (st : List Gate × List (Option ℕ)) : Prop :=
  st.2.length = w.length ∧
  AndOrOnly ⟨st.1, 0⟩ ∧
  ReadsBack n ⟨st.1, 0⟩ ∧
  (∀ g ∈ st.1, g.inputs.length = 2) ∧
  (∀ u, ∀ r, st.2.getD u none = some r → r < n + st.1.length) ∧
  (∀ u < w.length, w.getD u false =
    match st.2.getD u none with
    | none => false
    | some r => (st.1.foldl stepB x).getD r false)

theorem getD_append_lt {α : Type} (l : List α) (v d : α) (u : ℕ) (hu : u < l.length) :
    (l ++ [v]).getD u d = l.getD u d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hu]

theorem getD_append_eq {α : Type} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

theorem getD_append_gt {α : Type} (l : List α) (v d : α) (u : ℕ) (hu : l.length < u) :
    (l ++ [v]).getD u d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
  rfl

theorem bound_append {mp : List (Option ℕ)} {k : ℕ} {val : Option ℕ}
    (hbound : ∀ u r, mp.getD u none = some r → r < k)
    (hval : ∀ r, val = some r → r < k) :
    ∀ u r, (mp ++ [val]).getD u none = some r → r < k := by
  intro u r hr
  rcases Nat.lt_trichotomy u mp.length with h | rfl | h
  · rw [getD_append_lt mp val none u h] at hr; exact hbound u r hr
  · rw [getD_append_eq mp val none] at hr; exact hval r hr
  · rw [getD_append_gt mp val none u h] at hr; cases hr

theorem restrict_step_good {n : ℕ} {x x' : List Bool} (hx : x.length = n)
    {w : List Bool} {st : List Gate × List (Option ℕ)} {g : Gate}
    (hG : GoodState n x x' w st)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length = 2)
    (hrb : ∀ i ∈ g.inputs, i < w.length) :
    GoodState n x x' (stepB w g) (restrictStep n st g) ∧
    (restrictStep n st g).1.length ≤ st.1.length + 1 ∧
    ((∃ i ∈ g.inputs, st.2.getD i none = none) → (restrictStep n st g).1.length = st.1.length) := by
  obtain ⟨gs', mp⟩ := st
  dsimp only [GoodState] at hG
  obtain ⟨hmlen, hao, hrb', h2', hbound, heval⟩ := hG
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have ha_lt : a < w.length := hrb a (by rw [hab]; simp)
  have hb_lt : b < w.length := hrb b (by rw [hab]; simp)
  have ha_val := heval a ha_lt
  have hb_val := heval b hb_lt
  have hge_eval : ∀ r, (gs'.foldl stepB x).getD r false = (gs'.foldl stepB x).getD r false := fun _ => rfl
  have hstep_append (gnew : Gate) (hnew_op : gnew.op = .and ∨ gnew.op = .or)
      (hnew_in : ∃ a' b', gnew.inputs = [a', b'] ∧ a' < n + gs'.length ∧ b' < n + gs'.length) :
      AndOrOnly ⟨gs' ++ [gnew], 0⟩ ∧ ReadsBack n ⟨gs' ++ [gnew], 0⟩ ∧
      (∀ g0 ∈ gs' ++ [gnew], g0.inputs.length = 2) := by
    obtain ⟨a', b', hin, ha', hb'⟩ := hnew_in
    refine ⟨?_, ?_, ?_⟩
    · intro g0 hg0
      rcases List.mem_append.mp hg0 with h1 | h1
      · exact hao g0 h1
      · rw [List.mem_singleton.mp h1]; exact hnew_op
    · intro k hk i hi
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hlt : k < gs'.length
      · have hgat : gateAt ⟨gs' ++ [gnew], 0⟩ k = gateAt ⟨gs', 0⟩ k := by
          simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        rw [hgat] at hi
        exact hrb' k hlt i hi
      · have hk' : k = gs'.length := by omega
        subst hk'
        have hgat : gateAt ⟨gs' ++ [gnew], 0⟩ gs'.length = gnew := by simp [gateAt]
        rw [hgat, hin] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
    · intro g0 hg0
      rcases List.mem_append.mp hg0 with h1 | h1
      · exact h2' g0 h1
      · rw [List.mem_singleton.mp h1, hin]; rfl
  have hstep_wires (gnew : Gate) :
      (gs' ++ [gnew]).foldl stepB x = stepB (gs'.foldl stepB x) gnew := by
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen_w : (gs'.foldl stepB x).length = n + gs'.length := by
    rw [foldl_stepB_len, hx]
  have hold_keep (gnew : Gate) (u : ℕ) (hu : u < w.length) (r : ℕ) (hr : mp.getD u none = some r) :
      (gs'.foldl stepB x).getD r false = ((gs' ++ [gnew]).foldl stepB x).getD r false := by
    rw [hstep_wires]
    have hrlt : r < (gs'.foldl stepB x).length := by rw [hlen_w]; exact hbound u r hr
    simp [stepB, List.getD_eq_getElem?_getD, List.getElem?_append_left hrlt]
  cases g with | mk op inputs =>
  simp only at hop hab
  subst hab
  rcases hop with rfl | rfl
  ·
    cases hma : mp.getD a none with
    | none =>
      simp only [restrictStep, hma]
      refine ⟨⟨by simp [stepB, hmlen], hao, hrb', h2',
        bound_append hbound (fun _ h => by cases h), ?_⟩, by omega, fun _ => trivial⟩
      intro u hu
      simp only [stepB, List.length_append, List.length_singleton] at hu
      simp only [stepB]
      by_cases hlt : u < w.length
      · rw [getD_append_lt mp none none u (by omega), getD_append_lt w _ false u hlt]; exact heval u hlt
      · have hu' : u = w.length := by omega
        subst hu'
        rw [← hmlen, getD_append_eq, hmlen, getD_append_eq]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
          Bool.and_true, ha_val, hma, Bool.false_and]
    | some a' =>
      cases hmb : mp.getD b none with
      | none =>
        simp only [restrictStep, hma, hmb]
        refine ⟨⟨by simp [stepB, hmlen], hao, hrb', h2',
          bound_append hbound (fun _ h => by cases h), ?_⟩, by omega, fun _ => trivial⟩
        intro u hu
        simp only [stepB, List.length_append, List.length_singleton] at hu
        simp only [stepB]
        by_cases hlt : u < w.length
        · rw [getD_append_lt mp none none u (by omega), getD_append_lt w _ false u hlt]; exact heval u hlt
        · have hu' : u = w.length := by omega
          subst hu'
          rw [← hmlen, getD_append_eq, hmlen, getD_append_eq]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
            Bool.and_true, hb_val, hmb, Bool.and_false]
      | some b' =>
        simp only [restrictStep, hma, hmb]
        have ha'_lt : a' < n + gs'.length := hbound a a' hma
        have hb'_lt : b' < n + gs'.length := hbound b b' hmb
        obtain ⟨hao2, hrb2, h22⟩ := hstep_append (⟨.and, [a', b']⟩ : Gate) (.inl rfl) ⟨a', b', rfl, ha'_lt, hb'_lt⟩
        have hbnd2 : ∀ u r, (mp ++ [some (n + gs'.length)]).getD u none = some r →
            r < n + (gs' ++ [(⟨.and, [a', b']⟩ : Gate)]).length :=
          bound_append (fun u r hr => by have := hbound u r hr; simp; omega)
            (fun r hr => by injection hr with hr'; simp; omega)
        refine ⟨⟨by simp [stepB, hmlen], hao2, hrb2, h22, hbnd2, ?_⟩, by simp, ?_⟩
        · intro u hu
          simp only [stepB, List.length_append, List.length_singleton] at hu
          simp only [stepB]
          by_cases hlt : u < w.length
          · rw [getD_append_lt mp _ none u (by omega), getD_append_lt w _ false u hlt, heval u hlt]
            cases hmu : mp.getD u none with
            | none => rfl
            | some r => exact hold_keep ⟨.and, [a', b']⟩ u hlt r hmu
          · have hu' : u = w.length := by omega
            subst hu'
            rw [← hmlen, getD_append_eq, hmlen, getD_append_eq, hstep_wires]
            simp only [stepB]
            rw [← hlen_w, getD_append_eq]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
              Bool.and_true, ha_val, hb_val, hma, hmb]
        · rintro ⟨i, hi, hnone⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · rw [hma] at hnone; cases hnone
          · rw [hmb] at hnone; cases hnone
  ·
    cases hma : mp.getD a none with
    | none =>
      simp only [restrictStep, hma]
      refine ⟨⟨by simp [stepB, hmlen], hao, hrb', h2',
        bound_append hbound (fun r hr => hbound b r hr), ?_⟩, by omega, fun _ => trivial⟩
      intro u hu
      simp only [stepB, List.length_append, List.length_singleton] at hu
      simp only [stepB]
      by_cases hlt : u < w.length
      · rw [getD_append_lt mp _ none u (by omega), getD_append_lt w _ false u hlt]; exact heval u hlt
      · have hu' : u = w.length := by omega
        subst hu'
        rw [← hmlen, getD_append_eq, hmlen, getD_append_eq]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
          Bool.or_false, ha_val, hb_val, hma, Bool.false_or]
    | some a' =>
      cases hmb : mp.getD b none with
      | none =>
        simp only [restrictStep, hma, hmb]
        refine ⟨⟨by simp [stepB, hmlen], hao, hrb', h2',
          bound_append hbound (fun r hr => by injection hr with hr'; subst hr'; exact hbound a a' hma), ?_⟩, by omega, fun _ => trivial⟩
        intro u hu
        simp only [stepB, List.length_append, List.length_singleton] at hu
        simp only [stepB]
        by_cases hlt : u < w.length
        · rw [getD_append_lt mp _ none u (by omega), getD_append_lt w _ false u hlt]; exact heval u hlt
        · have hu' : u = w.length := by omega
          subst hu'
          rw [← hmlen, getD_append_eq, hmlen, getD_append_eq]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
            Bool.or_false, ha_val, hb_val, hma, hmb]
      | some b' =>
        simp only [restrictStep, hma, hmb]
        have ha'_lt : a' < n + gs'.length := hbound a a' hma
        have hb'_lt : b' < n + gs'.length := hbound b b' hmb
        obtain ⟨hao2, hrb2, h22⟩ := hstep_append (⟨.or, [a', b']⟩ : Gate) (.inr rfl) ⟨a', b', rfl, ha'_lt, hb'_lt⟩
        have hbnd2 : ∀ u r, (mp ++ [some (n + gs'.length)]).getD u none = some r →
            r < n + (gs' ++ [(⟨.or, [a', b']⟩ : Gate)]).length :=
          bound_append (fun u r hr => by have := hbound u r hr; simp; omega)
            (fun r hr => by injection hr with hr'; simp; omega)
        refine ⟨⟨by simp [stepB, hmlen], hao2, hrb2, h22, hbnd2, ?_⟩, by simp, ?_⟩
        · intro u hu
          simp only [stepB, List.length_append, List.length_singleton] at hu
          simp only [stepB]
          by_cases hlt : u < w.length
          · rw [getD_append_lt mp _ none u (by omega), getD_append_lt w _ false u hlt, heval u hlt]
            cases hmu : mp.getD u none with
            | none => rfl
            | some r => exact hold_keep ⟨.or, [a', b']⟩ u hlt r hmu
          · have hu' : u = w.length := by omega
            subst hu'
            rw [← hmlen, getD_append_eq, hmlen, getD_append_eq, hstep_wires]
            simp only [stepB]
            rw [← hlen_w, getD_append_eq]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
              Bool.or_false, ha_val, hb_val, hma, hmb]
        · rintro ⟨i, hi, hnone⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · rw [hma] at hnone; cases hnone
          · rw [hmb] at hnone; cases hnone

theorem restrict_foldl (n : ℕ) (x x' : List Bool) (hx : x.length = n)
    (gs : List Gate) (w : List Bool) (st : List Gate × List (Option ℕ))
    (hG : GoodState n x x' w st)
    (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (h2 : ∀ g ∈ gs, g.inputs.length = 2)
    (hrb : ∀ k (hk : k < gs.length), ∀ i ∈ gs[k].inputs, i < w.length + k) :
    GoodState n x x' (gs.foldl stepB w) (gs.foldl (restrictStep n) st) ∧
    (gs.foldl (restrictStep n) st).1.length ≤ st.1.length + gs.length ∧
    (∀ u < st.2.length, (gs.foldl (restrictStep n) st).2.getD u none = st.2.getD u none) ∧
    ((∃ g ∈ gs, ∃ i ∈ g.inputs, i < st.2.length ∧ st.2.getD i none = none) →
      (gs.foldl (restrictStep n) st).1.length < st.1.length + gs.length) := by
  induction gs generalizing w st with
  | nil =>
    refine ⟨hG, by simp, fun _ _ => rfl, ?_⟩
    rintro ⟨g, hg, _⟩; simp at hg
  | cons g gs ih =>
    have hstep := restrict_step_good hx hG (hop g (by simp)) (h2 g (by simp))
      (fun i hi => by simpa using hrb 0 (by simp) i hi)
    have hlen_w : (stepB w g).length = w.length + 1 := by simp [stepB]
    have hmp_pres : ∀ u < st.2.length, (restrictStep n st g).2.getD u none = st.2.getD u none := by
      intro u hu
      obtain ⟨gs', mp⟩ := st
      cases g with | mk op ins =>
      have h2g := h2 ⟨op, ins⟩ (by simp)
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp h2g
      rcases hop ⟨op, [a, b]⟩ (by simp) with rfl | rfl
      · cases hma : mp.getD a none <;> cases hmb : mp.getD b none <;>
          · simp only [restrictStep, hma, hmb]; exact getD_append_lt mp _ none u hu
      · cases hma : mp.getD a none <;> cases hmb : mp.getD b none <;>
          · simp only [restrictStep, hma, hmb]; exact getD_append_lt mp _ none u hu
    have hst2_len : st.2.length < (restrictStep n st g).2.length := by
      have h1 := hG.1; have h2s := hstep.1.1; omega
    have tail := ih (stepB w g) (restrictStep n st g) hstep.1
      (fun g' hg' => hop g' (by simp [hg']))
      (fun g' hg' => h2 g' (by simp [hg']))
      (fun k hk i hi => by
        have := hrb (k + 1) (by simp; omega) i (by simpa using hi)
        omega)
    refine ⟨tail.1, by simp only [List.foldl_cons, List.length_cons]; omega, ?_, ?_⟩
    · intro u hu
      rw [List.foldl_cons, tail.2.2.1 u (by omega), hmp_pres u hu]
    · rintro ⟨g', hg', i, hi, hilt, hnone⟩
      simp only [List.foldl_cons, List.length_cons]
      rcases List.mem_cons.mp hg' with rfl | hg'
      · have hsame := hstep.2.2 ⟨i, hi, hnone⟩
        have := tail.2.1
        omega
      · have hlt := tail.2.2.2 ⟨g', hg', i, hi, by omega, by rwa [hmp_pres i hilt]⟩
        have := hstep.2.1
        omega

theorem restrict_main (n : ℕ) (w0 : Fin n) (C : Circuit) (hAO : IsAO2 n C)
    (hUses : ∃ g ∈ C.gates, w0.val ∈ g.inputs) :
    let C' := restrictCircuit n w0.val C
    IsAO2 n C' ∧ C'.size < C.size ∧
      ∀ x : Fin n → Bool, circuitFun n C' x = circuitFun n C (Function.update x w0 false) := by
  classical
  let C' := restrictCircuit n w0.val C
  have hGood (x : Fin n → Bool) :
      GoodState n (List.ofFn x) (List.ofFn (Function.update x w0 false))
        (List.ofFn (Function.update x w0 false)) ([], initMap n w0.val) := by
    refine ⟨by simp [initMap], (fun g hg => by cases hg), (fun k hk => by cases hk),
      (fun g hg => by cases hg), ?_, ?_⟩
    · intro u r hr
      by_cases hu : u < n
      · simp only [initMap, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hu,
          Option.getD_some] at hr
        split_ifs at hr with h
        injection hr with hr'; subst hr'; dsimp only; simp only [List.length_nil]; omega
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [initMap]; omega)] at hr
        cases hr
    · intro u hu
      have hun : u < n := by simpa using hu
      simp only [initMap, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hun,
        Option.getD_some, List.foldl_nil]
      by_cases heq : u = w0.val
      · simp [heq, Function.update, show (⟨u, hun⟩ : Fin n) = w0 from Fin.ext heq]
      · have hne : (⟨u, hun⟩ : Fin n) ≠ w0 := fun h => heq (congrArg Fin.val h)
        simp [heq, hne, hun, Function.update]
  have hrb_gates : ∀ k (hk : k < C.gates.length), ∀ i ∈ C.gates[k].inputs, i < n + k := by
    intro k hk i hi
    have hgat : gateAt C k = C.gates[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hk]
    exact hAO.2.1 k hk i (hgat ▸ hi)
  have hrun (x : Fin n → Bool) := restrict_foldl n (List.ofFn x)
    (List.ofFn (Function.update x w0 false)) (by simp) C.gates
    (List.ofFn (Function.update x w0 false)) ([], initMap n w0.val) (hGood x)
    hAO.1 hAO.2.2 (fun k hk i hi => by simpa using hrb_gates k hk i hi)
  have h0 := hrun (fun _ => false)
  refine ⟨⟨h0.1.2.1, h0.1.2.2.1, h0.1.2.2.2.1⟩, ?_, ?_⟩
  · change (C.gates.foldl (restrictStep n) ([], initMap n w0.val)).1.length < C.gates.length
    obtain ⟨g, hg, hwin⟩ := hUses
    have hnone : (initMap n w0.val).getD w0.val none = none := by
      simp [initMap, List.getD_eq_getElem?_getD, w0.isLt]
    have h := h0.2.2.2 ⟨g, hg, w0.val, hwin, by simp [initMap, w0.isLt], hnone⟩
    simpa using h
  · intro x
    have hx := hrun x
    let res := C.gates.foldl (restrictStep n) ([], initMap n w0.val)
    change (res.1.foldl stepB (List.ofFn x)).getD ((res.2.getD C.output none).getD (n + res.1.length)) false =
      (C.gates.foldl stepB (List.ofFn (Function.update x w0 false))).getD C.output false
    by_cases hout : C.output < (C.gates.foldl stepB (List.ofFn (Function.update x w0 false))).length
    · rw [hx.1.2.2.2.2.2 C.output hout]
      cases hmo : res.2.getD C.output none with
      | none =>
        simp only [Option.getD_none]
        have hlen : (res.1.foldl stepB (List.ofFn x)).length = n + res.1.length := by
          rw [foldl_stepB_len]; simp
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      | some r => rfl
    · have hlen1 : (C.gates.foldl stepB (List.ofFn (Function.update x w0 false))).length ≤ C.output := by omega
      have hmo : res.2.getD C.output none = none := by
        have hreslen : res.2.length = (C.gates.foldl stepB (List.ofFn (Function.update x w0 false))).length := hx.1.1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [hmo, Option.getD_none]
      have hlen2 : (res.1.foldl stepB (List.ofFn x)).length = n + res.1.length := by
        rw [foldl_stepB_len]; simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
          List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen1]

theorem unused_wire_eval (n : ℕ) (w0 : Fin n) (C : Circuit)
    (hNoUse : ∀ g ∈ C.gates, w0.val ∉ g.inputs) (hOut : C.output ≠ w0.val)
    (x : Fin n → Bool) :
    circuitFun n C x = circuitFun n C (Function.update x w0 false) := by
  have key : ∀ (gs : List Gate) (w1 w2 : List Bool),
      w1.length = w2.length →
      (∀ i, i ≠ w0.val → w1.getD i false = w2.getD i false) →
      (∀ g ∈ gs, w0.val ∉ g.inputs) →
      ∀ i, i ≠ w0.val → (gs.foldl stepB w1).getD i false = (gs.foldl stepB w2).getD i false := by
    intro gs
    induction gs with
    | nil => intro w1 w2 _ heq _ i hi; exact heq i hi
    | cons g gs ih =>
      intro w1 w2 hlen heq hno i hi
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (stepB w1 g) (stepB w2 g) (by simp [stepB, hlen]) _ (fun g' hg' => hno g' (by simp [hg'])) i hi
      intro u hu
      by_cases hlt : u < w1.length
      · simp [stepB, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
          List.getElem?_append_left (by omega : u < w2.length)]
        simpa [List.getD_eq_getElem?_getD] using heq u hu
      · by_cases he : u = w1.length
        · subst he
          simp only [stepB, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl _), List.getElem?_append_right (by omega : w2.length ≤ w1.length)]
          simp only [Nat.sub_self, show w1.length - w2.length = 0 by omega, List.getElem?_cons_zero, Option.getD_some]
          congr 1
          apply List.map_congr_left
          intro p hp
          have hpne : p ≠ w0.val := fun h => hno g (by simp) (h ▸ hp)
          exact heq p hpne
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [stepB]; omega),
              List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [stepB]; omega)]
  apply key C.gates (List.ofFn x) (List.ofFn (Function.update x w0 false)) (by simp) _ hNoUse C.output hOut
  intro i hi
  by_cases hlt : i < n
  · have hne : (⟨i, hlt⟩ : Fin n) ≠ w0 := fun h => hi (congrArg Fin.val h)
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hlt, Function.update, hne]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]

theorem main_proof :
    ∀ (m : ℕ) (E : Finset (Fin 3 × Fin m)) (C : Circuit),
      (∀ (a b : Fin 3) (c d : Fin m), a ≠ b → c ≠ d →
        ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
      (∀ i : Fin 3, ∃ j : Fin m, ∀ k : Fin 3, (k, j) ∈ E ↔ k ≠ i) →
      IsAO2 (3 + m) C →
      (∀ x : Fin (3 + m) → Bool, circuitFun (3 + m) C x =
        decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd 3 e.2) = true)) →
      E.card + 2 ≤ C.size := by
  intro m E C hC4 hCore hAO hFun
  classical
  choose core hcore using hCore
  have hInj : Function.Injective core := by
    intro a b hab
    by_contra hne
    have h1 : (a, core b) ∈ E := (hcore b a).mpr hne
    rw [← hab] at h1
    exact ((hcore a a).mp h1) rfl
  let coreE : Finset (Fin 3 × Fin m) :=
    E.filter fun e => e.2 = core 0 ∨ e.2 = core 1 ∨ e.2 = core 2
  have hcoreE_iff : ∀ p q, (p, q) ∈ coreE ↔ ∃ i : Fin 3, q = core i ∧ p ≠ i := by
    intro p q
    simp only [coreE, Finset.mem_filter]
    constructor
    · rintro ⟨he, h0 | h1 | h2⟩
      · exact ⟨0, h0, (hcore 0 p).mp (h0 ▸ he)⟩
      · exact ⟨1, h1, (hcore 1 p).mp (h1 ▸ he)⟩
      · exact ⟨2, h2, (hcore 2 p).mp (h2 ▸ he)⟩
    · rintro ⟨i, rfl, hne⟩
      refine ⟨(hcore i p).mpr hne, ?_⟩
      fin_cases i <;> simp
  have hcoreE_card : coreE.card = 6 := by
    let pairs : Finset (Fin 3 × Fin 3) := Finset.univ.filter fun p => p.1 ≠ p.2
    have heq : coreE = pairs.image (fun p => (p.1, core p.2)) := by
      ext ⟨p, q⟩
      simp only [hcoreE_iff, Finset.mem_image, pairs, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨i, rfl, hne⟩; exact ⟨(p, i), hne, rfl, rfl⟩
      · rintro ⟨⟨p', i⟩, hne, rfl, rfl⟩; exact ⟨i, rfl, hne⟩
    rw [heq, Finset.card_image_of_injective]
    · decide
    · rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (hInj h.2)
  have hdeg1 : ∀ p1 p2 : Fin 3, ∀ q : Fin m,
      (p1, q) ∈ E → (p2, q) ∈ E → (q ≠ core 0 ∧ q ≠ core 1 ∧ q ≠ core 2) → p1 = p2 := by
    intro p1 p2 q h1 h2 hnc
    by_contra hne
    have hthird : ∃ c : Fin 3, c ≠ p1 ∧ c ≠ p2 := by
      fin_cases p1 <;> fin_cases p2 <;> simp_all
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
    obtain ⟨c, hc1, hc2⟩ := hthird
    have hqc : q ≠ core c := by fin_cases c <;> simp [hnc]
    exact hC4 p1 p2 q (core c) hne hqc ⟨h1, (hcore c p1).mpr hc1.symm, h2, (hcore c p2).mpr hc2.symm⟩
  suffices ind : ∀ k : ℕ, ∀ (F : Finset (Fin 3 × Fin m)) (D : Circuit),
      F ⊆ E → coreE ⊆ F → (F \ coreE).card = k →
      IsAO2 (3 + m) D →
      (∀ x : Fin (3 + m) → Bool, circuitFun (3 + m) D x =
        decide (∃ e ∈ F, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd 3 e.2) = true)) →
      F.card + 2 ≤ D.size by
    exact ind (E \ coreE).card E C (Finset.Subset.refl E) (Finset.filter_subset _ E) rfl hAO hFun
  intro k
  induction k with
  | zero =>
    intro F D _ hsub hzero hAO' hFun'
    have hFeq : F = coreE := by
      apply Finset.Subset.antisymm _ hsub
      intro e he
      by_contra hnc
      have := Finset.card_pos.mpr ⟨e, Finset.mem_sdiff.mpr ⟨he, hnc⟩⟩
      omega
    subst hFeq
    rw [hcoreE_card]
    exact c6_base m core hInj coreE hcoreE_iff D hAO' hFun'
  | succ k ih =>
    intro F D hFE hsub hcard hAO' hFun'
    obtain ⟨⟨p, q⟩, hpq⟩ := Finset.card_pos.mp (by omega : 0 < (F \ coreE).card)
    obtain ⟨hpqF, hpqN⟩ := Finset.mem_sdiff.mp hpq
    have hqnc : q ≠ core 0 ∧ q ≠ core 1 ∧ q ≠ core 2 := by
      refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> apply hpqN <;>
        exact Finset.mem_filter.mpr ⟨hFE hpqF, by simp [heq]⟩
    have huniq : ∀ p' : Fin 3, (p', q) ∈ F → p' = p := fun p' hp' =>
      hdeg1 p' p q (hFE hp') (hFE hpqF) hqnc
    let w0 : Fin (3 + m) := Fin.natAdd 3 q
    have hUses : ∃ g ∈ D.gates, w0.val ∈ g.inputs := by
      by_contra hno
      push_neg at hno
      by_cases hout : D.output = w0.val
      · let x : Fin (3 + m) → Bool := fun u => decide (u = w0)
        have hf1 : circuitFun (3 + m) D x = true := by
          change (D.gates.foldl stepB (List.ofFn x)).getD D.output false = true
          rw [hout, foldl_stepB_lt D.gates (List.ofFn x) w0.val (by simp [w0.isLt])]
          simp [x, List.getD_eq_getElem?_getD, w0.isLt]
        have hf2 : circuitFun (3 + m) D x = false := by
          rw [hFun' x, decide_eq_false_iff_not]
          rintro ⟨⟨a, b⟩, _, ha, _⟩
          have : Fin.castAdd m a = w0 := of_decide_eq_true ha
          have hval := congrArg Fin.val this
          simp [w0] at hval
          omega
        rw [hf1] at hf2; cases hf2
      · let x : Fin (3 + m) → Bool := fun u => decide (u = Fin.castAdd m p ∨ u = w0)
        have hsame := unused_wire_eval (3 + m) w0 D hno hout x
        have htrue : circuitFun (3 + m) D x = true := by
          rw [hFun' x, decide_eq_true_iff]
          exact ⟨(p, q), hpqF, by simp [x], by simp [x, w0]⟩
        have hfalse : circuitFun (3 + m) D (Function.update x w0 false) = false := by
          rw [hFun', decide_eq_false_iff_not]
          rintro ⟨⟨a, b⟩, _, _, hb⟩
          by_cases hbq : Fin.natAdd 3 b = w0
          · simp [hbq, Function.update] at hb
          · simp only [Function.update, dif_neg hbq, x, decide_eq_true_eq] at hb
            rcases hb with h1 | h2
            · have hval := congrArg Fin.val h1; simp at hval; omega
            · exact hbq h2
        rw [htrue, hfalse] at hsame; cases hsame
    obtain ⟨hAO2, hsz, hupd⟩ := restrict_main (3 + m) w0 D hAO' hUses
    let F' := F.erase (p, q)
    have hF'sub : F' ⊆ E := (Finset.erase_subset _ _).trans hFE
    have hcoreF' : coreE ⊆ F' := fun e he =>
      Finset.mem_erase.mpr ⟨fun heq => hpqN (heq ▸ he), hsub he⟩
    have hF'card : (F' \ coreE).card = k := by
      have heq : F' \ coreE = (F \ coreE).erase (p, q) := by
        ext e; simp [F', Finset.mem_sdiff, Finset.mem_erase]; tauto
      rw [heq, Finset.card_erase_of_mem hpq, hcard]; rfl
    have hF'fun : ∀ x : Fin (3 + m) → Bool,
        circuitFun (3 + m) (restrictCircuit (3 + m) w0.val D) x =
        decide (∃ e ∈ F', x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd 3 e.2) = true) := by
      intro x
      rw [hupd x, hFun']
      congr 1; apply propext
      constructor
      · rintro ⟨⟨a, b⟩, habF, ha, hb⟩
        have hbq : b ≠ q := by
          intro h; subst h
          simp [w0, Function.update] at hb
        have hne1 : Fin.castAdd m a ≠ w0 := fun h => by
          have := congrArg Fin.val h; simp [w0] at this; omega
        have hne2 : Fin.natAdd 3 b ≠ w0 := fun h => hbq (by
          have := congrArg Fin.val h; simp [w0] at this; exact Fin.ext this)
        simp only [Function.update, dif_neg hne1, dif_neg hne2] at ha hb
        exact ⟨(a, b), Finset.mem_erase.mpr ⟨fun h => hbq (congrArg Prod.snd h), habF⟩, ha, hb⟩
      · rintro ⟨⟨a, b⟩, habF', ha, hb⟩
        obtain ⟨hne, habF⟩ := Finset.mem_erase.mp habF'
        have hbq : b ≠ q := fun h => by
          subst h; exact hne (Prod.ext (huniq a habF) rfl)
        have hne1 : Fin.castAdd m a ≠ w0 := fun h => by
          have := congrArg Fin.val h; simp [w0] at this; omega
        have hne2 : Fin.natAdd 3 b ≠ w0 := fun h => hbq (by
          have := congrArg Fin.val h; simp [w0] at this; exact Fin.ext this)
        exact ⟨(a, b), habF, by simp [Function.update, hne1, ha], by simp [Function.update, hne2, hb]⟩
    have hrec := ih F' (restrictCircuit (3 + m) w0.val D) hF'sub hcoreF' hF'card hAO2 hF'fun
    have hFc : F'.card + 1 = F.card := Finset.card_erase_add_one hpqF
    omega

end PEqualNP.Outside.L_meta_17160

theorem PEqualNP.Outside.L_meta_17160 : (∀ (x1 : ℕ) (x2 : Finset (Fin (3 : ℕ) × Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (3 : ℕ)) (x6 x7 : Fin x1), x4 ≠ x5 → x6 ≠ x7 → ¬((x4, x6) ∈ x2 ∧ (x4, x7) ∈ x2 ∧ (x5, x6) ∈ x2 ∧ (x5, x7) ∈ x2)) → (∀ (x5 : Fin (3 : ℕ)), ∃ (x6 : Fin x1), ∀ (x7 : Fin (3 : ℕ)), (x7, x6) ∈ x2 ↔ x7 ≠ x5) → PEqualNP.TopForm.IsAO2 ((3 : ℕ) + x1) x3 → (∀ (x7 : Fin ((3 : ℕ) + x1) → Bool), PEqualNP.MetaComplexity.circuitFun ((3 : ℕ) + x1) x3 x7 = Decidable.decide (∃ x8 ∈ x2, x7 (Fin.castAdd x1 x8.1) = Bool.true ∧ x7 (Fin.natAdd (3 : ℕ) x8.2) = Bool.true)) → x2.card + (2 : ℕ) ≤ x3.size) := by
  exact PEqualNP.Outside.L_meta_17160.main_proof
