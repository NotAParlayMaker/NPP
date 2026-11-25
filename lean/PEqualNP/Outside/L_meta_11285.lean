import Mathlib
import PEqualNP.Defs

-- The signed-circuit semantics and live-wire construction follow L-meta-8724,
-- L-meta-1449, L-meta-1429 and L-meta-703. Each generated block checks a
-- consecutive part of a gate frontier. The blocks together exhaust all
-- ways to compute the target with at most nine binary gates.
namespace PEqualNP.Outside.L_meta_11285_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Build: the goal is reached from the available wires in k binary steps. Live: the same,
-- keeping only the wires still needed, so a search may range over small sets.
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

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
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

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
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

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
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

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
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

-- The upper and lower halves represent opposite target labels on 256 pairs of assignments.
abbrev W := BitVec 512
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 256 := ((x >>> 256) ^^^ x).setWidth 256
def cuts (ws : List W) : BitVec 256 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
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

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
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

def differs (i : Fin 256) (w : W) : Prop :=
  w.getLsbD (256+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem ops_differs (i : Fin 256) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 256+i.val < 512 := by omega
  have hi' : i.val < 512 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem cuts_spec (ws : List W) (i : Fin 256) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

-- The search: pick two live wires, apply one of the four operations, and keep each operand
-- only if it is still needed; every live run is found, so a false search rules out a build.
def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
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

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

-- Wires held up to complement, and what one binary gate reaches from them.
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a,ha,e⟩ => ⟨a,sub ha,e⟩)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 512 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 512)
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

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

-- Running a circuit on the 512 rows at once, NOT gates cost nothing.
private def bit (k : Fin 512) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 512) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 512) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#512)[k.val] = false; simp
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

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
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
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
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
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
end PEqualNP.Outside.L_meta_11285_aux
namespace PEqualNP.Outside.L_meta_11285_aux

def clean : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a,b,r) => dispatch extra
      (fun e s => !(ws.contains (s.headD 0)) && clean k e s) a b r)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem clean_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    clean n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [clean, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [clean, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e s => !(ws.contains (s.headD 0)) && clean k e s) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (fun e s => !(ws.contains (s.headD 0)) && clean k e s) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply Bool.and_eq_true_iff.mpr
        constructor
        · simpa [List.headD, List.contains_eq_mem] using hout
        · apply ih _ _ hnd _ hl
          simp; omega
      simp only [clean, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩


end PEqualNP.Outside.L_meta_11285_aux
namespace PEqualNP.Outside.L_meta_11285_aux.NatCheck
def full : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mask : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def aim : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000
def width : ℕ := 0x10000000000000000000000000000000000000000000000000000000000000000

def cutWord (v : ℕ) : ℕ := ((v >>> 256) ^^^ v) % width
def maskOf (v : List ℕ) := v.foldr (fun w s => cutWord w ||| s) 0
def opsN (a b : ℕ) := [a &&& b, a ||| b, a &&& (mask-b), b &&& (mask-a)]
def leaf (ws : List ℕ) := ws == [aim] || ws == [full]
def explore (extra : ℕ) (call : ℕ → List ℕ → Bool) (ws : List ℕ)
    (a b : ℕ) (r : List ℕ) : Bool :=
  let lo := maskOf r
  let a0 := cutWord a
  let b0 := cutWord b
  (opsN a b).any (fun w =>
    !ws.contains w &&
    (let v := cutWord w ||| lo
     (v == full && call extra (w::r)) ||
      (extra != 0 && ((v ||| a0 == full && call (extra-1) (w::a::r)) ||
                      (v ||| b0 == full && call (extra-1) (w::b::r)))) ||
      (extra ≥ 2 && v ||| a0 ||| b0 == full && call (extra-2) (w::a::b::r))))
def walk : ℕ → ℕ → List ℕ → Bool
  | 0, _, ws => leaf ws
  | k+1, e, ws => leaf ws || (pairs ws).any (fun (a,b,r) => explore e (walk k) ws a b r)
end PEqualNP.Outside.L_meta_11285_aux.NatCheck
namespace PEqualNP.Outside.L_meta_11285_aux.NatCheck

def asNs (ws : List W) : List ℕ := ws.map BitVec.toNat
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem nat_eq {n : ℕ} (x y : BitVec n) : (x.toNat == y.toNat) = (x == y) := by rfl
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem mask_val : mask = 2^512-1 := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem width_val : width = 2^256 := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem full_val : full = (-1 : BitVec 256).toNat := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem aim_val : aim = goal.toNat := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem opp_val : full = (~~~goal).toNat := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem cut_as (w : W) : cutWord w.toNat = (sep w).toNat := by
  simp only [cutWord,sep,BitVec.toNat_setWidth,BitVec.toNat_xor,BitVec.toNat_ushiftRight,width_val]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem masks_as (ws : List W) : maskOf (asNs ws) = (cuts ws).toNat := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    change (cutWord x.toNat ||| maskOf (asNs xs)) = (sep x ||| cuts xs).toNat
    rw [ih,cut_as,BitVec.toNat_or]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem ops_as (a b : W) : opsN a.toNat b.toNat = (ops a b).map BitVec.toNat := by
  simp [opsN,ops,mask_val]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem contains_as (ws : List W) (w : W) : (asNs ws).contains w.toNat = ws.contains w := by
  induction ws with
  | nil => rfl
  | cons v vs ih =>
    simpa only [asNs,List.map_cons,List.contains_cons,nat_eq] using
      congrArg (fun t => (w == v) || t) ih
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem leaf_as (ws : List W) : leaf (asNs ws) = (ws == [goal] || ws == [~~~goal]) := by
  rcases ws with _|⟨v,_|⟨z,zs⟩⟩
  · rfl
  · simp only [leaf,asNs,List.map_cons,List.map_nil,aim_val,opp_val,List.cons_beq_cons,nat_eq]
    rfl
  · simp only [leaf,asNs,List.map_cons,List.cons_beq_cons,List.beq_nil_eq,List.isEmpty_cons,Bool.and_false]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem single_map {α β : Type} (f : α → β) (xs : List α) :
    singles (xs.map f) = (singles xs).map (fun (x,r) => (f x,r.map f)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [singles,ih,List.map_map,Function.comp_def]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem pair_map {α β : Type} (f : α → β) (xs : List α) :
    pairs (xs.map f) = (pairs xs).map (fun (a,b,r) => (f a,f b,r.map f)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pairs,ih,single_map,List.map_map,Function.comp_def]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem explore_as (e : ℕ) (call : ℕ → List ℕ → Bool) (ws : List W) (a b : W) (r : List W) :
    explore e call (asNs ws) a.toNat b.toNat (asNs r) =
       dispatch e (fun n s => !(ws.contains (s.headD 0)) && call n (asNs s)) a b r := by
  simp only [explore,dispatch,ops_as,masks_as,List.any_map,Function.comp_def]
  apply List.any_congr rfl
  intro w
  simp only [contains_as,cut_as,full_val,← BitVec.toNat_or,nat_eq,List.headD_cons]
  cases h : ws.contains w <;> simp [h,asNs]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem walk_as (k e : ℕ) (ws : List W) : walk k e (asNs ws) = clean k e ws := by
  induction k generalizing e ws with
  | zero => exact leaf_as _
  | succ k ih =>
    simp only [walk,clean,leaf_as]
    simp only [asNs,pair_map,List.any_map,Function.comp_def]
    congr 1
    apply List.any_congr rfl
    rintro ⟨a,b,r⟩
    change explore e (walk k) (asNs ws) a.toNat b.toNat (asNs r) = _
    rw [explore_as]
    simp only [ih]
end PEqualNP.Outside.L_meta_11285_aux.NatCheck
namespace PEqualNP.Outside.L_meta_11285_aux.NatCheck
abbrev CallState := ℕ × List ℕ
def keepIf (b : Bool) (xs : List CallState) : List CallState := if b then xs else []
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem any_keepIf (b : Bool) (xs : List CallState) (f : CallState → Bool) :
    (keepIf b xs).any f = (b && xs.any f) := by cases b <;> simp [keepIf]
def nextFor (ws : List ℕ) (e a b : ℕ) (r : List ℕ) (w : ℕ) : List CallState :=
  let v := cutWord w ||| maskOf r
  let ca := cutWord a
  let cb := cutWord b
  keepIf (!ws.contains w) (
    keepIf (v == full) [(e,w::r)] ++
    keepIf (e != 0) (keepIf ((v ||| ca) == full) [(e-1,w::a::r)] ++
                      keepIf ((v ||| cb) == full) [(e-1,w::b::r)]) ++
    keepIf (decide (e ≥ 2) && (v ||| ca ||| cb == full)) [(e-2,w::a::b::r)])
def nextList (e : ℕ) (ws : List ℕ) : List CallState :=
  (pairs ws).flatMap (fun (a,b,r) => (opsN a b).flatMap (nextFor ws e a b r))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem any_next (e : ℕ) (call : ℕ → List ℕ → Bool) (ws : List ℕ) (a b : ℕ) (r : List ℕ) :
    explore e call ws a b r =
      ((opsN a b).flatMap (nextFor ws e a b r)).any (fun q => call q.1 q.2) := by
  simp only [explore,List.any_flatMap]
  apply List.any_congr rfl
  intro w
  simp only [nextFor,any_keepIf,List.any_append,List.any_cons,List.any_nil,Bool.or_false]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem split_walk {k e : ℕ} {ws : List ℕ} {fr : List CallState}
    (terminal : leaf ws = false) (cover : nextList e ws = fr)
    (rest : ∀ v ∈ fr, walk k v.1 v.2 = false) : walk (k+1) e ws = false := by
  have split : (pairs ws).any (fun (a,b,r) => explore e (walk k) ws a b r) =
      (nextList e ws).any (fun q => walk k q.1 q.2) := by
    simp only [nextList,List.any_flatMap]
    apply List.any_congr rfl
    rintro ⟨a,b,r⟩
    simpa only [List.any_flatMap] using any_next e (walk k) ws a b r
  rw [walk,terminal,Bool.false_or,split,cover]
  simpa only [List.any_eq_false,Bool.not_eq_true] using rest
end PEqualNP.Outside.L_meta_11285_aux.NatCheck
namespace PEqualNP.Outside.L_meta_11285_aux.NatCheck
def AllRejected (k : ℕ) (l : List CallState) : Prop := ∀ v ∈ l, walk k v.1 v.2 = false
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem emptyOk (k : ℕ) : AllRejected k [] := by simp [AllRejected]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem consOk {k e : ℕ} {ws : List ℕ} {l : List CallState}
    (h : walk k e ws = false) (t : AllRejected k l) : AllRejected k ((e,ws)::l) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl|hv
  · exact h
  · exact t _ hv
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem entersOnly {n : ℕ} (v : List W) (hn : v.Nodup)
    (start : v.sublists.filter (fun w => decide (w.length ≤ n + 1) && (cuts w == -1)) = [v])
    (reject : walk n (n+1-v.length) (asNs v) = false)
    (t : W) (ht : t = goal ∨ t = ~~~goal) (run : build basicOps t n v.toFinset) : False := by
  classical
  obtain ⟨s,hs,hl⟩ := compress run
  let u := v.filter (· ∈ s)
  have eq : u.toFinset = s := by
    ext w
    simp only [u,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hn' : u.Nodup := hn.filter _
  have hl' : live basicOps t n u.toFinset := eq.symm ▸ hl
  have room := live_card hl'
  rw [List.toFinset_card_of_nodup hn'] at room
  have m : u ∈ v.sublists.filter (fun w => decide (w.length ≤ n+1) && (cuts w == -1)) :=
    List.mem_filter.mpr ⟨List.mem_sublists.mpr (List.filter_sublist ..),by simp [room,cuts_full ht hl']⟩
  have uv : u = v := List.mem_singleton.mp (start ▸ m)
  have hit := clean_complete ht n u (n+1-u.length) hn' (by omega) hl'
  rw [uv,←walk_as] at hit
  exact Bool.noConfusion (reject.symm.trans hit)
end PEqualNP.Outside.L_meta_11285_aux.NatCheck
namespace PEqualNP.Outside.L_meta_11285_aux.NatCheck
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checkedBlock {k : ℕ} {l : List CallState}
    (h : l.all (fun q => !(walk k q.1 q.2)) = true) : AllRejected k l := by
  intro q hq
  simpa only [Bool.not_eq_true'] using List.all_eq_true.mp h q hq
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem appendOk {k : ℕ} {l r : List CallState} (hl : AllRejected k l) (hr : AllRejected k r) :
    AllRejected k (l++r) := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact hl q h
  · exact hr q h
end PEqualNP.Outside.L_meta_11285_aux.NatCheck
namespace PEqualNP.Outside.L_meta_11285_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity NatCheck
def graph (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,6]⟩, ⟨.or,[3,4]⟩, ⟨.and,[7,8]⟩, ⟨.or,[5,6]⟩, ⟨.or,[0,2]⟩, ⟨.or,[3,11]⟩, ⟨.and,[10,12]⟩, ⟨.or,[4,5]⟩, ⟨.and,[1,14]⟩, ⟨.or,[9,13]⟩, ⟨.or,[15,16]⟩],17⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem smallLegal : ∀ g ∈ smallCircuit.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [smallCircuit]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
theorem smallEval : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = graph x := by decide +kernel

def inputs7 : List W := [0x113ffe02c036de22888814308420bd75556addb7fb6ff88f842111223fc4490f000ffe00000ffe00000000000001fff1152a5c97f92ff007800000003fc0000f,0xfff24a051bdb6a050106284100c6029999b36edaadb6b17f8be2221fc3c09030fff000003ffffe00007e000003fe07f999336edaadb6b07f83e0001fc3c00030,0x224494d9ed6db448121040062819401e1e3c771cce3b27ff90440fe1fc0900c0000001fffffffe000000000ffc1ff81e1e3c771cce3b27ff80000fe1fc0000c0,0x4490276e76b00690242081905720083fe03f87e0ffc3fff8a088f0fe04520701000001fffff00000000003f07fe0000ee015036006c007f80000f0fe00000700,0x88e139b780c03901c0430e69804210dfffc007ff0ffc3791411fff0448a03812000001ffc00000000001ffff8000000662c0012002400780001fff0000003800,0xf09c0380701c01e0784f082198c631ffffff8000fffc2227e1f44489103c26400000000000000007f81fc000000000000c08000000000007c1f00000003c000,0xf00e01c0380e01e07879030c6211841ffffffffff00004447ff08891223c248800000000000000007ffe00000000000000008000000000007fe00000003c0000]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
theorem sample : ∀ j : Fin 512, graph (fun i => (inputs7.getD i.val 0)[j.val]) = goal[j.val] := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem ten_binary (cert : walk 9 3 (asNs inputs7) = false) (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = graph x) :
    9 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs7, holds inputs7.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 512) :
      (gs.foldl step (inputs7.map (bit k))).getD o false = bit k goal := by
    have same : List.ofFn (fun i : Fin 7 => bit k (inputs7.getD i.val 0)) =
        inputs7.map (bit k) := by
      apply List.ext_getElem (by simp [inputs7])
      intro i hi hj
      have hlt : i < inputs7.length := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs7.map (bit k)) = bit k goal
    rw [← same, he]
    exact sample k
  obtain ⟨t,ht,run⟩ := compile gs o hg inputs7 inputs7.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs7.toFinset) :
      build basicOps t b inputs7.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  apply entersOnly inputs7 (by decide +kernel) (n := 9) _ cert t ht (lift low run)
  decide +kernel

end PEqualNP.Outside.L_meta_11285_aux
namespace PEqualNP.Outside.L_meta_11285_aux.NatCheck.Delete7
def v0 : ℕ := 0x113ffe02c036de22888814308420bd75556addb7fb6ff88f842111223fc4490f000ffe00000ffe00000000000001fff1152a5c97f92ff007800000003fc0000f
def v1 : ℕ := 0xfff24a051bdb6a050106284100c6029999b36edaadb6b17f8be2221fc3c09030fff000003ffffe00007e000003fe07f999336edaadb6b07f83e0001fc3c00030
def v2 : ℕ := 0x224494d9ed6db448121040062819401e1e3c771cce3b27ff90440fe1fc0900c0000001fffffffe000000000ffc1ff81e1e3c771cce3b27ff80000fe1fc0000c0
def v3 : ℕ := 0x4490276e76b00690242081905720083fe03f87e0ffc3fff8a088f0fe04520701000001fffff00000000003f07fe0000ee015036006c007f80000f0fe00000700
def v4 : ℕ := 0x88e139b780c03901c0430e69804210dfffc007ff0ffc3791411fff0448a03812000001ffc00000000001ffff8000000662c0012002400780001fff0000003800
def v5 : ℕ := 0xf09c0380701c01e0784f082198c631ffffff8000fffc2227e1f44489103c26400000000000000007f81fc000000000000c08000000000007c1f00000003c000
def v6 : ℕ := 0xf00e01c0380e01e07879030c6211841ffffffffff00004447ff08891223c248800000000000000007ffe00000000000000008000000000007fe00000003c0000
def v7 : ℕ := 0x11324a0000124a00000000000000001111224c92a926b00f8020000203c0000000000000000ffe0000000000000007f111224c92a926b0078000000003c00000
def v8 : ℕ := 0xfffffe07dbfffe27898e3c7184e6bffdddfbfffffffff9ff8fe3333fffc4d93ffffffe003ffffe00007e000003fffff99d3b7edffdbff07f83e0001fffc0003f
def v9 : ℕ := 0xdb402c0249422888814308420bd644448912552494880040111203c04490f000ffe0000000000000000000001f8000408100550094000000000003c00000f
def v10 : ℕ := 0xeec000051bc920050106284100c6028888912248049001700bc2221dc0009030fff000003ff00000007e000003fe0008881122480490007803e0001fc0000030
def v11 : ℕ := 0x49400c0249400000000000000001414285514ca2b208f800001203c00000000000000000ffe00000000000001f81014285414c82b2007800000003c000000
def v12 : ℕ := 0x337ffedbed7ffe6a9a985436ac39fd7f5f7effbfff7fffff94651fe3ffcd49cf000ffffffffffe000000000ffc1fffff1f3e7f9fff3ff7ff80000fe1ffc000cf
def v13 : ℕ := 0x113b6a0200124a22888814308420bd61414288a33144d8000421100203c4490f000ffe000000000000000000000007e1010208833104d0000000000003c0000f
def v14 : ℕ := 0x224000d92d492048121040062819400a0a1422080410077010440ec1c00900c0000001fffff000000000000ffc1e000e0a142308061007f800000fe1c00000c0
def v15 : ℕ := 0x66d027ff7ff926d83630c1967f39483fea3fa7e8ffd3fff8b0ccfeffc45b07c1000001fffff00000000003fffffe000eea15236806d007f80000ffffc00007c0
def v16 : ℕ := 0x102602403006000000001004200835402a85a0fb43f88880001022044001010000000000000000000000000000000000000000000000000000000000000000
def v17 : ℕ := 0x66d4b7fffffdb6d83630c1967f39483ffe3ff7fcfffbffffb0ccfffffc5b07c1000001fffffffe00000003fffffff81efe3d777ccefb27ff8000fffffc0007c0
def v18 : ℕ := 0x55bfff6ef6b6deb2aca895b0d720bd7ff57fdff7ffefffffa4a9f1fe3fd64f0f000ffffffffffe00000003f07fe1fffff53f5ff7ffeff7ff8000f0fe3fc0070f
def v19 : ℕ := 0x112fd8008006d822888814208000b54015405817002c0007042101003b84480e000ffe00000ffe00000000000001fff1152a5c97f92ff007800000003fc0000f
def v20 : ℕ := 0x4480016c36800090242081805300000aa0150240048007702088e0dc00120600000001fffff00000000003f07fe0000ee015036006c007f80000f0fe00000700
def v21 : ℕ := 0x213802800018008000042080001055554005b70b6c308100011100088008020000000000000000000000000000000000000000000000000000000000000000
def v22 : ℕ := 0x99ffffb7c0f6ff23c8cb1e798462bdffffeadfffffffff9fc53fff267fe4791f000fffffc00ffe000001ffff8001fff777ea5db7fb6ff787801fff003fc0380f
def v23 : ℕ := 0x111ec6004036c622088810100420ad20002ad800f003c80e842000223744410d000ffe00000ffe00000000000001fff1152a5c97f92ff007800000003fc0000f
def v24 : ℕ := 0x88c001b500c0210140430a490042008aaa80024804900710411eee0440203010000001ffc00000000001ffff8000000662c0012002400780001fff0000003800
def v25 : ℕ := 0x109c0000000c0020080100000002115556ad8000b6fc00204010000110040040000000000000000000000000000000000000000000000000000000000000000
def v26 : ℕ := 0x1f3ffe3ac737de3e8f8cf4b29dacff7ffffffdb7fffffaaffe3f556abfc7cb6f000ffe00000ffe007f81fc000001fff115eadc97f92ff007fc1f00003fc3c00f
def v27 : ℕ := 0x10363e02c0361e208808043084209c60000005b7f000388d802011222ec4090b000ffe00000ffe00000000000001fff1152a5c97f92ff007800000003fc0000f
def v28 : ℕ := 0xe0000380701001c0704e082198c420aaa952000049002207a1e44488003826000000000000000007f81fc000000000000c08000000000007c1f00000003c000
def v29 : ℕ := 0x100e0000000600200808000000008415556addb7f000000404200000220400080000000000000000000000000000000000000000000000000000000000000000
def v30 : ℕ := 0xf13fffc2f83edfe2f8f9173ce631bd7ffffffffffb6ffccffff199b33ffc6d8f000ffe00000ffe007ffe00000001fff1152adc97f92ff007ffe000003ffc000f
def v31 : ℕ := 0x131fe02c030de028080143084203960000000000b6ff88b800111221dc04907000ffe00000ffe00000000000001fff1152a5c97f92ff007800000003fc0000f
def v32 : ℕ := 0xe00001c0380801c07071030c6211000aaa952248000004407bd088910038248000000000000000007ffe00000000000000008000000000007fe00000003c0000
def v33 : ℕ := 0x22400001094920000000000000000018183066188c32217f80400201c0000000000000003ffffe0000000000001e0018183066188c32207f80000001c0000000
def v34 : ℕ := 0xfff6deddfffffe4d1316684728df429f9fbf7fdeefbfb7ff9be62fffffc990f0fff001fffffffe00007e000fffffffff9f3f7fdeefbfb7ff83e00fffffc000f0
def v35 : ℕ := 0xddb24a0412924a050106284100c60281818308c2218490000ba2201e03c09030fff0000000000000007e000003e007e1810308c22184900003e0001e03c00030
def v36 : ℕ := 0x494d8e42494481210400628194006060c11044209068010040de03c0900c0000001ffc00000000000000ffc01f806060c11044209078000000fe03c0000c0
def v37 : ℕ := 0x44900204129002000000000000000019803306c0ad82b1788080201e00400000000000003ff000000000000003e0000880110240048000780000001e00000000
def v38 : ℕ := 0xfff26f6f7ffb6e952526a9d157e60abff9bfeffafff7ffffabeaf2ffc7d29731fff001fffffffe00007e03f07ffe07fff9376ffaaff6b7ff83e0f0ffc3c00730
def v39 : ℕ := 0xbb624801094b68050106284100c602801980681a003400070b620201c3809030fff00000000ffe00007e0000001e07f119226c9aa936b00783e00001c3c00030
def v40 : ℕ := 0x256a642004902420819057200826600c812052414e802008d0e004120701000001ffc0000000000003f07c00000660040120024007800000f0e000000700
def v41 : ℕ := 0x88e0080500c028010002084100420099998006da0db4311101022204408010100000000000000000000000000000000000000000000000000000000000000000
def v42 : ℕ := 0xfff37bb79bdb7b05c1472e6980c612dffff36fffaffeb7ffcbffff1fcbe0b832fff001fffffffe00007fffff83fe07fffbf36ffaaff6b7ff83ffff1fc3c03830
def v43 : ℕ := 0x771242001b1b4204010420000084020000336800a002806e8ae0001b83408020fff000003ffffe00007e000003fe07f999336edaadb6b07f83e0001fc3c00030
def v44 : ℕ := 0x131b280001100c0410628800010466640012502480680401ddd0008202802000001ffc00000000001ffff8000000662c0012002400780001fff0000003800
def v45 : ℕ := 0xf00400003014004010420000084021999b368000db680220a020008810080200000000000000000000000000000000000000000000000000000000000000000
def v46 : ℕ := 0xfffbca3d1fdbea1f0786f8c319ce639ffffffedaaffff37fffff665fd3c3d274fff000003ffffe007ffffc0003fe07f999f3eedaadb6b07fffff001fc3c3c030
def v47 : ℕ := 0xf0f20a0518da2a010002084100420080000006daa000315d81e0221742c01010fff000003ffffe00007e000003fe07f999336edaadb6b07f83e0001fc3c00030
def v48 : ℕ := 0x980380400801a0680d08219086106664c900002494200741d44401003424400000000000000007f81fc000000000000c08000000000007c1f00000003c000
def v49 : ℕ := 0xf0020000180a0000000000000000001999b36edaa00000440be00011020000000000000000000000007e000000000000000000000000000003e0000000000000
def v50 : ℕ := 0xfffe4bc53bdf6be5797f2b4d62d7869ffffffffffdb6b57ffff2aa9fe3fcb4b8fff000003ffffe007ffe000003fe07f99933eedaadb6b07fffe0001fc3fc0030
def v51 : ℕ := 0xff04a0503d16a050106284100c60280000000000db6b13b8002220ec1c09030fff000003ffffe000000000003fe07f999336edaadb6b07f8000001fc3c00030
def v52 : ℕ := 0xc01c0200401e07879030c62118406664c91255000040074108880203c248800000000000000007f8000000000000000008000000000007c000000003c0000
def v53 : ℕ := 0x44864200400000000000000001e003c0700ce0327f8800000e004000000000001fffff00000000000007c00000e00140300060007f8000000e000000000
def v54 : ℕ := 0x22449091894db04812104006281940001e00701c0038000710440f01f80900c000000000000ffe000000000f801ff8101e28741cc83b200780000f01fc0000c0
def v55 : ℕ := 0x44902326129002902420819057200821e00380e031c0d8002088f01e005207010000000000000000000003f003e00000e001006000c000000000f01e00000700
def v56 : ℕ := 0x40109180403000000000000000001e1e00071c0e38279100040f0048000000000001ffc00000000000000f80000006020001000200078000000f0000000000
def v57 : ℕ := 0xaae5bdffededbd49d2534e6fa85b50dffffc77ffcfff37ffd15fffe5fca938d2000001fffffffe000001fffffc1ff81e7efc773cce7b27ff801fffe1fc0038c0
def v58 : ℕ := 0x220484486d2d84481210400628194000003c7000c003006e904000e1b40900c0000000003ffffe00000000007c1ff8181c3c761ccc3b207f800000e1fc0000c0
def v59 : ℕ := 0x88a1292600800901c0430e69804210c1e1c000e301c41000411bf00400a0381200000000000000000001fff00000000060c0002000400000001ff00000003800
def v60 : ℕ := 0x200801805018008020040020808401e1e3c70000e3b022210040440900100400000000000000000000000000000000000000000000000000000000000000000
def v61 : ℕ := 0x2f4dd4f9ef6df45e1794f086399d631fffffff1ccfffe7fffe5f4fe9fd0bc2e4000001fffffffe007f81fc0ffc1ff81e1efcf71cce3b27fffc1f0fe1fc03c0c0
def v62 : ℕ := 0x204414c1e86c344010100004201100000000071cc00025dd80400ba16c080080000001fffffffe000000000ffc1ff81e1e3c771cce3b27ff80000fe1fc0000c0
def v63 : ℕ := 0xd094020020040160584b08011842301e1c3880001c4c0006e1b40080102c22400000000000000007f81fc000000000000c08000000000007c1f00000003c000
def v64 : ℕ := 0x200400c0280c0040101000042011001e1e3c771cc000044410400881200800800000000000000000000000000000000000000000000000000000000000000000
def v65 : ℕ := 0xf24e95d9fd6fb5e87a79430e6a19c41ffffffffffe3b27fffff48ff1fe3d24c8000001fffffffe007ffe000ffc1ff81e1e3cf71cce3b27ffffe00fe1fc3c00c0
def v66 : ℕ := 0x2409419c561b4080200400208084000000000000e3b23bb80040760dc010040000001fffffffe000000000ffc1ff81e1e3c771cce3b27ff80000fe1fc0000c0
def v67 : ℕ := 0xd00a0100100201a06869030842008401e1c388e3300000006fb080100234240800000000000000007ffe00000000000000008000000000007fe00000003c0000
def v68 : ℕ := 0x80212600800000000000000000001fe00007e00fc037900008f00400000000000001ffc0000000000003f00000000660000120024007800000f00000000000
def v69 : ℕ := 0xccf13ffff6f03f91e4638ff9d76218ffffff87fffffffff9e19ffffe4cf23f13000001fffff000000001ffffffe0000ee2d5036006c007f8001ffffe00003f00
def v70 : ℕ := 0x44100648763006902420819057200820003f8000f003c868a08000fa04520701000000003ff00000000000007fe000088015024004800078000000fe00000700
def v71 : ℕ := 0x8861189180403901c0430e69804210c01fc0001f003c000141170f0048a0381200000000000000000001fc0f8000000002c0000000000000001f0f0000003800
def v72 : ℕ := 0x400002806000010040080801100001fe03f80000fc3c22020084048000202000000000000000000000000000000000000000000000000000000000000000000
def v73 : ℕ := 0x4f99e77e77b1c69e27a4f1925fac6b3fffffffe0fffffffafe9ff4fe9553c765000001fffff000007f81fff07fe0000ee0d5836006c007f87c1ff0fe0003c700
def v74 : ℕ := 0x4090274670b006802020011046200820000007e0f0003dd88080b0b604500501000001fffff00000000003f07fe0000ee015036006c007f80000f0fe00000700
def v75 : ℕ := 0xb09c0100101c00e03847002088c63001fc07800003c00025e1704009101c06400000000000000007f81fc000000000000c08000000000007c1f00000003c000
def v76 : ℕ := 0x4000014030000080202001004200001fe03f87e0f000044020808090001004000000000000000000000000000000000000000000000000000000000000000000
def v77 : ℕ := 0xf49e27ee7ebe07f07c79839c77318c3fffffffffffc3fffcfff8f8ff267e2789000001fffff000007ffe03f07fe0000ee015836006c007f87fe0f0fe003c0700
def v78 : ℕ := 0x490262e46b006100400809015200820000000000fc3fbb88008706e04420301000001fffff00000000003f07fe0000ee015036006c007f80000f0fe00000700
def v79 : ℕ := 0xb00e0080080e01605859020c201184001fc0781f000000045f700801222c208800000000000000007ffe00000000000000008000000000007fe00000003c0000
def v80 : ℕ := 0x801003000000000000000000000001fffc000000ffc0200401f44000000000000000000000000000001fc000000000000c0000000000000001f000000000000
def v81 : ℕ := 0x8fe9f9bf87c1f91fc7c7feeb99ce73dfffffffff0ffff7b37f1fff4cd9a3fa76000001ffc00000007f81ffff8000000662c08120024007807c1fff000003f800
def v82 : ℕ := 0x80e0398780c03901c0430e69804210c0000007ff000035910100bb0448a03812000001ffc0000000000003ff8000000662000120024007800000ff0000003800
def v83 : ℕ := 0x708c0080701c01e0784f082198c6300003ff8000003c0223e0000489103c26400000000000000007f8000000000000000008000000000007c0000000003c000
def v84 : ℕ := 0x8000018000000100404102080000001fffc007ff0000040041108800002020000000000000000000000000000000000000000000000000000000000000000000
def v85 : ℕ := 0xf8ef39f7b8ce39e1f87b0f6de25394dffffffffffffc37d57fffff956abc3c9a000001ffc00000007fffffff8000000662c08120024007807fffff00003c3800
def v86 : ℕ := 0x8e1383780c0380180020c61804210c0000000000ffc3391000f770448801812000001ffc00000000001ffff8000000662c0012002400780001fff0000003800
def v87 : ℕ := 0x700e0040380e00e03838010462118400003ff800f00000443ee00091221c048800000000000000007ffe00000000000000008000000000007fe00000003c0000
def v88 : ℕ := 0x8000000000000000000000000001ffffff800000000007e1000000000000000000000000000007f8000000000000000008000000000007c00000000000000
def v89 : ℕ := 0xff0fc1f83f0fc1fe7ffdf38e7b9de71fffffffffffffc6667fffccd9b33fe6ec00000000000000007ffffc000000000000c08000000000007fff0000003fc000
def v90 : ℕ := 0xf01c0380701c01e0784f082198c6300000000000fffc222000f44489103c26400000000000000000001fc000000000000c0000000000000001f00000003c000
def v91 : ℕ := 0xf00601c0380e01e07879030c62118400000007fff000044401e08891223c24880000000000000000007e000000000000000000000000000003e00000003c0000
def wires0 : List ℕ := [v0,v1,v2,v3,v4,v5,v6]
def wires1 : List ℕ := [v7,v0,v1,v2,v3,v4,v5,v6]
def block0 : List CallState := ((nextList 1 wires1).drop 0).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed0 : AllRejected 7 block0 := checkedBlock (by decide +kernel)
def block1 : List CallState := ((nextList 1 wires1).drop 8).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed1 : AllRejected 7 block1 := checkedBlock (by decide +kernel)
def block2 : List CallState := ((nextList 1 wires1).drop 15).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed2 : AllRejected 7 block2 := checkedBlock (by decide +kernel)
def block3 : List CallState := ((nextList 1 wires1).drop 21).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed3 : AllRejected 7 block3 := checkedBlock (by decide +kernel)
def block4 : List CallState := ((nextList 1 wires1).drop 28).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed4 : AllRejected 7 block4 := checkedBlock (by decide +kernel)
def block5 : List CallState := ((nextList 1 wires1).drop 37).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed5 : AllRejected 7 block5 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node1 : walk 8 1 wires1 = false := by
  have rest := (appendOk closed0 (appendOk closed1 (appendOk closed2 (appendOk closed3 (appendOk closed4 (appendOk closed5 (emptyOk 7)))))))
  exact split_walk (k := 7) (e := 1) (ws := wires1) (by decide +kernel) (by decide +kernel) rest
def wires2 : List ℕ := [v8,v0,v2,v3,v4,v5,v6]
def block6 : List CallState := ((nextList 2 wires2).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed6 : AllRejected 7 block6 := checkedBlock (by decide +kernel)
def block7 : List CallState := ((nextList 2 wires2).drop 7).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed7 : AllRejected 7 block7 := checkedBlock (by decide +kernel)
def block8 : List CallState := ((nextList 2 wires2).drop 12).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed8 : AllRejected 7 block8 := checkedBlock (by decide +kernel)
def block9 : List CallState := ((nextList 2 wires2).drop 16).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed9 : AllRejected 7 block9 := checkedBlock (by decide +kernel)
def block10 : List CallState := ((nextList 2 wires2).drop 22).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed10 : AllRejected 7 block10 := checkedBlock (by decide +kernel)
def block11 : List CallState := ((nextList 2 wires2).drop 25).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed11 : AllRejected 7 block11 := checkedBlock (by decide +kernel)
def block12 : List CallState := ((nextList 2 wires2).drop 28).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed12 : AllRejected 7 block12 := checkedBlock (by decide +kernel)
def block13 : List CallState := ((nextList 2 wires2).drop 30).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed13 : AllRejected 7 block13 := checkedBlock (by decide +kernel)
def block14 : List CallState := ((nextList 2 wires2).drop 31).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed14 : AllRejected 7 block14 := checkedBlock (by decide +kernel)
def block15 : List CallState := ((nextList 2 wires2).drop 34).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed15 : AllRejected 7 block15 := checkedBlock (by decide +kernel)
def block16 : List CallState := ((nextList 2 wires2).drop 36).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed16 : AllRejected 7 block16 := checkedBlock (by decide +kernel)
def block17 : List CallState := ((nextList 2 wires2).drop 40).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed17 : AllRejected 7 block17 := checkedBlock (by decide +kernel)
def block18 : List CallState := ((nextList 2 wires2).drop 42).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed18 : AllRejected 7 block18 := checkedBlock (by decide +kernel)
def block19 : List CallState := ((nextList 2 wires2).drop 46).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed19 : AllRejected 7 block19 := checkedBlock (by decide +kernel)
def block20 : List CallState := ((nextList 2 wires2).drop 51).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed20 : AllRejected 7 block20 := checkedBlock (by decide +kernel)
def block21 : List CallState := ((nextList 2 wires2).drop 52).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed21 : AllRejected 7 block21 := checkedBlock (by decide +kernel)
def block22 : List CallState := ((nextList 2 wires2).drop 57).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed22 : AllRejected 7 block22 := checkedBlock (by decide +kernel)
def block23 : List CallState := ((nextList 2 wires2).drop 64).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed23 : AllRejected 7 block23 := checkedBlock (by decide +kernel)
def block24 : List CallState := ((nextList 2 wires2).drop 71).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed24 : AllRejected 7 block24 := checkedBlock (by decide +kernel)
def block25 : List CallState := ((nextList 2 wires2).drop 76).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed25 : AllRejected 7 block25 := checkedBlock (by decide +kernel)
def block26 : List CallState := ((nextList 2 wires2).drop 81).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed26 : AllRejected 7 block26 := checkedBlock (by decide +kernel)
def block27 : List CallState := ((nextList 2 wires2).drop 84).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed27 : AllRejected 7 block27 := checkedBlock (by decide +kernel)
def block28 : List CallState := ((nextList 2 wires2).drop 90).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed28 : AllRejected 7 block28 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node2 : walk 8 2 wires2 = false := by
  have rest := (appendOk closed6 (appendOk closed7 (appendOk closed8 (appendOk closed9 (appendOk closed10 (appendOk closed11 (appendOk closed12 (appendOk closed13 (appendOk closed14 (appendOk closed15 (appendOk closed16 (appendOk closed17 (appendOk closed18 (appendOk closed19 (appendOk closed20 (appendOk closed21 (appendOk closed22 (appendOk closed23 (appendOk closed24 (appendOk closed25 (appendOk closed26 (appendOk closed27 (appendOk closed28 (emptyOk 7))))))))))))))))))))))))
  exact split_walk (k := 7) (e := 2) (ws := wires2) (by decide +kernel) (by decide +kernel) rest
def wires3 : List ℕ := [v8,v0,v1,v2,v3,v4,v5,v6]
def block29 : List CallState := ((nextList 1 wires3).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed29 : AllRejected 7 block29 := checkedBlock (by decide +kernel)
def block30 : List CallState := ((nextList 1 wires3).drop 10).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed30 : AllRejected 7 block30 := checkedBlock (by decide +kernel)
def block31 : List CallState := ((nextList 1 wires3).drop 16).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed31 : AllRejected 7 block31 := checkedBlock (by decide +kernel)
def block32 : List CallState := ((nextList 1 wires3).drop 26).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed32 : AllRejected 7 block32 := checkedBlock (by decide +kernel)
def block33 : List CallState := ((nextList 1 wires3).drop 33).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed33 : AllRejected 7 block33 := checkedBlock (by decide +kernel)
def block34 : List CallState := ((nextList 1 wires3).drop 43).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed34 : AllRejected 7 block34 := checkedBlock (by decide +kernel)
def block35 : List CallState := ((nextList 1 wires3).drop 50).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed35 : AllRejected 7 block35 := checkedBlock (by decide +kernel)
def block36 : List CallState := ((nextList 1 wires3).drop 57).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed36 : AllRejected 7 block36 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node3 : walk 8 1 wires3 = false := by
  have rest := (appendOk closed29 (appendOk closed30 (appendOk closed31 (appendOk closed32 (appendOk closed33 (appendOk closed34 (appendOk closed35 (appendOk closed36 (emptyOk 7)))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires3) (by decide +kernel) (by decide +kernel) rest
def wires4 : List ℕ := [v9,v0,v1,v2,v3,v4,v5,v6]
def block37 : List CallState := ((nextList 1 wires4).drop 0).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed37 : AllRejected 7 block37 := checkedBlock (by decide +kernel)
def block38 : List CallState := ((nextList 1 wires4).drop 8).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed38 : AllRejected 7 block38 := checkedBlock (by decide +kernel)
def block39 : List CallState := ((nextList 1 wires4).drop 15).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed39 : AllRejected 7 block39 := checkedBlock (by decide +kernel)
def block40 : List CallState := ((nextList 1 wires4).drop 21).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed40 : AllRejected 7 block40 := checkedBlock (by decide +kernel)
def block41 : List CallState := ((nextList 1 wires4).drop 27).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed41 : AllRejected 7 block41 := checkedBlock (by decide +kernel)
def block42 : List CallState := ((nextList 1 wires4).drop 34).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed42 : AllRejected 7 block42 := checkedBlock (by decide +kernel)
def block43 : List CallState := ((nextList 1 wires4).drop 41).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed43 : AllRejected 7 block43 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node4 : walk 8 1 wires4 = false := by
  have rest := (appendOk closed37 (appendOk closed38 (appendOk closed39 (appendOk closed40 (appendOk closed41 (appendOk closed42 (appendOk closed43 (emptyOk 7))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires4) (by decide +kernel) (by decide +kernel) rest
def wires5 : List ℕ := [v10,v0,v2,v3,v4,v5,v6]
def block44 : List CallState := ((nextList 2 wires5).drop 0).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed44 : AllRejected 7 block44 := checkedBlock (by decide +kernel)
def block45 : List CallState := ((nextList 2 wires5).drop 6).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed45 : AllRejected 7 block45 := checkedBlock (by decide +kernel)
def block46 : List CallState := ((nextList 2 wires5).drop 13).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed46 : AllRejected 7 block46 := checkedBlock (by decide +kernel)
def block47 : List CallState := ((nextList 2 wires5).drop 22).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed47 : AllRejected 7 block47 := checkedBlock (by decide +kernel)
def block48 : List CallState := ((nextList 2 wires5).drop 28).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed48 : AllRejected 7 block48 := checkedBlock (by decide +kernel)
def block49 : List CallState := ((nextList 2 wires5).drop 31).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed49 : AllRejected 7 block49 := checkedBlock (by decide +kernel)
def block50 : List CallState := ((nextList 2 wires5).drop 37).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed50 : AllRejected 7 block50 := checkedBlock (by decide +kernel)
def block51 : List CallState := ((nextList 2 wires5).drop 43).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed51 : AllRejected 7 block51 := checkedBlock (by decide +kernel)
def block52 : List CallState := ((nextList 2 wires5).drop 48).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed52 : AllRejected 7 block52 := checkedBlock (by decide +kernel)
def block53 : List CallState := ((nextList 2 wires5).drop 56).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed53 : AllRejected 7 block53 := checkedBlock (by decide +kernel)
def block54 : List CallState := ((nextList 2 wires5).drop 64).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed54 : AllRejected 7 block54 := checkedBlock (by decide +kernel)
def block55 : List CallState := ((nextList 2 wires5).drop 72).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed55 : AllRejected 7 block55 := checkedBlock (by decide +kernel)
def block56 : List CallState := ((nextList 2 wires5).drop 80).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed56 : AllRejected 7 block56 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node5 : walk 8 2 wires5 = false := by
  have rest := (appendOk closed44 (appendOk closed45 (appendOk closed46 (appendOk closed47 (appendOk closed48 (appendOk closed49 (appendOk closed50 (appendOk closed51 (appendOk closed52 (appendOk closed53 (appendOk closed54 (appendOk closed55 (appendOk closed56 (emptyOk 7))))))))))))))
  exact split_walk (k := 7) (e := 2) (ws := wires5) (by decide +kernel) (by decide +kernel) rest
def wires6 : List ℕ := [v10,v0,v1,v2,v3,v4,v5,v6]
def block57 : List CallState := ((nextList 1 wires6).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed57 : AllRejected 7 block57 := checkedBlock (by decide +kernel)
def block58 : List CallState := ((nextList 1 wires6).drop 11).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed58 : AllRejected 7 block58 := checkedBlock (by decide +kernel)
def block59 : List CallState := ((nextList 1 wires6).drop 18).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed59 : AllRejected 7 block59 := checkedBlock (by decide +kernel)
def block60 : List CallState := ((nextList 1 wires6).drop 26).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed60 : AllRejected 7 block60 := checkedBlock (by decide +kernel)
def block61 : List CallState := ((nextList 1 wires6).drop 32).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed61 : AllRejected 7 block61 := checkedBlock (by decide +kernel)
def block62 : List CallState := ((nextList 1 wires6).drop 40).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed62 : AllRejected 7 block62 := checkedBlock (by decide +kernel)
def block63 : List CallState := ((nextList 1 wires6).drop 46).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed63 : AllRejected 7 block63 := checkedBlock (by decide +kernel)
def block64 : List CallState := ((nextList 1 wires6).drop 54).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed64 : AllRejected 7 block64 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node6 : walk 8 1 wires6 = false := by
  have rest := (appendOk closed57 (appendOk closed58 (appendOk closed59 (appendOk closed60 (appendOk closed61 (appendOk closed62 (appendOk closed63 (appendOk closed64 (emptyOk 7)))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires6) (by decide +kernel) (by decide +kernel) rest
def wires7 : List ℕ := [v11,v0,v2,v1,v3,v4,v5,v6]
def block65 : List CallState := ((nextList 1 wires7).drop 0).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed65 : AllRejected 7 block65 := checkedBlock (by decide +kernel)
def block66 : List CallState := ((nextList 1 wires7).drop 6).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed66 : AllRejected 7 block66 := checkedBlock (by decide +kernel)
def block67 : List CallState := ((nextList 1 wires7).drop 13).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed67 : AllRejected 7 block67 := checkedBlock (by decide +kernel)
def block68 : List CallState := ((nextList 1 wires7).drop 19).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed68 : AllRejected 7 block68 := checkedBlock (by decide +kernel)
def block69 : List CallState := ((nextList 1 wires7).drop 25).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed69 : AllRejected 7 block69 := checkedBlock (by decide +kernel)
def block70 : List CallState := ((nextList 1 wires7).drop 33).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed70 : AllRejected 7 block70 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node7 : walk 8 1 wires7 = false := by
  have rest := (appendOk closed65 (appendOk closed66 (appendOk closed67 (appendOk closed68 (appendOk closed69 (appendOk closed70 (emptyOk 7)))))))
  exact split_walk (k := 7) (e := 1) (ws := wires7) (by decide +kernel) (by decide +kernel) rest
def wires8 : List ℕ := [v12,v0,v1,v3,v4,v5,v6]
def block71 : List CallState := ((nextList 2 wires8).drop 0).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed71 : AllRejected 7 block71 := checkedBlock (by decide +kernel)
def block72 : List CallState := ((nextList 2 wires8).drop 5).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed72 : AllRejected 7 block72 := checkedBlock (by decide +kernel)
def block73 : List CallState := ((nextList 2 wires8).drop 9).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed73 : AllRejected 7 block73 := checkedBlock (by decide +kernel)
def block74 : List CallState := ((nextList 2 wires8).drop 10).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed74 : AllRejected 7 block74 := checkedBlock (by decide +kernel)
def block75 : List CallState := ((nextList 2 wires8).drop 15).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed75 : AllRejected 7 block75 := checkedBlock (by decide +kernel)
def block76 : List CallState := ((nextList 2 wires8).drop 22).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed76 : AllRejected 7 block76 := checkedBlock (by decide +kernel)
def block77 : List CallState := ((nextList 2 wires8).drop 27).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed77 : AllRejected 7 block77 := checkedBlock (by decide +kernel)
def block78 : List CallState := ((nextList 2 wires8).drop 30).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed78 : AllRejected 7 block78 := checkedBlock (by decide +kernel)
def block79 : List CallState := ((nextList 2 wires8).drop 32).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed79 : AllRejected 7 block79 := checkedBlock (by decide +kernel)
def block80 : List CallState := ((nextList 2 wires8).drop 34).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed80 : AllRejected 7 block80 := checkedBlock (by decide +kernel)
def block81 : List CallState := ((nextList 2 wires8).drop 38).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed81 : AllRejected 7 block81 := checkedBlock (by decide +kernel)
def block82 : List CallState := ((nextList 2 wires8).drop 41).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed82 : AllRejected 7 block82 := checkedBlock (by decide +kernel)
def block83 : List CallState := ((nextList 2 wires8).drop 43).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed83 : AllRejected 7 block83 := checkedBlock (by decide +kernel)
def block84 : List CallState := ((nextList 2 wires8).drop 47).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed84 : AllRejected 7 block84 := checkedBlock (by decide +kernel)
def block85 : List CallState := ((nextList 2 wires8).drop 49).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed85 : AllRejected 7 block85 := checkedBlock (by decide +kernel)
def block86 : List CallState := ((nextList 2 wires8).drop 55).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed86 : AllRejected 7 block86 := checkedBlock (by decide +kernel)
def block87 : List CallState := ((nextList 2 wires8).drop 62).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed87 : AllRejected 7 block87 := checkedBlock (by decide +kernel)
def block88 : List CallState := ((nextList 2 wires8).drop 70).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed88 : AllRejected 7 block88 := checkedBlock (by decide +kernel)
def block89 : List CallState := ((nextList 2 wires8).drop 76).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed89 : AllRejected 7 block89 := checkedBlock (by decide +kernel)
def block90 : List CallState := ((nextList 2 wires8).drop 82).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed90 : AllRejected 7 block90 := checkedBlock (by decide +kernel)
def block91 : List CallState := ((nextList 2 wires8).drop 88).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed91 : AllRejected 7 block91 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node8 : walk 8 2 wires8 = false := by
  have rest := (appendOk closed71 (appendOk closed72 (appendOk closed73 (appendOk closed74 (appendOk closed75 (appendOk closed76 (appendOk closed77 (appendOk closed78 (appendOk closed79 (appendOk closed80 (appendOk closed81 (appendOk closed82 (appendOk closed83 (appendOk closed84 (appendOk closed85 (appendOk closed86 (appendOk closed87 (appendOk closed88 (appendOk closed89 (appendOk closed90 (appendOk closed91 (emptyOk 7))))))))))))))))))))))
  exact split_walk (k := 7) (e := 2) (ws := wires8) (by decide +kernel) (by decide +kernel) rest
def wires9 : List ℕ := [v12,v0,v2,v1,v3,v4,v5,v6]
def block92 : List CallState := ((nextList 1 wires9).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed92 : AllRejected 7 block92 := checkedBlock (by decide +kernel)
def block93 : List CallState := ((nextList 1 wires9).drop 11).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed93 : AllRejected 7 block93 := checkedBlock (by decide +kernel)
def block94 : List CallState := ((nextList 1 wires9).drop 19).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed94 : AllRejected 7 block94 := checkedBlock (by decide +kernel)
def block95 : List CallState := ((nextList 1 wires9).drop 27).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed95 : AllRejected 7 block95 := checkedBlock (by decide +kernel)
def block96 : List CallState := ((nextList 1 wires9).drop 33).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed96 : AllRejected 7 block96 := checkedBlock (by decide +kernel)
def block97 : List CallState := ((nextList 1 wires9).drop 44).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed97 : AllRejected 7 block97 := checkedBlock (by decide +kernel)
def block98 : List CallState := ((nextList 1 wires9).drop 51).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed98 : AllRejected 7 block98 := checkedBlock (by decide +kernel)
def block99 : List CallState := ((nextList 1 wires9).drop 56).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed99 : AllRejected 7 block99 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node9 : walk 8 1 wires9 = false := by
  have rest := (appendOk closed92 (appendOk closed93 (appendOk closed94 (appendOk closed95 (appendOk closed96 (appendOk closed97 (appendOk closed98 (appendOk closed99 (emptyOk 7)))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires9) (by decide +kernel) (by decide +kernel) rest
def wires10 : List ℕ := [v13,v0,v2,v1,v3,v4,v5,v6]
def block100 : List CallState := ((nextList 1 wires10).drop 0).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed100 : AllRejected 7 block100 := checkedBlock (by decide +kernel)
def block101 : List CallState := ((nextList 1 wires10).drop 8).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed101 : AllRejected 7 block101 := checkedBlock (by decide +kernel)
def block102 : List CallState := ((nextList 1 wires10).drop 15).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed102 : AllRejected 7 block102 := checkedBlock (by decide +kernel)
def block103 : List CallState := ((nextList 1 wires10).drop 21).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed103 : AllRejected 7 block103 := checkedBlock (by decide +kernel)
def block104 : List CallState := ((nextList 1 wires10).drop 28).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed104 : AllRejected 7 block104 := checkedBlock (by decide +kernel)
def block105 : List CallState := ((nextList 1 wires10).drop 35).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed105 : AllRejected 7 block105 := checkedBlock (by decide +kernel)
def block106 : List CallState := ((nextList 1 wires10).drop 42).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed106 : AllRejected 7 block106 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node10 : walk 8 1 wires10 = false := by
  have rest := (appendOk closed100 (appendOk closed101 (appendOk closed102 (appendOk closed103 (appendOk closed104 (appendOk closed105 (appendOk closed106 (emptyOk 7))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires10) (by decide +kernel) (by decide +kernel) rest
def wires11 : List ℕ := [v14,v0,v1,v3,v4,v5,v6]
def block107 : List CallState := ((nextList 2 wires11).drop 0).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed107 : AllRejected 7 block107 := checkedBlock (by decide +kernel)
def block108 : List CallState := ((nextList 2 wires11).drop 4).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed108 : AllRejected 7 block108 := checkedBlock (by decide +kernel)
def wires12 : List ℕ := [v15,v0,v1,v4,v5,v6]
def block109 : List CallState := ((nextList 2 wires12).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed109 : AllRejected 6 block109 := checkedBlock (by decide +kernel)
def block110 : List CallState := ((nextList 2 wires12).drop 14).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed110 : AllRejected 6 block110 := checkedBlock (by decide +kernel)
def block111 : List CallState := ((nextList 2 wires12).drop 26).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed111 : AllRejected 6 block111 := checkedBlock (by decide +kernel)
def block112 : List CallState := ((nextList 2 wires12).drop 36).take 15
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed112 : AllRejected 6 block112 := checkedBlock (by decide +kernel)
def block113 : List CallState := ((nextList 2 wires12).drop 51).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed113 : AllRejected 6 block113 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node12 : walk 7 2 wires12 = false := by
  have rest := (appendOk closed109 (appendOk closed110 (appendOk closed111 (appendOk closed112 (appendOk closed113 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 2) (ws := wires12) (by decide +kernel) (by decide +kernel) rest
def block114 : List CallState := ((nextList 2 wires11).drop 10).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed114 : AllRejected 7 block114 := checkedBlock (by decide +kernel)
def block115 : List CallState := ((nextList 2 wires11).drop 11).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed115 : AllRejected 7 block115 := checkedBlock (by decide +kernel)
def block116 : List CallState := ((nextList 2 wires11).drop 12).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed116 : AllRejected 7 block116 := checkedBlock (by decide +kernel)
def block117 : List CallState := ((nextList 2 wires11).drop 15).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed117 : AllRejected 7 block117 := checkedBlock (by decide +kernel)
def block118 : List CallState := ((nextList 2 wires11).drop 19).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed118 : AllRejected 7 block118 := checkedBlock (by decide +kernel)
def block119 : List CallState := ((nextList 2 wires11).drop 21).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed119 : AllRejected 7 block119 := checkedBlock (by decide +kernel)
def block120 : List CallState := ((nextList 2 wires11).drop 25).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed120 : AllRejected 7 block120 := checkedBlock (by decide +kernel)
def block121 : List CallState := ((nextList 2 wires11).drop 29).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed121 : AllRejected 7 block121 := checkedBlock (by decide +kernel)
def block122 : List CallState := ((nextList 2 wires11).drop 32).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed122 : AllRejected 7 block122 := checkedBlock (by decide +kernel)
def block123 : List CallState := ((nextList 2 wires11).drop 35).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed123 : AllRejected 7 block123 := checkedBlock (by decide +kernel)
def block124 : List CallState := ((nextList 2 wires11).drop 37).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed124 : AllRejected 7 block124 := checkedBlock (by decide +kernel)
def block125 : List CallState := ((nextList 2 wires11).drop 39).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed125 : AllRejected 7 block125 := checkedBlock (by decide +kernel)
def block126 : List CallState := ((nextList 2 wires11).drop 41).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed126 : AllRejected 7 block126 := checkedBlock (by decide +kernel)
def block127 : List CallState := ((nextList 2 wires11).drop 44).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed127 : AllRejected 7 block127 := checkedBlock (by decide +kernel)
def block128 : List CallState := ((nextList 2 wires11).drop 47).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed128 : AllRejected 7 block128 := checkedBlock (by decide +kernel)
def block129 : List CallState := ((nextList 2 wires11).drop 50).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed129 : AllRejected 7 block129 := checkedBlock (by decide +kernel)
def block130 : List CallState := ((nextList 2 wires11).drop 55).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed130 : AllRejected 7 block130 := checkedBlock (by decide +kernel)
def block131 : List CallState := ((nextList 2 wires11).drop 59).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed131 : AllRejected 7 block131 := checkedBlock (by decide +kernel)
def block132 : List CallState := ((nextList 2 wires11).drop 64).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed132 : AllRejected 7 block132 := checkedBlock (by decide +kernel)
def block133 : List CallState := ((nextList 2 wires11).drop 70).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed133 : AllRejected 7 block133 := checkedBlock (by decide +kernel)
def block134 : List CallState := ((nextList 2 wires11).drop 74).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed134 : AllRejected 7 block134 := checkedBlock (by decide +kernel)
def block135 : List CallState := ((nextList 2 wires11).drop 78).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed135 : AllRejected 7 block135 := checkedBlock (by decide +kernel)
def block136 : List CallState := ((nextList 2 wires11).drop 83).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed136 : AllRejected 7 block136 := checkedBlock (by decide +kernel)
def block137 : List CallState := ((nextList 2 wires11).drop 88).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed137 : AllRejected 7 block137 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node11 : walk 8 2 wires11 = false := by
  have rest := (appendOk closed107 (appendOk closed108 (consOk node12 (appendOk closed114 (appendOk closed115 (appendOk closed116 (appendOk closed117 (appendOk closed118 (appendOk closed119 (appendOk closed120 (appendOk closed121 (appendOk closed122 (appendOk closed123 (appendOk closed124 (appendOk closed125 (appendOk closed126 (appendOk closed127 (appendOk closed128 (appendOk closed129 (appendOk closed130 (appendOk closed131 (appendOk closed132 (appendOk closed133 (appendOk closed134 (appendOk closed135 (appendOk closed136 (appendOk closed137 (emptyOk 7))))))))))))))))))))))))))))
  exact split_walk (k := 7) (e := 2) (ws := wires11) (by decide +kernel) (by decide +kernel) rest
def wires13 : List ℕ := [v14,v0,v2,v1,v3,v4,v5,v6]
def block138 : List CallState := ((nextList 1 wires13).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed138 : AllRejected 7 block138 := checkedBlock (by decide +kernel)
def block139 : List CallState := ((nextList 1 wires13).drop 9).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed139 : AllRejected 7 block139 := checkedBlock (by decide +kernel)
def block140 : List CallState := ((nextList 1 wires13).drop 12).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed140 : AllRejected 7 block140 := checkedBlock (by decide +kernel)
def block141 : List CallState := ((nextList 1 wires13).drop 13).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed141 : AllRejected 7 block141 := checkedBlock (by decide +kernel)
def block142 : List CallState := ((nextList 1 wires13).drop 18).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed142 : AllRejected 7 block142 := checkedBlock (by decide +kernel)
def block143 : List CallState := ((nextList 1 wires13).drop 25).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed143 : AllRejected 7 block143 := checkedBlock (by decide +kernel)
def block144 : List CallState := ((nextList 1 wires13).drop 31).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed144 : AllRejected 7 block144 := checkedBlock (by decide +kernel)
def block145 : List CallState := ((nextList 1 wires13).drop 35).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed145 : AllRejected 7 block145 := checkedBlock (by decide +kernel)
def block146 : List CallState := ((nextList 1 wires13).drop 40).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed146 : AllRejected 7 block146 := checkedBlock (by decide +kernel)
def block147 : List CallState := ((nextList 1 wires13).drop 46).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed147 : AllRejected 7 block147 := checkedBlock (by decide +kernel)
def block148 : List CallState := ((nextList 1 wires13).drop 50).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed148 : AllRejected 7 block148 := checkedBlock (by decide +kernel)
def block149 : List CallState := ((nextList 1 wires13).drop 52).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed149 : AllRejected 7 block149 := checkedBlock (by decide +kernel)
def block150 : List CallState := ((nextList 1 wires13).drop 55).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed150 : AllRejected 7 block150 := checkedBlock (by decide +kernel)
def block151 : List CallState := ((nextList 1 wires13).drop 58).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed151 : AllRejected 7 block151 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node13 : walk 8 1 wires13 = false := by
  have rest := (appendOk closed138 (appendOk closed139 (appendOk closed140 (appendOk closed141 (appendOk closed142 (appendOk closed143 (appendOk closed144 (appendOk closed145 (appendOk closed146 (appendOk closed147 (appendOk closed148 (appendOk closed149 (appendOk closed150 (appendOk closed151 (emptyOk 7)))))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires13) (by decide +kernel) (by decide +kernel) rest
def wires14 : List ℕ := [v16,v0,v3,v1,v2,v4,v5,v6]
def block152 : List CallState := ((nextList 1 wires14).drop 0).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed152 : AllRejected 7 block152 := checkedBlock (by decide +kernel)
def block153 : List CallState := ((nextList 1 wires14).drop 6).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed153 : AllRejected 7 block153 := checkedBlock (by decide +kernel)
def block154 : List CallState := ((nextList 1 wires14).drop 10).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed154 : AllRejected 7 block154 := checkedBlock (by decide +kernel)
def block155 : List CallState := ((nextList 1 wires14).drop 14).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed155 : AllRejected 7 block155 := checkedBlock (by decide +kernel)
def block156 : List CallState := ((nextList 1 wires14).drop 18).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed156 : AllRejected 7 block156 := checkedBlock (by decide +kernel)
def block157 : List CallState := ((nextList 1 wires14).drop 21).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed157 : AllRejected 7 block157 := checkedBlock (by decide +kernel)
def block158 : List CallState := ((nextList 1 wires14).drop 23).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed158 : AllRejected 7 block158 := checkedBlock (by decide +kernel)
def block159 : List CallState := ((nextList 1 wires14).drop 24).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed159 : AllRejected 7 block159 := checkedBlock (by decide +kernel)
def block160 : List CallState := ((nextList 1 wires14).drop 26).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed160 : AllRejected 7 block160 := checkedBlock (by decide +kernel)
def block161 : List CallState := ((nextList 1 wires14).drop 28).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed161 : AllRejected 7 block161 := checkedBlock (by decide +kernel)
def block162 : List CallState := ((nextList 1 wires14).drop 31).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed162 : AllRejected 7 block162 := checkedBlock (by decide +kernel)
def block163 : List CallState := ((nextList 1 wires14).drop 32).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed163 : AllRejected 7 block163 := checkedBlock (by decide +kernel)
def block164 : List CallState := ((nextList 1 wires14).drop 34).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed164 : AllRejected 7 block164 := checkedBlock (by decide +kernel)
def block165 : List CallState := ((nextList 1 wires14).drop 36).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed165 : AllRejected 7 block165 := checkedBlock (by decide +kernel)
def block166 : List CallState := ((nextList 1 wires14).drop 39).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed166 : AllRejected 7 block166 := checkedBlock (by decide +kernel)
def block167 : List CallState := ((nextList 1 wires14).drop 40).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed167 : AllRejected 7 block167 := checkedBlock (by decide +kernel)
def block168 : List CallState := ((nextList 1 wires14).drop 42).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed168 : AllRejected 7 block168 := checkedBlock (by decide +kernel)
def block169 : List CallState := ((nextList 1 wires14).drop 44).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed169 : AllRejected 7 block169 := checkedBlock (by decide +kernel)
def block170 : List CallState := ((nextList 1 wires14).drop 46).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed170 : AllRejected 7 block170 := checkedBlock (by decide +kernel)
def block171 : List CallState := ((nextList 1 wires14).drop 48).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed171 : AllRejected 7 block171 := checkedBlock (by decide +kernel)
def block172 : List CallState := ((nextList 1 wires14).drop 50).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed172 : AllRejected 7 block172 := checkedBlock (by decide +kernel)
def block173 : List CallState := ((nextList 1 wires14).drop 51).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed173 : AllRejected 7 block173 := checkedBlock (by decide +kernel)
def block174 : List CallState := ((nextList 1 wires14).drop 52).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed174 : AllRejected 7 block174 := checkedBlock (by decide +kernel)
def block175 : List CallState := ((nextList 1 wires14).drop 53).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed175 : AllRejected 7 block175 := checkedBlock (by decide +kernel)
def wires15 : List ℕ := [v17,v16,v0,v1,v4,v5,v6]
def block176 : List CallState := ((nextList 1 wires15).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed176 : AllRejected 6 block176 := checkedBlock (by decide +kernel)
def block177 : List CallState := ((nextList 1 wires15).drop 9).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed177 : AllRejected 6 block177 := checkedBlock (by decide +kernel)
def block178 : List CallState := ((nextList 1 wires15).drop 18).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed178 : AllRejected 6 block178 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node15 : walk 7 1 wires15 = false := by
  have rest := (appendOk closed176 (appendOk closed177 (appendOk closed178 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires15) (by decide +kernel) (by decide +kernel) rest
def block179 : List CallState := ((nextList 1 wires14).drop 55).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed179 : AllRejected 7 block179 := checkedBlock (by decide +kernel)
def block180 : List CallState := ((nextList 1 wires14).drop 58).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed180 : AllRejected 7 block180 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node14 : walk 8 1 wires14 = false := by
  have rest := (appendOk closed152 (appendOk closed153 (appendOk closed154 (appendOk closed155 (appendOk closed156 (appendOk closed157 (appendOk closed158 (appendOk closed159 (appendOk closed160 (appendOk closed161 (appendOk closed162 (appendOk closed163 (appendOk closed164 (appendOk closed165 (appendOk closed166 (appendOk closed167 (appendOk closed168 (appendOk closed169 (appendOk closed170 (appendOk closed171 (appendOk closed172 (appendOk closed173 (appendOk closed174 (appendOk closed175 (consOk node15 (appendOk closed179 (appendOk closed180 (emptyOk 7))))))))))))))))))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires14) (by decide +kernel) (by decide +kernel) rest
def wires16 : List ℕ := [v18,v0,v3,v1,v2,v4,v5,v6]
def block181 : List CallState := ((nextList 1 wires16).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed181 : AllRejected 7 block181 := checkedBlock (by decide +kernel)
def block182 : List CallState := ((nextList 1 wires16).drop 11).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed182 : AllRejected 7 block182 := checkedBlock (by decide +kernel)
def block183 : List CallState := ((nextList 1 wires16).drop 12).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed183 : AllRejected 7 block183 := checkedBlock (by decide +kernel)
def block184 : List CallState := ((nextList 1 wires16).drop 18).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed184 : AllRejected 7 block184 := checkedBlock (by decide +kernel)
def block185 : List CallState := ((nextList 1 wires16).drop 26).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed185 : AllRejected 7 block185 := checkedBlock (by decide +kernel)
def block186 : List CallState := ((nextList 1 wires16).drop 30).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed186 : AllRejected 7 block186 := checkedBlock (by decide +kernel)
def block187 : List CallState := ((nextList 1 wires16).drop 33).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed187 : AllRejected 7 block187 := checkedBlock (by decide +kernel)
def block188 : List CallState := ((nextList 1 wires16).drop 38).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed188 : AllRejected 7 block188 := checkedBlock (by decide +kernel)
def block189 : List CallState := ((nextList 1 wires16).drop 44).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed189 : AllRejected 7 block189 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node16 : walk 8 1 wires16 = false := by
  have rest := (appendOk closed181 (appendOk closed182 (appendOk closed183 (appendOk closed184 (appendOk closed185 (appendOk closed186 (appendOk closed187 (appendOk closed188 (appendOk closed189 (emptyOk 7))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires16) (by decide +kernel) (by decide +kernel) rest
def wires17 : List ℕ := [v19,v0,v3,v1,v2,v4,v5,v6]
def block190 : List CallState := ((nextList 1 wires17).drop 0).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed190 : AllRejected 7 block190 := checkedBlock (by decide +kernel)
def block191 : List CallState := ((nextList 1 wires17).drop 5).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed191 : AllRejected 7 block191 := checkedBlock (by decide +kernel)
def block192 : List CallState := ((nextList 1 wires17).drop 11).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed192 : AllRejected 7 block192 := checkedBlock (by decide +kernel)
def block193 : List CallState := ((nextList 1 wires17).drop 16).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed193 : AllRejected 7 block193 := checkedBlock (by decide +kernel)
def block194 : List CallState := ((nextList 1 wires17).drop 21).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed194 : AllRejected 7 block194 := checkedBlock (by decide +kernel)
def block195 : List CallState := ((nextList 1 wires17).drop 26).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed195 : AllRejected 7 block195 := checkedBlock (by decide +kernel)
def block196 : List CallState := ((nextList 1 wires17).drop 31).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed196 : AllRejected 7 block196 := checkedBlock (by decide +kernel)
def block197 : List CallState := ((nextList 1 wires17).drop 38).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed197 : AllRejected 7 block197 := checkedBlock (by decide +kernel)
def block198 : List CallState := ((nextList 1 wires17).drop 42).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed198 : AllRejected 7 block198 := checkedBlock (by decide +kernel)
def block199 : List CallState := ((nextList 1 wires17).drop 46).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed199 : AllRejected 7 block199 := checkedBlock (by decide +kernel)
def block200 : List CallState := ((nextList 1 wires17).drop 47).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed200 : AllRejected 7 block200 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node17 : walk 8 1 wires17 = false := by
  have rest := (appendOk closed190 (appendOk closed191 (appendOk closed192 (appendOk closed193 (appendOk closed194 (appendOk closed195 (appendOk closed196 (appendOk closed197 (appendOk closed198 (appendOk closed199 (appendOk closed200 (emptyOk 7))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires17) (by decide +kernel) (by decide +kernel) rest
def wires18 : List ℕ := [v20,v0,v3,v1,v2,v4,v5,v6]
def block201 : List CallState := ((nextList 1 wires18).drop 0).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed201 : AllRejected 7 block201 := checkedBlock (by decide +kernel)
def block202 : List CallState := ((nextList 1 wires18).drop 5).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed202 : AllRejected 7 block202 := checkedBlock (by decide +kernel)
def block203 : List CallState := ((nextList 1 wires18).drop 11).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed203 : AllRejected 7 block203 := checkedBlock (by decide +kernel)
def block204 : List CallState := ((nextList 1 wires18).drop 15).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed204 : AllRejected 7 block204 := checkedBlock (by decide +kernel)
def block205 : List CallState := ((nextList 1 wires18).drop 22).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed205 : AllRejected 7 block205 := checkedBlock (by decide +kernel)
def block206 : List CallState := ((nextList 1 wires18).drop 29).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed206 : AllRejected 7 block206 := checkedBlock (by decide +kernel)
def block207 : List CallState := ((nextList 1 wires18).drop 36).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed207 : AllRejected 7 block207 := checkedBlock (by decide +kernel)
def block208 : List CallState := ((nextList 1 wires18).drop 43).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed208 : AllRejected 7 block208 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node18 : walk 8 1 wires18 = false := by
  have rest := (appendOk closed201 (appendOk closed202 (appendOk closed203 (appendOk closed204 (appendOk closed205 (appendOk closed206 (appendOk closed207 (appendOk closed208 (emptyOk 7)))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires18) (by decide +kernel) (by decide +kernel) rest
def wires19 : List ℕ := [v21,v0,v4,v1,v2,v3,v5,v6]
def block209 : List CallState := ((nextList 1 wires19).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed209 : AllRejected 7 block209 := checkedBlock (by decide +kernel)
def block210 : List CallState := ((nextList 1 wires19).drop 7).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed210 : AllRejected 7 block210 := checkedBlock (by decide +kernel)
def block211 : List CallState := ((nextList 1 wires19).drop 11).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed211 : AllRejected 7 block211 := checkedBlock (by decide +kernel)
def block212 : List CallState := ((nextList 1 wires19).drop 15).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed212 : AllRejected 7 block212 := checkedBlock (by decide +kernel)
def block213 : List CallState := ((nextList 1 wires19).drop 19).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed213 : AllRejected 7 block213 := checkedBlock (by decide +kernel)
def block214 : List CallState := ((nextList 1 wires19).drop 23).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed214 : AllRejected 7 block214 := checkedBlock (by decide +kernel)
def block215 : List CallState := ((nextList 1 wires19).drop 26).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed215 : AllRejected 7 block215 := checkedBlock (by decide +kernel)
def block216 : List CallState := ((nextList 1 wires19).drop 30).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed216 : AllRejected 7 block216 := checkedBlock (by decide +kernel)
def block217 : List CallState := ((nextList 1 wires19).drop 34).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed217 : AllRejected 7 block217 := checkedBlock (by decide +kernel)
def block218 : List CallState := ((nextList 1 wires19).drop 38).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed218 : AllRejected 7 block218 := checkedBlock (by decide +kernel)
def block219 : List CallState := ((nextList 1 wires19).drop 40).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed219 : AllRejected 7 block219 := checkedBlock (by decide +kernel)
def block220 : List CallState := ((nextList 1 wires19).drop 44).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed220 : AllRejected 7 block220 := checkedBlock (by decide +kernel)
def block221 : List CallState := ((nextList 1 wires19).drop 50).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed221 : AllRejected 7 block221 := checkedBlock (by decide +kernel)
def block222 : List CallState := ((nextList 1 wires19).drop 53).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed222 : AllRejected 7 block222 := checkedBlock (by decide +kernel)
def block223 : List CallState := ((nextList 1 wires19).drop 55).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed223 : AllRejected 7 block223 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node19 : walk 8 1 wires19 = false := by
  have rest := (appendOk closed209 (appendOk closed210 (appendOk closed211 (appendOk closed212 (appendOk closed213 (appendOk closed214 (appendOk closed215 (appendOk closed216 (appendOk closed217 (appendOk closed218 (appendOk closed219 (appendOk closed220 (appendOk closed221 (appendOk closed222 (appendOk closed223 (emptyOk 7))))))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires19) (by decide +kernel) (by decide +kernel) rest
def wires20 : List ℕ := [v22,v0,v4,v1,v2,v3,v5,v6]
def block224 : List CallState := ((nextList 1 wires20).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed224 : AllRejected 7 block224 := checkedBlock (by decide +kernel)
def block225 : List CallState := ((nextList 1 wires20).drop 13).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed225 : AllRejected 7 block225 := checkedBlock (by decide +kernel)
def block226 : List CallState := ((nextList 1 wires20).drop 21).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed226 : AllRejected 7 block226 := checkedBlock (by decide +kernel)
def block227 : List CallState := ((nextList 1 wires20).drop 29).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed227 : AllRejected 7 block227 := checkedBlock (by decide +kernel)
def block228 : List CallState := ((nextList 1 wires20).drop 34).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed228 : AllRejected 7 block228 := checkedBlock (by decide +kernel)
def block229 : List CallState := ((nextList 1 wires20).drop 43).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed229 : AllRejected 7 block229 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node20 : walk 8 1 wires20 = false := by
  have rest := (appendOk closed224 (appendOk closed225 (appendOk closed226 (appendOk closed227 (appendOk closed228 (appendOk closed229 (emptyOk 7)))))))
  exact split_walk (k := 7) (e := 1) (ws := wires20) (by decide +kernel) (by decide +kernel) rest
def wires21 : List ℕ := [v23,v0,v4,v1,v2,v3,v5,v6]
def block230 : List CallState := ((nextList 1 wires21).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed230 : AllRejected 7 block230 := checkedBlock (by decide +kernel)
def block231 : List CallState := ((nextList 1 wires21).drop 7).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed231 : AllRejected 7 block231 := checkedBlock (by decide +kernel)
def block232 : List CallState := ((nextList 1 wires21).drop 13).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed232 : AllRejected 7 block232 := checkedBlock (by decide +kernel)
def block233 : List CallState := ((nextList 1 wires21).drop 19).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed233 : AllRejected 7 block233 := checkedBlock (by decide +kernel)
def block234 : List CallState := ((nextList 1 wires21).drop 22).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed234 : AllRejected 7 block234 := checkedBlock (by decide +kernel)
def block235 : List CallState := ((nextList 1 wires21).drop 26).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed235 : AllRejected 7 block235 := checkedBlock (by decide +kernel)
def block236 : List CallState := ((nextList 1 wires21).drop 32).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed236 : AllRejected 7 block236 := checkedBlock (by decide +kernel)
def block237 : List CallState := ((nextList 1 wires21).drop 39).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed237 : AllRejected 7 block237 := checkedBlock (by decide +kernel)
def block238 : List CallState := ((nextList 1 wires21).drop 44).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed238 : AllRejected 7 block238 := checkedBlock (by decide +kernel)
def block239 : List CallState := ((nextList 1 wires21).drop 48).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed239 : AllRejected 7 block239 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node21 : walk 8 1 wires21 = false := by
  have rest := (appendOk closed230 (appendOk closed231 (appendOk closed232 (appendOk closed233 (appendOk closed234 (appendOk closed235 (appendOk closed236 (appendOk closed237 (appendOk closed238 (appendOk closed239 (emptyOk 7)))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires21) (by decide +kernel) (by decide +kernel) rest
def wires22 : List ℕ := [v24,v0,v4,v1,v2,v3,v5,v6]
def block240 : List CallState := ((nextList 1 wires22).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed240 : AllRejected 7 block240 := checkedBlock (by decide +kernel)
def block241 : List CallState := ((nextList 1 wires22).drop 7).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed241 : AllRejected 7 block241 := checkedBlock (by decide +kernel)
def block242 : List CallState := ((nextList 1 wires22).drop 19).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed242 : AllRejected 7 block242 := checkedBlock (by decide +kernel)
def block243 : List CallState := ((nextList 1 wires22).drop 26).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed243 : AllRejected 7 block243 := checkedBlock (by decide +kernel)
def block244 : List CallState := ((nextList 1 wires22).drop 38).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed244 : AllRejected 7 block244 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node22 : walk 8 1 wires22 = false := by
  have rest := (appendOk closed240 (appendOk closed241 (appendOk closed242 (appendOk closed243 (appendOk closed244 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires22) (by decide +kernel) (by decide +kernel) rest
def wires23 : List ℕ := [v25,v0,v5,v1,v2,v3,v4,v6]
def block245 : List CallState := ((nextList 1 wires23).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed245 : AllRejected 7 block245 := checkedBlock (by decide +kernel)
def block246 : List CallState := ((nextList 1 wires23).drop 7).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed246 : AllRejected 7 block246 := checkedBlock (by decide +kernel)
def block247 : List CallState := ((nextList 1 wires23).drop 11).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed247 : AllRejected 7 block247 := checkedBlock (by decide +kernel)
def block248 : List CallState := ((nextList 1 wires23).drop 15).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed248 : AllRejected 7 block248 := checkedBlock (by decide +kernel)
def block249 : List CallState := ((nextList 1 wires23).drop 19).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed249 : AllRejected 7 block249 := checkedBlock (by decide +kernel)
def block250 : List CallState := ((nextList 1 wires23).drop 23).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed250 : AllRejected 7 block250 := checkedBlock (by decide +kernel)
def block251 : List CallState := ((nextList 1 wires23).drop 26).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed251 : AllRejected 7 block251 := checkedBlock (by decide +kernel)
def block252 : List CallState := ((nextList 1 wires23).drop 30).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed252 : AllRejected 7 block252 := checkedBlock (by decide +kernel)
def block253 : List CallState := ((nextList 1 wires23).drop 34).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed253 : AllRejected 7 block253 := checkedBlock (by decide +kernel)
def block254 : List CallState := ((nextList 1 wires23).drop 38).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed254 : AllRejected 7 block254 := checkedBlock (by decide +kernel)
def block255 : List CallState := ((nextList 1 wires23).drop 42).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed255 : AllRejected 7 block255 := checkedBlock (by decide +kernel)
def block256 : List CallState := ((nextList 1 wires23).drop 47).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed256 : AllRejected 7 block256 := checkedBlock (by decide +kernel)
def block257 : List CallState := ((nextList 1 wires23).drop 51).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed257 : AllRejected 7 block257 := checkedBlock (by decide +kernel)
def block258 : List CallState := ((nextList 1 wires23).drop 53).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed258 : AllRejected 7 block258 := checkedBlock (by decide +kernel)
def block259 : List CallState := ((nextList 1 wires23).drop 55).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed259 : AllRejected 7 block259 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node23 : walk 8 1 wires23 = false := by
  have rest := (appendOk closed245 (appendOk closed246 (appendOk closed247 (appendOk closed248 (appendOk closed249 (appendOk closed250 (appendOk closed251 (appendOk closed252 (appendOk closed253 (appendOk closed254 (appendOk closed255 (appendOk closed256 (appendOk closed257 (appendOk closed258 (appendOk closed259 (emptyOk 7))))))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires23) (by decide +kernel) (by decide +kernel) rest
def wires24 : List ℕ := [v26,v0,v5,v1,v2,v3,v4,v6]
def block260 : List CallState := ((nextList 1 wires24).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed260 : AllRejected 7 block260 := checkedBlock (by decide +kernel)
def block261 : List CallState := ((nextList 1 wires24).drop 11).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed261 : AllRejected 7 block261 := checkedBlock (by decide +kernel)
def block262 : List CallState := ((nextList 1 wires24).drop 19).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed262 : AllRejected 7 block262 := checkedBlock (by decide +kernel)
def block263 : List CallState := ((nextList 1 wires24).drop 26).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed263 : AllRejected 7 block263 := checkedBlock (by decide +kernel)
def block264 : List CallState := ((nextList 1 wires24).drop 30).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed264 : AllRejected 7 block264 := checkedBlock (by decide +kernel)
def block265 : List CallState := ((nextList 1 wires24).drop 34).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed265 : AllRejected 7 block265 := checkedBlock (by decide +kernel)
def block266 : List CallState := ((nextList 1 wires24).drop 38).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed266 : AllRejected 7 block266 := checkedBlock (by decide +kernel)
def block267 : List CallState := ((nextList 1 wires24).drop 44).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed267 : AllRejected 7 block267 := checkedBlock (by decide +kernel)
def block268 : List CallState := ((nextList 1 wires24).drop 48).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed268 : AllRejected 7 block268 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node24 : walk 8 1 wires24 = false := by
  have rest := (appendOk closed260 (appendOk closed261 (appendOk closed262 (appendOk closed263 (appendOk closed264 (appendOk closed265 (appendOk closed266 (appendOk closed267 (appendOk closed268 (emptyOk 7))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires24) (by decide +kernel) (by decide +kernel) rest
def wires25 : List ℕ := [v27,v0,v5,v1,v2,v3,v4,v6]
def block269 : List CallState := ((nextList 1 wires25).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed269 : AllRejected 7 block269 := checkedBlock (by decide +kernel)
def block270 : List CallState := ((nextList 1 wires25).drop 7).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed270 : AllRejected 7 block270 := checkedBlock (by decide +kernel)
def block271 : List CallState := ((nextList 1 wires25).drop 12).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed271 : AllRejected 7 block271 := checkedBlock (by decide +kernel)
def block272 : List CallState := ((nextList 1 wires25).drop 18).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed272 : AllRejected 7 block272 := checkedBlock (by decide +kernel)
def block273 : List CallState := ((nextList 1 wires25).drop 21).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed273 : AllRejected 7 block273 := checkedBlock (by decide +kernel)
def block274 : List CallState := ((nextList 1 wires25).drop 25).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed274 : AllRejected 7 block274 := checkedBlock (by decide +kernel)
def block275 : List CallState := ((nextList 1 wires25).drop 30).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed275 : AllRejected 7 block275 := checkedBlock (by decide +kernel)
def block276 : List CallState := ((nextList 1 wires25).drop 37).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed276 : AllRejected 7 block276 := checkedBlock (by decide +kernel)
def block277 : List CallState := ((nextList 1 wires25).drop 42).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed277 : AllRejected 7 block277 := checkedBlock (by decide +kernel)
def block278 : List CallState := ((nextList 1 wires25).drop 47).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed278 : AllRejected 7 block278 := checkedBlock (by decide +kernel)
def block279 : List CallState := ((nextList 1 wires25).drop 51).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed279 : AllRejected 7 block279 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node25 : walk 8 1 wires25 = false := by
  have rest := (appendOk closed269 (appendOk closed270 (appendOk closed271 (appendOk closed272 (appendOk closed273 (appendOk closed274 (appendOk closed275 (appendOk closed276 (appendOk closed277 (appendOk closed278 (appendOk closed279 (emptyOk 7))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires25) (by decide +kernel) (by decide +kernel) rest
def wires26 : List ℕ := [v28,v0,v5,v1,v2,v3,v4,v6]
def block280 : List CallState := ((nextList 1 wires26).drop 0).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed280 : AllRejected 7 block280 := checkedBlock (by decide +kernel)
def block281 : List CallState := ((nextList 1 wires26).drop 6).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed281 : AllRejected 7 block281 := checkedBlock (by decide +kernel)
def block282 : List CallState := ((nextList 1 wires26).drop 14).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed282 : AllRejected 7 block282 := checkedBlock (by decide +kernel)
def block283 : List CallState := ((nextList 1 wires26).drop 21).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed283 : AllRejected 7 block283 := checkedBlock (by decide +kernel)
def block284 : List CallState := ((nextList 1 wires26).drop 30).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed284 : AllRejected 7 block284 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node26 : walk 8 1 wires26 = false := by
  have rest := (appendOk closed280 (appendOk closed281 (appendOk closed282 (appendOk closed283 (appendOk closed284 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires26) (by decide +kernel) (by decide +kernel) rest
def wires27 : List ℕ := [v29,v0,v6,v1,v2,v3,v4,v5]
def block285 : List CallState := ((nextList 1 wires27).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed285 : AllRejected 7 block285 := checkedBlock (by decide +kernel)
def block286 : List CallState := ((nextList 1 wires27).drop 7).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed286 : AllRejected 7 block286 := checkedBlock (by decide +kernel)
def block287 : List CallState := ((nextList 1 wires27).drop 11).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed287 : AllRejected 7 block287 := checkedBlock (by decide +kernel)
def block288 : List CallState := ((nextList 1 wires27).drop 15).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed288 : AllRejected 7 block288 := checkedBlock (by decide +kernel)
def block289 : List CallState := ((nextList 1 wires27).drop 19).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed289 : AllRejected 7 block289 := checkedBlock (by decide +kernel)
def block290 : List CallState := ((nextList 1 wires27).drop 23).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed290 : AllRejected 7 block290 := checkedBlock (by decide +kernel)
def block291 : List CallState := ((nextList 1 wires27).drop 26).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed291 : AllRejected 7 block291 := checkedBlock (by decide +kernel)
def block292 : List CallState := ((nextList 1 wires27).drop 30).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed292 : AllRejected 7 block292 := checkedBlock (by decide +kernel)
def block293 : List CallState := ((nextList 1 wires27).drop 33).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed293 : AllRejected 7 block293 := checkedBlock (by decide +kernel)
def block294 : List CallState := ((nextList 1 wires27).drop 38).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed294 : AllRejected 7 block294 := checkedBlock (by decide +kernel)
def block295 : List CallState := ((nextList 1 wires27).drop 42).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed295 : AllRejected 7 block295 := checkedBlock (by decide +kernel)
def block296 : List CallState := ((nextList 1 wires27).drop 47).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed296 : AllRejected 7 block296 := checkedBlock (by decide +kernel)
def block297 : List CallState := ((nextList 1 wires27).drop 51).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed297 : AllRejected 7 block297 := checkedBlock (by decide +kernel)
def block298 : List CallState := ((nextList 1 wires27).drop 53).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed298 : AllRejected 7 block298 := checkedBlock (by decide +kernel)
def block299 : List CallState := ((nextList 1 wires27).drop 55).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed299 : AllRejected 7 block299 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node27 : walk 8 1 wires27 = false := by
  have rest := (appendOk closed285 (appendOk closed286 (appendOk closed287 (appendOk closed288 (appendOk closed289 (appendOk closed290 (appendOk closed291 (appendOk closed292 (appendOk closed293 (appendOk closed294 (appendOk closed295 (appendOk closed296 (appendOk closed297 (appendOk closed298 (appendOk closed299 (emptyOk 7))))))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires27) (by decide +kernel) (by decide +kernel) rest
def wires28 : List ℕ := [v30,v0,v6,v1,v2,v3,v4,v5]
def block300 : List CallState := ((nextList 1 wires28).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed300 : AllRejected 7 block300 := checkedBlock (by decide +kernel)
def block301 : List CallState := ((nextList 1 wires28).drop 11).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed301 : AllRejected 7 block301 := checkedBlock (by decide +kernel)
def block302 : List CallState := ((nextList 1 wires28).drop 18).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed302 : AllRejected 7 block302 := checkedBlock (by decide +kernel)
def block303 : List CallState := ((nextList 1 wires28).drop 26).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed303 : AllRejected 7 block303 := checkedBlock (by decide +kernel)
def block304 : List CallState := ((nextList 1 wires28).drop 32).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed304 : AllRejected 7 block304 := checkedBlock (by decide +kernel)
def block305 : List CallState := ((nextList 1 wires28).drop 36).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed305 : AllRejected 7 block305 := checkedBlock (by decide +kernel)
def block306 : List CallState := ((nextList 1 wires28).drop 44).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed306 : AllRejected 7 block306 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node28 : walk 8 1 wires28 = false := by
  have rest := (appendOk closed300 (appendOk closed301 (appendOk closed302 (appendOk closed303 (appendOk closed304 (appendOk closed305 (appendOk closed306 (emptyOk 7))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires28) (by decide +kernel) (by decide +kernel) rest
def wires29 : List ℕ := [v31,v0,v6,v1,v2,v3,v4,v5]
def block307 : List CallState := ((nextList 1 wires29).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed307 : AllRejected 7 block307 := checkedBlock (by decide +kernel)
def block308 : List CallState := ((nextList 1 wires29).drop 7).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed308 : AllRejected 7 block308 := checkedBlock (by decide +kernel)
def block309 : List CallState := ((nextList 1 wires29).drop 12).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed309 : AllRejected 7 block309 := checkedBlock (by decide +kernel)
def block310 : List CallState := ((nextList 1 wires29).drop 19).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed310 : AllRejected 7 block310 := checkedBlock (by decide +kernel)
def block311 : List CallState := ((nextList 1 wires29).drop 22).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed311 : AllRejected 7 block311 := checkedBlock (by decide +kernel)
def block312 : List CallState := ((nextList 1 wires29).drop 26).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed312 : AllRejected 7 block312 := checkedBlock (by decide +kernel)
def block313 : List CallState := ((nextList 1 wires29).drop 32).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed313 : AllRejected 7 block313 := checkedBlock (by decide +kernel)
def block314 : List CallState := ((nextList 1 wires29).drop 40).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed314 : AllRejected 7 block314 := checkedBlock (by decide +kernel)
def block315 : List CallState := ((nextList 1 wires29).drop 45).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed315 : AllRejected 7 block315 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node29 : walk 8 1 wires29 = false := by
  have rest := (appendOk closed307 (appendOk closed308 (appendOk closed309 (appendOk closed310 (appendOk closed311 (appendOk closed312 (appendOk closed313 (appendOk closed314 (appendOk closed315 (emptyOk 7))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires29) (by decide +kernel) (by decide +kernel) rest
def wires30 : List ℕ := [v32,v0,v6,v1,v2,v3,v4,v5]
def block316 : List CallState := ((nextList 1 wires30).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed316 : AllRejected 7 block316 := checkedBlock (by decide +kernel)
def block317 : List CallState := ((nextList 1 wires30).drop 10).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed317 : AllRejected 7 block317 := checkedBlock (by decide +kernel)
def block318 : List CallState := ((nextList 1 wires30).drop 18).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed318 : AllRejected 7 block318 := checkedBlock (by decide +kernel)
def block319 : List CallState := ((nextList 1 wires30).drop 26).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed319 : AllRejected 7 block319 := checkedBlock (by decide +kernel)
def block320 : List CallState := ((nextList 1 wires30).drop 39).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed320 : AllRejected 7 block320 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node30 : walk 8 1 wires30 = false := by
  have rest := (appendOk closed316 (appendOk closed317 (appendOk closed318 (appendOk closed319 (appendOk closed320 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires30) (by decide +kernel) (by decide +kernel) rest
def wires31 : List ℕ := [v33,v1,v2,v0,v3,v4,v5,v6]
def block321 : List CallState := ((nextList 1 wires31).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed321 : AllRejected 7 block321 := checkedBlock (by decide +kernel)
def block322 : List CallState := ((nextList 1 wires31).drop 10).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed322 : AllRejected 7 block322 := checkedBlock (by decide +kernel)
def block323 : List CallState := ((nextList 1 wires31).drop 18).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed323 : AllRejected 7 block323 := checkedBlock (by decide +kernel)
def block324 : List CallState := ((nextList 1 wires31).drop 27).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed324 : AllRejected 7 block324 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node31 : walk 8 1 wires31 = false := by
  have rest := (appendOk closed321 (appendOk closed322 (appendOk closed323 (appendOk closed324 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires31) (by decide +kernel) (by decide +kernel) rest
def wires32 : List ℕ := [v34,v1,v2,v0,v3,v4,v5,v6]
def block325 : List CallState := ((nextList 1 wires32).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed325 : AllRejected 7 block325 := checkedBlock (by decide +kernel)
def block326 : List CallState := ((nextList 1 wires32).drop 10).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed326 : AllRejected 7 block326 := checkedBlock (by decide +kernel)
def block327 : List CallState := ((nextList 1 wires32).drop 19).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed327 : AllRejected 7 block327 := checkedBlock (by decide +kernel)
def block328 : List CallState := ((nextList 1 wires32).drop 32).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed328 : AllRejected 7 block328 := checkedBlock (by decide +kernel)
def block329 : List CallState := ((nextList 1 wires32).drop 44).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed329 : AllRejected 7 block329 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node32 : walk 8 1 wires32 = false := by
  have rest := (appendOk closed325 (appendOk closed326 (appendOk closed327 (appendOk closed328 (appendOk closed329 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires32) (by decide +kernel) (by decide +kernel) rest
def wires33 : List ℕ := [v35,v1,v2,v0,v3,v4,v5,v6]
def block330 : List CallState := ((nextList 1 wires33).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed330 : AllRejected 7 block330 := checkedBlock (by decide +kernel)
def block331 : List CallState := ((nextList 1 wires33).drop 10).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed331 : AllRejected 7 block331 := checkedBlock (by decide +kernel)
def block332 : List CallState := ((nextList 1 wires33).drop 18).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed332 : AllRejected 7 block332 := checkedBlock (by decide +kernel)
def block333 : List CallState := ((nextList 1 wires33).drop 28).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed333 : AllRejected 7 block333 := checkedBlock (by decide +kernel)
def block334 : List CallState := ((nextList 1 wires33).drop 37).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed334 : AllRejected 7 block334 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node33 : walk 8 1 wires33 = false := by
  have rest := (appendOk closed330 (appendOk closed331 (appendOk closed332 (appendOk closed333 (appendOk closed334 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires33) (by decide +kernel) (by decide +kernel) rest
def wires34 : List ℕ := [v36,v1,v2,v0,v3,v4,v5,v6]
def block335 : List CallState := ((nextList 1 wires34).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed335 : AllRejected 7 block335 := checkedBlock (by decide +kernel)
def block336 : List CallState := ((nextList 1 wires34).drop 9).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed336 : AllRejected 7 block336 := checkedBlock (by decide +kernel)
def block337 : List CallState := ((nextList 1 wires34).drop 18).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed337 : AllRejected 7 block337 := checkedBlock (by decide +kernel)
def block338 : List CallState := ((nextList 1 wires34).drop 26).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed338 : AllRejected 7 block338 := checkedBlock (by decide +kernel)
def block339 : List CallState := ((nextList 1 wires34).drop 34).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed339 : AllRejected 7 block339 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node34 : walk 8 1 wires34 = false := by
  have rest := (appendOk closed335 (appendOk closed336 (appendOk closed337 (appendOk closed338 (appendOk closed339 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires34) (by decide +kernel) (by decide +kernel) rest
def wires35 : List ℕ := [v37,v1,v3,v0,v2,v4,v5,v6]
def block340 : List CallState := ((nextList 1 wires35).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed340 : AllRejected 7 block340 := checkedBlock (by decide +kernel)
def block341 : List CallState := ((nextList 1 wires35).drop 9).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed341 : AllRejected 7 block341 := checkedBlock (by decide +kernel)
def block342 : List CallState := ((nextList 1 wires35).drop 16).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed342 : AllRejected 7 block342 := checkedBlock (by decide +kernel)
def block343 : List CallState := ((nextList 1 wires35).drop 24).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed343 : AllRejected 7 block343 := checkedBlock (by decide +kernel)
def block344 : List CallState := ((nextList 1 wires35).drop 34).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed344 : AllRejected 7 block344 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node35 : walk 8 1 wires35 = false := by
  have rest := (appendOk closed340 (appendOk closed341 (appendOk closed342 (appendOk closed343 (appendOk closed344 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires35) (by decide +kernel) (by decide +kernel) rest
def wires36 : List ℕ := [v38,v1,v3,v0,v2,v4,v5,v6]
def block345 : List CallState := ((nextList 1 wires36).drop 0).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed345 : AllRejected 7 block345 := checkedBlock (by decide +kernel)
def block346 : List CallState := ((nextList 1 wires36).drop 12).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed346 : AllRejected 7 block346 := checkedBlock (by decide +kernel)
def block347 : List CallState := ((nextList 1 wires36).drop 24).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed347 : AllRejected 7 block347 := checkedBlock (by decide +kernel)
def block348 : List CallState := ((nextList 1 wires36).drop 33).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed348 : AllRejected 7 block348 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node36 : walk 8 1 wires36 = false := by
  have rest := (appendOk closed345 (appendOk closed346 (appendOk closed347 (appendOk closed348 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires36) (by decide +kernel) (by decide +kernel) rest
def wires37 : List ℕ := [v39,v1,v3,v0,v2,v4,v5,v6]
def block349 : List CallState := ((nextList 1 wires37).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed349 : AllRejected 7 block349 := checkedBlock (by decide +kernel)
def block350 : List CallState := ((nextList 1 wires37).drop 11).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed350 : AllRejected 7 block350 := checkedBlock (by decide +kernel)
def block351 : List CallState := ((nextList 1 wires37).drop 21).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed351 : AllRejected 7 block351 := checkedBlock (by decide +kernel)
def block352 : List CallState := ((nextList 1 wires37).drop 32).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed352 : AllRejected 7 block352 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node37 : walk 8 1 wires37 = false := by
  have rest := (appendOk closed349 (appendOk closed350 (appendOk closed351 (appendOk closed352 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires37) (by decide +kernel) (by decide +kernel) rest
def wires38 : List ℕ := [v40,v1,v3,v0,v2,v4,v5,v6]
def block353 : List CallState := ((nextList 1 wires38).drop 0).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed353 : AllRejected 7 block353 := checkedBlock (by decide +kernel)
def block354 : List CallState := ((nextList 1 wires38).drop 8).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed354 : AllRejected 7 block354 := checkedBlock (by decide +kernel)
def block355 : List CallState := ((nextList 1 wires38).drop 14).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed355 : AllRejected 7 block355 := checkedBlock (by decide +kernel)
def block356 : List CallState := ((nextList 1 wires38).drop 21).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed356 : AllRejected 7 block356 := checkedBlock (by decide +kernel)
def block357 : List CallState := ((nextList 1 wires38).drop 26).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed357 : AllRejected 7 block357 := checkedBlock (by decide +kernel)
def block358 : List CallState := ((nextList 1 wires38).drop 32).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed358 : AllRejected 7 block358 := checkedBlock (by decide +kernel)
def block359 : List CallState := ((nextList 1 wires38).drop 40).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed359 : AllRejected 7 block359 := checkedBlock (by decide +kernel)
def block360 : List CallState := ((nextList 1 wires38).drop 47).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed360 : AllRejected 7 block360 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node38 : walk 8 1 wires38 = false := by
  have rest := (appendOk closed353 (appendOk closed354 (appendOk closed355 (appendOk closed356 (appendOk closed357 (appendOk closed358 (appendOk closed359 (appendOk closed360 (emptyOk 7)))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires38) (by decide +kernel) (by decide +kernel) rest
def wires39 : List ℕ := [v41,v1,v4,v0,v2,v3,v5,v6]
def block361 : List CallState := ((nextList 1 wires39).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed361 : AllRejected 7 block361 := checkedBlock (by decide +kernel)
def block362 : List CallState := ((nextList 1 wires39).drop 7).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed362 : AllRejected 7 block362 := checkedBlock (by decide +kernel)
def block363 : List CallState := ((nextList 1 wires39).drop 9).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed363 : AllRejected 7 block363 := checkedBlock (by decide +kernel)
def block364 : List CallState := ((nextList 1 wires39).drop 12).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed364 : AllRejected 7 block364 := checkedBlock (by decide +kernel)
def block365 : List CallState := ((nextList 1 wires39).drop 15).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed365 : AllRejected 7 block365 := checkedBlock (by decide +kernel)
def block366 : List CallState := ((nextList 1 wires39).drop 19).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed366 : AllRejected 7 block366 := checkedBlock (by decide +kernel)
def block367 : List CallState := ((nextList 1 wires39).drop 23).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed367 : AllRejected 7 block367 := checkedBlock (by decide +kernel)
def block368 : List CallState := ((nextList 1 wires39).drop 27).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed368 : AllRejected 7 block368 := checkedBlock (by decide +kernel)
def block369 : List CallState := ((nextList 1 wires39).drop 30).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed369 : AllRejected 7 block369 := checkedBlock (by decide +kernel)
def block370 : List CallState := ((nextList 1 wires39).drop 32).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed370 : AllRejected 7 block370 := checkedBlock (by decide +kernel)
def block371 : List CallState := ((nextList 1 wires39).drop 36).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed371 : AllRejected 7 block371 := checkedBlock (by decide +kernel)
def block372 : List CallState := ((nextList 1 wires39).drop 39).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed372 : AllRejected 7 block372 := checkedBlock (by decide +kernel)
def block373 : List CallState := ((nextList 1 wires39).drop 42).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed373 : AllRejected 7 block373 := checkedBlock (by decide +kernel)
def block374 : List CallState := ((nextList 1 wires39).drop 47).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed374 : AllRejected 7 block374 := checkedBlock (by decide +kernel)
def block375 : List CallState := ((nextList 1 wires39).drop 52).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed375 : AllRejected 7 block375 := checkedBlock (by decide +kernel)
def block376 : List CallState := ((nextList 1 wires39).drop 56).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed376 : AllRejected 7 block376 := checkedBlock (by decide +kernel)
def block377 : List CallState := ((nextList 1 wires39).drop 58).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed377 : AllRejected 7 block377 := checkedBlock (by decide +kernel)
def block378 : List CallState := ((nextList 1 wires39).drop 61).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed378 : AllRejected 7 block378 := checkedBlock (by decide +kernel)
def block379 : List CallState := ((nextList 1 wires39).drop 62).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed379 : AllRejected 7 block379 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node39 : walk 8 1 wires39 = false := by
  have rest := (appendOk closed361 (appendOk closed362 (appendOk closed363 (appendOk closed364 (appendOk closed365 (appendOk closed366 (appendOk closed367 (appendOk closed368 (appendOk closed369 (appendOk closed370 (appendOk closed371 (appendOk closed372 (appendOk closed373 (appendOk closed374 (appendOk closed375 (appendOk closed376 (appendOk closed377 (appendOk closed378 (appendOk closed379 (emptyOk 7))))))))))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires39) (by decide +kernel) (by decide +kernel) rest
def wires40 : List ℕ := [v42,v1,v4,v0,v2,v3,v5,v6]
def block380 : List CallState := ((nextList 1 wires40).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed380 : AllRejected 7 block380 := checkedBlock (by decide +kernel)
def block381 : List CallState := ((nextList 1 wires40).drop 14).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed381 : AllRejected 7 block381 := checkedBlock (by decide +kernel)
def block382 : List CallState := ((nextList 1 wires40).drop 26).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed382 : AllRejected 7 block382 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node40 : walk 8 1 wires40 = false := by
  have rest := (appendOk closed380 (appendOk closed381 (appendOk closed382 (emptyOk 7))))
  exact split_walk (k := 7) (e := 1) (ws := wires40) (by decide +kernel) (by decide +kernel) rest
def wires41 : List ℕ := [v43,v1,v4,v0,v2,v3,v5,v6]
def block383 : List CallState := ((nextList 1 wires41).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed383 : AllRejected 7 block383 := checkedBlock (by decide +kernel)
def block384 : List CallState := ((nextList 1 wires41).drop 9).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed384 : AllRejected 7 block384 := checkedBlock (by decide +kernel)
def block385 : List CallState := ((nextList 1 wires41).drop 18).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed385 : AllRejected 7 block385 := checkedBlock (by decide +kernel)
def block386 : List CallState := ((nextList 1 wires41).drop 28).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed386 : AllRejected 7 block386 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node41 : walk 8 1 wires41 = false := by
  have rest := (appendOk closed383 (appendOk closed384 (appendOk closed385 (appendOk closed386 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires41) (by decide +kernel) (by decide +kernel) rest
def wires42 : List ℕ := [v44,v1,v4,v0,v2,v3,v5,v6]
def block387 : List CallState := ((nextList 1 wires42).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed387 : AllRejected 7 block387 := checkedBlock (by decide +kernel)
def block388 : List CallState := ((nextList 1 wires42).drop 7).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed388 : AllRejected 7 block388 := checkedBlock (by decide +kernel)
def block389 : List CallState := ((nextList 1 wires42).drop 17).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed389 : AllRejected 7 block389 := checkedBlock (by decide +kernel)
def block390 : List CallState := ((nextList 1 wires42).drop 25).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed390 : AllRejected 7 block390 := checkedBlock (by decide +kernel)
def block391 : List CallState := ((nextList 1 wires42).drop 37).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed391 : AllRejected 7 block391 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node42 : walk 8 1 wires42 = false := by
  have rest := (appendOk closed387 (appendOk closed388 (appendOk closed389 (appendOk closed390 (appendOk closed391 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires42) (by decide +kernel) (by decide +kernel) rest
def wires43 : List ℕ := [v45,v1,v5,v0,v2,v3,v4,v6]
def block392 : List CallState := ((nextList 1 wires43).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed392 : AllRejected 7 block392 := checkedBlock (by decide +kernel)
def block393 : List CallState := ((nextList 1 wires43).drop 7).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed393 : AllRejected 7 block393 := checkedBlock (by decide +kernel)
def block394 : List CallState := ((nextList 1 wires43).drop 9).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed394 : AllRejected 7 block394 := checkedBlock (by decide +kernel)
def block395 : List CallState := ((nextList 1 wires43).drop 12).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed395 : AllRejected 7 block395 := checkedBlock (by decide +kernel)
def block396 : List CallState := ((nextList 1 wires43).drop 15).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed396 : AllRejected 7 block396 := checkedBlock (by decide +kernel)
def block397 : List CallState := ((nextList 1 wires43).drop 18).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed397 : AllRejected 7 block397 := checkedBlock (by decide +kernel)
def block398 : List CallState := ((nextList 1 wires43).drop 22).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed398 : AllRejected 7 block398 := checkedBlock (by decide +kernel)
def block399 : List CallState := ((nextList 1 wires43).drop 24).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed399 : AllRejected 7 block399 := checkedBlock (by decide +kernel)
def block400 : List CallState := ((nextList 1 wires43).drop 28).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed400 : AllRejected 7 block400 := checkedBlock (by decide +kernel)
def block401 : List CallState := ((nextList 1 wires43).drop 31).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed401 : AllRejected 7 block401 := checkedBlock (by decide +kernel)
def block402 : List CallState := ((nextList 1 wires43).drop 34).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed402 : AllRejected 7 block402 := checkedBlock (by decide +kernel)
def block403 : List CallState := ((nextList 1 wires43).drop 38).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed403 : AllRejected 7 block403 := checkedBlock (by decide +kernel)
def block404 : List CallState := ((nextList 1 wires43).drop 42).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed404 : AllRejected 7 block404 := checkedBlock (by decide +kernel)
def block405 : List CallState := ((nextList 1 wires43).drop 45).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed405 : AllRejected 7 block405 := checkedBlock (by decide +kernel)
def block406 : List CallState := ((nextList 1 wires43).drop 51).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed406 : AllRejected 7 block406 := checkedBlock (by decide +kernel)
def block407 : List CallState := ((nextList 1 wires43).drop 54).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed407 : AllRejected 7 block407 := checkedBlock (by decide +kernel)
def block408 : List CallState := ((nextList 1 wires43).drop 57).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed408 : AllRejected 7 block408 := checkedBlock (by decide +kernel)
def block409 : List CallState := ((nextList 1 wires43).drop 59).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed409 : AllRejected 7 block409 := checkedBlock (by decide +kernel)
def block410 : List CallState := ((nextList 1 wires43).drop 61).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed410 : AllRejected 7 block410 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node43 : walk 8 1 wires43 = false := by
  have rest := (appendOk closed392 (appendOk closed393 (appendOk closed394 (appendOk closed395 (appendOk closed396 (appendOk closed397 (appendOk closed398 (appendOk closed399 (appendOk closed400 (appendOk closed401 (appendOk closed402 (appendOk closed403 (appendOk closed404 (appendOk closed405 (appendOk closed406 (appendOk closed407 (appendOk closed408 (appendOk closed409 (appendOk closed410 (emptyOk 7))))))))))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires43) (by decide +kernel) (by decide +kernel) rest
def wires44 : List ℕ := [v46,v1,v5,v0,v2,v3,v4,v6]
def block411 : List CallState := ((nextList 1 wires44).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed411 : AllRejected 7 block411 := checkedBlock (by decide +kernel)
def block412 : List CallState := ((nextList 1 wires44).drop 14).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed412 : AllRejected 7 block412 := checkedBlock (by decide +kernel)
def block413 : List CallState := ((nextList 1 wires44).drop 25).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed413 : AllRejected 7 block413 := checkedBlock (by decide +kernel)
def block414 : List CallState := ((nextList 1 wires44).drop 37).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed414 : AllRejected 7 block414 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node44 : walk 8 1 wires44 = false := by
  have rest := (appendOk closed411 (appendOk closed412 (appendOk closed413 (appendOk closed414 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires44) (by decide +kernel) (by decide +kernel) rest
def wires45 : List ℕ := [v47,v1,v5,v0,v2,v3,v4,v6]
def block415 : List CallState := ((nextList 1 wires45).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed415 : AllRejected 7 block415 := checkedBlock (by decide +kernel)
def block416 : List CallState := ((nextList 1 wires45).drop 9).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed416 : AllRejected 7 block416 := checkedBlock (by decide +kernel)
def block417 : List CallState := ((nextList 1 wires45).drop 18).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed417 : AllRejected 7 block417 := checkedBlock (by decide +kernel)
def block418 : List CallState := ((nextList 1 wires45).drop 28).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed418 : AllRejected 7 block418 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node45 : walk 8 1 wires45 = false := by
  have rest := (appendOk closed415 (appendOk closed416 (appendOk closed417 (appendOk closed418 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires45) (by decide +kernel) (by decide +kernel) rest
def wires46 : List ℕ := [v48,v1,v5,v0,v2,v3,v4,v6]
def block419 : List CallState := ((nextList 1 wires46).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed419 : AllRejected 7 block419 := checkedBlock (by decide +kernel)
def block420 : List CallState := ((nextList 1 wires46).drop 7).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed420 : AllRejected 7 block420 := checkedBlock (by decide +kernel)
def block421 : List CallState := ((nextList 1 wires46).drop 14).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed421 : AllRejected 7 block421 := checkedBlock (by decide +kernel)
def block422 : List CallState := ((nextList 1 wires46).drop 22).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed422 : AllRejected 7 block422 := checkedBlock (by decide +kernel)
def block423 : List CallState := ((nextList 1 wires46).drop 32).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed423 : AllRejected 7 block423 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node46 : walk 8 1 wires46 = false := by
  have rest := (appendOk closed419 (appendOk closed420 (appendOk closed421 (appendOk closed422 (appendOk closed423 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires46) (by decide +kernel) (by decide +kernel) rest
def wires47 : List ℕ := [v49,v1,v6,v0,v2,v3,v4,v5]
def block424 : List CallState := ((nextList 1 wires47).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed424 : AllRejected 7 block424 := checkedBlock (by decide +kernel)
def block425 : List CallState := ((nextList 1 wires47).drop 9).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed425 : AllRejected 7 block425 := checkedBlock (by decide +kernel)
def block426 : List CallState := ((nextList 1 wires47).drop 15).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed426 : AllRejected 7 block426 := checkedBlock (by decide +kernel)
def block427 : List CallState := ((nextList 1 wires47).drop 23).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed427 : AllRejected 7 block427 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node47 : walk 8 1 wires47 = false := by
  have rest := (appendOk closed424 (appendOk closed425 (appendOk closed426 (appendOk closed427 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires47) (by decide +kernel) (by decide +kernel) rest
def wires48 : List ℕ := [v50,v1,v6,v0,v2,v3,v4,v5]
def block428 : List CallState := ((nextList 1 wires48).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed428 : AllRejected 7 block428 := checkedBlock (by decide +kernel)
def block429 : List CallState := ((nextList 1 wires48).drop 10).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed429 : AllRejected 7 block429 := checkedBlock (by decide +kernel)
def block430 : List CallState := ((nextList 1 wires48).drop 21).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed430 : AllRejected 7 block430 := checkedBlock (by decide +kernel)
def block431 : List CallState := ((nextList 1 wires48).drop 34).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed431 : AllRejected 7 block431 := checkedBlock (by decide +kernel)
def block432 : List CallState := ((nextList 1 wires48).drop 43).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed432 : AllRejected 7 block432 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node48 : walk 8 1 wires48 = false := by
  have rest := (appendOk closed428 (appendOk closed429 (appendOk closed430 (appendOk closed431 (appendOk closed432 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires48) (by decide +kernel) (by decide +kernel) rest
def wires49 : List ℕ := [v51,v1,v6,v0,v2,v3,v4,v5]
def block433 : List CallState := ((nextList 1 wires49).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed433 : AllRejected 7 block433 := checkedBlock (by decide +kernel)
def block434 : List CallState := ((nextList 1 wires49).drop 10).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed434 : AllRejected 7 block434 := checkedBlock (by decide +kernel)
def block435 : List CallState := ((nextList 1 wires49).drop 18).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed435 : AllRejected 7 block435 := checkedBlock (by decide +kernel)
def block436 : List CallState := ((nextList 1 wires49).drop 25).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed436 : AllRejected 7 block436 := checkedBlock (by decide +kernel)
def block437 : List CallState := ((nextList 1 wires49).drop 34).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed437 : AllRejected 7 block437 := checkedBlock (by decide +kernel)
def block438 : List CallState := ((nextList 1 wires49).drop 44).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed438 : AllRejected 7 block438 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node49 : walk 8 1 wires49 = false := by
  have rest := (appendOk closed433 (appendOk closed434 (appendOk closed435 (appendOk closed436 (appendOk closed437 (appendOk closed438 (emptyOk 7)))))))
  exact split_walk (k := 7) (e := 1) (ws := wires49) (by decide +kernel) (by decide +kernel) rest
def wires50 : List ℕ := [v52,v1,v6,v0,v2,v3,v4,v5]
def block439 : List CallState := ((nextList 1 wires50).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed439 : AllRejected 7 block439 := checkedBlock (by decide +kernel)
def block440 : List CallState := ((nextList 1 wires50).drop 9).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed440 : AllRejected 7 block440 := checkedBlock (by decide +kernel)
def block441 : List CallState := ((nextList 1 wires50).drop 15).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed441 : AllRejected 7 block441 := checkedBlock (by decide +kernel)
def block442 : List CallState := ((nextList 1 wires50).drop 23).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed442 : AllRejected 7 block442 := checkedBlock (by decide +kernel)
def block443 : List CallState := ((nextList 1 wires50).drop 29).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed443 : AllRejected 7 block443 := checkedBlock (by decide +kernel)
def block444 : List CallState := ((nextList 1 wires50).drop 39).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed444 : AllRejected 7 block444 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node50 : walk 8 1 wires50 = false := by
  have rest := (appendOk closed439 (appendOk closed440 (appendOk closed441 (appendOk closed442 (appendOk closed443 (appendOk closed444 (emptyOk 7)))))))
  exact split_walk (k := 7) (e := 1) (ws := wires50) (by decide +kernel) (by decide +kernel) rest
def wires51 : List ℕ := [v53,v2,v3,v0,v1,v4,v5,v6]
def block445 : List CallState := ((nextList 1 wires51).drop 0).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed445 : AllRejected 7 block445 := checkedBlock (by decide +kernel)
def block446 : List CallState := ((nextList 1 wires51).drop 8).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed446 : AllRejected 7 block446 := checkedBlock (by decide +kernel)
def block447 : List CallState := ((nextList 1 wires51).drop 17).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed447 : AllRejected 7 block447 := checkedBlock (by decide +kernel)
def block448 : List CallState := ((nextList 1 wires51).drop 24).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed448 : AllRejected 7 block448 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node51 : walk 8 1 wires51 = false := by
  have rest := (appendOk closed445 (appendOk closed446 (appendOk closed447 (appendOk closed448 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires51) (by decide +kernel) (by decide +kernel) rest
def wires52 : List ℕ := [v17,v3,v0,v1,v4,v5,v6]
def block449 : List CallState := ((nextList 2 wires52).drop 0).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed449 : AllRejected 7 block449 := checkedBlock (by decide +kernel)
def block450 : List CallState := ((nextList 2 wires52).drop 4).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed450 : AllRejected 7 block450 := checkedBlock (by decide +kernel)
def block451 : List CallState := ((nextList 2 wires52).drop 5).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed451 : AllRejected 7 block451 := checkedBlock (by decide +kernel)
def block452 : List CallState := ((nextList 2 wires52).drop 7).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed452 : AllRejected 7 block452 := checkedBlock (by decide +kernel)
def block453 : List CallState := ((nextList 2 wires52).drop 8).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed453 : AllRejected 7 block453 := checkedBlock (by decide +kernel)
def block454 : List CallState := ((nextList 2 wires52).drop 16).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed454 : AllRejected 7 block454 := checkedBlock (by decide +kernel)
def block455 : List CallState := ((nextList 2 wires52).drop 21).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed455 : AllRejected 7 block455 := checkedBlock (by decide +kernel)
def wires53 : List ℕ := [v16,v0,v17,v1,v4,v5,v6]
def block456 : List CallState := ((nextList 1 wires53).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed456 : AllRejected 6 block456 := checkedBlock (by decide +kernel)
def block457 : List CallState := ((nextList 1 wires53).drop 11).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed457 : AllRejected 6 block457 := checkedBlock (by decide +kernel)
def block458 : List CallState := ((nextList 1 wires53).drop 19).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed458 : AllRejected 6 block458 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node53 : walk 7 1 wires53 = false := by
  have rest := (appendOk closed456 (appendOk closed457 (appendOk closed458 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires53) (by decide +kernel) (by decide +kernel) rest
def block459 : List CallState := ((nextList 2 wires52).drop 27).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed459 : AllRejected 7 block459 := checkedBlock (by decide +kernel)
def block460 : List CallState := ((nextList 2 wires52).drop 30).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed460 : AllRejected 7 block460 := checkedBlock (by decide +kernel)
def block461 : List CallState := ((nextList 2 wires52).drop 31).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed461 : AllRejected 7 block461 := checkedBlock (by decide +kernel)
def block462 : List CallState := ((nextList 2 wires52).drop 37).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed462 : AllRejected 7 block462 := checkedBlock (by decide +kernel)
def block463 : List CallState := ((nextList 2 wires52).drop 38).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed463 : AllRejected 7 block463 := checkedBlock (by decide +kernel)
def block464 : List CallState := ((nextList 2 wires52).drop 42).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed464 : AllRejected 7 block464 := checkedBlock (by decide +kernel)
def block465 : List CallState := ((nextList 2 wires52).drop 43).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed465 : AllRejected 7 block465 := checkedBlock (by decide +kernel)
def block466 : List CallState := ((nextList 2 wires52).drop 45).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed466 : AllRejected 7 block466 := checkedBlock (by decide +kernel)
def block467 : List CallState := ((nextList 2 wires52).drop 49).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed467 : AllRejected 7 block467 := checkedBlock (by decide +kernel)
def block468 : List CallState := ((nextList 2 wires52).drop 51).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed468 : AllRejected 7 block468 := checkedBlock (by decide +kernel)
def block469 : List CallState := ((nextList 2 wires52).drop 55).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed469 : AllRejected 7 block469 := checkedBlock (by decide +kernel)
def block470 : List CallState := ((nextList 2 wires52).drop 56).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed470 : AllRejected 7 block470 := checkedBlock (by decide +kernel)
def block471 : List CallState := ((nextList 2 wires52).drop 59).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed471 : AllRejected 7 block471 := checkedBlock (by decide +kernel)
def block472 : List CallState := ((nextList 2 wires52).drop 62).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed472 : AllRejected 7 block472 := checkedBlock (by decide +kernel)
def block473 : List CallState := ((nextList 2 wires52).drop 65).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed473 : AllRejected 7 block473 := checkedBlock (by decide +kernel)
def block474 : List CallState := ((nextList 2 wires52).drop 68).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed474 : AllRejected 7 block474 := checkedBlock (by decide +kernel)
def block475 : List CallState := ((nextList 2 wires52).drop 71).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed475 : AllRejected 7 block475 := checkedBlock (by decide +kernel)
def block476 : List CallState := ((nextList 2 wires52).drop 76).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed476 : AllRejected 7 block476 := checkedBlock (by decide +kernel)
def block477 : List CallState := ((nextList 2 wires52).drop 84).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed477 : AllRejected 7 block477 := checkedBlock (by decide +kernel)
def block478 : List CallState := ((nextList 2 wires52).drop 88).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed478 : AllRejected 7 block478 := checkedBlock (by decide +kernel)
def block479 : List CallState := ((nextList 2 wires52).drop 93).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed479 : AllRejected 7 block479 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node52 : walk 8 2 wires52 = false := by
  have rest := (appendOk closed449 (appendOk closed450 (appendOk closed451 (appendOk closed452 (appendOk closed453 (appendOk closed454 (appendOk closed455 (consOk node53 (appendOk closed459 (appendOk closed460 (appendOk closed461 (appendOk closed462 (appendOk closed463 (appendOk closed464 (appendOk closed465 (appendOk closed466 (appendOk closed467 (appendOk closed468 (appendOk closed469 (appendOk closed470 (appendOk closed471 (appendOk closed472 (appendOk closed473 (appendOk closed474 (appendOk closed475 (appendOk closed476 (appendOk closed477 (appendOk closed478 (appendOk closed479 (emptyOk 7))))))))))))))))))))))))))))))
  exact split_walk (k := 7) (e := 2) (ws := wires52) (by decide +kernel) (by decide +kernel) rest
def wires54 : List ℕ := [v17,v2,v3,v0,v1,v4,v5,v6]
def block480 : List CallState := ((nextList 1 wires54).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed480 : AllRejected 7 block480 := checkedBlock (by decide +kernel)
def block481 : List CallState := ((nextList 1 wires54).drop 11).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed481 : AllRejected 7 block481 := checkedBlock (by decide +kernel)
def block482 : List CallState := ((nextList 1 wires54).drop 21).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed482 : AllRejected 7 block482 := checkedBlock (by decide +kernel)
def block483 : List CallState := ((nextList 1 wires54).drop 29).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed483 : AllRejected 7 block483 := checkedBlock (by decide +kernel)
def block484 : List CallState := ((nextList 1 wires54).drop 35).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed484 : AllRejected 7 block484 := checkedBlock (by decide +kernel)
def block485 : List CallState := ((nextList 1 wires54).drop 44).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed485 : AllRejected 7 block485 := checkedBlock (by decide +kernel)
def block486 : List CallState := ((nextList 1 wires54).drop 49).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed486 : AllRejected 7 block486 := checkedBlock (by decide +kernel)
def block487 : List CallState := ((nextList 1 wires54).drop 56).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed487 : AllRejected 7 block487 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node54 : walk 8 1 wires54 = false := by
  have rest := (appendOk closed480 (appendOk closed481 (appendOk closed482 (appendOk closed483 (appendOk closed484 (appendOk closed485 (appendOk closed486 (appendOk closed487 (emptyOk 7)))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires54) (by decide +kernel) (by decide +kernel) rest
def wires55 : List ℕ := [v54,v3,v0,v1,v4,v5,v6]
def block488 : List CallState := ((nextList 2 wires55).drop 0).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed488 : AllRejected 7 block488 := checkedBlock (by decide +kernel)
def block489 : List CallState := ((nextList 2 wires55).drop 3).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed489 : AllRejected 7 block489 := checkedBlock (by decide +kernel)
def block490 : List CallState := ((nextList 2 wires55).drop 6).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed490 : AllRejected 7 block490 := checkedBlock (by decide +kernel)
def block491 : List CallState := ((nextList 2 wires55).drop 10).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed491 : AllRejected 7 block491 := checkedBlock (by decide +kernel)
def block492 : List CallState := ((nextList 2 wires55).drop 18).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed492 : AllRejected 7 block492 := checkedBlock (by decide +kernel)
def block493 : List CallState := ((nextList 2 wires55).drop 25).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed493 : AllRejected 7 block493 := checkedBlock (by decide +kernel)
def block494 : List CallState := ((nextList 2 wires55).drop 30).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed494 : AllRejected 7 block494 := checkedBlock (by decide +kernel)
def block495 : List CallState := ((nextList 2 wires55).drop 40).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed495 : AllRejected 7 block495 := checkedBlock (by decide +kernel)
def block496 : List CallState := ((nextList 2 wires55).drop 47).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed496 : AllRejected 7 block496 := checkedBlock (by decide +kernel)
def block497 : List CallState := ((nextList 2 wires55).drop 50).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed497 : AllRejected 7 block497 := checkedBlock (by decide +kernel)
def block498 : List CallState := ((nextList 2 wires55).drop 54).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed498 : AllRejected 7 block498 := checkedBlock (by decide +kernel)
def block499 : List CallState := ((nextList 2 wires55).drop 58).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed499 : AllRejected 7 block499 := checkedBlock (by decide +kernel)
def block500 : List CallState := ((nextList 2 wires55).drop 63).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed500 : AllRejected 7 block500 := checkedBlock (by decide +kernel)
def block501 : List CallState := ((nextList 2 wires55).drop 73).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed501 : AllRejected 7 block501 := checkedBlock (by decide +kernel)
def block502 : List CallState := ((nextList 2 wires55).drop 81).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed502 : AllRejected 7 block502 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node55 : walk 8 2 wires55 = false := by
  have rest := (appendOk closed488 (appendOk closed489 (appendOk closed490 (appendOk closed491 (appendOk closed492 (appendOk closed493 (appendOk closed494 (appendOk closed495 (appendOk closed496 (appendOk closed497 (appendOk closed498 (appendOk closed499 (appendOk closed500 (appendOk closed501 (appendOk closed502 (emptyOk 7))))))))))))))))
  exact split_walk (k := 7) (e := 2) (ws := wires55) (by decide +kernel) (by decide +kernel) rest
def wires56 : List ℕ := [v54,v2,v3,v0,v1,v4,v5,v6]
def block503 : List CallState := ((nextList 1 wires56).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed503 : AllRejected 7 block503 := checkedBlock (by decide +kernel)
def block504 : List CallState := ((nextList 1 wires56).drop 10).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed504 : AllRejected 7 block504 := checkedBlock (by decide +kernel)
def block505 : List CallState := ((nextList 1 wires56).drop 18).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed505 : AllRejected 7 block505 := checkedBlock (by decide +kernel)
def block506 : List CallState := ((nextList 1 wires56).drop 25).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed506 : AllRejected 7 block506 := checkedBlock (by decide +kernel)
def block507 : List CallState := ((nextList 1 wires56).drop 33).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed507 : AllRejected 7 block507 := checkedBlock (by decide +kernel)
def block508 : List CallState := ((nextList 1 wires56).drop 40).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed508 : AllRejected 7 block508 := checkedBlock (by decide +kernel)
def block509 : List CallState := ((nextList 1 wires56).drop 49).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed509 : AllRejected 7 block509 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node56 : walk 8 1 wires56 = false := by
  have rest := (appendOk closed503 (appendOk closed504 (appendOk closed505 (appendOk closed506 (appendOk closed507 (appendOk closed508 (appendOk closed509 (emptyOk 7))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires56) (by decide +kernel) (by decide +kernel) rest
def wires57 : List ℕ := [v55,v2,v3,v0,v1,v4,v5,v6]
def block510 : List CallState := ((nextList 1 wires57).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed510 : AllRejected 7 block510 := checkedBlock (by decide +kernel)
def block511 : List CallState := ((nextList 1 wires57).drop 7).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed511 : AllRejected 7 block511 := checkedBlock (by decide +kernel)
def block512 : List CallState := ((nextList 1 wires57).drop 15).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed512 : AllRejected 7 block512 := checkedBlock (by decide +kernel)
def block513 : List CallState := ((nextList 1 wires57).drop 23).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed513 : AllRejected 7 block513 := checkedBlock (by decide +kernel)
def block514 : List CallState := ((nextList 1 wires57).drop 32).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed514 : AllRejected 7 block514 := checkedBlock (by decide +kernel)
def block515 : List CallState := ((nextList 1 wires57).drop 40).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed515 : AllRejected 7 block515 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node57 : walk 8 1 wires57 = false := by
  have rest := (appendOk closed510 (appendOk closed511 (appendOk closed512 (appendOk closed513 (appendOk closed514 (appendOk closed515 (emptyOk 7)))))))
  exact split_walk (k := 7) (e := 1) (ws := wires57) (by decide +kernel) (by decide +kernel) rest
def wires58 : List ℕ := [v56,v2,v4,v0,v1,v3,v5,v6]
def block516 : List CallState := ((nextList 1 wires58).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed516 : AllRejected 7 block516 := checkedBlock (by decide +kernel)
def block517 : List CallState := ((nextList 1 wires58).drop 9).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed517 : AllRejected 7 block517 := checkedBlock (by decide +kernel)
def block518 : List CallState := ((nextList 1 wires58).drop 15).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed518 : AllRejected 7 block518 := checkedBlock (by decide +kernel)
def block519 : List CallState := ((nextList 1 wires58).drop 21).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed519 : AllRejected 7 block519 := checkedBlock (by decide +kernel)
def block520 : List CallState := ((nextList 1 wires58).drop 27).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed520 : AllRejected 7 block520 := checkedBlock (by decide +kernel)
def block521 : List CallState := ((nextList 1 wires58).drop 36).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed521 : AllRejected 7 block521 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node58 : walk 8 1 wires58 = false := by
  have rest := (appendOk closed516 (appendOk closed517 (appendOk closed518 (appendOk closed519 (appendOk closed520 (appendOk closed521 (emptyOk 7)))))))
  exact split_walk (k := 7) (e := 1) (ws := wires58) (by decide +kernel) (by decide +kernel) rest
def wires59 : List ℕ := [v57,v2,v4,v0,v1,v3,v5,v6]
def block522 : List CallState := ((nextList 1 wires59).drop 0).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed522 : AllRejected 7 block522 := checkedBlock (by decide +kernel)
def block523 : List CallState := ((nextList 1 wires59).drop 12).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed523 : AllRejected 7 block523 := checkedBlock (by decide +kernel)
def block524 : List CallState := ((nextList 1 wires59).drop 22).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed524 : AllRejected 7 block524 := checkedBlock (by decide +kernel)
def block525 : List CallState := ((nextList 1 wires59).drop 32).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed525 : AllRejected 7 block525 := checkedBlock (by decide +kernel)
def block526 : List CallState := ((nextList 1 wires59).drop 45).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed526 : AllRejected 7 block526 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node59 : walk 8 1 wires59 = false := by
  have rest := (appendOk closed522 (appendOk closed523 (appendOk closed524 (appendOk closed525 (appendOk closed526 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires59) (by decide +kernel) (by decide +kernel) rest
def wires60 : List ℕ := [v58,v2,v4,v0,v1,v3,v5,v6]
def block527 : List CallState := ((nextList 1 wires60).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed527 : AllRejected 7 block527 := checkedBlock (by decide +kernel)
def block528 : List CallState := ((nextList 1 wires60).drop 9).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed528 : AllRejected 7 block528 := checkedBlock (by decide +kernel)
def block529 : List CallState := ((nextList 1 wires60).drop 16).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed529 : AllRejected 7 block529 := checkedBlock (by decide +kernel)
def block530 : List CallState := ((nextList 1 wires60).drop 22).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed530 : AllRejected 7 block530 := checkedBlock (by decide +kernel)
def block531 : List CallState := ((nextList 1 wires60).drop 29).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed531 : AllRejected 7 block531 := checkedBlock (by decide +kernel)
def block532 : List CallState := ((nextList 1 wires60).drop 38).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed532 : AllRejected 7 block532 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node60 : walk 8 1 wires60 = false := by
  have rest := (appendOk closed527 (appendOk closed528 (appendOk closed529 (appendOk closed530 (appendOk closed531 (appendOk closed532 (emptyOk 7)))))))
  exact split_walk (k := 7) (e := 1) (ws := wires60) (by decide +kernel) (by decide +kernel) rest
def wires61 : List ℕ := [v59,v2,v4,v0,v1,v3,v5,v6]
def block533 : List CallState := ((nextList 1 wires61).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed533 : AllRejected 7 block533 := checkedBlock (by decide +kernel)
def block534 : List CallState := ((nextList 1 wires61).drop 9).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed534 : AllRejected 7 block534 := checkedBlock (by decide +kernel)
def block535 : List CallState := ((nextList 1 wires61).drop 17).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed535 : AllRejected 7 block535 := checkedBlock (by decide +kernel)
def block536 : List CallState := ((nextList 1 wires61).drop 27).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed536 : AllRejected 7 block536 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node61 : walk 8 1 wires61 = false := by
  have rest := (appendOk closed533 (appendOk closed534 (appendOk closed535 (appendOk closed536 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires61) (by decide +kernel) (by decide +kernel) rest
def wires62 : List ℕ := [v60,v2,v5,v0,v1,v3,v4,v6]
def block537 : List CallState := ((nextList 1 wires62).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed537 : AllRejected 7 block537 := checkedBlock (by decide +kernel)
def block538 : List CallState := ((nextList 1 wires62).drop 7).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed538 : AllRejected 7 block538 := checkedBlock (by decide +kernel)
def block539 : List CallState := ((nextList 1 wires62).drop 10).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed539 : AllRejected 7 block539 := checkedBlock (by decide +kernel)
def block540 : List CallState := ((nextList 1 wires62).drop 13).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed540 : AllRejected 7 block540 := checkedBlock (by decide +kernel)
def block541 : List CallState := ((nextList 1 wires62).drop 15).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed541 : AllRejected 7 block541 := checkedBlock (by decide +kernel)
def block542 : List CallState := ((nextList 1 wires62).drop 18).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed542 : AllRejected 7 block542 := checkedBlock (by decide +kernel)
def block543 : List CallState := ((nextList 1 wires62).drop 22).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed543 : AllRejected 7 block543 := checkedBlock (by decide +kernel)
def block544 : List CallState := ((nextList 1 wires62).drop 24).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed544 : AllRejected 7 block544 := checkedBlock (by decide +kernel)
def block545 : List CallState := ((nextList 1 wires62).drop 28).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed545 : AllRejected 7 block545 := checkedBlock (by decide +kernel)
def block546 : List CallState := ((nextList 1 wires62).drop 32).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed546 : AllRejected 7 block546 := checkedBlock (by decide +kernel)
def block547 : List CallState := ((nextList 1 wires62).drop 36).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed547 : AllRejected 7 block547 := checkedBlock (by decide +kernel)
def block548 : List CallState := ((nextList 1 wires62).drop 39).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed548 : AllRejected 7 block548 := checkedBlock (by decide +kernel)
def block549 : List CallState := ((nextList 1 wires62).drop 42).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed549 : AllRejected 7 block549 := checkedBlock (by decide +kernel)
def block550 : List CallState := ((nextList 1 wires62).drop 47).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed550 : AllRejected 7 block550 := checkedBlock (by decide +kernel)
def block551 : List CallState := ((nextList 1 wires62).drop 51).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed551 : AllRejected 7 block551 := checkedBlock (by decide +kernel)
def block552 : List CallState := ((nextList 1 wires62).drop 52).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed552 : AllRejected 7 block552 := checkedBlock (by decide +kernel)
def block553 : List CallState := ((nextList 1 wires62).drop 55).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed553 : AllRejected 7 block553 := checkedBlock (by decide +kernel)
def block554 : List CallState := ((nextList 1 wires62).drop 58).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed554 : AllRejected 7 block554 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node62 : walk 8 1 wires62 = false := by
  have rest := (appendOk closed537 (appendOk closed538 (appendOk closed539 (appendOk closed540 (appendOk closed541 (appendOk closed542 (appendOk closed543 (appendOk closed544 (appendOk closed545 (appendOk closed546 (appendOk closed547 (appendOk closed548 (appendOk closed549 (appendOk closed550 (appendOk closed551 (appendOk closed552 (appendOk closed553 (appendOk closed554 (emptyOk 7)))))))))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires62) (by decide +kernel) (by decide +kernel) rest
def wires63 : List ℕ := [v61,v2,v5,v0,v1,v3,v4,v6]
def block555 : List CallState := ((nextList 1 wires63).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed555 : AllRejected 7 block555 := checkedBlock (by decide +kernel)
def block556 : List CallState := ((nextList 1 wires63).drop 13).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed556 : AllRejected 7 block556 := checkedBlock (by decide +kernel)
def block557 : List CallState := ((nextList 1 wires63).drop 26).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed557 : AllRejected 7 block557 := checkedBlock (by decide +kernel)
def block558 : List CallState := ((nextList 1 wires63).drop 38).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed558 : AllRejected 7 block558 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node63 : walk 8 1 wires63 = false := by
  have rest := (appendOk closed555 (appendOk closed556 (appendOk closed557 (appendOk closed558 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires63) (by decide +kernel) (by decide +kernel) rest
def wires64 : List ℕ := [v62,v2,v5,v0,v1,v3,v4,v6]
def block559 : List CallState := ((nextList 1 wires64).drop 0).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed559 : AllRejected 7 block559 := checkedBlock (by decide +kernel)
def block560 : List CallState := ((nextList 1 wires64).drop 8).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed560 : AllRejected 7 block560 := checkedBlock (by decide +kernel)
def block561 : List CallState := ((nextList 1 wires64).drop 18).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed561 : AllRejected 7 block561 := checkedBlock (by decide +kernel)
def block562 : List CallState := ((nextList 1 wires64).drop 27).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed562 : AllRejected 7 block562 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node64 : walk 8 1 wires64 = false := by
  have rest := (appendOk closed559 (appendOk closed560 (appendOk closed561 (appendOk closed562 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires64) (by decide +kernel) (by decide +kernel) rest
def wires65 : List ℕ := [v63,v2,v5,v0,v1,v3,v4,v6]
def block563 : List CallState := ((nextList 1 wires65).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed563 : AllRejected 7 block563 := checkedBlock (by decide +kernel)
def block564 : List CallState := ((nextList 1 wires65).drop 7).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed564 : AllRejected 7 block564 := checkedBlock (by decide +kernel)
def block565 : List CallState := ((nextList 1 wires65).drop 14).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed565 : AllRejected 7 block565 := checkedBlock (by decide +kernel)
def block566 : List CallState := ((nextList 1 wires65).drop 23).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed566 : AllRejected 7 block566 := checkedBlock (by decide +kernel)
def block567 : List CallState := ((nextList 1 wires65).drop 33).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed567 : AllRejected 7 block567 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node65 : walk 8 1 wires65 = false := by
  have rest := (appendOk closed563 (appendOk closed564 (appendOk closed565 (appendOk closed566 (appendOk closed567 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires65) (by decide +kernel) (by decide +kernel) rest
def wires66 : List ℕ := [v64,v2,v6,v0,v1,v3,v4,v5]
def block568 : List CallState := ((nextList 1 wires66).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed568 : AllRejected 7 block568 := checkedBlock (by decide +kernel)
def block569 : List CallState := ((nextList 1 wires66).drop 7).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed569 : AllRejected 7 block569 := checkedBlock (by decide +kernel)
def block570 : List CallState := ((nextList 1 wires66).drop 10).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed570 : AllRejected 7 block570 := checkedBlock (by decide +kernel)
def block571 : List CallState := ((nextList 1 wires66).drop 13).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed571 : AllRejected 7 block571 := checkedBlock (by decide +kernel)
def block572 : List CallState := ((nextList 1 wires66).drop 16).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed572 : AllRejected 7 block572 := checkedBlock (by decide +kernel)
def block573 : List CallState := ((nextList 1 wires66).drop 20).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed573 : AllRejected 7 block573 := checkedBlock (by decide +kernel)
def block574 : List CallState := ((nextList 1 wires66).drop 23).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed574 : AllRejected 7 block574 := checkedBlock (by decide +kernel)
def block575 : List CallState := ((nextList 1 wires66).drop 26).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed575 : AllRejected 7 block575 := checkedBlock (by decide +kernel)
def block576 : List CallState := ((nextList 1 wires66).drop 30).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed576 : AllRejected 7 block576 := checkedBlock (by decide +kernel)
def block577 : List CallState := ((nextList 1 wires66).drop 32).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed577 : AllRejected 7 block577 := checkedBlock (by decide +kernel)
def block578 : List CallState := ((nextList 1 wires66).drop 36).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed578 : AllRejected 7 block578 := checkedBlock (by decide +kernel)
def block579 : List CallState := ((nextList 1 wires66).drop 39).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed579 : AllRejected 7 block579 := checkedBlock (by decide +kernel)
def block580 : List CallState := ((nextList 1 wires66).drop 42).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed580 : AllRejected 7 block580 := checkedBlock (by decide +kernel)
def block581 : List CallState := ((nextList 1 wires66).drop 47).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed581 : AllRejected 7 block581 := checkedBlock (by decide +kernel)
def block582 : List CallState := ((nextList 1 wires66).drop 51).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed582 : AllRejected 7 block582 := checkedBlock (by decide +kernel)
def block583 : List CallState := ((nextList 1 wires66).drop 53).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed583 : AllRejected 7 block583 := checkedBlock (by decide +kernel)
def block584 : List CallState := ((nextList 1 wires66).drop 56).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed584 : AllRejected 7 block584 := checkedBlock (by decide +kernel)
def block585 : List CallState := ((nextList 1 wires66).drop 58).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed585 : AllRejected 7 block585 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node66 : walk 8 1 wires66 = false := by
  have rest := (appendOk closed568 (appendOk closed569 (appendOk closed570 (appendOk closed571 (appendOk closed572 (appendOk closed573 (appendOk closed574 (appendOk closed575 (appendOk closed576 (appendOk closed577 (appendOk closed578 (appendOk closed579 (appendOk closed580 (appendOk closed581 (appendOk closed582 (appendOk closed583 (appendOk closed584 (appendOk closed585 (emptyOk 7)))))))))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires66) (by decide +kernel) (by decide +kernel) rest
def wires67 : List ℕ := [v65,v2,v6,v0,v1,v3,v4,v5]
def block586 : List CallState := ((nextList 1 wires67).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed586 : AllRejected 7 block586 := checkedBlock (by decide +kernel)
def block587 : List CallState := ((nextList 1 wires67).drop 13).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed587 : AllRejected 7 block587 := checkedBlock (by decide +kernel)
def block588 : List CallState := ((nextList 1 wires67).drop 26).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed588 : AllRejected 7 block588 := checkedBlock (by decide +kernel)
def block589 : List CallState := ((nextList 1 wires67).drop 38).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed589 : AllRejected 7 block589 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node67 : walk 8 1 wires67 = false := by
  have rest := (appendOk closed586 (appendOk closed587 (appendOk closed588 (appendOk closed589 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires67) (by decide +kernel) (by decide +kernel) rest
def wires68 : List ℕ := [v66,v2,v6,v0,v1,v3,v4,v5]
def block590 : List CallState := ((nextList 1 wires68).drop 0).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed590 : AllRejected 7 block590 := checkedBlock (by decide +kernel)
def block591 : List CallState := ((nextList 1 wires68).drop 8).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed591 : AllRejected 7 block591 := checkedBlock (by decide +kernel)
def block592 : List CallState := ((nextList 1 wires68).drop 19).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed592 : AllRejected 7 block592 := checkedBlock (by decide +kernel)
def block593 : List CallState := ((nextList 1 wires68).drop 28).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed593 : AllRejected 7 block593 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node68 : walk 8 1 wires68 = false := by
  have rest := (appendOk closed590 (appendOk closed591 (appendOk closed592 (appendOk closed593 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires68) (by decide +kernel) (by decide +kernel) rest
def wires69 : List ℕ := [v67,v2,v6,v0,v1,v3,v4,v5]
def block594 : List CallState := ((nextList 1 wires69).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed594 : AllRejected 7 block594 := checkedBlock (by decide +kernel)
def block595 : List CallState := ((nextList 1 wires69).drop 7).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed595 : AllRejected 7 block595 := checkedBlock (by decide +kernel)
def block596 : List CallState := ((nextList 1 wires69).drop 15).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed596 : AllRejected 7 block596 := checkedBlock (by decide +kernel)
def block597 : List CallState := ((nextList 1 wires69).drop 25).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed597 : AllRejected 7 block597 := checkedBlock (by decide +kernel)
def block598 : List CallState := ((nextList 1 wires69).drop 36).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed598 : AllRejected 7 block598 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node69 : walk 8 1 wires69 = false := by
  have rest := (appendOk closed594 (appendOk closed595 (appendOk closed596 (appendOk closed597 (appendOk closed598 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires69) (by decide +kernel) (by decide +kernel) rest
def wires70 : List ℕ := [v68,v3,v4,v0,v1,v2,v5,v6]
def block599 : List CallState := ((nextList 1 wires70).drop 0).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed599 : AllRejected 7 block599 := checkedBlock (by decide +kernel)
def block600 : List CallState := ((nextList 1 wires70).drop 8).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed600 : AllRejected 7 block600 := checkedBlock (by decide +kernel)
def block601 : List CallState := ((nextList 1 wires70).drop 15).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed601 : AllRejected 7 block601 := checkedBlock (by decide +kernel)
def block602 : List CallState := ((nextList 1 wires70).drop 22).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed602 : AllRejected 7 block602 := checkedBlock (by decide +kernel)
def block603 : List CallState := ((nextList 1 wires70).drop 29).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed603 : AllRejected 7 block603 := checkedBlock (by decide +kernel)
def block604 : List CallState := ((nextList 1 wires70).drop 39).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed604 : AllRejected 7 block604 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node70 : walk 8 1 wires70 = false := by
  have rest := (appendOk closed599 (appendOk closed600 (appendOk closed601 (appendOk closed602 (appendOk closed603 (appendOk closed604 (emptyOk 7)))))))
  exact split_walk (k := 7) (e := 1) (ws := wires70) (by decide +kernel) (by decide +kernel) rest
def wires71 : List ℕ := [v69,v3,v4,v0,v1,v2,v5,v6]
def block605 : List CallState := ((nextList 1 wires71).drop 0).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed605 : AllRejected 7 block605 := checkedBlock (by decide +kernel)
def block606 : List CallState := ((nextList 1 wires71).drop 6).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed606 : AllRejected 7 block606 := checkedBlock (by decide +kernel)
def block607 : List CallState := ((nextList 1 wires71).drop 8).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed607 : AllRejected 7 block607 := checkedBlock (by decide +kernel)
def block608 : List CallState := ((nextList 1 wires71).drop 18).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed608 : AllRejected 7 block608 := checkedBlock (by decide +kernel)
def block609 : List CallState := ((nextList 1 wires71).drop 26).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed609 : AllRejected 7 block609 := checkedBlock (by decide +kernel)
def block610 : List CallState := ((nextList 1 wires71).drop 33).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed610 : AllRejected 7 block610 := checkedBlock (by decide +kernel)
def block611 : List CallState := ((nextList 1 wires71).drop 34).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed611 : AllRejected 7 block611 := checkedBlock (by decide +kernel)
def block612 : List CallState := ((nextList 1 wires71).drop 35).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed612 : AllRejected 7 block612 := checkedBlock (by decide +kernel)
def block613 : List CallState := ((nextList 1 wires71).drop 44).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed613 : AllRejected 7 block613 := checkedBlock (by decide +kernel)
def block614 : List CallState := ((nextList 1 wires71).drop 49).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed614 : AllRejected 7 block614 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node71 : walk 8 1 wires71 = false := by
  have rest := (appendOk closed605 (appendOk closed606 (appendOk closed607 (appendOk closed608 (appendOk closed609 (appendOk closed610 (appendOk closed611 (appendOk closed612 (appendOk closed613 (appendOk closed614 (emptyOk 7)))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires71) (by decide +kernel) (by decide +kernel) rest
def wires72 : List ℕ := [v70,v3,v4,v0,v1,v2,v5,v6]
def block615 : List CallState := ((nextList 1 wires72).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed615 : AllRejected 7 block615 := checkedBlock (by decide +kernel)
def block616 : List CallState := ((nextList 1 wires72).drop 7).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed616 : AllRejected 7 block616 := checkedBlock (by decide +kernel)
def block617 : List CallState := ((nextList 1 wires72).drop 12).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed617 : AllRejected 7 block617 := checkedBlock (by decide +kernel)
def block618 : List CallState := ((nextList 1 wires72).drop 17).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed618 : AllRejected 7 block618 := checkedBlock (by decide +kernel)
def block619 : List CallState := ((nextList 1 wires72).drop 23).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed619 : AllRejected 7 block619 := checkedBlock (by decide +kernel)
def block620 : List CallState := ((nextList 1 wires72).drop 28).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed620 : AllRejected 7 block620 := checkedBlock (by decide +kernel)
def block621 : List CallState := ((nextList 1 wires72).drop 35).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed621 : AllRejected 7 block621 := checkedBlock (by decide +kernel)
def block622 : List CallState := ((nextList 1 wires72).drop 42).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed622 : AllRejected 7 block622 := checkedBlock (by decide +kernel)
def block623 : List CallState := ((nextList 1 wires72).drop 46).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed623 : AllRejected 7 block623 := checkedBlock (by decide +kernel)
def block624 : List CallState := ((nextList 1 wires72).drop 52).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed624 : AllRejected 7 block624 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node72 : walk 8 1 wires72 = false := by
  have rest := (appendOk closed615 (appendOk closed616 (appendOk closed617 (appendOk closed618 (appendOk closed619 (appendOk closed620 (appendOk closed621 (appendOk closed622 (appendOk closed623 (appendOk closed624 (emptyOk 7)))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires72) (by decide +kernel) (by decide +kernel) rest
def wires73 : List ℕ := [v71,v3,v4,v0,v1,v2,v5,v6]
def block625 : List CallState := ((nextList 1 wires73).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed625 : AllRejected 7 block625 := checkedBlock (by decide +kernel)
def block626 : List CallState := ((nextList 1 wires73).drop 9).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed626 : AllRejected 7 block626 := checkedBlock (by decide +kernel)
def block627 : List CallState := ((nextList 1 wires73).drop 19).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed627 : AllRejected 7 block627 := checkedBlock (by decide +kernel)
def block628 : List CallState := ((nextList 1 wires73).drop 29).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed628 : AllRejected 7 block628 := checkedBlock (by decide +kernel)
def block629 : List CallState := ((nextList 1 wires73).drop 41).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed629 : AllRejected 7 block629 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node73 : walk 8 1 wires73 = false := by
  have rest := (appendOk closed625 (appendOk closed626 (appendOk closed627 (appendOk closed628 (appendOk closed629 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires73) (by decide +kernel) (by decide +kernel) rest
def wires74 : List ℕ := [v72,v3,v5,v0,v1,v2,v4,v6]
def block630 : List CallState := ((nextList 1 wires74).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed630 : AllRejected 7 block630 := checkedBlock (by decide +kernel)
def block631 : List CallState := ((nextList 1 wires74).drop 7).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed631 : AllRejected 7 block631 := checkedBlock (by decide +kernel)
def block632 : List CallState := ((nextList 1 wires74).drop 9).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed632 : AllRejected 7 block632 := checkedBlock (by decide +kernel)
def block633 : List CallState := ((nextList 1 wires74).drop 12).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed633 : AllRejected 7 block633 := checkedBlock (by decide +kernel)
def block634 : List CallState := ((nextList 1 wires74).drop 15).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed634 : AllRejected 7 block634 := checkedBlock (by decide +kernel)
def block635 : List CallState := ((nextList 1 wires74).drop 19).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed635 : AllRejected 7 block635 := checkedBlock (by decide +kernel)
def block636 : List CallState := ((nextList 1 wires74).drop 23).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed636 : AllRejected 7 block636 := checkedBlock (by decide +kernel)
def block637 : List CallState := ((nextList 1 wires74).drop 27).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed637 : AllRejected 7 block637 := checkedBlock (by decide +kernel)
def block638 : List CallState := ((nextList 1 wires74).drop 31).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed638 : AllRejected 7 block638 := checkedBlock (by decide +kernel)
def block639 : List CallState := ((nextList 1 wires74).drop 35).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed639 : AllRejected 7 block639 := checkedBlock (by decide +kernel)
def block640 : List CallState := ((nextList 1 wires74).drop 39).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed640 : AllRejected 7 block640 := checkedBlock (by decide +kernel)
def block641 : List CallState := ((nextList 1 wires74).drop 43).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed641 : AllRejected 7 block641 := checkedBlock (by decide +kernel)
def block642 : List CallState := ((nextList 1 wires74).drop 49).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed642 : AllRejected 7 block642 := checkedBlock (by decide +kernel)
def block643 : List CallState := ((nextList 1 wires74).drop 53).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed643 : AllRejected 7 block643 := checkedBlock (by decide +kernel)
def block644 : List CallState := ((nextList 1 wires74).drop 56).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed644 : AllRejected 7 block644 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node74 : walk 8 1 wires74 = false := by
  have rest := (appendOk closed630 (appendOk closed631 (appendOk closed632 (appendOk closed633 (appendOk closed634 (appendOk closed635 (appendOk closed636 (appendOk closed637 (appendOk closed638 (appendOk closed639 (appendOk closed640 (appendOk closed641 (appendOk closed642 (appendOk closed643 (appendOk closed644 (emptyOk 7))))))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires74) (by decide +kernel) (by decide +kernel) rest
def wires75 : List ℕ := [v73,v3,v5,v0,v1,v2,v4,v6]
def block645 : List CallState := ((nextList 1 wires75).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed645 : AllRejected 7 block645 := checkedBlock (by decide +kernel)
def block646 : List CallState := ((nextList 1 wires75).drop 9).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed646 : AllRejected 7 block646 := checkedBlock (by decide +kernel)
def block647 : List CallState := ((nextList 1 wires75).drop 21).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed647 : AllRejected 7 block647 := checkedBlock (by decide +kernel)
def block648 : List CallState := ((nextList 1 wires75).drop 30).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed648 : AllRejected 7 block648 := checkedBlock (by decide +kernel)
def block649 : List CallState := ((nextList 1 wires75).drop 34).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed649 : AllRejected 7 block649 := checkedBlock (by decide +kernel)
def block650 : List CallState := ((nextList 1 wires75).drop 37).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed650 : AllRejected 7 block650 := checkedBlock (by decide +kernel)
def block651 : List CallState := ((nextList 1 wires75).drop 45).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed651 : AllRejected 7 block651 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node75 : walk 8 1 wires75 = false := by
  have rest := (appendOk closed645 (appendOk closed646 (appendOk closed647 (appendOk closed648 (appendOk closed649 (appendOk closed650 (appendOk closed651 (emptyOk 7))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires75) (by decide +kernel) (by decide +kernel) rest
def wires76 : List ℕ := [v74,v3,v5,v0,v1,v2,v4,v6]
def block652 : List CallState := ((nextList 1 wires76).drop 0).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed652 : AllRejected 7 block652 := checkedBlock (by decide +kernel)
def block653 : List CallState := ((nextList 1 wires76).drop 6).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed653 : AllRejected 7 block653 := checkedBlock (by decide +kernel)
def block654 : List CallState := ((nextList 1 wires76).drop 11).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed654 : AllRejected 7 block654 := checkedBlock (by decide +kernel)
def block655 : List CallState := ((nextList 1 wires76).drop 19).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed655 : AllRejected 7 block655 := checkedBlock (by decide +kernel)
def block656 : List CallState := ((nextList 1 wires76).drop 26).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed656 : AllRejected 7 block656 := checkedBlock (by decide +kernel)
def block657 : List CallState := ((nextList 1 wires76).drop 34).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed657 : AllRejected 7 block657 := checkedBlock (by decide +kernel)
def block658 : List CallState := ((nextList 1 wires76).drop 41).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed658 : AllRejected 7 block658 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node76 : walk 8 1 wires76 = false := by
  have rest := (appendOk closed652 (appendOk closed653 (appendOk closed654 (appendOk closed655 (appendOk closed656 (appendOk closed657 (appendOk closed658 (emptyOk 7))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires76) (by decide +kernel) (by decide +kernel) rest
def wires77 : List ℕ := [v75,v3,v5,v0,v1,v2,v4,v6]
def block659 : List CallState := ((nextList 1 wires77).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed659 : AllRejected 7 block659 := checkedBlock (by decide +kernel)
def block660 : List CallState := ((nextList 1 wires77).drop 7).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed660 : AllRejected 7 block660 := checkedBlock (by decide +kernel)
def block661 : List CallState := ((nextList 1 wires77).drop 14).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed661 : AllRejected 7 block661 := checkedBlock (by decide +kernel)
def block662 : List CallState := ((nextList 1 wires77).drop 23).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed662 : AllRejected 7 block662 := checkedBlock (by decide +kernel)
def block663 : List CallState := ((nextList 1 wires77).drop 34).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed663 : AllRejected 7 block663 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node77 : walk 8 1 wires77 = false := by
  have rest := (appendOk closed659 (appendOk closed660 (appendOk closed661 (appendOk closed662 (appendOk closed663 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires77) (by decide +kernel) (by decide +kernel) rest
def wires78 : List ℕ := [v76,v3,v6,v0,v1,v2,v4,v5]
def block664 : List CallState := ((nextList 1 wires78).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed664 : AllRejected 7 block664 := checkedBlock (by decide +kernel)
def block665 : List CallState := ((nextList 1 wires78).drop 7).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed665 : AllRejected 7 block665 := checkedBlock (by decide +kernel)
def block666 : List CallState := ((nextList 1 wires78).drop 10).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed666 : AllRejected 7 block666 := checkedBlock (by decide +kernel)
def block667 : List CallState := ((nextList 1 wires78).drop 13).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed667 : AllRejected 7 block667 := checkedBlock (by decide +kernel)
def block668 : List CallState := ((nextList 1 wires78).drop 16).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed668 : AllRejected 7 block668 := checkedBlock (by decide +kernel)
def block669 : List CallState := ((nextList 1 wires78).drop 20).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed669 : AllRejected 7 block669 := checkedBlock (by decide +kernel)
def block670 : List CallState := ((nextList 1 wires78).drop 24).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed670 : AllRejected 7 block670 := checkedBlock (by decide +kernel)
def block671 : List CallState := ((nextList 1 wires78).drop 28).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed671 : AllRejected 7 block671 := checkedBlock (by decide +kernel)
def block672 : List CallState := ((nextList 1 wires78).drop 32).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed672 : AllRejected 7 block672 := checkedBlock (by decide +kernel)
def block673 : List CallState := ((nextList 1 wires78).drop 36).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed673 : AllRejected 7 block673 := checkedBlock (by decide +kernel)
def block674 : List CallState := ((nextList 1 wires78).drop 40).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed674 : AllRejected 7 block674 := checkedBlock (by decide +kernel)
def block675 : List CallState := ((nextList 1 wires78).drop 44).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed675 : AllRejected 7 block675 := checkedBlock (by decide +kernel)
def block676 : List CallState := ((nextList 1 wires78).drop 50).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed676 : AllRejected 7 block676 := checkedBlock (by decide +kernel)
def block677 : List CallState := ((nextList 1 wires78).drop 53).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed677 : AllRejected 7 block677 := checkedBlock (by decide +kernel)
def block678 : List CallState := ((nextList 1 wires78).drop 55).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed678 : AllRejected 7 block678 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node78 : walk 8 1 wires78 = false := by
  have rest := (appendOk closed664 (appendOk closed665 (appendOk closed666 (appendOk closed667 (appendOk closed668 (appendOk closed669 (appendOk closed670 (appendOk closed671 (appendOk closed672 (appendOk closed673 (appendOk closed674 (appendOk closed675 (appendOk closed676 (appendOk closed677 (appendOk closed678 (emptyOk 7))))))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires78) (by decide +kernel) (by decide +kernel) rest
def wires79 : List ℕ := [v77,v3,v6,v0,v1,v2,v4,v5]
def block679 : List CallState := ((nextList 1 wires79).drop 0).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed679 : AllRejected 7 block679 := checkedBlock (by decide +kernel)
def block680 : List CallState := ((nextList 1 wires79).drop 6).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed680 : AllRejected 7 block680 := checkedBlock (by decide +kernel)
def block681 : List CallState := ((nextList 1 wires79).drop 9).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed681 : AllRejected 7 block681 := checkedBlock (by decide +kernel)
def block682 : List CallState := ((nextList 1 wires79).drop 20).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed682 : AllRejected 7 block682 := checkedBlock (by decide +kernel)
def block683 : List CallState := ((nextList 1 wires79).drop 30).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed683 : AllRejected 7 block683 := checkedBlock (by decide +kernel)
def block684 : List CallState := ((nextList 1 wires79).drop 32).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed684 : AllRejected 7 block684 := checkedBlock (by decide +kernel)
def block685 : List CallState := ((nextList 1 wires79).drop 34).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed685 : AllRejected 7 block685 := checkedBlock (by decide +kernel)
def block686 : List CallState := ((nextList 1 wires79).drop 43).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed686 : AllRejected 7 block686 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node79 : walk 8 1 wires79 = false := by
  have rest := (appendOk closed679 (appendOk closed680 (appendOk closed681 (appendOk closed682 (appendOk closed683 (appendOk closed684 (appendOk closed685 (appendOk closed686 (emptyOk 7)))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires79) (by decide +kernel) (by decide +kernel) rest
def wires80 : List ℕ := [v78,v3,v6,v0,v1,v2,v4,v5]
def block687 : List CallState := ((nextList 1 wires80).drop 0).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed687 : AllRejected 7 block687 := checkedBlock (by decide +kernel)
def block688 : List CallState := ((nextList 1 wires80).drop 6).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed688 : AllRejected 7 block688 := checkedBlock (by decide +kernel)
def block689 : List CallState := ((nextList 1 wires80).drop 11).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed689 : AllRejected 7 block689 := checkedBlock (by decide +kernel)
def block690 : List CallState := ((nextList 1 wires80).drop 19).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed690 : AllRejected 7 block690 := checkedBlock (by decide +kernel)
def block691 : List CallState := ((nextList 1 wires80).drop 26).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed691 : AllRejected 7 block691 := checkedBlock (by decide +kernel)
def block692 : List CallState := ((nextList 1 wires80).drop 34).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed692 : AllRejected 7 block692 := checkedBlock (by decide +kernel)
def block693 : List CallState := ((nextList 1 wires80).drop 40).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed693 : AllRejected 7 block693 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node80 : walk 8 1 wires80 = false := by
  have rest := (appendOk closed687 (appendOk closed688 (appendOk closed689 (appendOk closed690 (appendOk closed691 (appendOk closed692 (appendOk closed693 (emptyOk 7))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires80) (by decide +kernel) (by decide +kernel) rest
def wires81 : List ℕ := [v79,v3,v6,v0,v1,v2,v4,v5]
def block694 : List CallState := ((nextList 1 wires81).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed694 : AllRejected 7 block694 := checkedBlock (by decide +kernel)
def block695 : List CallState := ((nextList 1 wires81).drop 7).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed695 : AllRejected 7 block695 := checkedBlock (by decide +kernel)
def block696 : List CallState := ((nextList 1 wires81).drop 16).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed696 : AllRejected 7 block696 := checkedBlock (by decide +kernel)
def block697 : List CallState := ((nextList 1 wires81).drop 26).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed697 : AllRejected 7 block697 := checkedBlock (by decide +kernel)
def block698 : List CallState := ((nextList 1 wires81).drop 39).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed698 : AllRejected 7 block698 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node81 : walk 8 1 wires81 = false := by
  have rest := (appendOk closed694 (appendOk closed695 (appendOk closed696 (appendOk closed697 (appendOk closed698 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires81) (by decide +kernel) (by decide +kernel) rest
def wires82 : List ℕ := [v80,v4,v5,v0,v1,v2,v3,v6]
def block699 : List CallState := ((nextList 1 wires82).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed699 : AllRejected 7 block699 := checkedBlock (by decide +kernel)
def block700 : List CallState := ((nextList 1 wires82).drop 9).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed700 : AllRejected 7 block700 := checkedBlock (by decide +kernel)
def block701 : List CallState := ((nextList 1 wires82).drop 15).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed701 : AllRejected 7 block701 := checkedBlock (by decide +kernel)
def block702 : List CallState := ((nextList 1 wires82).drop 23).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed702 : AllRejected 7 block702 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node82 : walk 8 1 wires82 = false := by
  have rest := (appendOk closed699 (appendOk closed700 (appendOk closed701 (appendOk closed702 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires82) (by decide +kernel) (by decide +kernel) rest
def wires83 : List ℕ := [v81,v4,v5,v0,v1,v2,v3,v6]
def block703 : List CallState := ((nextList 1 wires83).drop 0).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed703 : AllRejected 7 block703 := checkedBlock (by decide +kernel)
def block704 : List CallState := ((nextList 1 wires83).drop 8).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed704 : AllRejected 7 block704 := checkedBlock (by decide +kernel)
def block705 : List CallState := ((nextList 1 wires83).drop 10).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed705 : AllRejected 7 block705 := checkedBlock (by decide +kernel)
def block706 : List CallState := ((nextList 1 wires83).drop 11).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed706 : AllRejected 7 block706 := checkedBlock (by decide +kernel)
def block707 : List CallState := ((nextList 1 wires83).drop 18).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed707 : AllRejected 7 block707 := checkedBlock (by decide +kernel)
def block708 : List CallState := ((nextList 1 wires83).drop 27).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed708 : AllRejected 7 block708 := checkedBlock (by decide +kernel)
def block709 : List CallState := ((nextList 1 wires83).drop 38).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed709 : AllRejected 7 block709 := checkedBlock (by decide +kernel)
def block710 : List CallState := ((nextList 1 wires83).drop 45).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed710 : AllRejected 7 block710 := checkedBlock (by decide +kernel)
def block711 : List CallState := ((nextList 1 wires83).drop 52).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed711 : AllRejected 7 block711 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node83 : walk 8 1 wires83 = false := by
  have rest := (appendOk closed703 (appendOk closed704 (appendOk closed705 (appendOk closed706 (appendOk closed707 (appendOk closed708 (appendOk closed709 (appendOk closed710 (appendOk closed711 (emptyOk 7))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires83) (by decide +kernel) (by decide +kernel) rest
def wires84 : List ℕ := [v82,v4,v5,v0,v1,v2,v3,v6]
def block712 : List CallState := ((nextList 1 wires84).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed712 : AllRejected 7 block712 := checkedBlock (by decide +kernel)
def block713 : List CallState := ((nextList 1 wires84).drop 9).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed713 : AllRejected 7 block713 := checkedBlock (by decide +kernel)
def block714 : List CallState := ((nextList 1 wires84).drop 15).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed714 : AllRejected 7 block714 := checkedBlock (by decide +kernel)
def block715 : List CallState := ((nextList 1 wires84).drop 21).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed715 : AllRejected 7 block715 := checkedBlock (by decide +kernel)
def block716 : List CallState := ((nextList 1 wires84).drop 26).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed716 : AllRejected 7 block716 := checkedBlock (by decide +kernel)
def block717 : List CallState := ((nextList 1 wires84).drop 30).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed717 : AllRejected 7 block717 := checkedBlock (by decide +kernel)
def block718 : List CallState := ((nextList 1 wires84).drop 38).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed718 : AllRejected 7 block718 := checkedBlock (by decide +kernel)
def block719 : List CallState := ((nextList 1 wires84).drop 48).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed719 : AllRejected 7 block719 := checkedBlock (by decide +kernel)
def block720 : List CallState := ((nextList 1 wires84).drop 52).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed720 : AllRejected 7 block720 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node84 : walk 8 1 wires84 = false := by
  have rest := (appendOk closed712 (appendOk closed713 (appendOk closed714 (appendOk closed715 (appendOk closed716 (appendOk closed717 (appendOk closed718 (appendOk closed719 (appendOk closed720 (emptyOk 7))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires84) (by decide +kernel) (by decide +kernel) rest
def wires85 : List ℕ := [v83,v4,v5,v0,v1,v2,v3,v6]
def block721 : List CallState := ((nextList 1 wires85).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed721 : AllRejected 7 block721 := checkedBlock (by decide +kernel)
def block722 : List CallState := ((nextList 1 wires85).drop 9).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed722 : AllRejected 7 block722 := checkedBlock (by decide +kernel)
def block723 : List CallState := ((nextList 1 wires85).drop 14).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed723 : AllRejected 7 block723 := checkedBlock (by decide +kernel)
def block724 : List CallState := ((nextList 1 wires85).drop 21).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed724 : AllRejected 7 block724 := checkedBlock (by decide +kernel)
def block725 : List CallState := ((nextList 1 wires85).drop 27).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed725 : AllRejected 7 block725 := checkedBlock (by decide +kernel)
def block726 : List CallState := ((nextList 1 wires85).drop 34).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed726 : AllRejected 7 block726 := checkedBlock (by decide +kernel)
def block727 : List CallState := ((nextList 1 wires85).drop 42).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed727 : AllRejected 7 block727 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node85 : walk 8 1 wires85 = false := by
  have rest := (appendOk closed721 (appendOk closed722 (appendOk closed723 (appendOk closed724 (appendOk closed725 (appendOk closed726 (appendOk closed727 (emptyOk 7))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires85) (by decide +kernel) (by decide +kernel) rest
def wires86 : List ℕ := [v84,v4,v6,v0,v1,v2,v3,v5]
def block728 : List CallState := ((nextList 1 wires86).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed728 : AllRejected 7 block728 := checkedBlock (by decide +kernel)
def block729 : List CallState := ((nextList 1 wires86).drop 7).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed729 : AllRejected 7 block729 := checkedBlock (by decide +kernel)
def block730 : List CallState := ((nextList 1 wires86).drop 9).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed730 : AllRejected 7 block730 := checkedBlock (by decide +kernel)
def block731 : List CallState := ((nextList 1 wires86).drop 12).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed731 : AllRejected 7 block731 := checkedBlock (by decide +kernel)
def block732 : List CallState := ((nextList 1 wires86).drop 15).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed732 : AllRejected 7 block732 := checkedBlock (by decide +kernel)
def block733 : List CallState := ((nextList 1 wires86).drop 18).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed733 : AllRejected 7 block733 := checkedBlock (by decide +kernel)
def block734 : List CallState := ((nextList 1 wires86).drop 22).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed734 : AllRejected 7 block734 := checkedBlock (by decide +kernel)
def block735 : List CallState := ((nextList 1 wires86).drop 24).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed735 : AllRejected 7 block735 := checkedBlock (by decide +kernel)
def block736 : List CallState := ((nextList 1 wires86).drop 28).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed736 : AllRejected 7 block736 := checkedBlock (by decide +kernel)
def block737 : List CallState := ((nextList 1 wires86).drop 31).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed737 : AllRejected 7 block737 := checkedBlock (by decide +kernel)
def block738 : List CallState := ((nextList 1 wires86).drop 34).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed738 : AllRejected 7 block738 := checkedBlock (by decide +kernel)
def block739 : List CallState := ((nextList 1 wires86).drop 38).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed739 : AllRejected 7 block739 := checkedBlock (by decide +kernel)
def block740 : List CallState := ((nextList 1 wires86).drop 42).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed740 : AllRejected 7 block740 := checkedBlock (by decide +kernel)
def block741 : List CallState := ((nextList 1 wires86).drop 45).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed741 : AllRejected 7 block741 := checkedBlock (by decide +kernel)
def block742 : List CallState := ((nextList 1 wires86).drop 50).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed742 : AllRejected 7 block742 := checkedBlock (by decide +kernel)
def block743 : List CallState := ((nextList 1 wires86).drop 53).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed743 : AllRejected 7 block743 := checkedBlock (by decide +kernel)
def block744 : List CallState := ((nextList 1 wires86).drop 56).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed744 : AllRejected 7 block744 := checkedBlock (by decide +kernel)
def block745 : List CallState := ((nextList 1 wires86).drop 58).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed745 : AllRejected 7 block745 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node86 : walk 8 1 wires86 = false := by
  have rest := (appendOk closed728 (appendOk closed729 (appendOk closed730 (appendOk closed731 (appendOk closed732 (appendOk closed733 (appendOk closed734 (appendOk closed735 (appendOk closed736 (appendOk closed737 (appendOk closed738 (appendOk closed739 (appendOk closed740 (appendOk closed741 (appendOk closed742 (appendOk closed743 (appendOk closed744 (appendOk closed745 (emptyOk 7)))))))))))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires86) (by decide +kernel) (by decide +kernel) rest
def wires87 : List ℕ := [v85,v4,v6,v0,v1,v2,v3,v5]
def block746 : List CallState := ((nextList 1 wires87).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed746 : AllRejected 7 block746 := checkedBlock (by decide +kernel)
def block747 : List CallState := ((nextList 1 wires87).drop 11).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed747 : AllRejected 7 block747 := checkedBlock (by decide +kernel)
def block748 : List CallState := ((nextList 1 wires87).drop 23).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed748 : AllRejected 7 block748 := checkedBlock (by decide +kernel)
def block749 : List CallState := ((nextList 1 wires87).drop 33).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed749 : AllRejected 7 block749 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node87 : walk 8 1 wires87 = false := by
  have rest := (appendOk closed746 (appendOk closed747 (appendOk closed748 (appendOk closed749 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires87) (by decide +kernel) (by decide +kernel) rest
def wires88 : List ℕ := [v86,v4,v6,v0,v1,v2,v3,v5]
def block750 : List CallState := ((nextList 1 wires88).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed750 : AllRejected 7 block750 := checkedBlock (by decide +kernel)
def block751 : List CallState := ((nextList 1 wires88).drop 7).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed751 : AllRejected 7 block751 := checkedBlock (by decide +kernel)
def block752 : List CallState := ((nextList 1 wires88).drop 17).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed752 : AllRejected 7 block752 := checkedBlock (by decide +kernel)
def block753 : List CallState := ((nextList 1 wires88).drop 26).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed753 : AllRejected 7 block753 := checkedBlock (by decide +kernel)
def block754 : List CallState := ((nextList 1 wires88).drop 38).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed754 : AllRejected 7 block754 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node88 : walk 8 1 wires88 = false := by
  have rest := (appendOk closed750 (appendOk closed751 (appendOk closed752 (appendOk closed753 (appendOk closed754 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires88) (by decide +kernel) (by decide +kernel) rest
def wires89 : List ℕ := [v87,v4,v6,v0,v1,v2,v3,v5]
def block755 : List CallState := ((nextList 1 wires89).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed755 : AllRejected 7 block755 := checkedBlock (by decide +kernel)
def block756 : List CallState := ((nextList 1 wires89).drop 7).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed756 : AllRejected 7 block756 := checkedBlock (by decide +kernel)
def block757 : List CallState := ((nextList 1 wires89).drop 16).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed757 : AllRejected 7 block757 := checkedBlock (by decide +kernel)
def block758 : List CallState := ((nextList 1 wires89).drop 25).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed758 : AllRejected 7 block758 := checkedBlock (by decide +kernel)
def block759 : List CallState := ((nextList 1 wires89).drop 38).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed759 : AllRejected 7 block759 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node89 : walk 8 1 wires89 = false := by
  have rest := (appendOk closed755 (appendOk closed756 (appendOk closed757 (appendOk closed758 (appendOk closed759 (emptyOk 7))))))
  exact split_walk (k := 7) (e := 1) (ws := wires89) (by decide +kernel) (by decide +kernel) rest
def wires90 : List ℕ := [v88,v5,v6,v0,v1,v2,v3,v4]
def block760 : List CallState := ((nextList 1 wires90).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed760 : AllRejected 7 block760 := checkedBlock (by decide +kernel)
def block761 : List CallState := ((nextList 1 wires90).drop 9).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed761 : AllRejected 7 block761 := checkedBlock (by decide +kernel)
def block762 : List CallState := ((nextList 1 wires90).drop 15).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed762 : AllRejected 7 block762 := checkedBlock (by decide +kernel)
def block763 : List CallState := ((nextList 1 wires90).drop 23).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed763 : AllRejected 7 block763 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node90 : walk 8 1 wires90 = false := by
  have rest := (appendOk closed760 (appendOk closed761 (appendOk closed762 (appendOk closed763 (emptyOk 7)))))
  exact split_walk (k := 7) (e := 1) (ws := wires90) (by decide +kernel) (by decide +kernel) rest
def wires91 : List ℕ := [v89,v5,v6,v0,v1,v2,v3,v4]
def block764 : List CallState := ((nextList 1 wires91).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed764 : AllRejected 7 block764 := checkedBlock (by decide +kernel)
def block765 : List CallState := ((nextList 1 wires91).drop 7).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed765 : AllRejected 7 block765 := checkedBlock (by decide +kernel)
def block766 : List CallState := ((nextList 1 wires91).drop 14).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed766 : AllRejected 7 block766 := checkedBlock (by decide +kernel)
def block767 : List CallState := ((nextList 1 wires91).drop 15).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed767 : AllRejected 7 block767 := checkedBlock (by decide +kernel)
def block768 : List CallState := ((nextList 1 wires91).drop 21).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed768 : AllRejected 7 block768 := checkedBlock (by decide +kernel)
def block769 : List CallState := ((nextList 1 wires91).drop 27).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed769 : AllRejected 7 block769 := checkedBlock (by decide +kernel)
def block770 : List CallState := ((nextList 1 wires91).drop 36).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed770 : AllRejected 7 block770 := checkedBlock (by decide +kernel)
def block771 : List CallState := ((nextList 1 wires91).drop 43).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed771 : AllRejected 7 block771 := checkedBlock (by decide +kernel)
def block772 : List CallState := ((nextList 1 wires91).drop 52).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed772 : AllRejected 7 block772 := checkedBlock (by decide +kernel)
def block773 : List CallState := ((nextList 1 wires91).drop 56).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed773 : AllRejected 7 block773 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node91 : walk 8 1 wires91 = false := by
  have rest := (appendOk closed764 (appendOk closed765 (appendOk closed766 (appendOk closed767 (appendOk closed768 (appendOk closed769 (appendOk closed770 (appendOk closed771 (appendOk closed772 (appendOk closed773 (emptyOk 7)))))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires91) (by decide +kernel) (by decide +kernel) rest
def wires92 : List ℕ := [v90,v5,v6,v0,v1,v2,v3,v4]
def block774 : List CallState := ((nextList 1 wires92).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed774 : AllRejected 7 block774 := checkedBlock (by decide +kernel)
def block775 : List CallState := ((nextList 1 wires92).drop 9).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed775 : AllRejected 7 block775 := checkedBlock (by decide +kernel)
def block776 : List CallState := ((nextList 1 wires92).drop 14).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed776 : AllRejected 7 block776 := checkedBlock (by decide +kernel)
def block777 : List CallState := ((nextList 1 wires92).drop 21).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed777 : AllRejected 7 block777 := checkedBlock (by decide +kernel)
def block778 : List CallState := ((nextList 1 wires92).drop 27).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed778 : AllRejected 7 block778 := checkedBlock (by decide +kernel)
def block779 : List CallState := ((nextList 1 wires92).drop 32).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed779 : AllRejected 7 block779 := checkedBlock (by decide +kernel)
def block780 : List CallState := ((nextList 1 wires92).drop 42).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed780 : AllRejected 7 block780 := checkedBlock (by decide +kernel)
def block781 : List CallState := ((nextList 1 wires92).drop 48).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed781 : AllRejected 7 block781 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node92 : walk 8 1 wires92 = false := by
  have rest := (appendOk closed774 (appendOk closed775 (appendOk closed776 (appendOk closed777 (appendOk closed778 (appendOk closed779 (appendOk closed780 (appendOk closed781 (emptyOk 7)))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires92) (by decide +kernel) (by decide +kernel) rest
def wires93 : List ℕ := [v91,v5,v6,v0,v1,v2,v3,v4]
def block782 : List CallState := ((nextList 1 wires93).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed782 : AllRejected 7 block782 := checkedBlock (by decide +kernel)
def block783 : List CallState := ((nextList 1 wires93).drop 9).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed783 : AllRejected 7 block783 := checkedBlock (by decide +kernel)
def block784 : List CallState := ((nextList 1 wires93).drop 15).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed784 : AllRejected 7 block784 := checkedBlock (by decide +kernel)
def block785 : List CallState := ((nextList 1 wires93).drop 20).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed785 : AllRejected 7 block785 := checkedBlock (by decide +kernel)
def block786 : List CallState := ((nextList 1 wires93).drop 26).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed786 : AllRejected 7 block786 := checkedBlock (by decide +kernel)
def block787 : List CallState := ((nextList 1 wires93).drop 35).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed787 : AllRejected 7 block787 := checkedBlock (by decide +kernel)
def block788 : List CallState := ((nextList 1 wires93).drop 46).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed788 : AllRejected 7 block788 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node93 : walk 8 1 wires93 = false := by
  have rest := (appendOk closed782 (appendOk closed783 (appendOk closed784 (appendOk closed785 (appendOk closed786 (appendOk closed787 (appendOk closed788 (emptyOk 7))))))))
  exact split_walk (k := 7) (e := 1) (ws := wires93) (by decide +kernel) (by decide +kernel) rest
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node0 : walk 9 3 wires0 = false := by
  have rest := (consOk node1 (consOk node2 (consOk node3 (consOk node4 (consOk node5 (consOk node6 (consOk node7 (consOk node8 (consOk node9 (consOk node10 (consOk node11 (consOk node13 (consOk node14 (consOk node16 (consOk node17 (consOk node18 (consOk node19 (consOk node20 (consOk node21 (consOk node22 (consOk node23 (consOk node24 (consOk node25 (consOk node26 (consOk node27 (consOk node28 (consOk node29 (consOk node30 (consOk node31 (consOk node32 (consOk node33 (consOk node34 (consOk node35 (consOk node36 (consOk node37 (consOk node38 (consOk node39 (consOk node40 (consOk node41 (consOk node42 (consOk node43 (consOk node44 (consOk node45 (consOk node46 (consOk node47 (consOk node48 (consOk node49 (consOk node50 (consOk node51 (consOk node52 (consOk node54 (consOk node55 (consOk node56 (consOk node57 (consOk node58 (consOk node59 (consOk node60 (consOk node61 (consOk node62 (consOk node63 (consOk node64 (consOk node65 (consOk node66 (consOk node67 (consOk node68 (consOk node69 (consOk node70 (consOk node71 (consOk node72 (consOk node73 (consOk node74 (consOk node75 (consOk node76 (consOk node77 (consOk node78 (consOk node79 (consOk node80 (consOk node81 (consOk node82 (consOk node83 (consOk node84 (consOk node85 (consOk node86 (consOk node87 (consOk node88 (consOk node89 (consOk node90 (consOk node91 (consOk node92 (consOk node93 (emptyOk 8)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  exact split_walk (k := 8) (e := 3) (ws := wires0) (by decide +kernel) (by decide +kernel) rest
end PEqualNP.Outside.L_meta_11285_aux.NatCheck.Delete7
open PEqualNP.Outside.L_meta_11285_aux in
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem PEqualNP.Outside.L_meta_11285 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o fits _ computes
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hm,hn⟩ := present
    have lt : binaryCost gs < gs.length := List.length_filter_lt_length_iff_exists.mpr
      ⟨g,hm,by simp [isBinary,hn]⟩
    have sameInputs : NatCheck.asNs inputs7 = NatCheck.Delete7.wires0 := by decide +kernel
    have cert : NatCheck.walk 9 3 (NatCheck.asNs inputs7) = false := by
      rw [sameInputs]
      exact NatCheck.Delete7.node0
    have lower := ten_binary cert gs o fits computes
    exact ⟨smallCircuit.gates,smallCircuit.output,smallLegal,by change 11 ≤ gs.length; omega,smallEval⟩
  · refine ⟨gs,o,?_,le_rfl,computes⟩
    intro g hg
    exact ⟨(fits g hg).1.imp_right (·.resolve_right fun h => present ⟨g,hg,h⟩), (fits g hg).2⟩
