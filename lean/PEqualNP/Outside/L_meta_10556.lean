import Mathlib
import PEqualNP.Defs

-- The live-wire search and four-input clique lower bound follow the proofs
-- in L-meta-8724, L-meta-1449, L-meta-1429 and L-meta-703.
-- For this graph, fixing a primary input after the first binary gate
-- removes two gates. Four of the resulting six-input lower bounds follow
-- from a four-clique, and two deletions exchange twin vertices.
-- Two finite certificates below handle the other cases.
namespace PEqualNP.Outside.L_meta_10556_aux

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
-- A live run mapped through a bitwise homomorphism is a build of the mapped goal; a wire
-- mapped to zero saves its gate.
def SignedBuild (k : ℕ) (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem sb_zero {av : Finset W} {z : W} (h : holds av z) : SignedBuild 0 av z := by
  rcases h with h | h | ⟨a,ha,rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not,build] using ha)))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem sb_wait {av : Finset W} {z : W} {k : ℕ} (h : SignedBuild k av z) :
    SignedBuild (k+1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem sb_le {av : Finset W} {z : W} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild k av z) :
    SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem sb_step {av : Finset W} {t a b z : W} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps a b) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k+1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩) (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩)))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem sb_advance {av : Finset W} {z t : W} {k : ℕ} (hz : reachable av z)
    (next : ∀ av' : Finset W, av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k+1) av t := by
  rcases hz with h | ⟨a,ha,b,hb,hn,w,hw,ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem mem_ops_reach {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

set_option maxRecDepth 5000 in
theorem mem_ops_zero {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hzero : x = 0 ∨ y = 0) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  have hc : holds av (0 : W) := .inl rfl
  have absorb (v : W) : v &&& (~~~(0 : W)) = v := by
    exact (congrArg (fun u : W => v &&& u) (BitVec.not_zero (n := 512))).trans BitVec.and_allOnes
  rcases hzero with rfl | rfl <;> rcases hz with rfl|rfl|rfl|rfl <;>
    first | rwa [absorb] | simp_all

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem live_transport {f : W → W} (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_wait (ih skip hav)
      · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
        intro av' sub ok
        apply ih tail
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact ok
        · exact holds_mono sub (hav u (by simp [he,hr]))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem live_transport_save {f : W → W}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hp : p ∈ s) (hpg : p ≠ g) (hzero : f p = 0)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild (k-1) av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact False.elim (hpg (by simpa [run] using hp))
  | succ k ih =>
      simp only [Nat.add_sub_cancel] at *
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_le (Nat.sub_le _ _) (ih skip hp hav)
      · have mapped := hm a b z hz
        have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he,hu])
        by_cases touches : p = a ∨ p = b
        · have zz : f a = 0 ∨ f b = 0 := touches.elim (fun h => .inl (h ▸ hzero)) (fun h => .inr (h ▸ hzero))
          have collapsed := mem_ops_zero (hav a ha) (hav b hb) zz mapped
          apply live_transport hm tail
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact collapsed
          · exact inOld u hr
        · have pr : p ∈ r := by
            rw [he] at hp
            simpa [Finset.mem_insert, touches, not_or.mp touches |>.1, not_or.mp touches |>.2] using hp
          have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
          have pos : 0 < k := by
            by_contra! hk
            have eq : k = 0 := by omega
            subst k
            change insert z r = {g} at tail
            exact hpg (by simpa [tail] using pt)
          have cost : (k-1)+1 = k := by omega
          rw [← cost]
          apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) mapped)
          intro av' sub ok
          apply ih tail pt
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact ok
          · exact holds_mono sub (inOld u hr)

-- Fixing input i to zero (restriction i) leaves the same four-input search, which fails at six.
def k4inputs : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842, 0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084, 0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108, 0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k4exact : search 6 k4inputs = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem goal_changes : ∀ k : Fin 256, differs k goal ∧ differs k (~~~goal) := by
  unfold differs
  decide +kernel


def graph (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,2]⟩, ⟨.or,[4,5]⟩, ⟨.or,[6,8]⟩, ⟨.and,[9,7]⟩, ⟨.or,[1,6]⟩, ⟨.and,[0,2]⟩, ⟨.or,[3,8]⟩, ⟨.and,[11,13]⟩, ⟨.or,[12,10]⟩, ⟨.or,[14,15]⟩, ⟨.and,[3,5]⟩, ⟨.or,[17,16]⟩],18⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem smallLegal : ∀ g ∈ smallCircuit.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [smallCircuit]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
theorem smallEval : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = graph x := by decide +kernel

def pick (a b : Fin 512) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 512 => w[(if k = a then b else k).val]))).cast List.length_ofFn

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem pick_bit (a b : Fin 512) (w : W) (j : ℕ) (hj : j < 512) :
    (pick a b w)[j] = w[(if (⟨j,hj⟩ : Fin 512) = a then b else ⟨j,hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [pick, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem pick_not (i j : Fin 512) (u : W) : pick i j (~~~u) = ~~~pick i j u :=
  BitVec.eq_of_getElem_eq fun k hk => by simp only [pick_bit, BitVec.getElem_not]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem pick_ops (i j : Fin 512) (a b z : W) (hz : z ∈ basicOps a b) :
    pick i j z ∈ basicOps (pick i j a) (pick i j b) := by
  have hand (u v : W) : pick i j (u &&& v) = (pick i j u &&& pick i j v) :=
    BitVec.eq_of_getElem_eq fun k hk => by simp only [pick_bit, BitVec.getElem_and]
  have hor (u v : W) : pick i j (u ||| v) = (pick i j u ||| pick i j v) :=
    BitVec.eq_of_getElem_eq fun k hk => by simp only [pick_bit, BitVec.getElem_or]
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand, hor, pick_not]

def Excluded (k : ℕ) (v : List W) : Prop := ∀ t, t = goal ∨ t = ~~~goal → ¬build basicOps t k v.toFinset

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem exclude_lift {k : ℕ} {v w : List W} (i : Fin 256) (a b : Fin 512) (x : W)
    (hx : x ≠ goal ∧ x ≠ ~~~goal) (hz : pick a b x = 0) (ht : pick a b goal = goal)
    (hp : ∀ u ∈ v, differs i u → u = x)
    (ha : ∀ u ∈ v, pick a b u = 0 ∨ pick a b u ∈ w) (lower : Excluded k w) : Excluded (k+1) v := by
  intro t ht' run
  obtain ⟨S, sub, liveS⟩ := compress run
  have dt : differs i t := by rcases ht' with rfl|rfl; exact (goal_changes i).1; exact (goal_changes i).2
  obtain ⟨u, hu, hd⟩ := live_separates (differs i) dt (ops_differs i) liveS
  have eq := hp u (List.mem_toFinset.mp (sub hu)) hd
  have xt : x ≠ t := by rcases ht' with rfl|rfl; exact hx.1; exact hx.2
  have useX : x ∈ S := eq ▸ hu
  have saved := live_transport_save (pick_ops a b) liveS useX xt hz (av := w.toFinset) (by
    intro z hz'
    rcases ha z (List.mem_toFinset.mp (sub hz')) with h|h
    · exact .inl h
    · exact .inr (.inr ⟨_, List.mem_toFinset.mpr h, .inl rfl⟩))
  have sign : pick a b t = goal ∨ pick a b t = ~~~goal := by
    rcases ht' with rfl|rfl
    · exact Or.inl ht
    · exact Or.inr (by rw [pick_not,ht])
  have opp : ~~~pick a b t = goal ∨ ~~~pick a b t = ~~~goal := by
    rcases sign with h|h <;> simp [h]
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  rcases saved with c|c|h|h
  · rcases sign with e|e
    · exact ne.1 (e.symm.trans c)
    · exact ne.2.2.1 (e.symm.trans c)
  · rcases sign with e|e
    · exact ne.2.1 (e.symm.trans c)
    · exact ne.2.2.2 (e.symm.trans c)
  · exact lower _ sign h
  · exact lower _ opp h
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem reject4 : Excluded 6 k4inputs := by
  intro t ht run
  have nd : k4inputs.Nodup := by decide +kernel
  exact Bool.noConfusion (k4exact.symm.trans (search_complete ht 6 k4inputs nd run))
end PEqualNP.Outside.L_meta_10556_aux

namespace PEqualNP.Outside.L_meta_10556_aux.Reduction

-- Pinning an input after the first binary gate reduces the remaining question
-- to eight binary gates on each of the seven vertex-deleted graphs.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def inputs7 : List W := [0x6225912c24bffc22410090405681ab5556aabab5df56eddf84210fc3f084408f00000000000ffc00000000003f80ff5512aabab5df566ddf000007c1f000000f,0xa44aa257fff4ac04a0e120a0811655999b332cd96d9b776d7c42107ff008887000000003fff000001fe00000007fff9193332c996d93776d7c00003ff0000070,0xc8937ffc495014490202410b40e903e1e3c3cf1e77e3b9f78884f8be1111078100007ffc000000000000001fc07f00a08141450a20a110200000f83e00000780,0x1fffc4988269589024240634a90205fe03fc0fe079fc3e79111fffc4222038101fff80000000000000000fffff80006e00cc0360106c0810001fffc000003800,0xf11c08e113826101c84879c1020c19fffc000fff81ffc07e23ff21084403c122e000000000000000001fffe00000000a6c0000400008800003ff00000003c000,0x1e00f021c03821e109782060c3061fffffff00001ffff8043e84210887c12440000000000000000001ff000000000006c0000000000800003e00000007c0000,0x1e007003e00c03e01f180c18304081fffffffffffe0000007e1084210fc2240800000000000000001fe000000000000000100000000000007c0000000f800000]
def vinput (i : Fin 7) := inputs7.getD i.val 0
def child : Fin 7 → List W := ![[0x8ab867aaa961830a1c07ccf12c4b12c9697ff02870a1825d5aadbff111f012470000007ff800000003ffc00000000000001ff007f00001fc4aa59ef000f00007,0x955aaad552861434005ad7f254952552bfe2b15081422da66cf7da122ff124380007fffff8000001fc000070000000001fe0000000007ffe4cf7da000ff00038,0x266d55067c28a90064a17bf4992649bff2a45281120cd20f8f39ef24ff1241c17fffff80000000fe000003f00000003fe0000000001ffe0385186000ff0001c0,0xd991999998d30046890dbf98e238ffe4c4c9641a24730437f03ef24ff2240e0afff8000000007f0000003f800000ffc0000000000fff8001b008200ff0000e00,0x61e61e61e7004e9932363d2f03ff8e07071188e44b8418c7ffc0fc8f4448f09480000000001f800000003c0003ff0000000000000fe000003000000f0000f000,0x7e07e07e001c70e1c3c7e24fffc0f038181e0f078c186107ffff00f8888f89200000000007e000000007c00ffc00000000000007f0000000020000f0000f0000],
[0x96c55c33d554b16262b1600af896258964b4bf84a1420af56adbdfc447c2241f000000003ffc000000001fc00000000000000f80000007f42adbd78003c0000f,0x2b4aad55433d52a4a55002d5792a4a92a95ff0894284b839b36defc8bc4448f1000003ffc0000000000fe00038000000000ff0000001f808112420003c0000f0,0x4d9336aaaaaa04090002853ffa4c9324dff95b920419451e3c717513ffc88300003ffffffffc00001ff00007f80000001ff00000003ffffe3c717503ffc00300,0x71ecc8cccccc68c00864287fcc711c7ff262652068e6105fc07e79bfc8901c22fffffc000000001fe000003fc000007fe00000001ffe0003c000083fc0001c00,0x8e30f30f30f38011d188d1b99781ffc7038386439708619fff807e3d1121e144ffc0000000000fe0000000380001ff80000000001fc00001c000083c0001e000,0xf03f03f03f000f1e1e0f1e2627ffe0781c0c087c1831861fffff8022223f1288000000000003f0000000000007fe0000000000000000000000000000003e0000],
[0x8abaaaaaa945122a2c02cff12c4b12c962bff12880a12d555aefba111ff112070007fffff800000003f8007000000000000ff00000007ffd4aefba000ff00007,0x955867d552a28514003fd4f254952552bff4b050714282ae6cb5dff221f024780000007ff8000001fc07c000000000001ff00007f00001fc4ca59ef000f00038,0x266d55067c28a90050c97bf4992649bfe4595281120cd20f8f39ef24ff1241c87fffff80000000fe000003f00000003fe0000000001ffe0383186000ff0001c0,0xd991999998d300468515bf98e238ffe4c962641a24730437f03ef24ff2240e11fff8000000007f0000003f800000ffc0000000000fff8002b010400ff0000e00,0x61e61e61e7004e991a663d2f03ff8e07118388e44b8418c7ffc0fc8f4448f0a280000000001f800000003c0003ff0000000000000fe000003000000f0000f000,0x7e07e07e001c70e1e387e24fffc0f0381e0c0f078c186107ffff00f8888f89040000000007e000000007c00ffc00000000000007f0000000040000f0000f0000],
[0xcb25b0cf555264c99515802de2589625a5897f12440906bab5d7dfc447c4444f00000000fff0000000007f000000000000001f00000003f895d7cf8003c0000f,0x3f4ad555aaa481020a0005ffe4a92a4acafff7048312294cd9656d3cbfc08830ff000ffffff0000000ff80fce0000000007fe0003f00fffc99656d3c3fc00030,0x55936aaa0cf92a54802a9a56e9324c937f92a1290824d41f1e79f7c93c4913c100000fff000000007f000000e00000007f8000000000fc040a2820003c0003c0,0xa61c73333331d3802343239b31c471ff9324ca41d147186fe07e7993c8903c9200fff0000000003f80000003000001ff8000000000ff000360001003c0003c00,0x38e38c3cc3ce00274c8c4ce35e07ff1c1c470c8e22b8618fff807e23d123c12400fff00000001fc0000000030007fe000000000000ff000360001003c003c000,0xc0fc0fc0fc001c3870f070fc9fff81e0607810f03cc0820fffff803e223e2208ff000000000fe000000000fc1ff80000000000003f0000000000003c003c0000],
[0x74cd0cf55514a4c909805aff12c4b2592c57fc44202a86b555df6f11f1f108270fff000fff000000007f0038000000000001fc00001f83f555df6e00f0f00007,0xb157555aaa2841028003fd7f254954aa57feac0a18411959996dbaf21ff011180000ffffff0000007f80f8070000000003fe0001f8007ff9996dbaf00ff00018,0xd2abaaa0cf452a401294afcf49926937fcaa149042a0e43e1e77cf2f2f1220e1f000fff00000003f800007c700000007fc00000007e07c0a0a20800f0f0000e0,0x2b323333338a4014a42937f98e238ffc990d59228d55085fe079f24ff2244708ffff000000001fc0000007f800000ff80000000007ff80066010400ff0000700,0xcc3cc3cc3cf013a7474ec192f03ff1c0e230623d1186319fff81fc844448fa52000000000003e00000000000003ff0000000000000000000000000000000f800,0xfc0fc0fc0039c387870fe24fffc0e0703c183c1e618421ffffe00f8888f84840000000000fc00000000f800ffc0000000000001f8000000800000f0000f0000],
[0x66867aaa94a4ca16016b5fe258962592c4bfe242041686b56bbefc447c7c4427ff8007ff80000001f800070000000000000fe000000f83f56bbef8003c3c0007,0xabaaad55284105001fe5afe4a92a4aa57ff560a18a211959b2db6bc887fc0918007fffff800000fe07e000e0000000003ff0001f80007ff932db6bc003fc0018,0x55d55067c52a402a62b6f9e9324c937fc950a50410d0e43e3cefbc93cbc490e1007ff80000003f000000f8e00000007fc000000001f07c0a14410003c3c000e0,0x991999998a4011408cdfff31c471ffc9926ac828a329085fc0f3c93ffc890308ff800000001fc000001fff000001ff80000000007fff8006c020803ffc000300,0x1e61e61e7013a68d371f325e07ff1c0e238311d15c42319fff03f23d11123c520000000003e00000001f000007fe0000000000007e0000008000003c00003c00,0xe07e07e0039c38f1c7f8c49fff81e0703c0c1e1e618c421ffffc03e22223e284000000007c00000007e0001ff80000000000001f80000000000003c00003c000],
[0xcd0cf55528a4ca2c02ad7f896258962592ffc484882d055ab76efc447c7c4847ff000fff00000003f0001c0000000000003fc000001f03fab36ef8003c3c0007,0x57555aaa51491500b596bf92a4a92a4affcac94914425aacdbbb688887fc923800ffffff000000fc00000380000000007fc000000000fffc9bbb680003fc0038,0xabaaa0cf8a324055495be7a4c9324dffa541521221a1a41f1dcfbd13cbc521c100fff00000003f000003e380000001ff8000000003e0fc0508810003c3c001c0,0x32333333144021821e7ffcc711c7fe930995a0604652082fe1f3ca3ffc8a0608ff000000001fc000007ffc000007fe00000000007fff00036040803ffc000600,0x3cc3cc3ce00386186ffcc9781ffc711c4e260383b88430cffe03f3fd111038920000000007e000000ffc00001ff800000000003ffc000000440003fc00003800,0xc0fc0fc0079c38e38fe3127ffe0781e070383c3c4318c30ffffc03e22223c52400000000f80000000f80007fe00000000000003f80000000040003c00003c000]]
def rowMaps : Fin 7 → ℕ := ![0x91ce6e5619ecbe79379b4ba9323915cadd34b0cf24b339bd26493191dba7d619ecbe79379b4ba932d98c32130684416091186c2a11058245a1b0a864260d048b4461509834220b1688c36190682c122d1186c2a1909845eee166b1d770355a9d42d155a2d7699459cdcadd3e9a5867b2f9e4967372b74fa67379b4ba93249ccd2c33d99cde6d2d98c8e692f9e4ce5d4996cc6452f92cde5d2496c8e453e9ecf24b36924c647228b4461b0a864260d0882c5a230d8541a0b048b4461909834220b1186c32110582436150c84c22090a84c1a11058261f0b83c0dfefb7bbc5dae972b85bad568b358ec35dabd56a750a65268b049f4f679259ccce6f369a4ce5b3197cba5b2292c9247228b4461b0a8b432130688c220b0d8641215098441a0b041a8c06030180c06030180c06030180ac562b158ac562b158ac562b1588442211088442211088442211085c2e170b85c2e12090482412090381c0e070381c0e0582c160b0582c16070381c0e070381c0804020100804020e8743a1d0e86a351a8d46030180ac562b0b85c2e170b85c2e170b85c2412090482412090482412070381c0e070381c0e07038160b0582c160b0582c16070381c0e070381c0e040201008040201008041f8fc7e3f1f8fc7e3f1f8e8743a1d0e8743a1a8d46a351a8d46a30180c06030180ac562b158ac5621108844221108845630180846a35108ac740b1081c422b180840e21108ac602110810423f1d0e8743a1a8d46a35180c06030158ac562b1088442210b85c2e17090482412070381c0b0582c0e07038100804,
0xb64d2c35f974a68f2d945067372b0d7e5f2a9bcd65d29a0c9ee56e9a586555999cde534794506e56c9a57e5f5999cd65d4796d06190981422030088c36150384406011686c2a070c84c0a011688c2a07098142203008b4461b038640a031688c36150c84c230355a95a2cb55a9512b94ba24e6e56eb64d2c35f97caab339b95bad9339bcd65d29a3ce66961afcce6f3596ca2833497caa672e94cb6512797d666f2ea3cb68327954d6532893c5a230d8540e190981422031688c32130284406230d86422030d85432130880436070c814060186c2e0b037ebedeaef76b9dcadf6eb65a6d165b1586bf5cacd5aab52a7d2e8f44a0c0273339bcd6693396ca25f2e96c9e55299449e2d1186c2a0716864260511844061b0c85426110081c0a03001a8d46a351a8d46a351a8d46030180c06030180c06030180c0562b158ac562b158ac562b158ac4c26130984c26130984c26130982e170b85c2e1709048241209048240e070381c0e070381c0b0582c160b0582c160b0381c0e070381c0e00000000000000006a351a8c06030180c0562b1585c2e170b85c2e170b85c2e12090482412090482412090381c0e070381c0e070381c0b0582c160b0582c160b0381c0e070381c0e07000000000000fc7e3f1f8fc7e3f1f8fc7e351a8d46a351a8d46030180c0602b158ac562b158984c26130984c261589860351a8d44c2b1302c00070009856260001c00260009856261a8980026000fc6a351a8d46030180c0562b158ac4c26130982e170b85c2e1209048240e07038160b0381c0e07000000000,
0x8f4e6e53dafcf255369ad26531e8edcad934afcf241339ad263f318f4fad93dafcf255369ad265331944320d0282c06091186c0e0b018245a1b038641a05048b446070681416031688c36070c814062d1186c320d05825eedb66b056f0353a953acb52a1d6e95439cdca7d6c9a4f6bf3c9548273729f5b267369ad26531f9ccd27b5f99cda6b319447a693c954ce932998ca23b3e9ecf241368fcc63d1d954826b298fca23d1d8b4461b038641a050580c5a230d81c1a0b048b446190681416031186c320b0182436070c8140609038340a0b01826130782c0df2f77abadd2e772b6db2cf66b2d82bf5baa54ea54ea552687049f4f679209ccce6d359a4ce6328954a6511d9047e3d1d8b4461b038b4320d0288c16030d864120d058240e05011a8c06030180c06030180c06030180984c26130984c26130984c2613070381c0e070381c0e070381c0e05c2e170b85c2e12090482412090381c0e070381c0e0582c160b0582c1604020100804020100000000000000000e8743a1d0e86a351a8d46030180984c260b85c2e170b85c2e170b85c2412090482412090482412070381c0e070381c0e07038160b0582c160b0582c16040201008040201008040000000000000000001f8fc7e3f1f8fc7e3f1f8e8743a1d0e8743a1a8d46a351a8d46a30180c06030180984c26130984c1c0e070381c0e0706026180706a350e0e84c0b0e000383013070001c0e0c04c1c0e010383f1d0e8743a1a8d46a35180c06030130984c260e070381c0b85c2e17090482412070381c0b0582c0804020000000,
0xafd666d248fc8e3d1cb74fad9619ed7e49478fc8e831eb74fac33dacc826f36a3c7e831e9f5b27b5f92d666d359251e474184c1a050882c0601118540e110580c022d0a81c260d028045a23038340a0b018b446150384c0a11018045a230a84c1a1105bddc2db63b056aa14ead5228539b74fad9619ed7e4b59904e6dd3eb64de6d359251e3f39b0cf6bf379b4d647418f496b3379251e47418e4fa7b25904da491f91c7a39209ac7e3d1c8b446150384c1a050882c062d118540e0d058b4461306814220b01854260d0882c020706814160300c05fefd7dbe5eef571b85bedd6db6592c762b0d82bf5aacd46a14fa75228f42a0c027d3d92c8273379b4d64b2491c72411f8f4722d118540e2d098340a230882c061509844020d0581c0a03001d0e8743a1d0e8743a1a8d46a351a8d46a351a8d46a351088442211088442211088442210e070381c0e070381c0e070381c0b85c2e170b85c2e12090482412090481c0e070381c0e0701c0e070381c0e070201008040201008040200000000000000001d0e8743a1d0e86a351088442170b85c2e170b85c2e170b848241209048241209048240e070381c0e070381c0e0701c0e070381c0e070381008040201008040201008000000000001f8fc7e3f1f8fc7e3f1f8fc743a1d0e8743a1a8d46a351a8d46a3510884422110884381c0e070381c0e0846a350e0d46a1c108000e1c00070420003870001c0007042350e070001c000fc743a1d0e86a351a8d4422110884381c0e0702e170b85c2412090481c0e070380e070381c0804000000000,
0x9251e3b1cb95b25f3cacc825d49a3c7e451cb74fa5f3cacc825d49a3c7e4f1d9f5b2792a92d6693299251e4527864260d02824021b0a81c1201168540e1306814022d0d81c320d028245a1b0a81c3213028045a1b0a864260d04b85b6bb5bad576b94ca5d02b74aa056a9140b95ba7d6c97cf25525acc82e56e9f5b25d4994c928f1f97cf2552ea4ca645278ecbe4b59974928f2293c727d3c92c82491f91476392a904a63f278ec722d0d8540e19098340a091686c2a070682436150c84c12010d81c3205048042a1306824020706814120179bc5deed75ba5cee571b85bedd6db657abb5cadd6ab34da652e9549a451e81009f4f24b2097cba4527954a64f1d92c92451c9047e3b1c8b43615038b43213068143619048542601068240e0500158ac562b130984c26130984c26130984c261088442211088442211088442210e070381c0e070381c0e070381c0b85c2e170b85c241209048240b0582c160b0582c0e070381c0e070381008040201008040200000000000000001d0e8743a1d0ac562b158ac4c261308442210b85c2e170b85c2e170b85c24120904824120904824120582c160b0582c160b0581c0e070381c0e070381c0804020100804020100800000000000000007e3f1f8fc7e3f1f8fc7e3a1d0e8743a1d0ac562b158ac5626130984c2613084422110884381c0e070381c10898561c1d098161c108000e1c0007042260e070001c1089838040e000383f1d0e8743a158ac562b130984c261088442210e070381c0b85c2e170904824120902c160b0381c0e04020000000,
0x9e566412d98d063d228e5867b2f9e566412d98d063d278ecf6bf3c95496b3319448e832293c220b01824021b0a81c1201118540e110580c02230d81c16030488c36150384406011186c2a11058259ac760aed6eb568b2d168943aed728b44a056e8740ad50a8134b0cf6bf2f9e4aa4b59904d2c33dafcb6632891d063d3497cf2552d98ca245278ecbe4b5996c8e832293c727b3c92c8263238f48a3b1c95482511e93c76391186c2a070882c06091186c2a0705824461b0882c06090d85422090086c0e03048042a110582402070580c12016bb55a6d167b3596c963b1586c15faf576b95bad5668d45a250e8541a04027b3c92c82692d98ca25f2d9149e552893c764b2391472411e8ec72230d8540e230882c061b048542201058240e0300130984c26130984c2613084422110884422110884422110870381c0e070381c0e070381c0e05c2e170b85c1c0e070381c0b0582c160b0582c0e070381c0e07020100804020100800000000000000e8743a1d0e87430180c06030158ac562b158984c261088442170b85c2e170b85c2e170b8381c0e070381c0e070381c0b0582c160b0582c160b0581c0e070381c0e070381c080402010080402010080400000000000000003f1f8fc7e3f1f8fc7e3a1d0e8743a1d0c06030180c0602b158ac562b130984c2613084422110884381c0e070381c10898561c1809838210001c38000e0844c1c0e00038211307038000e0fc743a1d0e86030180c0562b158ac4c2613098422110884381c0e0702e170b85c1c0e07038160b0381c0e04020000000,
0xa3c7e5b31a0c7a451c9bcda5d49a3c7e5b31a0c7a4f1d9b4d693299251e632891d0645278441603048043213068141201098340a110580c02190681416030486426050880c021909834220b04aad4ea550a7556a545a250e994ba2d12814aa1d029142a04ce6f369acba93299251e3f339bcda6b2d98ca247418f4ce5d4994cb663289149e3b37974928f2d91d0645278e4da491f98c8e3d228ec726b298fca23d278ec7219098340a110580c1219098340a110580c32110580c12190984412010c81406090084c1a1105824020d0282c060900ac55ead55aa54ea551a853e9d4da652e9549a451e8d45a250e8541a040267379b4d6672d98ca25d2d9149e532893c764923914723f1e8ec7219098340a110580c320909844020d058240a0300130984c26130984c261088442211088442211088442210e070381c0e070381c0e070381c090482412090381c0e070381c0b0582c160b0582c0e070381c0e070201008040201000000000000001a8d46a351a8c06030180c0562b158ac562613098422110848241209048241209048240e070381c0e070381c0e0702c160b0582c160b0582c16070381c0e070381c0e07038100804020100804020100000000000000000007e3f1f8fc7e3f1f8fc6a351a8d46a351a8c06030180c0562b158ac5626130984c2610884422110884381c0e070381c0e0844c2b0e0c04c1c108d4381c1089838040e00038211307038000e0fc6a351a8d46030180c0562b158ac4c2613098422110884381c0e0702412090481c0e0702c16070381c0804020000000]
def sourceRow (i : Fin 7) (j : Fin 512) : Fin 512 := Fin.ofNat 512 (rowMaps i >>> (9*j.val))
def restriction (i : Fin 7) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 512 => w[(sourceRow i k).val]))).cast List.length_ofFn

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem restriction_bit (i : Fin 7) (w : W) (j : ℕ) (hj : j < 512) :
    (restriction i w)[j] = w[(sourceRow i ⟨j, hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [restriction, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

-- Restriction reads rows, so it commutes with the bitwise gate operations.
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem restriction_not (i : Fin 7) (u : W) : restriction i (~~~u) = ~~~restriction i u :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [restriction_bit, BitVec.getElem_not]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem restriction_ops (i : Fin 7) (a b z : W) (hz : z ∈ basicOps a b) :
    restriction i z ∈ basicOps (restriction i a) (restriction i b) := by
  have hand (u v : W) : restriction i (u &&& v) = (restriction i u &&& restriction i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [restriction_bit, BitVec.getElem_and]
  have hor (u v : W) : restriction i (u ||| v) = (restriction i u ||| restriction i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [restriction_bit, BitVec.getElem_or]
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand, hor, restriction_not]

def remaining (i : Fin 7) : List W :=
  ((List.finRange 7).filter (· != i)).map fun j => restriction i (vinput j)

set_option maxRecDepth 8000 in
theorem projected_input : ∀ i : Fin 7, restriction i (vinput i) = 0 := by decide +kernel
set_option maxRecDepth 8000 in
theorem projected_goal : ∀ i : Fin 7, restriction i goal = goal := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem sameChildren : ∀ i : Fin 7, remaining i = child i := by decide +kernel
set_option maxRecDepth 8000 in
theorem input_index : ∀ w ∈ inputs7, ∃ i : Fin 7, vinput i = w := by
  intro w hw
  simp only [inputs7, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ | exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩ | exact ⟨6,rfl⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem restricted_available : ∀ i j : Fin 7, holds (remaining i).toFinset (restriction i (vinput j)) := by
  intro i j
  by_cases h : i = j
  · subst j
    exact Or.inl (projected_input i)
  · right; right
    exact ⟨_, List.mem_toFinset.mpr (List.mem_map.mpr ⟨j, by simp [Ne.symm h],rfl⟩), Or.inl rfl⟩

-- The first gate, on inputs i and j, does not separate some pair that only input i separates,
-- so input i stays live after it.
def changes (w : W) (r : Fin 256) : Bool :=
  w.getLsbD (256+r.val) != w.getLsbD r.val

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem index_of_op (a b z : W) (hz : z ∈ basicOps a b) :
    ∃ o : Fin 4, (ops a b).getD o.val 0 = z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem unchanged (w : W) (r : Fin 256) (h : changes w r = false) : ¬ differs r w := by
  simpa [changes, differs] using h

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem input_not_goal : ∀ i : Fin 7, vinput i ≠ goal ∧ vinput i ≠ ~~~goal := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem goal_changes : ∀ k : Fin 256, differs k goal ∧ differs k (~~~goal) := by
  unfold differs
  decide +kernel


def misses (i j : Fin 7) (op : Fin 4) (q : Fin 7) (r : Fin 256) : Bool :=
  !changes ((ops (vinput i) (vinput j)).getD op.val 0) r &&
  (List.finRange 7).all (fun h => h == q || !changes (vinput h) r)
def critical : ℕ := 0xc0785b0b603c0784708e03c0783706e03c0782b05603c0788310603c1580f01e0aa0546e8dd0200000000000a054ce99d02a0543286502a0542684d02a0541a83502a0d40a8150680306a0d40180340a99c01000000000008030a2144018030220440180301602c0180b00600c05608c658cb04608c558ab04608ce19c30400000000000608c899130462ac1182315608c758eb044008610c2004008510a2004008410820040089d13a00000000000004008710e2004208010021021780f1010b21644c8990b21643c8790b21e42c8590f2164b09610b000000000002164989310b00e05c0b80700e0480900700e0380700700e0ac1580701c01c0380e00e0841080700000000000

def code (i j : Fin 7) (o : Fin 4) : ℕ := (critical >>> (11*(4*(7*i.val+j.val)+o.val))) % 2048
def side (i j : Fin 7) (o : Fin 4) : Fin 7 := Fin.ofNat 7 (code i j o / 256)
def row (i j : Fin 7) (o : Fin 4) : Fin 256 := Fin.ofNat 256 (code i j o)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem criticalOK : ∀ i j : Fin 7, i ≠ j → ∀ o : Fin 4,
    (side i j o = i ∨ side i j o = j) ∧ misses i j o (side i j o) (row i j o) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem rawAfter {t : W} (ht : t = goal ∨ t = ~~~goal) (i j : Fin 7) (ne : i ≠ j)
    {z : W} (hz : z ∈ basicOps (vinput i) (vinput j)) {r : Finset W}
    (sub : r ⊆ inputs7.toFinset) {k : ℕ} (run : live basicOps t k (insert z r)) :
    ∃ q : Fin 7, (q = i ∨ q = j) ∧ vinput q ∈ r := by
  obtain ⟨o,ho⟩ := index_of_op _ _ _ hz
  obtain ⟨part,ok⟩ := criticalOK i j ne o
  refine ⟨_,part,?_⟩
  simp only [misses,Bool.and_eq_true,Bool.not_eq_true'] at ok
  obtain ⟨hw,others⟩ := ok
  let rr := row i j o
  have d : differs rr t := by
    rcases ht with rfl|rfl
    · exact (goal_changes rr).1
    · exact (goal_changes rr).2
  obtain ⟨u,hu,hd⟩ := live_separates (differs rr) d (ops_differs rr) run
  rcases Finset.mem_insert.mp hu with rfl|hu
  · exact False.elim (unchanged _ _ (ho ▸ hw) hd)
  · obtain ⟨a, rfl⟩ := input_index _ (List.mem_toFinset.mp (sub hu))
    by_contra denied
    have neq : a ≠ side i j o := fun eq => denied (eq ▸ hu)
    have v := List.all_eq_true.mp others a (List.mem_finRange a)
    have h : changes (vinput a) rr = false := by simpa [neq,rr] using v
    exact unchanged _ _ h hd
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem childrenND : ∀ i : Fin 7, (child i).Nodup := by decide +kernel
set_option maxRecDepth 4000 in
theorem projected_impossible (i : Fin 7) (t : W) (ht : t = goal ∨ t = ~~~goal)
    (bound : Excluded 8 (child i))
    (h : SignedBuild 8 (remaining i).toFinset (restriction i t)) : False := by
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  have signs : restriction i t = goal ∨ restriction i t = ~~~goal := by
    rcases ht with rfl|rfl
    · exact Or.inl (projected_goal i)
    · exact Or.inr (by rw [restriction_not, projected_goal])
  have opposite : ~~~restriction i t = goal ∨ ~~~restriction i t = ~~~goal := by
    rcases signs with h|h <;> simp [h]
  have no {u : W} (hu : u = goal ∨ u = ~~~goal) (run : build basicOps u 8 (remaining i).toFinset) : False := by
    exact bound _ hu (sameChildren i ▸ run)
  rcases h with c | c | run | run
  · rcases signs with h|h
    · exact ne.1 (h.symm.trans c)
    · exact ne.2.2.1 (h.symm.trans c)
  · rcases signs with h|h
    · exact ne.2.1 (h.symm.trans c)
    · exact ne.2.2.2 (h.symm.trans c)
  · exact no signs run
  · exact no opposite run

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem no_ten_binary (bounds : ∀ i, Excluded 8 (child i)) (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 10 inputs7.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 9) hl with endcase | ⟨a,ha,b,hb,hab,z,hz,_,rest,he,tail⟩
  · have tx : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := input_index _ (List.mem_toFinset.mp (hs tx))
    rcases ht with rfl|rfl
    · exact (input_not_goal i).1 hi
    · exact (input_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := input_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := input_index _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg vinput eq)
    have sub : rest ⊆ inputs7.toFinset := by
      intro u hu
      exact hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    obtain ⟨q,hq,keep⟩ := rawAfter ht i j hij hz sub tail
    have pg : vinput q ≠ t := by rcases ht with rfl|rfl; exact (input_not_goal q).1; exact (input_not_goal q).2
    apply projected_impossible q t ht (bounds q)
    apply live_transport_save (restriction_ops q)
      tail (Finset.mem_insert_of_mem keep) pg (projected_input q)
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|hw
    · apply mem_ops_zero (restricted_available q i) (restricted_available q j) _ (restriction_ops q _ _ _ hz)
      rcases hq with rfl | rfl
      · exact Or.inl (projected_input _)
      · exact Or.inr (projected_input _)
    · obtain ⟨k,rfl⟩ := input_index _ (List.mem_toFinset.mp (sub hw))
      exact restricted_available q k

set_option maxRecDepth 24000 in
set_option maxHeartbeats 20000000 in
theorem sample : ∀ j : Fin 512, graph (fun i => (inputs7.getD i.val 0)[j.val]) = goal[j.val] := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem eleven_binary (bounds : ∀ i, Excluded 8 (child i)) (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = graph x) :
    10 < binaryCost gs := by
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
  exact no_ten_binary bounds t ht (lift low run)


set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem replacement_of_restrictions (bounds : ∀ i, Excluded 8 (child i)) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o fits _ computes
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hm,hn⟩ := present
    have lt : binaryCost gs < gs.length := List.length_filter_lt_length_iff_exists.mpr
      ⟨g,hm,by simp [isBinary,hn]⟩
    have lower := eleven_binary bounds gs o fits computes
    exact ⟨smallCircuit.gates,smallCircuit.output,smallLegal,by change 12 ≤ gs.length; omega,smallEval⟩
  · refine ⟨gs,o,?_,le_rfl,computes⟩
    intro g hg
    exact ⟨(fits g hg).1.imp_right (·.resolve_right fun h => present ⟨g,hg,h⟩), (fits g hg).2⟩


-- A row selection transfers a signed lower bound across relabelings or repeated samples.
def rowChoice (code : ℕ) (k : Fin 512) : Fin 512 := Fin.ofNat 512 (code >>> (9*k.val))
def selectRows (code : ℕ) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 512 => w[(rowChoice code k).val]))).cast List.length_ofFn
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem selectRows_bit (i : ℕ) (w : W) (j : ℕ) (hj : j < 512) :
    (selectRows i w)[j] = w[(rowChoice i ⟨j, hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [selectRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

-- Restriction reads rows, so it commutes with the bitwise gate operations.
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem selectRows_not (i : ℕ) (u : W) : selectRows i (~~~u) = ~~~selectRows i u :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [selectRows_bit, BitVec.getElem_not]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem selectRows_ops (i : ℕ) (a b z : W) (hz : z ∈ basicOps a b) :
    selectRows i z ∈ basicOps (selectRows i a) (selectRows i b) := by
  have hand (u v : W) : selectRows i (u &&& v) = (selectRows i u &&& selectRows i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [selectRows_bit, BitVec.getElem_and]
  have hor (u v : W) : selectRows i (u ||| v) = (selectRows i u ||| selectRows i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [selectRows_bit, BitVec.getElem_or]
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand, hor, selectRows_not]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem transferRows {k : ℕ} (code : ℕ) (v w : List W) (hg : selectRows code goal = goal)
    (hm : v.all (fun z => w.contains (selectRows code z)) = true)
    (no : Excluded k w) : Excluded k v := by
  intro t signs h
  obtain ⟨S,sub,run⟩ := compress h
  have q := live_transport (selectRows_ops code) run (av := w.toFinset) (by
    intro u hu
    have m := List.all_eq_true.mp hm u (List.mem_toFinset.mp (sub hu))
    exact Or.inr (Or.inr ⟨selectRows code u,List.mem_toFinset.mpr (List.contains_iff_mem.mp m),Or.inl rfl⟩))
  have sign : selectRows code t = goal ∨ selectRows code t = ~~~goal := by
    rcases signs with rfl|rfl
    · exact Or.inl hg
    · exact Or.inr (by rw [selectRows_not,hg])
  have opp : ~~~selectRows code t = goal ∨ ~~~selectRows code t = ~~~goal := by
    rcases sign with hs|hs <;> simp [hs]
  have nonc : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  rcases q with h|h|h|h
  · rcases sign with e|e
    · exact nonc.1 (e.symm.trans h)
    · exact nonc.2.2.1 (e.symm.trans h)
  · rcases sign with e|e
    · exact nonc.2.1 (e.symm.trans h)
    · exact nonc.2.2.2 (e.symm.trans h)
  · exact no _ sign h
  · exact no _ opp h
def aux1_5 : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ef0842108421084210842108421084210842108421084210842108421084210842,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc0f1084210842108421084210842108421084210842108421084210842108421084,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000104210842108421084210842108421084210842108421084210842108421084210,0x100000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem rejectAux1_5 : Excluded 7 aux1_5 := by
  apply exclude_lift (k := 6) (w := k4inputs) 4 260 256 0x100000000000000000000000000000000000000000000000000000000000000000
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro u hu
    simp only [aux1_5,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl <;> unfold differs <;> decide +kernel
  · intro u hu
    simp only [aux1_5,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · exact reject4
def aux1_6 : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ef0842108421084210842108421084210842108421084210842108421084210842,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc0d1084210842108421084210842108421084210842108421084210842108421084,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000104210842108421084210842108421084210842108421084210842108421084210,0x100000000000000000000000000000000000000000000000000000000000000000,0x20000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem rejectAux1_6 : Excluded 8 aux1_6 := by
  apply exclude_lift (k := 7) (w := aux1_5) 1 257 256 0x20000000000000000000000000000000000000000000000000000000000000000
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro u hu
    simp only [aux1_6,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> unfold differs <;> decide +kernel
  · intro u hu
    simp only [aux1_6,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · exact rejectAux1_5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem pinned1 : Excluded 8 (child 1) := by
  apply transferRows 0x864be5f2f97cbe0f0783c1e0f0381c0e070393c9e4f2793c160b0582c16030180c06030080402010099cce673399cca6532994ca633198cc6630c86432190c97cbe5f2f97c1e0f0783c1e070381c0e072793c9e4f2782c160b0582c06030180c06010080402013399cce6733994ca6532994c6633198cc6190c86432192f97cbe5f2f83c1e0f0783c0e070381c0e4f2793c9e4f0582c160b0580c06030180c02010080402673399cce6732994ca653298cc6633198c32190c864325f2f97cbe5f0783c1e0f0781c0e070381c9e4f2793c9e0b0582c160b0180c060301804020100804ce673399cce6532994ca653198cc6633186432190c864be5f2f97cbe0f0783c1e0f0381c0e070393c9e4f2793c160b0582c16030180c06030980402050013044140400098220a020004c1105010002608828080013044140400098220a020004c1105010002608828080013044140400098220a020004c1105010002608828080013044140400098220a020004c1105010002608828080013044140400098220a020004c1105010002608828080013044140400098220a020004c1105010002608828080013044140400098220a020004c1105010002608828080013044140400098220a020004c1105010002608828080013044140400098220a020004c1105010002608828080013044140400098220a020004c1105010002608828080013044140400098220a020004c1105010002608828080013044140400098220a020004c1105010002608828080013044140400098220a020004c11050100026 _ aux1_6
  · decide +kernel
  · decide +kernel
  · exact rejectAux1_6
def aux3_5 : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83f70842108421084210842108421084210842108421084210842108421084210842,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc171084210842108421084210842108421084210842108421084210842108421084,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe82108421084210842108421084210842108421084210842108421084210842108,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210,0x80000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem rejectAux3_5 : Excluded 7 aux3_5 := by
  apply exclude_lift (k := 6) (w := k4inputs) 3 259 256 0x80000000000000000000000000000000000000000000000000000000000000000
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro u hu
    simp only [aux3_5,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl <;> unfold differs <;> decide +kernel
  · intro u hu
    simp only [aux3_5,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · exact reject4
def aux3_6 : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83f70842108421084210842108421084210842108421084210842108421084210842,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc151084210842108421084210842108421084210842108421084210842108421084,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe82108421084210842108421084210842108421084210842108421084210842108,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210,0x80000000000000000000000000000000000000000000000000000000000000000,0x20000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem rejectAux3_6 : Excluded 8 aux3_6 := by
  apply exclude_lift (k := 7) (w := aux3_5) 1 257 256 0x20000000000000000000000000000000000000000000000000000000000000000
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro u hu
    simp only [aux3_6,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> unfold differs <;> decide +kernel
  · intro u hu
    simp only [aux3_6,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · exact rejectAux3_5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem pinned3 : Excluded 8 (child 3) := by
  apply transferRows 0x86cbe5f2f97cbe130984c26130381c0e070393c9e4f2793c1e0f0783c1e030180c0603008040201009a4d269349a4ce673399cce633198cc6630d86c361b0d97cbe5f2f97c26130984c26070381c0e072793c9e4f2783c1e0f0783c06030180c0601008040201349a4d2693499cce673399cc6633198cc61b0d86c361b2f97cbe5f2f84c26130984c0e070381c0e4f2793c9e4f0783c1e0f0780c06030180c0201008040269349a4d2693399cce673398cc6633198c361b0d86c365f2f97cbe5f0984c26130981c0e070381c9e4f2793c9e0f0783c1e0f0180c060301804020100804d269349a4d2673399cce673198cc6633186c361b0d86cbe5f2f97cbe130984c26130381c0e070393c9e4f2793c1e0f0783c1e030180c06030082402050013048140600098240a030004c12050180026090280c0013048140600098240a030004c12050180026090280c0013048140600098240a030004c12050180026090280c0013048140600098240a030004c12050180026090280c0013048140600098240a030004c12050180026090280c0013048140600098240a030004c12050180026090280c0013048140600098240a030004c12050180026090280c0013048140600098240a030004c12050180026090280c0013048140600098240a030004c12050180026090280c0013048140600098240a030004c12050180026090280c0013048140600098240a030004c12050180026090280c0013048140600098240a030004c12050180026090280c0013048140600098240a030004c12050180026 _ aux3_6
  · decide +kernel
  · decide +kernel
  · exact rejectAux3_6
def aux4_5 : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83f70842108421084210842108421084210842108421084210842108421084210842,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc171084210842108421084210842108421084210842108421084210842108421084,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe82108421084210842108421084210842108421084210842108421084210842108,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210,0x80000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem rejectAux4_5 : Excluded 7 aux4_5 := by
  apply exclude_lift (k := 6) (w := k4inputs) 3 259 256 0x80000000000000000000000000000000000000000000000000000000000000000
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro u hu
    simp only [aux4_5,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl <;> unfold differs <;> decide +kernel
  · intro u hu
    simp only [aux4_5,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · exact reject4
def aux4_6 : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83e70842108421084210842108421084210842108421084210842108421084210842,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc071084210842108421084210842108421084210842108421084210842108421084,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe82108421084210842108421084210842108421084210842108421084210842108,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000104210842108421084210842108421084210842108421084210842108421084210,0x80000000000000000000000000000000000000000000000000000000000000000,0x100000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem rejectAux4_6 : Excluded 8 aux4_6 := by
  apply exclude_lift (k := 7) (w := aux4_5) 4 260 256 0x100000000000000000000000000000000000000000000000000000000000000000
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro u hu
    simp only [aux4_6,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> unfold differs <;> decide +kernel
  · intro u hu
    simp only [aux4_6,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · exact rejectAux4_5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem pinned4 : Excluded 8 (child 4) := by
  apply transferRows 0x87cc6633198cc60f0783c1e0f028140a0502954aa552a9541a0d068341a030180c0603008040201009d4ea753a9d4e673399cce66f379bcde6f0f87c3e1f0f98cc6633198c1e0f0783c1e05028140a052a954aa552a8341a0d0683406030180c06010080402013a9d4ea753a9cce673399ccde6f379bcde1f0f87c3e1f3198cc6633183c1e0f0783c0a05028140a552a954aa55068341a0d0680c06030180c02010080402753a9d4ea75399cce673399bcde6f379bc3e1f0f87c3e633198cc6630783c1e0f078140a0502814aa552a954aa0d068341a0d0180c060301804020100804ea753a9d4ea73399cce673379bcde6f3787c3e1f0f87cc6633198cc60f0783c1e0f028140a0502954aa552a9541a0d068341a030180c06030a824020100140401605000a0200b0280050100581400280802c0a00140401605000a0200b0280050100581400280802c0a00140401605000a0200b0280050100581400280802c0a00140401605000a0200b0280050100581400280802c0a00140401605000a0200b0280050100581400280802c0a00140401605000a0200b0280050100581400280802c0a00140401605000a0200b0280050100581400280802c0a00140401605000a0200b0280050100581400280802c0a00140401605000a0200b0280050100581400280802c0a00140401605000a0200b0280050100581400280802c0a00140401605000a0200b0280050100581400280802c0a00140401605000a0200b0280050100581400280802c0a00140401605000a0200b028005010058140028 _ aux4_6
  · decide +kernel
  · decide +kernel
  · exact rejectAux4_6
def aux5_5 : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83f70842108421084210842108421084210842108421084210842108421084210842,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc171084210842108421084210842108421084210842108421084210842108421084,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe82108421084210842108421084210842108421084210842108421084210842108,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210,0x80000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem rejectAux5_5 : Excluded 7 aux5_5 := by
  apply exclude_lift (k := 6) (w := k4inputs) 3 259 256 0x80000000000000000000000000000000000000000000000000000000000000000
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro u hu
    simp only [aux5_5,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl <;> unfold differs <;> decide +kernel
  · intro u hu
    simp only [aux5_5,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · exact reject4
def aux5_6 : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83e70842108421084210842108421084210842108421084210842108421084210842,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc071084210842108421084210842108421084210842108421084210842108421084,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe82108421084210842108421084210842108421084210842108421084210842108,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000104210842108421084210842108421084210842108421084210842108421084210,0x80000000000000000000000000000000000000000000000000000000000000000,0x100000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem rejectAux5_6 : Excluded 8 aux5_6 := by
  apply exclude_lift (k := 7) (w := aux5_5) 4 260 256 0x100000000000000000000000000000000000000000000000000000000000000000
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro u hu
    simp only [aux5_6,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> unfold differs <;> decide +kernel
  · intro u hu
    simp only [aux5_6,List.mem_cons,List.mem_nil_iff,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · exact rejectAux5_5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem pinned5 : Excluded 8 (child 5) := by
  apply transferRows 0x86cca6532994ca0f0783c1e0f028140a0502964b2592c9641a0d068341a030180c0603008040201009dcee773b9dcea753a9d4ea71389c4e2710d86c361b0d994ca65329941e0f0783c1e05028140a052c964b2592c8341a0d0683406030180c06010080402013b9dcee773b9d4ea753a9d4e271389c4e21b0d86c361b32994ca653283c1e0f0783c0a05028140a592c964b259068341a0d0680c06030180c02010080402773b9dcee773a9d4ea753a9c4e271389c4361b0d86c366532994ca650783c1e0f078140a0502814b2592c964b20d068341a0d0180c060301804020100804ee773b9dcee753a9d4ea75389c4e2713886c361b0d86cca6532994ca0f0783c1e0f028140a0502964b2592c9641a0d068341a030180c060309824020100150381405000a81c0a02800540e05014002a070280a00150381405000a81c0a02800540e05014002a070280a00150381405000a81c0a02800540e05014002a070280a00150381405000a81c0a02800540e05014002a070280a00150381405000a81c0a02800540e05014002a070280a00150381405000a81c0a02800540e05014002a070280a00150381405000a81c0a02800540e05014002a070280a00150381405000a81c0a02800540e05014002a070280a00150381405000a81c0a02800540e05014002a070280a00150381405000a81c0a02800540e05014002a070280a00150381405000a81c0a02800540e05014002a070280a00150381405000a81c0a02800540e05014002a070280a00150381405000a81c0a02800540e05014002a _ aux5_6
  · decide +kernel
  · decide +kernel
  · exact rejectAux5_6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem twin (h : Excluded 8 (child 0)) : Excluded 8 (child 2) := by
  apply transferRows 0x8ac8e71319346e4b2090c6a55158a4e26d1f98c962f1e904aa2d1d8acda4f319346e4b2090c6a55198ec1e030580412070b8440a010481c3e110283c060b0387c2e050182c02090f85c220f058240e1f0b8440a0f01804f66f34994c27f2d974b2672d94cc2572991ce26d278fcc64d1b92c5e47389b49e3d2090c6a551691c7e63268f48243198ec563f1b92c7a352a8cc76291b8bc8235168cc562927934962f218b4762b1487c2e110283c060b008243e170881416090387c2e0f0182c02090b8441e010481c22050780c02070280c16010481d0a81419fcfa793d9dce675389bcda6b339a4ca633097cb65d2c95caa530393c9a4b1791c7a41218fc7a331d8dc6a33148bc5a2b1487c2e110287c1e030585c02090883c0e050180416090310070381c0e070381c0e070381c0e06030180c06030180c06030180c05028140a05028140a05028140a040201008040200c06030180c060241209048241209030180c06030180c000000000000000006030180c060301890482412090402010080381c0e060301808040201008040201008040180c06030180c06030180c048241209048241209048240c06030180c06030180c000000000000000000030180c06030180c0603140a05028140a0502814090482412090482410080402010080401c0e070381c0e06030180c06030140a05028140a050301c0e05040200a06048060a00028180e05000140a06038140a00c28281209048241008040200e070381c0c06030180a050281408040201006030180c0482412060301800000000c0603 _ (child 0)
  · decide +kernel
  · decide +kernel
  · exact h
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem fromTwo (h0 : Excluded 8 (child 0)) (h6 : Excluded 8 (child 6)) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  apply replacement_of_restrictions
  intro i
  fin_cases i
  · exact h0
  · exact pinned1
  · exact twin h0
  · exact pinned3
  · exact pinned4
  · exact pinned5
  · exact h6
end PEqualNP.Outside.L_meta_10556_aux.Reduction

namespace PEqualNP.Outside.L_meta_10556_aux

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


end PEqualNP.Outside.L_meta_10556_aux
namespace PEqualNP.Outside.L_meta_10556_aux.NatCheck
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
end PEqualNP.Outside.L_meta_10556_aux.NatCheck
namespace PEqualNP.Outside.L_meta_10556_aux.NatCheck

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
end PEqualNP.Outside.L_meta_10556_aux.NatCheck
namespace PEqualNP.Outside.L_meta_10556_aux.NatCheck
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
end PEqualNP.Outside.L_meta_10556_aux.NatCheck
namespace PEqualNP.Outside.L_meta_10556_aux.NatCheck
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
end PEqualNP.Outside.L_meta_10556_aux.NatCheck
namespace PEqualNP.Outside.L_meta_10556_aux.NatCheck
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
end PEqualNP.Outside.L_meta_10556_aux.NatCheck
namespace PEqualNP.Outside.L_meta_10556_aux.NatCheck.Delete0
def v0 : ℕ := 0x8ab867aaa961830a1c07ccf12c4b12c9697ff02870a1825d5aadbff111f012470000007ff800000003ffc00000000000001ff007f00001fc4aa59ef000f00007
def v1 : ℕ := 0x955aaad552861434005ad7f254952552bfe2b15081422da66cf7da122ff124380007fffff8000001fc000070000000001fe0000000007ffe4cf7da000ff00038
def v2 : ℕ := 0x266d55067c28a90064a17bf4992649bff2a45281120cd20f8f39ef24ff1241c17fffff80000000fe000003f00000003fe0000000001ffe0385186000ff0001c0
def v3 : ℕ := 0xd991999998d30046890dbf98e238ffe4c4c9641a24730437f03ef24ff2240e0afff8000000007f0000003f800000ffc0000000000fff8001b008200ff0000e00
def v4 : ℕ := 0x61e61e61e7004e9932363d2f03ff8e07071188e44b8418c7ffc0fc8f4448f09480000000001f800000003c0003ff0000000000000fe000003000000f0000f000
def v5 : ℕ := 0x7e07e07e001c70e1c3c7e24fffc0f038181e0f078c186107ffff00f8888f89200000000007e000000007c00ffc00000000000007f0000000020000f0000f0000
def v6 : ℕ := 0x80182280000000000002c4f0040100402962b0000000000448a59a1001f000000000007ff8000000000000000000000000000000000001fc48a59a0000f00000
def v7 : ℕ := 0x9ffaeffffbe7973e1c5fdff37cdf37dbfffff178f1e3afff7efffff33ff1367f0007fffff8000001ffffc070000000001ffff007f0007ffe4ef7def00ff0003f
def v8 : ℕ := 0xaa0452aa961830a1c050801284a1289401d402870a18259120825e110001247000000000000000003ffc00000000000001ff007f0000000020004f000000007
def v9 : ℕ := 0x154288555286143400581302509425129680015081422da2245240022e0124380007ff8000000001fc000070000000001fe0000000007e02045240000f000038
def v10 : ℕ := 0x228450228208100040148f008020089602450001000820d0a29af20111000410000000000000000000000000000000000000000000000000000000000000000
def v11 : ℕ := 0xaefd77aefd69ab0a7ca7fff5bd6f5bfffbfff2a972add25fdfbdfff5fff253c77ffffffff80000fe03ffc3f00000003fe01ff007f01fffffcfbdfef0fff001c7
def v12 : ℕ := 0x889022a88141020a1806840124491240095ba02860a10050508410d100e012060000007ff800000003ffc00000000000001ff007f00001fc4aa59ef000f00007
def v13 : ℕ := 0x244510045408280060a033049124493692800281020c500285104004ee0241807fffff80000000fe000003f00000003fe0000000001ffe0385186000ff0001c0
def v14 : ℕ := 0x889001888841000208058c90200812c04049600820210015502cb241102002020000000000000000000000000000000000000000000000000000000000000000
def v15 : ℕ := 0x228662221208308140240610c43000929369020508082480a810db001d010450000007ff800000003ffc00000000000001ff007f00001fc4aa59ef000f00007
def v16 : ℕ := 0x510198111092004481083308c230ed248480041204520422a012400ee2040c08fff8000000007f0000003f800000ffc0000000000fff8001b008200ff0000e00
def v17 : ℕ := 0xa00620a100020810060c21004b020101118020408000455a80bc81004010040000000000000000000000000000000000000000000000000000000000000000
def v18 : ℕ := 0xebfe7febef61cf9b3e37fdff2fff9ecf6f7ff8ec7ba59adfffedffff55f8f2d78000007ff81f800003fffc0003ff0000001ff007ffe001fc7aa59eff00f0f007
def v19 : ℕ := 0x8a18618a086181020c01c0d02c0010c8686e700830218218002d037011b002430000007ff800000003ffc00000000000001ff007f00001fc4aa59ef000f00007
def v20 : ℕ := 0x6146184146004c912230310e03b48c06060008c40b041882a540400e4408e09080000000001f800000003c0003ff0000000000000fe000003000000f0000f000
def v21 : ℕ := 0xa00602a000000000007c0412c401008081e0000000000055aad00f00080000000000000000000000007c0000000000000000007f0000000020000f000000000
def v22 : ℕ := 0xfebfe7fea97df3ebdfc7eeffffcbf2f9797fff2ffcb9e35fffffbff999ff9b670000007fffe0000003ffc00ffc000000001ff007f00001fc4aa59ef000ff0007
def v23 : ℕ := 0x80b80780a961830a1c000cb0000b02c16161f02870a182580000bf01117012470000007ff800000003f8000000000000001ff000000001fc48a59e0000f00007
def v24 : ℕ := 0x74078054001c70e1c3c0220ed380e03010000f078c186102a5520008880f89200000000007e000000000000ffc000000000000000000000000000000000f0000
def v25 : ℕ := 0xb77fffd77eaebd3464fbfff6ddb76dffffe6f3d1934effafefffff36fff365f97ffffffff80000fffc0003f00000003fffe00000001fffffcdfffa00fff001f8
def v26 : ℕ := 0x9112aad102861434005a8402449124400d42a15081422da060c6101200e124380000007ff8000001fc000000000000001fe00000000001fc48e79a0000f00038
def v27 : ℕ := 0x222555022c28a90064a12804892248ad40044281120cd20983082524d00241c17ff80000000000fe000003800000003fe0000000001f800181082000f00001c0
def v28 : ℕ := 0x9110889110820004000897904010254084c02010004204266036d202222004080000000000000000000000000000000000000000000000000000000000000000
def v29 : ℕ := 0xdddbbbdddad71476895ffffaf6bdfff6ffebf55aa5732db7fcfffa5ffff52e3afffffffff8007f01fc003ff00000ffc01fe000000ffffffffcfffa0ffff00e38
def v30 : ℕ := 0x44a22444204143000524062148500123b229140810029800cc108100dd120300007fffff8000001fc000070000000001fe0000000007ffe4cf7da000ff00038
def v31 : ℕ := 0x488111088851004289052808a228daa44009440a243100119008204dd0040a02fff8000000007f0000003f800000ffc0000000000fff8001b008200ff0000e00
def v32 : ℕ := 0x1420a4142000410001215220095040207008040010008866cc0d802044020100000000000000000000000000000000000000000000000000000000000000000
def v33 : ℕ := 0xf5febef5f7865ebd327effff57ffaf57bff3b9f4cbc63de7fff7fe9f6ff9f4bc8007fffff81f8001fc003c7003ff00001fe000000fe07ffe7cf7da0f0ff0f038
def v34 : ℕ := 0x9418a094108610240048c2d054002150b8e2311080422520003702102bb104280007fffff8000001fc000070000000001fe0000000007ffe4cf7da000ff00038
def v35 : ℕ := 0x60a41420a5004a893224280d036a8a05001108a44a8410419300248d4008d08480000000001f800000003c0003ff0000000000000fe000003000000f0000f000
def v36 : ℕ := 0x1402a054000410200042c2425480201018020100800021066cf70010088100200000000000000000000000000000000000000000000000000000000000000000
def v37 : ℕ := 0xff5feaff529e74f5c3dff7ffffd5f57abffebf578d5a6da7ffffdafaafffad380007ffffffe00001fc07c07ffc0000001fe00007f0007ffe4ef7daf00fff0038
def v38 : ℕ := 0x81580a8152820414001815b000150542a7e0b05001420ca00000da02277024180007fffff8000001fc000070000000001fe0000000007ffe4cf7da000ff00038
def v39 : ℕ := 0x6a05402a001860c1c385200dab40d028001c0e070c184001930800e8800e89000000000007e000000007c00ffc00000000000007f0000000020000f0000f0000
def v40 : ℕ := 0x111001800000000013b90802049a4c0804000000000078038e204f20000007ff8000000000000000003800000000000000000001f800180082000f0000000
def v41 : ℕ := 0xfffddd9ffcfba946edadfffcfb3efffff6ed769b367fd63fff3fff6fff364fcbffffff8000007ffe00003ff00000ffffe00000000ffffe03b518600fff000fc0
def v42 : ℕ := 0x266c44066428a90064a040641906001b32241281120cd2080f010d200d1241c10007ff80000000fe000000700000003fe000000000007e02051040000f0001c0
def v43 : ℕ := 0xd990889980d30046890c84086218b6400449241a247304307006104b00240e0a8000000000007f0000003c000000ffc0000000000fe000003000000f00000e00
def v44 : ℕ := 0x2064140064000800202039240126080702000080020410078f00ec04440040800000000000000000000000000000000000000000000000000000000000000000
def v45 : ℕ := 0x67ef5f67ff28ef9976b77fff9bffcfbff7b5dae55b8cdacffff9ffafff5af1d5ffffff80001f80fe00003ff003ff003fe00000000ffffe03b518600fff00f1c0
def v46 : ℕ := 0x60941061828a100448142d0980041b8f0a452011008c20800390320bb1201417fffff80000000fe000003f00000003fe0000000001ffe0385186000ff0001c0
def v47 : ℕ := 0x41820a61830046991216040b02d9860005118864498008c070c0108b0048b01480000000001f800000003c0003ff0000000000000fe000003000000f0000f000
def v48 : ℕ := 0x2605400600082000408162449900403810040201000840078f390020880201000000000000000000000000000000000000000000000000000000000000000000
def v49 : ℕ := 0x7e6ff57e7c3cf9e1e7e7fbffffe6f9bffabe5f879e1cf30fffffeffcff9fc9e17fffff8007e000fe0007c3fffc00003fe0000007f01ffe03871860f0ff0f01c0
def v50 : ℕ := 0x6815007c208900242019b000260987e2a05080120492080000ef04771040c17fffff80000000fe000003f00000003fe0000000001ffe0385186000ff0001c0
def v51 : ℕ := 0x5802a078001450e18346800b66c0b000081a0d068c10210070c600d8008d88200000000007e000000007c00ffc00000000000007f0000000020000f0000f0000
def v52 : ℕ := 0x418018018000000000043d0802388e040401000000000007f000f00f40000000800000000000000000003c0000000000000000000fe000003000000f00000000
def v53 : ℕ := 0xf9f79ff9ffd34edfbb3fbfbfe3ffffe7c7d9ecfe6ff71cf7fffefecff66cfe9efff80000001fff0000003f8003ffffc0000000000fff8001b008200ff000fe00
def v54 : ℕ := 0x9811819818d3004689098290e00071e0c0c8641a24730430003e0240b2240e0a7ff8000000007f00000003800000ffc000000000001f800180082000f0000e00
def v55 : ℕ := 0x2066066067004e993232002701c70003031088e44b8418c00fc00c800448f09400000000001f80000000000003ff00000000000000000000000000000000f000
def v56 : ℕ := 0x58018018001000408105a208e200f0200008040204100007f03e0048800408000000000000000000000000000000000000000000000000000000000000000000
def v57 : ℕ := 0xff97f9ff98df70e7cbcfffdffff8fffcdcdf6f1fac7b6537fffff2fffaaf8f2afff8000007e07f000007ff8ffc00ffc000000007ffff8001b20820fff00f0e00
def v58 : ℕ := 0x8190198198c3000608081d9000380fc4c4c16018206304300000f2077220060afff8000000007f0000003f800000ffc0000000000fff8001b008200ff0000e00
def v59 : ℕ := 0x26066066000c70a142c240471dc0001818160b05880861000fc100b0088b81200000000007e000000007c00ffc00000000000007f0000000020000f0000f0000
def v60 : ℕ := 0x60060060000040810206200f03c080000010080408000007ffc00088000880000000000000000000000000000000000000000000000000000000000000000000
def v61 : ℕ := 0x7fe7fe7fe71c7ef9f3f7ff6ffffffe3f1f1f8fe7cf9c79c7fffffcffcccff9b48000000007ff80000007fc0fffff000000000007ffe00000320000ff000ff000
def v62 : ℕ := 0x1e01e01e7000e1830301d20003f0e07070180e0438418c00000fc074440709480000000001f800000003c0003ff0000000000000fe000003000000f0000f000
def v63 : ℕ := 0x1e01e01e001c3060c1c1c240fc007038180e070384186100003f0070888709200000000007e000000007c00ffc00000000000007f0000000020000f0000f0000
def wires0 : List ℕ := [v0,v1,v2,v3,v4,v5]
def wires1 : List ℕ := [v6,v0,v1,v2,v3,v4,v5]
def block0 : List CallState := ((nextList 1 wires1).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed0 : AllRejected 6 block0 := checkedBlock (by decide +kernel)
def block1 : List CallState := ((nextList 1 wires1).drop 14).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed1 : AllRejected 6 block1 := checkedBlock (by decide +kernel)
def block2 : List CallState := ((nextList 1 wires1).drop 25).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed2 : AllRejected 6 block2 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node1 : walk 7 1 wires1 = false := by
  have rest := (appendOk closed0 (appendOk closed1 (appendOk closed2 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires1) (by decide +kernel) (by decide +kernel) rest
def wires2 : List ℕ := [v7,v0,v1,v2,v3,v4,v5]
def block3 : List CallState := ((nextList 1 wires2).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed3 : AllRejected 6 block3 := checkedBlock (by decide +kernel)
def block4 : List CallState := ((nextList 1 wires2).drop 14).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed4 : AllRejected 6 block4 := checkedBlock (by decide +kernel)
def block5 : List CallState := ((nextList 1 wires2).drop 26).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed5 : AllRejected 6 block5 := checkedBlock (by decide +kernel)
def block6 : List CallState := ((nextList 1 wires2).drop 38).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed6 : AllRejected 6 block6 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node2 : walk 7 1 wires2 = false := by
  have rest := (appendOk closed3 (appendOk closed4 (appendOk closed5 (appendOk closed6 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires2) (by decide +kernel) (by decide +kernel) rest
def wires3 : List ℕ := [v8,v0,v1,v2,v3,v4,v5]
def block7 : List CallState := ((nextList 1 wires3).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed7 : AllRejected 6 block7 := checkedBlock (by decide +kernel)
def block8 : List CallState := ((nextList 1 wires3).drop 13).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed8 : AllRejected 6 block8 := checkedBlock (by decide +kernel)
def block9 : List CallState := ((nextList 1 wires3).drop 21).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed9 : AllRejected 6 block9 := checkedBlock (by decide +kernel)
def block10 : List CallState := ((nextList 1 wires3).drop 30).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed10 : AllRejected 6 block10 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node3 : walk 7 1 wires3 = false := by
  have rest := (appendOk closed7 (appendOk closed8 (appendOk closed9 (appendOk closed10 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires3) (by decide +kernel) (by decide +kernel) rest
def wires4 : List ℕ := [v9,v0,v1,v2,v3,v4,v5]
def block11 : List CallState := ((nextList 1 wires4).drop 0).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed11 : AllRejected 6 block11 := checkedBlock (by decide +kernel)
def block12 : List CallState := ((nextList 1 wires4).drop 12).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed12 : AllRejected 6 block12 := checkedBlock (by decide +kernel)
def block13 : List CallState := ((nextList 1 wires4).drop 22).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed13 : AllRejected 6 block13 := checkedBlock (by decide +kernel)
def block14 : List CallState := ((nextList 1 wires4).drop 31).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed14 : AllRejected 6 block14 := checkedBlock (by decide +kernel)
def block15 : List CallState := ((nextList 1 wires4).drop 41).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed15 : AllRejected 6 block15 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node4 : walk 7 1 wires4 = false := by
  have rest := (appendOk closed11 (appendOk closed12 (appendOk closed13 (appendOk closed14 (appendOk closed15 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires4) (by decide +kernel) (by decide +kernel) rest
def wires5 : List ℕ := [v10,v0,v2,v1,v3,v4,v5]
def block16 : List CallState := ((nextList 1 wires5).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed16 : AllRejected 6 block16 := checkedBlock (by decide +kernel)
def block17 : List CallState := ((nextList 1 wires5).drop 11).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed17 : AllRejected 6 block17 := checkedBlock (by decide +kernel)
def block18 : List CallState := ((nextList 1 wires5).drop 16).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed18 : AllRejected 6 block18 := checkedBlock (by decide +kernel)
def block19 : List CallState := ((nextList 1 wires5).drop 23).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed19 : AllRejected 6 block19 := checkedBlock (by decide +kernel)
def block20 : List CallState := ((nextList 1 wires5).drop 28).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed20 : AllRejected 6 block20 := checkedBlock (by decide +kernel)
def block21 : List CallState := ((nextList 1 wires5).drop 33).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed21 : AllRejected 6 block21 := checkedBlock (by decide +kernel)
def block22 : List CallState := ((nextList 1 wires5).drop 41).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed22 : AllRejected 6 block22 := checkedBlock (by decide +kernel)
def block23 : List CallState := ((nextList 1 wires5).drop 46).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed23 : AllRejected 6 block23 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node5 : walk 7 1 wires5 = false := by
  have rest := (appendOk closed16 (appendOk closed17 (appendOk closed18 (appendOk closed19 (appendOk closed20 (appendOk closed21 (appendOk closed22 (appendOk closed23 (emptyOk 6)))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires5) (by decide +kernel) (by decide +kernel) rest
def wires6 : List ℕ := [v11,v0,v2,v1,v3,v4,v5]
def block24 : List CallState := ((nextList 1 wires6).drop 0).take 16
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed24 : AllRejected 6 block24 := checkedBlock (by decide +kernel)
def block25 : List CallState := ((nextList 1 wires6).drop 16).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed25 : AllRejected 6 block25 := checkedBlock (by decide +kernel)
def block26 : List CallState := ((nextList 1 wires6).drop 30).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed26 : AllRejected 6 block26 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node6 : walk 7 1 wires6 = false := by
  have rest := (appendOk closed24 (appendOk closed25 (appendOk closed26 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires6) (by decide +kernel) (by decide +kernel) rest
def wires7 : List ℕ := [v12,v0,v2,v1,v3,v4,v5]
def block27 : List CallState := ((nextList 1 wires7).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed27 : AllRejected 6 block27 := checkedBlock (by decide +kernel)
def block28 : List CallState := ((nextList 1 wires7).drop 14).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed28 : AllRejected 6 block28 := checkedBlock (by decide +kernel)
def block29 : List CallState := ((nextList 1 wires7).drop 26).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed29 : AllRejected 6 block29 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node7 : walk 7 1 wires7 = false := by
  have rest := (appendOk closed27 (appendOk closed28 (appendOk closed29 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires7) (by decide +kernel) (by decide +kernel) rest
def wires8 : List ℕ := [v13,v0,v2,v1,v3,v4,v5]
def block30 : List CallState := ((nextList 1 wires8).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed30 : AllRejected 6 block30 := checkedBlock (by decide +kernel)
def block31 : List CallState := ((nextList 1 wires8).drop 14).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed31 : AllRejected 6 block31 := checkedBlock (by decide +kernel)
def block32 : List CallState := ((nextList 1 wires8).drop 24).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed32 : AllRejected 6 block32 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node8 : walk 7 1 wires8 = false := by
  have rest := (appendOk closed30 (appendOk closed31 (appendOk closed32 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires8) (by decide +kernel) (by decide +kernel) rest
def wires9 : List ℕ := [v14,v0,v3,v1,v2,v4,v5]
def block33 : List CallState := ((nextList 1 wires9).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed33 : AllRejected 6 block33 := checkedBlock (by decide +kernel)
def block34 : List CallState := ((nextList 1 wires9).drop 10).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed34 : AllRejected 6 block34 := checkedBlock (by decide +kernel)
def block35 : List CallState := ((nextList 1 wires9).drop 16).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed35 : AllRejected 6 block35 := checkedBlock (by decide +kernel)
def block36 : List CallState := ((nextList 1 wires9).drop 23).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed36 : AllRejected 6 block36 := checkedBlock (by decide +kernel)
def block37 : List CallState := ((nextList 1 wires9).drop 30).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed37 : AllRejected 6 block37 := checkedBlock (by decide +kernel)
def block38 : List CallState := ((nextList 1 wires9).drop 36).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed38 : AllRejected 6 block38 := checkedBlock (by decide +kernel)
def block39 : List CallState := ((nextList 1 wires9).drop 43).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed39 : AllRejected 6 block39 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node9 : walk 7 1 wires9 = false := by
  have rest := (appendOk closed33 (appendOk closed34 (appendOk closed35 (appendOk closed36 (appendOk closed37 (appendOk closed38 (appendOk closed39 (emptyOk 6))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires9) (by decide +kernel) (by decide +kernel) rest
def block40 : List CallState := ((nextList 3 wires0).drop 9).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed40 : AllRejected 7 block40 := checkedBlock (by decide +kernel)
def wires10 : List ℕ := [v15,v0,v3,v1,v2,v4,v5]
def block41 : List CallState := ((nextList 1 wires10).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed41 : AllRejected 6 block41 := checkedBlock (by decide +kernel)
def block42 : List CallState := ((nextList 1 wires10).drop 14).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed42 : AllRejected 6 block42 := checkedBlock (by decide +kernel)
def block43 : List CallState := ((nextList 1 wires10).drop 26).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed43 : AllRejected 6 block43 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node10 : walk 7 1 wires10 = false := by
  have rest := (appendOk closed41 (appendOk closed42 (appendOk closed43 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires10) (by decide +kernel) (by decide +kernel) rest
def wires11 : List ℕ := [v16,v0,v3,v1,v2,v4,v5]
def block44 : List CallState := ((nextList 1 wires11).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed44 : AllRejected 6 block44 := checkedBlock (by decide +kernel)
def block45 : List CallState := ((nextList 1 wires11).drop 14).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed45 : AllRejected 6 block45 := checkedBlock (by decide +kernel)
def block46 : List CallState := ((nextList 1 wires11).drop 26).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed46 : AllRejected 6 block46 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node11 : walk 7 1 wires11 = false := by
  have rest := (appendOk closed44 (appendOk closed45 (appendOk closed46 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires11) (by decide +kernel) (by decide +kernel) rest
def wires12 : List ℕ := [v17,v0,v4,v1,v2,v3,v5]
def block47 : List CallState := ((nextList 1 wires12).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed47 : AllRejected 6 block47 := checkedBlock (by decide +kernel)
def block48 : List CallState := ((nextList 1 wires12).drop 10).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed48 : AllRejected 6 block48 := checkedBlock (by decide +kernel)
def block49 : List CallState := ((nextList 1 wires12).drop 16).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed49 : AllRejected 6 block49 := checkedBlock (by decide +kernel)
def block50 : List CallState := ((nextList 1 wires12).drop 23).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed50 : AllRejected 6 block50 := checkedBlock (by decide +kernel)
def block51 : List CallState := ((nextList 1 wires12).drop 30).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed51 : AllRejected 6 block51 := checkedBlock (by decide +kernel)
def block52 : List CallState := ((nextList 1 wires12).drop 36).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed52 : AllRejected 6 block52 := checkedBlock (by decide +kernel)
def block53 : List CallState := ((nextList 1 wires12).drop 43).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed53 : AllRejected 6 block53 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node12 : walk 7 1 wires12 = false := by
  have rest := (appendOk closed47 (appendOk closed48 (appendOk closed49 (appendOk closed50 (appendOk closed51 (appendOk closed52 (appendOk closed53 (emptyOk 6))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires12) (by decide +kernel) (by decide +kernel) rest
def wires13 : List ℕ := [v18,v0,v4,v1,v2,v3,v5]
def block54 : List CallState := ((nextList 1 wires13).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed54 : AllRejected 6 block54 := checkedBlock (by decide +kernel)
def block55 : List CallState := ((nextList 1 wires13).drop 13).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed55 : AllRejected 6 block55 := checkedBlock (by decide +kernel)
def block56 : List CallState := ((nextList 1 wires13).drop 25).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed56 : AllRejected 6 block56 := checkedBlock (by decide +kernel)
def block57 : List CallState := ((nextList 1 wires13).drop 34).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed57 : AllRejected 6 block57 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node13 : walk 7 1 wires13 = false := by
  have rest := (appendOk closed54 (appendOk closed55 (appendOk closed56 (appendOk closed57 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires13) (by decide +kernel) (by decide +kernel) rest
def wires14 : List ℕ := [v19,v0,v4,v1,v2,v3,v5]
def block58 : List CallState := ((nextList 1 wires14).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed58 : AllRejected 6 block58 := checkedBlock (by decide +kernel)
def block59 : List CallState := ((nextList 1 wires14).drop 13).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed59 : AllRejected 6 block59 := checkedBlock (by decide +kernel)
def block60 : List CallState := ((nextList 1 wires14).drop 27).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed60 : AllRejected 6 block60 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node14 : walk 7 1 wires14 = false := by
  have rest := (appendOk closed58 (appendOk closed59 (appendOk closed60 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires14) (by decide +kernel) (by decide +kernel) rest
def wires15 : List ℕ := [v20,v0,v4,v1,v2,v3,v5]
def block61 : List CallState := ((nextList 1 wires15).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed61 : AllRejected 6 block61 := checkedBlock (by decide +kernel)
def block62 : List CallState := ((nextList 1 wires15).drop 10).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed62 : AllRejected 6 block62 := checkedBlock (by decide +kernel)
def block63 : List CallState := ((nextList 1 wires15).drop 20).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed63 : AllRejected 6 block63 := checkedBlock (by decide +kernel)
def block64 : List CallState := ((nextList 1 wires15).drop 30).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed64 : AllRejected 6 block64 := checkedBlock (by decide +kernel)
def block65 : List CallState := ((nextList 1 wires15).drop 38).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed65 : AllRejected 6 block65 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node15 : walk 7 1 wires15 = false := by
  have rest := (appendOk closed61 (appendOk closed62 (appendOk closed63 (appendOk closed64 (appendOk closed65 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires15) (by decide +kernel) (by decide +kernel) rest
def wires16 : List ℕ := [v21,v0,v5,v1,v2,v3,v4]
def block66 : List CallState := ((nextList 1 wires16).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed66 : AllRejected 6 block66 := checkedBlock (by decide +kernel)
def block67 : List CallState := ((nextList 1 wires16).drop 11).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed67 : AllRejected 6 block67 := checkedBlock (by decide +kernel)
def block68 : List CallState := ((nextList 1 wires16).drop 22).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed68 : AllRejected 6 block68 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node16 : walk 7 1 wires16 = false := by
  have rest := (appendOk closed66 (appendOk closed67 (appendOk closed68 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires16) (by decide +kernel) (by decide +kernel) rest
def wires17 : List ℕ := [v22,v5,v1,v2,v3,v4]
def block69 : List CallState := ((nextList 2 wires17).drop 0).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed69 : AllRejected 6 block69 := checkedBlock (by decide +kernel)
def block70 : List CallState := ((nextList 2 wires17).drop 5).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed70 : AllRejected 6 block70 := checkedBlock (by decide +kernel)
def block71 : List CallState := ((nextList 2 wires17).drop 11).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed71 : AllRejected 6 block71 := checkedBlock (by decide +kernel)
def block72 : List CallState := ((nextList 2 wires17).drop 17).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed72 : AllRejected 6 block72 := checkedBlock (by decide +kernel)
def block73 : List CallState := ((nextList 2 wires17).drop 20).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed73 : AllRejected 6 block73 := checkedBlock (by decide +kernel)
def block74 : List CallState := ((nextList 2 wires17).drop 21).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed74 : AllRejected 6 block74 := checkedBlock (by decide +kernel)
def block75 : List CallState := ((nextList 2 wires17).drop 24).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed75 : AllRejected 6 block75 := checkedBlock (by decide +kernel)
def block76 : List CallState := ((nextList 2 wires17).drop 27).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed76 : AllRejected 6 block76 := checkedBlock (by decide +kernel)
def block77 : List CallState := ((nextList 2 wires17).drop 30).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed77 : AllRejected 6 block77 := checkedBlock (by decide +kernel)
def block78 : List CallState := ((nextList 2 wires17).drop 35).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed78 : AllRejected 6 block78 := checkedBlock (by decide +kernel)
def block79 : List CallState := ((nextList 2 wires17).drop 39).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed79 : AllRejected 6 block79 := checkedBlock (by decide +kernel)
def block80 : List CallState := ((nextList 2 wires17).drop 42).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed80 : AllRejected 6 block80 := checkedBlock (by decide +kernel)
def block81 : List CallState := ((nextList 2 wires17).drop 48).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed81 : AllRejected 6 block81 := checkedBlock (by decide +kernel)
def block82 : List CallState := ((nextList 2 wires17).drop 53).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed82 : AllRejected 6 block82 := checkedBlock (by decide +kernel)
def block83 : List CallState := ((nextList 2 wires17).drop 59).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed83 : AllRejected 6 block83 := checkedBlock (by decide +kernel)
def block84 : List CallState := ((nextList 2 wires17).drop 65).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed84 : AllRejected 6 block84 := checkedBlock (by decide +kernel)
def block85 : List CallState := ((nextList 2 wires17).drop 67).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed85 : AllRejected 6 block85 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node17 : walk 7 2 wires17 = false := by
  have rest := (appendOk closed69 (appendOk closed70 (appendOk closed71 (appendOk closed72 (appendOk closed73 (appendOk closed74 (appendOk closed75 (appendOk closed76 (appendOk closed77 (appendOk closed78 (appendOk closed79 (appendOk closed80 (appendOk closed81 (appendOk closed82 (appendOk closed83 (appendOk closed84 (appendOk closed85 (emptyOk 6))))))))))))))))))
  exact split_walk (k := 6) (e := 2) (ws := wires17) (by decide +kernel) (by decide +kernel) rest
def wires18 : List ℕ := [v22,v0,v5,v1,v2,v3,v4]
def block86 : List CallState := ((nextList 1 wires18).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed86 : AllRejected 6 block86 := checkedBlock (by decide +kernel)
def block87 : List CallState := ((nextList 1 wires18).drop 13).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed87 : AllRejected 6 block87 := checkedBlock (by decide +kernel)
def block88 : List CallState := ((nextList 1 wires18).drop 24).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed88 : AllRejected 6 block88 := checkedBlock (by decide +kernel)
def block89 : List CallState := ((nextList 1 wires18).drop 31).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed89 : AllRejected 6 block89 := checkedBlock (by decide +kernel)
def block90 : List CallState := ((nextList 1 wires18).drop 39).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed90 : AllRejected 6 block90 := checkedBlock (by decide +kernel)
def block91 : List CallState := ((nextList 1 wires18).drop 45).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed91 : AllRejected 6 block91 := checkedBlock (by decide +kernel)
def block92 : List CallState := ((nextList 1 wires18).drop 53).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed92 : AllRejected 6 block92 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node18 : walk 7 1 wires18 = false := by
  have rest := (appendOk closed86 (appendOk closed87 (appendOk closed88 (appendOk closed89 (appendOk closed90 (appendOk closed91 (appendOk closed92 (emptyOk 6))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires18) (by decide +kernel) (by decide +kernel) rest
def wires19 : List ℕ := [v23,v5,v1,v2,v3,v4]
def block93 : List CallState := ((nextList 2 wires19).drop 0).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed93 : AllRejected 6 block93 := checkedBlock (by decide +kernel)
def block94 : List CallState := ((nextList 2 wires19).drop 4).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed94 : AllRejected 6 block94 := checkedBlock (by decide +kernel)
def block95 : List CallState := ((nextList 2 wires19).drop 9).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed95 : AllRejected 6 block95 := checkedBlock (by decide +kernel)
def block96 : List CallState := ((nextList 2 wires19).drop 16).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed96 : AllRejected 6 block96 := checkedBlock (by decide +kernel)
def block97 : List CallState := ((nextList 2 wires19).drop 22).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed97 : AllRejected 6 block97 := checkedBlock (by decide +kernel)
def block98 : List CallState := ((nextList 2 wires19).drop 32).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed98 : AllRejected 6 block98 := checkedBlock (by decide +kernel)
def block99 : List CallState := ((nextList 2 wires19).drop 42).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed99 : AllRejected 6 block99 := checkedBlock (by decide +kernel)
def block100 : List CallState := ((nextList 2 wires19).drop 54).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed100 : AllRejected 6 block100 := checkedBlock (by decide +kernel)
def block101 : List CallState := ((nextList 2 wires19).drop 60).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed101 : AllRejected 6 block101 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node19 : walk 7 2 wires19 = false := by
  have rest := (appendOk closed93 (appendOk closed94 (appendOk closed95 (appendOk closed96 (appendOk closed97 (appendOk closed98 (appendOk closed99 (appendOk closed100 (appendOk closed101 (emptyOk 6))))))))))
  exact split_walk (k := 6) (e := 2) (ws := wires19) (by decide +kernel) (by decide +kernel) rest
def wires20 : List ℕ := [v23,v0,v5,v1,v2,v3,v4]
def block102 : List CallState := ((nextList 1 wires20).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed102 : AllRejected 6 block102 := checkedBlock (by decide +kernel)
def block103 : List CallState := ((nextList 1 wires20).drop 11).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed103 : AllRejected 6 block103 := checkedBlock (by decide +kernel)
def block104 : List CallState := ((nextList 1 wires20).drop 17).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed104 : AllRejected 6 block104 := checkedBlock (by decide +kernel)
def block105 : List CallState := ((nextList 1 wires20).drop 25).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed105 : AllRejected 6 block105 := checkedBlock (by decide +kernel)
def block106 : List CallState := ((nextList 1 wires20).drop 31).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed106 : AllRejected 6 block106 := checkedBlock (by decide +kernel)
def block107 : List CallState := ((nextList 1 wires20).drop 41).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed107 : AllRejected 6 block107 := checkedBlock (by decide +kernel)
def block108 : List CallState := ((nextList 1 wires20).drop 49).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed108 : AllRejected 6 block108 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node20 : walk 7 1 wires20 = false := by
  have rest := (appendOk closed102 (appendOk closed103 (appendOk closed104 (appendOk closed105 (appendOk closed106 (appendOk closed107 (appendOk closed108 (emptyOk 6))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires20) (by decide +kernel) (by decide +kernel) rest
def wires21 : List ℕ := [v24,v0,v5,v1,v2,v3,v4]
def block109 : List CallState := ((nextList 1 wires21).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed109 : AllRejected 6 block109 := checkedBlock (by decide +kernel)
def block110 : List CallState := ((nextList 1 wires21).drop 11).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed110 : AllRejected 6 block110 := checkedBlock (by decide +kernel)
def block111 : List CallState := ((nextList 1 wires21).drop 22).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed111 : AllRejected 6 block111 := checkedBlock (by decide +kernel)
def block112 : List CallState := ((nextList 1 wires21).drop 33).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed112 : AllRejected 6 block112 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node21 : walk 7 1 wires21 = false := by
  have rest := (appendOk closed109 (appendOk closed110 (appendOk closed111 (appendOk closed112 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires21) (by decide +kernel) (by decide +kernel) rest
def block113 : List CallState := ((nextList 3 wires0).drop 22).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed113 : AllRejected 7 block113 := checkedBlock (by decide +kernel)
def wires22 : List ℕ := [v25,v1,v2,v0,v3,v4,v5]
def block114 : List CallState := ((nextList 1 wires22).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed114 : AllRejected 6 block114 := checkedBlock (by decide +kernel)
def block115 : List CallState := ((nextList 1 wires22).drop 14).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed115 : AllRejected 6 block115 := checkedBlock (by decide +kernel)
def block116 : List CallState := ((nextList 1 wires22).drop 21).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed116 : AllRejected 6 block116 := checkedBlock (by decide +kernel)
def block117 : List CallState := ((nextList 1 wires22).drop 32).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed117 : AllRejected 6 block117 := checkedBlock (by decide +kernel)
def block118 : List CallState := ((nextList 1 wires22).drop 42).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed118 : AllRejected 6 block118 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node22 : walk 7 1 wires22 = false := by
  have rest := (appendOk closed114 (appendOk closed115 (appendOk closed116 (appendOk closed117 (appendOk closed118 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires22) (by decide +kernel) (by decide +kernel) rest
def wires23 : List ℕ := [v26,v1,v2,v0,v3,v4,v5]
def block119 : List CallState := ((nextList 1 wires23).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed119 : AllRejected 6 block119 := checkedBlock (by decide +kernel)
def block120 : List CallState := ((nextList 1 wires23).drop 11).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed120 : AllRejected 6 block120 := checkedBlock (by decide +kernel)
def block121 : List CallState := ((nextList 1 wires23).drop 18).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed121 : AllRejected 6 block121 := checkedBlock (by decide +kernel)
def block122 : List CallState := ((nextList 1 wires23).drop 26).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed122 : AllRejected 6 block122 := checkedBlock (by decide +kernel)
def block123 : List CallState := ((nextList 1 wires23).drop 38).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed123 : AllRejected 6 block123 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node23 : walk 7 1 wires23 = false := by
  have rest := (appendOk closed119 (appendOk closed120 (appendOk closed121 (appendOk closed122 (appendOk closed123 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires23) (by decide +kernel) (by decide +kernel) rest
def wires24 : List ℕ := [v27,v1,v2,v0,v3,v4,v5]
def block124 : List CallState := ((nextList 1 wires24).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed124 : AllRejected 6 block124 := checkedBlock (by decide +kernel)
def block125 : List CallState := ((nextList 1 wires24).drop 13).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed125 : AllRejected 6 block125 := checkedBlock (by decide +kernel)
def block126 : List CallState := ((nextList 1 wires24).drop 19).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed126 : AllRejected 6 block126 := checkedBlock (by decide +kernel)
def block127 : List CallState := ((nextList 1 wires24).drop 29).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed127 : AllRejected 6 block127 := checkedBlock (by decide +kernel)
def block128 : List CallState := ((nextList 1 wires24).drop 40).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed128 : AllRejected 6 block128 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node24 : walk 7 1 wires24 = false := by
  have rest := (appendOk closed124 (appendOk closed125 (appendOk closed126 (appendOk closed127 (appendOk closed128 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires24) (by decide +kernel) (by decide +kernel) rest
def wires25 : List ℕ := [v28,v1,v3,v0,v2,v4,v5]
def block129 : List CallState := ((nextList 1 wires25).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed129 : AllRejected 6 block129 := checkedBlock (by decide +kernel)
def block130 : List CallState := ((nextList 1 wires25).drop 9).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed130 : AllRejected 6 block130 := checkedBlock (by decide +kernel)
def block131 : List CallState := ((nextList 1 wires25).drop 17).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed131 : AllRejected 6 block131 := checkedBlock (by decide +kernel)
def block132 : List CallState := ((nextList 1 wires25).drop 23).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed132 : AllRejected 6 block132 := checkedBlock (by decide +kernel)
def block133 : List CallState := ((nextList 1 wires25).drop 28).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed133 : AllRejected 6 block133 := checkedBlock (by decide +kernel)
def block134 : List CallState := ((nextList 1 wires25).drop 33).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed134 : AllRejected 6 block134 := checkedBlock (by decide +kernel)
def block135 : List CallState := ((nextList 1 wires25).drop 41).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed135 : AllRejected 6 block135 := checkedBlock (by decide +kernel)
def block136 : List CallState := ((nextList 1 wires25).drop 46).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed136 : AllRejected 6 block136 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node25 : walk 7 1 wires25 = false := by
  have rest := (appendOk closed129 (appendOk closed130 (appendOk closed131 (appendOk closed132 (appendOk closed133 (appendOk closed134 (appendOk closed135 (appendOk closed136 (emptyOk 6)))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires25) (by decide +kernel) (by decide +kernel) rest
def wires26 : List ℕ := [v29,v1,v3,v0,v2,v4,v5]
def block137 : List CallState := ((nextList 1 wires26).drop 0).take 18
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed137 : AllRejected 6 block137 := checkedBlock (by decide +kernel)
def block138 : List CallState := ((nextList 1 wires26).drop 18).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed138 : AllRejected 6 block138 := checkedBlock (by decide +kernel)
def block139 : List CallState := ((nextList 1 wires26).drop 30).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed139 : AllRejected 6 block139 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node26 : walk 7 1 wires26 = false := by
  have rest := (appendOk closed137 (appendOk closed138 (appendOk closed139 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires26) (by decide +kernel) (by decide +kernel) rest
def wires27 : List ℕ := [v30,v1,v3,v0,v2,v4,v5]
def block140 : List CallState := ((nextList 1 wires27).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed140 : AllRejected 6 block140 := checkedBlock (by decide +kernel)
def block141 : List CallState := ((nextList 1 wires27).drop 14).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed141 : AllRejected 6 block141 := checkedBlock (by decide +kernel)
def block142 : List CallState := ((nextList 1 wires27).drop 24).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed142 : AllRejected 6 block142 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node27 : walk 7 1 wires27 = false := by
  have rest := (appendOk closed140 (appendOk closed141 (appendOk closed142 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires27) (by decide +kernel) (by decide +kernel) rest
def wires28 : List ℕ := [v31,v1,v3,v0,v2,v4,v5]
def block143 : List CallState := ((nextList 1 wires28).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed143 : AllRejected 6 block143 := checkedBlock (by decide +kernel)
def block144 : List CallState := ((nextList 1 wires28).drop 14).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed144 : AllRejected 6 block144 := checkedBlock (by decide +kernel)
def block145 : List CallState := ((nextList 1 wires28).drop 26).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed145 : AllRejected 6 block145 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node28 : walk 7 1 wires28 = false := by
  have rest := (appendOk closed143 (appendOk closed144 (appendOk closed145 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires28) (by decide +kernel) (by decide +kernel) rest
def wires29 : List ℕ := [v32,v1,v4,v0,v2,v3,v5]
def block146 : List CallState := ((nextList 1 wires29).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed146 : AllRejected 6 block146 := checkedBlock (by decide +kernel)
def block147 : List CallState := ((nextList 1 wires29).drop 10).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed147 : AllRejected 6 block147 := checkedBlock (by decide +kernel)
def block148 : List CallState := ((nextList 1 wires29).drop 16).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed148 : AllRejected 6 block148 := checkedBlock (by decide +kernel)
def block149 : List CallState := ((nextList 1 wires29).drop 23).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed149 : AllRejected 6 block149 := checkedBlock (by decide +kernel)
def block150 : List CallState := ((nextList 1 wires29).drop 30).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed150 : AllRejected 6 block150 := checkedBlock (by decide +kernel)
def block151 : List CallState := ((nextList 1 wires29).drop 36).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed151 : AllRejected 6 block151 := checkedBlock (by decide +kernel)
def block152 : List CallState := ((nextList 1 wires29).drop 43).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed152 : AllRejected 6 block152 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node29 : walk 7 1 wires29 = false := by
  have rest := (appendOk closed146 (appendOk closed147 (appendOk closed148 (appendOk closed149 (appendOk closed150 (appendOk closed151 (appendOk closed152 (emptyOk 6))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires29) (by decide +kernel) (by decide +kernel) rest
def wires30 : List ℕ := [v33,v1,v4,v0,v2,v3,v5]
def block153 : List CallState := ((nextList 1 wires30).drop 0).take 16
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed153 : AllRejected 6 block153 := checkedBlock (by decide +kernel)
def block154 : List CallState := ((nextList 1 wires30).drop 16).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed154 : AllRejected 6 block154 := checkedBlock (by decide +kernel)
def block155 : List CallState := ((nextList 1 wires30).drop 25).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed155 : AllRejected 6 block155 := checkedBlock (by decide +kernel)
def block156 : List CallState := ((nextList 1 wires30).drop 32).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed156 : AllRejected 6 block156 := checkedBlock (by decide +kernel)
def block157 : List CallState := ((nextList 1 wires30).drop 38).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed157 : AllRejected 6 block157 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node30 : walk 7 1 wires30 = false := by
  have rest := (appendOk closed153 (appendOk closed154 (appendOk closed155 (appendOk closed156 (appendOk closed157 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires30) (by decide +kernel) (by decide +kernel) rest
def wires31 : List ℕ := [v34,v1,v4,v0,v2,v3,v5]
def block158 : List CallState := ((nextList 1 wires31).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed158 : AllRejected 6 block158 := checkedBlock (by decide +kernel)
def block159 : List CallState := ((nextList 1 wires31).drop 13).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed159 : AllRejected 6 block159 := checkedBlock (by decide +kernel)
def block160 : List CallState := ((nextList 1 wires31).drop 23).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed160 : AllRejected 6 block160 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node31 : walk 7 1 wires31 = false := by
  have rest := (appendOk closed158 (appendOk closed159 (appendOk closed160 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires31) (by decide +kernel) (by decide +kernel) rest
def wires32 : List ℕ := [v35,v1,v4,v0,v2,v3,v5]
def block161 : List CallState := ((nextList 1 wires32).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed161 : AllRejected 6 block161 := checkedBlock (by decide +kernel)
def block162 : List CallState := ((nextList 1 wires32).drop 10).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed162 : AllRejected 6 block162 := checkedBlock (by decide +kernel)
def block163 : List CallState := ((nextList 1 wires32).drop 19).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed163 : AllRejected 6 block163 := checkedBlock (by decide +kernel)
def block164 : List CallState := ((nextList 1 wires32).drop 27).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed164 : AllRejected 6 block164 := checkedBlock (by decide +kernel)
def block165 : List CallState := ((nextList 1 wires32).drop 36).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed165 : AllRejected 6 block165 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node32 : walk 7 1 wires32 = false := by
  have rest := (appendOk closed161 (appendOk closed162 (appendOk closed163 (appendOk closed164 (appendOk closed165 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires32) (by decide +kernel) (by decide +kernel) rest
def wires33 : List ℕ := [v36,v1,v5,v0,v2,v3,v4]
def block166 : List CallState := ((nextList 1 wires33).drop 0).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed166 : AllRejected 6 block166 := checkedBlock (by decide +kernel)
def block167 : List CallState := ((nextList 1 wires33).drop 8).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed167 : AllRejected 6 block167 := checkedBlock (by decide +kernel)
def block168 : List CallState := ((nextList 1 wires33).drop 13).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed168 : AllRejected 6 block168 := checkedBlock (by decide +kernel)
def block169 : List CallState := ((nextList 1 wires33).drop 16).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed169 : AllRejected 6 block169 := checkedBlock (by decide +kernel)
def block170 : List CallState := ((nextList 1 wires33).drop 20).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed170 : AllRejected 6 block170 := checkedBlock (by decide +kernel)
def block171 : List CallState := ((nextList 1 wires33).drop 24).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed171 : AllRejected 6 block171 := checkedBlock (by decide +kernel)
def block172 : List CallState := ((nextList 1 wires33).drop 28).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed172 : AllRejected 6 block172 := checkedBlock (by decide +kernel)
def block173 : List CallState := ((nextList 1 wires33).drop 32).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed173 : AllRejected 6 block173 := checkedBlock (by decide +kernel)
def block174 : List CallState := ((nextList 1 wires33).drop 36).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed174 : AllRejected 6 block174 := checkedBlock (by decide +kernel)
def block175 : List CallState := ((nextList 1 wires33).drop 41).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed175 : AllRejected 6 block175 := checkedBlock (by decide +kernel)
def block176 : List CallState := ((nextList 1 wires33).drop 44).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed176 : AllRejected 6 block176 := checkedBlock (by decide +kernel)
def block177 : List CallState := ((nextList 1 wires33).drop 45).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed177 : AllRejected 6 block177 := checkedBlock (by decide +kernel)
def block178 : List CallState := ((nextList 1 wires33).drop 48).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed178 : AllRejected 6 block178 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node33 : walk 7 1 wires33 = false := by
  have rest := (appendOk closed166 (appendOk closed167 (appendOk closed168 (appendOk closed169 (appendOk closed170 (appendOk closed171 (appendOk closed172 (appendOk closed173 (appendOk closed174 (appendOk closed175 (appendOk closed176 (appendOk closed177 (appendOk closed178 (emptyOk 6))))))))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires33) (by decide +kernel) (by decide +kernel) rest
def wires34 : List ℕ := [v37,v1,v5,v0,v2,v3,v4]
def block179 : List CallState := ((nextList 1 wires34).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed179 : AllRejected 6 block179 := checkedBlock (by decide +kernel)
def block180 : List CallState := ((nextList 1 wires34).drop 14).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed180 : AllRejected 6 block180 := checkedBlock (by decide +kernel)
def block181 : List CallState := ((nextList 1 wires34).drop 24).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed181 : AllRejected 6 block181 := checkedBlock (by decide +kernel)
def block182 : List CallState := ((nextList 1 wires34).drop 38).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed182 : AllRejected 6 block182 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node34 : walk 7 1 wires34 = false := by
  have rest := (appendOk closed179 (appendOk closed180 (appendOk closed181 (appendOk closed182 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires34) (by decide +kernel) (by decide +kernel) rest
def wires35 : List ℕ := [v38,v1,v5,v0,v2,v3,v4]
def block183 : List CallState := ((nextList 1 wires35).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed183 : AllRejected 6 block183 := checkedBlock (by decide +kernel)
def block184 : List CallState := ((nextList 1 wires35).drop 11).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed184 : AllRejected 6 block184 := checkedBlock (by decide +kernel)
def block185 : List CallState := ((nextList 1 wires35).drop 21).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed185 : AllRejected 6 block185 := checkedBlock (by decide +kernel)
def block186 : List CallState := ((nextList 1 wires35).drop 32).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed186 : AllRejected 6 block186 := checkedBlock (by decide +kernel)
def block187 : List CallState := ((nextList 1 wires35).drop 37).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed187 : AllRejected 6 block187 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node35 : walk 7 1 wires35 = false := by
  have rest := (appendOk closed183 (appendOk closed184 (appendOk closed185 (appendOk closed186 (appendOk closed187 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires35) (by decide +kernel) (by decide +kernel) rest
def wires36 : List ℕ := [v39,v1,v5,v0,v2,v3,v4]
def block188 : List CallState := ((nextList 1 wires36).drop 0).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed188 : AllRejected 6 block188 := checkedBlock (by decide +kernel)
def block189 : List CallState := ((nextList 1 wires36).drop 8).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed189 : AllRejected 6 block189 := checkedBlock (by decide +kernel)
def block190 : List CallState := ((nextList 1 wires36).drop 19).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed190 : AllRejected 6 block190 := checkedBlock (by decide +kernel)
def block191 : List CallState := ((nextList 1 wires36).drop 30).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed191 : AllRejected 6 block191 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node36 : walk 7 1 wires36 = false := by
  have rest := (appendOk closed188 (appendOk closed189 (appendOk closed190 (appendOk closed191 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires36) (by decide +kernel) (by decide +kernel) rest
def wires37 : List ℕ := [v40,v2,v3,v0,v1,v4,v5]
def block192 : List CallState := ((nextList 1 wires37).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed192 : AllRejected 6 block192 := checkedBlock (by decide +kernel)
def block193 : List CallState := ((nextList 1 wires37).drop 14).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed193 : AllRejected 6 block193 := checkedBlock (by decide +kernel)
def block194 : List CallState := ((nextList 1 wires37).drop 25).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed194 : AllRejected 6 block194 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node37 : walk 7 1 wires37 = false := by
  have rest := (appendOk closed192 (appendOk closed193 (appendOk closed194 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires37) (by decide +kernel) (by decide +kernel) rest
def wires38 : List ℕ := [v41,v2,v3,v0,v1,v4,v5]
def block195 : List CallState := ((nextList 1 wires38).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed195 : AllRejected 6 block195 := checkedBlock (by decide +kernel)
def block196 : List CallState := ((nextList 1 wires38).drop 14).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed196 : AllRejected 6 block196 := checkedBlock (by decide +kernel)
def block197 : List CallState := ((nextList 1 wires38).drop 26).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed197 : AllRejected 6 block197 := checkedBlock (by decide +kernel)
def block198 : List CallState := ((nextList 1 wires38).drop 37).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed198 : AllRejected 6 block198 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node38 : walk 7 1 wires38 = false := by
  have rest := (appendOk closed195 (appendOk closed196 (appendOk closed197 (appendOk closed198 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires38) (by decide +kernel) (by decide +kernel) rest
def wires39 : List ℕ := [v42,v2,v3,v0,v1,v4,v5]
def block199 : List CallState := ((nextList 1 wires39).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed199 : AllRejected 6 block199 := checkedBlock (by decide +kernel)
def block200 : List CallState := ((nextList 1 wires39).drop 14).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed200 : AllRejected 6 block200 := checkedBlock (by decide +kernel)
def block201 : List CallState := ((nextList 1 wires39).drop 22).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed201 : AllRejected 6 block201 := checkedBlock (by decide +kernel)
def block202 : List CallState := ((nextList 1 wires39).drop 34).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed202 : AllRejected 6 block202 := checkedBlock (by decide +kernel)
def block203 : List CallState := ((nextList 1 wires39).drop 41).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed203 : AllRejected 6 block203 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node39 : walk 7 1 wires39 = false := by
  have rest := (appendOk closed199 (appendOk closed200 (appendOk closed201 (appendOk closed202 (appendOk closed203 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires39) (by decide +kernel) (by decide +kernel) rest
def wires40 : List ℕ := [v43,v2,v3,v0,v1,v4,v5]
def block204 : List CallState := ((nextList 1 wires40).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed204 : AllRejected 6 block204 := checkedBlock (by decide +kernel)
def block205 : List CallState := ((nextList 1 wires40).drop 13).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed205 : AllRejected 6 block205 := checkedBlock (by decide +kernel)
def block206 : List CallState := ((nextList 1 wires40).drop 21).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed206 : AllRejected 6 block206 := checkedBlock (by decide +kernel)
def block207 : List CallState := ((nextList 1 wires40).drop 32).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed207 : AllRejected 6 block207 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node40 : walk 7 1 wires40 = false := by
  have rest := (appendOk closed204 (appendOk closed205 (appendOk closed206 (appendOk closed207 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires40) (by decide +kernel) (by decide +kernel) rest
def wires41 : List ℕ := [v44,v2,v4,v0,v1,v3,v5]
def block208 : List CallState := ((nextList 1 wires41).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed208 : AllRejected 6 block208 := checkedBlock (by decide +kernel)
def block209 : List CallState := ((nextList 1 wires41).drop 7).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed209 : AllRejected 6 block209 := checkedBlock (by decide +kernel)
def block210 : List CallState := ((nextList 1 wires41).drop 10).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed210 : AllRejected 6 block210 := checkedBlock (by decide +kernel)
def block211 : List CallState := ((nextList 1 wires41).drop 15).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed211 : AllRejected 6 block211 := checkedBlock (by decide +kernel)
def block212 : List CallState := ((nextList 1 wires41).drop 18).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed212 : AllRejected 6 block212 := checkedBlock (by decide +kernel)
def block213 : List CallState := ((nextList 1 wires41).drop 24).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed213 : AllRejected 6 block213 := checkedBlock (by decide +kernel)
def block214 : List CallState := ((nextList 1 wires41).drop 29).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed214 : AllRejected 6 block214 := checkedBlock (by decide +kernel)
def block215 : List CallState := ((nextList 1 wires41).drop 32).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed215 : AllRejected 6 block215 := checkedBlock (by decide +kernel)
def block216 : List CallState := ((nextList 1 wires41).drop 36).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed216 : AllRejected 6 block216 := checkedBlock (by decide +kernel)
def block217 : List CallState := ((nextList 1 wires41).drop 41).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed217 : AllRejected 6 block217 := checkedBlock (by decide +kernel)
def block218 : List CallState := ((nextList 1 wires41).drop 44).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed218 : AllRejected 6 block218 := checkedBlock (by decide +kernel)
def block219 : List CallState := ((nextList 1 wires41).drop 45).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed219 : AllRejected 6 block219 := checkedBlock (by decide +kernel)
def block220 : List CallState := ((nextList 1 wires41).drop 48).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed220 : AllRejected 6 block220 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node41 : walk 7 1 wires41 = false := by
  have rest := (appendOk closed208 (appendOk closed209 (appendOk closed210 (appendOk closed211 (appendOk closed212 (appendOk closed213 (appendOk closed214 (appendOk closed215 (appendOk closed216 (appendOk closed217 (appendOk closed218 (appendOk closed219 (appendOk closed220 (emptyOk 6))))))))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires41) (by decide +kernel) (by decide +kernel) rest
def wires42 : List ℕ := [v45,v2,v4,v0,v1,v3,v5]
def block221 : List CallState := ((nextList 1 wires42).drop 0).take 15
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed221 : AllRejected 6 block221 := checkedBlock (by decide +kernel)
def block222 : List CallState := ((nextList 1 wires42).drop 15).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed222 : AllRejected 6 block222 := checkedBlock (by decide +kernel)
def block223 : List CallState := ((nextList 1 wires42).drop 25).take 15
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed223 : AllRejected 6 block223 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node42 : walk 7 1 wires42 = false := by
  have rest := (appendOk closed221 (appendOk closed222 (appendOk closed223 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires42) (by decide +kernel) (by decide +kernel) rest
def wires43 : List ℕ := [v46,v2,v4,v0,v1,v3,v5]
def block224 : List CallState := ((nextList 1 wires43).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed224 : AllRejected 6 block224 := checkedBlock (by decide +kernel)
def block225 : List CallState := ((nextList 1 wires43).drop 9).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed225 : AllRejected 6 block225 := checkedBlock (by decide +kernel)
def block226 : List CallState := ((nextList 1 wires43).drop 21).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed226 : AllRejected 6 block226 := checkedBlock (by decide +kernel)
def block227 : List CallState := ((nextList 1 wires43).drop 32).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed227 : AllRejected 6 block227 := checkedBlock (by decide +kernel)
def block228 : List CallState := ((nextList 1 wires43).drop 37).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed228 : AllRejected 6 block228 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node43 : walk 7 1 wires43 = false := by
  have rest := (appendOk closed224 (appendOk closed225 (appendOk closed226 (appendOk closed227 (appendOk closed228 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires43) (by decide +kernel) (by decide +kernel) rest
def wires44 : List ℕ := [v47,v2,v4,v0,v1,v3,v5]
def block229 : List CallState := ((nextList 1 wires44).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed229 : AllRejected 6 block229 := checkedBlock (by decide +kernel)
def block230 : List CallState := ((nextList 1 wires44).drop 10).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed230 : AllRejected 6 block230 := checkedBlock (by decide +kernel)
def block231 : List CallState := ((nextList 1 wires44).drop 19).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed231 : AllRejected 6 block231 := checkedBlock (by decide +kernel)
def block232 : List CallState := ((nextList 1 wires44).drop 29).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed232 : AllRejected 6 block232 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node44 : walk 7 1 wires44 = false := by
  have rest := (appendOk closed229 (appendOk closed230 (appendOk closed231 (appendOk closed232 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires44) (by decide +kernel) (by decide +kernel) rest
def wires45 : List ℕ := [v48,v2,v5,v0,v1,v3,v4]
def block233 : List CallState := ((nextList 1 wires45).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed233 : AllRejected 6 block233 := checkedBlock (by decide +kernel)
def block234 : List CallState := ((nextList 1 wires45).drop 10).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed234 : AllRejected 6 block234 := checkedBlock (by decide +kernel)
def block235 : List CallState := ((nextList 1 wires45).drop 16).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed235 : AllRejected 6 block235 := checkedBlock (by decide +kernel)
def block236 : List CallState := ((nextList 1 wires45).drop 23).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed236 : AllRejected 6 block236 := checkedBlock (by decide +kernel)
def block237 : List CallState := ((nextList 1 wires45).drop 30).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed237 : AllRejected 6 block237 := checkedBlock (by decide +kernel)
def block238 : List CallState := ((nextList 1 wires45).drop 36).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed238 : AllRejected 6 block238 := checkedBlock (by decide +kernel)
def block239 : List CallState := ((nextList 1 wires45).drop 43).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed239 : AllRejected 6 block239 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node45 : walk 7 1 wires45 = false := by
  have rest := (appendOk closed233 (appendOk closed234 (appendOk closed235 (appendOk closed236 (appendOk closed237 (appendOk closed238 (appendOk closed239 (emptyOk 6))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires45) (by decide +kernel) (by decide +kernel) rest
def wires46 : List ℕ := [v49,v2,v5,v0,v1,v3,v4]
def block240 : List CallState := ((nextList 1 wires46).drop 0).take 15
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed240 : AllRejected 6 block240 := checkedBlock (by decide +kernel)
def block241 : List CallState := ((nextList 1 wires46).drop 15).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed241 : AllRejected 6 block241 := checkedBlock (by decide +kernel)
def block242 : List CallState := ((nextList 1 wires46).drop 25).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed242 : AllRejected 6 block242 := checkedBlock (by decide +kernel)
def block243 : List CallState := ((nextList 1 wires46).drop 32).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed243 : AllRejected 6 block243 := checkedBlock (by decide +kernel)
def block244 : List CallState := ((nextList 1 wires46).drop 38).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed244 : AllRejected 6 block244 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node46 : walk 7 1 wires46 = false := by
  have rest := (appendOk closed240 (appendOk closed241 (appendOk closed242 (appendOk closed243 (appendOk closed244 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires46) (by decide +kernel) (by decide +kernel) rest
def wires47 : List ℕ := [v50,v2,v5,v0,v1,v3,v4]
def block245 : List CallState := ((nextList 1 wires47).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed245 : AllRejected 6 block245 := checkedBlock (by decide +kernel)
def block246 : List CallState := ((nextList 1 wires47).drop 13).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed246 : AllRejected 6 block246 := checkedBlock (by decide +kernel)
def block247 : List CallState := ((nextList 1 wires47).drop 24).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed247 : AllRejected 6 block247 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node47 : walk 7 1 wires47 = false := by
  have rest := (appendOk closed245 (appendOk closed246 (appendOk closed247 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires47) (by decide +kernel) (by decide +kernel) rest
def wires48 : List ℕ := [v51,v2,v5,v0,v1,v3,v4]
def block248 : List CallState := ((nextList 1 wires48).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed248 : AllRejected 6 block248 := checkedBlock (by decide +kernel)
def block249 : List CallState := ((nextList 1 wires48).drop 11).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed249 : AllRejected 6 block249 := checkedBlock (by decide +kernel)
def block250 : List CallState := ((nextList 1 wires48).drop 18).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed250 : AllRejected 6 block250 := checkedBlock (by decide +kernel)
def block251 : List CallState := ((nextList 1 wires48).drop 27).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed251 : AllRejected 6 block251 := checkedBlock (by decide +kernel)
def block252 : List CallState := ((nextList 1 wires48).drop 36).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed252 : AllRejected 6 block252 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node48 : walk 7 1 wires48 = false := by
  have rest := (appendOk closed248 (appendOk closed249 (appendOk closed250 (appendOk closed251 (appendOk closed252 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires48) (by decide +kernel) (by decide +kernel) rest
def wires49 : List ℕ := [v52,v3,v4,v0,v1,v2,v5]
def block253 : List CallState := ((nextList 1 wires49).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed253 : AllRejected 6 block253 := checkedBlock (by decide +kernel)
def block254 : List CallState := ((nextList 1 wires49).drop 11).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed254 : AllRejected 6 block254 := checkedBlock (by decide +kernel)
def block255 : List CallState := ((nextList 1 wires49).drop 22).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed255 : AllRejected 6 block255 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node49 : walk 7 1 wires49 = false := by
  have rest := (appendOk closed253 (appendOk closed254 (appendOk closed255 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires49) (by decide +kernel) (by decide +kernel) rest
def wires50 : List ℕ := [v53,v4,v0,v1,v2,v5]
def block256 : List CallState := ((nextList 2 wires50).drop 0).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed256 : AllRejected 6 block256 := checkedBlock (by decide +kernel)
def block257 : List CallState := ((nextList 2 wires50).drop 4).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed257 : AllRejected 6 block257 := checkedBlock (by decide +kernel)
def block258 : List CallState := ((nextList 2 wires50).drop 11).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed258 : AllRejected 6 block258 := checkedBlock (by decide +kernel)
def block259 : List CallState := ((nextList 2 wires50).drop 17).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed259 : AllRejected 6 block259 := checkedBlock (by decide +kernel)
def block260 : List CallState := ((nextList 2 wires50).drop 21).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed260 : AllRejected 6 block260 := checkedBlock (by decide +kernel)
def block261 : List CallState := ((nextList 2 wires50).drop 25).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed261 : AllRejected 6 block261 := checkedBlock (by decide +kernel)
def block262 : List CallState := ((nextList 2 wires50).drop 29).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed262 : AllRejected 6 block262 := checkedBlock (by decide +kernel)
def block263 : List CallState := ((nextList 2 wires50).drop 32).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed263 : AllRejected 6 block263 := checkedBlock (by decide +kernel)
def block264 : List CallState := ((nextList 2 wires50).drop 33).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed264 : AllRejected 6 block264 := checkedBlock (by decide +kernel)
def block265 : List CallState := ((nextList 2 wires50).drop 36).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed265 : AllRejected 6 block265 := checkedBlock (by decide +kernel)
def block266 : List CallState := ((nextList 2 wires50).drop 39).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed266 : AllRejected 6 block266 := checkedBlock (by decide +kernel)
def block267 : List CallState := ((nextList 2 wires50).drop 42).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed267 : AllRejected 6 block267 := checkedBlock (by decide +kernel)
def block268 : List CallState := ((nextList 2 wires50).drop 49).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed268 : AllRejected 6 block268 := checkedBlock (by decide +kernel)
def block269 : List CallState := ((nextList 2 wires50).drop 53).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed269 : AllRejected 6 block269 := checkedBlock (by decide +kernel)
def block270 : List CallState := ((nextList 2 wires50).drop 55).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed270 : AllRejected 6 block270 := checkedBlock (by decide +kernel)
def block271 : List CallState := ((nextList 2 wires50).drop 59).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed271 : AllRejected 6 block271 := checkedBlock (by decide +kernel)
def block272 : List CallState := ((nextList 2 wires50).drop 64).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed272 : AllRejected 6 block272 := checkedBlock (by decide +kernel)
def block273 : List CallState := ((nextList 2 wires50).drop 69).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed273 : AllRejected 6 block273 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node50 : walk 7 2 wires50 = false := by
  have rest := (appendOk closed256 (appendOk closed257 (appendOk closed258 (appendOk closed259 (appendOk closed260 (appendOk closed261 (appendOk closed262 (appendOk closed263 (appendOk closed264 (appendOk closed265 (appendOk closed266 (appendOk closed267 (appendOk closed268 (appendOk closed269 (appendOk closed270 (appendOk closed271 (appendOk closed272 (appendOk closed273 (emptyOk 6)))))))))))))))))))
  exact split_walk (k := 6) (e := 2) (ws := wires50) (by decide +kernel) (by decide +kernel) rest
def wires51 : List ℕ := [v53,v3,v4,v0,v1,v2,v5]
def block274 : List CallState := ((nextList 1 wires51).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed274 : AllRejected 6 block274 := checkedBlock (by decide +kernel)
def block275 : List CallState := ((nextList 1 wires51).drop 13).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed275 : AllRejected 6 block275 := checkedBlock (by decide +kernel)
def block276 : List CallState := ((nextList 1 wires51).drop 24).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed276 : AllRejected 6 block276 := checkedBlock (by decide +kernel)
def block277 : List CallState := ((nextList 1 wires51).drop 30).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed277 : AllRejected 6 block277 := checkedBlock (by decide +kernel)
def block278 : List CallState := ((nextList 1 wires51).drop 40).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed278 : AllRejected 6 block278 := checkedBlock (by decide +kernel)
def block279 : List CallState := ((nextList 1 wires51).drop 48).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed279 : AllRejected 6 block279 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node51 : walk 7 1 wires51 = false := by
  have rest := (appendOk closed274 (appendOk closed275 (appendOk closed276 (appendOk closed277 (appendOk closed278 (appendOk closed279 (emptyOk 6)))))))
  exact split_walk (k := 6) (e := 1) (ws := wires51) (by decide +kernel) (by decide +kernel) rest
def wires52 : List ℕ := [v54,v4,v0,v1,v2,v5]
def block280 : List CallState := ((nextList 2 wires52).drop 0).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed280 : AllRejected 6 block280 := checkedBlock (by decide +kernel)
def block281 : List CallState := ((nextList 2 wires52).drop 4).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed281 : AllRejected 6 block281 := checkedBlock (by decide +kernel)
def block282 : List CallState := ((nextList 2 wires52).drop 12).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed282 : AllRejected 6 block282 := checkedBlock (by decide +kernel)
def block283 : List CallState := ((nextList 2 wires52).drop 17).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed283 : AllRejected 6 block283 := checkedBlock (by decide +kernel)
def block284 : List CallState := ((nextList 2 wires52).drop 24).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed284 : AllRejected 6 block284 := checkedBlock (by decide +kernel)
def block285 : List CallState := ((nextList 2 wires52).drop 34).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed285 : AllRejected 6 block285 := checkedBlock (by decide +kernel)
def block286 : List CallState := ((nextList 2 wires52).drop 46).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed286 : AllRejected 6 block286 := checkedBlock (by decide +kernel)
def block287 : List CallState := ((nextList 2 wires52).drop 52).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed287 : AllRejected 6 block287 := checkedBlock (by decide +kernel)
def block288 : List CallState := ((nextList 2 wires52).drop 63).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed288 : AllRejected 6 block288 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node52 : walk 7 2 wires52 = false := by
  have rest := (appendOk closed280 (appendOk closed281 (appendOk closed282 (appendOk closed283 (appendOk closed284 (appendOk closed285 (appendOk closed286 (appendOk closed287 (appendOk closed288 (emptyOk 6))))))))))
  exact split_walk (k := 6) (e := 2) (ws := wires52) (by decide +kernel) (by decide +kernel) rest
def wires53 : List ℕ := [v54,v3,v4,v0,v1,v2,v5]
def block289 : List CallState := ((nextList 1 wires53).drop 0).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed289 : AllRejected 6 block289 := checkedBlock (by decide +kernel)
def block290 : List CallState := ((nextList 1 wires53).drop 12).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed290 : AllRejected 6 block290 := checkedBlock (by decide +kernel)
def block291 : List CallState := ((nextList 1 wires53).drop 20).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed291 : AllRejected 6 block291 := checkedBlock (by decide +kernel)
def block292 : List CallState := ((nextList 1 wires53).drop 25).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed292 : AllRejected 6 block292 := checkedBlock (by decide +kernel)
def block293 : List CallState := ((nextList 1 wires53).drop 31).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed293 : AllRejected 6 block293 := checkedBlock (by decide +kernel)
def block294 : List CallState := ((nextList 1 wires53).drop 40).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed294 : AllRejected 6 block294 := checkedBlock (by decide +kernel)
def block295 : List CallState := ((nextList 1 wires53).drop 49).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed295 : AllRejected 6 block295 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node53 : walk 7 1 wires53 = false := by
  have rest := (appendOk closed289 (appendOk closed290 (appendOk closed291 (appendOk closed292 (appendOk closed293 (appendOk closed294 (appendOk closed295 (emptyOk 6))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires53) (by decide +kernel) (by decide +kernel) rest
def wires54 : List ℕ := [v55,v3,v4,v0,v1,v2,v5]
def block296 : List CallState := ((nextList 1 wires54).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed296 : AllRejected 6 block296 := checkedBlock (by decide +kernel)
def block297 : List CallState := ((nextList 1 wires54).drop 11).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed297 : AllRejected 6 block297 := checkedBlock (by decide +kernel)
def block298 : List CallState := ((nextList 1 wires54).drop 22).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed298 : AllRejected 6 block298 := checkedBlock (by decide +kernel)
def block299 : List CallState := ((nextList 1 wires54).drop 33).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed299 : AllRejected 6 block299 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node54 : walk 7 1 wires54 = false := by
  have rest := (appendOk closed296 (appendOk closed297 (appendOk closed298 (appendOk closed299 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires54) (by decide +kernel) (by decide +kernel) rest
def wires55 : List ℕ := [v56,v3,v5,v0,v1,v2,v4]
def block300 : List CallState := ((nextList 1 wires55).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed300 : AllRejected 6 block300 := checkedBlock (by decide +kernel)
def block301 : List CallState := ((nextList 1 wires55).drop 10).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed301 : AllRejected 6 block301 := checkedBlock (by decide +kernel)
def block302 : List CallState := ((nextList 1 wires55).drop 16).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed302 : AllRejected 6 block302 := checkedBlock (by decide +kernel)
def block303 : List CallState := ((nextList 1 wires55).drop 23).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed303 : AllRejected 6 block303 := checkedBlock (by decide +kernel)
def block304 : List CallState := ((nextList 1 wires55).drop 30).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed304 : AllRejected 6 block304 := checkedBlock (by decide +kernel)
def block305 : List CallState := ((nextList 1 wires55).drop 36).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed305 : AllRejected 6 block305 := checkedBlock (by decide +kernel)
def block306 : List CallState := ((nextList 1 wires55).drop 43).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed306 : AllRejected 6 block306 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node55 : walk 7 1 wires55 = false := by
  have rest := (appendOk closed300 (appendOk closed301 (appendOk closed302 (appendOk closed303 (appendOk closed304 (appendOk closed305 (appendOk closed306 (emptyOk 6))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires55) (by decide +kernel) (by decide +kernel) rest
def wires56 : List ℕ := [v57,v3,v5,v0,v1,v2,v4]
def block307 : List CallState := ((nextList 1 wires56).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed307 : AllRejected 6 block307 := checkedBlock (by decide +kernel)
def block308 : List CallState := ((nextList 1 wires56).drop 13).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed308 : AllRejected 6 block308 := checkedBlock (by decide +kernel)
def block309 : List CallState := ((nextList 1 wires56).drop 25).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed309 : AllRejected 6 block309 := checkedBlock (by decide +kernel)
def block310 : List CallState := ((nextList 1 wires56).drop 32).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed310 : AllRejected 6 block310 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node56 : walk 7 1 wires56 = false := by
  have rest := (appendOk closed307 (appendOk closed308 (appendOk closed309 (appendOk closed310 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires56) (by decide +kernel) (by decide +kernel) rest
def wires57 : List ℕ := [v58,v3,v5,v0,v1,v2,v4]
def block311 : List CallState := ((nextList 1 wires57).drop 0).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed311 : AllRejected 6 block311 := checkedBlock (by decide +kernel)
def block312 : List CallState := ((nextList 1 wires57).drop 12).take 15
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed312 : AllRejected 6 block312 := checkedBlock (by decide +kernel)
def block313 : List CallState := ((nextList 1 wires57).drop 27).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed313 : AllRejected 6 block313 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node57 : walk 7 1 wires57 = false := by
  have rest := (appendOk closed311 (appendOk closed312 (appendOk closed313 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires57) (by decide +kernel) (by decide +kernel) rest
def wires58 : List ℕ := [v59,v3,v5,v0,v1,v2,v4]
def block314 : List CallState := ((nextList 1 wires58).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed314 : AllRejected 6 block314 := checkedBlock (by decide +kernel)
def block315 : List CallState := ((nextList 1 wires58).drop 11).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed315 : AllRejected 6 block315 := checkedBlock (by decide +kernel)
def block316 : List CallState := ((nextList 1 wires58).drop 18).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed316 : AllRejected 6 block316 := checkedBlock (by decide +kernel)
def block317 : List CallState := ((nextList 1 wires58).drop 27).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed317 : AllRejected 6 block317 := checkedBlock (by decide +kernel)
def block318 : List CallState := ((nextList 1 wires58).drop 35).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed318 : AllRejected 6 block318 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node58 : walk 7 1 wires58 = false := by
  have rest := (appendOk closed314 (appendOk closed315 (appendOk closed316 (appendOk closed317 (appendOk closed318 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires58) (by decide +kernel) (by decide +kernel) rest
def wires59 : List ℕ := [v60,v4,v5,v0,v1,v2,v3]
def block319 : List CallState := ((nextList 1 wires59).drop 0).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed319 : AllRejected 6 block319 := checkedBlock (by decide +kernel)
def block320 : List CallState := ((nextList 1 wires59).drop 8).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed320 : AllRejected 6 block320 := checkedBlock (by decide +kernel)
def block321 : List CallState := ((nextList 1 wires59).drop 15).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed321 : AllRejected 6 block321 := checkedBlock (by decide +kernel)
def block322 : List CallState := ((nextList 1 wires59).drop 22).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed322 : AllRejected 6 block322 := checkedBlock (by decide +kernel)
def block323 : List CallState := ((nextList 1 wires59).drop 28).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed323 : AllRejected 6 block323 := checkedBlock (by decide +kernel)
def block324 : List CallState := ((nextList 1 wires59).drop 35).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed324 : AllRejected 6 block324 := checkedBlock (by decide +kernel)
def block325 : List CallState := ((nextList 1 wires59).drop 43).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed325 : AllRejected 6 block325 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node59 : walk 7 1 wires59 = false := by
  have rest := (appendOk closed319 (appendOk closed320 (appendOk closed321 (appendOk closed322 (appendOk closed323 (appendOk closed324 (appendOk closed325 (emptyOk 6))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires59) (by decide +kernel) (by decide +kernel) rest
def wires60 : List ℕ := [v61,v4,v5,v0,v1,v2,v3]
def block326 : List CallState := ((nextList 1 wires60).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed326 : AllRejected 6 block326 := checkedBlock (by decide +kernel)
def block327 : List CallState := ((nextList 1 wires60).drop 10).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed327 : AllRejected 6 block327 := checkedBlock (by decide +kernel)
def block328 : List CallState := ((nextList 1 wires60).drop 19).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed328 : AllRejected 6 block328 := checkedBlock (by decide +kernel)
def block329 : List CallState := ((nextList 1 wires60).drop 29).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed329 : AllRejected 6 block329 := checkedBlock (by decide +kernel)
def block330 : List CallState := ((nextList 1 wires60).drop 34).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed330 : AllRejected 6 block330 := checkedBlock (by decide +kernel)
def block331 : List CallState := ((nextList 1 wires60).drop 39).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed331 : AllRejected 6 block331 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node60 : walk 7 1 wires60 = false := by
  have rest := (appendOk closed326 (appendOk closed327 (appendOk closed328 (appendOk closed329 (appendOk closed330 (appendOk closed331 (emptyOk 6)))))))
  exact split_walk (k := 6) (e := 1) (ws := wires60) (by decide +kernel) (by decide +kernel) rest
def wires61 : List ℕ := [v62,v4,v5,v0,v1,v2,v3]
def block332 : List CallState := ((nextList 1 wires61).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed332 : AllRejected 6 block332 := checkedBlock (by decide +kernel)
def block333 : List CallState := ((nextList 1 wires61).drop 10).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed333 : AllRejected 6 block333 := checkedBlock (by decide +kernel)
def block334 : List CallState := ((nextList 1 wires61).drop 19).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed334 : AllRejected 6 block334 := checkedBlock (by decide +kernel)
def block335 : List CallState := ((nextList 1 wires61).drop 29).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed335 : AllRejected 6 block335 := checkedBlock (by decide +kernel)
def block336 : List CallState := ((nextList 1 wires61).drop 39).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed336 : AllRejected 6 block336 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node61 : walk 7 1 wires61 = false := by
  have rest := (appendOk closed332 (appendOk closed333 (appendOk closed334 (appendOk closed335 (appendOk closed336 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires61) (by decide +kernel) (by decide +kernel) rest
def wires62 : List ℕ := [v63,v4,v5,v0,v1,v2,v3]
def block337 : List CallState := ((nextList 1 wires62).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed337 : AllRejected 6 block337 := checkedBlock (by decide +kernel)
def block338 : List CallState := ((nextList 1 wires62).drop 11).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed338 : AllRejected 6 block338 := checkedBlock (by decide +kernel)
def block339 : List CallState := ((nextList 1 wires62).drop 18).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed339 : AllRejected 6 block339 := checkedBlock (by decide +kernel)
def block340 : List CallState := ((nextList 1 wires62).drop 29).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed340 : AllRejected 6 block340 := checkedBlock (by decide +kernel)
def block341 : List CallState := ((nextList 1 wires62).drop 38).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed341 : AllRejected 6 block341 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node62 : walk 7 1 wires62 = false := by
  have rest := (appendOk closed337 (appendOk closed338 (appendOk closed339 (appendOk closed340 (appendOk closed341 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires62) (by decide +kernel) (by decide +kernel) rest
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node0 : walk 8 3 wires0 = false := by
  have rest := (consOk node1 (consOk node2 (consOk node3 (consOk node4 (consOk node5 (consOk node6 (consOk node7 (consOk node8 (consOk node9 (appendOk closed40 (consOk node10 (consOk node11 (consOk node12 (consOk node13 (consOk node14 (consOk node15 (consOk node16 (consOk node17 (consOk node18 (consOk node19 (consOk node20 (consOk node21 (appendOk closed113 (consOk node22 (consOk node23 (consOk node24 (consOk node25 (consOk node26 (consOk node27 (consOk node28 (consOk node29 (consOk node30 (consOk node31 (consOk node32 (consOk node33 (consOk node34 (consOk node35 (consOk node36 (consOk node37 (consOk node38 (consOk node39 (consOk node40 (consOk node41 (consOk node42 (consOk node43 (consOk node44 (consOk node45 (consOk node46 (consOk node47 (consOk node48 (consOk node49 (consOk node50 (consOk node51 (consOk node52 (consOk node53 (consOk node54 (consOk node55 (consOk node56 (consOk node57 (consOk node58 (consOk node59 (consOk node60 (consOk node61 (consOk node62 (emptyOk 7)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  exact split_walk (k := 7) (e := 3) (ws := wires0) (by decide +kernel) (by decide +kernel) rest
end PEqualNP.Outside.L_meta_10556_aux.NatCheck.Delete0

namespace PEqualNP.Outside.L_meta_10556_aux.NatCheck.Delete6
def v0 : ℕ := 0xcd0cf55528a4ca2c02ad7f896258962592ffc484882d055ab76efc447c7c4847ff000fff00000003f0001c0000000000003fc000001f03fab36ef8003c3c0007
def v1 : ℕ := 0x57555aaa51491500b596bf92a4a92a4affcac94914425aacdbbb688887fc923800ffffff000000fc00000380000000007fc000000000fffc9bbb680003fc0038
def v2 : ℕ := 0xabaaa0cf8a324055495be7a4c9324dffa541521221a1a41f1dcfbd13cbc521c100fff00000003f000003e380000001ff8000000003e0fc0508810003c3c001c0
def v3 : ℕ := 0x32333333144021821e7ffcc711c7fe930995a0604652082fe1f3ca3ffc8a0608ff000000001fc000007ffc000007fe00000000007fff00036040803ffc000600
def v4 : ℕ := 0x3cc3cc3ce00386186ffcc9781ffc711c4e260383b88430cffe03f3fd111038920000000007e000000ffc00001ff800000000003ffc000000440003fc00003800
def v5 : ℕ := 0xc0fc0fc0079c38e38fe3127ffe0781e070383c3c4318c30ffffc03e22223c52400000000f80000000f80007fe00000000000003f80000000040003c00003c000
def v6 : ℕ := 0xdf5dffff79eddf2cb7bfff9be6f9be6fffffcdcd9c6f5ffefffffcccfffcda7fffffffff000000fff0001f80000000007fffc000001ffffebbfff8003ffc003f
def v7 : ℕ := 0x8808a55528a4ca2c022940094250942500350484882d05522444944478004847ff00000000000003f0001c0000000000003fc000001f0002204490003c000007
def v8 : ℕ := 0x12510aaa51491500b512801284a1284a6d00094914425aa4489100888380923800fff000000000fc00000380000000007fc000000000fc040891000003c00038
def v9 : ℕ := 0x8908a045082040040009678040100425804140000021041a154ebc00484400410000000000000000000000000000000000000000000000000000000000000000
def v10 : ℕ := 0xefaef5dfaab6ca7d4bffffadeb7adfffb7ffd696a9ada55fbfeffd57fffd69c7ffffffff00003f03f003ff80000001ff803fc00003ffffffbbeff803fffc01c7
def v11 : ℕ := 0x4404551020848a2802a418092248920012be8484880c0140a220404434384806ff000fff00000003f0001c0000000000003fc000001f03fab36ef8003c3c0007
def v12 : ℕ := 0x22a2008a8212005149528024892249da250012122180a005088101138381218000fff00000003f000003e380000001ff8000000003e0fc0508810003c3c001c0
def v13 : ℕ := 0xff3ff7773ce4ebae1effffcf73dffeb79bffe4e4ce7f0d7ff7fffe7ffcfe4e4fff000fff001fc003f07ffc000007fe00003fc0007fff03fbf36ef83ffc3c0607
def v14 : ℕ := 0xcd0cc44428a4ca2c0080030862180024926a4484882d0550160c34400074484700000fff00000003f000000000000000003fc000000003f8932e7800003c0007
def v15 : ℕ := 0x32330222144021821c5280461187689209002060465208254091023b8082060800000000001fc000007fe0000007fe00000000007fe000014000003fc0000600
def v16 : ℕ := 0xc00c4142000820802ac490802581004022600808804004ab602f044101008020000000000000000000000000000000000000000000000000000000000000000
def v17 : ℕ := 0xc00c05400084082002a1120962008020103804040008010ab76c0040202040040000000000000000000000000000000000000000000000000000000000000000
def v18 : ℕ := 0xcdfcffd52fbcfaef8fef7ffffe5f97e5f2fffcbccb3dc75ffffeffe67e7fcd67ff000ffff8000003ff801c7fe0000000003fc03f801f03fab76efbc03c3fc007
def v19 : ℕ := 0xd00f0152820c20c000c6d800058160582c7c080882504500002fc045c5c0843ff000fff00000003f0001c0000000000003fc000001f03fab36ef8003c3c0007
def v20 : ℕ := 0xf00a80071830c38d4200769c0701c0600038384310c205489003a20203852000000000f80000000f80007fe00000000000003f80000000040003c00003c000
def v21 : ℕ := 0xfffffaefdb7b5555fddfffb6edbb6fffffcbdb5b35e3febfdffffd9bcffdb3f900ffffff00003ffc0003e380000001ffffc0000003e0fffd9bbb6803c3fc01f8
def v22 : ℕ := 0x54555a2051491500b4841812248922005a8a894914425aa0c23040880438923800000fff000000fc00000000000000007fc00000000003f8933a6800003c0038
def v23 : ℕ := 0xa8aaa0458a32405548494024491245b50001121221a1a41304449513480121c10000000000003f000003e000000001ff8000000003e0000100000003c00001c0
def v24 : ℕ := 0x12111222104001001416bc8200812a02098080400442082cc1b34808848802080000000000000000000000000000000000000000000000000000000000000000
def v25 : ℕ := 0x4544488841091400a1800310a4280048f64a4909100052801a0820800374903000ffffff000000fc00000380000000007fc000000000fffc9bbb680003fc0038
def v26 : ℕ := 0x20222111040020820a6940451146d49100152020421000032040823778020400ff000000001fc000007ffc000007fe00000000007fff00036040803ffc000600
def v27 : ℕ := 0x14414828400104002594891004a820084e0201011000108cda036088011010100000000000000000000000000000000000000000000000000000000000000000
def v28 : ℕ := 0x431412821148110090023682a0010a42b1c8c84804424a2001b8080086ec822800ffffff000000fc00000380000000007fc000000000fffc9bbb680003fc0038
def v29 : ℕ := 0x40540a800108100085821212a4010040700808080000420cdbb80080022080200000000000000000000000000000000000000000000000000000000000000000
def v30 : ℕ := 0xd7fd5fea57dd3de3bff7bffffeafabeafffafd7d575adbafffff6beaa7ffd73c00fffffff80000fc0f8003ffe00000007fc0003f8000fffc9fbb6bc003ffc038
def v31 : ℕ := 0x1701502a504105003014ad8000a82a0a8fc2c141144218a00003680885dc121800ffffff000000fc00000380000000007fc000000000fffc9bbb680003fc0038
def v32 : ℕ := 0x80a80540069428e30a61006d5a0681a00030343443188103244403622003450400000000f80000000f80007fe00000000000003f80000000040003c00003c000
def v33 : ℕ := 0xbbbbb3ff9e7261d75f7fffe7d9f7ffffadd5f27267f3ac3ffdffff3fffcf27c9fffff000001fff00007fff800007ffff800000007ffffc0768c1803fffc007c0
def v34 : ℕ := 0x898880cc8a32405541000320c830016ca440521221a1a4101c0c3500034521c100fff00000003f0000000380000001ff800000000000fc040881000003c001c0
def v35 : ℕ := 0x10111330144021821624184310c5b2000894a06046520820e030422c340a0608ff000000001fc000007c1c000007fe00000000007c1f00026040803c3c000600
def v36 : ℕ := 0x2882800c800200104958c1200930411c040002022080200f1c03b111010020800000000000000000000000000000000000000000000000000000000000000000
def v37 : ℕ := 0x80a800c00210004109430224c80201e0200010100100800f1dcc0102020101000000000000000000000000000000000000000000000000000000000000000000
def v38 : ℕ := 0xebfeafcf8fbe78f7cffbf7ffff37cdfff5797e3e63b9e71fffffbff3ebe7e5e500fff000f8003f000f83e3ffe00001ff8000003f83e0fc050c8103c3c3c3c1c0
def v39 : ℕ := 0x2b02a00f882240144018e58001304c1f8541420220a124100003bc11c9c420c100fff00000003f000003e380000001ff8000000003e0fc0508810003c3c001c0
def v40 : ℕ := 0x40540f00058c38a286a0105b3605800050382c2c42184300e23002e02022c42400000000f80000000f80007fe00000000000003f80000000040003c00003c000
def v41 : ℕ := 0x3ef3ff3ff443a79a7ffffdff1fffff9f4fb7a3e3fed638effff3fbfffd9a3e9aff00000007ffc0000ffffc001ffffe000000003fffff0003644083fffc003e00
def v42 : ℕ := 0x2303303144021821003348700038e830191a0604652082001f00802ec8a0608ff000000001fc0000003fc000007fe000000000003ff000320408003fc000600
def v43 : ℕ := 0xcc0cc0ce0038618618001380e38010c46220383b88430c01e0031c0011038920000000007e000000f8000001ff800000000003f80000000040003c000003800
def v44 : ℕ := 0x300300040020820e63104710078080001020204210000fe1f00222200204000000000000000000000000000000000000000000000000000000000000000000
def v45 : ℕ := 0x3203303310400100101cec8001c07e1309858040044208200003c81ddc880208ff000000001fc000007ffc000007fe00000000007fff00036040803ffc000600
def v46 : ℕ := 0xc0cc0cc0039c186181800238ee00016070281c1c0108c3001e0c01c00221c12400000000f80000000f80007fe00000000000003f80000000040003c00003c000
def v47 : ℕ := 0xfcffcffce79fbefbefffdb7ffffff1fc7e3e3fbffb9cf3cffffff3ff3333fdb600000000ffe000000ffc007ffff800000000003ffc000000440003fc0003f800
def v48 : ℕ := 0x3c03c03ce0038618601cc90001f8701c0e060383b88430c00003f01d111038920000000007e00000007c00001ff80000000000007c0000004000003c00003800
def v49 : ℕ := 0xc03c03c0079c38e380031207e00380e030183c3c4318c30001fc00022223c52400000000f80000000000007fe00000000000000000000000000000000003c000
def wires0 : List ℕ := [v0,v1,v2,v3,v4,v5]
def block0 : List CallState := ((nextList 3 wires0).drop 0).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed0 : AllRejected 7 block0 := checkedBlock (by decide +kernel)
def wires1 : List ℕ := [v6,v0,v1,v2,v3,v4,v5]
def block1 : List CallState := ((nextList 1 wires1).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed1 : AllRejected 6 block1 := checkedBlock (by decide +kernel)
def block2 : List CallState := ((nextList 1 wires1).drop 14).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed2 : AllRejected 6 block2 := checkedBlock (by decide +kernel)
def block3 : List CallState := ((nextList 1 wires1).drop 25).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed3 : AllRejected 6 block3 := checkedBlock (by decide +kernel)
def block4 : List CallState := ((nextList 1 wires1).drop 36).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed4 : AllRejected 6 block4 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node1 : walk 7 1 wires1 = false := by
  have rest := (appendOk closed1 (appendOk closed2 (appendOk closed3 (appendOk closed4 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires1) (by decide +kernel) (by decide +kernel) rest
def wires2 : List ℕ := [v7,v0,v1,v2,v3,v4,v5]
def block5 : List CallState := ((nextList 1 wires2).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed5 : AllRejected 6 block5 := checkedBlock (by decide +kernel)
def block6 : List CallState := ((nextList 1 wires2).drop 14).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed6 : AllRejected 6 block6 := checkedBlock (by decide +kernel)
def block7 : List CallState := ((nextList 1 wires2).drop 24).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed7 : AllRejected 6 block7 := checkedBlock (by decide +kernel)
def block8 : List CallState := ((nextList 1 wires2).drop 36).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed8 : AllRejected 6 block8 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node2 : walk 7 1 wires2 = false := by
  have rest := (appendOk closed5 (appendOk closed6 (appendOk closed7 (appendOk closed8 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires2) (by decide +kernel) (by decide +kernel) rest
def wires3 : List ℕ := [v8,v0,v1,v2,v3,v4,v5]
def block9 : List CallState := ((nextList 1 wires3).drop 0).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed9 : AllRejected 6 block9 := checkedBlock (by decide +kernel)
def block10 : List CallState := ((nextList 1 wires3).drop 12).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed10 : AllRejected 6 block10 := checkedBlock (by decide +kernel)
def block11 : List CallState := ((nextList 1 wires3).drop 22).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed11 : AllRejected 6 block11 := checkedBlock (by decide +kernel)
def block12 : List CallState := ((nextList 1 wires3).drop 32).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed12 : AllRejected 6 block12 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node3 : walk 7 1 wires3 = false := by
  have rest := (appendOk closed9 (appendOk closed10 (appendOk closed11 (appendOk closed12 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires3) (by decide +kernel) (by decide +kernel) rest
def wires4 : List ℕ := [v9,v0,v2,v1,v3,v4,v5]
def block13 : List CallState := ((nextList 1 wires4).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed13 : AllRejected 6 block13 := checkedBlock (by decide +kernel)
def block14 : List CallState := ((nextList 1 wires4).drop 9).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed14 : AllRejected 6 block14 := checkedBlock (by decide +kernel)
def block15 : List CallState := ((nextList 1 wires4).drop 15).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed15 : AllRejected 6 block15 := checkedBlock (by decide +kernel)
def block16 : List CallState := ((nextList 1 wires4).drop 22).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed16 : AllRejected 6 block16 := checkedBlock (by decide +kernel)
def block17 : List CallState := ((nextList 1 wires4).drop 24).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed17 : AllRejected 6 block17 := checkedBlock (by decide +kernel)
def block18 : List CallState := ((nextList 1 wires4).drop 28).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed18 : AllRejected 6 block18 := checkedBlock (by decide +kernel)
def block19 : List CallState := ((nextList 1 wires4).drop 32).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed19 : AllRejected 6 block19 := checkedBlock (by decide +kernel)
def block20 : List CallState := ((nextList 1 wires4).drop 36).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed20 : AllRejected 6 block20 := checkedBlock (by decide +kernel)
def block21 : List CallState := ((nextList 1 wires4).drop 38).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed21 : AllRejected 6 block21 := checkedBlock (by decide +kernel)
def block22 : List CallState := ((nextList 1 wires4).drop 39).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed22 : AllRejected 6 block22 := checkedBlock (by decide +kernel)
def block23 : List CallState := ((nextList 1 wires4).drop 45).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed23 : AllRejected 6 block23 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node4 : walk 7 1 wires4 = false := by
  have rest := (appendOk closed13 (appendOk closed14 (appendOk closed15 (appendOk closed16 (appendOk closed17 (appendOk closed18 (appendOk closed19 (appendOk closed20 (appendOk closed21 (appendOk closed22 (appendOk closed23 (emptyOk 6))))))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires4) (by decide +kernel) (by decide +kernel) rest
def wires5 : List ℕ := [v10,v0,v2,v1,v3,v4,v5]
def block24 : List CallState := ((nextList 1 wires5).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed24 : AllRejected 6 block24 := checkedBlock (by decide +kernel)
def block25 : List CallState := ((nextList 1 wires5).drop 14).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed25 : AllRejected 6 block25 := checkedBlock (by decide +kernel)
def block26 : List CallState := ((nextList 1 wires5).drop 22).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed26 : AllRejected 6 block26 := checkedBlock (by decide +kernel)
def block27 : List CallState := ((nextList 1 wires5).drop 23).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed27 : AllRejected 6 block27 := checkedBlock (by decide +kernel)
def block28 : List CallState := ((nextList 1 wires5).drop 32).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed28 : AllRejected 6 block28 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node5 : walk 7 1 wires5 = false := by
  have rest := (appendOk closed24 (appendOk closed25 (appendOk closed26 (appendOk closed27 (appendOk closed28 (emptyOk 6))))))
  exact split_walk (k := 6) (e := 1) (ws := wires5) (by decide +kernel) (by decide +kernel) rest
def wires6 : List ℕ := [v11,v0,v2,v1,v3,v4,v5]
def block29 : List CallState := ((nextList 1 wires6).drop 0).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed29 : AllRejected 6 block29 := checkedBlock (by decide +kernel)
def block30 : List CallState := ((nextList 1 wires6).drop 12).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed30 : AllRejected 6 block30 := checkedBlock (by decide +kernel)
def block31 : List CallState := ((nextList 1 wires6).drop 23).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed31 : AllRejected 6 block31 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node6 : walk 7 1 wires6 = false := by
  have rest := (appendOk closed29 (appendOk closed30 (appendOk closed31 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires6) (by decide +kernel) (by decide +kernel) rest
def wires7 : List ℕ := [v12,v0,v2,v1,v3,v4,v5]
def block32 : List CallState := ((nextList 1 wires7).drop 0).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed32 : AllRejected 6 block32 := checkedBlock (by decide +kernel)
def block33 : List CallState := ((nextList 1 wires7).drop 12).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed33 : AllRejected 6 block33 := checkedBlock (by decide +kernel)
def block34 : List CallState := ((nextList 1 wires7).drop 23).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed34 : AllRejected 6 block34 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node7 : walk 7 1 wires7 = false := by
  have rest := (appendOk closed32 (appendOk closed33 (appendOk closed34 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires7) (by decide +kernel) (by decide +kernel) rest
def block35 : List CallState := ((nextList 3 wires0).drop 8).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed35 : AllRejected 7 block35 := checkedBlock (by decide +kernel)
def wires8 : List ℕ := [v13,v0,v3,v1,v2,v4,v5]
def block36 : List CallState := ((nextList 1 wires8).drop 0).take 18
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed36 : AllRejected 6 block36 := checkedBlock (by decide +kernel)
def block37 : List CallState := ((nextList 1 wires8).drop 18).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed37 : AllRejected 6 block37 := checkedBlock (by decide +kernel)
def block38 : List CallState := ((nextList 1 wires8).drop 29).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed38 : AllRejected 6 block38 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node8 : walk 7 1 wires8 = false := by
  have rest := (appendOk closed36 (appendOk closed37 (appendOk closed38 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires8) (by decide +kernel) (by decide +kernel) rest
def wires9 : List ℕ := [v14,v0,v3,v1,v2,v4,v5]
def block39 : List CallState := ((nextList 1 wires9).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed39 : AllRejected 6 block39 := checkedBlock (by decide +kernel)
def block40 : List CallState := ((nextList 1 wires9).drop 13).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed40 : AllRejected 6 block40 := checkedBlock (by decide +kernel)
def block41 : List CallState := ((nextList 1 wires9).drop 24).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed41 : AllRejected 6 block41 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node9 : walk 7 1 wires9 = false := by
  have rest := (appendOk closed39 (appendOk closed40 (appendOk closed41 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires9) (by decide +kernel) (by decide +kernel) rest
def wires10 : List ℕ := [v15,v0,v3,v1,v2,v4,v5]
def block42 : List CallState := ((nextList 1 wires10).drop 0).take 17
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed42 : AllRejected 6 block42 := checkedBlock (by decide +kernel)
def block43 : List CallState := ((nextList 1 wires10).drop 17).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed43 : AllRejected 6 block43 := checkedBlock (by decide +kernel)
def block44 : List CallState := ((nextList 1 wires10).drop 29).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed44 : AllRejected 6 block44 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node10 : walk 7 1 wires10 = false := by
  have rest := (appendOk closed42 (appendOk closed43 (appendOk closed44 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires10) (by decide +kernel) (by decide +kernel) rest
def wires11 : List ℕ := [v16,v0,v4,v1,v2,v3,v5]
def block45 : List CallState := ((nextList 1 wires11).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed45 : AllRejected 6 block45 := checkedBlock (by decide +kernel)
def block46 : List CallState := ((nextList 1 wires11).drop 10).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed46 : AllRejected 6 block46 := checkedBlock (by decide +kernel)
def block47 : List CallState := ((nextList 1 wires11).drop 16).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed47 : AllRejected 6 block47 := checkedBlock (by decide +kernel)
def block48 : List CallState := ((nextList 1 wires11).drop 24).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed48 : AllRejected 6 block48 := checkedBlock (by decide +kernel)
def block49 : List CallState := ((nextList 1 wires11).drop 32).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed49 : AllRejected 6 block49 := checkedBlock (by decide +kernel)
def block50 : List CallState := ((nextList 1 wires11).drop 40).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed50 : AllRejected 6 block50 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node11 : walk 7 1 wires11 = false := by
  have rest := (appendOk closed45 (appendOk closed46 (appendOk closed47 (appendOk closed48 (appendOk closed49 (appendOk closed50 (emptyOk 6)))))))
  exact split_walk (k := 6) (e := 1) (ws := wires11) (by decide +kernel) (by decide +kernel) rest
def block51 : List CallState := ((nextList 3 wires0).drop 13).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed51 : AllRejected 7 block51 := checkedBlock (by decide +kernel)
def block52 : List CallState := ((nextList 3 wires0).drop 14).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed52 : AllRejected 7 block52 := checkedBlock (by decide +kernel)
def block53 : List CallState := ((nextList 3 wires0).drop 15).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed53 : AllRejected 7 block53 := checkedBlock (by decide +kernel)
def wires12 : List ℕ := [v17,v0,v5,v1,v2,v3,v4]
def block54 : List CallState := ((nextList 1 wires12).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed54 : AllRejected 6 block54 := checkedBlock (by decide +kernel)
def block55 : List CallState := ((nextList 1 wires12).drop 10).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed55 : AllRejected 6 block55 := checkedBlock (by decide +kernel)
def block56 : List CallState := ((nextList 1 wires12).drop 16).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed56 : AllRejected 6 block56 := checkedBlock (by decide +kernel)
def block57 : List CallState := ((nextList 1 wires12).drop 24).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed57 : AllRejected 6 block57 := checkedBlock (by decide +kernel)
def block58 : List CallState := ((nextList 1 wires12).drop 32).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed58 : AllRejected 6 block58 := checkedBlock (by decide +kernel)
def block59 : List CallState := ((nextList 1 wires12).drop 41).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed59 : AllRejected 6 block59 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node12 : walk 7 1 wires12 = false := by
  have rest := (appendOk closed54 (appendOk closed55 (appendOk closed56 (appendOk closed57 (appendOk closed58 (appendOk closed59 (emptyOk 6)))))))
  exact split_walk (k := 6) (e := 1) (ws := wires12) (by decide +kernel) (by decide +kernel) rest
def wires13 : List ℕ := [v18,v0,v5,v1,v2,v3,v4]
def block60 : List CallState := ((nextList 1 wires13).drop 0).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed60 : AllRejected 6 block60 := checkedBlock (by decide +kernel)
def block61 : List CallState := ((nextList 1 wires13).drop 12).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed61 : AllRejected 6 block61 := checkedBlock (by decide +kernel)
def block62 : List CallState := ((nextList 1 wires13).drop 26).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed62 : AllRejected 6 block62 := checkedBlock (by decide +kernel)
def block63 : List CallState := ((nextList 1 wires13).drop 34).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed63 : AllRejected 6 block63 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node13 : walk 7 1 wires13 = false := by
  have rest := (appendOk closed60 (appendOk closed61 (appendOk closed62 (appendOk closed63 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires13) (by decide +kernel) (by decide +kernel) rest
def wires14 : List ℕ := [v19,v0,v5,v1,v2,v3,v4]
def block64 : List CallState := ((nextList 1 wires14).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed64 : AllRejected 6 block64 := checkedBlock (by decide +kernel)
def block65 : List CallState := ((nextList 1 wires14).drop 11).take 16
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed65 : AllRejected 6 block65 := checkedBlock (by decide +kernel)
def block66 : List CallState := ((nextList 1 wires14).drop 27).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed66 : AllRejected 6 block66 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node14 : walk 7 1 wires14 = false := by
  have rest := (appendOk closed64 (appendOk closed65 (appendOk closed66 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires14) (by decide +kernel) (by decide +kernel) rest
def wires15 : List ℕ := [v20,v0,v5,v1,v2,v3,v4]
def block67 : List CallState := ((nextList 1 wires15).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed67 : AllRejected 6 block67 := checkedBlock (by decide +kernel)
def block68 : List CallState := ((nextList 1 wires15).drop 10).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed68 : AllRejected 6 block68 := checkedBlock (by decide +kernel)
def block69 : List CallState := ((nextList 1 wires15).drop 20).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed69 : AllRejected 6 block69 := checkedBlock (by decide +kernel)
def block70 : List CallState := ((nextList 1 wires15).drop 32).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed70 : AllRejected 6 block70 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node15 : walk 7 1 wires15 = false := by
  have rest := (appendOk closed67 (appendOk closed68 (appendOk closed69 (appendOk closed70 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires15) (by decide +kernel) (by decide +kernel) rest
def block71 : List CallState := ((nextList 3 wires0).drop 20).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed71 : AllRejected 7 block71 := checkedBlock (by decide +kernel)
def wires16 : List ℕ := [v21,v1,v2,v0,v3,v4,v5]
def block72 : List CallState := ((nextList 1 wires16).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed72 : AllRejected 6 block72 := checkedBlock (by decide +kernel)
def block73 : List CallState := ((nextList 1 wires16).drop 14).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed73 : AllRejected 6 block73 := checkedBlock (by decide +kernel)
def block74 : List CallState := ((nextList 1 wires16).drop 25).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed74 : AllRejected 6 block74 := checkedBlock (by decide +kernel)
def block75 : List CallState := ((nextList 1 wires16).drop 34).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed75 : AllRejected 6 block75 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node16 : walk 7 1 wires16 = false := by
  have rest := (appendOk closed72 (appendOk closed73 (appendOk closed74 (appendOk closed75 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires16) (by decide +kernel) (by decide +kernel) rest
def wires17 : List ℕ := [v22,v1,v2,v0,v3,v4,v5]
def block76 : List CallState := ((nextList 1 wires17).drop 0).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed76 : AllRejected 6 block76 := checkedBlock (by decide +kernel)
def block77 : List CallState := ((nextList 1 wires17).drop 12).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed77 : AllRejected 6 block77 := checkedBlock (by decide +kernel)
def block78 : List CallState := ((nextList 1 wires17).drop 22).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed78 : AllRejected 6 block78 := checkedBlock (by decide +kernel)
def block79 : List CallState := ((nextList 1 wires17).drop 32).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed79 : AllRejected 6 block79 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node17 : walk 7 1 wires17 = false := by
  have rest := (appendOk closed76 (appendOk closed77 (appendOk closed78 (appendOk closed79 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires17) (by decide +kernel) (by decide +kernel) rest
def wires18 : List ℕ := [v23,v1,v2,v0,v3,v4,v5]
def block80 : List CallState := ((nextList 1 wires18).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed80 : AllRejected 6 block80 := checkedBlock (by decide +kernel)
def block81 : List CallState := ((nextList 1 wires18).drop 14).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed81 : AllRejected 6 block81 := checkedBlock (by decide +kernel)
def block82 : List CallState := ((nextList 1 wires18).drop 24).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed82 : AllRejected 6 block82 := checkedBlock (by decide +kernel)
def block83 : List CallState := ((nextList 1 wires18).drop 36).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed83 : AllRejected 6 block83 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node18 : walk 7 1 wires18 = false := by
  have rest := (appendOk closed80 (appendOk closed81 (appendOk closed82 (appendOk closed83 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires18) (by decide +kernel) (by decide +kernel) rest
def wires19 : List ℕ := [v24,v1,v3,v0,v2,v4,v5]
def block84 : List CallState := ((nextList 1 wires19).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed84 : AllRejected 6 block84 := checkedBlock (by decide +kernel)
def block85 : List CallState := ((nextList 1 wires19).drop 10).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed85 : AllRejected 6 block85 := checkedBlock (by decide +kernel)
def block86 : List CallState := ((nextList 1 wires19).drop 16).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed86 : AllRejected 6 block86 := checkedBlock (by decide +kernel)
def block87 : List CallState := ((nextList 1 wires19).drop 23).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed87 : AllRejected 6 block87 := checkedBlock (by decide +kernel)
def block88 : List CallState := ((nextList 1 wires19).drop 28).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed88 : AllRejected 6 block88 := checkedBlock (by decide +kernel)
def block89 : List CallState := ((nextList 1 wires19).drop 32).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed89 : AllRejected 6 block89 := checkedBlock (by decide +kernel)
def block90 : List CallState := ((nextList 1 wires19).drop 37).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed90 : AllRejected 6 block90 := checkedBlock (by decide +kernel)
def block91 : List CallState := ((nextList 1 wires19).drop 44).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed91 : AllRejected 6 block91 := checkedBlock (by decide +kernel)
def block92 : List CallState := ((nextList 1 wires19).drop 49).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed92 : AllRejected 6 block92 := checkedBlock (by decide +kernel)
def block93 : List CallState := ((nextList 1 wires19).drop 52).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed93 : AllRejected 6 block93 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node19 : walk 7 1 wires19 = false := by
  have rest := (appendOk closed84 (appendOk closed85 (appendOk closed86 (appendOk closed87 (appendOk closed88 (appendOk closed89 (appendOk closed90 (appendOk closed91 (appendOk closed92 (appendOk closed93 (emptyOk 6)))))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires19) (by decide +kernel) (by decide +kernel) rest
def block94 : List CallState := ((nextList 3 wires0).drop 25).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed94 : AllRejected 7 block94 := checkedBlock (by decide +kernel)
def wires20 : List ℕ := [v25,v1,v3,v0,v2,v4,v5]
def block95 : List CallState := ((nextList 1 wires20).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed95 : AllRejected 6 block95 := checkedBlock (by decide +kernel)
def block96 : List CallState := ((nextList 1 wires20).drop 14).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed96 : AllRejected 6 block96 := checkedBlock (by decide +kernel)
def block97 : List CallState := ((nextList 1 wires20).drop 26).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed97 : AllRejected 6 block97 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node20 : walk 7 1 wires20 = false := by
  have rest := (appendOk closed95 (appendOk closed96 (appendOk closed97 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires20) (by decide +kernel) (by decide +kernel) rest
def wires21 : List ℕ := [v26,v1,v3,v0,v2,v4,v5]
def block98 : List CallState := ((nextList 1 wires21).drop 0).take 17
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed98 : AllRejected 6 block98 := checkedBlock (by decide +kernel)
def block99 : List CallState := ((nextList 1 wires21).drop 17).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed99 : AllRejected 6 block99 := checkedBlock (by decide +kernel)
def block100 : List CallState := ((nextList 1 wires21).drop 28).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed100 : AllRejected 6 block100 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node21 : walk 7 1 wires21 = false := by
  have rest := (appendOk closed98 (appendOk closed99 (appendOk closed100 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires21) (by decide +kernel) (by decide +kernel) rest
def wires22 : List ℕ := [v27,v1,v4,v0,v2,v3,v5]
def block101 : List CallState := ((nextList 1 wires22).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed101 : AllRejected 6 block101 := checkedBlock (by decide +kernel)
def block102 : List CallState := ((nextList 1 wires22).drop 10).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed102 : AllRejected 6 block102 := checkedBlock (by decide +kernel)
def block103 : List CallState := ((nextList 1 wires22).drop 18).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed103 : AllRejected 6 block103 := checkedBlock (by decide +kernel)
def block104 : List CallState := ((nextList 1 wires22).drop 26).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed104 : AllRejected 6 block104 := checkedBlock (by decide +kernel)
def block105 : List CallState := ((nextList 1 wires22).drop 33).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed105 : AllRejected 6 block105 := checkedBlock (by decide +kernel)
def block106 : List CallState := ((nextList 1 wires22).drop 42).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed106 : AllRejected 6 block106 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node22 : walk 7 1 wires22 = false := by
  have rest := (appendOk closed101 (appendOk closed102 (appendOk closed103 (appendOk closed104 (appendOk closed105 (appendOk closed106 (emptyOk 6)))))))
  exact split_walk (k := 6) (e := 1) (ws := wires22) (by decide +kernel) (by decide +kernel) rest
def block107 : List CallState := ((nextList 3 wires0).drop 29).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed107 : AllRejected 7 block107 := checkedBlock (by decide +kernel)
def wires23 : List ℕ := [v28,v1,v4,v0,v2,v3,v5]
def block108 : List CallState := ((nextList 1 wires23).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed108 : AllRejected 6 block108 := checkedBlock (by decide +kernel)
def block109 : List CallState := ((nextList 1 wires23).drop 14).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed109 : AllRejected 6 block109 := checkedBlock (by decide +kernel)
def block110 : List CallState := ((nextList 1 wires23).drop 26).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed110 : AllRejected 6 block110 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node23 : walk 7 1 wires23 = false := by
  have rest := (appendOk closed108 (appendOk closed109 (appendOk closed110 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires23) (by decide +kernel) (by decide +kernel) rest
def block111 : List CallState := ((nextList 3 wires0).drop 31).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed111 : AllRejected 7 block111 := checkedBlock (by decide +kernel)
def wires24 : List ℕ := [v29,v1,v5,v0,v2,v3,v4]
def block112 : List CallState := ((nextList 1 wires24).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed112 : AllRejected 6 block112 := checkedBlock (by decide +kernel)
def block113 : List CallState := ((nextList 1 wires24).drop 10).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed113 : AllRejected 6 block113 := checkedBlock (by decide +kernel)
def block114 : List CallState := ((nextList 1 wires24).drop 18).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed114 : AllRejected 6 block114 := checkedBlock (by decide +kernel)
def block115 : List CallState := ((nextList 1 wires24).drop 24).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed115 : AllRejected 6 block115 := checkedBlock (by decide +kernel)
def block116 : List CallState := ((nextList 1 wires24).drop 32).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed116 : AllRejected 6 block116 := checkedBlock (by decide +kernel)
def block117 : List CallState := ((nextList 1 wires24).drop 41).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed117 : AllRejected 6 block117 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node24 : walk 7 1 wires24 = false := by
  have rest := (appendOk closed112 (appendOk closed113 (appendOk closed114 (appendOk closed115 (appendOk closed116 (appendOk closed117 (emptyOk 6)))))))
  exact split_walk (k := 6) (e := 1) (ws := wires24) (by decide +kernel) (by decide +kernel) rest
def wires25 : List ℕ := [v30,v1,v5,v0,v2,v3,v4]
def block118 : List CallState := ((nextList 1 wires25).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed118 : AllRejected 6 block118 := checkedBlock (by decide +kernel)
def block119 : List CallState := ((nextList 1 wires25).drop 14).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed119 : AllRejected 6 block119 := checkedBlock (by decide +kernel)
def block120 : List CallState := ((nextList 1 wires25).drop 15).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed120 : AllRejected 6 block120 := checkedBlock (by decide +kernel)
def block121 : List CallState := ((nextList 1 wires25).drop 25).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed121 : AllRejected 6 block121 := checkedBlock (by decide +kernel)
def block122 : List CallState := ((nextList 1 wires25).drop 33).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed122 : AllRejected 6 block122 := checkedBlock (by decide +kernel)
def block123 : List CallState := ((nextList 1 wires25).drop 38).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed123 : AllRejected 6 block123 := checkedBlock (by decide +kernel)
def block124 : List CallState := ((nextList 1 wires25).drop 39).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed124 : AllRejected 6 block124 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node25 : walk 7 1 wires25 = false := by
  have rest := (appendOk closed118 (appendOk closed119 (appendOk closed120 (appendOk closed121 (appendOk closed122 (appendOk closed123 (appendOk closed124 (emptyOk 6))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires25) (by decide +kernel) (by decide +kernel) rest
def wires26 : List ℕ := [v31,v1,v5,v0,v2,v3,v4]
def block125 : List CallState := ((nextList 1 wires26).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed125 : AllRejected 6 block125 := checkedBlock (by decide +kernel)
def block126 : List CallState := ((nextList 1 wires26).drop 13).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed126 : AllRejected 6 block126 := checkedBlock (by decide +kernel)
def block127 : List CallState := ((nextList 1 wires26).drop 26).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed127 : AllRejected 6 block127 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node26 : walk 7 1 wires26 = false := by
  have rest := (appendOk closed125 (appendOk closed126 (appendOk closed127 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires26) (by decide +kernel) (by decide +kernel) rest
def wires27 : List ℕ := [v32,v1,v5,v0,v2,v3,v4]
def block128 : List CallState := ((nextList 1 wires27).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed128 : AllRejected 6 block128 := checkedBlock (by decide +kernel)
def block129 : List CallState := ((nextList 1 wires27).drop 10).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed129 : AllRejected 6 block129 := checkedBlock (by decide +kernel)
def block130 : List CallState := ((nextList 1 wires27).drop 20).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed130 : AllRejected 6 block130 := checkedBlock (by decide +kernel)
def block131 : List CallState := ((nextList 1 wires27).drop 32).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed131 : AllRejected 6 block131 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node27 : walk 7 1 wires27 = false := by
  have rest := (appendOk closed128 (appendOk closed129 (appendOk closed130 (appendOk closed131 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires27) (by decide +kernel) (by decide +kernel) rest
def block132 : List CallState := ((nextList 3 wires0).drop 36).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed132 : AllRejected 7 block132 := checkedBlock (by decide +kernel)
def wires28 : List ℕ := [v33,v2,v3,v0,v1,v4,v5]
def block133 : List CallState := ((nextList 1 wires28).drop 0).take 18
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed133 : AllRejected 6 block133 := checkedBlock (by decide +kernel)
def block134 : List CallState := ((nextList 1 wires28).drop 18).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed134 : AllRejected 6 block134 := checkedBlock (by decide +kernel)
def block135 : List CallState := ((nextList 1 wires28).drop 29).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed135 : AllRejected 6 block135 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node28 : walk 7 1 wires28 = false := by
  have rest := (appendOk closed133 (appendOk closed134 (appendOk closed135 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires28) (by decide +kernel) (by decide +kernel) rest
def wires29 : List ℕ := [v34,v2,v3,v0,v1,v4,v5]
def block136 : List CallState := ((nextList 1 wires29).drop 0).take 15
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed136 : AllRejected 6 block136 := checkedBlock (by decide +kernel)
def block137 : List CallState := ((nextList 1 wires29).drop 15).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed137 : AllRejected 6 block137 := checkedBlock (by decide +kernel)
def block138 : List CallState := ((nextList 1 wires29).drop 25).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed138 : AllRejected 6 block138 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node29 : walk 7 1 wires29 = false := by
  have rest := (appendOk closed136 (appendOk closed137 (appendOk closed138 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires29) (by decide +kernel) (by decide +kernel) rest
def wires30 : List ℕ := [v35,v2,v3,v0,v1,v4,v5]
def block139 : List CallState := ((nextList 1 wires30).drop 0).take 17
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed139 : AllRejected 6 block139 := checkedBlock (by decide +kernel)
def block140 : List CallState := ((nextList 1 wires30).drop 17).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed140 : AllRejected 6 block140 := checkedBlock (by decide +kernel)
def block141 : List CallState := ((nextList 1 wires30).drop 28).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed141 : AllRejected 6 block141 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node30 : walk 7 1 wires30 = false := by
  have rest := (appendOk closed139 (appendOk closed140 (appendOk closed141 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires30) (by decide +kernel) (by decide +kernel) rest
def wires31 : List ℕ := [v36,v2,v4,v0,v1,v3,v5]
def block142 : List CallState := ((nextList 1 wires31).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed142 : AllRejected 6 block142 := checkedBlock (by decide +kernel)
def block143 : List CallState := ((nextList 1 wires31).drop 10).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed143 : AllRejected 6 block143 := checkedBlock (by decide +kernel)
def block144 : List CallState := ((nextList 1 wires31).drop 18).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed144 : AllRejected 6 block144 := checkedBlock (by decide +kernel)
def block145 : List CallState := ((nextList 1 wires31).drop 26).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed145 : AllRejected 6 block145 := checkedBlock (by decide +kernel)
def block146 : List CallState := ((nextList 1 wires31).drop 33).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed146 : AllRejected 6 block146 := checkedBlock (by decide +kernel)
def block147 : List CallState := ((nextList 1 wires31).drop 42).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed147 : AllRejected 6 block147 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node31 : walk 7 1 wires31 = false := by
  have rest := (appendOk closed142 (appendOk closed143 (appendOk closed144 (appendOk closed145 (appendOk closed146 (appendOk closed147 (emptyOk 6)))))))
  exact split_walk (k := 6) (e := 1) (ws := wires31) (by decide +kernel) (by decide +kernel) rest
def block148 : List CallState := ((nextList 3 wires0).drop 41).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed148 : AllRejected 7 block148 := checkedBlock (by decide +kernel)
def block149 : List CallState := ((nextList 3 wires0).drop 42).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed149 : AllRejected 7 block149 := checkedBlock (by decide +kernel)
def block150 : List CallState := ((nextList 3 wires0).drop 43).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed150 : AllRejected 7 block150 := checkedBlock (by decide +kernel)
def wires32 : List ℕ := [v37,v2,v5,v0,v1,v3,v4]
def block151 : List CallState := ((nextList 1 wires32).drop 0).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed151 : AllRejected 6 block151 := checkedBlock (by decide +kernel)
def block152 : List CallState := ((nextList 1 wires32).drop 9).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed152 : AllRejected 6 block152 := checkedBlock (by decide +kernel)
def block153 : List CallState := ((nextList 1 wires32).drop 17).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed153 : AllRejected 6 block153 := checkedBlock (by decide +kernel)
def block154 : List CallState := ((nextList 1 wires32).drop 25).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed154 : AllRejected 6 block154 := checkedBlock (by decide +kernel)
def block155 : List CallState := ((nextList 1 wires32).drop 33).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed155 : AllRejected 6 block155 := checkedBlock (by decide +kernel)
def block156 : List CallState := ((nextList 1 wires32).drop 42).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed156 : AllRejected 6 block156 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node32 : walk 7 1 wires32 = false := by
  have rest := (appendOk closed151 (appendOk closed152 (appendOk closed153 (appendOk closed154 (appendOk closed155 (appendOk closed156 (emptyOk 6)))))))
  exact split_walk (k := 6) (e := 1) (ws := wires32) (by decide +kernel) (by decide +kernel) rest
def wires33 : List ℕ := [v38,v2,v5,v0,v1,v3,v4]
def block157 : List CallState := ((nextList 1 wires33).drop 0).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed157 : AllRejected 6 block157 := checkedBlock (by decide +kernel)
def block158 : List CallState := ((nextList 1 wires33).drop 13).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed158 : AllRejected 6 block158 := checkedBlock (by decide +kernel)
def block159 : List CallState := ((nextList 1 wires33).drop 26).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed159 : AllRejected 6 block159 := checkedBlock (by decide +kernel)
def block160 : List CallState := ((nextList 1 wires33).drop 34).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed160 : AllRejected 6 block160 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node33 : walk 7 1 wires33 = false := by
  have rest := (appendOk closed157 (appendOk closed158 (appendOk closed159 (appendOk closed160 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires33) (by decide +kernel) (by decide +kernel) rest
def wires34 : List ℕ := [v39,v2,v5,v0,v1,v3,v4]
def block161 : List CallState := ((nextList 1 wires34).drop 0).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed161 : AllRejected 6 block161 := checkedBlock (by decide +kernel)
def block162 : List CallState := ((nextList 1 wires34).drop 12).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed162 : AllRejected 6 block162 := checkedBlock (by decide +kernel)
def block163 : List CallState := ((nextList 1 wires34).drop 26).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed163 : AllRejected 6 block163 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node34 : walk 7 1 wires34 = false := by
  have rest := (appendOk closed161 (appendOk closed162 (appendOk closed163 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires34) (by decide +kernel) (by decide +kernel) rest
def wires35 : List ℕ := [v40,v2,v5,v0,v1,v3,v4]
def block164 : List CallState := ((nextList 1 wires35).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed164 : AllRejected 6 block164 := checkedBlock (by decide +kernel)
def block165 : List CallState := ((nextList 1 wires35).drop 10).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed165 : AllRejected 6 block165 := checkedBlock (by decide +kernel)
def block166 : List CallState := ((nextList 1 wires35).drop 19).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed166 : AllRejected 6 block166 := checkedBlock (by decide +kernel)
def block167 : List CallState := ((nextList 1 wires35).drop 30).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed167 : AllRejected 6 block167 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node35 : walk 7 1 wires35 = false := by
  have rest := (appendOk closed164 (appendOk closed165 (appendOk closed166 (appendOk closed167 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires35) (by decide +kernel) (by decide +kernel) rest
def block168 : List CallState := ((nextList 3 wires0).drop 48).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed168 : AllRejected 7 block168 := checkedBlock (by decide +kernel)
def wires36 : List ℕ := [v41,v3,v4,v0,v1,v2,v5]
def block169 : List CallState := ((nextList 1 wires36).drop 0).take 16
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed169 : AllRejected 6 block169 := checkedBlock (by decide +kernel)
def block170 : List CallState := ((nextList 1 wires36).drop 16).take 15
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed170 : AllRejected 6 block170 := checkedBlock (by decide +kernel)
def block171 : List CallState := ((nextList 1 wires36).drop 31).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed171 : AllRejected 6 block171 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node36 : walk 7 1 wires36 = false := by
  have rest := (appendOk closed169 (appendOk closed170 (appendOk closed171 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires36) (by decide +kernel) (by decide +kernel) rest
def wires37 : List ℕ := [v42,v3,v4,v0,v1,v2,v5]
def block172 : List CallState := ((nextList 1 wires37).drop 0).take 17
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed172 : AllRejected 6 block172 := checkedBlock (by decide +kernel)
def block173 : List CallState := ((nextList 1 wires37).drop 17).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed173 : AllRejected 6 block173 := checkedBlock (by decide +kernel)
def block174 : List CallState := ((nextList 1 wires37).drop 31).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed174 : AllRejected 6 block174 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node37 : walk 7 1 wires37 = false := by
  have rest := (appendOk closed172 (appendOk closed173 (appendOk closed174 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires37) (by decide +kernel) (by decide +kernel) rest
def wires38 : List ℕ := [v43,v3,v4,v0,v1,v2,v5]
def block175 : List CallState := ((nextList 1 wires38).drop 0).take 14
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed175 : AllRejected 6 block175 := checkedBlock (by decide +kernel)
def block176 : List CallState := ((nextList 1 wires38).drop 14).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed176 : AllRejected 6 block176 := checkedBlock (by decide +kernel)
def block177 : List CallState := ((nextList 1 wires38).drop 25).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed177 : AllRejected 6 block177 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node38 : walk 7 1 wires38 = false := by
  have rest := (appendOk closed175 (appendOk closed176 (appendOk closed177 (emptyOk 6))))
  exact split_walk (k := 6) (e := 1) (ws := wires38) (by decide +kernel) (by decide +kernel) rest
def wires39 : List ℕ := [v44,v3,v5,v0,v1,v2,v4]
def block178 : List CallState := ((nextList 1 wires39).drop 0).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed178 : AllRejected 6 block178 := checkedBlock (by decide +kernel)
def block179 : List CallState := ((nextList 1 wires39).drop 7).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed179 : AllRejected 6 block179 := checkedBlock (by decide +kernel)
def block180 : List CallState := ((nextList 1 wires39).drop 10).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed180 : AllRejected 6 block180 := checkedBlock (by decide +kernel)
def block181 : List CallState := ((nextList 1 wires39).drop 15).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed181 : AllRejected 6 block181 := checkedBlock (by decide +kernel)
def block182 : List CallState := ((nextList 1 wires39).drop 17).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed182 : AllRejected 6 block182 := checkedBlock (by decide +kernel)
def block183 : List CallState := ((nextList 1 wires39).drop 22).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed183 : AllRejected 6 block183 := checkedBlock (by decide +kernel)
def block184 : List CallState := ((nextList 1 wires39).drop 24).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed184 : AllRejected 6 block184 := checkedBlock (by decide +kernel)
def block185 : List CallState := ((nextList 1 wires39).drop 28).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed185 : AllRejected 6 block185 := checkedBlock (by decide +kernel)
def block186 : List CallState := ((nextList 1 wires39).drop 34).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed186 : AllRejected 6 block186 := checkedBlock (by decide +kernel)
def block187 : List CallState := ((nextList 1 wires39).drop 39).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed187 : AllRejected 6 block187 := checkedBlock (by decide +kernel)
def block188 : List CallState := ((nextList 1 wires39).drop 42).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed188 : AllRejected 6 block188 := checkedBlock (by decide +kernel)
def block189 : List CallState := ((nextList 1 wires39).drop 44).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed189 : AllRejected 6 block189 := checkedBlock (by decide +kernel)
def block190 : List CallState := ((nextList 1 wires39).drop 46).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed190 : AllRejected 6 block190 := checkedBlock (by decide +kernel)
def block191 : List CallState := ((nextList 1 wires39).drop 47).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed191 : AllRejected 6 block191 := checkedBlock (by decide +kernel)
def block192 : List CallState := ((nextList 1 wires39).drop 50).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed192 : AllRejected 6 block192 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node39 : walk 7 1 wires39 = false := by
  have rest := (appendOk closed178 (appendOk closed179 (appendOk closed180 (appendOk closed181 (appendOk closed182 (appendOk closed183 (appendOk closed184 (appendOk closed185 (appendOk closed186 (appendOk closed187 (appendOk closed188 (appendOk closed189 (appendOk closed190 (appendOk closed191 (appendOk closed192 (emptyOk 6))))))))))))))))
  exact split_walk (k := 6) (e := 1) (ws := wires39) (by decide +kernel) (by decide +kernel) rest
def block193 : List CallState := ((nextList 3 wires0).drop 53).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed193 : AllRejected 7 block193 := checkedBlock (by decide +kernel)
def wires40 : List ℕ := [v45,v3,v5,v0,v1,v2,v4]
def block194 : List CallState := ((nextList 1 wires40).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed194 : AllRejected 6 block194 := checkedBlock (by decide +kernel)
def block195 : List CallState := ((nextList 1 wires40).drop 10).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed195 : AllRejected 6 block195 := checkedBlock (by decide +kernel)
def block196 : List CallState := ((nextList 1 wires40).drop 22).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed196 : AllRejected 6 block196 := checkedBlock (by decide +kernel)
def block197 : List CallState := ((nextList 1 wires40).drop 32).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed197 : AllRejected 6 block197 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node40 : walk 7 1 wires40 = false := by
  have rest := (appendOk closed194 (appendOk closed195 (appendOk closed196 (appendOk closed197 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires40) (by decide +kernel) (by decide +kernel) rest
def wires41 : List ℕ := [v46,v3,v5,v0,v1,v2,v4]
def block198 : List CallState := ((nextList 1 wires41).drop 0).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed198 : AllRejected 6 block198 := checkedBlock (by decide +kernel)
def block199 : List CallState := ((nextList 1 wires41).drop 10).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed199 : AllRejected 6 block199 := checkedBlock (by decide +kernel)
def block200 : List CallState := ((nextList 1 wires41).drop 20).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed200 : AllRejected 6 block200 := checkedBlock (by decide +kernel)
def block201 : List CallState := ((nextList 1 wires41).drop 33).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed201 : AllRejected 6 block201 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node41 : walk 7 1 wires41 = false := by
  have rest := (appendOk closed198 (appendOk closed199 (appendOk closed200 (appendOk closed201 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires41) (by decide +kernel) (by decide +kernel) rest
def block202 : List CallState := ((nextList 3 wires0).drop 56).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed202 : AllRejected 7 block202 := checkedBlock (by decide +kernel)
def wires42 : List ℕ := [v47,v5,v0,v1,v2,v3]
def block203 : List CallState := ((nextList 2 wires42).drop 0).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed203 : AllRejected 6 block203 := checkedBlock (by decide +kernel)
def block204 : List CallState := ((nextList 2 wires42).drop 6).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed204 : AllRejected 6 block204 := checkedBlock (by decide +kernel)
def block205 : List CallState := ((nextList 2 wires42).drop 12).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed205 : AllRejected 6 block205 := checkedBlock (by decide +kernel)
def block206 : List CallState := ((nextList 2 wires42).drop 18).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed206 : AllRejected 6 block206 := checkedBlock (by decide +kernel)
def block207 : List CallState := ((nextList 2 wires42).drop 22).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed207 : AllRejected 6 block207 := checkedBlock (by decide +kernel)
def block208 : List CallState := ((nextList 2 wires42).drop 27).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed208 : AllRejected 6 block208 := checkedBlock (by decide +kernel)
def block209 : List CallState := ((nextList 2 wires42).drop 28).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed209 : AllRejected 6 block209 := checkedBlock (by decide +kernel)
def block210 : List CallState := ((nextList 2 wires42).drop 33).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed210 : AllRejected 6 block210 := checkedBlock (by decide +kernel)
def block211 : List CallState := ((nextList 2 wires42).drop 38).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed211 : AllRejected 6 block211 := checkedBlock (by decide +kernel)
def block212 : List CallState := ((nextList 2 wires42).drop 39).take 3
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed212 : AllRejected 6 block212 := checkedBlock (by decide +kernel)
def block213 : List CallState := ((nextList 2 wires42).drop 42).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed213 : AllRejected 6 block213 := checkedBlock (by decide +kernel)
def block214 : List CallState := ((nextList 2 wires42).drop 47).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed214 : AllRejected 6 block214 := checkedBlock (by decide +kernel)
def block215 : List CallState := ((nextList 2 wires42).drop 53).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed215 : AllRejected 6 block215 := checkedBlock (by decide +kernel)
def block216 : List CallState := ((nextList 2 wires42).drop 59).take 4
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed216 : AllRejected 6 block216 := checkedBlock (by decide +kernel)
def block217 : List CallState := ((nextList 2 wires42).drop 63).take 5
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed217 : AllRejected 6 block217 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node42 : walk 7 2 wires42 = false := by
  have rest := (appendOk closed203 (appendOk closed204 (appendOk closed205 (appendOk closed206 (appendOk closed207 (appendOk closed208 (appendOk closed209 (appendOk closed210 (appendOk closed211 (appendOk closed212 (appendOk closed213 (appendOk closed214 (appendOk closed215 (appendOk closed216 (appendOk closed217 (emptyOk 6))))))))))))))))
  exact split_walk (k := 6) (e := 2) (ws := wires42) (by decide +kernel) (by decide +kernel) rest
def wires43 : List ℕ := [v47,v4,v5,v0,v1,v2,v3]
def block218 : List CallState := ((nextList 1 wires43).drop 0).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed218 : AllRejected 6 block218 := checkedBlock (by decide +kernel)
def block219 : List CallState := ((nextList 1 wires43).drop 12).take 13
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed219 : AllRejected 6 block219 := checkedBlock (by decide +kernel)
def block220 : List CallState := ((nextList 1 wires43).drop 25).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed220 : AllRejected 6 block220 := checkedBlock (by decide +kernel)
def block221 : List CallState := ((nextList 1 wires43).drop 33).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed221 : AllRejected 6 block221 := checkedBlock (by decide +kernel)
def block222 : List CallState := ((nextList 1 wires43).drop 42).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed222 : AllRejected 6 block222 := checkedBlock (by decide +kernel)
def block223 : List CallState := ((nextList 1 wires43).drop 51).take 2
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed223 : AllRejected 6 block223 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node43 : walk 7 1 wires43 = false := by
  have rest := (appendOk closed218 (appendOk closed219 (appendOk closed220 (appendOk closed221 (appendOk closed222 (appendOk closed223 (emptyOk 6)))))))
  exact split_walk (k := 6) (e := 1) (ws := wires43) (by decide +kernel) (by decide +kernel) rest
def wires44 : List ℕ := [v48,v5,v0,v1,v2,v3]
def block224 : List CallState := ((nextList 2 wires44).drop 0).take 6
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed224 : AllRejected 6 block224 := checkedBlock (by decide +kernel)
def block225 : List CallState := ((nextList 2 wires44).drop 6).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed225 : AllRejected 6 block225 := checkedBlock (by decide +kernel)
def block226 : List CallState := ((nextList 2 wires44).drop 15).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed226 : AllRejected 6 block226 := checkedBlock (by decide +kernel)
def block227 : List CallState := ((nextList 2 wires44).drop 26).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed227 : AllRejected 6 block227 := checkedBlock (by decide +kernel)
def block228 : List CallState := ((nextList 2 wires44).drop 34).take 10
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed228 : AllRejected 6 block228 := checkedBlock (by decide +kernel)
def block229 : List CallState := ((nextList 2 wires44).drop 44).take 18
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed229 : AllRejected 6 block229 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node44 : walk 7 2 wires44 = false := by
  have rest := (appendOk closed224 (appendOk closed225 (appendOk closed226 (appendOk closed227 (appendOk closed228 (appendOk closed229 (emptyOk 6)))))))
  exact split_walk (k := 6) (e := 2) (ws := wires44) (by decide +kernel) (by decide +kernel) rest
def wires45 : List ℕ := [v48,v4,v5,v0,v1,v2,v3]
def block230 : List CallState := ((nextList 1 wires45).drop 0).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed230 : AllRejected 6 block230 := checkedBlock (by decide +kernel)
def block231 : List CallState := ((nextList 1 wires45).drop 12).take 9
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed231 : AllRejected 6 block231 := checkedBlock (by decide +kernel)
def block232 : List CallState := ((nextList 1 wires45).drop 21).take 7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed232 : AllRejected 6 block232 := checkedBlock (by decide +kernel)
def block233 : List CallState := ((nextList 1 wires45).drop 28).take 8
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed233 : AllRejected 6 block233 := checkedBlock (by decide +kernel)
def block234 : List CallState := ((nextList 1 wires45).drop 36).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed234 : AllRejected 6 block234 := checkedBlock (by decide +kernel)
def block235 : List CallState := ((nextList 1 wires45).drop 48).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed235 : AllRejected 6 block235 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node45 : walk 7 1 wires45 = false := by
  have rest := (appendOk closed230 (appendOk closed231 (appendOk closed232 (appendOk closed233 (appendOk closed234 (appendOk closed235 (emptyOk 6)))))))
  exact split_walk (k := 6) (e := 1) (ws := wires45) (by decide +kernel) (by decide +kernel) rest
def wires46 : List ℕ := [v49,v4,v5,v0,v1,v2,v3]
def block236 : List CallState := ((nextList 1 wires46).drop 0).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed236 : AllRejected 6 block236 := checkedBlock (by decide +kernel)
def block237 : List CallState := ((nextList 1 wires46).drop 11).take 12
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed237 : AllRejected 6 block237 := checkedBlock (by decide +kernel)
def block238 : List CallState := ((nextList 1 wires46).drop 23).take 11
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed238 : AllRejected 6 block238 := checkedBlock (by decide +kernel)
def block239 : List CallState := ((nextList 1 wires46).drop 34).take 1
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem closed239 : AllRejected 6 block239 := checkedBlock (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node46 : walk 7 1 wires46 = false := by
  have rest := (appendOk closed236 (appendOk closed237 (appendOk closed238 (appendOk closed239 (emptyOk 6)))))
  exact split_walk (k := 6) (e := 1) (ws := wires46) (by decide +kernel) (by decide +kernel) rest
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem node0 : walk 8 3 wires0 = false := by
  have rest := (appendOk closed0 (consOk node1 (consOk node2 (consOk node3 (consOk node4 (consOk node5 (consOk node6 (consOk node7 (appendOk closed35 (consOk node8 (consOk node9 (consOk node10 (consOk node11 (appendOk closed51 (appendOk closed52 (appendOk closed53 (consOk node12 (consOk node13 (consOk node14 (consOk node15 (appendOk closed71 (consOk node16 (consOk node17 (consOk node18 (consOk node19 (appendOk closed94 (consOk node20 (consOk node21 (consOk node22 (appendOk closed107 (consOk node23 (appendOk closed111 (consOk node24 (consOk node25 (consOk node26 (consOk node27 (appendOk closed132 (consOk node28 (consOk node29 (consOk node30 (consOk node31 (appendOk closed148 (appendOk closed149 (appendOk closed150 (consOk node32 (consOk node33 (consOk node34 (consOk node35 (appendOk closed168 (consOk node36 (consOk node37 (consOk node38 (consOk node39 (appendOk closed193 (consOk node40 (consOk node41 (appendOk closed202 (consOk node42 (consOk node43 (consOk node44 (consOk node45 (consOk node46 (emptyOk 7)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  exact split_walk (k := 7) (e := 3) (ws := wires0) (by decide +kernel) (by decide +kernel) rest
end PEqualNP.Outside.L_meta_10556_aux.NatCheck.Delete6

open PEqualNP.Outside.L_meta_10556_aux PEqualNP.Outside.L_meta_10556_aux.Reduction PEqualNP.Outside.L_meta_10556_aux.NatCheck in
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem PEqualNP.Outside.L_meta_10556 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  apply fromTwo
  · apply entersOnly (child 0) (childrenND 0)
    · decide +kernel
    · exact Delete0.node0
  · apply entersOnly (child 6) (childrenND 6)
    · decide +kernel
    · exact Delete6.node0
