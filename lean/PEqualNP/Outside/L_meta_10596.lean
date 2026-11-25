import Mathlib
import PEqualNP.Defs

-- The graph G has edges 0-2 1-3 0-4 2-4 0-5 1-5 2-5 4-5 0-6 1-6 2-6 3-6 4-6. Its edge function
-- has a twelve-gate AND/OR circuit (twelve below), and every AND/OR/NOT circuit for it has at
-- least eleven gates other than NOT gates, even with NOT gates for free (eleven_binary). So a
-- list with a NOT gate has at least twelve gates, and one without is its own replacement.
-- The bound 11 = 1 + 2 + 8: fixing x5 false removes a gate and leaves G - 5 (K4 on 0, 2, 4, 6
-- and the triangle 1, 3, 6); there the first gate reads two inputs, one of them among
-- 0, 1, 2, 3, 4 and still read afterwards, so fixing that one false removes two gates and
-- leaves the bowtie or K4 with a pendant edge. Each needs eight gates: the bowtie by search;
-- for the other, the pendant input false removes a gate and leaves K4, seven gates by search.
-- The search, the compiler from gate lists and the transport of live runs are copied from
-- the merged proof of L-meta-8724 (which credits L-meta-1449, L-meta-1429 and L-meta-703).
namespace PEqualNP.Outside.L_meta_10596

open PEqualNP.CircuitLowerBounds

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

def differs (i : Fin 256) (w : W) : Prop :=
  w.getLsbD (256+i.val) ≠ w.getLsbD i.val

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

theorem goal_differs {t : W} (ht : t = goal ∨ t = ~~~goal) : ∀ i, differs i t := by
  rcases ht with rfl | rfl <;> unfold differs <;> decide +kernel

-- The Boolean form of differs, for checks by evaluation.
def changes (w : W) (r : Fin 256) : Bool :=
  w.getLsbD (256+r.val) != w.getLsbD r.val

theorem unchanged (w : W) (r : Fin 256) (h : changes w r = false) : ¬ differs r w := by
  simpa [changes, differs] using h

theorem changed {w : W} {r : Fin 256} (h : differs r w) : changes w r = true := by
  simpa [changes, differs] using h

theorem cuts_spec (ws : List W) (i : Fin 256) :
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
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs hg _) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

theorem index_of_op (a b z : W) (hz : z ∈ basicOps a b) :
    ∃ o : Fin 4, (ops a b).getD o.val 0 = z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩

-- The search: pick two live wires, apply one of the four operations, and keep each operand
-- only if it is still needed; every live run is found, so a false search rules out a build.
def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

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

theorem holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a,ha,e⟩ => ⟨a,sub ha,e⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

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

theorem sb_zero {av : Finset W} {z : W} (h : holds av z) : SignedBuild 0 av z := by
  rcases h with h | h | ⟨a,ha,rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not,build] using ha)))

theorem sb_wait {av : Finset W} {z : W} {k : ℕ} (h : SignedBuild k av z) :
    SignedBuild (k+1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

theorem sb_le {av : Finset W} {z : W} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild k av z) :
    SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {av : Finset W} {t a b z : W} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps a b) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k+1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩) (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩)))

theorem sb_advance {av : Finset W} {z t : W} {k : ℕ} (hz : reachable av z)
    (next : ∀ av' : Finset W, av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k+1) av t := by
  rcases hz with h | ⟨a,ha,b,hb,hn,w,hw,ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

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

-- Reading the rows of a wire through a map of rows commutes with the gate operations.
def reindex (σ : Fin 512 → Fin 512) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn fun k : Fin 512 => w[(σ k).val])).cast List.length_ofFn

theorem reindex_bit (σ : Fin 512 → Fin 512) (w : W) (j : ℕ) (hj : j < 512) :
    (reindex σ w)[j] = w[(σ ⟨j, hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [reindex, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem reindex_not (σ : Fin 512 → Fin 512) (u : W) : reindex σ (~~~u) = ~~~reindex σ u :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [reindex_bit, BitVec.getElem_not]

theorem reindex_ops (σ : Fin 512 → Fin 512) (a b z : W) (hz : z ∈ basicOps a b) :
    reindex σ z ∈ basicOps (reindex σ a) (reindex σ b) := by
  have hand (u v : W) : reindex σ (u &&& v) = (reindex σ u &&& reindex σ v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [reindex_bit, BitVec.getElem_and]
  have hor (u v : W) : reindex σ (u ||| v) = (reindex σ u ||| reindex σ v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [reindex_bit, BitVec.getElem_or]
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand, hor, reindex_not]

-- Excluded k v: no k binary gates over the wires v reach the goal or its complement.
def Excluded (k : ℕ) (v : List W) : Prop :=
  ∀ t, t = goal ∨ t = ~~~goal → ¬build basicOps t k v.toFinset

theorem excluded_of_search {k : ℕ} {v : List W} (hn : v.Nodup) (hs : search k v = false) :
    Excluded k v :=
  fun _ ht run => Bool.false_ne_true (hs.symm.trans (search_complete ht k v hn run))

-- Three tests on lists of wires, in Boolean form so that they are checked by evaluation.
-- plain: no wire of v is the goal or its complement.
def plain (v : List W) : Bool := v.all fun u => u != goal && u != ~~~goal

-- alone: among v, only the wire x separates pair i.
def alone (v : List W) (i : Fin 256) (x : W) : Bool := v.all fun u => !changes u i || u == x

-- restricts: the row map keeps the goal and sends every wire of v to zero or into w.
def restricts (σ : Fin 512 → Fin 512) (v w : List W) : Bool :=
  reindex σ goal == goal && v.all fun u => reindex σ u == 0 || w.contains (reindex σ u)

theorem plain_ne {v : List W} (h : plain v = true) {t u : W} (ht : t = goal ∨ t = ~~~goal)
    (hu : u ∈ v) : u ≠ t := by
  have := List.all_eq_true.mp h u hu
  simp only [Bool.and_eq_true, bne_iff_ne] at this
  rcases ht with rfl | rfl
  exacts [this.1, this.2]

theorem alone_eq {v : List W} {i : Fin 256} {x u : W} (h : alone v i x = true) (hu : u ∈ v)
    (hd : differs i u) : u = x := by
  simpa [changed hd] using List.all_eq_true.mp h u hu

theorem restricts_goal {σ : Fin 512 → Fin 512} {v w : List W} (h : restricts σ v w = true) :
    reindex σ goal = goal :=
  beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1

theorem restricts_holds {σ : Fin 512 → Fin 512} {v w : List W} (h : restricts σ v w = true)
    {u : W} (hu : u ∈ v) : holds w.toFinset (reindex σ u) := by
  have := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 u hu
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at this
  exact this.imp_right fun hm => .inr ⟨_, List.mem_toFinset.mpr hm, .inl rfl⟩

-- A live run over wires of v, one of which a restriction sends to zero, would give a build
-- over w with one step less.
theorem restrict_run {σ : Fin 512 → Fin 512} {k : ℕ} {s : Finset W} {v w : List W} {t p : W}
    (ht : t = goal ∨ t = ~~~goal) (hσ : restricts σ v w = true) (run : live basicOps t k s)
    (hp : p ∈ s) (hpt : p ≠ t) (hzero : reindex σ p = 0)
    (hav : ∀ u ∈ s, holds w.toFinset (reindex σ u)) (lower : Excluded (k - 1) w) : False := by
  have sign : reindex σ t = goal ∨ reindex σ t = ~~~goal := by
    rcases ht with rfl | rfl
    · exact .inl (restricts_goal hσ)
    · exact .inr (by rw [reindex_not, restricts_goal hσ])
  rcases live_transport_save (reindex_ops σ) run hp hpt hzero hav with c | c | h | h
  · rcases sign with e | e <;> exact absurd (e.symm.trans c) (by decide +kernel)
  · rcases sign with e | e <;> exact absurd (e.symm.trans c) (by decide +kernel)
  · exact lower _ sign h
  · exact lower _ (by rcases sign with e | e <;> simp [e]) h

-- One gate: if the wire x alone separates some pair, every run over v keeps x live, and a
-- restriction that sends x to zero saves a gate.
theorem lift_one {k : ℕ} {v w : List W} (σ : Fin 512 → Fin 512) (i : Fin 256) (x : W)
    (h : (plain v && alone v i x && reindex σ x == 0 && restricts σ v w) = true)
    (lower : Excluded k w) : Excluded (k + 1) v := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hv, only⟩, hzero⟩, hσ⟩ := h
  intro t ht run
  obtain ⟨s, sub, hl⟩ := compress run
  have inV : ∀ u ∈ s, u ∈ v := fun u hu => List.mem_toFinset.mp (sub hu)
  obtain ⟨u, hu, hd⟩ := live_separates (differs i) (goal_differs ht i) (ops_differs i) hl
  have hxs : x ∈ s := alone_eq only (inV u hu) hd ▸ hu
  exact restrict_run ht hσ hl hxs (plain_ne hv ht (inV x hxs)) hzero
    (fun z hz => restricts_holds hσ (inV z hz)) lower

-- Two gates: the first gate of a run over v reads two wires a and b of v. If one of them, x,
-- alone separates a pair that the gate does not separate either, x stays live after the
-- gate; a restriction that sends x to zero then removes the first gate and one more.
theorem lift_two {k : ℕ} {v : List W} (hv : plain v = true)
    (first : ∀ a ∈ v, ∀ b ∈ v, a ≠ b → ∀ z ∈ basicOps a b, ∃ x, (x = a ∨ x = b) ∧
      ∃ (i : Fin 256) (σ : Fin 512 → Fin 512) (w : List W), changes z i = false ∧
        alone v i x = true ∧ reindex σ x = 0 ∧ restricts σ v w = true ∧ Excluded k w) :
    Excluded (k + 2) v := by
  intro t ht run
  obtain ⟨s, sub, hl⟩ := compress run
  have inV : ∀ u ∈ s, u ∈ v := fun u hu => List.mem_toFinset.mp (sub hu)
  rcases first_live hl with done | ⟨a, ha, b, hb, hab, z, hz, -, rest, he, tail⟩
  · exact plain_ne hv ht (inV t (by simp [done])) rfl
  · have inRest : ∀ u ∈ rest, u ∈ v := fun u hu => inV u (he ▸ by simp [hu])
    obtain ⟨x, hx, i, σ, w, hiz, only, hzero, hσ, lower⟩ :=
      first a (inV a ha) b (inV b hb) hab z hz
    obtain ⟨u, hu, hd⟩ := live_separates (differs i) (goal_differs ht i) (ops_differs i) tail
    have hxr : x ∈ rest := by
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact absurd hd (unchanged _ _ hiz)
      · exact alone_eq only (inRest u hu) hd ▸ hu
    refine restrict_run ht hσ tail (Finset.mem_insert_of_mem hxr)
      (plain_ne hv ht (inRest x hxr)) hzero (fun u hu => ?_) lower
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact mem_ops_zero (restricts_holds hσ (inV a ha)) (restricts_holds hσ (inV b hb))
        (hx.imp (fun e : x = a => e ▸ hzero) fun e : x = b => e ▸ hzero) (reindex_ops σ a b u hz)
    · exact restricts_holds hσ (inRest u hu)

-- Row maps into a sample in product layout, by two tables: false row k reads row
-- tf[k mod |tf|] and true row k reads true row tt[(k div |tf|) mod |tt|].
def rowMap (tf tt : List ℕ) (k : Fin 512) : Fin 512 :=
  ⟨(if k.val < 256 then tf.getD (k.val % tf.length) 0
    else 256 + tt.getD ((k.val - 256) / tf.length % tt.length) 0) % 512, Nat.mod_lt _ (by decide)⟩

-- Samples in product layout: pair k joins the false row F[k mod |F|] and the true row
-- T[(k div |F|) mod |T|] of the function. K4 on four inputs: no six gates.
def k4Ins : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842,
  0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084,
  0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108,
  0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210]

theorem k4_search : search 6 k4Ins = false := by decide +kernel

-- K4 on inputs 0 to 3 with the pendant edge 3-4: pair 139 is the edge 3-4 against its
-- end 3, which only input 4 separates, and input 4 false leaves K4.
def k4pIns : List W := [0xffffc01ffffffc01ff007fc01ff007fc01ffffffc01ff007fc01ffff803ffff2211088442211088442211088442211088442211088442211088442211088442,
  0xf007fffe00ffffffe00007fffe00007fffe00ffffffe00007fffe00ffffc01ff4422110884422110884422110884422110884422110884422110884422110884,
  0x7ffffff007ffffffff8000000007ffffff007ffffffff8000000ffffffe008844221108844221108844221108844221108844221108844221108844221108,
  0xfff8000000007fffffffffffffffff8000000007fffffffffffffff0000000000080402010080402010080402010080402010080402010080402010080402010,
  0x7ffffffffffffffffffffffffff80000000000000000000000000f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0f0783c1e0]

theorem k4p_excluded : Excluded 7 k4pIns :=
  lift_one (rowMap [0, 1, 2, 3, 4] [0, 9, 18, 27, 36, 45, 54, 63, 72, 81, 90]) 139
    (k4pIns.getD 4 0) (by decide +kernel) (excluded_of_search (by decide +kernel) k4_search)

-- The bowtie, triangles 0-1-4 and 2-3-4: no seven gates.
def bowtieIns : List W := [0x3fffffffffc00ffc00ffc00ffc00ffc00ffc00ffc00fffff003ff003fffffff4892248922489224892248922489224892248922489224892248922489224892,
  0x3ffffffffffff00000fffff00000fffff00000fffff003ffffc00003fffffff9124491244912449124491244912449124491244912449124491244912449124,
  0xfc00ffc00ffffffffff0000000000ffffffffff00000003fffffffffc00ffc00e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e038,
  0xffff00000ffffffffffffffffffff000000000000000003ffffffffffff0000001c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c0,
  0xfffffffffffffffffffffffffffffffffffffc000000000000000000200802008020080200802008020080200802008020080200802008020080200]

theorem bowtie_search : search 7 bowtieIns = false := by decide +kernel

-- G - 5 on the inputs 0, 1, 2, 3, 4, 6, in this order. Its first 25 pairs are the separating
-- pairs for the first gate; the others only make every row present.
def ins6 : List W := [0xd5555555ab5dbaaaaaaab56bb755555556ad76eaaaaaaad5aedd555554e1385fc5022811408a045022811408a045022811408a045022811408a0450228e13840,
  0xe6666666cd96ecccccccd9b2dd9999999b365bb333333366cb766666664d93e21610b085842c21610b085842c21610b085842c21610b085842c21610b04d9002,
  0xf8787878f1e73f0f0f0f1e3ce7e1e1e1e3c79cfc3c3c3c78f39f878786147c8b1804c026013009804c026013009804c026013009804c026013009804c014008b,
  0xff807f80fe07cff00ff01fc0f9fe01fe03f81f3fc03fc07f03e7f807f88fa2e86027013809c04e027013809c04e027013809c04e027013809c04e027008022e8,
  0xffff8000fff80ffff0001fff01fffe0003ffe03fffc0007ffc07fff801f80604003801c00e007003801c00e007003801c00e007003801c00e007003800080604,
  0xffffffff00000fffffffe00001fffffffc00003fffffff800007ffffff0241100040020010008004002001000800400200100080040020010008004003024110]

-- Fixing input i < 5 false leaves K4 with a pendant edge for i = 1, 3 and the bowtie for
-- i = 0, 2, 4; the tables say where the rows of those samples sit in ins6.
def tables6 : List (List ℕ × List ℕ) := [
  ([26, 15, 5, 0, 1, 3, 2, 19, 9, 4],
   [5, 7, 9, 10, 62, 67, 69, 8, 17, 29, 14, 25, 31, 33, 24, 37, 43, 45, 39, 41, 47, 49]),
  ([26, 11, 0, 2, 4, 5, 6, 3, 9],
   [0, 2, 10, 61, 4, 14, 75, 24, 36, 39, 40, 3, 23, 67, 68, 17, 28, 31, 32, 43, 44, 47, 48]),
  ([26, 15, 5, 11, 12, 6, 2, 19, 9, 4],
   [5, 6, 9, 2, 22, 23, 66, 8, 17, 29, 4, 73, 28, 30, 24, 37, 43, 45, 36, 38, 44, 46]),
  ([26, 11, 0, 2, 4, 15, 12, 1, 19],
   [0, 2, 10, 61, 4, 14, 75, 24, 36, 39, 40, 1, 22, 62, 63, 8, 73, 25, 26, 37, 38, 41, 42]),
  ([26, 15, 5, 11, 12, 6, 0, 1, 3, 4],
   [5, 6, 7, 0, 1, 3, 57, 8, 17, 29, 4, 73, 28, 30, 14, 25, 31, 33, 75, 26, 32, 34])]

def sigma6 (i : ℕ) : Fin 512 → Fin 512 :=
  rowMap (tables6.getD i ([], [])).1 (tables6.getD i ([], [])).2

def target6 (i : ℕ) : List W := if i % 2 = 1 then k4pIns else bowtieIns

theorem target6_excluded (i : ℕ) : Excluded 7 (target6 i) := by
  unfold target6
  split
  · exact k4p_excluded
  · exact excluded_of_search (by decide +kernel) bowtie_search

-- The two checks behind lift_two on ins6: the restrictions, and for every first gate a pair
-- that it does not separate and that its smaller input alone separates.
theorem restricts6 : ∀ i : Fin 5, reindex (sigma6 i) (ins6.getD i 0) = 0 ∧
    restricts (sigma6 i) ins6 (target6 i) = true := by decide +kernel

theorem separating6 : ∀ i j : Fin 6, i < j → ∀ o : Fin 4, ∃ r : Fin 256,
    changes ((ops (ins6.getD i 0) (ins6.getD j 0)).getD o 0) r = false ∧
    alone ins6 r (ins6.getD i 0) = true := by decide +kernel

theorem ins6_index {u : W} (hu : u ∈ ins6) : ∃ i : Fin 6, ins6.getD i 0 = u := by
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hu
  exact ⟨⟨n, hn⟩, by simp [List.getD_eq_getElem?_getD, hn]⟩

-- The first gate on inputs i < j of G - 5: input i passes the test of lift_two.
theorem first6 (i j : Fin 6) (hij : i < j) (z : W)
    (hz : z ∈ basicOps (ins6.getD i 0) (ins6.getD j 0)) :
    ∃ (r : Fin 256) (σ : Fin 512 → Fin 512) (w : List W), changes z r = false ∧
      alone ins6 r (ins6.getD i 0) = true ∧ reindex σ (ins6.getD i 0) = 0 ∧
      restricts σ ins6 w = true ∧ Excluded 7 w := by
  obtain ⟨o, rfl⟩ := index_of_op _ _ _ hz
  obtain ⟨r, hrz, hri⟩ := separating6 i j hij o
  obtain ⟨hzero, hσ⟩ := restricts6 ⟨i, by omega⟩
  exact ⟨r, _, _, hrz, hri, hzero, hσ, target6_excluded i⟩

theorem ins6_excluded : Excluded 9 ins6 := by
  refine lift_two (by decide +kernel) fun a ha b hb hab z hz => ?_
  obtain ⟨i, rfl⟩ := ins6_index ha
  obtain ⟨j, rfl⟩ := ins6_index hb
  rcases lt_or_gt_of_ne (fun e : i = j => hab (by rw [e])) with hij | hij
  · exact ⟨_, .inl rfl, first6 i j hij z hz⟩
  · exact ⟨_, .inr rfl, first6 j i hij z (ops_swap _ _ ▸ hz)⟩

-- G itself: ins6 with input 5 false, except the true row of pair 255, the edge 0-5 against its
-- end 0, which only input 5 separates.
def ins7 : List W := [0xd5555555ab5dbaaaaaaab56bb755555556ad76eaaaaaaad5aedd555554e1385fc5022811408a045022811408a045022811408a045022811408a0450228e13840,
  0x66666666cd96ecccccccd9b2dd9999999b365bb333333366cb766666664d93e21610b085842c21610b085842c21610b085842c21610b085842c21610b04d9002,
  0x78787878f1e73f0f0f0f1e3ce7e1e1e1e3c79cfc3c3c3c78f39f878786147c8b1804c026013009804c026013009804c026013009804c026013009804c014008b,
  0x7f807f80fe07cff00ff01fc0f9fe01fe03f81f3fc03fc07f03e7f807f88fa2e86027013809c04e027013809c04e027013809c04e027013809c04e027008022e8,
  0x7fff8000fff80ffff0001fff01fffe0003ffe03fffc0007ffc07fff801f80604003801c00e007003801c00e007003801c00e007003801c00e007003800080604,
  0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x7fffffff00000fffffffe00001fffffffc00003fffffff800007ffffff0241100040020010008004002001000800400200100080040020010008004003024110]

theorem ins7_excluded : Excluded 10 ins7 :=
  lift_one (fun k => if k = 511 then 510 else k) 255 (ins7.getD 5 0) (by decide +kernel)
    ins6_excluded

-- The edge function as the step writes it; the rows of ins7 are 256 false and 256 true
-- inputs of it.
def graph (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

theorem sample : ∀ j : Fin 512, graph (fun i => (ins7.getD i.val 0)[j.val]) = goal[j.val] := by
  decide +kernel

-- Every AND/OR/NOT list for the edge function has at least eleven gates other than NOT gates.
theorem eleven_binary (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = graph x) :
    10 < binaryCost gs := by
  by_contra! low
  have evaluate (k : Fin 512) : (gs.foldl step (ins7.map (bit k))).getD o false = bit k goal := by
    have same : List.ofFn (fun i : Fin 7 => bit k (ins7.getD i.val 0)) = ins7.map (bit k) := by
      apply List.ext_getElem (by simp [ins7])
      intro i hi hj
      have hlt : i < ins7.length := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (ins7.map (bit k)) = bit k goal
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg ins7 ins7.toFinset
    (fun u hu => .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)) evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins7.toFinset) :
      build basicOps t b ins7.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact ins7_excluded t ht (lift low run)

-- A least AND/OR circuit: twelve gates.
def twelve : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [6, 5]⟩,
  ⟨.and, [10, 7]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [10, 0]⟩, ⟨.and, [13, 2]⟩, ⟨.or, [14, 12]⟩,
  ⟨.or, [13, 2]⟩, ⟨.and, [16, 4]⟩, ⟨.or, [17, 15]⟩], 18⟩

theorem twelve_eval : ∀ x : Fin 7 → Bool, twelve.eval (List.ofFn x) = graph x := by
  decide +kernel

-- A list with a NOT gate has more gates than binary ones, hence at least twelve; a list
-- without one is already an AND/OR list.
theorem replacement (gates : List Gate) (o : ℕ) (fits : ∀ g ∈ gates, legal g)
    (computes : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graph x) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = graph x := by
  by_cases present : ∃ g ∈ gates, g.op = .not
  · obtain ⟨g, hm, hn⟩ := present
    have cut : binaryCost gates < gates.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, hm, by simp [isBinary, hn]⟩
    have eleven := eleven_binary gates o fits computes
    exact ⟨twelve.gates, twelve.output, by simp [twelve], by change 12 ≤ _; omega, twelve_eval⟩
  · exact ⟨gates, o, fun g hg => ⟨(fits g hg).1.imp_right (·.resolve_right fun h =>
      present ⟨g, hg, h⟩), (fits g hg).2⟩, le_rfl, computes⟩

end PEqualNP.Outside.L_meta_10596

theorem PEqualNP.Outside.L_meta_10596 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  exact PEqualNP.Outside.L_meta_10596.replacement gates o fits computes
