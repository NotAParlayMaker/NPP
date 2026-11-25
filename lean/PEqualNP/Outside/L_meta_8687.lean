import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8687

-- This development is the proof of L-meta-8628 by pierandozzimichael (pull request 12834; signed
-- live-wire search after L-meta-8463 and L-meta-1449, Apache-2.0) with the table, the sampled
-- input words, the search depth and the witness circuit replaced.
-- Every pair of a true and a false row of the target is sampled. The search is split two levels
-- deep into chunks, one kernel check each (the split lemmas are mine).

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

-- The upper and lower halves represent opposite target labels on 255 pairs of assignments.
abbrev W := BitVec 510
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 255 := ((x >>> 255) ^^^ x).setWidth 255
def cuts (ws : List W) : BitVec 255 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 255) ++ (0 : BitVec 255)
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

def differs (i : Fin 255) (w : W) : Prop :=
  w.getLsbD (255+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 255) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 255+i.val < 510 := by omega
  have hi' : i.val < 510 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 255) :
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
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 255)[j]
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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

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
  · change reachable av (BitVec.allOnes 510 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 510)
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

private def bit (k : Fin 510) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 510) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 510) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#510)[k.val] = false; simp
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
def inputs : List W := [0x3bb6f76deedbddb7bb6f76deedbddb7bb6f76deedbddb7bb6f76deedbddb7bb68000fffe0003fff8000fffe00000007fff000000000007fff000000000000000, 0x376deedbddb7bb6f76deedbddb7bb6f76deedbddb7bb6f76deedbddb7bb6f76d80000001fffffff80000001fffc0000000fffe00000000000fffe00000000000, 0x2ee3ddc7bb8f771eee3ddc7bb8f771eee3ddc7bb8f771eee3ddc7bb8f771eee38000000000000007ffffffffffc00000000001fffc00000000001fffc0007fff, 0x1e1fbc3f787ef0fde1fbc3f787ef0fde1fbc3f787ef0fde1fbc3f787ef0fde1f800000000000000000000000003ffffffffffffffc000000000000003fffffff, 0x1ff83ff07fe0ffc1ff83ff07fe0ffc1ff83ff07fe0ffc1ff83ff07fe0ffc1ff800000000000000000000000000000000000000003ffffffffffffffffffffff]

def complementInputs : List W := inputs.map (fun w => ~~~w)

def targetFun (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xfee8e888 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 8000 in
theorem sample_rows : ∀ j : Fin 510,
    targetFun (fun i => (complementInputs.getD i.val 0)[j.val]) = (~~~goal)[j.val] := by
  decide +kernel

theorem bound_from_impossible (n : ℕ)
    (impossible : ∀ t, t = goal ∨ t = ~~~goal → build basicOps t n inputs.toFinset → False)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = targetFun x) :
    n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ complementInputs, holds inputs.toFinset u := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
    exact .inr (.inr ⟨w, List.mem_toFinset.mpr hw, .inr rfl⟩)
  have evaluate (k : Fin 510) :
      (gs.foldl step (complementInputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 5) : Bool := bit k (complementInputs.getD i.val 0)
    have width : complementInputs.length = 5 := rfl
    have same : List.ofFn x = complementInputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < complementInputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (complementInputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample_rows k
  obtain ⟨t,ht,run⟩ := compile gs o hg complementInputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact impossible t ht (lift low run)

theorem allSplit {β : Type} (f : β → Bool) (l : List β) (n : ℕ) :
    l.all f = ((l.take n).all f && (l.drop n).all f) := by
  rw [← List.all_append, List.take_append_drop]

theorem splitStep {β : Type} (f : β → Bool) (l : List β) (n m k : ℕ) (hk : n + m = k)
    (h1 : ((l.drop n).take m).all f = true) (h2 : (l.drop k).all f = true) :
    (l.drop n).all f = true := by
  subst hk
  rw [allSplit f (l.drop n) m, h1, Bool.true_and, List.drop_drop]
  simpa [Nat.add_comm] using h2

def cand (extra : ℕ) (a b : W) (r : List W) : List (ℕ × List W) :=
  (ops a b).flatMap fun w =>
    (if ((sep w ||| cuts r) == -1) = true then [(extra, w :: r)] else []) ++
    ((if ((extra != 0) && ((sep w ||| cuts r) ||| sep a == -1)) = true then [(extra - 1, w :: a :: r)] else []) ++
    ((if ((extra != 0) && ((sep w ||| cuts r) ||| sep b == -1)) = true then [(extra - 1, w :: b :: r)] else []) ++
    (if (decide (extra ≥ 2) && ((sep w ||| cuts r) ||| sep a ||| sep b == -1)) = true then [(extra - 2, w :: a :: b :: r)] else [])))

theorem any_if {β : Type} (c : Bool) (s : β) (f : β → Bool) :
    (if c = true then [s] else []).any f = (c && f s) := by
  cases c <;> simp

theorem dispatch_eq (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) :
    dispatch extra next a b r = (cand extra a b r).any (fun s => next s.1 s.2) := by
  simp only [dispatch, cand, ops, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.any_cons, List.any_nil, Bool.or_false, List.any_append, any_if, Bool.and_assoc,
    Bool.or_assoc, Bool.and_or_distrib_left]

def nexts (extra : ℕ) (ws : List W) : List (ℕ × List W) :=
  (pairs ws).flatMap fun p => cand extra p.1 p.2.1 p.2.2

theorem opt_step (k extra : ℕ) (ws : List W) : optimized (k + 1) extra ws =
    ((ws == [goal] || ws == [~~~goal]) || (nexts extra ws).any (fun s => optimized k s.1 s.2)) := by
  show ((ws == [goal] || ws == [~~~goal]) || (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)) = _
  congr 1
  rw [nexts, List.any_flatMap]
  congr 1
  funext p
  rcases p with ⟨a, b, r⟩
  exact dispatch_eq extra (optimized k) a b r

def expand (L : List (ℕ × List W)) : List (ℕ × List W) := L.flatMap fun s => nexts s.1 s.2

def clean (L : List (ℕ × List W)) : Bool := L.all (fun s => !(s.2 == [goal] || s.2 == [~~~goal]))

theorem down (k : ℕ) (L : List (ℕ × List W)) (hc : clean L = true)
    (h : ∀ t ∈ expand L, optimized k t.1 t.2 = false) :
    ∀ s ∈ L, optimized (k + 1) s.1 s.2 = false := by
  intro s hs
  rw [opt_step]
  have hg := List.all_eq_true.mp hc s hs
  have hg' : (s.2 == [goal] || s.2 == [~~~goal]) = false := by simpa using hg
  rw [hg', Bool.false_or, List.any_eq_false]
  intro t ht
  rw [h t (List.mem_flatMap.mpr ⟨s, hs, ht⟩)]
  exact Bool.false_ne_true

def level0 : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ 8 + 1) && (cuts ws == -1))).map
    (fun ws => (8 + 1 - ws.length, ws))

def level2 : List (ℕ × List W) := expand (expand level0)

def midOK (s : ℕ × List W) : Bool := (nexts s.1 s.2).all (fun t => !optimized 5 t.1 t.2)

set_option maxRecDepth 32000 in
theorem clean0 : clean level0 = true := by decide +kernel

set_option maxRecDepth 32000 in
theorem clean1 : clean (expand level0) = true := by decide +kernel

set_option maxRecDepth 32000 in
theorem clean2 : clean level2 = true := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk0 : ((List.drop 0 level2).take 27).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk1 : ((List.drop 27 level2).take 33).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk2 : ((List.drop 60 level2).take 41).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk3 : ((List.drop 101 level2).take 21).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk4 : ((List.drop 122 level2).take 21).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk5 : ((List.drop 143 level2).take 29).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk6 : ((List.drop 172 level2).take 34).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk7 : ((List.drop 206 level2).take 31).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk8 : ((List.drop 237 level2).take 52).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk9 : ((List.drop 289 level2).take 29).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk10 : ((List.drop 318 level2).take 51).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk11 : ((List.drop 369 level2).take 30).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk12 : ((List.drop 399 level2).take 39).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk13 : ((List.drop 438 level2).take 41).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk14 : ((List.drop 479 level2).take 30).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk15 : ((List.drop 509 level2).take 51).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk16 : ((List.drop 560 level2).take 29).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk17 : ((List.drop 589 level2).take 50).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk18 : ((List.drop 639 level2).take 33).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk19 : ((List.drop 672 level2).take 40).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk20 : ((List.drop 712 level2).take 42).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk21 : ((List.drop 754 level2).take 32).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk22 : ((List.drop 786 level2).take 49).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk23 : ((List.drop 835 level2).take 29).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk24 : ((List.drop 864 level2).take 48).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk25 : ((List.drop 912 level2).take 31).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk26 : ((List.drop 943 level2).take 42).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk27 : ((List.drop 985 level2).take 42).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk28 : ((List.drop 1027 level2).take 31).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk29 : ((List.drop 1058 level2).take 51).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk30 : ((List.drop 1109 level2).take 29).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk31 : ((List.drop 1138 level2).take 46).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk32 : ((List.drop 1184 level2).take 33).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk33 : ((List.drop 1217 level2).take 37).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk34 : ((List.drop 1254 level2).take 44).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk35 : ((List.drop 1298 level2).take 31).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk36 : ((List.drop 1329 level2).take 54).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk37 : ((List.drop 1383 level2).take 28).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk38 : ((List.drop 1411 level2).take 52).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk39 : ((List.drop 1463 level2).take 28).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk40 : ((List.drop 1491 level2).take 39).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk41 : ((List.drop 1530 level2).take 41).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk42 : ((List.drop 1571 level2).take 30).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk43 : ((List.drop 1601 level2).take 51).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk44 : ((List.drop 1652 level2).take 29).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk45 : ((List.drop 1681 level2).take 50).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk46 : ((List.drop 1731 level2).take 33).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk47 : ((List.drop 1764 level2).take 40).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk48 : ((List.drop 1804 level2).take 42).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk49 : ((List.drop 1846 level2).take 32).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk50 : ((List.drop 1878 level2).take 49).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk51 : ((List.drop 1927 level2).take 29).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk52 : ((List.drop 1956 level2).take 48).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk53 : ((List.drop 2004 level2).take 31).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk54 : ((List.drop 2035 level2).take 42).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk55 : ((List.drop 2077 level2).take 42).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk56 : ((List.drop 2119 level2).take 31).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk57 : ((List.drop 2150 level2).take 51).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk58 : ((List.drop 2201 level2).take 29).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk59 : ((List.drop 2230 level2).take 46).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk60 : ((List.drop 2276 level2).take 33).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk61 : ((List.drop 2309 level2).take 37).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk62 : ((List.drop 2346 level2).take 44).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk63 : ((List.drop 2390 level2).take 31).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk64 : ((List.drop 2421 level2).take 54).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk65 : ((List.drop 2475 level2).take 28).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk66 : ((List.drop 2503 level2).take 52).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk67 : ((List.drop 2555 level2).take 26).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk68 : ((List.drop 2581 level2).take 26).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk69 : ((List.drop 2607 level2).take 44).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk70 : ((List.drop 2651 level2).take 27).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk71 : ((List.drop 2678 level2).take 29).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk72 : ((List.drop 2707 level2).take 45).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk73 : ((List.drop 2752 level2).take 29).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk74 : ((List.drop 2781 level2).take 46).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk75 : ((List.drop 2827 level2).take 34).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk76 : ((List.drop 2861 level2).take 39).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk77 : ((List.drop 2900 level2).take 44).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk78 : ((List.drop 2944 level2).take 27).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk79 : ((List.drop 2971 level2).take 29).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk80 : ((List.drop 3000 level2).take 39).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk81 : ((List.drop 3039 level2).take 29).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk82 : ((List.drop 3068 level2).take 40).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk83 : ((List.drop 3108 level2).take 33).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk84 : ((List.drop 3141 level2).take 34).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk85 : ((List.drop 3175 level2).take 49).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk86 : ((List.drop 3224 level2).take 31).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk87 : ((List.drop 3255 level2).take 52).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk88 : ((List.drop 3307 level2).take 25).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk89 : ((List.drop 3332 level2).take 26).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk90 : ((List.drop 3358 level2).take 45).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk91 : ((List.drop 3403 level2).take 27).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk92 : ((List.drop 3430 level2).take 33).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk93 : ((List.drop 3463 level2).take 40).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk94 : ((List.drop 3503 level2).take 31).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk95 : ((List.drop 3534 level2).take 49).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk96 : ((List.drop 3583 level2).take 30).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem chunk97 : ((List.drop 3613 level2).take 42).all midOK = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf_tail : (List.drop 3655 level2).all midOK = true := by
  decide +kernel

theorem leaf_all : (List.drop 0 level2).all midOK = true :=
  (splitStep midOK _ 0 27 27 rfl chunk0 (splitStep midOK _ 27 33 60 rfl chunk1 (splitStep midOK _ 60 41 101 rfl chunk2 (splitStep midOK _ 101 21 122 rfl chunk3 (splitStep midOK _ 122 21 143 rfl chunk4 (splitStep midOK _ 143 29 172 rfl chunk5 (splitStep midOK _ 172 34 206 rfl chunk6 (splitStep midOK _ 206 31 237 rfl chunk7 (splitStep midOK _ 237 52 289 rfl chunk8 (splitStep midOK _ 289 29 318 rfl chunk9 (splitStep midOK _ 318 51 369 rfl chunk10 (splitStep midOK _ 369 30 399 rfl chunk11 (splitStep midOK _ 399 39 438 rfl chunk12 (splitStep midOK _ 438 41 479 rfl chunk13 (splitStep midOK _ 479 30 509 rfl chunk14 (splitStep midOK _ 509 51 560 rfl chunk15 (splitStep midOK _ 560 29 589 rfl chunk16 (splitStep midOK _ 589 50 639 rfl chunk17 (splitStep midOK _ 639 33 672 rfl chunk18 (splitStep midOK _ 672 40 712 rfl chunk19 (splitStep midOK _ 712 42 754 rfl chunk20 (splitStep midOK _ 754 32 786 rfl chunk21 (splitStep midOK _ 786 49 835 rfl chunk22 (splitStep midOK _ 835 29 864 rfl chunk23 (splitStep midOK _ 864 48 912 rfl chunk24 (splitStep midOK _ 912 31 943 rfl chunk25 (splitStep midOK _ 943 42 985 rfl chunk26 (splitStep midOK _ 985 42 1027 rfl chunk27 (splitStep midOK _ 1027 31 1058 rfl chunk28 (splitStep midOK _ 1058 51 1109 rfl chunk29 (splitStep midOK _ 1109 29 1138 rfl chunk30 (splitStep midOK _ 1138 46 1184 rfl chunk31 (splitStep midOK _ 1184 33 1217 rfl chunk32 (splitStep midOK _ 1217 37 1254 rfl chunk33 (splitStep midOK _ 1254 44 1298 rfl chunk34 (splitStep midOK _ 1298 31 1329 rfl chunk35 (splitStep midOK _ 1329 54 1383 rfl chunk36 (splitStep midOK _ 1383 28 1411 rfl chunk37 (splitStep midOK _ 1411 52 1463 rfl chunk38 (splitStep midOK _ 1463 28 1491 rfl chunk39 (splitStep midOK _ 1491 39 1530 rfl chunk40 (splitStep midOK _ 1530 41 1571 rfl chunk41 (splitStep midOK _ 1571 30 1601 rfl chunk42 (splitStep midOK _ 1601 51 1652 rfl chunk43 (splitStep midOK _ 1652 29 1681 rfl chunk44 (splitStep midOK _ 1681 50 1731 rfl chunk45 (splitStep midOK _ 1731 33 1764 rfl chunk46 (splitStep midOK _ 1764 40 1804 rfl chunk47 (splitStep midOK _ 1804 42 1846 rfl chunk48 (splitStep midOK _ 1846 32 1878 rfl chunk49 (splitStep midOK _ 1878 49 1927 rfl chunk50 (splitStep midOK _ 1927 29 1956 rfl chunk51 (splitStep midOK _ 1956 48 2004 rfl chunk52 (splitStep midOK _ 2004 31 2035 rfl chunk53 (splitStep midOK _ 2035 42 2077 rfl chunk54 (splitStep midOK _ 2077 42 2119 rfl chunk55 (splitStep midOK _ 2119 31 2150 rfl chunk56 (splitStep midOK _ 2150 51 2201 rfl chunk57 (splitStep midOK _ 2201 29 2230 rfl chunk58 (splitStep midOK _ 2230 46 2276 rfl chunk59 (splitStep midOK _ 2276 33 2309 rfl chunk60 (splitStep midOK _ 2309 37 2346 rfl chunk61 (splitStep midOK _ 2346 44 2390 rfl chunk62 (splitStep midOK _ 2390 31 2421 rfl chunk63 (splitStep midOK _ 2421 54 2475 rfl chunk64 (splitStep midOK _ 2475 28 2503 rfl chunk65 (splitStep midOK _ 2503 52 2555 rfl chunk66 (splitStep midOK _ 2555 26 2581 rfl chunk67 (splitStep midOK _ 2581 26 2607 rfl chunk68 (splitStep midOK _ 2607 44 2651 rfl chunk69 (splitStep midOK _ 2651 27 2678 rfl chunk70 (splitStep midOK _ 2678 29 2707 rfl chunk71 (splitStep midOK _ 2707 45 2752 rfl chunk72 (splitStep midOK _ 2752 29 2781 rfl chunk73 (splitStep midOK _ 2781 46 2827 rfl chunk74 (splitStep midOK _ 2827 34 2861 rfl chunk75 (splitStep midOK _ 2861 39 2900 rfl chunk76 (splitStep midOK _ 2900 44 2944 rfl chunk77 (splitStep midOK _ 2944 27 2971 rfl chunk78 (splitStep midOK _ 2971 29 3000 rfl chunk79 (splitStep midOK _ 3000 39 3039 rfl chunk80 (splitStep midOK _ 3039 29 3068 rfl chunk81 (splitStep midOK _ 3068 40 3108 rfl chunk82 (splitStep midOK _ 3108 33 3141 rfl chunk83 (splitStep midOK _ 3141 34 3175 rfl chunk84 (splitStep midOK _ 3175 49 3224 rfl chunk85 (splitStep midOK _ 3224 31 3255 rfl chunk86 (splitStep midOK _ 3255 52 3307 rfl chunk87 (splitStep midOK _ 3307 25 3332 rfl chunk88 (splitStep midOK _ 3332 26 3358 rfl chunk89 (splitStep midOK _ 3358 45 3403 rfl chunk90 (splitStep midOK _ 3403 27 3430 rfl chunk91 (splitStep midOK _ 3430 33 3463 rfl chunk92 (splitStep midOK _ 3463 40 3503 rfl chunk93 (splitStep midOK _ 3503 31 3534 rfl chunk94 (splitStep midOK _ 3534 49 3583 rfl chunk95 (splitStep midOK _ 3583 30 3613 rfl chunk96 (splitStep midOK _ 3613 42 3655 rfl chunk97 leaf_tail))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem leaf_all' : ∀ s ∈ level2, midOK s = true := by
  have h := leaf_all
  rw [List.drop_zero] at h
  exact List.all_eq_true.mp h

theorem level0_false : ∀ s ∈ level0, optimized 8 s.1 s.2 = false := by
  refine down 7 level0 clean0 (down 6 _ clean1 (down 5 _ clean2 ?_))
  intro t ht
  obtain ⟨s, hs, hts⟩ := List.mem_flatMap.mp ht
  have hs' : s ∈ level2 := hs
  have hl : midOK s = true := leaf_all' s hs'
  have ht2 := List.all_eq_true.mp hl t hts
  simpa using ht2

theorem full_search : search 8 inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws
  cases hc : (decide (ws.length ≤ 8 + 1) && (cuts ws == -1)) with
  | false => simp [hc]
  | true =>
    have hm : (8 + 1 - ws.length, ws) ∈ level0 :=
      List.mem_map.mpr ⟨ws, List.mem_filter.mpr ⟨hws, hc⟩, rfl⟩
    have := level0_false _ hm
    simp [hc, this]

theorem no_six_binary (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 8 inputs.toFinset) : False := by
  have nd : inputs.Nodup := by decide +kernel
  exact Bool.noConfusion (full_search.symm.trans (search_complete ht 8 inputs nd run))

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

theorem witness_eval : ∀ x : Fin 5 → Bool, witness.eval (List.ofFn x) = targetFun x := by
  decide

end PEqualNP.Outside.L_meta_8687

theorem PEqualNP.Outside.L_meta_8687 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xfee8e888 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xfee8e888 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_8687.binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_8687.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_8687.isBinary, op]⟩
    have bound := PEqualNP.Outside.L_meta_8687.bound_from_impossible
      8 PEqualNP.Outside.L_meta_8687.no_six_binary C.gates C.output fits computes
    refine ⟨PEqualNP.Outside.L_meta_8687.witness, PEqualNP.Outside.L_meta_8687.witness_mono,
      ?_, PEqualNP.Outside.L_meta_8687.witness_eval⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g,mem,eq⟩).elim)), cap⟩
