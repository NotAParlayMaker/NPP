import Mathlib
import PEqualNP.Defs

-- The signed live-wire search and its soundness are copied from the checked L-meta-8463
-- proof (PR 12653), which follows L-meta-1449, Apache-2.0, through L-meta-8713. Only the
-- sampled rows, the target, the witness and the layered form of the search are new: 96 pairs
-- of a true and a false assignment of the monotone target on 6 inputs, nearest pairs first,
-- rule out 7 binary gates.
namespace PEqualNP.Outside.L_meta_13307

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

-- The upper and lower halves represent opposite target labels on 96 pairs of assignments.
abbrev W := BitVec 192
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 96 := ((x >>> 96) ^^^ x).setWidth 96
def cuts (ws : List W) : BitVec 96 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 96) ++ (0 : BitVec 96)
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

def differs (i : Fin 96) (w : W) : Prop :=
  w.getLsbD (96+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 96) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 96+i.val < 192 := by omega
  have hi' : i.val < 192 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 96) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 96)[j]
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
  · change reachable av (BitVec.allOnes 192 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 192)
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

private def bit (k : Fin 192) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 192) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 192) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#192)[k.val] = false; simp
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
-- The same search in a split form: a state is refuted either by a table that covers all its
-- successors, or by a depth-first search that runs on natural-number words.
def stepStates (k : ℕ) (a b : W) (r : List W) : List (List W) :=
  (ops a b).flatMap fun z =>
    (if (sep z ||| cuts r == -1) && decide (r.length + 1 ≤ k + 1) then [z :: r] else []) ++
    ((if (sep z ||| cuts r ||| sep a == -1) && decide (r.length + 2 ≤ k + 1)
        then [z :: a :: r] else []) ++
    ((if (sep z ||| cuts r ||| sep b == -1) && decide (r.length + 2 ≤ k + 1)
        then [z :: b :: r] else []) ++
    (if (sep z ||| cuts r ||| sep a ||| sep b == -1) && decide (r.length + 3 ≤ k + 1)
        then [z :: a :: b :: r] else [])))

def expand (k : ℕ) (l : List W) : List (List W) :=
  (pairs l).flatMap fun p => stepStates k p.1 p.2.1 p.2.2

def isGoal (l : List W) : Bool := l == [goal] || l == [~~~goal]

theorem step_complete {k : ℕ} {a b z : W} {r kept : List W}
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r) (hlen : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) : (z :: kept) ∈ stepStates k a b r := by
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  have hz' : z ∈ ops a b := List.mem_toFinset.mp hz
  refine List.mem_flatMap.mpr ⟨z, hz', ?_⟩
  rcases hk with rfl | rfl | rfl | rfl
  · have e : (sep z ||| cuts kept == -1) = true := by
      rw [beq_iff_eq]; exact hc
    have e2 : decide (kept.length + 1 ≤ k + 1) = true := decide_eq_true (by omega)
    refine List.mem_append_left _ ?_
    rw [if_pos (by rw [Bool.and_eq_true]; exact ⟨e, e2⟩)]
    exact List.mem_singleton_self _
  · have e : (sep z ||| cuts r ||| sep a == -1) = true := by
      rw [beq_iff_eq, ← hc]; simp only [cuts, List.foldr_cons]; ac_rfl
    have e2 : decide (r.length + 2 ≤ k + 1) = true :=
      decide_eq_true (by simp only [List.length_cons] at hlen; omega)
    refine List.mem_append_right _ (List.mem_append_left _ ?_)
    rw [if_pos (by rw [Bool.and_eq_true]; exact ⟨e, e2⟩)]
    exact List.mem_singleton_self _
  · have e : (sep z ||| cuts r ||| sep b == -1) = true := by
      rw [beq_iff_eq, ← hc]; simp only [cuts, List.foldr_cons]; ac_rfl
    have e2 : decide (r.length + 2 ≤ k + 1) = true :=
      decide_eq_true (by simp only [List.length_cons] at hlen; omega)
    refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ ?_))
    rw [if_pos (by rw [Bool.and_eq_true]; exact ⟨e, e2⟩)]
    exact List.mem_singleton_self _
  · have e : (sep z ||| cuts r ||| sep a ||| sep b == -1) = true := by
      rw [beq_iff_eq, ← hc]; simp only [cuts, List.foldr_cons]; ac_rfl
    have e2 : decide (r.length + 3 ≤ k + 1) = true :=
      decide_eq_true (by simp only [List.length_cons] at hlen; omega)
    refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ ?_))
    rw [if_pos (by rw [Bool.and_eq_true]; exact ⟨e, e2⟩)]
    exact List.mem_singleton_self _

theorem expand_complete {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {l : List W}
    (hn : l.Nodup) {a b z : W} {needed : Finset W}
    (ha : a ∈ l.toFinset) (hb : b ∈ l.toFinset) (hab : a ≠ b) (hz : z ∈ basicOps a b)
    (hout : z ∉ l.toFinset) (hs : l.toFinset = insert a (insert b needed))
    (tail : live basicOps g k (insert z needed)) :
    ∃ c ∈ expand k l, c.Nodup ∧ live basicOps g k c.toFinset := by
  obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : W} (perm : l.Perm (a :: b :: r))
      (hset : l.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b)
      (mem : (a, b, r) ∈ pairs l) :
      ∃ c ∈ expand k l, c.Nodup ∧ live basicOps g k c.toFinset := by
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
    have hc1 := step_complete (k := k) hop hk (by omega) (cuts_full hg hl)
    exact ⟨z :: kept, List.mem_flatMap.mpr ⟨(a, b, r), mem, hc1⟩, hnd, hl⟩
  rcases hm with direct | swap
  · exact go hp hs hz direct
  · exact go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz) swap

theorem goal_stop {g : W} (hg : g = goal ∨ g = ~~~goal) {l : List W} (e : l = [g]) :
    isGoal l = true := by
  rcases hg with rfl | rfl <;> simp [isGoal, e]

def RefutedAll (k : ℕ) (t : List (List W)) : Prop :=
  ∀ l ∈ t, ∀ g, (g = goal ∨ g = ~~~goal) → l.Nodup → ¬ live basicOps g k l.toFinset

theorem refuted_append {k : ℕ} {s t : List (List W)} (hs : RefutedAll k s)
    (ht : RefutedAll k t) : RefutedAll k (s ++ t) :=
  fun l hl => (List.mem_append.mp hl).elim (hs l) (ht l)

theorem refuted_split {k : ℕ} {l : List W} {t : List (List W)} (hgoal : isGoal l = false)
    (hcov : (expand k l).all (fun c => t.contains c) = true) (ht : RefutedAll k t) :
    RefutedAll (k + 1) [l] := by
  intro l' hl' g hg hn hlive
  obtain rfl := List.mem_singleton.mp hl'
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · rw [goal_stop hg (singleton_list hn done)] at hgoal
    exact Bool.noConfusion hgoal
  · obtain ⟨c, hc, hcn, hcl⟩ := expand_complete hg hn ha hb hab hz hout hs tail
    have hin := List.all_eq_true.mp hcov c hc
    exact ht c (by simpa using hin) g hg hcn hcl

-- The copied search again, on the numbers of the words, written for the kernel.
def fsep (x : ℕ) : ℕ := Nat.mod (Nat.xor (Nat.shiftRight x 96) x) (Nat.pow 2 96)

def fcuts (l : List ℕ) : ℕ := List.rec 0 (fun w _ v => Nat.lor (fsep w) v) l

def forceB (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (f 0) (fun m _ => f (Nat.succ m)) n

theorem forceB_eq (n : ℕ) (f : ℕ → Bool) : forceB n f = f n := by
  cases n <;> rfl

def fdispatchV (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) (sa sb : ℕ)
    (w v : ℕ) : Bool :=
  ((Nat.beq v (Nat.sub (Nat.pow 2 96) 1)) && next extra (w :: r)) ||
  ((extra != 0) &&
    (((Nat.beq (Nat.lor v sa) (Nat.sub (Nat.pow 2 96) 1)) && next (extra - 1) (w :: a :: r)) ||
     ((Nat.beq (Nat.lor v sb) (Nat.sub (Nat.pow 2 96) 1)) && next (extra - 1) (w :: b :: r)))) ||
  ((decide (extra ≥ 2)) && (Nat.beq (Nat.lor (Nat.lor v sa) sb) (Nat.sub (Nat.pow 2 96) 1)) &&
    next (extra - 2) (w :: a :: b :: r))

def fdispatchW (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) (base sa sb : ℕ)
    (w : ℕ) : Bool :=
  forceB w fun w => forceB (Nat.lor (fsep w) base) (fdispatchV extra next a b r sa sb w)

def fdispatch (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) : Bool :=
  forceB extra fun extra => forceB a fun a => forceB b fun b => forceB (fcuts r) fun base =>
    forceB (fsep a) fun sa => forceB (fsep b) fun sb =>
      fdispatchW extra next a b r base sa sb (Nat.land a b) ||
      (fdispatchW extra next a b r base sa sb (Nat.lor a b) ||
      (fdispatchW extra next a b r base sa sb
        (Nat.land a (Nat.sub (Nat.sub (Nat.pow 2 192) 1) b)) ||
      fdispatchW extra next a b r base sa sb
        (Nat.land b (Nat.sub (Nat.sub (Nat.pow 2 192) 1) a))))

def fisGoal (l : List ℕ) : Bool :=
  match l with
  | [x] => Nat.beq x 6277101735386680763835789423128438253588091106870490562560 || Nat.beq x 79228162514264337593543950335
  | _ => false

def foptimized : ℕ → ℕ → List ℕ → Bool
  | 0, _, ws => fisGoal ws
  | k + 1, extra, ws => fisGoal ws ||
    (pairs ws).any (fun p => fdispatch extra (foptimized k) p.1 p.2.1 p.2.2)

theorem fsep_eq (x : W) : fsep x.toNat = (sep x).toNat := by
  simp only [fsep, sep, BitVec.toNat_setWidth, BitVec.toNat_xor, BitVec.toNat_ushiftRight]
  rfl

theorem fcuts_eq (l : List W) : fcuts (l.map BitVec.toNat) = (cuts l).toNat := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    change Nat.lor (fsep x.toNat) (fcuts (xs.map BitVec.toNat)) = (sep x ||| cuts xs).toNat
    rw [ih, fsep_eq, BitVec.toNat_or]
    rfl

theorem full_eq (v : BitVec 96) : Nat.beq v.toNat (Nat.sub (Nat.pow 2 96) 1) = (v == -1) := by
  have h : (-1 : BitVec 96).toNat = Nat.sub (Nat.pow 2 96) 1 := by decide +kernel
  rw [← h, Bool.eq_iff_iff]
  constructor
  · intro e
    exact beq_iff_eq.mpr (BitVec.toNat_inj.mp (Nat.eq_of_beq_eq_true e))
  · intro e
    rw [beq_iff_eq.mp e]
    exact Nat.beq_refl _

theorem goal_num : goal.toNat = 6277101735386680763835789423128438253588091106870490562560 ∧ (~~~goal).toNat = 79228162514264337593543950335 := by decide +kernel

theorem fisGoal_eq (l : List W) :
    fisGoal (l.map BitVec.toNat) = (l == [goal] || l == [~~~goal]) := by
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · rfl
  · change (Nat.beq x.toNat 6277101735386680763835789423128438253588091106870490562560 || Nat.beq x.toNat 79228162514264337593543950335) = ([x] == [goal] || [x] == [~~~goal])
    have t (y : W) : Nat.beq x.toNat y.toNat = ([x] == [y]) := by
      rw [Bool.eq_iff_iff]
      constructor
      · intro e
        rw [BitVec.toNat_inj.mp (Nat.eq_of_beq_eq_true e)]
        exact beq_self_eq_true _
      · intro e
        have xy : x = y := by simpa using e
        rw [xy]
        exact Nat.beq_refl _
    rw [← goal_num.1, ← goal_num.2, t, t]
  · simp [fisGoal]

theorem fdispatchW_eq (extra : ℕ) (next : ℕ → List W → Bool) (fnext : ℕ → List ℕ → Bool)
    (hnext : ∀ e l, fnext e (l.map BitVec.toNat) = next e l) (a b w : W) (r : List W) :
    fdispatchW extra fnext a.toNat b.toNat (r.map BitVec.toNat) (cuts r).toNat (sep a).toNat
      (sep b).toNat w.toNat =
    (((sep w ||| cuts r == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((sep w ||| cuts r ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((sep w ||| cuts r ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (sep w ||| cuts r ||| sep a ||| sep b == -1) &&
      next (extra - 2) (w :: a :: b :: r))) := by
  have e1 : Nat.beq (Nat.lor (fsep w.toNat) (cuts r).toNat) (Nat.sub (Nat.pow 2 96) 1) =
      (sep w ||| cuts r == -1) := by
    rw [← full_eq, fsep_eq, BitVec.toNat_or]; rfl
  have e2 : Nat.beq (Nat.lor (Nat.lor (fsep w.toNat) (cuts r).toNat) (sep a).toNat)
      (Nat.sub (Nat.pow 2 96) 1) = (sep w ||| cuts r ||| sep a == -1) := by
    rw [← full_eq, fsep_eq, BitVec.toNat_or, BitVec.toNat_or]; rfl
  have e3 : Nat.beq (Nat.lor (Nat.lor (fsep w.toNat) (cuts r).toNat) (sep b).toNat)
      (Nat.sub (Nat.pow 2 96) 1) = (sep w ||| cuts r ||| sep b == -1) := by
    rw [← full_eq, fsep_eq, BitVec.toNat_or, BitVec.toNat_or]; rfl
  have e4 : Nat.beq (Nat.lor (Nat.lor (Nat.lor (fsep w.toNat) (cuts r).toNat) (sep a).toNat)
      (sep b).toNat) (Nat.sub (Nat.pow 2 96) 1) = (sep w ||| cuts r ||| sep a ||| sep b == -1) := by
    rw [← full_eq, fsep_eq, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or]; rfl
  have n1 : fnext extra (w.toNat :: r.map BitVec.toNat) = next extra (w :: r) :=
    hnext extra (w :: r)
  have n2 : fnext (extra - 1) (w.toNat :: a.toNat :: r.map BitVec.toNat) =
      next (extra - 1) (w :: a :: r) := hnext (extra - 1) (w :: a :: r)
  have n3 : fnext (extra - 1) (w.toNat :: b.toNat :: r.map BitVec.toNat) =
      next (extra - 1) (w :: b :: r) := hnext (extra - 1) (w :: b :: r)
  have n4 : fnext (extra - 2) (w.toNat :: a.toNat :: b.toNat :: r.map BitVec.toNat) =
      next (extra - 2) (w :: a :: b :: r) := hnext (extra - 2) (w :: a :: b :: r)
  unfold fdispatchW
  rw [forceB_eq, forceB_eq]
  unfold fdispatchV
  rw [e1, e2, e3, e4, n1, n2, n3, n4]

theorem fdispatch_eq (extra : ℕ) (next : ℕ → List W → Bool) (fnext : ℕ → List ℕ → Bool)
    (hnext : ∀ e l, fnext e (l.map BitVec.toNat) = next e l) (a b : W) (r : List W) :
    fdispatch extra fnext a.toNat b.toNat (r.map BitVec.toNat) = dispatch extra next a b r := by
  have h1 : Nat.land a.toNat b.toNat = (a &&& b).toNat := (BitVec.toNat_and a b).symm
  have h2 : Nat.lor a.toNat b.toNat = (a ||| b).toNat := (BitVec.toNat_or a b).symm
  have h3 : Nat.land a.toNat (Nat.sub (Nat.sub (Nat.pow 2 192) 1) b.toNat) =
      (a &&& ~~~b).toNat := by
    rw [BitVec.toNat_and, BitVec.toNat_not]; rfl
  have h4 : Nat.land b.toNat (Nat.sub (Nat.sub (Nat.pow 2 192) 1) a.toNat) =
      (b &&& ~~~a).toNat := by
    rw [BitVec.toNat_and, BitVec.toNat_not]; rfl
  unfold fdispatch
  simp only [forceB_eq]
  rw [fcuts_eq, fsep_eq, fsep_eq, h1, h2, h3, h4,
    fdispatchW_eq extra next fnext hnext, fdispatchW_eq extra next fnext hnext,
    fdispatchW_eq extra next fnext hnext, fdispatchW_eq extra next fnext hnext]
  simp only [dispatch, ops, List.any_cons, List.any_nil, Bool.or_false]

theorem singles_map {α β : Type} (f : α → β) (l : List α) :
    singles (l.map f) = (singles l).map (fun p => (f p.1, p.2.map f)) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, singles, ih, List.map_map]
    congr 1

theorem pairs_map {α β : Type} (f : α → β) (l : List α) :
    pairs (l.map f) = (pairs l).map (fun p => (f p.1, f p.2.1, p.2.2.map f)) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, pairs, ih, singles_map, List.map_map, List.map_append]
    congr 1

theorem foptimized_eq (k extra : ℕ) (ws : List W) :
    foptimized k extra (ws.map BitVec.toNat) = optimized k extra ws := by
  induction k generalizing extra ws with
  | zero => exact fisGoal_eq ws
  | succ k ih =>
    change (fisGoal (ws.map BitVec.toNat) ||
      (pairs (ws.map BitVec.toNat)).any
        (fun p => fdispatch extra (foptimized k) p.1 p.2.1 p.2.2)) =
      ((ws == [goal] || ws == [~~~goal]) ||
        (pairs ws).any (fun p => dispatch extra (optimized k) p.1 p.2.1 p.2.2))
    rw [fisGoal_eq, pairs_map, List.any_map]
    congr 2
    funext p
    exact fdispatch_eq extra (optimized k) (foptimized k) (fun e l => ih e l) p.1 p.2.1 p.2.2

def fastAll (k : ℕ) (t : List (List W)) : Bool :=
  t.any fun l => foptimized k (k + 1 - l.length) (l.map BitVec.toNat)

theorem refuted_fast {k : ℕ} {t : List (List W)} (h : fastAll k t = false) :
    RefutedAll k t := by
  intro l hl g hg hn hlive
  have card := live_card hlive
  rw [List.toFinset_card_of_nodup hn] at card
  have run := optimized_complete hg k l (k + 1 - l.length) hn (by omega) hlive
  rw [← foptimized_eq] at run
  have all : fastAll k t = true := List.any_eq_true.mpr ⟨l, hl, run⟩
  rw [h] at all
  exact Bool.noConfusion all


def inputs : List W := [0x7dff7d5feaf5fff9ed7f6bda0000000000003c0000780000, 0x8a9b8bf45faa62aeb6c5b56d801f81fc0fe002aeb605b16c, 0xee42efec353f519e73a39ce77e007ffc001fc19e71838ce3, 0xde2186a77f7ec87e1f90fc3ffe000003ffffc07e0f807c1f, 0x87f7df9efcf9c405ff8803ff01ffffffffffc001ff8003ff, 0xbeefbe7df3e7c002007fffffffffffffffffc000007fffff]

def complementInputs : List W := inputs.map (fun w => ~~~w)

def targetFun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3937053352 * 2 ^ 32 + 3936922280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sample_rows : ∀ j : Fin 192,
    targetFun (fun i => (complementInputs.getD i.val 0)[j.val]) = (~~~goal)[j.val] := by
  decide +kernel

theorem bound_from_impossible (n : ℕ)
    (impossible : ∀ t, t = goal ∨ t = ~~~goal → build basicOps t n inputs.toFinset → False)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = targetFun x) :
    n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ complementInputs, holds inputs.toFinset u := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
    exact .inr (.inr ⟨w, List.mem_toFinset.mpr hw, .inr rfl⟩)
  have evaluate (k : Fin 192) :
      (gs.foldl step (complementInputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (complementInputs.getD i.val 0)
    have width : complementInputs.length = 6 := rfl
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

theorem inputs_nodup : inputs.Nodup := by decide +kernel

def c1 : List (List W) := [[0x7dff7d5feaf5fff9ed7f6bda0000000000003c0000780000, 0x8a9b8bf45faa62aeb6c5b56d801f81fc0fe002aeb605b16c, 0xee42efec353f519e73a39ce77e007ffc001fc19e71838ce3, 0xde2186a77f7ec87e1f90fc3ffe000003ffffc07e0f807c1f, 0x87f7df9efcf9c405ff8803ff01ffffffffffc001ff8003ff, 0xbeefbe7df3e7c002007fffffffffffffffffc000007fffff]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1_r : RefutedAll 7 c1 := refuted_fast (by decide +kernel)

def topLayer : List (List W) := inputs.sublists.filter (fun ws => cuts ws == -1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem top_cover : topLayer.all (fun c => (c1).contains c) = true := by decide +kernel

theorem no_small_binary (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 7 inputs.toFinset) : False := by
  classical
  obtain ⟨s, hs, hl⟩ := compress run
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := inputs_nodup.filter _
  have hl' : live basicOps t 7 ws.toFinset := eq.symm ▸ hl
  have hc := cuts_full ht hl'
  have mem : ws ∈ topLayer :=
    List.mem_filter.mpr ⟨List.mem_sublists.mpr (List.filter_sublist ..), by simp [hc]⟩
  have hin := List.all_eq_true.mp top_cover ws mem
  exact (c1_r) ws (by simpa using hin) t ht hnd hl'

-- An AND/OR circuit of 9 gates, found by exact search.
def witness : Circuit :=
  ⟨[⟨.and, [4, 5]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [0, 8]⟩,
    ⟨.and, [2, 9]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [0, 12]⟩,
    ⟨.or, [10, 13]⟩], 14⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

set_option maxRecDepth 100000 in
theorem witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = targetFun x := by
  decide +kernel

end PEqualNP.Outside.L_meta_13307

theorem PEqualNP.Outside.L_meta_13307 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937053352 * 2 ^ 32 + 3936922280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937053352 * 2 ^ 32 + 3936922280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_13307.binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_13307.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_13307.isBinary, op]⟩
    have bound := PEqualNP.Outside.L_meta_13307.bound_from_impossible
      7 PEqualNP.Outside.L_meta_13307.no_small_binary C.gates C.output fits computes
    refine ⟨PEqualNP.Outside.L_meta_13307.witness, PEqualNP.Outside.L_meta_13307.witness_mono,
      ?_, PEqualNP.Outside.L_meta_13307.witness_eval⟩
    change 9 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g,mem,eq⟩).elim)), cap⟩
