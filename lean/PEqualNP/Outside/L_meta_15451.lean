import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15451

-- The signed live-wire search follows L-meta-1449 and L-meta-8463, Apache-2.0.
-- Sixty pairs of a true point and a false point sample the target; with NOT gates free,
-- 8 gates of two inputs cannot separate them, so a circuit with a NOT gate has at least 10 gates.

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

-- The upper and lower halves represent opposite target labels on 60 pairs of assignments.
abbrev W := BitVec 120
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 60 := ((x >>> 60) ^^^ x).setWidth 60
def cuts (ws : List W) : BitVec 60 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 60) ++ (0 : BitVec 60)
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

def differs (i : Fin 60) (w : W) : Prop :=
  w.getLsbD (60+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 60) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 60+i.val < 120 := by omega
  have hi' : i.val < 120 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 60) :
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
  change (cuts ws)[j] = (BitVec.allOnes 60)[j]
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
  · change reachable av (BitVec.allOnes 120 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 120)
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

private def bit (k : Fin 120) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 120) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 120) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#120)[k.val] = false; simp
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
def inputs : List W := [0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff]

def complementInputs : List W := inputs.map (fun w => ~~~w)

def targetFun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3941132488 * 2 ^ 32 + 3936938120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 8000 in
theorem sample_rows : ∀ j : Fin 120,
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
  have evaluate (k : Fin 120) :
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

def tab0 : List (ℕ × List W) :=
  [(2, [0xfebdeddd7fffffffcb8e1c03ffffff, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab1 : List (ℕ × List W) :=
  [(2, [0x3e697268000000030706070000000, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab2 : List (ℕ × List W) :=
  [(2, [0x9c01000108bf24ffc000000003f00f, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab3 : List (ℕ × List W) :=
  [(2, [0x540100013f32f2a000000003800e00, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab4 : List (ℕ × List W) :=
  [(2, [0x500100011a2262afc0000003a23e3f, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab5 : List (ℕ × List W) :=
  [(2, [0x2c0825dc40449d5000001c000001c0, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab6 : List (ℕ × List W) :=
  [(2, [0x7fefb7ffff76fffff0707fff800fff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab7 : List (ℕ × List W) :=
  [(2, [0x280820d840440d5fc0001f8c0001ff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab8 : List (ℕ × List W) :=
  [(2, [0x82b4c800259900000b8e00005dc000, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab9 : List (ℕ × List W) :=
  [(1, [0xfebdeddd7fffffffcb8e1c03ffffff, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab10 : List (ℕ × List W) :=
  [(1, [0x3e697268000000030706070000000, 0x57e79727bf32f2a030706073800e00, 0xfc0100013fffffffc0000003ffffff, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab11 : List (ℕ × List W) :=
  [(2, [0xfd7b5ab3ffffffffc781830fffffff, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab12 : List (ℕ × List W) :=
  [(2, [0x180100012c34b4c000000003c3cfcc, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab13 : List (ℕ × List W) :=
  [(2, [0x16f84ec0000000007f80fc000000, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab14 : List (ℕ × List W) :=
  [(1, [0x6a485042510900000000000000000, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab15 : List (ℕ × List W) :=
  [(1, [0xfffffffffffffff03bfe7c73ddcfc0, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab16 : List (ℕ × List W) :=
  [(1, [0x14079007883220a000700070000000, 0x57e79727bf32f2a030706073800e00, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab17 : List (ℕ × List W) :=
  [(1, [0x456212229302422000000000000000, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab18 : List (ℕ × List W) :=
  [(1, [0x10031003882220afc07180fc02300f, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab19 : List (ℕ × List W) :=
  [(1, [0x7fefb7ffff76fffff0707fff800fff, 0x57e79727bf32f2a030706073800e00, 0x7c0827ffc044ffffc0007ffc000fff, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab20 : List (ℕ × List W) :=
  [(1, [0x280820d840440d5fc0001f8c0001ff, 0x57e79727bf32f2a030706073800e00, 0x7c0827ffc044ffffc0007ffc000fff, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab21 : List (ℕ × List W) :=
  [(1, [0xeffefffef7dfdf7fcf8f9f0c7df1f3, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x57e79727bf32f2a030706073800e00, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab22 : List (ℕ × List W) :=
  [(1, [0x128585052c30b08030706073800e00, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab23 : List (ℕ × List W) :=
  [(1, [0x540100013f32f2a000000003800e00, 0x57e79727bf32f2a030706073800e00, 0xfc0100013fffffffc0000003ffffff, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab24 : List (ℕ × List W) :=
  [(1, [0x500100011a2262afc0000003a23e3f, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab25 : List (ℕ × List W) :=
  [(1, [0x414212229202422fc401830c203033, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x57e79727bf32f2a030706073800e00, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab26 : List (ℕ × List W) :=
  [(1, [0x88106848408d045fc00f808c03f00f, 0x57e79727bf32f2a030706073800e00, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab27 : List (ℕ × List W) :=
  [(1, [0xfd7ffaffdbff6fffc7ff83fc3ff03f, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab28 : List (ℕ × List W) :=
  [(1, [0x82b4c800259900000b8e00005dc000, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x7c0827ffc044ffffc0007ffc000fff, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab29 : List (ℕ × List W) :=
  [(1, [0x84125802c08b003fc001800c003003, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab30 : List (ℕ × List W) :=
  [(1, [0x640802b2c0404b3fc000030c000033, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab31 : List (ℕ × List W) :=
  [(1, [0x514312239a2262a030706073800e00, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab32 : List (ℕ × List W) :=
  [(1, [0xa81868d840cd0d500b8e1c005dc1c0, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab33 : List (ℕ × List W) :=
  [(1, [0x2c0825dc40449d5000001c000001c0, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x7c0827ffc044ffffc0007ffc000fff, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab34 : List (ℕ × List W) :=
  [(1, [0x8c14e84c409d0450000e000001c000, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab35 : List (ℕ × List W) :=
  [(1, [0x9c01000108bf24ffc000000003f00f, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab36 : List (ℕ × List W) :=
  [(1, [0x43e007203700d20030006003800e00, 0x57e79727bf32f2a030706073800e00, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab37 : List (ℕ × List W) :=
  [(1, [0x1805a04d083424c0007e00f003c00c, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab38 : List (ℕ × List W) :=
  [(1, [0x22a80590254099000b801c005c01c0, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab39 : List (ℕ × List W) :=
  [(1, [0x16f84ec0000000007f80fc000000, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab40 : List (ℕ × List W) :=
  [(1, [0xfd7b5ab3ffffffffc781830fffffff, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab41 : List (ℕ × List W) :=
  [(1, [0xdff7ff6fffbff6fff07fe0ff83fe0f, 0x57e79727bf32f2a030706073800e00, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab42 : List (ℕ × List W) :=
  [(1, [0x180100012c34b4c000000003c3cfcc, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab43 : List (ℕ × List W) :=
  [(1, [0xbebffddfedffbdffcbff9cfc5ff1cf, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab44 : List (ℕ × List W) :=
  [(1, [0xfc1fffffc8ffffffc07ffffc03ffff, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0xfc0100013fffffffc0000003ffffff])]

def tab45 : List (ℕ × List W) :=
  [(1, [0x616802b013404b00078003003c0030, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab46 : List (ℕ × List W) :=
  [(1, [0x81725800138b0000078180003c3000, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab47 : List (ℕ × List W) :=
  [(1, [0x600807b00040db0000007f00000ff0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0xfc0100013fffffffc0000003ffffff])]

def tab48 : List (ℕ × List W) :=
  [(1, [0xa84a54c24149440080e1c0041c1c0, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x57e79727bf32f2a030706073800e00, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab49 : List (ℕ × List W) :=
  [(1, [0x2bceddc400000000b8e1c00000000, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab50 : List (ℕ × List W) :=
  [(1, [0xffe79727bffffffff0706073ffffff, 0x57e79727bf32f2a030706073800e00, 0xfc0100013fffffffc0000003ffffff, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab51 : List (ℕ × List W) :=
  [(1, [0xa018489040c9091fc781830c3c3033, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab52 : List (ℕ × List W) :=
  [(1, [0x540007278000f2a000006070000e00, 0x57e79727bf32f2a030706073800e00, 0x7c0827ffc044ffffc0007ffc000fff, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab53 : List (ℕ × List W) :=
  [(1, [0x3e790003f32000030700003800000, 0x57e79727bf32f2a030706073800e00, 0x7c0827ffc044ffffc0007ffc000fff, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab54 : List (ℕ × List W) :=
  [(1, [0x600000003740db0000000003fc0ff0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab55 : List (ℕ × List W) :=
  [(1, [0xfd7a7fffd3cfffffc781fffc3c3fff, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab56 : List (ℕ × List W) :=
  [(1, [0xa800000000cd0d5fc00000007ff1ff, 0x57e79727bf32f2a030706073800e00, 0xfc0100013fffffffc0000003ffffff, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab57 : List (ℕ × List W) :=
  [(1, [0xf7ffdfb7fffbfbbff7f1e37fbc3e33, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab58 : List (ℕ × List W) :=
  [(1, [0xac00000025dd9d50000000005dc1c0, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab59 : List (ℕ × List W) :=
  [(1, [0xa438489041c90910038000001c0000, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x57e79727bf32f2a030706073800e00, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff])]

def tab60 : List (ℕ × List W) :=
  [(1, [0x1c00204fc00424ffc00000fc00000f, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0xfc0100013fffffffc0000003ffffff])]

def tab61 : List (ℕ × List W) :=
  [(1, [0xfc17f84fffffffffc07f80ffffffff, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab62 : List (ℕ × List W) :=
  [(1, [0x1800254d0004b4c000007cf0000fcc, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x7c0827ffc044ffffc0007ffc000fff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff]),
   (1, [0x17a5ab2c00000000781830c000000, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff])]

def tab63 : List (ℕ × List W) :=
  [(1, [0xe400000013cb4b3fc00000003c3033, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff]),
   (1, [0x50000223800062afc00063fc000e3f, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x7c0827ffc044ffffc0007ffc000fff, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab64 : List (ℕ × List W) :=
  [(1, [0x8017d80008bb0000007f800003f000, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0x7c0827ffc044ffffc0007ffc000fff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0xfc0100013fffffffc0000003ffffff]),
   (1, [0xfebcefffe5ddffffcb8e7ffc5dcfff, 0xaebceddc65dd9d500b8e1c005dc1c0, 0x7c0827ffc044ffffc0007ffc000fff, 0x57e79727bf32f2a030706073800e00, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f, 0xfc0100013fffffffc0000003ffffff])]

def tab65 : List (ℕ × List W) :=
  [(1, [0x7c0000010044ffffc0000000000fff, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f]),
   (1, [0xfc0927ffffffffffc0007fffffffff, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f])]

def tab66 : List (ℕ × List W) :=
  [(1, [0x827fec000000000007ffc000000, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f]),
   (1, [0x800100003fbb000000000003fff000, 0x7c0827ffc044ffffc0007ffc000fff, 0xfc0100013fffffffc0000003ffffff, 0x57e79727bf32f2a030706073800e00, 0xaebceddc65dd9d500b8e1c005dc1c0, 0xe57a5ab2d3cb4b3fc781830c3c3033, 0x9c17f84fc8bf24ffc07f80fc03f00f])]

def table : List (ℕ × List W) := tab0 ++ tab1 ++ tab2 ++ tab3 ++ tab4 ++ tab5 ++ tab6 ++ tab7 ++ tab8 ++ tab9 ++ tab10 ++ tab11 ++ tab12 ++ tab13 ++ tab14 ++ tab15 ++ tab16 ++ tab17 ++ tab18 ++ tab19 ++ tab20 ++ tab21 ++ tab22 ++ tab23 ++ tab24 ++ tab25 ++ tab26 ++ tab27 ++ tab28 ++ tab29 ++ tab30 ++ tab31 ++ tab32 ++ tab33 ++ tab34 ++ tab35 ++ tab36 ++ tab37 ++ tab38 ++ tab39 ++ tab40 ++ tab41 ++ tab42 ++ tab43 ++ tab44 ++ tab45 ++ tab46 ++ tab47 ++ tab48 ++ tab49 ++ tab50 ++ tab51 ++ tab52 ++ tab53 ++ tab54 ++ tab55 ++ tab56 ++ tab57 ++ tab58 ++ tab59 ++ tab60 ++ tab61 ++ tab62 ++ tab63 ++ tab64 ++ tab65 ++ tab66

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf0 : tab0.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf1 : tab1.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf2 : tab2.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf3 : tab3.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf4 : tab4.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf5 : tab5.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf6 : tab6.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf7 : tab7.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf8 : tab8.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf9 : tab9.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf10 : tab10.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf11 : tab11.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf12 : tab12.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf13 : tab13.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf14 : tab14.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf15 : tab15.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf16 : tab16.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf17 : tab17.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf18 : tab18.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf19 : tab19.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf20 : tab20.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf21 : tab21.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf22 : tab22.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf23 : tab23.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf24 : tab24.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf25 : tab25.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf26 : tab26.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf27 : tab27.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf28 : tab28.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf29 : tab29.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf30 : tab30.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf31 : tab31.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf32 : tab32.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf33 : tab33.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf34 : tab34.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf35 : tab35.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf36 : tab36.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf37 : tab37.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf38 : tab38.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf39 : tab39.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf40 : tab40.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf41 : tab41.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf42 : tab42.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf43 : tab43.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf44 : tab44.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf45 : tab45.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf46 : tab46.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf47 : tab47.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf48 : tab48.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf49 : tab49.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf50 : tab50.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf51 : tab51.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf52 : tab52.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf53 : tab53.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf54 : tab54.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf55 : tab55.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf56 : tab56.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf57 : tab57.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf58 : tab58.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf59 : tab59.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf60 : tab60.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf61 : tab61.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf62 : tab62.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf63 : tab63.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf64 : tab64.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf65 : tab65.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf66 : tab66.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  decide +kernel

theorem leaf_all : table.all (fun c => !(optimized 7 c.1 c.2)) = true := by
  simp only [table, List.all_append, leaf0, leaf1, leaf2, leaf3, leaf4, leaf5, leaf6, leaf7, leaf8, leaf9, leaf10, leaf11, leaf12, leaf13, leaf14, leaf15, leaf16, leaf17, leaf18, leaf19, leaf20, leaf21, leaf22, leaf23, leaf24, leaf25, leaf26, leaf27, leaf28, leaf29, leaf30, leaf31, leaf32, leaf33, leaf34, leaf35, leaf36, leaf37, leaf38, leaf39, leaf40, leaf41, leaf42, leaf43, leaf44, leaf45, leaf46, leaf47, leaf48, leaf49, leaf50, leaf51, leaf52, leaf53, leaf54, leaf55, leaf56, leaf57, leaf58, leaf59, leaf60, leaf61, leaf62, leaf63, leaf64, leaf65, leaf66, Bool.and_self]

def optT (e : ℕ) (ws : List W) : Bool := if (e, ws) ∈ table then false else optimized 7 e ws

theorem optT_eq : optT = optimized 7 := by
  funext e ws
  unfold optT
  split_ifs with h
  · have hc := List.all_eq_true.mp leaf_all _ h
    dsimp only at hc
    revert hc
    cases optimized 7 e ws <;> simp
  · rfl

def optRoot (e : ℕ) (ws : List W) : Bool :=
  (ws == [goal] || ws == [~~~goal]) || (pairs ws).any (fun (a, b, r) => dispatch e optT a b r)

theorem optRoot_eq : optRoot = optimized 8 := by
  funext e ws
  simp only [optRoot, optT_eq, optimized]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem all_front : inputs.sublists.all
    (fun l => decide (9 < l.length) || (cuts l != -1) || !(optRoot (9 - l.length) l)) = true := by
  decide +kernel

theorem search_none : search 8 inputs = false := by
  cases hs : search 8 inputs with
  | false => rfl
  | true =>
    obtain ⟨ws, hmem, hws⟩ := List.any_eq_true.mp hs
    have hrow := List.all_eq_true.mp all_front ws hmem
    rw [optRoot_eq] at hrow
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hws
    obtain ⟨⟨hlen, hcut⟩, hopt⟩ := hws
    simp [hopt, hcut, Nat.not_lt.mpr hlen] at hrow

theorem no_small_binary (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 8 inputs.toFinset) : False :=
  Bool.noConfusion (search_none.symm.trans (search_complete ht 8 inputs (by decide) run))

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [6, 2]⟩, ⟨.and, [7, 3]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [10, 1]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [12, 0]⟩, ⟨.and, [13, 11]⟩, ⟨.or, [14, 8]⟩], 15⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

theorem witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = targetFun x := by
  decide +kernel

end PEqualNP.Outside.L_meta_15451

theorem PEqualNP.Outside.L_meta_15451 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132488 * 2 ^ 32 + 3936938120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132488 * 2 ^ 32 + 3936938120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_15451.binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_15451.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_15451.isBinary, op]⟩
    have bound := PEqualNP.Outside.L_meta_15451.bound_from_impossible
      8 PEqualNP.Outside.L_meta_15451.no_small_binary C.gates C.output fits computes
    refine ⟨PEqualNP.Outside.L_meta_15451.witness, PEqualNP.Outside.L_meta_15451.witness_mono,
      ?_, PEqualNP.Outside.L_meta_15451.witness_eval⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g,mem,eq⟩).elim)), cap⟩
