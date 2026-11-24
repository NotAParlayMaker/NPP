import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1449_aux

-- The live-wire compression argument follows the project proof of L-meta-703.
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
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
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

open PEqualNP.CircuitLowerBounds

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
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#512)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

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
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
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
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
theorem bound_from_search (T n : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 512, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : search n ins = false)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 512) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 5) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (ins.map (bit k)) = bit k goal
    rw [← same, he]
    exact row k
  obtain ⟨t,ht,run⟩ := compile gs o hg ins ins.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins.toFinset) : build basicOps t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  have found := search_complete ht n ins nd (lift low run)
  exact Bool.noConfusion (rejection.symm.trans found)

theorem replace (T m : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 512, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : search (m-2) ins = false)
    (upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ gs.length = m ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) :
    ∃ (ds : List Gate) (p : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ ds.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨ds,p⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hm,hn⟩ := present
    have cut : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g,hm,by simp [isBinary, hn]⟩
    have b := bound_from_search T (m-2) ins nd row width rejection gs o hg he
    obtain ⟨ds,p,ok,size,ev⟩ := upper
    exact ⟨ds,p,ok,by omega,ev⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hm
    obtain ⟨hop,cap⟩ := hg g hm
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g,hm,eq⟩).elim)),cap⟩
def ins_feeefeea : List W := [0xffffffffffffffffffffff01fc07f01fff80fffc07ffe03f80fe03fff01fffff0000000000000000000000000000000000000000000000000000000000000000, 0xfffffffffffffffffffffffe0007ffe03fff01fff80fffc000fffc07ffe03f800000000000000000000002040810204081020408102040810204081020408102, 0xfffffffffffffffffffffffffff800003ffffe00000fffffff000007ffffc0000000000000000000000024489122448912244891224489122448912244891224, 0xffffffffffffffffffffffffffffffffc0000000000ffffffffffff800000000ffffffffffffffffffffc8912244891224489122448912244891224489122448, 0xfffffffffffffffffffffffffffffffffffffffffff000000000000000000000fffffffffffffffffffff0e1c3870e1c3870e1c3870e1c3870e1c3870e1c3870]

theorem nd_feeefeea : ins_feeefeea.Nodup := by decide +kernel

theorem spec_feeefeea : ∀ j : Fin 512, Nat.testBit 0xfeeefeea (∑ i : Fin 5, if (ins_feeefeea.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_feeefeea : search 4 ins_feeefeea = false := by decide +kernel

def gates_feeefeea : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [2, 3]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [6, 9]⟩]

theorem upper_feeefeea : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfeeefeea (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_feeefeea, 10, ?_, rfl, ?_⟩
  · simp [gates_feeefeea]
  · decide +kernel

def ins_fefefeaa : List W := [0xffffffffffffffffffffff01fc07f01fff80fe03f80fffc07f01fc07ffffffff0000000000000000000000000000000000000000000000000000000000000000, 0xfffffffffffffffffffffffe0007ffe03fff0003fff01fff8001fff80fe03f80000000000000000000000a142850a142850a142850a142850a142850a142850a, 0xfffffffffffffffffffffffffff800003ffffffc00001ffffffe00000fffc000000000000000000000000c183060c183060c183060c183060c183060c183060c, 0xffffffffffffffffffffffffffffffffc000000000001ffffffffffff0000000ffffffffffffffffffffd0a142850a142850a142850a142850a142850a142850, 0xffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000ffffffffffffffffffffe0c183060c183060c183060c183060c183060c183060]

theorem nd_fefefeaa : ins_fefefeaa.Nodup := by decide +kernel

theorem spec_fefefeaa : ∀ j : Fin 512, Nat.testBit 0xfefefeaa (∑ i : Fin 5, if (ins_fefefeaa.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_fefefeaa : search 2 ins_fefefeaa = false := by decide +kernel

def gates_fefefeaa : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [3, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [0, 7]⟩]

theorem upper_fefefeaa : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfefefeaa (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_fefefeaa, 8, ?_, rfl, ?_⟩
  · simp [gates_fefefeaa]
  · decide +kernel

def ins_fefefee8 : List W := [0xffffffffffffffffffffff01fc07f01fff80fe03f80fffc07f01fc07ffe03fff0000000000000000000002040810204081020408102040810204081020408102, 0xfffffffffffffffffffffffe0007ffe03fff0003fff01fff8001fff80fffc07f0000000000000000000004081020408102040810204081020408102040810204, 0xfffffffffffffffffffffffffff800003ffffffc00001ffffffe00000fffff800000000000000000000008102040810204081020408102040810204081020408, 0xffffffffffffffffffffffffffffffffc000000000001ffffffffffff0000000ffffffffffffffffffffd0a142850a142850a142850a142850a142850a142850, 0xffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000ffffffffffffffffffffe0c183060c183060c183060c183060c183060c183060]

theorem nd_fefefee8 : ins_fefefee8.Nodup := by decide +kernel

theorem spec_fefefee8 : ∀ j : Fin 512, Nat.testBit 0xfefefee8 (∑ i : Fin 5, if (ins_fefefee8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_fefefee8 : search 6 ins_fefefee8 = false := by decide +kernel

def gates_fefefee8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [0, 2]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [5, 11]⟩]

theorem upper_fefefee8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfefefee8 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_fefefee8, 12, ?_, rfl, ?_⟩
  · simp [gates_fefefee8]
  · decide +kernel

def ins_fefefeea : List W := [0xffffffffffffffffffffffffffc0fc0fc0fff03f03f03ffc0fc0fc0fff03ffff0000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffff000fff03ffc003ffc0fff000fff03ffc0fc00000000000000000000000000082082082082082082082082082082082082082, 0xfffffffffffffffffffffffffffffff00003fffffc0000ffffff00003ffff0000000000000000000000000000104104104104104104104104104104104104104, 0xfffffffffffffffffffffffffffffffffffc0000000000ffffffffffc0000000fffffffffffffffffffffffffa28a28a28a28a28a28a28a28a28a28a28a28a28, 0xffffffffffffffffffffffffffffffffffffffffffffff000000000000000000fffffffffffffffffffffffffc30c30c30c30c30c30c30c30c30c30c30c30c30]

theorem nd_fefefeea : ins_fefefeea.Nodup := by decide +kernel

theorem spec_fefefeea : ∀ j : Fin 512, Nat.testBit 0xfefefeea (∑ i : Fin 5, if (ins_fefefeea.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_fefefeea : search 4 ins_fefefeea = false := by decide +kernel

def gates_fefefeea : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [3, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [8, 9]⟩]

theorem upper_fefefeea : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfefefeea (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_fefefeea, 10, ?_, rfl, ?_⟩
  · simp [gates_fefefeea]
  · decide +kernel

def ins_fffefee8 : List W := [0xffffffffffffffffffffffffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff0000000000000000000000000082082082082082082082082082082082082082, 0xffffffffffffffffffffffffffff000fff000fff000fff03ffc003ffc0fff03f0000000000000000000000000104104104104104104104104104104104104104, 0xfffffffffffffffffffffffffffffff000000ffffff00003fffffc0000ffffc00000000000000000000000000208208208208208208208208208208208208208, 0xfffffffffffffffffffffffffffffffffffff00000000003ffffffffff0000000000000000000000000000000410410410410410410410410410410410410410, 0xfffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000fffffffffffffffffffffffff820820820820820820820820820820820820820]

theorem nd_fffefee8 : ins_fffefee8.Nodup := by decide +kernel

theorem spec_fffefee8 : ∀ j : Fin 512, Nat.testBit 0xfffefee8 (∑ i : Fin 5, if (ins_fffefee8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_fffefee8 : search 8 ins_fffefee8 = false := by decide +kernel

def gates_fffefee8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [1, 4]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [9, 11]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [12, 13]⟩]

theorem upper_fffefee8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 10 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfffefee8 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_fffefee8, 14, ?_, rfl, ?_⟩
  · simp [gates_fffefee8]
  · decide +kernel

def ins_fefefeee : List W := [0xfffffffffffffffffffffffffffffffc1f07c1ff83e0f83ff07c1f07fe0ffc1f0000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffe007fe0ffc00ffc1ff801ff83ff07fe00000000000000000000000000000000000000000000000000000000000000000, 0xfffffffffffffffffffffffffffffffffff8000fffff0001ffffe0003fff80000000000000000000000000000000000842108421084210842108421084210842, 0xfffffffffffffffffffffffffffffffffffffff000000001ffffffffc0000000ffffffffffffffffffffffffffffffd294a5294a5294a5294a5294a5294a5294, 0xfffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000ffffffffffffffffffffffffffffffe318c6318c6318c6318c6318c6318c6318]

theorem nd_fefefeee : ins_fefefeee.Nodup := by decide +kernel

theorem spec_fefefeee : ∀ j : Fin 512, Nat.testBit 0xfefefeee (∑ i : Fin 5, if (ins_fefefeee.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_fefefeee : search 2 ins_fefefeee = false := by decide +kernel

def gates_fefefeee : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [3, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [6, 7]⟩]

theorem upper_fefefeee : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfefefeee (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_fefefeee, 8, ?_, rfl, ?_⟩
  · simp [gates_fefefeee]
  · decide +kernel

def ins_fffefeea : List W := [0xfffffffffffffffffffffffffffffffc1f07c1f07c1f07c1ff83e0f83ff07fff0000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffe007fe007fe007fe0ffc00ffc1ff83e00000000000000000000000000000000842108421084210842108421084210842, 0xfffffffffffffffffffffffffffffffffff800007ffff8000fffff0001fffc000000000000000000000000000000001084210842108421084210842108421084, 0xffffffffffffffffffffffffffffffffffffffff800000000ffffffffe0000000000000000000000000000000000002108421084210842108421084210842108, 0xfffffffffffffffffffffffffffffffffffffffffffffffff000000000000000ffffffffffffffffffffffffffffffc210842108421084210842108421084210]

theorem nd_fffefeea : ins_fffefeea.Nodup := by decide +kernel

theorem spec_fffefeea : ∀ j : Fin 512, Nat.testBit 0xfffefeea (∑ i : Fin 5, if (ins_fffefeea.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_fffefeea : search 6 ins_fffefeea = false := by decide +kernel

def gates_fffefeea : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [2, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [0, 11]⟩]

theorem upper_fffefeea : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfffefeea (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_fffefeea, 12, ?_, rfl, ?_⟩
  · simp [gates_fffefeea]
  · decide +kernel

def ins_fffefeee : List W := [0xfffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0ff0f0f0ff0ff0f0000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffff00ff00ff00ff0ff00ff0ff0ff00000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000ffff000ffff000fff0000000000000000000000000000000000000002222222222222222222222222222, 0xffffffffffffffffffffffffffffffffffffffffffff0000000fffffff0000000000000000000000000000000000000000004444444444444444444444444444, 0xfffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000ffffffffffffffffffffffffffffffffffff8888888888888888888888888888]

theorem nd_fffefeee : ins_fffefeee.Nodup := by decide +kernel

theorem spec_fffefeee : ∀ j : Fin 512, Nat.testBit 0xfffefeee (∑ i : Fin 5, if (ins_fffefeee.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_fffefeee : search 4 ins_fffefeee = false := by decide +kernel

def gates_fffefeee : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [8, 9]⟩]

theorem upper_fffefeee : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfffefeee (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_fffefeee, 10, ?_, rfl, ?_⟩
  · simp [gates_fffefeee]
  · decide +kernel

def ins_fffefefe : List W := [0xfffffffffffffffffffffffffffffffffffffffffff1c71c71c71f8e38fc71c70000000000000000000000000000000000000000000000000000000000000000, 0xfffffffffffffffffffffffffffffffffffffffffffe07e07e07e3f03f1f81f80000000000000000000000000000000000000000000000000000000000000000, 0xfffffffffffffffffffffffffffffffffffffffffffff8007ff803ffc01ffe000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffff800003ffffe000000000000000000000000000000000000000000000002492492492492492492492, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000ffffffffffffffffffffffffffffffffffffffffffc924924924924924924924]

theorem nd_fffefefe : ins_fffefefe.Nodup := by decide +kernel

theorem spec_fffefefe : ∀ j : Fin 512, Nat.testBit 0xfffefefe (∑ i : Fin 5, if (ins_fffefefe.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_fffefefe : search 2 ins_fffefefe = false := by decide +kernel

def gates_fffefefe : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [6, 7]⟩]

theorem upper_fffefefe : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfffefefe (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_fffefefe, 8, ?_, rfl, ?_⟩
  · simp [gates_fffefefe]
  · decide +kernel

def ins_fffffffe : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffd55555550000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffe66666660000000000000000000000000000000000000000000000000000000000000000, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffff87878780000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff807f800000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000000000000000000000000000000]

theorem nd_fffffffe : ins_fffffffe.Nodup := by decide +kernel

theorem spec_fffffffe : ∀ j : Fin 512, Nat.testBit 0xfffffffe (∑ i : Fin 5, if (ins_fffffffe.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_fffffffe : search 2 ins_fffffffe = false := by decide +kernel

def gates_fffffffe : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [6, 7]⟩]

theorem upper_fffffffe : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfffffffe (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_fffffffe, 8, ?_, rfl, ?_⟩
  · simp [gates_fffffffe]
  · decide +kernel

end PEqualNP.Outside.L_meta_1449_aux

open PEqualNP.Outside.L_meta_1449_aux

set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.L_meta_1449 : ∀ T ∈ ({0xfeeefeea, 0xfefefeaa, 0xfefefee8, 0xfefefeea, 0xfffefee8, 0xfefefeee, 0xfffefeea, 0xfffefeee, 0xfffefefe, 0xfffffffe} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T mem gs o hg _ he
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact replace 0xfeeefeea 6 ins_feeefeea nd_feeefeea spec_feeefeea rfl reject_feeefeea upper_feeefeea gs o hg he
  · exact replace 0xfefefeaa 4 ins_fefefeaa nd_fefefeaa spec_fefefeaa rfl reject_fefefeaa upper_fefefeaa gs o hg he
  · exact replace 0xfefefee8 8 ins_fefefee8 nd_fefefee8 spec_fefefee8 rfl reject_fefefee8 upper_fefefee8 gs o hg he
  · exact replace 0xfefefeea 6 ins_fefefeea nd_fefefeea spec_fefefeea rfl reject_fefefeea upper_fefefeea gs o hg he
  · exact replace 0xfffefee8 10 ins_fffefee8 nd_fffefee8 spec_fffefee8 rfl reject_fffefee8 upper_fffefee8 gs o hg he
  · exact replace 0xfefefeee 4 ins_fefefeee nd_fefefeee spec_fefefeee rfl reject_fefefeee upper_fefefeee gs o hg he
  · exact replace 0xfffefeea 8 ins_fffefeea nd_fffefeea spec_fffefeea rfl reject_fffefeea upper_fffefeea gs o hg he
  · exact replace 0xfffefeee 6 ins_fffefeee nd_fffefeee spec_fffefeee rfl reject_fffefeee upper_fffefeee gs o hg he
  · exact replace 0xfffefefe 4 ins_fffefefe nd_fffefefe spec_fffefefe rfl reject_fffefefe upper_fffefefe gs o hg he
  · exact replace 0xfffffffe 4 ins_fffffffe nd_fffffffe spec_fffffffe rfl reject_fffffffe upper_fffffffe gs o hg he
