import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1439_aux

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
def ins_eaeaeae8 : List W := [0xfffffc001ffffffffffffe000fffffffffffff0007ffffffffffff8003ffffff0000080040020010008004002001000800400200100080040020010008004002, 0xffffffffe000fff8003ffffff0007ffc001ffffff8003ffe000ffffffc001fff0024912489244922491248924492249124892449224912489244922491248924, 0xffffffffffff0000003fffffffff8000001fffffffffc000000fffffffffe000ffc9224912489244922491248924492249124892449224912489244922491248, 0xffffffffffffffffffc0000000000000001ffffffffffffffff0000000000000fff1c38e1c70e3871c38e1c70e3871c38e1c70e3871c38e1c70e3871c38e1c70, 0xffffffffffffffffffffffffffffffffffe00000000000000000000000000000fffe03f01f80fc07e03f01f80fc07e03f01f80fc07e03f01f80fc07e03f01f80]

theorem nd_eaeaeae8 : ins_eaeaeae8.Nodup := by decide +kernel

theorem spec_eaeaeae8 : ∀ j : Fin 512, Nat.testBit 0xeaeaeae8 (∑ i : Fin 5, if (ins_eaeaeae8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eaeaeae8 : search 4 ins_eaeaeae8 = false := by decide +kernel

def gates_eaeaeae8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [1, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [8, 9]⟩]

theorem upper_eaeaeae8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeaeaeae8 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_eaeaeae8, 10, ?_, rfl, ?_⟩
  · simp [gates_eaeaeae8]
  · decide +kernel

def ins_eee8eae8 : List W := [0xfffffc001ffffff8003ffffff0007fffffffff0007ffffffffffff8003ffffff0004082041020810408204102081040820410208104082041020810408204102, 0xffffffffe000ffffffc001ffffff8003fffffffff8003ffe000ffffffc001fff0008904482241120890448224112089044822411208904482241120890448224, 0xffffffffffff0000000001fffffffffc001fffffffffc000000fffffffffe000ffd122891448a245122891448a245122891448a245122891448a245122891448, 0xfffffffffffffffffffffe0000000000001ffffffffffffffff0000000000000ffe1c30e1870c3861c30e1870c3861c30e1870c3861c30e1870c3861c30e1870, 0xffffffffffffffffffffffffffffffffffe00000000000000000000000000000fffe03f01f80fc07e03f01f80fc07e03f01f80fc07e03f01f80fc07e03f01f80]

theorem nd_eee8eae8 : ins_eee8eae8.Nodup := by decide +kernel

theorem spec_eee8eae8 : ∀ j : Fin 512, Nat.testBit 0xeee8eae8 (∑ i : Fin 5, if (ins_eee8eae8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eee8eae8 : search 5 ins_eee8eae8 = false := by decide +kernel

def gates_eee8eae8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [1, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [7, 10]⟩]

theorem upper_eee8eae8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 7 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeee8eae8 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_eee8eae8, 11, ?_, rfl, ?_⟩
  · simp [gates_eee8eae8]
  · decide +kernel

def ins_eee8eee0 : List W := [0xfffffc001ffffff8003ffffff0007fffffffff0007fffffe000ffffffc001fff00042821410a085042821410a085042821410a085042821410a085042821410a, 0xffffffffe000ffffffc001ffffff8003fffffffff8003ffffff0007fffffe00000083041820c106083041820c106083041820c106083041820c106083041820c, 0xffffffffffff0000000001fffffffffc001fffffffffc0000000007fffffffffffd1428a1450a2851428a1450a2851428a1450a2851428a1450a2851428a1450, 0xfffffffffffffffffffffe0000000000001fffffffffffffffffff8000000000ffe1830c1860c3061830c1860c3061830c1860c3061830c1860c3061830c1860, 0xffffffffffffffffffffffffffffffffffe00000000000000000000000000000fffe03f01f80fc07e03f01f80fc07e03f01f80fc07e03f01f80fc07e03f01f80]

theorem nd_eee8eee0 : ins_eee8eee0.Nodup := by decide +kernel

theorem spec_eee8eee0 : ∀ j : Fin 512, Nat.testBit 0xeee8eee0 (∑ i : Fin 5, if (ins_eee8eee0.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eee8eee0 : search 4 ins_eee8eee0 = false := by decide +kernel

def gates_eee8eee0 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [7, 9]⟩]

theorem upper_eee8eee0 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeee8eee0 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_eee8eee0, 10, ?_, rfl, ?_⟩
  · simp [gates_eee8eee0]
  · decide +kernel

def ins_eeeaeaa8 : List W := [0xfffffc001ffffff8003ffffff0007ffffffffffff8003fffffffffffffffffff0000080040020010008004002001000800400200100080040020010008004002, 0xffffffffe000ffffffc001ffffff8003ffe000ffffffc001fff0007ffc001fff0009504a825412a09504a825412a09504a825412a09504a825412a09504a8254, 0xffffffffffff0000000001fffffffffc000000fffffffffe0000007fffffe000ffd262931498a4c5262931498a4c5262931498a4c5262931498a4c5262931498, 0xfffffffffffffffffffffe0000000000000000ffffffffffffffff8000000000ffe3831c18e0c7063831c18e0c7063831c18e0c7063831c18e0c7063831c18e0, 0xffffffffffffffffffffffffffffffffffffff00000000000000000000000000fffc03e01f00f807c03e01f00f807c03e01f00f807c03e01f00f807c03e01f00]

theorem nd_eeeaeaa8 : ins_eeeaeaa8.Nodup := by decide +kernel

theorem spec_eeeaeaa8 : ∀ j : Fin 512, Nat.testBit 0xeeeaeaa8 (∑ i : Fin 5, if (ins_eeeaeaa8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eeeaeaa8 : search 7 ins_eeeaeaa8 = false := by decide +kernel

def gates_eeeaeaa8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [3, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [11, 12]⟩]

theorem upper_eeeaeaa8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeeeaeaa8 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_eeeaeaa8, 13, ?_, rfl, ?_⟩
  · simp [gates_eeeaeaa8]
  · decide +kernel

def ins_eeeaeac8 : List W := [0xfffffc001ffffff8003ffffff0007ffffffffffff8003ffffffffffffc001fff0000480240120090048024012009004802401200900480240120090048024012, 0xffffffffe000ffffffc001ffffff8003ffe000ffffffc001fff0007fffffffff0009104882441220910488244122091048824412209104882441220910488244, 0xffffffffffff0000000001fffffffffc000000fffffffffe0000007fffffe000ffd262931498a4c5262931498a4c5262931498a4c5262931498a4c5262931498, 0xfffffffffffffffffffffe0000000000000000ffffffffffffffff8000000000ffe3831c18e0c7063831c18e0c7063831c18e0c7063831c18e0c7063831c18e0, 0xffffffffffffffffffffffffffffffffffffff00000000000000000000000000fffc03e01f00f807c03e01f00f807c03e01f00f807c03e01f00f807c03e01f00]

theorem nd_eeeaeac8 : ins_eeeaeac8.Nodup := by decide +kernel

theorem spec_eeeaeac8 : ∀ j : Fin 512, Nat.testBit 0xeeeaeac8 (∑ i : Fin 5, if (ins_eeeaeac8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eeeaeac8 : search 5 ins_eeeaeac8 = false := by decide +kernel

def gates_eeeaeac8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [3, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [7, 10]⟩]

theorem upper_eeeaeac8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 7 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeeeaeac8 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_eeeaeac8, 11, ?_, rfl, ?_⟩
  · simp [gates_eeeaeac8]
  · decide +kernel

def ins_eeeaeae0 : List W := [0xfffffc001ffffff8003ffffff0007ffffffffffff8003ffffffffffffc001fff00002801400a005002801400a005002801400a005002801400a005002801400a, 0xffffffffe000ffffffc001ffffff8003ffe000ffffffc001fff0007fffffe00000093049824c126093049824c126093049824c126093049824c126093049824c, 0xffffffffffff0000000001fffffffffc000000fffffffffe0000007fffffffffffd242921490a485242921490a485242921490a485242921490a485242921490, 0xfffffffffffffffffffffe0000000000000000ffffffffffffffff8000000000ffe3831c18e0c7063831c18e0c7063831c18e0c7063831c18e0c7063831c18e0, 0xffffffffffffffffffffffffffffffffffffff00000000000000000000000000fffc03e01f00f807c03e01f00f807c03e01f00f807c03e01f00f807c03e01f00]

theorem nd_eeeaeae0 : ins_eeeaeae0.Nodup := by decide +kernel

theorem spec_eeeaeae0 : ∀ j : Fin 512, Nat.testBit 0xeeeaeae0 (∑ i : Fin 5, if (ins_eeeaeae0.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eeeaeae0 : search 5 ins_eeeaeae0 = false := by decide +kernel

def gates_eeeaeae0 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [0, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [9, 10]⟩]

theorem upper_eeeaeae0 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 7 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeeeaeae0 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_eeeaeae0, 11, ?_, rfl, ?_⟩
  · simp [gates_eeeaeae0]
  · decide +kernel

def ins_eeeaece0 : List W := [0xfffffc001ffffff8003ffffff0007ffffffffffff8003ffffff0007ffc001fff00012809404a025012809404a025012809404a025012809404a025012809404a, 0xffffffffe000ffffffc001ffffff8003ffe000ffffffc001ffffffffffffe00000083041820c106083041820c106083041820c106083041820c106083041820c, 0xffffffffffff0000000001fffffffffc000000fffffffffe0000007fffffffffffd242921490a485242921490a485242921490a485242921490a485242921490, 0xfffffffffffffffffffffe0000000000000000ffffffffffffffff8000000000ffe3831c18e0c7063831c18e0c7063831c18e0c7063831c18e0c7063831c18e0, 0xffffffffffffffffffffffffffffffffffffff00000000000000000000000000fffc03e01f00f807c03e01f00f807c03e01f00f807c03e01f00f807c03e01f00]

theorem nd_eeeaece0 : ins_eeeaece0.Nodup := by decide +kernel

theorem spec_eeeaece0 : ∀ j : Fin 512, Nat.testBit 0xeeeaece0 (∑ i : Fin 5, if (ins_eeeaece0.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eeeaece0 : search 3 ins_eeeaece0 = false := by decide +kernel

def gates_eeeaece0 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [2, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [6, 8]⟩]

theorem upper_eeeaece0 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 5 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeeeaece0 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_eeeaece0, 9, ?_, rfl, ?_⟩
  · simp [gates_eeeaece0]
  · decide +kernel

def ins_fee8e8e8 : List W := [0xfffffc001fff0007ffc001ffffff8003fffffffff8003fffffffff8003ffffff0008884442221110888444222111088844422211108884442221110888444222, 0xffffffffe0000007fffffe000ffffffc001fffffffffc001fffffffffc001fff0011108884442221110888444222111088844422211108884442221110888444, 0xfffffffffffffff8000000000fffffffffe000fffffffffe000fffffffffe0000022211108884442221110888444222111088844422211108884442221110888, 0xfffffffffffffffffffffffff0000000000000fffffffffffff0000000000000ffc3c21e10f087843c21e10f087843c21e10f087843c21e10f087843c21e10f0, 0xffffffffffffffffffffffffffffffffffffff00000000000000000000000000fffc03e01f00f807c03e01f00f807c03e01f00f807c03e01f00f807c03e01f00]

theorem nd_fee8e8e8 : ins_fee8e8e8.Nodup := by decide +kernel

theorem spec_fee8e8e8 : ∀ j : Fin 512, Nat.testBit 0xfee8e8e8 (∑ i : Fin 5, if (ins_fee8e8e8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_fee8e8e8 : search 6 ins_fee8e8e8 = false := by decide +kernel

def gates_fee8e8e8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [1, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.and, [4, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [8, 11]⟩]

theorem upper_fee8e8e8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfee8e8e8 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_fee8e8e8, 12, ?_, rfl, ?_⟩
  · simp [gates_fee8e8e8]
  · decide +kernel

def ins_fee8eaa8 : List W := [0xfffffc001fff0007ffc001ffffff8003fffffffff8003fffffffffffffffffff0008084042021010808404202101080840420210108084042021010808404202, 0xffffffffe0000007fffffe000ffffffc001fffffffffc001fff0007ffc001fff0011508a845422a11508a845422a11508a845422a11508a845422a11508a8454, 0xfffffffffffffff8000000000fffffffffe000fffffffffe0000007fffffe00000226113089844c226113089844c226113089844c226113089844c2261130898, 0xfffffffffffffffffffffffff0000000000000ffffffffffffffff8000000000ffc3821c10e087043821c10e087043821c10e087043821c10e087043821c10e0, 0xffffffffffffffffffffffffffffffffffffff00000000000000000000000000fffc03e01f00f807c03e01f00f807c03e01f00f807c03e01f00f807c03e01f00]

theorem nd_fee8eaa8 : ins_fee8eaa8.Nodup := by decide +kernel

theorem spec_fee8eaa8 : ∀ j : Fin 512, Nat.testBit 0xfee8eaa8 (∑ i : Fin 5, if (ins_fee8eaa8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_fee8eaa8 : search 7 ins_fee8eaa8 = false := by decide +kernel

def gates_fee8eaa8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [1, 2]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [5, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [11, 12]⟩]

theorem upper_fee8eaa8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfee8eaa8 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_fee8eaa8, 13, ?_, rfl, ?_⟩
  · simp [gates_fee8eaa8]
  · decide +kernel

def ins_fee8eac8 : List W := [0xfffffc001fff0007ffc001ffffff8003fffffffff8003ffffffffffffc001fff0008484242121090848424212109084842421210908484242121090848424212, 0xffffffffe0000007fffffe000ffffffc001fffffffffc001fff0007fffffffff0011108884442221110888444222111088844422211108884442221110888444, 0xfffffffffffffff8000000000fffffffffe000fffffffffe0000007fffffe00000226113089844c226113089844c226113089844c226113089844c2261130898, 0xfffffffffffffffffffffffff0000000000000ffffffffffffffff8000000000ffc3821c10e087043821c10e087043821c10e087043821c10e087043821c10e0, 0xffffffffffffffffffffffffffffffffffffff00000000000000000000000000fffc03e01f00f807c03e01f00f807c03e01f00f807c03e01f00f807c03e01f00]

theorem nd_fee8eac8 : ins_fee8eac8.Nodup := by decide +kernel

theorem spec_fee8eac8 : ∀ j : Fin 512, Nat.testBit 0xfee8eac8 (∑ i : Fin 5, if (ins_fee8eac8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_fee8eac8 : search 7 ins_fee8eac8 = false := by decide +kernel

def gates_fee8eac8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [0, 3]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [8, 12]⟩]

theorem upper_fee8eac8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xfee8eac8 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_fee8eac8, 13, ?_, rfl, ?_⟩
  · simp [gates_fee8eac8]
  · decide +kernel

end PEqualNP.Outside.L_meta_1439_aux

open PEqualNP.Outside.L_meta_1439_aux

set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.L_meta_1439 : ∀ T ∈ ({0xeaeaeae8, 0xeee8eae8, 0xeee8eee0, 0xeeeaeaa8, 0xeeeaeac8, 0xeeeaeae0, 0xeeeaece0, 0xfee8e8e8, 0xfee8eaa8, 0xfee8eac8} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T mem gs o hg _ he
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact replace 0xeaeaeae8 6 ins_eaeaeae8 nd_eaeaeae8 spec_eaeaeae8 rfl reject_eaeaeae8 upper_eaeaeae8 gs o hg he
  · exact replace 0xeee8eae8 7 ins_eee8eae8 nd_eee8eae8 spec_eee8eae8 rfl reject_eee8eae8 upper_eee8eae8 gs o hg he
  · exact replace 0xeee8eee0 6 ins_eee8eee0 nd_eee8eee0 spec_eee8eee0 rfl reject_eee8eee0 upper_eee8eee0 gs o hg he
  · exact replace 0xeeeaeaa8 9 ins_eeeaeaa8 nd_eeeaeaa8 spec_eeeaeaa8 rfl reject_eeeaeaa8 upper_eeeaeaa8 gs o hg he
  · exact replace 0xeeeaeac8 7 ins_eeeaeac8 nd_eeeaeac8 spec_eeeaeac8 rfl reject_eeeaeac8 upper_eeeaeac8 gs o hg he
  · exact replace 0xeeeaeae0 7 ins_eeeaeae0 nd_eeeaeae0 spec_eeeaeae0 rfl reject_eeeaeae0 upper_eeeaeae0 gs o hg he
  · exact replace 0xeeeaece0 5 ins_eeeaece0 nd_eeeaece0 spec_eeeaece0 rfl reject_eeeaece0 upper_eeeaece0 gs o hg he
  · exact replace 0xfee8e8e8 8 ins_fee8e8e8 nd_fee8e8e8 spec_fee8e8e8 rfl reject_fee8e8e8 upper_fee8e8e8 gs o hg he
  · exact replace 0xfee8eaa8 9 ins_fee8eaa8 nd_fee8eaa8 spec_fee8eaa8 rfl reject_fee8eaa8 upper_fee8eaa8 gs o hg he
  · exact replace 0xfee8eac8 9 ins_fee8eac8 nd_fee8eac8 spec_fee8eac8 rfl reject_fee8eac8 upper_fee8eac8 gs o hg he
