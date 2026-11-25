import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Convert
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16525_aux

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

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
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

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
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
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
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
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
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

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
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

def targetFun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008372970 * 2 ^ 32 + 4004178600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def w0 : W := ((0xc000061a00000286 : BitVec 64) ++ (0x0000180300001868 : BitVec 64) ++ (0xf4621e1ec00787ae : BitVec 64) ++ (0x3491dfc3d188787b : BitVec 64))
def w1 : W := ((0x3fa071e0975df539 : BitVec 64) ++ (0xfb82200cfe81c782 : BitVec 64) ++ (0xefbdf1e3bffd7dfb : BitVec 64) ++ (0xfbee207fbef7c78e : BitVec 64))
def w2 : W := ((0x034d18c179818900 : BitVec 64) ++ (0x43fd01200d346305 : BitVec 64) ++ (0x4b0d59d17fc1994d : BitVec 64) ++ (0xc97b11ad2c356745 : BitVec 64))
def w3 : W := ((0x1c968921a0e62070 : BitVec 64) ++ (0x847e0410725a2486 : BitVec 64) ++ (0x9996a9a9b0fe6e71 : BitVec 64) ++ (0xca742e16665aa6a6 : BitVec 64))
def w4 : W := ((0x003af8c50db81049 : BitVec 64) ++ (0x52a4240400ebe314 : BitVec 64) ++ (0x00bafae500f8707e : BitVec 64) ++ (0x0384681c02ebeb94 : BitVec 64))
def w5 : W := ((0x00796925ae304c11 : BitVec 64) ++ (0xac4b010801e5a496 : BitVec 64) ++ (0x02796d65bf007f80 : BitVec 64) ++ (0x0d0bb02809e5b596 : BitVec 64))

def inputs : List W := [w0, w1, w2, w3, w4, w5]

set_option maxRecDepth 10000 in
theorem sample_rows0 : ∀ j : Fin 64,
    targetFun (fun i => (inputs.getD i.val 0)[j.val]) = (~~~goal)[j.val] := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem sample_rows1 : ∀ j : Fin 64,
    targetFun (fun i => (inputs.getD i.val 0)[64 + j.val]) = (~~~goal)[64 + j.val] := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem sample_rows2 : ∀ j : Fin 64,
    targetFun (fun i => (inputs.getD i.val 0)[128 + j.val]) = (~~~goal)[128 + j.val] := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem sample_rows3 : ∀ j : Fin 64,
    targetFun (fun i => (inputs.getD i.val 0)[192 + j.val]) = (~~~goal)[192 + j.val] := by
  decide +kernel

theorem sample_rows : ∀ j : Fin 256,
    targetFun (fun i => (inputs.getD i.val 0)[j.val]) = (~~~goal)[j.val] := by
  intro j
  by_cases h0 : j.val < 64
  · exact sample_rows0 ⟨j.val, h0⟩
  by_cases h1 : j.val < 128
  · have h := sample_rows1 ⟨j.val - 64, by omega⟩
    have he : 64 + (j.val - 64) = j.val := by omega
    simpa only [he] using h
  by_cases h2 : j.val < 192
  · have h := sample_rows2 ⟨j.val - 128, by omega⟩
    have he : 128 + (j.val - 128) = j.val := by omega
    simpa only [he] using h
  · have h := sample_rows3 ⟨j.val - 192, by omega⟩
    have he : 192 + (j.val - 192) = j.val := by omega
    simpa only [he] using h

theorem bound_from_impossible (n : ℕ)
    (impossible : ∀ t, t = goal ∨ t = ~~~goal → build basicOps t n inputs.toFinset → False)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = targetFun x) :
    n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have width : inputs.length = 6 := rfl
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample_rows k
  obtain ⟨t,ht,run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact impossible t ht (lift low run)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child0 : optimized 7 1 [(w0 &&& w1), w0, w1, w2, w3, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child1 : optimized 7 1 [(w0 ||| w1), w0, w1, w2, w3, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child2 : optimized 7 1 [(w0 &&& ~~~w1), w0, w1, w2, w3, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child3 : optimized 7 1 [(w1 &&& ~~~w0), w0, w1, w2, w3, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child4 : optimized 7 1 [(w0 &&& w2), w0, w2, w1, w3, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child5 : optimized 7 1 [(w0 ||| w2), w0, w2, w1, w3, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child6 : optimized 7 1 [(w0 &&& ~~~w2), w0, w2, w1, w3, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child7 : optimized 7 1 [(w2 &&& ~~~w0), w0, w2, w1, w3, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child8 : optimized 7 1 [(w0 &&& w3), w0, w3, w1, w2, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child9 : optimized 7 1 [(w0 ||| w3), w0, w3, w1, w2, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child10 : optimized 7 1 [(w0 &&& ~~~w3), w0, w3, w1, w2, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child11 : optimized 7 1 [(w3 &&& ~~~w0), w0, w3, w1, w2, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child12 : optimized 7 1 [(w0 &&& w4), w0, w4, w1, w2, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child13 : optimized 7 1 [(w0 ||| w4), w0, w4, w1, w2, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child14 : optimized 7 1 [(w0 &&& ~~~w4), w0, w4, w1, w2, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child15 : optimized 7 1 [(w4 &&& ~~~w0), w0, w4, w1, w2, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child16 : optimized 7 1 [(w0 &&& w5), w0, w5, w1, w2, w3, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child17 : optimized 7 1 [(w0 ||| w5), w0, w5, w1, w2, w3, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child18 : optimized 7 1 [(w0 &&& ~~~w5), w0, w5, w1, w2, w3, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child19 : optimized 7 1 [(w5 &&& ~~~w0), w0, w5, w1, w2, w3, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child20 : optimized 7 1 [(w1 &&& w2), w1, w2, w0, w3, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child21 : optimized 7 1 [(w1 ||| w2), w1, w2, w0, w3, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child22 : optimized 7 1 [(w1 &&& ~~~w2), w1, w2, w0, w3, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child23 : optimized 7 1 [(w2 &&& ~~~w1), w1, w2, w0, w3, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child24 : optimized 7 1 [(w1 &&& w3), w1, w3, w0, w2, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child25 : optimized 7 1 [(w1 ||| w3), w1, w3, w0, w2, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child26 : optimized 7 1 [(w1 &&& ~~~w3), w1, w3, w0, w2, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child27 : optimized 7 1 [(w3 &&& ~~~w1), w1, w3, w0, w2, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child28 : optimized 7 1 [(w1 &&& w4), w1, w4, w0, w2, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child29 : optimized 7 1 [(w1 ||| w4), w1, w4, w0, w2, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child30 : optimized 7 1 [(w1 &&& ~~~w4), w1, w4, w0, w2, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child31 : optimized 7 1 [(w4 &&& ~~~w1), w1, w4, w0, w2, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child32 : optimized 7 1 [(w1 &&& w5), w1, w5, w0, w2, w3, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child33 : optimized 7 1 [(w1 ||| w5), w1, w5, w0, w2, w3, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child34 : optimized 7 1 [(w1 &&& ~~~w5), w1, w5, w0, w2, w3, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child35 : optimized 7 1 [(w5 &&& ~~~w1), w1, w5, w0, w2, w3, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child36 : optimized 7 1 [(w2 &&& w3), w2, w3, w0, w1, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child37 : optimized 7 1 [(w2 ||| w3), w2, w3, w0, w1, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child38 : optimized 7 1 [(w2 &&& ~~~w3), w2, w3, w0, w1, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child39 : optimized 7 1 [(w3 &&& ~~~w2), w2, w3, w0, w1, w4, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child40 : optimized 7 1 [(w2 &&& w4), w2, w4, w0, w1, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child41 : optimized 7 2 [(w2 ||| w4), w2, w0, w1, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child42 : optimized 7 1 [(w2 ||| w4), w2, w4, w0, w1, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child43 : optimized 7 1 [(w2 &&& ~~~w4), w2, w4, w0, w1, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child44 : optimized 7 2 [(w4 &&& ~~~w2), w2, w0, w1, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child45 : optimized 7 1 [(w4 &&& ~~~w2), w2, w4, w0, w1, w3, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child46 : optimized 7 1 [(w2 &&& w5), w2, w5, w0, w1, w3, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child47 : optimized 7 1 [(w2 ||| w5), w2, w5, w0, w1, w3, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child48 : optimized 7 1 [(w2 &&& ~~~w5), w2, w5, w0, w1, w3, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child49 : optimized 7 1 [(w5 &&& ~~~w2), w2, w5, w0, w1, w3, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child50 : optimized 7 1 [(w3 &&& w4), w3, w4, w0, w1, w2, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child51 : optimized 7 1 [(w3 ||| w4), w3, w4, w0, w1, w2, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child52 : optimized 7 1 [(w3 &&& ~~~w4), w3, w4, w0, w1, w2, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child53 : optimized 7 1 [(w4 &&& ~~~w3), w3, w4, w0, w1, w2, w5] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child54 : optimized 7 1 [(w3 &&& w5), w3, w5, w0, w1, w2, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child55 : optimized 7 2 [(w3 ||| w5), w3, w0, w1, w2, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child56 : optimized 7 1 [(w3 ||| w5), w3, w5, w0, w1, w2, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child57 : optimized 7 1 [(w3 &&& ~~~w5), w3, w5, w0, w1, w2, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child58 : optimized 7 2 [(w5 &&& ~~~w3), w3, w0, w1, w2, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child59 : optimized 7 1 [(w5 &&& ~~~w3), w3, w5, w0, w1, w2, w4] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child60 : optimized 7 1 [(w4 &&& w5), w4, w5, w0, w1, w2, w3] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child61 : optimized 7 1 [(w4 ||| w5), w4, w5, w0, w1, w2, w3] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child62 : optimized 7 1 [(w4 &&& ~~~w5), w4, w5, w0, w1, w2, w3] = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child63 : optimized 7 1 [(w5 &&& ~~~w4), w4, w5, w0, w1, w2, w3] = false := by
  decide +kernel

theorem shape0 (next : ℕ → List W → Bool)
    (h0 : next 1 [(w0 &&& w1), w0, w1, w2, w3, w4, w5] = false)
    (h1 : next 1 [(w0 ||| w1), w0, w1, w2, w3, w4, w5] = false)
    (h2 : next 1 [(w0 &&& ~~~w1), w0, w1, w2, w3, w4, w5] = false)
    (h3 : next 1 [(w1 &&& ~~~w0), w0, w1, w2, w3, w4, w5] = false) : dispatch 3 next w0 w1 [w2, w3, w4, w5] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h0, h1, h2, h3]
  rfl

theorem branch0 : dispatch 3 (optimized 7) w0 w1 [w2, w3, w4, w5] = false :=
  shape0 (optimized 7) child0 child1 child2 child3

theorem shape1 (next : ℕ → List W → Bool)
    (h4 : next 1 [(w0 &&& w2), w0, w2, w1, w3, w4, w5] = false)
    (h5 : next 1 [(w0 ||| w2), w0, w2, w1, w3, w4, w5] = false)
    (h6 : next 1 [(w0 &&& ~~~w2), w0, w2, w1, w3, w4, w5] = false)
    (h7 : next 1 [(w2 &&& ~~~w0), w0, w2, w1, w3, w4, w5] = false) : dispatch 3 next w0 w2 [w1, w3, w4, w5] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h4, h5, h6, h7]
  rfl

theorem branch1 : dispatch 3 (optimized 7) w0 w2 [w1, w3, w4, w5] = false :=
  shape1 (optimized 7) child4 child5 child6 child7

theorem shape2 (next : ℕ → List W → Bool)
    (h8 : next 1 [(w0 &&& w3), w0, w3, w1, w2, w4, w5] = false)
    (h9 : next 1 [(w0 ||| w3), w0, w3, w1, w2, w4, w5] = false)
    (h10 : next 1 [(w0 &&& ~~~w3), w0, w3, w1, w2, w4, w5] = false)
    (h11 : next 1 [(w3 &&& ~~~w0), w0, w3, w1, w2, w4, w5] = false) : dispatch 3 next w0 w3 [w1, w2, w4, w5] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h8, h9, h10, h11]
  rfl

theorem branch2 : dispatch 3 (optimized 7) w0 w3 [w1, w2, w4, w5] = false :=
  shape2 (optimized 7) child8 child9 child10 child11

theorem shape3 (next : ℕ → List W → Bool)
    (h12 : next 1 [(w0 &&& w4), w0, w4, w1, w2, w3, w5] = false)
    (h13 : next 1 [(w0 ||| w4), w0, w4, w1, w2, w3, w5] = false)
    (h14 : next 1 [(w0 &&& ~~~w4), w0, w4, w1, w2, w3, w5] = false)
    (h15 : next 1 [(w4 &&& ~~~w0), w0, w4, w1, w2, w3, w5] = false) : dispatch 3 next w0 w4 [w1, w2, w3, w5] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h12, h13, h14, h15]
  rfl

theorem branch3 : dispatch 3 (optimized 7) w0 w4 [w1, w2, w3, w5] = false :=
  shape3 (optimized 7) child12 child13 child14 child15

theorem shape4 (next : ℕ → List W → Bool)
    (h16 : next 1 [(w0 &&& w5), w0, w5, w1, w2, w3, w4] = false)
    (h17 : next 1 [(w0 ||| w5), w0, w5, w1, w2, w3, w4] = false)
    (h18 : next 1 [(w0 &&& ~~~w5), w0, w5, w1, w2, w3, w4] = false)
    (h19 : next 1 [(w5 &&& ~~~w0), w0, w5, w1, w2, w3, w4] = false) : dispatch 3 next w0 w5 [w1, w2, w3, w4] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h16, h17, h18, h19]
  rfl

theorem branch4 : dispatch 3 (optimized 7) w0 w5 [w1, w2, w3, w4] = false :=
  shape4 (optimized 7) child16 child17 child18 child19

theorem shape5 (next : ℕ → List W → Bool)
    (h20 : next 1 [(w1 &&& w2), w1, w2, w0, w3, w4, w5] = false)
    (h21 : next 1 [(w1 ||| w2), w1, w2, w0, w3, w4, w5] = false)
    (h22 : next 1 [(w1 &&& ~~~w2), w1, w2, w0, w3, w4, w5] = false)
    (h23 : next 1 [(w2 &&& ~~~w1), w1, w2, w0, w3, w4, w5] = false) : dispatch 3 next w1 w2 [w0, w3, w4, w5] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h20, h21, h22, h23]
  rfl

theorem branch5 : dispatch 3 (optimized 7) w1 w2 [w0, w3, w4, w5] = false :=
  shape5 (optimized 7) child20 child21 child22 child23

theorem shape6 (next : ℕ → List W → Bool)
    (h24 : next 1 [(w1 &&& w3), w1, w3, w0, w2, w4, w5] = false)
    (h25 : next 1 [(w1 ||| w3), w1, w3, w0, w2, w4, w5] = false)
    (h26 : next 1 [(w1 &&& ~~~w3), w1, w3, w0, w2, w4, w5] = false)
    (h27 : next 1 [(w3 &&& ~~~w1), w1, w3, w0, w2, w4, w5] = false) : dispatch 3 next w1 w3 [w0, w2, w4, w5] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h24, h25, h26, h27]
  rfl

theorem branch6 : dispatch 3 (optimized 7) w1 w3 [w0, w2, w4, w5] = false :=
  shape6 (optimized 7) child24 child25 child26 child27

theorem shape7 (next : ℕ → List W → Bool)
    (h28 : next 1 [(w1 &&& w4), w1, w4, w0, w2, w3, w5] = false)
    (h29 : next 1 [(w1 ||| w4), w1, w4, w0, w2, w3, w5] = false)
    (h30 : next 1 [(w1 &&& ~~~w4), w1, w4, w0, w2, w3, w5] = false)
    (h31 : next 1 [(w4 &&& ~~~w1), w1, w4, w0, w2, w3, w5] = false) : dispatch 3 next w1 w4 [w0, w2, w3, w5] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h28, h29, h30, h31]
  rfl

theorem branch7 : dispatch 3 (optimized 7) w1 w4 [w0, w2, w3, w5] = false :=
  shape7 (optimized 7) child28 child29 child30 child31

theorem shape8 (next : ℕ → List W → Bool)
    (h32 : next 1 [(w1 &&& w5), w1, w5, w0, w2, w3, w4] = false)
    (h33 : next 1 [(w1 ||| w5), w1, w5, w0, w2, w3, w4] = false)
    (h34 : next 1 [(w1 &&& ~~~w5), w1, w5, w0, w2, w3, w4] = false)
    (h35 : next 1 [(w5 &&& ~~~w1), w1, w5, w0, w2, w3, w4] = false) : dispatch 3 next w1 w5 [w0, w2, w3, w4] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h32, h33, h34, h35]
  rfl

theorem branch8 : dispatch 3 (optimized 7) w1 w5 [w0, w2, w3, w4] = false :=
  shape8 (optimized 7) child32 child33 child34 child35

theorem shape9 (next : ℕ → List W → Bool)
    (h36 : next 1 [(w2 &&& w3), w2, w3, w0, w1, w4, w5] = false)
    (h37 : next 1 [(w2 ||| w3), w2, w3, w0, w1, w4, w5] = false)
    (h38 : next 1 [(w2 &&& ~~~w3), w2, w3, w0, w1, w4, w5] = false)
    (h39 : next 1 [(w3 &&& ~~~w2), w2, w3, w0, w1, w4, w5] = false) : dispatch 3 next w2 w3 [w0, w1, w4, w5] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h36, h37, h38, h39]
  rfl

theorem branch9 : dispatch 3 (optimized 7) w2 w3 [w0, w1, w4, w5] = false :=
  shape9 (optimized 7) child36 child37 child38 child39

theorem shape10 (next : ℕ → List W → Bool)
    (h40 : next 1 [(w2 &&& w4), w2, w4, w0, w1, w3, w5] = false)
    (h41 : next 2 [(w2 ||| w4), w2, w0, w1, w3, w5] = false)
    (h42 : next 1 [(w2 ||| w4), w2, w4, w0, w1, w3, w5] = false)
    (h43 : next 1 [(w2 &&& ~~~w4), w2, w4, w0, w1, w3, w5] = false)
    (h44 : next 2 [(w4 &&& ~~~w2), w2, w0, w1, w3, w5] = false)
    (h45 : next 1 [(w4 &&& ~~~w2), w2, w4, w0, w1, w3, w5] = false) : dispatch 3 next w2 w4 [w0, w1, w3, w5] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h40, h41, h42, h43, h44, h45]
  rfl

theorem branch10 : dispatch 3 (optimized 7) w2 w4 [w0, w1, w3, w5] = false :=
  shape10 (optimized 7) child40 child41 child42 child43 child44 child45

theorem shape11 (next : ℕ → List W → Bool)
    (h46 : next 1 [(w2 &&& w5), w2, w5, w0, w1, w3, w4] = false)
    (h47 : next 1 [(w2 ||| w5), w2, w5, w0, w1, w3, w4] = false)
    (h48 : next 1 [(w2 &&& ~~~w5), w2, w5, w0, w1, w3, w4] = false)
    (h49 : next 1 [(w5 &&& ~~~w2), w2, w5, w0, w1, w3, w4] = false) : dispatch 3 next w2 w5 [w0, w1, w3, w4] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h46, h47, h48, h49]
  rfl

theorem branch11 : dispatch 3 (optimized 7) w2 w5 [w0, w1, w3, w4] = false :=
  shape11 (optimized 7) child46 child47 child48 child49

theorem shape12 (next : ℕ → List W → Bool)
    (h50 : next 1 [(w3 &&& w4), w3, w4, w0, w1, w2, w5] = false)
    (h51 : next 1 [(w3 ||| w4), w3, w4, w0, w1, w2, w5] = false)
    (h52 : next 1 [(w3 &&& ~~~w4), w3, w4, w0, w1, w2, w5] = false)
    (h53 : next 1 [(w4 &&& ~~~w3), w3, w4, w0, w1, w2, w5] = false) : dispatch 3 next w3 w4 [w0, w1, w2, w5] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h50, h51, h52, h53]
  rfl

theorem branch12 : dispatch 3 (optimized 7) w3 w4 [w0, w1, w2, w5] = false :=
  shape12 (optimized 7) child50 child51 child52 child53

theorem shape13 (next : ℕ → List W → Bool)
    (h54 : next 1 [(w3 &&& w5), w3, w5, w0, w1, w2, w4] = false)
    (h55 : next 2 [(w3 ||| w5), w3, w0, w1, w2, w4] = false)
    (h56 : next 1 [(w3 ||| w5), w3, w5, w0, w1, w2, w4] = false)
    (h57 : next 1 [(w3 &&& ~~~w5), w3, w5, w0, w1, w2, w4] = false)
    (h58 : next 2 [(w5 &&& ~~~w3), w3, w0, w1, w2, w4] = false)
    (h59 : next 1 [(w5 &&& ~~~w3), w3, w5, w0, w1, w2, w4] = false) : dispatch 3 next w3 w5 [w0, w1, w2, w4] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h54, h55, h56, h57, h58, h59]
  rfl

theorem branch13 : dispatch 3 (optimized 7) w3 w5 [w0, w1, w2, w4] = false :=
  shape13 (optimized 7) child54 child55 child56 child57 child58 child59

theorem shape14 (next : ℕ → List W → Bool)
    (h60 : next 1 [(w4 &&& w5), w4, w5, w0, w1, w2, w3] = false)
    (h61 : next 1 [(w4 ||| w5), w4, w5, w0, w1, w2, w3] = false)
    (h62 : next 1 [(w4 &&& ~~~w5), w4, w5, w0, w1, w2, w3] = false)
    (h63 : next 1 [(w5 &&& ~~~w4), w4, w5, w0, w1, w2, w3] = false) : dispatch 3 next w4 w5 [w0, w1, w2, w3] = false := by
  unfold dispatch
  simp only [ops, List.any_cons, List.any_nil]
  simp only [h60, h61, h62, h63]
  rfl

theorem branch14 : dispatch 3 (optimized 7) w4 w5 [w0, w1, w2, w3] = false :=
  shape14 (optimized 7) child60 child61 child62 child63

theorem root_pairs (next : ℕ → List W → Bool) :
    (pairs inputs).any (fun (a, b, r) => dispatch 3 next a b r) =
    (dispatch 3 next w0 w1 [w2, w3, w4, w5] || (dispatch 3 next w0 w2 [w1, w3, w4, w5] || (dispatch 3 next w0 w3 [w1, w2, w4, w5] || (dispatch 3 next w0 w4 [w1, w2, w3, w5] || (dispatch 3 next w0 w5 [w1, w2, w3, w4] || (dispatch 3 next w1 w2 [w0, w3, w4, w5] || (dispatch 3 next w1 w3 [w0, w2, w4, w5] || (dispatch 3 next w1 w4 [w0, w2, w3, w5] || (dispatch 3 next w1 w5 [w0, w2, w3, w4] || (dispatch 3 next w2 w3 [w0, w1, w4, w5] || (dispatch 3 next w2 w4 [w0, w1, w3, w5] || (dispatch 3 next w2 w5 [w0, w1, w3, w4] || (dispatch 3 next w3 w4 [w0, w1, w2, w5] || (dispatch 3 next w3 w5 [w0, w1, w2, w4] || (dispatch 3 next w4 w5 [w0, w1, w2, w3] || false))))))))))))))) := by
  rfl

theorem root_with (next : ℕ → List W → Bool) :
    inputs.sublists.any (fun ws =>
      decide (ws.length ≤ 9) && (cuts ws == -1) && next (9 - ws.length) ws) =
    next 3 inputs := by
  change (next 3 inputs || false) = next 3 inputs
  exact Bool.or_false _

theorem root_only : search 8 inputs = optimized 8 3 inputs :=
  root_with (optimized 8)

theorem optimized_step (k extra : ℕ) (ws : List W) :
    optimized (k + 1) extra ws =
      ((ws == [goal] || ws == [~~~goal]) ||
        (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)) := rfl

theorem root_finish (next : ℕ → List W → Bool)
    (h0 : dispatch 3 next w0 w1 [w2, w3, w4, w5] = false)
    (h1 : dispatch 3 next w0 w2 [w1, w3, w4, w5] = false)
    (h2 : dispatch 3 next w0 w3 [w1, w2, w4, w5] = false)
    (h3 : dispatch 3 next w0 w4 [w1, w2, w3, w5] = false)
    (h4 : dispatch 3 next w0 w5 [w1, w2, w3, w4] = false)
    (h5 : dispatch 3 next w1 w2 [w0, w3, w4, w5] = false)
    (h6 : dispatch 3 next w1 w3 [w0, w2, w4, w5] = false)
    (h7 : dispatch 3 next w1 w4 [w0, w2, w3, w5] = false)
    (h8 : dispatch 3 next w1 w5 [w0, w2, w3, w4] = false)
    (h9 : dispatch 3 next w2 w3 [w0, w1, w4, w5] = false)
    (h10 : dispatch 3 next w2 w4 [w0, w1, w3, w5] = false)
    (h11 : dispatch 3 next w2 w5 [w0, w1, w3, w4] = false)
    (h12 : dispatch 3 next w3 w4 [w0, w1, w2, w5] = false)
    (h13 : dispatch 3 next w3 w5 [w0, w1, w2, w4] = false)
    (h14 : dispatch 3 next w4 w5 [w0, w1, w2, w3] = false) :
    ((inputs == [goal] || inputs == [~~~goal]) ||
      (pairs inputs).any (fun (a, b, r) => dispatch 3 next a b r)) = false := by
  have h : (inputs == [goal] || inputs == [~~~goal]) = false := by decide
  rw [h, Bool.false_or, root_pairs]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, Bool.false_or]

set_option maxHeartbeats 0 in
theorem reject : search 8 inputs = false :=
  root_only.trans ((optimized_step 7 3 inputs).trans
    (root_finish (optimized 7) branch0 branch1 branch2 branch3 branch4 branch5 branch6 branch7 branch8 branch9 branch10 branch11 branch12 branch13 branch14))

theorem no_small (t : W) (ht : t = goal ∨ t = ~~~goal) (run : build basicOps t 8 inputs.toFinset) : False :=
  Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs (by decide) run))

def witness : Circuit := ⟨[⟨.or, [2, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [3, 6]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = targetFun x := by
  decide +kernel

end PEqualNP.Outside.L_meta_16525_aux

theorem PEqualNP.Outside.L_meta_16525 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4004178600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4004178600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_16525_aux.binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_16525_aux.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_16525_aux.isBinary, op]⟩
    have bound := PEqualNP.Outside.L_meta_16525_aux.bound_from_impossible 8 PEqualNP.Outside.L_meta_16525_aux.no_small C.gates C.output fits computes
    refine ⟨PEqualNP.Outside.L_meta_16525_aux.witness, PEqualNP.Outside.L_meta_16525_aux.witness_mono, ?_, PEqualNP.Outside.L_meta_16525_aux.witness_eval⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g,mem,eq⟩).elim)), cap⟩

