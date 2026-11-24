import PEqualNP.Defs
import Mathlib.Tactic.Convert
import Mathlib.Data.List.Sublists

namespace PEqualNP.Outside.L_meta_3110

-- Adapted from the live-wire compression argument by jackboykin in project PR 795.
-- Each stored signal represents a Boolean function up to complementation.
namespace Signed2964
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def build {α : Type} [DecidableEq α] (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)
def live {α : Type} [DecidableEq α] (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)
theorem compress {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α} {k : ℕ}
    {available : Finset α} (h : build ops goal k available) :
    ∃ s ⊆ available, live ops goal k s := by
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
theorem live_card {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α} {k : ℕ}
    {s : Finset α} (h : live ops goal k s) : s.card ≤ k + 1 := by
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
theorem live_separates {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    (D : α → Prop) (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
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
theorem first_live {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : ℕ} {s : Finset α} (h : live ops goal (k + 1) s) :
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

abbrev m := 258
abbrev V := BitVec (2 * m)
abbrev W := V
def norm (x : W) : W := if x.getLsbD 0 then ~~~x else x
def ops (a b : W) : List W :=
  [norm (a &&& b),norm (a &&& ~~~b),norm (~~~a &&& b),norm (~~~a &&& ~~~b)]
def sep (w : W) : BitVec m := ((w >>> m) ^^^ w).setWidth m
def cuts (ws : List W) : BitVec m := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec m) ++ (0 : BitVec m)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))
def rawInputs : List W := [0x843f80211fc01f807e0f80441f80f810821108fc3f0f020882108488a1f8f83c0007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07, 0xf83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038, 0x108410fe20ffe200104211088210913f009f0f808bff03e10042f88790211ff40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0, 0x210821084208441123ff00113fff800427e40227fc22008217ff200225fff120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000, 0xffc0407fff100020fc84207fc421021ff9000ff9104023fff8840007fe422200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000, 0x4210821084208842410842220842245ffffff002008043fffffffff80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000, 0x8421042108411084ffffffc01000401ffffffffffffffc04010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000, 0xffffffc000820000ffffffffffffffe8420844000104010822084214000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000, 0xffffffffffffffff82108400208400108410884422088a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000]
def inputs : List W := rawInputs.map norm
def assignment (k : Fin (2*m)) (i : Fin 9) : Bool := (rawInputs.getD i.val 0).getLsbD k.val
def target (x : Fin 9 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
set_option maxHeartbeats 0 in
theorem target_bits : ∀ k : Fin (2*m), target (assignment k) = goal.getLsbD k.val := by decide +kernel
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
abbrev basicOps (a b : W) := (ops a b).toFinset
def differs (i : Fin m) (w : W) : Prop :=
  w.getLsbD (m+i.val) ≠ w.getLsbD i.val

private theorem norm_diff (i : Fin m) (w : W) : differs i (norm w) ↔ differs i w := by
  have hi : i.val < 2*m := by have := i.isLt; omega
  have hj : m+i.val < 2*m := by have := i.isLt; omega
  unfold norm differs
  split <;> simp [BitVec.getLsbD_not,hi,hj]

theorem ops_differs (i : Fin m) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  have hi : i.val < 2*m := by have := i.isLt; omega
  have hj : m+i.val < 2*m := by have := i.isLt; omega
  by_contra! eq
  simp only [differs,not_not] at eq
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  simp [BitVec.getLsbD_eq_getElem hi,BitVec.getLsbD_eq_getElem hj] at eq
  rcases hz with rfl | rfl | rfl | rfl <;>
    rw [norm_diff] at hd <;>
    simp [differs,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hj,eq.1,eq.2] at hd

theorem goal_differs : ∀ i : Fin m, differs i goal := by unfold differs; decide +kernel

theorem cuts_spec (ws : List W) (i : Fin m) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or,Bool.or_eq_true,ih]
    have hi : i.val < 2*m := by have := i.isLt; omega
    simp [sep,i.isLt,differs,hi,Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes m)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext w
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  rw [BitVec.and_comm b a,BitVec.and_comm b (~~~a),BitVec.and_comm (~~~b) a,BitVec.and_comm (~~~b) (~~~a)]
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
    · exact List.nodup_cons.mpr ⟨fun hm => (List.nodup_cons.mp habr).1 (List.mem_cons_of_mem _ hm),
        (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2⟩
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind
theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc
theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin m) := [3, 0, 4, 7, 1, 2, 5, 8, 16]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      !(b.getLsbD (m+i.val) ^^ b.getLsbD i.val) || b == a))) = true := by decide +kernel
  obtain ⟨i, _, hAll⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    change b.getLsbD (m+i.val) ≠ b.getLsbD i.val at hd
    cases h : b.getLsbD (m+i.val) <;> cases e : b.getLsbD i.val <;> simp_all
  obtain ⟨b, hb, hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb
theorem input_live (k : ℕ) (hb : build basicOps goal k inputs.toFinset) :
    live basicOps goal k inputs.toFinset := by
  obtain ⟨S, hsub, hLive⟩ := compress hb
  exact full_inputs hsub hLive ▸ hLive
theorem extend_live {m n : ℕ} (le : m ≤ n) (h : live basicOps goal m inputs.toFinset) :
    live basicOps goal n inputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih
def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    !(w == a || w == b || r.contains w) && (
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r)))
def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (hfresh : z ∉ a :: b :: r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  rw [Bool.and_eq_true]
  constructor
  · simpa [List.mem_cons, and_assoc] using hfresh
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega,
      .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega,
      .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩
theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk
          (fun hm => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm)))
          (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap,
          go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩


def allBad (k : ℕ) : List (ℕ × List W) → Prop
  | [] => True
  | (e,ws) :: xs => optimized k e ws = false ∧ allBad k xs

theorem bad_at {e k : ℕ} {ws : List W} {xs : List (ℕ × List W)}
    (h : allBad k xs) (hm : (e,ws) ∈ xs) : optimized k e ws = false := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    obtain ⟨j,ys⟩ := x
    rcases List.mem_cons.mp hm with eq | old
    · cases eq; exact h.1
    · exact ih h.2 old

theorem dispatch_mono (f t : ℕ → List W → Bool)
    (mono : ∀ e ws, f e ws = true → t e ws = true)
    (e : ℕ) (a b : W) (r : List W) :
    dispatch e f a b r = true → dispatch e t a b r = true := by
  intro h
  obtain ⟨x,hx,hy⟩ := List.any_eq_true.mp h
  apply List.any_eq_true.mpr
  refine ⟨x, hx, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hy ⊢
  grind

def oneLayer (e : ℕ) (ws : List W) (f : ℕ → List W → Bool) : Bool :=
  ws == [goal] || (pairs ws).any (fun (a,b,r) => dispatch e f a b r)

theorem certify {k e : ℕ} {ws : List W} (xs : List (ℕ × List W))
    (hex : oneLayer e ws (fun j ys => !xs.contains (j,ys)) = false)
    (hbad : allBad k xs) : optimized (k+1) e ws = false := by
  cases hrun : optimized (k+1) e ws with
  | false => rfl
  | true =>
    have mono (j : ℕ) (ys : List W) (ok : optimized k j ys = true) :
        (!xs.contains (j,ys)) = true := by
      by_contra! hn
      have hm : (j,ys) ∈ xs := by simpa using hn
      have h := bad_at hbad hm
      simp_all
    have test : oneLayer e ws (fun j ys => !xs.contains (j,ys)) = true := by
      change oneLayer e ws (optimized k) = true at hrun
      simp only [oneLayer, Bool.or_eq_true, List.any_eq_true] at hrun ⊢
      rcases hrun with done | ⟨⟨a,b,r⟩,hm,hh⟩
      · exact .inl done
      · exact .inr ⟨(a,b,r),hm,dispatch_mono _ _ mono e a b r hh⟩
    exact Bool.noConfusion (hex.symm.trans test)

end Signed2964

namespace Signed2964

private theorem index_zero : (decide (0 < 2*m)) = true := by decide

private def ph (a : W) (s : Bool) : W := if s then ~~~a else a

-- Transforming bits by a permutation of rows can change which output phase is canonical.
private def readRows (p : Fin (2*m) → Fin (2*m)) (x : W) : W :=
  BitVec.ofNat _ (Nat.ofBits fun i => x.getLsbD (p i).val)

private theorem read_readRows (p : Fin (2*m) → Fin (2*m)) (x : W) (i : Fin (2*m)) :
    (readRows p x).getLsbD i.val = x.getLsbD (p i).val := by
  rw [readRows,BitVec.getLsbD_ofNat]
  simp [i.isLt]

private theorem readRows_not (p : Fin (2*m) → Fin (2*m)) (x : W) :
    readRows p (~~~x) = ~~~readRows p x := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  let i : Fin (2*m) := ⟨k,hk⟩
  change (readRows p _).getLsbD i.val = (~~~readRows p x).getLsbD i.val
  simp only [read_readRows,BitVec.getLsbD_not,i.isLt,(p i).isLt,decide_true,Bool.true_and]

private theorem readRows_and (p : Fin (2*m) → Fin (2*m)) (x y : W) :
    readRows p (x &&& y) = readRows p x &&& readRows p y := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  let i : Fin (2*m) := ⟨k,hk⟩
  change (readRows p _).getLsbD i.val = (readRows p x &&& readRows p y).getLsbD i.val
  simp only [read_readRows,BitVec.getLsbD_and]

private theorem readRows_inj {p : Fin (2*m) → Fin (2*m)} (hp : p.Surjective) :
    (readRows p).Injective := by
  intro a b eq
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  obtain ⟨j,hj⟩ := hp ⟨k,hk⟩
  have got := congrArg (fun x : W => x.getLsbD j.val) eq
  simpa only [read_readRows,hj] using got

private theorem norm_not (x : W) : norm (~~~x) = norm x := by
  unfold norm
  rw [BitVec.getLsbD_not]
  have h : 0 < 2*m := by decide
  simp only [h,decide_true,Bool.true_and]
  cases x.getLsbD 0 <;> simp

private theorem ph_undo (x : W) (s : Bool) : ph (ph x s) s = x := by
  cases s <;> simp [ph]

private theorem norm_first (x : W) : (norm x).getLsbD 0 = false := by
  unfold norm
  cases h : x.getLsbD 0 <;>
    simp only [h,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_not,index_zero,Bool.true_and,
      Bool.not_true]

-- Preserve the phase at row zero to obtain an injection on all words, including raw words.
def move (p : Fin (2*m) → Fin (2*m)) (x : W) := ph (norm (readRows p x)) (x.getLsbD 0)

private theorem move_inj {p : Fin (2*m) → Fin (2*m)} (hp : p.Surjective) :
    (move p).Injective := by
  intro a b eq
  have first (x : W) : (move p x).getLsbD 0 = x.getLsbD 0 := by
    unfold move
    cases h : x.getLsbD 0 <;>
      simp only [ph,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_not,norm_first,
        index_zero,Bool.true_and,Bool.not_false]
  have same : a.getLsbD 0 = b.getLsbD 0 := (first a).symm.trans
    ((congrArg (fun x : W => x.getLsbD 0) eq).trans (first b))
  unfold move at eq
  rw [same] at eq
  have hn := congrArg (fun x => ph x (b.getLsbD 0)) eq
  simp only [ph_undo] at hn
  unfold norm at hn
  split at hn <;> split at hn
  · exact readRows_inj hp (by simpa using congrArg (fun x : W => ~~~x) hn)
  · have h : ~~~a = b := readRows_inj hp ((readRows_not p a).trans hn)
    have := congrArg (fun x : W => x.getLsbD 0) h
    simp only [BitVec.getLsbD_not,index_zero,Bool.true_and,same] at this
    revert this
    generalize b.getLsbD 0 = t
    cases t <;> simp
  · have h : a = ~~~b := readRows_inj hp (hn.trans (readRows_not p b).symm)
    have := congrArg (fun x : W => x.getLsbD 0) h
    simp only [BitVec.getLsbD_not,index_zero,Bool.true_and,same] at this
    revert this
    generalize b.getLsbD 0 = t
    cases t <;> simp
  · exact readRows_inj hp hn

private theorem norm_read_norm (p : Fin (2*m) → Fin (2*m)) (x : W) :
    norm (readRows p (norm x)) = norm (readRows p x) := by
  by_cases h : x.getLsbD 0 = true
  · rw [show norm x = ~~~x from ite_eq_left h,readRows_not,norm_not]
  · rw [show norm x = x from ite_eq_right h]

private theorem move_norm (p : Fin (2*m) → Fin (2*m)) (x : W) :
    move p (norm x) = norm (readRows p x) := by
  simp only [move,norm_first,ph,Bool.false_eq_true,ite_false,norm_read_norm]

private theorem ops_phase (a b : W) (s t : Bool) : norm (ph a s &&& ph b t) ∈ basicOps a b := by
  cases s <;> cases t <;> simp [basicOps,ops,ph]

private theorem signed_image (p : Fin (2*m) → Fin (2*m)) (a : W) (s : Bool) :
    ∃ t, readRows p (ph a s) = ph (move p a) t := by
  refine ⟨s ^^ ((readRows p a).getLsbD 0 ^^ a.getLsbD 0),?_⟩
  cases h : (readRows p a).getLsbD 0 <;> cases e : a.getLsbD 0 <;> cases s <;>
    simp only [move,ph,norm,h,e,readRows_not,Bool.false_eq_true,ite_false,ite_true,BitVec.not_not,
      Bool.xor_false,Bool.xor_true,Bool.not_true,Bool.not_false]

private theorem move_member (p : Fin (2*m) → Fin (2*m)) {a b z : W} (h : z ∈ basicOps a b) :
    move p z ∈ basicOps (move p a) (move p b) := by
  have aux (s t : Bool) : move p (norm (ph a s &&& ph b t)) ∈ basicOps (move p a) (move p b) := by
    obtain ⟨u,hu⟩ := signed_image p a s
    obtain ⟨v,hv⟩ := signed_image p b t
    rw [move_norm,readRows_and,hu,hv]
    exact ops_phase _ _ _ _
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact aux false false
  · exact aux false true
  · exact aux true false
  · exact aux true true

-- Check a concrete canonical signal image one row at a time.
theorem move_of_bits (p : Fin (2*m) → Fin (2*m)) (a b : W)
    (h0 : a.getLsbD 0 = false)
    (h : ∀ i : Fin (2*m), (a.getLsbD (p i).val ^^ a.getLsbD (p 0).val) = b.getLsbD i.val) :
    move p a = b := by
  have first : (readRows p a).getLsbD 0 = a.getLsbD (p 0).val := read_readRows p a 0
  simp only [move,h0,ph,Bool.false_eq_true,ite_false,norm,first]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  let i : Fin (2*m) := ⟨k,hk⟩
  change (if a.getLsbD (p 0).val then ~~~readRows p a else readRows p a).getLsbD i.val = _
  cases flag : a.getLsbD (p 0).val <;>
    simpa only [flag,Bool.xor_false,Bool.xor_true,Bool.false_eq_true,ite_false,ite_true,
      BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and,read_readRows] using h i

def rowImage (p : Fin (2*m) → Fin (2*m)) (x y : W) : Prop :=
  ∀ i : Fin (2*m), x.getLsbD (p i).val = y.getLsbD i.val

private theorem readRows_eq {p : Fin (2*m) → Fin (2*m)} {x y : W} (h : rowImage p x y) :
    readRows p x = y := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  exact (read_readRows p x ⟨k,hk⟩).trans (h ⟨k,hk⟩)

theorem move_literal {p : Fin (2*m) → Fin (2*m)} {a b x y : W} (h : rowImage p a b)
    (hx : norm a = x) (hy : norm b = y) : move p x = y := by
  rw [←hx,move_norm,readRows_eq h,hy]

theorem move_gate {p : Fin (2*m) → Fin (2*m)} {a b a' b' x y : W}
    (s t : Bool) (ha : rowImage p a a') (hb : rowImage p b b')
    (hx : norm (ph a s &&& ph b t) = x) (hy : norm (ph a' s &&& ph b' t) = y) :
    move p x = y := by
  rw [←hx,move_norm,readRows_and,←hy]
  cases s <;> cases t <;> simp only [ph,Bool.false_eq_true,ite_false,ite_true,readRows_not,
    readRows_eq ha,readRows_eq hb]

theorem move_live (p : Fin (2*m) → Fin (2*m)) (hp : p.Surjective)
    (hg : move p goal = goal) (n : Nat) (s : Finset W) (h : live basicOps goal n s) :
    live basicOps goal n (s.image (move p)) := by
  induction n generalizing s with
  | zero => change s = {goal} at h; simp [h,live,hg]
  | succ k ih =>
    rcases h with h | ⟨a,ha,b,hb,hne,z,hz,hfresh,r,hs,hl⟩
    · exact Or.inl (ih _ h)
    · refine Or.inr ⟨_,Finset.mem_image_of_mem _ ha,_,Finset.mem_image_of_mem _ hb,
        (move_inj hp).ne hne,_,move_member p hz,?_,r.image (move p),?_,?_⟩
      · intro hm
        obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hm
        exact hfresh ((move_inj hp he) ▸ hw)
      · simp [hs]
      · simpa using ih _ hl

theorem reject_image (p : Fin (2*m) → Fin (2*m)) (hp : p.Surjective)
    (hg : move p goal = goal) (hs : inputs.toFinset.image (move p) = inputs.toFinset)
    (a b : W) (he : move p a = b) (hb : ¬ live basicOps goal 10 (insert b inputs.toFinset)) :
    ¬ live basicOps goal 10 (insert a inputs.toFinset) := by
  intro h
  have h' := move_live p hp hg _ _ h
  exact hb (by simpa only [Finset.image_insert,he,hs] using h')

def rootDead (zs : List W) : Prop := ∀ z ∈ zs, ¬ live basicOps goal 10 (insert z inputs.toFinset)

theorem rootDead_cons {z : W} {zs : List W}
    (hz : ¬ live basicOps goal 10 (insert z inputs.toFinset)) (hs : rootDead zs) :
    rootDead (z :: zs) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | other
  · exact hz
  · exact hs _ other


end Signed2964

namespace Signed2964.Orbit

-- A concrete table packs each row index in a separate ten-bit field.
def rowAt (table index : Nat) : Nat := ((table >>> (10*index)) &&& 1023) % (2*m)
def rowMap (table : Nat) (i : Fin (2*m)) : Fin (2*m) :=
  ⟨rowAt table i.val,Nat.mod_lt _ (by decide)⟩

def checkRows (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n+1 => f n && checkRows f n

theorem checkRows_sound (f : Nat → Bool) (n : Nat) (h : checkRows f n = true) :
    ∀ i < n, f i = true := by
  induction n with
  | zero => exact fun _ h => by omega
  | succ n ih =>
    have ⟨hn,ht⟩ : f n = true ∧ checkRows f n = true := by simpa only [checkRows,Bool.and_eq_true] using h
    intro i hi
    by_cases eq : i=n
    · exact eq ▸ hn
    · exact ih ht i (by omega)

theorem table_onto (table : Nat)
    (h : checkRows (fun k => rowAt table (rowAt table k) == k) (2*m) = true) :
    (rowMap table).Surjective := by
  intro i
  exact ⟨rowMap table i, Fin.ext (beq_iff_eq.mp (checkRows_sound _ _ h _ i.isLt))⟩

theorem table_image (table : Nat) (x y : W)
    (h : checkRows (fun k => x.getLsbD (rowAt table k) == y.getLsbD k) (2*m) = true) :
    rowImage (rowMap table) x y := fun i => beq_iff_eq.mp (checkRows_sound _ _ h _ i.isLt)

end Signed2964.Orbit

namespace Signed3110

open Signed2964

def baseRaw : List W := rawInputs ++ [rawInputs.getD 0 0 &&& rawInputs.getD 2 0]

def orWire (js : List Nat) : W := (js.map (fun i => baseRaw.getD i 0)).foldr (· ||| ·) 0

def augmented (js : List Nat) : List W := baseRaw ++ [orWire js]

def initial (js : List Nat) : Finset W := ((augmented js).map norm).toFinset.erase 0

def Exclusion := ∀ js : List Nat, js.length ≤ 2 → ¬build basicOps goal 11 (initial js)

end Signed3110

namespace Signed3110

open Signed2964

def slot (j : Nat) : Fin 11 := if h : j<10 then ⟨j,by omega⟩ else 10

private theorem zeroSlot : baseRaw.getD (10 : Fin 11).val 0 = 0 := by rfl

private theorem slot_value (j : Nat) : baseRaw.getD (slot j).val 0 = baseRaw.getD j 0 := by
  by_cases h : j<10
  · simp [slot,h]
  · rw [show slot j = 10 by simp [slot,h],zeroSlot]
    exact (List.getD_eq_default _ _ (by change 10 ≤ j; omega)).symm

private theorem rightZero (w : W) : w ||| (0:W) = w := BitVec.or_zero

private theorem swap_pair (a b : Fin 11) : initial [a.val,b.val] = initial [b.val,a.val] := by
  simp only [initial,augmented,orWire,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil]
  rw [rightZero,rightZero,BitVec.or_comm]

theorem canonical_pair (js : List Nat) (h : js.length ≤ 2) :
    ∃ a b : Fin 11, a ≤ b ∧ initial js = initial [a.val,b.val] := by
  have reduce : ∃ a b : Fin 11, initial js = initial [a.val,b.val] := by
    rcases js with _ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩
    · refine ⟨10,10,?_⟩
      simp only [initial,augmented,orWire,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
        zeroSlot,rightZero]
    · refine ⟨slot a,10,?_⟩
      simp only [initial,augmented,orWire,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
        zeroSlot,slot_value,rightZero]
    · refine ⟨slot a,slot b,?_⟩
      simp only [initial,augmented,orWire,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,slot_value]
    · simp at h
  obtain ⟨a,b,eq⟩ := reduce
  by_cases ab : a ≤ b
  · exact ⟨a,b,ab,eq⟩
  · exact ⟨b,a,le_of_not_ge ab,eq.trans (swap_pair a b)⟩

theorem of_pairs (h : ∀ a b : Fin 11, a ≤ b → ¬build basicOps goal 11 (initial [a.val,b.val])) :
    Exclusion := by
  intro js width
  obtain ⟨a,b,ab,eq⟩ := canonical_pair js width
  rw [eq]
  exact h a b ab

end Signed3110

namespace Signed3110

open Signed2964

def wiresFor (js : List Nat) : List W := ((augmented js).map norm).eraseDups.filter (· != 0)

theorem wires_set (js : List Nat) : (wiresFor js).toFinset = initial js := by
  ext w
  simp [wiresFor,initial,and_comm]

def necessary (xs : List W) (a : W) : Bool := cuts (xs.filter (· != a)) != -1

def candidates (xs : List W) : List (List W) :=
  let fixed := xs.filter (necessary xs)
  let extra := xs.filter (fun a => !necessary xs a)
  (extra.sublists.map (fun r => fixed ++ r)).filter (fun ws => cuts ws == -1)

private theorem covers {s : Finset W} {k : Nat} (h : live basicOps goal k s)
    (xs : List W) (sub : s ⊆ xs.toFinset) : cuts xs = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  obtain ⟨x,hx,yes⟩ := live_separates (differs ⟨j,hj⟩) (goal_differs _) (ops_differs _) h
  have seen := (cuts_spec xs ⟨j,hj⟩).mpr ⟨x,List.mem_toFinset.mp (sub hx),yes⟩
  change (cuts xs)[j] = (BitVec.allOnes m)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using seen

theorem find_candidate {k : Nat} {xs : List W} {s : Finset W}
    (sub : s ⊆ xs.toFinset) (h : live basicOps goal k s) :
    ∃ ws ∈ candidates xs, ws.toFinset = s := by
  have fixed (a : W) (ha : necessary xs a = true) : a ∈ s := by
    by_contra outside
    have full := covers h (xs.filter (· != a)) (by
      intro w hw
      apply List.mem_toFinset.mpr
      apply List.mem_filter.mpr
      exact ⟨List.mem_toFinset.mp (sub hw), bne_iff_ne.mpr (fun eq => outside (eq ▸ hw))⟩)
    simp [necessary,full] at ha
  let mandatory := xs.filter (necessary xs)
  let extra := xs.filter (fun a => !necessary xs a)
  let chosen := extra.filter (fun a => decide (a ∈ s))
  have repr : (mandatory ++ chosen).toFinset = s := by
    ext a
    constructor
    · intro ha
      rcases List.mem_append.mp (List.mem_toFinset.mp ha) with must | keep
      · exact fixed a (List.mem_filter.mp must).2
      · exact of_decide_eq_true (List.mem_filter.mp keep).2
    · intro ha
      have ax := List.mem_toFinset.mp (sub ha)
      apply List.mem_toFinset.mpr
      apply List.mem_append.mpr
      cases flag : necessary xs a
      · exact Or.inr (List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨ax,by simp [flag]⟩,by simp [ha]⟩)
      · exact Or.inl (List.mem_filter.mpr ⟨ax,flag⟩)
  refine ⟨_,?_,repr⟩
  apply List.mem_filter.mpr
  exact ⟨List.mem_map.mpr ⟨chosen,List.mem_sublists.mpr List.filter_sublist,rfl⟩,
    beq_iff_eq.mpr (covers h _ (by rw [repr]))⟩

def admissible (roots : List (List W)) (a b : Fin 11) : Bool :=
  (candidates (wiresFor [a.val,b.val])).all fun ws => roots.any fun ys => ws.toFinset == ys.toFinset

theorem root_cover {allRoots : List (List W)} (group : Fin 11 → Fin 11 → List (List W))
    (small : ∀ a b, group a b ⊆ allRoots)
    (checked : ∀ a b : Fin 11, a ≤ b → admissible (group a b) a b = true)
    (dead : ∀ ws ∈ allRoots, ¬live basicOps goal 11 ws.toFinset) : Exclusion := by
  apply of_pairs
  intro a b ab run
  obtain ⟨s,sub,active⟩ := compress run
  obtain ⟨ws,hx,hs⟩ := find_candidate (xs := wiresFor [a.val,b.val])
    (by simpa only [wires_set] using sub) active
  obtain ⟨ys,hy,eq⟩ := List.any_eq_true.mp (List.all_eq_true.mp (checked a b ab) ws hx)
  apply dead ys (small a b hy)
  rw [←beq_iff_eq.mp eq,hs]
  exact active

end Signed3110

namespace Signed3110
def w0 : Signed2964.W := 0x780f03fb9e03f06e73ce67301c0705cf33ce739774e0307c00000000000000003f07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
def w1 : Signed2964.W := 0x3dee01fe070000000000000016b5d6ab703c0b0ed755d6b5a375e0703c0000001fffc0ffc1c000000000000007fffffffe0f03c3fffffffffffffc1c1f8
def w2 : Signed2964.W := 0x100200fc000000401000001001010001008083f000200000080080010f8000000000003f000000000000000000000000000000fc000000000000000003e00
def w3 : Signed2964.W := 0x3c07800003fe07001b07803a06f06006dee0002c0f0c00075af7b001a0507c000f81e00000ffc1c007c1e00fc1fe1801fffc000f03c30001fffffe007c1c1f8
def w4 : Signed2964.W := 0x78007f80e03c007f01e07038007807ce79cce60380e0b80701ee0360400706001f001ff83c0f801ff07c1e0f001e01ffffffffe0f03c3f81e07fe0fe1801c1c0
def w5 : Signed2964.W := 0x108410fe20ffe200104211088210913f009f0f808bff03e10042f88790211ff40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
def w6 : Signed2964.W := 0x210821084208441123ff00113fff800427e40227fc22008217ff200225fff120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
def w7 : Signed2964.W := 0x2108310a42fc441123ff10113fff810527e502a7fff200a217ff2802a5ffffa000000000003f000000ffc0000fffe00001f80001fffc000001ffc000007fffe00
def w8 : Signed2964.W := 0x318c31fe62ffe61133ff1119bfff913f27ff0fa7ffff03e317fff887b5fffff40000001f803ff80000ffc0000fffe007c1ffc3e1ffffc0f801fffe01e07ffffc0
def w9 : Signed2964.W := 0x40100000800008000000002008002002104220000000005f87e017c000000000000000000000000000000000000000000000000000000007e1f801f0000000000
def w10 : Signed2964.W := 0x4210821084208842410842220842245ffffff002008043fffffffff80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
def w11 : Signed2964.W := 0x4210921284fc8842414852220852255ffffff08283f043fffffffff880050f8100000000003f00000000000000000007fffffc0000fc00fffffffffe000003e00
def w12 : Signed2964.W := 0x509410fea0ffea00104211288a10b13f10df2f808bff03ff87e2ffc790211ff40000001f803ff8000000000000000007c007c3e000ffc0ffe1f83ff1e00003fc0
def w13 : Signed2964.W := 0x529492fea4ffea42514a532a8a52b57fffffff828bff43ffffffffff90251ff50000001f803ff8000000000000000007ffffffe000ffc0ffffffffffe00003fc0
def w14 : Signed2964.W := 0x6318a318c628cc5363ff42333fffa45ffffff227fca243fffffffffa25fff521000000000000000000ffc0000fffe007fffffc01ff0000fffffffffe007ffc000
def w15 : Signed2964.W := 0x739c03dce602ee030000003bae07b06000000000000003db76def6b7356070743fff81ffffc0ffc1c000001fffc1fe1800000000000000fffffffffffffc1c1f8
def w16 : Signed2964.W := 0x8421042108411084ffffffc01000401ffffffffffffffc04010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000
def w17 : Signed2964.W := 0x8421142308fd1084ffffffc01010411ffffffffffffffc2401000900c0810f8800000000003f00003fffffe000000007ffffffffffffff0000000000000003e00
def w18 : Signed2964.W := 0x94a514ff28fff284ffffffc89210d13fffffffffffffffe50142f987d0a11ffc0000001f803ff8003fffffe000000007fffffffffffffff800003e01e00003fc0
def w19 : Signed2964.W := 0xa52925294a495495ffffffd13fffc01ffffffffffffffc8617ff210265fff12800000000000000003fffffe00fffe007ffffffffffffff0001ffc000007ffc000
def w20 : Signed2964.W := 0xb5ac05ed6a037605b81705d9b605d02000000f703c0f0c000000000775e0707c3fff81ffffc0ffc1ff07c1ffffc1fe18000003fe0f03c30000000001fffc1c1f8
def w21 : Signed2964.W := 0xc431042188411884ffffffe01800601ffffffffffffffc5f87e017c04080000800000000000000003fffffe000000007ffffffffffffff07e1f801f0000000000
def w22 : Signed2964.W := 0xc63186318c6198c6ffffffe21842645ffffffffffffffffffffffff84084040900000000000000003fffffe000000007fffffffffffffffffffffffe000000000
def w23 : Signed2964.W := 0xd6b406f5ac03ba06d80007ea8000707ad01aed50000d0f5d6000d7b55000005c3fff81ffffc0ffc1ff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8
def w24 : Signed2964.W := 0xe7380701ce001c07e81d06f33c076040f740e07034000c1e779c073065c060083fff81e07fc007c1ff07c1ffffc1fe183ff83c1e0f000307ffffc1fe1ffc1c038
def w25 : Signed2964.W := 0xf7bc07fdee03fe07f81f07fbbe07f07ef7deef703c0f0fdf77def7b775e0707c3fff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
def w26 : Signed2964.W := 0xf83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
def w27 : Signed2964.W := 0xf83e1807f0fc3f08086118fc3f18798310432190c7f1147f87e01fc1f9f18f9e7e0f80007c3f07c00000001f0fc01e000000000000fc0007e1f801f01e7c03e38
def w28 : Signed2964.W := 0xf8be18fff0ffff08186319fcbf18f9bf10df2f90cfff17ff87e2ffc7f9f19ffe7e0f801ffc3fffc00000001f0fc01e07c007c3e000ffc0ffe1f83ff1fe7c03ff8
def w29 : Signed2964.W := 0xf93e290df20c7f192bff08fd3ffff88637e62337fc3314df97ff37c37dfff1be7e0f80007c0007c000ffc01f0ffffe0001f80001ff000007e1ffc1f01e7ffc038
def w30 : Signed2964.W := 0xfa3e8a15f424bf4a49294afe3f4a7cdffffff112449157fffffffff979f4849f7e0f80007c0007c00000001f0fc01e07fffffc00000000fffffffffe1e7c00038
def w31 : Signed2964.W := 0xfc3f0c25f8453f8cfffffffc3f08789ffffffffffffffc5f87e017c179f0809e7e0f80007c0007c03fffffff0fc01e07ffffffffffffff07e1f801f01e7c00038
def w32 : Signed2964.W := 0xffc0407fff100020fc84207fc421021ff9000ff9104023fff8840007fe422200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
def w33 : Signed2964.W := 0xffc0507ffffc0020fcc4307fc431031ff9010ff993f023fff8840807fe432f80bff0001fffff00003f00001ff0000007fe0003fe00fc00fffe000001ff8003e00
def w34 : Signed2964.W := 0xffc450ffffffe220fcc6317fc631933ff99f0ff99bff23fff8c6f887fe633ff4bff0001ffffff8003f00001ff0000007fe07c3fe00ffc0fffe003e01ff8003fc0
def w35 : Signed2964.W := 0xffc8617fff184431ffff207fffff821fffe40ffffc6223ffffff2007fffff320bff0001fffc000003fffc01fffffe007fff803ffff0000ffffffc001fffffc000
def w36 : Signed2964.W := 0xffd0c27fff308862fd8c627fcc63265ffffffffb10c063fffffffffffe462601bff0001fffc000003f00001ff0000007fffffffe000000ffffffffffff8000000
def w37 : Signed2964.W := 0xffe1447fff5110a4ffffffffd421421ffffffffffffffffff9840107fec22208bff0001fffc000003ffffffff0000007fffffffffffffffffe000001ff8000000
def w38 : Signed2964.W := 0xfffe487fff143f28fca528ffff297a9ff9422ff9545137ffffe417c7fff2a29effff801fffc007c03f00001fffc01e07fe0003fe000000fffff801f1fffc00038
def w39 : Signed2964.W := 0xffffffc000820000ffffffffffffffe8420844000104010822084214000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000
def w40 : Signed2964.W := 0xffffffc080820800ffffffffffffffea524a64000104015fa7e857d4000008403fffffe0000000003ffffffffffffff80000000000000007e1f801f0000000000
def w41 : Signed2964.W := 0xffffffc200fe0000ffffffffffffffe94209448083f4012822084a1480010fc03fffffe0003f00003ffffffffffffff80000000000fc000000000000000003e00
def w42 : Signed2964.W := 0xffffffc5f0863f08ffffffffffffffea524a65104515155fa7e857d579f088de7fffffe07c0007c03ffffffffffffff80000000000000007e1f801f01e7c00038
def w43 : Signed2964.W := 0xffffffc8428a4411ffffffffffffffec67ec4627fd26018a37ff621625fff9603fffffe0000000003ffffffffffffff801f80001ff00000001ffc000007ffc000
def w44 : Signed2964.W := 0xffffffd084a28842fffffffffffffffffffff402018443fffffffffc00040c413fffffe0000000003ffffffffffffffffffffc00000000fffffffffe000000000
def w45 : Signed2964.W := 0xffffffe108c31084fffffffffffffffffffffffffffffd0c23084314408008483fffffe0000000003fffffffffffffffffffffffffffff0000000000000000000
def w46 : Signed2964.W := 0xfffffffe20ffe200ffffffffffffffff429f4f808bff03e9224afa9790211ff43fffffff803ff8003fffffffffffffffc007c3e000ffc0f800003e01e00003fc0
def w47 : Signed2964.W := 0xffffffffff920020fffffffffffffffffb084ff9114423fffa8c4217fe422a40bfffffffffc000003ffffffffffffffffe0003fe000000fffe000001ff8000000
def w48 : Signed2964.W := 0xffffffffffffffff82108400208400108410884422088a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
def w49 : Signed2964.W := 0xffffffffffffffff82108420288420129452a84422088a5fc7f097e0010840003fffffffffffffffc0000000000000000000000000000007e1f801f0000000000
def w50 : Signed2964.W := 0xffffffffffffffff8250940020940111841188c4a3f88a3044108c2081094f803fffffffffffffffc0000000000000000000000000fc000000000000000003e00
def w51 : Signed2964.W := 0xffffffffffffffff8a318cfc3f8c78929452a95466199e5fc7f097e179f8c09e7fffffffffffffffc000001f0fc01e000000000000000007e1f801f01e7c00038
def w52 : Signed2964.W := 0xffffffffffffffff92529508a294913f849f8fc4abff8bf14452fca791295ff43fffffffffffffffc000000000000007c007c3e000ffc0f800003e01e00003fc0
def w53 : Signed2964.W := 0xffffffffffffffffa3ff84113fff8014a7f48a67fe2a8a9257ffa42225fff1203fffffffffffffffc0ffc0000fffe00001f80001ff00000001ffc000007ffc000
def w54 : Signed2964.W := 0xffffffffffffffffc318c62228c6245ffffff8462288cbfffffffff8010c44013fffffffffffffffc000000000000007fffffc00000000fffffffffe000000000
def w55 : Signed2964.W := 0xfffffffffffffffffe94a47fe4a5021ffd108ffd3248abfffc948427ff4a6200bfffffffffffffffff00001ff0000007fe0003fe000000fffe000001ff8000000
def w56 : Signed2964.W := 0xffffffffffffffffffffffc03084401ffffffffffffffe1445108520418840083fffffffffffffffffffffe000000007ffffffffffffff0000000000000000000
def w57 : Signed2964.W := 0xfffffffffffffffffffffffffffffff8c618cc44230c8b186618c634010848403ffffffffffffffffffffffffffffff8000000000000000000000000000000000
def t0 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w48]
def t1 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w48]
def t2 : List Signed2964.W := [w4,w5,w6,w10,w16,w25,w26,w32,w39,w48]
def t3 : List Signed2964.W := [w2,w4,w5,w6,w10,w16,w25,w26,w32,w39,w48]
def t4 : List Signed2964.W := [w2,w6,w10,w16,w24,w26,w32,w39,w48]
def t5 : List Signed2964.W := [w5,w6,w10,w16,w24,w25,w26,w32,w39,w48]
def t6 : List Signed2964.W := [w2,w6,w10,w16,w24,w25,w26,w32,w39,w48]
def t7 : List Signed2964.W := [w2,w5,w6,w10,w16,w24,w26,w32,w39,w48]
def t8 : List Signed2964.W := [w2,w5,w6,w10,w16,w24,w25,w26,w32,w39,w48]
def t9 : List Signed2964.W := [w5,w6,w10,w16,w23,w25,w26,w32,w39,w48]
def t10 : List Signed2964.W := [w2,w5,w6,w10,w16,w23,w25,w26,w32,w39,w48]
def t11 : List Signed2964.W := [w3,w5,w6,w10,w16,w25,w26,w32,w39,w48]
def t12 : List Signed2964.W := [w2,w3,w5,w6,w10,w16,w25,w26,w32,w39,w48]
def t13 : List Signed2964.W := [w5,w6,w10,w16,w20,w25,w26,w32,w39,w48]
def t14 : List Signed2964.W := [w2,w5,w6,w10,w16,w20,w25,w26,w32,w39,w48]
def t15 : List Signed2964.W := [w5,w6,w10,w15,w16,w25,w26,w32,w39,w48]
def t16 : List Signed2964.W := [w2,w5,w6,w10,w15,w16,w25,w26,w32,w39,w48]
def t17 : List Signed2964.W := [w1,w5,w6,w10,w16,w25,w26,w32,w39,w48]
def t18 : List Signed2964.W := [w1,w2,w5,w6,w10,w16,w25,w26,w32,w39,w48]
def t19 : List Signed2964.W := [w0,w5,w6,w10,w16,w25,w26,w32,w39,w48]
def t20 : List Signed2964.W := [w0,w2,w5,w6,w10,w16,w25,w26,w32,w39,w48]
def t21 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w28,w32,w39,w48]
def t22 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w28,w32,w39,w48]
def t23 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w29,w32,w39,w48]
def t24 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w29,w32,w39,w48]
def t25 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w38,w39,w48]
def t26 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w38,w39,w48]
def t27 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w30,w32,w39,w48]
def t28 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w30,w32,w39,w48]
def t29 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w31,w32,w39,w48]
def t30 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w31,w32,w39,w48]
def t31 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w42,w48]
def t32 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w42,w48]
def t33 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w48,w51]
def t34 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w48,w51]
def t35 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w27,w32,w39,w48]
def t36 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w27,w32,w39,w48]
def t37 : List Signed2964.W := [w5,w6,w8,w10,w16,w25,w26,w32,w39,w48]
def t38 : List Signed2964.W := [w2,w5,w6,w8,w10,w16,w25,w26,w32,w39,w48]
def t39 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w34,w39,w48]
def t40 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w34,w39,w48]
def t41 : List Signed2964.W := [w5,w6,w10,w13,w16,w25,w26,w32,w39,w48]
def t42 : List Signed2964.W := [w2,w5,w6,w10,w13,w16,w25,w26,w32,w39,w48]
def t43 : List Signed2964.W := [w5,w6,w10,w16,w18,w25,w26,w32,w39,w48]
def t44 : List Signed2964.W := [w2,w5,w6,w10,w16,w18,w25,w26,w32,w39,w48]
def t45 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w46,w48]
def t46 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w46,w48]
def t47 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w48,w52]
def t48 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w48,w52]
def t49 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w35,w39,w48]
def t50 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w35,w39,w48]
def t51 : List Signed2964.W := [w5,w6,w10,w14,w16,w25,w26,w32,w39,w48]
def t52 : List Signed2964.W := [w2,w5,w6,w10,w14,w16,w25,w26,w32,w39,w48]
def t53 : List Signed2964.W := [w5,w6,w10,w16,w19,w25,w26,w32,w39,w48]
def t54 : List Signed2964.W := [w2,w5,w6,w10,w16,w19,w25,w26,w32,w39,w48]
def t55 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w43,w48]
def t56 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w43,w48]
def t57 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w48,w53]
def t58 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w48,w53]
def t59 : List Signed2964.W := [w5,w6,w7,w10,w16,w25,w26,w32,w39,w48]
def t60 : List Signed2964.W := [w2,w5,w6,w7,w10,w16,w25,w26,w32,w39,w48]
def t61 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w36,w39,w48]
def t62 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w36,w39,w48]
def t63 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w37,w39,w48]
def t64 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w37,w39,w48]
def t65 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w47,w48]
def t66 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w47,w48]
def t67 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w48,w55]
def t68 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w48,w55]
def t69 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w33,w39,w48]
def t70 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w33,w39,w48]
def t71 : List Signed2964.W := [w5,w6,w10,w16,w22,w25,w26,w32,w39,w48]
def t72 : List Signed2964.W := [w2,w5,w6,w10,w16,w22,w25,w26,w32,w39,w48]
def t73 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w44,w48]
def t74 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w44,w48]
def t75 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w48,w54]
def t76 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w48,w54]
def t77 : List Signed2964.W := [w5,w6,w10,w11,w16,w25,w26,w32,w39,w48]
def t78 : List Signed2964.W := [w2,w5,w6,w10,w11,w16,w25,w26,w32,w39,w48]
def t79 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w45,w48]
def t80 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w45,w48]
def t81 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w48,w56]
def t82 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w48,w56]
def t83 : List Signed2964.W := [w5,w6,w10,w16,w17,w25,w26,w32,w39,w48]
def t84 : List Signed2964.W := [w2,w5,w6,w10,w16,w17,w25,w26,w32,w39,w48]
def t85 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w48,w57]
def t86 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w48,w57]
def t87 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w41,w48]
def t88 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w41,w48]
def t89 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w48,w50]
def t90 : List Signed2964.W := [w2,w5,w6,w10,w16,w25,w26,w32,w39,w48,w50]
def t91 : List Signed2964.W := [w4,w5,w6,w9,w10,w16,w25,w26,w32,w39,w48]
def t92 : List Signed2964.W := [w5,w6,w9,w16,w25,w26,w30,w32,w39,w48]
def t93 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w39,w48,w51]
def t94 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w31,w32,w39,w48]
def t95 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w28,w32,w39,w48]
def t96 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w38,w39,w48]
def t97 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w39,w42,w48]
def t98 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w29,w32,w39,w48]
def t99 : List Signed2964.W := [w0,w5,w6,w9,w10,w16,w25,w26,w32,w39,w48]
def t100 : List Signed2964.W := [w5,w6,w9,w10,w15,w16,w25,w26,w32,w39,w48]
def t101 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w39,w48,w56]
def t102 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w39,w48,w55]
def t103 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w39,w48,w57]
def t104 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w39,w48,w53]
def t105 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w48,w49]
def t106 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w39,w48,w49]
def t107 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w37,w39,w48]
def t108 : List Signed2964.W := [w5,w6,w9,w10,w16,w19,w25,w26,w32,w39,w48]
def t109 : List Signed2964.W := [w5,w6,w10,w16,w21,w25,w26,w32,w39,w48]
def t110 : List Signed2964.W := [w5,w6,w9,w10,w16,w21,w25,w26,w32,w39,w48]
def t111 : List Signed2964.W := [w5,w6,w9,w10,w16,w20,w25,w26,w32,w39,w48]
def t112 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w30,w32,w39,w48]
def t113 : List Signed2964.W := [w5,w6,w9,w10,w13,w16,w25,w26,w32,w39,w48]
def t114 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w39,w44,w48]
def t115 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w39,w48,w54]
def t116 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w36,w39,w48]
def t117 : List Signed2964.W := [w5,w6,w9,w10,w16,w22,w25,w26,w32,w39,w48]
def t118 : List Signed2964.W := [w5,w6,w9,w10,w14,w16,w25,w26,w32,w39,w48]
def t119 : List Signed2964.W := [w5,w6,w9,w10,w16,w24,w25,w26,w32,w39,w48]
def t120 : List Signed2964.W := [w1,w5,w6,w9,w10,w16,w25,w26,w32,w39,w48]
def t121 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w39,w46,w48]
def t122 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w34,w39,w48]
def t123 : List Signed2964.W := [w5,w6,w9,w10,w16,w18,w25,w26,w32,w39,w48]
def t124 : List Signed2964.W := [w5,w6,w8,w9,w10,w16,w25,w26,w32,w39,w48]
def t125 : List Signed2964.W := [w5,w6,w10,w12,w16,w25,w26,w32,w39,w48]
def t126 : List Signed2964.W := [w5,w6,w9,w10,w12,w16,w25,w26,w32,w39,w48]
def t127 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w39,w47,w48]
def t128 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w39,w43,w48]
def t129 : List Signed2964.W := [w5,w6,w10,w16,w25,w26,w32,w39,w40,w48]
def t130 : List Signed2964.W := [w5,w6,w9,w10,w16,w25,w26,w32,w39,w40,w48]
def rootWords : List (List Signed2964.W) := [t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28,t29,t30,t31,t32,t33,t34,t35,t36,t37,t38,t39,t40,t41,t42,t43,t44,t45,t46,t47,t48,t49,t50,t51,t52,t53,t54,t55,t56,t57,t58,t59,t60,t61,t62,t63,t64,t65,t66,t67,t68,t69,t70,t71,t72,t73,t74,t75,t76,t77,t78,t79,t80,t81,t82,t83,t84,t85,t86,t87,t88,t89,t90]
def rootReps : List (List Signed2964.W) := [t0,t1,t2,t3,t4,t5,t6,t8,t9,t10,t11,t12,t14,t15,t16,t18,t20,t24,t26,t30,t34,t35,t36,t50,t52,t54,t56,t58,t59,t60,t63,t64,t66,t68,t69,t70,t82,t83,t84,t89,t90]
private def choices : Array (List (Fin 91)) := #[[0,1],[0,1,2,3],[0,1,4,5,6,7,8],[0,1,9,10],[0,1,11,12],[0,1,13,14],[0,1,15,16],[0,1,17,18],[0,1,19,20],[0,1],[0,1],[],[0,1],[0,1,21,22],[0,1,23,24],[0,1,25,26],[0,1,27,28],[0,1,29,30],[0,1,31,32],[0,1,33,34],[0,1,35,36],[0,1],[],[],[0,1],[0,1,37,38],[0,1,39,40],[0,1,41,42],[0,1,43,44],[0,1,45,46],[0,1,47,48],[0,1],[0,1],[],[],[],[0,1],[0,1,49,50],[0,1,51,52],[0,1,53,54],[0,1,55,56],[0,1,57,58],[0,1,59,60],[0,1],[],[],[],[],[0,1],[0,1,61,62],[0,1,63,64],[0,1,65,66],[0,1,67,68],[0,1,69,70],[0,1],[],[],[],[],[],[0,1],[0,1,71,72],[0,1,73,74],[0,1,75,76],[0,1,77,78],[0,1],[],[],[],[],[],[],[0,1],[0,1,79,80],[0,1,81,82],[0,1,83,84],[0,1],[],[],[],[],[],[],[],[0,1],[0,1,85,86],[0,1,87,88],[0,1],[],[],[],[],[],[],[],[],[0,1],[0,1,89,90],[0,1],[],[],[],[],[],[],[],[],[],[0,1],[0,1],[],[],[],[],[],[],[],[],[],[],[0,1]]
private def family (a b : Fin 11) : List (List Signed2964.W) :=
  ((choices[a.val*11+b.val]?).getD []).map fun i => rootWords[i.val]'(by exact i.isLt)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem family_checked : ∀ a b : Fin 11, a ≤ b → admissible (family a b) a b = true := by decide +kernel
theorem of_roots (h : ∀ ws ∈ rootWords, ¬Signed2964.live Signed2964.basicOps Signed2964.goal 11 ws.toFinset) : Exclusion := by
  apply root_cover family _ family_checked h
  intro a b ws hw
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
  exact List.getElem_mem _
end Signed3110

namespace Signed3110
open Signed2964 Signed2964.Orbit
private theorem image_and {p : Fin (2*m) → Fin (2*m)} {a b c d : W} (h : rowImage p a b) (k : rowImage p c d) :
    rowImage p (a &&& c) (b &&& d) := by intro i; simp only [BitVec.getLsbD_and,h i,k i]
private theorem image_or {p : Fin (2*m) → Fin (2*m)} {a b c d : W} (h : rowImage p a b) (k : rowImage p c d) :
    rowImage p (a ||| c) (b ||| d) := by intro i; simp only [BitVec.getLsbD_or,h i,k i]
private def raw0 : W := 0x843f80211fc01f807e0f80441f80f810821108fc3f0f020882108488a1f8f83c0007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07
private def raw1 : W := 0xf83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def raw2 : W := 0x108410fe20ffe200104211088210913f009f0f808bff03e10042f88790211ff40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def raw3 : W := 0x210821084208441123ff00113fff800427e40227fc22008217ff200225fff120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def raw4 : W := 0xffc0407fff100020fc84207fc421021ff9000ff9104023fff8840007fe422200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def raw5 : W := 0x4210821084208842410842220842245ffffff002008043fffffffff80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def raw6 : W := 0x8421042108411084ffffffc01000401ffffffffffffffc04010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def raw7 : W := 0xffffffc000820000ffffffffffffffe8420844000104010822084214000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def raw8 : W := 0xffffffffffffffff82108400208400108410884422088a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def table1 : Nat := 0x61d85619886116e5b16d5bd6b5dd755d9785d15c5615a5655d56d565515555de97a9e679de87954c5294b535494992449523769db759d875dd9751d5745d274d324c1314cd2f43d0b4350c4390a42109701bf705c3709be6e9b96edbd6f1b56d1b66e1b76c1af6c5b36c9ac6adae6b5826018160d7f5a1695a9675ed7d5e97c5f97958d62591665955f57960585725c5735c150545535494e53e0080e01809ff69daa6a1a96999d6819e6859f671f67e5f77e1f5641926458f7edfe7f1fd7e9a3691a56899865d9966d9a64d94659957c1f47bdf27c5f37adee7b1ed6318b6358e6258a785e4789e378144519475154850d204892147d3a4f13d4ed3e4e51946d1a47118735d0739cf7312b4b12d4b92a41907415df775de77141501424fd1e475354dd364e1344511345517459104451272dc7725c8729c6711c54a12949d0240d0421483210862086c1a86b1b4691d4731d0761c85a1585815c5b1645414853154e73a0e4394e638c4a1204912c470902208c21360d9350d6354d7348d333cd0344300b82f0c42d0340902c0a03008018072f8bd2fcc1300bc2e0b72e4bb2e8b32c8b42d8b52b8ad2bcb12c0aa2a4ac2ac801f87f2047d198671a0651e47b1e07a1f077184601886418c5d1705e17c701bc711b84e13c511404c134fe404ff400fd294a8298a72909b2789c27c9d268f43dcf53d8f32389023c8d3e4fc3e8fb3e0a1288a328096254972649824492250933b8f23b4f03bcf13a4ec3a8eb2288922c8c21c8837ce2380e1378421104510c461041e0801f074380e83b0e43c0dc17064180681632cce330cd328290a82b0b0280100500cdd36cdc3683f0f8400f41c06c330d4340d8320481104c150500e03c10324c531cc6320c4308c3098270940000402
private abbrev perm1 := rowMap table1
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem onto1 : perm1.Surjective := table_onto _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem fixes1 : move perm1 goal = goal := move_literal (table_image table1 goal goal (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to0 : rowImage perm1 raw0 raw0 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to1 : rowImage perm1 raw1 raw5 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to2 : rowImage perm1 raw2 raw8 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to3 : rowImage perm1 raw3 raw3 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to4 : rowImage perm1 raw4 raw4 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to5 : rowImage perm1 raw5 raw1 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to6 : rowImage perm1 raw6 raw7 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to7 : rowImage perm1 raw7 raw6 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to8 : rowImage perm1 raw8 raw2 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w0 : move perm1 w0 = w24 := move_literal (image_or raw1to0 raw1to8) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w1 : move perm1 w1 = w15 := move_literal (image_or raw1to0 raw1to7) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w5 : move perm1 w5 = w48 := move_literal raw1to2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w6 : move perm1 w6 = w6 := move_literal raw1to3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w8 : move perm1 w8 = w53 := move_literal (image_or raw1to2 raw1to3) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w9 : move perm1 w9 = w9 := move_literal (image_and raw1to1 raw1to5) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w10 : move perm1 w10 = w26 := move_literal raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w12 : move perm1 w12 = w49 := move_literal (image_or raw1to2 (image_and raw1to1 raw1to5)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w13 : move perm1 w13 = w51 := move_literal (image_or raw1to2 raw1to5) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w14 : move perm1 w14 = w29 := move_literal (image_or raw1to3 raw1to5) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w16 : move perm1 w16 = w39 := move_literal raw1to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w18 : move perm1 w18 = w57 := move_literal (image_or raw1to2 raw1to6) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w20 : move perm1 w20 = w4 := move_literal (image_or raw1to0 raw1to5) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w22 : move perm1 w22 = w42 := move_literal (image_or raw1to5 raw1to6) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w24 : move perm1 w24 = w0 := move_literal (image_or raw1to0 raw1to2) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w25 : move perm1 w25 = w25 := move_literal raw1to0 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w26 : move perm1 w26 = w10 := move_literal raw1to1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w30 : move perm1 w30 = w30 := move_literal (image_or raw1to1 raw1to5) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w32 : move perm1 w32 = w32 := move_literal raw1to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w34 : move perm1 w34 = w55 := move_literal (image_or raw1to2 raw1to4) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w36 : move perm1 w36 = w38 := move_literal (image_or raw1to4 raw1to5) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w39 : move perm1 w39 = w16 := move_literal raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w40 : move perm1 w40 = w21 := move_literal (image_or raw1to7 (image_and raw1to1 raw1to5)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w43 : move perm1 w43 = w19 := move_literal (image_or raw1to3 raw1to7) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w44 : move perm1 w44 = w31 := move_literal (image_or raw1to5 raw1to7) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w46 : move perm1 w46 = w56 := move_literal (image_or raw1to2 raw1to7) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w47 : move perm1 w47 = w37 := move_literal (image_or raw1to4 raw1to7) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w48 : move perm1 w48 = w5 := move_literal raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w53 : move perm1 w53 = w8 := move_literal (image_or raw1to3 raw1to8) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w54 : move perm1 w54 = w28 := move_literal (image_or raw1to5 raw1to8) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w55 : move perm1 w55 = w34 := move_literal (image_or raw1to4 raw1to8) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w56 : move perm1 w56 = w46 := move_literal (image_or raw1to6 raw1to8) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv1w57 : move perm1 w57 = w18 := move_literal (image_or raw1to7 raw1to8) (by decide +kernel) (by decide +kernel)
private def table2 : Nat := 0x6edba6f5bc6e5b66d5b86ddb46659866d9a65d9e675a06859f6719464d966557d5f17b5f9795e96458d66595625815f5855e4f53b4e93c4f9394dd364d5384d11545117459134691946d1c4611144112705c070dc26f9bf8060080e027fdfc7edfe7f5fa6a1a76a9a9699a468da5689b16c1b36c9af6b1ae6b5ab7c5f27c1f47cdef7ddf67e5f87d5ec7adee7b58d6318e62d906499163d896298661d88611855b56e5bd6b5b1e77a9e97a1e57994b5314d5254a4952648d246058260d7f601695a9675a1e2785e478de0775df779dc515475114652143501415093f485204891f4791d5d9775e1745d5595715a5755b5615555957551d776dd8769d9759d2755d474dd14c5324cd2f4c10c43d0d4390b4250a421725cd705c55154d525414f539c8725cb729c7739cd741cf731c4719c54b52b4b12e4a9284a52740d044090641d052e4b82ecba2dcb42ccb62d4b225c96264982549c26c9e27c9d268922449424c7b1e8791f0771e0621846418c601785d17c5c0ec390e03a0f0370d4340cc360c8130481505011060170641a0580f038102fcbe304c02f0bd3fcfe405003f4fa3e4fc3ecf8298a52a0a7290a2284a3280af2b8b12c0ad2a8ac2aca93bcf03b8f23c4ed3d4f43dcf63ccea3a4ec3ac8b2288c2248e2408f234872208421486208831ac6c1b4691a8e53a0e7398e3390491284b11c4808c24084221fc802047d1f8671a065198e037ce2384de36cdd370da10c4510844118410f83f1003d07c1e0801d0701b1d0751d8721cc571685816c591585315055148d5364d6360d7350d034cd2344cf0bc300c42d0b80a0340b0300901c08018701c46e1bc4f144501384d130c631cc9320c5330cb338cd328c2310c30ac290a82c0a02609c25004020000401403
private abbrev perm2 := rowMap table2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem onto2 : perm2.Surjective := table_onto _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem fixes2 : move perm2 goal = goal := move_literal (table_image table2 goal goal (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to0 : rowImage perm2 raw0 raw1 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to1 : rowImage perm2 raw1 raw0 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to2 : rowImage perm2 raw2 raw5 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to3 : rowImage perm2 raw3 raw8 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to4 : rowImage perm2 raw4 raw6 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to5 : rowImage perm2 raw5 raw2 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to6 : rowImage perm2 raw6 raw4 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to7 : rowImage perm2 raw7 raw7 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to8 : rowImage perm2 raw8 raw3 := table_image _ _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w0 : move perm2 w0 = w29 := move_literal (image_or raw2to0 raw2to8) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w2 : move perm2 w2 = w9 := move_literal (image_and raw2to0 raw2to2) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w4 : move perm2 w4 = w4 := move_literal (image_or raw2to0 raw2to1) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w5 : move perm2 w5 = w10 := move_literal raw2to2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w6 : move perm2 w6 = w48 := move_literal raw2to3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w8 : move perm2 w8 = w54 := move_literal (image_or raw2to2 raw2to3) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w9 : move perm2 w9 = w2 := move_literal (image_and raw2to1 raw2to5) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w10 : move perm2 w10 = w5 := move_literal raw2to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w11 : move perm2 w11 = w12 := move_literal (image_or raw2to5 (image_and raw2to0 raw2to2)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w13 : move perm2 w13 = w13 := move_literal (image_or raw2to2 raw2to5) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w15 : move perm2 w15 = w38 := move_literal (image_or raw2to0 raw2to6) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w16 : move perm2 w16 = w32 := move_literal raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w18 : move perm2 w18 = w36 := move_literal (image_or raw2to2 raw2to6) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w19 : move perm2 w19 = w55 := move_literal (image_or raw2to3 raw2to6) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w21 : move perm2 w21 = w33 := move_literal (image_or raw2to6 (image_and raw2to1 raw2to5)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w22 : move perm2 w22 = w34 := move_literal (image_or raw2to5 raw2to6) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w24 : move perm2 w24 = w30 := move_literal (image_or raw2to0 raw2to2) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w25 : move perm2 w25 = w26 := move_literal raw2to0 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w26 : move perm2 w26 = w25 := move_literal raw2to1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w28 : move perm2 w28 = w20 := move_literal (image_or raw2to1 raw2to2) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w29 : move perm2 w29 = w0 := move_literal (image_or raw2to1 raw2to3) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w30 : move perm2 w30 = w24 := move_literal (image_or raw2to1 raw2to5) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w31 : move perm2 w31 = w3 := move_literal (image_or raw2to1 raw2to6) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w32 : move perm2 w32 = w16 := move_literal raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w34 : move perm2 w34 = w22 := move_literal (image_or raw2to2 raw2to4) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w35 : move perm2 w35 = w56 := move_literal (image_or raw2to3 raw2to4) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w36 : move perm2 w36 = w18 := move_literal (image_or raw2to4 raw2to5) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w37 : move perm2 w37 = w37 := move_literal (image_or raw2to4 raw2to6) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w38 : move perm2 w38 = w15 := move_literal (image_or raw2to1 raw2to4) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w39 : move perm2 w39 = w39 := move_literal raw2to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w41 : move perm2 w41 = w40 := move_literal (image_or raw2to7 (image_and raw2to0 raw2to2)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w42 : move perm2 w42 = w1 := move_literal (image_or raw2to1 raw2to7) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w43 : move perm2 w43 = w57 := move_literal (image_or raw2to3 raw2to7) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w44 : move perm2 w44 = w46 := move_literal (image_or raw2to5 raw2to7) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w45 : move perm2 w45 = w47 := move_literal (image_or raw2to6 raw2to7) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w46 : move perm2 w46 = w44 := move_literal (image_or raw2to2 raw2to7) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w48 : move perm2 w48 = w6 := move_literal raw2to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w49 : move perm2 w49 = w7 := move_literal (image_or raw2to8 (image_and raw2to1 raw2to5)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w51 : move perm2 w51 = w23 := move_literal (image_or raw2to1 raw2to8) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w52 : move perm2 w52 = w14 := move_literal (image_or raw2to2 raw2to8) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w53 : move perm2 w53 = w53 := move_literal (image_or raw2to3 raw2to8) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w54 : move perm2 w54 = w8 := move_literal (image_or raw2to5 raw2to8) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w55 : move perm2 w55 = w19 := move_literal (image_or raw2to4 raw2to8) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w56 : move perm2 w56 = w35 := move_literal (image_or raw2to6 raw2to8) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem mv2w57 : move perm2 w57 = w43 := move_literal (image_or raw2to7 raw2to8) (by decide +kernel) (by decide +kernel)
private theorem carryt13 (h : ¬ live basicOps goal 11 t2.toFinset) : ¬ live basicOps goal 11 t13.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t13.toFinset.image (move perm1) = t2.toFinset := by
    simp only [t13,t2,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w16,mv1w20,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt91 (h : ¬ live basicOps goal 11 t3.toFinset) : ¬ live basicOps goal 11 t91.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t91.toFinset.image (move perm2) = t3.toFinset := by
    simp only [t91,t3,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w4,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt19 (h : ¬ live basicOps goal 11 t5.toFinset) : ¬ live basicOps goal 11 t19.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t19.toFinset.image (move perm1) = t5.toFinset := by
    simp only [t19,t5,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w0,mv1w5,mv1w6,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt27 (h : ¬ live basicOps goal 11 t5.toFinset) : ¬ live basicOps goal 11 t27.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t27.toFinset.image (move perm2) = t5.toFinset := by
    simp only [t27,t5,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w30,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt92 (h : ¬ live basicOps goal 11 t6.toFinset) : ¬ live basicOps goal 11 t92.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t92.toFinset.image (move perm2) = t6.toFinset := by
    simp only [t92,t6,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w16,mv2w25,mv2w26,mv2w30,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt33 (h : ¬ live basicOps goal 11 t9.toFinset) : ¬ live basicOps goal 11 t33.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t33.toFinset.image (move perm2) = t9.toFinset := by
    simp only [t33,t9,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48,mv2w51] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt93 (h : ¬ live basicOps goal 11 t10.toFinset) : ¬ live basicOps goal 11 t93.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t93.toFinset.image (move perm2) = t10.toFinset := by
    simp only [t93,t10,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48,mv2w51] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt29 (h : ¬ live basicOps goal 11 t11.toFinset) : ¬ live basicOps goal 11 t29.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t29.toFinset.image (move perm2) = t11.toFinset := by
    simp only [t29,t11,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w31,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt94 (h : ¬ live basicOps goal 11 t12.toFinset) : ¬ live basicOps goal 11 t94.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t94.toFinset.image (move perm2) = t12.toFinset := by
    simp only [t94,t12,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w31,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt95 (h : ¬ live basicOps goal 11 t14.toFinset) : ¬ live basicOps goal 11 t95.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t95.toFinset.image (move perm2) = t14.toFinset := by
    simp only [t95,t14,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w28,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt17 (h : ¬ live basicOps goal 11 t15.toFinset) : ¬ live basicOps goal 11 t17.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t17.toFinset.image (move perm1) = t15.toFinset := by
    simp only [t17,t15,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w1,mv1w5,mv1w6,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt25 (h : ¬ live basicOps goal 11 t15.toFinset) : ¬ live basicOps goal 11 t25.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t25.toFinset.image (move perm2) = t15.toFinset := by
    simp only [t25,t15,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w38,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt96 (h : ¬ live basicOps goal 11 t16.toFinset) : ¬ live basicOps goal 11 t96.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t96.toFinset.image (move perm2) = t16.toFinset := by
    simp only [t96,t16,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w38,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt97 (h : ¬ live basicOps goal 11 t18.toFinset) : ¬ live basicOps goal 11 t97.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t97.toFinset.image (move perm2) = t18.toFinset := by
    simp only [t97,t18,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w42,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt98 (h : ¬ live basicOps goal 11 t20.toFinset) : ¬ live basicOps goal 11 t98.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t98.toFinset.image (move perm2) = t20.toFinset := by
    simp only [t98,t20,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w29,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt99 (h : ¬ live basicOps goal 11 t24.toFinset) : ¬ live basicOps goal 11 t99.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t99.toFinset.image (move perm2) = t24.toFinset := by
    simp only [t99,t24,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w0,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt100 (h : ¬ live basicOps goal 11 t26.toFinset) : ¬ live basicOps goal 11 t100.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t100.toFinset.image (move perm2) = t26.toFinset := by
    simp only [t100,t26,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w15,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt101 (h : ¬ live basicOps goal 11 t50.toFinset) : ¬ live basicOps goal 11 t101.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t101.toFinset.image (move perm2) = t50.toFinset := by
    simp only [t101,t50,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48,mv2w56] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt102 (h : ¬ live basicOps goal 11 t54.toFinset) : ¬ live basicOps goal 11 t102.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t102.toFinset.image (move perm2) = t54.toFinset := by
    simp only [t102,t54,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48,mv2w55] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt103 (h : ¬ live basicOps goal 11 t56.toFinset) : ¬ live basicOps goal 11 t103.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t103.toFinset.image (move perm2) = t56.toFinset := by
    simp only [t103,t56,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48,mv2w57] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt104 (h : ¬ live basicOps goal 11 t58.toFinset) : ¬ live basicOps goal 11 t104.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t104.toFinset.image (move perm2) = t58.toFinset := by
    simp only [t104,t58,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48,mv2w53] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt105 (h : ¬ live basicOps goal 11 t59.toFinset) : ¬ live basicOps goal 11 t105.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t105.toFinset.image (move perm2) = t59.toFinset := by
    simp only [t105,t59,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48,mv2w49] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt106 (h : ¬ live basicOps goal 11 t60.toFinset) : ¬ live basicOps goal 11 t106.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t106.toFinset.image (move perm2) = t60.toFinset := by
    simp only [t106,t60,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48,mv2w49] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt65 (h : ¬ live basicOps goal 11 t63.toFinset) : ¬ live basicOps goal 11 t65.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t65.toFinset.image (move perm1) = t63.toFinset := by
    simp only [t65,t63,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w47,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt107 (h : ¬ live basicOps goal 11 t64.toFinset) : ¬ live basicOps goal 11 t107.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t107.toFinset.image (move perm2) = t64.toFinset := by
    simp only [t107,t64,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w37,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt108 (h : ¬ live basicOps goal 11 t68.toFinset) : ¬ live basicOps goal 11 t108.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t108.toFinset.image (move perm2) = t68.toFinset := by
    simp only [t108,t68,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w19,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt109 (h : ¬ live basicOps goal 11 t69.toFinset) : ¬ live basicOps goal 11 t109.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t109.toFinset.image (move perm2) = t69.toFinset := by
    simp only [t109,t69,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w21,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt110 (h : ¬ live basicOps goal 11 t70.toFinset) : ¬ live basicOps goal 11 t110.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t110.toFinset.image (move perm2) = t70.toFinset := by
    simp only [t110,t70,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w9,mv2w10,mv2w16,mv2w21,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt21 (h : ¬ live basicOps goal 11 t13.toFinset) : ¬ live basicOps goal 11 t21.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t21.toFinset.image (move perm2) = t13.toFinset := by
    simp only [t21,t13,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w28,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt111 (h : ¬ live basicOps goal 11 t91.toFinset) : ¬ live basicOps goal 11 t111.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t111.toFinset.image (move perm1) = t91.toFinset := by
    simp only [t111,t91,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w20,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt23 (h : ¬ live basicOps goal 11 t19.toFinset) : ¬ live basicOps goal 11 t23.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t23.toFinset.image (move perm2) = t19.toFinset := by
    simp only [t23,t19,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w29,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt112 (h : ¬ live basicOps goal 11 t92.toFinset) : ¬ live basicOps goal 11 t112.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t112.toFinset.image (move perm1) = t92.toFinset := by
    simp only [t112,t92,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w25,mv1w30,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt41 (h : ¬ live basicOps goal 11 t33.toFinset) : ¬ live basicOps goal 11 t41.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t41.toFinset.image (move perm1) = t33.toFinset := by
    simp only [t41,t33,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w13,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt113 (h : ¬ live basicOps goal 11 t93.toFinset) : ¬ live basicOps goal 11 t113.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t113.toFinset.image (move perm1) = t93.toFinset := by
    simp only [t113,t93,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w13,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt73 (h : ¬ live basicOps goal 11 t29.toFinset) : ¬ live basicOps goal 11 t73.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t73.toFinset.image (move perm1) = t29.toFinset := by
    simp only [t73,t29,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w44,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt114 (h : ¬ live basicOps goal 11 t94.toFinset) : ¬ live basicOps goal 11 t114.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t114.toFinset.image (move perm1) = t94.toFinset := by
    simp only [t114,t94,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w44,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt115 (h : ¬ live basicOps goal 11 t95.toFinset) : ¬ live basicOps goal 11 t115.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t115.toFinset.image (move perm1) = t95.toFinset := by
    simp only [t115,t95,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48,mv1w54] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt31 (h : ¬ live basicOps goal 11 t17.toFinset) : ¬ live basicOps goal 11 t31.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t31.toFinset.image (move perm2) = t17.toFinset := by
    simp only [t31,t17,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w42,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt61 (h : ¬ live basicOps goal 11 t25.toFinset) : ¬ live basicOps goal 11 t61.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t61.toFinset.image (move perm1) = t25.toFinset := by
    simp only [t61,t25,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w36,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt116 (h : ¬ live basicOps goal 11 t96.toFinset) : ¬ live basicOps goal 11 t116.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t116.toFinset.image (move perm1) = t96.toFinset := by
    simp only [t116,t96,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w36,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt117 (h : ¬ live basicOps goal 11 t97.toFinset) : ¬ live basicOps goal 11 t117.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t117.toFinset.image (move perm1) = t97.toFinset := by
    simp only [t117,t97,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w22,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt118 (h : ¬ live basicOps goal 11 t98.toFinset) : ¬ live basicOps goal 11 t118.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t118.toFinset.image (move perm1) = t98.toFinset := by
    simp only [t118,t98,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w14,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt119 (h : ¬ live basicOps goal 11 t99.toFinset) : ¬ live basicOps goal 11 t119.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t119.toFinset.image (move perm1) = t99.toFinset := by
    simp only [t119,t99,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w24,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt120 (h : ¬ live basicOps goal 11 t100.toFinset) : ¬ live basicOps goal 11 t120.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t120.toFinset.image (move perm1) = t100.toFinset := by
    simp only [t120,t100,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w1,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt121 (h : ¬ live basicOps goal 11 t101.toFinset) : ¬ live basicOps goal 11 t121.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t121.toFinset.image (move perm1) = t101.toFinset := by
    simp only [t121,t101,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w46,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt122 (h : ¬ live basicOps goal 11 t102.toFinset) : ¬ live basicOps goal 11 t122.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t122.toFinset.image (move perm1) = t102.toFinset := by
    simp only [t122,t102,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w34,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt123 (h : ¬ live basicOps goal 11 t103.toFinset) : ¬ live basicOps goal 11 t123.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t123.toFinset.image (move perm1) = t103.toFinset := by
    simp only [t123,t103,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w18,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt124 (h : ¬ live basicOps goal 11 t104.toFinset) : ¬ live basicOps goal 11 t124.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t124.toFinset.image (move perm1) = t104.toFinset := by
    simp only [t124,t104,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w8,mv1w9,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt125 (h : ¬ live basicOps goal 11 t105.toFinset) : ¬ live basicOps goal 11 t125.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t125.toFinset.image (move perm1) = t105.toFinset := by
    simp only [t125,t105,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w12,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt126 (h : ¬ live basicOps goal 11 t106.toFinset) : ¬ live basicOps goal 11 t126.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t126.toFinset.image (move perm1) = t106.toFinset := by
    simp only [t126,t106,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w12,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt79 (h : ¬ live basicOps goal 11 t65.toFinset) : ¬ live basicOps goal 11 t79.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t79.toFinset.image (move perm2) = t65.toFinset := by
    simp only [t79,t65,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w45,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt127 (h : ¬ live basicOps goal 11 t107.toFinset) : ¬ live basicOps goal 11 t127.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t127.toFinset.image (move perm1) = t107.toFinset := by
    simp only [t127,t107,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w47,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt128 (h : ¬ live basicOps goal 11 t108.toFinset) : ¬ live basicOps goal 11 t128.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t128.toFinset.image (move perm1) = t108.toFinset := by
    simp only [t128,t108,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w43,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt129 (h : ¬ live basicOps goal 11 t109.toFinset) : ¬ live basicOps goal 11 t129.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t129.toFinset.image (move perm1) = t109.toFinset := by
    simp only [t129,t109,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w40,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt130 (h : ¬ live basicOps goal 11 t110.toFinset) : ¬ live basicOps goal 11 t130.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t130.toFinset.image (move perm1) = t110.toFinset := by
    simp only [t130,t110,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w9,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w40,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt75 (h : ¬ live basicOps goal 11 t21.toFinset) : ¬ live basicOps goal 11 t75.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t75.toFinset.image (move perm1) = t21.toFinset := by
    simp only [t75,t21,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48,mv1w54] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt22 (h : ¬ live basicOps goal 11 t111.toFinset) : ¬ live basicOps goal 11 t22.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t22.toFinset.image (move perm2) = t111.toFinset := by
    simp only [t22,t111,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w28,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt51 (h : ¬ live basicOps goal 11 t23.toFinset) : ¬ live basicOps goal 11 t51.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t51.toFinset.image (move perm1) = t23.toFinset := by
    simp only [t51,t23,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w14,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt7 (h : ¬ live basicOps goal 11 t112.toFinset) : ¬ live basicOps goal 11 t7.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t7.toFinset.image (move perm2) = t112.toFinset := by
    simp only [t7,t112,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w24,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt42 (h : ¬ live basicOps goal 11 t113.toFinset) : ¬ live basicOps goal 11 t42.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t42.toFinset.image (move perm2) = t113.toFinset := by
    simp only [t42,t113,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w13,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt45 (h : ¬ live basicOps goal 11 t73.toFinset) : ¬ live basicOps goal 11 t45.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t45.toFinset.image (move perm2) = t73.toFinset := by
    simp only [t45,t73,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w46,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt46 (h : ¬ live basicOps goal 11 t114.toFinset) : ¬ live basicOps goal 11 t46.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t46.toFinset.image (move perm2) = t114.toFinset := by
    simp only [t46,t114,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w46,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt38 (h : ¬ live basicOps goal 11 t115.toFinset) : ¬ live basicOps goal 11 t38.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t38.toFinset.image (move perm2) = t115.toFinset := by
    simp only [t38,t115,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w8,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt71 (h : ¬ live basicOps goal 11 t31.toFinset) : ¬ live basicOps goal 11 t71.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t71.toFinset.image (move perm1) = t31.toFinset := by
    simp only [t71,t31,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w16,mv1w22,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt43 (h : ¬ live basicOps goal 11 t61.toFinset) : ¬ live basicOps goal 11 t43.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t43.toFinset.image (move perm2) = t61.toFinset := by
    simp only [t43,t61,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w18,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt44 (h : ¬ live basicOps goal 11 t116.toFinset) : ¬ live basicOps goal 11 t44.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t44.toFinset.image (move perm2) = t116.toFinset := by
    simp only [t44,t116,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w18,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt40 (h : ¬ live basicOps goal 11 t117.toFinset) : ¬ live basicOps goal 11 t40.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t40.toFinset.image (move perm2) = t117.toFinset := by
    simp only [t40,t117,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w34,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt48 (h : ¬ live basicOps goal 11 t118.toFinset) : ¬ live basicOps goal 11 t48.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t48.toFinset.image (move perm2) = t118.toFinset := by
    simp only [t48,t118,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48,mv2w52] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt28 (h : ¬ live basicOps goal 11 t119.toFinset) : ¬ live basicOps goal 11 t28.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t28.toFinset.image (move perm2) = t119.toFinset := by
    simp only [t28,t119,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w30,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt32 (h : ¬ live basicOps goal 11 t120.toFinset) : ¬ live basicOps goal 11 t32.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t32.toFinset.image (move perm2) = t120.toFinset := by
    simp only [t32,t120,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w42,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt74 (h : ¬ live basicOps goal 11 t121.toFinset) : ¬ live basicOps goal 11 t74.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t74.toFinset.image (move perm2) = t121.toFinset := by
    simp only [t74,t121,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w44,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt72 (h : ¬ live basicOps goal 11 t122.toFinset) : ¬ live basicOps goal 11 t72.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t72.toFinset.image (move perm2) = t122.toFinset := by
    simp only [t72,t122,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w22,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt62 (h : ¬ live basicOps goal 11 t123.toFinset) : ¬ live basicOps goal 11 t62.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t62.toFinset.image (move perm2) = t123.toFinset := by
    simp only [t62,t123,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w36,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt76 (h : ¬ live basicOps goal 11 t124.toFinset) : ¬ live basicOps goal 11 t76.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t76.toFinset.image (move perm2) = t124.toFinset := by
    simp only [t76,t124,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48,mv2w54] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt77 (h : ¬ live basicOps goal 11 t125.toFinset) : ¬ live basicOps goal 11 t77.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t77.toFinset.image (move perm2) = t125.toFinset := by
    simp only [t77,t125,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w11,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt78 (h : ¬ live basicOps goal 11 t126.toFinset) : ¬ live basicOps goal 11 t78.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t78.toFinset.image (move perm2) = t126.toFinset := by
    simp only [t78,t126,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w11,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt80 (h : ¬ live basicOps goal 11 t127.toFinset) : ¬ live basicOps goal 11 t80.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t80.toFinset.image (move perm2) = t127.toFinset := by
    simp only [t80,t127,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w45,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt86 (h : ¬ live basicOps goal 11 t128.toFinset) : ¬ live basicOps goal 11 t86.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t86.toFinset.image (move perm2) = t128.toFinset := by
    simp only [t86,t128,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48,mv2w57] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt87 (h : ¬ live basicOps goal 11 t129.toFinset) : ¬ live basicOps goal 11 t87.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t87.toFinset.image (move perm2) = t129.toFinset := by
    simp only [t87,t129,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w41,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt88 (h : ¬ live basicOps goal 11 t130.toFinset) : ¬ live basicOps goal 11 t88.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t88.toFinset.image (move perm2) = t130.toFinset := by
    simp only [t88,t130,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w2,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w41,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt37 (h : ¬ live basicOps goal 11 t75.toFinset) : ¬ live basicOps goal 11 t37.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t37.toFinset.image (move perm2) = t75.toFinset := by
    simp only [t37,t75,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w8,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt47 (h : ¬ live basicOps goal 11 t51.toFinset) : ¬ live basicOps goal 11 t47.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t47.toFinset.image (move perm2) = t51.toFinset := by
    simp only [t47,t51,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48,mv2w52] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt81 (h : ¬ live basicOps goal 11 t45.toFinset) : ¬ live basicOps goal 11 t81.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t81.toFinset.image (move perm1) = t45.toFinset := by
    simp only [t81,t45,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48,mv1w56] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt39 (h : ¬ live basicOps goal 11 t71.toFinset) : ¬ live basicOps goal 11 t39.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t39.toFinset.image (move perm2) = t71.toFinset := by
    simp only [t39,t71,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w34,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt85 (h : ¬ live basicOps goal 11 t43.toFinset) : ¬ live basicOps goal 11 t85.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t85.toFinset.image (move perm1) = t43.toFinset := by
    simp only [t85,t43,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48,mv1w57] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt57 (h : ¬ live basicOps goal 11 t37.toFinset) : ¬ live basicOps goal 11 t57.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t57.toFinset.image (move perm1) = t37.toFinset := by
    simp only [t57,t37,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48,mv1w53] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt49 (h : ¬ live basicOps goal 11 t81.toFinset) : ¬ live basicOps goal 11 t49.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t49.toFinset.image (move perm2) = t81.toFinset := by
    simp only [t49,t81,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w35,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt67 (h : ¬ live basicOps goal 11 t39.toFinset) : ¬ live basicOps goal 11 t67.toFinset := by
  intro run
  have run' := move_live perm1 onto1 fixes1 _ _ run
  have eq : t67.toFinset.image (move perm1) = t39.toFinset := by
    simp only [t67,t39,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv1w5,mv1w6,mv1w10,mv1w16,mv1w25,mv1w26,mv1w32,mv1w39,mv1w48,mv1w55] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt55 (h : ¬ live basicOps goal 11 t85.toFinset) : ¬ live basicOps goal 11 t55.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t55.toFinset.image (move perm2) = t85.toFinset := by
    simp only [t55,t85,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w25,mv2w26,mv2w32,mv2w39,mv2w43,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem carryt53 (h : ¬ live basicOps goal 11 t67.toFinset) : ¬ live basicOps goal 11 t53.toFinset := by
  intro run
  have run' := move_live perm2 onto2 fixes2 _ _ run
  have eq : t53.toFinset.image (move perm2) = t67.toFinset := by
    simp only [t53,t67,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,mv2w5,mv2w6,mv2w10,mv2w16,mv2w19,mv2w25,mv2w26,mv2w32,mv2w39,mv2w48] <;> decide +kernel
  exact h (eq ▸ run')
private theorem consDead {x : List W} {xs : List (List W)} (one : ¬live basicOps goal 11 x.toFinset)
    (rest : ∀ w ∈ xs, ¬live basicOps goal 11 w.toFinset) : ∀ w ∈ x::xs, ¬live basicOps goal 11 w.toFinset := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hx
  · exact one
  · exact rest w hx
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem of_representatives (h : ∀ ws ∈ rootReps, ¬live basicOps goal 11 ws.toFinset) : Exclusion := by
  have nt0 := h t0 (by decide +kernel)
  have nt1 := h t1 (by decide +kernel)
  have nt2 := h t2 (by decide +kernel)
  have nt3 := h t3 (by decide +kernel)
  have nt4 := h t4 (by decide +kernel)
  have nt5 := h t5 (by decide +kernel)
  have nt6 := h t6 (by decide +kernel)
  have nt8 := h t8 (by decide +kernel)
  have nt9 := h t9 (by decide +kernel)
  have nt10 := h t10 (by decide +kernel)
  have nt11 := h t11 (by decide +kernel)
  have nt12 := h t12 (by decide +kernel)
  have nt14 := h t14 (by decide +kernel)
  have nt15 := h t15 (by decide +kernel)
  have nt16 := h t16 (by decide +kernel)
  have nt18 := h t18 (by decide +kernel)
  have nt20 := h t20 (by decide +kernel)
  have nt24 := h t24 (by decide +kernel)
  have nt26 := h t26 (by decide +kernel)
  have nt30 := h t30 (by decide +kernel)
  have nt34 := h t34 (by decide +kernel)
  have nt35 := h t35 (by decide +kernel)
  have nt36 := h t36 (by decide +kernel)
  have nt50 := h t50 (by decide +kernel)
  have nt52 := h t52 (by decide +kernel)
  have nt54 := h t54 (by decide +kernel)
  have nt56 := h t56 (by decide +kernel)
  have nt58 := h t58 (by decide +kernel)
  have nt59 := h t59 (by decide +kernel)
  have nt60 := h t60 (by decide +kernel)
  have nt63 := h t63 (by decide +kernel)
  have nt64 := h t64 (by decide +kernel)
  have nt66 := h t66 (by decide +kernel)
  have nt68 := h t68 (by decide +kernel)
  have nt69 := h t69 (by decide +kernel)
  have nt70 := h t70 (by decide +kernel)
  have nt82 := h t82 (by decide +kernel)
  have nt83 := h t83 (by decide +kernel)
  have nt84 := h t84 (by decide +kernel)
  have nt89 := h t89 (by decide +kernel)
  have nt90 := h t90 (by decide +kernel)
  have nt13 := carryt13 nt2
  have nt91 := carryt91 nt3
  have nt19 := carryt19 nt5
  have nt27 := carryt27 nt5
  have nt92 := carryt92 nt6
  have nt33 := carryt33 nt9
  have nt93 := carryt93 nt10
  have nt29 := carryt29 nt11
  have nt94 := carryt94 nt12
  have nt95 := carryt95 nt14
  have nt17 := carryt17 nt15
  have nt25 := carryt25 nt15
  have nt96 := carryt96 nt16
  have nt97 := carryt97 nt18
  have nt98 := carryt98 nt20
  have nt99 := carryt99 nt24
  have nt100 := carryt100 nt26
  have nt101 := carryt101 nt50
  have nt102 := carryt102 nt54
  have nt103 := carryt103 nt56
  have nt104 := carryt104 nt58
  have nt105 := carryt105 nt59
  have nt106 := carryt106 nt60
  have nt65 := carryt65 nt63
  have nt107 := carryt107 nt64
  have nt108 := carryt108 nt68
  have nt109 := carryt109 nt69
  have nt110 := carryt110 nt70
  have nt21 := carryt21 nt13
  have nt111 := carryt111 nt91
  have nt23 := carryt23 nt19
  have nt112 := carryt112 nt92
  have nt41 := carryt41 nt33
  have nt113 := carryt113 nt93
  have nt73 := carryt73 nt29
  have nt114 := carryt114 nt94
  have nt115 := carryt115 nt95
  have nt31 := carryt31 nt17
  have nt61 := carryt61 nt25
  have nt116 := carryt116 nt96
  have nt117 := carryt117 nt97
  have nt118 := carryt118 nt98
  have nt119 := carryt119 nt99
  have nt120 := carryt120 nt100
  have nt121 := carryt121 nt101
  have nt122 := carryt122 nt102
  have nt123 := carryt123 nt103
  have nt124 := carryt124 nt104
  have nt125 := carryt125 nt105
  have nt126 := carryt126 nt106
  have nt79 := carryt79 nt65
  have nt127 := carryt127 nt107
  have nt128 := carryt128 nt108
  have nt129 := carryt129 nt109
  have nt130 := carryt130 nt110
  have nt75 := carryt75 nt21
  have nt22 := carryt22 nt111
  have nt51 := carryt51 nt23
  have nt7 := carryt7 nt112
  have nt42 := carryt42 nt113
  have nt45 := carryt45 nt73
  have nt46 := carryt46 nt114
  have nt38 := carryt38 nt115
  have nt71 := carryt71 nt31
  have nt43 := carryt43 nt61
  have nt44 := carryt44 nt116
  have nt40 := carryt40 nt117
  have nt48 := carryt48 nt118
  have nt28 := carryt28 nt119
  have nt32 := carryt32 nt120
  have nt74 := carryt74 nt121
  have nt72 := carryt72 nt122
  have nt62 := carryt62 nt123
  have nt76 := carryt76 nt124
  have nt77 := carryt77 nt125
  have nt78 := carryt78 nt126
  have nt80 := carryt80 nt127
  have nt86 := carryt86 nt128
  have nt87 := carryt87 nt129
  have nt88 := carryt88 nt130
  have nt37 := carryt37 nt75
  have nt47 := carryt47 nt51
  have nt81 := carryt81 nt45
  have nt39 := carryt39 nt71
  have nt85 := carryt85 nt43
  have nt57 := carryt57 nt37
  have nt49 := carryt49 nt81
  have nt67 := carryt67 nt39
  have nt55 := carryt55 nt85
  have nt53 := carryt53 nt67
  apply of_roots
  exact consDead nt0 (consDead nt1 (consDead nt2 (consDead nt3 (consDead nt4 (consDead nt5 (consDead nt6 (consDead nt7 (consDead nt8 (consDead nt9 (consDead nt10 (consDead nt11 (consDead nt12 (consDead nt13 (consDead nt14 (consDead nt15 (consDead nt16 (consDead nt17 (consDead nt18 (consDead nt19 (consDead nt20 (consDead nt21 (consDead nt22 (consDead nt23 (consDead nt24 (consDead nt25 (consDead nt26 (consDead nt27 (consDead nt28 (consDead nt29 (consDead nt30 (consDead nt31 (consDead nt32 (consDead nt33 (consDead nt34 (consDead nt35 (consDead nt36 (consDead nt37 (consDead nt38 (consDead nt39 (consDead nt40 (consDead nt41 (consDead nt42 (consDead nt43 (consDead nt44 (consDead nt45 (consDead nt46 (consDead nt47 (consDead nt48 (consDead nt49 (consDead nt50 (consDead nt51 (consDead nt52 (consDead nt53 (consDead nt54 (consDead nt55 (consDead nt56 (consDead nt57 (consDead nt58 (consDead nt59 (consDead nt60 (consDead nt61 (consDead nt62 (consDead nt63 (consDead nt64 (consDead nt65 (consDead nt66 (consDead nt67 (consDead nt68 (consDead nt69 (consDead nt70 (consDead nt71 (consDead nt72 (consDead nt73 (consDead nt74 (consDead nt75 (consDead nt76 (consDead nt77 (consDead nt78 (consDead nt79 (consDead nt80 (consDead nt81 (consDead nt82 (consDead nt83 (consDead nt84 (consDead nt85 (consDead nt86 (consDead nt87 (consDead nt88 (consDead nt89 (consDead nt90 ((by simp))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
end Signed3110

namespace Signed3110

open Signed2964 PEqualNP.CircuitLowerBounds

def bitAt (k : Fin (2*m)) (w : W) := w.getLsbD k.val

theorem bit_getD (k : Fin (2*m)) (ws : List W) (j : Nat) :
    bitAt k (ws.getD j 0) = (ws.map (bitAt k)).getD j false := by
  induction ws generalizing j with
  | nil => simp [bitAt]
  | cons w ws ih => cases j <;> simp_all

def binary (andGate : Bool) : List W → W
  | [] => if andGate then ~~~(0:W) else 0
  | [a] => a
  | a::b::_ => if andGate then a &&& b else a ||| b

def wordGate (op : GateOp) (args : List W) : W :=
  match op with
  | .and => binary true args
  | .or => binary false args
  | .not => ~~~(args.headD 0)
  | _ => 0

def stepW (ws : List W) (g : Gate) := ws ++ [wordGate g.op (g.inputs.map fun j => ws.getD j 0)]
def runW (gs : List Gate) (ws : List W) := gs.foldl stepW ws

def stepB (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun j => ws.getD j false)]

private theorem read_bin (k : Fin (2*m)) (op : GateOp) (args : List W)
    (ok : op = .and ∨ op = .or ∨ op = .not) (len : args.length ≤ 2) :
    bitAt k (wordGate op args) = op.eval (args.map (bitAt k)) := by
  rcases args with _ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩ <;>
    rcases ok with rfl | rfl | rfl <;> simp_all [bitAt, wordGate, binary, GateOp.eval,k.isLt]

theorem run_rows (k : Fin (2*m)) (gs : List Gate) (ws : List W)
    (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (runW gs ws).map (bitAt k) = gs.foldl stepB (ws.map (bitAt k)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change (runW gs (stepW ws g)).map (bitAt k) = gs.foldl stepB (stepB (ws.map (bitAt k)) g)
    rw [ih _ (fun q hq => ok q (List.mem_cons_of_mem _ hq))]
    apply congrArg (gs.foldl stepB)
    have hg := ok g (by simp)
    simp only [stepW,stepB,List.map_append,List.map_cons,List.map_nil]
    rw [read_bin _ _ _ hg.1 (by simpa using hg.2)]
    simp only [List.map_map,Function.comp_def,bit_getD]

theorem raw_rows (k : Fin (2*m)) : rawInputs.map (bitAt k) = List.ofFn (assignment k) := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn]; rfl
  · intro j hj _
    have hj' : j < rawInputs.length := by simpa using hj
    simp only [List.getElem_map,List.getElem_ofFn,assignment,bitAt,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj',Option.getD_some]

def leading (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 2]
def postedInputs (js : List Nat) (x : Fin 9 → Bool) :=
  leading x ++ [GateOp.or.eval (js.map fun i => (leading x).getD i false)]

theorem base_rows (k : Fin (2*m)) : baseRaw.map (bitAt k) = leading (assignment k) := by
  simp only [baseRaw,leading,List.map_append,List.map_cons,List.map_nil,raw_rows]
  simp only [bitAt,BitVec.getLsbD_and,assignment]
  rfl

private theorem read_or (k : Fin (2*m)) (xs : List W) :
    bitAt k (xs.foldr (· ||| ·) 0) = GateOp.or.eval (xs.map (bitAt k)) := by
  induction xs with
  | nil => simp [bitAt,GateOp.eval]
  | cons x xs ih =>
    simp only [List.foldr_cons,bitAt,BitVec.getLsbD_or,GateOp.eval,List.map_cons,List.any_cons,id_eq] at ih ⊢
    exact congrArg (fun t => x.getLsbD k.val || t) ih

theorem full_rows (js : List Nat) (k : Fin (2*m)) : (augmented js).map (bitAt k) = postedInputs js (assignment k) := by
  simp only [augmented,postedInputs,List.map_append,List.map_cons,List.map_nil,base_rows]
  rw [orWire,read_or]
  simp only [List.map_map,Function.comp_def,bit_getD,base_rows]

end Signed3110

namespace Signed3110
open Signed2964 PEqualNP.CircuitLowerBounds

private def phaseW {d : Nat} (a : BitVec d) (s : Bool) := if s then ~~~a else a

private theorem bit_phase {d : Nat} (a : BitVec d) (s : Bool) (j : Fin d) :
    (phaseW a s).getLsbD j.val = (a.getLsbD j.val ^^ s) := by
  cases s <;> simp [phaseW,j.isLt]

private def canonicalW {d : Nat} (a : BitVec d) := phaseW a (a.getLsbD 0)

private theorem canonical_not {d : Nat} (hd : 0 < d) (a : BitVec d) :
    canonicalW (~~~a) = canonicalW a := by
  unfold canonicalW phaseW
  rw [BitVec.getLsbD_not]
  simp only [hd,decide_true,Bool.true_and]
  cases a.getLsbD 0 <;> simp

private theorem canonical_phase {d : Nat} (hd : 0 < d) (a : BitVec d) (s : Bool) :
    canonicalW (phaseW a s) = canonicalW a := by
  cases s
  · rfl
  · exact canonical_not hd _

private theorem canonical_zero {d : Nat} : canonicalW (0 : BitVec d) = 0 := by
  simp [canonicalW,phaseW]

private theorem canonical_canonical {d : Nat} (hd : 0 < d) (a : BitVec d) :
    canonicalW (canonicalW a) = canonicalW a := canonical_phase hd _ _

private theorem signed_from {d : Nat} (a : BitVec d) (s : Bool) :
    ∃ u, phaseW a s = phaseW (canonicalW a) u := by
  refine ⟨a.getLsbD 0 ^^ s,?_⟩
  cases h : a.getLsbD 0 <;> cases s <;> simp [canonicalW,phaseW,h,BitVec.not_not]

private theorem normalize_gate {d : Nat} (hd : 0 < d) (a b : BitVec d) (op s t : Bool) :
    ∃ u v, canonicalW (if op then phaseW a s &&& phaseW b t else phaseW a s ||| phaseW b t) =
      canonicalW (phaseW (canonicalW a) u &&& phaseW (canonicalW b) v) := by
  cases op
  · obtain ⟨u,hu⟩ := signed_from a (!s)
    obtain ⟨v,hv⟩ := signed_from b (!t)
    refine ⟨u,v,?_⟩
    rw [←hu,←hv]
    change canonicalW (phaseW a s ||| phaseW b t) = _
    rw [← canonical_not hd (phaseW a s ||| phaseW b t),BitVec.not_or]
    cases s <;> cases t <;> simp [phaseW,BitVec.not_not]
  · obtain ⟨u,hu⟩ := signed_from a s
    obtain ⟨v,hv⟩ := signed_from b t
    exact ⟨u,v,by simp [hu,hv]⟩

private theorem collapsed {d : Nat} (hd : 0 < d) (x y : BitVec d) (u v : Bool)
    (h : x = 0 ∨ y = 0 ∨ x = y) :
    canonicalW (phaseW x u &&& phaseW y v) = 0 ∨
    canonicalW (phaseW x u &&& phaseW y v) = canonicalW x ∨
    canonicalW (phaseW x u &&& phaseW y v) = canonicalW y := by
  rcases h with rfl | rfl | rfl <;> cases u <;> cases v <;>
    simp [phaseW,canonical_not hd] <;> exact Or.inl canonical_zero

private def held (s : Finset W) (x : W) := canonicalW x = 0 ∨ canonicalW x ∈ s

private theorem held_up {s t : Finset W} (sub : s ⊆ t) {x : W} (h : held s x) : held t x :=
  h.imp_right (fun hx => sub hx)

private theorem held_zero (s : Finset W) : held s 0 := Or.inl canonical_zero

private theorem held_not (s : Finset W) (x : W) (h : held s x) : held s (~~~x) := by
  simpa only [held,canonical_not (by decide : 0 < 2*m)] using h

private theorem lookup_held {s : Finset W} {ws : List W} (av : ∀ x ∈ ws, held s x) (j : Nat) :
    held s (ws.getD j 0) := by
  by_cases hi : j<ws.length
  · simpa [List.getD_eq_getElem?_getD,hi] using av _ (List.getElem_mem (l:=ws) hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact held_zero _

private theorem binary_step {s : Finset W} (k : Nat) (andGate : Bool) (a b : W)
    (ha : held s a) (hb : held s b)
    (tail : ∀ t, s ⊆ t → held t (binary andGate [a,b]) → build basicOps goal k t) :
    build basicOps goal (k+1) s := by
  have hd : 0 < 2*m := by decide
  let x := canonicalW a
  let y := canonicalW b
  obtain ⟨u,v,eq⟩ := normalize_gate hd a b andGate false false
  change canonicalW (binary andGate [a,b]) = canonicalW (phaseW x u &&& phaseW y v) at eq
  by_cases bad : x=0 ∨ y=0 ∨ x=y
  · apply Or.inl
    apply tail _ (Finset.Subset.refl _)
    unfold held
    rw [eq]
    rcases collapsed hd x y u v bad with hz | hx | hy
    · exact Or.inl hz
    · rw [hx,canonical_canonical hd]; exact ha
    · rw [hy,canonical_canonical hd]; exact hb
  · push Not at bad
    let z := canonicalW (phaseW x u &&& phaseW y v)
    refine Or.inr ⟨x,ha.resolve_left bad.1,y,hb.resolve_left bad.2.1,bad.2.2,z,?_,
      tail (insert z s) (Finset.subset_insert _ _) (Or.inr (eq ▸ Finset.mem_insert_self _ _))⟩
    cases u <;> cases v <;> simp [z,basicOps,ops,Signed2964.norm,canonicalW,phaseW]

def isNot (g : Gate) : Bool := match g.op with | .not => true | _ => false

def cost : List Gate → Nat
  | [] => 0
  | g :: gs => if isNot g then cost gs else cost gs + 1

theorem accounting (gs : List Gate) : cost gs + gs.countP isNot = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h : isNot g <;> simp [cost,h] <;> omega

private theorem walk (gs : List Gate) (ws : List W) (o : Nat) (s : Finset W)
    (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (av : ∀ x ∈ ws, held s x) (hit : canonicalW ((runW gs ws).getD o 0) = goal) :
    build basicOps goal (cost gs) s := by
  induction gs generalizing ws s with
  | nil =>
    change canonicalW (ws.getD o 0) = goal at hit
    obtain zero | mem := lookup_held av o
    · exact False.elim ((by decide +kernel : goal ≠ 0) (hit.symm.trans zero))
    · exact hit ▸ mem
  | cons g gs ih =>
    let args := g.inputs.map fun j => ws.getD j 0
    have ready : ∀ x ∈ args, held s x := by
      intro x hx
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
      exact lookup_held av j
    have next (t : Finset W) (sub : s ⊆ t) (h : held t (wordGate g.op args)) :
        build basicOps goal (cost gs) t := by
      apply ih (stepW ws g) t (fun q hq => ok q (List.mem_cons_of_mem _ hq)) _ hit
      intro x hx
      rcases List.mem_append.mp hx with old | now
      · exact held_up sub (av x old)
      · exact (List.mem_singleton.mp now) ▸ h
    have bg (andGate : Bool) (same : wordGate g.op args = binary andGate args) :
        build basicOps goal (cost gs + 1) s := by
      cases hargs : args with
      | nil =>
        apply Or.inl (next _ (Finset.Subset.refl _) _)
        rw [same,hargs]
        cases andGate
        · exact held_zero _
        · exact held_not _ _ (held_zero _)
      | cons a xs =>
        have ha := ready a (by simp [hargs])
        cases xs with
        | nil =>
          exact Or.inl (next _ (Finset.Subset.refl _) (by rw [same,hargs]; exact ha))
        | cons b bs =>
          have hb := ready b (by simp [hargs])
          apply binary_step (cost gs) andGate a b ha hb
          intro t sub out
          exact next t sub (by rw [same,hargs]; exact out)
    rcases ok g (by simp) with hg | hg | hg
    · simpa only [cost,isNot,hg,Bool.false_eq_true,ite_false] using bg true (by rw [hg];rfl)
    · simpa only [cost,isNot,hg,Bool.false_eq_true,ite_false] using bg false (by rw [hg];rfl)
    · have free : held s (wordGate g.op args) := by
        rw [hg]
        apply held_not
        cases h : args with
        | nil => exact held_zero _
        | cons x xs => exact ready x (by simp [h])
      simpa only [cost,isNot,hg,ite_true] using next _ (Finset.Subset.refl _) free

theorem circuit_build (js : List Nat) (C : Circuit) (ok : PEqualNP.MetaComplexity.FanInTwo C)
    (size : C.size ≤ 13) (nots : C.gates.countP isNot = 2)
    (correct : ∀ x : Fin 9 → Bool, C.eval (postedInputs js x) = target x) :
    build basicOps goal 11 (initial js) := by
  have basis : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    simpa [PEqualNP.MetaComplexity.FanInTwo] using ok
  have hit : (runW C.gates (augmented js)).getD C.output 0 = goal := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro j hj
    let k : Fin (2*m) := ⟨j,hj⟩
    change bitAt k _ = _
    rw [bit_getD,run_rows k _ _ basis,full_rows]
    exact (correct (assignment k)).trans (target_bits k)
  have proof := walk C.gates (augmented js) C.output (initial js)
    (fun g hg => (basis g hg).1) (by
      intro x hx
      by_cases hz : canonicalW x = 0
      · exact Or.inl hz
      · exact Or.inr (Finset.mem_erase.mpr ⟨hz,List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,hx,rfl⟩)⟩)) (by
      rw [hit];decide +kernel)
  have count := accounting C.gates
  change C.gates.length ≤ 13 at size
  have bound : cost C.gates ≤ 11 := by omega
  have pad : ∀ r, build basicOps goal (cost C.gates+r) (initial js) := by
    intro r
    induction r with
    | zero => exact proof
    | succ r ih => exact Or.inl ih
  exact (show cost C.gates+(11-cost C.gates)=11 by omega) ▸ pad _

end Signed3110

namespace Signed3110

theorem of_exclusion (excluded : Exclusion) : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x7 : ℕ) => Bool.false) Bool.false x6.op) x3.gates = (2 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro js width C ok size count
  by_contra! correct
  have hcount : C.gates.countP isNot = 2 := by
    have eq : isNot = (fun g : PEqualNP.CircuitLowerBounds.Gate =>
      PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op) := by
      funext g
      unfold isNot
      cases g.op <;> rfl
    rw [eq]; exact count
  exact excluded js width (circuit_build js C ok size hcount (fun x => Classical.byContradiction (correct x)))

end Signed3110

namespace Signed2964.Projection

variable {A B : Type} [DecidableEq A] [DecidableEq B]

def zeros (f : A → B) (zero : B) (s : Finset A) := (s.filter (fun a => f a = zero)).card

private theorem zeros_add_le (f : A → B) (zero : B) (a : A) (t : Finset A) :
    zeros f zero (insert a t) ≤ zeros f zero t + if f a = zero then 1 else 0 := by
  classical
  unfold zeros
  rw [Finset.filter_insert]
  by_cases h : f a = zero
  · simpa [h] using Finset.card_insert_le a (t.filter fun a => f a = zero)
  · simp [h]

private theorem zeros_add_eq (f : A → B) (zero : B) (a : A) (t : Finset A) (fresh : a ∉ t) :
    zeros f zero (insert a t) = zeros f zero t + if f a = zero then 1 else 0 := by
  classical
  unfold zeros
  rw [Finset.filter_insert]
  by_cases h : f a = zero
  · simp [h, fresh]
  · simp [h]

-- Constants can be removed when restricting a live circuit to a set of rows.
-- A normalized gate with two identical operands can also reuse its operand.
theorem contract {ops : A → A → Finset A} {ops' : B → B → Finset B}
    (f : A → B) (zero : B) {g : A} (desired : f g ≠ zero)
    (gate : ∀ a b z, z ∈ ops a b → f z = zero ∨ f z = f a ∨ f z = f b ∨
      (f a ≠ zero ∧ f b ≠ zero ∧ f a ≠ f b ∧ f z ∈ ops' (f a) (f b)))
    (n : Nat) (s : Finset A) (T : Finset B)
    (available : ∀ x ∈ s, f x ≠ zero → f x ∈ T) (h : live ops g n s) :
    ∃ k, build ops' (f g) k T ∧ k + zeros f zero s ≤ n := by
  classical
  induction n generalizing s T with
  | zero =>
    change s = {g} at h
    subst s
    exact ⟨0, available g (by simp) desired, by simp [zeros, desired]⟩
  | succ n ih =>
    rcases h with idle | ⟨a,ha,b,hb,_,z,hz,fresh,r,eq,tail⟩
    · obtain ⟨k,hk,hc⟩ := ih _ _ available idle
      exact ⟨k,hk,by omega⟩
    have subset : r ⊆ s := by rw [eq]; intro i hi; simp [hi]
    have disk := zeros_add_eq f zero z r (fun hi => fresh (subset hi))
    have budget : zeros f zero s ≤ zeros f zero r + (if f a = zero then 1 else 0) +
          (if f b = zero then 1 else 0) := by
      rw [eq]
      have aBound := zeros_add_le f zero a (insert b r)
      have bBound := zeros_add_le f zero b r
      omega
    have step := gate a b z hz
    have both (ea : f a = zero) (eb : f b = zero) : f z = zero := by
      rcases step with h | h | h | h
      · exact h
      · exact h.trans ea
      · exact h.trans eb
      · exact False.elim (h.1 ea)
    have free (reuse : f z ≠ zero → f z ∈ T) :
        ∃ k, build ops' (f g) k T ∧ k + zeros f zero s ≤ n+1 := by
      have after (x) (hm : x ∈ insert z r) (nonzero : f x ≠ zero) : f x ∈ T := by
        rcases Finset.mem_insert.mp hm with rfl | hr
        · exact reuse nonzero
        · exact available _ (subset hr) nonzero
      obtain ⟨k,built,hc⟩ := ih _ _ after tail
      refine ⟨k,built,?_⟩
      by_cases ea : f a = zero <;> by_cases eb : f b = zero
      · simp [ea,eb,both ea eb] at budget disk; omega
      all_goals simp [ea,eb] at budget; split at disk <;> omega
    rcases step with eu | eu | eu | ⟨na,nb,ab,op⟩
    · exact free (fun h => False.elim (h eu))
    · exact free (fun h => eu ▸ available a ha (eu ▸ h))
    · exact free (fun h => eu ▸ available b hb (eu ▸ h))
    · have after (x) (hm : x ∈ insert z r) (nonzero : f x ≠ zero) : f x ∈ insert (f z) T := by
        rcases Finset.mem_insert.mp hm with rfl | hr
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (available _ (subset hr) nonzero)
      obtain ⟨k,built,hc⟩ := ih _ _ after tail
      refine ⟨k+1, Or.inr ⟨f a,available _ ha na,f b,available _ hb nb,ab,f z,op,built⟩,?_⟩
      simp [na,nb] at budget
      split at disk <;> omega

end Signed2964.Projection

namespace Signed2964.Projection

def project (mask w : W) : W :=
  let x := w &&& mask
  let y := (~~~w) &&& mask
  if x.toNat ≤ y.toNat then x else y
def phase (x : W) (b : Bool) : W := if b then ~~~x else x

def opsM (mask a b : W) : Finset W :=
  {project mask (a &&& b), project mask (a &&& ~~~b),
    project mask ((~~~a) &&& b), project mask ((~~~a) &&& ~~~b)}

end Signed2964.Projection

namespace Signed2964.Projection

private theorem flip_mask {m a b : W} (h : a &&& m = b &&& m) :
    (~~~a) &&& m = (~~~b) &&& m := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  have eq := congrArg (fun x : W => x.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and] at eq ⊢
  cases e : m.getLsbD i <;> simp [e] at eq ⊢
  exact eq

private theorem project_congr {m a b : W} (h : a &&& m = b &&& m) :
    project m a = project m b := by unfold project; rw [h,flip_mask h]

theorem project_not (m a : W) : project m (~~~a) = project m a := by
  simp only [project, BitVec.not_not]
  split <;> split
  · apply BitVec.eq_of_toNat_eq; omega
  · rfl
  · rfl
  · omega

private theorem mask_id (m a : W) : (a &&& m) &&& m = a &&& m := by
  simp [BitVec.and_assoc]

private theorem phase_project (m a : W) (p : Bool) :
    ∃ s, phase a p &&& m = phase (project m a) s &&& m := by
  by_cases h : (a &&& m).toNat ≤ ((~~~a) &&& m).toNat
  · have eq : project m a = a &&& m := if_pos h
    cases p
    · exact ⟨false, (mask_id m a).symm.trans (by rw [eq]; rfl)⟩
    · exact ⟨true, flip_mask ((mask_id m a).symm.trans (by rw [eq]))⟩
  · have eq : project m a = (~~~a) &&& m := if_neg h
    have base : (~~~a) &&& m = project m a &&& m := (mask_id m (~~~a)).symm.trans (by rw [eq])
    cases p
    · exact ⟨true, by simpa [phase] using flip_mask base⟩
    · exact ⟨false, base⟩

private theorem phase_project_id (m a : W) : project m (project m a) = project m a := by
  by_cases h : (a &&& m).toNat ≤ ((~~~a) &&& m).toNat
  · have eq : project m a = a &&& m := if_pos h
    exact project_congr (by rw [eq,mask_id])
  · have eq : project m a = (~~~a) &&& m := if_neg h
    calc project m (project m a) = project m (~~~a) := project_congr (by rw [eq,mask_id])
         _ = project m a := project_not ..

private theorem project_phase (m w : W) (p : Bool) : project m (phase w p) = project m w := by
  cases p <;> simp [phase, project_not]

private theorem project_zero (mask : W) : project mask 0 = 0 := by simp [project]

private theorem representation {a b z : W} (m : W) (hz : z ∈ basicOps a b) :
    ∃ p q, project m z = project m (phase (project m a) p &&& phase (project m b) q) := by
  have sub (z' : W) : project m (norm z') = project m z' := by
    unfold norm; split <;> simp [project_not]
  have pick (p q : Bool) : ∃ i j, project m (norm (phase a p &&& phase b q)) =
      project m (phase (project m a) i &&& phase (project m b) j) := by
    obtain ⟨i,hi⟩ := phase_project m a p
    obtain ⟨j,hj⟩ := phase_project m b q
    refine ⟨i,j,(sub _).trans (project_congr ?_)⟩
    have distribute (x y : W) : (x &&& y) &&& m = (x &&& m) &&& (y &&& m) := by
      simp only [← BitVec.and_assoc]; rw [BitVec.and_assoc x m y, BitVec.and_comm m y]
      simp [BitVec.and_assoc]
    rw [distribute, hi,hj,← distribute]
  simp only [basicOps, List.mem_toFinset, ops,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact pick false false
  · exact pick false true
  · exact pick true false
  · exact pick true true

set_option maxRecDepth 4000 in
theorem gate_projection (m : W) (a b z : W) (hz : z ∈ basicOps a b) :
    project m z = 0 ∨ project m z = project m a ∨ project m z = project m b ∨
    (project m a ≠ 0 ∧ project m b ≠ 0 ∧ project m a ≠ project m b ∧
      project m z ∈ opsM m (project m a) (project m b)) := by
  obtain ⟨p,q,eq⟩ := representation m hz
  by_cases a0 : project m a = 0
  · rw [a0] at eq
    cases p <;> cases q <;> simp [phase,project_not,phase_project_id] at eq <;>
      first | exact Or.inl eq | exact Or.inl (eq.trans (project_zero m)) | exact Or.inr (Or.inl eq) | exact Or.inr (Or.inr (Or.inl eq))
  by_cases b0 : project m b = 0
  · rw [b0] at eq
    cases p <;> cases q <;> simp [phase,project_not,phase_project_id] at eq <;>
      first | exact Or.inl eq | exact Or.inl (eq.trans (project_zero m)) | exact Or.inr (Or.inl eq) | exact Or.inr (Or.inr (Or.inl eq))
  by_cases same : project m a = project m b
  · rw [same] at eq
    cases p <;> cases q <;> simp [phase,project_not,phase_project_id] at eq <;>
      first | exact Or.inl eq | exact Or.inl (eq.trans (project_zero m)) | exact Or.inr (Or.inl eq) | exact Or.inr (Or.inr (Or.inl eq))
  refine Or.inr (Or.inr (Or.inr ⟨a0,b0,same,?_⟩))
  cases p <;> cases q <;> simp [opsM,phase] at eq ⊢ <;> aesop

end Signed2964.Projection

namespace Signed2964.Projection
abbrev ProbeData := BitVec m × List W × Nat
def allProbes : Array ProbeData := #[
  (0,[],0),
  (0xc646d9,[0x11818240000000000000000000000000000000000000000000000000000000000060601,0x11120000000000000000000000000000000000000000000000000000000000000646c1,0x10800240000000000000000000000000000000000000000000000000000000000c64019,0x96400000000000000000000000000000000000000000000000000000000000006d9],3),
  (0x668000a5b,[0x8a000282c0000000000000000000000000000000000000000000000000000000000000a03,0x8200020080000000000000000000000000000000000000000000000000000000608000a43,0xa000002c000000000000000000000000000000000000000000000000000000006800001b,0x9640000000000000000000000000000000000000000000000000000000000000a5b],3),
  (0x18c4508ca0000000000000000000000000000000000000000000000000,[0x211140128000000000000000000000000000000000000000000000000000000000005000a0000000000000000000000000000000000000000000000000,0x201100020000000000000000000000000000000000000000000000000000000018045080a0000000000000000000000000000000000000000000000000,0x11000128000000000000000000000000000000000000000000000000000000000c4000ca0000000000000000000000000000000000000000000000000,0x4230800000000000000000000000000000000000000000000000000000000000508ca0000000000000000000000000000000000000000000000000],3),
  (0x63200000125d,[0x8480000048340000000000000000000000000000000000000000000000000000000000001205,0x8080000040100000000000000000000000000000000000000000000000000000602000001245,0x48000000034000000000000000000000000000000000000000000000000000003200000001d,0x964000000000000000000000000000000000000000000000000000000000000125d],3),
  (0x668000000000000000000000000000002359,[0x9800000000000000000000000000000088240000000000000000000000000000060000000000000000000000000000002201,0x1200000000000000000000000000000084000000000000000000000000000000068000000000000000000000000000002341,0x8800000000000000000000000000000000240000000000000000000000000000668000000000000000000000000000000019,0x9640000000000000000000000000000000000000000000000000000000000002359],3),
  (0x18620002188c20000000000000000000000000000000000000000000000000,[0x218000084010800000000000000000000000000000000000000000000000000000600002100020000000000000000000000000000000000000000000000000,0x10800082000000000000000000000000000000000000000000000000000000000620002188020000000000000000000000000000000000000000000000000,0x208000000010800000000000000000000000000000000000000000000000000018620000000c20000000000000000000000000000000000000000000000000,0x4230800000000000000000000000000000000000000000000000000000000002188c20000000000000000000000000000000000000000000000000],3),
  (0xb94a800b,[0xa128002c00000000000000000000000000000000000000000000000000000000000a0003,0x6022000800000000000000000000000000000000000000000000000000000000180a8003,0xa000002c00000000000000000000000000000000000000000000000000000000b800000b,0x108002400000000000000000000000000000000000000000000000000000000014a800b],3),
  (0x5514a42a0000000000000000000000000000000000,[0x441280a8000000000000000000000000000000000000000000000000000000000000a00a0000000000000000000000000000000000,0x14021020000000000000000000000000000000000000000000000000000000000500a40a0000000000000000000000000000000000,0x440000a8000000000000000000000000000000000000000000000000000000005500002a0000000000000000000000000000000000,0x108088000000000000000000000000000000000000000000000000000000000014a42a0000000000000000000000000000000000],3),
  (0x600000d000000000012800002b,[0x800003000000000000a000002c00000000000000000000000000000000000000000000c0000000000000000003,0x8000020000000000002000000800000000000000000000000000000000000000600000d0000000000008000003,0x1400000000000000000a400000000000000000000000000000000000000000000d000000000000000002b,0xa000002c000000000000000000000000000000000000000000000000000000012800002b],3),
  (0x3000a31100012a0000000000000000000000000000000000,[0x400280440000a8000000000000000000000000000000000000000000000000000000a00000000a0000000000000000000000000000000000,0x40020004000020000000000000000000000000000000000000000000000000003000a20100000a0000000000000000000000000000000000,0x8800000488000000000000000000000000000000000000000000000000000000a20000012a0000000000000000000000000000000000,0x440000a8000000000000000000000000000000000000000000000000000000011100012a0000000000000000000000000000000000],3),
  (0xc00000015000000005200000002d,[0x100000005000000000480000000340000000000000000000000000000000000000000000140000000000000000005,0x10000000400000000008000000010000000000000000000000000000000000000c000000150000000002000000005,0x1400000000000000000a4000000000000000000000000000000000000000000015000000000000000002d,0x48000000034000000000000000000000000000000000000000000000000000005200000002d],3),
  (0x1800009100000000484000002520000,[0x20000240000000002100000014800000000000000000000000000000000000000000009000000000000000000120000,0x20000200000000000100000004000000000000000000000000000000000000001800009100000000004000000120000,0x44000000000000000090800000000000000000000000000000000000000000009100000000000000002520000,0x2100000014800000000000000000000000000000000000000000000000000000484000002520000],3),
  (0xb3000000000000000000000009600000000d,[0xc800000000000000000000000480000000340000000000000000000000000000120000000000000000000000000000000005,0x4400000000000000000000000180000000100000000000000000000000000000130000000000000000000000006000000005,0x8800000000000000000000000000000000240000000000000000000000000000b3000000000000000000000000000000000d,0x48000000034000000000000000000000000000000000000000000000000000009600000000d],3),
  (0x25280000000000000000000008a4000000520000,[0x14800000000000000000000002100000014800000000000000000000000000000120000000000000000000000000000000120000,0x4200000000000000000000000900000004000000000000000000000000000000128000000000000000000000024000000120000,0x10800000000000000000000000000000010800000000000000000000000000002528000000000000000000000000000000520000,0x21000000148000000000000000000000000000000000000000000000000000008a4000000520000],3),
  (0x252800000000000000000000000000000000000011a00000000d,[0x14800000000000000000000000000000000000000480000000340000000000000120000000000000000000000000000000000000000000000005,0x420000000000000000000000000000000000000028000000010000000000000012800000000000000000000000000000000000000a000000005,0x1080000000000000000000000000000000000000000000000024000000000000252800000000000000000000000000000000000000000000000d,0x48000000034000000000000000000000000000000000000000000000000000011a00000000d],3),
  (0x4630000000000000000000000000000270000000000000000029,[0x18800000000000000000000000000009000000000000000000240000000000000220000000000000000000000000000240000000000000000001,0x8400000000000000000000000000008800000000000000000000000000000000230000000000000000000000000000270000000000000000001,0x10800000000000000000000000000000000000000000000000240000000000004630000000000000000000000000000000000000000000000029,0x1400000000000000000a40000000000000000000000000000000000000000000270000000000000000029],3),
  (0x8c300000000000000232000001220000000000000000000000000000000000,[0x308000000000000008800000008800000000000000000000000000000000000004200000000000000220000000020000000000000000000000000000000000,0x104000000000000008400000000000000000000000000000000000000000000004300000000000000232000000020000000000000000000000000000000000,0x20800000000000000000000000880000000000000000000000000000000000008c300000000000000000000001220000000000000000000000000000000000,0x880000048800000000000000000000000000000000000000000000000000000232000001220000000000000000000000000000000000],3),
  (0xa180ccc82,[0x82030300800000000000000000000000000000000000000000000000000000000000c0c02,0x6022000800000000000000000000000000000000000000000000000000000000180cc002,0x8200020080000000000000000000000000000000000000000000000000000000a18000c82,0x11120000000000000000000000000000000000000000000000000000000000000ccc82],3),
  (0xaa6618880000000000000000000,[0x8980602000000000000000000000000000000000000000000000000000000000006018080000000000000000000,0x29100020000000000000000000000000000000000000000000000000000000000a6600080000000000000000000,0x8800402000000000000000000000000000000000000000000000000000000000aa0018880000000000000000000,0x88220000000000000000000000000000000000000000000000000000000000006618880000000000000000000],3),
  (0x158000000000000000000001206000003104,[0x600000000000000000000040100000004000000000000000000000000000000018000000000000000000001206000000100,0x12000000000000000000000480000000c4000000000000000000000000000000000000000000000000000001200000003100,0x1200000000000000000000000000000084000000000000000000000000000000158000000000000000000000000000003104,0x8080000040100000000000000000000000000000000000000000000000000001206000003104],3),
  (0x14c000000000000254000061100000000000000000000,[0x30000000000000840000004000000000000000000000000000000000000000000c000000000000254000001000000000000000000000,0x1100000000000009000001840000000000000000000000000000000000000000000000000000000240000061000000000000000000000,0x110000000000000000000104000000000000000000000000000000000000000014c000000000000000000061100000000000000000000,0x1100000804000000000000000000000000000000000000000000000000000000254000061100000000000000000000],3),
  (0x6014002018188006,[0x80100080206000180000000000000000000000000000000000000000000000000000000000180006,0x80000080200000180000000000000000000000000000000000000000000000006000002018000006,0x100080004000100000000000000000000000000000000000000000000000000014002000188006,0x602200080000000000000000000000000000000000000000000000000000000018188006],3),
  (0xa48040ac400180000000000000000000,[0x820100b0000600000000000000000000000000000000000000000000000000000000000c000180000000000000000000,0x8001008000060000000000000000000000000000000000000000000000000000a00040a0000180000000000000000000,0x2010020000400000000000000000000000000000000000000000000000000000480400c400180000000000000000000,0x29100020000000000000000000000000000000000000000000000000000000000ac400180000000000000000000],3),
  (0xc0000c4000000000000000000000000000000000000000018298002,[0x10000300000000000000000000000000000000000000000020a0000800000000000000c0000000000000000000000000000000000000000000280002,0x10000200000000000000000000000000000000000000000020000008000000000c0000c4000000000000000000000000000000000000000018000002,0x11000000000000000000000000000000000000000000084000000000000000000c4000000000000000000000000000000000000000000298002,0x602200080000000000000000000000000000000000000000000000000000000018298002],3),
  (0x501840000000000000000050294080000000000000000000000000000000000,[0x406000000000000000000040a002000000000000000000000000000000000000001800000000000000000000280080000000000000000000000000000000000,0x4040000000000000000000400002000000000000000000000000000000000000501840000000000000000050000080000000000000000000000000000000000,0x21000000000000000000008400000000000000000000000000000000000000001840000000000000000000294080000000000000000000000000000000000,0x1402102000000000000000000000000000000000000000000000000000000000050294080000000000000000000000000000000000],3),
  (0x14c00000000000000000000000000000000004400a000310004,[0x30000000000000000000000000000000000100020000040000000000000000000c00000000000000000000000000000000004400a000010000,0x110000000000000000000000000000000000110000000c400000000000000000000000000000000000000000000000000000044000000310000,0x110000000000000000000000000000000000000000000840000000000000000014c000000000000000000000000000000000000000000310004,0x10008000400010000000000000000000000000000000000000000000000000004400a000310004],3),
  (0x9000019000000000000000000a000006008000006,[0x400006000000000000000000080000080200000180000000000000000000000000000180000000000000000000000000000000006,0x4400000000000000000000000180000000100000000000000000000000000000190000000000000000000000006000000006,0x400002000000000000000000000000000200000080000000000000000000000090000190000000000000000000000000008000006,0x8000008020000018000000000000000000000000000000000000000000000000a000006008000006],3),
  (0x1100188000000000120014020000180000000000000000000,[0x4006000000000000800100800006000000000000000000000000000000000000000180000000000000000000000180000000000000000000,0x4200000000000000500000004000000000000000000000000000000000000000188000000000000014000000180000000000000000000,0x4002000000000000000000800002000000000000000000000000000000000001100188000000000000000020000180000000000000000000,0x800100800006000000000000000000000000000000000000000000000000000120014020000180000000000000000000],3),
  (0x1400018800000000000000000000000000000001200000a008000006,[0x100006000000000000000000000000000000000080000080200000180000000000000180000000000000000000000000000000000000000000000006,0x420000000000000000000000000000000000000028000000010000000000000018800000000000000000000000000000000000000a000000006,0x100002000000000000000000000000000000000000000000200000080000000014000188000000000000000000000000000000000000000008000006,0x8000008020000018000000000000000000000000000000000000000000000001200000a008000006],3),
  (0x4800c20000000000000000000000000000000008800002200200001800,[0x20030000000000000000000000000000000000020000008008000060000000000000c00000000000000000000000000000000000000000000000001800,0x20800000000000000000000000000000000000000088000000040000000000000c20000000000000000000000000000000000000002200000001800,0x20010000000000000000000000000000000000000000000008000020000000004800c20000000000000000000000000000000000000000000200001800,0x20000008008000060000000000000000000000000000000000000000000000008800002200200001800],3),
  (0x31800000000000000000002400000032000000000a000000004,[0x60000000000000000000080000000080000000020000000000000000000000001800000000000000000002400000002000000000a000000000,0x420000000000000000000090000000400000000028000000010000000000000000000000000000000000002400000000000000000a000000000,0x420000000000000000000000000000000000000028000000010000000000000031800000000000000000000000000000000000000a000000004,0x10000000400000000008000000010000000000000000000000000000000000002400000032000000000a000000004],3),
  (0x18600000000000000000000004400000a2000000002200000001000,[0x1800000000000000000000010000000080000000080000000000000000000000060000000000000000000000440000002000000002200000000000,0x20800000000000000000000011000000800000000088000000040000000000000000000000000000000000000440000000000000002200000000000,0x20800000000000000000000000000000000000000088000000040000000000001860000000000000000000000000000000000000002200000001000,0x10000008000000000080000000400000000000000000000000000000000000004400000a2000000002200000001000],3),
  (0xcd180c0d0,[0x130600014000000000000000000000000000000000000000000000000000000000c1800010,0x24402000000000000000000000000000000000000000000000000000000000000d180c010,0x11000001400000000000000000000000000000000000000000000000000000000cd00000d0,0x2010340000000000000000000000000000000000000000000000000000000000180c0d0],3),
  (0x30c4318c20000000000,[0x4300c0108000000000000000000000000000000000000000000000000000000000c0300020000000000,0x21084000000000000000000000000000000000000000000000000000000000000c4318020000000000,0x410000108000000000000000000000000000000000000000000000000000000030c4000c20000000000,0x4230800000000000000000000000000000000000000000000000000000000000318c20000000000],3),
  (0x300c100000000000028040f0,[0x40104000000000000a0001c00000000000000000000000000000000000000000000000000000000002800030,0x4000400000000000080000800000000000000000000000000000000000000000300010000000000002804030,0x10400000000000000001c00000000000000000000000000000000000000000000c100000000000000000f0,0x201034000000000000000000000000000000000000000000000000000000000028040f0],3),
  (0x3188000000000000508c60000000000,[0x42200000000000014011800000000000000000000000000000000000000000000000000000000000500060000000000,0x40200000000000010001000000000000000000000000000000000000000000003008000000000000508060000000000,0x2200000000000000011800000000000000000000000000000000000000000000188000000000000000c60000000000,0x4230800000000000000000000000000000000000000000000000000000000000508c60000000000],3),
  (0x198040000000000000000000000000000000000000000048140d0,[0x260000000000000000000000000000000000000000000120001400000000000001800000000000000000000000000000000000000000004800010,0x40100000000000000000000000000000000000000000100400000000000000001804000000000000000000000000000000000000000004814010,0x2200000000000000000000000000000000000000000000000014000000000000198040000000000000000000000000000000000000000000000d0,0x201034000000000000000000000000000000000000000000000000000000000048140d0],3),
  (0xc180000000000000000000014a4000000150,[0x600000000000000000000040100000004000000000000000000000000000000018000000000000000000001404000000140,0x10200000000000000000000050800000005400000000000000000000000000000000000000000000000000001400000000140,0x10200000000000000000000000000000005400000000000000000000000000000c18000000000000000000000000000000150,0x108000000014000000000000000000000000000000000000000000000000000014a4000000150],3),
  (0xaa0000000000000000000005248000001440000000,[0x28000000000000000000001002000000400000000000000000000000000000000a0000000000000000000005008000001400000000,0x8800000000000000000000141000000051000000000000000000000000000000000000000000000000000005000000001400000000,0x8800000000000000000000000000000051000000000000000000000000000000aa0000000000000000000000000000001440000000,0x41000000011000000000000000000000000000000000000000000000000000005248000001440000000],3),
  (0x6000001408000000000001410000000000000000170,[0x80000050000000000000010400000000000000001c00000000000000000000000000001400000000000000000000000000000000030,0x80000040000000000000000400000000000000000800000000000000000000006000001408000000000000010000000000000000030,0x10200000000000000000000000000000005400000000000000000000000000001408000000000000000000000000000000170,0x10400000000000000001c00000000000000000000000000000000000000000001410000000000000000170],3),
  (0x600001220000000000001440000000000000001540000000,[0x8000048000000000000011000000000000000015000000000000000000000000000001200000000000000000000000000000000140000000,0x8000040000000000000001000000000000000004000000000000000000000000600001220000000000000040000000000000000140000000,0x8800000000000000000000000000000051000000000000000000000000000001220000000000000000000000000000001540000000,0x11000000000000000015000000000000000000000000000000000000000000001440000000000000001540000000],3),
  (0x4c810000000000000000000000000002430000000000000000070,[0x320000000000000000000000000000010400000000000000001c00000000000004800000000000000000000000000000000000000000000000030,0x100400000000000000000000000000000c00000000000000000800000000000004810000000000000000000000000000030000000000000000030,0x22000000000000000000000000000000000000000000000000140000000000004c810000000000000000000000000000000000000000000000070,0x10400000000000000001c00000000000000000000000000000000000000000002430000000000000000070],3),
  (0x94a0000000000000000000000000002540000000000000000540000000,[0x52000000000000000000000000000011000000000000000015000000000000000480000000000000000000000000000000000000000000000140000000,0x108000000000000000000000000000050000000000000000040000000000000004a0000000000000000000000000000140000000000000000140000000,0x420000000000000000000000000000000000000000000000110000000000000094a0000000000000000000000000000000000000000000000540000000,0x11000000000000000015000000000000000000000000000000000000000000002540000000000000000540000000],3),
  (0x5014000000000000000000000000900030000000000006010020,[0x500000000000000000000000020000800000000000000400000000000000000014000000000000000000000000900030000000000000010000,0x40100000000000000000000000024000000000000000180400000000000000000000000000000000000000000000900000000000000006010000,0x40100000000000000000000000000000000000000000100400000000000000005014000000000000000000000000000000000000000006010020,0x4000400000000000080000800000000000000000000000000000000000000000900030000000000006010020],3),
  (0xa014000000000000441200c011000000000000000000000000000000000000,[0x5000000000000100400000400000000000000000000000000000000000000000140000000000004412000010000000000000000000000000000000000000,0x80100000000000011000030040000000000000000000000000000000000000000000000000000000440000c010000000000000000000000000000000000000,0x8010000000000000000002004000000000000000000000000000000000000000a014000000000000000000c011000000000000000000000000000000000000,0x1008010004000000000000000000000000000000000000000000000000000000441200c011000000000000000000000000000000000000],3),
  (0x6018000000000000000000028000000030000000148000000020,[0x600000000000000000000800000000800000000200000000000000000000000018000000000000000000028000000030000000008000000000,0x80200000000000000000000a00000000000000005200000000000000000000000000000000000000000000028000000000000000148000000000,0x80200000000000000000000000000000000000004200000000000000000000006018000000000000000000000000000000000000148000000020,0x200000000400000001000000000800000000000000000000000000000000000028000000030000000148000000020],3),
  (0x630000000000000000000000240000140000000510000000100000000,[0xc00000000000000000000008000004000000000400000000000000000000000030000000000000000000000240000140000000010000000000000000,0x8400000000000000000000009000000000000014400000000000000000000000000000000000000000000000240000000000000510000000000000000,0x8400000000000000000000000000000000000010400000000000000000000000630000000000000000000000000000000000000510000000100000000,0x1000001000000004000000004000000000000000000000000000000000000000240000140000000510000000100000000],3),
  (0x6000600800000000000000000000000181000c180,[0x800080200000000000000000000000060000106000000000000000000000000000000000000000000000000000000001800000180,0x800000200000000000000000000000040000004000000000000000000000000060000008000000000000000000000001810000180,0x8020000000000000000000000000000010600000000000000000000000000000600800000000000000000000000000000c180,0x2040030200000000000000000000000000000000000000000000000000000000181000c180],3),
  (0xc01804000000000000001880601800000000000000000000,[0x10020100000000000000060008060000000000000000000000000000000000000000000000000000000001800001800000000000000000000,0x10000100000000000000040000040000000000000000000000000000000000000c00004000000000000001880001800000000000000000000,0x20100000000000000000008060000000000000000000000000000000000000001804000000000000000000601800000000000000000000,0x22018020000000000000000000000000000000000000000000000000000000001880601800000000000000000000],3),
  (0xa018000000000000000000029804000004180,[0x80200000000000000000000260000000106000000000000000000000000000000000000000000000000000001800000000180,0x600000000000000000000040100000004000000000000000000000000000000018000000000000000000001804000000180,0x8020000000000000000000000000000010600000000000000000000000000000a018000000000000000000000000000004180,0x220000000102000000000000000000000000000000000000000000000000000029804000004180],3),
  (0x280c00000000000a310000201800000000000000000000,[0x2010000000000008c000008060000000000000000000000000000000000000000000000000000000300000001800000000000000000000,0x30000000000000840000004000000000000000000000000000000000000000000c000000000000310000001800000000000000000000,0x2010000000000000000000806000000000000000000000000000000000000000280c000000000000000000201800000000000000000000,0x8400000802000000000000000000000000000000000000000000000000000000a310000201800000000000000000000],3),
  (0x3000c00000000000000000000000000000000004a808000014080,[0x30000000000000000000000000000000000100020000040000000000000000000c000000000000000000000000000000000048008000014000,0x400100000000000000000000000000000000001220000000502000000000000000000000000000000000000000000000000000048000000014000,0x40010000000000000000000000000000000000000000000050200000000000003000c000000000000000000000000000000000000000000014080,0x22000000010200000000000000000000000000000000000000000000000000004a808000014080],3),
  (0x50014000000000000000000000000a02820000000000000014080,[0x500000000000000000000000020000800000000000000400000000000000000014000000000000000000000000a00020000000000000014000,0x400100000000000000000000000028020000000000000000502000000000000000000000000000000000000000000a00000000000000000014000,0x400100000000000000000000000000000000000000000000502000000000000050014000000000000000000000000000000000000000000014080,0x8020000000000000000102000000000000000000000000000000000000000000a02820000000000000014080],3),
  (0x1200240000000000000000000000012088200000000000000240400,[0x9000000000000000000000000400008000000000000008000000000000000000240000000000000000000000012000200000000000000240000,0x8001000000000000000000000000480200000000000000009010000000000000000000000000000000000000000012000000000000000000240000,0x8001000000000000000000000000000000000000000000009010000000000001200240000000000000000000000000000000000000000000240400,0x80200000000000000001010000000000000000000000000000000000000000012088200000000000000240400],3),
  (0x60000090004000000000012008000000000000000000000000000014180,[0x800002400000000000000080200000000000000000000000000000106000000000000090000000000000000000000000000000000000000000000000180,0x800002000000000000000000200000000000000000000000000000004000000060000090004000000000000008000000000000000000000000000000180,0x400100000000000000000000000000000000000000000000502000000000000090004000000000000000000000000000000000000000000014180,0x80200000000000000000000000000000106000000000000000000000000000012008000000000000000000000000000014180],3),
  (0xc00002200040000000000240040000000000000000000000000000242400,[0x10000088000000000000001001000000000000000000000000000001090000000000002200000000000000000000000000000000000000000000000002400,0x10000080000000000000000001000000000000000000000000000000080000000c00002200040000000000000040000000000000000000000000000002400,0x8001000000000000000000000000000000000000000000009010000000000002200040000000000000000000000000000000000000000000242400,0x1001000000000000000000000000000001090000000000000000000000000000240040000000000000000000000000000242400],3),
  (0xa00000a000800000000000001800000000000000000000300c000000100,[0x8000028000000000000000002000000000000000000000c00000000040000000000000a0000000000000000000000000000000000000003000000000100,0x8000020000000000000000002000000000000000000000000000000040000000a00000a0008000000000000018000000000000000000000000000000100,0x8002000000000000000000000000000000000000802000000000000000000000a000800000000000000000000000000000000000300c000000100,0x60000000000000000000004010000000400000000000000000000000000000001800000000000000000000300c000000100],3),
  (0xa000140100000000000000a000000000000000000000c018000001000000000,[0x800050000000000000000080000000000000000000030000000004000000000000001400000000000000000000000000000000000000c000000001000000000,0x8000400000000000000000800000000000000000000000000000040000000000a000140100000000000000a0000000000000000000000000000001000000000,0x10040000000000000000000000000000000000020040000000000000000000001401000000000000000000000000000000000000c018000001000000000,0x28000000000000000000001002000000400000000000000000000000000000000a000000000000000000000c018000001000000000],3),
  (0x1800000c000000000000000000000000000000014050008010018000,[0x200000100000000000000000000000000000000101400000400600000000000000000000000000000000000000000000000000000050000000018000,0x30000000000000000000000000000000000100020000040000000000000000000c000000000000000000000000000000000050008000018000,0x20000010000000000000000000000000000000000000000040060000000000001800000c000000000000000000000000000000000000000010018000,0x100400000400200000000000000000000000000000000000000000000000000014050008010018000],3),
  (0x300003000000000000000000000000000000000481200100085000000,[0x4000040000000000000000000000000000000002048000002140000000000000000000000000000000000000000000000000000001200000005000000,0xc0000000000000000000000000000000000040004000100000000000000000003000000000000000000000000000000000001200100005000000,0x4000040000000000000000000000000000000000000000002140000000000000300003000000000000000000000000000000000000000000085000000,0x2008000002040000000000000000000000000000000000000000000000000000481200100085000000],3),
  (0x28000014000000000000000000000180c00020000000000010018000,[0x200000100000000000000000000002030000000000000000400600000000000000000000000000000000000000000000c00000000000000000018000,0x500000000000000000000000020000800000000000000400000000000000000014000000000000000000000000c00020000000000000018000,0x200000100000000000000000000000000000000000000000400600000000000028000014000000000000000000000000000000000000000010018000,0x2010000000000000000400200000000000000000000000000000000000000000180c00020000000000010018000],3),
  (0x1400140000000002805010040014000000000000000000000000000000000000,[0x10001000000000020140001000500000000000000000000000000000000000000000000000000000005000000014000000000000000000000000000000000000,0x5000000000000100400000400000000000000000000000000000000000000000140000000000005010000014000000000000000000000000000000000000,0x10001000000000000000001000500000000000000000000000000000000000001400140000000000000000040014000000000000000000000000000000000000,0x20040001000100000000000000000000000000000000000000000000000000002805010040014000000000000000000000000000000000000],3),
  (0xc000000000c00000000001801000000000000000000006000c000010000,[0x1000000000100000000000600000000000000000000001800000000400000000000000000000000000000018000000000000000000000060000000010000,0x10000000001000000000004000000000000000000000000000000004000000000c000000000c000000000018010000000000000000000000000000010000,0x30000000000000000000000000000000000100020000040000000000000000000c00000000000000000000000000000000006000c000010000,0x20040000000000000000000080010000000000000000000000000000000000001801000000000000000000006000c000010000],3),
  (0x6000000000300000000000a000800000000000000000001800180004000000,[0x80000000004000000000028000000000000000000000006000000010000000000000000000000000000000a000000000000000000000001800000004000000,0x80000000004000000000020000000000000000000000000000000010000000006000000000300000000000a000800000000000000000000000000004000000,0xc0000000000000000000000000000000000040004000100000000000000000003000000000000000000000000000000000001800180004000000,0x8002000000000000000000002000200000000000000000000000000000000000a000800000000000000000001800180004000000],3),
  (0x18000000001800001800000001000003000000002000000000c000000000,[0x2000000000200000200000000400000c0000000000000000030000000000000000000000000000000000000000000003000000000000000000c000000000,0x200000000020000000000000040000000000000000000000030000000000000018000000001800000000000001000000000000000000000000c000000000,0x60000000000000000000080000000080000000020000000000000000000000001800000000000000000003000000002000000000c000000000,0x20000000040000040000000000000000010000000000000000000000000000001800000001000003000000002000000000c000000000],3),
  (0x1800000030000003000000080000000300000100000000018000000000000000,[0x2000000040000004000000200000000c000000000000000600000000000000000000000000000000000000000000000300000000000000018000000000000000,0x20000000400000000000002000000000000000000000000600000000000000001800000030000000000000080000000000000000000000018000000000000000,0xc00000000000000000000008000004000000000400000000000000000000000030000000000000000000000300000100000000018000000000000000,0x40000002000000004000000000000000200000000000000000000000000000003000000080000000300000100000000018000000000000000],3),
  (0xef9cecedb,[0x8a138382c00000000000000000000000000000000000000000000000000000000000e0e03,0x138708096400000000000000000000000000000000000000000000000000000000e1c00018,0x2e52a002c00000000000000000000000000000000000000000000000000000000f9cec01b,0x19a000296c0000000000000000000000000000000000000000000000000000000ef8000edb,0x3191b640000000000000000000000000000000000000000000000000000000001cecedb],5),
  (0xf780000000000000000000016b600000335d,[0xd8000000000000000000000084800000c8340000000000000000000000000000160000000000000000000000000000003205,0x56000000000000000000000481800000c4100000000000000000000000000000178000000000000000000001606000003345,0x112000000000000000000000588000000cd400000000000000000000000000000000000000000000000000001600000003340,0x19a0000000000000000000000000000008d640000000000000000000000000000f7800000000000000000000000000000335d,0x18c800000497400000000000000000000000000000000000000000000000000016b600000335d],5),
  (0x673800000000000000000002c00000037000000015a00000002d,[0x1c80000000000000000000010000000d000000000480000000340000000000000320000000000000000000000000000340000000000000000005,0xc60000000000000000000090000000c80000000028000000010000000000000033800000000000000000002c00000037000000000a000000005,0x84200000000000000000000b0000000400000000568000000010000000000000000000000000000000000002c00000000000000015a000000000,0x94a0000000000000000000000000000000000000468000000034000000000000673800000000000000000000000000000000000015a00000002d,0x300000005400000001480000000b4000000000000000000000000000000000002c00000037000000015a00000002d],5),
  (0x1c0001cc00000000000000000000000000000001605400a018398006,[0x10000700000000000000000000000000000000008010008020e0001800000000000001c0000000000000000000000000000000000000000000380006,0x20000110000000000000000000000000000000010150000040e600000000000000000000000000000000000000000000000000000054000000398000,0x530000000000000000000000000000000000110028000c4001000000000000001cc00000000000000000000000000000000005400a000398006,0x30000310000000000000000000000000000000000000000060a60008000000001c0001cc000000000000000000000000000000000000000018398006,0x18050008060620018000000000000000000000000000000000000000000000001605400a018398006],5),
  (0x5d814000000000000000000000000b02c300000000000068140f0,[0x3600000000000000000000000000040104000000000001a0001c00000000000005800000000000000000000000000000000000000000006800030,0x140500000000000000000000000024000c00000000000180400800000000000005814000000000000000000000000b00030000000000006814030,0x44010000000000000000000000002c0200000000000001a0502000000000000000000000000000000000000000000b00000000000000006814000,0x66010000000000000000000000000000000000000000012050340000000000005d8140000000000000000000000000000000000000000068140f0,0xc0304000000000000a0103c00000000000000000000000000000000000000000b02c300000000000068140f0],5),
  (0xe00000b000c00000000001a01800000000000000000006b80c000014180,[0x800002c000000000000000802000000000000000000002e00000001060000000000000b0000000000000000000000000000000000000003800000000180,0x1000000400100000000000680000000000000000000001a2000000050200000000000000000000000000001a000000000000000000000068000000014000,0x18000024001000000000004802000000000000000000000000000005060000000e00000b000c00000000001a018000000000000000000000000000014180,0xc003000000000000000000000000000000000012a02000005020000000000000b000c00000000000000000000000000000000006b80c000014180,0x280600000000000000000000a6010000010600000000000000000000000000001a01800000000000000000006b80c000014180],5),
  (0xb3bd6c0000000000000000000000000000000011cef3a004f756dd,[0xee03000000000000000000000000000000000452b4a0012050340000000000003bc0c0000000000000000000000000000000011cef3a004c140d8,0x42f0800000000000000000000000000000000046014c00130809640000000000003c00000000000000000000000000000000001180130004c00018,0xd5b0000000000000000000000000000000004310468011cc00340000000000003d6c0000000000000000000000000000000011cc13a004f7401d,0x844110000000000000000000000000000000004732000013dd120000000000000000000000000000000000000000000000000011cc000004f74000,0xc671900000000000000000000000000000000000000000139d1b640000000000b3bd6c000000000000000000000000000000000000000004f756dd,0x6338c8003595b7400000000000000000000000000000000000000000000000011cef3a004f756dd],6),
  (0x56c0056f40000000000000000000001f5d002f00000000001bf6b802b,[0x110001b800000000000000000000000d4000b000000000000a1a8002c00000000000002e00000000000000000000000150002c00000000000002a0003,0xb0000b500000000000000000000006d3000a80000000000060a60008000000002c0002f40000000000000000000001f5d002f00000000000182b8003,0x42000411000000000000000000000025740000000000000025dae00000000000000000000000000000000000000000015d000000000000000076b8000,0x159d00000000000000000000000464009c00000000000198c00a400000000000056f4000000000000000000000015d002f00000000000076b802b,0x5300053900000000000000000000000000000000000000002f5ae002c000000056c0056f40000000000000000000000000000000000000001bf6b802b,0x3954003400000000006ed2a00ac00000000000000000000000000000000000001f5d002f00000000001bf6b802b],6),
  (0x2b5adb40000000002bad6b355d6b52a0000000000000000000000000000000000,[0x84368000000000006a0a80441a80a800000000000000000000000000000000000005a000000000000a82a00002a00a0000000000000000000000000000000000,0x541650000000000a694a40140a502000000000000000000000000000000000001505b40000000002bad6b20502b40a0000000000000000000000000000000000,0x210821000000000022b5001135ad000000000000000000000000000000000000000000000000000000ad40000d6b4000000000000000000000000000000000000,0x2b2d000000000002318c80318c488000000000000000000000000000000000000adb400000000000ad6b200d6b52a0000000000000000000000000000000000,0x294a6900000000000000001565ad0a80000000000000000000000000000000002b5adb4000000000000000155d6b52a0000000000000000000000000000000000,0x2ca528d555294a800000000000000000000000000000000000000000000000002bad6b355d6b52a0000000000000000000000000000000000],6),
  (0xf01ce1d800000000000000680e03da07a181cfd86,[0x4070070000000000000000200801080882070f01800000000000000000000000001c01c00000000000000000000000000001c3c06,0x8010812000000000000001a00002680680011f6000000000000000000000000000000000000000000000006800001a01a00003d80,0x1007380000000000000000080100f200204073120000000000000000000000000001ce00000000000000000000003c0000001cc000,0x5285600000000000000000000b681800051d61000000000000000000000000001ce1d800000000000000000003da060001cfd86,0x1c031832000000000000000000000000686033b60800000000000000000000000f01ce1d8000000000000000000000001a181cfd86,0xa01807280a860737218000000000000000000000000000000000000000000000680e03da07a181cfd86],6),
  (0x1d739cc0000000035aeb55aae679980000000000000000000,[0x5c07000000000010821108b81e060000000000000000000000000000000000000701c000000000000000000e078180000000000000000000,0x104211000000000d008d068089e60000000000000000000000000000000000000000000000000003400341a00079800000000000000000000,0x21ce00000000000423a402239822000000000000000000000000000000000000007380000000000000e80000e600000000000000000000000,0x14a53000000000002ad500289a640000000000000000000000000000000000000739cc00000000000eb5400e679980000000000000000000,0x34c6310000000000000006a999662000000000000000000000000000000000001d739cc000000000000001aae679980000000000000000000,0x529a512ab98e260000000000000000000000000000000000000000000000000035aeb55aae679980000000000000000000],6),
  (0xd01a00000ee81800001e000001c180006b80000034300000035ec000000170,[0x6800003800600000700000000600018c000000c08000000c03000000040000001a00000e801800001e0000000180006b800000343000000340c000000140,0x400800003a2000000010000001020001a0000000d00000000d08000000054000000000000e8000000000000000000000680000003400000003400000000140,0x100200000088020000020000002040001ae000000000000000d7b000000000000000000000000000000000000000000006b80000000000000035ec000000000,0x1402800002aa02000000000000306000000000000000000000d6b000000054000d01a00000ee818000000000001c180000000000000000000035ec000000170,0x1ba0600000000000000000012a00000090c00000095a00000001c000000000000ee8180000000000000000006b80000034300000035ec000000170,0x38000007060000a600000050400000053900000005c0000000000000000000001e000001c180006b80000034300000035ec000000170],6),
  (0x35a0001d6b0000003600001aa0000006b4000354000000d758000001540000000,[0x68000700c000000d000000280000018c0000c4000000300600000040000000001a0001d0300000036000000a0000006b4000354000000d018000001400000000,0x1080007420000000100000088000001a00000d000000034100000005100000000000001d00000000000000000000000680000340000000d000000001400000000,0x4200001084000000400000220000001ad00000000000035d600000000000000000000000000000000000000000000006b4000000000000d758000000000000000,0x52800054a40000000000002a800000000000000000000359600000051000000035a0001d6b0000000000001aa000000000000000000000d758000001540000000,0x35ac0000000000000000000012900009500000025540000001500000000000001d6b0000000000000000000006b4000354000000d758000001540000000,0x5800006a8000000a500005100000014d200000055000000000000000000000003600001aa0000006b4000354000000d758000001540000000],6)
]
def probeData (hint : Nat) : ProbeData := allProbes[hint]?.getD (0,[],0)

def admissible (p : ProbeData) (e : Nat) (ws : List W) : Bool :=
  let mask : W := p.1 ++ p.1
  let xs := ws.map (project mask)
  xs.all (fun x => x == 0 || p.2.1.contains x) && e + xs.countP (· != 0) ≤ p.2.2 + 1

def probeBlocked (e : Nat) (ws : List W) (hint : Nat) : Bool :=
  0 < hint && hint < allProbes.size && admissible (probeData hint) e ws

end Signed2964.Projection

namespace Signed2964.Projection

def probeCover (lo : BitVec m) (ws : List W) := (cuts ws &&& lo) == lo

private def four (mask a b : W) : List W :=
  [project mask (a &&& b),project mask (a &&& ~~~b),
   project mask (~~~a &&& b),project mask (~~~a &&& ~~~b)]

private def blockedPair (lo : BitVec m) (cap : Nat) (src : List W) (a b : W) (rest : List W) :=
  (four (lo ++ lo) a b).all fun z => src.contains z ||
    (keepChoices a b rest).all fun kept => decide (cap < (z :: kept).length) || !probeCover lo (z :: kept)

-- Each source is required. Every possible first operation either duplicates a source,
-- retains too many signals for the remaining gate budget, or misses a crossing.
def smallCheck (lo : BitVec m) (lits : List W) (cap : Nat) : Bool :=
  decide lits.Nodup && !lits.contains (project (lo ++ lo) goal) &&
  (lits.all fun a => !probeCover lo (lits.filter (· != a))) &&
  (pairs lits).all fun (a,b,r) => blockedPair lo cap lits a b r

private theorem active_project (lo : BitVec m) (i : Fin m) (on : lo.getLsbD i.val = true) (x : W) :
    differs i (project (lo++lo) x) ↔ differs i x := by
  have left : (lo++lo).getLsbD i.val = true := by simp only [BitVec.getLsbD_append,i.isLt,ite_true,on]
  have right : (lo++lo).getLsbD (m+i.val) = true := by
    rw [BitVec.getLsbD_append,ite_eq_right (by omega),Nat.add_sub_cancel_left,on]
  have hi : i.val < 2*m := by have := i.isLt;omega
  have hj : m+i.val < 2*m := by have := i.isLt;omega
  by_cases choice : (x &&& (lo++lo)).toNat ≤ ((~~~x) &&& (lo++lo)).toNat <;>
    simp only [project,choice,ite_true,ite_false,differs,BitVec.getLsbD_and,BitVec.getLsbD_not,left,right,
      Bool.and_true,hi,hj,decide_true,Bool.true_and]
  exact not_congr Bool.not_inj_iff

private theorem four_mem {mask a b z : W} :
    z ∈ four mask a b ↔ z ∈ opsM mask a b := by simp [four,opsM]

private theorem local_swap (mask a b : W) : opsM mask a b = opsM mask b a := by
  ext z
  simp only [opsM,Finset.mem_insert,Finset.mem_singleton]
  rw [BitVec.and_comm b a,BitVec.and_comm b (~~~a),BitVec.and_comm (~~~b) a,BitVec.and_comm (~~~b) (~~~a)]
  tauto

private theorem active_gate (lo : BitVec m) (i : Fin m) (on : lo.getLsbD i.val = true)
    (a b z : W) (hz : z ∈ opsM (lo++lo) a b) (hd : differs i z) : differs i a ∨ differs i b := by
  have hi : i.val < 2*m := by have := i.isLt;omega
  have hj : m+i.val < 2*m := by have := i.isLt;omega
  by_contra! same
  simp only [differs,not_not] at same
  simp only [opsM,Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    rw [active_project lo i on] at hd <;>
    simp only [differs,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hj,decide_true,Bool.true_and,
      same.1,same.2,ne_self_iff_false] at hd

private theorem local_cover {lo : BitVec m} {s : Finset W} {k : Nat}
    (h : live (opsM (lo++lo)) (project (lo++lo) goal) k s)
    (xs : List W) (sup : s ⊆ xs.toFinset) : probeCover lo xs = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro j hj
  rw [BitVec.getLsbD_and]
  let i : Fin m := ⟨j,hj⟩
  cases flag : lo.getLsbD j with
  | false => exact Bool.and_false _
  | true =>
    have target := (active_project lo i flag goal).mpr (goal_differs i)
    obtain ⟨w,hw,yes⟩ := live_separates (differs i) target (active_gate lo i flag) h
    simpa only [Bool.and_true] using (cuts_spec xs i).mpr ⟨w,List.mem_toFinset.mp (sup hw),yes⟩

theorem no_small (lo : BitVec m) (lits : List W) (cap : Nat) (h : smallCheck lo lits cap = true) :
    ¬ build (opsM (lo++lo)) (project (lo++lo) goal) cap lits.toFinset := by
  simp only [smallCheck,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at h
  obtain ⟨⟨⟨nd,absent⟩,must⟩,steps⟩ := h
  intro attempt
  obtain ⟨s,sub,liveS⟩ := compress attempt
  have identical : s = lits.toFinset := by
    apply Finset.Subset.antisymm sub
    intro a ha
    by_contra out
    have loss := List.all_eq_true.mp must a (List.mem_toFinset.mp ha)
    have full := local_cover liveS (lits.filter (· != a)) (by
      intro w hw
      exact List.mem_toFinset.mpr (List.mem_filter.mpr
        ⟨List.mem_toFinset.mp (sub hw),bne_iff_ne.mpr (fun eq => out (eq ▸ hw))⟩))
    simp [full] at loss
  subst s
  have notDone : lits.toFinset ≠ {project (lo++lo) goal} := by
    intro eq
    have mem : project (lo++lo) goal ∈ lits := List.mem_toFinset.mp (by rw [eq]; simp)
    simp [mem] at absent
  cases cap with
  | zero => exact notDone liveS
  | succ k =>
    rcases first_live liveS with done | ⟨a,ha,b,hb,ab,z,hz,fresh,needed,eq,tail⟩
    · exact notDone done
    obtain ⟨r,pair,hperm⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) ab
    have fail {a b : W} (pair : (a,b,r) ∈ pairs lits) (perm : lits.Perm (a::b::r))
        (he : lits.toFinset = insert a (insert b needed)) (op : z ∈ opsM (lo++lo) a b) : False := by
      have reject := List.all_eq_true.mp steps (a,b,r) pair
      have outcome := List.all_eq_true.mp reject z (four_mem.mpr op)
      have hzout : z ∉ lits := fun h => fresh (List.mem_toFinset.mpr h)
      obtain ⟨kept,hk,hnd,hfin⟩ := recover_kept perm nd he
      have after : live (opsM (lo++lo)) (project (lo++lo) goal) k (z::kept).toFinset := by
        simpa only [List.toFinset_cons,hfin] using tail
      have new : z ∉ kept := by
        intro hk'
        apply fresh
        rw [he]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hk'))
      have card := live_card after
      rw [List.toFinset_card_of_nodup (List.nodup_cons.mpr ⟨new,hnd⟩)] at card
      have room : ¬ (k+1 < (z::kept).length) := by omega
      have covered := local_cover after (z::kept) (Finset.Subset.refl _)
      have retained : (keepChoices a b r).all (fun kept =>
          decide (k+1 < (z::kept).length) || !probeCover lo (z::kept)) = true := by
        simpa only [List.contains_eq_mem,hzout,decide_false,Bool.false_or] using outcome
      have bad := List.all_eq_true.mp retained kept hk
      simp only [covered,Bool.not_true,Bool.or_false,decide_eq_true_eq] at bad
      exact room bad
    rcases pair with direct | swap
    · exact fail direct hperm eq hz
    · exact fail swap (hperm.trans (.swap _ _ _)) (by rw [eq,Finset.insert_comm]) (local_swap _ _ _ ▸ hz)

end Signed2964.Projection

namespace Signed2964.Projection

def follows (p : ProbeData) : Bool :=
  project (p.1 ++ p.1) goal != 0 && smallCheck p.1 p.2.1 p.2.2

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem checked : ∀ j : Fin 79, follows (probeData (j.val+1)) = true := by decide +kernel

private theorem count_partition {A : Type} [DecidableEq A] (f : A → W) (ws : List A) (nd : ws.Nodup) :
    zeros f 0 ws.toFinset + (ws.map f).countP (· != 0) = ws.length := by
  classical
  let z : A → Bool := fun a => decide (f a = 0)
  have test : (fun a => decide (¬ z a)) = (fun w : W => w != 0) ∘ f := by
    funext a
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, z, decide_eq_true_eq, bne_iff_ne]
  rw [zeros,nd.card_eq_countP,List.countP_map]
  have splitCounts := (List.length_eq_countP_add_countP (l := ws) z).symm
  rw [test] at splitCounts
  exact splitCounts

private theorem extend {A : Type} [DecidableEq A] {ops : A → A → Finset A} {g : A}
    {S : Finset A} {k j : Nat} (hk : k ≤ j) (h : build ops g k S) : build ops g j S := by
  induction hk with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem not_live_of_probeBlocked (n e : Nat) (ws : List W) (hint : Nat)
    (nd : ws.Nodup) (room : e+ws.length=n+1) (passed : probeBlocked e ws hint = true) :
    ¬ live basicOps goal n ws.toFinset := by
  simp only [probeBlocked,Bool.and_eq_true,decide_eq_true_eq] at passed
  obtain ⟨⟨pos,lt⟩,ok⟩ := passed
  have size : allProbes.size = 80 := by decide +kernel
  let p := probeData hint
  let mask := p.1 ++ p.1
  have checkedAt : follows p = true := by
    obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : hint ≠ 0)
    exact checked ⟨h,by omega⟩
  simp only [follows,Bool.and_eq_true,bne_iff_ne] at checkedAt
  obtain ⟨nonzero,certificate⟩ := checkedAt
  change admissible p e ws = true at ok
  simp only [admissible,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  obtain ⟨literals,budget⟩ := ok
  intro h
  obtain ⟨k,built,numeric⟩ := contract (project mask) 0 nonzero (gate_projection mask)
    n ws.toFinset p.2.1.toFinset (by
      intro x hx nx
      have yes := literals (project mask x) (List.mem_map.mpr ⟨x,List.mem_toFinset.mp hx,rfl⟩)
      simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at yes
      exact List.mem_toFinset.mpr (yes.resolve_left nx)) h
  have partition := count_partition (project mask) ws nd
  change e + (ws.map (project mask)).countP (· != 0) ≤ p.2.2+1 at budget
  exact no_small _ _ _ certificate (extend (by omega) built)

end Signed2964.Projection

namespace Signed3110
open Signed2964
namespace Hints
private def shiftTab : Array Nat := #[0x1501020e0000060e06090b0204020b0004002c0100040d020300000401030300035c120107000f05002f0a010d010c101700030400020b004d0313000007030a,0xb0a080500010a04010102050b00000405000f02060a000707000204000018052d0a170300001901162600000b07060003010c0900013b1309020f011c220304,0x200010201120600010100000e03000b000300010e030808041805000b0001070500010c0105040a0f041d2400000121002809000409000000180a00000300,0x1300000b0d1800030003250e04020002080534010505020004100205002f030304000105000401090605020218170106170407002e1d121500100201040a0a01,0xe00000a0217030708050001010003000747030901040200000e0f02010503050504000c040205040000010602012000020000010c070d0c1d020b0907030201,0x10005010606010500050000010205040d0a030e0500011d0e010b00040a0301000500030100030319003103000e040300070001010703041b10020d062b0102,0x100100000060b00010145020409060700010b002b18020202020315050b00030305070107140605060d03000710040e000c002d000526010413230201120d0a,0x70106031300070006251c101e000400062a01030506010306000400010f011402010e013f02020002000909070e030302020125420d000a010102000c00,0xe00010230042014050218010a19030901212f0809021009000e0e030e170301060107000a01082601040b0200010f00000300050212000000000b0151320300,0x5000616080b16000b0602050018020537070d300209020309000c020e020f0718100e001b000907080c0100000b000018090017020803160414000417030602,0x15161d030a0001070b4a81250b0000061232010208091b0607010e001f0b0f0c05000c010300190701000c01080b150000020a0401020003050a01743d051220,0x206110b0a00010b000b0e08050100100702120300082c240004080410010b26031503310200000407030200000c00080302000c00011900280303010f090101,0x2001b040d020205010000041f17021800000d0e000000090e1a0a07050303221714030000120b0b0c120202310302030211260200020b210105020c1b01031e,0x8031b001c04002947120d00090f1f040600002b0a340200060804010603000206112208010502010702121f010000060a07180801060a150100380002020713,0x1d03004a030912080010110001030202090600030100000b03040400330a02010b000b0033000b1e0101010c001d05020e01200200050002010f070106062004,0xb001000608011106030703020b0608080806040f0012140100041633031703010c010100010a003d0d002a070b0115000e0006000b01000006020c0206201000,0x10a020b1a1d021d1b08020b01040f003708000014130204080200150500000306060024000000010306000317000202260d05010105091226093b0700000b30,0x7080002170a03021f0f091d0901111b0402220100012406020b1025010002050b0009071900011a300220060100122e011700080b0b1f10030d2d0b03450200,0xc01002606000000001209040103110203090018110902010203060c0206020002010d0100010137100b0503000103000103040d010b0409040407120a110026,0x12410401231804010000100004020221090800011005080d1c02041902170302020c01010b11037b0200010000050b0601000108010004021803032301050204,0x601418010211011d03230c270b02090520010601000208020200011702090709010d181e0107020e0c10070303092406030010010b040c0334190f1b03000507,0x200400020001340f1c040001020801050b08020b1e0d0a04020100060c0300050c170e00050226001124000100120402000335000801017d000a0008051f0d04,0x1e2200000712021c00041501010d03020b080a040000010304030441050304830e231f00160d01000e0912070906070a070400030e0201056500000d3917020c,0x401110a030d0207031407390000231b2c02071110002405102f0f0e000708030d00030000040e1439300105030b00390218030700160c1b03020e2d01160004,0x60400052b020224000501020500120a0f010b0639012a02000b01050002000200020910000e12000f0503002800030b0d1e0002062f02020006050803000407,0x14021f22060014010435240202080d00003227170335141e1f021e0e000200030e04061d231b1905050105030101019e01090001010f000f180a043428050024,0x150600040005070519380014001c0401050202204603015a0802044c0501010766131216010d2a000903000233003b08030c01000002040708060d120f2e1709,0xf00130e00061401040405000014170f01011304010201100b0a142a1322281a18091c01180401080409044c1901050000020012010907030303111200231c04,0x170003040121072008010d1215050e0e09131306010001001b0c000005000b0c0d040c1e02061017171d17024d29000a00081600031118020103040d00001710,0xe2004001613041e01151c060202112b00030605012d160417003c180010256a0f0a0b06052d110011040002002b02060e09253c47001f0020020c080e44011d,0x1021d31160502010819060103396410010e050400060b084301020a0400050100190500030a140a0b381b020309100002000501180f0a1a2429011036020f0d,0x17020102281c0209021309040402040f050106180204050302080b02100200120a303c050001001207110200200222064e000638180100400b0500060000000b,0x93e1234261f020f0a00070065143e500040035405140210070f0d00011001020815061604070b0203100a030000040700030b02132a0702030201020701003b,0x70202071b03014e2409040a070519131c06050a0102130a0808210c1402083d07071302000a19102400010a03210e022306183b0f0900100f050b1300120901,0x467240180023000a010103030504040f09200201011a0d021213030001001404170601100113050581262d0e01390e101a000239021a0e00240d07000d110915,0xb050401112e0a000833081f80060101071b030503053521024a1202010205031b0103020d031e14000000000022330303001436004200122400010405011132,0x911045c010a17000f0000410e1c0315008607020d063b000600080022070003002c160000130f1f1b01000209000d02030d010c1b1b090c2700090b2a0e3c0d,0x2118040401090100000043000e421e0b3a2d000702000b011a000c010052010901041803132327000f1f110201050002000a096804030c08090e000602261e13,0x134014343a0a1510062e1b031900010603210100040e05070d0400031b1f030841032c05201e0006353001014e000a562023100b070a00022c00191807081413,0x60d280b002401051e0303012a1415040203020a54530401000502014a1f038224080146260106004e06301105011623051a020108011c00600d20000405,0x80b000002101b030f04310408060608000612300e0623130e0a0c051d35193a020a010b480b07251c020334021a0f151503022a05280e07040c00030805010c,0xb2800040014000b02010671130a058b0627072600063b1b00130100000342060001012c011b0000150909070b241015650603054a0044110f0904142a001201,0xe0021000412152315020a022121006000400c1601010200021811050702090d1e08186d281804140000091602580427150003100001001b0d]
private def probeTab : Array Nat := #[0x469c0921914389292c087320d3008a0008000063000114f05004a34e10300010008001048c00018024072c0860c100038000000801002400,0x2c9a28c0e0001602862800280007191438c001d10000201962c7800b2e52387063439e00003802e99d809c043c50e0009e581c0870018004,0x26243c5880060b0e31109581c0000e04001122400700b0000403038c423108100000220078388604e39e90040a10e0cf1a2c00001601c387,0x1314b0c1a240310e0c6003c1d11e00006000205846183090e0e1d181961c60106784930e840961204583020cf002c2049e060109a182c388,0xe3004508003873c1c00100200870048f098e0092c041d643890c6000204016022439e061cb880684f010058f07131530118c01c50e0c393,0xf05381021c58b442001207189004688606471838002005808e580000e783a24604f0288886ac0e8400c50098010000b80000a5160e1c09e,0xe3192c001c3800200392340170000200070e1c0073c30607421c50c0631607080c3c726f0f1b1878381171c0888ac04c30e1cb9e07143a6,0xe00f00001c0920400d87228e1a70e2e3818800109108c0031601180382c6018ac108c241c3809d14b00000008b12580ac400c0803c08387,0x10c901005840c04000003c1e3898e1d14700301160200022002508000580803c0061a042c0001b3814708005c5460160118000172e1c087,0x12000800e02580001c0000110003002d603101c38000d83b00e4838c0000911125e18746083ac029910486c000b064cf00781e3000e1c087,0x3d140002e103c6430c001004c600001c04f442c3870000000000d1803d1918c0f3c387065c0213c003458a783873d1c025121c5b8161c600,0x2203c30eb00a1121c381001c3880e1929e003008c2cc000024309000c016a7601e21610009070e1cbc3421cdc5423098c16b580b120058b,0x8c00c0e008211808616000438c1600100062004e301c3810e5800388300078600381180000b0204380001c38025140450e1c63b0004b80,0xf1a1c6004838c0e243a6021d18312841026c840810e581ac040418c2a5cf00001c3930e0008900043880004000180048010022451679012,0x1279621162c44396200978ab0001083442c18005c6865cc9e60190831204007021c0b0261c61a0318093071c38700841871c041800e021b4,0x1800b07263000c0000c0c18003ac0e1d18102243a116009001a2c382001d10006000030000407024c10058240872e00f071800387001c316,0x204009005a180001d1110208b08068c3830e04480860c603000c609004860b3d1cc132c004810e1e296020000d06022802d1060c004c38b,0xe3061e0eb83960058600001c023007c007860100210784090e00002000000824ecb072c01b00421e2c4005802c04080002c1c19e0e02401,0x389103098c0e30617021c187060c01624001000e011000ec00020078007461c00618500070e05806000df00460460942300803c1c381,0xe0c40c32904c500b90b93458b27865c248060c61417143971832200003008442a898012322002cc1da82c1c0870000000240060c1608480,0x185048002583803c58616421c009246120012000871200987001c6070224b8b8a4928700000008c1c016025c10112000970e0a20c045810c,0x630d2001207073c086004e2668c0f146002e383c500585a22e009031804b0c18046070e263c58f1cf0802080168a04483028584300300a3,0x430000004e22604583232c580016c1c3832c1c3a606184a10e304458a2081e08689098c1c3c3164800b401c59e0e1c38388001960e08009,0x280e34f18780140e000a50e1c0070e0c400180060c0f20187061c1ac0e4e3022d183818c211300000100003008912540269c0c02c0001080,0x438b00001d3018f1400c0e1c3800f180070000383000060b1800397026438116796096118c008a1d822901cf1600361870e843a65915094,0x2c0122c3c00580000c3804c2438900d0b802ec441e2a1c38000240000e00012240c0070050f0c2cd0b07121d6008e0e300005a1a3582cf00,0x4278b021c1d8000e78a070e30589421c1923c1c995065e39e180401e1208d0b1a6c48c3c004802cb018926311a0000c08c980000310c0000,0x4046002a1c6801a6001e0f1c022005800000480003c00b8c031400200b040c120003b2c0402c007839200c81c72c2098000013808a00000,0x8a48b87021c0000e1e40001186070855780011c644001c04318040160e003872a00387048808c0200013000048026000003c02346061e280,0x230907182c4800200016041c387020838d002c981880000c002c00c022400902322820e4a2070058f0902783800c544840e89043181c492,0x4c01ac005800b188c10018481930e1c700006a58318013a190000202e183800008d80000002146040070e044090004a0c0024180,0x220f03041c38c120010010004960f0c043023278b0030b0c160860028000000c1c6010002207122c980000c0000e00b8000003892c32307,0x8c2c009001c1002605289001d608128468b760e1962458481281c0133d0c00b0e78007240c9a14458000010c00800000360e003835800409,0x2221183228d16940003c2c084003109708a06000006617000400760c00080c480c3011c0250e00000000412112001000084016026c00c,0x783800004d9e1c1c3c58c00600001c0020078114180180044304891a3848c004cb00000038d2c003890001180000218002863080c1e2a7,0x4a00b260e040009a7838c46200000004022001cd802c01082580441c8e1c616011c1000000023181c000191801e0004b9e00000163600480,0x6b00a2011c08c5801b004658b0300780030001dc500046070c1c09e000c080000000028b0b173c1d90c24584801694980001d2000000680,0x31c014000000412c06803650000421c40716243800e6c00960322873c386073c300138a003800e0008d00000000e8ca076000100000800c,0x8d20105001c60c041c58002003ac2084b2602010812c00380881c00706326a68a040000088f0c028801202000070e006000eb0f0c245d180,0x8e0c107460228000040800000017029860100000800e26181100189a0e2c0180e1c1869e586070e1c40306383970e5990c042d607300e7c7,0x11639328213008a040140114192287800000c00020c04487000c08b0e30382024cf01161c00318001961201180000039e001c480182c007,0x181cd458e1e2a1887a30c002e3030f14645009c5a0268810b402c487200400700e4400007860c207a2c8000018c18843841810b004080601,0x12062a10e000030c0039e188cb07064cb0c181d0c502245872c550816c2cf001c0048016016344a5961e0e085833c203c52c4c0070f0c016,0x59159000008f460400b800e000200030580020044f188c000422c047041e2810e2021e2c80095021c021180801e000460718b4380100d62c,0x440800b425e2c80600402001c62412300088a256078a08382001c3b00058383021c6070204f0e0e00101121c99200000002c341813c00580,0x20e5c5180408202058010c0460b270c8263d186001209801301c2002458f21420001e00c001e8c5dd833c88a0006000b0261c01e2c5c383,0xe30487061c3871878080030c4833d1a381171400e0e3108036509820078007380001600045ac0e1c3800f0c5813cb16111204313002c1c5,0x22e1892c8820100002072c04003608c000000230018253008c00b8c0714f0706000008a0118c5c0c3800e60b302e1c38018300002c08600,0x551e3830e580074c1d0806c022008a4c48c1288080001c00312221930e253008f1d3308a00032000000004000000088013440c4ce00b0081,0x239a0e005800000000006e400005c5a60e5c0a30f183a646040820e0cf21101c007000180000310872c003880030000421c02c000a187,0x80d5122d1c19e0a58023120c4830e1c0468c1c62e2c35087004c41624317033c1c41618007163714f012c0000700000003c010c60f1c3ce,0xe5a2270f1c3070e0c10c1a040458c04001181c00216585a1029c38c18203ac0e584431ac50038e483c3184838c4298189420c90c1294b16,0xe58192001c1a11858323064c3a10258381770c3038878a0088013144658b070f0c3800f1e3030230f160e8868c004a30742b008058110c3,0x2004974200022009c0884c5c1096058400005404616000ac1858007161c022101c6010ed90013c012010204f30181d8003c5c387425c3a3,0x98000e00013000000c00240022c24380040000742b10870e1c0bc02303800f1980012083c30078d8c00784828a1d3020224499190c007,0x890d08c42000010e016070800f0b580000900003923c58b871a780891f0c1018a5e7c41c8801e00003821a086000e48381101c60c1004007,0x2a3230e263230f18400040008701163078a2c0000000a138a58a8b3c00002003458d580400c1878f0000261a14d051170e043811310b00,0x50003b6884c38b01196470e24c16021d60c0eb0c0700984c5000038100022808a1c9801a00000025a2040eb45876278f00002c0301c00381,0x202398860c604021c3c324c0387422d9071c8c996880d6130e18da1253c38700050c5966821e882438800786871c01082445a19e18c0092,0x20018000010128a3498902490993c0228706f06210ed800230006c70519080461cf1e3c78100005a1920e0c0c70e00017600018c2c00b9e,0x8a303bc0e21d221805c270430007000490c1604000060070b064a3002668b96464c580162003b001048400017a30010496180218c060c001,0x420e189451801e02082030e101000000009003038006963a00ed86230e1c00e12000000002387161c58c5058087060230c460c106020464f,0x881c0c33c0c382021e3872e08045861e4120e003a7004cb0700005832d18145420038302305830258f01005cb800e0c0130000387022c044,0xe8c0878a4c00c0e0c98340243960f340001810080860049e0e1c9831c241195c5810016b0381881c38c1a0038724040070e000966514981,0x21e4168a223890114f1e304a38918318010e24497021c003041c0070e1ca880e0858e182468b0e1d0b25848b00180001612264210e244ac,0x18007000000000000010000180000c38088004800004107001c081162439e0424121129e18826301800206683160060000183b08624481,0x200b2200000008f14607881cb80001e2000e040930021000068520912b038000247008a001030e0c000021c3800e1c3870070681182c000,0x182018900000070e856080084f0b2801800010c3802710bc5431800002001014ed9d8000b01008848b87103228006349871600c000200043,0x2c1c582432039200004801088398281c007001c00960000b000b04870e1c380460000c1621097181c3a5001c0072c0000100b22275078187,0x114607328c1c30e8c4c5882458c18b43c3005840724480090e1cb45101c6014224607180919e3c040800000380125c382185c3800084497,0x103498902301a20278b013c8a30100000870e080a3423040b0e004872c58609262500386351ac00001808c59087100048100240468c30009,0xe2580d0e0c38712784017c10180646038c2e0101218c860c100918b0e1c5c5185802348004801244388604802c0e1c0002c311000f1c380,0x185c3c50e3063806240920e2c181024d009010c44e0110981902c00c643058c001c387580cb0710203800e0d8128a646160005387001c600,0x21c0010e1e1871c8838d2c00a030e1c581260000102343b6421a2130000a090e240922e7838990013173c00000025a3070e48021200418b,0x3c003870088000421c9074600607001e780001c6004c340012c490878e00022021c000181c58000204808c00387002020086040001224001,0x24303963c2c5b0000c6040e1d301160008e001c01718845cb06602210e5c0000e8c00000486430e000300000f143c0e18100a06164c7801e,0x8c26203462cb462c1c0090e30380031400b00040003c009808c8404d185000c008400818000093c1c9901848384427a18700016074408583,0x18881b2040408c000d60002021830e000262c0000b8e249870e1c007111c008240450d00000012432680008c087030e3c48ab0c0058003a0,0x144402187141160e003a7600000c1800000001c08016057a446004c68c1c0000110a890e2c08b071400c281e2c6046c08c06340168a60383,0x483b02c8c04500483850482281191420c3c0cd82000000946001071a103810006297002e28e022498b2f15b320860f0c046438016bc380,0x1e31e028c1211201846000018000846150e0180036005c31a262008c4039e0000008007a34d64583800e1c00c0478b078a1c3824644009,0x20e587025a3824e1c630001c98c8e5d6010e20183020d08b008c6000e0e3960e000070068994048a780008a6ac9b18b830e000340284001,0x86780001a000390118022421c0a0022d0b0024c480011534600580968c00403064c1a212000210f0ca1e011800016786130e240870004b16,0x24303c5008460000000800e30f1e04200870e1c387122c38432304960eec4871248380180839e3c04009000000102086170c1c3070f184c5,0x166800900200000024080260048c001c01306003893c00480301c4801278016461cb0c020c0000e9e20701140802648001120228c1204387,0xe30007022448718046461824007001c10c2e483b0041c3a1121c0001802400120c3832c1c0ac193c1803c58000180060026519830000601,0xe59080000038b02304929a00dac009c3801244614108c109000100c2e240018600b000c1c007122c38c961cba20e2c5800e3001e2c02200,0x450cb0c190c0898808403060018d061cf00360000100841802c00607063000700004920000007105c20312867922518da23c2d1000000b07,0xb000011140000200000004c4800698007000404300310a70f0c3c80114412021e180000000018243870668f170001880009a2ac0000410,0x281c60708844803c00393241d3160e306800118009282038c18040000000b83582c387163018948006121800b093c64b8300311000200400,0x4e8400088000228a780460032214160629e0001080001c014001c00312780010e48000161c087061c3810000045007960c300d0804458416,0x23a2003c0908024080130404721011c08000480070000b1400018071820b808c1c04600006220031b086c78001003400c125800058c2180,0x1804200f454e79308580000200343972e013458e0d80b000001778c002216000070e000000e1c38716040089000b803cc06000030f00,0x2600f0c4a1c0a6466010006000010634087600462a58041a0020c1073c06793065801217393870000f0b010c00000000000270b0c0000580,0x180c0010ec00000eb008d1830d03000038002981803c021873058b00023018a0e0001318001968c8640c10881810e009968a1c3878a78601,0x193cf160f0d0930204a8702004812f18045402c7000478b0c480061688004b20e086070250382003048218243870e9808246d89073c2c61e,0x400119e0e1cc23000cd00162c487245c807040068000001880230b08111c387040c5811c043978ab25895824387030c107420c4800220580,0x240002c4908c4204000161d8021232289181cb809c2e2823c011a32c799012c0060017140070079180002408b4a003960061601301cb23,0x3c004870e5c0003c9c38c00b061e000231b00243804a00000421c4876031087003240000005a2361c0c41e98f1e051438004013434008100,0x42885872a040078649608041c6208e62380021c1821320017120101e180014518080180118b80420c5b90114480007a5c518046072c34582,0x3000b42040168a5c5003c050c62c00f070e58d0c8a2c18034786457f2121e1604b870230587008400e0e1e322164d18190053008678000,0xb06109400002005804c1c64100040432e3000000389870e3840c2e26180005818c0430f47041cf4650618000208380180439e4a1c080,0x11c387168c3801624082041cf001800d8b003068304d80162c08b00001d10000780460e0222606853018c08f1e024964500001940e30644,0x218e000c0128e84d8c4258007000518600000a2120cb00043460a02000a80e02402160d2871888022002c00742c018000011801a8cf00,0x121c00006326800e84600643008c00b000000c00030000000580004406006090000007182cf039058389000001e000840000003801601b00,0x6001101881e400001c0000e241c718004810000382000c10c0e5c20c060c3838e20da12c004203c1c0010e000008e0039600023090e5a180,0x1024393160c40c0278b2110784ac3cb00ce121c6870e4808888c109e081c6004424b823d1c0328e840034c596210e861a32c2c0802c1c113,0xb00800e78181000048c682c02a12326b0180038010000010e782098e4c0215aec117000c5800e5c0474e001c70050615121c3872c1c082,0xe2c3832e240478e002c301107018c8c4440004101009c080181e30012000b00004587161c6020004aa12404080001c1a1180800101181b0,0x409814600003a20e0c0070000b83021c387183218a0e5109200306160ed40078600015001e2170e043871a4cb160e1d6264258644181c380,0x420068c400044b121e1801a00387009c0008ac848c07151360334000008940300c049e027808c4661897046d09e3c1c3802c0c601180c581,0x581c386340014f3c1c445061c401001c382180038000580472c0000002300015800126007a30706000002e00000005860058880079614104,0x16b081610244034284101020038028003a1027858c0025082000c000010c000004d00b04021800e0000000500b02c383808f181072400387,0x12316018a79302245840706841962c00396281c0168c580020e84383305c01601143960e2d30000309800e00687001c0070e1c0012e01380,0x1020607020d61e421c381008ca000e78381581c3870e0531e0600009011c00900016000e0c3870231107602d1800c584870230f01061c712,0x3c20b2c0830082027800e0c04b472e2460c020860c0e8460002b9d8c0e005a126583a20e2010c18016092c58b368cc258e06003074201c81,0x2d10f018a2d613062c3a24e58991422c496582e3000f14480260c380012e2822a2c4bc8c78680300018000043968e5c604420460c040cf44,0x10841260024b87186d10018000273c0220c0e8d60b0200627000108b58b000001156008c0410006243002c04081062460b000c00012303c3,0x192061c008005c0481318f00007800c4200387023218758d43b08a5800712ca22c0c00381001c500245809b0208f03189c5890200608,0x182531206322871a0038042000ac181c000421c636860160c2424383461c601021c7070e84600261d386880c3c5885809e0e001ac02c0001,0x4e784840e1d61b1c1c081585840710e408200011960e0621818083c35a080872cc130c000008206062800200b23101e189002c4892608645,0x121c1300310082000049e041e3c711121a18c1cb222c843971800007101c09642043c3001c009181d003001838044040818c303870e4e287,0x20ca081600e44424cf0b021c00100024004e096080e0891600500000e000c42c1d807581c0070402380100d301040218b00005803c0c39e,0x85c41e0678007102400000000000e000002000d0000003bc18041032c2418100303c3120000058404800c54622010c0460e183800e20100,0x44e3308c063810e31d83304848900022825830381442414300240000034d02020419e8c1c02c0e18c0020241804eb03960000b8706c010b,0x168a1878684492000860700010800e0440d001c6c4183848c2c003805804c2242005801800b8718080870e4c000240c68c422db0c46c8000,0x24607321c02d2e00480168400d9e000008cda59e0e00000002c03b8e04a1700b0383001c00e4201c96182e2823000412000000c9c30380,0xe2db3b06300920e0418960243934314b0709183898a040c800003a28600b030600012061c00c18310a2000110c00984a1161d1004600046,0x114388043038706303a100200a10e0049346262803d143896a004871200007060463000000808a7808c0600000264000012243875001180,0x101d40600383822d1cbc6448584d3c54408005c6090f18307581c59e245468c16308af2e00002181d0c42f20045000858c0e2c0930004394,0x3c023000630000001d1070279a070824b070400b4d12003803c041800601080421c38c0c1000700b04872e3062f0e00000645809e3c02687,0x46306210e1c387421cc03061cf072804096050c6076c2419e121dd8d0678b03029a79e0f180453c24b80001ca0134303ac0024387021c645,0x8c1c3c32eec5820e1c0ac19101070e02587005e3001a1d62c8c1c00216350c50e0038b6248383020221644553090e790142c791074c04183,0x30780000e0c392600d2000e2ca00021c4960f0c0162f222026058a16010c0004e586082830f450e30392081c1830e00000190c08b5826394,0x46e09802c0a280004034e0030f078b18487281e3213c1c3880eb00870430f0058080003c0c000001800000000000c0c43c0000000000119e,0x316458878007020c00000080c700049006004b083c00003006460c860582c907a28b182c38018c0b16030c9c6021e30006246070030b45,0x230396001c18000000000e8c3c524583840f1859502587160e103842c243872c2c6028c30a458a580040604f1602007452a24002362cb1e,0x6023001830b1e0118000291839600858070e8cf0d2c8462c0024018061c044762c4130118380026c1c5889c9070c000174e0c407442c387,0x5400c002c0173c3108b8d100166030582164e3070e1c18242243961830b1b0030002180000826d04821604593000009e162040700045c4,0x62306043831230008300c080001c103420018100000390000007008400710044c58e5900c043160d10262c6882e3c70e881811830080,0x240440e58607000062c0018388000800c90ec0010078480061c080000049712580883c24f07005808c02841ce601c0070e003885878030,0x90c3c003810000000011000000800800000480001cd000ec0381044848200c171e0e204c63c10900042d60c00600022400c005454007,0x591c000001c0033c306961030f431208c0b2e1e1872e843a62e0c607424c0c6061c6013c458012e301813d0c38705156363c01e00128c927,0x58f00261e7875825da62cb04c400001140ec4c01020438c260038a2a00013020038076004804c30022011900700203890eec0070f2c580,0x220c2176c00c4d0020c0b06001800e3101300009a1022402c44350898f100210e00d08021c38c02c8017000400b18b00438a1c0000e5cb80,0xe580438a006010e00b8c0001093007938c4084f078a58b0b44b00014400ac63c262013c24b2002841a016003870e0060000006070834187,0x1971e282531e42500162c000000e8c9a100001c60e0140c3c30007001cb0c0e30f07001c022005842a4c0c4003c2019e161c4800120047,0x100c39e0e1c00c0e99e000e00380061c000000db0c4c30a830ec058306001a14220380061c62c00006070e30000000c3c4581c39b0e00387,0xe8c0075855609600000c000000042006870034603001c087001dd8d281c400160e2000e1cf4304018230e8da011cb00893c862c52c0c39e,0x24000870e1c9870e4c009320038b0e1d3092648481000c1813c785970e20f052c2d0c5123069e0600380005860b01200170e000000000f21,0x580c0450048007120038700784a1001d3820314f0700001260202187003228000c062c0078b07040c0806b180a0467838c00183871830000,0x201e6000e38380021c1833c00f07000038b0614f010038000288a20018003880002380720c00000004808a0000c427800076000120c0400e,0x132e280581c4834648b028a1d0a6000060004c800716000000e022800000017005c0160001200000cf25241c3c68a0010d3600389001c107,0x3200900040160000c0f07121d0870258000001c616302c0024600080347890202518300e7a40c7a2519e2e04d8000001182c651a10e00092,0x2400003001c00000540160008001310c0030098008011038000306030f14002010c2011858580000c5c51801097000000c2c1c0160001607,0xe086160e04b0b8a003c5865c382000000300000070004f160004387126c0020e1c01388b1601041c3802604380000109e1280483021c000,0x562c3005c0000e2c0002c8400000047170e50b038e8c916003104458c039e0420f1e0e0c3c70e2458736680032c5c1963d1560c8e05086,0x5cf0800250c70600112501c18710301800ab02060e01621449c38200000002e04197003400618310831800012001c58044c1a00021c3a4,0x58781a11a30180181c045480408c0e30b002c58b0102000168c1c6070e00081013c180003800000000035810ba13c1c000020c00c020800c,0x182108b0e500870e10b830e598168e1c0000e9839e2c5c397161d08302301870648000005963018851000000400868e187000d222021c000,0x2c005803c1c48c0e2c3c5005c39e6c0008988d04803c0c38842590070630187022c98b0e0cd220200044871109e5800007188c0138c1c401,0x16005800e004a14204a96880c917061c38700840808a0400c0e08f080e00f0c004c08b021cb8e0e240244400180000c3c60e0e43b111a300,0x2000000e24b0740323010e1e2012d1438c581cf010f1000708000028c1c0003ca0480000009658240000a6c407181c0840e30b090e2c081,0x160000002000c8000811e0078000193d0802c080310001383180460c2c1c6032e501160e0038901103c7000c01b421c0140e8c2000e00008,0x186c9451801307041c03612a01070e30387040000000242804c00587421c380581c0260088b038d100070085686005c9210e027800e1db2c,0x3c8859600280072c780001335c92160000318009870e2d10010003a218006078c1d0876c25101020061e000038c46000000e004800008080,0x1c30000200263c00645868c392001c000423038706003a38c5838802000010e081b0181c0001008381121c6002e8618306110921918b87,0x480002e2090802003c358581000030916011408926261920e0862200003810030000180400c00503890001643000cf1e0402280180d300,0x2448022001c383243000806b0397183049e46b11880e0e79e0c8c61618045818a1d62117222b61258b2c08591038d0c70702010463d18507,0x6006070e5a2ac0404b0110594020e000000f11081001c4460031134102cb4b0000f1228263010e01317104c60704489071c4d6000e1d080,0x1d180000039206b064410240320c3960708b27871c601872a58387428e38b8a21087969c3800e30f09005838c0024b2c6401080420182c,0x300302c0040044001b6128808b000038000003c52850080182c0010e784ac1c001820e1c6003c8c01e0e2c0263c1cc0c6c783a18e05308,0x861c38a0e00389002580b0e8468c005809e02262c4000110b8e5cb128ab0b0800b0b8900040121a2490086000000001180248c6070e00600,0x18040c45916280165039b1878030120099688480001a2c08b0e8850c16483972a01e210008000042000b011418c161c3800e4c3810020016,0x2cb000044000b0000030044000000678b0758581800e7800c0e0400b860099b3c04a00160838c3cb13453e2c000080910b2c8c982061c0c5,0xe000432a20f30240532c8c591800404ba6000038142880070208b088e0d3070000f36003000b000c0161800189011438c26580430000380,0x3180700051c60110193367a30212251804000f07008c200000108c1600000160008c0602303007839e0e8218c0d143879c2c007024d636,0x1c3c424581a1051838001180470048080360c1800eb418000005802ec06010e00b4500100014a04003181c3810e4c407401c393721c012,0xe5c00c0084381020932c061cbac86018011858000185038c122098b0e0c030071c0438c00a47000c00000c03810e0c400250c0468c00000,0x185890c003010000d8001240491401101160e78045110c01700e01c93c0c10700022a701184005d14b1358262a12e4039e3cc008700040c6,0x8a580073c3458e0e016010e0c19e46023440e00001048419c881c109002c6094230000011c901900c007060004e86340348a5c08000b060c,0xd81871a0048900016091610c12000008006780800ec0583240800988101072c787454478f162c1cb00602d1890e1c38c02c0103421c9ac,0x121e300240004402840160f0d10188040210110000123000000080000f0e2800e001000404000006c00700003801624f07002400c8658481,0xe846000f184a6030e7968ec06803c043bb24583960e9c00c0e00388183809a2c780810878f0a01183c60059080321000100003cb8822312,0x900048d030cb0062050871878083460420b0e322b00249807345a280433c00c43190800f106011831107425c181005a18740048010230096,0x90862970e481070058b1e00ec6170c243808e680010e1d280900c907502e29b241418010001ac8a1e209008400c120401b4c31281601c003,0x2c31d97002000000000008800382232068c001cb220438f0d0030387105c4071830f46240218712000460120b0004006810e4cf000000681,0x8a0cc0c065cb1658580092800001001c00712311012c045a124103831830407125a18b0285196011c00c0e840a118783814238b441284181,0x2d12202000170e78388000071e442000028d808000781a146006073d0c0460e30614001c39e0e78500182ca963c04000061c0174230f17,0x961c00b0e1c00700004c70e1c38717183a2011038725145972f189158c4e5928858107001c3a15c30000240008c2c7830c062e7800000188,0x4110800080180583008000056012c08021860000012003848804387001c380441c0872604b810084f0b0e583873c306894200007121c745,0x8804f0202303900e041238a4804319145962e000030e589808cb090790000808a00000421c01e0e00388600011e02080870000f070488000,0x10e28018000010200f161224187005d0872d143c4027cf300000383189c000000000000580000e016036c0c58c06300a35c68587101c187,0x21cb013c00480000c0070000043005cd9e0004b3006306000e000000314d03162d1848632345425cb83101dc898e6c3873c8cd9e4458a00,0x2ed8487002400c76301a3002d90940062452c25280031980900586074e8a3892658f01872e2968a0c3a036ec3870e083a124000017608921,0x903ac00003801916280060058334301800058389001c0000e613800024380000038020001000e8c10000c1380000038c00004000050f25,0x2c013b0071840700010800e064008800980262c0800e00000181d01988840818a016000000b8002000000f3400024b09c500600ac00025ac,0x1804000581c38c0401322007800c001cf080e2058060183c61201600261e3453cb808087190803c0c0168c05287001c0b002d8480281c600,0x303888c0018b18843801a0460312000010084603180c00800303968800000000098d180001e8a640002c1c00712b020112000082e00045,0x800001107221c4456910f00007858100e0396100161e466060716316000084008180810800ecf4508784130e18989023164806c0307,0xeb03a31225600880059858018070058a3b020c5801a011c700000003c48382045c48062000000f1c00100004000078182001d3000000b07,0x604a090ec40220f1670c1c5c00c00011273c1e2030478383191808012496164204b30000059e3c04380182c08700303838a2c0a10058480,0x20400000000012151802c58084009c0002c007030000c01120d100108cf3030001162c01180000048d181d0c31318007000098b1824000,0x128cb87120c28c0e4d10524840822c1c386180230000003801800983188838d0e0010c901c0800400387003062244043968c48b171230580,0x487105e22c0030b0b061c002040c60106503870001821001c09e3c78009360002c240111e2800900601c1801830000002c00b0e25607,0x72c024364400000305c70818240a2000042106022802439800008c00c1858b00913ca9e02044070e2c38b0f0c3c3180018c013c080,0x2a0d9e0630000306d283041c00b0e880003c84a070e1c0ac500002c00240131935609071c0050e1cb071802280001c00e0e480876c00007,0x2250978a1818c240001e0200007041dd800e59098001cb451c0420240596004c04aa10e006483d10a0730203894c361803c0000e00d8480,0x120c030000c09632240820e0458c2620021180000061205800000012000000b441d30788040038f140450000000011438704023810e04f21,0x78f0044003820c1e2c30e003800084621001c380422000700022a60009087001d607001c0130e24396600800042000450c001160e2c389,0x9811e2e0000c8a040000400389001d607590c380448401e100049a4e0219e3cb00070e1c0070000187020048c1204d01000e18c0116700,0x123801e0d103808678f073c0c08988843a718000890e000878a2d100240cc452e01083161c00700c0d805800b8c2d0c6070f141010f2000c,0x18383880e0c08000880070000388002400b2e009840078007005c3c6180400700243923c022803c0010000000008a1c000349c0801600000,0x40130f1c007281d0150119100723220c020001600040004236296360860000000001824000000000000e8380861c60016250000e00002,0x1831901071cf30361c4005804426608400c2e246160e48b10125c3810e1e307884c1820478d0c0204387008800c3c1c98000313b9001c20b,0x28c4a102044800e304a12c1c98788f09c50e04120010c3c600662800e4d180121c38c120838c184dc81029c3c412584a20078383268c981,0x6030100000a346220400c12040810604f1c001000c100000718605830004b002c20b070650380000c9078b180220ed83811a846010004098,0xe1c99e0318b03160cb0318200003c3a28702ecb000468007622400700004a3001d080068c0830e0130002000176098000020c4802600487,0x3c0d6001831809060039e102cf12103061e020008018c0682442e68e8d10b17161c1a18c316008a083870009187061cb870e04045005cb2c,0x181c0c7004908028011015805d81582c080020439e00580160e00380000d6070e0000c0030030001c90318090801001080024838c0058607,0x448300483a1000538107143a5001c93106080010e000800e1c88c9d14101008538000500200e006001800b800000000066004e2401616,0x4c1c4811a143808e1cb8000009801288a1e86107074d140820114b072648900000408700043803c011800059087001c1268e001260000000,0x3c1cc2300010c618040c500000078e000801884083880c3b0244a20d441cb0c0649c8c0e203899c0458812006081678181502c0174430101]
private def hashWord (w : W) : Nat :=
  let x := w.toNat % 4294967291
  ((x*x+1)*(x+17)) % 4294967291
private def field (t : Array Nat) (bits i : Nat) : Nat :=
  (t[i/64]?.getD 0 >>> ((i % 64)*bits)) % (2^bits)
def hint (ws : List W) : Nat :=
  let h := (ws.foldl (fun v w => v + hashWord w) 0) % 4294967291
  let b := h % 2745
  let s := (h / 2745 + field shiftTab 8 b) % 14272
  field probeTab 7 s
end Hints
end Signed3110

namespace Signed3110
open Signed2964

def cutRun (B : Nat → List W → Bool) : Nat → Nat → List W → Bool
  | 0,_,ws => ws == [goal]
  | k+1,e,ws => !(B e ws) && oneLayer e ws (cutRun B k)

theorem cutRun_complete (B : Nat → List W → Bool)
    (certified : ∀ n e (ws : List W), ws.Nodup → e + ws.length = n+1 →
      B e ws = true → ¬ live basicOps goal n ws.toFinset)
    (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    cutRun B n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [cutRun, singleton_list hn h]
  | succ k ih =>
    have unblocked : B extra ws = false := by
      cases htest : B extra ws with
      | false => rfl
      | true => exact (certified _ _ _ hn room htest h).elim
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rw [cutRun,unblocked]; simp [oneLayer,singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (cutRun B k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (cutRun B k) hop hk
          (fun hm => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm)))
          (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [cutRun,unblocked,Bool.not_false,Bool.true_and,oneLayer,Bool.or_eq_true,List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap,
          go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def allCutBad (B : Nat → List W → Bool) (k : ℕ) : List (ℕ × List W) → Prop
  | [] => True
  | (e,ws) :: xs => cutRun B k e ws = false ∧ allCutBad B k xs

theorem cutBad_at {B : Nat → List W → Bool} {e k : ℕ} {ws : List W} {xs : List (ℕ × List W)}
    (h : allCutBad B k xs) (hm : (e,ws) ∈ xs) : cutRun B k e ws = false := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    obtain ⟨j,ys⟩ := x
    rcases List.mem_cons.mp hm with eq | old
    · cases eq; exact h.1
    · exact ih h.2 old


theorem cutCertify {B : Nat → List W → Bool} {k e : ℕ} {ws : List W} (xs : List (ℕ × List W))
    (hex : oneLayer e ws (fun j ys => !xs.contains (j,ys)) = false)
    (hbad : allCutBad B k xs) : cutRun B (k+1) e ws = false := by
  cases hrun : cutRun B (k+1) e ws with
  | false => rfl
  | true =>
    have mono (j : ℕ) (ys : List W) (ok : cutRun B k j ys = true) :
        (!xs.contains (j,ys)) = true := by
      by_contra! hn
      have hm : (j,ys) ∈ xs := by simpa using hn
      have h := cutBad_at hbad hm
      simp_all
    have test : oneLayer e ws (fun j ys => !xs.contains (j,ys)) = true := by
      have step : oneLayer e ws (cutRun B k) = true := by
        change (!(B e ws) && oneLayer e ws (cutRun B k)) = true at hrun
        rw [Bool.and_eq_true] at hrun
        exact hrun.2
      simp only [oneLayer, Bool.or_eq_true, List.any_eq_true] at step ⊢
      rcases step with done | ⟨⟨a,b,r⟩,hm,hh⟩
      · exact .inl done
      · exact .inr ⟨(a,b,r),hm,dispatch_mono _ _ mono e a b r hh⟩
    exact Bool.noConfusion (hex.symm.trans test)

end Signed3110

namespace Signed3110

open Signed2964

private def apart (w : W) : Prop := w.getLsbD 33 ≠ w.getLsbD 259

private theorem apart_norm (w : W) : apart (norm w) ↔ apart w := by
  have hi : 33 < 2*m := by decide
  have hj : 259 < 2*m := by decide
  unfold Signed2964.norm apart
  split <;> simp [hi,hj]

private theorem apart_ops (a b z : W) (hz : z ∈ basicOps a b) (hd : apart z) :
    apart a ∨ apart b := by
  by_contra! eq
  simp only [apart,not_not] at eq
  have h₁ : 33 < 2*m := by decide
  have h₂ : 259 < 2*m := by decide
  simp [BitVec.getLsbD_eq_getElem h₁,BitVec.getLsbD_eq_getElem h₂] at eq
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    rw [apart_norm] at hd <;>
    simp [apart,h₁,h₂,eq.1,eq.2] at hd

theorem reject_swap (n : Nat) (ws : List W)
    (same : ws.all (fun w => w.getLsbD 33 == w.getLsbD 259) = true) :
    ¬ live basicOps goal n ws.toFinset := by
  intro live_wire
  have target : apart goal := by unfold apart; decide +kernel
  obtain ⟨w,hw,diff⟩ := live_separates apart target apart_ops live_wire
  exact diff (beq_iff_eq.mp (List.all_eq_true.mp same w (List.mem_toFinset.mp hw)))

theorem reject_symmetric_prefix (n : Nat) :
    ¬ live basicOps goal n t4.toFinset :=
  reject_swap n t4 (by decide +kernel)

end Signed3110

namespace Signed3110
open Signed2964
namespace Numeric
def blocker (e : Nat) (ws : List W) : Bool :=
  if e ≤ 1 then
    let i := Hints.hint ws
    Projection.probeBlocked e ws i
  else false
private def w0 : W := 0x0
private def w1 : W := 0x10800000842000427e400020000008217ff2000000400000000000000000000000000000000000001f800000000000001ffc000000000000
private def w2 : W := 0x82108fc1f087882104221104411144f83e013c178f0809e40000000000000000000001f0fc01e000000000000000007e1f801f01e7c00038
private def w3 : W := 0x104211088210912f008f078089f701e10042788790211ff400000000000000000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def w4 : W := 0x21ef00111f7b800423e40223dc22008213ef200224f7b120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def w5 : W := 0x23ff00001000000427e40227fc2200000100000000800000000000000000000000ffc0000000000001f80001ff00000000000000000000000
private def w6 : W := 0x410842000000001ffffff00200804004010001000000000000000000000000000000000000000007fffffc000000000000000000000000000
private def w7 : W := 0x410842220842244f7bef7002008041efbbef7bd80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def w8 : W := 0x580003ea8000706a500a65100005054d200053955000005c00000000000000003f0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8
private def w9 : W := 0x680d02f31c036040734060301400040e338c031064c0200800000000000000003f07c1ffffc1fe183ff83c1e0f000307ffffc1fe1ffc1c038
private def w10 : W := 0x780f03fb9e03f06e73ce67301c0705cf33ce739774e0307c00000000000000003f07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def w11 : W := 0x7c84207fc421020f790007b9104021efb8840007fe42220080000000000000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def w12 : W := 0x7def7bc01000400f7bef77bbddf77404010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def w13 : W := 0x7def7bffdf7bffe84208440001040108220842140000084000000000000000003ffffffffffffff8000000000000000000000000000000000
private def w14 : W := 0x1ce001c070000000000000000b540a07034000c165594052065c06008000000007fc007c1c0000000000000003ff83c1e0f000307ffffc1fe1ffc1c038
private def w15 : W := 0x5f0043f080000000000000002104221104411145785e015c179f0809e400000007c0007c000000000000000000000000000000007e1f801f01e7c00038
private def w16 : W := 0x80008400000420000021080040084020088220080004220020021112000000000000000000000000000000000000000000000000000000000000000000
private def w17 : W := 0x842084411000000000000000425e40227fc22008215f7200225fff1200000000000000000000000000000000001f80001ff00000001ffc000007ffc000
private def w18 : W := 0x1000208000000000000000001f009f0000008003e10042f8800000040000000000000000000000000000000007c007c000000000f800003e00000000000
private def w19 : W := 0x10842088420000000000000017bdf7b002008042f7ddf7bde80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def w20 : W := 0x2000410000104211000000001f009f0f808bff0000000000000000000000000000000000000000000000000007c007c3e000ffc00000000000000000000
private def w21 : W := 0x21084110840000000000000017bdf7bbfffefbfc04010001004080000800000000000000000000000000000007ffffffffffffff0000000000000000000
private def w22 : W := 0x35ac01ba0600000000000000129012a95000090e55400095a15000001c0000001fffc0ffc1c000000000000007fe07fffe0003c3fffe003fffff80001f8
private def w23 : W := 0x3dee01fe070000000000000016b5d6ab703c0b0ed755d6b5a375e0703c0000001fffc0ffc1c000000000000007fffffffe0f03c3fffffffffffffc1c1f8
private def w24 : W := 0x3e207de200000000000000001700970b808afb02e10042b883902117b40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def w25 : W := 0x3fff1000200000000000000017b9000bf9104022f7d8840003fe4222008000001fffc000000000000000000007fe0003fe000000fffe000001ff8000000
private def w26 : W := 0x3fff7dffff00000000000000108410884422088a1044108420010840000000001fffffffffc000000000000000000000000000000000000000000000000
private def w27 : W := 0x100200fc000000401000001001010001008083f000200000080080010f8000000000003f000000000000000000000000000000fc000000000000000003e00
private def w28 : W := 0x100a00fc40000042100002108105008502808bf200a00042280280211fa000000000003f000000000000000000000000000000fc000000000000000003e00
private def w29 : W := 0x20000008001003e0000001f8000000200007c020000000210000001f8100000000000000000000f80000003e000000000001f0000000000000000003e0000
private def w30 : W := 0x20080008401003e2000003f8800400a40207c822008000632002003f9120000000000000000000f80000003e000000000001f0000000000000000003e0000
private def w31 : W := 0x80000020004001004000004004010821100200804020882108480004040100000000000000000000000000000000000000000000000000000000000000000
private def w32 : W := 0x80000020004001084000084204052fe51002008040a29fff2848000404010000000000000000000000000000000001f800000000000001ffc000000000000
private def w33 : W := 0x801000208040010040000040041f08bf1002008043e18863f8c80004040100000000000000000000000000000007c007c000000000f800003e00000000000
private def w34 : W := 0x100000040008007e0f800000000010821108fc3f0f0000000000000000000000000000000000000f83e000000000000000001f0fc3c0000000000000000000
private def w35 : W := 0x100000040008027fff800100000052fe512affff2f0000100000000800000000000000000000000fffe000000000001f80001fffc3c0000000000000000000
private def w36 : W := 0x100200041008017e2f9000000001f08bf1f8fcbfff0000000000000000000000000000000000000f83e0000000007c007c3e1f0fffc0000000000000000000
private def w37 : W := 0x4108000efe2000042110002109120009f00008bbf00000042f88000211df400000000003ff80000000000000000000007c00000ffc00000003e00000003fc0
private def w38 : W := 0x8210000084411037b00003bde800006e40006ec220000077b200001bdd120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def w39 : W := 0x10820000208842010842000842244006fff00200804000077bfff8000404010000000000000000000000000000000001fffc000000000001fffffe000000000
private def w40 : W := 0x21040000411084037bdf801000400006fff006efbfdc000100010000800008000000000000000000ffffe00000000001fffc01ffffff0000000000000000000
private def w41 : W := 0x3406800003ba060000078000007060001ae000000d0c000000d7b00000005c000f81e00000ffc1c00001e000001e180007fc000003c30000003ffe0000001f8
private def w42 : W := 0x38070000001c0700190680380660400640e00024000c000718073001804008000f81e0000007c1c007c1e00fc1fe1801f83c000f00030001ffc1fe007c1c038
private def w43 : W := 0x3c07800003fe07001b07803a06f06006dee0002c0f0c00075af7b001a0507c000f81e00000ffc1c007c1e00fc1fe1801fffc000f03c30001fffffe007c1c1f8
private def w44 : W := 0x3e080000043f08002108803b0878800042200044111400076017c001b0809e400f8000000007c0000000000fc01e00000000000000000001f801f0007c00038
private def w45 : W := 0x3fbf8000820000037bdf803bdefde002084000010400000208421000000840000fffe00000000000ffffe00ffffff8000000000000000000000000000000000
private def w46 : W := 0x3fbf8000efffdf021084002084000004108004220888000410842001084000000fffe0003fffffc000000000000000000000000000000000000000000000000
private def w47 : W := 0x8010fa00fbc000104211008010813d009d0e808bee03a00002e80680011f600000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def w48 : W := 0x10021080208401123de000100f7800427a40227b8220080101f2002040f7120000000000000000000ffc000003fe00001f80001ff0000000007c0000003fc000
private def w49 : W := 0x200821004208042410842020042045defbdd002008043a0781fe8380004040100000000000000000000000000000007fffffc00000000f81e07fe0e000000000
private def w50 : W := 0x401042008410084f7def7000000001defbddeefbbeee800000000000000000000000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def w51 : W := 0x68006f00c038006d000070280000078c018cc40000c0b006000c0340000004001f001ff83c0f801ff0001e0f000001ffe07fffe0003c3f81e003e0fe180001c0
private def w52 : W := 0x70007000e000007e01c060300070040e700c06030000800701c00300400600001f001e003c00001ff07c1e0f001e0183ff83c1e0f0003001e07c00e01801c000
private def w53 : W := 0x78007f80e03c007f01e07038007807ce79cce60380e0b80701ee0360400706001f001ff83c0f801ff07c1e0f001e01ffffffffe0f03c3f81e07fe0fe1801c1c0
private def w54 : W := 0x7c0407a0f100020f4842003c021021de9000ee9104023a0780400068602220081f0001f83c000003f000000f0000007fe0003fe000000f81e000001e18000000
private def w55 : W := 0x7c1f7c000820000f7def703c0f787684208440001040100200840140000084001f07fe0000000003fffffe0f03fe1f8000000000000000000000000000000000
private def w56 : W := 0x7c1f7fa0ffbc0f782108400008400108410884422088a00401080200008400001f07fff83fff83fc000000000000000000000000000000000000000000000000
private def w57 : W := 0x80208001004010800200804010808800000000040101000802000400810808240000000000000000000000000000000000000000000000000000000000000000
private def w58 : W := 0x84040021110002004802004402002010800008900402020880000008a02020080000000000000000000000000000000000000000000000000000000000000000
private def w59 : W := 0x843f8000080000007e0f80441f80f800000000001000000000000000000080000007e000000000000f83e00003e01e0000000000000000000000000000000000
private def w60 : W := 0x843f80211fc01f802008000008000000000000402008000000000000008000000007e00003f003e0000000000000000000000000000000000000000000000000
private def w61 : W := 0x100400042004220000000008020010020002010000110041004010811020009400000000000000000000000000000000000000000000000000000000000000000
private def w62 : W := 0x1080007e20100000100000088000001f00000f80004003e100000007900002000000001f800000000000000000000007c00003e0000000f800000001e00000000
private def w63 : W := 0x108400f42003a200100001088000103a001a0d00000d03410000d085100000540000001f8000f8000000000000000007c007c3e00003c0f800003e01e000001c0
private def w64 : W := 0x108400fc2003e200100201088200903e009e0f00080f03c10042f087102010740000001f8000f8000000000000000007c007c3e00003c0f800003e01e000001c0
private def w65 : W := 0x108410c00082000010421108821091280008040001040100000040040000084000000000000000000000000000000000000000000000000000000000000000000
private def w66 : W := 0x108410de20bee200000000088210912000000000000003e10042f88790211ff40000001f803ff800000000000000000000000000000000f800003e01e00003fc0
private def w67 : W := 0x108410ee20df6200104211088210912000000f808b7f00000000000790211bf40000001f803ff8000000000000000000000003e000ffc00000000001e00003fc0
private def w68 : W := 0x108410f620f7a200100011088000113b001b0d8003dd03610000d88590000ed40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def w69 : W := 0x108410fe20ffe2000000000000000010001008000208020000008000000000000000001f803ff8000000000000000000000000000000000000000000000000000
private def w70 : W := 0x108410fe20ffe200104211088210913f009f0f808bff03e10042f88790211ff40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def w71 : W := 0x18060804300423080020080c030818820002010040111041806010c11830809640000000000000000000000000000000000000000000000000000000000000000
private def w72 : W := 0x18c0407e311000201480200cc020021f08000f89004023e1880000079a0202008000001f800000000000000000000007c00003e0000000f800000001e00000000
private def w73 : W := 0x18c7f8c00082000017e2f90cc3f89fa80008040001040100000040040000084000007e000000000000f83e00003e01e0000000000000000000000000000000000
private def w74 : W := 0x18c7f8fe31ffe3f802008000008000100010080402088200000080000008000000007e1f803ff83e0000000000000000000000000000000000000000000000000
private def w75 : W := 0x2008000040000400002100103f080000004000004400000207e0000021f080000000000000000000000000000fc00000000000000000000001f80000007c00000
private def w76 : W := 0x210000084200000020840011042100042100022110000082108400022442200000000000000000000000000000000000000000000000000000000000000000000
private def w77 : W := 0x2108010042000401201d00113c0700002740002034000002179c000025c0600000000000000000000007c0000fc1e00001f800000f00000001ffc000007c1c000
private def w78 : W := 0x2108010842004401201f00113e07800427c402203c02008217de200225e0702000000000000000000007c0000fc1e00001f800000f00000001ffc000007c1c000
private def w79 : W := 0x210821000000000023ff00113fff800002000000000000000208000000000000000000000000000000ffc0000fffe000000000000000000000000000000000000
private def w80 : W := 0x210821004200041123bd00113def0000276000277400000217bd000025dee000000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def w81 : W := 0x2108210842084411000000112fff8000000000000000008216ff2002257ff1200000000000000000000000000fffe000000000000000000001ffc000007ffc000
private def w82 : W := 0x210821084208441102100000208400000400000420000000041000000108400000000000000000000000000000000000000000000000000000000000000000000
private def w83 : W := 0x210821084208441122f7001137bd800000000225fc2200000000000225fbf120000000000000000000ffc0000fffe00000000001ff00000000000000007ffc000
private def w84 : W := 0x210821084208441123ff00113fff800427e40227fc22008217ff200225fff120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def w85 : W := 0x2108310a42fc441123ff10113fff810527e502a7fff200a217ff2802a5ffffa000000000003f000000ffc0000fffe00001f80001fffc000001ffc000007fffe00
private def w86 : W := 0x280a080050040508002108143f080880004000004410100287e0004029f080824000000000000000000000000fc00000000000000000000001f80000007c00000
private def w87 : W := 0x2940400a531000202484201544210205290002a9104020a298840002ae42220080000000000000000000000000000000000000000000000000000000000000000
private def w88 : W := 0x294bf9000080000027fff8157fff8f800200000001000000020800000000080000007e000000000000fffe000fffe1e0000000000000000000000000000000000
private def w89 : W := 0x294bf90a53fc45f902108000208400000400000422008000041000000108400000007e00003f003e0000000000000000000000000000000000000000000000000
private def w90 : W := 0x318c31fe62ffe61133ff1119bfff913f27ff0fa7ffff03e317fff887b5fffff40000001f803ff80000ffc0000fffe007c1ffc3e1ffffc0f801fffe01e07ffffc0
private def w91 : W := 0x40100000800008000000002008002002104220000000005f87e017c000000000000000000000000000000000000000000000000000000007e1f801f0000000000
private def w92 : W := 0x4200001084000000400000220000001ff9000000000003fff88400000000000000000000000000000000000000000007fe000000000000fffe000000000000000
private def w93 : W := 0x42100200840008024008022208022040f740e0000000001e779c073000000000000000000000000000000000000000003ff83c0000000007ffffc1fe000000000
private def w94 : W := 0x4210021084008802400002220000205ad01ae0000000035d6000d7b00000000000000000000000000000000000000007fe07fc00000000fffe003ffe000000000
private def w95 : W := 0x4210021084008802400802220802205ef7dee000000003df77def7b00000000000000000000000000000000000000007fffffc00000000fffffffffe000000000
private def w96 : W := 0x421082000000000041084222084224484208400000000108220842100000000000000000000000000000000000000000000000000000000000000000000000000
private def w97 : W := 0x42108200840008424108422208422440ff60f0020000401effbd077800040001000000000000000000000000000000003ff83c0000000007ffffc1fe000000000
private def w98 : W := 0x421082108420884200000000000000108410800000000210441084200000000000000000000000000000000000000000000000000000000000000000000000000
private def w99 : W := 0x4210821084208842000000220842244000000000000003fbfefffef8000404010000000000000000000000000000000000000000000000fffffffffe000000000
private def w100 : W := 0x4210821084208842400042220000245bd81bf0000080437de800dff80000040100000000000000000000000000000007fe07fc00000000fffe003ffe000000000
private def w101 : W := 0x4210821084208842410842220842245ffffff002008043fffffffff80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def w102 : W := 0x529402d4a402aa020000002a8000306000000000000003596000d6b5100000543fff81ffffc0ffc1c000001ff0001e1800000000000000fffe003fffff80001f8
private def w103 : W := 0x529492fea4ffea42514a532a8a52b57fffffff828bff43ffffffffff90251ff50000001f803ff8000000000000000007ffffffe000ffc0ffffffffffe00003fc0
private def w104 : W := 0x63180300c6000c03000000332c072040000000000000001a769c0630254060003fff81e07fc007c1c000001fffc1fe180000000000000007ffffc1fe1ffc1c038
private def w105 : W := 0x6318a318c628cc5363ff42333fffa45ffffff227fca243fffffffffa25fff521000000000000000000ffc0000fffe007fffffc01ff0000fffffffffe007ffc000
private def w106 : W := 0x739c03dce602ee030000003bae07b06000000000000003db76def6b7356070743fff81ffffc0ffc1c000001fffc1fe1800000000000000fffffffffffffc1c1f8
private def w107 : W := 0x781e0804f0042f080000003c2f083880000000000000005b86e016c1397080967e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def w108 : W := 0x7bc0405ef71000200000003fc421020000000000000003fbf8840007be422200bff0001fffc000000000001ff000000000000000000000fffe000001ff8000000
private def w109 : W := 0x7bdefbc0008200000000003fefffbfe0000000000000010822084214000008403fffffe0000000000000001ffffffff8000000000000000000000000000000000
private def w110 : W := 0x7bdefbdef7beef7b0000000020840000000000000000021044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def w111 : W := 0x8020000100001000082108c0100040021042211044111404010001004080000800000000000000000000000000000000000000000000000000000000000000000
private def w112 : W := 0x8400002108000000fc8420400000001ff9000ff910402004000000004000000000000000000000003f00000000000007fe0003fe0000000000000000000000000
private def w113 : W := 0x8420040108001004e81d06c010004000f740e07034000c04010001004080000800000000000000003f07c1e0000000003ff83c1e0f00030000000000000000000
private def w114 : W := 0x8420042108011004d80007c00000401ad01aed50000d0c04000001004000000800000000000000003f0001e000000007fe07fffe0003c30000000000000000000
private def w115 : W := 0x8420042108011004f81f07c01000401ef7deef703c0f0c04010001004080000800000000000000003f07c1e000000007fffffffe0f03c30000000000000000000
private def w116 : W := 0x8421040000000000ffffffc0100040084208440001040000000000000000000000000000000000003fffffe000000000000000000000000000000000000000000
private def w117 : W := 0x8421040108001084efbdeec010004000ff60f07f7400fc04010001004080000800000000000000003fffffe0000000003ff83c1fff003f0000000000000000000
private def w118 : W := 0x842104210841108482108400000000108410884422088800000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def w119 : W := 0x8421042108411084bef7bdc01000400000000ffdff7fbc00000000004080000800000000000000003fffffe000000000000003ffffffff0000000000000000000
private def w120 : W := 0x8421042108411084dc00ffc00000401bd81bfdd803ddfc04000001004000000800000000000000003f003fe000000007fe07fffe00ffff0000000000000000000
private def w121 : W := 0x8421042108411084ffffffc01000401ffffffffffffffc04010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def w122 : W := 0x8421142308fd1084ffffffc01010411ffffffffffffffc2401000900c0810f8800000000003f00003fffffe000000007ffffffffffffff0000000000000003e00
private def w123 : W := 0x94a404e528033204980005c88000502000000d50000d0c00000000055000005c3fff81ffffc0ffc1ff0001fff0001e18000003fe0003c30000000001ff80001f8
private def w124 : W := 0x94a514ff28fff284ffffffc89210d13fffffffffffffffe50142f987d0a11ffc0000001f803ff8003fffffe000000007fffffffffffffff800003e01e00003fc0
private def w125 : W := 0xa52805014a001405a81504d1340540000000007034000c000000000065c060083fff81e07fc007c1ff07c1ffffc1fe180000001e0f000300000000001ffc1c038
private def w126 : W := 0xa52925294a495495ffffffd13fffc01ffffffffffffffc8617ff210265fff12800000000000000003fffffe00fffe007ffffffffffffff0001ffc000007ffc000
private def w127 : W := 0xb5ac05ed6a037605b81705d9b605d02000000f703c0f0c000000000775e0707c3fff81ffffc0ffc1ff07c1ffffc1fe18000003fe0f03c30000000001fffc1c1f8
private def w128 : W := 0xb82e080570043708082108dc3708588000000110441114000000000179f0809e7e0f80007c0007c00000001f0fc01e000000000000000000000000001e7c00038
private def w129 : W := 0xbdc0406f7b100020bc84205dc421020000000ff91040200000000007fe422200bff0001fffc000003f00001ff0000000000003fe0000000000000001ff8000000
private def w130 : W := 0xbdef7dc000820000bef7bdddf7bddba0000004000104000000000004000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def w131 : W := 0xbdef7def7bdf77bd8210840020840000000008442208880000000000010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def w132 : W := 0xc63006018c001806c80006e200006040d000e05000000c1c60000730400000083fff81e07fc007c1ff0001fff0001e183e003c1e00000307fe0001fe1f8000038
private def w133 : W := 0xc63186318c6198c6ffffffe21842645ffffffffffffffffffffffff84084040900000000000000003fffffe000000007fffffffffffffffffffffffe000000000
private def w134 : W := 0xd0340005a0003a00080000e800007002100221100001045d000017815000001c3e0f80007c0007c00000001f00001e000000000000000007e00001f01e0000038
private def w135 : W := 0xd6800075ac000000d800006a8000001ad0000d500000035d60000005500000003ff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def w136 : W := 0xd6b406c000020000d80007ea80007068400844000004010820004214000000403fff81e0000000003f0001fff0001e18000000000000000000000000000000000
private def w137 : W := 0xd6b406f5ac03ba0680000400000000108010884000080a1040008420000000003fff81ffffc0ffc1c000000000000000000000000000000000000000000000000
private def w138 : W := 0xd6b406f5ac03ba06d80007ea8000707ad01aed50000d0f5d6000d7b55000005c3fff81ffffc0ffc1ff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8
private def w139 : W := 0xd6b416ffacfffa06d84217ea8210f17fd09fefd08bff0ffd6042ffb7d0211ffc3fff81ffffffffc1ff0001fff0001e1ffe07fffe00ffc3fffe003fffff8003ff8
private def w140 : W := 0xd6b486f5ac23ba46d90847ea8842747ffffffd52008d4ffffffffffd5004045d3fff81ffffc0ffc1ff0001fff0001e1ffffffffe0003c3ffffffffffff80001f8
private def w141 : W := 0xd6b506f5ac43ba86ffffffea9000707fffffffffffffff5d6100d7b55080005c3fff81ffffc0ffc1fffffffff0001e1ffffffffffffffffffe003fffff80001f8
private def w142 : W := 0xd8360805b0043b08080008ec00007882100221100011145d800017c15800009e7e0f80007c0007c00000001f00001e000000000000000007e00001f01e0000038
private def w143 : W := 0xdec04077bd100020dc00206ec000021bd8000dd80040237de8000005da000200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def w144 : W := 0xdef7dec000820000dc00ffeec0007fe8400844000104010820004214000008403fffffe0000000003f003ffff0001ff8000000000000000000000000000000000
private def w145 : W := 0xdef7def7bdf7bbee80008400000000108010884002088a1040008420000000003fffffffffffffffc000000000000000000000000000000000000000000000000
private def w146 : W := 0xe0380001c0001c00080100f03c006000104020100400041e0780070061c000083e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def w147 : W := 0xe7000001ce000000e804007304010000f10000701000001e70840000644020003ff000007fc000003f00001ff00000003e00001e00000007fe0000001f8000000
private def w148 : W := 0xe738070000000000e81d06f33c076040420040000000000822080210000000003fff81e0000000003f07c1ffffc1fe18000000000000000000000000000000000
private def w149 : W := 0xe7380701ce001c078010040020040000840080402000081044100420010040003fff81e07fc007c1c000000000000000000000000000000000000000000000000
private def w150 : W := 0xe7380701ce001c07e81d06f33c076040f740e07034000c1e779c073065c060083fff81e07fc007c1ff07c1ffffc1fe183ff83c1e0f000307ffffc1fe1ffc1c038
private def w151 : W := 0xe7382709ce085c17ebff06f33fffe044f7e4e277fc220c9e77ff273265fff1283fff81e07fc007c1ffffc1fffffffe183ff83c1fff000307ffffc1fe1ffffc038
private def w152 : W := 0xe7388711ce209c47e91d46f33c47645ffffff07234804ffffffffff865c464093fff81e07fc007c1ff07c1ffffc1fe1ffffffc1e0f0003fffffffffe1ffc1c038
private def w153 : W := 0xe7390721ce411c87fffffff33c07605ffffffffffffffc1e779c073065c060083fff81e07fc007c1ffffffffffc1fe1fffffffffffffff07ffffc1fe1ffc1c038
private def w154 : W := 0xe83a0801d0001d08082108f43d086880104020104400141e87a0074069d0800a7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def w155 : W := 0xef404001df000020ec84207744210200f90000791000201ef88400006e422000bff000007fc000003f00001ff00000003e00001e00000007fe0000001f8000000
private def w156 : W := 0xef7bef0000000000efbdeef77def6ec0420040000000000822080210000000003fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def w157 : W := 0xef7bef01df001dff8210840020840000840080442000881044100420010840003fffffe07fc007ffc000000000000000000000000000000000000000000000000
private def w158 : W := 0xf03c0005e0003e00080100f83e007002104221100401045f07c0178171e0001c3e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def w159 : W := 0xf780007dee000000f804007b8401001ef1000f70100003df70840007744020003ff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def w160 : W := 0xf7bc07c000020000f81f07fbbe07f068420844000004010822084214000000403fff81e0000000003f07c1ffffc1fe18000000000000000000000000000000000
private def w161 : W := 0xf7bc07fdee03fe0780100400200400108410884020080a1044108420010040003fff81ffffc0ffc1c000000000000000000000000000000000000000000000000
private def w162 : W := 0xf7bc07fdee03fe07f81f07fbbe07f07ef7deef703c0f0fdf77def7b775e0707c3fff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def w163 : W := 0xf7bc17ffeefffe07f85f17fbbe17f17ff7dfeff0bfff0fff77deffb7f5e17ffc3fff81ffffffffc1ff07c1ffffc1fe1ffffffffe0fffc3fffffffffffffc1fff8
private def w164 : W := 0xf7bc27fdee0bfe17fbff07fbbffff07ef7feef77fc2f0fdf77fff7b775fff17c3fff81ffffc0ffc1ffffc1fffffffe1fffffffffff03c3fffffffffffffffc1f8
private def w165 : W := 0xf7bc87fdee23fe47f91f47fbbe47f47fffffff723c8f4fffffffffff75e4747d3fff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def w166 : W := 0xf7bd07fdee43fe87fffffffbbe07f07fffffffffffffffdf77def7b775e0707c3fff81ffffc0ffc1ffffffffffc1fe1ffffffffffffffffffffffffffffc1c1f8
private def w167 : W := 0xf8000005f00000000800007c04000002100001100000005f80800001784000003e0000007c0000000000001f000000000000000000000007e00000001e0000000
private def w168 : W := 0xf83e080000000000082108fc3f087880000000000000000802000200000000003e0f8000000000000000001f0fc01e00000000000000000000000000000000000
private def w169 : W := 0xf83e0805f0043f080000000020000000000000000000001004000400010000003e0f80007c0007c00000000000000000000000000000000000000000000000000
private def w170 : W := 0xf83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def w171 : W := 0xf83e1807f0fc3f08086118fc3f18798310432190c7f1147f87e01fc1f9f18f9e7e0f80007c3f07c00000001f0fc01e000000000000fc0007e1f801f01e7c03e38
private def w172 : W := 0xf8be18fff0ffff08186319fcbf18f9bf10df2f90cfff17ff87e2ffc7f9f19ffe7e0f801ffc3fffc00000001f0fc01e07c007c3e000ffc0ffe1f83ff1fe7c03ff8
private def w173 : W := 0xf93e290df20c7f192bff08fd3ffff88637e62337fc3314df97ff37c37dfff1be7e0f80007c0007c000ffc01f0ffffe0001f80001ff000007e1ffc1f01e7ffc038
private def w174 : W := 0xfa3e8a15f424bf4a49294afe3f4a7cdffffff112449157fffffffff979f4849f7e0f80007c0007c00000001f0fc01e07fffffc00000000fffffffffe1e7c00038
private def w175 : W := 0xfc3f0c25f8453f8cfffffffc3f08789ffffffffffffffc5f87e017c179f0809e7e0f80007c0007c03fffffff0fc01e07ffffffffffffff07e1f801f01e7c00038
private def w176 : W := 0xfebe0ef5fc07bf0ed8210ffebf0878fad05aed50441d1f5fe7e0d7f579f080de7fff81ffffc0ffc1ff0001ffffc01e1ffe07fffe0003c3fffff83ffffffc001f8
private def w177 : W := 0xff3e0f05fe043f0fe83d0eff3f0f78c2f742e17074111c5ff7fc17f17df0e09e7fff81e07fc007c1ff07c1ffffc1fe183ff83c1e0f000307ffffc1fe1ffc1c038
private def w178 : W := 0xffbe0ffdfe07ff0ff83f0fffbf0ff8fef7deef707c1f1fdff7fef7f77df0f0fe7fff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def w179 : W := 0xffc0404000000000fc84207fc4210208400004000000010820000004000000003ff00000000000003f00001ff0000000000000000000000000000000000000000
private def w180 : W := 0xffc0407fff1000208000000000000010800008400000021040000000000000003ff0001fffc000000000000000000000000000000000000000000000000000000
private def w181 : W := 0xffc0407fff100020fc84207fc421021ff9000ff9104023fff8840007fe422200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def w182 : W := 0xffc0507ffffc0020fcc4307fc431031ff9010ff993f023fff8840807fe432f80bff0001fffff00003f00001ff0000007fe0003fe00fc00fffe000001ff8003e00
private def w183 : W := 0xffc450ffffffe220fcc6317fc631933ff99f0ff99bff23fff8c6f887fe633ff4bff0001ffffff8003f00001ff0000007fe07c3fe00ffc0fffe003e01ff8003fc0
private def w184 : W := 0xffc8617fff184431ffff207fffff821fffe40ffffc6223ffffff2007fffff320bff0001fffc000003fffc01fffffe007fff803ffff0000ffffffc001fffffc000
private def w185 : W := 0xffd0c27fff308862fd8c627fcc63265ffffffffb10c063fffffffffffe462601bff0001fffc000003f00001ff0000007fffffffe000000ffffffffffff8000000
private def w186 : W := 0xffe1447fff5110a4ffffffffd421421ffffffffffffffffff9840107fec22208bff0001fffc000003ffffffff0000007fffffffffffffffffe000001ff8000000
private def w187 : W := 0xfff446ffff13ba26fc8427ffc421727ff91aeff9104d2ffff884d7b7fe42225cbfff81ffffc0ffc1ff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8
private def w188 : W := 0xfff8477fff101c27fc9d26fffc27625fff40eff934402fffff9c0737ffc26208bfff81ffffc007c1ff07c1ffffc1fe1ffff83ffe0f0003ffffffc1fffffc1c038
private def w189 : W := 0xfffc47ffff13fe27fc9f27fffe27f27fffdeeff93c4f2fffffdef7b7ffe2727cbfff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def w190 : W := 0xfffe487fff143f28fca528ffff297a9ff9422ff9545137ffffe417c7fff2a29effff801fffc007c03f00001fffc01e07fe0003fe000000fffff801f1fffc00038
private def w191 : W := 0xffffffc0008200008210840020840000000000000000000000000000000000003fffffe0000000000000000000000000000000000000000000000000000000000
private def w192 : W := 0xffffffc000820000ffffffffffffffe8420844000104010822084214000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def w193 : W := 0xffffffc1ce821c07ffffffffffffffe8f748e47035040d1e779c473465c068483fffffe07fc007c1fffffffffffffff83ff83c1e0f000307ffffc1fe1ffc1c038
private def w194 : W := 0xffffffc5f0863f08ffffffffffffffea524a65104515155fa7e857d579f088de7fffffe07c0007c03ffffffffffffff80000000000000007e1f801f01e7c00038
private def w195 : W := 0xffffffc8428a4411ffffffffffffffec67ec4627fd26018a37ff621625fff9603fffffe0000000003ffffffffffffff801f80001ff00000001ffc000007ffc000
private def w196 : W := 0xffffffd084a28842fffffffffffffffffffff402018443fffffffffc00040c413fffffe0000000003ffffffffffffffffffffc00000000fffffffffe000000000
private def w197 : W := 0xffffffe108c31084fffffffffffffffffffffffffffffd0c23084314408008483fffffe0000000003fffffffffffffffffffffffffffff0000000000000000000
private def w198 : W := 0xfffffff5ac83ba06fffffffffffffffad21aed50010d0f5d6208d7b55000085c3fffffffffc0ffc1fffffffffffffffffe07fffe0003c3fffe003fffff80001f8
private def w199 : W := 0xfffffffdee83fe07fffffffffffffffef7deef703d0f0fdf77def7b775e0787c3fffffffffc0ffc1fffffffffffffffffffffffe0f03c3fffffffffffffc1c1f8
private def w200 : W := 0xfffffffe20ffe200ffffffffffffffff429f4f808bff03e9224afa9790211ff43fffffff803ff8003fffffffffffffffc007c3e000ffc0f800003e01e00003fc0
private def w201 : W := 0xffffffffff920020fffffffffffffffffb084ff9114423fffa8c4217fe422a40bfffffffffc000003ffffffffffffffffe0003fe000000fffe000001ff8000000
private def w202 : W := 0xffffffffffffffff82108400208400108410884422088a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def w203 : W := 0xffffffffffffffff8250940020940111841188c4a3f88a3044108c2081094f803fffffffffffffffc0000000000000000000000000fc000000000000000003e00
private def w204 : W := 0xffffffffffffffff8a318cfc3f8c78929452a95466199e5fc7f097e179f8c09e7fffffffffffffffc000001f0fc01e000000000000000007e1f801f01e7c00038
private def w205 : W := 0xffffffffffffffff92529508a294913f849f8fc4abff8bf14452fca791295ff43fffffffffffffffc000000000000007c007c3e000ffc0f800003e01e00003fc0
private def w206 : W := 0xffffffffffffffffa3ff84113fff8014a7f48a67fe2a8a9257ffa42225fff1203fffffffffffffffc0ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def w207 : W := 0xffffffffffffffffc318c62228c6245ffffff8462288cbfffffffff8010c44013fffffffffffffffc000000000000007fffffc00000000fffffffffe000000000
private def w208 : W := 0xffffffffffffffffda1087eaa084707ad41aed54220d8f5d6410d7b55108405c3fffffffffffffffff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8
private def w209 : W := 0xffffffffffffffffea1d86f33c876050f750e87436088e1e779c873065c860083fffffffffffffffff07c1ffffc1fe183ff83c1e0f000307ffffc1fe1ffc1c038
private def w210 : W := 0xfffffffffffffffffa1f87fbbe87f07ef7deef743e0f8fdf77def7b775e8707c3fffffffffffffffff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def w211 : W := 0xfffffffffffffffffe94a47fe4a5021ffd108ffd3248abfffc948427ff4a6200bfffffffffffffffff00001ff0000007fe0003fe000000fffe000001ff8000000
private def w212 : W := 0xffffffffffffffffffffffc03084401ffffffffffffffe1445108520418840083fffffffffffffffffffffe000000007ffffffffffffff0000000000000000000
private def w213 : W := 0xfffffffffffffffffffffffffffffff8c618cc44230c8b186618c634010848403ffffffffffffffffffffffffffffff8000000000000000000000000000000000
private def sr0 : List W := [w0,w70,w150,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r0 : cutRun blocker 10 0 sr0 = false := by decide +kernel
private def sr1 : List W := [w0,w84,w138,w70,w101,w121,w162,w170,w181,w192,w202]
private theorem r1 : cutRun blocker 10 0 sr1 = false := by decide +kernel
private def sr2 : List W := [w0,w138,w162,w70,w84,w101,w121,w170,w181,w192,w202]
private theorem r2 : cutRun blocker 10 0 sr2 = false := by decide +kernel
private def sr3 : List W := [w0,w150,w162,w70,w84,w101,w121,w170,w181,w192,w202]
private theorem r3 : cutRun blocker 10 0 sr3 = false := by decide +kernel
private def sr4 : List W := [w1,w84,w101,w70,w121,w138,w162,w170,w181,w192,w202]
private theorem r4 : cutRun blocker 10 0 sr4 = false := by decide +kernel
private def sr5 : List W := [w1,w84,w101,w70,w121,w150,w162,w170,w181,w192,w202]
private theorem r5 : cutRun blocker 10 0 sr5 = false := by decide +kernel
private def sr6 : List W := [w2,w170,w202,w70,w84,w101,w121,w138,w162,w181,w192]
private theorem r6 : cutRun blocker 10 0 sr6 = false := by decide +kernel
private def sr7 : List W := [w2,w170,w202,w70,w84,w101,w121,w150,w162,w181,w192]
private theorem r7 : cutRun blocker 10 0 sr7 = false := by decide +kernel
private def sr8 : List W := [w3,w70,w202,w84,w101,w121,w138,w162,w170,w181,w192]
private theorem r8 : cutRun blocker 10 0 sr8 = false := by decide +kernel
private def sr9 : List W := [w3,w70,w202,w84,w101,w121,w150,w162,w170,w181,w192]
private theorem r9 : cutRun blocker 10 0 sr9 = false := by decide +kernel
private def sr10 : List W := [w4,w84,w202,w70,w101,w121,w138,w162,w170,w181,w192]
private theorem r10 : cutRun blocker 10 0 sr10 = false := by decide +kernel
private def sr11 : List W := [w4,w84,w202,w70,w101,w121,w150,w162,w170,w181,w192]
private theorem r11 : cutRun blocker 10 0 sr11 = false := by decide +kernel
private def sr12 : List W := [w5,w84,w121,w70,w101,w138,w162,w170,w181,w192,w202]
private theorem r12 : cutRun blocker 10 0 sr12 = false := by decide +kernel
private def sr13 : List W := [w5,w84,w121,w70,w101,w150,w162,w170,w181,w192,w202]
private theorem r13 : cutRun blocker 10 0 sr13 = false := by decide +kernel
private def sr14 : List W := [w6,w101,w121,w70,w84,w138,w162,w170,w181,w192,w202]
private theorem r14 : cutRun blocker 10 0 sr14 = false := by decide +kernel
private def sr15 : List W := [w6,w101,w121,w70,w84,w150,w162,w170,w181,w192,w202]
private theorem r15 : cutRun blocker 10 0 sr15 = false := by decide +kernel
private def sr16 : List W := [w7,w101,w202,w70,w84,w121,w138,w162,w170,w181,w192]
private theorem r16 : cutRun blocker 10 0 sr16 = false := by decide +kernel
private def sr17 : List W := [w7,w101,w202,w70,w84,w121,w150,w162,w170,w181,w192]
private theorem r17 : cutRun blocker 10 0 sr17 = false := by decide +kernel
private def sr18 : List W := [w8,w138,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r18 : cutRun blocker 10 0 sr18 = false := by decide +kernel
private def sr19 : List W := [w9,w150,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r19 : cutRun blocker 10 0 sr19 = false := by decide +kernel
private def sr20 : List W := [w10,w162,w202,w70,w84,w101,w121,w138,w170,w181,w192]
private theorem r20 : cutRun blocker 10 0 sr20 = false := by decide +kernel
private def sr21 : List W := [w10,w162,w202,w70,w84,w101,w121,w150,w170,w181,w192]
private theorem r21 : cutRun blocker 10 0 sr21 = false := by decide +kernel
private def sr22 : List W := [w11,w181,w202,w70,w84,w101,w121,w138,w162,w170,w192]
private theorem r22 : cutRun blocker 10 0 sr22 = false := by decide +kernel
private def sr23 : List W := [w11,w181,w202,w70,w84,w101,w121,w150,w162,w170,w192]
private theorem r23 : cutRun blocker 10 0 sr23 = false := by decide +kernel
private def sr24 : List W := [w12,w121,w202,w70,w84,w101,w138,w162,w170,w181,w192]
private theorem r24 : cutRun blocker 10 0 sr24 = false := by decide +kernel
private def sr25 : List W := [w12,w121,w202,w70,w84,w101,w150,w162,w170,w181,w192]
private theorem r25 : cutRun blocker 10 0 sr25 = false := by decide +kernel
private def sr26 : List W := [w13,w192,w202,w70,w84,w101,w121,w138,w162,w170,w181]
private theorem r26 : cutRun blocker 10 0 sr26 = false := by decide +kernel
private def sr27 : List W := [w13,w192,w202,w70,w84,w101,w121,w150,w162,w170,w181]
private theorem r27 : cutRun blocker 10 0 sr27 = false := by decide +kernel
private def sr28 : List W := [w14,w150,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r28 : cutRun blocker 10 0 sr28 = false := by decide +kernel
private def sr29 : List W := [w15,w170,w192,w70,w84,w101,w121,w138,w162,w181,w202]
private theorem r29 : cutRun blocker 10 0 sr29 = false := by decide +kernel
private def sr30 : List W := [w15,w170,w192,w70,w84,w101,w121,w150,w162,w181,w202]
private theorem r30 : cutRun blocker 10 0 sr30 = false := by decide +kernel
private def sr31 : List W := [w16,w70,w84,w101,w121,w138,w162,w170,w181,w192,w202]
private theorem r31 : cutRun blocker 10 0 sr31 = false := by decide +kernel
private def sr32 : List W := [w16,w70,w84,w101,w121,w150,w162,w170,w181,w192,w202]
private theorem r32 : cutRun blocker 10 0 sr32 = false := by decide +kernel
private def sr33 : List W := [w17,w84,w192,w70,w101,w121,w138,w162,w170,w181,w202]
private theorem r33 : cutRun blocker 10 0 sr33 = false := by decide +kernel
private def sr34 : List W := [w17,w84,w192,w70,w101,w121,w150,w162,w170,w181,w202]
private theorem r34 : cutRun blocker 10 0 sr34 = false := by decide +kernel
private def sr35 : List W := [w18,w70,w101,w84,w121,w138,w162,w170,w181,w192,w202]
private theorem r35 : cutRun blocker 10 0 sr35 = false := by decide +kernel
private def sr36 : List W := [w18,w70,w101,w84,w121,w150,w162,w170,w181,w192,w202]
private theorem r36 : cutRun blocker 10 0 sr36 = false := by decide +kernel
private def sr37 : List W := [w19,w101,w192,w70,w84,w121,w138,w162,w170,w181,w202]
private theorem r37 : cutRun blocker 10 0 sr37 = false := by decide +kernel
private def sr38 : List W := [w19,w101,w192,w70,w84,w121,w150,w162,w170,w181,w202]
private theorem r38 : cutRun blocker 10 0 sr38 = false := by decide +kernel
private def sr39 : List W := [w20,w70,w121,w84,w101,w138,w162,w170,w181,w192,w202]
private theorem r39 : cutRun blocker 10 0 sr39 = false := by decide +kernel
private def sr40 : List W := [w20,w70,w121,w84,w101,w150,w162,w170,w181,w192,w202]
private theorem r40 : cutRun blocker 10 0 sr40 = false := by decide +kernel
private def sr41 : List W := [w21,w121,w192,w70,w84,w101,w138,w162,w170,w181,w202]
private theorem r41 : cutRun blocker 10 0 sr41 = false := by decide +kernel
private def sr42 : List W := [w21,w121,w192,w70,w84,w101,w150,w162,w170,w181,w202]
private theorem r42 : cutRun blocker 10 0 sr42 = false := by decide +kernel
private def sr43 : List W := [w22,w138,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r43 : cutRun blocker 10 0 sr43 = false := by decide +kernel
private def sr44 : List W := [w23,w162,w192,w70,w84,w101,w121,w138,w170,w181,w202]
private theorem r44 : cutRun blocker 10 0 sr44 = false := by decide +kernel
private def sr45 : List W := [w23,w162,w192,w70,w84,w101,w121,w150,w170,w181,w202]
private theorem r45 : cutRun blocker 10 0 sr45 = false := by decide +kernel
private def sr46 : List W := [w24,w70,w192,w84,w101,w121,w138,w162,w170,w181,w202]
private theorem r46 : cutRun blocker 10 0 sr46 = false := by decide +kernel
private def sr47 : List W := [w24,w70,w192,w84,w101,w121,w150,w162,w170,w181,w202]
private theorem r47 : cutRun blocker 10 0 sr47 = false := by decide +kernel
private def sr48 : List W := [w25,w181,w192,w70,w84,w101,w121,w138,w162,w170,w202]
private theorem r48 : cutRun blocker 10 0 sr48 = false := by decide +kernel
private def sr49 : List W := [w25,w181,w192,w70,w84,w101,w121,w150,w162,w170,w202]
private theorem r49 : cutRun blocker 10 0 sr49 = false := by decide +kernel
private def sr50 : List W := [w26,w192,w202,w70,w84,w101,w121,w138,w162,w170,w181]
private theorem r50 : cutRun blocker 10 0 sr50 = false := by decide +kernel
private def sr51 : List W := [w26,w192,w202,w70,w84,w101,w121,w150,w162,w170,w181]
private theorem r51 : cutRun blocker 10 0 sr51 = false := by decide +kernel
private def sr52 : List W := [w27,w70,w162,w84,w101,w121,w138,w170,w181,w192,w202]
private theorem r52 : cutRun blocker 10 0 sr52 = false := by decide +kernel
private def sr53 : List W := [w27,w70,w162,w84,w101,w121,w150,w170,w181,w192,w202]
private theorem r53 : cutRun blocker 10 0 sr53 = false := by decide +kernel
private def sr54 : List W := [w28,w70,w138,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r54 : cutRun blocker 10 0 sr54 = false := by decide +kernel
private def sr55 : List W := [w29,w84,w162,w70,w101,w121,w138,w170,w181,w192,w202]
private theorem r55 : cutRun blocker 10 0 sr55 = false := by decide +kernel
private def sr56 : List W := [w29,w84,w162,w70,w101,w121,w150,w170,w181,w192,w202]
private theorem r56 : cutRun blocker 10 0 sr56 = false := by decide +kernel
private def sr57 : List W := [w30,w84,w150,w70,w101,w121,w162,w170,w181,w192,w202]
private theorem r57 : cutRun blocker 10 0 sr57 = false := by decide +kernel
private def sr58 : List W := [w31,w101,w162,w70,w84,w121,w138,w170,w181,w192,w202]
private theorem r58 : cutRun blocker 10 0 sr58 = false := by decide +kernel
private def sr59 : List W := [w31,w101,w162,w70,w84,w121,w150,w170,w181,w192,w202]
private theorem r59 : cutRun blocker 10 0 sr59 = false := by decide +kernel
private def sr60 : List W := [w32,w101,w138,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r60 : cutRun blocker 10 0 sr60 = false := by decide +kernel
private def sr61 : List W := [w33,w101,w150,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r61 : cutRun blocker 10 0 sr61 = false := by decide +kernel
private def sr62 : List W := [w34,w121,w162,w70,w84,w101,w138,w170,w181,w192,w202]
private theorem r62 : cutRun blocker 10 0 sr62 = false := by decide +kernel
private def sr63 : List W := [w34,w121,w162,w70,w84,w101,w150,w170,w181,w192,w202]
private theorem r63 : cutRun blocker 10 0 sr63 = false := by decide +kernel
private def sr64 : List W := [w35,w121,w138,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r64 : cutRun blocker 10 0 sr64 = false := by decide +kernel
private def sr65 : List W := [w36,w121,w150,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r65 : cutRun blocker 10 0 sr65 = false := by decide +kernel
private def sr66 : List W := [w37,w70,w181,w84,w101,w121,w138,w162,w170,w192,w202]
private theorem r66 : cutRun blocker 10 0 sr66 = false := by decide +kernel
private def sr67 : List W := [w37,w70,w181,w84,w101,w121,w150,w162,w170,w192,w202]
private theorem r67 : cutRun blocker 10 0 sr67 = false := by decide +kernel
private def sr68 : List W := [w38,w84,w181,w70,w101,w121,w138,w162,w170,w192,w202]
private theorem r68 : cutRun blocker 10 0 sr68 = false := by decide +kernel
private def sr69 : List W := [w38,w84,w181,w70,w101,w121,w150,w162,w170,w192,w202]
private theorem r69 : cutRun blocker 10 0 sr69 = false := by decide +kernel
private def sr70 : List W := [w39,w101,w181,w70,w84,w121,w138,w162,w170,w192,w202]
private theorem r70 : cutRun blocker 10 0 sr70 = false := by decide +kernel
private def sr71 : List W := [w39,w101,w181,w70,w84,w121,w150,w162,w170,w192,w202]
private theorem r71 : cutRun blocker 10 0 sr71 = false := by decide +kernel
private def sr72 : List W := [w40,w121,w181,w70,w84,w101,w138,w162,w170,w192,w202]
private theorem r72 : cutRun blocker 10 0 sr72 = false := by decide +kernel
private def sr73 : List W := [w40,w121,w181,w70,w84,w101,w150,w162,w170,w192,w202]
private theorem r73 : cutRun blocker 10 0 sr73 = false := by decide +kernel
private def sr74 : List W := [w41,w138,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r74 : cutRun blocker 10 0 sr74 = false := by decide +kernel
private def sr75 : List W := [w42,w150,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r75 : cutRun blocker 10 0 sr75 = false := by decide +kernel
private def sr76 : List W := [w43,w162,w181,w70,w84,w101,w121,w138,w170,w192,w202]
private theorem r76 : cutRun blocker 10 0 sr76 = false := by decide +kernel
private def sr77 : List W := [w43,w162,w181,w70,w84,w101,w121,w150,w170,w192,w202]
private theorem r77 : cutRun blocker 10 0 sr77 = false := by decide +kernel
private def sr78 : List W := [w44,w170,w181,w70,w84,w101,w121,w138,w162,w192,w202]
private theorem r78 : cutRun blocker 10 0 sr78 = false := by decide +kernel
private def sr79 : List W := [w44,w170,w181,w70,w84,w101,w121,w150,w162,w192,w202]
private theorem r79 : cutRun blocker 10 0 sr79 = false := by decide +kernel
private def sr80 : List W := [w45,w181,w192,w70,w84,w101,w121,w138,w162,w170,w202]
private theorem r80 : cutRun blocker 10 0 sr80 = false := by decide +kernel
private def sr81 : List W := [w45,w181,w192,w70,w84,w101,w121,w150,w162,w170,w202]
private theorem r81 : cutRun blocker 10 0 sr81 = false := by decide +kernel
private def sr82 : List W := [w46,w181,w202,w70,w84,w101,w121,w138,w162,w170,w192]
private theorem r82 : cutRun blocker 10 0 sr82 = false := by decide +kernel
private def sr83 : List W := [w46,w181,w202,w70,w84,w101,w121,w150,w162,w170,w192]
private theorem r83 : cutRun blocker 10 0 sr83 = false := by decide +kernel
private def sr84 : List W := [w47,w70,w170,w84,w101,w121,w138,w162,w181,w192,w202]
private theorem r84 : cutRun blocker 10 0 sr84 = false := by decide +kernel
private def sr85 : List W := [w47,w70,w170,w84,w101,w121,w150,w162,w181,w192,w202]
private theorem r85 : cutRun blocker 10 0 sr85 = false := by decide +kernel
private def sr86 : List W := [w48,w84,w170,w70,w101,w121,w138,w162,w181,w192,w202]
private theorem r86 : cutRun blocker 10 0 sr86 = false := by decide +kernel
private def sr87 : List W := [w48,w84,w170,w70,w101,w121,w150,w162,w181,w192,w202]
private theorem r87 : cutRun blocker 10 0 sr87 = false := by decide +kernel
private def sr88 : List W := [w49,w101,w170,w70,w84,w121,w138,w162,w181,w192,w202]
private theorem r88 : cutRun blocker 10 0 sr88 = false := by decide +kernel
private def sr89 : List W := [w49,w101,w170,w70,w84,w121,w150,w162,w181,w192,w202]
private theorem r89 : cutRun blocker 10 0 sr89 = false := by decide +kernel
private def sr90 : List W := [w50,w121,w170,w70,w84,w101,w138,w162,w181,w192,w202]
private theorem r90 : cutRun blocker 10 0 sr90 = false := by decide +kernel
private def sr91 : List W := [w50,w121,w170,w70,w84,w101,w150,w162,w181,w192,w202]
private theorem r91 : cutRun blocker 10 0 sr91 = false := by decide +kernel
private def sr92 : List W := [w51,w138,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r92 : cutRun blocker 10 0 sr92 = false := by decide +kernel
private def sr93 : List W := [w52,w150,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r93 : cutRun blocker 10 0 sr93 = false := by decide +kernel
private def sr94 : List W := [w53,w162,w170,w70,w84,w101,w121,w138,w181,w192,w202]
private theorem r94 : cutRun blocker 10 0 sr94 = false := by decide +kernel
private def sr95 : List W := [w53,w162,w170,w70,w84,w101,w121,w150,w181,w192,w202]
private theorem r95 : cutRun blocker 10 0 sr95 = false := by decide +kernel
private def sr96 : List W := [w54,w170,w181,w70,w84,w101,w121,w138,w162,w192,w202]
private theorem r96 : cutRun blocker 10 0 sr96 = false := by decide +kernel
private def sr97 : List W := [w54,w170,w181,w70,w84,w101,w121,w150,w162,w192,w202]
private theorem r97 : cutRun blocker 10 0 sr97 = false := by decide +kernel
private def sr98 : List W := [w55,w170,w192,w70,w84,w101,w121,w138,w162,w181,w202]
private theorem r98 : cutRun blocker 10 0 sr98 = false := by decide +kernel
private def sr99 : List W := [w55,w170,w192,w70,w84,w101,w121,w150,w162,w181,w202]
private theorem r99 : cutRun blocker 10 0 sr99 = false := by decide +kernel
private def sr100 : List W := [w56,w170,w202,w70,w84,w101,w121,w138,w162,w181,w192]
private theorem r100 : cutRun blocker 10 0 sr100 = false := by decide +kernel
private def sr101 : List W := [w56,w170,w202,w70,w84,w101,w121,w150,w162,w181,w192]
private theorem r101 : cutRun blocker 10 0 sr101 = false := by decide +kernel
private def sr102 : List W := [w57,w162,w170,w70,w84,w101,w121,w138,w181,w192,w202]
private theorem r102 : cutRun blocker 10 0 sr102 = false := by decide +kernel
private def sr103 : List W := [w57,w162,w170,w70,w84,w101,w121,w150,w181,w192,w202]
private theorem r103 : cutRun blocker 10 0 sr103 = false := by decide +kernel
private def sr104 : List W := [w58,w162,w181,w70,w84,w101,w121,w138,w170,w192,w202]
private theorem r104 : cutRun blocker 10 0 sr104 = false := by decide +kernel
private def sr105 : List W := [w58,w162,w181,w70,w84,w101,w121,w150,w170,w192,w202]
private theorem r105 : cutRun blocker 10 0 sr105 = false := by decide +kernel
private def sr106 : List W := [w59,w162,w192,w70,w84,w101,w121,w138,w170,w181,w202]
private theorem r106 : cutRun blocker 10 0 sr106 = false := by decide +kernel
private def sr107 : List W := [w59,w162,w192,w70,w84,w101,w121,w150,w170,w181,w202]
private theorem r107 : cutRun blocker 10 0 sr107 = false := by decide +kernel
private def sr108 : List W := [w60,w162,w202,w70,w84,w101,w121,w138,w170,w181,w192]
private theorem r108 : cutRun blocker 10 0 sr108 = false := by decide +kernel
private def sr109 : List W := [w60,w162,w202,w70,w84,w101,w121,w150,w170,w181,w192]
private theorem r109 : cutRun blocker 10 0 sr109 = false := by decide +kernel
private def sr110 : List W := [w61,w70,w170,w84,w101,w121,w138,w162,w181,w192,w202]
private theorem r110 : cutRun blocker 10 0 sr110 = false := by decide +kernel
private def sr111 : List W := [w61,w70,w170,w84,w101,w121,w150,w162,w181,w192,w202]
private theorem r111 : cutRun blocker 10 0 sr111 = false := by decide +kernel
private def sr112 : List W := [w62,w70,w181,w84,w101,w121,w138,w162,w170,w192,w202]
private theorem r112 : cutRun blocker 10 0 sr112 = false := by decide +kernel
private def sr113 : List W := [w62,w70,w181,w84,w101,w121,w150,w162,w170,w192,w202]
private theorem r113 : cutRun blocker 10 0 sr113 = false := by decide +kernel
private def sr114 : List W := [w63,w70,w138,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r114 : cutRun blocker 10 0 sr114 = false := by decide +kernel
private def sr115 : List W := [w64,w70,w162,w84,w101,w121,w138,w170,w181,w192,w202]
private theorem r115 : cutRun blocker 10 0 sr115 = false := by decide +kernel
private def sr116 : List W := [w64,w70,w162,w84,w101,w121,w150,w170,w181,w192,w202]
private theorem r116 : cutRun blocker 10 0 sr116 = false := by decide +kernel
private def sr117 : List W := [w64,w150,w162,w70,w84,w101,w121,w170,w181,w192,w202]
private theorem r117 : cutRun blocker 10 0 sr117 = false := by decide +kernel
private def sr118 : List W := [w65,w70,w192,w84,w101,w121,w138,w162,w170,w181,w202]
private theorem r118 : cutRun blocker 10 0 sr118 = false := by decide +kernel
private def sr119 : List W := [w65,w70,w192,w84,w101,w121,w150,w162,w170,w181,w202]
private theorem r119 : cutRun blocker 10 0 sr119 = false := by decide +kernel
private def sr120 : List W := [w66,w70,w121,w84,w101,w138,w162,w170,w181,w192,w202]
private theorem r120 : cutRun blocker 10 0 sr120 = false := by decide +kernel
private def sr121 : List W := [w66,w70,w121,w84,w101,w150,w162,w170,w181,w192,w202]
private theorem r121 : cutRun blocker 10 0 sr121 = false := by decide +kernel
private def sr122 : List W := [w67,w70,w101,w84,w121,w138,w162,w170,w181,w192,w202]
private theorem r122 : cutRun blocker 10 0 sr122 = false := by decide +kernel
private def sr123 : List W := [w67,w70,w101,w84,w121,w150,w162,w170,w181,w192,w202]
private theorem r123 : cutRun blocker 10 0 sr123 = false := by decide +kernel
private def sr124 : List W := [w68,w70,w84,w101,w121,w138,w162,w170,w181,w192,w202]
private theorem r124 : cutRun blocker 10 0 sr124 = false := by decide +kernel
private def sr125 : List W := [w68,w70,w84,w101,w121,w150,w162,w170,w181,w192,w202]
private theorem r125 : cutRun blocker 10 0 sr125 = false := by decide +kernel
private def sr126 : List W := [w69,w70,w202,w84,w101,w121,w138,w162,w170,w181,w192]
private theorem r126 : cutRun blocker 10 0 sr126 = false := by decide +kernel
private def sr127 : List W := [w69,w70,w202,w84,w101,w121,w150,w162,w170,w181,w192]
private theorem r127 : cutRun blocker 10 0 sr127 = false := by decide +kernel
private def sr128 : List W := [w71,w150,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r128 : cutRun blocker 10 0 sr128 = false := by decide +kernel
private def sr129 : List W := [w72,w150,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r129 : cutRun blocker 10 0 sr129 = false := by decide +kernel
private def sr130 : List W := [w73,w150,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r130 : cutRun blocker 10 0 sr130 = false := by decide +kernel
private def sr131 : List W := [w74,w150,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r131 : cutRun blocker 10 0 sr131 = false := by decide +kernel
private def sr132 : List W := [w75,w84,w170,w70,w101,w121,w138,w162,w181,w192,w202]
private theorem r132 : cutRun blocker 10 0 sr132 = false := by decide +kernel
private def sr133 : List W := [w75,w84,w170,w70,w101,w121,w150,w162,w181,w192,w202]
private theorem r133 : cutRun blocker 10 0 sr133 = false := by decide +kernel
private def sr134 : List W := [w76,w84,w181,w70,w101,w121,w138,w162,w170,w192,w202]
private theorem r134 : cutRun blocker 10 0 sr134 = false := by decide +kernel
private def sr135 : List W := [w76,w84,w181,w70,w101,w121,w150,w162,w170,w192,w202]
private theorem r135 : cutRun blocker 10 0 sr135 = false := by decide +kernel
private def sr136 : List W := [w77,w84,w150,w70,w101,w121,w162,w170,w181,w192,w202]
private theorem r136 : cutRun blocker 10 0 sr136 = false := by decide +kernel
private def sr137 : List W := [w78,w84,w162,w70,w101,w121,w138,w170,w181,w192,w202]
private theorem r137 : cutRun blocker 10 0 sr137 = false := by decide +kernel
private def sr138 : List W := [w78,w84,w162,w70,w101,w121,w150,w170,w181,w192,w202]
private theorem r138 : cutRun blocker 10 0 sr138 = false := by decide +kernel
private def sr139 : List W := [w78,w138,w162,w70,w84,w101,w121,w170,w181,w192,w202]
private theorem r139 : cutRun blocker 10 0 sr139 = false := by decide +kernel
private def sr140 : List W := [w79,w84,w192,w70,w101,w121,w138,w162,w170,w181,w202]
private theorem r140 : cutRun blocker 10 0 sr140 = false := by decide +kernel
private def sr141 : List W := [w79,w84,w192,w70,w101,w121,w150,w162,w170,w181,w202]
private theorem r141 : cutRun blocker 10 0 sr141 = false := by decide +kernel
private def sr142 : List W := [w80,w70,w84,w101,w121,w138,w162,w170,w181,w192,w202]
private theorem r142 : cutRun blocker 10 0 sr142 = false := by decide +kernel
private def sr143 : List W := [w80,w70,w84,w101,w121,w150,w162,w170,w181,w192,w202]
private theorem r143 : cutRun blocker 10 0 sr143 = false := by decide +kernel
private def sr144 : List W := [w81,w84,w121,w70,w101,w138,w162,w170,w181,w192,w202]
private theorem r144 : cutRun blocker 10 0 sr144 = false := by decide +kernel
private def sr145 : List W := [w81,w84,w121,w70,w101,w150,w162,w170,w181,w192,w202]
private theorem r145 : cutRun blocker 10 0 sr145 = false := by decide +kernel
private def sr146 : List W := [w82,w84,w202,w70,w101,w121,w138,w162,w170,w181,w192]
private theorem r146 : cutRun blocker 10 0 sr146 = false := by decide +kernel
private def sr147 : List W := [w82,w84,w202,w70,w101,w121,w150,w162,w170,w181,w192]
private theorem r147 : cutRun blocker 10 0 sr147 = false := by decide +kernel
private def sr148 : List W := [w83,w84,w101,w70,w121,w138,w162,w170,w181,w192,w202]
private theorem r148 : cutRun blocker 10 0 sr148 = false := by decide +kernel
private def sr149 : List W := [w83,w84,w101,w70,w121,w150,w162,w170,w181,w192,w202]
private theorem r149 : cutRun blocker 10 0 sr149 = false := by decide +kernel
private def sr150 : List W := [w86,w138,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r150 : cutRun blocker 10 0 sr150 = false := by decide +kernel
private def sr151 : List W := [w87,w138,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r151 : cutRun blocker 10 0 sr151 = false := by decide +kernel
private def sr152 : List W := [w88,w138,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r152 : cutRun blocker 10 0 sr152 = false := by decide +kernel
private def sr153 : List W := [w89,w138,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r153 : cutRun blocker 10 0 sr153 = false := by decide +kernel
private def sr154 : List W := [w90,w70,w84,w101,w121,w138,w162,w170,w181,w192,w202]
private theorem r154 : cutRun blocker 10 0 sr154 = false := by decide +kernel
private def sr155 : List W := [w90,w70,w84,w101,w121,w150,w162,w170,w181,w192,w202]
private theorem r155 : cutRun blocker 10 0 sr155 = false := by decide +kernel
private def sr156 : List W := [w91,w101,w170,w70,w84,w121,w138,w162,w181,w192,w202]
private theorem r156 : cutRun blocker 10 0 sr156 = false := by decide +kernel
private def sr157 : List W := [w91,w101,w170,w70,w84,w121,w150,w162,w181,w192,w202]
private theorem r157 : cutRun blocker 10 0 sr157 = false := by decide +kernel
private def sr158 : List W := [w92,w101,w181,w70,w84,w121,w138,w162,w170,w192,w202]
private theorem r158 : cutRun blocker 10 0 sr158 = false := by decide +kernel
private def sr159 : List W := [w92,w101,w181,w70,w84,w121,w150,w162,w170,w192,w202]
private theorem r159 : cutRun blocker 10 0 sr159 = false := by decide +kernel
private def sr160 : List W := [w93,w101,w150,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r160 : cutRun blocker 10 0 sr160 = false := by decide +kernel
private def sr161 : List W := [w94,w101,w138,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r161 : cutRun blocker 10 0 sr161 = false := by decide +kernel
private def sr162 : List W := [w95,w101,w162,w70,w84,w121,w138,w170,w181,w192,w202]
private theorem r162 : cutRun blocker 10 0 sr162 = false := by decide +kernel
private def sr163 : List W := [w95,w101,w162,w70,w84,w121,w150,w170,w181,w192,w202]
private theorem r163 : cutRun blocker 10 0 sr163 = false := by decide +kernel
private def sr164 : List W := [w96,w101,w192,w70,w84,w121,w138,w162,w170,w181,w202]
private theorem r164 : cutRun blocker 10 0 sr164 = false := by decide +kernel
private def sr165 : List W := [w96,w101,w192,w70,w84,w121,w150,w162,w170,w181,w202]
private theorem r165 : cutRun blocker 10 0 sr165 = false := by decide +kernel
private def sr166 : List W := [w97,w70,w101,w84,w121,w138,w162,w170,w181,w192,w202]
private theorem r166 : cutRun blocker 10 0 sr166 = false := by decide +kernel
private def sr167 : List W := [w97,w70,w101,w84,w121,w150,w162,w170,w181,w192,w202]
private theorem r167 : cutRun blocker 10 0 sr167 = false := by decide +kernel
private def sr168 : List W := [w98,w101,w202,w70,w84,w121,w138,w162,w170,w181,w192]
private theorem r168 : cutRun blocker 10 0 sr168 = false := by decide +kernel
private def sr169 : List W := [w98,w101,w202,w70,w84,w121,w150,w162,w170,w181,w192]
private theorem r169 : cutRun blocker 10 0 sr169 = false := by decide +kernel
private def sr170 : List W := [w99,w101,w121,w70,w84,w138,w162,w170,w181,w192,w202]
private theorem r170 : cutRun blocker 10 0 sr170 = false := by decide +kernel
private def sr171 : List W := [w99,w101,w121,w70,w84,w150,w162,w170,w181,w192,w202]
private theorem r171 : cutRun blocker 10 0 sr171 = false := by decide +kernel
private def sr172 : List W := [w100,w84,w101,w70,w121,w138,w162,w170,w181,w192,w202]
private theorem r172 : cutRun blocker 10 0 sr172 = false := by decide +kernel
private def sr173 : List W := [w100,w84,w101,w70,w121,w150,w162,w170,w181,w192,w202]
private theorem r173 : cutRun blocker 10 0 sr173 = false := by decide +kernel
private def sr174 : List W := [w102,w121,w138,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r174 : cutRun blocker 10 0 sr174 = false := by decide +kernel
private def sr175 : List W := [w103,w70,w101,w84,w121,w138,w162,w170,w181,w192,w202]
private theorem r175 : cutRun blocker 10 0 sr175 = false := by decide +kernel
private def sr176 : List W := [w103,w70,w101,w84,w121,w150,w162,w170,w181,w192,w202]
private theorem r176 : cutRun blocker 10 0 sr176 = false := by decide +kernel
private def sr177 : List W := [w104,w121,w150,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r177 : cutRun blocker 10 0 sr177 = false := by decide +kernel
private def sr178 : List W := [w105,w84,w101,w70,w121,w138,w162,w170,w181,w192,w202]
private theorem r178 : cutRun blocker 10 0 sr178 = false := by decide +kernel
private def sr179 : List W := [w105,w84,w101,w70,w121,w150,w162,w170,w181,w192,w202]
private theorem r179 : cutRun blocker 10 0 sr179 = false := by decide +kernel
private def sr180 : List W := [w106,w121,w162,w70,w84,w101,w138,w170,w181,w192,w202]
private theorem r180 : cutRun blocker 10 0 sr180 = false := by decide +kernel
private def sr181 : List W := [w106,w121,w162,w70,w84,w101,w150,w170,w181,w192,w202]
private theorem r181 : cutRun blocker 10 0 sr181 = false := by decide +kernel
private def sr182 : List W := [w107,w121,w170,w70,w84,w101,w138,w162,w181,w192,w202]
private theorem r182 : cutRun blocker 10 0 sr182 = false := by decide +kernel
private def sr183 : List W := [w107,w121,w170,w70,w84,w101,w150,w162,w181,w192,w202]
private theorem r183 : cutRun blocker 10 0 sr183 = false := by decide +kernel
private def sr184 : List W := [w108,w121,w181,w70,w84,w101,w138,w162,w170,w192,w202]
private theorem r184 : cutRun blocker 10 0 sr184 = false := by decide +kernel
private def sr185 : List W := [w108,w121,w181,w70,w84,w101,w150,w162,w170,w192,w202]
private theorem r185 : cutRun blocker 10 0 sr185 = false := by decide +kernel
private def sr186 : List W := [w109,w121,w192,w70,w84,w101,w138,w162,w170,w181,w202]
private theorem r186 : cutRun blocker 10 0 sr186 = false := by decide +kernel
private def sr187 : List W := [w109,w121,w192,w70,w84,w101,w150,w162,w170,w181,w202]
private theorem r187 : cutRun blocker 10 0 sr187 = false := by decide +kernel
private def sr188 : List W := [w110,w121,w202,w70,w84,w101,w138,w162,w170,w181,w192]
private theorem r188 : cutRun blocker 10 0 sr188 = false := by decide +kernel
private def sr189 : List W := [w110,w121,w202,w70,w84,w101,w150,w162,w170,w181,w192]
private theorem r189 : cutRun blocker 10 0 sr189 = false := by decide +kernel
private def sr190 : List W := [w111,w121,w170,w70,w84,w101,w138,w162,w181,w192,w202]
private theorem r190 : cutRun blocker 10 0 sr190 = false := by decide +kernel
private def sr191 : List W := [w111,w121,w170,w70,w84,w101,w150,w162,w181,w192,w202]
private theorem r191 : cutRun blocker 10 0 sr191 = false := by decide +kernel
private def sr192 : List W := [w112,w121,w181,w70,w84,w101,w138,w162,w170,w192,w202]
private theorem r192 : cutRun blocker 10 0 sr192 = false := by decide +kernel
private def sr193 : List W := [w112,w121,w181,w70,w84,w101,w150,w162,w170,w192,w202]
private theorem r193 : cutRun blocker 10 0 sr193 = false := by decide +kernel
private def sr194 : List W := [w113,w121,w150,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r194 : cutRun blocker 10 0 sr194 = false := by decide +kernel
private def sr195 : List W := [w114,w121,w138,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r195 : cutRun blocker 10 0 sr195 = false := by decide +kernel
private def sr196 : List W := [w115,w121,w162,w70,w84,w101,w138,w170,w181,w192,w202]
private theorem r196 : cutRun blocker 10 0 sr196 = false := by decide +kernel
private def sr197 : List W := [w115,w121,w162,w70,w84,w101,w150,w170,w181,w192,w202]
private theorem r197 : cutRun blocker 10 0 sr197 = false := by decide +kernel
private def sr198 : List W := [w116,w121,w192,w70,w84,w101,w138,w162,w170,w181,w202]
private theorem r198 : cutRun blocker 10 0 sr198 = false := by decide +kernel
private def sr199 : List W := [w116,w121,w192,w70,w84,w101,w150,w162,w170,w181,w202]
private theorem r199 : cutRun blocker 10 0 sr199 = false := by decide +kernel
private def sr200 : List W := [w117,w70,w121,w84,w101,w138,w162,w170,w181,w192,w202]
private theorem r200 : cutRun blocker 10 0 sr200 = false := by decide +kernel
private def sr201 : List W := [w117,w70,w121,w84,w101,w150,w162,w170,w181,w192,w202]
private theorem r201 : cutRun blocker 10 0 sr201 = false := by decide +kernel
private def sr202 : List W := [w118,w121,w202,w70,w84,w101,w138,w162,w170,w181,w192]
private theorem r202 : cutRun blocker 10 0 sr202 = false := by decide +kernel
private def sr203 : List W := [w118,w121,w202,w70,w84,w101,w150,w162,w170,w181,w192]
private theorem r203 : cutRun blocker 10 0 sr203 = false := by decide +kernel
private def sr204 : List W := [w119,w101,w121,w70,w84,w138,w162,w170,w181,w192,w202]
private theorem r204 : cutRun blocker 10 0 sr204 = false := by decide +kernel
private def sr205 : List W := [w119,w101,w121,w70,w84,w150,w162,w170,w181,w192,w202]
private theorem r205 : cutRun blocker 10 0 sr205 = false := by decide +kernel
private def sr206 : List W := [w120,w84,w121,w70,w101,w138,w162,w170,w181,w192,w202]
private theorem r206 : cutRun blocker 10 0 sr206 = false := by decide +kernel
private def sr207 : List W := [w120,w84,w121,w70,w101,w150,w162,w170,w181,w192,w202]
private theorem r207 : cutRun blocker 10 0 sr207 = false := by decide +kernel
private def sr208 : List W := [w123,w101,w138,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r208 : cutRun blocker 10 0 sr208 = false := by decide +kernel
private def sr209 : List W := [w124,w70,w121,w84,w101,w138,w162,w170,w181,w192,w202]
private theorem r209 : cutRun blocker 10 0 sr209 = false := by decide +kernel
private def sr210 : List W := [w124,w70,w121,w84,w101,w150,w162,w170,w181,w192,w202]
private theorem r210 : cutRun blocker 10 0 sr210 = false := by decide +kernel
private def sr211 : List W := [w125,w101,w150,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r211 : cutRun blocker 10 0 sr211 = false := by decide +kernel
private def sr212 : List W := [w126,w84,w121,w70,w101,w138,w162,w170,w181,w192,w202]
private theorem r212 : cutRun blocker 10 0 sr212 = false := by decide +kernel
private def sr213 : List W := [w126,w84,w121,w70,w101,w150,w162,w170,w181,w192,w202]
private theorem r213 : cutRun blocker 10 0 sr213 = false := by decide +kernel
private def sr214 : List W := [w127,w101,w162,w70,w84,w121,w138,w170,w181,w192,w202]
private theorem r214 : cutRun blocker 10 0 sr214 = false := by decide +kernel
private def sr215 : List W := [w127,w101,w162,w70,w84,w121,w150,w170,w181,w192,w202]
private theorem r215 : cutRun blocker 10 0 sr215 = false := by decide +kernel
private def sr216 : List W := [w128,w101,w170,w70,w84,w121,w138,w162,w181,w192,w202]
private theorem r216 : cutRun blocker 10 0 sr216 = false := by decide +kernel
private def sr217 : List W := [w128,w101,w170,w70,w84,w121,w150,w162,w181,w192,w202]
private theorem r217 : cutRun blocker 10 0 sr217 = false := by decide +kernel
private def sr218 : List W := [w129,w101,w181,w70,w84,w121,w138,w162,w170,w192,w202]
private theorem r218 : cutRun blocker 10 0 sr218 = false := by decide +kernel
private def sr219 : List W := [w129,w101,w181,w70,w84,w121,w150,w162,w170,w192,w202]
private theorem r219 : cutRun blocker 10 0 sr219 = false := by decide +kernel
private def sr220 : List W := [w130,w101,w192,w70,w84,w121,w138,w162,w170,w181,w202]
private theorem r220 : cutRun blocker 10 0 sr220 = false := by decide +kernel
private def sr221 : List W := [w130,w101,w192,w70,w84,w121,w150,w162,w170,w181,w202]
private theorem r221 : cutRun blocker 10 0 sr221 = false := by decide +kernel
private def sr222 : List W := [w131,w101,w202,w70,w84,w121,w138,w162,w170,w181,w192]
private theorem r222 : cutRun blocker 10 0 sr222 = false := by decide +kernel
private def sr223 : List W := [w131,w101,w202,w70,w84,w121,w150,w162,w170,w181,w192]
private theorem r223 : cutRun blocker 10 0 sr223 = false := by decide +kernel
private def sr224 : List W := [w132,w70,w138,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r224 : cutRun blocker 10 0 sr224 = false := by decide +kernel
private def sr225 : List W := [w132,w84,w150,w70,w101,w121,w162,w170,w181,w192,w202]
private theorem r225 : cutRun blocker 10 0 sr225 = false := by decide +kernel
private def sr226 : List W := [w133,w101,w121,w70,w84,w138,w162,w170,w181,w192,w202]
private theorem r226 : cutRun blocker 10 0 sr226 = false := by decide +kernel
private def sr227 : List W := [w133,w101,w121,w70,w84,w150,w162,w170,w181,w192,w202]
private theorem r227 : cutRun blocker 10 0 sr227 = false := by decide +kernel
private def sr228 : List W := [w134,w138,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r228 : cutRun blocker 10 0 sr228 = false := by decide +kernel
private def sr229 : List W := [w135,w138,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r229 : cutRun blocker 10 0 sr229 = false := by decide +kernel
private def sr230 : List W := [w136,w138,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r230 : cutRun blocker 10 0 sr230 = false := by decide +kernel
private def sr231 : List W := [w137,w138,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r231 : cutRun blocker 10 0 sr231 = false := by decide +kernel
private def sr232 : List W := [w138,w84,w162,w70,w101,w121,w150,w170,w181,w192,w202]
private theorem r232 : cutRun blocker 10 0 sr232 = false := by decide +kernel
private def sr233 : List W := [w139,w70,w138,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r233 : cutRun blocker 10 0 sr233 = false := by decide +kernel
private def sr234 : List W := [w140,w101,w138,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r234 : cutRun blocker 10 0 sr234 = false := by decide +kernel
private def sr235 : List W := [w141,w121,w138,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r235 : cutRun blocker 10 0 sr235 = false := by decide +kernel
private def sr236 : List W := [w142,w84,w170,w70,w101,w121,w138,w162,w181,w192,w202]
private theorem r236 : cutRun blocker 10 0 sr236 = false := by decide +kernel
private def sr237 : List W := [w142,w84,w170,w70,w101,w121,w150,w162,w181,w192,w202]
private theorem r237 : cutRun blocker 10 0 sr237 = false := by decide +kernel
private def sr238 : List W := [w143,w84,w181,w70,w101,w121,w138,w162,w170,w192,w202]
private theorem r238 : cutRun blocker 10 0 sr238 = false := by decide +kernel
private def sr239 : List W := [w143,w84,w181,w70,w101,w121,w150,w162,w170,w192,w202]
private theorem r239 : cutRun blocker 10 0 sr239 = false := by decide +kernel
private def sr240 : List W := [w144,w84,w192,w70,w101,w121,w138,w162,w170,w181,w202]
private theorem r240 : cutRun blocker 10 0 sr240 = false := by decide +kernel
private def sr241 : List W := [w144,w84,w192,w70,w101,w121,w150,w162,w170,w181,w202]
private theorem r241 : cutRun blocker 10 0 sr241 = false := by decide +kernel
private def sr242 : List W := [w145,w84,w202,w70,w101,w121,w138,w162,w170,w181,w192]
private theorem r242 : cutRun blocker 10 0 sr242 = false := by decide +kernel
private def sr243 : List W := [w145,w84,w202,w70,w101,w121,w150,w162,w170,w181,w192]
private theorem r243 : cutRun blocker 10 0 sr243 = false := by decide +kernel
private def sr244 : List W := [w146,w150,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r244 : cutRun blocker 10 0 sr244 = false := by decide +kernel
private def sr245 : List W := [w147,w150,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r245 : cutRun blocker 10 0 sr245 = false := by decide +kernel
private def sr246 : List W := [w148,w150,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r246 : cutRun blocker 10 0 sr246 = false := by decide +kernel
private def sr247 : List W := [w149,w150,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r247 : cutRun blocker 10 0 sr247 = false := by decide +kernel
private def sr248 : List W := [w150,w70,w162,w84,w101,w121,w138,w170,w181,w192,w202]
private theorem r248 : cutRun blocker 10 0 sr248 = false := by decide +kernel
private def sr249 : List W := [w151,w84,w150,w70,w101,w121,w162,w170,w181,w192,w202]
private theorem r249 : cutRun blocker 10 0 sr249 = false := by decide +kernel
private def sr250 : List W := [w152,w101,w150,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r250 : cutRun blocker 10 0 sr250 = false := by decide +kernel
private def sr251 : List W := [w153,w121,w150,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r251 : cutRun blocker 10 0 sr251 = false := by decide +kernel
private def sr252 : List W := [w154,w70,w170,w84,w101,w121,w138,w162,w181,w192,w202]
private theorem r252 : cutRun blocker 10 0 sr252 = false := by decide +kernel
private def sr253 : List W := [w154,w70,w170,w84,w101,w121,w150,w162,w181,w192,w202]
private theorem r253 : cutRun blocker 10 0 sr253 = false := by decide +kernel
private def sr254 : List W := [w155,w70,w181,w84,w101,w121,w138,w162,w170,w192,w202]
private theorem r254 : cutRun blocker 10 0 sr254 = false := by decide +kernel
private def sr255 : List W := [w155,w70,w181,w84,w101,w121,w150,w162,w170,w192,w202]
private theorem r255 : cutRun blocker 10 0 sr255 = false := by decide +kernel
private def sr256 : List W := [w156,w70,w192,w84,w101,w121,w138,w162,w170,w181,w202]
private theorem r256 : cutRun blocker 10 0 sr256 = false := by decide +kernel
private def sr257 : List W := [w156,w70,w192,w84,w101,w121,w150,w162,w170,w181,w202]
private theorem r257 : cutRun blocker 10 0 sr257 = false := by decide +kernel
private def sr258 : List W := [w157,w70,w202,w84,w101,w121,w138,w162,w170,w181,w192]
private theorem r258 : cutRun blocker 10 0 sr258 = false := by decide +kernel
private def sr259 : List W := [w157,w70,w202,w84,w101,w121,w150,w162,w170,w181,w192]
private theorem r259 : cutRun blocker 10 0 sr259 = false := by decide +kernel
private def sr260 : List W := [w158,w162,w170,w70,w84,w101,w121,w138,w181,w192,w202]
private theorem r260 : cutRun blocker 10 0 sr260 = false := by decide +kernel
private def sr261 : List W := [w158,w162,w170,w70,w84,w101,w121,w150,w181,w192,w202]
private theorem r261 : cutRun blocker 10 0 sr261 = false := by decide +kernel
private def sr262 : List W := [w159,w162,w181,w70,w84,w101,w121,w138,w170,w192,w202]
private theorem r262 : cutRun blocker 10 0 sr262 = false := by decide +kernel
private def sr263 : List W := [w159,w162,w181,w70,w84,w101,w121,w150,w170,w192,w202]
private theorem r263 : cutRun blocker 10 0 sr263 = false := by decide +kernel
private def sr264 : List W := [w160,w162,w192,w70,w84,w101,w121,w138,w170,w181,w202]
private theorem r264 : cutRun blocker 10 0 sr264 = false := by decide +kernel
private def sr265 : List W := [w160,w162,w192,w70,w84,w101,w121,w150,w170,w181,w202]
private theorem r265 : cutRun blocker 10 0 sr265 = false := by decide +kernel
private def sr266 : List W := [w161,w162,w202,w70,w84,w101,w121,w138,w170,w181,w192]
private theorem r266 : cutRun blocker 10 0 sr266 = false := by decide +kernel
private def sr267 : List W := [w161,w162,w202,w70,w84,w101,w121,w150,w170,w181,w192]
private theorem r267 : cutRun blocker 10 0 sr267 = false := by decide +kernel
private def sr268 : List W := [w163,w70,w150,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r268 : cutRun blocker 10 0 sr268 = false := by decide +kernel
private def sr269 : List W := [w163,w70,w162,w84,w101,w121,w138,w170,w181,w192,w202]
private theorem r269 : cutRun blocker 10 0 sr269 = false := by decide +kernel
private def sr270 : List W := [w163,w70,w162,w84,w101,w121,w150,w170,w181,w192,w202]
private theorem r270 : cutRun blocker 10 0 sr270 = false := by decide +kernel
private def sr271 : List W := [w164,w84,w138,w70,w101,w121,w162,w170,w181,w192,w202]
private theorem r271 : cutRun blocker 10 0 sr271 = false := by decide +kernel
private def sr272 : List W := [w164,w84,w162,w70,w101,w121,w138,w170,w181,w192,w202]
private theorem r272 : cutRun blocker 10 0 sr272 = false := by decide +kernel
private def sr273 : List W := [w164,w84,w162,w70,w101,w121,w150,w170,w181,w192,w202]
private theorem r273 : cutRun blocker 10 0 sr273 = false := by decide +kernel
private def sr274 : List W := [w165,w101,w162,w70,w84,w121,w138,w170,w181,w192,w202]
private theorem r274 : cutRun blocker 10 0 sr274 = false := by decide +kernel
private def sr275 : List W := [w165,w101,w162,w70,w84,w121,w150,w170,w181,w192,w202]
private theorem r275 : cutRun blocker 10 0 sr275 = false := by decide +kernel
private def sr276 : List W := [w166,w121,w162,w70,w84,w101,w138,w170,w181,w192,w202]
private theorem r276 : cutRun blocker 10 0 sr276 = false := by decide +kernel
private def sr277 : List W := [w166,w121,w162,w70,w84,w101,w150,w170,w181,w192,w202]
private theorem r277 : cutRun blocker 10 0 sr277 = false := by decide +kernel
private def sr278 : List W := [w167,w170,w181,w70,w84,w101,w121,w138,w162,w192,w202]
private theorem r278 : cutRun blocker 10 0 sr278 = false := by decide +kernel
private def sr279 : List W := [w167,w170,w181,w70,w84,w101,w121,w150,w162,w192,w202]
private theorem r279 : cutRun blocker 10 0 sr279 = false := by decide +kernel
private def sr280 : List W := [w168,w170,w192,w70,w84,w101,w121,w138,w162,w181,w202]
private theorem r280 : cutRun blocker 10 0 sr280 = false := by decide +kernel
private def sr281 : List W := [w168,w170,w192,w70,w84,w101,w121,w150,w162,w181,w202]
private theorem r281 : cutRun blocker 10 0 sr281 = false := by decide +kernel
private def sr282 : List W := [w169,w170,w202,w70,w84,w101,w121,w138,w162,w181,w192]
private theorem r282 : cutRun blocker 10 0 sr282 = false := by decide +kernel
private def sr283 : List W := [w169,w170,w202,w70,w84,w101,w121,w150,w162,w181,w192]
private theorem r283 : cutRun blocker 10 0 sr283 = false := by decide +kernel
private def sr284 : List W := [w172,w70,w170,w84,w101,w121,w138,w162,w181,w192,w202]
private theorem r284 : cutRun blocker 10 0 sr284 = false := by decide +kernel
private def sr285 : List W := [w172,w70,w170,w84,w101,w121,w150,w162,w181,w192,w202]
private theorem r285 : cutRun blocker 10 0 sr285 = false := by decide +kernel
private def sr286 : List W := [w173,w84,w170,w70,w101,w121,w138,w162,w181,w192,w202]
private theorem r286 : cutRun blocker 10 0 sr286 = false := by decide +kernel
private def sr287 : List W := [w173,w84,w170,w70,w101,w121,w150,w162,w181,w192,w202]
private theorem r287 : cutRun blocker 10 0 sr287 = false := by decide +kernel
private def sr288 : List W := [w174,w101,w170,w70,w84,w121,w138,w162,w181,w192,w202]
private theorem r288 : cutRun blocker 10 0 sr288 = false := by decide +kernel
private def sr289 : List W := [w174,w101,w170,w70,w84,w121,w150,w162,w181,w192,w202]
private theorem r289 : cutRun blocker 10 0 sr289 = false := by decide +kernel
private def sr290 : List W := [w175,w121,w170,w70,w84,w101,w138,w162,w181,w192,w202]
private theorem r290 : cutRun blocker 10 0 sr290 = false := by decide +kernel
private def sr291 : List W := [w175,w121,w170,w70,w84,w101,w150,w162,w181,w192,w202]
private theorem r291 : cutRun blocker 10 0 sr291 = false := by decide +kernel
private def sr292 : List W := [w176,w138,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r292 : cutRun blocker 10 0 sr292 = false := by decide +kernel
private def sr293 : List W := [w177,w150,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r293 : cutRun blocker 10 0 sr293 = false := by decide +kernel
private def sr294 : List W := [w178,w162,w170,w70,w84,w101,w121,w138,w181,w192,w202]
private theorem r294 : cutRun blocker 10 0 sr294 = false := by decide +kernel
private def sr295 : List W := [w178,w162,w170,w70,w84,w101,w121,w150,w181,w192,w202]
private theorem r295 : cutRun blocker 10 0 sr295 = false := by decide +kernel
private def sr296 : List W := [w179,w181,w192,w70,w84,w101,w121,w138,w162,w170,w202]
private theorem r296 : cutRun blocker 10 0 sr296 = false := by decide +kernel
private def sr297 : List W := [w179,w181,w192,w70,w84,w101,w121,w150,w162,w170,w202]
private theorem r297 : cutRun blocker 10 0 sr297 = false := by decide +kernel
private def sr298 : List W := [w180,w181,w202,w70,w84,w101,w121,w138,w162,w170,w192]
private theorem r298 : cutRun blocker 10 0 sr298 = false := by decide +kernel
private def sr299 : List W := [w180,w181,w202,w70,w84,w101,w121,w150,w162,w170,w192]
private theorem r299 : cutRun blocker 10 0 sr299 = false := by decide +kernel
private def sr300 : List W := [w183,w70,w181,w84,w101,w121,w138,w162,w170,w192,w202]
private theorem r300 : cutRun blocker 10 0 sr300 = false := by decide +kernel
private def sr301 : List W := [w183,w70,w181,w84,w101,w121,w150,w162,w170,w192,w202]
private theorem r301 : cutRun blocker 10 0 sr301 = false := by decide +kernel
private def sr302 : List W := [w184,w84,w181,w70,w101,w121,w138,w162,w170,w192,w202]
private theorem r302 : cutRun blocker 10 0 sr302 = false := by decide +kernel
private def sr303 : List W := [w184,w84,w181,w70,w101,w121,w150,w162,w170,w192,w202]
private theorem r303 : cutRun blocker 10 0 sr303 = false := by decide +kernel
private def sr304 : List W := [w185,w101,w181,w70,w84,w121,w138,w162,w170,w192,w202]
private theorem r304 : cutRun blocker 10 0 sr304 = false := by decide +kernel
private def sr305 : List W := [w185,w101,w181,w70,w84,w121,w150,w162,w170,w192,w202]
private theorem r305 : cutRun blocker 10 0 sr305 = false := by decide +kernel
private def sr306 : List W := [w186,w121,w181,w70,w84,w101,w138,w162,w170,w192,w202]
private theorem r306 : cutRun blocker 10 0 sr306 = false := by decide +kernel
private def sr307 : List W := [w186,w121,w181,w70,w84,w101,w150,w162,w170,w192,w202]
private theorem r307 : cutRun blocker 10 0 sr307 = false := by decide +kernel
private def sr308 : List W := [w187,w138,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r308 : cutRun blocker 10 0 sr308 = false := by decide +kernel
private def sr309 : List W := [w188,w150,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r309 : cutRun blocker 10 0 sr309 = false := by decide +kernel
private def sr310 : List W := [w189,w162,w181,w70,w84,w101,w121,w138,w170,w192,w202]
private theorem r310 : cutRun blocker 10 0 sr310 = false := by decide +kernel
private def sr311 : List W := [w189,w162,w181,w70,w84,w101,w121,w150,w170,w192,w202]
private theorem r311 : cutRun blocker 10 0 sr311 = false := by decide +kernel
private def sr312 : List W := [w190,w170,w181,w70,w84,w101,w121,w138,w162,w192,w202]
private theorem r312 : cutRun blocker 10 0 sr312 = false := by decide +kernel
private def sr313 : List W := [w190,w170,w181,w70,w84,w101,w121,w150,w162,w192,w202]
private theorem r313 : cutRun blocker 10 0 sr313 = false := by decide +kernel
private def sr314 : List W := [w191,w192,w202,w70,w84,w101,w121,w138,w162,w170,w181]
private theorem r314 : cutRun blocker 10 0 sr314 = false := by decide +kernel
private def sr315 : List W := [w191,w192,w202,w70,w84,w101,w121,w150,w162,w170,w181]
private theorem r315 : cutRun blocker 10 0 sr315 = false := by decide +kernel
private def sr316 : List W := [w193,w150,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r316 : cutRun blocker 10 0 sr316 = false := by decide +kernel
private def sr317 : List W := [w194,w170,w192,w70,w84,w101,w121,w138,w162,w181,w202]
private theorem r317 : cutRun blocker 10 0 sr317 = false := by decide +kernel
private def sr318 : List W := [w194,w170,w192,w70,w84,w101,w121,w150,w162,w181,w202]
private theorem r318 : cutRun blocker 10 0 sr318 = false := by decide +kernel
private def sr319 : List W := [w195,w84,w192,w70,w101,w121,w138,w162,w170,w181,w202]
private theorem r319 : cutRun blocker 10 0 sr319 = false := by decide +kernel
private def sr320 : List W := [w195,w84,w192,w70,w101,w121,w150,w162,w170,w181,w202]
private theorem r320 : cutRun blocker 10 0 sr320 = false := by decide +kernel
private def sr321 : List W := [w196,w101,w192,w70,w84,w121,w138,w162,w170,w181,w202]
private theorem r321 : cutRun blocker 10 0 sr321 = false := by decide +kernel
private def sr322 : List W := [w196,w101,w192,w70,w84,w121,w150,w162,w170,w181,w202]
private theorem r322 : cutRun blocker 10 0 sr322 = false := by decide +kernel
private def sr323 : List W := [w197,w121,w192,w70,w84,w101,w138,w162,w170,w181,w202]
private theorem r323 : cutRun blocker 10 0 sr323 = false := by decide +kernel
private def sr324 : List W := [w197,w121,w192,w70,w84,w101,w150,w162,w170,w181,w202]
private theorem r324 : cutRun blocker 10 0 sr324 = false := by decide +kernel
private def sr325 : List W := [w198,w138,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r325 : cutRun blocker 10 0 sr325 = false := by decide +kernel
private def sr326 : List W := [w199,w162,w192,w70,w84,w101,w121,w138,w170,w181,w202]
private theorem r326 : cutRun blocker 10 0 sr326 = false := by decide +kernel
private def sr327 : List W := [w199,w162,w192,w70,w84,w101,w121,w150,w170,w181,w202]
private theorem r327 : cutRun blocker 10 0 sr327 = false := by decide +kernel
private def sr328 : List W := [w200,w70,w192,w84,w101,w121,w138,w162,w170,w181,w202]
private theorem r328 : cutRun blocker 10 0 sr328 = false := by decide +kernel
private def sr329 : List W := [w200,w70,w192,w84,w101,w121,w150,w162,w170,w181,w202]
private theorem r329 : cutRun blocker 10 0 sr329 = false := by decide +kernel
private def sr330 : List W := [w201,w181,w192,w70,w84,w101,w121,w138,w162,w170,w202]
private theorem r330 : cutRun blocker 10 0 sr330 = false := by decide +kernel
private def sr331 : List W := [w201,w181,w192,w70,w84,w101,w121,w150,w162,w170,w202]
private theorem r331 : cutRun blocker 10 0 sr331 = false := by decide +kernel
private def sr332 : List W := [w204,w170,w202,w70,w84,w101,w121,w138,w162,w181,w192]
private theorem r332 : cutRun blocker 10 0 sr332 = false := by decide +kernel
private def sr333 : List W := [w204,w170,w202,w70,w84,w101,w121,w150,w162,w181,w192]
private theorem r333 : cutRun blocker 10 0 sr333 = false := by decide +kernel
private def sr334 : List W := [w205,w70,w202,w84,w101,w121,w138,w162,w170,w181,w192]
private theorem r334 : cutRun blocker 10 0 sr334 = false := by decide +kernel
private def sr335 : List W := [w205,w70,w202,w84,w101,w121,w150,w162,w170,w181,w192]
private theorem r335 : cutRun blocker 10 0 sr335 = false := by decide +kernel
private def sr336 : List W := [w206,w84,w202,w70,w101,w121,w138,w162,w170,w181,w192]
private theorem r336 : cutRun blocker 10 0 sr336 = false := by decide +kernel
private def sr337 : List W := [w206,w84,w202,w70,w101,w121,w150,w162,w170,w181,w192]
private theorem r337 : cutRun blocker 10 0 sr337 = false := by decide +kernel
private def sr338 : List W := [w207,w101,w202,w70,w84,w121,w138,w162,w170,w181,w192]
private theorem r338 : cutRun blocker 10 0 sr338 = false := by decide +kernel
private def sr339 : List W := [w207,w101,w202,w70,w84,w121,w150,w162,w170,w181,w192]
private theorem r339 : cutRun blocker 10 0 sr339 = false := by decide +kernel
private def sr340 : List W := [w208,w138,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r340 : cutRun blocker 10 0 sr340 = false := by decide +kernel
private def sr341 : List W := [w209,w150,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r341 : cutRun blocker 10 0 sr341 = false := by decide +kernel
private def sr342 : List W := [w210,w162,w202,w70,w84,w101,w121,w138,w170,w181,w192]
private theorem r342 : cutRun blocker 10 0 sr342 = false := by decide +kernel
private def sr343 : List W := [w210,w162,w202,w70,w84,w101,w121,w150,w170,w181,w192]
private theorem r343 : cutRun blocker 10 0 sr343 = false := by decide +kernel
private def sr344 : List W := [w211,w181,w202,w70,w84,w101,w121,w138,w162,w170,w192]
private theorem r344 : cutRun blocker 10 0 sr344 = false := by decide +kernel
private def sr345 : List W := [w211,w181,w202,w70,w84,w101,w121,w150,w162,w170,w192]
private theorem r345 : cutRun blocker 10 0 sr345 = false := by decide +kernel
private def sr346 : List W := [w212,w121,w202,w70,w84,w101,w138,w162,w170,w181,w192]
private theorem r346 : cutRun blocker 10 0 sr346 = false := by decide +kernel
private def sr347 : List W := [w212,w121,w202,w70,w84,w101,w150,w162,w170,w181,w192]
private theorem r347 : cutRun blocker 10 0 sr347 = false := by decide +kernel
private def sr348 : List W := [w213,w192,w202,w70,w84,w101,w121,w138,w162,w170,w181]
private theorem r348 : cutRun blocker 10 0 sr348 = false := by decide +kernel
private def sr349 : List W := [w213,w192,w202,w70,w84,w101,w121,w150,w162,w170,w181]
private theorem r349 : cutRun blocker 10 0 sr349 = false := by decide +kernel
private def sr350 : List W := [w0,w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r350 : cutRun blocker 10 1 sr350 = false := by decide +kernel
private def sr351 : List W := [w0,w84,w70,w101,w121,w162,w170,w181,w192,w202]
private theorem r351 : cutRun blocker 10 1 sr351 = false := by decide +kernel
private def sr352 : List W := [w0,w162,w70,w84,w101,w121,w170,w181,w192,w202]
private theorem r352 : cutRun blocker 10 1 sr352 = false := by decide +kernel
private def sr353 : List W := [w8,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r353 : cutRun blocker 10 1 sr353 = false := by decide +kernel
private def sr354 : List W := [w9,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r354 : cutRun blocker 10 1 sr354 = false := by decide +kernel
private def sr355 : List W := [w10,w202,w70,w84,w101,w121,w138,w170,w181,w192]
private theorem r355 : cutRun blocker 10 1 sr355 = false := by decide +kernel
private def sr356 : List W := [w14,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r356 : cutRun blocker 10 1 sr356 = false := by decide +kernel
private def sr357 : List W := [w22,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r357 : cutRun blocker 10 1 sr357 = false := by decide +kernel
private def sr358 : List W := [w23,w192,w70,w84,w101,w121,w150,w170,w181,w202]
private theorem r358 : cutRun blocker 10 1 sr358 = false := by decide +kernel
private def sr359 : List W := [w27,w70,w84,w101,w121,w150,w170,w181,w192,w202]
private theorem r359 : cutRun blocker 10 1 sr359 = false := by decide +kernel
private def sr360 : List W := [w27,w162,w84,w101,w121,w150,w170,w181,w192,w202]
private theorem r360 : cutRun blocker 10 1 sr360 = false := by decide +kernel
private def sr361 : List W := [w28,w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r361 : cutRun blocker 10 1 sr361 = false := by decide +kernel
private def sr362 : List W := [w29,w84,w70,w101,w121,w138,w170,w181,w192,w202]
private theorem r362 : cutRun blocker 10 1 sr362 = false := by decide +kernel
private def sr363 : List W := [w29,w162,w70,w101,w121,w138,w170,w181,w192,w202]
private theorem r363 : cutRun blocker 10 1 sr363 = false := by decide +kernel
private def sr364 : List W := [w30,w84,w70,w101,w121,w162,w170,w181,w192,w202]
private theorem r364 : cutRun blocker 10 1 sr364 = false := by decide +kernel
private def sr365 : List W := [w32,w101,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r365 : cutRun blocker 10 1 sr365 = false := by decide +kernel
private def sr366 : List W := [w33,w101,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r366 : cutRun blocker 10 1 sr366 = false := by decide +kernel
private def sr367 : List W := [w35,w121,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r367 : cutRun blocker 10 1 sr367 = false := by decide +kernel
private def sr368 : List W := [w36,w121,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r368 : cutRun blocker 10 1 sr368 = false := by decide +kernel
private def sr369 : List W := [w37,w181,w84,w101,w121,w150,w162,w170,w192,w202]
private theorem r369 : cutRun blocker 10 1 sr369 = false := by decide +kernel
private def sr370 : List W := [w38,w181,w70,w101,w121,w138,w162,w170,w192,w202]
private theorem r370 : cutRun blocker 10 1 sr370 = false := by decide +kernel
private def sr371 : List W := [w41,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r371 : cutRun blocker 10 1 sr371 = false := by decide +kernel
private def sr372 : List W := [w42,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r372 : cutRun blocker 10 1 sr372 = false := by decide +kernel
private def sr373 : List W := [w43,w181,w70,w84,w101,w121,w138,w170,w192,w202]
private theorem r373 : cutRun blocker 10 1 sr373 = false := by decide +kernel
private def sr374 : List W := [w47,w170,w84,w101,w121,w150,w162,w181,w192,w202]
private theorem r374 : cutRun blocker 10 1 sr374 = false := by decide +kernel
private def sr375 : List W := [w48,w170,w70,w101,w121,w138,w162,w181,w192,w202]
private theorem r375 : cutRun blocker 10 1 sr375 = false := by decide +kernel
private def sr376 : List W := [w51,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r376 : cutRun blocker 10 1 sr376 = false := by decide +kernel
private def sr377 : List W := [w52,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r377 : cutRun blocker 10 1 sr377 = false := by decide +kernel
private def sr378 : List W := [w53,w170,w70,w84,w101,w121,w150,w181,w192,w202]
private theorem r378 : cutRun blocker 10 1 sr378 = false := by decide +kernel
private def sr379 : List W := [w63,w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r379 : cutRun blocker 10 1 sr379 = false := by decide +kernel
private def sr380 : List W := [w64,w70,w84,w101,w121,w150,w170,w181,w192,w202]
private theorem r380 : cutRun blocker 10 1 sr380 = false := by decide +kernel
private def sr381 : List W := [w64,w150,w70,w84,w101,w121,w170,w181,w192,w202]
private theorem r381 : cutRun blocker 10 1 sr381 = false := by decide +kernel
private def sr382 : List W := [w64,w162,w70,w84,w101,w121,w170,w181,w192,w202]
private theorem r382 : cutRun blocker 10 1 sr382 = false := by decide +kernel
private def sr383 : List W := [w67,w101,w84,w121,w150,w162,w170,w181,w192,w202]
private theorem r383 : cutRun blocker 10 1 sr383 = false := by decide +kernel
private def sr384 : List W := [w71,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r384 : cutRun blocker 10 1 sr384 = false := by decide +kernel
private def sr385 : List W := [w72,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r385 : cutRun blocker 10 1 sr385 = false := by decide +kernel
private def sr386 : List W := [w73,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r386 : cutRun blocker 10 1 sr386 = false := by decide +kernel
private def sr387 : List W := [w74,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r387 : cutRun blocker 10 1 sr387 = false := by decide +kernel
private def sr388 : List W := [w77,w84,w70,w101,w121,w162,w170,w181,w192,w202]
private theorem r388 : cutRun blocker 10 1 sr388 = false := by decide +kernel
private def sr389 : List W := [w78,w84,w70,w101,w121,w138,w170,w181,w192,w202]
private theorem r389 : cutRun blocker 10 1 sr389 = false := by decide +kernel
private def sr390 : List W := [w78,w138,w70,w84,w101,w121,w170,w181,w192,w202]
private theorem r390 : cutRun blocker 10 1 sr390 = false := by decide +kernel
private def sr391 : List W := [w78,w162,w70,w84,w101,w121,w170,w181,w192,w202]
private theorem r391 : cutRun blocker 10 1 sr391 = false := by decide +kernel
private def sr392 : List W := [w83,w101,w70,w121,w138,w162,w170,w181,w192,w202]
private theorem r392 : cutRun blocker 10 1 sr392 = false := by decide +kernel
private def sr393 : List W := [w86,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r393 : cutRun blocker 10 1 sr393 = false := by decide +kernel
private def sr394 : List W := [w87,w138,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r394 : cutRun blocker 10 1 sr394 = false := by decide +kernel
private def sr395 : List W := [w87,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r395 : cutRun blocker 10 1 sr395 = false := by decide +kernel
private def sr396 : List W := [w88,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r396 : cutRun blocker 10 1 sr396 = false := by decide +kernel
private def sr397 : List W := [w89,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r397 : cutRun blocker 10 1 sr397 = false := by decide +kernel
private def sr398 : List W := [w93,w101,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r398 : cutRun blocker 10 1 sr398 = false := by decide +kernel
private def sr399 : List W := [w94,w101,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r399 : cutRun blocker 10 1 sr399 = false := by decide +kernel
private def sr400 : List W := [w102,w121,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r400 : cutRun blocker 10 1 sr400 = false := by decide +kernel
private def sr401 : List W := [w103,w101,w84,w121,w150,w162,w170,w181,w192,w202]
private theorem r401 : cutRun blocker 10 1 sr401 = false := by decide +kernel
private def sr402 : List W := [w104,w121,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r402 : cutRun blocker 10 1 sr402 = false := by decide +kernel
private def sr403 : List W := [w105,w101,w70,w121,w138,w162,w170,w181,w192,w202]
private theorem r403 : cutRun blocker 10 1 sr403 = false := by decide +kernel
private def sr404 : List W := [w113,w121,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r404 : cutRun blocker 10 1 sr404 = false := by decide +kernel
private def sr405 : List W := [w114,w121,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r405 : cutRun blocker 10 1 sr405 = false := by decide +kernel
private def sr406 : List W := [w123,w101,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r406 : cutRun blocker 10 1 sr406 = false := by decide +kernel
private def sr407 : List W := [w125,w101,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r407 : cutRun blocker 10 1 sr407 = false := by decide +kernel
private def sr408 : List W := [w132,w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r408 : cutRun blocker 10 1 sr408 = false := by decide +kernel
private def sr409 : List W := [w132,w84,w70,w101,w121,w162,w170,w181,w192,w202]
private theorem r409 : cutRun blocker 10 1 sr409 = false := by decide +kernel
private def sr410 : List W := [w134,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r410 : cutRun blocker 10 1 sr410 = false := by decide +kernel
private def sr411 : List W := [w135,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r411 : cutRun blocker 10 1 sr411 = false := by decide +kernel
private def sr412 : List W := [w136,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r412 : cutRun blocker 10 1 sr412 = false := by decide +kernel
private def sr413 : List W := [w137,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r413 : cutRun blocker 10 1 sr413 = false := by decide +kernel
private def sr414 : List W := [w138,w84,w70,w101,w121,w150,w170,w181,w192,w202]
private theorem r414 : cutRun blocker 10 1 sr414 = false := by decide +kernel
private def sr415 : List W := [w139,w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r415 : cutRun blocker 10 1 sr415 = false := by decide +kernel
private def sr416 : List W := [w140,w101,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r416 : cutRun blocker 10 1 sr416 = false := by decide +kernel
private def sr417 : List W := [w141,w121,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r417 : cutRun blocker 10 1 sr417 = false := by decide +kernel
private def sr418 : List W := [w146,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r418 : cutRun blocker 10 1 sr418 = false := by decide +kernel
private def sr419 : List W := [w147,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r419 : cutRun blocker 10 1 sr419 = false := by decide +kernel
private def sr420 : List W := [w148,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r420 : cutRun blocker 10 1 sr420 = false := by decide +kernel
private def sr421 : List W := [w149,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r421 : cutRun blocker 10 1 sr421 = false := by decide +kernel
private def sr422 : List W := [w150,w70,w84,w101,w121,w138,w170,w181,w192,w202]
private theorem r422 : cutRun blocker 10 1 sr422 = false := by decide +kernel
private def sr423 : List W := [w151,w84,w70,w101,w121,w162,w170,w181,w192,w202]
private theorem r423 : cutRun blocker 10 1 sr423 = false := by decide +kernel
private def sr424 : List W := [w152,w101,w70,w84,w121,w162,w170,w181,w192,w202]
private theorem r424 : cutRun blocker 10 1 sr424 = false := by decide +kernel
private def sr425 : List W := [w153,w121,w70,w84,w101,w162,w170,w181,w192,w202]
private theorem r425 : cutRun blocker 10 1 sr425 = false := by decide +kernel
private def sr426 : List W := [w163,w70,w84,w101,w121,w138,w170,w181,w192,w202]
private theorem r426 : cutRun blocker 10 1 sr426 = false := by decide +kernel
private def sr427 : List W := [w163,w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r427 : cutRun blocker 10 1 sr427 = false := by decide +kernel
private def sr428 : List W := [w163,w150,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r428 : cutRun blocker 10 1 sr428 = false := by decide +kernel
private def sr429 : List W := [w163,w162,w84,w101,w121,w150,w170,w181,w192,w202]
private theorem r429 : cutRun blocker 10 1 sr429 = false := by decide +kernel
private def sr430 : List W := [w164,w84,w70,w101,w121,w150,w170,w181,w192,w202]
private theorem r430 : cutRun blocker 10 1 sr430 = false := by decide +kernel
private def sr431 : List W := [w164,w84,w70,w101,w121,w162,w170,w181,w192,w202]
private theorem r431 : cutRun blocker 10 1 sr431 = false := by decide +kernel
private def sr432 : List W := [w164,w138,w70,w101,w121,w162,w170,w181,w192,w202]
private theorem r432 : cutRun blocker 10 1 sr432 = false := by decide +kernel
private def sr433 : List W := [w164,w162,w70,w101,w121,w138,w170,w181,w192,w202]
private theorem r433 : cutRun blocker 10 1 sr433 = false := by decide +kernel
private def sr434 : List W := [w172,w170,w84,w101,w121,w150,w162,w181,w192,w202]
private theorem r434 : cutRun blocker 10 1 sr434 = false := by decide +kernel
private def sr435 : List W := [w173,w170,w70,w101,w121,w138,w162,w181,w192,w202]
private theorem r435 : cutRun blocker 10 1 sr435 = false := by decide +kernel
private def sr436 : List W := [w176,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r436 : cutRun blocker 10 1 sr436 = false := by decide +kernel
private def sr437 : List W := [w177,w170,w70,w84,w101,w121,w162,w181,w192,w202]
private theorem r437 : cutRun blocker 10 1 sr437 = false := by decide +kernel
private def sr438 : List W := [w178,w170,w70,w84,w101,w121,w150,w181,w192,w202]
private theorem r438 : cutRun blocker 10 1 sr438 = false := by decide +kernel
private def sr439 : List W := [w183,w181,w84,w101,w121,w150,w162,w170,w192,w202]
private theorem r439 : cutRun blocker 10 1 sr439 = false := by decide +kernel
private def sr440 : List W := [w184,w181,w70,w101,w121,w138,w162,w170,w192,w202]
private theorem r440 : cutRun blocker 10 1 sr440 = false := by decide +kernel
private def sr441 : List W := [w187,w138,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r441 : cutRun blocker 10 1 sr441 = false := by decide +kernel
private def sr442 : List W := [w187,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r442 : cutRun blocker 10 1 sr442 = false := by decide +kernel
private def sr443 : List W := [w188,w181,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r443 : cutRun blocker 10 1 sr443 = false := by decide +kernel
private def sr444 : List W := [w189,w181,w70,w84,w101,w121,w138,w170,w192,w202]
private theorem r444 : cutRun blocker 10 1 sr444 = false := by decide +kernel
private def sr445 : List W := [w193,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r445 : cutRun blocker 10 1 sr445 = false := by decide +kernel
private def sr446 : List W := [w198,w192,w70,w84,w101,w121,w162,w170,w181,w202]
private theorem r446 : cutRun blocker 10 1 sr446 = false := by decide +kernel
private def sr447 : List W := [w199,w192,w70,w84,w101,w121,w150,w170,w181,w202]
private theorem r447 : cutRun blocker 10 1 sr447 = false := by decide +kernel
private def sr448 : List W := [w208,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r448 : cutRun blocker 10 1 sr448 = false := by decide +kernel
private def sr449 : List W := [w209,w202,w70,w84,w101,w121,w162,w170,w181,w192]
private theorem r449 : cutRun blocker 10 1 sr449 = false := by decide +kernel
private def sr450 : List W := [w210,w202,w70,w84,w101,w121,w138,w170,w181,w192]
private theorem r450 : cutRun blocker 10 1 sr450 = false := by decide +kernel
private def sr451 : List W := [w27,w84,w101,w121,w150,w170,w181,w192,w202]
private theorem r451 : cutRun blocker 10 2 sr451 = false := by decide +kernel
private def sr452 : List W := [w29,w70,w101,w121,w138,w170,w181,w192,w202]
private theorem r452 : cutRun blocker 10 2 sr452 = false := by decide +kernel
private def sr453 : List W := [w87,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r453 : cutRun blocker 10 2 sr453 = false := by decide +kernel
private def sr454 : List W := [w187,w70,w84,w101,w121,w162,w170,w192,w202]
private theorem r454 : cutRun blocker 10 2 sr454 = false := by decide +kernel
private def sr455 : List W := [w10,w27,w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r455 : cutRun blocker 11 1 sr455 = false := by decide +kernel
private def sr456 : List W := [w23,w27,w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r456 : cutRun blocker 11 1 sr456 = false := by decide +kernel
private def sr457 : List W := [w27,w43,w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r457 : cutRun blocker 11 1 sr457 = false := by decide +kernel
private def sr458 : List W := [w27,w53,w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r458 : cutRun blocker 11 1 sr458 = false := by decide +kernel
private def sr459 : List W := [w27,w70,w84,w85,w101,w121,w162,w170,w181,w192,w202]
private theorem r459 : cutRun blocker 11 1 sr459 = false := by decide +kernel
private def sr460 : List W := [w27,w70,w84,w101,w105,w121,w162,w170,w181,w192,w202]
private theorem r460 : cutRun blocker 11 1 sr460 = false := by decide +kernel
private def sr461 : List W := [w27,w70,w84,w101,w106,w121,w162,w170,w181,w192,w202]
private theorem r461 : cutRun blocker 11 1 sr461 = false := by decide +kernel
private def sr462 : List W := [w27,w70,w84,w101,w121,w122,w162,w170,w181,w192,w202]
private theorem r462 : cutRun blocker 11 1 sr462 = false := by decide +kernel
private def sr463 : List W := [w27,w70,w84,w101,w121,w126,w162,w170,w181,w192,w202]
private theorem r463 : cutRun blocker 11 1 sr463 = false := by decide +kernel
private def sr464 : List W := [w27,w70,w84,w101,w121,w127,w162,w170,w181,w192,w202]
private theorem r464 : cutRun blocker 11 1 sr464 = false := by decide +kernel
private def sr465 : List W := [w27,w70,w84,w101,w121,w138,w162,w170,w181,w192,w202]
private theorem r465 : cutRun blocker 11 1 sr465 = false := by decide +kernel
private def sr466 : List W := [w27,w70,w84,w101,w121,w150,w162,w170,w181,w192,w202]
private theorem r466 : cutRun blocker 11 1 sr466 = false := by decide +kernel
private def sr467 : List W := [w27,w70,w84,w101,w121,w162,w170,w171,w181,w192,w202]
private theorem r467 : cutRun blocker 11 1 sr467 = false := by decide +kernel
private def sr468 : List W := [w27,w70,w84,w101,w121,w162,w170,w173,w181,w192,w202]
private theorem r468 : cutRun blocker 11 1 sr468 = false := by decide +kernel
private def sr469 : List W := [w27,w70,w84,w101,w121,w162,w170,w175,w181,w192,w202]
private theorem r469 : cutRun blocker 11 1 sr469 = false := by decide +kernel
private def sr470 : List W := [w27,w70,w84,w101,w121,w162,w170,w181,w182,w192,w202]
private theorem r470 : cutRun blocker 11 1 sr470 = false := by decide +kernel
private def sr471 : List W := [w27,w70,w84,w101,w121,w162,w170,w181,w184,w192,w202]
private theorem r471 : cutRun blocker 11 1 sr471 = false := by decide +kernel
private def sr472 : List W := [w27,w70,w84,w101,w121,w162,w170,w181,w186,w192,w202]
private theorem r472 : cutRun blocker 11 1 sr472 = false := by decide +kernel
private def sr473 : List W := [w27,w70,w84,w101,w121,w162,w170,w181,w190,w192,w202]
private theorem r473 : cutRun blocker 11 1 sr473 = false := by decide +kernel
private def sr474 : List W := [w27,w70,w84,w101,w121,w162,w170,w181,w192,w195,w202]
private theorem r474 : cutRun blocker 11 1 sr474 = false := by decide +kernel
private def sr475 : List W := [w27,w70,w84,w101,w121,w162,w170,w181,w192,w201,w202]
private theorem r475 : cutRun blocker 11 1 sr475 = false := by decide +kernel
private def sr476 : List W := [w27,w70,w84,w101,w121,w162,w170,w181,w192,w202,w203]
private theorem r476 : cutRun blocker 11 1 sr476 = false := by decide +kernel
private def sr477 : List W := [w27,w70,w84,w101,w121,w162,w170,w181,w192,w202,w204]
private theorem r477 : cutRun blocker 11 1 sr477 = false := by decide +kernel
private def sr478 : List W := [w27,w70,w84,w101,w121,w162,w170,w181,w192,w202,w206]
private theorem r478 : cutRun blocker 11 1 sr478 = false := by decide +kernel
private def sr479 : List W := [w27,w70,w84,w101,w121,w162,w170,w181,w192,w202,w211]
private theorem r479 : cutRun blocker 11 1 sr479 = false := by decide +kernel
private def sr480 : List W := [w27,w70,w84,w101,w121,w162,w170,w181,w192,w202,w212]
private theorem r480 : cutRun blocker 11 1 sr480 = false := by decide +kernel
private def sr481 : List W := [w27,w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r481 : cutRun blocker 11 2 sr481 = false := by decide +kernel
private def sr482 : List W := [w27,w84,w101,w121,w150,w162,w170,w181,w192,w202]
private theorem r482 : cutRun blocker 11 2 sr482 = false := by decide +kernel
private def sr483 : List W := [w43,w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r483 : cutRun blocker 11 2 sr483 = false := by decide +kernel
private def sr484 : List W := [w53,w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r484 : cutRun blocker 11 2 sr484 = false := by decide +kernel
private def sr485 : List W := [w70,w84,w85,w101,w121,w162,w170,w181,w192,w202]
private theorem r485 : cutRun blocker 11 2 sr485 = false := by decide +kernel
private def sr486 : List W := [w70,w84,w101,w106,w121,w162,w170,w181,w192,w202]
private theorem r486 : cutRun blocker 11 2 sr486 = false := by decide +kernel
private def sr487 : List W := [w70,w84,w101,w121,w122,w162,w170,w181,w192,w202]
private theorem r487 : cutRun blocker 11 2 sr487 = false := by decide +kernel
private def sr488 : List W := [w70,w84,w101,w121,w138,w162,w170,w181,w192,w202]
set_option maxRecDepth 12000 in
private theorem r488 : cutRun blocker 11 2 sr488 = false := cutCertify [(0,sr31),(0,sr124),(0,sr142),(0,sr154),(0,sr35),(0,sr122),(0,sr166),(0,sr175),(0,sr39),(0,sr120),(0,sr200),(0,sr209),(1,sr379),(0,sr114),(1,sr361),(0,sr54),(1,sr408),(0,sr224),(1,sr415),(0,sr233),(0,sr115),(0,sr52),(1,sr422),(0,sr248),(1,sr426),(0,sr269),(0,sr110),(0,sr84),(0,sr252),(0,sr284),(0,sr112),(0,sr66),(0,sr254),(0,sr300),(0,sr118),(0,sr46),(0,sr256),(0,sr328),(0,sr126),(0,sr8),(0,sr258),(0,sr334),(0,sr4),(1,sr392),(0,sr148),(0,sr172),(1,sr403),(0,sr178),(0,sr12),(0,sr144),(0,sr206),(0,sr212),(1,sr351),(0,sr1),(1,sr431),(1,sr432),(0,sr271),(1,sr389),(0,sr137),(2,sr452),(1,sr362),(1,sr363),(0,sr55),(1,sr433),(0,sr272),(0,sr132),(1,sr375),(0,sr86),(0,sr236),(1,sr435),(0,sr286),(0,sr134),(1,sr370),(0,sr68),(0,sr238),(1,sr440),(0,sr302),(0,sr140),(0,sr33),(0,sr240),(0,sr319),(0,sr146),(0,sr10),(0,sr242),(0,sr336),(0,sr14),(0,sr170),(0,sr204),(0,sr226),(1,sr399),(0,sr161),(1,sr365),(0,sr60),(1,sr406),(0,sr208),(1,sr416),(0,sr234),(0,sr162),(0,sr58),(0,sr214),(0,sr274),(0,sr156),(0,sr88),(0,sr216),(0,sr288),(0,sr158),(0,sr70),(0,sr218),(0,sr304),(0,sr164),(0,sr37),(0,sr220),(0,sr321),(0,sr168),(0,sr16),(0,sr222),(0,sr338),(1,sr405),(0,sr195),(1,sr367),(0,sr64),(1,sr400),(0,sr174),(1,sr417),(0,sr235),(0,sr196),(0,sr62),(0,sr180),(0,sr276),(0,sr190),(0,sr90),(0,sr182),(0,sr290),(0,sr192),(0,sr72),(0,sr184),(0,sr306),(0,sr198),(0,sr41),(0,sr186),(0,sr323),(0,sr202),(0,sr24),(0,sr188),(0,sr346),(1,sr352),(0,sr2),(1,sr390),(1,sr391),(0,sr139),(1,sr410),(0,sr228),(1,sr376),(0,sr92),(1,sr393),(0,sr150),(1,sr436),(0,sr292),(1,sr411),(0,sr229),(1,sr371),(0,sr74),(2,sr453),(1,sr394),(1,sr395),(0,sr151),(2,sr454),(1,sr441),(1,sr442),(0,sr308),(1,sr412),(0,sr230),(1,sr357),(0,sr43),(1,sr396),(0,sr152),(1,sr446),(0,sr325),(1,sr413),(0,sr231),(1,sr353),(0,sr18),(1,sr397),(0,sr153),(1,sr448),(0,sr340),(0,sr260),(0,sr94),(0,sr102),(0,sr294),(0,sr262),(1,sr373),(0,sr76),(0,sr104),(1,sr444),(0,sr310),(0,sr264),(0,sr44),(0,sr106),(0,sr326),(0,sr266),(1,sr355),(0,sr20),(0,sr108),(1,sr450),(0,sr342),(0,sr278),(0,sr78),(0,sr96),(0,sr312),(0,sr280),(0,sr29),(0,sr98),(0,sr317),(0,sr282),(0,sr6),(0,sr100),(0,sr332),(0,sr296),(0,sr48),(0,sr80),(0,sr330),(0,sr298),(0,sr22),(0,sr82),(0,sr344),(0,sr314),(0,sr26),(0,sr50),(0,sr348)] (by decide +kernel) ⟨r31,r124,r142,r154,r35,r122,r166,r175,r39,r120,r200,r209,r379,r114,r361,r54,r408,r224,r415,r233,r115,r52,r422,r248,r426,r269,r110,r84,r252,r284,r112,r66,r254,r300,r118,r46,r256,r328,r126,r8,r258,r334,r4,r392,r148,r172,r403,r178,r12,r144,r206,r212,r351,r1,r431,r432,r271,r389,r137,r452,r362,r363,r55,r433,r272,r132,r375,r86,r236,r435,r286,r134,r370,r68,r238,r440,r302,r140,r33,r240,r319,r146,r10,r242,r336,r14,r170,r204,r226,r399,r161,r365,r60,r406,r208,r416,r234,r162,r58,r214,r274,r156,r88,r216,r288,r158,r70,r218,r304,r164,r37,r220,r321,r168,r16,r222,r338,r405,r195,r367,r64,r400,r174,r417,r235,r196,r62,r180,r276,r190,r90,r182,r290,r192,r72,r184,r306,r198,r41,r186,r323,r202,r24,r188,r346,r352,r2,r390,r391,r139,r410,r228,r376,r92,r393,r150,r436,r292,r411,r229,r371,r74,r453,r394,r395,r151,r454,r441,r442,r308,r412,r230,r357,r43,r396,r152,r446,r325,r413,r231,r353,r18,r397,r153,r448,r340,r260,r94,r102,r294,r262,r373,r76,r104,r444,r310,r264,r44,r106,r326,r266,r355,r20,r108,r450,r342,r278,r78,r96,r312,r280,r29,r98,r317,r282,r6,r100,r332,r296,r48,r80,r330,r298,r22,r82,r344,r314,r26,r50,r348,True.intro⟩
private def sr489 : List W := [w70,w84,w101,w121,w150,w162,w170,w181,w192,w202]
set_option maxRecDepth 12000 in
private theorem r489 : cutRun blocker 11 2 sr489 = false := cutCertify [(0,sr32),(0,sr125),(0,sr143),(0,sr155),(0,sr36),(1,sr383),(0,sr123),(0,sr167),(1,sr401),(0,sr176),(0,sr40),(0,sr121),(0,sr201),(0,sr210),(1,sr350),(0,sr0),(1,sr427),(1,sr428),(0,sr268),(1,sr380),(0,sr116),(2,sr451),(1,sr359),(1,sr360),(0,sr53),(1,sr429),(0,sr270),(0,sr111),(1,sr374),(0,sr85),(0,sr253),(1,sr434),(0,sr285),(0,sr113),(1,sr369),(0,sr67),(0,sr255),(1,sr439),(0,sr301),(0,sr119),(0,sr47),(0,sr257),(0,sr329),(0,sr127),(0,sr9),(0,sr259),(0,sr335),(0,sr5),(0,sr149),(0,sr173),(0,sr179),(0,sr13),(0,sr145),(0,sr207),(0,sr213),(1,sr388),(0,sr136),(1,sr364),(0,sr57),(1,sr409),(0,sr225),(1,sr423),(0,sr249),(0,sr138),(0,sr56),(1,sr414),(0,sr232),(1,sr430),(0,sr273),(0,sr133),(0,sr87),(0,sr237),(0,sr287),(0,sr135),(0,sr69),(0,sr239),(0,sr303),(0,sr141),(0,sr34),(0,sr241),(0,sr320),(0,sr147),(0,sr11),(0,sr243),(0,sr337),(0,sr15),(0,sr171),(0,sr205),(0,sr227),(1,sr398),(0,sr160),(1,sr366),(0,sr61),(1,sr407),(0,sr211),(1,sr424),(0,sr250),(0,sr163),(0,sr59),(0,sr215),(0,sr275),(0,sr157),(0,sr89),(0,sr217),(0,sr289),(0,sr159),(0,sr71),(0,sr219),(0,sr305),(0,sr165),(0,sr38),(0,sr221),(0,sr322),(0,sr169),(0,sr17),(0,sr223),(0,sr339),(1,sr404),(0,sr194),(1,sr368),(0,sr65),(1,sr402),(0,sr177),(1,sr425),(0,sr251),(0,sr197),(0,sr63),(0,sr181),(0,sr277),(0,sr191),(0,sr91),(0,sr183),(0,sr291),(0,sr193),(0,sr73),(0,sr185),(0,sr307),(0,sr199),(0,sr42),(0,sr187),(0,sr324),(0,sr203),(0,sr25),(0,sr189),(0,sr347),(1,sr352),(0,sr3),(1,sr381),(1,sr382),(0,sr117),(1,sr418),(0,sr244),(1,sr377),(0,sr93),(1,sr384),(0,sr128),(1,sr437),(0,sr293),(1,sr419),(0,sr245),(1,sr372),(0,sr75),(1,sr385),(0,sr129),(1,sr443),(0,sr309),(1,sr420),(0,sr246),(1,sr356),(0,sr28),(1,sr386),(0,sr130),(1,sr445),(0,sr316),(1,sr421),(0,sr247),(1,sr354),(0,sr19),(1,sr387),(0,sr131),(1,sr449),(0,sr341),(0,sr261),(1,sr378),(0,sr95),(0,sr103),(1,sr438),(0,sr295),(0,sr263),(0,sr77),(0,sr105),(0,sr311),(0,sr265),(1,sr358),(0,sr45),(0,sr107),(1,sr447),(0,sr327),(0,sr267),(0,sr21),(0,sr109),(0,sr343),(0,sr279),(0,sr79),(0,sr97),(0,sr313),(0,sr281),(0,sr30),(0,sr99),(0,sr318),(0,sr283),(0,sr7),(0,sr101),(0,sr333),(0,sr297),(0,sr49),(0,sr81),(0,sr331),(0,sr299),(0,sr23),(0,sr83),(0,sr345),(0,sr315),(0,sr27),(0,sr51),(0,sr349)] (by decide +kernel) ⟨r32,r125,r143,r155,r36,r383,r123,r167,r401,r176,r40,r121,r201,r210,r350,r0,r427,r428,r268,r380,r116,r451,r359,r360,r53,r429,r270,r111,r374,r85,r253,r434,r285,r113,r369,r67,r255,r439,r301,r119,r47,r257,r329,r127,r9,r259,r335,r5,r149,r173,r179,r13,r145,r207,r213,r388,r136,r364,r57,r409,r225,r423,r249,r138,r56,r414,r232,r430,r273,r133,r87,r237,r287,r135,r69,r239,r303,r141,r34,r241,r320,r147,r11,r243,r337,r15,r171,r205,r227,r398,r160,r366,r61,r407,r211,r424,r250,r163,r59,r215,r275,r157,r89,r217,r289,r159,r71,r219,r305,r165,r38,r221,r322,r169,r17,r223,r339,r404,r194,r368,r65,r402,r177,r425,r251,r197,r63,r181,r277,r191,r91,r183,r291,r193,r73,r185,r307,r199,r42,r187,r324,r203,r25,r189,r347,r352,r3,r381,r382,r117,r418,r244,r377,r93,r384,r128,r437,r293,r419,r245,r372,r75,r385,r129,r443,r309,r420,r246,r356,r28,r386,r130,r445,r316,r421,r247,r354,r19,r387,r131,r449,r341,r261,r378,r95,r103,r438,r295,r263,r77,r105,r311,r265,r358,r45,r107,r447,r327,r267,r21,r109,r343,r279,r79,r97,r313,r281,r30,r99,r318,r283,r7,r101,r333,r297,r49,r81,r331,r299,r23,r83,r345,r315,r27,r51,r349,True.intro⟩
private def sr490 : List W := [w70,w84,w101,w121,w162,w170,w171,w181,w192,w202]
private theorem r490 : cutRun blocker 11 2 sr490 = false := by decide +kernel
private def sr491 : List W := [w70,w84,w101,w121,w162,w170,w181,w182,w192,w202]
private theorem r491 : cutRun blocker 11 2 sr491 = false := by decide +kernel
private def sr492 : List W := [w70,w84,w101,w121,w162,w170,w181,w186,w192,w202]
private theorem r492 : cutRun blocker 11 2 sr492 = false := by decide +kernel
private def sr493 : List W := [w70,w84,w101,w121,w162,w170,w181,w192,w202,w203]
private theorem r493 : cutRun blocker 11 2 sr493 = false := by decide +kernel
private def sr494 : List W := [w70,w84,w101,w121,w162,w170,w181,w192,w202]
private theorem r494 : cutRun blocker 11 3 sr494 = false := by decide +kernel
private def localRoots : List (List W) := [sr494,sr481,sr484,sr458,t4,sr489,sr482,sr466,sr488,sr465,sr483,sr457,sr464,sr486,sr461,sr456,sr455,sr468,sr473,sr469,sr477,sr490,sr467,sr471,sr460,sr463,sr474,sr478,sr485,sr459,sr492,sr472,sr475,sr479,sr491,sr470,sr480,sr487,sr462,sr493,sr476]
private theorem roots_eq : rootReps = localRoots := by decide +kernel
private theorem closeOne (B : Nat → List W → Bool)
    (sound : ∀ n e (ws : List W), ws.Nodup → e + ws.length = n+1 →
      B e ws = true → ¬ live basicOps goal n ws.toFinset)
    (e : Nat) (ws : List W) (hn : ws.Nodup) (room : e+ws.length = 12)
    (h : cutRun B 11 e ws = false) : ¬ live basicOps goal 11 ws.toFinset := by
  intro hl
  exact Bool.noConfusion (h.symm.trans (cutRun_complete B sound 11 ws e hn room hl))
theorem rootReps_dead (sound : ∀ n e (ws : List W), ws.Nodup → e + ws.length = n+1 →
      blocker e ws = true → ¬ live basicOps goal n ws.toFinset) :
      ∀ ws ∈ rootReps, ¬ live basicOps goal 11 ws.toFinset := by
  rw [roots_eq]
  intro ws hm
  simp only [localRoots,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact closeOne blocker sound 3 sr494 (by decide +kernel) (by rfl) r494
  · exact closeOne blocker sound 2 sr481 (by decide +kernel) (by rfl) r481
  · exact closeOne blocker sound 2 sr484 (by decide +kernel) (by rfl) r484
  · exact closeOne blocker sound 1 sr458 (by decide +kernel) (by rfl) r458
  · exact reject_symmetric_prefix 11
  · exact closeOne blocker sound 2 sr489 (by decide +kernel) (by rfl) r489
  · exact closeOne blocker sound 2 sr482 (by decide +kernel) (by rfl) r482
  · exact closeOne blocker sound 1 sr466 (by decide +kernel) (by rfl) r466
  · exact closeOne blocker sound 2 sr488 (by decide +kernel) (by rfl) r488
  · exact closeOne blocker sound 1 sr465 (by decide +kernel) (by rfl) r465
  · exact closeOne blocker sound 2 sr483 (by decide +kernel) (by rfl) r483
  · exact closeOne blocker sound 1 sr457 (by decide +kernel) (by rfl) r457
  · exact closeOne blocker sound 1 sr464 (by decide +kernel) (by rfl) r464
  · exact closeOne blocker sound 2 sr486 (by decide +kernel) (by rfl) r486
  · exact closeOne blocker sound 1 sr461 (by decide +kernel) (by rfl) r461
  · exact closeOne blocker sound 1 sr456 (by decide +kernel) (by rfl) r456
  · exact closeOne blocker sound 1 sr455 (by decide +kernel) (by rfl) r455
  · exact closeOne blocker sound 1 sr468 (by decide +kernel) (by rfl) r468
  · exact closeOne blocker sound 1 sr473 (by decide +kernel) (by rfl) r473
  · exact closeOne blocker sound 1 sr469 (by decide +kernel) (by rfl) r469
  · exact closeOne blocker sound 1 sr477 (by decide +kernel) (by rfl) r477
  · exact closeOne blocker sound 2 sr490 (by decide +kernel) (by rfl) r490
  · exact closeOne blocker sound 1 sr467 (by decide +kernel) (by rfl) r467
  · exact closeOne blocker sound 1 sr471 (by decide +kernel) (by rfl) r471
  · exact closeOne blocker sound 1 sr460 (by decide +kernel) (by rfl) r460
  · exact closeOne blocker sound 1 sr463 (by decide +kernel) (by rfl) r463
  · exact closeOne blocker sound 1 sr474 (by decide +kernel) (by rfl) r474
  · exact closeOne blocker sound 1 sr478 (by decide +kernel) (by rfl) r478
  · exact closeOne blocker sound 2 sr485 (by decide +kernel) (by rfl) r485
  · exact closeOne blocker sound 1 sr459 (by decide +kernel) (by rfl) r459
  · exact closeOne blocker sound 2 sr492 (by decide +kernel) (by rfl) r492
  · exact closeOne blocker sound 1 sr472 (by decide +kernel) (by rfl) r472
  · exact closeOne blocker sound 1 sr475 (by decide +kernel) (by rfl) r475
  · exact closeOne blocker sound 1 sr479 (by decide +kernel) (by rfl) r479
  · exact closeOne blocker sound 2 sr491 (by decide +kernel) (by rfl) r491
  · exact closeOne blocker sound 1 sr470 (by decide +kernel) (by rfl) r470
  · exact closeOne blocker sound 1 sr480 (by decide +kernel) (by rfl) r480
  · exact closeOne blocker sound 2 sr487 (by decide +kernel) (by rfl) r487
  · exact closeOne blocker sound 1 sr462 (by decide +kernel) (by rfl) r462
  · exact closeOne blocker sound 2 sr493 (by decide +kernel) (by rfl) r493
  · exact closeOne blocker sound 1 sr476 (by decide +kernel) (by rfl) r476
end Numeric
end Signed3110

namespace Signed3110
open Signed2964

theorem solved : Exclusion := by
  apply of_representatives
  apply Numeric.rootReps_dead
  intro n e ws nd room hit
  unfold Numeric.blocker at hit
  split at hit
  · exact Projection.not_live_of_probeBlocked n e ws _ nd room hit
  · contradiction

end Signed3110

end PEqualNP.Outside.L_meta_3110

theorem PEqualNP.Outside.L_meta_3110 : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x7 : ℕ) => Bool.false) Bool.false x6.op) x3.gates = (2 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_3110.Signed3110.of_exclusion PEqualNP.Outside.L_meta_3110.Signed3110.solved
