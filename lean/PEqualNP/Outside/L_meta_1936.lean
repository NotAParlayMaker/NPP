import Mathlib
import PEqualNP.Defs

-- Uses the induced-graph bounds of L-meta-1667 and the finite circuit search of L-meta-515.
namespace PEqualNP.Outside.L_meta_1936

namespace ThetaSigned
abbrev Wire (X : Type) := X → Bool
def inv {X : Type} (f : Wire X) : Wire X := fun x => !(f x)
def bit {X : Type} (b : Bool) : Wire X := fun _ => b
def bin {X : Type} (isOr : Bool) (a b : Wire X) : Wire X :=
  fun x => if isOr then a x || b x else a x && b x
def plus {X : Type} (P : Set (Wire X)) (f : Wire X) : Set (Wire X) :=
  {g | g ∈ P ∨ g = f ∨ g = inv f}
def Closed {X : Type} (P : Set (Wire X)) : Prop :=
  (∀ b, bit b ∈ P) ∧ ∀ f ∈ P, inv f ∈ P
theorem inv_inv {X : Type} (f : Wire X) : inv (inv f) = f := by funext x; simp [inv]
theorem plus_closed {X : Type} {P : Set (Wire X)} (hP : Closed P) (f : Wire X) : Closed (plus P f) := by
  refine ⟨fun b => Or.inl (hP.1 b),?_⟩
  intro g hg
  rcases hg with hg|rfl|rfl
  · exact Or.inl (hP.2 _ hg)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (inv_inv _))
inductive Run {X : Type} : Set (Wire X) → ℕ → Wire X → Prop
  | done {P k f} : f ∈ P → Run P k f
  | gate {P k f a b} (isOr : Bool) : a ∈ P → b ∈ P →
      Run (plus P (bin isOr a b)) k f → Run P (k+1) f
end ThetaSigned

namespace P2828
open ThetaSigned
abbrev Y := Fin 9 → Bool
def small : Set (Wire Y) := {f | (∃ c, f=bit c) ∨ ∃ i : Fin 9, f=(fun x => x i) ∨ f=inv (fun x => x i)}
theorem small_closed : Closed small := by
  constructor
  · exact fun b => Or.inl ⟨b,rfl⟩
  · intro f hf
    rcases hf with ⟨b,rfl⟩|⟨i,rfl|rfl⟩
    · exact Or.inl ⟨!b,rfl⟩
    · exact Or.inr ⟨i,Or.inr rfl⟩
    · exact Or.inr ⟨i,Or.inl (inv_inv _)⟩
def nine (y : Y) : Bool := (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5)
end P2828

namespace P2828Live
variable {α : Type} [DecidableEq α]
def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)
def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
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
    (h : live ops goal k s) : s.card ≤ k+1 := by
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
end P2828Live
namespace P2828Live
variable {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
theorem first_live {k : ℕ} {s : Finset α} (h : live ops goal (k+1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,tail⟩
      · exact .inl done
      · exact .inr ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,Or.inl tail⟩
    · exact .inr step
end P2828Live
namespace P2828Check
abbrev W := BitVec 1378
def neg (x : W) : W := ~~~x
def both (x y : W) : W := x &&& y
def canon (x : W) : W := if x.getLsbD 0 then neg x else x
def ops (x y : W) : List W :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
def sep (x : W) := (x ^^^ (x >>> 689)).setWidth 689
def cuts (ws : List W) : BitVec 689 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := canon (((-1 : BitVec 689) ++ (0 : BitVec 689)))
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a,rest) :: (singles rest).map (fun (b,bs) => (b,a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b,bs) => (a,b,bs)) ++
      (pairs rest).map (fun (b,c,bs) => (b,c,a :: bs))
def rawInputs : List W := [0x2aaaaaaaaaabaab555d556bebaab6adb557aad55ebb7daab6ab5575557add7edefb75fef8000000000000000007fffff8000000007ffa900a801202004212000849425ffaab16212008042142480955602a1bfffffffe14015555544d5502048aa4b58100469aaad540804cae850155aaaa02012aae0855a827795115115115115115115115115115115115114805400901002109000424a12ffd558b1090040210a12404aab0150d00000000,
0x333333333332cf399966672b3ccdb36d99acfe66b2fafccdb3de7bf99acee6f6f7dfeb778000000000000007ff8000000000007fffff8200014a000521444ffd11014800100a1444401114c148373ffffffff5560149608188808899228cccb311948060d9860412233359351020c884114ccd6551033a857588208e08e08e08e08e08e08e08e08e08e08e08c10000a5000290a227fe8880a40008050a2220088a60a41b900000000aab00a4b,
0x3c3c3c3c3c3cf3de1e787bcfdf0e3c71e1cf37873cdcef0e3ce79dfe1cf77bf8bae5f3fb0000000000007ff8000000000007fffff800004a321079784e098000260000920020409816e67fffffffee0128cec2012a121e1e021e0206016303042c220f870638f0e598c0864a678702714e33020a84bc457288758c50c50c50c50c50c50c50c50c50c50c50c5002519083cbc2704c000130000490010204c0b733000000007009467610095090,
0x3fc03fc03fc0fc1fe07f83f3eff03f81fe0fc7f83f1f7ff03f07e19fe0f87cbf3cf9fdbd0000000007ff8000000000007fffff8000003390c06382018000049000187120ddcf9fffffffe01871d9c06443010004406041601de015607e00203bc049f07819c00b02633c198098781d82b0ccf0743a439a0c768a01a41a41a41a41a41a41a41a41a41a41a41a59c86031c100c0000248000c38906ee7c0000000000c38ece0322180800220302,
0x3fffc0003fff001fff8003fc0fffc001fff007ffc01f8fffc007fe1fff007f3fc0fe7e3e0000000000000000000007fffff800000000406303804c4e098e092638218007fffff8e0fb3b98a1802208818c0a1bb98f839e9fe0000a9b000fdf8001b40787e000545000c3e0050787e00145030f80051c602109002a4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4a03181c0262704c704931c10c00000000c707d9dcc50c0110440c6050ddcc7c1c,
0x3fffffffc000001ffffffc000ffffffe000007ffffe00ffffff8001fffff803fff007fc07ff8007ff8000000007ff800000000000000007c03fc0f8ff00001c7fffffff8010c00001c3c0000013c0001f00c0001f3fc1e3e6aaa200000030337440007effb96000003f7fb3007afeaa4000fdfed401f7a803d80006c06c06c06c06c06c06c06c06c06c06c06c03e01fe07c7f80000e000000000008600000e1e0000009e0000f8060000f9fe0,
0x3fffffffffffffe0000000000ffffffffffff80000000fffffffffe00000003fffff80000007ff8000000007ff8000000000000000007c7ffc000ff001fffff8003e01c0e1f000009fc0003e01c000f9fff00021fc001f7e777f7766dd7000000000079f2679fbeddc00000007df377beeb00000001cc57a80000370370370370370370370370370370370373e3ffe0007f800000000001f00e070f800004fe0001f00e0007cfff80010fe000,
0x3ffffffffffffffffffffffff00000000000000000000fffffffffffffffffc0000000000000007ff8007ff8000000000000000000007f8000007ffffff00e07c03ffe04fe001f00e0001f3ffe0010fe00001c3e000001c19541ddf9fe9cfcc893ddf00000000000000000000050150ab1c020103b40000000003383383383383383383383383383383383383fc00000000000f80703e01fff027f000f8070000f9fff00087f00000e1f00000,
0x3ffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000007fffff8007ff8000000000000000000000007ffffffff00001fff007ffc0000700001fff00001fc000001f0000001fc00000008180008899008cdcc03bb60800000004100000044f60000000000000000000000000003c03c03c03c03c03c03c03c03c03c03c03c000000000380000fff803ffe0000380000fff80000fe000000f8000000fe000000]
def inputs := rawInputs.map canon
end P2828Check
namespace P2828Check
variable {α : Type}
theorem pick_one {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a,rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a,rest),hm,rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)
theorem pick_two {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a,b,rest) ∈ pairs ws ∨ (b,a,rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b,r),hm,rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r,.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a,r),hm,rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a,b,r),hm,rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b,a,r),hm,rfl⟩))
end P2828Check
namespace P2828Check
abbrev basicOps (a b : W) := (ops a b).toFinset
def differs (i : Fin 689) (w : W) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (689+i.val)
theorem neg_differs (i : Fin 689) (w : W) : differs i (neg w) ↔ differs i w := by
  have lo : i.val < 1378 := by omega
  have hi : 689+i.val < 1378 := by omega
  simp [neg, differs, hi, lo]
theorem canon_differs (i : Fin 689) (w : W) : differs i (canon w) ↔ differs i w := by
  unfold canon
  split <;> simp [neg_differs]
theorem ops_differs (i : Fin 689) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  by_contra! h
  have e₁ : a.getLsbD i.val = a.getLsbD (689+i.val) := by simpa [differs] using h.1
  have e₂ : b.getLsbD i.val = b.getLsbD (689+i.val) := by simpa [differs] using h.2
  have lo : i.val < 1378 := by omega
  have hi : 689+i.val < 1378 := by omega
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [canon_differs] at hd <;>
    simp only [both, neg, differs, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, lo, e₁, e₂] at hd <;> simp_all
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem goal_differs (i : Fin 689) : differs i goal := by
  rw [goal, canon_differs]
  unfold differs
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [i.isLt, show ¬689 + i.val < 689 by omega]
  exact BitVec.getElem_allOnes _ _
theorem cuts_spec (ws : List W) (i : Fin 689) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    simp [sep, i.isLt, differs]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem cuts_full {k : ℕ} {ws : List W} (h : P2828Live.live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := P2828Live.live_separates (differs ⟨j,hj⟩) (goal_differs ⟨j,hj⟩) (ops_differs ⟨j,hj⟩) h
  have hbit := (cuts_spec ws ⟨j,hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 689)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, both, BitVec.and_comm]
  grind [BitVec.and_comm]
end P2828Check
namespace P2828Check
def keepChoices (a b : W) (r : List W) := [r, a::r, b::r, a::b::r]
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simpa [hp.mem_iff] using (hp.mem_iff (a := v))
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a::b::r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a::r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b::r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind
theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc
end P2828Check
namespace P2828Check
private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))
private def bit (k : Fin 1378) (z : W) := z[k.val]
theorem canon_neg (x : W) : canon (~~~x) = canon x := by
  unfold canon neg
  simp only [BitVec.getLsbD_not, BitVec.not_not]
  cases h : x.getLsbD 0 <;> simp [h]
theorem sign (x : W) : x = canon x ∨ x = neg (canon x) := by
  unfold canon neg
  split <;> simp
theorem signed_both {x y a b : W} (hx : x = a ∨ x = neg a) (hy : y = b ∨ y = neg b) :
    canon (x &&& y) ∈ basicOps a b := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp [basicOps, ops, both]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem same_both {x y : W} (eq : canon x = canon y) :
    canon (x &&& y) = canon x ∨ canon (x &&& y) = 0 := by
  have signs : x = y ∨ x = ~~~y := by
    rcases sign x with h|h <;> rcases sign y with j|j <;> rw [eq] at h
    · exact .inl (h.trans j.symm)
    · exact .inr (h.trans (by simpa only [neg, BitVec.not_not] using congrArg (fun v : W => ~~~v) j.symm))
    · exact .inr (h.trans (congrArg neg j.symm))
    · exact .inl (h.trans j.symm)
  rcases signs with rfl|rfl
  · exact .inl (by rw [BitVec.and_self])
  · exact .inr (by rw [BitVec.not_and_self]; decide)
def represents (available : Finset W) (w : List W) :=
  ∀ u ∈ w, canon u = 0 ∨ canon u ∈ available
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    canon z = 0 ∨ canon z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon z ∈ basicOps a b := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x,hx, (h | h) | ⟨y,hy, hh⟩⟩)
  · subst z; left; decide
  · subst z; left; decide
  · subst z; exact (hw _ hx).imp_right Or.inl
  · subst z; rw [canon_neg]; exact (hw _ hx).imp_right Or.inl
  · have andCase (u v : W) (hu : canon u = 0 ∨ canon u ∈ available)
        (hv : canon v = 0 ∨ canon v ∈ available) :
        canon (u &&& v) = 0 ∨ canon (u &&& v) ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon (u &&& v) ∈ basicOps a b := by
      have zeroOrFull (t : W) (h : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 1378 := by
        rcases sign t with h'|h' <;> rw [h] at h'
        · exact .inl h'
        · exact .inr h'
      rcases hu with h | hu
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.zero_and (x := v))).trans (by decide)
        · rw [BitVec.allOnes_and]; exact hv.imp_right Or.inl
      rcases hv with h | hv
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.and_zero (x := u))).trans (by decide)
        · rw [BitVec.and_allOnes]; exact .inr (.inl hu)
      by_cases h : canon u = canon v
      · rcases same_both h with ht|ht
        · exact .inr (.inl (ht ▸ hu))
        · exact .inl ht
      · exact .inr (.inr ⟨_,hu,_,hv,h,signed_both (sign u) (sign v)⟩)
    rcases hh with rfl|rfl
    · exact andCase x y (hw _ hx) (hw _ hy)
    · rw [← canon_neg (x ||| y), BitVec.not_or]
      exact andCase _ _ (by simpa only [canon_neg] using hw _ hx) (by simpa only [canon_neg] using hw _ hy)
open ThetaSigned P2828
def assignment (k : Fin 1378) (i : Fin 9) := bit k (rawInputs.getD i.val 0)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem graph_rows : ∀ k : Fin 1378, nine (assignment k) =
    bit k ((-1 : BitVec 689) ++ (0 : BitVec 689)) := by
  let x := fun (i : Nat) => rawInputs.getD i 0
  let H := (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
  have h : H = ((-1 : BitVec 689) ++ (0 : BitVec 689)) := by decide +kernel
  intro k
  rw [← h]
  simp only [H,bit,BitVec.getElem_or,BitVec.getElem_and]
  have nine_eq : ∀ y : Y, nine y = ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5)) := fun _ => rfl
  exact nine_eq (assignment k)
def rawOps (a b : W) := [both a b, both a (neg b), both (neg a) b, both (neg a) (neg b)]
theorem sep_canon (x : W) : sep (canon x) = sep x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h (v : W) : (sep v)[i] = true ↔ differs ⟨i,hi⟩ v := by
    change (sep v).getLsbD i = true ↔ _
    simp [sep, hi, differs]
  have eq := (h (canon x)).trans ((canon_differs ⟨i,hi⟩ x).trans (h x).symm)
  exact Bool.eq_iff_iff.mpr eq
def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (rawOps a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (canon w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra-1) (canon w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra-1) (canon w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra-2) (canon w :: a :: b :: r))
def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a,b,r) => dispatch extra (optimized k) a b r)
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z::kept) = -1) (ht : next (k-kept.length) (z::kept) = true) :
    dispatch extra next a b r = true := by
  have hmap : ops a b = (rawOps a b).map canon := rfl
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp (hmap ▸ List.mem_toFinset.mp hz)
  apply List.any_eq_true.mpr
  refine ⟨w,hw,?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [cuts, List.foldr_cons, sep_canon] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2 <;> omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1 <;> ac_rfl⟩, by convert ht using 2 <;> omega⟩
end P2828Check
namespace P2828Check
theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : P2828Live.live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases P2828Live.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : P2828Live.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        have hc := P2828Live.live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
end P2828Check

namespace SignedCofactor
open ThetaSigned
def literals (n : Nat) : Set (Wire (Fin n → Bool)) :=
  {f | (∃ c, f=bit c) ∨ ∃ i : Fin n, f=(fun x => x i) ∨ f=inv (fun x => x i)}
theorem literals_closed (n : Nat) : Closed (literals n) := by
  constructor
  · exact fun b => Or.inl ⟨b,rfl⟩
  · intro f hf
    rcases hf with ⟨b,rfl⟩|⟨i,rfl|rfl⟩
    · exact Or.inl ⟨!b,rfl⟩
    · exact Or.inr ⟨i,Or.inr rfl⟩
    · exact Or.inr ⟨i,Or.inl (inv_inv _)⟩
end SignedCofactor

namespace P2828Generic
open P2828Check P2828Live ThetaSigned
def wordBit (r : Fin 1378) (w : W) := w[r.val]
def representsPool {T} (pick : Fin 1378 → T) (P : Set (Wire T)) (S : Finset W) :=
  ∀ f ∈ P, ∃ w, (canon w=0 ∨ canon w ∈ S) ∧ ∀ r, f (pick r)=wordBit r w
private def possibleIn (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))
private theorem singletonPossible {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possibleIn ws x ∧ possibleIn ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possibleIn]
  · simp only [possibleIn, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind
private theorem pairPossible {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possibleIn ws (x &&& y) ∧ possibleIn ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possibleIn] using (show possibleIn ws 0 ∧ possibleIn ws y from ⟨by simp [possibleIn], (singletonPossible hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possibleIn] using (show possibleIn ws 0 ∧ possibleIn ws x from ⟨by simp [possibleIn], (singletonPossible (.inr hx)).1⟩)
  · simp only [possibleIn, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem anyBuild {T : Type} (pick : Fin 1378 → T) {target : Wire T}
    (agrees : ∀ r, target (pick r) = wordBit r goal) {P : Set (Wire T)} {k : Nat} (h : Run P k target) :
    ∀ av, representsPool pick P av → P2828Live.build basicOps goal k av := by
  generalize eqF : target = f at h
  induction h with
  | @done P k f hf =>
    subst f
    intro av rep
    obtain ⟨u,hu,huv⟩ := rep _ hf
    have eq : u = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      exact ((huv ⟨i,hi⟩).symm.trans (agrees ⟨i,hi⟩))
    rw [eq,show canon goal=goal by decide +kernel] at hu
    have ing : goal ∈ av := hu.resolve_left (by decide)
    induction k with
    | zero => exact ing
    | succ k ih => exact Or.inl ih
  | @gate P k f a b op ha hb tail ih =>
    intro av rep
    obtain ⟨u,ru,eu⟩ := rep _ ha
    obtain ⟨v,rv,ev⟩ := rep _ hb
    let z := if op then u ||| v else u &&& v
    have hbits (r) : ThetaSigned.bin op a b (pick r) = wordBit r z := by
      cases op <;> simp [z,ThetaSigned.bin,eu,ev,wordBit]
    have add {av' : Finset W} (sub : av ⊆ av') (has : canon z=0 ∨ canon z ∈ av') :
        representsPool pick (plus P (ThetaSigned.bin op a b)) av' := by
      rintro g (old|rfl|rfl)
      · obtain ⟨w,hw,e⟩ := rep g old
        exact ⟨w,hw.imp_right (fun h => sub h),e⟩
      · exact ⟨_,has,hbits⟩
      · refine ⟨~~~z,by simpa only [canon_neg] using has,?_⟩
        intro r
        simp [ThetaSigned.inv,hbits,wordBit]
    have hws : represents av [u,v] := by
      intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl <;> assumption
    have hz : possibleIn [u,v] z := by
      have hh := pairPossible (ws:=[u,v]) (Or.inr (List.mem_cons_self ..) : u=0 ∨ u∈[u,v])
        (Or.inr (by simp) : v=0 ∨ v∈[u,v])
      cases op <;> first | exact hh.1 | exact hh.2
    rcases classify hws hz with hz|hz|⟨a',ha',b',hb',ne,mem⟩
    · exact Or.inl (ih eqF av (add (fun _ h=>h) (Or.inl hz)))
    · exact Or.inl (ih eqF av (add (fun _ h=>h) (Or.inr hz)))
    · exact Or.inr ⟨a',ha',b',hb',ne,_,mem,ih eqF _ (add (Finset.subset_insert ..) (Or.inr (Finset.mem_insert_self ..)))⟩
def columnPick {n : Nat} (cols : List W) (r : Fin 1378) (i : Fin n) := wordBit r (cols.getD i.val 0)
def signals (cols : List W) := cols.map canon
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem columnGood {n} (cols : List W) (len : cols.length=n) :
    representsPool (columnPick (n:=n) cols) (SignedCofactor.literals n) (signals cols).toFinset := by
  have present (i : Fin n) : canon (cols.getD i.val 0) ∈ (signals cols).toFinset := by
    have h : i.val < cols.length := len ▸ i.isLt
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨_,by rw [List.getD_eq_getElem _ _ h];exact List.getElem_mem ..,rfl⟩
  rintro f (⟨b,rfl⟩|⟨i,rfl|rfl⟩)
  · cases b
    · exact ⟨0,Or.inl (by decide),by simp [ThetaSigned.bit,wordBit]⟩
    · exact ⟨-1,Or.inl (by decide),by intro r; exact (BitVec.getElem_allOnes r.val r.isLt).symm⟩
  · exact ⟨_,Or.inr (present i),fun r=>rfl⟩
  · refine ⟨~~~(cols.getD i.val 0),Or.inr ?_,?_⟩
    · rw [canon_neg];exact present i
    · intro r;simp [inv,columnPick,wordBit]
def critical (ws : List W) (sites : List (Fin 689)) : Bool :=
  ws.all fun a => sites.any fun i => ws.all fun b => (b.getLsbD i.val == b.getLsbD (689+i.val)) || b == a
theorem all_required {ws : List W} {sites} {k s} (crit : critical ws sites=true)
    (hs : s⊆ws.toFinset) (hr : live basicOps goal k s) : s=ws.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  obtain ⟨i,_,all⟩ := List.any_eq_true.mp (List.all_eq_true.mp crit a (List.mem_toFinset.mp ha))
  obtain ⟨b,hb,hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) hr
  have eq := List.all_eq_true.mp all _ (List.mem_toFinset.mp (hs hb))
  simp only [Bool.or_eq_true,beq_iff_eq] at eq
  exact eq.resolve_left hd ▸ hb
end P2828Generic
namespace P2828Check
open ThetaSigned P2828 P2828Generic P2828Live
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem inputLive {k} (h : Run small k nine) : live basicOps goal k inputs.toFinset := by
  have b := anyBuild (columnPick (n:=9) rawInputs) (target:=nine) graph_rows h _ (columnGood rawInputs rfl)
  obtain ⟨s,hs,hl⟩ := compress b
  exact all_required (ws:=inputs) (sites:=[0,32,64,96,128,150,182,204,226]) (by decide +kernel) hs hl ▸ hl
end P2828Check

namespace P2828Live
variable {α β : Type} [DecidableEq α] [DecidableEq β]
def kept (p : α → Option β) (s : Finset α) : Finset β := s.biUnion (fun a => (p a).toFinset)
def zeros (p : α → Option β) (s : Finset α) : ℕ :=
  (s.filter (fun a => p a = none)).card
theorem kept_insert (p : α → Option β) (a : α) (s : Finset α) :
    kept p (insert a s) = (p a).toFinset ∪ kept p s := by
  simp [kept]
theorem zeros_some {p : α → Option β} {a : α} {v : β} (h : p a = some v) (s : Finset α) :
    zeros p (insert a s) = zeros p s := by simp [zeros, Finset.filter_insert, h]
theorem zeros_none {p : α → Option β} {a : α} (h : p a = none) {s : Finset α} (ha : a ∉ s) :
    zeros p (insert a s) = zeros p s + 1 := by simp [zeros, Finset.filter_insert, h, ha]
theorem zeros_le (p : α → Option β) (a : α) (s : Finset α) :
    zeros p (insert a s) ≤ zeros p s + 1 := by
  cases h : p a with
  | some v => rw [zeros_some h]; omega
  | none =>
    by_cases hm : a ∈ s
    · rw [Finset.insert_eq_of_mem hm]; omega
    · exact (zeros_none h hm).le
theorem zeros_mono (p : α → Option β) {s t : Finset α} (h : s ⊆ t) :
    zeros p s ≤ zeros p t := Finset.card_le_card (Finset.filter_subset_filter _ h)
theorem build_mono {ops : β → β → Finset β} {goal : β} {k : ℕ} {s t : Finset β}
    (hs : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hs h
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,tail⟩
    · exact .inl (ih hs skip)
    · exact .inr ⟨a,hs ha,b,hs hb,hab,z,hz,ih (Finset.insert_subset_insert _ hs) tail⟩
def projects (p : α → Option β) (ops : α → α → Finset α) (ops' : β → β → Finset β) : Prop :=
  ∀ a b z, z ∈ ops a b → ∀ v, p z = some v →
    p a = some v ∨ p b = some v ∨
    ∃ u w, p a = some u ∧ p b = some w ∧ u ≠ w ∧ v ∈ ops' u w
theorem zeros_step {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    (P : projects p ops ops') {a b z : α} (hz : z ∈ ops a b) (r : Finset α)
    (fresh : z ∉ insert a (insert b r)) :
    zeros p (insert a (insert b r)) ≤ zeros p (insert z r)+1 := by
  have mono := zeros_mono p (Finset.subset_insert z r)
  cases ha : p a with
  | some u =>
    rw [zeros_some ha]
    have h := zeros_le p b r
    omega
  | none =>
    cases hb : p b with
    | some v =>
      have h := zeros_le p a (insert b r)
      rw [zeros_some hb] at h
      omega
    | none =>
      have hzn : p z = none := by
        cases he : p z with
        | none => rfl
        | some v => simpa [ha, hb] using P a b z hz v he
      have hzout : z ∉ r := by intro h; exact fresh (by simp [h])
      rw [zeros_none hzn hzout]
      have u := zeros_le p a (insert b r)
      have v := zeros_le p b r
      omega
theorem zeros_budget {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) : zeros p s ≤ k := by
  induction k generalizing s with
  | zero => change s = {g} at h; simp [h, zeros, hg]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact (ih skip).trans (by omega)
    · exact (zeros_step P hz r hn).trans (Nat.succ_le_succ (ih tail))
theorem project_live {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) (n : ℕ) (budget : k ≤ n + zeros p s) :
    build ops' g' n (kept p s) := by
  induction k generalizing s n with
  | zero =>
    change s = {g} at h
    have mem : g' ∈ kept p s := by simp [h, kept, hg]
    induction n with
    | zero => exact mem
    | succ n ih => exact Or.inl (ih (by omega))
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact ih skip n (by omega)
    · have dz := zeros_step P hz r hn
      have free (hs : kept p (insert z r) ⊆ kept p (insert a (insert b r))) :
          build ops' g' n (kept p (insert a (insert b r))) :=
        build_mono hs (ih tail n (by omega))
      cases hZ : p z with
      | none =>
        apply free
        simp [kept_insert, hZ]
        exact fun _ hx => Finset.mem_union_right _ (Finset.mem_union_right _ hx)
      | some v =>
        rcases P a b z hz v hZ with ha|hb|⟨u,w,hA,hB,hw,hop⟩
        · apply free
          simp [kept_insert, hZ, ha]
        · apply free
          simp [kept_insert, hZ, hb]
        · rw [zeros_some hA, zeros_some hB] at budget
          have dz' := zeros_some hZ r
          have bound := zeros_budget hg P tail
          cases n with
          | zero => omega
          | succ n =>
            have next := ih tail n (by omega)
            have covers : kept p (insert z r) ⊆ insert v (kept p (insert a (insert b r))) := by
              simp [kept_insert,hZ,hA,hB]
              intro x hx
              simp only [Finset.mem_insert] at hx ⊢
              tauto
            exact Or.inr ⟨u, by simp [kept_insert,hA], w, by simp [kept_insert,hB],
                hw, v, hop, build_mono covers next⟩
end P2828Live

namespace P2828Check
def crop (m : W) (r : Fin 1378) (x : W) : W :=
  (x &&& m) ||| (if x[r.val] then ~~~m else 0)
def pos (m : W) (r : Fin 1378) (i : Nat) := if m.getLsbD i then i else r.val
theorem pos_lt (m : W) (r : Fin 1378) {i} (hi : i < 1378) : pos m r i < 1378 := by
  unfold pos; split <;> omega
theorem crop_bit (m : W) (r : Fin 1378) (x : W) (i : Nat) (hi : i < 1378) :
    (crop m r x).getLsbD i = x.getLsbD (pos m r i) := by
  unfold crop pos
  rw [BitVec.getLsbD_eq_getElem hi (x := m)]
  cases hr : x[r.val] <;> cases hm : m[i] <;> simp [hr,hm,hi]
theorem crop_and (m : W) (r : Fin 1378) (x y : W) :
    crop m r (x &&& y) = crop m r x &&& crop m r y := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (x &&& y)).getLsbD j = (crop m r x &&& crop m r y).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_and]
theorem crop_neg (m : W) (r : Fin 1378) (x : W) :
    crop m r (~~~x) = ~~~crop m r x := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (~~~x)).getLsbD j = (~~~crop m r x).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_not, h, pos_lt _ _ h]
def wrap (x : W) : Option W := if canon x = 0 then none else some (canon x)
theorem wrap_neg (x : W) : wrap (~~~x) = wrap x := by simp only [wrap, canon_neg]
def cropOpt (m : W) (r : Fin 1378) (x : W) := wrap (crop m r x)
theorem crop_canon (m : W) (r : Fin 1378) (x : W) :
    cropOpt m r (canon x) = cropOpt m r x := by
  unfold canon
  split
  · simp only [cropOpt, neg, crop_neg, wrap_neg]
  · rfl
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem binary_project {x y v : W} (h : wrap (x &&& y) = some v) :
    wrap x = some v ∨ wrap y = some v ∨
    ∃ u w, wrap x = some u ∧ wrap y = some w ∧ u ≠ w ∧ v ∈ basicOps u w := by
  have trivial (t : W) (ht : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 1378 := by
    rcases sign t with h'|h' <;> rw [ht] at h'
    · exact .inl h'
    · exact .inr h'
  by_cases hx : canon x = 0
  · rcases trivial _ hx with rfl|rfl
    · rw [show (0 : W) &&& y = 0 from BitVec.zero_and] at h
      have h0 : wrap 0 = none := by decide
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.allOnes_and] at h; exact .inr (.inl h)
  by_cases hy : canon y = 0
  · rcases trivial _ hy with rfl|rfl
    · rw [show x &&& (0 : W) = 0 from BitVec.and_zero] at h
      have h0 : wrap 0 = none := by decide
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.and_allOnes] at h; exact .inl h
  have hn : canon (x &&& y) ≠ 0 := by intro hn; simp [wrap, hn] at h
  have hval : canon (x &&& y) = v := by simpa only [wrap, if_neg hn, Option.some.injEq] using h
  by_cases eq : canon x = canon y
  · rcases same_both eq with same|bad
    · exact .inl (by simp only [wrap, if_neg hx, ← hval, same])
    · exact False.elim (hn bad)
  · exact .inr (.inr ⟨canon x,canon y,by simp only [wrap,if_neg hx],by simp only [wrap,if_neg hy],eq,
        hval ▸ signed_both (sign x) (sign y)⟩)
theorem mask_projects (m : W) (r : Fin 1378) : P2828Live.projects (cropOpt m r) basicOps basicOps := by
  intro a b z hz v hv
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [crop_canon] at hv <;> simp only [cropOpt, both, neg, crop_and, crop_neg] at hv ⊢ <;>
    simpa only [wrap_neg] using binary_project hv
def projectedBudget (m : W) (r : Fin 1378) (n : Nat) (ws : List W) : Nat :=
  n - (ws.filter (fun w => (cropOpt m r w).isNone)).length
def available (m : W) (r : Fin 1378) (ws : List W) : List W :=
  (ws.filterMap (cropOpt m r)).dedup
theorem projected_bound (m : W) (r : Fin 1378) (n : Nat) {ws : List W} (hn : ws.Nodup) :
    n ≤ projectedBudget m r n ws + P2828Live.zeros (cropOpt m r) ws.toFinset := by
  let xs := ws.filter (fun w => (cropOpt m r w).isNone)
  have eq : (xs.toFinset) = ws.toFinset.filter (fun w => cropOpt m r w = none) := by
    ext w; simp [xs]
  have card := List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist :
    xs.Sublist ws))
  rw [eq] at card
  change (ws.toFinset.filter (fun w => cropOpt m r w = none)).card = xs.length at card
  change n ≤ n-xs.length + (ws.toFinset.filter (fun w => cropOpt m r w = none)).card
  omega
end P2828Check

namespace P2828Check
open ThetaSigned
variable {T : Type}
def interpret (pick : T → Fin 1378) (w : W) : Wire T := fun x => w.getLsbD (pick x).val
theorem interpret_neg (pick : T → Fin 1378) (w : W) : interpret pick (neg w) = inv (interpret pick w) := by
  funext x
  simp [neg,interpret,inv,(pick x).isLt]
theorem interpret_canon (pick : T → Fin 1378) (w : W) :
    interpret pick (canon w) = interpret pick w ∨ interpret pick (canon w) = inv (interpret pick w) := by
  unfold canon; split
  · exact Or.inr (interpret_neg _ _)
  · exact Or.inl rfl
theorem interpret_both (pick : T → Fin 1378) (a b : W) :
    interpret pick (both a b) = bin false (interpret pick a) (interpret pick b) := by
  funext x;simp [interpret,both,bin]
theorem Run_pad {P : Set (Wire T)} {k f} (h : Run P k f) : Run P (k+1) f := by
  induction h with
  | done hf => exact .done hf
  | gate op ha hb _ ih => exact .gate op ha hb ih
theorem Run_inv {P : Set (Wire T)} {k f} (h : Run P k f) (hc : Closed P) : Run P k (inv f) := by
  induction h with
  | done hf => exact .done (hc.2 _ hf)
  | gate op ha hb _ ih => exact .gate op ha hb (ih (plus_closed hc _))
theorem decode_build (pick : T → Fin 1378) {g k s} (h : P2828Live.build basicOps g k s)
    {P : Set (Wire T)} (hp : Closed P) (raw : ∀ a ∈ s, interpret pick a ∈ P) :
    Run P k (interpret pick g) := by
  induction k generalizing s P with
  | zero => exact .done (raw _ h)
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,_,z,hz,ht⟩
    · exact Run_pad (ih skip hp raw)
    · have put {s₁ s₂ : W} (ha' : interpret pick s₁ ∈ P) (hb' : interpret pick s₂ ∈ P)
          (ed : z = canon (both s₁ s₂)) : Run P (k+1) (interpret pick g) := by
        apply Run.gate false ha' hb'
        apply ih ht (plus_closed hp _)
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hv
        · rcases interpret_canon pick (both s₁ s₂) with same|opp
          · exact Or.inr (Or.inl (ed ▸ same.trans (interpret_both _ _ _)))
          · exact Or.inr (Or.inr (ed ▸ opp.trans (congrArg inv (interpret_both _ _ _))))
        · exact Or.inl (raw _ hv)
      have an : interpret pick (neg a) ∈ P := interpret_neg pick a ▸ hp.2 _ (raw _ ha)
      have bn : interpret pick (neg b) ∈ P := interpret_neg pick b ▸ hp.2 _ (raw _ hb)
      simp [basicOps,ops] at hz
      rcases hz with hz|hz|hz|hz
      · exact put (raw _ ha) (raw _ hb) hz
      · exact put (raw _ ha) bn hz
      · exact put an (raw _ hb) hz
      · exact put an bn hz
end P2828Check

namespace P2828Live
variable {α β : Type} [DecidableEq α] [DecidableEq β]
inductive History (ops : α → α → Finset α) (start : Finset α) : Finset α → Prop where
  | initial : History ops start start
  | gate {s} (old : History ops start s) {a b z} (ha : a ∈ s) (hb : b ∈ s)
      (hz : z ∈ ops a b) : History ops start (insert z s)
theorem History.contains {ops : α → α → Finset α} {start s} (h : History ops start s) : start ⊆ s := by
  induction h with
  | initial => exact Finset.Subset.refl _
  | gate old ha hb hz ih => exact ih.trans (Finset.subset_insert _ _)
theorem kept_mono (p : α → Option β) {s t : Finset α} (h : s ⊆ t) : kept p s ⊆ kept p t := by
  intro v hv
  obtain ⟨x,hx,px⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨x,h hx,px⟩
theorem kept_of {p : α → Option β} {s : Finset α} {a : α} {v : β} (ha : a ∈ s) (hp : p a = some v) :
    v ∈ kept p s := Finset.mem_biUnion.mpr ⟨a,ha,by simp [hp]⟩
def price (p : α → Option β) (start s : Finset α) := (kept p s \ kept p start).card
theorem History.compose {ops : α → α → Finset α} {ops' : β → β → Finset β} {p : α → Option β}
    (proj : projects p ops ops') {start s} (h : History ops start s) {g : β} {k : ℕ}
    (tail : build ops' g k (kept p s)) : build ops' g (k + price p start s) (kept p start) := by
  induction h generalizing k with
  | initial => simpa [price] using tail
  | @gate s old a b z ha hb hz ih =>
    cases eq : p z with
    | none => simpa [price,kept_insert,eq] using ih (by simpa [kept_insert,eq] using tail)
    | some v =>
      have avail : kept p (insert z s) = insert v (kept p s) := by simp [kept_insert,eq]
      by_cases dup : v ∈ kept p s
      · rw [Finset.insert_eq_of_mem dup] at avail
        simpa [price,avail] using ih (avail ▸ tail)
      · have nv : v ∉ kept p start := fun hv => dup (kept_mono p old.contains hv)
        have cost : price p start (insert z s) = price p start s + 1 := by
          simp [price,avail,Finset.insert_sdiff_of_notMem, nv,dup]
        obtain ea|eb|⟨u,w,eu,ew,ne,mem⟩ := proj a b z hz v eq
        · exact (dup (kept_of ha ea)).elim
        · exact (dup (kept_of hb eb)).elim
        · have t : build ops' g (k+1) (kept p s) :=
            Or.inr ⟨u,kept_of ha eu,w,kept_of hb ew,ne,v,mem,avail ▸ tail⟩
          simpa [cost,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih t
theorem face_budget {ops : α → α → Finset α} {ops' : β → β → Finset β} {p : α → Option β}
    (proj : projects p ops ops') {start hist s g g' k} (past : History ops start hist)
    (pool : s ⊆ hist) (target : p g = some g') (run : live ops g k s) :
    build ops' g' (k - zeros p s + price p start hist) (kept p start) := by
  apply past.compose proj
  apply build_mono (kept_mono p pool)
  exact project_live target proj run _ (by omega)
end P2828Live

namespace P2828Check
open P2828 ThetaSigned
private def rowPages : Array Nat := #[0x888bd179af2564004118415a6b481102156200010192,0x89312223b1588cc519a31388ab555a80456800d59802,0x898be225af75740255c808894b595c00756e0195b005,0x8a51462831989ec622731789ab5d5e80c57802d5d80a,0x8a914d7dafa5bab701602b5b6b68150295b2b6014027,0x8b716a2cb1d8b115d9db1c8acb7d5f80e8aab795f00d,0x8c31822fafc8bcb89610118bab85608108b8b816000f,0x8d31a233b208cd1963231f8c6b91620138c4b8d61812,0x8d6c0980b0058c0541a84f8d4bfd7f2fd58a0501a04c,0x8e51c63846f8dcc899fb218dac123630359005d63816,0x8f71ea3cc788eed49a8b508ed1d63a3828e6d3da734d,0x91121e4348590920e414819011fe3f3878fad523e353,0x91922d843075d4ba41c838915225833055d0b9c1b836,0x92d2564a493925245a1b2392123e4730991abad64818,0x9432824fc9e93b271ac35793726a4cb8c93125dab355,0x95f2ba56cac9572aa54ca894f29a52b8f94928e51359,0x9652c594327960c9992b245dcbb41e83c5940641d873,0x9712de5b32b96acaa5a329966bbd6681c59806d6581a,0x9833025fcbe97ae6a5e3999772e9af35d972d71adb5a,0x99d336664cb995326644c798d31662361986d826135f,0x9af35a6acd49a7349d1ba29a3341ba37399edc9b8b70,0x9c938e714e19c137e6f4dd9b936e6d3779b2dda6c375,0x9e33c277cee9db3b275ba89d53a6743a79cf39a72ba6,0x9ff3fa7ecfc9f73ea7ccf89ef3da7abaa9e93ce793a9,0xa0b41281d02a02cb996b2ca00c3986b0c59c0741f85b,0xa1b43285d0aa12cc28432fa0ec428330f5a007d6781e,0xa354668c517a2d4568a513a254468850fa1cd91b1b62,0xa5149e93525a4948e91521a4147e8f51da38d9a8db65,0xa674ca98d30a5f4b9d8bb0a5b4b295d2aa52de9bcb78,0xa835029fd3ea7b4f29dd3aa734e29bd36a6adf29a37b,0xaa3542a7d4ea9b532a5d4aa93522a3d46a8b512a1d42,0xac3582afd5eabb572add5aab3562abd56aab552a9d52]
private def rowAt (i : Nat) : Fin 1378 := Fin.ofNat 1378 (((rowPages.getD (i/16) 0) >>> (11*(i % 16))) &&& 2047)
private def bits (x : Y) : BitVec 9 := (BitVec.ofBoolListLE (List.ofFn x)).setWidth 9
private theorem bits_spec (x : Y) (i : Fin 9) : (bits x).getLsbD i.val = x i := by
  simp only [bits,BitVec.getLsbD_setWidth,decide_eq_true i.isLt,Bool.true_and,BitVec.getLsbD_ofBoolListLE]
  fin_cases i <;> rfl
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem row_ok : ∀ (v : Fin 512) (i : Fin 9),
  assignment (rowAt v.val) i = (BitVec.ofNat 9 v.val).getLsbD i.val := by decide +kernel
def chooseRow (x : Y) := rowAt (bits x).toNat
theorem chooseRow_spec (x : Y) : assignment (chooseRow x)=x := by
  funext i
  have e := row_ok ⟨(bits x).toNat,(bits x).isLt⟩ i
  simpa only [chooseRow, BitVec.ofNat_toNat, BitVec.setWidth_eq, bits_spec] using e
end P2828Check

namespace P2828Check
open P2828 ThetaSigned P2828Live
def pin (fixed values : BitVec 9) (y : Y) : Y := fun i =>
  if fixed.getLsbD i.val then values.getLsbD i.val else y i
def faceMaskList (fixed values : BitVec 9) : List (Fin 9) → W
  | [] => BitVec.allOnes 1378
  | i :: is =>
    let rest := faceMaskList fixed values is
    let column := rawInputs.getD i.val 0
    if fixed.getLsbD i.val then
      (if values.getLsbD i.val then column else neg column) &&& rest
    else rest
def faceMask (fixed values : BitVec 9) := faceMaskList fixed values (List.finRange 9)
def pickFace (f v : BitVec 9) (y : Y) := chooseRow (pin f v y)
theorem pickFace_row (f v : BitVec 9) (y : Y) : assignment (pickFace f v y) = pin f v y := chooseRow_spec _
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem pickFace_inside (f v : BitVec 9) (y : Y) :
    (faceMask f v).getLsbD (pickFace f v y).val = true := by
  let r := pickFace f v y
  have val (i : Fin 9) : (rawInputs.getD i.val 0).getLsbD r.val = pin f v y i := by
    exact congrFun (pickFace_row f v y) i
  have go : ∀ is : List (Fin 9), (faceMaskList f v is).getLsbD r.val = true := by
    intro is
    induction is with
    | nil => simp only [faceMaskList,BitVec.getLsbD_allOnes,decide_eq_true r.isLt]
    | cons i is ih =>
      cases hi : f.getLsbD i.val <;> cases hv : v.getLsbD i.val <;>
        simp only [faceMaskList,hi,hv,Bool.false_eq_true,if_false,if_true,neg,BitVec.getLsbD_and,
          BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and,val,pin,ih] <;> rfl
  exact go _
theorem interpret_crop (f v : BitVec 9) (r : Fin 1378) (w : W) :
    interpret (pickFace f v) (crop (faceMask f v) r w) = interpret (pickFace f v) w := by
  funext y
  simp only [interpret,crop_bit _ _ _ _ (pickFace f v y).isLt,pos,pickFace_inside,if_true]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem interpret_raw (f v : BitVec 9) (i : Fin 9) : interpret (pickFace f v) (rawInputs.getD i.val 0) ∈ small := by
  have eq : interpret (pickFace f v) (rawInputs.getD i.val 0) = fun y => pin f v y i := by
    funext y;exact congrFun (pickFace_row f v y) i
  rw [eq]
  unfold pin
  split
  · exact small_closed.1 _
  · exact Or.inr ⟨i,Or.inl rfl⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem decoded_kept (f v : BitVec 9) (r : Fin 1378) :
    ∀ w ∈ kept (cropOpt (faceMask f v) r) inputs.toFinset, interpret (pickFace f v) w ∈ small := by
  intro w hw
  obtain ⟨a,ha,hw⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨raw,mem,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  obtain ⟨i,hi,ei⟩ := List.getElem_of_mem mem
  have len : rawInputs.length = 9 := rfl
  have e : rawInputs.getD i 0 = raw := by rw [List.getD_eq_getElem _ _ hi];exact ei
  have hh : interpret (pickFace f v) raw ∈ small := e ▸ interpret_raw f v ⟨i,by omega⟩
  have hh' : cropOpt (faceMask f v) r (canon raw) = some w := by simpa using hw
  rw [crop_canon] at hh'
  unfold cropOpt wrap at hh'
  split at hh'
  · contradiction
  obtain rfl := Option.some.inj hh'
  rcases interpret_canon (pickFace f v) (crop (faceMask f v) r raw) with hs|hs <;>
    rw [hs,interpret_crop] <;> first | exact hh | exact small_closed.2 _ hh
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem interpret_goal (f v : BitVec 9) : interpret (pickFace f v) goal = fun y => nine (pin f v y) := by
  have hg : goal = ((-1 : BitVec 689) ++ (0 : BitVec 689)) := by decide +kernel
  funext y
  have z := graph_rows (pickFace f v y)
  rw [pickFace_row] at z
  rw [hg]
  exact z.symm
end P2828Check

namespace P2828Check
open P2828 ThetaSigned P2828Live
structure Face where
  fixed : BitVec 9
  values : BitVec 9
  lower : ℕ
  mask : W
  anchor : Fin 1378
def Face.Valid (c : Face) : Prop := c.mask = faceMask c.fixed c.values ∧
    (∃ g, cropOpt c.mask c.anchor goal = some g) ∧
    ∀ k, Run small k (fun y => nine (pin c.fixed c.values y)) → c.lower ≤ k
end P2828Check

namespace P2828Minor
open P2828Check P2828Live P2828Generic ThetaSigned
structure Minor where
  lower : Nat
  mask : W
  anchor : Fin 1378
def Minor.Valid (c : Minor) (base : List W) : Prop :=
  ∃ g, cropOpt c.mask c.anchor goal = some g ∧
    ∀ k, build basicOps g k (kept (cropOpt c.mask c.anchor) base.toFinset) → c.lower ≤ k
theorem transfer {T : Type} (base : List W) (c : Minor) (pick : T → Fin 1378)
    (inside : ∀ t, c.mask.getLsbD (pick t).val = true) (P : Set (Wire T)) (closed : Closed P)
    (raw : ∀ w ∈ base, interpret pick w ∈ P) (F : Wire T)
    (target : interpret pick goal = F) (someGoal : ∃ g, cropOpt c.mask c.anchor goal = some g)
    (lower : ∀ k, Run P k F → c.lower ≤ k) : c.Valid base := by
  obtain ⟨g,hg⟩ := someGoal
  refine ⟨g,hg,?_⟩
  intro k proof
  have same (w : W) : interpret pick (crop c.mask c.anchor w) = interpret pick w := by
    funext y
    simp only [interpret,crop_bit _ _ _ _ (pick y).isLt,pos,inside,if_true]
  have image (u v : W) (ev : cropOpt c.mask c.anchor u = some v) :
      interpret pick v = interpret pick u ∨ interpret pick v = inv (interpret pick u) := by
    unfold cropOpt wrap at ev
    split at ev
    · contradiction
    obtain rfl := Option.some.inj ev
    simpa only [same] using interpret_canon pick (crop c.mask c.anchor u)
  have haveRaw (w : W) (hw : w ∈ kept (cropOpt c.mask c.anchor) base.toFinset) : interpret pick w ∈ P := by
    obtain ⟨u,hu,m⟩ := Finset.mem_biUnion.mp hw
    have pr : cropOpt c.mask c.anchor u = some w := by simpa using m
    rcases image u w pr with e|e
    · rw [e]; exact raw _ (List.mem_toFinset.mp hu)
    · rw [e]; exact closed.2 _ (raw _ (List.mem_toFinset.mp hu))
  have yes := decode_build pick proof closed haveRaw
  apply lower k
  rcases image goal g hg with e|e
  · rwa [e,target] at yes
  · rw [e,target] at yes
    simpa only [inv_inv] using Run_inv yes closed
def seen (base h : List W) := h.toFinset ∪ base.toFinset
def rejects (base : List W) (c : Minor) (k : ℕ) (ws hist : List W) : Bool :=
  let p := cropOpt c.mask c.anchor
  decide (k - zeros p ws.toFinset + price p base.toFinset (seen base hist) < c.lower)
theorem safe {base c k ws hist} (valid : Minor.Valid c base)
    (past : History basicOps base.toFinset (seen base hist)) (pool : ws.toFinset ⊆ seen base hist)
    (run : live basicOps goal k ws.toFinset) : rejects base c k ws hist = false := by
  obtain ⟨g,hg,lower⟩ := valid
  exact decide_eq_false (Nat.not_lt.mpr (lower _ (face_budget (mask_projects _ _) past pool hg run)))
theorem ofOrdinary (c : Face) (valid : c.Valid) : Minor.Valid ⟨c.lower,c.mask,c.anchor⟩ inputs := by
  obtain ⟨em,⟨g,hg⟩,bound⟩ := valid
  refine ⟨g,hg,?_⟩
  rw [em] at hg ⊢
  intro k h
  have decoded := decode_build (pickFace c.fixed c.values) h P2828.small_closed (decoded_kept _ _ _)
  apply bound k
  unfold cropOpt wrap at hg
  split at hg
  · contradiction
  obtain rfl := Option.some.inj hg
  rcases interpret_canon (pickFace c.fixed c.values) (crop (faceMask c.fixed c.values) c.anchor goal) with e|e <;>
    rw [e,interpret_crop,interpret_goal] at decoded
  · exact decoded
  · simpa only [inv_inv] using Run_inv decoded P2828.small_closed
end P2828Minor

namespace P2828Check
open P2828Live
def gone (p : W → Option W) (ws : List W) := (ws.filter fun w => (p w).isNone).length
def paid (p : W → Option W) (ws : List W) (base : List W) :=
  ((ws.filterMap p).filter (fun z => !base.contains z)).dedup.length
theorem gone_eq (p : W → Option W) {ws : List W} (hn : ws.Nodup) : gone p ws = zeros p ws.toFinset := by
  unfold gone zeros
  rw [← List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist ..))]
  congr 1
  ext a
  simp [Option.isNone_iff_eq_none]
end P2828Check

namespace P2828Check
def limited (m : W) (r : Fin 1378) (w : W) : W := (if w[r.val] then ~~~w else w) &&& m
theorem limited_anchor (m : W) (r : Fin 1378) (w : W) : (limited m r w)[r.val] = false := by
  cases e : w[r.val] <;> simp [limited,e]
theorem limited_crop (m : W) (r : Fin 1378) (w : W) :
    canon (crop m r w) = canon (limited m r w) := by
  cases e : w[r.val] with
  | false => simp [crop,limited,e]
  | true =>
    have eq : crop m r w = ~~~(limited m r w) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp only [crop,limited,e,ite_true,BitVec.getElem_or,BitVec.getElem_and,BitVec.getElem_not]
      cases w[i] <;> cases m[i] <;> rfl
    rw [eq,canon_neg]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem limited_zero (m : W) (r : Fin 1378) (w : W) :
    canon (limited m r w) = 0 ↔ limited m r w = 0 := by
  constructor
  · intro h
    rcases sign (limited m r w) with a|a
    · exact a.trans h
    · rw [h] at a
      have e := congrArg (fun z : W => z[r.val]) a
      rw [limited_anchor] at e
      exact False.elim (Bool.noConfusion (e.trans (BitVec.getElem_allOnes _ _)))
  · rintro h;rw [h];decide
def projectFast (m : W) (r : Fin 1378) (w : W) : Option W :=
  let q := limited m r w
  if q=0 then none else some (canon q)
theorem projectFast_eq (m : W) (r : Fin 1378) : projectFast m r = cropOpt m r := by
  funext w
  simp only [projectFast,cropOpt,wrap,limited_crop,limited_zero]
end P2828Check

namespace P2828Minor
open P2828Check P2828Live
private theorem kept_list (p : W → Option W) (ws : List W) :
    kept p ws.toFinset = (ws.filterMap p).toFinset := by
  ext a; simp [kept,List.mem_filterMap]
theorem price_eq (base : List W) (p : W → Option W) (hist : List W) :
    paid p hist (base.filterMap p) = price p base.toFinset (seen base hist) := by
  let h := (hist.filterMap p).filter fun z => !(base.filterMap p).contains z
  change h.dedup.length = _
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup _),List.toFinset_dedup]
  unfold price seen
  rw [show kept p (hist.toFinset ∪ base.toFinset) = kept p hist.toFinset ∪ kept p base.toFinset by
    ext a; simp [kept, or_and_right, exists_or]]
  rw [kept_list,kept_list]
  congr 1
  ext a
  simp [h]
def cheap (base : List W) (c : Minor) (k : Nat) (ws hist : List W) : Bool :=
  let p := projectFast c.mask c.anchor
  let rem := k - (ws.filter (fun w => limited c.mask c.anchor w == 0)).length
  if c.lower ≤ rem then false else
    decide (rem + paid p hist (base.filterMap p) < c.lower)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem cheap_eq (base : List W) (c : Minor) (k : Nat) (ws hist : List W) (hn : ws.Nodup) :
    cheap base c k ws hist = rejects base c k ws hist := by
  have columns (w : W) : (projectFast c.mask c.anchor w).isNone = (limited c.mask c.anchor w == 0) := by
    let z := limited c.mask c.anchor w
    change (if z=0 then none else some (canon z)).isNone = (z == 0)
    by_cases hz : z=0
    · rw [if_pos hz,hz];rfl
    · rw [if_neg hz];exact (beq_eq_false_iff_ne.mpr hz).symm
  change _ = decide (_ < _)
  rw [← projectFast_eq,←gone_eq _ hn,← price_eq]
  unfold cheap gone
  simp only [columns]
  split
  · symm; apply decide_eq_false;omega
  · rfl
end P2828Minor

namespace P2828Truth
open P2828Check P2828Minor P2828Live P2828Generic ThetaSigned SignedCofactor
def index {n} (x : Fin n → Bool) : Nat :=
  (List.finRange n).foldl (fun a i => a + if x i then 2^i.val else 0) 0
def truth (n t : Nat) (x : Fin n → Bool) := t.testBit (index x)
def select {n} (map : Array (Fin 1378)) (x : Fin n → Bool) : Fin 1378 := map.getD (index x) 0
def literal {n} (w : Wire (Fin n → Bool)) : Prop :=
  (∃ b : Bool, ∀ x, w x=b) ∨ ∃ i : Fin n, ∃ b : Bool, ∀ x, w x = (x i != b)
instance {n} (w : Wire (Fin n → Bool)) : Decidable (literal w) := by unfold literal;infer_instance
theorem mem_literal {n w} (hw : @literal n w) : w ∈ literals n := by
  rcases hw with ⟨b,e⟩|⟨i,b,e⟩
  · exact Or.inl ⟨b,funext e⟩
  · refine Or.inr ⟨i,?_⟩
    cases b
    · exact Or.inl (funext fun x => by simpa using e x)
    · exact Or.inr (funext fun x => by simpa [inv] using e x)
theorem validates {n t} (base : List W) (c : Minor) (rows : Array (Fin 1378))
    (inside : ∀ x : Fin n → Bool, c.mask.getLsbD (select rows x).val=true)
    (raw : base.all (fun w => decide (literal (interpret (@select n rows) w))) = true)
    (target : ∀ x : Fin n → Bool, interpret (select rows) goal x = truth n t x)
    (someGoal : ∃ g, cropOpt c.mask c.anchor goal = some g)
    (lower : ∀ k, Run (literals n) k (truth n t) → c.lower ≤ k) : c.Valid base := by
  apply transfer base c (select rows) inside _ (literals_closed n) _ _ (funext target) someGoal lower
  intro w hw
  exact mem_literal (of_decide_eq_true (List.all_eq_true.mp raw w hw))
theorem table_live {n k t} (cols : List W) (sites : List (Fin 689))
    (len : cols.length=n) (agrees : ∀ r : Fin 1378, truth n t (columnPick cols r) = wordBit r goal)
    (crit : critical (signals cols) sites=true) (run : Run (literals n) k (truth n t)) :
    live basicOps goal k (signals cols).toFinset := by
  obtain ⟨s,hs,hr⟩ := compress (anyBuild _ agrees run _ (columnGood cols len))
  exact all_required crit hs hr ▸ hr
theorem table_lower {n t cap extra k : Nat} (cols : List W) (sites : List (Fin 689))
    (len : cols.length=n) (agrees : ∀ r : Fin 1378, truth n t (columnPick cols r) = wordBit r goal)
    (crit : critical (signals cols) sites=true) (nodup : (signals cols).Nodup)
    (room : extra + (signals cols).length = cap+1) (scan : optimized cap extra (signals cols) = false)
    (run : Run (literals n) k (truth n t)) : cap+1 ≤ k := by
  by_contra! tooSmall
  have hl := table_live cols sites len agrees crit run
  have pad (k' : Nat) (h : k≤k') : live basicOps goal k' (signals cols).toFinset := by
    induction h with
    | refl => exact hl
    | step _ ih => exact Or.inl ih
  have yes := optimized_complete cap _ extra nodup room (pad _ (by omega))
  exact Bool.noConfusion (yes.symm.trans scan)
end P2828Truth

namespace C4Base
open ThetaSigned
abbrev Y := Fin 7 → Bool
def small : Set (Wire Y) := {f | (∃ c, f=bit c) ∨ ∃ i : Fin 7, f=(fun x => x i) ∨ f=inv (fun x => x i)}
def nine (y : Y) : Bool := (y 0 && y 1) || (y 2 && y 4) || (y 0 && y 5) || (y 2 && y 5) || (y 3 && y 5) || (y 1 && y 6) || (y 3 && y 6) || (y 4 && y 6)
theorem small_closed : Closed small := by
  constructor
  · exact fun b => Or.inl ⟨b,rfl⟩
  · intro f hf
    rcases hf with ⟨b,rfl⟩|⟨i,rfl|rfl⟩
    · exact Or.inl ⟨!b,rfl⟩
    · exact Or.inr ⟨i,Or.inr rfl⟩
    · exact Or.inr ⟨i,Or.inl (inv_inv _)⟩
end C4Base

namespace UnifiedSearch
open P2828Minor P2828Check P2828Live
def widen (v : Nat) : W :=
  let copy := fun x : Nat => x + (if x.testBit 0 then (((1<<<457)-1)<<<232) else 0)
  BitVec.ofNat 1378 (copy (v % (1<<<232)) ||| (copy (v>>>232) <<< 689))
abbrev Advice := List W → List W → List Minor
def checkChild (base : List W) (ad : Advice) (further : ℕ → List W → List W → Bool) (k : ℕ)
    (ws hist : List W) (extra : ℕ) (child : List W) : Bool :=
  match child with
  | [] => false
  | z :: _ => !(ws.contains z) && !((ad ws hist).any (fun c => cheap base c k child (z::hist))) &&
      further extra child (z::hist)
def guided (base : List W) (ad : Advice) : ℕ → ℕ → List W → List W → Bool
  | 0, _, ws, _ => ws == [goal]
  | k+1, extra, ws, hist => ws == [goal] ||
    let more := checkChild base ad (guided base ad k) k ws hist
    (pairs ws).any (fun (a,b,r) => dispatch extra more a b r)
theorem guided_complete (base : List W) (ad : Advice) (valid : ∀ ws hist, ∀ c ∈ ad ws hist, c.Valid base)
    (n : ℕ) (ws hist : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (past : History basicOps base.toFinset (seen base hist))
    (pool : ws.toFinset ⊆ seen base hist) (h : live basicOps goal n ws.toFinset) :
    guided base ad n extra ws hist = true := by
  induction n generalizing ws hist extra with
  | zero => simp [guided,singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [guided,singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have extendSeen : seen base (z::hist) = insert z (seen base hist) := by simp [P2828Minor.seen]
      have extended : History basicOps base.toFinset (seen base (z::hist)) := extendSeen ▸ .gate past (pool ha) (pool hb) hz
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (checkChild base ad (guided base ad k) k ws hist) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have sub : kept.toFinset ⊆ ws.toFinset := by rw [hfin,hset];exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨fun hv => hout (sub (List.mem_toFinset.mpr hv)),hnk⟩
        have hl : live basicOps goal k (z::kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd,List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) _ hop hk (by omega) (by omega) (cuts_full hl)
        have pool' : (z::kept).toFinset ⊆ seen base (z::hist) := by
          rw [extendSeen,List.toFinset_cons]; exact Finset.insert_subset_insert _ (sub.trans pool)
        have succ := ih _ _ (k-kept.length) hnd (by simp;omega) extended pool' hl
        have none : (ad ws hist).any (fun c => cheap base c k (z::kept) (z::hist)) = false :=
          List.any_eq_false.mpr fun c hc => by rw [cheap_eq _ _ _ _ _ hnd,safe (valid _ _ c hc) extended pool' hl]; decide
        have fresh : z ∉ ws := by simpa using hout
        simp [checkChild,fresh,none,succ]
      simp only [guided,Bool.or_eq_true,List.any_eq_true]
      right
      rcases hm with direct|swap
      · exact ⟨(a,b,r),direct,go hp hs hz⟩
      · exact ⟨(b,a,r),swap,go (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
end UnifiedSearch
namespace UnifiedLeaf0
open UnifiedSearch (widen)
open P2828Check P2828Live P2828Generic P2828Truth P2828Minor ThetaSigned SignedCofactor
def cols : List W := [(widen 0x9fdebe96753d7f9fcf4797e96fffc94c4d978adc1243e73f76be7852f3e020416080c308a089c09803102602003301184c18c02070349c380073),(widen 0x3dbf723bf2ffa5c837fa6ba7269ebfc7fba78763c9f61af58bdc8aae7c42408e4209021800488010166061a85442a48200158000cc85dc000e7c),(widen 0xf73357f53f7f5cbfedceb09cf38bc4bbdf4c7efcb71e899d50ef15cf9108ce0c0a1000a248003a045846812884442c02a026360509806001cf80),(widen 0x67eebf238ed7dfa5b4fdfe7f0fffa166e033a616603d7fe37df5e1f4261815009c500c040b2414016084985081840a649140245e034021c1f000),(widen 0x4ef7d7cbfd4fab639a1b29fff1aa3ff9d7df7921efcce810dbf9ff09483100300402e844b22104e980091e010110135009880898127a01fe0000)]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 6 2 (signals cols)=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower (k) (run : Run (literals 5) k (truth 5 0xfefceea0)) : 7≤k :=
  table_lower (cap:=6) (extra:=2) cols [7,13,0,1,3] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) scan run
end UnifiedLeaf0
namespace UnifiedLeaf1
open UnifiedSearch (widen)
open P2828Check P2828Live P2828Generic P2828Truth P2828Minor ThetaSigned SignedCofactor
def cols : List W := [(widen 0x7fe00bf047d607f5013f806ff8223faedea87f16055dbf1e38494f83c77f807381870001f0021f0000f8003f800e003820304cae0e38000781c3),(widen 0xf768245a7ed6a04cb9d9a418129df4ec0de7ef01af97f7224bc7389e4d8060047038d6080500c08090005dc029209787080b93500001c7381e0c),(widen 0xd2db6695ab2d20de0eac75c9a7729255859f12ccd9e6de4fc092913ff0088824558100a0464626241815620b440c9810005046ce0fc000001ff0),(widen 0x8fc6de0ce0635c3d6684cfc4ad8651f0737db9ae0bf8fa8495f83fe490a140c208501b4d090090c0c02081500271238dac09b8300001f83fe000),(widen 0xb1b18db3611f33831c6333236bf1ce33f343485e57ff1cf921ffc2092200010820609c40019800db0302898033b142c01e0fb110f001ffc00000),(widen 0x8f8fb38e9f00fe70fde70f1f188fc18830c0c1e3f3ffe0ffff24245008420230828200b212ed231d0d5c02238004405052b04480fffe00000000)]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 7 2 (signals cols)=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower (k) (run : Run (literals 6) k (truth 6 0xfffeffccfafaf888)) : 8≤k :=
  table_lower (cap:=7) (extra:=2) cols [2,0,13,4,1,3] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) scan run
end UnifiedLeaf1
namespace UnifiedLeaf2
open UnifiedSearch (widen)
open P2828Check P2828Live P2828Generic P2828Truth P2828Minor ThetaSigned SignedCofactor
def cols : List W := [(widen 0xffffffffffffffffffffffffffffffffffffffffffdfd7fe57d3e7f57bffffffffffffffffffffffffffffffffffffffffff20340081500c601b),(widen 0xba79cbfd2e5daadc00000000000000000000000000000000000000000044a43a34101b60dc),(widen 0xffffffffffffffffffffffffffffffffffffffffff3ff45d4fd633bce9000000000000000000000000000000000000000000c20ad2260ea28ce0),(widen 0xed7ffbbcedfcef960000000000000000000000000000000000000000001240840a88c08f00)]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 3 0 (signals cols)=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower (k) (run : Run (literals 4) k (truth 4 0xeea0)) : 4≤k :=
  table_lower (cap:=3) (extra:=0) cols [5,9,0,1] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) scan run
end UnifiedLeaf2
namespace UnifiedLeaf3
open UnifiedSearch (widen)
open P2828Check P2828Live P2828Generic P2828Truth P2828Minor ThetaSigned SignedCofactor
def cols : List W := [(widen 0x7a023fb020ffe829ff437f8447f9a1f647fc17c85d6ff8e0f0f0f1c737700c3c000c3f8040fe083f8007f000f007e063839d6fb8e0707070c31),(widen 0x48a93fbb5a2106b26c3e62453bf2b9cef3fdc137a7e7fc9279393935d708a01c3b0230068160144800bb8095e05b81c0848221000038383831c6),(widen 0x4d64d4c699a3538dd68ea38ee5296f46de8aa9ddd8fb5bf012527fc1f848f6c040582107cd93ca6242c40d29ce4c020134d87b5bf000003fc1f8),(widen 0xac1c7211b758ceedc19790bb0ca7e0f3afa665f893fc7124bfc03ffe008458280db3782c85cb1483a902a021b0bf9565e491fc70003fc03ffe00),(widen 0x9b63b24f8fc6399c326d8d9fe399e7319e9e1ac84eff9a493fffd240a81000322e23c0301000158d2d1300c63191d800c8078480003fffc00000),(widen 0xf71f4dc07f7df87bf1e37c791f8710f341807e03fa7fe3ffe4a4a4ab04610340804c04416a10623050044f000600000a01280203ffc000000000)]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 6 1 (signals cols)=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower (k) (run : Run (literals 6) k (truth 6 0xffffffccf8f88888)) : 7≤k :=
  table_lower (cap:=6) (extra:=1) cols [1,0,22,39,3,2] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) scan run
end UnifiedLeaf3
namespace UnifiedC4
open UnifiedSearch (widen)
open P2828Check P2828Live P2828Generic P2828Truth P2828Minor ThetaSigned SignedCofactor
def cols : List W := [(widen 0x507619494848240f0e83fb98007ac0be8fc384922aa4aa49400495ffff003e38000000000f0f83fff8003fc07f80c004922aa4aa49400495f800),(widen 0xa2120815d8690b2b023eaa88056a6c8abfc2d924c449009014a93ffabf00000001f87801f0003c000007c03f803f005924c449009014a90002bf),(widen 0x30bac2258c801200107ffbaf58003b5b51540038b071ccfd81ffd8500a003fc00000000000003ffffff8003fffc0000038b071ccfd800018500a),(widen 0x50124ba0112dd5fa07fffcfe6bf000062a80e3f077e00e3fe0e01602c00000000000001fff03fffffffffc00000000e3f077e00e0000e01602c),(widen 0xc82240c1ee84618fdb6f330d4800091344106fc007801ffc18cfc1833000000001ff8001ffffc000000000000000006fc00780000018cfc18330),(widen 0xf1fc9703fd577f1dacb7c3f674b3b27c001f70003ffff0021ff02007c0ffc00001fffffe00000000000000000000007000000010021ff02007c0),(widen 0xfe3f27fdf66781eecf3bfc07873c3c6038207ffff8001f03e1003e0400fffffffe0000000000000000000000000000000038001f03e1003e0400)]
def base := signals cols
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem root {k} (h : Run C4Base.small k C4Base.nine) : live basicOps goal k base.toFinset := by
  have eq : ∀ x, C4Base.nine x=truth 7 0xfffffffeffffffccfffafffaf8f88888 x := by decide +kernel
  exact table_live cols [0,11,22,33,42,53,70] (by decide +kernel) (by decide +kernel) (by decide +kernel) ((funext eq) ▸ h)
def face0 : Minor := ⟨7,(widen 0xd89e6a22796d0d0f1400467fa851341403c224911125526ab52400000ffc1c7fe0787fe00f0400007f8000000403fa24911125526ab526a0540),6⟩
def pick0 : Array (Fin 1378) := #[87,42,57,45,22,711,25,714,6,717,722,749,8,719,724,823,17,19,726,728,737,739,770,825,10,721,730,826,741,883,856,827]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid0 : face0.Valid base := validates (n:=5) (t:=0xfefceea0) base face0 pick0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf0.lower
def face1 : Minor := ⟨7,(widen 0x7453d1a117b8c7024800450a7ffc4a4aaab9007480e20026600262cc5ffc03ffe007ffe000000000007ffc0003fff9007480e33026730262cc5),0⟩
def pick1 : Array (Fin 1378) := #[87,11,57,13,0,689,2,691,6,695,722,747,7,696,723,810,17,18,726,727,706,707,763,812,10,699,730,813,710,879,819,814]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid1 : face1.Valid base := validates (n:=5) (t:=0xfefceea0) base face1 pick1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf0.lower
def face2 : Minor := ⟨8,(widen 0xfafedb45feed22a05f8000301940ffff9d57f1c0f881ff1c01f1fe9fd3fffffffffffffe000fc0000000003ffffffff1c0f881ff1ffff1fe9fd3),0⟩
def pick2 : Array (Fin 1378) := #[87,11,0,689,42,12,1,690,22,15,4,693,711,712,713,794,6,695,7,696,717,744,718,796,8,697,9,698,719,797,720,884,17,18,706,707,19,20,708,709,737,738,769,850,739,740,804,906,10,699,710,879,721,758,806,909,741,852,775,887,883,910,888,889]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid2 : face2.Valid base := validates (n:=6) (t:=0xfffeffccfafaf888) base face2 pick2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf1.lower
def face3 : Minor := ⟨4,(widen 0xd0124822316c0d0e1000440a285000000282241010211022a00000000ffc007fe0787fe00f040000000000000003fa241010211022b52620540),6⟩
def pick3 : Array (Fin 1378) := #[87,57,22,25,6,722,8,724,17,726,737,770,10,730,741,856]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid3 : face3.Valid base := validates (n:=4) (t:=0xeea0) base face3 pick3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face4 : Minor := ⟨4,(widen 0xc0980000080200008000301040c28c814780000001e00000300018c300000000007ffe000000000000003fffffff9000c001e01c06300018c3),0⟩
def pick4 : Array (Fin 1378) := #[87,11,42,12,0,689,1,690,6,695,717,744,7,696,718,796]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid4 : face4.Valid base := validates (n:=4) (t:=0xeea0) base face4 pick4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face5 : Minor := ⟨4,(widen 0x240000000000000800000000001140003880000001800018500a003fc00000000000003ffffff8003fffc0000038b071ccfd800018500a),1⟩
def pick5 : Array (Fin 1378) := #[42,19,12,20,45,728,14,729,1,708,690,709,3,766,692,836]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid5 : face5.Valid base := validates (n:=4) (t:=0xeea0) base face5 pick5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face6 : Minor := ⟨4,(widen 0xa000004000000000000000000000449009014a900000000000001f87801f0003c000007c03f803f005924c449009014a90002bf),0⟩
def pick6 : Array (Fin 1378) := #[0,1,2,3,4,713,5,716,7,718,723,751,9,720,725,843]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid6 : face6.Valid base := validates (n:=4) (t:=0xeea0) base face6 pick6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face7 : Minor := ⟨4,(widen 0x480000000000001000000000000000049200000a494004800000003e38000000000f0f83fff8003fc07f80c004922aa4aa49400495f800),11⟩
def pick7 : Array (Fin 1378) := #[11,18,12,20,13,727,14,729,15,738,712,740,16,771,715,837]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid7 : face7.Valid base := validates (n:=4) (t:=0xeea0) base face7 pick7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face8 : Minor := ⟨4,(widen 0x600100000000000000000400000007800000180001833000000001ff8001ffffc000000000000000006fc00780000018cfc18330),4⟩
def pick8 : Array (Fin 1378) := #[22,15,25,16,4,693,5,694,8,697,724,754,9,698,725,857]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid8 : face8.Valid base := validates (n:=4) (t:=0xeea0) base face8 pick8
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face9 : Minor := ⟨4,(widen 0xa00400402a000a05100000009000d0110000140c000051400014a00000001c7fe000000000040000000003f807f3f8140d0014514a0014a0013),0⟩
def pick9 : Array (Fin 1378) := #[87,22,0,4,42,711,1,713,17,737,706,769,19,739,708,804]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid9 : face9.Valid base := validates (n:=4) (t:=0xeea0) base face9 pick9
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face10 : Minor := ⟨4,(widen 0xc0d000008020001080003018008315001500000080e00c0050c00140000000000787fe000fc000000000007fc0ffa0c00080e00c0a50c09940),6⟩
def pick10 : Array (Fin 1378) := #[87,42,11,12,22,711,15,712,6,717,695,744,8,719,697,797]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid10 : face10.Valid base := validates (n:=4) (t:=0xeea0) base face10 pick10
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face11 : Minor := ⟨4,(widen 0xa000840022800a043000000014044808c0081c040000300000006881100003ffe000000000fc00000000000003fff81c0488023006001c68811),0⟩
def pick11 : Array (Fin 1378) := #[87,17,11,18,22,737,15,738,0,706,689,707,4,769,693,850]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid11 : face11.Valid base := validates (n:=4) (t:=0xeea0) base face11 pick11
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face12 : Minor := ⟨4,(widen 0x545350a0112845024800450a295802400290003080620026200000440ffc03ffe0007fe0000000000003fc00000ff8003080633026310262c40),6⟩
def pick12 : Array (Fin 1378) := #[87,57,11,13,17,726,18,727,6,722,695,747,10,730,699,813]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid12 : face12.Valid base := validates (n:=4) (t:=0xeea0) base face12 pick12
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face13 : Minor := ⟨4,(widen 0x589a6220112905020000462b2851240002c000910124002a310000000ffc1c7fe0007fe0000000007f8000000403f800910125526a3102a0440),6⟩
def pick13 : Array (Fin 1378) := #[87,57,42,45,17,726,19,728,6,722,717,749,10,730,721,826]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid13 : face13.Valid base := validates (n:=4) (t:=0xeea0) base face13 pick13
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face14 : Minor := ⟨7,(widen 0xe0368fc02a880e253483c098b4c4d83ffe08fffc0000ffde00fdff83f003ffffe000001ffffffffffffffffffffff8fffffffeffde00fdff83f),0⟩
def pick14 : Array (Fin 1378) := #[87,11,0,689,42,12,1,690,57,13,2,691,45,14,3,692,22,15,4,693,711,712,713,794,25,16,5,694,714,715,716,828,17,18,706,707,19,20,708,709,726,727,763,812,728,729,766,836,737,738,769,850,739,740,804,906,770,771,772,858,825,837,844,838]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid14 : face14.Valid base := validates (n:=6) (t:=0xffffffccf8f88888) base face14 pick14
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf3.lower
def face15 : Minor := ⟨7,(widen 0x1c0d80209987e1130c403f878c3c39fc7df800007ffe0fc1effc1fbff00000001ffffffffffffffffffffffffffffffffc7ffe0fc1effc1fbff),0⟩
def pick15 : Array (Fin 1378) := #[87,0,11,689,22,4,15,693,57,2,13,691,25,5,16,694,42,1,12,690,711,713,712,794,45,3,14,692,714,716,715,828,6,7,695,696,8,9,697,698,722,723,747,810,724,725,754,857,717,718,744,796,719,720,797,884,749,751,750,832,823,843,833,834]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid15 : face15.Valid base := validates (n:=6) (t:=0xffffffccf8f88888) base face15 pick15
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf3.lower
def face16 : Minor := ⟨4,(widen 0x70124121133887020000440a785040020281005400a00022600220000ffc007fe007ffe000000000007c000003f3f9005400a110227302204c5),0⟩
def pick16 : Array (Fin 1378) := #[87,57,0,2,6,722,7,723,17,726,706,763,10,730,710,819]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid16 : face16.Valid base := validates (n:=4) (t:=0xeea0) base face16 pick16
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face17 : Minor := ⟨4,(widen 0x888c20026840080510000201800134100142040100055040150400000ffc1c7fe0787fe000040000000000000403fa04010005506ab506a0540),6⟩
def pick17 : Array (Fin 1378) := #[87,42,17,19,6,717,10,721,22,711,737,739,8,719,741,883]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid17 : face17.Valid base := validates (n:=4) (t:=0xeea0) base face17 pick17
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face18 : Minor := ⟨4,(widen 0x244190010690020048000100140c4a488039000480020000000260cc1ffc03ffe007ffe0000000000000000003fff9000480033026730260cc1),0⟩
def pick18 : Array (Fin 1378) := #[87,11,17,18,6,695,10,699,0,689,706,707,7,696,710,879]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid18 : face18.Valid base := validates (n:=4) (t:=0xeea0) base face18 pick18
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face19 : Minor := ⟨4,(widen 0xc0160a0028080c0514004018a0401014020024900000524a0024000000001c7fe00000000f0400007f8000000403f824911124524a0024a0000),17⟩
def pick19 : Array (Fin 1378) := #[87,17,42,19,57,726,45,728,22,737,711,739,25,770,714,825]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid19 : face19.Valid base := validates (n:=4) (t:=0xeea0) base face19 pick19
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face20 : Minor := ⟨4,(widen 0x60128180028806000000400834c4480aaa0800740000000600006280500003ffe000000000000000007ffc0003fff8007480e23006000062805),0⟩
def pick20 : Array (Fin 1378) := #[87,17,11,18,57,726,13,727,0,706,689,707,2,763,691,812]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid20 : face20.Valid base := validates (n:=4) (t:=0xeea0) base face20 pick20
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face21 : Minor := ⟨4,(widen 0x180c002019050103040006078810301401c0000011240240a52400000000000000787fe00f0400007f8000000403fa249011240240a52400140),6⟩
def pick21 : Array (Fin 1378) := #[87,42,57,45,22,711,25,714,6,717,722,749,8,719,724,823]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid21 : face21.Valid base := validates (n:=4) (t:=0xeea0) base face21 pick21
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def face22 : Minor := ⟨4,(widen 0x140180201180c102080005020c3c084828b8000000e200006000028c500000000007ffe000000000007ffc0003fff9007400e200006300028c5),0⟩
def pick22 : Array (Fin 1378) := #[87,11,57,13,0,689,2,691,6,695,722,747,7,696,723,810]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid22 : face22.Valid base := validates (n:=4) (t:=0xeea0) base face22 pick22
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) UnifiedLeaf2.lower
def faces : Array Minor := #[face0,face1,face2,face3,face4,face5,face6,face7,face8,face9,face10,face11,face12,face13,face14,face15,face16,face17,face18,face19,face20,face21,face22]
def faceAt (i : Fin 23) := faces[i.val]
theorem valid (i : Fin 23) : (faceAt i).Valid base := by
  fin_cases i
  · exact valid0
  · exact valid1
  · exact valid2
  · exact valid3
  · exact valid4
  · exact valid5
  · exact valid6
  · exact valid7
  · exact valid8
  · exact valid9
  · exact valid10
  · exact valid11
  · exact valid12
  · exact valid13
  · exact valid14
  · exact valid15
  · exact valid16
  · exact valid17
  · exact valid18
  · exact valid19
  · exact valid20
  · exact valid21
  · exact valid22
def masks : Array Nat := #[0x57,0x113,0x0,0x202,0x2,0x1067,0xc23f,0x3,0x8277,0x1,0x4,0xf7,0x827,0xe3,0x215,0x1e7,0x224,0xce7,0x117,0x286,0x12,0x6,0x22,0x317,0x2f,0x1b3,0x60,0x227,0x441,0x287,0x10,0x1a7,0xc72,0xa3,0x41,0x23,0x36,0x150,0x1d7,0x5,0x9f7,0x7,0x111,0x81f7,0x1a3,0x67,0x2af,0x4c7,0x81,0x177,0x917,0x9b7,0x282,0x291,0xc7,0x517,0x9d7,0x2b4,0x4cb7,0x8b57,0x687,0x183,0x1a57,0xc1,0xab,0x800,0x237,0x6f,0x140,0x2187,0x15,0xc7f7,0x100,0x8217,0x5c1,0x244,0x46,0x80b7,0x4ef,0x43a7,0x80,0x417,0x102,0xf17,0x8a17,0x11,0xe1,0x210,0x3d7,0x82,0x8197,0x16b,0x257,0x285,0x110,0xa17,0x43,0xc157,0x822,0x4a07,0x357,0x37,0x8157,0x2c7,0x3e7,0x2a0,0x4e7,0x153,0x8a6,0x887,0x681,0x4000,0x83f7,0x977,0x4727,0x127,0x27,0x4215,0x26,0x3f,0xc355,0x577,0x97,0x40c7,0x25,0xd7,0x137,0x8b97,0x8127,0xb7,0x2d5,0x116,0x17,0x337,0xc457,0x2b7,0xd04,0x4177,0x143,0x2e7,0x810,0x40a7,0x63,0xe7,0x880,0x217,0x20,0x157,0x14b,0xc27,0xba7,0x8a7,0x132,0xaa7,0xc4f6,0x53,0x447,0x1467,0x45,0x77,0x82f7,0xd37,0xb37,0x4b77,0x4437,0x200,0x957,0x47,0x4245,0x477,0x11a7,0x804,0xc807,0x457,0xaf,0x541,0x197,0x2a7,0x81d7,0x823,0x373,0x267,0x8417,0x820,0x41a7,0x416,0x220,0xae7,0x142,0x8b7,0x5c7,0x437,0x84f7,0x44,0x8097,0xd3,0x42a7,0x1b7,0x2197,0x42,0xd1,0x8c7,0xe67,0xce13,0x52f,0xa7,0xa5f,0x8117,0x443,0x8dd7,0xe17,0x67f,0x20b7,0x867,0x2c5,0xa1,0x5f,0xe87,0x81b7,0x2d7,0x2a1,0xc2a7,0x105,0x485,0x4467,0x1f7,0x8877,0x986,0x6b,0x84,0x300,0x55,0x1bf,0x557,0x401,0x4337,0x3a7,0xbf7,0x46f,0x8057,0x4cf,0x4c5,0x685,0x87,0x8237,0x6c7,0x297,0x2f7,0x2ff,0x8317,0xc9f7,0x440,0xc117,0x400,0x1ac7,0xc1f7,0x826,0x3b7,0x280,0x85,0x41b7,0x40,0x4bef,0x42b7,0x391,0xa6f,0x1f3,0x4306,0x913,0x201,0x226,0x445,0xaf7,0x923,0x404,0x122,0x42ef,0xe97,0x57f,0x21af,0x1047,0xa0,0x4c1,0x922,0x22f,0x13,0x4f7,0x8977,0x42e7,0x937,0x936,0x24,0xc004,0x4127,0x8b37,0x6bf,0x7f,0x123,0x8000,0x5d7,0x3bf,0x7d7,0x4d27,0x43e7,0x877]
def pages : Array Nat := #[0x884004020103c1c0a0683016040100814090100804040401c0c04028100602010080200,0x1208c44090100842200107c0e1e010083a020a870361a0c80830170105804150a04c2402,0x1c01004371b0d46807198c8620201010602f010b85a02000b0562a148600828138984a09,0x491c8c0a228000844218d88441200087e041f0f4040202008043c1d8082a3a1c8080402,0x1008a80e01008a65228808a0020113c121627134040201130444b021280e00010089248,0x30144be040a808bc5d2e16c82022d02c0402011645c31290100e582b888ac55028081802,0x11a80469340082a6702198040232808046431808042d011888661010244e18138080402,0x3b1d4e8023980884720214804020a1c40470378083a6e36808046c0a8840427358c00402,0x5140fe7e01008087d3e008040701008f66d24008e82d3d0080802111e40878010081277,0x1024a40245a291288438c004860121404840201106020219d04744089c0004400080402,0x1008ce0216a44129105240a08f472340e2933854fc4301008120203808040246010ec3f,0x500886994c2104e090125c8602048252c7401008041f0100804024aa3d2802498080892,0x5088404a0350093e32010093c3101024049d0108c0402010083a0201270ba154d8093436,0x54aa00402020080409539ec04a601295482301008040203808449c51899260204a880402,0x5a2c0eb4011496604010096427492c5608a022bc04ae010115a155609c1202192ad5493,0x5f0597abc35808046b5d80862ba0d8c172b85b809229c090242a04010516cb5048081231,0x100804c601008000262b1042c30101c088a61008306a04b0404c00100804bf049801202,0x678259ccd0133004020201d9631650086cc9011bd900256808120a0d8258e09010086002,0x10083c736b35404d4010090a0201008040269809a40201344084301009a00c010081402,0x18388126070811c0020100808df010d860026f37446026e36db4666c809b0d7180080402,0x2822804020109c04e801008a40266b9c04e60101c046b023940052721f8600201009c602,0x1008040f013c0040262bbddced14809d8eb5d0080402020c40409113a808300105404e9,0x7987c0402790302a7401008ce025280812150480804f10c00804024f8080402010080402,0x10600407010240402010080402583dd24020200012027b00804020603dea020203004f4,0x100804020b0c004db7f80014021696804020100854fe0ebf5f8041f809f6fa4881df2f8,0x38094e15010600503629d004370b008fc028100a02093c8084e09802495ab1050080402,0x10080e1286008040913c2c6e0201429fb09110080508010c20e020102a0d05820080487,0x100a2a8a0106005148080a26028900804600f2b6220288174c002878321c0486b6c126b,0x1474ce0204c702c30010263655300243d1a8c88c04430500a311701008240248c582450,0xbc9649130480a460233b200e029101e4202900084c0901008011f8f008a402010280402,0x30132b3981c040201026540241b200e0d010081283948da500293c9812040a8084e6b,0x130049125e020b00a5cb51180a5a0a29026580201008046a010086ca1048094209]
def bucket (i : Nat) : Nat := masks.getD (((pages.getD (i/32) 0) >>> (9*(i % 32))) &&& 511) 0
def old (w : W) := (w.toNat % 2^232) + (((w.toNat >>> 689) % 2^232) <<< 232)
def code (ws : List W) := ws.foldl (fun a w=>a+(old w) % 65521) 0
def advice (ws hist : List W) : List Minor :=
  let m := bucket ((code ws+37*code hist) % 1021)
  ((List.finRange 23).filter (fun i=>m.testBit i.val)).map faceAt
theorem advice_ok (ws hist : List W) : ∀ c∈advice ws hist,c.Valid base := by
  rintro c hc;obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc;exact valid i
def rootPair (i : Nat) : Bool := match (pairs base)[i]? with
  | none => false
  | some (a,b,r) => dispatch 4 (UnifiedSearch.checkChild base advice (UnifiedSearch.guided base advice 9) 9 base []) a b r
end UnifiedC4

namespace UnifiedC4
open P2828Check P2828Live P2828Generic P2828Truth P2828Minor ThetaSigned SignedCofactor
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check0 : rootPair 0=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check1 : rootPair 1=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check2 : rootPair 2=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check3 : rootPair 3=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check4 : rootPair 4=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check5 : rootPair 5=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check6 : rootPair 6=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check7 : rootPair 7=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check8 : rootPair 8=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check9 : rootPair 9=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check10 : rootPair 10=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check11 : rootPair 11=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check12 : rootPair 12=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check13 : rootPair 13=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check14 : rootPair 14=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check15 : rootPair 15=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check16 : rootPair 16=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check17 : rootPair 17=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check18 : rootPair 18=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check19 : rootPair 19=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem check20 : rootPair 20=false := by decide +kernel
theorem allPairs (i : Fin 21) : rootPair i.val=false := by
  fin_cases i
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
theorem noTen : UnifiedSearch.guided base advice 10 4 base [] = false := by
  have len : (pairs base).length=21 := by decide
  apply Bool.eq_false_iff.mpr
  intro hit
  simp only [UnifiedSearch.guided,Bool.or_eq_true] at hit
  rcases hit with short|next
  · exact (by decide +kernel : (base==[goal])≠true) short
  obtain ⟨q,hq,ok⟩ := List.any_eq_true.mp next
  obtain ⟨i,hi⟩ := List.get_of_mem hq
  have no := allPairs (Fin.cast len i)
  simp only [Fin.val_cast,rootPair,List.getElem?_eq_getElem i.isLt] at no
  rw [←hi] at ok
  exact Bool.noConfusion (no.symm.trans ok)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem signed_lower {k} (hr : Run C4Base.small k C4Base.nine) : 11≤k := by
  by_contra! tooSmall
  have hl := root hr
  have stride (t : Nat) (le : k≤t) : live basicOps goal t base.toFinset := by
    induction le with
    | refl => exact hl
    | step _ ih => exact Or.inl ih
  have start : P2828Minor.seen base []=base.toFinset := by simp [P2828Minor.seen]
  have yes := UnifiedSearch.guided_complete base advice advice_ok 10 base [] 4
    (by decide +kernel) (by decide +kernel) (start ▸ History.initial) (start ▸ Finset.Subset.refl _) (stride 10 (by omega))
  exact Bool.noConfusion (yes.symm.trans noTen)
end UnifiedC4

namespace P2828Raw
open P2828Check P2828Live
def data : Array Face := #[
⟨17,0,11,0x155540005540002aa801400015240005500014402000154800a000520000100080007fffffffffffffffff8000000007fffff800169c547e9391f250d6d9434a5a000000050d0444254a5b5d622871544000000000200aaaa0202aa000375400a0681b960102ab341b3010280aa4105cd06d50031a84748840a40a40a40a40a40a40a40a40a40a40a40a4b4e2a3f49c8f9286b6ca1a52d002aa74286822212a52daeb11438aa2223383e3,0⟩,
⟨66,0,11,0x6669998d4c0000000000001994d0500000000000665311900000014887ff8007ffffffff8007fffffffffff800000018002b5f00ade000002eec0b63f0e05ebbb202eeb00b608c00000000a8802b68000000000000003334cee6b78000000000000cca6cae80000000003329aaee000000a77dc01c01c01c01c01c01c01c01c01c01c01c000c0015af8056f5dd80177605b1f8702f5dd901775805b046f830007f544015b4,2⟩,
⟨132,0,11,0xf1c38e1e30c878c32310000000000000000007451a0c04ffffff8007ff8007fffffffffff8000007ff8035cdef8000000671f819c0016901dfa0670919800000000100d73121c0d5ede02068a020000000003340000078f9c70f1a673f79b59828e884000cdde54003ba8d778a402c02c02c02c02c02c02c02c02c02c02c02c01ae6f7c343d80338fc0ce000b480efd033848cc06000fff0806b9890e06af6f, 0⟩,
⟨24,0,11,0x3fc00003e000007c001000007e0000380000e0000000f800600007804003000040fffffffff8007ffffffff8000000007fffff8c0c3c1c31b07671f249c7c60ed800000000000007460e04371a30f4e442301c2000021fe00481f000443e020800063fa0ad9c00067a6000027c0a30000bc0a005d28075d4114114114114114114114114114114114106061e0e18d83b38f924e3e3076f9118338f826233a307021b8d187a7221180e1,0⟩,
⟨160,0,11,0x1fffff800001ff000000000000000000000ff803f8007ff8007ff8007ff8007ffffffffffffff8003fc038000000ff0380000000300f3e0ff03c3e0c000c3ef000ff3e3c00c03e0000014020601600000282208100469fffffc0804cff80000514e30000284a0857fc27fcc10c10c10c10c10c10c10c10c10c10c10c10001fe01f8380707f81c1fe000fd8079f07f81e1f0600061f78007f9f1e00601f, 0⟩]
def faceAt (i : Fin 5) := data[i.val]
end P2828Raw

namespace P2828Raw
open P2828 P2828Check ThetaSigned SignedCofactor
theorem pull {X Z : Type} {P : Set (Wire X)} {k f} (hr : Run P k f) (phi : Z → X) :
    ∀ Q : Set (Wire Z), (∀ g ∈ P, (fun z => g (phi z)) ∈ Q) → Run Q k (fun z => f (phi z)) := by
  induction hr with
  | done h => exact fun Q hh => .done (hh _ h)
  | @gate P k f a b op ha hb hr ih =>
    intro Q hh
    apply Run.gate op (hh _ ha) (hh _ hb)
    apply ih
    intro g hg
    rcases hg with h|rfl|rfl
    · exact Or.inl (hh _ h)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
def insertVars {n : Nat} (idx : Fin 9 → Option (Fin n)) (x : Fin n → Bool) (v : Fin 9) :=
  match idx v with
  | none => false
  | some i => x i
theorem pullSmall {n : Nat} (idx : Fin 9 → Option (Fin n)) (f : Wire P2828.Y) (h : f ∈ P2828.small) :
    (fun x => f (insertVars idx x)) ∈ literals n := by
  rcases h with ⟨b,rfl⟩|⟨i,rfl|rfl⟩
  · exact Or.inl ⟨b,rfl⟩
  · cases e : idx i with
    | none => exact Or.inl ⟨false,funext fun x => by simp [insertVars,e,ThetaSigned.bit]⟩
    | some j => exact Or.inr ⟨j,Or.inl (funext fun x => by simp [insertVars,e])⟩
  · cases e : idx i with
    | none => exact Or.inl ⟨true,funext fun x => by simp [insertVars,e,inv,ThetaSigned.bit]⟩
    | some j => exact Or.inr ⟨j,Or.inr (funext fun x => by simp [insertVars,e,inv])⟩
def Lower4 := ∀ k, Run C4Base.small k C4Base.nine → 11 ≤ k
def selector0 : Fin 9 → Option (Fin 7) := ![none,some 0,some 5,some 3,none,some 4,some 1,some 2,some 6]
theorem good0 (lower : Lower4) : (faceAt 0).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector0) (literals 7) (pullSmall selector0)
  have eq : ∀ x, nine (pin (faceAt 0).fixed (faceAt 0).values (insertVars selector0 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
def selector1 : Fin 9 → Option (Fin 7) := ![some 0,none,some 4,some 6,some 1,some 5,none,some 2,some 3]
theorem good1 (lower : Lower4) : (faceAt 1).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector1) (literals 7) (pullSmall selector1)
  have eq : ∀ x, nine (pin (faceAt 1).fixed (faceAt 1).values (insertVars selector1 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
def selector2 : Fin 9 → Option (Fin 7) := ![some 5,some 0,none,some 4,some 2,some 3,some 1,none,some 6]
theorem good2 (lower : Lower4) : (faceAt 2).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector2) (literals 7) (pullSmall selector2)
  have eq : ∀ x, nine (pin (faceAt 2).fixed (faceAt 2).values (insertVars selector2 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
def selector3 : Fin 9 → Option (Fin 7) := ![some 3,some 5,some 0,none,none,some 6,some 2,some 1,some 4]
theorem good3 (lower : Lower4) : (faceAt 3).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector3) (literals 7) (pullSmall selector3)
  have eq : ∀ x, nine (pin (faceAt 3).fixed (faceAt 3).values (insertVars selector3 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
def selector4 : Fin 9 → Option (Fin 7) := ![some 0,some 5,some 3,some 6,some 1,none,some 2,none,some 4]
theorem good4 (lower : Lower4) : (faceAt 4).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector4) (literals 7) (pullSmall selector4)
  have eq : ∀ x, nine (pin (faceAt 4).fixed (faceAt 4).values (insertVars selector4 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem allValid (lower : Lower4) (i : Fin 5) : (faceAt i).Valid := by
  fin_cases i
  · exact good0 lower
  · exact good1 lower
  · exact good2 lower
  · exact good3 lower
  · exact good4 lower
end P2828Raw

namespace P2828Raw
open P2828Check P2828Live P2828Minor P2828 ThetaSigned
def mkMinor (f : Face) : Minor := ⟨f.lower,f.mask,f.anchor⟩
def allFaces (_ _ : List W) : List Minor := (List.finRange 5).map fun i=>mkMinor (faceAt i)
theorem facesGood (ws hist) : ∀c∈allFaces ws hist,c.Valid inputs := by
  intro c hc
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
  exact ofOrdinary _ (allValid (fun _ h => UnifiedC4.signed_lower h) i)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem rawScan : UnifiedSearch.guided inputs allFaces 13 5 inputs []=false := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower14 {k} (h : Run small k nine) : 14≤k := by
  by_contra! bad
  have pad (t : Nat) (le : k≤t) : live basicOps goal t inputs.toFinset := by
    induction le with
    | refl => exact inputLive h
    | step _ ih => exact Or.inl ih
  have start : P2828Minor.seen inputs []=inputs.toFinset := by simp [P2828Minor.seen]
  have result := UnifiedSearch.guided_complete inputs allFaces facesGood 13 inputs [] 5 (by decide +kernel) (by decide)
    (start ▸ History.initial) (start ▸ Finset.Subset.refl _) (pad 13 (by omega))
  exact Bool.noConfusion (result.symm.trans rawScan)
end P2828Raw

namespace SignedCircuitAux
open PEqualNP.CircuitLowerBounds
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
end SignedCircuitAux
namespace ThetaSigned
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity SignedCircuitAux
def isBinary (g : Gate) : Bool := match g.op with | .not => false | _ => true
def budget (gs : List Gate) := gs.countP isBinary
def readW {X : Type} (w : X → List Bool) (i : ℕ) : Wire X := fun x => (w x).getD i false
def observe {X : Type} (w : X → List Bool) (g : Gate) : Wire X :=
  fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)
def emits {X : Type} (w : X → List Bool) (g : Gate) (x : X) := w x ++ [observe w g x]
theorem decode {X : Type} (w : X → List Bool) (g : Gate) (ok : Ok g) (P : Set (Wire X))
    (cp : Closed P) (hw : ∀ i, readW w i ∈ P) :
    (isBinary g = false ∧ observe w g ∈ P) ∨
    (isBinary g = true ∧ ∃ a ∈ P, ∃ b ∈ P, ∃ op, observe w g = bin op a b) := by
  rcases g with ⟨op,inputs⟩
  obtain ⟨allowed,short⟩ := ok
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at allowed
  change op = _ ∨ op = _ ∨ op = _ at allowed
  rcases allowed with rfl|rfl|rfl
  · refine Or.inr ⟨rfl,?_⟩
    rcases inputs with _|⟨a,_|⟨b,_|⟨d,tl⟩⟩⟩
    · exact ⟨_,cp.1 true,_,cp.1 true,false,rfl⟩
    · refine ⟨_,hw a,_,cp.1 true,false,?_⟩
      funext x; simp [bin,readW,observe,bit,GateOp.eval]
    · refine ⟨_,hw a,_,hw b,false,?_⟩
      funext x; simp [bin,readW,observe,bit,GateOp.eval]
    · change (a::b::d::tl).length ≤ 2 at short; simp at short
  · refine Or.inr ⟨rfl,?_⟩
    rcases inputs with _|⟨a,_|⟨b,_|⟨d,tl⟩⟩⟩
    · exact ⟨_,cp.1 false,_,cp.1 false,true,rfl⟩
    · refine ⟨_,hw a,_,cp.1 false,true,?_⟩
      funext x; simp [bin,readW,observe,bit,GateOp.eval]
    · refine ⟨_,hw a,_,hw b,true,?_⟩
      funext x; simp [bin,readW,observe,bit,GateOp.eval]
    · change (a::b::d::tl).length ≤ 2 at short; simp at short
  · refine Or.inl ⟨rfl,?_⟩
    cases inputs with
    | nil => exact cp.1 true
    | cons a tl => exact cp.2 _ (hw a)
theorem reads_after {X : Type} (w : X → List Bool) (g : Gate) (m : ℕ)
    (wm : ∀ x, (w x).length=m) (P : Set (Wire X)) (old : ∀ i, readW w i ∈ P)
    (fresh : observe w g ∈ P) : ∀ i, readW (emits w g) i ∈ P := by
  intro i
  by_cases e : i=m
  · have eq : readW (emits w g) i = observe w g := by
      funext x
      change (w x ++ [_]).getD i false = _
      rw [e,← wm x,getD_snoc_eq]
    exact eq ▸ fresh
  · have eq : readW (emits w g) i = readW w i := by
      funext x
      change (w x ++ [_]).getD i false = _
      exact getD_snoc_ne _ _ _ _ (by rw [wm x];exact e)
    exact eq ▸ old i
theorem compile {X : Type} (gs : List Gate) (out : ℕ) (ok : ∀ g ∈ gs, Ok g) :
    ∀ (w : X → List Bool) (m : ℕ), (∀ x, (w x).length=m) → ∀ P : Set (Wire X),
      Closed P → (∀ i, readW w i ∈ P) →
      Run P (budget gs) (fun x => (wiresFrom gs (w x)).getD out false) := by
  induction gs with
  | nil => intro w m wm P cp hw; exact .done (hw out)
  | cons g gs ih =>
    intro w m wm P cp hw
    have next := ih (fun g' hg => ok g' (List.mem_cons_of_mem _ hg)) (emits w g) (m+1)
      (fun x => by simp [emits,wm])
    obtain one|two := decode w g (ok g (List.mem_cons_self ..)) P cp hw
    · rcases one with ⟨hn,v⟩
      simp only [budget,List.countP_cons,hn,Bool.false_eq_true,ite_false,Nat.add_zero]
      exact next P cp (reads_after w g m wm P hw v)
    · rcases two with ⟨hn,a,ha,b,hb,op,v⟩
      simp only [budget,List.countP_cons,hn,ite_true]
      apply Run.gate op ha hb
      exact next _ (plus_closed cp _) (reads_after w g m wm _ (fun i => Or.inl (hw i)) (Or.inr (Or.inl v)))
end ThetaSigned
namespace FirstFree
open ThetaSigned SignedCofactor PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity SignedCircuitAux
theorem raw (n i : Nat) : readW (fun x : Fin n → Bool => List.ofFn x) i ∈ literals n := by
  by_cases h : i<n
  · exact Or.inr ⟨⟨i,h⟩,Or.inl (funext fun x => by simpa [readW] using (show (List.ofFn x).getD (⟨i,h⟩ : Fin n) false = x ⟨i,h⟩ from by simp [h]))⟩
  · exact Or.inl ⟨false,funext fun x => List.getD_eq_default _ _ (by simpa using h)⟩
end FirstFree
namespace FirstFree
open P2828 ThetaSigned PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity SignedCircuitAux
theorem shape (C : Circuit) (fan : FanInTwo C) (sz : C.size ≤ 15)
    (hn : ∀ x : Y, (C.wires (List.ofFn x)).getD 9 false = !x 0)
    (out : circuitFun 9 C = nine) :
    ∃ B : Circuit, B.gates = C.gates.drop 1 ∧ B.size=14 ∧
      (∀ g ∈ B.gates, g.op=.and ∨ g.op=.or) ∧ FanInTwo B ∧
      ∀ x : Y, B.eval (List.ofFn x ++ [!x 0]) = nine x := by
  rcases C with ⟨gs,port⟩
  cases gs with
  | nil =>
    have e := hn (fun _ => false)
    change (List.ofFn (fun _ : Fin 9 => false)).getD 9 false = true at e
    rw [List.getD_eq_default _ _ (by simp)] at e
    contradiction
  | cons g gs =>
    let w := fun x : Y => List.ofFn x
    have obs : observe w g = inv (fun x => x 0) := by
      funext x
      have hh := hn x
      change (wiresFrom gs (emits w g x)).getD 9 false = _ at hh
      rw [getD_wiresFrom gs _ 9 (by simp [emits,w])] at hh
      simpa [emits,w,inv] using hh
    have exactW (x : Y) : emits w g x=List.ofFn x ++ [!x 0] := by
      change w x ++ [observe w g x] = List.ofFn x ++ [!x 0]
      rw [obs]
      rfl
    have ok (t) (ht : t∈gs) : Ok t := fan t (List.mem_cons_of_mem g ht)
    have evalAll (x : Y) : (wiresFrom gs (emits w g x)).getD port false = nine x := congrFun out x
    have run := compile gs port ok (emits w g) 10 (by simp [emits,w]) small small_closed
        (reads_after w g 9 (by simp [w]) _ (raw 9) (Or.inr ⟨0,Or.inr obs⟩))
    have lb := P2828Raw.lower14 ((funext evalAll) ▸ run)
    have le := List.countP_le_length (p:=isBinary) (l:=gs)
    change gs.length+1≤15 at sz
    change 14 ≤ gs.countP isBinary at lb
    refine ⟨⟨gs,port⟩,rfl,by change gs.length=14;omega,?_,ok,?_⟩
    · intro t ht
      have o := (ok t ht).1
      change t.op=.and ∨ t.op=.or ∨ t.op=.not at o
      rcases o with e|e|e
      · exact Or.inl e
      · exact Or.inr e
      · obtain ⟨a,b,form⟩ := List.append_of_mem ht
        have ha := List.countP_le_length (p:=isBinary) (l:=a)
        have hb := List.countP_le_length (p:=isBinary) (l:=b)
        have nb : isBinary t = false := by simp [isBinary,e]
        have short : gs.countP isBinary < gs.length := by
          change gs = a ++ t :: b at form
          rw [form]
          simp [List.countP_append,nb]
          omega
        omega
    · intro x
      change (wiresFrom gs (List.ofFn x ++ [!x 0])).getD port false = nine x
      rw [←exactW]
      exact evalAll x
end FirstFree

namespace Cert
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega

def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h

def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)

set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)

set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)

set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)

set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)

set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)

set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)

set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩

set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

end Cert

namespace Front2778

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
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
    (h : live ops goal k s) : s.card ≤ k+1 := by
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

end Front2778

namespace Front2778
variable {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}

theorem first_live {k : ℕ} {s : Finset α} (h : live ops goal (k+1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,tail⟩
      · exact .inl done
      · exact .inr ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,Or.inl tail⟩
    · exact .inr step

end Front2778


namespace Front2778
namespace Price
open Cert
variable {A R : Type} [DecidableEq A]

structure Model (A R : Type) where
  good : A → Wire R → Prop
  op : Bool → A → A → A
  combine_ok : ∀ b {x y f g},good x f → good y g → good (op b x y) (combine b f g)

def choices (M : Model A R) (a b : A) : Finset A := {M.op false a b,M.op true a b}

private theorem cost_ins (a : A) (s : Finset A) (v : A→Wire R) :
    ∑ w∈insert a s,cost (v w) ≤ cost (v a)+∑ w∈s,cost (v w) := by
  by_cases h : a∈s
  · simp [Finset.insert_eq_of_mem h]
  · simp [Finset.sum_insert h]

theorem finish (M : Model A R) (t : A) (T : Wire R) (terminal : ∀ f,M.good t f → f=T)
    (nc : ¬Constant T) {k s} (program : live (choices M) t k s)
    {roots : List (Wire R)} {p : ℕ} {bank : List (Wire R)} (history : Reach roots p bank)
    (v : A → Wire R) (hg : ∀ w∈s,M.good w (v w)) (ha : ∀ w∈s,Available bank (v w)) :
    ∃ q last,Reach roots q last ∧ Available last T ∧ q+(∑ w∈s,cost (v w))≤p+k := by
  classical
  induction k generalizing s p bank v with
  | zero =>
    change s={t} at program
    subst s
    have same := terminal _ (hg t (by simp))
    exact ⟨p,bank,history,same ▸ ha t (by simp),by simp [same,cost,nc]⟩
  | succ k ih =>
    rcases program with skip | ⟨a,am,b,bm,ab,z,how,fresh,r,rfl,tail⟩
    · obtain ⟨q,last,built,hit,num⟩ := ih skip history v hg ha
      exact ⟨q,last,built,hit,by omega⟩
    obtain ⟨op,eq⟩ : ∃ op,z=M.op op a b := by
      rcases (show z=M.op false a b ∨ z=M.op true a b by simpa [choices] using how) with h|h
      · exact ⟨false,h⟩
      · exact ⟨true,h⟩
    let out := combine op (v a) (v b)
    let v' := Function.update v z out
    have zr : z∉r := fun mem => fresh (by simp [mem])
    have sub : r⊆insert a (insert b r) := (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    have back {w} (mem : w∈r) : v' w=v w := Function.update_of_ne (show w≠z from fun eq => zr (eq ▸ mem)) ..
    have same : v' z=out := Function.update_self ..
    obtain ⟨p',bank',next,know,inherit,bill⟩ := extend_two roots op history (ha a am) (ha b bm)
    have good' : ∀ w∈insert z r,M.good w (v' w) := by
      intro w mem
      rcases Finset.mem_insert.mp mem with rfl|h
      · rw [same,eq]
        exact M.combine_ok op (hg a am) (hg b bm)
      · rw [back h];exact hg _ (sub h)
    have available' : ∀ w∈insert z r,Available bank' (v' w) := by
      intro w mem
      rcases Finset.mem_insert.mp mem with rfl|h
      · exact same ▸ know
      · rw [back h];exact inherit _ (ha _ (sub h))
    obtain ⟨q,last,built,hit,num⟩ := ih tail next v' good' available'
    rw [Finset.sum_insert zr,same] at num
    have old : (∑ w∈r,cost (v' w))=∑ w∈r,cost (v w) := Finset.sum_congr rfl (fun _ hw => congrArg cost (back hw))
    rw [old] at num
    have h₁ := cost_ins a (insert b r) v
    have h₂ := cost_ins b r v
    change p'+cost (v a)+cost (v b) ≤ p+1+cost out at bill
    exact ⟨q,last,built,hit,by omega⟩

theorem cut_bound (M : Model A R) (t : A) (T : Wire R) (terminal : ∀ f,M.good t f → f=T)
    (nc : ¬Constant T) {k s} (program : live (choices M) t k s) {roots : List (Wire R)}
    {p bank} (history : Reach roots p bank) {L : ℕ}
    (low : ∀ q last,Reach roots q last → Available last T → L≤q)
    (marked : Finset A) (sub : marked⊆s)
    (repr : ∀ w∈s,∃ f,M.good w f ∧ Available bank f ∧ (w∈marked → Constant f)) :
    L+marked.card≤p+k := by
  classical
  let v (w : A) : Wire R := if h : w∈s then (repr w h).choose else fun _ => false
  have rep {w} (hw : w∈s) : M.good w (v w) ∧ Available bank (v w) ∧ (w∈marked → Constant (v w)) := by
    simpa [v,hw] using (repr w hw).choose_spec
  obtain ⟨q,last,done,out,size⟩ := finish M t T terminal nc program history v
    (fun _ hw => (rep hw).1) (fun _ hw => (rep hw).2.1)
  have markedSum : (∑ w∈marked,cost (v w))=marked.card := by
    calc
      _ = ∑ _w∈marked,(1 : ℕ) := Finset.sum_congr rfl fun w hw => by simp [cost,(rep (sub hw)).2.2 hw]
      _ = _ := by simp
  have all := Finset.sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => Nat.zero_le (cost (v i)))
  have lower := low _ _ done out
  omega

end Price
end Front2778
namespace Complement2311
namespace Face
open Front2778
open Cert hiding inputs seed
abbrev rawFull := Cert.inputs
abbrev S := Sig
structure Data where
  mask : ℕ
  lb : ℕ
  pos : S
  neg : S
  ps : List Row
  ns : List Row
  ones : Nat := 0
  residual : Nat := 0
  singles : Nat := 0
def targetWord (d : Data) := movedWord (fixRows (511 ^^^ (d.mask ||| d.ones)) d.ones) graph
def below (m : ℕ) (r t : Row) := (r.val &&& m &&& t.val)=(r.val&&&m) ∧ (r.val &&& m &&& 1)=(t.val &&& m &&& 1)
instance (m r t) : Decidable (below m r t) := inferInstanceAs (Decidable (_ ∧ _))
def Up (m : ℕ) (f : Wire Row) := ∀ r t, below m r t → f r=true → f t=true
def compat (d : Data) (w : S) (f : Wire Row) :=
  Up d.mask f ∧ (∀ r,bit r d.pos=true → bit r w=true → f r=true) ∧
    ∀ r,bit r d.neg=true → f r=true → bit r w=true
def dataOp (isOr : Bool) (a b : S) := if isOr then a|||b else a&&&b
theorem op_compat (d : Data) (b : Bool) {a c : S} {f g : Wire Row} (ha : compat d a f) (hc : compat d c g) :
    compat d (dataOp b a c) (combine b f g) := by
  rcases ha with ⟨uf,pf,nf⟩
  rcases hc with ⟨ug,pg,ng⟩
  cases b
  · exact ⟨fun x y le h => Bool.and_eq_true_iff.mpr ⟨uf x y le (Bool.and_eq_true_iff.mp h).1,ug x y le (Bool.and_eq_true_iff.mp h).2⟩,
      fun r hp h => by
        have h0 : bit r a=true ∧ bit r c=true := by simpa [dataOp,bit] using h
        exact Bool.and_eq_true_iff.mpr ⟨pf r hp h0.1,pg r hp h0.2⟩,
      fun r hn h => by
        have v := Bool.and_eq_true_iff.mp h
        simpa only [dataOp,Bool.false_eq_true,ite_false,bit,BitVec.getLsbD_and] using Bool.and_eq_true_iff.mpr ⟨nf r hn v.1,ng r hn v.2⟩⟩
  · exact ⟨fun x y le h => Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp h).imp (uf x y le) (ug x y le)),
      fun r hp h => by
        have h0 : bit r a=true ∨ bit r c=true := by simpa [dataOp,bit] using h
        exact Bool.or_eq_true_iff.mpr (h0.imp (pf r hp) (pg r hp)),
      fun r hn h => by
        rcases (Bool.or_eq_true_iff.mp h) with v|v
        · simpa only [dataOp,ite_true,bit,BitVec.getLsbD_or] using Bool.or_eq_true_iff.mpr (Or.inl (nf r hn v) : bit r a=true ∨ bit r c=true)
        · simpa only [dataOp,ite_true,bit,BitVec.getLsbD_or] using Bool.or_eq_true_iff.mpr (Or.inr (ng r hn v) : bit r a=true ∨ bit r c=true)⟩
def model (d : Data) : Price.Model S Row := ⟨compat d,dataOp,op_compat d⟩

def checkEnds (d : Data) := (List.finRange 512).all fun u =>
  if bit u (targetWord d) then d.ps.any (fun r => bit r d.pos && bit r graph && decide (below d.mask r u))
  else d.ns.any (fun r => bit r d.neg && !bit r graph && decide (below d.mask u r))

theorem terminal {d : Data} (checked : checkEnds d=true) {f : Wire Row} (good : compat d graph f) :
    f=observe (targetWord d) := by
  rcases good with ⟨up,pos,neg⟩
  funext u
  have hh := List.all_eq_true.mp checked u (List.mem_finRange u)
  change f u=bit u (targetWord d)
  cases ht : bit u (targetWord d)
  · simp [ht] at hh
    obtain ⟨r,_,⟨rn,rg⟩,le⟩ := hh
    cases hu : f u
    · rfl
    · have impossible := neg r rn (up u r le hu)
      simp_all
  · simp [ht] at hh
    obtain ⟨r,_,⟨rp,rg⟩,le⟩ := hh
    exact up r u le (pos r rp rg)

def nonePositive (d : Data) (w : S) := (d.pos&&&w)==0
def allNegative (d : Data) (w : S) := (d.neg&&&w)==d.neg
def dead (d : Data) (w : S) := nonePositive d w || allNegative d w
def dominates (d : Data) (v w : S) := ((w&&&d.pos)&&&v)==(w&&&d.pos) && ((v&&&d.neg)&&&w)==(v&&&d.neg)

theorem left_const {d : Data} {w} (h : nonePositive d w=true) : compat d w (fun _=>false) := by
  have eq := beq_iff_eq.mp h
  refine ⟨fun _ _ _ => id,?_,fun _ _ h => Bool.noConfusion h⟩
  intro r p b
  have ee := congrArg (bit r) eq
  simp only [bit,BitVec.getLsbD_and,BitVec.getLsbD_zero,show d.pos.getLsbD r.val=true from p,show w.getLsbD r.val=true from b] at ee
  have hz : (0:S).getLsbD r.val=false := by simp
  exact Bool.noConfusion (ee.trans hz)

theorem right_const {d : Data} {w} (h : allNegative d w=true) : compat d w (fun _=>true) := by
  have eq := beq_iff_eq.mp h
  refine ⟨fun _ _ _ => id,fun _ _ _ => rfl,?_⟩
  intro r n _
  have ee := congrArg (bit r) eq
  simpa [bit,show d.neg.getLsbD r.val=true from n] using ee

theorem improve {d : Data} {v w : S} {f} (h : dominates d v w=true) (good : compat d v f) : compat d w f := by
  rcases (show (w&&&d.pos)&&&v=w&&&d.pos ∧ (v&&&d.neg)&&&w=v&&&d.neg by simpa [dominates] using h) with ⟨hp,hn⟩
  refine ⟨good.1,?_,?_⟩
  · intro r pr wr
    apply good.2.1 r pr
    have e := congrArg (bit r) hp
    simpa [bit,show d.pos.getLsbD r.val=true from pr,show w.getLsbD r.val=true from wr] using e
  · intro r nr fr
    have vr := good.2.2 r nr fr
    have e := congrArg (bit r) hn
    simpa [bit,show d.neg.getLsbD r.val=true from nr,show v.getLsbD r.val=true from vr] using e

def carries (d : Data) (bank : List (Wire Row)) (w : S) := ∃ f,
  compat d w f ∧ Available bank f ∧ (dead d w=true → Constant f)

theorem trivial {d : Data} {w bank} (h : dead d w=true) : carries d bank w := by
  rcases Bool.or_eq_true_iff.mp h with off|on
  · exact ⟨_,left_const off,Or.inr ⟨false,rfl⟩,fun _ => ⟨false,rfl⟩⟩
  · exact ⟨_,right_const on,Or.inr ⟨true,rfl⟩,fun _ => ⟨true,rfl⟩⟩

end Face
end Complement2311
namespace Complement2311.Face
open Cert
def info (d : Data) : ColumnInfo := (511 ^^^ (d.mask ||| d.ones),d.ones,d.residual,d.singles,d.lb)
def geometry (d : Data) :=
  colCheck 511 (info d) (boundsBefore known383) &&
  decide (d.mask=colFree 511 (info d).1 d.ones)
theorem pinned_lower (d : Data) (ok : geometry d=true) :
    Lower (vars d.mask) (targetWord d) d.lb := by
  have cert := (Bool.and_eq_true_iff.mp ok).1
  have eq := of_decide_eq_true (Bool.and_eq_true_iff.mp ok).2
  let z := (info d).1
  let free := colFree 511 z d.ones
  let G := targetWord d
  let wanted := supportPairs d.singles
  have same : chartGoal 511 = graph := by decide +kernel
  simp only [colCheck,info,same,Bool.and_eq_true] at cert
  have geom := cert.2
  have properG := cert.1.1.1
  change properB G=true at properG
  have maskEq : d.mask=free := eq
  rw [maskEq]
  by_cases no : d.residual=0
  · simp only [info,no,ite_true,Bool.and_eq_true,decide_eq_true_eq,same] at geom
    intro p bank run hit
    exact (of_decide_eq_true geom.2).trans (lower_count (proper_of _ properG) wanted geom.1 p bank run hit)
  · simp only [info,no,ite_false,Bool.and_eq_true,decide_eq_true_eq,same] at geom
    intro p bank run hit
    exact (of_decide_eq_true geom.2).trans (lift_ok geom.1.2 (proper_of _ properG) (proper_of _ geom.1.1)
      (before_sound known383 valid383 d.residual) p bank run hit)
end Complement2311.Face
namespace Complement2311.Face
open Cert hiding inputs seed

def rawAt (i : Fin 9) := rawFull.getD i.val zero
def extra := neg (rawAt 0)
def start := extra::rawFull
def seen (h : List S) := h++start
def cheap (d : Data) (z : S) (past : List S) := dead d z || past.any (fun a => dominates d a z)
def price (d : Data) : List S → ℕ
  | [] => if cheap d extra rawFull then 0 else 1
  | z::h => price d h + (if cheap d z (seen h) then 0 else 1)

inductive History : List S → Prop where
  | empty : History []
  | gate {h : List S} (prior : History h) {a b : S} (oldA : a∈seen h) (oldB : b∈seen h) (op : Bool) :
      History (dataOp op a b::h)

def checkInputs (d : Data) := (List.finRange 9).all fun i =>
  dead d (rawAt i) || (d.mask.testBit i.val && (vars d.mask).contains (rawAt i))

theorem up_raw (m : ℕ) (i : Fin 9) (active : m.testBit i.val=true) : Up m (observe (rawAt i)) := by
  intro x y le hx
  have atI := congrArg (fun n : ℕ => n.testBit i.val) le.1
  have on : x.val.testBit i.val=true := (input_coords i x) ▸ hx
  change bit y (rawAt i)=true
  rw [show bit y (rawAt i)=y.val.testBit i.val from input_coords i y]
  simpa only [Nat.testBit_and,active,on,Bool.true_and,Bool.and_true] using atI

theorem present_raw (d : Data) (ok : checkInputs d=true) {w} (hw : w∈rawFull) :
    carries d ((vars d.mask).map observe) w := by
  change w∈Cert.inputs at hw
  rw [←input_list] at hw
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  have supplied := List.all_eq_true.mp ok i (List.mem_finRange i)
  rcases Bool.or_eq_true_iff.mp supplied with free | h
  · exact trivial free
  by_cases e : dead d (rawAt i)=true
  · exact trivial e
  obtain ⟨active,bank⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨_,⟨up_raw _ _ active,fun _ _ => id,fun _ _ => id⟩,
    Or.inl (List.mem_map.mpr ⟨_,List.contains_iff_mem.mp bank,rfl⟩),fun v => False.elim (e v)⟩

theorem free_copy {d : Data} {bank : List (Wire Row)} {z : S} {past : List S}
    (yes : cheap d z past=true) (supply : ∀ u∈past,carries d bank u) : carries d bank z := by
  by_cases c : dead d z=true
  · exact trivial c
  have some := (Bool.or_eq_true_iff.mp yes).resolve_left c
  obtain ⟨u,hu,relation⟩ := List.any_eq_true.mp some
  obtain ⟨f,hf,av,_⟩ := supply _ hu
  exact ⟨f,improve relation hf,av,fun h => False.elim (c h)⟩

def checkExtra (d : Data) := cheap d extra rawFull || (d.mask.testBit 0 && (vars d.mask).contains (rawAt 0))
theorem up_extra (m : ℕ) (active : m.testBit 0=true) : Up m (observe extra) := by
  intro x y le hx
  have e := congrArg (fun n : ℕ => n.testBit 0) le.2
  have bitEq : x.val.testBit 0 = y.val.testBit 0 := by
    simpa only [Nat.testBit_and,active,show (1:ℕ).testBit 0=true from rfl,Bool.and_true] using e
  have same : bit x (rawAt 0)=bit y (rawAt 0) := (input_coords 0 x).trans (bitEq.trans (input_coords 0 y).symm)
  change observe (neg (rawAt 0)) y=true
  change observe (neg (rawAt 0)) x=true at hx
  rw [obs_neg] at hx ⊢
  change (!(bit x (rawAt 0)))=true at hx
  change (!(bit y (rawAt 0)))=true
  rwa [same] at hx

theorem base_history (d : Data) (ok : checkInputs d=true) (ex : checkExtra d=true) :
    ∃ p≤price d [],∃ bank,Reach ((vars d.mask).map observe) p bank ∧ ∀ w∈seen [],carries d bank w := by
  let rs := (vars d.mask).map observe
  have raw : ∀ w∈rawFull,carries d rs w := fun w hw => present_raw d ok hw
  by_cases noCost : cheap d extra rawFull=true
  · refine ⟨0,by simp [price,noCost],rs,Reach.start,?_⟩
    intro w hw
    rcases List.mem_cons.mp (show w∈extra::rawFull from hw) with rfl|mem
    · exact free_copy noCost raw
    · exact raw _ mem
  obtain ⟨active,here⟩ := Bool.and_eq_true_iff.mp ((Bool.or_eq_true_iff.mp ex).resolve_left noCost)
  have haveX : Available rs (observe (rawAt 0)) := Or.inl (List.mem_map_of_mem (List.contains_iff_mem.mp here))
  let bank := inv (observe (rawAt 0))::rs
  refine ⟨1,by simp [price,noCost],bank,Reach.one .start haveX,?_⟩
  intro w hw
  rcases List.mem_cons.mp (show w∈extra::rawFull from hw) with rfl|mem
  · have fresh : dead d extra≠true := fun h => noCost (Bool.or_eq_true_iff.mpr (Or.inl h))
    refine ⟨observe extra,⟨up_extra _ active,fun _ _ => id,fun _ _ => id⟩,?_,fun h => (fresh h).elim⟩
    exact Or.inl (by rw [show observe extra=inv (observe (rawAt 0)) from obs_neg _]; exact List.mem_cons_self ..)
  · obtain ⟨f,hf,af,c⟩ := raw _ mem
    exact ⟨f,hf,available_cons _ af,c⟩
theorem history_model (d : Data) (ok : checkInputs d=true) (ex : checkExtra d=true) {hist} (path : History hist) :
    ∃ p≤price d hist,∃ bank,Reach ((vars d.mask).map observe) p bank ∧ ∀ w∈seen hist,carries d bank w := by
  induction path with
  | empty =>
    exact base_history d ok ex
  | @gate h path a b ha hb op ih =>
    obtain ⟨p,count,bank,prev,old⟩ := ih
    let z := dataOp op a b
    change ∃ q≤price d (z::h),∃ next,Reach _ q next ∧ ∀ w∈seen (z::h),carries d next w
    by_cases yes : cheap d z (seen h)=true
    · refine ⟨p,by simpa [price,yes] using count,bank,prev,?_⟩
      intro w hw
      rcases List.mem_cons.mp (show w∈z::seen h from hw) with rfl|m
      · exact free_copy yes old
      · exact old _ m
    obtain ⟨f,gf,af,_⟩ := old a ha
    obtain ⟨g,gg,ag,_⟩ := old b hb
    have fresh := Reach.two op prev af ag
    refine ⟨p+1,by simp [price,yes];omega,_,fresh,?_⟩
    intro w hw
    rcases List.mem_cons.mp (show w∈z::seen h from hw) with rfl|m
    · exact ⟨_,op_compat d op gf gg,Or.inl (List.mem_cons_self ..),
        fun hh => False.elim (yes (Bool.or_eq_true_iff.mpr (Or.inl hh)))⟩
    obtain ⟨v,gv,av,dv⟩ := old _ m
    exact ⟨v,gv,available_cons _ av,dv⟩

end Complement2311.Face
namespace Complement2311
open PEqualNP.CircuitLowerBounds Cert Front2778
def ops (u v : Sig) : Finset Sig := {u&&&v,u|||v}
def admitted (s : Finset Sig) (u : Sig) := u=zero ∨ u=one ∨ u∈s
def source := inputs ++ [neg (inputs.getD 0 zero)]
def possible (s : Finset Sig) (u : Sig) := admitted s u ∨ ∃ a∈s,∃ b∈s,a≠b ∧ u∈ops a b
@[simp] theorem one_and (a : Sig) : one &&& a = a := BitVec.allOnes_and
@[simp] theorem and_one (a : Sig) : a &&& one = a := BitVec.and_allOnes
@[simp] theorem one_or (a : Sig) : one ||| a = one := BitVec.allOnes_or
@[simp] theorem or_one (a : Sig) : a ||| one = one := BitVec.or_allOnes
theorem admit_bin {s : Finset Sig} {a b : Sig} (d : Bool) (ha : admitted s a) (hb : admitted s b) :
    possible s (bin d a b) := by
  rcases ha with (rfl|rfl|ha)
  · cases d <;> simp_all [possible,admitted,bin,zero]
  · cases d <;> simp_all [possible,admitted,bin,zero]
  rcases hb with (rfl|rfl|hb)
  · cases d <;> simp_all [possible,admitted,bin,zero]
  · cases d <;> simp_all [possible,admitted,bin,zero]
  by_cases h : a=b
  · subst b;cases d <;> simp [possible,admitted,bin,ha]
  · exact Or.inr ⟨a,ha,b,hb,h,by cases d <;> simp [ops,bin]⟩
theorem read_admit {s} {w : List Sig} (sup : ∀ v∈w,admitted s v) (j : ℕ) : admitted s (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[j]? with
  | none => exact Or.inl rfl
  | some a => exact sup a (List.mem_of_getElem? h)
theorem admit_gate {s w} (sup : ∀ v∈w,admitted s v) (g : Gate)
    (ok : g.op=.and ∨ g.op=.or) (n : g.inputs.length≤2) : possible s (gv w g) := by
  rcases g with ⟨op,l⟩
  cases l with
  | nil => rcases ok with rfl|rfl <;> simp [possible,admitted,gv]
  | cons a l =>
    cases l with
    | nil =>
      rcases ok with rfl|rfl <;> apply Or.inl <;> simpa [gv,bin,zero] using read_admit sup a
    | cons b l =>
      cases l with
      | nil =>
        rcases ok with rfl|rfl
        · simpa [gv,bin] using admit_bin false (read_admit sup a) (read_admit sup b)
        · simpa [gv,bin,zero] using admit_bin true (read_admit sup a) (read_admit sup b)
      | cons c l => simp at n
theorem compile_unsigned (gs : List Gate) (j : ℕ) (w : List Sig) (s : Finset Sig)
    (ok : ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (sup : ∀ v∈w,admitted s v) (out : (execute gs w).getD j zero=graph) :
    build ops graph gs.length s := by
  induction gs generalizing w s with
  | nil =>
    change w.getD j zero=graph at out
    have got := out ▸ read_admit sup j
    rcases got with h|h|h
    · exact False.elim (graph_proper.1 h)
    · exact False.elim (graph_proper.2 h)
    · exact h
  | cons g gs ih =>
    have here := ok g (by simp)
    have rest : ∀ t∈gs,(t.op=.and ∨ t.op=.or) ∧ t.inputs.length≤2 :=
      fun t ht => ok t (List.mem_cons_of_mem _ ht)
    rcases admit_gate sup g here.1 here.2 with old|⟨a,ha,b,hb,ab,how⟩
    · apply Or.inl (ih (w++[gv w g]) s rest _ out)
      intro v hv
      rcases (show v∈w ∨ v=gv w g by simpa using hv) with m|rfl
      · exact sup _ m
      · exact old
    · refine Or.inr ⟨a,ha,b,hb,ab,gv w g,how,ih (w++[gv w g]) (insert (gv w g) s) rest ?_ out⟩
      intro v hv
      rcases (show v∈w ∨ v=gv w g by simpa using hv) with m|rfl
      · exact (sup _ m).imp_right (fun h => h.imp_right (fun q => Finset.mem_insert_of_mem q))
      · exact Or.inr (Or.inr (Finset.mem_insert_self ..))
end Complement2311
namespace Complement2311.Face
open Front2778
open Cert hiding inputs seed
def checked (d : Data) :=
  checkEnds d && checkInputs d && checkExtra d && properB (targetWord d) && geometry d
def rejects (d : Data) (k : ℕ) (ws hist : List S) :=
  decide (price d hist+k < d.lb+(ws.filter (dead d)).length)

theorem reject_sound {d : Data} (ok : checked d=true) {n ws hist}
    (past : History hist) (seenW : ∀w∈ws,w∈seen hist) (nd : ws.Nodup)
    (run : live Complement2311.ops graph n ws.toFinset) : rejects d n ws hist=false := by
  obtain ⟨⟨⟨⟨ends,inputsOk⟩,extraOk⟩,proper⟩,geo⟩ :=
    (show (((checkEnds d=true ∧ checkInputs d=true) ∧ checkExtra d=true) ∧ properB (targetWord d)=true) ∧ geometry d=true
      by simpa only [checked,Bool.and_eq_true] using ok)
  obtain ⟨p,amount,bank,prog,supply⟩ := history_model d inputsOk extraOk past
  let marks := (ws.filter (dead d)).toFinset
  have sub : marks ⊆ ws.toFinset := fun w hw => List.mem_toFinset.mpr (List.mem_filter.mp (List.mem_toFinset.mp hw)).1
  have representation (w : S) (mem : w∈ws.toFinset) :
      ∃ f,(model d).good w f ∧ Available bank f ∧ (w∈marks → Constant f) := by
    obtain ⟨f,good,there,c⟩ := supply w (seenW w (List.mem_toFinset.mp mem))
    exact ⟨f,good,there,fun h => c (List.mem_filter.mp (List.mem_toFinset.mp h)).2⟩
  have low := pinned_lower d geo
  have same : Price.choices (model d)=Complement2311.ops := by
    funext u v
    simp [Price.choices,model,dataOp,Complement2311.ops]
  have priceOK := Price.cut_bound (model d) graph (observe (targetWord d))
    (fun _ hh => terminal ends hh) (observe_proper (proper_of _ proper)) (same.symm ▸ run) prog
    low marks sub representation
  have markLen : marks.card=(ws.filter (dead d)).length := List.toFinset_card_of_nodup (nd.filter _)
  rw [markLen] at priceOK
  simp only [rejects,decide_eq_false_iff_not,not_lt]
  omega

end Complement2311.Face
namespace Cert
theorem raw15 : Lower inputs graph 15 := by
  intro p bank prog output
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live graph_proper prog output
  have plain : S=inputs.toFinset := by
    rcases all_roots run (fun w hw => List.mem_append_left _ (sub w hw)) with direct|seeded
    · exact direct
    have h : seed∈S := seeded ▸ List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_singleton_self _))
    exact False.elim ((by decide +kernel : seed∉inputs) (sub _ h))
  subst S
  by_contra! small
  exact dead_start (before_sound known383 valid383) geomdead tablesdead k t (by omega) run
end Cert
namespace Complement2311.Face
open Front2778
open Cert hiding inputs seed
def full : Data := ⟨511,15,0x300000001000003000000000000000000000000010000003000000000000000040000000201023048,0x40002000000000000000000000000001000200000000000010300000000000000040000100100000000200004040000000000,[3,6,12,13,17,24,33,66,132,133,160,264,265,288,320,321],[42,50,69,104,116,138,200,201,208,261,276,385,402],0,511,0⟩

theorem full_inputs : checkInputs full=true := by decide +kernel
theorem full_extra : checkExtra full=true := by decide +kernel
theorem full_end : checkEnds full=true := by decide +kernel
theorem full_goal : targetWord full=graph := by decide +kernel
theorem full_roots : vars full.mask=rawFull := by decide +kernel

theorem max_price (d : Data) (hist : List S) : price d hist≤hist.length+1 := by
  induction hist with
  | nil => simp only [price,List.length_nil]; split <;> decide
  | cons z h ih => simp only [price,List.length_cons]; split <;> omega

def badGate (z : S) (hist : List S) :=
  cheap full z (seen hist)

theorem bad_short {z : S} {hist ws : List S} {k} (past : History hist) (bad : badGate z hist=true)
    (sup : ∀w∈ws,w∈z::seen hist) (run : live Complement2311.ops graph k ws.toFinset) :
    15≤1+hist.length+k := by
  obtain ⟨p,hp,bank,prog,supply⟩ := history_model full full_inputs full_extra past
  rw [full_roots] at prog
  have rep (w : S) (hw : w∈ws.toFinset) : ∃ f,(model full).good w f ∧ Available bank f ∧ (w∈(∅ : Finset S) → Constant f) := by
    have carry : carries full bank w := by
      rcases List.mem_cons.mp (sup _ (List.mem_toFinset.mp hw)) with rfl|here
      · exact free_copy bad supply
      exact supply _ here
    obtain ⟨f,good,af,_⟩ := carry
    exact ⟨f,good,af,by simp⟩
  have same : Price.choices (model full)=Complement2311.ops := by
    funext u v
    simp [Price.choices,model,dataOp,Complement2311.ops]
  have tight := Price.cut_bound (model full) graph (observe graph)
    (fun _ hg => full_goal ▸ terminal full_end hg) (observe_proper graph_proper) (same.symm ▸ run) prog
    raw15 ∅ (Finset.empty_subset _) rep
  have upper := max_price full hist
  simp only [Finset.card_empty,Nat.add_zero] at tight
  omega
end Complement2311.Face
namespace Complement2311
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Cert Front2778
def wrapper (C : Circuit) : Circuit := ⟨⟨.not,[0]⟩::C.gates,C.output⟩
theorem wrapper_fan (C : Circuit) (ok : FanInTwo C) : FanInTwo (wrapper C) := by
  intro g h
  rcases List.mem_cons.mp h with rfl|h
  · simp
  · exact ok _ h
theorem wrapper_eval (C : Circuit) (x : Fin 9→Bool) :
    (wrapper C).eval (List.ofFn x) = C.eval (List.ofFn x ++ [!x 0]) := by
  dsimp [wrapper,Circuit.eval,Circuit.wires,GateOp.eval]
  simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
theorem input_build (C : Circuit) (fan : FanInTwo C) (ok : ∀ g∈C.gates,g.op=.and ∨ g.op=.or)
    (works : ∀ x : Fin 9→Bool,C.eval (List.ofFn x ++ [!x 0])=edge x) :
    build ops graph C.size source.toFinset := by
  have eq : (execute C.gates source).getD C.output zero=graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    have ev := table_eval (wrapper C) (wrapper_fan C fan) C.output r
    change bit r ((execute C.gates source).getD C.output zero)=(wrapper C).eval (List.ofFn (sample r)) at ev
    exact ev.trans ((wrapper_eval C _).trans ((works _).trans (edge_table r).symm))
  exact compile_unsigned _ _ _ _ (fun g h => ⟨ok _ h,(fan _ h).2⟩)
    (fun _ h => Or.inr (Or.inr (List.mem_toFinset.mpr h))) eq
end Complement2311
namespace Complement2311
open Cert Front2778
def distinguish (p n : Row) (a : Sig) := bit p a=true ∧ bit n a=false
theorem transfer (p n : Row) (a b z : Sig) (hz : z∈ops a b) :
    distinguish p n z → distinguish p n a ∨ distinguish p n b := by
  rcases (show z=a&&&b ∨ z=a|||b by simpa [ops] using hz) with rfl|rfl <;>
    simp only [distinguish,bit,BitVec.getLsbD_and,BitVec.getLsbD_or] <;>
    cases a.getLsbD p.val <;> cases a.getLsbD n.val <;> cases b.getLsbD p.val <;> cases b.getLsbD n.val <;> decide
def sites : List (Row × Row) := [(3,42), (3,69), (6,42), (12,116), (17,69), (33,69), (66,42), (132,116), (264,42)]
theorem each_raw : ∀ a∈inputs,∃ v∈sites, distinguish v.1 v.2 graph ∧
    ∀ w∈source, distinguish v.1 v.2 w → w=a := by
  have finite : ∀ i : Fin 9, let v := sites.getD i.val (0,0)
      distinguish v.1 v.2 graph ∧
      ∀ j : Fin 10, distinguish v.1 v.2 (source.getD j.val zero) →
        source.getD j.val zero=inputs.getD i.val zero := by unfold distinguish; decide +kernel
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem ha
  let u : Fin 9 := ⟨i,hi⟩
  have e : i<sites.length := u.isLt
  have vIn : sites.getD i (0,0) ∈ sites := by rw [List.getD_eq_getElem _ _ e];exact List.getElem_mem ..
  refine ⟨_,vIn,(finite u).1,?_⟩
  intro w hw d
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hw
  let q : Fin 10 := ⟨j,hj⟩
  have hq := (finite u).2 q
  change distinguish (sites.getD i (0,0)).1 (sites.getD i (0,0)).2 (source.getD j zero) → source.getD j zero=inputs.getD i zero at hq
  rw [List.getD_eq_getElem _ _ hj,List.getD_eq_getElem _ _ hi] at hq
  exact hq d
theorem root_cases {s k} (h : live ops graph k s) (sub : s⊆source.toFinset) :
    s=inputs.toFinset ∨ s=source.toFinset := by
  have required : inputs.toFinset⊆s := by
    intro a ha
    obtain ⟨v,_,sep,only⟩ := each_raw a (List.mem_toFinset.mp ha)
    obtain ⟨w,hw,good⟩ := live_separates _ sep (transfer v.1 v.2) h
    exact (only w (List.mem_toFinset.mp (sub hw)) good) ▸ hw
  by_cases use : neg (inputs.getD 0 zero)∈s
  · right
    apply Finset.Subset.antisymm sub
    intro w hw
    rcases (show w∈inputs ∨ w=neg (inputs.getD 0 zero) by simpa [source,or_comm] using hw) with old|rfl
    · exact required (List.mem_toFinset.mpr old)
    · exact use
  · left
    apply Finset.Subset.antisymm _ required
    intro w hw
    rcases (show w∈inputs ∨ w=neg (inputs.getD 0 zero) by simpa [source,or_comm] using sub hw) with old|rfl
    · exact List.mem_toFinset.mpr old
    · exact (use hw).elim
theorem to_reach {s k} (h : live ops graph k s) {roots : List (Wire Row)} {p bank}
    (history : Reach roots p bank) (know : ∀ w∈s, Available bank (observe w)) :
    ∃ q≤p+k,∃ last,Reach roots q last ∧ Available last (observe graph) := by
  induction k generalizing s p bank with
  | zero =>
    change s={graph} at h
    exact ⟨p,by omega,bank,history,know graph (h ▸ Finset.mem_singleton_self _)⟩
  | succ k ih =>
    rcases h with sk|⟨a,ha,b,hb,_,z,how,_,r,rfl,tail⟩
    · obtain ⟨q,num,last,done,hit⟩ := ih sk history know
      exact ⟨q,by omega,last,done,hit⟩
    obtain ⟨d,eq⟩ : ∃ d : Bool,z=bin d a b := by
      rcases (show z=a&&&b ∨ z=a|||b by simpa [ops] using how) with l|r
      · exact ⟨false,l⟩
      · exact ⟨true,r⟩
    have built := Reach.two d history (know a ha) (know b hb)
    have next : ∀w∈insert z r, Available (combine d (observe a) (observe b)::bank) (observe w) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl|hw
      · rw [eq,obs_bin]; exact Or.inl (List.mem_cons_self ..)
      · exact available_cons _ (know _ (by simp [hw]))
    obtain ⟨q,num,last,done,hit⟩ := ih tail built next
    exact ⟨q,by omega,last,done,hit⟩
theorem no_plain (h : live ops graph 14 inputs.toFinset) : False := by
  let roots := inputs.map observe
  have sup : ∀ w∈inputs.toFinset, Available roots (observe w) := fun _ hw =>
    Or.inl (List.mem_map_of_mem (List.mem_toFinset.mp hw))
  obtain ⟨q,num,last,done,hit⟩ := to_reach h (Reach.start (roots:=roots)) sup
  have lb := raw15 q last done hit
  omega
end Complement2311
namespace Complement2311.Search
open Front2778
open Cert hiding inputs seed
abbrev posRows := Face.full.ps
abbrev nMask := Face.full.neg
def remaining (p : Row) : List Sig → Sig
  | [] => nMask
  | w::ws => if bit p w then w&&&remaining p ws else remaining p ws
def separates (ws : List Sig) := posRows.all (fun p => remaining p ws==0)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a,rest) :: (singles rest).map (fun (b,bs) => (b,a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b,bs) => (a,b,bs)) ++
      (pairs rest).map (fun (b,c,bs) => (b,c,a :: bs))

theorem pick_one {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a,rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a,rest),hm,rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a,b,rest) ∈ pairs ws ∨ (b,a,rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b,r),hm,rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r,.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a,r),hm,rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a,b,r),hm,rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b,a,r),hm,rfl⟩))
def keepChoices (a b : Sig) (r : List Sig) := [r, a::r, b::r, a::b::r]

theorem recover_kept {ws r : List Sig} {a b : Sig} {needed : Finset Sig}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simpa [hp.mem_iff] using (hp.mem_iff (a := v))
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a::b::r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a::r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b::r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

def children (k : ℕ) (ws hist : List Sig) := (pairs ws).flatMap fun (a,b,r) =>
  [a&&&b,a|||b].flatMap fun z =>
    if !Face.badGate z hist then (keepChoices a b r).filterMap fun retained =>
      let child := z::retained
      if child.length≤k+1 && separates child then some child else none
    else []

end Complement2311.Search
namespace Complement2311.Order
open Front2778 Cert

structure Cmd where
  left : Sig
  right : Sig
  gate : Bool
  deriving DecidableEq

def Cmd.val (c : Cmd) := bin c.gate c.left c.right
set_option maxRecDepth 12000 in
theorem Cmd.choice (c : Cmd) : c.val∈ops c.left c.right := by
  cases c with | mk a b d => cases d <;> simp [Cmd.val,ops,bin]

inductive Plan : Finset Sig → List Cmd → Prop where
  | done {s} (out : graph∈s) : Plan s []
  | add {s c cs} (a : c.left∈s) (b : c.right∈s) (diff : c.left≠c.right)
      (tail : Plan (insert c.val s) cs) : Plan s (c::cs)

set_option maxRecDepth 12000 in
theorem from_build {n s} (h : build ops graph n s) : ∃ cs,cs.length≤n ∧ Plan s cs := by
  induction n generalizing s with
  | zero => exact ⟨[],by decide,.done h⟩
  | succ n ih =>
    rcases h with skip|⟨a,ha,b,hb,ne,z,option,tail⟩
    · obtain ⟨cs,size,prog⟩ := ih skip
      exact ⟨cs,by omega,prog⟩
    obtain ⟨d,hz⟩ : ∃ d : Bool,z=bin d a b := by
      rcases (show z=a&&&b ∨ z=a|||b by simpa [ops] using option) with e|e
      · exact ⟨false,e⟩
      · exact ⟨true,e⟩
    obtain ⟨cs,size,prog⟩ := ih tail
    exact ⟨⟨a,b,d⟩::cs,by simp;omega,.add ha hb ne (by change Plan (insert (bin d a b) s) cs; rwa [←hz])⟩

set_option maxRecDepth 12000 in
theorem exchange {p : List Cmd} {s c d cs} (h : Plan s (p++c::d::cs))
    (l : d.left≠c.val) (r : d.right≠c.val) : Plan s (p++d::c::cs) := by
  induction p generalizing s with
  | nil =>
    cases h with
    | add a b diff next =>
      cases next with
      | add e f sep tail =>
        apply Plan.add ((Finset.mem_insert.mp e).resolve_left l) ((Finset.mem_insert.mp f).resolve_left r) sep
        apply Plan.add (Finset.mem_insert_of_mem a) (Finset.mem_insert_of_mem b) diff
        simpa only [Finset.insert_comm c.val d.val] using tail
  | cons x p ih =>
    cases h with
    | add a b neq next => exact .add a b neq (ih next)

def radix : Nat := 2^512
def weight : List Cmd → Nat
  | [] => 0
  | c::cs => c.val.toNat*radix^cs.length+weight cs

def Sorted (cs : List Cmd) := ∀ p c d t, cs=p++c::d::t →
  d.left=c.val ∨ d.right=c.val ∨ c.val.toNat≤d.val.toNat

end Complement2311.Order
namespace Complement2311.Order
open Front2778 Cert

theorem promote {s} (p block : List Cmd) (d : Cmd) (t : List Cmd)
    (run : Plan s (p++block++d::t))
    (available : ∀ u∈block,d.left≠u.val ∧ d.right≠u.val) : Plan s (p++d::(block++t)) := by
  induction block using List.reverseRecOn generalizing t with
  | nil => simpa using run
  | append_singleton v u ih =>
    have lu:=available u (by simp)
    have prior : Plan s ((p++v)++u::d::t) := by simpa [List.append_assoc] using run
    have shift:=exchange prior lu.1 lu.2
    have h:=ih (u::t) (by simpa [List.append_assoc] using shift)
      (fun x hx=>available x (List.mem_append_left _ hx))
    simpa [List.append_assoc] using h

theorem weight_small (cs : List Cmd) : weight cs<radix^cs.length := by
  induction cs with
  | nil => simp [weight]
  | cons c cs ih =>
    have digit : c.val.toNat+1≤radix := c.val.isLt
    have total:=Nat.mul_le_mul_right (radix^cs.length) digit
    simp only [weight,List.length_cons,pow_succ]
    nlinarith

theorem prefix_lt (p : List Cmd) {xs ys : List Cmd} (same : xs.length=ys.length)
    (lt : weight xs<weight ys) : weight (p++xs)<weight (p++ys) := by
  induction p with
  | nil => exact lt
  | cons c p ih =>
    simp only [List.cons_append,weight,List.length_append,same]
    exact Nat.add_lt_add_left ih _

theorem rotation_lt (p block : List Cmd) (c d : Cmd) (t : List Cmd) (lt : d.val.toNat<c.val.toNat) :
    weight (p++d::c::(block++t)) < weight (p++c::(block++d::t)) := by
  apply prefix_lt p (by simp;omega)
  have len : (c::(block++t)).length=(block++d::t).length := by simp;omega
  have rest:=weight_small (c::(block++t))
  rw [len] at rest
  have rank:=Nat.mul_le_mul_right (radix^(block++d::t).length) lt
  change d.val.toNat*radix^(c::(block++t)).length+weight (c::(block++t)) <
    c.val.toNat*radix^(block++d::t).length+weight (block++d::t)
  rw [len]
  nlinarith

def LexSorted (cs : List Cmd) := ∀ p c block d t, cs=p++c::(block++d::t) →
  (∀ u∈c::block,d.left≠u.val ∧ d.right≠u.val) → c.val.toNat≤d.val.toNat

theorem lex_ordered {s n} (h : build ops graph n s) :
    ∃ cs,cs.length≤n ∧ Plan s cs ∧ LexSorted cs := by
  classical
  obtain ⟨cs,bound,run⟩ := from_build h
  let feasible (w : Nat) := ∃ ds : List Cmd,ds.length≤n ∧ Plan s ds ∧ weight ds=w
  have witness : ∃ w,feasible w := ⟨_,cs,bound,run,rfl⟩
  obtain ⟨ds,sz,pl,rank⟩ := Nat.find_spec witness
  refine ⟨ds,sz,pl,?_⟩
  intro p c block d t eq legs
  by_contra! wrong
  have head : Plan s (p++(c::block)++d::t) := by simpa [List.append_assoc,eq] using pl
  have moved:=promote p (c::block) d t head legs
  have sz' : (p++d::c::(block++t)).length≤n := by simpa [eq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using sz
  have minimum:=Nat.find_min' witness (show feasible (weight (p++d::c::(block++t))) from ⟨_,sz',moved,rfl⟩)
  have improved:=rotation_lt p block c d t wrong
  rw [←eq,rank] at improved
  omega
end Complement2311.Order
namespace Complement2311.Order
open Cert
def allows : List Sig → Sig → Sig → Sig → Bool
  | [],_,_,_ => true
  | v::vs,a,b,z => a==v || b==v || (decide (v.toNat≤z.toNat) && allows vs a b z)

def DeepFollows : List Sig → List Cmd → Prop
  | _,[] => True
  | h,c::cs => allows h c.left c.right c.val=true ∧ DeepFollows (c.val::h) cs

theorem allowed_prefix {cs} (sort : LexSorted cs) (p block : List Cmd) (d : Cmd) (t : List Cmd)
    (eq : cs=p++block++d::t) (clear : ∀ u∈block,d.left≠u.val ∧ d.right≠u.val) :
    allows (p.reverse.map Cmd.val) d.left d.right d.val=true := by
  induction p using List.reverseRecOn generalizing block with
  | nil => rfl
  | append_singleton p c ih =>
    simp only [List.reverse_append,List.reverse_singleton,List.singleton_append,List.map_cons,allows]
    by_cases left : d.left=c.val
    · simp [left]
    by_cases right : d.right=c.val
    · simp [right]
    have free : ∀ u∈c::block,d.left≠u.val ∧ d.right≠u.val := by
      intro u mem
      rcases List.mem_cons.mp mem with rfl|later
      · exact ⟨left,right⟩
      exact clear _ later
    have form : cs=p++c::(block++d::t) := by simpa [List.append_assoc] using eq
    have small:=sort p c block d t form free
    have next:=ih (c::block) (by simpa [List.append_assoc] using form) free
    simpa [left,right,small] using next

theorem deep_follows {cs} (sort : LexSorted cs) : DeepFollows [] cs := by
  have aux (rem : List Cmd) (p : List Cmd) (eq : cs=p++rem) : DeepFollows (p.reverse.map Cmd.val) rem := by
    induction rem generalizing p with
    | nil => trivial
    | cons c rem ih =>
      refine ⟨allowed_prefix sort p [] c rem (by simpa using eq) (by simp),?_⟩
      simpa using ih (p++[c]) (by simpa [List.append_assoc] using eq)
  exact aux cs [] rfl
end Complement2311.Order
namespace Complement2311.Order
open Front2778 Cert

inductive Needed : Finset Sig → List Cmd → Prop where
  | done : Needed {graph} []
  | add {r : Finset Sig} {c : Cmd} {cs : List Cmd} (different : c.left≠c.right)
      (fresh : c.val∉insert c.left (insert c.right r)) (tail : Needed (insert c.val r) cs) :
      Needed (insert c.left (insert c.right r)) (c::cs)

theorem Needed.live {s cs} (h : Needed s cs) : Front2778.live ops graph cs.length s := by
  induction h with
  | done => rfl
  | @add r c cs ne fresh tail ih =>
    exact Or.inr ⟨c.left,by simp,c.right,by simp,ne,c.val,c.choice,fresh,r,rfl,ih⟩

theorem compress_cmds {s cs} (prog : Plan s cs) :
    ∃ ds,ds.Sublist cs ∧ ∃ t⊆s,Needed t ds := by
  induction prog with
  | done hit =>
    exact ⟨[],.slnil,{graph},Finset.singleton_subset_iff.mpr hit,.done⟩
  | @add s c cs a b diff tail ih =>
    obtain ⟨ds,sub,t,old,prog⟩ := ih
    by_cases already : t⊆s
    · exact ⟨ds,sub.cons _,t,already,prog⟩
    have inT : c.val∈t := by
      by_contra no
      apply already
      intro x hx
      exact (Finset.mem_insert.mp (old hx)).resolve_left (fun e=>no (e ▸ hx))
    have fresh : c.val∉s := fun h => already ((Finset.insert_eq_of_mem h) ▸ old)
    let rest := t.erase c.val
    have smaller : rest⊆s := by
      intro x hx
      exact (Finset.mem_insert.mp (old (Finset.mem_erase.mp hx).2)).resolve_left (Finset.mem_erase.mp hx).1
    have included := Finset.insert_subset a (Finset.insert_subset b smaller)
    exact ⟨c::ds,sub.cons₂ _,_,included,.add diff (fun h=>fresh (included h)) (by simpa [rest,Finset.insert_erase inT] using prog)⟩

theorem must_spend {k s} (h : Front2778.live ops graph k s) (inside : s⊆source.toFinset) : 14≤k := by
  let roots := inputs.map observe
  let v := inputs.getD 0 zero
  have existsV : v∈inputs := by decide +kernel
  have first : Available roots (observe v) := Or.inl (List.mem_map_of_mem existsV)
  have hist := Reach.one Reach.start first
  have present : ∀w∈s, Available (inv (observe v)::roots) (observe w) := by
    intro w hw
    have mem := List.mem_toFinset.mp (inside hw)
    rcases List.mem_append.mp mem with x|last
    · exact available_cons _ (Or.inl (List.mem_map_of_mem x))
    have eq : w=neg v := List.mem_singleton.mp last
    rw [eq,obs_neg]
    exact Or.inl (List.mem_cons_self ..)
  obtain ⟨q,num,last,r,hit⟩ := to_reach h hist present
  have lower := raw15 q last r hit
  omega

theorem ordered_root (h : build ops graph 14 source.toFinset) :
    ∃ cs,cs.length=14 ∧ Needed source.toFinset cs ∧ LexSorted cs := by
  obtain ⟨cs,small,p,order⟩ := lex_ordered h
  obtain ⟨ds,sub,t,inside,need⟩ := compress_cmds p
  have ge := must_spend need.live inside
  have le := sub.length_le
  have same : ds=cs := sub.eq_of_length (by omega)
  subst ds
  have count : cs.length=14 := by omega
  rcases root_cases (count ▸ need.live) inside with plain|all
  · exact False.elim (no_plain (plain ▸ (count ▸ need.live)))
  exact ⟨cs,count,all ▸ need,order⟩
end Complement2311.Order
namespace Complement2311.Search
open Front2778
open Cert hiding inputs seed
open Complement2311.Order

theorem allows_comm (hist : List Sig) (a b z : Sig) : allows hist a b z=allows hist b a z := by
  induction hist with
  | nil => rfl
  | cons v vs ih => simp only [allows,ih,Bool.or_comm (a==v) (b==v)]

theorem Needed.head {s c cs} (r : Needed s (c::cs)) : ∃ t,s=insert c.left (insert c.right t) ∧
    c.left≠c.right ∧ c.val∉s ∧ Needed (insert c.val t) cs := by
  cases r with
  | @add t a l ne fresh next => exact ⟨t,rfl,ne,fresh,next⟩

def sortedChildren (k : ℕ) (ws hist : List Sig) := (pairs ws).flatMap fun (a,b,r) =>
  [a&&&b,a|||b].flatMap fun z =>
    if allows hist a b z && !Face.badGate z hist then (keepChoices a b r).filterMap fun retained =>
      let child := z::retained
      if child.length≤k+1 && separates child then some child else none
    else []

end Complement2311.Search
namespace Complement2311.Face
open Cert hiding inputs seed
open Front2778

structure Fresh where
  gate : Bool
  left : Fin 10
  right : Fin 10
def pool (useExtra : Bool) := if useExtra then start else rawFull
def lookup (useExtra : Bool) (i : Fin 10) := (pool useExtra).getD i.val zero
def Fresh.value (a : Fresh) (useExtra : Bool) := dataOp a.gate (lookup useExtra a.left) (lookup useExtra a.right)
def usable (useExtra : Bool) (a : Fresh) :=
  decide (a.left.val < (pool useExtra).length ∧ a.right.val < (pool useExtra).length)
def planBank (useExtra : Bool) (jobs : List Fresh) := jobs.map (fun a=>a.value useExtra) ++ pool useExtra
def initialPrice (d : Data) (useExtra : Bool) := if useExtra then price d [] else 0

theorem initial_model {d : Data} (ok : checkInputs d=true) (ex : checkExtra d=true) (useExtra : Bool) :
    ∃ p ≤ initialPrice d useExtra, ∃ bank,Reach ((vars d.mask).map observe) p bank ∧ ∀ w∈pool useExtra,carries d bank w := by
  cases useExtra with
  | false => exact ⟨0,Nat.zero_le _,_,.start,fun _ hw=>present_raw d ok hw⟩
  | true => exact base_history d ok ex

theorem plan_model {d : Data} (ok : checkInputs d=true) (ex : checkExtra d=true) (useExtra : Bool)
    (jobs : List Fresh) (available : jobs.all (usable useExtra)=true) :
    ∃ p ≤ initialPrice d useExtra+jobs.length,∃ bank,Reach ((vars d.mask).map observe) p bank ∧
        ∀ w∈planBank useExtra jobs,carries d bank w := by
  induction jobs with
  | nil => simpa [planBank] using initial_model ok ex useExtra
  | cons a jobs ih =>
    have passes := Bool.and_eq_true_iff.mp (show usable useExtra a && jobs.all (usable useExtra) = true from available)
    have ij := of_decide_eq_true passes.1
    obtain ⟨p,number,bank,r,prev⟩ := ih passes.2
    have read (i : Fin 10) (hi : i.val < (pool useExtra).length) : carries d bank (lookup useExtra i) := by
      apply prev
      apply List.mem_append_right
      rw [lookup,List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem ..
    obtain ⟨f,hf,af,_⟩ := read a.left ij.1
    obtain ⟨g,hg,ag,_⟩ := read a.right ij.2
    refine ⟨p+1,by simp only [List.length_cons];omega,_,Reach.two a.gate r af ag,?_⟩
    intro w hw
    rcases List.mem_cons.mp (show w∈a.value useExtra::planBank useExtra jobs from hw) with rfl|prior
    · by_cases h : dead d (a.value useExtra)=true
      · exact trivial h
      exact ⟨_,op_compat d a.gate hf hg,Or.inl (List.mem_cons_self ..),fun impossible => (h impossible).elim⟩
    obtain ⟨v,hv,av,c⟩ := prev w prior
    exact ⟨v,hv,available_cons _ av,c⟩

def planChecks (d : Data) (ws : List S) (extraOn : Bool) (jobs : List Fresh) :=
  jobs.all (usable extraOn) && ws.all (fun w => cheap d w (planBank extraOn jobs))

theorem synth_bound {d : Data} (ok : checked d=true) {n ws on jobs} (tests : planChecks d ws on jobs=true)
    (nd : ws.Nodup) (run : live Complement2311.ops graph n ws.toFinset) :
    d.lb+(ws.filter (dead d)).length ≤ initialPrice d on+jobs.length+n := by
  obtain ⟨⟨⟨⟨ends,inputsOk⟩,extraOk⟩,proper⟩,geo⟩ :=
    (show (((checkEnds d=true ∧ checkInputs d=true) ∧ checkExtra d=true) ∧ properB (targetWord d)=true) ∧ geometry d=true
      by simpa only [checked,Bool.and_eq_true] using ok)
  obtain ⟨gates,cover⟩ := Bool.and_eq_true_iff.mp tests
  obtain ⟨p,amount,bank,prog,supply⟩ := plan_model inputsOk extraOk on jobs gates
  let marks := (ws.filter (dead d)).toFinset
  have sub : marks ⊆ ws.toFinset := fun w hw => List.mem_toFinset.mpr (List.mem_filter.mp (List.mem_toFinset.mp hw)).1
  have representation (w : S) (mem : w∈ws.toFinset) :
      ∃ f,(model d).good w f ∧ Available bank f ∧ (w∈marks → Constant f) := by
    obtain ⟨f,good,there,c⟩ := free_copy (List.all_eq_true.mp cover w (List.mem_toFinset.mp mem)) supply
    exact ⟨f,good,there,fun h => c (List.mem_filter.mp (List.mem_toFinset.mp h)).2⟩
  have same : Price.choices (model d)=Complement2311.ops := by
    funext u v
    simp [Price.choices,model,dataOp,Complement2311.ops]
  have bound := Price.cut_bound (model d) graph (observe (targetWord d))
    (fun _ hh => terminal ends hh) (observe_proper (proper_of _ proper)) (same.symm ▸ run) prog
    (pinned_lower d geo) marks sub representation
  have markLen : marks.card=(ws.filter (dead d)).length := List.toFinset_card_of_nodup (nd.filter _)
  rw [markLen] at bound
  omega
end Complement2311.Face
namespace Complement2311.Search
open Front2778
open Cert hiding inputs seed
open Complement2311.Order

abbrev Hints := Nat → Nat × Nat × Nat
abbrev Table := Array (Nat × Nat)
abbrev Facts := Nat → Option Face.Data
def decode : Nat → Nat → List Face.Fresh
  | 0, _ => []
  | n+1, packed =>
    if packed=0 then [] else
      let v := (packed &&& 255)-1
      ⟨decide (100≤v),Fin.ofNat 10 ((v % 100)/10),Fin.ofNat 10 (v % 10)⟩::decode n (packed >>> 8)

def proofCut (hints : Hints) (facts : Facts) (i k : Nat) (ws h : List Sig) :=
  let (fi,mode,bits) := hints i
  (facts fi).any fun d =>
    if mode=0 then Face.rejects d k ws h
    else
      let on := mode==2
      let actions := decode 12 bits
      Face.planChecks d ws on actions &&
        decide (Face.initialPrice d on+actions.length+k<d.lb+(ws.filter (Face.dead d)).length)

theorem proofCut_no {hints facts i k ws h}
    (valid : ∀ j d,facts j=some d → Face.checked d=true)
    (past : Face.History h) (sup : ∀w∈ws,w∈Face.seen h) (nd : ws.Nodup) (run : live ops graph k ws.toFinset) :
    proofCut hints facts i k ws h=false := by
  unfold proofCut
  obtain ⟨fi,mode,bits⟩ := hints i
  dsimp only
  cases eq : facts fi with
  | none => rfl
  | some d =>
    simp only [Option.any_some]
    split
    · exact Face.reject_sound (valid _ _ eq) past sup nd run
    apply Bool.eq_false_iff.mpr
    intro yes
    have both := Bool.and_eq_true_iff.mp yes
    have bound := Face.synth_bound (valid _ _ eq) both.1 nd run
    exact (Nat.not_lt.mpr bound) (of_decide_eq_true both.2)

def unpack (p : Nat) : Nat × Nat :=
  if !p.testBit 0 then (0, p >>> 1) else
  if !p.testBit 1 then (1+((p >>> 2) &&& 7), p >>> 5) else
  if !p.testBit 2 then (9+((p >>> 3) &&& 15), p >>> 7) else
  if !p.testBit 3 then (25+((p >>> 4) &&& 63), p >>> 10) else
  if !p.testBit 4 then (89+((p >>> 5) &&& 127), p >>> 12) else
  if !p.testBit 5 then (217+((p >>> 6) &&& 127), p >>> 13) else
  if !p.testBit 6 then (345+((p >>> 7) &&& 127), p >>> 14) else
  if !p.testBit 7 then (473+((p >>> 8) &&& 127), p >>> 15) else
  if !p.testBit 8 then (601+((p >>> 9) &&& 31), p >>> 14) else
  if !p.testBit 9 then (633+((p >>> 10) &&& 31), p >>> 15) else
  if !p.testBit 10 then (665+((p >>> 11) &&& 7), p >>> 14) else
  if !p.testBit 11 then (673+((p >>> 12) &&& 7), p >>> 15) else
  if !p.testBit 12 then (681+((p >>> 13) &&& 3), p >>> 15) else
  if !p.testBit 13 then (685, p >>> 14) else
  if !p.testBit 14 then (686, p >>> 15) else
  (687, p >>> 15)

def scan (hints : Hints) (facts : Facts) (k : Nat) (hist : List Sig) (next : Nat→List Sig→List Sig→Bool) :
    List (List Sig) → Nat → Nat → Bool
  | [],_,_ => true
  | []::_,_,_ => false
  | (z::r)::more,idx,packed =>
    let code := (unpack packed).1
    let localCheck := if code=1 then next idx (z::r) (z::hist) else proofCut hints facts code k (z::r) (z::hist)
    localCheck && scan hints facts k hist next more (idx+if code=1 then 1 else 0) (unpack packed).2

theorem scan_seen {hints facts k hist next kids idx packed z r}
    (all : scan hints facts k hist next kids idx packed=true) (mem : z::r∈kids) :
    (∃ j,proofCut hints facts j k (z::r) (z::hist)=true) ∨ ∃ i,next i (z::r) (z::hist)=true := by
  induction kids generalizing idx packed with
  | nil => simp at mem
  | cons child more ih =>
    cases child with
    | nil => simp [scan] at all
    | cons v vs =>
      have both := Bool.and_eq_true_iff.mp all
      rcases List.mem_cons.mp mem with eq|later
      · obtain rfl := (List.cons.inj eq).1
        obtain rfl := (List.cons.inj eq).2
        by_cases zero : (unpack packed).1=1
        · exact Or.inr ⟨_,by simpa [zero] using both.1⟩
        · exact Or.inl ⟨_,by simpa [zero] using both.1⟩
      exact ih both.2 later

end Complement2311.Search
namespace Complement2311.Face
def d0 : Data := ⟨494,11,0x100000001000001000000000000000000000000010000001000000000000000040000000000001040,0x4000000000000000000000000000000100000000000000100000000000000040000000110000000000000040000000000,[6,12,66,132,160,264,288,320],[42,100,104,138,200,260,386],0,494,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f0 : checked d0=true := by decide +kernel
def d1 : Data := ⟨510,12,0x100000001000001000000000000000000000000010000001000000000000000040000000001001040,0x40000000000000000000000000000001000000000000000010100000000000000040000100100000000000004040000000000,[6,12,24,66,132,160,264,288,320],[42,50,104,116,138,200,208,276,402],0,510,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f1 : checked d1=true := by decide +kernel
def d2 : Data := ⟨383,13,0x300000001000003000000000000000000000000000000000000000000000000040000000201023048,0x1400200000000000000000000000000000000000100100000002200004040000000000,[3,6,12,13,17,24,33,66,264,265,288,320,321],[42,50,69,73,104,116,261,274,276],0,383,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f2 : checked d2=true := by decide +kernel
def d3 : Data := ⟨447,13,0x1000003000000000000000000000000010000003000000000000000000000000201023048,0x40002000000000000000000000000001000200000000000000000000000000000060000000000000000000014040000000000,[3,6,12,13,17,24,33,132,133,160,264,265,288],[42,50,52,137,138,261,276,385,402],0,447,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f3 : checked d3=true := by decide +kernel
def d4 : Data := ⟨334,7,0x100000000000001000000000000000000000000000000000000000000000000040000000000001040,0x140000000000000000000000000000000000000000000001100000000000000400,[6,12,66,264,320],[10,68,72,258,260],0,334,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f4 : checked d4=true := by decide +kernel
def d5 : Data := ⟨428,7,0x1000001000000000000000000000000010000001000000000000000000000000000001000,0x1000000000000000000000000000000100000000000000000000000000000010000000000000000000000011000000000,[12,132,160,264,288],[36,40,136,260,384],0,428,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f5 : checked d5=true := by decide +kernel
def d6 : Data := ⟨350,8,0x100000000000001000000000000000000000000000000000000000000000000040000000001001040,0x1400000000000000000000000000000000000000000000001001000000000000000400,[6,12,24,66,264,320],[10,72,84,274,276],0,350,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f6 : checked d6=true := by decide +kernel
def d7 : Data := ⟨366,8,0x100000001000001000000000000000000000000000000000000000000000000040000000000001040,0x140000000000000000000000000000000000000110000000000000040000000000,[6,12,66,264,288,320],[42,100,104,258,260],0,366,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f7 : checked d7=true := by decide +kernel
end Complement2311.Face
namespace Complement2311.Face
def d8 : Data := ⟨430,8,0x1000001000000000000000000000000010000001000000000000000000000000000001040,0x4000000000000000000000000000000100000000000000000000000000000040000000000000000000000041000000000,[6,12,132,160,264,288],[36,42,138,260,386],0,430,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f8 : checked d8=true := by decide +kernel
def d9 : Data := ⟨444,8,0x1000001000000000000000000000000010000001000000000000000000000000001001000,0x10000000000000000000000000000001000000000000000000000000000000000010000000000000000000010010000000000,[12,24,132,160,264,288],[40,52,136,276,400],0,444,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f9 : checked d9=true := by decide +kernel
def d10 : Data := ⟨462,8,0x100000000000001000000000000000000000000000000001000000000000000040000000000001040,0x4000000000000000000000000000000100000000000000100000000000000040000000000000000100000000000000000,[6,12,66,132,264,320],[68,138,200,260,386],0,462,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f10 : checked d10=true := by decide +kernel
def d11 : Data := ⟨492,8,0x100000001000001000000000000000000000000010000001000000000000000000000000000001000,0x1000000000000000000000000000000100000000000000100000000000000000000000110000000000000000000000000,[12,132,160,264,288,320],[100,104,200,260,384],0,492,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f11 : checked d11=true := by decide +kernel
def d12 : Data := ⟨486,8,0x100000001000000000000000000000000000000010000001000000000000000040000000000000040,0x4000000000000000000000000000000100000000000000001000000000000000000000010000000000000000400000000,[6,66,132,160,288,320],[34,100,192,260,386],0,486,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f12 : checked d12=true := by decide +kernel
def d13 : Data := ⟨191,11,0x10000003000000000000000000000000201023048,0x4060000000000000000000014040000000020,[3,6,12,13,17,24,33,132,133,160],[5,42,50,52,137,138,146],0,191,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f13 : checked d13=true := by decide +kernel
def d14 : Data := ⟨319,11,0x1000003000000000000000000000000000000000000000000000000000000000201023048,0x1400200000000000000000000000000000000000000000000000000014040000000200,[3,6,12,13,17,24,33,264,265,288],[9,42,50,52,261,274,276],0,319,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f14 : checked d14=true := by decide +kernel
def d15 : Data := ⟨379,11,0x300000001000003000000000000000000000000000000000000000000000000040000000201020008,0x400020000000000000000000000000000000000010100000002000004040000000000,[3,17,24,33,66,264,265,288,320,321],[42,50,73,104,112,257,274],0,379,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f15 : checked d15=true := by decide +kernel
end Complement2311.Face
namespace Complement2311.Face
def d16 : Data := ⟨487,11,0x300000001000000000000000000000000000000010000003000000000000000040000000200000048,0x6000000000000000000000000000000300000000000000003000000000000000000000010000000200000000400000000,[3,6,33,66,132,133,160,288,320,321],[34,69,100,192,193,260,261,385,386],0,487,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f16 : checked d16=true := by decide +kernel
def d17 : Data := ⟨255,12,0x10000003000000000000000040000000201023048,0x10300000000000004040000100100000000200004040000000000,[3,6,12,13,17,24,33,66,132,133,160],[42,50,69,104,116,138,146,200,201,208],0,255,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f17 : checked d17=true := by decide +kernel
def d18 : Data := ⟨503,12,0x300000001000000000000000000000000000000010000003000000000000000040000000200020048,0x40002000000000000000000000000001000200000000000010002000000000000000000100000000000200004000000000000,[3,6,17,33,66,132,133,160,288,320,321],[50,69,116,193,208,261,276,385,402],0,503,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f18 : checked d18=true := by decide +kernel
def d19 : Data := ⟨507,12,0x300000001000003000000000000000000000000010000000000000000000000040000000201020008,0x40002000000000000000000000000000000000000000000010300000000000000040000010100000000000004040000000000,[3,17,24,33,66,160,264,265,288,320,321],[42,50,104,112,138,200,201,208,385,402],0,507,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f19 : checked d19=true := by decide +kernel
def d20 : Data := ⟨495,10,0x1000000010000000000000000000000000000000100000010000000000000000400000000000001420000,0x40000000000000000000000000000001000000000000000010000000000000000000000100000000000000004000000000000,[17,22,24,82,148,176,304,336],[50,116,208,276,402],16,486,9⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f20 : checked d20=true := by decide +kernel
def d21 : Data := ⟨487,9,0x1000000010000000000000000000000000000000100000010000000000000000400000000000000420000,0x40000000000000000000000000000001000000000000000010000000000000000000000100000000000000004000000000000,[17,22,82,148,176,304,336],[50,116,208,276,402],16,486,1⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f21 : checked d21=true := by decide +kernel
def d22 : Data := ⟨190,7,0x10000001000000000000000000000000001001040,0x4040000000000000000000014040000000000,[6,12,24,132,160],[42,50,52,138,146],0,190,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f22 : checked d22=true := by decide +kernel
def d23 : Data := ⟨222,7,0x1000000000000000040000000001001040,0x10100000000000004040000000000001000000000000000000000,[6,12,24,66,132],[84,138,146,200,208],0,222,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f23 : checked d23=true := by decide +kernel
end Complement2311.Face
namespace Complement2311.Face
def d24 : Data := ⟨238,7,0x10000001000000000000000040000000000001040,0x100000000000000040000000110000000000000040000000000,[6,12,66,132,160],[42,100,104,138,200],0,238,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f24 : checked d24=true := by decide +kernel
def d25 : Data := ⟨318,7,0x1000001000000000000000000000000000000000000000000000000000000000001001040,0x1400000000000000000000000000000000000000000000000000000014040000000000,[6,12,24,264,288],[42,50,52,274,276],0,318,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f25 : checked d25=true := by decide +kernel
def d26 : Data := ⟨378,7,0x100000001000001000000000000000000000000000000000000000000000000040000000001000000,0x400000000000000000000000000000000000000010100000000000004040000000000,[24,66,264,288,320],[42,50,104,112,274],0,378,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f26 : checked d26=true := by decide +kernel
def d27 : Data := ⟨476,7,0x100000000000001000000000000000000000000000000001000000000000000000000000001001000,0x10000000000000000000000000000001000000000000000010100000000000000000000000000001000000000000000000000,[12,24,132,264,320],[84,200,208,276,400],0,476,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f27 : checked d27=true := by decide +kernel
def d28 : Data := ⟨490,7,0x100000001000001000000000000000000000000010000000000000000000000040000000000000000,0x4000000000000000000000000000000000000000000000100000000000000040000000100000000000000040000000000,[66,160,264,288,320],[42,104,138,200,386],0,490,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f28 : checked d28=true := by decide +kernel
def d29 : Data := ⟨504,7,0x100000001000001000000000000000000000000010000000000000000000000000000000001000000,0x10000000000000000000000000000000000000000000000010100000000000000000000010100000000000000000000000000,[24,160,264,288,320],[104,112,200,208,400],0,504,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f29 : checked d29=true := by decide +kernel
def d30 : Data := ⟨30,4,0x1001040,0x140400,[6,12,24],[10,18,20],0,30,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f30 : checked d30=true := by decide +kernel
def d31 : Data := ⟨78,4,0x40000000000001040,0x1100000000000000400,[6,12,66],[10,68,72],0,78,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f31 : checked d31=true := by decide +kernel
end Complement2311.Face
namespace Complement2311.Face
def d32 : Data := ⟨156,4,0x1000000000000000000000000001001000,0x1010000000000000000000000000000100000,[12,24,132],[20,136,144],0,156,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f32 : checked d32=true := by decide +kernel
def d33 : Data := ⟨166,4,0x10000001000000000000000000000000000000040,0x400000000000000000000001400000000,[6,132,160],[34,36,130],0,166,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f33 : checked d33=true := by decide +kernel
def d34 : Data := ⟨172,4,0x10000001000000000000000000000000000001000,0x10000000000000000000000011000000000,[12,132,160],[36,40,136],0,172,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f34 : checked d34=true := by decide +kernel
def d35 : Data := ⟨198,4,0x1000000000000000040000000000000040,0x1000000000000000400000000000000100000000000000000,[6,66,132],[68,130,192],0,198,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f35 : checked d35=true := by decide +kernel
def d36 : Data := ⟨326,4,0x100000000000000000000000000000000000000000000000000000000000000040000000000000040,0x140000000000000000000000000000000000000000000000100000000000000000,[6,66,320],[68,258,260],0,326,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f36 : checked d36=true := by decide +kernel
def d37 : Data := ⟨330,4,0x100000000000001000000000000000000000000000000000000000000000000040000000000000000,0x40000000000000000000000000000000000000000000001000000000000000400,[66,264,320],[10,72,258],0,330,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f37 : checked d37=true := by decide +kernel
def d38 : Data := ⟨332,4,0x100000000000001000000000000000000000000000000000000000000000000000000000000001000,0x100000000000000000000000000000000000000000000001100000000000000000,[12,264,320],[68,72,260],0,332,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f38 : checked d38=true := by decide +kernel
def d39 : Data := ⟨344,4,0x100000000000001000000000000000000000000000000000000000000000000000000000001000000,0x100000000000000000000000000000000000000000000000101000000000000000000,[24,264,320],[72,80,272],0,344,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f39 : checked d39=true := by decide +kernel
end Complement2311.Face
namespace Complement2311.Face
def d40 : Data := ⟨354,4,0x100000001000000000000000000000000000000000000000000000000000000040000000000000000,0x40000000000000000000000000000000000000001000000000000000400000000,[66,288,320],[34,96,258],0,354,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f40 : checked d40=true := by decide +kernel
def d41 : Data := ⟨396,4,0x1000000000000000000000000000000001000000000000000000000000000001000,0x1000000000000000000000000000000100000000000000000000000000000010000000000000000000000000000000000,[12,132,264],[136,260,384],0,396,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f41 : checked d41=true := by decide +kernel
def d42 : Data := ⟨424,4,0x1000001000000000000000000000000010000000000000000000000000000000000000000,0x1000000000000000000000000000000000000000000000000000000000000010000000000000000000000010000000000,[160,264,288],[40,136,384],0,424,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f42 : checked d42=true := by decide +kernel
def d43 : Data := ⟨480,4,0x100000001000000000000000000000000000000010000000000000000000000000000000000000000,0x1000000000000000000000000000000000000000000000001000000000000000000000001000000000000000000000000,[160,288,320],[96,192,384],0,480,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f43 : checked d43=true := by decide +kernel
def d44 : Data := ⟨31,7,0x1023048,0x140620,[3,6,12,13,17,24],[5,9,10,18,20],0,31,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f44 : checked d44=true := by decide +kernel
def d45 : Data := ⟨167,7,0x10000003000000000000000000000000200000048,0x600000000000000000000001400000020,[3,6,33,132,133,160],[5,34,36,129,130],0,167,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f45 : checked d45=true := by decide +kernel
def d46 : Data := ⟨313,7,0x1000003000000000000000000000000000000000000000000000000000000000201020000,0x100020000000000000000000000000000000000000000000000000001010000000200,[17,24,33,264,265,288],[9,40,48,257,272],0,313,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f46 : checked d46=true := by decide +kernel
def d47 : Data := ⟨355,7,0x300000001000000000000000000000000000000000000000000000000000000040000000200000008,0x60000000000000000000000000000000000000001000000020000000400000000,[3,33,66,288,320,321],[34,65,96,257,258],0,355,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f47 : checked d47=true := by decide +kernel
end Complement2311.Face
namespace Complement2311.Face
def d48 : Data := ⟨174,5,0x10000001000000000000000000000000000001040,0x40000000000000000000000041000000000,[6,12,132,160],[36,42,138],0,174,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f48 : checked d48=true := by decide +kernel
def d49 : Data := ⟨206,5,0x1000000000000000040000000000001040,0x100000000000000040000000000000000100000000000000000,[6,12,66,132],[68,138,200],0,206,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f49 : checked d49=true := by decide +kernel
def d50 : Data := ⟨286,5,0x1000000000000000000000000000000000000000000000000000000000001001040,0x1400000000000000000000000000000000000000000000000000000000000000000400,[6,12,24,264],[10,274,276],0,286,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f50 : checked d50=true := by decide +kernel
def d51 : Data := ⟨316,5,0x1000001000000000000000000000000000000000000000000000000000000000001001000,0x1000000000000000000000000000000000000000000000000000000010010000000000,[12,24,264,288],[40,52,276],0,316,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f51 : checked d51=true := by decide +kernel
def d52 : Data := ⟨189,8,0x10000003000000000000000000000000201023000,0x1030000000000000000000010010000000020,[12,13,17,24,33,132,133,160],[5,40,52,136,137,144],0,189,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f52 : checked d52=true := by decide +kernel
def d53 : Data := ⟨347,8,0x300000000000003000000000000000000000000000000000000000000000000040000000001020008,0x400020000000000000000000000000000000000000000000103000000000000000400,[3,17,24,66,264,265,320,321],[10,72,73,80,257,274],0,347,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f53 : checked d53=true := by decide +kernel
def d54 : Data := ⟨127,9,0x40000000201023048,0x100100000002200004040000000000,[3,6,12,13,17,24,33,66],[42,50,69,73,104,116],0,127,0⟩
set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f54 : checked d54=true := by decide +kernel
end Complement2311.Face
namespace Complement2311.Face
def evidence : Array Data := #[d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15,d16,d17,d18,d19,d20,d21,d22,d23,d24,d25,d26,d27,d28,d29,d30,d31,d32,d33,d34,d35,d36,d37,d38,d39,d40,d41,d42,d43,d44,d45,d46,d47,d48,d49,d50,d51,d52,d53,d54]
def fact (i : Fin 55) := evidence[i.val]
theorem valid (i) : checked (fact i)=true := by
  fin_cases i
  · exact f0
  · exact f1
  · exact f2
  · exact f3
  · exact f4
  · exact f5
  · exact f6
  · exact f7
  · exact f8
  · exact f9
  · exact f10
  · exact f11
  · exact f12
  · exact f13
  · exact f14
  · exact f15
  · exact f16
  · exact f17
  · exact f18
  · exact f19
  · exact f20
  · exact f21
  · exact f22
  · exact f23
  · exact f24
  · exact f25
  · exact f26
  · exact f27
  · exact f28
  · exact f29
  · exact f30
  · exact f31
  · exact f32
  · exact f33
  · exact f34
  · exact f35
  · exact f36
  · exact f37
  · exact f38
  · exact f39
  · exact f40
  · exact f41
  · exact f42
  · exact f43
  · exact f44
  · exact f45
  · exact f46
  · exact f47
  · exact f48
  · exact f49
  · exact f50
  · exact f51
  · exact f52
  · exact f53
  · exact f54
end Complement2311.Face
namespace Complement2311.Search
def planWords : Array Nat := #[0,0,3,2,13,15,4,12,5,28,24,7,10,36,11,22,8,38,41,26,92,19,108,23,88,109,111,14,110,145,76,35473,4416,14912,141,51,6208,10048,29,29256,143,86,17,50,33095,34887,71,3392,15168,68,35402,6221,69,1165,27,35147,33100,7232,17728,33093,48787,33098,44,147,87,18051,74,32,18050,8471872,20,27282,6275,6274,27533,182,12931,47,8340800,10063,54,26511,30282,33096,2703,48,10293568,15180,15170,6212,9090,16,33,8461376,10053,72,3395,8136512,32332,8469312,30284,12930,35,8457536,6213,3404,131,130,3405,45,32130,8982848,7298,39,6210,9091,8263744,10051,29272,32600,34,31815,32327,90,46,30540,3898432,31818,31,4554304,37763,10052,40263,8129856,4553792,8141376,32588,40268,40303,32342,12943,8555651,4418,79,77,75,3394,114,7481152,29258,7617088,29767,7617344,33155,49,8130880,8260928,4556864,9054016,35405,10304064,15171,8522383,25,29255,7412800,7411776,7474496,7475520,7486016,32131,7478336,34705,37,7488832,7606592,7608384,7619904,29772,35655,7748160,7813952,7808832,8133696,8261952,35202,8272704,115,35203,8984640,32365,8330304,8338240,40267,8927808,37762,9101,3408,7415616,7420736,7423296,8919104,37777,35217,29292,30535,7605568,35143,105,7748416,35151,35213,8272448,8329280,32586,8394816,26499,8464192,8920128,8993344,9059136,32580,80,29008,7408960,28999,29776,7486272,7477312,43153,7609408,102,7743296,7750976,30317,33411,33410,7816512,30538,6211,8264768,8267584,8337984,8333120,35971,8922944,8928064,8996160,8981824,10050,10055,10295360,10306880,10299200,32344,32402,35419,8551811,3895874,9208450,29273,40338,9016194,33088,1576256,29004,9115712,32141,32145,11740992,29773,7612224,29775,32583,9058880,7737664,33169,7806016,33423,6216,2562112,31816,34691,11085632,32333,20610,27522,35658,8917312,8988480,8993600,9047360,10292544,10296384,10304320,15183,15184,11025216,11027776,11748672,38217,32655,8483394,7634509,7802178,7813954,9181314,7237,34905,35163,95,17732,8260931,8272707,3396,34908,33099,35164,38234,26509,8489027,29248,32320,30528,7420480,29002,30,32147,29261,10430272,38035,7736640,30280,30536,7802176,34880,6215,8132672,31819,11017280,32331,32336,33091,8326464,35403,8403776,35970,45907,8469056,8916288,34891,34926,8985664,35146,35400,9127232,11013440,43084,45900,33090,35444,37775,38031,33108,6782339,43151,35397,26755,7765581,7808834,32070,30575,31812,28290,8263747,8486478,15173,9201539,9081986,38237,32087,17740,32599,7244,9202562,9202322,26513,33092,30554,7481154,8546962,1410,8979597,8919107,1411,32065,38209,29760,3804480,6285,9768257,8202049,7409984,29005,43,112,11738176,29263,29768,38033,32657,40,9124672,33171,30285,7740480,7739456,7813696,3872832,1120320,3807296,9771073,34690,31821,32328,35458,35659,10437952,40779,45898,8392000,32845,8406336,8457538,8469314,8471874,8460352,34888,34893,9051200,9061696,9048384,2570816,12947,2560320,3876672,2559296,9119552,43138,10369856,40525,43082,11734336,8916291,9072973,8483138,3895618,29252,8551810,7502920,8486787,10321735,9073741,27535,8480643,30543,29270,10295362,9075789,8136514,8485954,3898434,35416,8263757,9144391,8267587,9071490,2172601664,9210498,9176195,1155,8329297,11741011,2690,9177730,9078861,7050114,83,1169,81,11037570,9193091,17730,6982034,31808,116,31875,31874,31885,9794113,11014464,32643,32642,32653,91,38291,32659,7804992,28992,32576,35136,9105,96,7671104,30023,11090752,8327488,10115,32840,8398656,35715,32593,37779,11024960,35395,38018,35138,38275,40768,35392,45888,9124416,38530,9116736,17795,38289,10358080,40520,10364736,43395,117,35648,11020096,11016256,48771,11735360,8916290,2559298,8158595,7500109,7435850,6782083,7044226,8355203,7631437,7631439,9007695,7502925,9731458,32844,3412,7481167,7044482,7828032,18063,7486275,9073229,8341122,1953905216,7763021,8358275,7634512,8329347,11042690,1956450624,7605581,6782851,7044994,9073731,7612227,7608386,9008194,40517,8480899,11761235,42,8546435,2172063042,2172074818,2172077378,11761491,8546179,8547202,7831872,3872835,9008207,118,2172390722,2168159298,2168814658,8354897,6784899,7047042,9075786,9799555,45893,31813,668290,7244162,35214,2172533570,2172521794,2168815170,8355409,7047554,6785411,9016195,8945229,30532,32325,9076291,35140,9076301,9115715,271235,2172601666,2172587330,2172599106,32587,9144651,10460491,11045506,9147779,8424013,32086,8457539,21,9176451,6768259,9176450,5270402,33102,9213570,12487811,9802627,34885,9013327,15188,8919117,6787971,32877,9726850,9011025,1422,12490115,2707,9791363,8486464,11761216,8945216,8267586,29302,7252098,8469315,10321745,10324290,30556,12478339,12454547,6953106,6979474,30275,104,34906,30548,8522370,8979587,32340,2324201037,275075,4588675,6982290,2827643778,12479122,6949522,9635214,6967442,40258]
def hints : Hints := fun i =>
  let v := planWords.getD i 0
  (v &&& 63,(v >>> 6) &&& 3,v >>> 8)
def packed0 : Array Nat := #[0x1bbc2420a12840842908002be108421036784290841081084a104210000001,0x2274bd29baf14f4001863d080118a7b14623bde97aebbd0f43d8f43def43d0f427593fe87a13a101a,0x4765764a7b3c6976001661761000c5dbb0821087acc1080ec8bddbb295303851dddaae0ecb70025,0x22b2840841a42004210800c184210421087a1000af857c1872638308311ca3b830800cf70031,0x4565080842136114ea10821084210f419aaf55dd9cce921d988e51dc66166abf5670046,0x22e8b8b117068bf30a528a50f517e80529617ea2fd45cea2e75670057,0x159304248521492908404a421088e51dc333a487021296310058,0xab561042101bbdbbc21294245e155dabb810b4c70867f5670064,0x4435cb129862908018d3a6019ce739322314c628b2190e4398e4390e4390e426593fc8721321070,0x8128408bc69080108b080108458b0431084001709931c4c0e2c22c204567007d,0x204a10108421080d7184108426cd8406cf6cf0aaf55dd29092784204312dc2abc567008f,0x87181084214a12845084310037085c3cb0b86974c0e10810c4b73bd00a6,0x3ae4c109294921886e26cd9b36921c0d96e529b59c0b8,0x2168410801086974c0e170f2c2e155dabb804570867c56700bb,0x10250809b08422c043508108422c00af857c164b8b99d2438b080b0e4b716100c7,0x21160421085094a0421000708d68b08b080b0e4b71623947700d8,0x12608490a520300170830e4c70610733a487023106100e6,0x346696839b420b59806b4ad69ad19ce59cb2190e4396e4390e42659bfc8721c87213210ee,0x1684000708308585c6aee064b706100fa,0x20421361085094210d40295296b4223a487021084223947700ff,0xcc0f18490a6a02525577a88e571a607ae3010f,0xa956d5b56855a535ad15aab5aab5ad4356d42559bfa86a1a86a1a86a12a1111,0x1326d0099278921d292c2e04cc7264c9930000,0x982109212801384e13d2e585c2711d2438138427a5d30384e239477011a,0x3456d574ba52ad7705663ab5651dc000,0x1ac21a5cb0b95a810b4c70d2e981c21011f,0x2274bd29baf14f4001863d084629ec518f7bdebbdebaeba3a0126,0x89d2f4a6ebc53d00118f62ef7bd005c1863d08463d128,0x2274bd29baf14f400463d8bbdef40c1c63de842463de81b1fb1e0c1e4c78c7bd0fb008957f8c7ba1f12a,0x44e97a01c7a231ef7bd29baf14f4123d12d,0x44e97a01c7a226fbdef69d3ac7bd1d70c63de85355eabbc62921fbd1d7f611d2ff5a3f12e,0x469c4071231ef4077f4bdeba75d000]
def packed1 : Array Nat := #[0x3b4c0d1e872f8f62944e5e3d000,0x2cff1e969bae06123d12f,0x231ef69d301838c7bd009bc9be31ef4b0bd355dabb80c1b4c708ae7fba9f000,0x7dfd0c7a1ef434c0e21b1fb1e6cfe2d5ff422bdfef45fb130,0x23d0f7a33d4fd0bae1fbad0bb9088e637ee5e7a9f2165bbf6431c87b90f721133,0x11d95d929ecf1a5d80007176ec19dbb29d80c1bb768c0c18067c1e418376566089dbb15c5713c,0x1d7654b7ba0c10f598033e19f07b5e0fae5fb30443b15c5713d,0x1d9324e8bb4852ed24a6290949dd971a41b626294a52913f,0x1d87b14a4e094a4fd72ff1eb7d6c4c5294a529141,0x1d35dd83a7ee9fa4e5e977f10fee7aded78ec3beeddbb000,0x8bb2903d12376076fc176d7a63ddf8e00ef8000,0x22eca8850bd19b76118887f73d3130feecf1fcd7821f0ef887d0bd57142,0x220dd8230ec7e63ddef7887f73c60f8ec3beeddbb143,0x768dd9529ef1d18067c33e32ff8f5beec3c79af6626bf83cb7000,0x1d8400c1707b5eef1eb7c11060c1bb02f02f144,0x30836f7b73c135e0c4d7b17cb7145,0x6d7c2ef7bd55bdaf363f31e9394a598f7afe07146,0x1071595070839b41c20e89e83a0e83a27f507aa0e004be4b8cc9767338cc470041cf70000,0x159303030a429480061060f2638311ca3b8399d24384620cf70147,0x12d58400308306528322f1abb800cf7014a,0x1d961ef42cc2112de29fdcfd07f67bd2df39e0306cd0714c,0x10f5d74841290f67bf73f41e2c44a529150,0xab5610420c18def84a10b409cfd01e41845725c57154,0xe85d3c37bfbdf097b45f2de29f1cf39e0376f06e9f6c5725c5715d,0x456535c29c5e3484001f7861f6180c183162c0c31060c002e1649161160740db73ddb715f,0x2060e9bc58203062c581dbf05cedea4f084139e1b73ddb7165,0x210f17842c18316009e09e64fee7e83c2045be03062d07169,0x2116042743d061065565285001c268b160b0e414a5294a516f,0x4215628306051e039a0c2045be167bca5294a5177,0x108307c9f8c20d13d13c26c1f3f7cfe5bc53e9a8f2af0808b7e5be73c463117c,0x20c19ae109420ca338411bc375755ef1f49e10186116fba1c3cd770f182,0x418306906371366e83c0b7cb39f137118a]
def packed2 : Array Nat := #[0x4183060c02178fa4f5755f2de29f0c9ce8ce79cf00c2118b,0x19615610814a96b37e83c103d9ef66f8c7c479eff5c77190,0x1b569ad56b50b6a154d3fd47d42a84350baf5083adb196,0x2604cabd41e9aaf130ede4c3b7f07cc7000,0xba78402709de3eabd9bf41e78fa4f01f67bd9be1388f3de6dfc7719d,0x39bc2f1f55ea9e3e93c06ede1072edbb7b47cc719f,0x33159598666d986756666ce9f59d3660097c971992ece671988e00ccf70000,0x2b069aa4d21484949b4a412908699412c425294a5291a1,0x1397d369082532fb59e096225ebd294a5291a7,0x3356accd9859b306afb57d2709599276b3e867566cd8725d871a9,0x1d0f478357dabf2cbd38fe96d9f7effabc7cf7ef7cfe8f55d8725d871ab,0x531596980d3080869d3eb3c78d999d3a61366e9b306efb77e9d534ca708a78867d674db73ddb71ac,0xd50bebc9ea61aa17d3a84106efb77df3dfbd353aff0d0ebbc7cfeaf7cf42f55db73ddb71b2,0x78f551ebc5e975174fc70097c4be3cff57aff1c875de33662d07000,0x33198599b3acfa176adeccaaca12814a96b34bc708414a5294a51b6,0x19d55beaaea567502952dabd7bc78616b3ca5294a5000,0xce9b87f1d30c3285994676610c375761e6c6be875de4386177bd1dbdef71bb,0xa614dc0213635f5761e5978f9efdefdff57be7a6eabb309f7f1be,0x330f67f17d58a56600de13677073f5de78fdacf82fe03f11eb3cb3c771c2,0x93092109f87bbdb3f3b88957af0a17f40ff33bd7b97c871c4,0x169e00de196b0f15de1fbe587ef86fd771c8,0x664d9804e139bb0f733635f2af5fdacf82fc2711e972ef2ef000,0x4bd66ec3d2db3e6c6be2b5acb96115adeb71c9,0x45d17c622f4cea2fdea2fd45dd45d1745e2046f0dd5955a6185c43aef7bd000,0x15935b24294820c0b61076f2638311ca3b8399d24384636cf701ca,0x2108306008423df76fba7e23fb6f2213dc1cd,0x9ae1c6094bc3ddbe63c1c1d4,0x11745c02709c83e8b917c1c000,0x21294245e56b725db698e52c70701d6,0x4250c07ab7047be5c1c1d9,0xe842908afe2bf2f603c9f87823dfe6ff27c4a5291dd,0x564d2cebcbc66c1b71286e26cd9b369b6f0d85e94db6e6db71e0]
def packed3 : Array Nat := #[0x4c135dd084a5009c2757cb94274db782757cba414a5294a51e1,0x961ac2af972ab54b6cbe5d225cb1e4,0xa4210842010ab20f93f0f05bc487978cff9bfc9f294b83c7071e5,0x4b96045f0883ef0f11df890841db1ee,0x1da4eec9383b24f95e3e57649fe8fb8f123c000,0x12d58405b083b652db22f1abb800cf701f1,0xae5a4e049c293952724fae3c3d7c1f3,0x1d930264df487e52649f2ebc98000,0x1ad35a1049c2edd89385dbb0294a514a52945294a51f4,0x21294245e56b725db698e52c70701f7,0x49c2549c93ea927baf2c41fa,0x210836c2010852ad5942d0203d085b73ddb71fb,0x5375be9c2ac20804255f78fab28ff47dc7891e747fabfd1fe9c33db73ddb7208,0x9769e06ac051e03a4e28fae3c227f12749c1db000,0x264c9ab0264df487e928f975e4c264c993000,0x9095f5957ca3ea927baf2afbc7c4a529000,0x886b962530c5210031a74c6739ce4cc6318a39cb2cb232020e,0x110d72c4a618a42000ce739c88c631640c699698c9cf1211,0x44565894cc3e290800339ce722318c5935c318f69d3a6672739ce06b8631a6239477a683819d0f9ce8dfe31214,0x886b962031a6339cc6311470c52153331217,0x110d72c40634c673989b8a8ea3d621099cc620a3aaf55de31490e1094d070cf67e3a5f21a,0x8d3881899cc620b3ef396210ce533121f,0x234e20626731895e72c4a10b92c40295e770f2c2f188420ce23947702a57f2a47f221,0x6bd30598832f8c62944cb2f1225,0x3c4d72d3082331226,0x8c5a6bd3a611880d3b4f189aee1e585e9aaed5dc0840ce62b9f228,0x15c7210834ed3c4a134feefc97e32fdf7cfaf7f2e9e122a,0x1c863909af1a6052a5b196fc99fe53f331ce4e122e,0x15cb2edc8cecb42cd435ac6eda85598fcc3ea15439a86350e6a1232,0x160b2c178170c5816108b162cdc3175c9c00b082c974a459278b1604567023a,0x2c5e305c3058458b894a5002c2373713038b16076f7023d,0x5c2505c22f1a420105c584005f47162c0bc41705c32638981c5f978b081159c0023f]
def packed4 : Array Nat := #[0x4429e22ca709b08c503d2bd319afe1903d63c17e1f1653fb245,0x448c316508430dfcbeb5e99f79f0ce85f0f94a5246,0x585a2c2c20146946546d11c4642c5725c57247,0x44180214cfbcff2fad7a07a57a03eb1e3205725c5724a,0x10c98288490a52003079178d20306224a52924c,0x23040600f470621e2f1ae780c44252924f,0x180e0cb5e4af018f0f8000,0xa7e390fc7a70fc7a6103d2bf1ae7d37c2781681eb1e163fabd67000,0x104d74c4094869be13f1ae78b70ed9631c1f07250,0xac22c209cfe73f094fbe0be81e95e2d887c07d63c0b4efe1253,0x2121c1794e052a5b4deb9ea6f84f05c31793fb257,0x98139afcb9e95af13021e4c087f07cc7000,0x105e82f009c274cf5afa6f5cf537c2782d33ef3c5e7fa7e07000,0xada99e94af427821eac087c27cc7000,0x4ef0a67ad7aa096c43d33ef3c0b18f18f259,0x985193264dd9e3f02781e4c92781ebef0dbc25b,0xf67b2c178f70c58f75c9defd9b87ec211607b082c974a7d9278bf604567025c,0x18c26ca729e180a70bd3d253e0794e21bc25f,0x64e04218614f5084d94a100214a5b43a52124f21fb896e76f70261,0x3184d94e53814e14b5253e078a736f7426a,0x61e52a3c21a656aa86218813275adca708538499304a52925294a494a52926c,0x9813c0f493c0f4a87825e4e1bc000,0x8b87e2109426c11bc37f6fa879b2ef8a736f74294a5272,0x42d043cd180426cda5194468e211d51858725d87275,0x11069b80426cbbfedf50f04be7bf86f10bf0bd0bd3755d8725d8727c,0x10250808458084d9b0854708108422c58f8f85e3c69160b44f05e4584f715c5727e,0x8eaa38551f5161a841f1ff8fbd3ebede1113cc4f36fc4f17ecf715c5728d,0x3556f75ea529ea052a5b5f6f0793efbc294a5291,0x152604f03dede950f0c3e4c264c993000,0x18d1736a5fe99517029543d1722e22e86f10dea1fd67000,0x24c26ba4da4d82521e4fbef5b2b8f1fb79631c1f07293,0x561087a3c21bf0df09438deb661f10bf0be7bf86f42fe8f55dd775dd7296]
def packed5 : Array Nat := #[0x18c26fb3c228432bc26cee727df78129cdbca717ecdbf23cb729b,0x8c98490060b8330fcee032b8f1fb7a3102f02f2a0,0xb4f00610650f018c2f1b78a8f0612a1,0x3993e601384e6d43dcf93efbcafb79b2efa529000,0x2b69b0c3f7de4e17ab4a5385ea9fd77000,0x12beb36a1eb661f08a9b366cbbf5adeb72a3,0x1efde33dc30a52bdfb8fb081ec2373713038bf6076f702a4,0x43861870e1821859bb33e18bdc2a6,0x64e04218614a1084d94f500214a5b43a52124f21fb896e76f702a8,0x10c30cd8430dd343a61d07e87f1ebdc2b1,0x156368de6ccbe7c7dee2b2,0x1587ebf33d39de2f7dee2b3,0x6e1c604370dd1bc294a11421bc437faf961746fa5d30386e1037f2f896e743bc002b4,0x685a684a5010a42d02eddf4294a5294a52b9,0x88328043f5f99ee1fcef17bddfe7c2eae5d5ca5294a52bf,0x10e3021021885e708408422c00e6b45db161058ce505e4584f715c572c1,0x408430c084dc3d0f366c21ac3054b5b8c67482108ce521c32cf,0x9826ba2135d214809c272eae138ce904f6c2719ca25294a5292da,0x2ac2549af1569e5c1290e332fad85c633ab7f2c4d735cd72dd,0xa16855ab560d685c3f9deb669f0a52bb76eff3f7bf6f72e0,0x1fef849480305c19a7f1997c061418346311102f02f2e3,0x517e00c0706cef018d5cbabbe3c1a78334f000,0x9d37e04e83f197c34f9313ab97572694a757a4fe17000,0x257d6aad9a7c217572eaff5f99ff5f51fd2eb1fe23f11f2e5,0x75c98289b366c0600c1e799b480c1888d9b15c572e6,0xae26c2b3facfcb53af7f2601fadae7f12b5feabf294b55ff57d67000,0x3600c2aefc01f80c4bf3c7e7b17cb72e7,0x468d1bb94f01d9b7ca11e5766df4dc53c7dc000,0x23c81af4a32a3f9c0de0479087214790b210e42c84f7c9ee4be4972e8,0x264d181302fd24c0bf4d8e3ee4c73c000,0x2375cac323847a453c7dfa2f0,0x3613763d47dca39e2f1]
def packed6 : Array Nat := #[0x5a10434ba6070b8796170c57dabb8108115c3fdf159c002f2,0x2168410a30a528c252a30b5a08c28c31882304fd2946c1fcb69fa30b6cbf02111b4e8c31b0fc002fc,0x11a346003060c534060c640cf715c57000,0x8cfd17f69e05a100301c1ac70a780c5b7e0f715c5730a,0x9d37e4c981302fc0dfa6c7003e4c264c993000,0x1235a32aa0db684225294a52930c,0x24257d723d8eaad807c22423d294a52930f,0x1071595070839b41c20f541c83a27a0e83a0e89fd004be4b8cc9767338cc470041cf70000,0x160b2c178170c58175c9c2c21162c59b8600b082c974a459278b16045670310,0x582cd8b082c5d458b09459401616b4592e2c47490e02c5e4b7162394770313,0x8c8c2a932429129005c20c3916220c25294a529316,0x4c124182305c271f9dc442274bd294a52931a,0x16d398b000e1061146418542d8725d8731d,0x2c035e038511e383c20ebe18725d8731f,0x12eaabaf52840a54b6ba5e0f17c77c294a5321,0x9936813252509932609898ae4c57000,0xa809ea7b4bd311e264c1c7c0ae4c57000,0x2610426d2904a43c5f1df162574bc2c5fe23f99f4bedbc87323,0x2b08b160bafeebf094fbd4bd71f847e28e75f09c7c35ad328,0x4216308458b2842019f842bf88f3605f3a045f078b87ef83fe3cb732b,0x23168c58408c26c0be15fc47ae3f08fc51d1a8e75f640b461334,0x9f373009c273711e3605fe2f8ef95d2fe7c5e1388fa5ec9fc87000,0x15b4d95c77c93af8e3ed56d000,0x257d66e23c6c0be1150cb09c7c52fce97337,0xb178c1639f0a52858458b8802c2373713038b16076f7033a,0x582cd8b085165162c22c5d401616b4592e2c47490e02c5e4b716239477033c,0x9a779dc59dd33b813b846e6fcc47008817f311c033f,0xe038b007080e10a52851e038d38f16cdfc584058725b8b0947700340,0x8c1241868e0b8643fc5f04f88844a529345,0x6b42b40a3c19a320c20a294a5348,0x3400de51e1497c647841e7c14a5349,0xd0adaad2ac56aca59e15958aeac57000]
def packed7 : Array Nat := #[0x158410952094878be09f16214b3ca59e180fddbe23967ba7c7734b,0x2556ada06b43d9f25f3b3ef852942938643f9bb737350,0x75e58291b89b04f8a7df1591e323ff3cb7354,0x5a1684010887e1dff67c97cecfbe151bce79f640b11c47355,0x4da026d1fc09f132624f3e90fe6e4f37000,0x9dfad5087e1df8429e7c321f19bb73735a,0x1593032429481840061060f2638311ca3b8399d24384620cf7035c,0x9a779dc99de772813b846e6fcc47008817f311c035f,0x308585cad6e0440bc1830360,0x9302e1252901830e4c706d5fc18524381132f06100361,0x61ac212ab502cba4201e41845725c57366,0x5610a4e119f19e50b67f260df097f29f120e2bc1a4f6e2beebcc736b,0x48420c1830608c3fdfbefc9837c25fca7c4a365ef3f640399e6736e,0x6b4ada906f95e07e4a2bc457c27cc7000,0x1a334b41cda105acc35a56b4d6e7396739cb2c8cb20371,0x346696839b4201ad2b5a6b39cb3902d2b31ce11b9373,0xd19a5a0e6d0806ab2b5a6b39cb39087ad66cc6b7390085ad28eecd9873867f56706ea7f3a1f376,0x346696802d6601ad2b5a6b39cb2017e69684cc235937b,0x698d2d005acc035a56b4d6739663cdad0846b40367d9f9d2e981dad0846619f159c1ab9f33937e,0xd39b42d06b4a6b59ce4669682cc51db9383,0x686da16835a535ace73566d68a3a8f9c83399d243b5a730b3660a3b77f6b73d9f385,0x19b98435a6b59c838f6b4d69479db9387,0x6b4d6b2103ed8dd265d211b9388,0x69335aca5a98dc4b53901296b63799d2438cbd2e981c2104b97f4b87f389,0x379b72908252dc6ff13fc2fc588dce42138b,0x7216e438f39e6136d0d9f6748463da42fe57e217f23fcbf7f389e138e,0x12d58400308306528322f1abb800cf70394,0x308585cad6e0440bc1830396,0xed01c0719e16171abb8192dc18400397,0x2613026edfce9fd229f8993199f8000,0x484bd719f14fd5467de3fcb1399fa529000,0xaf9a2e8ba5170bddc0a5a1d171174b7c000]
def packed8 : Array Nat := #[0x6ee04218614a129ea109b00214a5b43a52124f21fb896e76f70398,0x87bb94fbba71b770ddc29a1d3bbe77eddd13ebdc3a1,0x3d9ecdfb085f65f7eebefd840f616b7d92e2c47490e02fde4b71623947703a2,0x6ef05fbbcb48b06ee16eee4b8c7e3bcddd13e31ff5c3a5,0x117268ba402725e8722f31f45c000,0x264cad4826484c9932624a9294a5000,0xab5204f3bf477891f264c4a37d29494a5000,0xe7cf9aa4d29e69009c27366ca09cd9b484e5f5c25294a529000,0x3522b69b362b56acbeb89aa55b0ead87000,0x15934cb3654852094cb04b10beb97d7ac778c7ddbe23bd7f2ef2ef3a6,0x2556ada906b65a5a47ddcb7c294aadeed5be6bf43b6873a8,0x10b5a90084dcc7c60f772df0a8f43d1beadf35f4a5343b6873a9,0x232690929062f0f77a47c44216b1de31f7cfe23c77b97c873ad,0xd6a42580f2c227e5846fa6bf43b687000,0xdafcae9691f3731f9614d9b46fabcf9f3000,0x4afacd940da6d32c2aad6b5000,0x2bc6cc1a5fe97e56709fc0e0bfc07f7efe26ba1f8d0fee3d77000,0x152adab6ad2ad29ad6d6aad6b5aaa2aaaa0000,0xa956d5a15694d6ab556b52ad282cdd71b53b0,0x54ab6ad0aab29ad56aad6b5af5ad6d6a15ab5a51dc75edb30cfeace0dd4fd5a3f000,0x2a55b56855a535aad55a886ff54b42c2cdd71b53b1,0x54ab6ad0ab4a6b55aab5ad5ad6b6b50273f39fad5303b5a0b1712dd9867c56706ae7eba5f000,0x152adab42ad29ad56aa801ead0584235b53b2,0x54ab6ad0ab4a6b55aab5ab5ad6d6a04f7e7bf5ab5a02c5e4b70db06c47f6b6bd9f3b4,0x56b51535ad56a243ea6b5a5343db5000,0x34d6b551fbd55aa6a555000,0x1373e64f32f3039846e6fcc47008817f311c03b5,0xa257552dbcd32c214a5294a53b6,0xd7694abe0d693a0f9278afeec5bf129384a5294a53b7,0x14b432380424e83e0c7eec5bf13e9f2d17f53f91e9788f84f11f3b8,0x3633e035e03a83e233fa4e2545f145f14fe17000,0x21294245e56b725db698e52c70703bc]
def packed9 : Array Nat := #[0xac972c25eb2cb8efeadd2da3e5c1c000,0x1b258d84dd27eb706bf2eb7e3bf,0x5b08585cad6e0440bc1db03c0,0x25812c2a4fab7005f2c3c1,0x6e57adc68f9b90fe000,0x257a5cb0b95fdcd719ed31f58e7e981f584003c2,0xa607103ef05d53c5abfe915eff7a000,0x11cc6fdcbcf53e42cb77f1c87b90f7213c3,0xebc75f103af05c75f14f4223dfd000,0x8e637ee5e7a9f21669bec86390f7213c7,0x347000,0x75f13af06c7ec78ebe29e8447bfbd000,0x9fd000,0x95f8a57c095f05cc9f14f4223dfd000,0x28e4afc412be0b993e29e8447bfbd000,0x8e637ee5e7a9f21669bec86390f7213cb,0x1e79e7c516c7fd000,0x298324bfc629000,0x7df4c19b3f000,0x8d4f1bf6a779ea7a9c2b5e9bea9c39ce7b939fbdef7bd3cf,0x47a1ef467a9fa17533eeb423d1,0x8f43de8cf53f42ea67dd68513d4,0x11e87bd19ea7e85d70fdd687b90f7213d7,0x8f43de8ceeb42ed4e13dc,0x2398dfb979ea7c859a6fc721ee4204f3df,0xd000,0x11cc6fdcbcecd4e13e2,0x4a7fcc637000,0x13e3,0x2529000,0x98ff2dfddbb000,0x5e31000]
def packed10 : Array Nat := #[0x36be17754d7f3e4,0x13e5,0xc1f000,0xef63f31eef7be7bfee79184c1f4e7f0efbb76ec03e6,0x2c1f3e7,0x1b5fb7bdb9e135e0c4d7b17cb70000,0x3bdef6f7edaff6bdb9fcc7a4eeddbb98f7afe070000,0x564c0c0c294a40c1e4c707e5e51dc1e2e921c08c4003e8,0xe6f0d53be16f18f18f3e9,0x7bfe830af000,0x12d580e060c2946aee0036cf000000,0x1a000,0x129000,0xa2ff41fecbf83f000,0x64fa4ffd000,0xd47ea93ea,0xd17dba2f3eb,0x16f000,0x13ec,0x301e93ed,0x39f2000,0x143ea1f48f000,0x717ea1f48f000,0x87676294a5294a53ee,0x543ea1f3ef,0x8559b73f0,0x4e73f2,0x38bf000,0xe6f000,0xd17dba2f3f3,0xc3d3f4,0x162c16177bd3f5]
def packed11 : Array Nat := #[0x2eaca6b94e2f1a42003ef0c3ec30183162c0e20c18649174dfc583a06db83f6,0x83048c573f8,0x2b062c2a8fe7de15f93f3fa,0x5000,0x13fb,0xb9579b7000,0x5d3fc,0x3079000,0x393fd,0xb9579b7000,0x3b27fa5000,0x19000,0x1720fea9000,0x3a97987000,0x19000,0x162c16177bd3fe,0x380e2c01c27407e8306529429a2c582c393a5294a3ff,0x2b03294a5000,0x12ab5669d9ce5401,0x11000,0x305dab402,0x557f000,0xe6f000,0x5d403,0x3b27fa5000,0x1722fcb3ca5000,0xa3ca5000,0xace7000,0xb9579b7000,0x6e55e1ef000,0x308783f404,0xc9f9000]
def packed12 : Array Nat := #[0x112f406,0x25407,0x1d79d7875e177bd408,0x5d409,0x6e55e1ef000,0x3765000,0x4185580395e740a,0x15e7000,0x67000,0x15673bb40c,0x567f000,0x66f84fe3779ecbd5dfd33e32739079ce7bb379ee1ef000,0x8dc93f7dcf7000,0x1bc7d27abaafb2fe29f06e7324dfa326fe73c587fedf67040d,0x3460851b6740e,0x69000,0x3b27fa5000,0x6e55e1ef000,0x5000,0x13fae9000,0x4a3ff5c472ef410,0xace7000,0x1b569b50e7ada7f000,0xab4d6d49efcf7da2d5000,0x9f5000,0x1b569adad6a000,0x1b569adaaa3c5b35b7f000,0x54d6ae3fb5a5000,0xd694bf5000,0x5000,0xe7000,0xd17dba2f411]
def packed13 : Array Nat := #[0xf1f55e52faabf49ebafeede1072edbb7b47cc70412,0x6a3e9413,0x25eb66ad6b5000,0x1af9bfbcff5000,0x1981384e6cdafbff2e5000,0x12f59b36ad6b5000,0x1414,0xd47ea9415,0x607fe6fea9000,0x25eb66ad6b5000,0x14c08559b7416,0x3d418,0x33a6ce990c37a6ef7bd000,0x2984084d987419,0x2ba6cc2567eb3f4d998741c,0x2acfe17f41d,0x141e,0x141f,0x627f64fb2f000,0x14a5000,0x35420,0x6b3f5421,0x33a74d990c37a6ef7bd000,0x1be47fc6ffd000,0x664d981384e6cdb2bfd2e9000,0x15b33654844a59925422,0x1423,0x33a74d990c37a6ef7bd000,0x674fa3f66acd8a5000,0x19de7000,0x93f000,0x9b9b1afabb0f042b2f687f7efceffd5ef9e9baaf99fdc726f0424]
def packed14 : Array Nat := #[0x26ee3853726f426,0xb2f000,0x1987b3d98a56a7fd2fe0e7ebbde3f6b3d9b36759e59e3b8427,0x129000,0xd47ea9428,0x1264f77b67f63f8d6feabd7859d341debdcbe438429,0xd75add97000,0x757f5000,0x2d3fabf5878aef1fbe587ef86fd770000,0x25eb66ad6b5000,0x564d6c94a41060ede4c707e5e51dc1e2e921c08c40042b,0x7bfedb0af000,0xe6f0d53be16f18f18f42c,0,0x603cf742d,0x1084183047bfe5ee9fecfedbc440042e,0x5c000,0x255fdb16f432,0x4e52ef000,0x118f433,0xd7b5fd5000,0x1aeb7000,0x965125000,0x294afee4bb6d31e5967f172f000000,0x597ad54b69620ab0fa5987e5dfd77c0000,0x603cf7434,0,0x2bf7047bfb9fdcbc000435,0x358000,0x301e9436,0x6b000,0x243d437]
def packed15 : Array Nat := #[0x5e31000,0x4b294a5000,0x1aca5000,0x45f000,0x12d5f2e557f74b6cb1cfd24b960000,0x627438,0x215641f8aff878210b7921e5e33feefd1f77fc9fe6ff4e19ee5f172f0439,0x84258877bfa3e9ec3f43e,0x10db8c631442,0x6b36fd97cb1000,0x11000,0xd69000,0xd69000,0x316f000,0x603cf7444,0x301e9445,0x972c41f78788efc90841db0446,0x12d580e076c2946aee0036cf000000,0x1a000,0xae5a4e49c55c78f0fc000000,0x9603cb50e07bc000,0x12f5aa9652da7c000,0x1e0fe042ef7a5448,0x965125000,0x294afee4bb6d31e5967f172f000000,0x597ad54b69620ab0fa5987e5dfd77c0000,0x2ac3e49eebf8bfd77c000000,0x3a26f000,0x68f68f000,0x68f68f000,0x19bc1084210bd7c9744b,0x2a7d53ea9f000]
def packed16 : Array Nat := #[0x627451,0x420842956aca1682081e842db8452,0x36c295650b4081e843dbf6fd5fd2afa3f879bf82134e0f27ff0fc9bc45d,0x68f68f000,0x2d1ef5f468,0x153ed1e000,0x10db8c631469,0x5a3e3146b,0x5375be9c2ac20957de3eaca3fddfee3c10923dd9ffabfd1fe9c33db7eddb70046c,0x1d3f6e1e9c9bc472,0x38348f000,0xa9f000,0x1ad29000,0x6b36fd97cb1000,0x2b8e400701e25087bbf25fb2fdf7cfaf7f2473,0x1af1a6052a5b196fd4e53fcc72000,0x2b58ddb50ab31f987d439a86350e6a1475,0x1ae00380f1284e739fe7039ce720f47a,0xd78ab7c0a54b629198f97e5000,0x15ac6eda85558faa1cd431a84c3ea147b,0x2b001c07895d3c8bd575dc033e271ef000,0x2b8800e03c4a139ce7f9c64e739fb9480,0x2f97e511c77000,0x35e36df02952d8a4c9e5331000,0x15ac6eda85558f987d42a87350c6a1481,0xae200380f128423398f54700f486,0x2dbf71f8814a9a1e2438471dc52fc6f000,0x5000,0x56f35e2052a5b14993ca6625000,0xa5000,0x3854700f55d77488,0xa771f8800e03a75be290ce5331000]
def packed17 : Array Nat := #[0x22ac1a769e2f9ff9c672f9fe94a5000,0x2e3f1b6f814a9a1e2438471dc52fc6f000,0x5000,0x687c69814a96c5219ca6639000,0x15ab34a5000,0x571001c072843ddf00f19cc7b1489,0x15800e03c4a10d3f9c33120f48b,0x15ac6eda85558f987d42a87350c6a148d,0x2b001c07895d3c8bd575dc033e271ef000,0x28fd6f000,0x2b001c07895d3c8bd575dc033e271ef000,0x4e9e1492,0x11a6cc469da756f0ff9000,0x1b9000,0x2e3f1b6f814a9a1e2438471dc52fc6f000,0x277e9a5e9fc629000,0xd39af4d2d000,0x1af4d26e87ab7a687000,0x541bd9768378ceb5ccbf30f06f081bc35ad6b5ae739ae547494,0x2b965db919d96851496,0x15cb2edc8cecb4204f497,0x2b965db919d9687350e6a1498,0x2b965db919d9687350b261e149b,0xae59765a1797fcb46749e,0x15ac6eda85558fe6a18d4249f,0xd000,0x162ca0b8170c5817a38b166e18bae4e05b778948b1604567000000,0x58b01a529000,0x68e9000,0x58bc60b860b08b894a50d38f13038b160743bc0004a2,0xd1c9000,0x2c5941702e18b02f47162cdc31750a182c1705b778948b16045670004a3]
def packed18 : Array Nat := #[0x3d3ff8f4fc7a681e95f8d73c5c2781681eb1e163fabd67000,0x159a7e69f94fbc281e95e2d887c07d63c0b26f26f4a4,0x4362f29d2dc6b9e1709e0b862fdbffb000,0x4cb9e95af13021e4c087f07cc7000,0x99e94af427821eac087c27cc7000,0x44bcdbf4a5,0xbde5000,0x23468c8c2dc771c13f4ff7ffcfe8febf91851fc7f32d9c4a6,0x183079000,0x9de1b694a7,0x267de7f97d6bc2ff4af06e703fd63cc815dc715c04a8,0x71c271c4a9,0x4ef0d413fc574aa,0x122c20c8c2ba34ab,0x2f6fc6ff4ac,0x394ad,0x305f66f4ae,0x14af,0x2116f4b0,0x9bc9bc8ff0af12f0db98f01f59c63967000,0x305f66f4b2,0x36c125cf74b3,0x4aff4b5,0x60f000,0x9000,0x305f66f4b6,0x133d6bdf9f82f6fc43febfbcf1f1f99fe81f04b7,0x1312f000,0xf7eca0b8f70c58f75c9decdc3f7a38b05b778948bf604567000000,0xfefffbf01a529000,0x68e9000,0xc613653c321be494e21bc0004b8]
def packed19 : Array Nat := #[0x4dbff4f4b9,0x32709bcfaebe129000,0xdc086e1bc30a7a86e6ca58671fb643c4a487ee25b9d0ef0004ba,0x193c34b530c37438ba1e7f81f250cebf5f7c0000,0xe7cc13a529000,0xc9c20b5ad4bb,0x52d4bd,0x2694fbf4be,0xc5e9000,0xcafd6f000,0x18c26ca73bff03e48a736f5f7c0004bf,0x423ed4c0,0x9de94a413bc172a7a778c1c000,0x193a42186e9bcfaebe974000,0x23488c2ad6a94c1,0x23264a5351e902f4e2a3a8e9000,0x5ad0ff2785f4c2,0x14ef02f4c3,0x423e54c4,0,0x12f000,0x5539f000,0x2d079a3366d28ca091a3888ea8c2c384c5,0x8d19b4a3288d1c447546171dc736963fd6ff230803fa353fc8d2ff86fce7c4c9,0x3060cf7000,0xcaf000,0x4af6c294cb,0x4ae9000,0x137365dff6fa87821097b9ff0de6bff0bd0bd3755d8771d87004cc,0x26ee3853771c4ce,0x32000,0x464c20182e0c94cf]
def packed20 : Array Nat := #[0x68e9000,0x17f018419874d0,0xcaf000,0x56beb5f4d1,0x16beb5f12f000,0x33f000,0x11a31611184d9874d2,0x305474d4,0x364e3000,0x283fdeff4d5,0x27000,0xd000,0x6b3789f000,0xfa78b00f4d6,0x5000,0x5af9312f000,0xea7fbd4f4d7,0xfa7fb00f4d8,0x354d9,0xd78df85f000,0xd66eb7000,0x421a9b4da,0x13b4dd,0xd78df85f000,0x1b604225cf74de,0x62ff4e1,0x64ff4e2,0xfa78b00f4e3,0x63caf37d9e2813fcdfe70f7de08b094e6de538bf66df91e5b84e4,0x5000,0xd12f000,0x868ff4e6]
def packed21 : Array Nat := #[0x359badd97000,0x69da700f08f923c2ee2ded3d7761cb7000,0x2d3eaff28780cc2f1b7800fe0da70000,0xd78df85f000,0x3dfbc67b8614a57b8fb08d38f13038bf60743bc0004e8,0xd1c9000,0x43861870e1871eccf8603bc004e9,0xad000,0x32709bcfaebe129000,0xdc086e1bc30a50dcd94f58671fb643c4a487ee25b9d0ef0004ea,0x10f274b530c37438ba1e7f81f250cebf5f7c0000,0xc9c20b5ad4eb,0x52d4ed,0xe7cc13a529000,0x2694fbf4ee,0xc5e9000,0xcafd6f000,0xad000,0x5000,0x7d7e67837fcef17bc1de000000,0x6e04370de18528a1b9b29ea586abb643c4a487ee25b9d0ef0004ef,0xdc38c0dd1bc0de21bfd7d1bc210dcd68b16105a2794179168de59f4f0,0x6e04370de181b9b87f5f366c21aa5adc690421ba2794870c4f4,0x1b3bc063572eaef8f177fd9fe59f000,0x4c65f0d3e4c4eae5d5c993264f57a4fe17000,0x2821084233b4f74f9,0x2bf857f08fe5000,0x108fe54fe,0x2109d8a529413f4874ff04269d03fcbfc5c3fda19fc4ff,0x60c194f7000,0x95ed84a9505,0x5fafccf06ff9de084bdffdff9f1757dbff1bee1e1dfda1dfc0506]
def packed22 : Array Nat := #[0xa52871be19fc508,0x645000,0x58b162c2da2c9719c6734f60f34f000,0xd1e29000,0xe3fc0c194a5000,0x51e5000,0x3742fd0bf000,0x46f34f000,0x15ef509,0x85a105d946750a,0x60946750e,0x935c67000,0x2acd777be47f3750f,0x42ff37000,0x1af37000,0x16f7000,0x3cf3cf3cf3cf1e7b4f3c9719c6734f60f34f000,0x49734f510,0x13ebfc4c994a5000,0x79fe5000,0x21682ecad511,0x9687514,0x559aeef7e8fe87515,0x317c467000,0x1e87000,0x95cdf3000,0x4ae6b94a5000,0xa5a105d9427516,0x1f57000,0x1acb69f000,0x1af97000,0x425519]
def packed23 : Array Nat := #[0x1acb69f000,0x1b6094bd51b,0x4bd51d,0x6b5ef000,0x41966751e,0x1acb69f000,0x7ffeff000,0x1b577e00fc064bf3c7e7b17cb70000,0x8f206bd28ca8fe70378000,0x11e40d7a51955bff3804e720f51f,0xe73d7e2720f000,0x47908dfa513f2e57fe70bfe0000,0x23c81af4a32993c2351fe7000,0x8f212bf4a3037869c6779d23f000,0x3ce2b4a5000,0xc84efa30378d9e3765d33f000,0x11baf23847a77e29e3ee13fe000000,0x1bb1d65f8fba07e39e000000,0x46ee53c8c20ec23c54dc53c7dc0520,0x97f4887f2a3f9d6bdce0de0479087214790b210e42c87b7cf6ee3e5c7521,0x2d0dcf6ba6d72daed5cf6bc40529,0x2d0851851851842d74dae5b5da1bff6bc4052b,0x268c249d8e3ee4c73c0000,0x75c91c23d3714f1f7740000,0x1bb1d51f7e9c73c0000,0x81ac70a780c5b7e3b715c57531,0x4c0dfa6c7003e4c264c993000,0x91ec7556c03e11211f23d47f4bc453f8a7f532,0x8d1a34a07e594f2bfe0378ec23c54dc53c23fe00000,0x42d08428c294a3094a8c2d688c25ae9b5cb6bb4a1fdaf100533,0x23468d28ca8da46468d18000,0x13bf469dfa519dff253c249d8e19ff2639e00000]
def packed24 : Array Nat := #[0x8d19423caedc74dc53c7dc000,0x12fe21fd1ad7b9c23c84390a3c85908721643dbe7b771f2e3853c,0x4d24fb74d8e3ee4c73c000,0x123847a453c7dfa000,0x3763d47dca39e000,0x46060fb707db9a7000,0x1db9a7000,0x993000,0x16c294a50ff8b7f544,0x253238b7f000,0x25ff000,0x1ad29000,0x10db8c631545,0xd6a7fecbf1000,0x31547,0x6b36fd97cb1000,0x162ca0b8170c58175c9c2f47162cdc305b778948b1604567000000,0x58b01a529000,0x68e9000,0x160b362c20ba8b01ca51ad1719e921c058bc96e2f33e51dc00548,0x18bd29000,0x494472ef000,0x6156b5549,0x23230aa4c94894830e4588832a94a5254a,0x4afac6d565d97000,0x63fadff000,0x1720fea9000,0x5554c,0x6b65d97000,0x6156b554d,0x2da73160631fc519062a16c38000,0x3a97987000]
def packed25 : Array Nat := #[0x5554e,0xea7fbd4f54f,0xc1e5000,0x1720fea9000,0xd6a5e54f000,0x4f6de5000,0x1af97000,0x35550,0x3a97987000,0xd6a5e54f000,0x10b1ff551,0xea7fbd4f553,0x210cfd8c22c59439df88f3605f363f05afff078b87ef83fe3cb70554,0x25559,0x58b162c2da2c9719c6734f60f34f000,0x5000,0xce9000,0x2e9000,0xe11f000,0x5ef000,0x65f5bc1bc6739ff58fd978a3fcea3b254f25f5bc97000,0xb163605f0afe23c8ee783fe11f86bfa31afe75f643dff71da70000,0x11818325c57000,0x313e156b555a,0x5555b,0xd6a5e54f000,0x162f182c73e14a50b08b88d38f13038b160743bc00055c,0xd1c9000,0x160b362c214a2c071751ad1719e921c058bc96e2f33e51dc0055d,0x18bd29000,0x494472ef000,0x134ef3b8b3ba469c7f3c5c02265fcf870000000]
def packed26 : Array Nat := #[0x38752ff87387e1c294a52ff87ea97fd1a71fc3f0fcd0703876cf000000,0x58bc60b1cf852942c07162e234e3c4c0e2c581d0ef000000,0xb059b1610a50b01c58ba946b458e7f490e02c5e4b71683947700055e,0x22f84a45f41c13e2c42967917c5f0fc3967ba7c7755f,0x22ff9b04f8a7df1591e323ff3cb7000,0x1722fcb3ca5000,0x45560,0xd79000,0x2b03294a5000,0xa3ca5000,0x45561,0x1722fcb3ca5000,0x1aca5000,0x23d000,0x6b000,0x5000,0xad91f294a5000,0xa3ca5000,0x1aca5000,0x323e157d562,0x19000,0x6b421f877f27fe4be0dcffde7df151bce79f6434e3dfda70563,0x5187bf866ff9a7564,0x8c0c19457000,0x19000,0x9000,0x45566,0x1aca5000,0x564c0c94a40c20c1e4c707e5e51dc1e2e921c08c400567,0x7bfe830af000,0xe6f0d53be16f18f18f568,0x134ef3b933b9469c7f3c5c02265fcf870000000]
def packed27 : Array Nat := #[0x16172bfb81132f060c000000,0x159303252903084183c98e0c83f94770683a4870231000569,0x62ec5f17252c5ea3176efc5f1702265ecd07000000,0x693030693890585cafee044cbc183000000,0x159a7e50d1ff260df097f29f120e2bc1a4f6e2beebcc756b,0x906f95e07e4a2bc457c27cc7000,0x649000,0x35d5ff18f000,0x46bf56c,0x25718f000,0x72b955fdcd639fa7580f20e5740f8000,0x3bbf37000,0x6b48f000,0x184abf56d,0x83fefdf7f15f06f91dcf77fe53e4a365ef3f646cf67ff67056e,0x3592e9000,0x35bee9000,0x379b72094b71bf6785f8b16e72000,0x63c9b6802e0ba421690bf95fa17f23fcbf7f256f,0x47a1ef467a9fa17533ee85bd0e7a1571,0xd68252d2b348b11b9000,0xc79666da00b82e9085a1b5ce4e70af576,0x1ad04a5a3bcce438b8384df2af000,0x9000,0xde6d04a5a56691623729000,0x129000,0xcc0b84e70af55d67578,0x47a1ef467a9fa17533ee85bd0e7a1579,0x199b6802e0ba4216999078df9d957e,0x35bcc12969713f486e4b1000,0x6db8c01705d389e49ed2aeb38a9faa7957000,0x34766f000]
def packed28 : Array Nat := #[0x6f0ffe3c86cfb3a4216999078dae739580,0x4639000,0xe7cb92589707000,0xe6dc600b82e90a8ed28e41e28ff3947582,0x6f368252d28b11b9669000,0x18cdb401705d389e49ed2aeb38a9faa7957000,0x966999c87000,0xe6d68252cd22c46e5a5000,0x1bcda1af5b4b1ba4566f1b9000,0x1ad04a5a3bcce438b8384df2af000,0x9000,0x1ad04a5a3bcce438b8384df2af000,0x9000,0x1b1b9b91296db7f2ecbff9000,0x18cdb401705d389e49ed2aeb38a9faa7957000,0x8589e1583,0x36d6947cb1b3d3ff9000,0x18cdb5a04fed000,0x350bedbff8cda529000,0xc64e3369000,0x12d580e060c2946aee0036cf000000,0x1a000,0x16172bfb81132f060c000000,0x12d580e060c2946aee0036cf000000,0x37709bcfaebe129000,0xdc086e1bc30a529ea1b9b8671fb643c4a487ee25b9d0ef000586,0x10f774b530c37438ba1e7f81f250cebf5f7c0000,0xddc20b5ad587,0x52d589,0xe7cc13a529000,0x2694fbf58a,0xc5e9000]
def packed29 : Array Nat := #[0xcafd6f000,0x430dca74e36efd7fe43c971ff44f83bc000000,0xf67b37ec214beebec071ad1719e921c05fbc96e2f33e51dc0058b,0x18bd29000,0x494472ef000,0x1e0bc0748b1b19f1de0513f99ff5c0058c,0x4a3ff5c472ef58d,0x4f981384e6cd929494a5000,0x157d58e,0x35a93731f04260ffef96f8a8f43d1be45fc245fe6beade9baaf21ed90f058f,0x234b43f7fc29bf9ff592,0x127f60f000,0xe69000,0x4a3ff5c472ef594,0x11934929eef48f8f4fc20ffeb1df8b83c5e3bdcbe438595,0x4afcd97000,0x34d02ffc07ab4a15bf1aa9f5000,0x572cbb7233b265f987e42c85b90d721596,0x35a2c313e03d5a5189f1aa9f5000,0x572cbb7233b265f987e42c85b90d72159a,0x28f000,0x9b9f324bcc69c7f3c5c02265fcf870000000,0x4b294a5000,0x4b294a5000,0x6c8f15fa0f8210c7ffde2df93e9f2d17f53f91e9726fe13937f059e,0x32384e191ed3f5a0,0x25735ca9000,0x63f000,0x965125000,0x294afee4bb6d31e5967f172f000000,0x597ad54b69620ab0fa5987e5dfd77c0000,0x364b3749f7ee0d7e9ffeb7e000000]
def packed30 : Array Nat := #[0x16172bfb81132f076c000000,0x258a4fbf7065f2c00000,0xa52bfb92edb4c79619f172f000000,0xd000,0,0x11000,0,0,0x11000,0,0,0,0x11000,0,0,0,0,0xd000,0,0x11000,0xd000,0,0x11000,0xd000,0x4f000,0xd000,0,0x11000,0,0xd000,0x11000,0]
def packed31 : Array Nat := #[0x11000,0,0,0,0x1def7edcfc000,0,0x3b76000,0,0xe830af000,0x14bf55f2c7e000,0x2a9000,0x5b0af000,0,0x3000,0x15a2,0,0x56136e5a3,0x15a4,0x16bf39c000,0x5b0af000,0,0xb74000,0x2b067de15f93f000,0,0x230a35a5,0,0x15a6,0,0x74000,0,0xb74000,0x2c5ba000]
def packed32 : Array Nat := #[0,0xab5a7,0x5ce4dfab000,0x74000,0x8dcf7000,0x367000,0x15a8,0,0x3af74000,0x74000,0x1bb000,0x55bb5a9,0,0,0x346000,0x47fedff927efbf6e000,0xf5f176af000,0x5b0af000,0x5b0af000,0,0,0x2a9000,0x56136e5aa,0x15ab,0,0x36130e5ac,0x15ad,0,0xa60425ae,0x15b0,0x33000,0]
def packed33 : Array Nat := #[0,0x15b1,0x6604e139b36e5d25000,0,0x1374debff000,0x137000,0x26e15b2,0x9000,0x2a9000,0x2a9000,0x15000,0xedb0af000,0x14bf55f2c7e000,0,0x19ff8000,0x55fdb16f000,0x56af000,0x81f000,0x5b16f000,0x81f000,0,0,0x5b000,0,0,0x227000,0x10f4f15b3,0x7a75b5,0x89cb1000,0x397000,0x1084b15b6,0x227000]
def packed34 : Array Nat := #[0x11000,0,0x11000,0xd71000,0,0x3000,0,0x9000,0x174a5b9,0x743d5ba,0xd71000,0x15bf000,0x3bff000,0x195f000,0x7ff000,0x1e7000,0x66f000,0,0x7a15bb,0x1d000,0,0x84210864bdc75bd,0x1565c3,0,0,0x1d000,0x22792f000,0x227000,0x44f1000,0x1d000,0x36c2ada04215c4,0x15c9]
def packed35 : Array Nat := #[0x3b3f000,0x74000,0x1d000,0x1d000,0x1084210c97b8e5ca,0x24be27000,0x227000,0x11000,0x125e000,0x11000,0xd71000,0x125e000,0x5375affa70ab5affa72ffe5d0,0x74e000,0x48f000,0,0x27ff000,0x89cb1000,0x74e15d2,0x294a5294a5000,0,0xd000,0x11000,0x4f000,0,0xd000,0,0,0x11000,0x4f000,0,0xd000]
def packed36 : Array Nat := #[0,0x11000,0x4f000,0,0,0xd000,0x294a5294a5000,0,0,0x294a5294a5000,0,0x294a5294a5000,0,0x11000,0x4f000,0,0,0xd000,0,0xd000,0,0,0xd000,0xd000,0xd000,0,0xd000,0,0,0xd000,0xd000,0x11000]
def packed37 : Array Nat := #[0x4f000,0xd000,0x173f000,0x5000,0x5294a5294a5000,0x147f12f000,0x46a1fa346000,0,0,0,0x1f9f9f5ffc7e000,0x4ef000,0,0,0x367000,0,0,0,0x367000,0x38e15d3,0,0,0x367000,0x367000,0x36fd7bf000,0x17bf000,0x1a7000,0x1a15d4,0,0xa5a5d5,0,0x47d7bf000]
def packed38 : Array Nat := #[0xd000,0x4a3552000,0x15d6,0x29de95d7,0xb7ff5d8,0x6a15d9,0x368c000,0,0x15000,0x23466d1814615db,0x54000,0,0x4dd378ffe000,0x137000,0x26e15dd,0x359b000,0xbfd7ff30e000,0,0x2cda330e000,0x183000,0x147f51c000,0x15de,0x1601e000,0x7b00f000,0xf601e000,0,0x1b000,0,0,0x15df,0x25e0,0xe3f6e15e1]
def packed39 : Array Nat := #[0,0,0,0x1601e000,0xb362f1b27897b07a8e000,0xb00f000,0,0,0x173f000,0x5000,0x1a7000,0x1a15e2,0,0xa5a5e3,0,0x1a7000,0x19df162da2dc741d83f000,0x194a5000,0x5000,0x67ff000,0xcef9e79e7b4f3dc741d83f000,0x38e59f000,0x4c994a5000,0x5000,0x77ff000,0x5000,0x5000,0x5000,0x5000,0,0,0x210bb294a55e4]
def packed40 : Array Nat := #[0x5000,0x5000,0x5000,0,0,0,0x171bed000,0x18df000,0x14a5000,0,0x215e7,0x3065000,0,0,0x7ffbce000,0x191f000,0x59f000,0x215e9,0x127f000,0x73000,0x1d0f5ffe5eb,0,0x215ec,0x12b9ae5000,0,0,0,0xa15ee,0,0x3a000,0,0x15bf000]
def packed41 : Array Nat := #[0xec9b8000,0x35e8d1ad7b9c000,0x1af46adf5af73804e720f5ef,0xb9ce792ffef20f000,0x11bf44ff2be0000,0x1af462351fe7000,0x4afc79d23f000,0x79ca5000,0x65d33f000,0x981bf4d8e00f930993000,0x123d8eacfff00f844847c8f15f0,0x249d8e7dc98e780000,0x91c23d3714f3eee80000,0x1bb1d53efd38e780000,0x6fff000,0x13000,0x48f1000,0,0x89cb1000,0x468ca11e57614dc53cfb85f1,0x2692614d8e7dc98e785f2,0x123847a453cfbf4000,0x3763d4fb9473c000,0x46060d43fb9ee7000,0x2e7000,0x13000,0x5b0a5295f3,0x129000,0x35e8d1ad7b9c000,0x6bd1ab7d6bdce04e720f5f4,0xb9e4be2720f000,0x237e89fe57c0000]
def packed42 : Array Nat := #[0x1af462351fe7000,0x4afc79d23f000,0x44e5000,0x65d33f000,0x11000,0x11000,0xd71000,0,0x3876af000,0x54000,0x189aa000,0x1fff000,0x54000,0x54000,0x54000,0x7b00f000,0,0x19c97000,0x1a7000,0x7b00f000,0x7b00f000,0x2c5e77da2dc741d83f000,0x5000,0x11f000,0x5ef000,0,0x54000,0x54000,0x173f000,0x3876af000,0x48e7f6af000,0x1d000]
def packed43 : Array Nat := #[0x18bf000,0x18bf000,0x2b000,0x46000,0xa33fff5f5,0,0x18bf000,0xe830af000,0x14bf55f2c7e000,0xac1942156f85bd23ce75f6,0xe830af000,0xeef000,0,0,0x7dd97000,0x4a5294a529000,0,0x4f000,0xd000,0,0,0x11000,0x4a5294a529000,0,0,0x4f000,0xd000,0,0,0x11000,0x4a5294a529000,0]
def packed44 : Array Nat := #[0x4a5294a529000,0,0,0,0,0,0x1a7000,0x1a15f8,0,0xa5a5f9,0,0x3876af000,0x3fff8000,0xf5f176af000,0x2b000,0x465000,0x1ad4a6ed000,0x1185375fa,0x465000,0x8d2d000,0xf5f176af000,0x1eb907f6af000,0,0xd000,0,0,0,0xd000,0,0,0x364791c27000,0x247000]
def packed45 : Array Nat := #[0x191c275fb,0,0,0,0,0x23000,0x15fc,0x2b000,0,0,0,0,0,0,0x25fd,0x15fe,0,0,0,0x227000,0,0x227000,0x227000,0x11000,0,0,0x1d000,0,0,0,0,0]
def packed46 : Array Nat := #[0,0,0,0,0,0,0,0x227000,0x11000,0,0,0,0,0,0,0,0,0x227000,0,0,0xd000,0,0,0x9000,0,0,0,0,0,0,0,0]
def packed47 : Array Nat := #[0,0x215ff,0xd000,0,0x5000,0,0,0x1601,0,0,0,0,0x1602,0,0,0,0x227000,0x5000,0x9000,0x11000,0,0,0x294a5294a5000,0,0xd000,0,0x5000,0,0,0,0,0]
def packed48 : Array Nat := #[0,0,0]
def rows : Array (Array Nat) := #[packed0,packed1,packed2,packed3,packed4,packed5,packed6,packed7,packed8,packed9,packed10,packed11,packed12,packed13,packed14,packed15,packed16,packed17,packed18,packed19,packed20,packed21,packed22,packed23,packed24,packed25,packed26,packed27,packed28,packed29,packed30,packed31,packed32,packed33,packed34,packed35,packed36,packed37,packed38,packed39,packed40,packed41,packed42,packed43,packed44,packed45,packed46,packed47,packed48]
def config (id : Nat) : Nat × Nat :=
  let v := (rows.getD (id / 32) #[]).getD (id % 32) 0
  (v &&& 4095,v >>> 12)
end Complement2311.Search
namespace Complement2311.Search
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Cert
open Complement2311.Order

def factsAt (i : Nat) := Face.evidence[i]?
theorem validAt (i d) (h : factsAt i=some d) : Face.checked d=true := by
  have inside : i<Face.evidence.size := by
    by_contra! no
    simp [factsAt,Array.getElem?_eq_none no] at h
  let idx : Fin 55 := ⟨i,inside⟩
  have eq : d=Face.fact idx := by
    simpa [factsAt,Array.getElem?_eq_getElem inside,Face.fact,idx,eq_comm] using h
  exact eq ▸ Face.valid idx

theorem initial_supply : ∀ w∈source,w∈Face.seen [] := by
  intro w hw
  simpa [source,Face.seen,Face.start,Face.extra,Face.rawAt,or_comm] using hw
end Complement2311.Search
namespace Complement2311.Search
open Cert hiding inputs seed
def negRows : List Row := [42,50,69,104,116,138,200,201,208,261,276,385,402]
def misses (w : Sig) : List Row → Nat
  | [] => 0
  | n::ns => ((misses w ns) <<< 1) ||| (if bit n w then 0 else 1)
def encode (w : Sig) (block : Nat) : List Row → Nat
  | [] => 0
  | p::ps => ((encode w block ps) <<< 13) ||| (if bit p w then block else 0)
def coverage (w : Sig) := encode w (misses w negRows) posRows
def unionCover : List Sig → ℕ
  | [] => 0
  | w::ws => coverage w ||| unionCover ws
def pairMask : Nat := 2^208-1
def fastSep (ws : List Sig) := ((unionCover ws)&&&pairMask)==pairMask

theorem misses_lt (w : Sig) (ns : List Row) : misses w ns < 2^ns.length := by
  induction ns with
  | nil => simp [misses]
  | cons n ns ih =>
    unfold misses
    apply Nat.or_lt_two_pow
    · simp [Nat.shiftLeft_eq,Nat.pow_succ];omega
    · have pos := Nat.two_pow_pos ns.length
      cases h : bit n w <;> simp [Nat.pow_succ] <;> omega

theorem misses_at (w : Sig) (ns : List Row) (j : Fin ns.length) :
    (misses w ns).testBit j.val= !(bit ns[j] w) := by
  induction ns with
  | nil => exact Fin.elim0 j
  | cons n ns ih =>
    cases j using Fin.cases with
    | zero => cases h : bit n w <;> simp [misses,Nat.testBit_or,h]
    | succ j =>
      cases h : bit n w <;> simp [misses,Nat.testBit_or,Nat.testBit_shiftLeft,h,Nat.testBit_one_eq_true_iff_self_eq_zero,ih]

theorem encode_at (w : Sig) (ps : List Row) {block : Nat} (size : block<2^13)
    (i : Fin ps.length) (j : Fin 13) :
    (encode w block ps).testBit (i.val*13+j.val) = (bit ps[i] w && block.testBit j.val) := by
  induction ps with
  | nil => exact Fin.elim0 i
  | cons p ps ih =>
    cases i using Fin.cases with
    | zero =>
      have hj := j.isLt
      cases h : bit p w <;> simp [encode,Nat.testBit_or,Nat.testBit_shiftLeft,h,show ¬13≤j.val by omega]
    | succ i =>
      let t := (i.val+1)*13+j.val
      have large : 13≤t := by dsimp [t];omega
      have sub : t-13=i.val*13+j.val := by dsimp [t];omega
      have ht : block.testBit t=false := Nat.testBit_lt_two_pow (lt_of_lt_of_le size (Nat.pow_le_pow_right (by decide) large))
      have ht' : block.testBit ((i.val+1)*13+j.val)=false := ht
      cases h : bit p w <;> simp [encode,Nat.testBit_or,Nat.testBit_shiftLeft,h,show 13≤(i.val+1)*13+j.val from large,show (i.val+1)*13+j.val-13=i.val*13+j.val from sub,ht',ih]

theorem union_hit {w ws i} (mem : w∈ws) (hit : (coverage w).testBit i=true) : (unionCover ws).testBit i=true := by
  induction ws with
  | nil => simp at mem
  | cons a ws ih =>
    rw [unionCover,Nat.testBit_or,Bool.or_eq_true]
    rcases List.mem_cons.mp mem with rfl|rest
    · exact Or.inl hit
    · exact Or.inr (ih rest)

theorem all_posrows : ∀ i : Fin 16, bit posRows[i] graph=true := by decide +kernel
theorem all_negrows : ∀ i : Fin 13, bit negRows[i] graph=false := by decide +kernel
theorem fastSep_ok {ws k} (run : Front2778.live ops graph k ws.toFinset) : fastSep ws=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and]
  cases ht : pairMask.testBit t with
  | false => simp
  | true =>
    have small : t<208 := by
      by_contra! bad
      have off : pairMask.testBit t=false := Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : pairMask<2^208) (Nat.pow_le_pow_right (by decide) bad))
      simp_all
    let i : Fin 16 := ⟨t/13,by omega⟩
    let j : Fin 13 := ⟨t % 13,by omega⟩
    obtain ⟨w,mem,on,off⟩ := Front2778.live_separates (fun w => bit posRows[i] w=true ∧ bit negRows[j] w=false)
      ⟨all_posrows i,all_negrows j⟩ (transfer _ _) run
    have flag := encode_at w posRows (block:=misses w negRows) (misses_lt w negRows) i j
    have eq := misses_at w negRows j
    change (misses w negRows).testBit j.val= !(bit negRows[j] w) at eq
    change (coverage w).testBit (i.val*13+j.val)=(bit posRows[i] w && (misses w negRows).testBit j.val) at flag
    rw [eq,on,off] at flag
    have idx : i.val*13+j.val=t := by dsimp [i,j];omega
    rw [idx] at flag
    simpa using union_hit (List.mem_toFinset.mp mem) (by simpa [coverage] using flag)
end Complement2311.Search
namespace Complement2311.Search
open Cert hiding inputs seed
def tiles (v : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => ((tiles v k) <<< 13)|||v
structure Enc where
  val : Sig
  pos : Nat
  off : Nat
def enc (w : Sig) : Enc := ⟨w,encode w 8191 posRows,tiles (misses w negRows) 16⟩
def Enc.gate (d : Bool) (a b : Enc) : Enc :=
  if d then ⟨a.val|||b.val,a.pos|||b.pos,a.off&&&b.off⟩
  else ⟨a.val&&&b.val,a.pos&&&b.pos,a.off|||b.off⟩
def Enc.both (a : Enc) := a.pos&&&a.off
def Enc.Good (a : Enc) := ∀ (i : Fin 16) (j : Fin 13),
  a.pos.testBit (i.val*13+j.val)=bit posRows[i] a.val ∧
  a.off.testBit (i.val*13+j.val)= !(bit negRows[j] a.val)
theorem tiles_bit (v k : Nat) (bound : v<2^13) (i : Fin k) (j : Fin 13) :
    (tiles v k).testBit (i.val*13+j.val)=v.testBit j.val := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases i using Fin.cases with
    | zero => have hj := j.isLt; simp [tiles,Nat.testBit_or,Nat.testBit_shiftLeft,show ¬13≤j.val by omega]
    | succ i =>
      have large : 13≤(i.val+1)*13+j.val := by omega
      have sub : (i.val+1)*13+j.val-13=i.val*13+j.val := by omega
      have hi := Nat.testBit_lt_two_pow (lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) large))
      simp [tiles,Nat.testBit_or,Nat.testBit_shiftLeft,large,sub,hi,ih]
theorem enc_good (w : Sig) : (enc w).Good := by
  intro i j
  constructor
  · have h := encode_at w posRows (block:=8191) (by decide) i j
    change (encode w 8191 posRows).testBit (i.val*13+j.val)=(bit posRows[i] w && (8191:Nat).testBit j.val) at h
    have yes : Nat.testBit 8191 j.val=true := by
      change Nat.testBit (2^13-1) j.val=true
      exact (Nat.testBit_two_pow_sub_one 13 j.val).trans (decide_eq_true j.isLt)
    simpa [enc,yes] using h
  · exact (tiles_bit _ 16 (misses_lt w negRows) i j).trans (misses_at w negRows j)
theorem Enc.good_gate {a b : Enc} (ha : a.Good) (hb : b.Good) (d : Bool) : (a.gate d b).Good := by
  intro i j
  obtain ⟨pa,na⟩ := ha i j
  obtain ⟨pb,nb⟩ := hb i j
  cases d <;> simp [Enc.gate,Nat.testBit_or,Nat.testBit_and,pa,pb,na,nb,bit]
theorem both_at {a : Enc} (h : a.Good) (i : Fin 16) (j : Fin 13) :
  a.both.testBit (i.val*13+j.val)=(coverage a.val).testBit (i.val*13+j.val) := by
  obtain ⟨yes,no⟩ := h i j
  have x := encode_at a.val posRows (block:=misses a.val negRows) (misses_lt _ _) i j
  change (coverage a.val).testBit (i.val*13+j.val) = (bit posRows[i] a.val && (misses a.val negRows).testBit j.val) at x
  rw [Enc.both,Nat.testBit_and,yes,no,x]
  exact congrArg (fun v => bit posRows[i] a.val && v) (misses_at a.val negRows j).symm
end Complement2311.Search
namespace Complement2311.Search
open Front2778
open Cert hiding inputs seed
open Complement2311.Order

def wideChildren (k : ℕ) (ws hist : List Sig) := (pairs ws).flatMap fun (a,b,r) =>
  [a&&&b,a|||b].flatMap fun z =>
    if allows hist a b z && !Face.badGate z hist then (keepChoices a b r).filterMap fun retained =>
      let child := z::retained
      if child.length≤k+1 && fastSep child then some child else none
    else []

theorem wide_child_sorted {ws hist : List Sig} {c cs} (h : Needed ws.toFinset (c::cs))
    (budget : hist.length+cs.length+1=14) (hn : ws.Nodup) (order : DeepFollows hist (c::cs))
    (past : Face.History hist) (supply : ∀w∈ws,w∈Face.seen hist) :
    ∃ rem,c.val::rem∈wideChildren cs.length ws hist ∧ (c.val::rem).Nodup ∧ Needed (c.val::rem).toFinset cs ∧
      Face.History (c.val::hist) ∧ ∀w∈c.val::rem,w∈Face.seen (c.val::hist) := by
  obtain ⟨r,shape,ab,new,next⟩ := Needed.head h
  let z := c.val
  let a := c.left
  let b := c.right
  have hop : z∈ops a b := c.choice
  have tail := next.live
  have am : a∈ws := List.mem_toFinset.mp (shape ▸ (by simp [a,b]))
  have bm : b∈ws := List.mem_toFinset.mp (shape ▸ (by simp [a,b]))
  obtain ⟨rest,choice,swapped⟩ := pick_two am bm ab
  have credit : (!Face.badGate z hist)=true := by
    simp only [Bool.not_eq_true']
    apply Bool.eq_false_iff.mpr
    intro bad
    classical
    let all := z::r.toList
    have identity : all.toFinset=insert z r := by simp [all]
    have sup : ∀w∈all,w∈z::Face.seen hist := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl|there
      · exact List.mem_cons_self ..
      have inside : w∈r := Finset.mem_toList.mp there
      exact List.mem_cons_of_mem _ (supply _ (List.mem_toFinset.mp (shape ▸ (by simp [inside]))))
    have impossible := Face.bad_short past bad sup (identity.symm ▸ tail)
    omega
  have oldA := supply a am
  have oldB := supply b bm
  have hbuild : Face.History (z::hist) := by
    rcases (show z=a&&&b ∨ z=a|||b by simpa [ops] using hop) with hx|hx
    · rw [hx]; exact Face.History.gate past oldA oldB false
    · rw [hx]; exact Face.History.gate past oldA oldB true
  have go {a b : Sig} (picked : (a,b,rest)∈pairs ws) (perm : ws.Perm (a::b::rest))
      (shape : ws.toFinset=insert a (insert b r)) (hop : z∈ops a b) (okOrd : allows hist a b z=true) :
      ∃ rem,z::rem∈wideChildren cs.length ws hist ∧ (z::rem).Nodup ∧ Needed (z::rem).toFinset cs ∧
        Face.History (z::hist) ∧ ∀w∈z::rem,w∈Face.seen (z::hist) := by
    obtain ⟨rem,hkept,nd,eq⟩ := recover_kept perm hn shape
    have old : rem.toFinset⊆ws.toFinset := by rw [eq,shape];exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    have valid : (z::rem).Nodup := List.nodup_cons.mpr ⟨fun hm => new (old (List.mem_toFinset.mpr hm)),nd⟩
    have run : Needed (z::rem).toFinset cs := by simpa [eq] using next
    have fits := live_card run.live
    rw [List.toFinset_card_of_nodup valid] at fits
    have sep := fastSep_ok run.live
    refine ⟨rem,?_,valid,run,hbuild,?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨_,picked,List.mem_flatMap.mpr ⟨z,?_,?_⟩⟩
      · simpa [ops] using hop
      · simp only [credit,okOrd,Bool.and_true,ite_true]
        exact List.mem_filterMap.mpr ⟨rem,hkept,by simp [sep]; simpa using fits⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl|given
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (supply _ (List.mem_toFinset.mp (old (List.mem_toFinset.mpr given))))
  rcases choice with one|two
  · exact go one swapped shape hop order.1
  · apply go two (swapped.trans (.swap _ _ _)) (shape.trans (Finset.insert_comm ..))
    simpa only [ops,BitVec.and_comm a b,BitVec.or_comm a b] using hop

    exact (allows_comm hist a b z) ▸ order.1

end Complement2311.Search
namespace Complement2311.Search
open Complement2311.Order
open Cert hiding inputs seed
def unionEnc : List Enc → Nat
  | [] => 0
  | a::as => a.both ||| unionEnc as
def encKeep (k : Nat) (a b z : Enc) (r : List Enc) :=
  let rc := unionEnc r
  let ac := a.both ||| rc
  let bc := b.both ||| rc
  let abc := a.both ||| bc
  let zc := z.both
  let tagged := [(r,rc),(a::r,ac),(b::r,bc),(a::b::r,abc)]
  tagged.filterMap fun (keep,u) =>
    if keep.length≤k && (((zc|||u)&&&pairMask)==pairMask) then some (z.val::keep.map Enc.val) else none
def matrixWideChildren (k : Nat) (ws hist : List Sig) := (pairs (ws.map enc)).flatMap fun (a,b,r) =>
  [a.gate false b,a.gate true b].flatMap fun z =>
    if allows hist a.val b.val z.val && !Face.badGate z.val hist then encKeep k a b z r else []
theorem singles_map {A B} (f : A→B) (ws : List A) :
    singles (ws.map f) = (singles ws).map (fun (a,r) => (f a,r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a r ih => simp [singles,ih,List.map_map,Function.comp_def]
theorem pairs_map {A B} (f : A→B) (ws : List A) :
    pairs (ws.map f) = (pairs ws).map (fun (a,b,r) => (f a,f b,r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a r ih => simp [pairs,singles_map,ih,List.map_map,Function.comp_def]
theorem union_same {xs : List Enc} (good : ∀x∈xs,x.Good) (i : Fin 16) (j : Fin 13) :
    (unionEnc xs).testBit (i.val*13+j.val)=(unionCover (xs.map Enc.val)).testBit (i.val*13+j.val) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [unionEnc,unionCover,Nat.testBit_or,both_at (good a (by simp)) i j,ih (fun x hx=>good x (by simp [hx]))]
theorem masked_same {xs : List Enc} (good : ∀x∈xs,x.Good) :
    (unionEnc xs)&&&pairMask=(unionCover (xs.map Enc.val))&&&pairMask := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_and]
  cases ht : pairMask.testBit t with
  | false => simp
  | true =>
    have small : t<208 := decide_eq_true_iff.mp ((Nat.testBit_two_pow_sub_one 208 t).symm.trans ht)
    let i : Fin 16 := ⟨t/13,by omega⟩
    let j : Fin 13 := ⟨t % 13,by omega⟩
    have idx : i.val*13+j.val=t := by dsimp [i,j];omega
    simpa [idx] using union_same good i j
theorem sameKeep (k : Nat) {a b z : Enc} {r : List Enc} (ha : a.Good) (hb : b.Good)
    (hz : z.Good) (hr : ∀x∈r,x.Good) :
    encKeep k a b z r = (keepChoices a.val b.val (r.map Enc.val)).filterMap fun retained =>
      let child := z.val::retained
      if child.length≤k+1 && fastSep child then some child else none := by
  have consGood {c : Enc} {cs : List Enc} (hc : c.Good) (hs : ∀v∈cs,v.Good) : ∀v∈c::cs,v.Good := by
    intro v m;rcases List.mem_cons.mp m with rfl|m;exact hc;exact hs v m
  have m0 := masked_same (consGood hz hr)
  have m1 := masked_same (consGood hz (consGood ha hr))
  have m2 := masked_same (consGood hz (consGood hb hr))
  have m3 := masked_same (consGood hz (consGood ha (consGood hb hr)))
  simp only [unionEnc,List.map_cons] at m0 m1 m2 m3
  simp [encKeep,keepChoices,List.filterMap,fastSep,List.length_map,m0,m1,m2,m3]
theorem matrixWideEq (k ws hist) : matrixWideChildren k ws hist=wideChildren k ws hist := by
  simp only [matrixWideChildren,pairs_map,List.flatMap_map,Function.comp_def]
  unfold wideChildren
  apply List.flatMap_congr
  rintro ⟨a,b,r⟩ _
  change _ = (([a&&&b,a|||b] : List Sig).flatMap _)
  have hr : ∀x∈r.map enc,x.Good := by intro x hx;obtain ⟨w,_,rfl⟩ := List.mem_map.mp hx;exact enc_good w
  have andKeep := sameKeep k (enc_good a) (enc_good b) (Enc.good_gate (enc_good a) (enc_good b) false) hr
  have orKeep := sameKeep k (enc_good a) (enc_good b) (Enc.good_gate (enc_good a) (enc_good b) true) hr
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [andKeep,orKeep]
  simp [Enc.gate,enc,List.map_map,Function.comp_def]
end Complement2311.Search
namespace Complement2311.Search.Flat
open Cert hiding inputs seed
open Complement2311.Order
def packs : Array Nat := #[0x2e0003580004b0000d400012800024c0007c3800786000eec001e1400342800775000eca001e0c00341800773000ec6001d4c003c1000772000ec4001d4800399000632000f02001dc4003b0800751000e62001c8400310800000000,0xf08007dd000fb2001f72003ae4007d8800fa1001d42003f2200764400fc0801f61003b2000760000eb0001f98002f28005e1000bb2001792002ec4005d0800bc8801781002b02005d0400aa0801694001ec8003640004c8000980001,0xa8400de4401bc8003590006f0000ddc001ba8003550006a8400be60013c3802795004f0a009dd4013ca002774004ee40095c8013a9002742004a84009e44012c8802781004b02009540013cc001f87003f2c007a5800fbb001f94003,0x1400135c0026b0004e96008eec011e50022c80041900083000115c0020b80045600082c0011500020a0004130008f2400fdc801fa9003f42007a8400fe4001ec8003a80007ee000fd4001ea8003f40007f2a00de5001ac9003582006,0xf28015e1002bba00579200aee4015d4802aa900579100ab22015dc402bc800528000aee00155c002ba800555000ae80015e60027cb804f87009f2c013dd8027ca004f84009ec8013e48027c1004d82009f22013644027b8804f61009,0xf2001be00037b8006e5000de8001be54033ca00655200cf30017e5c02fca805f8500bf28017e1002ec1005d7200baa4017e4402ec88058a000bf20017e0002fb8005d7000bea001754002fcc00579700af0e015e5402bc280577500a,0xb2401fe4403ec8807f8100f14001f60003eb8007d5000ff3001de5c03bc380779500eeea01de5003bc200779200eb2401ddc803bc880759100ef0201d60403ab800755000ea8001de48036c9006f7200dea401b548035500068a000d,0xe80027e4804bb90090a0012b2002550004bba808f94011b20022640044c0008d700112e0023540044a8008d400112800224c0047cc008795010f2802164804050008590010b00021500043cc007f9700ff2a01fe1403fca007f8400f,0xa80033e5805fca80bf94017b2402f58005cc800a980015ac002a580056a800a950015a8002a5000549800af94014b24029e6004fcb009f86013f2a027e5004fc2009d92013b04027e4404ec8809f80013ec002758004fa8009d50013,0xea004f68409ac881379802534604860c09099012131024300048580090a801214002426004868c08cc9811983023c8004354407ba000ef6101cac2039d800734000df5001bd06035d4c0685000cf90019ec0033580067a800cf40019,0xae00715880ded001bf91036ee206dd440daa881b79003650006ddc00dba801b620036b4606b6880d6d081ada0035b260695880d2d081a591034ee20662800cfc90195910321400642c00c058017da202e1600595880aed1014591027,0xaa407b6840f6c001ed5003db4807968c0f2c981e58003cac0079e600efcb81df9503bf0a07764c0eec901d8a003baa00776900ead181d59303ab440756000eab001d5a4039b440736000e6b801cf98038eec07164c0e2c881c0a0038,0xa8008b690112d10221a00423200845c0108b00215500422a008450010ad2020d93041b24083684106b8020d50041b44080ac0100580202300400600816900fed201f58203eaa407c5480fad081f58003eaa007c5400fac281eda403d,0x1600a28c0146b90281520502a00a1e1813ac182758104eea009d54013ad20265a204cb02099584133ca825f7504bf2609764c12ec8825d7004bac4095544126c8024da1048ae0091e5811ec8823d81047f2008f64011fb00238b0045,0xac40bcd0817ab802f2b005d1600baa80176b802eaa005c1400b8a40172d202d5a105ab480b3650166d082cab00591600b36801653002cd93058f240b0280160a002b0b0054b480a768814c58029d40053b280a42c014ab9028ab0051,0xee00d79401af98035f2006bc400d62c01a9500348a00695200d354c1a2c88345610681600cddcc194500328b0063a800c74c018eb90313520622a40c54c8189990311320625600c42c0189a80310a0061f2c0c1e48182c903075205f,0xec00ebe541d3b883a571074ee00e95c01d3c2039e80073ec00e7dd81cac8839590072d0a0e3d941c7c0038e85070eca0e1e0c1c2d18365a106cb020d95841b1580360b006cf240d76481afb9035f5206be420d6a801ac50035f9006b,0xac00ffe0c1f85003f78307db060fa2801f49903e13107c3200f85c01f0b003e15007c2800f84c01f2d183d9a307b3260f64c01ed9903d13207a5200f44c01eba803cd50079cc00f1d001e3c203bf95076ae20eddc01dab803b784075,0x160123e04242c08480a0090ac811e2c023ab804759508ab48115508224a1044da0089060113690222d10445a0088b4410be54212c98425910845601062c020ec8841531082540105684206d084079707ff2c0ffdd81ffca03ff6407f,0xb021338802655804c0b0098f2212f64425fb084bd6109754012e28025f1004bd72096a8412d68425bc304a795094ac6129648252c084a561094b461262c024fcb049786092f2a125e4824ac9049581092540124280249400495a3091,0xb48141688282d08500b00a0aa014150827da104f94209fb4013ea4027ed204f5a209eb4013d69026eb804dd8309ab4213560426ac004d798099f2e133e1c267ca84cf85099f2613364c267b984cf92099ee4133e44266c884cf81099,0x16015d6442b6b0856aa00adf2015be002b730056f970acf2a1595c82b2a90565700ac16015768c2aad1854f960a8f0c151e542a2c18547920a8b24150a802a0500542800a8b4614e2c029fc08530a00a6ae014a2c0288180515a20a1,0xb481656882cad00597960b1b261636442c7cc0587960b0f0c161e542c3c98585930b0f221616442c3b00585600b0ea0161e602bfcb857f950aff0a15fe4c2bec9857f920aff0415fdc82bfc8857d910aff0215f5c02bf10057ab00ae,0xb00182dc0304b8060d500c1f24181dc8303a90607900c0f00181dc0301b00601600c0ca0181d003005805f8b00be3401796402f0c805e1800bc2e01795802f0b005e1500bc160175e542e2b805bda40b4b441695082cca1059da00b3,0xac019a280332c80665a20cbb4019758032fca8655910ca14019564032bc2864f820c9140193e08322c10640a00c8ac018dd80317a8062d500c5b4218760430fd1860da30c1f06183d8c306b1860da10c1b2218360430630860d510c1,0x1401b5e14367c106c8a00d9f041b0280362b806bd400d72801ae5083505806a0300d4b4a1a769034eca069d920d3aa41a64c834ed08698b00d3aa01a75c834ad00695400d2b481a3688346c9068da00d1a801a368433ab80675a00cd,0x1401cf64c39bc88730a00e6ae01cb500396d1071d420e32841c6ac038c58071d420e2ae41c3680386a00709400e1b481c1688382b90705a00e0a801c168037ab006f5500ddb441b9680372b006e7850dbf081b75c036ea806dd400db,0xee01e55c03cbc2078f600f1c801e3dd43c3c88785910f0f201e16403c3b2077f800efc801dfd903bbc18773520ec2a41d82c03b2b9075b520eb5401d62803abc80757600eaea01d58803abcc074f940e9b201d35c03a6a00748a00e8,0xf0c201e54402c1880791100b22200a8040050080280100a801f82803efb987d0a00fab461f268c3e4c987c9320f95401f24c03e49907c3300f82601f1d403dea807bf400f6f081ebe543d2b007a7840f3ea01e7e543cbb88795710f2,0x160242a8047c5008fa9011fb0423a5484755808e8b011d2a023954046c5008d750117ca022dd0045b2808a750112b442182c0432b80865a210bb04216ac042c58085d7210a2a421360042458081f85102f0220428040858080f96100,0x26227064c4dc9909b93013732626c5cc4d89909b13113626026c64c4d4b989a9321353262685cc4d09909a1701332a02665c04bca809794012f26025e5c04a4a80949401292602525c049ca809394012726024f500494580918a0122,0xaa02e02805bca08b40b01661602c84c458ac88b0aa0161eec2c164c580500af8b015e1602ba2c0569500ac8a01591602b158855c580a98b01521602a02c053c500a47921471602885c050c580a08a01401602784404e8b889c141138,0x1603622c06c0a10d79311aeac235aa806b4500d68b01ab5403542806a8580d38b01a6160343500680580cf8b019408231c600639b80c6931189b2830d648618580c18a01821603024c4600580bf04017e1602ee2c05d2b08b9785170,0x2c23ce64079da90f33321e67003cc600799a80f30b01e51603be2c0776b80ed8b01d91603a62c0746d20e7d941cfb4239f68073c580e70a01ccf24395690716a00e28b01c4b28384640701c00df9801bf1603744c46e4a08da8b01b4,0x6e04045c080aa0101792201ee4403d4880790900f90201ee0402d8080728100f30201e40403880804581001a01fe3203fc6007f8b80ff1601fe2a03fd64c7d9500fb0a01f6a803e14c07c0580f78b01ee5403d0a407a0b18f39431e7,0x30042658084ca8109940213260426a00844c01081602102a04205008409810828020e10041c600826d19045a1208b02411584821b810417020816040ea80819481030b0204b4640568480ac0901461202a824054c480a18901580202,0x2624704c88dc9911b13123626046c4c88d49891a9302352644684c88ccb01191502322864565008acc01139602272a044e50089c98113a8022610044ca408944811289021e500432200864c010c1602182a04305008609810c280215,0xb464d454899c581335712655404cbe58988581305a325fae04b42c09645812b5912555404aa2c0950a09291212521604a22c09405812796224e26249a280930c0125b7024aac04925c091c58122890241ee247fe0c8f4c091c141238,0x540530280a60a994b14129524252a2c0a54581490b02911605202c0a34b11448b028726250c280a18581418a0281b224fe6409f5c013e18027cac04f50c49dcc013bf91276ec24ecdc09db1013b0b02721604e25489c0501370b026b,0x3005782c0aecd015c9902b93005725c0ae4b015cf962b6f2256d644adbb015b5602b6f2e56be44ad6c895ad702b5f2c568548ab8581565712ab540557e58aa6d19537812a426253e2c0a7ea814e15029c1605362c0a685814cd91298,0x6805d2504b90581715912e15405c2504b7c9096fd712db2625b6a80b6cb116b0b02d5b225a95c4b515016a0b02d12c45982c0b2ac8964d312c9262592a80b24581641902c070057e600afeb015f5a22bcae4579644af2c815e3802bc,0x2e0603580c04b0180950301f265fb64cbf7b997ef632fdac65fb644bf6c097ed712fdaa25fb580beec097cf932f5ee65ebd8cbd6c897ad812f5ae25ebe08bd3b117a1a02f3b205e6640bccc01799702f3ac05e6580bcca81799712f2,0xae4687e14d0bc299e78233a160670280cdca8996da532cb48659548cb09919655032c1606562c0ca8201950b03271606422c0c805018e8b031bf2a62f640c5c5018b78531316061ca80c3148186560308340603640c04c8180980301,0x5206f8240df0c81bd97037b2a06f6500dec981bd8a037a5206ea240dd4c81b99703732a06e6500dcc981b9a903721206e4d48db8581b68b03685406c9e44d86c89b08a035ef226b82c0d68a99ab1903567006aa2c0d4c581a50b0346,0x720770640ee0b01d99503b32807664c0eccb01d89503b12807624c0ec6b81d70b03ad340754540ea9c81d49903a96807522c0ea0581d35703a5f0a744508e78581ce57139b540737e58e64d21c794338f28071ea40e0d481c0090380,0x2e08aa581154a822a9714522e08a4601125b822416343e28687c5850f8b0a1db5243a664874105098502108a041d520838241070c020d37041930082edc1058a0a058a0406140802a40fe8b81fc1703f16c07e0280fb8b19dc9a03b9,0x1409ba28135420a674314c9062992605314c02629904c42c0986281308c825e9904bb2e09661051cac9a3659146c3408c8641190c02321704642c08c85411902122fd9345eb228bd0c517918a2f03145eb228ac681154c822a980455,0x42bc25c16bdb02d71605a62c6b40545644c82c4990587520ad22415a4a9ab234053dac0a742414d040299d6052a680a4460146ca128b190516320a28641444a028894250a300a156493feb927fd814ff3209da6413acc026fb704de,0x5097b0a12f38415e1]
def get (i : Nat) := ((packs.getD (i / 32) 0) >>> (23*(i % 32))) &&& 8388607
def remaining (i : Nat) := if i<1 then 14 else if i<26 then 13 else if i<294 then 12 else if i<963 then 11 else if i<1442 then 10 else if i<1532 then 9 else 8
def recover : Nat → Nat → List Sig × List Sig
  | 0,_ => (source,[])
  | _+1,0 => (source,[])
  | d+1,id+1 =>
    let x := get (id+1)
    let (ws,h) := recover d (x&&&4095)
    let a := ws.getD ((x>>>12)&&&15) 0
    let b := ws.getD ((x>>>16)&&&15) 0
    let z := if x.testBit 20 then a|||b else a&&&b
    let r := (ws.erase a).erase b
    let withB := if x.testBit 22 then b::r else r
    let withA := if x.testBit 21 then a::withB else withB
    (z::withA,z::h)
def matchChild (k id : Nat) (ws hist : List Sig) :=
  decide (id<1539 ∧ remaining id=k) && (ws==(recover 6 id).1) && (hist==(recover 6 id).2)
def test (id : Nat) :=
  let (ws,h) := recover 6 id
  let k := remaining id-1
  let cfg := config id
  scan hints factsAt k h (matchChild k) (matrixWideChildren k ws h) cfg.1 cfg.2
def chunk (b : Nat) := (List.range 8).all fun j => if b*8+j<1539 then test (b*8+j) else true
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem all_test (verified : ∀ b : Fin 193,chunk b.val=true) (i : Nat) (hi : i<1539) : test i=true := by
  let b : Fin 193 := ⟨i/8,by omega⟩
  have hh := List.all_eq_true.mp (verified b) (i % 8) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have eq : b.val*8+i % 8=i := by dsimp [b];omega
  simpa only [eq,hi,ite_true] using hh
end Complement2311.Search.Flat
namespace Complement2311.Search.Flat
open Front2778
open Cert hiding inputs seed
open Complement2311.Order

theorem exclude (verified : ∀ b : Fin 193, chunk b.val=true)
    {id ws hist cs} (inside : id<1539) (time : remaining id=cs.length)
    (wires : ws=(recover 6 id).1) (events : hist=(recover 6 id).2)
    (budget : hist.length+cs.length=14) (past : Face.History hist)
    (supply : ∀ w∈ws,w∈Face.seen hist) (nd : ws.Nodup)
    (order : DeepFollows hist cs) (run : Needed ws.toFinset cs) : False := by
  induction cs generalizing id ws hist with
  | nil =>
    simp only [List.length_nil] at time
    unfold remaining at time
    split_ifs at time <;> omega
  | cons c cs ih =>
    have checked := all_test verified id inside
    unfold test at checked
    simp only [matrixWideEq,← wires,← events,time,List.length_cons,Nat.add_sub_cancel] at checked
    obtain ⟨rem,mem,nd',run',hist',supply'⟩ := wide_child_sorted run (by simpa [Nat.add_assoc] using budget) nd order past supply
    rcases scan_seen checked mem with ⟨j,yes⟩|⟨child,yes⟩
    · exact Bool.noConfusion (yes.symm.trans (proofCut_no validAt hist' supply' nd' run'.live))
    · simp only [matchChild,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at yes
      exact ih yes.1.1.1 yes.1.1.2 yes.1.2 yes.2
        (by simp only [List.length_cons] at budget ⊢; omega) hist' supply' nd' order.2 run'

theorem no_circuit_flat (verified : ∀ b : Fin 193, chunk b.val=true)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) (cap : C.size≤15)
    (first : ∀ x : P2828.Y,(C.wires (List.ofFn x)).getD 9 false= !x 0)
    (out : PEqualNP.MetaComplexity.circuitFun 9 C=P2828.nine) : False := by
  obtain ⟨B,_,size,gates,hfan,ok⟩ := FirstFree.shape C fan cap first out
  have prog := input_build B hfan gates ok
  rw [size] at prog
  obtain ⟨cs,count,run,sort⟩ := ordered_root prog
  exact exclude verified (id:=0) (ws:=source) (hist:=[]) (by decide) (by rw [count]; rfl) rfl rfl
    (by simpa using count) Face.History.empty initial_supply (by decide +kernel)
    (deep_follows sort) run
end Complement2311.Search.Flat
namespace Complement2311.Search.Flat
def group (b : Nat) := (List.range 4).all fun j => if b*4+j<193 then chunk (b*4+j) else true
theorem all_chunks (h : ∀ b : Fin 49,group b.val=true) (i : Fin 193) : chunk i.val=true := by
  let b : Fin 49 := ⟨i.val / 4,by omega⟩
  have x := List.all_eq_true.mp (h b) (i.val % 4) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have e : b.val*4+i.val % 4=i.val := by dsimp [b];omega
  simpa only [e,i.isLt,ite_true] using x
end Complement2311.Search.Flat
namespace Complement2311.Search.Flat
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group0 : group 0=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group1 : group 1=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group2 : group 2=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group3 : group 3=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group4 : group 4=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group5 : group 5=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group6 : group 6=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group7 : group 7=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group8 : group 8=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group9 : group 9=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group10 : group 10=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group11 : group 11=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group12 : group 12=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group13 : group 13=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group14 : group 14=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group15 : group 15=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group16 : group 16=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group17 : group 17=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group18 : group 18=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group19 : group 19=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group20 : group 20=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group21 : group 21=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group22 : group 22=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group23 : group 23=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group24 : group 24=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group25 : group 25=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group26 : group 26=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group27 : group 27=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group28 : group 28=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group29 : group 29=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group30 : group 30=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group31 : group 31=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group32 : group 32=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group33 : group 33=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group34 : group 34=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group35 : group 35=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group36 : group 36=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group37 : group 37=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group38 : group 38=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group39 : group 39=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group40 : group 40=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group41 : group 41=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group42 : group 42=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group43 : group 43=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group44 : group 44=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group45 : group 45=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group46 : group 46=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group47 : group 47=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem group48 : group 48=true := by decide +kernel
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem checked : ∀ b : Fin 193,chunk b.val=true := by
  apply all_chunks
  intro b
  fin_cases b
  · exact group0
  · exact group1
  · exact group2
  · exact group3
  · exact group4
  · exact group5
  · exact group6
  · exact group7
  · exact group8
  · exact group9
  · exact group10
  · exact group11
  · exact group12
  · exact group13
  · exact group14
  · exact group15
  · exact group16
  · exact group17
  · exact group18
  · exact group19
  · exact group20
  · exact group21
  · exact group22
  · exact group23
  · exact group24
  · exact group25
  · exact group26
  · exact group27
  · exact group28
  · exact group29
  · exact group30
  · exact group31
  · exact group32
  · exact group33
  · exact group34
  · exact group35
  · exact group36
  · exact group37
  · exact group38
  · exact group39
  · exact group40
  · exact group41
  · exact group42
  · exact group43
  · exact group44
  · exact group45
  · exact group46
  · exact group47
  · exact group48
end Complement2311.Search.Flat
end PEqualNP.Outside.L_meta_1936
open PEqualNP.Outside.L_meta_1936

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_1936.SignedCircuitAux
theorem PEqualNP.Outside.L_meta_1936 :     ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  have impossible := Complement2311.Search.Flat.no_circuit_flat Complement2311.Search.Flat.checked
  intro ins short C fan size
  by_contra! computes
  let a : Gate := ⟨.and,ins⟩
  let n : Gate := ⟨.not,[0]⟩
  let B : Circuit := ⟨n::a::C.gates,C.output⟩
  apply impossible B
  · intro g hg
    rcases List.mem_cons.mp hg with rfl|later
    · simp [n]
    rcases List.mem_cons.mp later with rfl|later
    · exact ⟨by simp [a],short⟩
    exact fan _ later
  · change C.gates.length+1+1≤15
    change C.gates.length≤13 at size
    omega
  · intro x
    change (wiresFrom (a::C.gates) (List.ofFn x ++ [GateOp.not.eval ([0].map fun i=>(List.ofFn x).getD i false)])).getD 9 false=_
    rw [getD_wiresFrom _ _ 9 (by simp)]
    simp [GateOp.eval,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  · funext x
    change (wiresFrom C.gates _).getD C.output false=_
    simpa [wiresFrom,B,a,n,Circuit.eval,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD,List.getElem?_ofFn,P2828.nine] using computes x
