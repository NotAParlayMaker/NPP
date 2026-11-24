import Mathlib
import PEqualNP.Defs

-- Uses the finite circuit search method of L-meta-515.
namespace PEqualNP.Outside.L_meta_2828

namespace ImportedHelpers
open PEqualNP.CircuitLowerBounds
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end ImportedHelpers

namespace ThetaSigned
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev Wire (X : Type) := X → Bool
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def inv {X : Type} (f : Wire X) : Wire X := fun x => !(f x)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def bit {X : Type} (b : Bool) : Wire X := fun _ => b
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def bin {X : Type} (isOr : Bool) (a b : Wire X) : Wire X :=
  fun x => if isOr then a x || b x else a x && b x
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def plus {X : Type} (P : Set (Wire X)) (f : Wire X) : Set (Wire X) :=
  {g | g ∈ P ∨ g = f ∨ g = inv f}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Closed {X : Type} (P : Set (Wire X)) : Prop :=
  (∀ b, bit b ∈ P) ∧ ∀ f ∈ P, inv f ∈ P

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inv_inv {X : Type} (f : Wire X) : inv (inv f) = f := by funext x; simp [inv]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem plus_closed {X : Type} {P : Set (Wire X)} (hP : Closed P) (f : Wire X) : Closed (plus P f) := by
  refine ⟨fun b => Or.inl (hP.1 b),?_⟩
  intro g hg
  rcases hg with hg|rfl|rfl
  · exact Or.inl (hP.2 _ hg)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (inv_inv _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
inductive Run {X : Type} : Set (Wire X) → ℕ → Wire X → Prop
  | done {P k f} : f ∈ P → Run P k f
  | gate {P k f a b} (isOr : Bool) : a ∈ P → b ∈ P →
      Run (plus P (bin isOr a b)) k f → Run P (k+1) f

end ThetaSigned

namespace P2828
open ThetaSigned
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev Y := Fin 9 → Bool
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def small : Set (Wire Y) := {f | (∃ c, f=bit c) ∨ ∃ i : Fin 9, f=(fun x => x i) ∨ f=inv (fun x => x i)}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_closed : Closed small := by
  constructor
  · exact fun b => Or.inl ⟨b,rfl⟩
  · intro f hf
    rcases hf with ⟨b,rfl⟩|⟨i,rfl|rfl⟩
    · exact Or.inl ⟨!b,rfl⟩
    · exact Or.inr ⟨i,Or.inr rfl⟩
    · exact Or.inr ⟨i,Or.inl (inv_inv _)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def nine (y : Y) : Bool := (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5)
end P2828

namespace P2828Live

variable {α : Type} [DecidableEq α]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev W := BitVec 1378
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def neg (x : W) : W := ~~~x
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def both (x y : W) : W := x &&& y
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def canon (x : W) : W := if x.getLsbD 0 then neg x else x
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ops (x y : W) : List W :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sep (x : W) := (x ^^^ (x >>> 689)).setWidth 689
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cuts (ws : List W) : BitVec 689 := ws.foldr (fun w v => sep w ||| v) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def goal : W := canon (((-1 : BitVec 689) ++ (0 : BitVec 689)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a,rest) :: (singles rest).map (fun (b,bs) => (b,a :: bs))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b,bs) => (a,b,bs)) ++
      (pairs rest).map (fun (b,c,bs) => (b,c,a :: bs))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rawInputs : List W := [0x2aaaaaaaaaabaab555d556bebaab6adb557aad55ebb7daab6ab5575557add7edefb75fef8000000000000000007fffff8000000007ffa900a801202004212000849425ffaab16212008042142480955602a1bfffffffe14015555544d5502048aa4b58100469aaad540804cae850155aaaa02012aae0855a827795115115115115115115115115115115115114805400901002109000424a12ffd558b1090040210a12404aab0150d00000000,
0x333333333332cf399966672b3ccdb36d99acfe66b2fafccdb3de7bf99acee6f6f7dfeb778000000000000007ff8000000000007fffff8200014a000521444ffd11014800100a1444401114c148373ffffffff5560149608188808899228cccb311948060d9860412233359351020c884114ccd6551033a857588208e08e08e08e08e08e08e08e08e08e08e08c10000a5000290a227fe8880a40008050a2220088a60a41b900000000aab00a4b,
0x3c3c3c3c3c3cf3de1e787bcfdf0e3c71e1cf37873cdcef0e3ce79dfe1cf77bf8bae5f3fb0000000000007ff8000000000007fffff800004a321079784e098000260000920020409816e67fffffffee0128cec2012a121e1e021e0206016303042c220f870638f0e598c0864a678702714e33020a84bc457288758c50c50c50c50c50c50c50c50c50c50c50c5002519083cbc2704c000130000490010204c0b733000000007009467610095090,
0x3fc03fc03fc0fc1fe07f83f3eff03f81fe0fc7f83f1f7ff03f07e19fe0f87cbf3cf9fdbd0000000007ff8000000000007fffff8000003390c06382018000049000187120ddcf9fffffffe01871d9c06443010004406041601de015607e00203bc049f07819c00b02633c198098781d82b0ccf0743a439a0c768a01a41a41a41a41a41a41a41a41a41a41a41a59c86031c100c0000248000c38906ee7c0000000000c38ece0322180800220302,
0x3fffc0003fff001fff8003fc0fffc001fff007ffc01f8fffc007fe1fff007f3fc0fe7e3e0000000000000000000007fffff800000000406303804c4e098e092638218007fffff8e0fb3b98a1802208818c0a1bb98f839e9fe0000a9b000fdf8001b40787e000545000c3e0050787e00145030f80051c602109002a4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4a03181c0262704c704931c10c00000000c707d9dcc50c0110440c6050ddcc7c1c,
0x3fffffffc000001ffffffc000ffffffe000007ffffe00ffffff8001fffff803fff007fc07ff8007ff8000000007ff800000000000000007c03fc0f8ff00001c7fffffff8010c00001c3c0000013c0001f00c0001f3fc1e3e6aaa200000030337440007effb96000003f7fb3007afeaa4000fdfed401f7a803d80006c06c06c06c06c06c06c06c06c06c06c06c03e01fe07c7f80000e000000000008600000e1e0000009e0000f8060000f9fe0,
0x3fffffffffffffe0000000000ffffffffffff80000000fffffffffe00000003fffff80000007ff8000000007ff8000000000000000007c7ffc000ff001fffff8003e01c0e1f000009fc0003e01c000f9fff00021fc001f7e777f7766dd7000000000079f2679fbeddc00000007df377beeb00000001cc57a80000370370370370370370370370370370370373e3ffe0007f800000000001f00e070f800004fe0001f00e0007cfff80010fe000,
0x3ffffffffffffffffffffffff00000000000000000000fffffffffffffffffc0000000000000007ff8007ff8000000000000000000007f8000007ffffff00e07c03ffe04fe001f00e0001f3ffe0010fe00001c3e000001c19541ddf9fe9cfcc893ddf00000000000000000000050150ab1c020103b40000000003383383383383383383383383383383383383fc00000000000f80703e01fff027f000f8070000f9fff00087f00000e1f00000,
0x3ffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000007fffff8007ff8000000000000000000000007ffffffff00001fff007ffc0000700001fff00001fc000001f0000001fc00000008180008899008cdcc03bb60800000004100000044f60000000000000000000000000003c03c03c03c03c03c03c03c03c03c03c03c000000000380000fff803ffe0000380000fff80000fe000000f8000000fe000000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def inputs := rawInputs.map canon

end P2828Check
namespace P2828Check
variable {α : Type}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev basicOps (a b : W) := (ops a b).toFinset
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def differs (i : Fin 689) (w : W) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (689+i.val)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem neg_differs (i : Fin 689) (w : W) : differs i (neg w) ↔ differs i w := by
  have lo : i.val < 1378 := by omega
  have hi : 689+i.val < 1378 := by omega
  simp [neg, differs, hi, lo]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canon_differs (i : Fin 689) (w : W) : differs i (canon w) ↔ differs i w := by
  unfold canon
  split <;> simp [neg_differs]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem goal_differs (i : Fin 689) : differs i goal := by
  rw [goal, canon_differs]
  unfold differs
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [i.isLt, show ¬689 + i.val < 689 by omega]
  exact BitVec.getElem_allOnes _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cuts_spec (ws : List W) (i : Fin 689) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    simp [sep, i.isLt, differs]

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, both, BitVec.and_comm]
  grind [BitVec.and_comm]

end P2828Check

namespace P2828Check

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def keepChoices (a b : W) (r : List W) := [r, a::r, b::r, a::b::r]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def bit (k : Fin 1378) (z : W) := z[k.val]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canon_neg (x : W) : canon (~~~x) = canon x := by
  unfold canon neg
  simp only [BitVec.getLsbD_not, BitVec.not_not]
  cases h : x.getLsbD 0 <;> simp [h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sign (x : W) : x = canon x ∨ x = neg (canon x) := by
  unfold canon neg
  split <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signed_both {x y a b : W} (hx : x = a ∨ x = neg a) (hy : y = b ∨ y = neg b) :
    canon (x &&& y) ∈ basicOps a b := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp [basicOps, ops, both]

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def represents (available : Finset W) (w : List W) :=
  ∀ u ∈ w, canon u = 0 ∨ canon u ∈ available

set_option maxRecDepth 100000 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def assignment (k : Fin 1378) (i : Fin 9) := bit k (rawInputs.getD i.val 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : P2828Live.live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 689) := [0, 32, 64, 96, 128, 150, 182, 204, 226]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      (b.getLsbD i.val == b.getLsbD (689+i.val)) || b == a))) = true := by decide
  obtain ⟨i,_,hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hrow
    exact hrow.resolve_left hd
  obtain ⟨b,hb,hd⟩ := P2828Live.live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def good (P : Set (Wire Y)) (av : Finset W) : Prop :=
  ∀ f ∈ P, ∃ u : W, (canon u = 0 ∨ canon u ∈ av) ∧ ∀ r, f (assignment r) = bit r u

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signedBuild {P : Set (Wire Y)} {k : ℕ} (h : ThetaSigned.Run P k nine) :
    ∀ av, good P av → P2828Live.build basicOps goal k av := by
  generalize eqF : nine = f at h
  induction h with
  | @done P k f hf =>
    subst f
    intro av rep
    obtain ⟨u,hu,huv⟩ := rep _ hf
    have eq : u = ((-1 : BitVec 689) ++ (0 : BitVec 689)) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      exact ((huv ⟨i,hi⟩).symm.trans (graph_rows ⟨i,hi⟩))
    rw [eq] at hu
    have ing : goal ∈ av := hu.resolve_left (by decide)
    induction k with
    | zero => exact ing
    | succ k ih => exact Or.inl ih
  | @gate P k f a b op ha hb tail ih =>
    intro av rep
    obtain ⟨u,ru,eu⟩ := rep _ ha
    obtain ⟨v,rv,ev⟩ := rep _ hb
    let z := if op then u ||| v else u &&& v
    have hbits (r) : ThetaSigned.bin op a b (assignment r) = bit r z := by
      cases op <;> simp [z,ThetaSigned.bin,eu,ev,bit]
    have add {av' : Finset W} (sub : av ⊆ av') (has : canon z=0 ∨ canon z ∈ av') :
        good (plus P (ThetaSigned.bin op a b)) av' := by
      rintro g (old|rfl|rfl)
      · obtain ⟨w,hw,e⟩ := rep g old
        exact ⟨w,hw.imp_right (fun h => sub h),e⟩
      · exact ⟨_,has,hbits⟩
      · refine ⟨~~~z,by simpa only [canon_neg] using has,?_⟩
        intro r
        simp [ThetaSigned.inv,hbits,bit]
    have hws : represents av [u,v] := by
      intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl <;> assumption
    have hz : possible [u,v] z := by
      have hh := pair (ws:=[u,v]) (Or.inr (List.mem_cons_self ..) : u=0 ∨ u∈[u,v])
        (Or.inr (by simp) : v=0 ∨ v∈[u,v])
      cases op <;> first | exact hh.1 | exact hh.2
    rcases classify hws hz with hz|hz|⟨a',ha',b',hb',ne,mem⟩
    · exact Or.inl (ih eqF av (add (fun _ h=>h) (Or.inl hz)))
    · exact Or.inl (ih eqF av (add (fun _ h=>h) (Or.inr hz)))
    · exact Or.inr ⟨a',ha',b',hb',ne,_,mem,ih eqF _ (add (Finset.subset_insert ..) (Or.inr (Finset.mem_insert_self ..)))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem initialGood : good small inputs.toFinset := by
  rintro f (⟨b,rfl⟩|⟨i,rfl|rfl⟩)
  · cases b
    · exact ⟨0,Or.inl (by decide),by simp [ThetaSigned.bit,bit]⟩
    · exact ⟨-1,Or.inl (by decide),by intro r; exact (BitVec.getElem_allOnes r.val r.isLt).symm⟩
  · refine ⟨_,Or.inr ?_,fun _=>rfl⟩
    change canon (rawInputs.getD i.val 0) ∈ inputs.toFinset
    fin_cases i <;> decide +kernel
  · refine ⟨~~~(rawInputs.getD i.val 0),Or.inr ?_,?_⟩
    · rw [canon_neg]
      fin_cases i <;> decide +kernel
    · intro r; simp [assignment,ThetaSigned.inv,bit]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inputLive {k} (h : ThetaSigned.Run small k nine) : P2828Live.live basicOps goal k inputs.toFinset := by
  obtain ⟨s,hs,hl⟩ := P2828Live.compress (signedBuild h _ initialGood)
  exact (full_inputs hs hl) ▸ hl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rawOps (a b : W) := [both a b, both a (neg b), both (neg a) b, both (neg a) (neg b)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sep_canon (x : W) : sep (canon x) = sep x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h (v : W) : (sep v)[i] = true ↔ differs ⟨i,hi⟩ v := by
    change (sep v).getLsbD i = true ↔ _
    simp [sep, hi, differs]
  have eq := (h (canon x)).trans ((canon_differs ⟨i,hi⟩ x).trans (h x).symm)
  exact Bool.eq_iff_iff.mpr eq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (rawOps a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (canon w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra-1) (canon w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra-1) (canon w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra-2) (canon w :: a :: b :: r))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a,b,r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
open ThetaSigned PEqualNP.MetaComplexity ImportedHelpers
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev cornerGate (g : BinaryGate) := ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def literals (n : Nat) : Set (Wire (Fin n → Bool)) :=
  {f | (∃ c, f=bit c) ∨ ∃ i : Fin n, f=(fun x => x i) ∨ f=inv (fun x => x i)}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem literals_closed (n : Nat) : Closed (literals n) := by
  constructor
  · exact fun b => Or.inl ⟨b,rfl⟩
  · intro f hf
    rcases hf with ⟨b,rfl⟩|⟨i,rfl|rfl⟩
    · exact Or.inl ⟨!b,rfl⟩
    · exact Or.inr ⟨i,Or.inr rfl⟩
    · exact Or.inr ⟨i,Or.inl (inv_inv _)⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def step (w : List Bool) (g : BinaryGate) := w ++ [g.op (w.getD g.left false) (w.getD g.right false)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sign {X : Type} (a : Bool) (f : Wire X) : Wire X := fun x => f x == a
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signs {X : Type} {P : Set (Wire X)} (hp : Closed P) {f} (hf : f ∈ P) (s : Bool) : sign s f ∈ P := by
  cases s
  · exact hp.2 f hf
  · have e : sign true f = f := funext fun x => by cases h : f x <;> simp [sign,h]
    exact e ▸ hf
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gated {X : Type} (gs : List BinaryGate) (out : Nat) (p : Bool)
    (ok : ∀ g ∈ gs, cornerGate g) :
    ∀ (w : X → List Bool) (m : Nat), (∀ x, (w x).length=m) → ∀ P : Set (Wire X),
    Closed P → (∀ i, (fun x => (w x).getD i false) ∈ P) →
    Run P gs.length (fun x => ((gs.foldl step (w x)).getD out false) != p) := by
  induction gs with
  | nil =>
    intro w m len P closed reads
    apply Run.done
    cases p
    · simpa using reads out
    · exact closed.2 _ (reads out)
  | cons g gs ih =>
    intro w m len P closed reads
    obtain ⟨a,b,eq⟩ := ok g (by simp)
    let left : Wire X := fun x => (w x).getD g.left false
    let right : Wire X := fun x => (w x).getD g.right false
    let f := bin false (sign a left) (sign b right)
    have next (x : X) : step (w x) g = w x ++ [f x] := by simp [step,f,bin,sign,left,right,eq]
    apply Run.gate false (signs closed (reads g.left) a) (signs closed (reads g.right) b)
    apply ih (fun t h => ok t (by simp [h])) (fun x => step (w x) g) (m+1)
      (fun x => by simp [next,len]) (plus P f) (plus_closed closed f)
    intro i
    by_cases hit : i=m
    · have hn : (fun x => (step (w x) g).getD i false) = f := by
        funext x
        rw [next,hit,←len x,getD_snoc_eq]
      exact Or.inr (Or.inl hn)
    · have hn : (fun x => (step (w x) g).getD i false) = (fun x => (w x).getD i false) := by
        funext x
        rw [next,getD_snoc_ne _ _ _ _ (by rw [len x];exact hit)]
      exact Or.inl (hn ▸ reads i)
end SignedCofactor

namespace P2828Generic
open P2828Check P2828Live ThetaSigned
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def wordBit (r : Fin 1378) (w : W) := w[r.val]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def representsPool {T} (pick : Fin 1378 → T) (P : Set (Wire T)) (S : Finset W) :=
  ∀ f ∈ P, ∃ w, (canon w=0 ∨ canon w ∈ S) ∧ ∀ r, f (pick r)=wordBit r w
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def possibleIn (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem singletonPossible {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possibleIn ws x ∧ possibleIn ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possibleIn]
  · simp only [possibleIn, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def columnPick {n : Nat} (cols : List W) (r : Fin 1378) (i : Fin n) := wordBit r (cols.getD i.val 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def signals (cols : List W) := cols.map canon
set_option maxRecDepth 100000 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def critical (ws : List W) (sites : List (Fin 689)) : Bool :=
  ws.all fun a => sites.any fun i => ws.all fun b => (b.getLsbD i.val == b.getLsbD (689+i.val)) || b == a
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_required {ws : List W} {sites} {k s} (crit : critical ws sites=true)
    (hs : s⊆ws.toFinset) (hr : live basicOps goal k s) : s=ws.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  obtain ⟨i,_,all⟩ := List.any_eq_true.mp (List.all_eq_true.mp crit a (List.mem_toFinset.mp ha))
  obtain ⟨b,hb,hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) hr
  have eq := List.all_eq_true.mp all _ (List.mem_toFinset.mp (hs hb))
  simp only [Bool.or_eq_true,beq_iff_eq] at eq
  exact eq.resolve_left hd ▸ hb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeFunc {n} (es : List (Fin n × Fin n)) (x : Fin n → Bool) := es.any fun e => x e.1 && x e.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeWord {n} (es : List (Fin n × Fin n)) (cols : List W) : W :=
  es.foldr (fun e out => ((cols.getD e.1.val 0) &&& (cols.getD e.2.val 0)) ||| out) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem edgeRows {n} (es : List (Fin n × Fin n)) (cols : List W) (r : Fin 1378) :
    edgeFunc es (columnPick cols r) = wordBit r (edgeWord es cols) := by
  induction es with
  | nil => simp [edgeFunc,edgeWord,wordBit]
  | cons e t ih =>
    change (columnPick cols r e.1 && columnPick cols r e.2 || edgeFunc t (columnPick cols r)) =
      wordBit r (((cols.getD e.1.val 0) &&& (cols.getD e.2.val 0)) ||| edgeWord t cols)
    simp only [ih,columnPick,wordBit,BitVec.getElem_or,BitVec.getElem_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem graph_lower {n cap extra k : Nat} (es : List (Fin n × Fin n)) (cols : List W) (sites : List (Fin 689))
    (len : cols.length=n) (ok : edgeWord es cols=goal) (crit : critical (signals cols) sites=true)
    (nodup : (signals cols).Nodup) (room : extra+(signals cols).length=cap+1)
    (scan : optimized cap extra (signals cols) = false)
    (run : Run (SignedCofactor.literals n) k (edgeFunc es)) : cap+1 ≤ k := by
  by_contra! small
  have agrees (r : Fin 1378) : edgeFunc es (columnPick cols r) = wordBit r goal := by rw [edgeRows,ok]
  obtain ⟨s,hs,hr⟩ := compress (anyBuild _ agrees run _ (columnGood cols len))
  rw [all_required crit hs hr] at hr
  have enough (t : Nat) (le : k≤t) : live basicOps goal t (signals cols).toFinset := by
    induction le with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  have yes := optimized_complete cap (signals cols) extra nodup room (enough cap (by omega))
  rw [scan] at yes
  contradiction
end P2828Generic

namespace P2828Live
variable {α β : Type} [DecidableEq α] [DecidableEq β]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def kept (p : α → Option β) (s : Finset α) : Finset β := s.biUnion (fun a => (p a).toFinset)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def zeros (p : α → Option β) (s : Finset α) : ℕ :=
  (s.filter (fun a => p a = none)).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kept_insert (p : α → Option β) (a : α) (s : Finset α) :
    kept p (insert a s) = (p a).toFinset ∪ kept p s := by
  simp [kept]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeros_some {p : α → Option β} {a : α} {v : β} (h : p a = some v) (s : Finset α) :
    zeros p (insert a s) = zeros p s := by simp [zeros, Finset.filter_insert, h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeros_none {p : α → Option β} {a : α} (h : p a = none) {s : Finset α} (ha : a ∉ s) :
    zeros p (insert a s) = zeros p s + 1 := by simp [zeros, Finset.filter_insert, h, ha]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeros_le (p : α → Option β) (a : α) (s : Finset α) :
    zeros p (insert a s) ≤ zeros p s + 1 := by
  cases h : p a with
  | some v => rw [zeros_some h]; omega
  | none =>
    by_cases hm : a ∈ s
    · rw [Finset.insert_eq_of_mem hm]; omega
    · exact (zeros_none h hm).le

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeros_mono (p : α → Option β) {s t : Finset α} (h : s ⊆ t) :
    zeros p s ≤ zeros p t := Finset.card_le_card (Finset.filter_subset_filter _ h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem build_mono {ops : β → β → Finset β} {goal : β} {k : ℕ} {s t : Finset β}
    (hs : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hs h
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,tail⟩
    · exact .inl (ih hs skip)
    · exact .inr ⟨a,hs ha,b,hs hb,hab,z,hz,ih (Finset.insert_subset_insert _ hs) tail⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def projects (p : α → Option β) (ops : α → α → Finset α) (ops' : β → β → Finset β) : Prop :=
  ∀ a b z, z ∈ ops a b → ∀ v, p z = some v →
    p a = some v ∨ p b = some v ∨
    ∃ u w, p a = some u ∧ p b = some w ∧ u ≠ w ∧ v ∈ ops' u w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeros_budget {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) : zeros p s ≤ k := by
  induction k generalizing s with
  | zero => change s = {g} at h; simp [h, zeros, hg]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact (ih skip).trans (by omega)
    · exact (zeros_step P hz r hn).trans (Nat.succ_le_succ (ih tail))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def crop (m : W) (r : Fin 1378) (x : W) : W :=
  (x &&& m) ||| (if x[r.val] then ~~~m else 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pos (m : W) (r : Fin 1378) (i : Nat) := if m.getLsbD i then i else r.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pos_lt (m : W) (r : Fin 1378) {i} (hi : i < 1378) : pos m r i < 1378 := by
  unfold pos; split <;> omega
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crop_bit (m : W) (r : Fin 1378) (x : W) (i : Nat) (hi : i < 1378) :
    (crop m r x).getLsbD i = x.getLsbD (pos m r i) := by
  unfold crop pos
  rw [BitVec.getLsbD_eq_getElem hi (x := m)]
  cases hr : x[r.val] <;> cases hm : m[i] <;> simp [hr,hm,hi]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crop_and (m : W) (r : Fin 1378) (x y : W) :
    crop m r (x &&& y) = crop m r x &&& crop m r y := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (x &&& y)).getLsbD j = (crop m r x &&& crop m r y).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crop_neg (m : W) (r : Fin 1378) (x : W) :
    crop m r (~~~x) = ~~~crop m r x := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (~~~x)).getLsbD j = (~~~crop m r x).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_not, h, pos_lt _ _ h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def wrap (x : W) : Option W := if canon x = 0 then none else some (canon x)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wrap_neg (x : W) : wrap (~~~x) = wrap x := by simp only [wrap, canon_neg]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cropOpt (m : W) (r : Fin 1378) (x : W) := wrap (crop m r x)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crop_canon (m : W) (r : Fin 1378) (x : W) :
    cropOpt m r (canon x) = cropOpt m r x := by
  unfold canon
  split
  · simp only [cropOpt, neg, crop_neg, wrap_neg]
  · rfl

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask_projects (m : W) (r : Fin 1378) : P2828Live.projects (cropOpt m r) basicOps basicOps := by
  intro a b z hz v hv
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [crop_canon] at hv <;> simp only [cropOpt, both, neg, crop_and, crop_neg] at hv ⊢ <;>
    simpa only [wrap_neg] using binary_project hv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def projectedBudget (m : W) (r : Fin 1378) (n : Nat) (ws : List W) : Nat :=
  n - (ws.filter (fun w => (cropOpt m r w).isNone)).length

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def available (m : W) (r : Fin 1378) (ws : List W) : List W :=
  (ws.filterMap (cropOpt m r)).dedup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem available_spec (m : W) (r : Fin 1378) (ws : List W) :
    (available m r ws).toFinset = P2828Live.kept (cropOpt m r) ws.toFinset := by
  ext y; simp [available, P2828Live.kept, List.mem_filterMap]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem face_build (m : W) (r : Fin 1378) {g : W} (hg : cropOpt m r goal = some g)
    {k : ℕ} {ws : List W} (hn : ws.Nodup) (h : P2828Live.live basicOps goal k ws.toFinset) :
    P2828Live.build basicOps g (projectedBudget m r k ws) (available m r ws).toFinset := by
  rw [available_spec]
  exact P2828Live.project_live hg (mask_projects m r) h _ (projected_bound m r k hn)
end P2828Check

namespace P2828Check
open ThetaSigned
variable {T : Type}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def interpret (pick : T → Fin 1378) (w : W) : Wire T := fun x => w.getLsbD (pick x).val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem interpret_neg (pick : T → Fin 1378) (w : W) : interpret pick (neg w) = inv (interpret pick w) := by
  funext x
  simp [neg,interpret,inv,(pick x).isLt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem interpret_canon (pick : T → Fin 1378) (w : W) :
    interpret pick (canon w) = interpret pick w ∨ interpret pick (canon w) = inv (interpret pick w) := by
  unfold canon; split
  · exact Or.inr (interpret_neg _ _)
  · exact Or.inl rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem interpret_both (pick : T → Fin 1378) (a b : W) :
    interpret pick (both a b) = bin false (interpret pick a) (interpret pick b) := by
  funext x;simp [interpret,both,bin]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run_pad {P : Set (Wire T)} {k f} (h : Run P k f) : Run P (k+1) f := by
  induction h with
  | done hf => exact .done hf
  | gate op ha hb _ ih => exact .gate op ha hb ih

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run_inv {P : Set (Wire T)} {k f} (h : Run P k f) (hc : Closed P) : Run P k (inv f) := by
  induction h with
  | done hf => exact .done (hc.2 _ hf)
  | gate op ha hb _ ih => exact .gate op ha hb (ih (plus_closed hc _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
inductive History (ops : α → α → Finset α) (start : Finset α) : Finset α → Prop where
  | initial : History ops start start
  | gate {s} (old : History ops start s) {a b z} (ha : a ∈ s) (hb : b ∈ s)
      (hz : z ∈ ops a b) : History ops start (insert z s)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem History.contains {ops : α → α → Finset α} {start s} (h : History ops start s) : start ⊆ s := by
  induction h with
  | initial => exact Finset.Subset.refl _
  | gate old ha hb hz ih => exact ih.trans (Finset.subset_insert _ _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kept_mono (p : α → Option β) {s t : Finset α} (h : s ⊆ t) : kept p s ⊆ kept p t := by
  intro v hv
  obtain ⟨x,hx,px⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨x,h hx,px⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kept_of {p : α → Option β} {s : Finset α} {a : α} {v : β} (ha : a ∈ s) (hp : p a = some v) :
    v ∈ kept p s := Finset.mem_biUnion.mpr ⟨a,ha,by simp [hp]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def price (p : α → Option β) (start s : Finset α) := (kept p s \ kept p start).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def rowMap : Array (Fin 1378) := #[402, 32, 0, 689, 33, 34, 722, 723, 65, 35, 1, 690, 754, 755, 756, 1092, 2, 691, 3, 692, 4, 693, 725, 1093, 787, 820, 788, 1094, 789, 1095, 1096, 1097, 5, 694, 6, 695, 7, 696, 726, 1098, 8, 697, 9, 698, 759, 1099, 760, 1100, 10, 699, 11, 700, 12, 701, 727, 1101, 791, 1102, 792, 1103, 793, 1104, 1105, 1106, 39, 40, 728, 729, 41, 42, 730, 731, 43, 44, 732, 733, 762, 763, 1107, 1108, 13, 702, 734, 1109, 14, 703, 735, 1110, 796, 827, 1111, 1112, 797, 1113, 1114, 1115, 15, 704, 736, 1116, 16, 705, 737, 1117, 17, 706, 738, 1118, 764, 1119, 1120, 1121, 18, 707, 739, 1122, 19, 708, 740, 1123, 799, 1124, 1125, 1126, 800, 1127, 1128, 1129, 76, 52, 20, 709, 765, 766, 767, 1130, 79, 53, 21, 710, 768, 769, 770, 1131, 22, 711, 23, 712, 771, 1132, 772, 1133, 801, 831, 802, 1134, 1135, 1136, 1137, 1138, 845, 846, 847, 1139, 898, 1140, 1141, 1142, 848, 849, 850, 1143, 1144, 1145, 1146, 1147, 851, 1148, 852, 1149, 903, 1150, 1151, 1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 54, 55, 743, 744, 773, 774, 1161, 1162, 56, 57, 745, 746, 775, 776, 1163, 1164, 24, 713, 747, 1165, 777, 1166, 1167, 1168, 803, 835, 1169, 1170, 1171, 1172, 1173, 1174, 853, 854, 1175, 1176, 908, 1177, 1178, 1179, 855, 856, 1180, 1181, 1182, 1183, 1184, 1185, 857, 1186, 1187, 1188, 911, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 115, 59, 25, 714, 60, 61, 749, 750, 804, 805, 806, 1200, 807, 808, 1201, 1202, 26, 715, 27, 716, 28, 717, 751, 1203, 809, 1204, 810, 1205, 811, 1206, 1207, 1208, 858, 859, 860, 1209, 861, 862, 1210, 1211, 921, 1212, 922, 1213, 1214, 1215, 1216, 1217, 863, 1218, 864, 1219, 865, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 880, 881, 882, 1231, 883, 884, 1232, 1233, 930, 931, 1234, 1235, 1236, 1237, 1238, 1239, 885, 1240, 886, 1241, 887, 1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249, 1250, 1251, 1252, 934, 1253, 1254, 1255, 935, 1256, 1257, 1258, 936, 1259, 1260, 1261, 1262, 1263, 1264, 1265, 937, 1266, 1267, 1268, 938, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279, 91, 63, 29, 718, 780, 781, 782, 1280, 812, 813, 814, 1281, 1282, 1283, 1284, 1285, 30, 719, 31, 720, 783, 1286, 784, 1287, 815, 1288, 816, 1289, 1290, 1291, 1292, 1293, 866, 867, 868, 1294, 1295, 1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 869, 1307, 870, 1308, 1309, 1310, 1311, 1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 888, 889, 890, 1321, 1322, 1323, 1324, 1325, 944, 945, 1326, 1327, 1328, 1329, 1330, 1331, 891, 1332, 892, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def bits (x : Y) : BitVec 9 := (BitVec.ofBoolListLE (List.ofFn x)).setWidth 9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bits_spec (x : Y) (i : Fin 9) : (bits x).getLsbD i.val = x i := by
  simp only [bits,BitVec.getLsbD_setWidth,decide_eq_true i.isLt,Bool.true_and,BitVec.getLsbD_ofBoolListLE]
  exact ImportedHelpers.getD_ofFn 9 x false i
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_ok : ∀ (v : Fin 512) (i : Fin 9),
  assignment (rowMap.getD v.val 0) i = (BitVec.ofNat 9 v.val).getLsbD i.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def chooseRow (x : Y) := rowMap.getD (bits x).toNat 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chooseRow_spec (x : Y) : assignment (chooseRow x)=x := by
  funext i
  have e := row_ok ⟨(bits x).toNat,(bits x).isLt⟩ i
  simpa only [chooseRow, BitVec.ofNat_toNat, BitVec.setWidth_eq, bits_spec] using e
end P2828Check

namespace P2828Check
open P2828 ThetaSigned P2828Live

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pin (fixed values : BitVec 9) (y : Y) : Y := fun i =>
  if fixed.getLsbD i.val then values.getLsbD i.val else y i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def faceMaskList (fixed values : BitVec 9) : List (Fin 9) → W
  | [] => BitVec.allOnes 1378
  | i :: is =>
    let rest := faceMaskList fixed values is
    let column := rawInputs.getD i.val 0
    if fixed.getLsbD i.val then
      (if values.getLsbD i.val then column else neg column) &&& rest
    else rest

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def faceMask (fixed values : BitVec 9) := faceMaskList fixed values (List.finRange 9)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pickFace (f v : BitVec 9) (y : Y) := chooseRow (pin f v y)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pickFace_row (f v : BitVec 9) (y : Y) : assignment (pickFace f v y) = pin f v y := chooseRow_spec _

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem interpret_crop (f v : BitVec 9) (r : Fin 1378) (w : W) :
    interpret (pickFace f v) (crop (faceMask f v) r w) = interpret (pickFace f v) w := by
  funext y
  simp only [interpret,crop_bit _ _ _ _ (pickFace f v y).isLt,pos,pickFace_inside,if_true]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem interpret_raw (f v : BitVec 9) (i : Fin 9) : interpret (pickFace f v) (rawInputs.getD i.val 0) ∈ small := by
  have eq : interpret (pickFace f v) (rawInputs.getD i.val 0) = fun y => pin f v y i := by
    funext y;exact congrFun (pickFace_row f v y) i
  rw [eq]
  unfold pin
  split
  · exact small_closed.1 _
  · exact Or.inr ⟨i,Or.inl rfl⟩

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem interpret_goal (f v : BitVec 9) : interpret (pickFace f v) goal = fun y => nine (pin f v y) := by
  have hg : goal = ((-1 : BitVec 689) ++ (0 : BitVec 689)) := by decide +kernel
  funext y
  have z := graph_rows (pickFace f v y)
  rw [pickFace_row] at z
  rw [hg]
  exact z.symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem face_run {f v : BitVec 9} {r : Fin 1378} {g : W} (hg : cropOpt (faceMask f v) r goal = some g)
    {hist s : Finset W} {k : ℕ} (past : History basicOps inputs.toFinset hist) (pool : s ⊆ hist)
    (run : live basicOps goal k s) :
    Run small (k - zeros (cropOpt (faceMask f v) r) s + price (cropOpt (faceMask f v) r) inputs.toFinset hist)
      (fun y => nine (pin f v y)) := by
  obtain h := face_budget (mask_projects _ _) past pool hg run
  have decoded := decode_build (pickFace f v) h small_closed (decoded_kept f v r)
  unfold cropOpt wrap at hg
  split at hg
  · contradiction
  obtain rfl := Option.some.inj hg
  rcases interpret_canon (pickFace f v) (crop (faceMask f v) r goal) with h|h <;>
    rw [h,interpret_crop,interpret_goal] at decoded
  · exact decoded
  · simpa only [inv_inv] using Run_inv decoded small_closed
end P2828Check

namespace P2828Check
open P2828 ThetaSigned P2828Live
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Face where
  fixed : BitVec 9
  values : BitVec 9
  lower : ℕ
  mask : W
  anchor : Fin 1378

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Face.Valid (c : Face) : Prop := c.mask = faceMask c.fixed c.values ∧
    (∃ g, cropOpt c.mask c.anchor goal = some g) ∧
    ∀ k, Run small k (fun y => nine (pin c.fixed c.values y)) → c.lower ≤ k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def allSeen (hist : List W) := hist.toFinset ∪ inputs.toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rejects (c : Face) (k : ℕ) (ws hist : List W) : Bool :=
  let p := cropOpt c.mask c.anchor
  decide (k - zeros p ws.toFinset + price p inputs.toFinset (allSeen hist) < c.lower)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rejects_false {c : Face} (valid : c.Valid) {k ws hist}
    (past : History basicOps inputs.toFinset (allSeen hist)) (pool : ws.toFinset ⊆ allSeen hist)
    (run : live basicOps goal k ws.toFinset) : rejects c k ws hist = false := by
  obtain ⟨em,⟨g,hg⟩,bound⟩ := valid
  rw [em] at hg
  have hr := bound _ (face_run hg past pool run)
  simp only [rejects,em,decide_eq_false_iff_not,not_lt]
  exact hr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev Advice := List W → List W → List Face

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def checkChild (ad : List Face) (further : ℕ → List W → List W → Bool) (k : ℕ)
    (ws hist : List W) (extra : ℕ) (child : List W) : Bool :=
  match child with
  | [] => false
  | z :: _ => !(ws.contains z) && !(ad.any (fun c => rejects c k child (z::hist))) &&
      further extra child (z::hist)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def guided (ad : Advice) : ℕ → ℕ → List W → List W → Bool
  | 0, _, ws, _ => ws == [goal]
  | k+1, extra, ws, hist => ws == [goal] ||
    let more := checkChild (ad ws hist) (guided ad k) k ws hist
    (pairs ws).any (fun (a,b,r) => dispatch extra more a b r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem guided_complete (ad : Advice) (valid : ∀ ws hist, ∀ c ∈ ad ws hist, c.Valid)
    (n : ℕ) (ws hist : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (past : History basicOps inputs.toFinset (allSeen hist))
    (pool : ws.toFinset ⊆ allSeen hist) (h : live basicOps goal n ws.toFinset) :
    guided ad n extra ws hist = true := by
  induction n generalizing ws hist extra with
  | zero => simp [guided,singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [guided,singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have seen : allSeen (z::hist) = insert z (allSeen hist) := by simp [allSeen]
      have extended : History basicOps inputs.toFinset (allSeen (z::hist)) := seen ▸ .gate past (pool ha) (pool hb) hz
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (checkChild (ad ws hist) (guided ad k) k ws hist) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have sub : kept.toFinset ⊆ ws.toFinset := by rw [hfin,hset];exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨fun hv => hout (sub (List.mem_toFinset.mpr hv)),hnk⟩
        have hl : live basicOps goal k (z::kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd,List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) _ hop hk (by omega) (by omega) (cuts_full hl)
        have pool' : (z::kept).toFinset ⊆ allSeen (z::hist) := by
          rw [seen,List.toFinset_cons]; exact Finset.insert_subset_insert _ (sub.trans pool)
        have succ := ih _ _ (k-kept.length) hnd (by simp;omega) extended pool' hl
        have none : (ad ws hist).any (fun c => rejects c k (z::kept) (z::hist)) = false :=
          List.any_eq_false.mpr fun c hc => by rw [rejects_false (valid _ _ c hc) extended pool' hl]; decide
        have fresh : z ∉ ws := by simpa using hout
        simp [checkChild,fresh,none,succ]
      simp only [guided,Bool.or_eq_true,List.any_eq_true]
      right
      rcases hm with direct|swap
      · exact ⟨(a,b,r),direct,go hp hs hz⟩
      · exact ⟨(b,a,r),swap,go (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
end P2828Check

namespace P2828Minor
open P2828Check P2828Live P2828Generic ThetaSigned

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Minor where
  lower : Nat
  mask : W
  anchor : Fin 1378

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Minor.Valid (c : Minor) (base : List W) : Prop :=
  ∃ g, cropOpt c.mask c.anchor goal = some g ∧
    ∀ k, build basicOps g k (kept (cropOpt c.mask c.anchor) base.toFinset) → c.lower ≤ k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def seen (base h : List W) := h.toFinset ∪ base.toFinset
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rejects (base : List W) (c : Minor) (k : ℕ) (ws hist : List W) : Bool :=
  let p := cropOpt c.mask c.anchor
  decide (k - zeros p ws.toFinset + price p base.toFinset (seen base hist) < c.lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem safe {base c k ws hist} (valid : Minor.Valid c base)
    (past : History basicOps base.toFinset (seen base hist)) (pool : ws.toFinset ⊆ seen base hist)
    (run : live basicOps goal k ws.toFinset) : rejects base c k ws hist = false := by
  obtain ⟨g,hg,lower⟩ := valid
  exact decide_eq_false (Nat.not_lt.mpr (lower _ (face_budget (mask_projects _ _) past pool hg run)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gone (p : W → Option W) (ws : List W) := (ws.filter fun w => (p w).isNone).length
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def paid (p : W → Option W) (ws : List W) (base : List W) :=
  ((ws.filterMap p).filter (fun z => !base.contains z)).dedup.length
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def quicker (c : Face) (k : ℕ) (ws hist : List W) : Bool :=
  let p := cropOpt c.mask c.anchor
  let rem := k - gone p ws
  if c.lower ≤ rem then false else
    decide (rem + paid p hist (inputs.filterMap p) < c.lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gone_eq (p : W → Option W) {ws : List W} (hn : ws.Nodup) : gone p ws = zeros p ws.toFinset := by
  unfold gone zeros
  rw [← List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist ..))]
  congr 1
  ext a
  simp [Option.isNone_iff_eq_none]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem kept_list (p : W → Option W) (ws : List W) :
    kept p ws.toFinset = (ws.filterMap p).toFinset := by
  ext a; simp [kept,List.mem_filterMap]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem paid_eq (p : W → Option W) (hist : List W) :
    paid p hist (inputs.filterMap p) = price p inputs.toFinset (allSeen hist) := by
  let h := (hist.filterMap p).filter fun z => !(inputs.filterMap p).contains z
  change h.dedup.length = _
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup _),List.toFinset_dedup]
  unfold price allSeen
  rw [show kept p (hist.toFinset ∪ inputs.toFinset) = kept p hist.toFinset ∪ kept p inputs.toFinset by
    ext a; simp [kept, or_and_right, exists_or]]
  rw [kept_list,kept_list]
  congr 1
  ext a
  simp [h]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem quicker_eq (c : Face) (k : Nat) (ws hist : List W) (hn : ws.Nodup) :
    quicker c k ws hist = rejects c k ws hist := by
  simp only [quicker,rejects,gone_eq _ hn,paid_eq]
  split
  · symm;apply decide_eq_false
    omega
  · rfl
end P2828Check

namespace P2828Check
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def limited (m : W) (r : Fin 1378) (w : W) : W := (if w[r.val] then ~~~w else w) &&& m
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem limited_anchor (m : W) (r : Fin 1378) (w : W) : (limited m r w)[r.val] = false := by
  cases e : w[r.val] <;> simp [limited,e]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 100000 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def projectFast (m : W) (r : Fin 1378) (w : W) : Option W :=
  let q := limited m r w
  if q=0 then none else some (canon q)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem projectFast_eq (m : W) (r : Fin 1378) : projectFast m r = cropOpt m r := by
  funext w
  simp only [projectFast,cropOpt,wrap,limited_crop,limited_zero]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def maskedReject (c : Face) (k : Nat) (ws hist : List W) : Bool :=
  let p := projectFast c.mask c.anchor
  let rem := k - (ws.filter (fun w => limited c.mask c.anchor w == 0)).length
  if c.lower ≤ rem then false else
    decide (rem + paid p hist (inputs.filterMap p) < c.lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem masked_eq (c : Face) (k : Nat) (ws hist : List W) (hn : ws.Nodup) :
    maskedReject c k ws hist = rejects c k ws hist := by
  rw [← quicker_eq _ _ _ _ hn]
  unfold maskedReject quicker gone
  rw [←projectFast_eq]
  have columns (w : W) : (projectFast c.mask c.anchor w).isNone = (limited c.mask c.anchor w == 0) := by
    let z := limited c.mask c.anchor w
    change (if z=0 then none else some (canon z)).isNone = (z == 0)
    by_cases hz : z=0
    · rw [if_pos hz,hz];rfl
    · rw [if_neg hz];exact (beq_eq_false_iff_ne.mpr hz).symm
  simp only [columns]
end P2828Check

namespace P2828Minor
open P2828Check P2828Live
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem kept_list (p : W → Option W) (ws : List W) :
    kept p ws.toFinset = (ws.filterMap p).toFinset := by
  ext a; simp [kept,List.mem_filterMap]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cheap (base : List W) (c : Minor) (k : Nat) (ws hist : List W) : Bool :=
  let p := projectFast c.mask c.anchor
  let rem := k - (ws.filter (fun w => limited c.mask c.anchor w == 0)).length
  if c.lower ≤ rem then false else
    decide (rem + paid p hist (base.filterMap p) < c.lower)

set_option maxRecDepth 100000 in
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

namespace P2828Check
open P2828Live
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev Site := Fin 689
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low (u : W) (i : Site) := u.getLsbD i.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def high (u : W) (i : Site) := u.getLsbD (689+i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Sole (s : Finset W) (a : W) (i : Site) : Prop := ∀ w ∈ s, differs i w → w=a
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Opposite (s : Finset W) : Prop :=
  ∃ a ∈ s, ∃ i j : Site, Sole s a i ∧ Sole s a j ∧ low a i ≠ low a j
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem canon_bit (x : W) (i : Nat) (h : i<1378) :
    (canon x).getLsbD i = (x.getLsbD i != x.getLsbD 0) := by
  unfold canon
  cases e : x.getLsbD 0 <;> simp only [Bool.false_eq_true,if_false,if_true,Bool.bne_false,Bool.bne_true,neg,BitVec.getLsbD_not,h,decide_true,Bool.true_and]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem op_gives {a b z : W} (h : z ∈ basicOps a b) :
    ∃ p q r : Bool, ∀ i : Nat, i < 1378 →
      z.getLsbD i = (((a.getLsbD i != p) && (b.getLsbD i != q)) != r) := by
  simp [basicOps,ops] at h
  rcases h with rfl|rfl|rfl|rfl
  · refine ⟨false,false,(both a b).getLsbD 0,fun i hi => ?_⟩
    rw [canon_bit _ _ hi]; simp [both]
  · refine ⟨false,true,(both a (neg b)).getLsbD 0,fun i hi => ?_⟩
    rw [canon_bit _ _ hi]; simp [both,neg,hi]
  · refine ⟨true,false,(both (neg a) b).getLsbD 0,fun i hi => ?_⟩
    rw [canon_bit _ _ hi]; simp [both,neg,hi]
  · refine ⟨true,true,(both (neg a) (neg b)).getLsbD 0,fun i hi => ?_⟩
    rw [canon_bit _ _ hi]; simp [both,neg,hi]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem corner_dir :
    ∀ a a' c c' b d p q r : Bool,
    let g := fun (x y : Bool) => (((x != p) && (y != q)) != r)
    g a b ≠ g a' b → g c d ≠ g c' d → a≠c → g a b≠g c d := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem transmit {a b z : W} (op : z ∈ basicOps a b) {i j : Site}
    (bi : ¬differs i b) (bj : ¬differs j b) (zi : differs i z) (zj : differs j z)
    (opposed : low a i ≠ low a j) : low z i ≠ low z j := by
  obtain ⟨p,q,r,eq⟩ := op_gives op
  have bi' : low b i = high b i := not_ne_iff.mp bi
  have bj' : low b j = high b j := not_ne_iff.mp bj
  have e0 (t : Site) : low z t = (((low a t != p) && (low b t != q)) != r) := eq _ (by omega)
  have e1 (t : Site) : high z t = (((high a t != p) && (high b t != q)) != r) := eq _ (by omega)
  change low z i ≠ high z i at zi
  change low z j ≠ high z j at zj
  rw [e0,e1,←bi'] at zi
  rw [e0,e1,←bj'] at zj
  rw [e0,e0]
  exact corner_dir _ _ _ _ _ _ p q r zi zj opposed

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tight_unate {k : Nat} {s : Finset W} (run : live basicOps goal k s)
    (tight : s.card = k+1) : ¬Opposite s := by
  induction k generalizing s with
  | zero =>
    change s={goal} at run
    rintro ⟨a,ha,i,j,_,_,op⟩
    obtain rfl := Finset.mem_singleton.mp (run ▸ ha : a ∈ {goal})
    have const (t : Site) : low goal t = false := by
      have hg : goal = ((-1 : BitVec 689) ++ (0 : BitVec 689)) := by decide
      rw [low,hg,BitVec.getLsbD_append]
      simp [t.isLt]
    exact op ((const _).trans (const _).symm)
  | succ k ih =>
    rcases run with skip|⟨x,hx,y,hy,hxy,z,hz,out,rest,rfl,tail⟩
    · have c := live_card skip
      omega
    · have zr : z ∉ rest := fun h => out (by simp [h])
      have bound := live_card tail
      rw [Finset.card_insert_of_notMem zr] at bound
      have h₁ := Finset.card_insert_le x (insert y rest)
      have h₂ := Finset.card_insert_le y rest
      have xr : x ∉ rest := by
        intro h
        have e := Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : x ∈ insert y rest)
        rw [e] at tight
        omega
      have yr : y ∉ rest := by
        intro h
        rw [Finset.insert_eq_of_mem h] at tight
        have := Finset.card_insert_le x rest
        omega
      have tc : (insert z rest).card = k+1 := by rw [Finset.card_insert_of_notMem zr]; omega
      intro bad
      obtain ⟨a,ha,i,j,si,sj,opp⟩ := bad
      apply ih tail tc
      have advance (h : a ∉ rest) (t : Site) (only : Sole (insert x (insert y rest)) a t) :
          Sole (insert z rest) z t := by
        rintro w hw diff
        rcases Finset.mem_insert.mp hw with rfl|old
        · rfl
        · exact False.elim (h (only w (by simp [old]) diff ▸ old))
      have carry (h : a ≠ x ∧ a ≠ y) (t : Site) (only : Sole (insert x (insert y rest)) a t) :
          Sole (insert z rest) a t := by
        intro w hw diff
        rcases Finset.mem_insert.mp hw with rfl|old
        · rcases ops_differs t x y w hz diff with dx|dy
          · exact ((h.1 (only x (by simp) dx).symm).elim)
          · exact ((h.2 (only y (by simp) dy).symm).elim)
        · exact only w (by simp [old]) diff
      have getDiff (t : Site) (sole : Sole (insert z rest) z t) : differs t z := by
        obtain ⟨w,hw,d⟩ := live_separates (differs t) (goal_differs t) (ops_differs t) tail
        exact sole _ hw d ▸ d
      rcases Finset.mem_insert.mp ha with rfl|ha
      · have ni := advance xr i si
        have nj := advance xr j sj
        exact ⟨z,by simp,i,j,ni,nj,transmit hz (fun h => hxy (si y (by simp) h).symm)
          (fun h => hxy (sj y (by simp) h).symm) (getDiff _ ni) (getDiff _ nj) opp⟩
      · rcases Finset.mem_insert.mp ha with rfl|ha
        · have ni := advance yr i si
          have nj := advance yr j sj
          rw [ops_swap] at hz
          exact ⟨z,by simp,i,j,ni,nj,transmit hz (fun h => hxy (si x (by simp) h))
            (fun h => hxy (sj x (by simp) h)) (getDiff _ ni) (getDiff _ nj) opp⟩
        · have ne : a ≠ x ∧ a ≠ y := ⟨fun e => xr (e ▸ ha),fun e => yr (e ▸ ha)⟩
          exact ⟨a,by simp [ha],i,j,carry ne i si,carry ne j sj,opp⟩
end P2828Check

namespace P2828Check
open P2828Live
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def directionBad (ws : List W) (a : W) : Bool :=
  let missing := ~~~(cuts (ws.filter (· != a)))
  let column := a.setWidth 689
  (missing &&& column != 0) && (missing &&& ~~~column != 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def unateBad (ws : List W) := ws.any (directionBad ws)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem nonzero_site (x : BitVec 689) (h : x ≠ 0) :
    ∃ i : Site, x.getLsbD i.val = true := by
  by_contra! all
  apply h
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have b := all ⟨j,hj⟩
  change x[j] = (0#689)[j]
  rw [BitVec.getElem_zero]
  simpa only [BitVec.getLsbD_eq_getElem hj] using (Bool.eq_false_iff.mpr b)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem direction_witness {ws a} (mem : a ∈ ws) (bad : directionBad ws a = true) :
    Opposite ws.toFinset := by
  let rest := ws.filter (· != a)
  let v := cuts rest
  let b := a.setWidth 689
  change ((~~~v &&& b != 0) && (~~~v &&& ~~~b != 0)) = true at bad
  simp only [Bool.and_eq_true,bne_iff_ne] at bad
  obtain ⟨i,hi⟩ := nonzero_site _ bad.1
  obtain ⟨j,hj⟩ := nonzero_site _ bad.2
  have facts (t : Site) : b.getLsbD t.val = low a t := by simp [b,low,t.isLt]
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,j.isLt,decide_true,Bool.true_and,
    Bool.and_eq_true,Bool.not_eq_true',facts] at hi hj
  have only (t : Site) (missing : v.getLsbD t.val=false) : Sole ws.toFinset a t := by
    intro w hw hd
    by_contra ne
    have present : w ∈ rest := List.mem_filter.mpr ⟨List.mem_toFinset.mp hw,by simpa using ne⟩
    have cut := (cuts_spec rest t).mpr ⟨w,present,hd⟩
    exact Bool.noConfusion (missing.symm.trans cut)
  exact ⟨a,List.mem_toFinset.mpr mem,i,j,only i hi.1,only j hj.1,by rw [hi.2,hj.2];decide⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem unate_safe {k ws} (run : live basicOps goal k ws.toFinset)
    (tight : ws.toFinset.card=k+1) : unateBad ws = false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  obtain ⟨a,mem,hit⟩ := List.any_eq_true.mp bad
  exact tight_unate run tight (direction_witness mem hit)
end P2828Check

namespace P2828Minor
open P2828Check P2828Live
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev Advice := List W → List W → List Minor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def checkChild (base : List W) (ad : Advice) (further : ℕ → List W → List W → Bool) (k : ℕ)
    (ws hist : List W) (extra : ℕ) (child : List W) : Bool :=
  match child with
  | [] => false
  | z :: _ => !(ws.contains z) && !((extra == 0) && unateBad child) && !((ad child (z::hist)).any (fun c => cheap base c k child (z::hist))) &&
      further extra child (z::hist)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def guided (base : List W) (ad : Advice) : ℕ → ℕ → List W → List W → Bool
  | 0, _, ws, _ => ws == [goal]
  | k+1, extra, ws, hist => ws == [goal] ||
    let more := checkChild base ad (guided base ad k) k ws hist
    (pairs ws).any (fun (a,b,r) => dispatch extra more a b r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
        have none : (ad (z::kept) (z::hist)).any (fun c => cheap base c k (z::kept) (z::hist)) = false :=
          List.any_eq_false.mpr fun c hc => by rw [cheap_eq _ _ _ _ _ hnd,safe (valid _ _ c hc) extended pool' hl]; decide
        have fresh : z ∉ ws := by simpa using hout
        have pass : ((k-kept.length == 0) && unateBad (z::kept)) = false := by
          by_cases zero : k-kept.length=0
          · have tight : (z::kept).toFinset.card=k+1 := by rw [List.toFinset_card_of_nodup hnd,List.length_cons];omega
            simp [unate_safe hl tight]
          · simp [zero]
        simp [checkChild,fresh,none,succ,pass]
      simp only [guided,Bool.or_eq_true,List.any_eq_true]
      right
      rcases hm with direct|swap
      · exact ⟨(a,b,r),direct,go hp hs hz⟩
      · exact ⟨(b,a,r),swap,go (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
end P2828Minor

namespace P2828Truth
open P2828Check P2828Minor P2828Live P2828Generic ThetaSigned SignedCofactor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def index {n} (x : Fin n → Bool) : Nat :=
  (List.finRange n).foldl (fun a i => a + if x i then 2^i.val else 0) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def truth (n t : Nat) (x : Fin n → Bool) := t.testBit (index x)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def select {n} (map : Array (Fin 1378)) (x : Fin n → Bool) : Fin 1378 := map.getD (index x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def literal {n} (w : Wire (Fin n → Bool)) : Prop :=
  (∃ b : Bool, ∀ x, w x=b) ∨ ∃ i : Fin n, ∃ b : Bool, ∀ x, w x = (x i != b)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
instance {n} (w : Wire (Fin n → Bool)) : Decidable (literal w) := by unfold literal;infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mem_literal {n w} (hw : @literal n w) : w ∈ literals n := by
  rcases hw with ⟨b,e⟩|⟨i,b,e⟩
  · exact Or.inl ⟨b,funext e⟩
  · refine Or.inr ⟨i,?_⟩
    cases b
    · exact Or.inl (funext fun x => by simpa using e x)
    · exact Or.inr (funext fun x => by simpa [inv] using e x)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validates {n t} (base : List W) (c : Minor) (rows : Array (Fin 1378))
    (inside : ∀ x : Fin n → Bool, c.mask.getLsbD (select rows x).val=true)
    (raw : base.all (fun w => decide (literal (interpret (@select n rows) w))) = true)
    (target : ∀ x : Fin n → Bool, interpret (select rows) goal x = truth n t x)
    (someGoal : ∃ g, cropOpt c.mask c.anchor goal = some g)
    (lower : ∀ k, Run (literals n) k (truth n t) → c.lower ≤ k) : c.Valid base := by
  apply transfer base c (select rows) inside _ (literals_closed n) _ _ (funext target) someGoal lower
  intro w hw
  exact mem_literal (of_decide_eq_true (List.all_eq_true.mp raw w hw))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem table_live {n k t} (cols : List W) (sites : List (Fin 689))
    (len : cols.length=n) (agrees : ∀ r : Fin 1378, truth n t (columnPick cols r) = wordBit r goal)
    (crit : critical (signals cols) sites=true) (run : Run (literals n) k (truth n t)) :
    live basicOps goal k (signals cols).toFinset := by
  obtain ⟨s,hs,hr⟩ := compress (anyBuild _ agrees run _ (columnGood cols len))
  exact all_required crit hs hr ▸ hr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

namespace P2828Root
open P2828Check
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def data : Array Face := #[
⟨19, 0, 8, 0x44440001040000888004000040000010000040000000400000000100000000000007ffffffffffffff8000000000007ff800000149c54349390d2109000424a1200000001090444210a134840000000000000000020022a20200820000444002008021001008804020000080220001010080000000000004020020020020020020020020020020020020a4e2a1a49c8690848002125090022a240848222108509a4211438aa2000381a0, 5⟩,
⟨0,0,0,0,0⟩,
⟨320, 0, 11, 0x1fffffffc000007fff8000007ff8007ff8007fffffffffffffffff80000000000ffe0000000001fe381e0fe000603fe001fe3fe006000fe01e03ffe000088000002203233fc449f060d986000223fffbb09820c884114fffffffe33a857fffc08c08c08c08c08c08c08c08c08c08c08c08c1c001ffc007ff0007fc0000ff1c0f07f000301ff000ff1ff0030007f00f01fff, 0⟩,
⟨24, 0, 11, 0x3fc00003e000007c001000007e0000380000e0000000f800600007804003000040fffffffff8007ffffffff8000000007fffff8c0c3c1c31b07671f249c7c60ed800000000000007460e04371a30f4e442301c2000021fe00481f000443e020800063fa0ad9c00067a6000027c0a30000bc0a005d28075d4114114114114114114114114114114114106061e0e18d83b38f924e3e3076f9118338f826233a307021b8d187a7221180e1, 0⟩,
⟨0,0,0,0,0⟩,
⟨66, 0, 11, 0x6669998d4c0000000000001994d0500000000000665311900000014887ff8007ffffffff8007fffffffffff800000018002b5f00ade000002eec0b63f0e05ebbb202eeb00b608c00000000a8802b68000000000000003334cee6b78000000000000cca6cae80000000003329aaee000000a77dc01c01c01c01c01c01c01c01c01c01c01c000c0015af8056f5dd80177605b1f8702f5dd901775805b046f830007f544015b4, 2⟩,
⟨17, 0, 11, 0x155540005540002aa801400015240005500014402000154800a000520000100080007fffffffffffffffff8000000007fffff800169c547e9391f250d6d9434a5a000000050d0444254a5b5d622871544000000000200aaaa0202aa000375400a0681b960102ab341b3010280aa4105cd06d50031a84748840a40a40a40a40a40a40a40a40a40a40a40a4b4e2a3f49c8f9286b6ca1a52d002aa74286822212a52daeb11438aa2223383e3, 0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨280, 0, 8, 0xf8006000078040030000408000007ff8007ffffffff8000000007fffff8000000001b07600024800060ed800000000000000060e04201a30f4e002301c2000021f60048170000404000000063fa0ad9c0002300000027c0a30000bc0a005d28075c0100100100100100100100100100100100106061e0e00d83b0001240003076c11183000026230030702100d187a7001180e1, 0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩,
⟨0,0,0,0,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def faceAt (i : Fin 45) : Face := data[i.val]
end P2828Root

namespace P2828Check
open P2828 P2828Live ThetaSigned PEqualNP.MetaComplexity ImportedHelpers
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def seed (y : Y) := y 0 || y 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gateWord := (rawInputs.getD 0 0) ||| (rawInputs.getD 1 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gift := canon gateWord
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def given := plus small seed
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seededPhysical (C : BinaryCircuit) (p : Bool)
    (ok : ∀ g ∈ C.gates, SignedCofactor.cornerGate g)
    (out : ∀ x : Y, (C.eval (List.ofFn x ++ [x 0 || x 1,false]) != p) = nine x) :
    Run given C.size nine := by
  have hr := SignedCofactor.gated C.gates C.output p ok (fun x : Y => List.ofFn x ++ [x 0 || x 1,false]) 11
    (fun _ => by simp) given (plus_closed small_closed seed)
  apply (funext out) ▸ hr
  intro i
  by_cases h : i<9
  · apply Or.inl
    refine Or.inr ⟨⟨i,h⟩,Or.inl (funext fun x => ?_)⟩
    rw [List.getD_append _ _ _ _ (by simpa using h),getD_ofFn 9 x false ⟨i,h⟩]
  · by_cases e : i=9
    · exact Or.inr (Or.inl (funext fun x => by simp [e,seed,List.getD_eq_getElem?_getD]))
    · apply Or.inl
      refine Or.inl ⟨false,funext fun x => ?_⟩
      by_cases e' : i=10
      · simp [e',ThetaSigned.bit,List.getD_eq_getElem?_getD]
      · exact List.getD_eq_default _ _ (by simp; omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seedGood : good given (insert gift inputs.toFinset) := by
  rintro f (old|rfl|rfl)
  · obtain ⟨w,e,hm⟩ := initialGood _ old
    exact ⟨w,e.imp_right (Finset.mem_insert_of_mem),hm⟩
  · exact ⟨gateWord,Or.inr (Finset.mem_insert_self ..),fun r => by
      change ((rawInputs.getD 0 0)[r.val] || (rawInputs.getD 1 0)[r.val]) = gateWord[r.val]
      simp [gateWord]⟩
  · refine ⟨~~~gateWord,Or.inr ?_,?_⟩
    · rw [canon_neg]; exact Finset.mem_insert_self ..
    · intro r
      change (!((rawInputs.getD 0 0)[r.val] || (rawInputs.getD 1 0)[r.val])) = (~~~gateWord)[r.val]
      simp [gateWord]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seedRoots {k} (h : Run given k nine) :
    live basicOps goal k inputs.toFinset ∨ live basicOps goal k (gift::inputs).toFinset := by
  obtain ⟨s,hs,hl⟩ := compress (signedBuild h _ seedGood)
  have entire : inputs.toFinset ⊆ s := by
    intro a ha
    let sites : List (Fin 689) := [0,32,64,96,128,150,182,204,226]
    have necessary : inputs.all (fun a => sites.any (fun i => (gift::inputs).all (fun b =>
        (b.getLsbD i.val == b.getLsbD (689+i.val)) || b == a))) = true := by decide +kernel
    obtain ⟨i,_,hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
    obtain ⟨b,hb,hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) hl
    have incl : b ∈ gift::inputs := List.mem_toFinset.mp (by simpa using hs hb)
    have he := List.all_eq_true.mp hAll b incl
    simp only [Bool.or_eq_true,beq_iff_eq] at he
    exact he.resolve_left hd ▸ hb
  by_cases use : gift ∈ s
  · right
    rwa [List.toFinset_cons,← Finset.Subset.antisymm hs (Finset.insert_subset use entire)]
  · have sub : s ⊆ inputs.toFinset := by
      intro a ha
      exact (Finset.mem_insert.mp (hs ha)).resolve_left (fun h => use (h ▸ ha))
    exact Or.inl ((Finset.Subset.antisymm sub entire) ▸ hl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gift_op : gift ∈ basicOps (inputs.getD 0 0) (inputs.getD 1 0) := by decide +kernel
end P2828Check

namespace P2828NineMinor
open P2828Check P2828Minor P2828Truth P2828Live ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mixed := truth 6 0xfffefffafcfceeaa
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Lower := ∀ k, Run (literals 6) k mixed → 10 ≤ k
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def asMinor (c : Face) : Minor := ⟨c.lower,c.mask,c.anchor⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def d1 : Minor := ⟨10,0x333594d20000000000000000000000034980000000000000000007fffff8000007ff8000000014b0000000000001580003b000b6056001140c00037aa00000e428002b68000088000000000003328020860d9860412233b5dfff820c884000ccd67c0a33a8577ff840c40c40c40c40c40c40c40c40c40c40c40c00000a590029202b0fc0ac0001d8005b02b0008a060001bd2800000d0a000a4b,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rows1 : Array (Fin 1378) := #[0,722,6,726,3,725,11,727,25,749,860,1210,27,751,864,1221,32,34,694,696,691,693,699,701,59,61,859,862,715,717,1218,1220,1,756,9,760,788,1096,792,1105,806,1201,922,1216,810,1207,1225,1229,35,755,697,1099,820,1095,1102,1104,805,808,1212,1215,1204,1206,1224,1228]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def d2 : Minor := ⟨10,0xccd65000000d20000000000000000000006880180000000000000007ff8007ff8000007ff8000000a8030000000560380000000300b36056008140c00083aa000d5242800c0280000014000401400000280208100469aebf740804cff80000500a20000280a0855fc27f8410410410410410410410410410410410410000540190100202b01c0ac000fd8059b02b0040a0600041d2800150d0a00000b,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rows2 : Array (Fin 1378) := #[32,691,40,702,34,693,42,703,59,715,881,1240,61,717,884,1242,0,3,728,734,722,725,730,735,25,27,882,886,749,751,1232,1243,35,820,44,827,755,1095,763,1113,805,1204,931,1246,808,1206,1237,1250,1,788,732,1111,756,1096,1107,1114,806,810,1234,1247,1201,1207,1238,1251]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def d3 : Minor := ⟨10,0x60c1860c104030410100000000000000000003000804000000000000000007ffffffff8000000000000000894b0000000461f811800169009b20460011000000000000d5100080d4a48000088000000000003300000070d9c70e1a673b59b59820c884000ccd654003ba8d778a000c00c00c00c00c00c00c00c00c00c00c00c00044a58002900230fc08c000b4804d902300088060005bd080011090a000a4b,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rows3 : Array (Fin 1378) := #[0,728,3,734,6,736,11,739,1,732,788,1111,9,738,792,1125,32,40,691,702,694,704,699,707,35,44,820,827,697,706,1102,1124,25,882,27,886,860,1254,864,1267,806,1234,810,1247,922,1260,1225,1274,59,881,715,1240,859,1253,1218,1266,805,931,1204,1246,1212,1259,1224,1273]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def data : Array Minor := #[asMinor (P2828Root.faceAt 0),d1,d2,d3,asMinor (P2828Root.faceAt 3),asMinor (P2828Root.faceAt 2),asMinor (P2828Root.faceAt 6),asMinor (P2828Root.faceAt 5),asMinor (P2828Root.faceAt 16)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cut (i : Fin 9) : Minor := data[i.val]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def advice (_ _ : List W) := (List.finRange 9).map cut
end P2828NineMinor

namespace P2828NineMinor
open P2828Check P2828Minor P2828Truth P2828Live ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem diag1 (low : Lower) : d1.Valid inputs :=
  validates (n:=6) (t:=0xfffefffafcfceeaa) inputs d1 rows1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Option.isSome_iff_exists.mp (by decide +kernel)) low
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem diag2 (low : Lower) : d2.Valid inputs :=
  validates (n:=6) (t:=0xfffefffafcfceeaa) inputs d2 rows2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Option.isSome_iff_exists.mp (by decide +kernel)) low
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem diag3 (low : Lower) : d3.Valid inputs :=
  validates (n:=6) (t:=0xfffefffafcfceeaa) inputs d3 rows3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Option.isSome_iff_exists.mp (by decide +kernel)) low
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid (low : Lower) (good : ∀ i, (P2828Root.faceAt i).Valid) (i : Fin 9) : (cut i).Valid inputs := by
  fin_cases i
  · exact ofOrdinary (P2828Root.faceAt 0) (good 0)
  · exact diag1 low
  · exact diag2 low
  · exact diag3 low
  · exact ofOrdinary (P2828Root.faceAt 3) (good 3)
  · exact ofOrdinary (P2828Root.faceAt 2) (good 2)
  · exact ofOrdinary (P2828Root.faceAt 6) (good 6)
  · exact ofOrdinary (P2828Root.faceAt 5) (good 5)
  · exact ofOrdinary (P2828Root.faceAt 16) (good 16)
end P2828NineMinor

namespace P2828NineMinor
open P2828Check P2828Minor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rootPair (i : Nat) := match (pairs (gift::inputs))[i]? with
  | none => false
  | some (a,b,r) => dispatch 4 (P2828Minor.checkChild inputs advice (P2828Minor.guided inputs advice 12) 12 (gift::inputs) [gift]) a b r
end P2828NineMinor

namespace P2828NineMinor
open P2828Check P2828Minor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closed : P2828Minor.guided inputs advice 13 4 (gift::inputs) [gift] = false := by decide +kernel
end P2828NineMinor

namespace P2828Raw
open P2828Check P2828Live
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def data : Array Face := #[
⟨17, 0, 11, 0x155540005540002aa801400015240005500014402000154800a000520000100080007fffffffffffffffff8000000007fffff800169c547e9391f250d6d9434a5a000000050d0444254a5b5d622871544000000000200aaaa0202aa000375400a0681b960102ab341b3010280aa4105cd06d50031a84748840a40a40a40a40a40a40a40a40a40a40a40a4b4e2a3f49c8f9286b6ca1a52d002aa74286822212a52daeb11438aa2223383e3, 0⟩,
⟨66, 0, 11, 0x6669998d4c0000000000001994d0500000000000665311900000014887ff8007ffffffff8007fffffffffff800000018002b5f00ade000002eec0b63f0e05ebbb202eeb00b608c00000000a8802b68000000000000003334cee6b78000000000000cca6cae80000000003329aaee000000a77dc01c01c01c01c01c01c01c01c01c01c01c000c0015af8056f5dd80177605b1f8702f5dd901775805b046f830007f544015b4, 2⟩,
⟨132, 0, 11, 0xf1c38e1e30c878c32310000000000000000007451a0c04ffffff8007ff8007fffffffffff8000007ff8035cdef8000000671f819c0016901dfa0670919800000000100d73121c0d5ede02068a020000000003340000078f9c70f1a673f79b59828e884000cdde54003ba8d778a402c02c02c02c02c02c02c02c02c02c02c02c01ae6f7c343d80338fc0ce000b480efd033848cc06000fff0806b9890e06af6f, 0⟩,
⟨24, 0, 11, 0x3fc00003e000007c001000007e0000380000e0000000f800600007804003000040fffffffff8007ffffffff8000000007fffff8c0c3c1c31b07671f249c7c60ed800000000000007460e04371a30f4e442301c2000021fe00481f000443e020800063fa0ad9c00067a6000027c0a30000bc0a005d28075d4114114114114114114114114114114114106061e0e18d83b38f924e3e3076f9118338f826233a307021b8d187a7221180e1, 0⟩,
⟨160, 0, 11, 0x1fffff800001ff000000000000000000000ff803f8007ff8007ff8007ff8007ffffffffffffff8003fc038000000ff0380000000300f3e0ff03c3e0c000c3ef000ff3e3c00c03e0000014020601600000282208100469fffffc0804cff80000514e30000284a0857fc27fcc10c10c10c10c10c10c10c10c10c10c10c10001fe01f8380707f81c1fe000fd8079f07f81e1f0600061f78007f9f1e00601f, 0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def faceAt (i : Fin 5) := data[i.val]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def bank : Array (List (Fin 5)) := #[[0], [0], [0], [0], [0], [0], [0], [0], [1], [1], [0], [1], [1], [1], [1], [2], [0], [2], [1], [2], [2], [0], [3], [1], [2], [3], [0], [0], [0], [0], [1], [2], [4], [1], [1], [2]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rawPair (i : Nat) := match (pairs inputs)[i]? with
  | none => false
  | some (a,b,r) => dispatch 5 (checkChild ((bank.getD i []).map faceAt) (fun _ _ _ => true) 12 inputs []) a b r
end P2828Raw

namespace P2828Raw
open P2828Check P2828Live P2828 ThetaSigned
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def advice (_ _ : List W) : List Face := (List.finRange 5).map faceAt
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem firstScan : guided advice 13 5 inputs [] = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signed_fourteen {k : Nat} (facts : ∀ i, (faceAt i).Valid) (run : Run small k nine) : 14 ≤ k := by
  by_contra! low
  have pad (t : Nat) (le : k ≤ t) : live basicOps goal t inputs.toFinset := by
    induction le with
    | refl => exact inputLive run
    | step _ ih => exact Or.inl ih
  have ok (s h : List W) (c : Face) (hc : c ∈ advice s h) : c.Valid := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
    exact facts i
  have initial : allSeen [] = inputs.toFinset := by simp [allSeen]
  have cert := guided_complete advice ok 13 inputs [] 5 (by decide) (by decide) (initial ▸ History.initial)
    (initial ▸ Finset.Subset.refl _) (pad _ (by omega))
  rw [firstScan] at cert
  contradiction
end P2828Raw

namespace C4Base
open ThetaSigned
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev Y := Fin 7 → Bool
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def small : Set (Wire Y) := {f | (∃ c, f=bit c) ∨ ∃ i : Fin 7, f=(fun x => x i) ∨ f=inv (fun x => x i)}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def nine (y : Y) : Bool := (y 0 && y 1) || (y 2 && y 4) || (y 0 && y 5) || (y 2 && y 5) || (y 3 && y 5) || (y 1 && y 6) || (y 3 && y 6) || (y 4 && y 6)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_closed : Closed small := by
  constructor
  · exact fun b => Or.inl ⟨b,rfl⟩
  · intro f hf
    rcases hf with ⟨b,rfl⟩|⟨i,rfl|rfl⟩
    · exact Or.inl ⟨!b,rfl⟩
    · exact Or.inr ⟨i,Or.inr rfl⟩
    · exact Or.inr ⟨i,Or.inl (inv_inv _)⟩

end C4Base

namespace P2828Raw
open P2828 P2828Check ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def insertVars {n : Nat} (idx : Fin 9 → Option (Fin n)) (x : Fin n → Bool) (v : Fin 9) :=
  match idx v with
  | none => false
  | some i => x i
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Lower4 := ∀ k, Run C4Base.small k C4Base.nine → 11 ≤ k
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector0 : Fin 9 → Option (Fin 7) := ![none,some 0,some 5,some 3,none,some 4,some 1,some 2,some 6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem good0 (lower : Lower4) : (faceAt 0).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector0) (literals 7) (pullSmall selector0)
  have eq : ∀ x, nine (pin (faceAt 0).fixed (faceAt 0).values (insertVars selector0 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector1 : Fin 9 → Option (Fin 7) := ![some 0,none,some 4,some 6,some 1,some 5,none,some 2,some 3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem good1 (lower : Lower4) : (faceAt 1).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector1) (literals 7) (pullSmall selector1)
  have eq : ∀ x, nine (pin (faceAt 1).fixed (faceAt 1).values (insertVars selector1 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector2 : Fin 9 → Option (Fin 7) := ![some 5,some 0,none,some 4,some 2,some 3,some 1,none,some 6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem good2 (lower : Lower4) : (faceAt 2).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector2) (literals 7) (pullSmall selector2)
  have eq : ∀ x, nine (pin (faceAt 2).fixed (faceAt 2).values (insertVars selector2 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector3 : Fin 9 → Option (Fin 7) := ![some 3,some 5,some 0,none,none,some 6,some 2,some 1,some 4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem good3 (lower : Lower4) : (faceAt 3).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector3) (literals 7) (pullSmall selector3)
  have eq : ∀ x, nine (pin (faceAt 3).fixed (faceAt 3).values (insertVars selector3 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector4 : Fin 9 → Option (Fin 7) := ![some 0,some 5,some 3,some 6,some 1,none,some 2,none,some 4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem good4 (lower : Lower4) : (faceAt 4).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector4) (literals 7) (pullSmall selector4)
  have eq : ∀ x, nine (pin (faceAt 4).fixed (faceAt 4).values (insertVars selector4 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact lower k run
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allValid (lower : Lower4) (i : Fin 5) : (faceAt i).Valid := by
  fin_cases i
  · exact good0 lower
  · exact good1 lower
  · exact good2 lower
  · exact good3 lower
  · exact good4 lower
end P2828Raw

namespace C4RLive

variable {α : Type} [DecidableEq α]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

end C4RLive

namespace C4RLive
variable {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

end C4RLive

namespace C4RCheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev W := BitVec 464
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def neg (x : W) : W := ~~~x
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def both (x y : W) : W := x &&& y
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def canon (x : W) : W := if x.getLsbD 0 then neg x else x
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def ops (x y : W) : List W :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sep (x : W) := (x ^^^ (x >>> 232)).setWidth 232
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cuts (ws : List W) : BitVec 232 := ws.foldr (fun w v => sep w ||| v) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def goal : W := canon (((-1 : BitVec 232) ++ (0 : BitVec 232)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a,rest) :: (singles rest).map (fun (b,bs) => (b,a :: bs))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b,bs) => (a,b,bs)) ++
      (pairs rest).map (fun (b,c,bs) => (b,c,a :: bs))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def advance (k : ℕ) (next : List W → Bool) (a b : W) (rest : List W) : Bool :=
  let ds := ops a b
  let base := cuts rest
  let attempt := fun (kept : List W) (covered : BitVec 232) =>
    if kept.length + 1 ≤ k+1 then
      ds.any (fun z => (covered ||| sep z == -1) && next (z :: kept))
    else false
  attempt rest base || attempt (a :: rest) (sep a ||| base) ||
    attempt (b :: rest) (sep b ||| base) || attempt (a :: b :: rest) (sep a ||| (sep b ||| base))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def search : ℕ → List W → Bool
  | 0, ws => ws == [goal]
  | k+1, ws => ws == [goal] || (pairs ws).any (fun (a,b,rest) => advance k (search k) a b rest)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rawInputs : List W := [0x507619494848240f0e83fb98007ac0be8fc384922aa4aa49400495ffff003e38000000000f0f83fff8003fc07f80c004922aa4aa49400495f800, 0xa2120815d8690b2b023eaa88056a6c8abfc2d924c449009014a93ffabf00000001f87801f0003c000007c03f803f005924c449009014a90002bf, 0x30bac2258c801200107ffbaf58003b5b51540038b071ccfd81ffd8500a003fc00000000000003ffffff8003fffc0000038b071ccfd800018500a, 0x50124ba0112dd5fa07fffcfe6bf000062a80e3f077e00e3fe0e01602c00000000000001fff03fffffffffc00000000e3f077e00e0000e01602c, 0xc82240c1ee84618fdb6f330d4800091344106fc007801ffc18cfc1833000000001ff8001ffffc000000000000000006fc00780000018cfc18330, 0xf1fc9703fd577f1dacb7c3f674b3b27c001f70003ffff0021ff02007c0ffc00001fffffe00000000000000000000007000000010021ff02007c0, 0xfe3f27fdf66781eecf3bfc07873c3c6038207ffff8001f03e1003e0400fffffffe0000000000000000000000000000000038001f03e1003e0400]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def inputs := rawInputs.map canon

end C4RCheck
namespace C4RCheck
variable {α : Type}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
end C4RCheck

namespace C4RCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev basicOps (a b : W) := (ops a b).toFinset
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def differs (i : Fin 232) (w : W) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (232+i.val)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem neg_differs (i : Fin 232) (w : W) : differs i (neg w) ↔ differs i w := by
  have lo : i.val < 464 := by omega
  have hi : 232+i.val < 464 := by omega
  simp [neg, differs, hi, lo]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canon_differs (i : Fin 232) (w : W) : differs i (canon w) ↔ differs i w := by
  unfold canon
  split <;> simp [neg_differs]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ops_differs (i : Fin 232) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  by_contra! h
  have e₁ : a.getLsbD i.val = a.getLsbD (232+i.val) := by simpa [differs] using h.1
  have e₂ : b.getLsbD i.val = b.getLsbD (232+i.val) := by simpa [differs] using h.2
  have lo : i.val < 464 := by omega
  have hi : 232+i.val < 464 := by omega
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [canon_differs] at hd <;>
    simp only [both, neg, differs, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, lo, e₁, e₂] at hd <;> simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem goal_differs (i : Fin 232) : differs i goal := by
  rw [goal, canon_differs]
  unfold differs
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [i.isLt, show ¬232 + i.val < 232 by omega]
  exact BitVec.getElem_allOnes _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cuts_spec (ws : List W) (i : Fin 232) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    simp [sep, i.isLt, differs]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cuts_full {k : ℕ} {ws : List W} (h : C4RLive.live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := C4RLive.live_separates (differs ⟨j,hj⟩) (goal_differs ⟨j,hj⟩) (ops_differs ⟨j,hj⟩) h
  have hbit := (cuts_spec ws ⟨j,hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 232)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, both, BitVec.and_comm]
  grind [BitVec.and_comm]

end C4RCheck

namespace C4RCheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def keepChoices (a b : W) (r : List W) := [r, a::r, b::r, a::b::r]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem advance_has {k : ℕ} {next : List W → Bool} {a b z : W} {r kept : List W}
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (hn : kept.length+1 ≤ k+1) (hc : cuts (z::kept) = -1) (ht : next (z::kept) = true) :
    advance k next a b r = true := by
  have hh : (ops a b).any (fun w => (cuts kept ||| sep w == -1) && next (w :: kept)) := by
    apply List.any_eq_true.mpr
    refine ⟨z, by simpa [basicOps] using hz, ?_⟩
    change sep z ||| cuts kept = -1 at hc
    simp [BitVec.or_comm (cuts kept), hc, ht]
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [advance, hn, ite_true, cuts, List.foldr_cons] at * <;> simp_all

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem search_complete (n : ℕ) (ws : List W) (hn : ws.Nodup)
    (h : C4RLive.live basicOps goal n ws.toFinset) : search n ws = true := by
  induction n generalizing ws with
  | zero => simp [search, singleton_list hn h]
  | succ k ih =>
    rcases C4RLive.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [search, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          advance k (search k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : C4RLive.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        apply advance_has hop hk _ (cuts_full hl) (ih _ hnd hl)
        have hc := C4RLive.live_card hl
        rw [List.toFinset_card_of_nodup hnd] at hc
        exact hc
      simp only [search, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

end C4RCheck

namespace C4RCheck
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def bit (k : Fin 464) (z : W) := z[k.val]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 464) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canon_neg (x : W) : canon (~~~x) = canon x := by
  unfold canon neg
  simp only [BitVec.getLsbD_not, BitVec.not_not]
  cases h : x.getLsbD 0 <;> simp [h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sign (x : W) : x = canon x ∨ x = neg (canon x) := by
  unfold canon neg
  split <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signed_both {x y a b : W} (hx : x = a ∨ x = neg a) (hy : y = b ∨ y = neg b) :
    canon (x &&& y) ∈ basicOps a b := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp [basicOps, ops, both]

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def represents (available : Finset W) (w : List W) :=
  ∀ u ∈ w, canon u = 0 ∨ canon u ∈ available

set_option maxRecDepth 100000 in
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
      have zeroOrFull (t : W) (h : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 464 := by
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

open ThetaSigned C4Base
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def assignment (k : Fin 464) (i : Fin 7) := bit k (rawInputs.getD i.val 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : C4RLive.live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 232) := [0, 11, 22, 33, 42, 53, 70]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      (b.getLsbD i.val == b.getLsbD (232+i.val)) || b == a))) = true := by decide
  obtain ⟨i,_,hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hrow
    exact hrow.resolve_left hd
  obtain ⟨b,hb,hd⟩ := C4RLive.live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem graph_rows : ∀ k : Fin 464, nine (assignment k) =
    bit k ((-1 : BitVec 232) ++ (0 : BitVec 232)) := by
  let x := fun (i : Nat) => rawInputs.getD i 0
  let H := (x 0 &&& x 1) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6)
  have h : H = ((-1 : BitVec 232) ++ (0 : BitVec 232)) := by decide +kernel
  intro k
  rw [← h]
  simp only [H,bit,BitVec.getElem_or,BitVec.getElem_and]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def good (P : Set (Wire Y)) (av : Finset W) : Prop :=
  ∀ f ∈ P, ∃ u : W, (canon u = 0 ∨ canon u ∈ av) ∧ ∀ r, f (assignment r) = bit r u

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signedBuild {P : Set (Wire Y)} {k : ℕ} (h : ThetaSigned.Run P k nine) :
    ∀ av, good P av → C4RLive.build basicOps goal k av := by
  generalize eqF : nine = f at h
  induction h with
  | @done P k f hf =>
    subst f
    intro av rep
    obtain ⟨u,hu,huv⟩ := rep _ hf
    have eq : u = ((-1 : BitVec 232) ++ (0 : BitVec 232)) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      exact ((huv ⟨i,hi⟩).symm.trans (graph_rows ⟨i,hi⟩))
    rw [eq] at hu
    have ing : goal ∈ av := hu.resolve_left (by decide)
    induction k with
    | zero => exact ing
    | succ k ih => exact Or.inl ih
  | @gate P k f a b op ha hb tail ih =>
    intro av rep
    obtain ⟨u,ru,eu⟩ := rep _ ha
    obtain ⟨v,rv,ev⟩ := rep _ hb
    let z := if op then u ||| v else u &&& v
    have hbits (r) : ThetaSigned.bin op a b (assignment r) = bit r z := by
      cases op <;> simp [z,ThetaSigned.bin,eu,ev,bit]
    have add {av' : Finset W} (sub : av ⊆ av') (has : canon z=0 ∨ canon z ∈ av') :
        good (plus P (ThetaSigned.bin op a b)) av' := by
      rintro g (old|rfl|rfl)
      · obtain ⟨w,hw,e⟩ := rep g old
        exact ⟨w,hw.imp_right (fun h => sub h),e⟩
      · exact ⟨_,has,hbits⟩
      · refine ⟨~~~z,by simpa only [canon_neg] using has,?_⟩
        intro r
        simp [ThetaSigned.inv,hbits,bit]
    have hws : represents av [u,v] := by
      intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl <;> assumption
    have hz : possible [u,v] z := by
      have hh := pair (ws:=[u,v]) (Or.inr (List.mem_cons_self ..) : u=0 ∨ u∈[u,v])
        (Or.inr (by simp) : v=0 ∨ v∈[u,v])
      cases op <;> first | exact hh.1 | exact hh.2
    rcases classify hws hz with hz|hz|⟨a',ha',b',hb',ne,mem⟩
    · exact Or.inl (ih eqF av (add (fun _ h=>h) (Or.inl hz)))
    · exact Or.inl (ih eqF av (add (fun _ h=>h) (Or.inr hz)))
    · exact Or.inr ⟨a',ha',b',hb',ne,_,mem,ih eqF _ (add (Finset.subset_insert ..) (Or.inr (Finset.mem_insert_self ..)))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem initialGood : good small inputs.toFinset := by
  rintro f (⟨b,rfl⟩|⟨i,rfl|rfl⟩)
  · cases b
    · exact ⟨0,Or.inl (by decide),by simp [ThetaSigned.bit,bit]⟩
    · exact ⟨-1,Or.inl (by decide),by intro r; exact (BitVec.getElem_allOnes r.val r.isLt).symm⟩
  · refine ⟨_,Or.inr ?_,fun _=>rfl⟩
    change canon (rawInputs.getD i.val 0) ∈ inputs.toFinset
    fin_cases i <;> decide +kernel
  · refine ⟨~~~(rawInputs.getD i.val 0),Or.inr ?_,?_⟩
    · rw [canon_neg]
      fin_cases i <;> decide +kernel
    · intro r; simp [assignment,ThetaSigned.inv,bit]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inputLive {k} (h : ThetaSigned.Run small k nine) : C4RLive.live basicOps goal k inputs.toFinset := by
  obtain ⟨s,hs,hl⟩ := C4RLive.compress (signedBuild h _ initialGood)
  exact (full_inputs hs hl) ▸ hl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rawOps (a b : W) := [both a b, both a (neg b), both (neg a) b, both (neg a) (neg b)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sep_canon (x : W) : sep (canon x) = sep x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h (v : W) : (sep v)[i] = true ↔ differs ⟨i,hi⟩ v := by
    change (sep v).getLsbD i = true ↔ _
    simp [sep, hi, differs]
  have eq := (h (canon x)).trans ((canon_differs ⟨i,hi⟩ x).trans (h x).symm)
  exact Bool.eq_iff_iff.mpr eq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (rawOps a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (canon w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra-1) (canon w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra-1) (canon w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra-2) (canon w :: a :: b :: r))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a,b,r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

end C4RCheck

namespace C4RCheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : C4RLive.live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases C4RLive.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
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
        have hl : C4RLive.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        have hc := C4RLive.live_card hl
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

end C4RCheck

namespace C4RLive
variable {α β : Type} [DecidableEq α] [DecidableEq β]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def kept (p : α → Option β) (s : Finset α) : Finset β := s.biUnion (fun a => (p a).toFinset)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def zeros (p : α → Option β) (s : Finset α) : ℕ :=
  (s.filter (fun a => p a = none)).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kept_insert (p : α → Option β) (a : α) (s : Finset α) :
    kept p (insert a s) = (p a).toFinset ∪ kept p s := by
  simp [kept]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeros_some {p : α → Option β} {a : α} {v : β} (h : p a = some v) (s : Finset α) :
    zeros p (insert a s) = zeros p s := by simp [zeros, Finset.filter_insert, h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeros_none {p : α → Option β} {a : α} (h : p a = none) {s : Finset α} (ha : a ∉ s) :
    zeros p (insert a s) = zeros p s + 1 := by simp [zeros, Finset.filter_insert, h, ha]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeros_le (p : α → Option β) (a : α) (s : Finset α) :
    zeros p (insert a s) ≤ zeros p s + 1 := by
  cases h : p a with
  | some v => rw [zeros_some h]; omega
  | none =>
    by_cases hm : a ∈ s
    · rw [Finset.insert_eq_of_mem hm]; omega
    · exact (zeros_none h hm).le

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeros_mono (p : α → Option β) {s t : Finset α} (h : s ⊆ t) :
    zeros p s ≤ zeros p t := Finset.card_le_card (Finset.filter_subset_filter _ h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem build_mono {ops : β → β → Finset β} {goal : β} {k : ℕ} {s t : Finset β}
    (hs : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hs h
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,tail⟩
    · exact .inl (ih hs skip)
    · exact .inr ⟨a,hs ha,b,hs hb,hab,z,hz,ih (Finset.insert_subset_insert _ hs) tail⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def projects (p : α → Option β) (ops : α → α → Finset α) (ops' : β → β → Finset β) : Prop :=
  ∀ a b z, z ∈ ops a b → ∀ v, p z = some v →
    p a = some v ∨ p b = some v ∨
    ∃ u w, p a = some u ∧ p b = some w ∧ u ≠ w ∧ v ∈ ops' u w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zeros_budget {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) : zeros p s ≤ k := by
  induction k generalizing s with
  | zero => change s = {g} at h; simp [h, zeros, hg]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact (ih skip).trans (by omega)
    · exact (zeros_step P hz r hn).trans (Nat.succ_le_succ (ih tail))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

end C4RLive

namespace C4RCheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def crop (m : W) (r : Fin 464) (x : W) : W :=
  (x &&& m) ||| (if x[r.val] then ~~~m else 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pos (m : W) (r : Fin 464) (i : Nat) := if m.getLsbD i then i else r.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pos_lt (m : W) (r : Fin 464) {i} (hi : i < 464) : pos m r i < 464 := by
  unfold pos; split <;> omega
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crop_bit (m : W) (r : Fin 464) (x : W) (i : Nat) (hi : i < 464) :
    (crop m r x).getLsbD i = x.getLsbD (pos m r i) := by
  unfold crop pos
  rw [BitVec.getLsbD_eq_getElem hi (x := m)]
  cases hr : x[r.val] <;> cases hm : m[i] <;> simp [hr,hm,hi]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crop_and (m : W) (r : Fin 464) (x y : W) :
    crop m r (x &&& y) = crop m r x &&& crop m r y := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (x &&& y)).getLsbD j = (crop m r x &&& crop m r y).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crop_neg (m : W) (r : Fin 464) (x : W) :
    crop m r (~~~x) = ~~~crop m r x := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (~~~x)).getLsbD j = (~~~crop m r x).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_not, h, pos_lt _ _ h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def wrap (x : W) : Option W := if canon x = 0 then none else some (canon x)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wrap_neg (x : W) : wrap (~~~x) = wrap x := by simp only [wrap, canon_neg]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cropOpt (m : W) (r : Fin 464) (x : W) := wrap (crop m r x)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crop_canon (m : W) (r : Fin 464) (x : W) :
    cropOpt m r (canon x) = cropOpt m r x := by
  unfold canon
  split
  · simp only [cropOpt, neg, crop_neg, wrap_neg]
  · rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem binary_project {x y v : W} (h : wrap (x &&& y) = some v) :
    wrap x = some v ∨ wrap y = some v ∨
    ∃ u w, wrap x = some u ∧ wrap y = some w ∧ u ≠ w ∧ v ∈ basicOps u w := by
  have trivial (t : W) (ht : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 464 := by
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask_projects (m : W) (r : Fin 464) : C4RLive.projects (cropOpt m r) basicOps basicOps := by
  intro a b z hz v hv
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [crop_canon] at hv <;> simp only [cropOpt, both, neg, crop_and, crop_neg] at hv ⊢ <;>
    simpa only [wrap_neg] using binary_project hv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def projectedBudget (m : W) (r : Fin 464) (n : Nat) (ws : List W) : Nat :=
  n - (ws.filter (fun w => (cropOpt m r w).isNone)).length

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def available (m : W) (r : Fin 464) (ws : List W) : List W :=
  (ws.filterMap (cropOpt m r)).dedup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem available_spec (m : W) (r : Fin 464) (ws : List W) :
    (available m r ws).toFinset = C4RLive.kept (cropOpt m r) ws.toFinset := by
  ext y; simp [available, C4RLive.kept, List.mem_filterMap]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem projected_bound (m : W) (r : Fin 464) (n : Nat) {ws : List W} (hn : ws.Nodup) :
    n ≤ projectedBudget m r n ws + C4RLive.zeros (cropOpt m r) ws.toFinset := by
  let xs := ws.filter (fun w => (cropOpt m r w).isNone)
  have eq : (xs.toFinset) = ws.toFinset.filter (fun w => cropOpt m r w = none) := by
    ext w; simp [xs]
  have card := List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist :
    xs.Sublist ws))
  rw [eq] at card
  change (ws.toFinset.filter (fun w => cropOpt m r w = none)).card = xs.length at card
  change n ≤ n-xs.length + (ws.toFinset.filter (fun w => cropOpt m r w = none)).card
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem face_build (m : W) (r : Fin 464) {g : W} (hg : cropOpt m r goal = some g)
    {k : ℕ} {ws : List W} (hn : ws.Nodup) (h : C4RLive.live basicOps goal k ws.toFinset) :
    C4RLive.build basicOps g (projectedBudget m r k ws) (available m r ws).toFinset := by
  rw [available_spec]
  exact C4RLive.project_live hg (mask_projects m r) h _ (projected_bound m r k hn)
end C4RCheck

namespace ThetaBinary
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds ImportedHelpers
open ThetaSigned
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def signed (b : Bool) (v : Bool) := if b then !v else v
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def BW {n : ℕ} (gs : List BinaryGate) (x : Fin n → Bool) := (BinaryCircuit.mk gs 0).wires (List.ofFn x)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Reads {n : ℕ} (gs : List BinaryGate) (f : Wire (Fin n → Bool)) : Prop :=
  (∃ b, f = bit b) ∨ ∃ i < n + gs.length, ∃ b : Bool, ∀ x, f x = signed b ((BW gs x).getD i false)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bw_length {n} (gs : List BinaryGate) (x : Fin n → Bool) : (BW gs x).length = n+gs.length := by
  have aux : ∀ (ls : List BinaryGate) (w : List Bool),
      (ls.foldl (fun (w : List Bool) (g : BinaryGate) => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) w).length =
      w.length + ls.length := by
    intro ls
    induction ls with
    | nil => simp
    | cons g gs ih => intro w; simp only [List.foldl_cons,ih,List.length_append,List.length_nil,List.length_cons]; omega
  simpa [BW,BinaryCircuit.wires] using aux gs (List.ofFn x)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bw_append {n} (gs : List BinaryGate) (g : BinaryGate) (x : Fin n → Bool) :
    BW (gs++[g]) x = BW gs x ++ [g.op ((BW gs x).getD g.left false) ((BW gs x).getD g.right false)] := by
  simp [BW,BinaryCircuit.wires,List.foldl_append]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reads_inv {n} {gs : List BinaryGate} {f : Wire (Fin n → Bool)} (h : Reads gs f) : Reads gs (inv f) := by
  rcases h with ⟨b,rfl⟩|⟨i,hi,b,e⟩
  · exact Or.inl ⟨!b,rfl⟩
  · exact Or.inr ⟨i,hi,!b,fun x => by cases b <;> simp [inv,e,signed]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reads_extend {n} {gs : List BinaryGate} (g : BinaryGate) {f : Wire (Fin n → Bool)}
    (h : Reads gs f) : Reads (gs++[g]) f := by
  rcases h with h|⟨i,hi,b,e⟩
  · exact Or.inl h
  · refine Or.inr ⟨i,by simp;omega,b,?_⟩
    intro x
    rw [bw_append,List.getD_append _ _ _ _ (by rw [bw_length];exact hi)]
    exact e x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ref {n} {gs : List BinaryGate} {f : Wire (Fin n → Bool)} (h : Reads gs f) :
    ∃ i : ℕ, ∃ u : Bool → Bool, ∀ x, f x = u ((BW gs x).getD i false) := by
  rcases h with ⟨b,rfl⟩|⟨i,hi,b,e⟩
  · exact ⟨0,fun _=>b,fun _=>rfl⟩
  · exact ⟨i,signed b,e⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem realise {n} {P : Set (Wire (Fin n → Bool))} {k f}
    (h : Run P k f) : ∀ gs : List BinaryGate, (∀ g ∈ P, Reads gs g) →
    ∃ gs' : List BinaryGate, gs'.length ≤ gs.length+k ∧ Reads gs' f := by
  induction h with
  | @done P k f hf => intro gs rep;exact ⟨gs,by omega,rep _ hf⟩
  | @gate P k f a b op ha hb tail ih =>
    intro gs rep
    obtain ⟨i,u,eu⟩ := ref (rep a ha)
    obtain ⟨j,v,ev⟩ := ref (rep b hb)
    let g : BinaryGate := ⟨fun l r => if op then u l || v r else u l && v r,i,j⟩
    have out : Reads (gs++[g]) (bin op a b) := by
      refine Or.inr ⟨n+gs.length,by simp, false,?_⟩
      intro x
      rw [bw_append,←bw_length gs x,getD_snoc_eq]
      simp [bin,g,signed,eu x,ev x]
    obtain ⟨ls,cap,final⟩ := ih (gs++[g]) (by
      rintro q (hq|rfl|rfl)
      · exact reads_extend g (rep q hq)
      · exact out
      · exact reads_inv out)
    exact ⟨ls,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cap,final⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bw_prefix {n} (l r : List BinaryGate) (x : Fin n → Bool) (i : ℕ) (hi : i<n+l.length) :
    (BW (l++r) x).getD i false = (BW l x).getD i false := by
  induction r using List.reverseRecOn with
  | nil => simp
  | append_singleton r g ih =>
    rw [← List.append_assoc,bw_append,List.getD_append _ _ _ _ (by simp [bw_length];omega),ih]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem export_run {n} {P : Set (Wire (Fin n → Bool))} {k f}
    (h : Run P k f) (raw : ∀ g ∈ P, Reads [] g)
    (nc : ∀ b, f ≠ bit b) (np : ∀ (i : Fin n) (b : Bool), f ≠ fun x => signed b (x i)) :
    HasBinarySize n f k := by
  obtain ⟨gs,cap,rep⟩ := realise h [] raw
  simp only [List.length_nil,zero_add] at cap
  rcases rep with ⟨b,hb⟩|⟨i,hi,b,ef⟩
  · exact (nc b hb).elim
  · cases b with
    | false => exact ⟨⟨gs,i⟩,cap,fun x => (ef x).symm⟩
    | true =>
      by_cases lo : i < n
      · apply (np ⟨i,lo⟩ true _).elim
        funext x
        have pr := bw_prefix [] gs x i (by simp;exact lo)
        simp only [List.nil_append] at pr
        rw [ef,pr]
        exact congrArg _ (getD_ofFn n x false ⟨i,lo⟩)
      · let j := i-n
        have hj : j<gs.length := by dsimp [j];omega
        let pre:=gs.take j
        let g:=gs[j]
        have plen : pre.length = j := List.length_take_of_le hj.le
        have sp : gs = (pre ++ [g]) ++ gs.drop (j+1) := by
          rw [List.append_assoc,List.singleton_append,←List.drop_eq_getElem_cons hj,List.take_append_drop]
        let newG : BinaryGate := ⟨fun a b => !(g.op a b),g.left,g.right⟩
        refine ⟨⟨pre++[newG],i⟩,?_,?_⟩
        · change (pre++[newG]).length ≤ k
          simp only [List.length_append,List.length_singleton,plen]; omega
        · intro x
          have ij : i=n+pre.length := by rw [plen];dsimp [j];omega
          have old := bw_prefix (pre++[g]) (gs.drop (j+1)) x i (by simp [ij])
          rw [← sp] at old
          rw [ef,old]
          change (BW (pre++[newG]) x).getD i false = _
          rw [bw_append,bw_append,ij,←bw_length pre x,getD_snoc_eq,getD_snoc_eq]
          rfl
end ThetaBinary

namespace C4RCheck
open ThetaSigned
variable {T : Type}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def interpret (pick : T → Fin 464) (w : W) : Wire T := fun x => w.getLsbD (pick x).val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem interpret_neg (pick : T → Fin 464) (w : W) : interpret pick (neg w) = inv (interpret pick w) := by
  funext x
  simp [neg,interpret,inv,(pick x).isLt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem interpret_canon (pick : T → Fin 464) (w : W) :
    interpret pick (canon w) = interpret pick w ∨ interpret pick (canon w) = inv (interpret pick w) := by
  unfold canon; split
  · exact Or.inr (interpret_neg _ _)
  · exact Or.inl rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem interpret_both (pick : T → Fin 464) (a b : W) :
    interpret pick (both a b) = bin false (interpret pick a) (interpret pick b) := by
  funext x;simp [interpret,both,bin]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run_pad {P : Set (Wire T)} {k f} (h : Run P k f) : Run P (k+1) f := by
  induction h with
  | done hf => exact .done hf
  | gate op ha hb _ ih => exact .gate op ha hb ih

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Run_inv {P : Set (Wire T)} {k f} (h : Run P k f) (hc : Closed P) : Run P k (inv f) := by
  induction h with
  | done hf => exact .done (hc.2 _ hf)
  | gate op ha hb _ ih => exact .gate op ha hb (ih (plus_closed hc _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem decode_build (pick : T → Fin 464) {g k s} (h : C4RLive.build basicOps g k s)
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
end C4RCheck

namespace C4RLive
variable {α β : Type} [DecidableEq α] [DecidableEq β]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
inductive History (ops : α → α → Finset α) (start : Finset α) : Finset α → Prop where
  | initial : History ops start start
  | gate {s} (old : History ops start s) {a b z} (ha : a ∈ s) (hb : b ∈ s)
      (hz : z ∈ ops a b) : History ops start (insert z s)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem History.contains {ops : α → α → Finset α} {start s} (h : History ops start s) : start ⊆ s := by
  induction h with
  | initial => exact Finset.Subset.refl _
  | gate old ha hb hz ih => exact ih.trans (Finset.subset_insert _ _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kept_mono (p : α → Option β) {s t : Finset α} (h : s ⊆ t) : kept p s ⊆ kept p t := by
  intro v hv
  obtain ⟨x,hx,px⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨x,h hx,px⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kept_of {p : α → Option β} {s : Finset α} {a : α} {v : β} (ha : a ∈ s) (hp : p a = some v) :
    v ∈ kept p s := Finset.mem_biUnion.mpr ⟨a,ha,by simp [hp]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def price (p : α → Option β) (start s : Finset α) := (kept p s \ kept p start).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem face_budget {ops : α → α → Finset α} {ops' : β → β → Finset β} {p : α → Option β}
    (proj : projects p ops ops') {start hist s g g' k} (past : History ops start hist)
    (pool : s ⊆ hist) (target : p g = some g') (run : live ops g k s) :
    build ops' g' (k - zeros p s + price p start hist) (kept p start) := by
  apply past.compose proj
  apply build_mono (kept_mono p pool)
  exact project_live target proj run _ (by omega)
end C4RLive

namespace C4RCheck
open C4Base ThetaSigned
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def rowMap : Array (Fin 464) := #[87, 11, 0, 232, 42, 12, 1, 233, 57, 13, 2, 234, 45, 14, 3, 235, 22, 15, 4, 236, 254, 255, 256, 337, 25, 16, 5, 237, 257, 258, 259, 371, 6, 238, 7, 239, 260, 287, 261, 339, 265, 290, 266, 353, 292, 293, 294, 375, 8, 240, 9, 241, 262, 340, 263, 427, 267, 297, 268, 400, 366, 376, 386, 377, 17, 18, 249, 250, 19, 20, 251, 252, 269, 270, 306, 355, 271, 272, 309, 379, 280, 281, 312, 393, 282, 283, 347, 449, 313, 314, 315, 401, 368, 380, 387, 381, 10, 242, 253, 422, 264, 301, 349, 452, 273, 356, 362, 357, 369, 382, 388, 383, 284, 395, 318, 430, 426, 453, 431, 432, 399, 402, 408, 403, 370, 384, 389, 385]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def bits (x : Y) : BitVec 7 := (BitVec.ofBoolListLE (List.ofFn x)).setWidth 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bits_spec (x : Y) (i : Fin 7) : (bits x).getLsbD i.val = x i := by
  simp only [bits,BitVec.getLsbD_setWidth,decide_eq_true i.isLt,Bool.true_and,BitVec.getLsbD_ofBoolListLE]
  exact ImportedHelpers.getD_ofFn 7 x false i
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_ok : ∀ (v : Fin 128) (i : Fin 7),
  assignment (rowMap.getD v.val 0) i = (BitVec.ofNat 7 v.val).getLsbD i.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def chooseRow (x : Y) := rowMap.getD (bits x).toNat 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chooseRow_spec (x : Y) : assignment (chooseRow x)=x := by
  funext i
  have e := row_ok ⟨(bits x).toNat,(bits x).isLt⟩ i
  simpa only [chooseRow, BitVec.ofNat_toNat, BitVec.setWidth_eq, bits_spec] using e
end C4RCheck

namespace C4RCheck
open C4Base ThetaSigned C4RLive

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pin (fixed values : BitVec 7) (y : Y) : Y := fun i =>
  if fixed.getLsbD i.val then values.getLsbD i.val else y i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def faceMaskList (fixed values : BitVec 7) : List (Fin 7) → W
  | [] => BitVec.allOnes 464
  | i :: is =>
    let rest := faceMaskList fixed values is
    let column := rawInputs.getD i.val 0
    if fixed.getLsbD i.val then
      (if values.getLsbD i.val then column else neg column) &&& rest
    else rest

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def faceMask (fixed values : BitVec 7) := faceMaskList fixed values (List.finRange 7)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pickFace (f v : BitVec 7) (y : Y) := chooseRow (pin f v y)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pickFace_row (f v : BitVec 7) (y : Y) : assignment (pickFace f v y) = pin f v y := chooseRow_spec _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pickFace_inside (f v : BitVec 7) (y : Y) :
    (faceMask f v).getLsbD (pickFace f v y).val = true := by
  let r := pickFace f v y
  have val (i : Fin 7) : (rawInputs.getD i.val 0).getLsbD r.val = pin f v y i := by
    exact congrFun (pickFace_row f v y) i
  have go : ∀ is : List (Fin 7), (faceMaskList f v is).getLsbD r.val = true := by
    intro is
    induction is with
    | nil => simp only [faceMaskList,BitVec.getLsbD_allOnes,decide_eq_true r.isLt]
    | cons i is ih =>
      cases hi : f.getLsbD i.val <;> cases hv : v.getLsbD i.val <;>
        simp only [faceMaskList,hi,hv,Bool.false_eq_true,if_false,if_true,neg,BitVec.getLsbD_and,
          BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and,val,pin,ih] <;> rfl
  exact go _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem interpret_crop (f v : BitVec 7) (r : Fin 464) (w : W) :
    interpret (pickFace f v) (crop (faceMask f v) r w) = interpret (pickFace f v) w := by
  funext y
  simp only [interpret,crop_bit _ _ _ _ (pickFace f v y).isLt,pos,pickFace_inside,if_true]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem interpret_raw (f v : BitVec 7) (i : Fin 7) : interpret (pickFace f v) (rawInputs.getD i.val 0) ∈ small := by
  have eq : interpret (pickFace f v) (rawInputs.getD i.val 0) = fun y => pin f v y i := by
    funext y;exact congrFun (pickFace_row f v y) i
  rw [eq]
  unfold pin
  split
  · exact small_closed.1 _
  · exact Or.inr ⟨i,Or.inl rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem decoded_kept (f v : BitVec 7) (r : Fin 464) :
    ∀ w ∈ kept (cropOpt (faceMask f v) r) inputs.toFinset, interpret (pickFace f v) w ∈ small := by
  intro w hw
  obtain ⟨a,ha,hw⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨raw,mem,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  obtain ⟨i,hi,ei⟩ := List.getElem_of_mem mem
  have len : rawInputs.length = 7 := rfl
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem interpret_goal (f v : BitVec 7) : interpret (pickFace f v) goal = fun y => nine (pin f v y) := by
  have hg : goal = ((-1 : BitVec 232) ++ (0 : BitVec 232)) := by decide +kernel
  funext y
  have z := graph_rows (pickFace f v y)
  rw [pickFace_row] at z
  rw [hg]
  exact z.symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem face_run {f v : BitVec 7} {r : Fin 464} {g : W} (hg : cropOpt (faceMask f v) r goal = some g)
    {hist s : Finset W} {k : ℕ} (past : History basicOps inputs.toFinset hist) (pool : s ⊆ hist)
    (run : live basicOps goal k s) :
    Run small (k - zeros (cropOpt (faceMask f v) r) s + price (cropOpt (faceMask f v) r) inputs.toFinset hist)
      (fun y => nine (pin f v y)) := by
  obtain h := face_budget (mask_projects _ _) past pool hg run
  have decoded := decode_build (pickFace f v) h small_closed (decoded_kept f v r)
  unfold cropOpt wrap at hg
  split at hg
  · contradiction
  obtain rfl := Option.some.inj hg
  rcases interpret_canon (pickFace f v) (crop (faceMask f v) r goal) with h|h <;>
    rw [h,interpret_crop,interpret_goal] at decoded
  · exact decoded
  · simpa only [inv_inv] using Run_inv decoded small_closed
end C4RCheck

namespace C4RCheck
open C4Base ThetaSigned C4RLive
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
structure Face where
  fixed : BitVec 7
  values : BitVec 7
  lower : ℕ
  mask : W
  anchor : Fin 464

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Face.Valid (c : Face) : Prop := c.mask = faceMask c.fixed c.values ∧
    (∃ g, cropOpt c.mask c.anchor goal = some g) ∧
    ∀ k, Run small k (fun y => nine (pin c.fixed c.values y)) → c.lower ≤ k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def allSeen (hist : List W) := hist.toFinset ∪ inputs.toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rejects (c : Face) (k : ℕ) (ws hist : List W) : Bool :=
  let p := cropOpt c.mask c.anchor
  decide (k - zeros p ws.toFinset + price p inputs.toFinset (allSeen hist) < c.lower)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rejects_false {c : Face} (valid : c.Valid) {k ws hist}
    (past : History basicOps inputs.toFinset (allSeen hist)) (pool : ws.toFinset ⊆ allSeen hist)
    (run : live basicOps goal k ws.toFinset) : rejects c k ws hist = false := by
  obtain ⟨em,⟨g,hg⟩,bound⟩ := valid
  rw [em] at hg
  have hr := bound _ (face_run hg past pool run)
  simp only [rejects,em,decide_eq_false_iff_not,not_lt]
  exact hr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev Advice := List W → List W → List Face

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def checkChild (ad : List Face) (further : ℕ → List W → List W → Bool) (k : ℕ)
    (ws hist : List W) (extra : ℕ) (child : List W) : Bool :=
  match child with
  | [] => false
  | z :: _ => !(ws.contains z) && !(ad.any (fun c => rejects c k child (z::hist))) &&
      further extra child (z::hist)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def guided (ad : Advice) : ℕ → ℕ → List W → List W → Bool
  | 0, _, ws, _ => ws == [goal]
  | k+1, extra, ws, hist => ws == [goal] ||
    let more := checkChild (ad ws hist) (guided ad k) k ws hist
    (pairs ws).any (fun (a,b,r) => dispatch extra more a b r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem guided_complete (ad : Advice) (valid : ∀ ws hist, ∀ c ∈ ad ws hist, c.Valid)
    (n : ℕ) (ws hist : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (past : History basicOps inputs.toFinset (allSeen hist))
    (pool : ws.toFinset ⊆ allSeen hist) (h : live basicOps goal n ws.toFinset) :
    guided ad n extra ws hist = true := by
  induction n generalizing ws hist extra with
  | zero => simp [guided,singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [guided,singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have seen : allSeen (z::hist) = insert z (allSeen hist) := by simp [allSeen]
      have extended : History basicOps inputs.toFinset (allSeen (z::hist)) := seen ▸ .gate past (pool ha) (pool hb) hz
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (checkChild (ad ws hist) (guided ad k) k ws hist) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have sub : kept.toFinset ⊆ ws.toFinset := by rw [hfin,hset];exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨fun hv => hout (sub (List.mem_toFinset.mpr hv)),hnk⟩
        have hl : live basicOps goal k (z::kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd,List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) _ hop hk (by omega) (by omega) (cuts_full hl)
        have pool' : (z::kept).toFinset ⊆ allSeen (z::hist) := by
          rw [seen,List.toFinset_cons]; exact Finset.insert_subset_insert _ (sub.trans pool)
        have succ := ih _ _ (k-kept.length) hnd (by simp;omega) extended pool' hl
        have none : (ad ws hist).any (fun c => rejects c k (z::kept) (z::hist)) = false :=
          List.any_eq_false.mpr fun c hc => by rw [rejects_false (valid _ _ c hc) extended pool' hl]; decide
        have fresh : z ∉ ws := by simpa using hout
        simp [checkChild,fresh,none,succ]
      simp only [guided,Bool.or_eq_true,List.any_eq_true]
      right
      rcases hm with direct|swap
      · exact ⟨(a,b,r),direct,go hp hs hz⟩
      · exact ⟨(b,a,r),swap,go (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
end C4RCheck

namespace C4RCheck
open C4RLive
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gone (p : W → Option W) (ws : List W) := (ws.filter fun w => (p w).isNone).length
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def paid (p : W → Option W) (ws : List W) (base : List W) :=
  ((ws.filterMap p).filter (fun z => !base.contains z)).dedup.length
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def quicker (c : Face) (k : ℕ) (ws hist : List W) : Bool :=
  let p := cropOpt c.mask c.anchor
  let rem := k - gone p ws
  if c.lower ≤ rem then false else
    decide (rem + paid p hist (inputs.filterMap p) < c.lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gone_eq (p : W → Option W) {ws : List W} (hn : ws.Nodup) : gone p ws = zeros p ws.toFinset := by
  unfold gone zeros
  rw [← List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist ..))]
  congr 1
  ext a
  simp [Option.isNone_iff_eq_none]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem kept_list (p : W → Option W) (ws : List W) :
    kept p ws.toFinset = (ws.filterMap p).toFinset := by
  ext a; simp [kept,List.mem_filterMap]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem paid_eq (p : W → Option W) (hist : List W) :
    paid p hist (inputs.filterMap p) = price p inputs.toFinset (allSeen hist) := by
  let h := (hist.filterMap p).filter fun z => !(inputs.filterMap p).contains z
  change h.dedup.length = _
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup _),List.toFinset_dedup]
  unfold price allSeen
  rw [show kept p (hist.toFinset ∪ inputs.toFinset) = kept p hist.toFinset ∪ kept p inputs.toFinset by
    ext a; simp [kept, or_and_right, exists_or]]
  rw [kept_list,kept_list]
  congr 1
  ext a
  simp [h]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem quicker_eq (c : Face) (k : Nat) (ws hist : List W) (hn : ws.Nodup) :
    quicker c k ws hist = rejects c k ws hist := by
  simp only [quicker,rejects,gone_eq _ hn,paid_eq]
  split
  · symm;apply decide_eq_false
    omega
  · rfl
end C4RCheck

namespace C4RCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def limited (m : W) (r : Fin 464) (w : W) : W := (if w[r.val] then ~~~w else w) &&& m
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem limited_anchor (m : W) (r : Fin 464) (w : W) : (limited m r w)[r.val] = false := by
  cases e : w[r.val] <;> simp [limited,e]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem limited_crop (m : W) (r : Fin 464) (w : W) :
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem limited_zero (m : W) (r : Fin 464) (w : W) :
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def projectFast (m : W) (r : Fin 464) (w : W) : Option W :=
  let q := limited m r w
  if q=0 then none else some (canon q)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem projectFast_eq (m : W) (r : Fin 464) : projectFast m r = cropOpt m r := by
  funext w
  simp only [projectFast,cropOpt,wrap,limited_crop,limited_zero]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def maskedReject (c : Face) (k : Nat) (ws hist : List W) : Bool :=
  let p := projectFast c.mask c.anchor
  let rem := k - (ws.filter (fun w => limited c.mask c.anchor w == 0)).length
  if c.lower ≤ rem then false else
    decide (rem + paid p hist (inputs.filterMap p) < c.lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem masked_eq (c : Face) (k : Nat) (ws hist : List W) (hn : ws.Nodup) :
    maskedReject c k ws hist = rejects c k ws hist := by
  rw [← quicker_eq _ _ _ _ hn]
  unfold maskedReject quicker gone
  rw [←projectFast_eq]
  have columns (w : W) : (projectFast c.mask c.anchor w).isNone = (limited c.mask c.anchor w == 0) := by
    let z := limited c.mask c.anchor w
    change (if z=0 then none else some (canon z)).isNone = (z == 0)
    by_cases hz : z=0
    · rw [if_pos hz,hz];rfl
    · rw [if_neg hz];exact (beq_eq_false_iff_ne.mpr hz).symm
  simp only [columns]
end C4RCheck

namespace C4RSpeed
open C4Base ThetaSigned C4RLive C4RCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def checkChild (ad : List Face) (further : ℕ → List W → List W → Bool) (k : ℕ)
    (ws hist : List W) (extra : ℕ) (child : List W) : Bool :=
  match child with
  | [] => false
  | z :: _ => !(ws.contains z) && !(ad.any (fun c => maskedReject c k child (z::hist))) &&
      further extra child (z::hist)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def guided (ad : Advice) : ℕ → ℕ → List W → List W → Bool
  | 0, _, ws, _ => ws == [goal]
  | k+1, extra, ws, hist => ws == [goal] ||
    let more := checkChild (ad ws hist) (guided ad k) k ws hist
    (pairs ws).any (fun (a,b,r) => dispatch extra more a b r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem guided_complete (ad : Advice) (valid : ∀ ws hist, ∀ c ∈ ad ws hist, c.Valid)
    (n : ℕ) (ws hist : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (past : History basicOps inputs.toFinset (allSeen hist))
    (pool : ws.toFinset ⊆ allSeen hist) (h : live basicOps goal n ws.toFinset) :
    guided ad n extra ws hist = true := by
  induction n generalizing ws hist extra with
  | zero => simp [guided,singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [guided,singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have seen : allSeen (z::hist) = insert z (allSeen hist) := by simp [allSeen]
      have extended : History basicOps inputs.toFinset (allSeen (z::hist)) := seen ▸ .gate past (pool ha) (pool hb) hz
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (checkChild (ad ws hist) (guided ad k) k ws hist) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have sub : kept.toFinset ⊆ ws.toFinset := by rw [hfin,hset];exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨fun hv => hout (sub (List.mem_toFinset.mpr hv)),hnk⟩
        have hl : live basicOps goal k (z::kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd,List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) _ hop hk (by omega) (by omega) (cuts_full hl)
        have pool' : (z::kept).toFinset ⊆ allSeen (z::hist) := by
          rw [seen,List.toFinset_cons]; exact Finset.insert_subset_insert _ (sub.trans pool)
        have succ := ih _ _ (k-kept.length) hnd (by simp;omega) extended pool' hl
        have none : (ad ws hist).any (fun c => maskedReject c k (z::kept) (z::hist)) = false :=
          List.any_eq_false.mpr fun c hc => by rw [masked_eq _ _ _ _ hnd,rejects_false (valid _ _ c hc) extended pool' hl]; decide
        have fresh : z ∉ ws := by simpa using hout
        simp [checkChild,fresh,none,succ]
      simp only [guided,Bool.or_eq_true,List.any_eq_true]
      right
      rcases hm with direct|swap
      · exact ⟨(a,b,r),direct,go hp hs hz⟩
      · exact ⟨(b,a,r),swap,go (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
end C4RSpeed

namespace C4Lite
open C4RCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def data : Array Face := #[⟨3,0,7,0xd89e6a22796d0d0f1400467fa851341403c224911125526ab52400000ffc1c7fe0787fe00f0400007f8000000403fa24911125526ab526a0540,6⟩,
⟨20,0,7,0x7453d1a117b8c7024800450a7ffc4a4aaab9007480e20026600262cc5ffc03ffe007ffe000000000007ffc0003fff9007480e33026730262cc5,0⟩,
⟨8,0,8,0xfafedb45feed22a05f8000301940ffff9d57f1c0f881ff1c01f1fe9fd3fffffffffffffe000fc0000000003ffffffff1c0f881ff1ffff1fe9fd3,0⟩,
⟨7,0,4,0xd0124822316c0d0e1000440a285000000282241010211022a00000000ffc007fe0787fe00f040000000000000003fa241010211022b52620540,6⟩,
⟨88,0,4,0xc0980000080200008000301040c28c814780000001e00000300018c300000000007ffe000000000000003fffffff9000c001e01c06300018c3,0⟩,
⟨52,4,4,0x240000000000000800000000001140003880000001800018500a003fc00000000000003ffffff8003fffc0000038b071ccfd800018500a,1⟩,
⟨67,2,4,0xa000004000000000000000000000449009014a900000000000001f87801f0003c000007c03f803f005924c449009014a90002bf,0⟩,
⟨35,1,4,0x480000000000001000000000000000049200000a494004800000003e38000000000f0f83fff8003fc07f80c004922aa4aa49400495f800,11⟩,
⟨84,16,4,0x600100000000000000000400000007800000180001833000000001ff8001ffffc000000000000000006fc00780000018cfc18330,4⟩,
⟨41,0,4,0xa00400402a000a05100000009000d0110000140c000051400014a00000001c7fe000000000040000000003f807f3f8140d0014514a0014a0013,0⟩,
⟨74,0,4,0xc0d000008020001080003018008315001500000080e00c0050c00140000000000787fe000fc000000000007fc0ffa0c00080e00c0a50c09940,6⟩,
⟨44,0,4,0xa000840022800a043000000014044808c0081c040000300000006881100003ffe000000000fc00000000000003fff81c0488023006001c68811,0⟩,
⟨22,0,4,0x545350a0112845024800450a295802400290003080620026200000440ffc03ffe0007fe0000000000003fc00000ff8003080633026310262c40,6⟩,
⟨19,0,4,0x589a6220112905020000462b2851240002c000910124002a310000000ffc1c7fe0007fe0000000007f8000000403f800910125526a3102a0440,6⟩,
⟨32,0,7,0xe0368fc02a880e253483c098b4c4d83ffe08fffc0000ffde00fdff83f003ffffe000001ffffffffffffffffffffff8fffffffeffde00fdff83f,0⟩,
⟨64,0,7,0x1c0d80209987e1130c403f878c3c39fc7df800007ffe0fc1effc1fbff00000001ffffffffffffffffffffffffffffffffc7ffe0fc1effc1fbff,0⟩,
⟨21,0,4,0x70124121133887020000440a785040020281005400a00022600220000ffc007fe007ffe000000000007c000003f3f9005400a110227302204c5,0⟩,
⟨11,0,4,0x888c20026840080510000201800134100142040100055040150400000ffc1c7fe0787fe000040000000000000403fa04010005506ab506a0540,6⟩,
⟨28,0,4,0x244190010690020048000100140c4a488039000480020000000260cc1ffc03ffe007ffe0000000000000000003fff9000480033026730260cc1,0⟩,
⟨35,0,4,0xc0160a0028080c0514004018a0401014020024900000524a0024000000001c7fe00000000f0400007f8000000403f824911124524a0024a0000,17⟩,
⟨52,0,4,0x60128180028806000000400834c4480aaa0800740000000600006280500003ffe000000000000000007ffc0003fff8007480e23006000062805,0⟩,
⟨67,0,4,0x180c002019050103040006078810301401c0000011240240a52400000000000000787fe00f0400007f8000000403fa249011240240a52400140,6⟩,
⟨84,0,4,0x140180201180c102080005020c3c084828b8000000e200006000028c500000000007ffe000000000007ffc0003fff9007400e200006300028c5,0⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def faceAt (i : Fin 23) := data[i.val]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def buckets : Array (List (Fin 23)) := #[[0,1,2,4,6],[0,1,4,8],[],[],[],[1,9],[1],[0,1,2,5,6,12],[1],[0,1,2,3,4,5,9,14,15],[0,1],[0,1,2,4,5,6,9,15],[1],[],[],[],[0],[2],[],[],[1],[0,1,2,4,5,6,7],[0,1,2,5,11],[0,1,5,6,7],[2],[0,2,4,9],[0,1,2,5,6,7,8],[],[],[],[2,5,9],[0,1,2,5,6,7,10,11],[],[0,1,2,4,8],[1,2,7,9],[1,4],[1,2],[],[1,5],[],[0,1,2,4,8,9],[0,1,2,3,5],[],[0,1,4,5,7,8],[5,6],[0,1,2,5,9],[0,6,10],[1,2],[],[0,1,2,7,9],[],[],[4],[0,1],[0,1,2,5,7,8],[],[1,4,5,6,10,11],[0,1,5,7],[],[],[0],[0,6],[0,1,5],[1,2,4,5],[0],[4,6,8],[0,1,2,4,6,7,8],[0,2],[0,1,2,4,5,6,7,8,11],[1],[0,1,2,3,5],[0,1,2],[0,4,8],[0,1,2,4,5,6,7,8,15],[0,1,5,7,8],[0,1,2,4,6],[],[0,1,2,5,6],[0,1,2,3,5,7,9],[],[0,1,2,6,7,10],[0,7],[1],[],[],[0,1,2,4,5,6,8],[0,1,2,4,8,11],[0,1,2,4,5,7,8,11],[0,1],[1,7,9],[0,4,7,9],[0,1,2,6,7],[0,1,2,4,8,10],[],[1],[0,1,2,4,6,7,8,11],[],[],[],[2,4,5,7,9],[0,1,2,4,5,7,10,11,14],[1,2],[],[0,1,2,4,6,8,9,11,15],[0,1,2,7,9,10],[],[],[1],[],[],[0,1,7,8],[0,1,2,4,6,9,11,12],[1],[0,6,7],[],[0,1,3,5,7],[11],[0,1,2,4,5,9],[0,1,2,6,7],[0,1,2,3,5,6],[6,8],[1],[0,1,2,4,6],[0,1,2,7,8,13],[2],[0,2,4],[0,1,2,4,5,6,7,8,9,10,14,15],[0],[8],[0,1,2,4,9,15],[],[],[0,1,2,4,6],[0,1],[0,6,7,8,10],[1],[2,6,9],[0,6],[1,2,6],[],[],[],[0,1,2,4,5,7,15],[0,1,2,3,5,6,7,10],[1,5],[0],[0,1,2,5,7,8,9,14],[],[],[7],[],[0,1,2,4,10],[1,8],[0,1,2,4,8,9,10,11],[],[],[0,2,4,9],[0,1,2,4,9,11,15],[],[],[],[0,1,2,5,11],[],[0,1,2,5,6,12],[0,4],[0,5,6,7],[0,6],[4,9],[0,1,2,4,6,7,8,9],[0,1],[1],[1,8],[0,1,2,4,5,6,8],[0,1,2,3,5,7,9],[1,7],[],[],[],[0,1,2,4,5,6,7],[0,1,2,4,7,8,15],[],[11],[0,1,3,5,6,8],[0,1,2,4,6,9],[0,2,7,9],[4,8],[],[1,2],[1],[0,1,2,4,9,11],[0,1,2,4,10],[0,1,6],[],[],[],[0,2],[0,1,2,3,5],[0,2],[0],[],[0,1,2,4,6,8,14,15],[0,1,2,3,5,6],[1,5,11],[],[0,1,2,5,6],[],[],[0,1,2,9,11,14],[0,1,2,4,6,8,9],[],[],[0,1,2,4,5],[],[],[0,1,2,4,6,8,15],[1],[0,1,2,6,7,9],[1,2],[],[0,1,2,5,6,7,8,9],[5,7,9],[],[0,1,2,5,6,7,10],[],[],[],[0,7],[0,1,4,6,8],[0,2],[],[0,1,5,7],[1,2],[1,2,5,7,11],[],[],[0,1,2,7,11],[0,7,9,10],[0,1,2,7,9],[],[14],[0,1,2,4,5,6,7,8,9,15],[],[0,1,2,4,5,6,8,11],[1,4],[],[],[1,8],[1],[0,1,2,5,8,9,10,14],[0,1,2,4,5,9],[],[0,1,2,5,8],[],[0,1,2,5],[0,2,4,9,14],[1,2,5],[0,1,2,3,4,5],[0],[],[],[0,2,4,6,8,9,14,15],[1],[0,1,2,4,5,6,8,10],[0,6],[],[1],[],[0,1,2,4,7],[0,1,2,5,6],[0,1,2,5],[],[8],[0,1,2,7,11],[0,1,2,6,7,14],[],[],[0,1],[],[],[0,2,5],[0,1,2,4,6,7],[1],[],[],[0,1,2,4,5,8],[0,1,2,4,7,8,9,11,15],[7],[2],[],[],[],[0,1,2,5,8,15],[1],[0,1,2,4,6],[0,2],[0,1,2,4,5,7],[0,1,2,5],[0,2,4,6,7,9],[0,1,2,6,7,9],[1],[],[1,2,4,8],[1],[1],[0,1,2,4],[],[0,1,2,4,5,8,9],[],[0,1,2,4,6,10,14,15],[],[0,7],[0,1,2,4,5,7,9],[2,8,10,11],[0,1,2,4,5,6,8,14],[0,1,6,8],[0,1,2,5,6,7,9],[],[1,8],[0],[],[0,6,7],[1,2,5],[1],[4,11],[],[],[],[0,1],[],[0],[],[],[0,1,2,3,5,6],[0,1,2,4,5,8],[1,2],[0,1,2,6,7,9],[0,1,2],[0,1],[0,1,2,5,7,14],[0,1,5,6],[0,1,2,5,6,7],[7],[7,11],[2],[0,1,2,4,9],[0],[0,1,2,4,9],[0,1,2,5,6],[],[0,1,2,6,7,9],[],[],[5],[1],[],[0,1,2,4,6,8],[],[0,1,3,6,8],[0,1,2,5,6,7],[0,1,2,5,10,11],[],[],[],[],[0,1,2,5,7,8],[],[],[],[0,1,2,5],[0,1,2,5,7,8,9,11],[0],[0],[],[0,1,2,3,5,6],[0,1,2,5,7,11],[],[0],[0,2],[0,1,2,4],[1,4,5,8],[0,1,2,5,7,9,11],[0,1,2,3,5,6],[],[2],[0,1,2,6,7],[1,2,4,5,6,7,10,14,15],[],[0,1,4,6],[1,2],[0,2,7,9],[0,1,2,6,10],[],[],[0,1,2,7,9],[],[],[],[],[0,1,5],[],[0,1,2,5,6,10,12],[],[0],[],[0,1,2,4,5,6,8],[0,2,6],[],[],[0,1,2,4,8,11],[0,1,2,4,5,6],[],[0,1,2,5,6,7,10],[0,1,2,4,5,6,7,9,15],[],[0,1,5,7],[0,1,2,4,5,8,10,11],[],[],[0,1,2,4,5,8,9,11],[0],[],[0,1,2,4,6,8],[0,1,2,4,6,7,8],[0,1,2,4,5,6,8,9,11,14],[0,1,2,6,10],[0,6],[],[0,1],[],[],[],[],[0,1,5],[0,1,2,4,5,10,14],[9],[],[0,1,2,4,6,8,11],[],[0,1,2,6,7,14],[0,1,2,6],[0],[],[],[1],[],[],[0,2,6,9,14],[0,1,2,4,5,6,10],[0,1,2,4,6,8],[0,1,2,5,7,8,12],[2,11],[0,1,2,4,8,11],[],[0],[0,2],[0,1,2,11,14,15],[1,2],[0,1,2,4,6,10],[1],[],[0,1,2,3,5,7],[],[0,6,8,10],[1],[0,1,6,8],[0,1,2,4,7,8],[0,1,2,5,7,9],[5],[0,2],[0,1,2,4,6,7,8,15],[],[],[1],[0,1,5,11],[1,8],[],[0,1,4,5,6,8,9],[0,1],[0,1,2,5,6,7,9],[0,1,2,4,5,6,7],[0,1,2,4,5,6,8],[0],[],[0],[0,1,2,5,6,9],[0,1,2,4,10,15],[1,4],[],[1],[1,2],[0],[0,1,2,4,8],[0,1,2,6,10],[0,1,2,4,9],[],[5,11],[0,1,2,5,7,8,14],[1,2,4,10],[0,7],[0,1,2,5,9],[5,9],[0,1,2,4,5,6,8],[],[0,1,2,5,6,7,9,11],[0,1,4,6,8],[],[],[0,1,4,6,8],[1,6,8],[0,1,2,4,5,7,11],[1,5],[0,1,2,6,7,8,10],[],[0],[0,1,6],[0],[0,1,2,4,5,10],[],[],[],[0,1,2,4,5,6,7,10,15],[],[2,6],[0],[0,1,2,5,6,7,10],[0,1,2,3,5],[],[0,1,2,4,7,15],[0,1,6,8],[1],[0,1],[],[0,1,4,6,7],[0,1,5,7],[0,1,2,5,7,9,14],[0,1,2,4,5,7,8],[],[0,1,2,4,6],[],[],[0,1,2,4,7,8,13],[],[],[],[],[0,7],[],[],[0],[1,6],[0],[0,1,2,5,9],[2],[0],[],[0,1,2,4,6,10],[],[0,4,6,7],[14],[],[0,1,2,6,7,11],[0,1,2,6,7],[],[0,1,2,5,6,9,10,11],[0,1,2,4,5,6,8],[0,1,4,9,10,11,14,15],[0,1],[1],[],[],[0,1,2,3,5,8,10],[],[0,1,2,5,7],[0,1,2,3,4,6,9,11],[0],[0,1,2,4,8,15],[],[2],[],[],[0,1,2,5,11],[0,1,6,10],[],[],[0,1,2,3,5,6],[1],[0,1,2,4,6,7,8,10,11,15],[],[],[0,1,2,4,9,10,11],[],[0,1,2,3,4,5,6,9,10],[],[],[],[],[],[0,1,2,4,5,8,9],[],[],[0,1,2,4,5,7,13],[],[0,1,2,5,6,11],[0,2,6,7,9],[0,1,2,5,8],[4],[],[],[],[],[],[0,7],[0,5,7],[0,1,2,3,4,6],[],[0,1,2,7,9,10,11],[0,1,2,4,6,8,15],[0,1,2,4,5,7,8,15],[0,1,2,4,6,7,9],[0,5,7,9],[],[0,1,5],[0,1,2,5,7,9,14,15],[0,2,8],[],[0,7],[0,1,2,6,7],[],[0,2,7,10],[1],[],[],[],[0,1,2,5,6,10,14],[1],[0,1,2,4,5,6,7,8],[0,1,6],[0],[0,1,2,4,5,6,11,15],[0,7],[],[1,2,7,8,11],[],[],[],[0,7],[0,1,2,4,5,8],[0,1,3,5,6],[1,8],[0,1,2,4,6],[2,7],[1],[0,1,4,6,8],[],[0,1],[],[8,9],[],[0,2,4,6],[0,1,2,5,7],[],[1,8],[],[],[0,1,2,3,4,5,7,8],[],[0,2],[],[],[],[0,1,6,8],[7],[0,1,2,4,6,8,10],[],[1,2],[],[0,7],[1],[0,10],[0,6],[0],[],[0,1,2,4,5,6,8],[1],[],[],[],[5,9],[0,1,2,4,5,8,9,14],[0,1,2,5,7,8,9],[],[0,1,2],[0,1,2,4,5,6,7,8,9,11],[0,1,2,3,5,6,10],[0,1,2,4,6,15],[0,1,2,4,5,7,8],[],[],[0,1,2,3,6,7,10],[],[0,1,2,5,6,7,8],[],[],[],[],[],[],[],[],[],[],[0,1,2,4,5,6],[],[],[],[0,1,2,3,5],[0,2,6,7,10],[],[],[0],[1,2],[0],[],[9],[],[0,1,2,6,7,9],[],[],[0,1,2,5],[1,2],[0,1,2,5,11],[0,2,7,9,10],[],[],[0,1,2,5,7,8],[0,1,2,7],[0,1,2,4,5,9,15],[],[0,1,2,5,11],[1],[],[0,1,2,6,7,9,10],[0,1,2,5,6,7,8],[0,1,2,5,11],[],[],[],[0,1,2,4,7,9],[],[0],[0,1,2,4,6],[1],[],[5],[0,1,2,4,5,6,7,9],[0,1,2,4,7,8],[],[],[],[],[],[],[0],[],[0,1],[],[0,1,2,3,5],[],[0,1,2,3,4,5,6,7,9],[0,1,2,4,8,9,15],[0,1],[0,1,2,4,9],[0,1,2,4,5,6,7,8,11,14,15],[6,10],[],[0,6,7],[1],[0,1,2,4,8,14,15],[10],[0,1,2,7,9],[0,1,2,6,7,9,11,12],[0,4,8],[],[],[],[],[0,1,2,4,7,8,15],[0,1,2,5,6],[],[2],[0,1,2,4,6],[0,1,2,4,5,6,7,8,14,15],[0,1,2,4,6,7,9],[],[0,7],[1,5],[],[],[],[],[],[],[],[2],[0,1,2,5,7,9],[0,1,2,4,6,10],[5],[1,2,5,11],[0],[0,2],[],[0,1,2,4,5,6,8,10],[0],[0,1,2,4,5,7,8,9],[],[7,9],[],[0,1,2,4,5,8],[],[1,5],[0,1,2,4,8,10],[],[0,1,2,5],[0,1,2,4,5,7,8],[0,2,7],[],[0,1,2,3,5],[],[1,2],[0,1,2,6],[],[0,1],[0,1,2,4,5,7,9],[],[],[0,1,2,4,5,7,8,14],[6],[0,1,2,3,5,6,7,8,9,11,14],[2],[],[],[0,1,2,4,5,7,9,14],[0,7],[],[0,4,7,8,9],[],[],[0,6],[0,1,2,3,5,6,9,11],[10],[0,1,4,5,6,7,8],[],[],[0,1,2,4,8,10],[1,2,8,9,14],[0,2],[0],[],[],[0,1,4,8,11],[0,1,2,4,8],[0,1],[],[],[0,1,4,6,8],[0],[0,1,2,4,6,7,9],[0,9],[1],[1,2,5,9],[0,1,2,5,11],[0,2,6,10],[],[0,1,6],[0,2,7,9],[0,1,2,4,5,6,7,9,11],[],[0,1,5,8,11],[0,1,2,4,6,10],[4],[0,1,6],[],[],[2,10],[],[1,5,8],[],[0,1,2,4,5,7,8,9],[0,1,2,3,5,6,7,9,14],[],[0,1,2,3,5],[],[0,1,6,8],[0,1,2,4,7,9,10,11],[],[],[7],[0,1,2,4,8],[0,1,2,3,4,5,6,8,10],[0,1,2,4,9],[],[0,1,2,4,8],[],[],[0,1,2,3,5,7,8,13],[0,1,2,6,12],[],[2],[0,1,2,3,5,6],[],[0,1,5],[5,7],[0,6,7,10],[4],[0],[0,1,6],[0,4],[1,5,8,11],[0],[],[0,7],[1,5],[0,1,2,3,5,9],[0],[],[0,1,2,6,7,9],[0,1,4],[],[],[],[2],[],[],[1,8],[],[0,1,2,4,5,6,7,10],[0,1,2,4,5,6,8,11,15],[0,1,2,4,6],[],[],[0],[0,1,2,4,6,7,8],[],[0,1,2,5,6,7,9,14],[],[0,1,2,4,5,8,11],[0,1],[1,2,4,5,8,11],[],[0,1],[0,4,6,7],[0,1,2,6,7,9],[],[2,5],[],[0],[1,5,8],[2,14,15],[0,1,2,5,8,14],[0,1,2,4,8,9],[0,1,4,6,8],[0,2],[],[1,2],[1],[0],[0,1,2,4,5,8,9,11,15],[0,1,2,3,4,5,7,9,10],[],[0,1,2,3,4,5,6],[0,1,2,6,7],[0,1,5,8],[1,2,4,8],[0],[],[],[0,1,5,6,7],[0,1],[0,4,6,7],[1,2,4,8],[],[15],[0],[],[],[],[0,1],[0,1,2,5,8],[0,1,2,4,6,7,8,10],[0],[0,1,2,5,11],[0,1,2,4,6],[0],[0,1,2,4,5,8,10,11],[],[0],[0,1,2,4,5,8,10,11],[0,1,2,6,7],[],[],[0,1,2,5,6,7,10],[],[],[],[],[0,1,2,3,4,5,7,8,9],[0],[1,8],[2],[0,1,2,4,6,7,8,9,10],[],[0,1,5],[0,1,2,5,6,9],[0,1,2,5,8,10,11,14],[],[1,5],[],[0,1,2,5,6,7,8,9,14],[6,8],[0],[0,1,2,4,5,6,11]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def code (ws : List W) := ws.foldl (fun a w=>a+w.toNat % 65521) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def advice (ws hist : List W) : List Face := (buckets.getD ((code ws+37*code hist)%1021) []).map faceAt
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem advice_ok (facts : ∀i,(faceAt i).Valid) (ws hist : List W) : ∀ c∈advice ws hist,c.Valid := by
  rintro c hc;obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc;exact facts i
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rootPair (i : Nat) : Bool := match (pairs inputs)[i]? with
  | none => false
  | some (a,b,r) => dispatch 4 (C4RSpeed.checkChild (advice inputs []) (C4RSpeed.guided advice 9) 9 inputs []) a b r
end C4Lite

namespace C4Small
open C4RCheck C4RLive ThetaSigned
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def wordBit (r : Fin 464) (w : W) := w[r.val]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def representsPool {T} (pick : Fin 464 → T) (P : Set (Wire T)) (S : Finset W) :=
  ∀ f ∈ P, ∃ w, (canon w=0 ∨ canon w ∈ S) ∧ ∀ r, f (pick r)=wordBit r w
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def possibleIn (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem singletonPossible {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possibleIn ws x ∧ possibleIn ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possibleIn]
  · simp only [possibleIn, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem anyBuild {T : Type} (pick : Fin 464 → T) {target : Wire T}
    (agrees : ∀ r, target (pick r) = wordBit r goal) {P : Set (Wire T)} {k : Nat} (h : Run P k target) :
    ∀ av, representsPool pick P av → C4RLive.build basicOps goal k av := by
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def columnPick {n : Nat} (cols : List W) (r : Fin 464) (i : Fin n) := wordBit r (cols.getD i.val 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def signals (cols : List W) := cols.map canon
set_option maxRecDepth 100000 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def critical (ws : List W) (sites : List (Fin 232)) : Bool :=
  ws.all fun a => sites.any fun i => ws.all fun b => (b.getLsbD i.val == b.getLsbD (232+i.val)) || b == a
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_required {ws : List W} {sites} {k s} (crit : critical ws sites=true)
    (hs : s⊆ws.toFinset) (hr : live basicOps goal k s) : s=ws.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  obtain ⟨i,_,all⟩ := List.any_eq_true.mp (List.all_eq_true.mp crit a (List.mem_toFinset.mp ha))
  obtain ⟨b,hb,hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) hr
  have eq := List.all_eq_true.mp all _ (List.mem_toFinset.mp (hs hb))
  simp only [Bool.or_eq_true,beq_iff_eq] at eq
  exact eq.resolve_left hd ▸ hb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeFunc {n} (es : List (Fin n × Fin n)) (x : Fin n → Bool) := es.any fun e => x e.1 && x e.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def edgeWord {n} (es : List (Fin n × Fin n)) (cols : List W) : W :=
  es.foldr (fun e out => ((cols.getD e.1.val 0) &&& (cols.getD e.2.val 0)) ||| out) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem edgeRows {n} (es : List (Fin n × Fin n)) (cols : List W) (r : Fin 464) :
    edgeFunc es (columnPick cols r) = wordBit r (edgeWord es cols) := by
  induction es with
  | nil => simp [edgeFunc,edgeWord,wordBit]
  | cons e t ih =>
    change (columnPick cols r e.1 && columnPick cols r e.2 || edgeFunc t (columnPick cols r)) =
      wordBit r (((cols.getD e.1.val 0) &&& (cols.getD e.2.val 0)) ||| edgeWord t cols)
    simp only [ih,columnPick,wordBit,BitVec.getElem_or,BitVec.getElem_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem graph_lower {n cap extra k : Nat} (es : List (Fin n × Fin n)) (cols : List W) (sites : List (Fin 232))
    (len : cols.length=n) (ok : edgeWord es cols=goal) (crit : critical (signals cols) sites=true)
    (nodup : (signals cols).Nodup) (room : extra+(signals cols).length=cap+1)
    (scan : optimized cap extra (signals cols) = false)
    (run : Run (SignedCofactor.literals n) k (edgeFunc es)) : cap+1 ≤ k := by
  by_contra! small
  have agrees (r : Fin 464) : edgeFunc es (columnPick cols r) = wordBit r goal := by rw [edgeRows,ok]
  obtain ⟨s,hs,hr⟩ := compress (anyBuild _ agrees run _ (columnGood cols len))
  rw [all_required crit hs hr] at hr
  have enough (t : Nat) (le : k≤t) : live basicOps goal t (signals cols).toFinset := by
    induction le with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  have yes := optimized_complete cap (signals cols) extra nodup room (enough cap (by omega))
  rw [scan] at yes
  contradiction
end C4Small

namespace C4Small.Leaf0
open C4Small C4RCheck ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def es : List (Fin 5 × Fin 5) := [(0, 2), (0, 3), (1, 3), (1, 4), (2, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cols : List W := [0x9fdebe96753d7f9fcf4797e96fffc94c4d978adc1243e73f76be7852f3e020416080c308a089c09803102602003301184c18c02070349c380073, 0x3dbf723bf2ffa5c837fa6ba7269ebfc7fba78763c9f61af58bdc8aae7c42408e4209021800488010166061a85442a48200158000cc85dc000e7c, 0xf73357f53f7f5cbfedceb09cf38bc4bbdf4c7efcb71e899d50ef15cf9108ce0c0a1000a248003a045846812884442c02a026360509806001cf80, 0x67eebf238ed7dfa5b4fdfe7f0fffa166e033a616603d7fe37df5e1f4261815009c500c040b2414016084985081840a649140245e034021c1f000, 0x4ef7d7cbfd4fab639a1b29fff1aa3ff9d7df7921efcce810dbf9ff09483100300402e844b22104e980091e010110135009880898127a01fe0000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 6 2 (signals cols)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower {k} (hr : Run (literals 5) k (edgeFunc es)) : 7 ≤ k :=
  graph_lower (cap:=6) (extra:=2) es cols [7, 13, 0, 1, 3] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) scan hr
end C4Small.Leaf0

namespace C4Small.Leaf1
open C4Small C4RCheck ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def es : List (Fin 6 × Fin 6) := [(0, 1), (2, 3), (0, 4), (2, 4), (1, 5), (3, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cols : List W := [0x7fe00bf047d607f5013f806ff8223faedea87f16055dbf1e38494f83c77f807381870001f0021f0000f8003f800e003820304cae0e38000781c3, 0xf768245a7ed6a04cb9d9a418129df4ec0de7ef01af97f7224bc7389e4d8060047038d6080500c08090005dc029209787080b93500001c7381e0c, 0xd2db6695ab2d20de0eac75c9a7729255859f12ccd9e6de4fc092913ff0088824558100a0464626241815620b440c9810005046ce0fc000001ff0, 0x8fc6de0ce0635c3d6684cfc4ad8651f0737db9ae0bf8fa8495f83fe490a140c208501b4d090090c0c02081500271238dac09b8300001f83fe000, 0xb1b18db3611f33831c6333236bf1ce33f343485e57ff1cf921ffc2092200010820609c40019800db0302898033b142c01e0fb110f001ffc00000, 0x8f8fb38e9f00fe70fde70f1f188fc18830c0c1e3f3ffe0ffff24245008420230828200b212ed231d0d5c02238004405052b04480fffe00000000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 7 2 (signals cols)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower {k} (hr : Run (literals 6) k (edgeFunc es)) : 8 ≤ k :=
  graph_lower (cap:=7) (extra:=2) es cols [2, 0, 13, 4, 1, 3] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) scan hr
end C4Small.Leaf1

namespace C4Small.Leaf2
open C4Small C4RCheck ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def es : List (Fin 4 × Fin 4) := [(0, 2), (0, 3), (1, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cols : List W := [0xffffffffffffffffffffffffffffffffffffffffffdfd7fe57d3e7f57bffffffffffffffffffffffffffffffffffffffffff20340081500c601b, 0xba79cbfd2e5daadc00000000000000000000000000000000000000000044a43a34101b60dc, 0xffffffffffffffffffffffffffffffffffffffffff3ff45d4fd633bce9000000000000000000000000000000000000000000c20ad2260ea28ce0, 0xed7ffbbcedfcef960000000000000000000000000000000000000000001240840a88c08f00]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 3 0 (signals cols)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower {k} (hr : Run (literals 4) k (edgeFunc es)) : 4 ≤ k :=
  graph_lower (cap:=3) (extra:=0) es cols [5, 9, 0, 1] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) scan hr
end C4Small.Leaf2

namespace C4Small.Leaf3
open C4Small C4RCheck ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def es : List (Fin 6 × Fin 6) := [(0, 1), (2, 4), (1, 5), (3, 5), (4, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cols : List W := [0x7a023fb020ffe829ff437f8447f9a1f647fc17c85d6ff8e0f0f0f1c737700c3c000c3f8040fe083f8007f000f007e063839d6fb8e0707070c31, 0x48a93fbb5a2106b26c3e62453bf2b9cef3fdc137a7e7fc9279393935d708a01c3b0230068160144800bb8095e05b81c0848221000038383831c6, 0x4d64d4c699a3538dd68ea38ee5296f46de8aa9ddd8fb5bf012527fc1f848f6c040582107cd93ca6242c40d29ce4c020134d87b5bf000003fc1f8, 0xac1c7211b758ceedc19790bb0ca7e0f3afa665f893fc7124bfc03ffe008458280db3782c85cb1483a902a021b0bf9565e491fc70003fc03ffe00, 0x9b63b24f8fc6399c326d8d9fe399e7319e9e1ac84eff9a493fffd240a81000322e23c0301000158d2d1300c63191d800c8078480003fffc00000, 0xf71f4dc07f7df87bf1e37c791f8710f341807e03fa7fe3ffe4a4a4ab04610340804c04416a10623050044f000600000a01280203ffc000000000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 6 1 (signals cols)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower {k} (hr : Run (literals 6) k (edgeFunc es)) : 7 ≤ k :=
  graph_lower (cap:=6) (extra:=1) es cols [1, 0, 22, 39, 3, 2] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) scan hr
end C4Small.Leaf3

namespace C4Lite
open C4RCheck ThetaSigned SignedCofactor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def insertVars {n : Nat} (idx : Fin 7 → Option (Fin n)) (x : Fin n → Bool) (v : Fin 7) :=
  match idx v with
  | none => false
  | some i => x i
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pullSmall {n : Nat} (idx : Fin 7 → Option (Fin n)) (f : Wire C4Base.Y) (h : f ∈ C4Base.small) :
    (fun x => f (insertVars idx x)) ∈ literals n := by
  rcases h with ⟨b,rfl⟩|⟨i,rfl|rfl⟩
  · exact Or.inl ⟨b,rfl⟩
  · cases e : idx i with
    | none => exact Or.inl ⟨false,funext fun x => by simp [insertVars,e,ThetaSigned.bit]⟩
    | some j => exact Or.inr ⟨j,Or.inl (funext fun x => by simp [insertVars,e])⟩
  · cases e : idx i with
    | none => exact Or.inl ⟨true,funext fun x => by simp [insertVars,e,inv,ThetaSigned.bit]⟩
    | some j => exact Or.inr ⟨j,Or.inr (funext fun x => by simp [insertVars,e,inv])⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector0 : Fin 7 → Option (Fin 5) := ![none,none,some 0,some 1,some 2,some 3,some 4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok0 : (faceAt 0).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector0) (literals 5) (pullSmall selector0)
  have eq : ∀ x,C4Base.nine (pin (faceAt 0).fixed (faceAt 0).values (insertVars selector0 x))=C4Small.edgeFunc C4Small.Leaf0.es x := by decide +kernel
  exact C4Small.Leaf0.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector1 : Fin 7 → Option (Fin 5) := ![some 0,some 2,none,some 1,none,some 3,some 4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok1 : (faceAt 1).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector1) (literals 5) (pullSmall selector1)
  have eq : ∀ x,C4Base.nine (pin (faceAt 1).fixed (faceAt 1).values (insertVars selector1 x))=C4Small.edgeFunc C4Small.Leaf0.es x := by decide +kernel
  exact C4Small.Leaf0.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector2 : Fin 7 → Option (Fin 6) := ![some 0,some 1,some 2,none,some 3,some 4,some 5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok2 : (faceAt 2).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector2) (literals 6) (pullSmall selector2)
  have eq : ∀ x,C4Base.nine (pin (faceAt 2).fixed (faceAt 2).values (insertVars selector2 x))=C4Small.edgeFunc C4Small.Leaf1.es x := by decide +kernel
  exact C4Small.Leaf1.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector3 : Fin 7 → Option (Fin 4) := ![none,none,none,some 0,some 1,some 2,some 3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3 : (faceAt 3).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector3) (literals 4) (pullSmall selector3)
  have eq : ∀ x,C4Base.nine (pin (faceAt 3).fixed (faceAt 3).values (insertVars selector3 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector4 : Fin 7 → Option (Fin 4) := ![some 0,some 2,some 1,none,none,some 3,none]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4 : (faceAt 4).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector4) (literals 4) (pullSmall selector4)
  have eq : ∀ x,C4Base.nine (pin (faceAt 4).fixed (faceAt 4).values (insertVars selector4 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector5 : Fin 7 → Option (Fin 4) := ![some 1,some 3,none,some 2,none,none,some 0]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5 : (faceAt 5).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector5) (literals 4) (pullSmall selector5)
  have eq : ∀ x,C4Base.nine (pin (faceAt 5).fixed (faceAt 5).values (insertVars selector5 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector6 : Fin 7 → Option (Fin 4) := ![none,none,some 0,some 1,some 2,some 3,none]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6 : (faceAt 6).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector6) (literals 4) (pullSmall selector6)
  have eq : ∀ x,C4Base.nine (pin (faceAt 6).fixed (faceAt 6).values (insertVars selector6 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector7 : Fin 7 → Option (Fin 4) := ![none,none,some 1,some 2,some 3,none,some 0]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7 : (faceAt 7).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector7) (literals 4) (pullSmall selector7)
  have eq : ∀ x,C4Base.nine (pin (faceAt 7).fixed (faceAt 7).values (insertVars selector7 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector8 : Fin 7 → Option (Fin 4) := ![some 0,some 2,none,some 1,none,some 3,none]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8 : (faceAt 8).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector8) (literals 4) (pullSmall selector8)
  have eq : ∀ x,C4Base.nine (pin (faceAt 8).fixed (faceAt 8).values (insertVars selector8 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector9 : Fin 7 → Option (Fin 4) := ![none,some 1,some 2,none,some 0,none,some 3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok9 : (faceAt 9).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector9) (literals 4) (pullSmall selector9)
  have eq : ∀ x,C4Base.nine (pin (faceAt 9).fixed (faceAt 9).values (insertVars selector9 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector10 : Fin 7 → Option (Fin 4) := ![some 1,none,some 0,none,some 2,some 3,none]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok10 : (faceAt 10).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector10) (literals 4) (pullSmall selector10)
  have eq : ∀ x,C4Base.nine (pin (faceAt 10).fixed (faceAt 10).values (insertVars selector10 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector11 : Fin 7 → Option (Fin 4) := ![some 1,some 3,none,none,some 2,none,some 0]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok11 : (faceAt 11).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector11) (literals 4) (pullSmall selector11)
  have eq : ∀ x,C4Base.nine (pin (faceAt 11).fixed (faceAt 11).values (insertVars selector11 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector12 : Fin 7 → Option (Fin 4) := ![some 1,none,none,some 0,none,some 3,some 2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok12 : (faceAt 12).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector12) (literals 4) (pullSmall selector12)
  have eq : ∀ x,C4Base.nine (pin (faceAt 12).fixed (faceAt 12).values (insertVars selector12 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector13 : Fin 7 → Option (Fin 4) := ![none,none,some 1,some 0,none,some 3,some 2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok13 : (faceAt 13).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector13) (literals 4) (pullSmall selector13)
  have eq : ∀ x,C4Base.nine (pin (faceAt 13).fixed (faceAt 13).values (insertVars selector13 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector14 : Fin 7 → Option (Fin 6) := ![some 0,some 1,some 2,some 3,some 4,none,some 5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok14 : (faceAt 14).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector14) (literals 6) (pullSmall selector14)
  have eq : ∀ x,C4Base.nine (pin (faceAt 14).fixed (faceAt 14).values (insertVars selector14 x))=C4Small.edgeFunc C4Small.Leaf3.es x := by decide +kernel
  exact C4Small.Leaf3.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector15 : Fin 7 → Option (Fin 6) := ![some 1,some 0,some 4,some 3,some 2,some 5,none]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok15 : (faceAt 15).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector15) (literals 6) (pullSmall selector15)
  have eq : ∀ x,C4Base.nine (pin (faceAt 15).fixed (faceAt 15).values (insertVars selector15 x))=C4Small.edgeFunc C4Small.Leaf3.es x := by decide +kernel
  exact C4Small.Leaf3.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector16 : Fin 7 → Option (Fin 4) := ![none,some 1,none,some 0,none,some 2,some 3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok16 : (faceAt 16).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector16) (literals 4) (pullSmall selector16)
  have eq : ∀ x,C4Base.nine (pin (faceAt 16).fixed (faceAt 16).values (insertVars selector16 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector17 : Fin 7 → Option (Fin 4) := ![none,none,some 0,none,some 3,some 2,some 1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok17 : (faceAt 17).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector17) (literals 4) (pullSmall selector17)
  have eq : ∀ x,C4Base.nine (pin (faceAt 17).fixed (faceAt 17).values (insertVars selector17 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector18 : Fin 7 → Option (Fin 4) := ![some 0,some 3,none,none,none,some 2,some 1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok18 : (faceAt 18).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector18) (literals 4) (pullSmall selector18)
  have eq : ∀ x,C4Base.nine (pin (faceAt 18).fixed (faceAt 18).values (insertVars selector18 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector19 : Fin 7 → Option (Fin 4) := ![none,none,some 1,some 2,some 3,none,some 0]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok19 : (faceAt 19).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector19) (literals 4) (pullSmall selector19)
  have eq : ∀ x,C4Base.nine (pin (faceAt 19).fixed (faceAt 19).values (insertVars selector19 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector20 : Fin 7 → Option (Fin 4) := ![some 1,some 3,none,some 2,none,none,some 0]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok20 : (faceAt 20).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector20) (literals 4) (pullSmall selector20)
  have eq : ∀ x,C4Base.nine (pin (faceAt 20).fixed (faceAt 20).values (insertVars selector20 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector21 : Fin 7 → Option (Fin 4) := ![none,none,some 0,some 1,some 2,some 3,none]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok21 : (faceAt 21).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector21) (literals 4) (pullSmall selector21)
  have eq : ∀ x,C4Base.nine (pin (faceAt 21).fixed (faceAt 21).values (insertVars selector21 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def selector22 : Fin 7 → Option (Fin 4) := ![some 0,some 2,none,some 1,none,some 3,none]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok22 : (faceAt 22).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars selector22) (literals 4) (pullSmall selector22)
  have eq : ∀ x,C4Base.nine (pin (faceAt 22).fixed (faceAt 22).values (insertVars selector22 x))=C4Small.edgeFunc C4Small.Leaf2.es x := by decide +kernel
  exact C4Small.Leaf2.lower ((funext eq) ▸ run)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid (i : Fin 23) : (faceAt i).Valid := by
  fin_cases i
  · exact ok0
  · exact ok1
  · exact ok2
  · exact ok3
  · exact ok4
  · exact ok5
  · exact ok6
  · exact ok7
  · exact ok8
  · exact ok9
  · exact ok10
  · exact ok11
  · exact ok12
  · exact ok13
  · exact ok14
  · exact ok15
  · exact ok16
  · exact ok17
  · exact ok18
  · exact ok19
  · exact ok20
  · exact ok21
  · exact ok22
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_0 : rootPair 0 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_1 : rootPair 1 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_2 : rootPair 2 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_3 : rootPair 3 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_4 : rootPair 4 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_5 : rootPair 5 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_6 : rootPair 6 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_7 : rootPair 7 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_8 : rootPair 8 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_9 : rootPair 9 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_10 : rootPair 10 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_11 : rootPair 11 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_12 : rootPair 12 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_13 : rootPair 13 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_14 : rootPair 14 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_15 : rootPair 15 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_16 : rootPair 16 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_17 : rootPair 17 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_18 : rootPair 18 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_19 : rootPair 19 = false := by decide +kernel
end C4Lite

namespace C4Lite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_20 : rootPair 20 = false := by decide +kernel
end C4Lite

namespace C4Lite
open C4RCheck C4Base ThetaSigned C4RLive PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem roots_close (roots : ∀ i : Fin 21, rootPair i.val = false) : C4RSpeed.guided advice 10 4 inputs [] = false := by
  have len : (pairs inputs).length = 21 := by decide
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [C4RSpeed.guided,Bool.or_eq_true] at h
  rcases h with stop|step
  · exact (by decide : (inputs == [goal]) ≠ true) stop
  · obtain ⟨p,hp,ok⟩ := List.any_eq_true.mp step
    obtain ⟨i,hi⟩ := List.get_of_mem hp
    have no := roots (Fin.cast len i)
    simp only [Fin.val_cast,rootPair,List.getElem?_eq_getElem i.isLt] at no
    rw [←hi] at ok
    exact Bool.noConfusion (no.symm.trans ok)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_roots : ∀ i : Fin 21, rootPair i.val = false := by
  intro i
  fin_cases i
  · exact root_0
  · exact root_1
  · exact root_2
  · exact root_3
  · exact root_4
  · exact root_5
  · exact root_6
  · exact root_7
  · exact root_8
  · exact root_9
  · exact root_10
  · exact root_11
  · exact root_12
  · exact root_13
  · exact root_14
  · exact root_15
  · exact root_16
  · exact root_17
  · exact root_18
  · exact root_19
  · exact root_20

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signed_lower {k} (hr : Run small k nine) : 11 ≤ k := by
  by_contra! bad
  have liveK := inputLive hr
  have live_more : ∀ t, k ≤ t → live basicOps goal t inputs.toFinset := by
    intro t bound
    induction bound with
    | refl => exact liveK
    | step _ ih => exact Or.inl ih
  have initial : allSeen [] = inputs.toFinset := by simp [allSeen]
  have cert := C4RSpeed.guided_complete advice (advice_ok valid) 10 inputs [] 4 (by decide) (by decide)
    (initial ▸ History.initial) (initial ▸ Finset.Subset.refl _) (live_more 10 (by omega))
  exact Bool.noConfusion (cert.symm.trans (roots_close all_roots))
end C4Lite

namespace P2828Raw
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower14 {k : Nat} (run : ThetaSigned.Run P2828.small k P2828.nine) : 14 ≤ k :=
  signed_fourteen (allValid (fun _ h => C4Lite.signed_lower h)) run
end P2828Raw

namespace P2828Lollipop
open P2828Check P2828Minor P2828Live P2828Generic P2828Truth ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cols : List W := [0x36f1a4e5d549afd348cddb249ef548addd512b7748816ef72c6ad94b713d49936e9e25975aac4acf67316b2dac49cfb594adadac8aadfae4258d2c85504bb9d31fc11dd515de116da5ba25e84bfc9571c2278e719c67200fff0007ff800fff0003ff800fff0003ffc001fffc00000000000000fffe0003fff0003fff8001fffc000fffc000fffe0007ffe0007fff0000000000007fe00ff803fe00ff807f80ff00fe00fe0ab8e001c738ce339,0x1a76af6afd3fd6f5db56ed49aa33df36fea269115bbab77b55ba47d5b754dea5baa6ea8bc69d8d752b5aa57695dad693bd4afed77e9d2a6e4ab7543f4c950ac564d26c4e264727b7ae8a4b7ffe2c3e7ee5e09292bf87c000000000000000000003fffff0000003fffffe00000000000fffe00000000000000000000000000000000fffffff00000007ffffff80000000000ffe000000000000000000007fff0000ffff000c3f60f000000fc3e,0x2d7b3db369929a5afda77692d45a91a444f7cdbe6ddcdbbd9ad36aa6d9a8eb49d4cb532d6cd6d9da35acd6bb5a6d69daebeba49dd4d753b4935a994a61268d268964b6fb7c8a4adaf5dfff28945159ff0849257e1ff80000000007fffff0000003fffffffffffc000000000000000000000000000000000000003ffffffe0000000ffffffffffffff800000000000000000000000000000003ffff00007fffffff0000000cff8000003f0ffc0,0xe3dcfdc7e24e49c91c4471fe77cfbc76f3b71db8eef1ddee31c74f8e3ce8f8f1f13bc4ef719ee67b9cfe7239c8e731cce7338e667199cc71c63e2138638de7f3188c76fb7efff030712924d26861fb67093f07fe4815ff0000007fffffffffffc000000000000000000000000000000000000fffffffc0000003ffffffffffffff00000000000000000000000000000000000007ffff00003ffffffff8000000000000003c00001f83ff0000,0x305e09e04fc7f8ff1ff87fe3f87f1df877c3fe1ff0f7e1ef03ff873f0df0f3f1e7e3df8f781ef07bc1f707dc1f707de0f383cf07b81ee0f9e07cfc7c0bc0efb7ddfff870390c8c1c381d1c7239187fdb9f03ffa4092a9ffffffff800000000000000000000000000000000000007fff0000000ffffffffffffffc00000000000000000000000000000000000000000007ff000007ffffffffc000000000000000000000003000f01ffc000000,0x3f9ff1ff8ff8ff1fe1ff87fcff9fe1ff87fc7fe3ff07fe0ffc1ff83ff1ff03fe07fc1ff07fe0ff83fe07f81fe07f81ff03fc0ff83fe0ff01ff80ff9ff3fff0381e0f0783c1f0f0e0c1e1e183c1e39feddffe48495254200000000000000000000000000000000000000000000007ffffffffff00000000000000000000000000000000000000000000000000000000007fffffff8000000000000000000000000000000000000ffe000000000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def target := truth 6 0xfffefffafcfccc00
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def base := signals cols
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem live_root {k} (h : Run (literals 6) k target) : live basicOps goal k base.toFinset :=
  table_live cols [37,16,27,1,2,0] (by decide +kernel) (by decide +kernel) (by decide +kernel) h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face0 : Minor := ⟨7,0x90e5b1a2ab6502cb73224db610ab75222aed488b77e9108d39526b48ec2b66c9161da68a553b53098ce94d253b6304a6b5252537552051bda72d37aafb4462ce03ee22aea21ee925a45da17b4036a8e3dd8718e6398dff000fff8007ff000fffc007ff000fffc003ffe0003ffffffffffffff0001fffc000fffc0007ffe0003fff0003fff0001fff8001fff8000ffffffffffff801ff007fc01ff007f807f00ff01ff01f5471ffe38c731cc6,1⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def constraints : List Minor := [face0]
end P2828Lollipop

namespace P2828CycleFive
open P2828Check P2828Minor P2828Live P2828Generic P2828Truth ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cols : List W := [0x3af57d7f75783edc7775d9cf6aab7e45bb1e65965ca5997f8ef3c2979df5eafafeeaf07db8eeebb39ed556fc8b763ccb2cb94b32ff1de7852f3bebd5f5fdd5e0fb71ddd7673daaadf916ec799659729665fe3bcf0a5e628700000707c003f800000000fc07f00007f00000003c0fc270e001cd050e00000e0f8007f000000001f80fe0000fe0000000781f84e1c0039a0a1c00001c1f000fe000000003f01fc0001fc0000000f03f09c380073,0x29efbfb5b90bdf6dbb9aeb55bd5746eadd668ad8adcae7e5b5e45573e7d3df7f6b7217bedb7735d6ab7aae8dd5bacd15b15b95cfcb6bc8aae7cfa7befed6e42f7db6ee6bad56f55d1bab759a2b62b72b9f96d79155cf8b00000707f800000000003f80fff8000000000003f03ff002f00039f01600000e0ff000000000007f01fff0000000000007e07fe005e00073e02c00001c1fe00000000000fe03ffe000000000000fc0ffc00bc000e7c,0x27fdd5d90fbdefb6dd3375eae87ddb536e8b337336bf8aaac778ae7c8f4ffbabb21f7bdf6dba66ebd5d0fbb6a6dd1666e66d7f15558ef15cf91e9ff757643ef7bedb74cdd7aba1f76d4dba2ccdccdafe2aab1de2b9f22c000707f8000000000fe03fff0000000000003f03ffc0000180073e0058000e0ff0000000001fc07ffe0000000000007e07ff800003000e7c00b0001c1fe0000000003f80fffc000000000000fc0fff000006001cf80,0x1fafe90fdddef63f6edcb973cf9e6c7c773c5c5df8d334d31faf0fa1333f5fd21fbbbdec7eddb972e79f3cd8f8ee78b8bbf1a669a63f5e1f42667ebfa43f777bd8fdbb72e5cf3e79b1f1dcf17177e34cd34c7ebc3e84d03807f8000001fc000fffc00000000003f8003ffc000000010707c00260700ff0000003f8001fff800000000007f0007ff8000000020e0f8004c0e01fe0000007f0003fff00000000000fe000fff0000000041c1f000,0x3fc90fedefef7bc78f1f3e7cf1e78f9f87cf9fe1c71c471c67cff84a40ff921fdbdfdef78f1e3e7cf9e3cf1f3f0f9f3fc38e388e38cf9ff09481ff243fb7bfbdef1e3c7cf9f3c79e3e7e1f3e7f871c711c719f3fe129003ff800000001fffff000000000000003ffffc0000000000007f80003807ff000000003ffffe000000000000007ffff8000000000000ff0000700ffe000000007ffffc00000000000000fffff0000000000001fe0000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower {k} (h : Run (literals 5) k (truth 5 0xfefceea0)) : 7 ≤ k :=
  table_lower (cap:=6) (extra:=2) cols [7, 13, 0, 1, 3] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h
end P2828CycleFive

namespace P2828Lollipop
open P2828Check P2828Minor P2828Live P2828Generic P2828Truth ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rows0 : Array (Fin 1378) := #[48,1,6,10,16,690,20,699,26,691,695,700,31,720,710,741,37,40,696,701,706,731,711,742,44,732,735,743,722,749,747,751]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok0 : face0.Valid base :=
  validates (n:=5) (t:=0xfefceea0) base face0 rows0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) (fun _ h => P2828CycleFive.lower h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid (c : Minor) (h : c ∈ constraints) : c.Valid base := by
  simp only [constraints,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl
  · exact ok0
end P2828Lollipop

namespace C1Base
open ThetaSigned
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev Y := Fin 6 → Bool
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def small : Set (Wire Y) := {f | (∃ c, f=bit c) ∨ ∃ i : Fin 6, f=(fun x => x i) ∨ f=inv (fun x => x i)}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def nine (y : Y) : Bool := (y 1 && y 3) || (y 1 && y 4) || (y 2 && y 4) || (y 0 && y 5) || (y 2 && y 5) || (y 3 && y 5)
end C1Base

namespace P2828Lollipop
open P2828Check P2828Minor P2828Live P2828Generic P2828Truth ThetaSigned SignedCofactor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signed_lower {k} (h : Run (literals 6) k target) : 8 ≤ k := by
  by_contra! low
  have init := live_root h
  have pad (k' : Nat) (le : k ≤ k') : live basicOps goal k' base.toFinset := by
    induction le with
    | refl => exact init
    | step _ ih => exact Or.inl ih
  have seen0 : seen base [] = base.toFinset := by simp [seen]
  have ck := safe (base:=base) (c:=face0) (k:=7) (ws:=base) (hist:=[]) ok0
    (seen0 ▸ History.initial) (seen0 ▸ Finset.Subset.refl _) (pad _ (by omega))
  exact Bool.noConfusion ((by decide +kernel : rejects base face0 7 base [] = true).symm.trans ck)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem prior {k} (h : Run C1Base.small k C1Base.nine) : 8 ≤ k := by
  have e : ∀ x, target x = C1Base.nine x := by decide +kernel
  apply signed_lower
  exact (funext e).symm ▸ h
end P2828Lollipop

namespace P2828Root
open P2828 P2828Check ThetaSigned SignedCofactor P2828Raw
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def perm0 : Fin 9 → Option (Fin 6) := ![none,none,some 1,some 3,none,some 2,some 0,some 4,some 5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid0 : (P2828Root.faceAt 0).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars perm0) (literals 6) (pullSmall perm0)
  have eq : ∀ x, nine (pin (P2828Root.faceAt 0).fixed (P2828Root.faceAt 0).values (insertVars perm0 x)) = C1Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact P2828Lollipop.prior run
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def perm2 : Fin 9 → Option (Fin 7) := ![some 6,some 3,some 5,some 0,some 1,some 4,none,some 2,none]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid2 : (P2828Root.faceAt 2).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars perm2) (literals 7) (pullSmall perm2)
  have eq : ∀ x, nine (pin (P2828Root.faceAt 2).fixed (P2828Root.faceAt 2).values (insertVars perm2 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact C4Lite.signed_lower run
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def perm3 : Fin 9 → Option (Fin 7) := ![some 3,some 5,some 0,none,none,some 6,some 2,some 1,some 4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid3 : (P2828Root.faceAt 3).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars perm3) (literals 7) (pullSmall perm3)
  have eq : ∀ x, nine (pin (P2828Root.faceAt 3).fixed (P2828Root.faceAt 3).values (insertVars perm3 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact C4Lite.signed_lower run
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def perm5 : Fin 9 → Option (Fin 7) := ![some 0,none,some 4,some 6,some 1,some 5,none,some 2,some 3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid5 : (P2828Root.faceAt 5).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars perm5) (literals 7) (pullSmall perm5)
  have eq : ∀ x, nine (pin (P2828Root.faceAt 5).fixed (P2828Root.faceAt 5).values (insertVars perm5 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact C4Lite.signed_lower run
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def perm6 : Fin 9 → Option (Fin 7) := ![none,some 0,some 5,some 3,none,some 4,some 1,some 2,some 6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid6 : (P2828Root.faceAt 6).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars perm6) (literals 7) (pullSmall perm6)
  have eq : ∀ x, nine (pin (P2828Root.faceAt 6).fixed (P2828Root.faceAt 6).values (insertVars perm6 x)) = C4Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact C4Lite.signed_lower run
end P2828Root

namespace P2828Root
open P2828 P2828Check ThetaSigned SignedCofactor P2828Raw
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def perm16 : Fin 9 → Option (Fin 6) := ![some 3,some 5,some 2,none,none,some 1,some 0,some 4,none]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid16 : (P2828Root.faceAt 16).Valid := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  intro k h
  have run := pull h (insertVars perm16) (literals 6) (pullSmall perm16)
  have eq : ∀ x, nine (pin (P2828Root.faceAt 16).fixed (P2828Root.faceAt 16).values (insertVars perm16 x)) = C1Base.nine x := by decide +kernel
  rw [funext eq] at run
  exact P2828Lollipop.prior run
end P2828Root

namespace P2828NineMinor
open P2828Check P2828Minor P2828Live P2828 ThetaSigned
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem raw_closed : ¬ live basicOps goal 13 inputs.toFinset := by
  intro run
  have initial : allSeen [] = inputs.toFinset := by simp [allSeen]
  have ok (s h : List W) (c : Face) (hc : c ∈ P2828Raw.advice s h) : c.Valid := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
    exact P2828Raw.allValid (fun _ h => C4Lite.signed_lower h) i
  have yes := P2828Check.guided_complete _ ok 13 inputs [] 5 (by decide) (by decide)
    (initial ▸ History.initial) (initial ▸ Finset.Subset.refl _) run
  rw [P2828Raw.firstScan] at yes
  contradiction
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem selected (low : Lower) (i : Fin 9) : (cut i).Valid inputs := by
  fin_cases i
  · exact ofOrdinary (P2828Root.faceAt 0) P2828Root.valid0
  · exact diag1 low
  · exact diag2 low
  · exact diag3 low
  · exact ofOrdinary (P2828Root.faceAt 3) P2828Root.valid3
  · exact ofOrdinary (P2828Root.faceAt 2) P2828Root.valid2
  · exact ofOrdinary (P2828Root.faceAt 6) P2828Root.valid6
  · exact ofOrdinary (P2828Root.faceAt 5) P2828Root.valid5
  · exact ofOrdinary (P2828Root.faceAt 16) P2828Root.valid16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signed_lower (lower : Lower) {k} (run : Run given k nine) : 14 ≤ k := by
  by_contra! low
  have pad {S : Finset W} (hr : live basicOps goal k S) (t : Nat) (h : k≤t) : live basicOps goal t S := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  rcases seedRoots run with raw|both
  · exact raw_closed (pad raw _ (by omega))
  · have e : seen inputs [gift] = insert gift inputs.toFinset := by simp [seen]
    have pool : (gift::inputs).toFinset = seen inputs [gift] := by rw [e,List.toFinset_cons]
    have past : History basicOps inputs.toFinset (seen inputs [gift]) := by
      rw [e]
      exact .gate .initial (by decide) (by decide) gift_op
    have ok (s h : List W) (c : Minor) (hc : c ∈ advice s h) : c.Valid inputs := by
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
      exact selected lower i
    have cert := P2828Minor.guided_complete inputs advice ok 13 (gift::inputs) [gift] 4
      (by decide) (by decide) past (pool ▸ Finset.Subset.refl _) (pad both _ (by omega))
    exact Bool.noConfusion (cert.symm.trans closed)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem circuit_lower (lower : Lower) (C : PEqualNP.MetaComplexity.BinaryCircuit) (p : Bool)
    (ok : ∀ g ∈ C.gates, SignedCofactor.cornerGate g)
    (out : ∀ x : Y, (C.eval (List.ofFn x ++ [x 0 || x 1,false]) != p) = nine x) : 14 ≤ C.size :=
  signed_lower lower (seededPhysical C p ok out)
end P2828NineMinor

namespace P2828Check
open P2828Live

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def summary : List W → BitVec 689 × BitVec 689
  | [] => (0,0)
  | w::ws =>
    let p := summary ws
    (sep w ||| p.1, p.2 ||| (p.1 &&& sep w))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem summary_cuts (ws : List W) : (summary ws).1 = cuts ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [summary,cuts,ih,List.foldr_cons]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sep_spec (w : W) (i : Site) : (sep w).getLsbD i.val = true ↔ differs i w := by
  simp [sep,i.isLt,differs]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem summary_unique (ws : List W) (i : Site) (off : (summary ws).2.getLsbD i.val = false) :
    ∀ a ∈ ws, ∀ b ∈ ws, differs i a → differs i b → a=b := by
  induction ws with
  | nil => simp
  | cons x ws ih =>
    simp only [summary,BitVec.getLsbD_or,BitVec.getLsbD_and,Bool.or_eq_false_iff] at off
    intro a ha b hb da db
    rcases List.mem_cons.mp ha with ea|ma
    · subst a
      rcases List.mem_cons.mp hb with eb|mb
      · exact eb.symm
      · have c := (cuts_spec ws i).mpr ⟨b,mb,db⟩
        have sd := (sep_spec x i).mpr da
        have no := off.2
        rw [summary_cuts,c,sd] at no
        contradiction
    · rcases List.mem_cons.mp hb with eb|mb
      · subst b
        have c := (cuts_spec ws i).mpr ⟨a,ma,da⟩
        have sd := (sep_spec x i).mpr db
        have no := off.2
        rw [summary_cuts,c,sd] at no
        contradiction
      · exact ih off.1 a ma b mb da db

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def quickUnate (ws : List W) : Bool :=
  let once := ~~~(summary ws).2
  ws.any fun w =>
    let m := once &&& sep w
    let col := w.setWidth 689
    (m &&& col != 0) && (m &&& ~~~col != 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem site_nonzero (x : BitVec 689) (h : x ≠ 0) : ∃ i : Site, x.getLsbD i.val=true := by
  by_contra! all
  apply h
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have b := all ⟨j,hj⟩
  change x[j] = (0#689)[j]
  rw [BitVec.getElem_zero]
  simpa only [BitVec.getLsbD_eq_getElem hj] using (Bool.eq_false_iff.mpr b)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem quick_unate_safe {k ws} (run : live basicOps goal k ws.toFinset)
    (tight : ws.toFinset.card=k+1) : quickUnate ws = false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  obtain ⟨a,ha,h⟩ := List.any_eq_true.mp bad
  simp only [Bool.and_eq_true,bne_iff_ne] at h
  obtain ⟨i,hi⟩ := site_nonzero _ h.1
  obtain ⟨j,hj⟩ := site_nonzero _ h.2
  have loweq (t : Site) : (a.setWidth 689).getLsbD t.val = low a t := by simp [low,t.isLt]
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,j.isLt,decide_true,Bool.true_and,
    Bool.and_eq_true,Bool.not_eq_true',loweq] at hi hj
  have sole (t : Site) (off : (summary ws).2.getLsbD t.val=false) (da : differs t a) : Sole ws.toFinset a t :=
    fun w hw dw => summary_unique ws t off w (List.mem_toFinset.mp hw) a ha dw da
  exact tight_unate run tight ⟨a,List.mem_toFinset.mpr ha,i,j,sole _ hi.1.1 ((sep_spec a i).mp hi.1.2),
    sole _ hj.1.1 ((sep_spec a j).mp hj.1.2),by rw [hi.2,hj.2];decide⟩
end P2828Check

namespace P2828NFast
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mask : Nat := 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def full : Nat := 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def goal : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def canon (x : Nat) := if x.testBit 0 then x ^^^ full else x
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sep (x : Nat) := (x ^^^ (x >>> 689)) &&& mask
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def summary : List Nat → Nat × Nat
  | [] => (0,0)
  | w::ws =>
    let (a,b) := summary ws
    let s := sep w
    (s ||| a, b ||| (a &&& s))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def unate (ws : List Nat) :=
  let once := mask ^^^ (summary ws).2
  ws.any fun w =>
    let m := once &&& sep w
    let col := w &&& mask
    (m &&& col != 0) && (m &&& (mask ^^^ col) != 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def projection (m a w : Nat) := (if w.testBit a then full ^^^ w else w) &&& m
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def projected (m a w : Nat) : Option Nat :=
  let z := projection m a w
  if z = 0 then none else some (canon z)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def charge (p : Nat → Option Nat) (hist raw : List Nat) :=
  ((hist.filterMap p).filter (fun z => !raw.contains z)).dedup.length
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def reject (base : List Nat) (k : Nat) (ws h : List Nat) (face : Nat × Nat × Nat) :=
  let (lb,m,a) := face
  let p := projected m a
  let rem := k - (ws.filter fun w => projection m a w == 0).length
  if lb ≤ rem then false else
    decide (rem + charge p h (base.filterMap p) < lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a::r => (a,r) :: (singles r).map (fun (b,s) => (b,a::s))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a::r => (singles r).map (fun (b,s) => (a,b,s)) ++ (pairs r).map (fun (b,c,s) => (b,c,a::s))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cover : List Nat → Nat
  | [] => 0
  | w::r => sep w ||| cover r
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def dispatch (e : Nat) (f : Nat → List Nat → Bool) (a b : Nat) (r : List Nat) :=
  let other := cover r
  let sa := sep a
  let sb := sep b
  [a &&& b,a &&& (full ^^^ b),(full ^^^ a) &&& b,(full ^^^ a) &&& (full ^^^ b)].any fun w =>
    let v := sep w ||| other
    let z := canon w
    (v == mask && f e (z::r)) ||
    (e != 0 && (((v ||| sa) == mask && f (e-1) (z::a::r)) || ((v ||| sb) == mask && f (e-1) (z::b::r)))) ||
    (e ≥ 2 && (v ||| sa ||| sb) == mask && f (e-2) (z::a::b::r))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev FaceCode := Nat × Nat × Nat
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def check (base : List Nat) (faces : List FaceCode) (next : Nat → List Nat → List Nat → Bool) (k : Nat) (ws h : List Nat) (e : Nat) (ch : List Nat) :=
  match ch with
  | [] => false
  | z::_ => !ws.contains z && !(e==0 && unate ch) && !(faces.any (reject base k ch (z::h))) && next e ch (z::h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def search (base : List Nat) (faces : List FaceCode) : Nat → Nat → List Nat → List Nat → Bool
  | 0,_,ws,_ => ws == [goal]
  | k+1,e,ws,h => ws == [goal] || (pairs ws).any (fun (a,b,r) => dispatch e (check base faces (search base faces k) k ws h) a b r)
end P2828NFast

namespace P2828NFast
open P2828Check P2828Minor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def encode (ws : List W) := ws.map BitVec.toNat
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def codes (fs : List Minor) : List FaceCode := fs.map (fun c => (c.lower,c.mask.toNat,c.anchor.val))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem full_eq : full = (BitVec.allOnes 1378).toNat := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask_eq : mask = (BitVec.allOnes 689).toNat := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask_bits : mask = 2^689-1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem neg_word (w : W) : full ^^^ w.toNat = (~~~w).toNat := by
  rw [BitVec.not_def,BitVec.toNat_xor,full_eq]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem neg_short (w : BitVec 689) : mask ^^^ w.toNat = (~~~w).toNat := by
  rw [BitVec.not_def,BitVec.toNat_xor,mask_eq]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canon_word (w : W) : canon w.toNat = (P2828Check.canon w).toNat := by
  change (if w.getLsbD 0 then w.toNat ^^^ full else w.toNat) = _
  unfold P2828Check.canon P2828Check.neg
  rw [Nat.xor_comm w.toNat full,neg_word]
  split <;> rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_word (w : W) : w.toNat &&& mask = (w.setWidth 689).toNat := by
  rw [mask_bits,Nat.and_two_pow_sub_one_eq_mod,BitVec.toNat_setWidth]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sep_word (w : W) : sep w.toNat = (P2828Check.sep w).toNat := by
  unfold sep P2828Check.sep
  rw [mask_bits,Nat.and_two_pow_sub_one_eq_mod,BitVec.toNat_setWidth,BitVec.toNat_xor,BitVec.toNat_ushiftRight]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem summary_word (ws : List W) :
    summary (encode ws) = ((P2828Check.summary ws).1.toNat,(P2828Check.summary ws).2.toNat) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change summary (w.toNat::encode ws) = _
    simp only [summary,ih,P2828Check.summary,sep_word,BitVec.toNat_or,BitVec.toNat_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem is_zero {n} (x : BitVec n) : (x.toNat == 0) = (x == 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact @BitVec.toNat_inj n x (0 : BitVec n)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem not_zero {n} (x : BitVec n) : (x.toNat != 0) = (x != 0) := by
  change (!(x.toNat == (0 : Nat))) = (!(x == (0 : BitVec n)))
  rw [is_zero]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem unate_word (ws : List W) : unate (encode ws) = quickUnate ws := by
  unfold unate quickUnate
  rw [summary_word]
  simp only [encode,List.any_map,Function.comp_def]
  apply List.any_congr rfl
  intro w
  rw [neg_short,sep_word,short_word,neg_short]
  simp only [← BitVec.toNat_and,not_zero]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem projection_word (m w : W) (a : Fin 1378) :
    projection m.toNat a.val w.toNat = (limited m a w).toNat := by
  have bit : w.toNat.testBit a.val=w[a.val] := rfl
  unfold projection limited
  rw [bit]
  cases e : w[a.val] <;> simp only [e,Bool.false_eq_true,ite_false,ite_true,neg_word,BitVec.toNat_and]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem projected_word (m w : W) (a : Fin 1378) :
    projected m.toNat a.val w.toNat = (projectFast m a w).map BitVec.toNat := by
  unfold projected projectFast
  rw [projection_word]
  by_cases e : limited m a w=0
  · simp [e]
  · have ne : (limited m a w).toNat ≠ 0 := fun h => e (BitVec.toNat_inj.mp (show _ = (0 : W).toNat from h))
    rw [if_neg e,if_neg ne,canon_word]
    rfl

end P2828NFast

namespace P2828NFast
open P2828Check P2828Minor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem contains_word (ws : List W) (w : W) : (encode ws).contains w.toNat = ws.contains w := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem,encode,List.mem_map]
  constructor
  · rintro ⟨z,h,e⟩
    exact BitVec.toNat_inj.mp e ▸ h
  · intro h
    exact ⟨w,h,rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem project_list (m : W) (a : Fin 1378) (ws : List W) :
    (encode ws).filterMap (projected m.toNat a.val) = encode (ws.filterMap (projectFast m a)) := by
  simp only [encode,List.filterMap_map,List.map_filterMap,Function.comp_def,projected_word]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem charge_word (m : W) (a : Fin 1378) (ws ys : List W) :
    charge (projected m.toNat a.val) (encode ws) (encode ys) = paid (projectFast m a) ws ys := by
  unfold charge paid
  rw [project_list]
  have eq (l : List W) : (encode l).filter (fun v => !(encode ys).contains v)
      = encode (l.filter (fun w => !ys.contains w)) := by
    have same (w : W) : (!((ys.map BitVec.toNat).contains w.toNat)) = !(ys.contains w) :=
      congrArg Bool.not (contains_word ys w)
    simp only [encode,List.filter_map,Function.comp_def,same]
  rw [eq]
  unfold encode
  rw [List.dedup_map_of_injective (fun _ _ e => BitVec.toNat_inj.mp e),List.length_map]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reject_word (base ws h : List W) (k) (c : Minor) :
    reject (encode base) k (encode ws) (encode h) (c.lower,c.mask.toNat,c.anchor.val) =
      cheap base c k ws h := by
  have zeros : ((encode ws).filter (fun w => projection c.mask.toNat c.anchor.val w == 0)).length =
      (ws.filter (fun w => limited c.mask c.anchor w == 0)).length := by
    simp only [encode,List.filter_map,Function.comp_def,projection_word,List.length_map,is_zero]
  simp only [reject,cheap,zeros,project_list,charge_word]

end P2828NFast

namespace P2828NFast
open P2828Check
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem encode_eq (ws : List W) : encode ws = ws.map BitVec.toNat := rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem encode_cons (w : W) (ws : List W) : encode (w::ws) = w.toNat :: encode ws := rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_word (ws : List W) : cover (encode ws) = (cuts ws).toNat := by
  induction ws with
  | nil => rfl
  | cons w ws ih => change sep w.toNat ||| cover (encode ws) = (P2828Check.sep w ||| cuts ws).toNat
                    rw [sep_word,ih,BitVec.toNat_or]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem four_word (a b : W) :
    [a.toNat &&& b.toNat,a.toNat &&& (full ^^^ b.toNat),(full ^^^ a.toNat) &&& b.toNat,
       (full ^^^ a.toNat) &&& (full ^^^ b.toNat)] = encode (rawOps a b) := by
  simp only [rawOps,encode,List.map_cons,List.map_nil,both,P2828Check.neg,BitVec.toNat_and,neg_word]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem is_full (w : BitVec 689) : (w.toNat == mask) = (w == -1) := by
  rw [mask_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,BitVec.toNat_inj]
  rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dispatch_word (extra : Nat) (f : Nat → List Nat → Bool) (g : Nat → List W → Bool)
    (eqn : ∀ j ws, f j (encode ws)=g j ws) (a b : W) (r : List W) :
    dispatch extra f a.toNat b.toNat (encode r) = P2828Check.dispatch extra g a b r := by
  unfold dispatch P2828Check.dispatch
  simp only [four_word,encode,List.any_map,Function.comp_def]
  apply List.any_congr rfl
  intro w
  simp only [←encode_eq,cover_word,sep_word,←BitVec.toNat_or,is_full,canon_word,←encode_cons,eqn]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem single_map (ws : List W) :
    singles (encode ws) = (P2828Check.singles ws).map (fun (b,r) => (b.toNat,encode r)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    simp only [encode_cons,singles,P2828Check.singles,List.map_cons,ih,List.map_map,Function.comp_def]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pair_map (ws : List W) :
    pairs (encode ws) = (P2828Check.pairs ws).map (fun (a,b,r) => (a.toNat,b.toNat,encode r)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    simp only [encode_cons,pairs,P2828Check.pairs,single_map,ih,List.map_append,List.map_map,Function.comp_def]
end P2828NFast

namespace P2828WFast
open P2828Check P2828Live P2828Minor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev Advice := List W → List W → List Minor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def checkChild (base : List W) (ad : Advice) (further : ℕ → List W → List W → Bool) (k : ℕ)
    (ws hist : List W) (extra : ℕ) (child : List W) : Bool :=
  match child with
  | [] => false
  | z :: _ => !(ws.contains z) && !((extra == 0) && quickUnate child) && !((ad child (z::hist)).any (fun c => cheap base c k child (z::hist))) &&
      further extra child (z::hist)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def guided (base : List W) (ad : Advice) : ℕ → ℕ → List W → List W → Bool
  | 0, _, ws, _ => ws == [goal]
  | k+1, extra, ws, hist => ws == [goal] ||
    let more := checkChild base ad (guided base ad k) k ws hist
    (pairs ws).any (fun (a,b,r) => dispatch extra more a b r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
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
        have none : (ad (z::kept) (z::hist)).any (fun c => cheap base c k (z::kept) (z::hist)) = false :=
          List.any_eq_false.mpr fun c hc => by rw [cheap_eq _ _ _ _ _ hnd,safe (valid _ _ c hc) extended pool' hl]; decide
        have fresh : z ∉ ws := by simpa using hout
        have pass : ((k-kept.length == 0) && quickUnate (z::kept)) = false := by
          by_cases zero : k-kept.length=0
          · have tight : (z::kept).toFinset.card=k+1 := by rw [List.toFinset_card_of_nodup hnd,List.length_cons];omega
            simp [quick_unate_safe hl tight]
          · simp [zero]
        simp [checkChild,fresh,none,succ,pass]
      simp only [guided,Bool.or_eq_true,List.any_eq_true]
      right
      rcases hm with direct|swap
      · exact ⟨(a,b,r),direct,go hp hs hz⟩
      · exact ⟨(b,a,r),swap,go (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
end P2828WFast

namespace P2828NFast
open P2828Check P2828Minor P2828Live
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem goal_word : P2828Check.goal.toNat = goal := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem at_goal (ws : List W) : (encode ws == [goal]) = (ws == [P2828Check.goal]) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  rw [←goal_word]
  change ws.map BitVec.toNat = [P2828Check.goal].map BitVec.toNat ↔ _
  exact List.map_inj_right (fun _ _ e => BitVec.toNat_inj.mp e)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem child_word (base ws h ch : List W) (fs : List Minor) (k e : Nat)
    (f : Nat → List Nat → List Nat → Bool) (g : Nat → List W → List W → Bool)
    (eqn : ∀ j v hist,f j (encode v) (encode hist)=g j v hist) :
    check (encode base) (codes fs) f k (encode ws) (encode h) e (encode ch) =
      P2828WFast.checkChild base (fun _ _ => fs) g k ws h e ch := by
  cases ch with
  | nil => rfl
  | cons z tail =>
    change (!((encode ws).contains z.toNat) && !(e==0 && unate (encode (z::tail))) &&
      !((codes fs).any (reject (encode base) k (encode (z::tail)) (encode (z::h)))) &&
      f e (encode (z::tail)) (encode (z::h))) = _
    rw [contains_word,unate_word,eqn]
    unfold P2828WFast.checkChild
    congr 3
    simp only [codes,List.any_map,Function.comp_def,reject_word]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem search_word (base : List W) (fs : List Minor) (k : Nat) (e : Nat) (ws h : List W) :
    search (encode base) (codes fs) k e (encode ws) (encode h) =
      P2828WFast.guided base (fun _ _ => fs) k e ws h := by
  induction k generalizing e ws h with
  | zero => exact at_goal ws
  | succ k ih =>
    simp only [search,P2828WFast.guided,at_goal,pair_map,List.any_map,Function.comp_def]
    congr 1
    apply List.any_congr rfl
    rintro ⟨a,b,r⟩
    apply dispatch_word
    intro j v
    exact child_word base ws h v fs k j _ _ (fun j v hist => ih j v hist)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem complete {base ws hist : List W} {k extra : Nat} {fs : List Minor}
    (valid : ∀ c∈fs, c.Valid base) (hn : ws.Nodup) (room : extra+ws.length=k+1)
    (past : History basicOps base.toFinset (seen base hist)) (pool : ws.toFinset ⊆ seen base hist)
    (run : live basicOps P2828Check.goal k ws.toFinset) :
    search (encode base) (codes fs) k extra (encode ws) (encode hist) = true := by
  rw [search_word]
  exact P2828WFast.guided_complete _ _ (fun _ _ c h => valid c h) _ _ _ _ hn room past pool run
end P2828NFast

namespace P2828MixedNat
open P2828NFast
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def raw : List Nat := [0x2eaaadfaaab555d555bf5556aabaaab7eaaad5575556fd555aaaeaaadfaaab555d555bf5556aabaaab7eaaad5575556fd555aaaeaaadfaaab555d555bf5556aabaaab7eaaad5575556fd555aaaeaaadfaaab555d555be000000000000000000000000000000000000000000003ffffffffffff8000000000000ffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xb3cf6acccd999679ed5999b332cf3dab33366659e7b56666cccb3cf6acccd999679ed5999b332cf3dab33366659e7b56666cccb3cf6acccd999679ed5999b332cf3dab33366659e7b56666cccb3cf6acccd999679ed40000000000000000000ffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffe0000000000003ffffffffffff8000000000000,0x33cf38cf0f1e1e79e719e1e3c3cf3ce33c3c7879e79c67878f0f3cf38cf0f1e1e79e719e1e3c3cf3ce33c3c7879e79c67878f0f3cf38cf0f1e1e79e719e1e3c3cf3ce33c3c7879e79c67878f0f3cf38cf0f1e1e79e718000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffff8000000000000fffffffffffffffffffffffffc0000000000000000000000000,0x3f03f0ff01fe07e07e1fe03fc0fc0fc3fc07f81f81f87f80ff03f03f0ff01fe07e07e1fe03fc0fc0fc3fc07f81f81f87f80ff03f03f0ff01fe07e07e1fe03fc0fc0fc3fc07f81f81f87f80ff03f03f0ff01fe07e07e0000000000000000000000000000000000000000000003fffffffffffffffffffffffff00000000000000000000000003fffffffffffffffffffffffff000000000000000000000000000000000000000000000000000,0x3ffc00fffe0007ff801fffc000fff003fff8001ffe007fff0003ffc00fffe0007ff801fffc000fff003fff8001ffe007fff0003ffc00fffe0007ff801fffc000fff003fff8001ffe007fff0003ffc00fffe0007ff8000000007ffffffffffff00000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000,0x3c00000fffffff800001fffffff000003ffffffe000007ffffffc00000fffffff800001fffffff000003ffffffe000007ffffffc00000fffffff800001fffffff000003ffffffe000007ffffffc00000fffffff8000000000007fffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def constraints : List FaceCode := [(7,0x11555205554aaa2aaa40aaa95545554815552aa8aaa902aaa5551555205554aaa2aaa40aaa95545554815552aa8aaa902aaa5551555205554aaa2aaa40aaa95545554815552aa8aaa902aaa5551555205554aaa2aaa41ffffffffffffffffffffffffffffffffffffffffffffc0000000000007ffffffffffff0000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0),(7,0x34c3095333266698612a6664ccd30c254ccc999a6184a99993334c3095333266698612a6664ccd30c254ccc999a6184a99993334c3095333266698612a6664ccd30c254ccc999a6184a99993334c3095333266698612bfffffffffffffffffff0000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000001ffffffffffffc0000000000007ffffffffffff,0),(7,0x3c0fc0f00fe01f81f81e01fc03f03f03c03f807e07e07807f00fc0fc0f00fe01f81f81e01fc03f03f03c03f807e07e07807f00fc0fc0f00fe01f81f81e01fc03f03f03c03f807e07e07807f00fc0fc0f00fe01f81f81fffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000fffffffffffffffffffffffffc0000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffff,0),(7,0xc30c730f0e1e18618e61e1c3c30c31cc3c387861863987870f0c30c730f0e1e18618e61e1c3c30c31cc3c387861863987870f0c30c730f0e1e18618e61e1c3c30c31cc3c387861863987870f0c30c730f0e1e18618e7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000007ffffffffffff00000000000000000000000003fffffffffffffffffffffffff,0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def branch (i : Nat) := match (pairs raw)[i]? with
  | none => false
  | some (a,b,r) => dispatch 4 (check raw constraints (search raw constraints 8) 8 raw []) a b r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem endSearch (roots : ∀ i : Fin 15, branch i.val = false) : search raw constraints 9 4 raw [] = false := by
  have len : (pairs raw).length=15 := by decide +kernel
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [search,Bool.or_eq_true] at h
  rcases h with stop|step
  · exact (by decide +kernel : (raw == [goal]) ≠ true) stop
  · obtain ⟨p,hp,ok⟩ := List.any_eq_true.mp step
    obtain ⟨i,hi⟩ := List.get_of_mem hp
    have no := roots (Fin.cast len i)
    simp only [Fin.val_cast,branch,List.getElem?_eq_getElem i.isLt] at no
    rw [←hi] at ok
    exact Bool.noConfusion (no.symm.trans ok)
end P2828MixedNat

namespace P2828MixedNat
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no0 : branch 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no1 : branch 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no2 : branch 2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no3 : branch 3 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no4 : branch 4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no5 : branch 5 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no6 : branch 6 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no7 : branch 7 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no8 : branch 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no9 : branch 9 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no10 : branch 10 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no11 : branch 11 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no12 : branch 12 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no13 : branch 13 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no14 : branch 14 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allRoots (i : Fin 15) : branch i.val=false := by
  fin_cases i
  · exact no0
  · exact no1
  · exact no2
  · exact no3
  · exact no4
  · exact no5
  · exact no6
  · exact no7
  · exact no8
  · exact no9
  · exact no10
  · exact no11
  · exact no12
  · exact no13
  · exact no14
end P2828MixedNat

namespace P2828Mixed
open P2828Check P2828Minor P2828Truth P2828Live P2828Generic ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cols : List W := [0x2eaaadfaaab555d555bf5556aabaaab7eaaad5575556fd555aaaeaaadfaaab555d555bf5556aabaaab7eaaad5575556fd555aaaeaaadfaaab555d555bf5556aabaaab7eaaad5575556fd555aaaeaaadfaaab555d555be000000000000000000000000000000000000000000003ffffffffffff8000000000000ffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
0xb3cf6acccd999679ed5999b332cf3dab33366659e7b56666cccb3cf6acccd999679ed5999b332cf3dab33366659e7b56666cccb3cf6acccd999679ed5999b332cf3dab33366659e7b56666cccb3cf6acccd999679ed40000000000000000000ffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffe0000000000003ffffffffffff8000000000000,
0x33cf38cf0f1e1e79e719e1e3c3cf3ce33c3c7879e79c67878f0f3cf38cf0f1e1e79e719e1e3c3cf3ce33c3c7879e79c67878f0f3cf38cf0f1e1e79e719e1e3c3cf3ce33c3c7879e79c67878f0f3cf38cf0f1e1e79e718000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffff8000000000000fffffffffffffffffffffffffc0000000000000000000000000,
0x3f03f0ff01fe07e07e1fe03fc0fc0fc3fc07f81f81f87f80ff03f03f0ff01fe07e07e1fe03fc0fc0fc3fc07f81f81f87f80ff03f03f0ff01fe07e07e1fe03fc0fc0fc3fc07f81f81f87f80ff03f03f0ff01fe07e07e0000000000000000000000000000000000000000000003fffffffffffffffffffffffff00000000000000000000000003fffffffffffffffffffffffff000000000000000000000000000000000000000000000000000,
0x3ffc00fffe0007ff801fffc000fff003fff8001ffe007fff0003ffc00fffe0007ff801fffc000fff003fff8001ffe007fff0003ffc00fffe0007ff801fffc000fff003fff8001ffe007fff0003ffc00fffe0007ff8000000007ffffffffffff00000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000,
0x3c00000fffffff800001fffffff000003ffffffe000007ffffffc00000fffffff800001fffffff000003ffffffe000007ffffffc00000fffffff800001fffffff000003ffffffe000007ffffffc00000fffffff8000000000007fffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mixed := truth 6 0xfffefffafcfceeaa
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def base := signals cols
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem live_root {k} (h : Run (literals 6) k mixed) : live basicOps goal k base.toFinset :=
  table_live cols [0,209,318,56,61,126] (by decide +kernel) (by decide +kernel) (by decide +kernel) h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face0 : Minor := ⟨4,0x10001200000aaa00024000015540004800002aa80009000005550001200000aaa00024000015540004800002aa80009000005550001200000aaa00024000015540004800002aa80009000005550001200000aaa000241ffffff8000000000000fffffffffffffffffffffffffc000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face1 : Minor := ⟨7,0x11555205554aaa2aaa40aaa95545554815552aa8aaa902aaa5551555205554aaa2aaa40aaa95545554815552aa8aaa902aaa5551555205554aaa2aaa40aaa95545554815552aa8aaa902aaa5551555205554aaa2aaa41ffffffffffffffffffffffffffffffffffffffffffffc0000000000007ffffffffffff0000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face2 : Minor := ⟨7,0x34c3095333266698612a6664ccd30c254ccc999a6184a99993334c3095333266698612a6664ccd30c254ccc999a6184a99993334c3095333266698612a6664ccd30c254ccc999a6184a99993334c3095333266698612bfffffffffffffffffff0000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000001ffffffffffffc0000000000007ffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face3 : Minor := ⟨8,0x3030f8c0f0fe1e061f181e1fc3c0c3e303c3f878187c60787f0f030f8c0f0fe1e061f181e1fc3c0c3e303c3f878187c60787f0f030f8c0f0fe1e061f181e1fc3c0c3e303c3f878187c60787f0f030f8c0f0fe1e061f180000007ffffffffffff00000000000000000000000003fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000fffffffffffffffffffffffffc0000000000000000000000000,102⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face4 : Minor := ⟨7,0x3c0fc0f00fe01f81f81e01fc03f03f03c03f807e07e07807f00fc0fc0f00fe01f81f81e01fc03f03f03c03f807e07e07807f00fc0fc0f00fe01f81f81e01fc03f03f03c03f807e07e07807f00fc0fc0f00fe01f81f81fffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000fffffffffffffffffffffffffc0000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face5 : Minor := ⟨7,0xc30c730f0e1e18618e61e1c3c30c31cc3c387861863987870f0c30c730f0e1e18618e61e1c3c30c31cc3c387861863987870f0c30c730f0e1e18618e61e1c3c30c31cc3c387861863987870f0c30c730f0e1e18618e7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000007ffffffffffff00000000000000000000000003fffffffffffffffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face6 : Minor := ⟨6,0x3fffff00000007ffffe0000000fffffc0000001fffff80000003fffff00000007ffffe0000000fffffc0000001fffff80000003fffff00000007ffffe0000000fffffc0000001fffff80000003fffff00000007fffffffffff800000000000000000000000000000000000003fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face7 : Minor := ⟨4,0x15552000000002aaa4000000005554800000000aaa90000000015552000000002aaa4000000005554800000000aaa90000000015552000000002aaa4000000005554800000000aaa90000000015552000000002aaa41ffffff8000000000000000000000000000000000000000000000000007ffffffffffff0000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face8 : Minor := ⟨8,0x25965b56666cccb2cb6acccd9996596d5999b332cb2dab3336665965b56666cccb2cb6acccd9996596d5999b332cb2dab3336665965b56666cccb2cb6acccd9996596d5999b332cb2dab3336665965b56666cccb2cb6a0000000000000000000ffffffffffffe0000000000003ffffffffffff8000000000000ffffffffffffe00000000000000000000000000000000000000ffffffffffffe0000000000003ffffffffffff8000000000000,51⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face9 : Minor := ⟨4,0x1005400005400a00a80000a8014015000015002802a00002a005005400005400a00a80000a8014015000015002802a00002a005005400005400a00a80000a8014015000015002802a00002a005005400005400a00a801ffffffffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000001ffffffffffffc0000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face10 : Minor := ⟨8,0x3ff03f000fe01ffe07e001fc03ffc0fc003f807ff81f8007f00fff03f000fe01ffe07e001fc03ffc0fc003f807ff81f8007f00fff03f000fe01ffe07e001fc03ffc0fc003f807ff81f8007f00fff03f000fe01ffe07e00000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000003fffffffffffffffffffffffff000000000000000000000000000000000000000000000000000,204⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face11 : Minor := ⟨7,0x1d659535a5ab4bacb2a6b4b569759654d696ad2eb2ca9ad2d5a5d659535a5ab4bacb2a6b4b569759654d696ad2eb2ca9ad2d5a5d659535a5ab4bacb2a6b4b569759654d696ad2eb2ca9ad2d5a5d659535a5ab4bacb2a6000000000000000000000000000000000000000000003ffffffffffff8000000000000ffffffffffffe0000000000003ffffffffffff8000000000000fffffffffffffffffffffffffc0000000000000000000000000,102⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face12 : Minor := ⟨7,0xfff000fffe001ffe001fffc003ffc003fff8007ff8007fff000fff000fffe001ffe001fffc003ffc003fff8007ff8007fff000fff000fffe001ffe001fffc003ffc003fff8007ff8007fff000fff000fffe001ffe00000007ffffffffffff000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000,204⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face13 : Minor := ⟨6,0x8c336a33339991866d4666733230cda8ccce664619b51999ccc8c336a33339991866d4666733230cda8ccce664619b51999ccc8c336a33339991866d4666733230cda8ccce664619b51999ccc8c336a33339991866d40000007ffffffffffffffffffffffffe0000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000ffffffffffffe0000000000003ffffffffffff8000000000000,51⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face14 : Minor := ⟨4,0x400011030206080002206040c10000440c08182000088181030400011030206080002206040c10000440c08182000088181030400011030206080002206040c10000440c081820000881810304000110302060800023fffffffffffffffffff0000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000007ffffffffffff000000000000000000000000000000000000007ffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face15 : Minor := ⟨6,0x3fffffe0000007fffffc000000ffffff8000001ffffff0000003fffffe0000007fffffc000000ffffff8000001ffffff0000003fffffe0000007fffffc000000ffffff8000001ffffff0000003fffffe0000007fffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face16 : Minor := ⟨6,0xfcf38c0f0e1e1f9e7181e1c3c3f3ce303c38787e79c607870f0fcf38c0f0e1e1f9e7181e1c3c3f3ce303c38787e79c607870f0fcf38c0f0e1e1f9e7181e1c3c3f3ce303c38787e79c607870f0fcf38c0f0e1e1f9e7180000007fffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000000000003ffffffffffff8000000000000fffffffffffffffffffffffffc0000000000000000000000000,102⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face17 : Minor := ⟨5,0x3403005003200680600a006400d00c01400c801a018028019003403005003200680600a006400d00c01400c801a018028019003403005003200680600a006400d00c01400c801a018028019003403005003200680600bfffffffffffffffffff0000000000001ffffffffffffc0000000000000000000000000fffffffffffffffffffffffffc00000000000000000000000000000000000001ffffffffffffc0000000000007ffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face18 : Minor := ⟨4,0x1042005040a00208400a08140041080141028008210028205001042005040a00208400a08140041080141028008210028205001042005040a00208400a08140041080141028008210028205001042005040a0020841ffffffffffffffffffffffffffffffffffffffffffffc0000000000007ffffffffffff0000000000001ffffffffffffc0000000000007ffffffffffff00000000000000000000000003fffffffffffffffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face19 : Minor := ⟨4,0x10410001110222082000222044410400044408882080008881110410001110222082000222044410400044408882080008881110410001110222082000222044410400044408882080008881110410001110222082001fffffffffffffffffff0000000000001ffffffffffffc0000000000007ffffffffffff0000000000001ffffffffffffffffffffffffffffffffffffff0000000000001ffffffffffffc0000000000007ffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face20 : Minor := ⟨7,0x8ccc9a33cc6791999346798cf2333268cf319e46664d19e633c8ccc9a33cc6791999346798cf2333268cf319e46664d19e633c8ccc9a33cc6791999346798cf2333268cf319e46664d19e633c8ccc9a33cc6791999340000000000000000000ffffffffffffe0000000000003fffffffffffffffffffffffff00000000000000000000000003fffffffffffffffffffffffffffffffffffffe0000000000003ffffffffffff8000000000000,51⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face21 : Minor := ⟨7,0x3ff000fff0001ffe001ffe0003ffc003ffc0007ff8007ff8000fff000fff0001ffe001ffe0003ffc003ffc0007ff8007ff8000fff000fff0001ffe001ffe0003ffc003ffc0007ff8007ff8000fff000fff0001ffe001fffffff8000000000000fffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffff,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def data : Array Minor := #[face0,face1,face2,face3,face4,face5,face6,face7,face8,face9,face10,face11,face12,face13,face14,face15,face16,face17,face18,face19,face20,face21]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def face (i : Fin 22) := data[i.val]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def advice (_ _ : List W) := (List.finRange 22).map face
end P2828Mixed

namespace P2828MixedLeaf1
open P2828Check P2828Minor P2828Truth P2828Live P2828Generic ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cols : List W := [0x2d56f56ab7ab55bd5aadead56f56ab7ab55bd5aadead56f56ab7ab55bd5aadead56f56ab7ab55bd5aadead56f56ab7ab55bd5aadead56f56ab7ab55bd5aadead56f56ab7ab55bd5aadead56f56ab7ab55bd5aadead56e0000fffff800000000000000000000000003ffffe00000fffff80000000001fffff000000000000000000000000007ffffc00001fffff00000000003ffffe00000000000000000000000000fffff800003ffffe00000,
0x367b59b3dacd9ed66cf6b367b59b3dacd9ed66cf6b367b59b3dacd9ed66cf6b367b59b3dacd9ed66cf6b367b59b3dacd9ed66cf6b367b59b3dacd9ed66cf6b367b59b3dacd9ed66cf6b367b59b3dacd9ed66cf6b367b40000000000000000000000000fffff800003ffffffffff0000000000000000000000000000000000001fffff000007fffffffffe0000000000000000000000000000000000003ffffe00000ffffffffffc0000000000,
0x79c7e3ce3f1e71f8f38fc79c7e3ce3f1e71f8f38fc79c7e3ce3f1e71f8f38fc79c7e3ce3f1e71f8f38fc79c7e3ce3f1e71f8f38fc79c7e3ce3f1e71f8f38fc79c7e3ce3f1e71f8f38fc79c7e3ce3f1e71f8f38fc79c6000000000000003ffffe00000ffffffffffc0000000000000000000000000000000000007ffffc00001ffffffffff8000000000000000000000000000000000000fffff800003ffffffffff000000000000000000000,
0x381f9fc0fcfe07e7f03f3f81f9fc0fcfe07e7f03f3f81f9fc0fcfe07e7f03f3f81f9fc0fcfe07e7f03f3f81f9fc0fcfe07e7f03f3f81f9fc0fcfe07e7f03f3f81f9fc0fcfe07e7f03f3f81f9fc0fcfe07e7f03f3f81f9ffff00000000003ffffffffff00000000000000000000000000000003ffffe00000000007fffffffffe00000000000000000000000000000007ffffc0000000000ffffffffffc0000000000000000000000000000000,
0x3fe01fff00fff807ffc03ffe01fff00fff807ffc03ffe01fff00fff807ffc03ffe01fff00fff807ffc03ffe01fff00fff807ffc03ffe01fff00fff807ffc03ffe01fff00fff807ffc03ffe01fff00fff807ffc03ffe01ffffffffffffffc000000000000000000000000000000000000000003fffffffffffffff8000000000000000000000000000000000000000007fffffffffffffff000000000000000000000000000000000000000000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower {k} (h : Run (literals 5) k (truth 5 0xfefceea0)) : 7 ≤ k :=
  table_lower (cap:=6) (extra:=2) cols [84,129,21,23,50] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h
end P2828MixedLeaf1

namespace P2828MixedLeaf2
open P2828Check P2828Minor P2828Truth P2828Live P2828Generic ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cols : List W := [0x17d5ab5f56ad7d5ab5f56ad7d5ab5f56ad7d5ab5f56ad7d5ab5f56ad7d5ab5f56ad7d5ab5f56ad7d5ab5f56ad7d5ab5f56ad7d5ab5f56ad7d5ab5f56ad7d5ab5f56ad7d5ab5f56ad7d5ab5f56ad7d5ab5f56ad7d5ab5e000000000000000000fffffc00000fffffc00000000000000000000000000000000000000fffffc00000fffffc00000000000000000000000000000000000000fffffc00000fffffc000000000000000000000000000,
0x3d66cdf59b37d66cdf59b37d66cdf59b37d66cdf59b37d66cdf59b37d66cdf59b37d66cdf59b37d66cdf59b37d66cdf59b37d66cdf59b37d66cdf59b37d66cdf59b37d66cdf59b37d66cdf59b37d66cdf59b37d66cdf5fc00000000000000000000000000000000000000fffffc00000fffffc00000000000000000000000000000000000000fffffc00000fffffc00000000000000000000000000000000000000fffffc00000fffffc00000,
0x2678f199e3c6678f199e3c6678f199e3c6678f199e3c6678f199e3c6678f199e3c6678f199e3c6678f199e3c6678f199e3c6678f199e3c6678f199e3c6678f199e3c6678f199e3c6678f199e3c6678f199e3c6678f198000000000000000000fffffffffff00000000000fffffffffff0000000000000000000000fffffffffff00000000000fffffffffff0000000000000000000000fffffffffff00000000000fffffffffff00000000000,
0x387f01e1fc0787f01e1fc0787f01e1fc0787f01e1fc0787f01e1fc0787f01e1fc0787f01e1fc0787f01e1fc0787f01e1fc0787f01e1fc0787f01e1fc0787f01e1fc0787f01e1fc0787f01e1fc0787f01e1fc0787f01e00000000fffffc00000ffffffffffffffffffffff0000000000000000000000fffffc00000ffffffffffffffffffffff0000000000000000000000fffffc00000ffffffffffffffffffffff0000000000000000000000,
0x7ffe01fff807ffe01fff807ffe01fff807ffe01fff807ffe01fff807ffe01fff807ffe01fff807ffe01fff807ffe01fff807ffe01fff807ffe01fff807ffe01fff807ffe01fff807ffe01fff807ffe01fff807ffe000000000fffffffffff00000000000000000000000000000000000000000000fffffffffff00000000000000000000000000000000000000000000fffffffffff00000000000000000000000000000000000000000000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower {k} (h : Run (literals 5) k (truth 5 0xfefeccaa)) : 7 ≤ k :=
  table_lower (cap:=6) (extra:=2) cols [0,92,187,26,31] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h
end P2828MixedLeaf2

namespace P2828MixedLeaf4
open P2828Check P2828Minor P2828Truth P2828Live P2828Generic ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cols : List W := [0x15aeafab5d5f56babead757d5aeafab5d5f56babead757d5aeafab5d5f56babead757d5aeafab5d5f56babead757d5aeafab5d5f56babead757d5aeafab5d5f56babead757d5aeafab5d5f56babead757d5aeafab5d5e0000000000000000000000000000000000fffffe0000000000000000000000000000000000000000000001fffffc0000000000000000000000000000000000000000000003fffff80000000000000000000000000000,
0x26cb3acd96759b2ceb3659d66cb3acd96759b2ceb3659d66cb3acd96759b2ceb3659d66cb3acd96759b2ceb3659d66cb3acd96759b2ceb3659d66cb3acd96759b2ceb3659d66cb3acd96759b2ceb3659d66cb3acd9674000007fffff000000000003fffff800000000000000003fffff800000fffffe000000000007fffff000000000000000007fffff000001fffffc00000000000fffffe00000000000000000fffffe000003fffff800000,
0x38f3ccf1e799e3cf33c79e678f3ccf1e799e3cf33c79e678f3ccf1e799e3cf33c79e678f3ccf1e799e3cf33c79e678f3ccf1e799e3cf33c79e678f3ccf1e799e3cf33c79e678f3ccf1e799e3cf33c79e678f3ccf1e799fffff80000000000000000000000000000000000000003fffffffffff00000000000000000000000000000000000000007ffffffffffe0000000000000000000000000000000000000000fffffffffffc00000000000,
0x3f03f0fe07e1fc0fc3f81f87f03f0fe07e1fc0fc3f81f87f03f0fe07e1fc0fc3f81f87f03f0fe07e1fc0fc3f81f87f03f0fe07e1fc0fc3f81f87f03f0fe07e1fc0fc3f81f87f03f0fe07e1fc0fc3f81f87f03f0fe07e000000000000000001fffffc00000000000fffffffffffc00000000000000000000003fffff800000000001fffffffffff800000000000000000000007fffff000000000003fffffffffff00000000000000000000000,
0x3ffc00fff801fff003ffe007ffc00fff801fff003ffe007ffc00fff801fff003ffe007ffc00fff801fff003ffe007ffc00fff801fff003ffe007ffc00fff801fff003ffe007ffc00fff801fff003ffe007ffc00fff80000000000000000001fffffffffffffffff00000000000000000000000000000000003ffffffffffffffffe00000000000000000000000000000000007ffffffffffffffffc0000000000000000000000000000000000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower {k} (h : Run (literals 5) k (truth 5 0xfefafcaa)) : 7 ≤ k :=
  table_lower (cap:=6) (extra:=2) cols [0,96,98,27,58] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h
end P2828MixedLeaf4

namespace P2828MixedLeaf5
open P2828Check P2828Minor P2828Truth P2828Live P2828Generic ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cols : List W := [0x2bd5aeaf56babd5aeaf56babd5aeaf56babd5aeaf56babd5aeaf56babd5aeaf56babd5aeaf56babd5aeaf56babd5aeaf56babd5aeaf56babd5aeaf56babd5aeaf56babd5aeaf56babd5aeaf56babd5aeaf56babd5aeae000000000000000000000003fffff000003fffff000000000000000000000000000000000000003fffff000003fffff000000000000000000000000000000000000003fffff000003fffff0000000000000000000000,
0x3d66cbf59b2fd66cbf59b2fd66cbf59b2fd66cbf59b2fd66cbf59b2fd66cbf59b2fd66cbf59b2fd66cbf59b2fd66cbf59b2fd66cbf59b2fd66cbf59b2fd66cbf59b2fd66cbf59b2fd66cbf59b2fd66cbf59b2fd66cbf5fc00000000003fffff000000000000000000000000000000000fffffc00000000003fffff000000000000000000000000000000000fffffc00000000003fffff000000000000000000000000000000000fffffc00000,
0xe78f339e3cce78f339e3cce78f339e3cce78f339e3cce78f339e3cce78f339e3cce78f339e3cce78f339e3cce78f339e3cce78f339e3cce78f339e3cce78f339e3cce78f339e3cce78f339e3cce78f339e3cce78f338000000000000000000000003ffffffffffc00000000003fffff0000000000000000000000000003ffffffffffc00000000003fffff0000000000000000000000000003ffffffffffc00000000003fffff00000000000,
0x307f03c1fc0f07f03c1fc0f07f03c1fc0f07f03c1fc0f07f03c1fc0f07f03c1fc0f07f03c1fc0f07f03c1fc0f07f03c1fc0f07f03c1fc0f07f03c1fc0f07f03c1fc0f07f03c1fc0f07f03c1fc0f07f03c1fc0f07f03c00000000fffffc00000000003fffffffffffffffffffffc0000000000000000fffffc00000000003fffffffffffffffffffffc0000000000000000fffffc00000000003fffffffffffffffffffffc0000000000000000,
0x7ffc01fff007ffc01fff007ffc01fff007ffc01fff007ffc01fff007ffc01fff007ffc01fff007ffc01fff007ffc01fff007ffc01fff007ffc01fff007ffc01fff007ffc01fff007ffc01fff007ffc01fff007ffc000000000ffffffffffffffffc00000000000000000000000000000000000000ffffffffffffffffc00000000000000000000000000000000000000ffffffffffffffffc00000000000000000000000000000000000000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower {k} (h : Run (literals 5) k (truth 5 0xfefaccea)) : 7 ≤ k :=
  table_lower (cap:=6) (extra:=2) cols [0,47,25,27,55] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h
end P2828MixedLeaf5

namespace P2828Mixed
open P2828Check P2828Minor P2828Truth P2828Live P2828Generic ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rows1 : Array (Fin 1378) := #[0,51,102,153,204,694,255,697,306,699,701,703,408,705,707,709,510,561,713,715,717,719,721,723,612,726,728,730,732,734,736,738]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok1 : face1.Valid base :=
  validates (n:=5) (t:=0xfefceea0) base face1 rows1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) (fun _ h => P2828MixedLeaf1.lower h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rows2 : Array (Fin 1378) := #[0,689,102,691,204,693,255,696,306,357,701,702,408,459,707,708,510,711,713,714,717,718,721,722,612,725,728,729,732,733,736,737]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok2 : face2.Valid base :=
  validates (n:=5) (t:=0xfefeccaa) base face2 rows2 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) (fun _ h => P2828MixedLeaf2.lower h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rows4 : Array (Fin 1378) := #[0,689,51,690,102,691,153,692,306,357,699,700,701,702,703,704,510,711,561,712,713,714,715,716,612,725,726,727,728,729,730,731]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4 : face4.Valid base :=
  validates (n:=5) (t:=0xfefafcaa) base face4 rows4 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) (fun _ h => P2828MixedLeaf4.lower h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rows5 : Array (Fin 1378) := #[0,689,51,690,204,693,694,695,306,357,699,700,408,459,705,706,510,711,561,712,717,718,719,720,612,725,726,727,732,733,734,735]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5 : face5.Valid base :=
  validates (n:=5) (t:=0xfefaccea) base face5 rows5 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (Option.isSome_iff_exists.mp (by decide +kernel)) (fun _ h => P2828MixedLeaf5.lower h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def four : List Minor := [face1,face2,face4,face5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem four_valid (c : Minor) (h : c ∈ four) : c.Valid base := by
  simp only [four,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl
  · exact ok1
  · exact ok2
  · exact ok4
  · exact ok5
end P2828Mixed

namespace P2828Mixed
open P2828Check P2828Minor P2828Live P2828Generic P2828Truth ThetaSigned SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem signed_lower {k : Nat} (h : Run (literals 6) k mixed) : 10 ≤ k := by
  by_contra! small
  have init := live_root h
  have pad (k' : Nat) (h : k ≤ k') : live basicOps goal k' base.toFinset := by
    induction h with
    | refl => exact init
    | step _ ih => exact Or.inl ih
  have seen0 : seen base [] = base.toFinset := by simp [seen]
  have h1 := P2828NFast.complete (base:=base) (ws:=base) (hist:=[]) (k:=9) (extra:=4) (fs:=four)
    four_valid (by decide +kernel) (by decide +kernel)
    (seen0 ▸ History.initial) (seen0 ▸ Finset.Subset.refl _) (pad 9 (by omega))
  have cols : P2828NFast.encode base = P2828MixedNat.raw := by decide +kernel
  have cs : P2828NFast.codes four = P2828MixedNat.constraints := by decide +kernel
  rw [cols,cs] at h1
  exact Bool.noConfusion (h1.symm.trans (P2828MixedNat.endSearch P2828MixedNat.allRoots))
end P2828Mixed

end PEqualNP.Outside.L_meta_2828

open PEqualNP.Outside.L_meta_2828

theorem PEqualNP.Outside.L_meta_2828 : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  exact P2828NineMinor.circuit_lower (fun _ h => P2828Mixed.signed_lower h)
