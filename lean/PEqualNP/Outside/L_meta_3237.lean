import Mathlib
import PEqualNP.Defs

-- The signed search and base cofactor certificates follow the L-meta-2210 proof of sirusdv.
-- Uses the finite circuit search method of L-meta-515.
namespace PEqualNP.Outside.L_meta_3237_aux

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


end PEqualNP.Outside.L_meta_3237_aux

namespace PEqualNP.Outside.L_meta_3237_aux.Gift9
open P2828Check P2828 P2828Live ThetaSigned
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
    let sites : List (Fin 689) := [0, 32, 64, 96, 128, 150, 182, 204, 226]
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
def root := gift::inputs
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def onFace (f v : BitVec 9) := plus small (fun y => seed (pin f v y))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma decoded_gift (f v : BitVec 9) (r : Fin 1378) :
    ∀ w ∈ kept (cropOpt (faceMask f v) r) root.toFinset, interpret (pickFace f v) w ∈ onFace f v := by
  intro w hw
  simp only [root,List.toFinset_cons] at hw
  rw [kept_insert] at hw
  rcases Finset.mem_union.1 hw with h | h
  · have eq : cropOpt (faceMask f v) r gift = some w := by simpa using h
    change cropOpt _ r (canon gateWord) = some w at eq
    rw [crop_canon] at eq
    unfold cropOpt wrap at eq
    split at eq
    · contradiction
    obtain rfl := Option.some.inj eq
    have sig : interpret (pickFace f v) gateWord = fun y => seed (pin f v y) := by
      funext y
      have a := congrFun (pickFace_row f v y) 0
      have b := congrFun (pickFace_row f v y) 1
      change (rawInputs.getD 0 0).getLsbD (pickFace f v y).val = pin f v y 0 at a
      change (rawInputs.getD 1 0).getLsbD (pickFace f v y).val = pin f v y 1 at b
      change ((rawInputs.getD 0 0) ||| (rawInputs.getD 1 0)).getLsbD (pickFace f v y).val =
        (pin f v y 0 || pin f v y 1)
      rw [BitVec.getLsbD_or,a,b]
    rcases interpret_canon (pickFace f v) (crop (faceMask f v) r gateWord) with hs|hs
    · rw [hs,interpret_crop,sig]; exact Or.inr (Or.inl rfl)
    · rw [hs,interpret_crop,sig]; exact Or.inr (Or.inr rfl)
  · exact Or.inl (decoded_kept f v r _ h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gift_face_run {f v : BitVec 9} {r : Fin 1378} {g : W} (hg : cropOpt (faceMask f v) r goal = some g)
    {hist s : Finset W} {k : ℕ} (past : History basicOps root.toFinset hist) (pool : s ⊆ hist)
    (run : live basicOps goal k s) :
    Run (onFace f v) (k - zeros (cropOpt (faceMask f v) r) s + price (cropOpt (faceMask f v) r) root.toFinset hist)
      (fun y => nine (pin f v y)) := by
  obtain h := face_budget (mask_projects _ _) past pool hg run
  have cl : Closed (onFace f v) := plus_closed small_closed _
  have decoded := decode_build (pickFace f v) h cl (decoded_gift f v r)
  unfold cropOpt wrap at hg
  split at hg
  · contradiction
  obtain rfl := Option.some.inj hg
  rcases interpret_canon (pickFace f v) (crop (faceMask f v) r goal) with h|h <;>
    rw [h,interpret_crop,interpret_goal] at decoded
  · exact decoded
  · simpa only [inv_inv] using Run_inv decoded cl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Valid (c : Face) : Prop := c.mask = faceMask c.fixed c.values ∧
    (∃ g, cropOpt c.mask c.anchor goal = some g) ∧
    ∀ k, Run (onFace c.fixed c.values) k (fun y => nine (pin c.fixed c.values y)) → c.lower ≤ k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gallSeen (hist : List W) := hist.toFinset ∪ root.toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def grejects (c : Face) (k : ℕ) (ws hist : List W) : Bool :=
  let p := cropOpt c.mask c.anchor
  decide (k - zeros p ws.toFinset + price p root.toFinset (gallSeen hist) < c.lower)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem grejects_false {c : Face} (valid : Valid c) {k ws hist}
    (past : History basicOps root.toFinset (gallSeen hist)) (pool : ws.toFinset ⊆ gallSeen hist)
    (run : live basicOps goal k ws.toFinset) : grejects c k ws hist = false := by
  obtain ⟨em,⟨g,hg⟩,bound⟩ := valid
  rw [em] at hg
  have hr := bound _ (gift_face_run hg past pool run)
  simp only [grejects,em,decide_eq_false_iff_not,not_lt]
  exact hr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev gAdvice := List W → List W → List Face

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gcheckChild (ad : List Face) (further : ℕ → List W → List W → Bool) (k : ℕ)
    (ws hist : List W) (extra : ℕ) (child : List W) : Bool :=
  match child with
  | [] => false
  | z :: _ => !(ws.contains z) && !(ad.any (fun c => grejects c k child (z::hist))) &&
      further extra child (z::hist)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gguided (ad : gAdvice) : ℕ → ℕ → List W → List W → Bool
  | 0, _, ws, _ => ws == [goal]
  | k+1, extra, ws, hist => ws == [goal] ||
    let more := gcheckChild (ad ws hist) (gguided ad k) k ws hist
    (pairs ws).any (fun (a,b,r) => dispatch extra more a b r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gguided_complete (ad : gAdvice) (valid : ∀ ws hist, ∀ c ∈ ad ws hist, Valid c)
    (n : ℕ) (ws hist : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (past : History basicOps root.toFinset (gallSeen hist))
    (pool : ws.toFinset ⊆ gallSeen hist) (h : live basicOps goal n ws.toFinset) :
    gguided ad n extra ws hist = true := by
  induction n generalizing ws hist extra with
  | zero => simp [gguided,singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [gguided,singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have seen : gallSeen (z::hist) = insert z (gallSeen hist) := by simp [gallSeen]
      have extended : History basicOps root.toFinset (gallSeen (z::hist)) := seen ▸ .gate past (pool ha) (pool hb) hz
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (gcheckChild (ad ws hist) (gguided ad k) k ws hist) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have sub : kept.toFinset ⊆ ws.toFinset := by rw [hfin,hset];exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨fun hv => hout (sub (List.mem_toFinset.mpr hv)),hnk⟩
        have hl : live basicOps goal k (z::kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd,List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) _ hop hk (by omega) (by omega) (cuts_full hl)
        have pool' : (z::kept).toFinset ⊆ gallSeen (z::hist) := by
          rw [seen,List.toFinset_cons]; exact Finset.insert_subset_insert _ (sub.trans pool)
        have succ := ih _ _ (k-kept.length) hnd (by simp;omega) extended pool' hl
        have none : (ad ws hist).any (fun c => grejects c k (z::kept) (z::hist)) = false :=
          List.any_eq_false.mpr fun c hc => by rw [grejects_false (valid _ _ c hc) extended pool' hl]; decide
        have fresh : z ∉ ws := by simpa using hout
        simp [gcheckChild,fresh,none,succ]
      simp only [gguided,Bool.or_eq_true,List.any_eq_true]
      right
      rcases hm with direct|swap
      · exact ⟨(a,b,r),direct,go hp hs hz⟩
      · exact ⟨(b,a,r),swap,go (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sixth : Face := ⟨320,0,11,faceMask 320 0,0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def faceList : List Face := (List.finRange 5).map P2828Raw.faceAt ++ [sixth]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gbank : gAdvice := fun _ _ => faceList

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first_close : gguided gbank 13 4 root [] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower_from_faces (valid : ∀ c ∈ faceList, Valid c)
    (rawLower : ∀ k, live basicOps goal k inputs.toFinset → 14 ≤ k)
    {k : Nat} (h : Run given k nine) : 14 ≤ k := by
  by_contra! low
  rcases seedRoots h with no|yes
  · exact (Nat.not_lt_of_ge (rawLower k no)) low
  · have pad {a : Finset W} (t : Nat) (le : k ≤ t) (hl : live basicOps goal k a) : live basicOps goal t a := by
      induction le with
      | refl => exact hl
      | step _ ih => exact Or.inl ih
    have start : gallSeen [] = root.toFinset := by simp [gallSeen]
    have chk := gguided_complete gbank (fun _ _ _ hc => valid _ hc) 13 root [] 4 (by decide)
      (by decide) (start ▸ History.initial) (start ▸ Finset.Subset.refl _)
      (pad 13 (by omega) yes)
    exact Bool.noConfusion (chk.symm.trans first_close)
end PEqualNP.Outside.L_meta_3237_aux.Gift9

namespace PEqualNP.Outside.L_meta_3237_aux.Gift9
open PEqualNP.MetaComplexity
open ThetaSigned P2828

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def bstep (s : List Bool) (g : BinaryGate) : List Bool :=
  s ++ [g.op (s.getD g.left false) (s.getD g.right false)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def read {X : Type} (w : X → List Bool) (i : Nat) : Wire X := fun x => (w x).getD i false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def chooseSign {X : Type} (f : Wire X) (s : Bool) : Wire X := if s then f else inv f

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma choose_mem {X : Type} {P : Set (Wire X)} (cl : Closed P) (f : Wire X) (hf : f∈P)
    (s : Bool) : chooseSign f s∈P := by
  cases s
  · exact cl.2 f hf
  · exact hf

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma choose_value {X : Type} (f : Wire X) (s : Bool) (x : X) : chooseSign f s x = (f x == s) := by
  cases s <;> cases h : f x <;> simp [chooseSign,inv,h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem compile_signed {X : Type} (gs : List BinaryGate) (out : Nat)
    (ok : ∀ g∈gs, ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b)) :
    ∀ (w : X → List Bool) (m : Nat), (∀ x,(w x).length=m) →
    ∀ (P : Set (Wire X)), Closed P → (∀i,read w i∈P) → ∀ phase : Bool,
      Run P gs.length (fun x => ((gs.foldl bstep (w x)).getD out false != phase)) := by
  induction gs with
  | nil =>
    intro w m len P cl avail phase
    cases phase
    · have h : (fun x => ((w x).getD out false != false)) = read w out := by
        funext x
        change ((w x).getD out false != false) = (w x).getD out false
        cases (w x).getD out false <;> rfl
      exact .done (h ▸ avail out)
    · have h : (fun x => ((w x).getD out false != true)) = inv (read w out) := by
        funext x
        change ((w x).getD out false != true) = !((w x).getD out false)
        cases (w x).getD out false <;> rfl
      exact .done (h ▸ cl.2 _ (avail out))
  | cons g gs ih =>
    intro w m len P cl avail phase
    obtain ⟨a,b,op⟩ := ok g (by simp)
    let left := chooseSign (read w g.left) a
    let right := chooseSign (read w g.right) b
    let v := bin false left right
    have vval (x : X) : v x = g.op ((w x).getD g.left false) ((w x).getD g.right false) := by
      rw [op]
      change (chooseSign _ a x && chooseSign _ b x)=_
      rw [choose_value,choose_value]; rfl
    apply Run.gate false (choose_mem cl _ (avail _) a) (choose_mem cl _ (avail _) b)
    apply ih (fun k hk => ok k (List.mem_cons_of_mem _ hk)) (fun x => bstep (w x) g) (m+1)
      (fun x => by simp [bstep,len]) (plus P v) (plus_closed cl v) _ phase
    intro i
    by_cases hm : i=m
    · have eq : read (fun x => bstep (w x) g) i = v := by
        funext x
        change (w x ++ [_]).getD i false=v x
        rw [hm,←len x,ImportedHelpers.getD_snoc_eq,vval]
      exact Or.inr (Or.inl eq)
    · have eq : read (fun x => bstep (w x) g) i = read w i := by
        funext x
        exact ImportedHelpers.getD_snoc_ne _ _ _ _ (by rwa [len])
      exact Or.inl (eq ▸ avail i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem binary_run (C : BinaryCircuit) (phase : Bool)
    (ok : ∀ g∈C.gates, ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b))
    (correct : ∀ x : Y, (C.eval (List.ofFn x ++ [seed x,false]) != phase) = nine x) :
    Run given C.size nine := by
  let state (x : Y) := List.ofFn x ++ [seed x,false]
  have cl : Closed given := plus_closed small_closed seed
  have sources (i : Nat) : read state i∈given := by
    by_cases hi : i<9
    · have eq : read state i = (fun x : Y => x ⟨i,hi⟩) := by
        funext x
        change (List.ofFn x ++ [seed x,false]).getD i false=_
        rw [List.getD_append _ _ _ _ (by simpa using hi)]
        exact ImportedHelpers.getD_ofFn _ _ false ⟨i,hi⟩
      exact Or.inl (Or.inr ⟨⟨i,hi⟩,Or.inl eq⟩)
    · by_cases eq9 : i=9
      · have eq : read state i=seed := by
          funext x
          change (List.ofFn x ++ [seed x,false]).getD i false=_
          rw [eq9,List.getD_append_right _ _ _ _ (by simp)]
          simp
        exact Or.inr (Or.inl eq)
      · have eq : read state i=bit false := by
          funext x
          change (List.ofFn x ++ [seed x,false]).getD i false=false
          rw [List.getD_append_right _ _ _ _ (by simp;omega),List.length_ofFn]
          cases hi' : i-9 with
          | zero => omega
          | succ t => cases t <;> rfl
        exact eq ▸ cl.1 false
  have hr := compile_signed C.gates C.output ok state 11 (fun x => by simp [state]) given cl sources phase
  have eq : (fun x : Y => ((C.gates.foldl bstep (state x)).getD C.output false != phase)) = nine :=
    funext correct
  exact eq ▸ hr

end PEqualNP.Outside.L_meta_3237_aux.Gift9

namespace PEqualNP.Outside.L_meta_3237_aux.GiftFaces
open P2828Check P2828 P2828Live ThetaSigned
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev Y7 := Fin 7 → Bool
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lits (n : Nat) : Set (Wire (Fin n → Bool)) := {f | (∃ c, f=ThetaSigned.bit c) ∨ ∃ i : Fin n, f=(fun x => x i) ∨ f=inv (fun x => x i)}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def graph7 (y : Y7) : Bool := (y 0 && y 1) || (y 2 && y 4) || (y 0 && y 5) || (y 2 && y 5) || (y 3 && y 5) || (y 1 && y 6) || (y 3 && y 6) || (y 4 && y 6)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sm7 := lits 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h05 (y : Y7) := y 0 || y 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h35 (y : Y7) := y 3 || y 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem clraw : Closed sm7 := by
  constructor
  · intro b; exact Or.inl ⟨b,rfl⟩
  · rintro f (⟨b,rfl⟩|⟨i,rfl|rfl⟩)
    · exact Or.inl ⟨!b,rfl⟩
    · exact Or.inr ⟨i,Or.inr rfl⟩
    · exact Or.inr ⟨i,Or.inl (inv_inv _)⟩
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
    (fun x => f (insertVars idx x)) ∈ lits n := by
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
theorem pull_face {face : Face} (idx : Fin 9 → Option (Fin 7)) (Q : Set (Wire Y7))
    (closed : Closed Q) (raw : sm7 ⊆ Q)
    (hseed : (fun x => Gift9.seed (pin face.fixed face.values (insertVars idx x))) ∈ Q)
    (eq : ∀ x, nine (pin face.fixed face.values (insertVars idx x)) = graph7 x)
    (bound : ∀ k, Run Q k graph7 → face.lower ≤ k) :
    ∀ k, Run (Gift9.onFace face.fixed face.values) k (fun y => nine (pin face.fixed face.values y)) →
      face.lower ≤ k := by
  intro k h
  have hr := pull h (insertVars idx) Q (by
    intro g hg
    rcases hg with old|rfl|rfl
    · exact raw (pullSmall idx g old)
    · exact hseed
    · exact closed.2 _ hseed)
  rw [funext eq] at hr
  exact bound _ hr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def idx0 : Fin 9 → Option (Fin 7) := ![none,some 0,some 5,some 3,none,some 4,some 1,some 2,some 6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid0 (bound : ∀ k, Run sm7 k graph7 → 11 ≤ k) : Gift9.Valid (P2828Raw.faceAt 0) := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  apply pull_face idx0 sm7 clraw (fun _ h => h) _ (by decide +kernel) bound
  exact Or.inr ⟨0,Or.inl (funext (by decide +kernel : ∀ x, Gift9.seed (pin (P2828Raw.faceAt 0).fixed (P2828Raw.faceAt 0).values (insertVars idx0 x)) = x 0))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def idx1 : Fin 9 → Option (Fin 7) := ![some 0,none,some 4,some 6,some 1,some 5,none,some 2,some 3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid1 (bound : ∀ k, Run sm7 k graph7 → 11 ≤ k) : Gift9.Valid (P2828Raw.faceAt 1) := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  apply pull_face idx1 sm7 clraw (fun _ h => h) _ (by decide +kernel) bound
  exact Or.inr ⟨0,Or.inl (funext (by decide +kernel : ∀ x, Gift9.seed (pin (P2828Raw.faceAt 1).fixed (P2828Raw.faceAt 1).values (insertVars idx1 x)) = x 0))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def idx2 : Fin 9 → Option (Fin 7) := ![some 5,some 0,none,some 4,some 2,some 3,some 1,none,some 6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid2 (bound : ∀ k, Run (plus sm7 h05) k graph7 → 11 ≤ k) : Gift9.Valid (P2828Raw.faceAt 2) := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  apply pull_face idx2 (plus sm7 h05) (plus_closed clraw _) (fun _ hg => Or.inl hg) _ (by decide +kernel) bound
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, Gift9.seed (pin (P2828Raw.faceAt 2).fixed (P2828Raw.faceAt 2).values (insertVars idx2 x)) = h05 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def idx3 : Fin 9 → Option (Fin 7) := ![some 3,some 5,some 0,none,none,some 6,some 2,some 1,some 4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid3 (bound : ∀ k, Run (plus sm7 h35) k graph7 → 11 ≤ k) : Gift9.Valid (P2828Raw.faceAt 3) := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  apply pull_face idx3 (plus sm7 h35) (plus_closed clraw _) (fun _ hg => Or.inl hg) _ (by decide +kernel) bound
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, Gift9.seed (pin (P2828Raw.faceAt 3).fixed (P2828Raw.faceAt 3).values (insertVars idx3 x)) = h35 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def idx4 : Fin 9 → Option (Fin 7) := ![some 0,some 5,some 3,some 6,some 1,none,some 2,none,some 4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid4 (bound : ∀ k, Run (plus sm7 h05) k graph7 → 11 ≤ k) : Gift9.Valid (P2828Raw.faceAt 4) := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  apply pull_face idx4 (plus sm7 h05) (plus_closed clraw _) (fun _ hg => Or.inl hg) _ (by decide +kernel) bound
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, Gift9.seed (pin (P2828Raw.faceAt 4).fixed (P2828Raw.faceAt 4).values (insertVars idx4 x)) = h05 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def idx5 : Fin 9 → Option (Fin 7) := ![some 5,some 3,some 6,some 4,some 2,some 0,none,some 1,none]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid5 (bound : ∀ k, Run (plus sm7 h35) k graph7 → 11 ≤ k) : Gift9.Valid Gift9.sixth := by
  refine ⟨by decide +kernel,Option.isSome_iff_exists.mp (by decide +kernel),?_⟩
  apply pull_face idx5 (plus sm7 h35) (plus_closed clraw _) (fun _ hg => Or.inl hg) _ (by decide +kernel) bound
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, Gift9.seed (pin Gift9.sixth.fixed Gift9.sixth.values (insertVars idx5 x)) = h35 x)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_valid (r : ∀ k, Run sm7 k graph7 → 11 ≤ k)
    (a : ∀ k, Run (plus sm7 h05) k graph7 → 11 ≤ k)
    (b : ∀ k, Run (plus sm7 h35) k graph7 → 11 ≤ k) : ∀ face ∈ Gift9.faceList, Gift9.Valid face := by
  intro face hf
  rcases List.mem_append.1 hf with first|last
  · obtain ⟨i,_,rfl⟩ := List.mem_map.1 first
    fin_cases i
    · exact valid0 r
    · exact valid1 r
    · exact valid2 a
    · exact valid3 b
    · exact valid4 a
  · have eq : face = Gift9.sixth := by simpa using last
    exact eq ▸ valid5 b
end PEqualNP.Outside.L_meta_3237_aux.GiftFaces

namespace PEqualNP.Outside.L_meta_3237_aux
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
end SignedCofactor

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


end PEqualNP.Outside.L_meta_3237_aux

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta

open C4Base ThetaSigned C4RCheck C4RLive

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def seed (a b : Fin 7) (y : C4Base.Y) : Bool := y a || y b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gateWord (a b : Fin 7) : W := (rawInputs.getD a.val 0) ||| (rawInputs.getD b.val 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def gift (a b : Fin 7) : W := canon (gateWord a b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root (a b : Fin 7) : List W := gift a b :: inputs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def given (a b : Fin 7) : Set (Wire C4Base.Y) := ThetaSigned.plus C4Base.small (seed a b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed_good (a b : Fin 7) : good (given a b) (insert (gift a b) inputs.toFinset) := by
  rintro f (old | rfl | rfl)
  · obtain ⟨w,e,hm⟩ := initialGood _ old
    exact ⟨w,e.imp_right Finset.mem_insert_of_mem,hm⟩
  · refine ⟨gateWord a b,Or.inr (Finset.mem_insert_self ..),?_⟩
    intro r
    change ((rawInputs.getD a.val 0)[r.val] || (rawInputs.getD b.val 0)[r.val]) =
      (gateWord a b)[r.val]
    simp [gateWord]
  · refine ⟨~~~gateWord a b,Or.inr ?_,?_⟩
    · rw [canon_neg]
      exact Finset.mem_insert_self ..
    · intro r
      change (!((rawInputs.getD a.val 0)[r.val] || (rawInputs.getD b.val 0)[r.val])) =
        (~~~gateWord a b)[r.val]
      simp [gateWord]

def necessary (a b : Fin 7) (sites : List (Fin 232)) : Prop :=
  inputs.all (fun w => sites.any (fun i => (root a b).all (fun x =>
    (x.getLsbD i.val == x.getLsbD (232+i.val)) || x == w))) = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed_roots (a b : Fin 7) (sites : List (Fin 232)) (need : necessary a b sites)
    {k : ℕ} (h : ThetaSigned.Run (given a b) k C4Base.nine) :
    live basicOps goal k inputs.toFinset ∨ live basicOps goal k (root a b).toFinset := by
  obtain ⟨s,hs,hl⟩ := compress (signedBuild h _ (seed_good a b))
  have entire : inputs.toFinset ⊆ s := by
    intro w hw
    obtain ⟨i,_,hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp need w (List.mem_toFinset.mp hw))
    obtain ⟨x,hx,hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) hl
    have incl : x ∈ root a b := List.mem_toFinset.mp (by simpa [root] using hs hx)
    have e := List.all_eq_true.mp hAll x incl
    simp only [Bool.or_eq_true,beq_iff_eq] at e
    exact e.resolve_left hd ▸ hx
  by_cases use : gift a b ∈ s
  · right
    rwa [root,List.toFinset_cons,← Finset.Subset.antisymm hs (Finset.insert_subset use entire)]
  · have sub : s ⊆ inputs.toFinset := by
      intro w hw
      exact (Finset.mem_insert.mp (hs hw)).resolve_left (fun e => use (e ▸ hw))
    exact Or.inl ((Finset.Subset.antisymm sub entire) ▸ hl)

theorem history_of_gift (a b w : W) (ha : a ∈ inputs.toFinset) (hb : b ∈ inputs.toFinset)
    (hop : w ∈ basicOps a b) : History basicOps inputs.toFinset (allSeen [w]) := by
  simpa [allSeen] using History.gate History.initial ha hb hop

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def bank (table : Array (List (Fin 23))) (ws hist : List W) : List Face :=
  (table.getD ((C4Lite.code ws + 37*C4Lite.code hist)%1021) []).map C4Lite.faceAt

theorem bank_valid (table : Array (List (Fin 23))) :
    ∀ ws hist, ∀ c ∈ bank table ws hist, c.Valid := by
  intro ws hist c hc
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
  exact C4Lite.valid i


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rootPair (ad : Advice) (seed : W) (i : ℕ) : Bool :=
  let ws := seed :: inputs
  let hist := [seed]
  match (pairs ws)[i]? with
  | none => false
  | some (a,b,r) =>
    dispatch 3 (C4RSpeed.checkChild (ad ws hist) (C4RSpeed.guided ad 9) 9 ws hist) a b r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem roots_close (ad : Advice) (a b : Fin 7)
    (roots : ∀ i : Fin 28, rootPair ad (gift a b) i.val = false) :
    C4RSpeed.guided ad 10 3 (root a b) [gift a b] = false := by
  let ws := root a b
  let hist := [gift a b]
  have len : (pairs ws).length = 28 := by rfl
  apply Bool.eq_false_iff.mpr
  intro h
  change C4RSpeed.guided ad 10 3 ws hist = true at h
  simp only [C4RSpeed.guided,Bool.or_eq_true] at h
  rcases h with stop | step
  · have eq := congrArg List.length (beq_iff_eq.mp stop)
    have hlen : ws.length = 8 := by rfl
    simp [hlen] at eq
  · obtain ⟨p,hp,ok⟩ := List.any_eq_true.mp step
    obtain ⟨i,hi⟩ := List.get_of_mem hp
    have no := roots (Fin.cast len i)
    simp only [Fin.val_cast] at no
    change (match (pairs ws)[i.val]? with
      | none => false
      | some (a,b,r) =>
        dispatch 3 (C4RSpeed.checkChild (ad ws hist) (C4RSpeed.guided ad 9) 9 ws hist) a b r) =
      false at no
    rw [List.getElem?_eq_getElem i.isLt] at no
    rw [←hi] at ok
    exact Bool.noConfusion (no.symm.trans ok)

theorem pad_live {k t : ℕ} {s : Finset W} (bound : k ≤ t)
    (h : live basicOps goal k s) : live basicOps goal t s := by
  induction bound with
  | refl => exact h
  | step _ ih => exact Or.inl ih

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem raw_lower {k : ℕ} (h : live basicOps goal k inputs.toFinset) : 11 ≤ k := by
  by_contra! low
  have initial : allSeen [] = inputs.toFinset := by simp [allSeen]
  have cert := C4RSpeed.guided_complete C4Lite.advice (C4Lite.advice_ok C4Lite.valid)
    10 inputs [] 4 (by decide) (by decide) (initial ▸ History.initial)
    (initial ▸ Finset.Subset.refl _) (pad_live (by omega) h)
  exact Bool.noConfusion (cert.symm.trans (C4Lite.roots_close C4Lite.all_roots))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower_with (a b : Fin 7) (sites : List (Fin 232)) (need : necessary a b sites)
    (nd : (root a b).Nodup)
    (past : History basicOps inputs.toFinset (allSeen [gift a b]))
    (ad : Advice) (valid : ∀ ws hist, ∀ c ∈ ad ws hist, c.Valid)
    (closed : C4RSpeed.guided ad 10 3 (root a b) [gift a b] = false)
    {k : ℕ} (h : ThetaSigned.Run (given a b) k C4Base.nine) : 11 ≤ k := by
  by_contra! low
  rcases seed_roots a b sites need h with raw | use
  · exact (Nat.not_lt_of_ge (raw_lower raw)) low
  · have pool : (root a b).toFinset ⊆ allSeen [gift a b] := by simp [root,allSeen]
    have cert := C4RSpeed.guided_complete ad valid 10 (root a b) [gift a b] 3 nd
      (by rfl) past pool (pad_live (by omega) use)
    exact Bool.noConfusion (cert.symm.trans closed)



end PEqualNP.Outside.L_meta_3237_aux.GiftTheta

namespace PEqualNP.Outside.L_meta_3237_aux.Credit7
open C4Base ThetaSigned C4RLive C4RCheck
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def onFace (a b : Fin 7) (f v : BitVec 7) := plus small (fun y => GiftTheta.seed a b (pin f v y))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma decoded_gift (a b : Fin 7) (f v : BitVec 7) (r : Fin 464) :
    ∀ w ∈ kept (cropOpt (faceMask f v) r) (GiftTheta.root a b).toFinset, interpret (pickFace f v) w ∈ onFace a b f v := by
  intro w hw
  simp only [GiftTheta.root,List.toFinset_cons] at hw
  rw [kept_insert] at hw
  rcases Finset.mem_union.1 hw with h | h
  · have eq : cropOpt (faceMask f v) r (GiftTheta.gift a b) = some w := by simpa using h
    change cropOpt _ r (canon (GiftTheta.gateWord a b)) = some w at eq
    rw [crop_canon] at eq
    unfold cropOpt wrap at eq
    split at eq
    · contradiction
    obtain rfl := Option.some.inj eq
    have sig : interpret (pickFace f v) (GiftTheta.gateWord a b) = fun y => GiftTheta.seed a b (pin f v y) := by
      funext y
      have left := congrFun (pickFace_row f v y) a
      have right := congrFun (pickFace_row f v y) b
      change (rawInputs.getD a.val 0).getLsbD (pickFace f v y).val = pin f v y a at left
      change (rawInputs.getD b.val 0).getLsbD (pickFace f v y).val = pin f v y b at right
      change ((rawInputs.getD a.val 0) ||| (rawInputs.getD b.val 0)).getLsbD (pickFace f v y).val =
        (pin f v y a || pin f v y b)
      rw [BitVec.getLsbD_or,left,right]
    rcases interpret_canon (pickFace f v) (crop (faceMask f v) r (GiftTheta.gateWord a b)) with hs|hs
    · rw [hs,interpret_crop,sig]; exact Or.inr (Or.inl rfl)
    · rw [hs,interpret_crop,sig]; exact Or.inr (Or.inr rfl)
  · exact Or.inl (decoded_kept f v r _ h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem gift_face_run (a b : Fin 7) {f v : BitVec 7} {r : Fin 464} {g : W} (hg : cropOpt (faceMask f v) r goal = some g)
    {hist s : Finset W} {k : ℕ} (past : History basicOps (GiftTheta.root a b).toFinset hist) (pool : s ⊆ hist)
    (run : live basicOps goal k s) :
    Run (onFace a b f v) (k - zeros (cropOpt (faceMask f v) r) s + price (cropOpt (faceMask f v) r) (GiftTheta.root a b).toFinset hist)
      (fun y => nine (pin f v y)) := by
  obtain h := face_budget (mask_projects _ _) past pool hg run
  have cl : Closed (onFace a b f v) := plus_closed small_closed _
  have decoded := decode_build (pickFace f v) h cl (decoded_gift a b f v r)
  unfold cropOpt wrap at hg
  split at hg
  · contradiction
  obtain rfl := Option.some.inj hg
  rcases interpret_canon (pickFace f v) (crop (faceMask f v) r goal) with h|h <;>
    rw [h,interpret_crop,interpret_goal] at decoded
  · exact decoded
  · simpa only [inv_inv] using Run_inv decoded cl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def Valid (a b : Fin 7) (c : Face) : Prop := c.mask = faceMask c.fixed c.values ∧
    (∃ g, cropOpt c.mask c.anchor goal = some g) ∧
    ∀ k, Run (onFace a b c.fixed c.values) k (fun y => nine (pin c.fixed c.values y)) → c.lower ≤ k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def seen (base hist : List W) := hist.toFinset ∪ base.toFinset
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rej (base : List W) (c : Face) (k : ℕ) (ws hist : List W) : Bool :=
  let p := cropOpt c.mask c.anchor
  decide (k - zeros p ws.toFinset + price p base.toFinset (seen base hist) < c.lower)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reject_no {a b : Fin 7} {c : Face} (valid : Valid a b c) {k ws hist}
    (past : History basicOps (GiftTheta.root a b).toFinset (seen (GiftTheta.root a b) hist))
    (pool : ws.toFinset ⊆ seen (GiftTheta.root a b) hist)
    (run : live basicOps goal k ws.toFinset) : rej (GiftTheta.root a b) c k ws hist = false := by
  obtain ⟨em,⟨g,hg⟩,bound⟩ := valid
  rw [em] at hg
  have hr := bound _ (gift_face_run a b hg past pool run)
  simp only [rej,em,decide_eq_false_iff_not,not_lt]
  exact hr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem kept_list' (p : W → Option W) (ws : List W) :
    kept p ws.toFinset = (ws.filterMap p).toFinset := by
  ext a; simp [kept,List.mem_filterMap]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem paid_credit (base : List W) (p : W → Option W) (hist : List W) :
    paid p hist (base.filterMap p) = price p base.toFinset (seen base hist) := by
  let h := (hist.filterMap p).filter fun z => !(base.filterMap p).contains z
  change h.dedup.length = _
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup _),List.toFinset_dedup]
  unfold price seen
  rw [show kept p (hist.toFinset ∪ base.toFinset) = kept p hist.toFinset ∪ kept p base.toFinset by
    ext a; simp [kept,or_and_right,exists_or]]
  rw [kept_list',kept_list']
  congr 1
  ext a; simp [h]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def quick (base : List W) (c : Face) (k : Nat) (ws hist : List W) : Bool :=
  let p := cropOpt c.mask c.anchor
  let rem := k - gone p ws
  if c.lower ≤ rem then false else decide (rem + paid p hist (base.filterMap p) < c.lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem quick_eq (base : List W) (c : Face) (k : Nat) (ws hist : List W) (hn : ws.Nodup) :
    quick base c k ws hist = rej base c k ws hist := by
  simp only [quick,rej,gone_eq _ hn,paid_credit]
  split
  · symm;apply decide_eq_false;omega
  · rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def maskedReject (base : List W) (c : Face) (k : Nat) (ws hist : List W) : Bool :=
  let p := projectFast c.mask c.anchor
  let rem := k - (ws.filter (fun w => limited c.mask c.anchor w == 0)).length
  if c.lower ≤ rem then false else
    decide (rem + paid p hist (base.filterMap p) < c.lower)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem masked_eq (base : List W) (c : Face) (k : Nat) (ws hist : List W) (hn : ws.Nodup) :
    maskedReject base c k ws hist = rej base c k ws hist := by
  rw [← quick_eq base _ _ _ _ hn]
  unfold maskedReject quick gone
  rw [←projectFast_eq]
  have columns (w : W) : (projectFast c.mask c.anchor w).isNone = (limited c.mask c.anchor w == 0) := by
    let z := limited c.mask c.anchor w
    change (if z=0 then none else some (canon z)).isNone = (z == 0)
    by_cases hz : z=0
    · rw [if_pos hz,hz];rfl
    · rw [if_neg hz];exact (beq_eq_false_iff_ne.mpr hz).symm
  simp only [columns]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def checkChild (base : List W) (ad : List Face) (further : ℕ → List W → List W → Bool) (k : ℕ)
    (ws hist : List W) (extra : ℕ) (child : List W) : Bool :=
  match child with
  | [] => false
  | z :: _ => !(ws.contains z) && !(ad.any (fun c => maskedReject base c k child (z::hist))) &&
      further extra child (z::hist)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def guided (base : List W) (ad : Advice) : ℕ → ℕ → List W → List W → Bool
  | 0, _, ws, _ => ws == [goal]
  | k+1, extra, ws, hist => ws == [goal] ||
    let more := checkChild base (ad ws hist) (guided base ad k) k ws hist
    (pairs ws).any (fun (a,b,r) => dispatch extra more a b r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem guided_complete (i j : Fin 7) (ad : Advice) (valid : ∀ ws hist, ∀ c ∈ ad ws hist, Valid i j c)
    (n : ℕ) (ws hist : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (past : History basicOps (GiftTheta.root i j).toFinset (seen (GiftTheta.root i j) hist))
    (pool : ws.toFinset ⊆ seen (GiftTheta.root i j) hist) (h : live basicOps goal n ws.toFinset) :
    guided (GiftTheta.root i j) ad n extra ws hist = true := by
  induction n generalizing ws hist extra with
  | zero => simp [guided,singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [guided,singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have seenEq : seen (GiftTheta.root i j) (z::hist) = insert z (seen (GiftTheta.root i j) hist) := by simp [seen]
      have extended : History basicOps (GiftTheta.root i j).toFinset (seen (GiftTheta.root i j) (z::hist)) := seenEq ▸ .gate past (pool ha) (pool hb) hz
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (checkChild (GiftTheta.root i j) (ad ws hist) (guided (GiftTheta.root i j) ad k) k ws hist) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have sub : kept.toFinset ⊆ ws.toFinset := by rw [hfin,hset];exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨fun hv => hout (sub (List.mem_toFinset.mpr hv)),hnk⟩
        have hl : live basicOps goal k (z::kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd,List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) _ hop hk (by omega) (by omega) (cuts_full hl)
        have pool' : (z::kept).toFinset ⊆ seen (GiftTheta.root i j) (z::hist) := by
          rw [seenEq,List.toFinset_cons]; exact Finset.insert_subset_insert _ (sub.trans pool)
        have succ := ih _ _ (k-kept.length) hnd (by simp;omega) extended pool' hl
        have none : (ad ws hist).any (fun c => maskedReject (GiftTheta.root i j) c k (z::kept) (z::hist)) = false :=
          List.any_eq_false.mpr fun c hc => by rw [masked_eq (GiftTheta.root i j) _ _ _ _ hnd,reject_no (valid _ _ c hc) extended pool' hl]; decide
        have fresh : z ∉ ws := by simpa using hout
        simp [checkChild,fresh,none,succ]
      simp only [guided,Bool.or_eq_true,List.any_eq_true]
      right
      rcases hm with direct|swap
      · exact ⟨(a,b,r),direct,go hp hs hz⟩
      · exact ⟨(b,a,r),swap,go (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
end PEqualNP.Outside.L_meta_3237_aux.Credit7

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta

open C4RCheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def emit (condition : Bool) (extra : ℕ) (ws : List W) : List (ℕ × List W) :=
  if condition then [(extra,ws)] else []

theorem any_emit (condition : Bool) (extra : ℕ) (ws : List W)
    (next : ℕ → List W → Bool) :
    (emit condition extra ws).any (fun p => next p.1 p.2) =
      (condition && next extra ws) := by
  cases condition <;> simp [emit]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def choices (extra : ℕ) (a b : W) (r : List W) : List (ℕ × List W) :=
  (rawOps a b).flatMap fun w =>
    let z := canon w
    let v := sep w ||| cuts r
    emit (v == -1) extra (z :: r) ++
    emit ((extra != 0) && (v ||| sep a == -1)) (extra-1) (z :: a :: r) ++
    emit ((extra != 0) && (v ||| sep b == -1)) (extra-1) (z :: b :: r) ++
    emit ((extra ≥ 2) && (v ||| sep a ||| sep b == -1)) (extra-2) (z :: a :: b :: r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dispatch_choices (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) :
    dispatch extra next a b r = (choices extra a b r).any (fun p => next p.1 p.2) := by
  unfold dispatch choices
  rw [List.any_flatMap]
  dsimp only
  apply congrArg (fun f : W → Bool => (rawOps a b).any f)
  funext w
  simp only [List.any_append,any_emit,Bool.and_or_distrib_left,Bool.and_assoc,Bool.or_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def rootChildren (w : W) (i : ℕ) : List (ℕ × List W) :=
  match (pairs (w::inputs))[i]? with
  | none => []
  | some (a,b,r) => choices 3 a b r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def childCheck (ad : Advice) (w : W) (p : ℕ × List W) : Bool :=
  C4RSpeed.checkChild (ad (w::inputs) [w]) (C4RSpeed.guided ad 9) 9 (w::inputs) [w] p.1 p.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def childAt (ad : Advice) (w : W) (i j : ℕ) : Bool :=
  match (rootChildren w i)[j]? with
  | none => false
  | some p => childCheck ad w p

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_children_eq (ad : Advice) (w : W) (i : ℕ) :
    rootPair ad w i = (rootChildren w i).any (childCheck ad w) := by
  unfold rootPair rootChildren
  dsimp only
  cases eq : (pairs (w::inputs))[i]? with
  | none => rfl
  | some x =>
    obtain ⟨a,b,r⟩ := x
    change dispatch 3 (C4RSpeed.checkChild (ad (w::inputs) [w]) (C4RSpeed.guided ad 9)
      9 (w::inputs) [w]) a b r = (choices 3 a b r).any (childCheck ad w)
    exact dispatch_choices 3 (fun extra child => childCheck ad w (extra,child)) a b r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_of_children (ad : Advice) (w : W) (i size : ℕ)
    (len : (rootChildren w i).length = size)
    (h : ∀ j : Fin size, childAt ad w i j.val = false) : rootPair ad w i = false := by
  rw [root_children_eq]
  apply List.any_eq_false.mpr
  intro p hp
  obtain ⟨j,eq⟩ := List.get_of_mem hp
  have step := h (Fin.cast len j)
  simp only [childAt,Fin.val_cast,List.getElem?_eq_getElem j.isLt] at step
  rw [←eq]
  exact Bool.eq_false_iff.mp step

end PEqualNP.Outside.L_meta_3237_aux.GiftTheta

namespace PEqualNP.Outside.L_meta_3237_aux.PathCheck

variable {State : Type*}

def follow (next : State → List State) (root : State) (path : List ℕ) : Option State :=
  path.foldl (fun current i => current.bind fun s => (next s)[i]?) (some root)

theorem follow_snoc (next : State → List State) (root : State) (p : List ℕ) (i : ℕ) :
    follow next root (p ++ [i]) = (follow next root p).bind (fun s => (next s)[i]?) := by
  unfold follow
  rw [List.foldl_append]
  rfl

def checkAt (next : State → List State) (check : State → Bool) (root : State) (path : List ℕ) : Bool :=
  ((follow next root path).map check).getD false

def terminalAt (next : State → List State) (goal : State → Bool) (root : State) (path : List ℕ) : Bool :=
  checkAt next goal root path

def childCount (next : State → List State) (root : State) (path : List ℕ) : ℕ :=
  ((follow next root path).map fun s => (next s).length).getD 0

theorem close_by_children (next : State → List State) (goal check : State → Bool)
    (step : ∀ s, check s = (goal s || (next s).any check))
    (root : State) (path : List ℕ) (arity : ℕ)
    (terminal : terminalAt next goal root path = false)
    (len : childCount next root path = arity)
    (passed : ∀ i : Fin arity, checkAt next check root (path ++ [i.val]) = false) :
    checkAt next check root path = false := by
  cases here : follow next root path with
  | none => simp [checkAt,here]
  | some s =>
    have done : goal s = false := by simpa [terminalAt,checkAt,here] using terminal
    have l : (next s).length = arity := by simpa [childCount,here] using len
    have kids : (next s).any check = false := by
      apply List.any_eq_false.mpr
      intro t ht
      obtain ⟨i,e⟩ := List.get_of_mem ht
      have q := passed (Fin.cast l i)
      rw [←e]
      apply Bool.eq_false_iff.mp
      simpa [checkAt,follow_snoc,here,List.getElem?_eq_getElem i.isLt] using q
    simpa [checkAt,here,done,kids] using step s

end PEqualNP.Outside.L_meta_3237_aux.PathCheck

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck
open GiftTheta
open PEqualNP.Outside.L_meta_3237_aux.PathCheck

abbrev State := ℕ × ℕ × List W × List W

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def startState (base : List W) : State := (10,3,base,[])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def goalOf : State → Bool := fun (_,_,ws,_) => ws == [goal]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def score (base : List W) (ad : Advice) : State → Bool :=
  fun (k,e,ws,hist) => Credit7.guided base ad k e ws hist

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def keepChild (base : List W) (ad : Advice) (k : ℕ) (ws hist : List W)
    (p : ℕ × List W) : Option State :=
  match p.2 with
  | [] => none
  | z :: _ =>
    if (!ws.contains z && !(ad ws hist).any (fun c => Credit7.maskedReject base c k p.2 (z::hist)))
      then some (k,p.1,p.2,z::hist) else none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def next (base : List W) (ad : Advice) : State → List State
  | (0,_,_,_) => []
  | (k+1,e,ws,hist) =>
    (pairs ws).flatMap fun (a,b,r) => (choices e a b r).filterMap (keepChild base ad k ws hist)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem keepChild_score (base : List W) (ad : Advice) (k : ℕ) (ws hist : List W)
    (p : ℕ × List W) :
    ((keepChild base ad k ws hist p).map (score base ad)).getD false =
    Credit7.checkChild base (ad ws hist) (Credit7.guided base ad k) k ws hist p.1 p.2 := by
  obtain ⟨e,c⟩ := p
  cases c with
  | nil => rfl
  | cons z tail =>
    let flag := !ws.contains z && !(ad ws hist).any
      (fun f => Credit7.maskedReject base f k (z::tail) (z::hist))
    change ((if flag then some (k,e,z::tail,z::hist) else none).map (score base ad)).getD false =
      (flag && Credit7.guided base ad k e (z::tail) (z::hist))
    cases flag <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem step (base : List W) (ad : Advice) (s : State) :
    score base ad s = (goalOf s || (next base ad s).any (score base ad)) := by
  obtain ⟨k,e,ws,hist⟩ := s
  cases k with
  | zero => simp [score,goalOf,next,Credit7.guided]
  | succ k =>
    simp only [score,goalOf,next,Credit7.guided,List.any_flatMap]
    apply congrArg (fun t : Bool => (ws == [goal]) || t)
    apply congrArg (fun f : W × W × List W → Bool => (pairs ws).any f)
    funext x
    obtain ⟨a,b,r⟩ := x
    rw [dispatch_choices,List.any_filterMap]
    apply congrArg (fun f : ℕ × List W → Bool => (choices e a b r).any f)
    funext p
    have h := (keepChild_score base ad k ws hist p).symm
    cases he : keepChild base ad k ws hist p <;> simpa [he] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def test (base : List W) (ad : Advice) (path : List ℕ) : Bool :=
  checkAt (next base ad) (score base ad) (startState base) path

theorem close (base : List W) (ad : Advice) (path : List ℕ) (arity : ℕ)
    (stop : terminalAt (next base ad) goalOf (startState base) path = false)
    (len : childCount (next base ad) (startState base) path = arity)
    (h : ∀ i : Fin arity, test base ad (path ++ [i.val]) = false) :
    test base ad path = false :=
  close_by_children (next base ad) goalOf (score base ad) (step base ad)
    (startState base) path arity stop len h

theorem root_closed (base : List W) (ad : Advice)
    (h : test base ad [] = false) : Credit7.guided base ad 10 3 base [] = false := h

end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def creditData05 : Array (List (Fin 23)) := #[[2],[7,9,15],[],[1],[1,5,0,9,7],[9,1,2,6,10,5,0],[0,7,1,5,4,6],[7,0],[2,7,0],[],[1],[0,7,2,9],[2,7,0,9],[1,0,5,2,7,3],[0,9,6,7,4,8,1],
  [0,7,9,2,1,8],[0],[2,7,0,1,9],[1,4,7],[1,2,0,7,15,5,6,8,19,9,4],[0,1,5,8,2,7,6],[0,1,5,7,9],[],[2,9,6,10,4],[1,9],[0,15,1,4,7,2,8,19],[10],[],
  [1,9,7],[0,2,1,9,4,8],[1,9,11],[],[],[7,0,2],[0,1,6,5,7,2,10,19,3],[0,1,7],[0,1,2,6,7,15,19,10,4],[0],[],[2,9,0,1,4],[0,1,5,9,4,2,3,6],
  [0,1,6,10,9,7],[0,7],[1],[9,0,1,5,2,19,8,6],[1,0,5,2,7],[1],[1,5,0,2,8,9],[],[],[2,4,0,1,7,6,9],[],[0,1,5,2,7,14,9],[0],[0,6,1],
  [0,1,5,2,8,9,7],[],[0,1,6,2,7],[0,5],[],[0,9,7],[],[],[6,1],[0,6,1,4,7,2],[7,0],[2,15,0,1,4,9,6,8],[1,8,7,0,2],[1,5],[],[0,1,5,9],[],
  [0,7,1,9,2,5,4,8,15],[],[0,2],[7],[0,7,6,1,2],[7,9,4],[0,1,5,2,3,9,7],[],[1],[0,1,9,7],[0,19,2,7,1],[0,7,6,9],[1],[0,7,2,9,1,5],[],[4,8,2,15],
  [1,0,6,5],[],[0],[1,4,0],[2,1],[],[],[4],[1,6,0,2,15],[7,0,1,2,5,6,9],[1],[1,5,0,4,6,7,9,2],[0,7,1,2,19],[],[7,1,9,0,8,6],[1],[1,2],[],[],
  [6,0],[1,0,5,7,2,8],[],[0,7,1],[1],[2],[7,0,6,1,2,9,8],[2],[2,7,4],[],[0,2,9,1,6,7,15],[1],[1,3,0,5,7],[1,7,11],[0,7,1,6,2,8,9],[6,0,1,5,7,2],
  [],[0,6,2,10],[],[0,1,5,14,2,9],[0,7,1,2,6,15,8],[],[8,1,0],[1],[2,0],[2,0,6,1,9,8],[7,1,0,5],[],[6,0,1,7,2,5],[0,6,1,2,7,5,9],[0,6],
  [1,5,2,0,8],[7,0,1],[7,0,9],[0,6,1,19,2],[0,6,1,2,5,10,7,19],[0,3,9,6],[1,15,0,4,2,6],[],[0,7,9,5],[1,4,0,7,6,2,8,9],[],[0],[],[],[],[],
  [1,0,2,7,13,8],[7,9,6],[19,4],[],[7,0],[0,4,2,1,9,11],[0,2,9,1,7,19],[7,2,0,4,11,9],[],[1],[],[0,1,3,7,5],[0,1,2,9,5],[1,0,8,2,9,19,7],
  [0,7,1,6,2,9,8],[0,1,9,7,4],[0,9,2,4],[0,6,1,7,19],[],[19,1,2,0],[7,0,2],[],[0],[7,0,6,10],[],[1,8],[0,6,1,5,3,19,8],[0,6,1,7,2],[1,7],
  [1,0,2,8,19,11,9],[1,0,6,7,4,2,9,8,15],[],[0,7,1,9,5,2,8,4],[0],[0,1,7,6,2,9,11,5],[1,5,0,9],[],[1,7,0,2,13],[1,5,0,8,7,9,4,2,10],[0,1,5],[],
  [1,8,0,2,9,4],[1],[1,8,0,2],[7,2,0,5,3,11,9],[10,2],[6],[],[7,0,1,2,4,11],[5,0,1,3,7,2],[0,7,2,1,6,9,5,4,15],[0,7,4,8,1],[0,2,19],
  [0,7,19,1,2,10],[1],[0,7],[0,1,2,3,6,7,9,8,5],[0,6,1,2,10,7],[0,7],[4,0,6,1,7,2],[1,0,4,2,8],[],[],[9],[7,8,0],[0,9,1,2,7,4,8,5,15],[],
  [0,1,7,2,6,9,4,15,8],[1,4,9,0,8,6,2,7],[9,7,2,15],[10,0,6],[2],[],[0,7,15,1,2,14,9,4,8],[5,0,1,2,6,19,9],[7],[0,1,7,2,6,9,19,12,8,4],[],[1,8],
  [],[1],[],[0,1,9],[2],[0,6,2],[7,0,2,6,1,4,15,8],[6],[0,7,9,4],[2,0],[],[],[1,5,7,9],[2,7],[0,7,1,5,2,4,8],[4,2,0,7,1,19,10,9],[0,1,5,9,7],[],
  [],[],[1,2,9],[0,1,8,9,6,2,7,19,4],[6,10,1,5],[7,0,1,6,5],[5,2,9],[4,0,7,1,8,5,2],[8,2],[2,0,7],[1,9,0,4,7,2,8],[],[1,2,0,9,8,15,4,5,6],[],
  [0,7],[],[1,4,7,2,0,8],[0],[0,5,7,1,10,9,8],[0,5,2,9,4,1],[2,0],[0,7,2,1,11,9],[0,9,1,7,5,8,2],[1,0,9,4,8,2],[2],[0,5,6,1],[2],[],
  [0,1,9,2,15,6,19],[0,1,6,19,2,15],[1,4,0,2,8],[1,5],[6,0,1,2,7],[0,1],[7,0,9,4,1],[],[0,9,1,5],[],[0],[1,0,7,6,9,5],[1,0,7,5,9,4,2],
  [0,9,7,1,5],[0,1,3,2,5,6,19],[],[0,1,6,2,7,5,19],[1,2,5],[4,7,9,2,0,8,1,6,10],[0,1,7,9,5,2,6,4,8],[],[1,0,7,8,11],[0],[],[2,4,1,0,10],[0,1,7],
  [7,0,1,2,6,15,9],[0,1],[7,0,1,2],[15,2,0,7],[0,7,2,9,10,1,6],[0,1,6,2,7,19,4,8],[0],[],[0,5,6,1,7,2,9,4,14,8],[0,1,4,2,15,6,7,8,9],[0,9,7,6],
  [0,7,9,1,2,6],[7,0,1,9,2],[6,1,7,0,4],[2,0,1,7,9,5,6],[9,11,0,5,15],[5,2,1],[0,7,6,4,1,15,9,8],[1,0,5,2,3,9,7],[0,1,7],[7,1,0,4,5,2],
  [0,6,1,5,7,9],[],[0,6,10],[1,0,7,11,4],[],[0,19,7,2],[],[],[2,1],[0,1,5,7,2,6,8,3],[],[0,9,2],[0,1,7,2,4,9,5,6,14],[0,7,1,2,6,15],
  [5,0,7,1,8,4,2,11],[5,2,1,0],[0,9,19,7,1,8],[4,2,0,9,1,7,10],[],[],[0,7,9],[8,1],[0,6,1,19,2,10],[9,4,0],[0,6,1,2,9,7],[0,9,1,2,4,8,15],[],
  [0,7,9,11],[0,1,7,2,8],[6,12,4],[0,4,8],[0,7],[1,8,5,0,7,3,19,9],[1,0,5,7,2],[0],[1,7,0,8,2,4],[],[1,0,8,5,2,7],[7,1,0,9],[1,9],[1],[9,7,15,4],
  [0,1,5,2],[1,0],[],[0,19,1,2,10,9],[0,1,5,9,14,3,7],[6,0,9,10,2,19],[4,1],[0,1],[0,1,6,7,2,19],[4],[5,1,3],[0,2],[],[],[1,7,0,6,11],[5],
  [1,0,9],[5,1,0,9,8,7],[0,1,5,2,10,6,7,11,4,15,19],[6,0,2],[10,1],[0],[15],[],[],[6,5,7,0,9,1,2],[1,8,9],[0,6,1,9,11,4,8,2,5],[2,0],[0,6,2],
  [0,7,6,1,8],[],[],[0,1,5,3,7],[6,0,7,2],[0,7,6,1,2,11],[7,0],[0,1,2,9,5,6],[1,5,9,0,11],[7,2,0,1,15,9,14],[1,0,2,5,7,8,9],[2],[1,7,0,2,5],[],
  [5],[],[0,7,1,9,6,2,10,15],[2,9,1],[1,4,0,8],[5,4],[],[0,5,3,7],[2,0,7,5,6,9,19,10],[0,1,7,8,19],[],[],[0,2],[0,6,2,5,7,9,1,10],[0,7,1,6,9,2],
  [2,9],[1,2,7],[9,0,1,2,4,19,15],[1],[],[0,1,7,9,5,2],[0,1,4,2,15,6,9,8],[0,9],[2],[0],[0,6,1,7,9,2,8,5],[0,6,7],[9,2],[],[6],[],
  [0,1,4,5,2,8,9,19],[1,0,6,2,9,5],[],[6,2,9,0,14,4],[0,6,7,1,5,9,19,2,8,4],[0,7,1,19,2,8,9,4],[],[7,0,2,1,9,11,8],[],[0,7,6,1,2],[0,7,1,8],[],
  [7,2,1,8,0,9],[1],[8],[],[7,1,9,2,6,10,0,8],[0,6,9,2,1,19,4,7],[],[0,6,7,9,2],[1,0,7,2,5,11,6,9],[1],[],[],[0,1,7,6,2,9,5,14,8],[2],[],
  [0,6,5,1,8,7,4,15],[7,4],[],[6,7,1,2,0],[9,7,0,8,4,2,6,1],[0,6,7],[],[0,7,19,2,9,6],[0,7,1,6],[2],[9,2,4],[1,0,7,5,2,9,19],[1,8,0,6],[0],
  [0,6,5,9,7,10,11],[1],[9,10],[],[2,1],[],[2,9,0,6,1,4,8,5,15],[],[6],[1,0,9,2,5,7,6,8,11,4],[15],[7,1,8],[1,8,7],[1,0,7,2,6,4],[1,5,0,2,9,7],
  [0,1,5,2,6,9],[1],[5,0,1,2,7],[10,1],[],[4,8],[0,1],[1,0,6,5,8,7,2,9],[0,1,7,9],[],[7,1,0,2,8],[6,0,7,2,9,1,5],[9,8,0,4,2],[1,5,2,7,0],[],
  [9,6,0,8],[2],[6],[0,1,5,2,9],[1,9,0,5,2],[],[2],[2,7],[4,0,2,7,1,5,9],[0],[5,6,0,1],[],[5,1,0,7,8,9],[5],[0,7,1,19,2,6],[7,1,2,0,9],[],[6],[],
  [0,7,2,9,11],[5],[0],[0,19,7],[1,0,3,2,5],[1,5],[8,4,0],[0,1,7,8,2,6,9,4],[0,9,1,5,11,2],[0,2,6,9,5,1,7],[1],[1,0,5,7,9,8,6,4,2,15],[5,9,2],
  [0,4,6,9,2],[3,6,5,0,1,7],[0,1,2,6,7,5,9,14],[],[0,2,10],[0,1,7,6,9,2,19],[],[0,7,6,1,2,9,8],[0],[],[1,5,0,6,2,15],[0,2],[14,11,6,1],[],[1,0],
  [2,0],[0,9,2,3],[4],[0,5,2,1,6],[0],[1,0,6,5,4,2],[0,7,6,1,2,19,11,9,4],[1,8,0,7,2],[0,6],[0,2,6,1,19],[5,4,9,1,7,8,0,2],[],[],[1,3,0,7,2,5],
  [9,0,2,19,7],[2,9],[],[1,0,9,6,7,19,2,8],[7,1,0,2,8],[1],[0,1,3,2,6,7,5],[2,9,0,12,7],[6],[0,2,5,1,10,9,3],[9,0,6,7,19,1,2],[6,0,1],[0],
  [2,9,0,4,6,1],[4,7,1],[0,1,7,2,5,3],[],[9,10],[4,9,2,7,6,0],[],[7,0,1,4,6,2,8,15],[0],[0,7,1,2,9,5,6,15,4,8],[2,15,7,0],[],[2,4,0,1,9,10],[1],
  [1,2],[0,4,6],[2],[0,7,6,1,19],[9,2],[7,2],[0],[0,7,1,5,3,2,6,10],[1],[0],[0,2],[9,7,4],[5,1,0,9,2,4,15,6,7,19,10],[0,6,2],[0,7,5,19],
  [5,7,0,1,9,8,2],[1,7],[],[0,7,1,2,8],[1,0,7,5],[15,4,0],[],[1,8],[2,9],[0,6,1,2,9,7],[],[4,2],[],[0,1],[],[1,7,0,2,5,6,4,15,8,11],[],
  [0,7,1,9,2,6],[],[0,7,6,9],[],[1,0,9,7,2,19,8],[],[1],[1,7,2,9,0,6,11],[],[5,8,1],[],[],[],[0,9],[8,1,0,9,4],[],[0,7,1,15,4,2,8],[2,9,11,0,5],
  [],[0,5,1],[7,9,0,1,8,2,4],[7,0,6,1,4,2,15,8],[6],[19,9,0,2],[],[1],[0,3,1,5,9],[0,2,7,9,1,4],[7,0,1,2,10],[],[1,8],[0,2,1,7,6,4,9,15],
  [1,8,4,2],[],[0,1,4,6,7,9,2,10],[5,1,0,2,10,11],[0,7,9,1,2,8,4],[15,0,7,1,2,14,6,4,9,8],[0,6,1,3],[7],[1,8,0,5],[0,6,9],[0,7,1,6,2,10],[],
  [2,9,0,1,7],[6,4,9,15,0,2],[],[4,0,6,2],[0,19,9],[1,8,0,5,2],[],[1,0,4,2,5,15,8,9],[0],[],[],[8,1,7],[1,8,6,7,0],[0,1],[7,2,9,0,1,5,8],
  [1,0,5,7,2,11,9,3,8,19,6],[2],[6],[1,9],[2],[0,6,8],[0,1,9,6,2,3],[1],[6,0,1,2,7],[0],[0,5,1,9],[4,1,0,2,7],[0,1,6,2,4,10,8],[0,1,7,5,8],[],[],
  [],[0,2,1,9,19],[5,0,8,6,4,15,2,1],[7,0,2,10],[6,5,2,0,1],[1,4],[0,7,2,1,11],[0,7],[2,15,0],[],[0,1,2,9,5,7,15,6,4],[],[1,0,4,7,6,2,8],[5,0,2],
  [],[],[0,9,1,7,2,6,19,12],[4,0,19,9],[0,6,1,5,8],[0,1,5,2,7],[0,7,1,6,4,2],[5],[9,2],[],[2,1,0,5,6,10,9,11,8],[1,9],[],[],[2],[0,8,1,2],[0,7],
  [],[1,0,2],[],[0,1,5,11,2],[0,7,1,6,2,19],[2],[2,0,11],[],[0],[1],[9,0,7,1,2,19,15],[6,4,15,0],[1,0,8],[1],[0,1,2,7,4,10],[9,2,4,0,8,1],[],
  [0,1,2,10,7],[],[0],[6,1,0,9,7,8,15,2,19,4],[0,5,1,2,9,7,11,14],[1,0,2,9,7,5,8,15,4],[6,0,7,19,1,8],[6,0,2],[2,7,0],[0,7,1,2,19,6,8,9,5],
  [0,1,2,4],[0,9,2,7],[],[0,2,6,9,7],[1,0,7,4,2,6,19,15],[],[1,8,4],[2,4,9],[0,7,6,10,4,1],[0,1,5,19,6,9],[1,3,0,7,2,5],[],[0,15,2,6,7,14,1],
  [0,1,7,11],[0,9],[],[1],[6,0,7,9,4,8],[7,0,1,2,6,15,9,4,8],[6,2,0],[],[],[0,1,4,7,6,2,8,5,15],[0,6,7,4],[0,6,7,19],[],[2,0,7,11,9],[2,0],[0],
  [],[],[5,0,1,6,9,2,8,19],[],[9,7,2,0],[0,1,6,9,2,8,7],[],[0,1,2,7,5,4,9,6],[4,0,8,1],[2],[],[],[1,0,5,8,2,4],[0,7,2,1,5,9,8,4,14,15],
  [1,0,6,7,19],[0,1,2,6,7,11,3],[0,1,7,2,5,3],[1,0,2,9,4],[7,1,2,0],[9,4,0],[0,1],[2,9,4,0],[0,6,1,2,10,7,15,9],[],[1,0,11,2,10,5],[],[1,5],
  [9,2],[0,7,2,1,6,10],[],[4,6,0,10],[0],[6,0,3],[0,7,1,19,2,6],[1,5,0,7,11,8,2,15,10],[1],[1,7,4],[],[1,7,8,9],[0],[7,0,1,5,2,4,6,3,9,8,15],
  [0,6,1,2,7],[0,19,9,6],[0,1,9],[1,0,10],[0,1,5,9,7,2,14],[1],[0,6,8,7],[],[],[1,4,0,2,9,8],[],[],[7,0,6,1,9,2,4,3,5,8],[1,0,2,5,7,8,9],
  [5,9,11],[9,2,0,7,4,15,6,3],[],[9,1,0,2,19],[0,1,2,7,15],[9,2],[],[6,0,7,2],[1,0],[],[0,1,6,2,7,9,10,19],[9,1,0,4,2,13,19],[],[0,7,2,1,9,5,8],
  [],[0,1,6,2,7,9],[0,1,9,7,2,11],[1,4,0,7,2,9],[7,6,0,1,2,9,8],[],[0,2,5,1,7,6,8],[1],[0],[],[2,7,0,6,5],[],[1],[],[8,1,0,2,4],[15,4,0],[],
  [0,7],[0,7,1,2,15,6,4,5,9],[],[],[0,1,4,8,5,2,9],[7,0,9,4],[0,8,1,7,2,9],[0,5,1,8],[],[],[0,1,4,6],[1,6,0],[1,0,9,4,15,2],[10,0,2,1],[],[],
  [0,1,9],[],[],[0,7,2,1,4,9,8,15],[1],[],[9,0,7,4,1,2,6,15,8,19],[2,15,0,4,9],[],[8,1],[2,4],[],[],[7,5],[7,0,6,1,2],[0,9,2,15],[0],
  [0,7,1,6,4,2,9],[],[1],[4,6,10],[6,2,0],[2,9,7,0,1,19,5,8],[1,5],[1],[4,1,8],[1,9],[0,1,6,2,9,7,14],[1,2,15,0],[],[10,0,2],[7,0,6,9],[1],[0,7],
  [1,0,6,2,9,3,7],[],[19,6],[5,1,0,2,7,9],[0,4,7],[7,1,0,2,5,8],[15,2,0,9,6,4],[4,2,0,9,1,6],[0,7,1,2,6,9,15,11],[8,9,1,4,0],[],[0,8],
  [9,7,1,0,15,2,8,19],[1,8,0],[9],[0,6],[],[6,0,9,7,10,2],[1,8],[1,0,8,7,9,4,2,6,19],[1,9,0,2,5,7,19,4,15],[],[0,9],[7,0,1,8,2,9],[2,0,1,4,9,15],
  [0,1,19],[],[1,2],[1,0,5,2,7,4],[0,7],[1,0,2,5,9,8,4],[10],[0,1,7,15,2,4,9],[],[0,6,1,7,2],[1,0,7,2,9,5,8],[1,7],[1,0,8,5,2],[5,1,7],[2,0,6],
  [0,1,7,9,4,8,2],[0,4,2,9,1,8,7,15],[],[2],[9],[1,5,9,4,8],[1,2,0,7,4,8],[11],[7,1,6,0,5,9,2,8],[2,9,7,1],[0,1,5,2,9,7,14,8],
  [9,0,2,1,19,6,4,15],[0,7,1],[],[0],[0,4,1,10],[0,6,7],[0,1,5,4,9,19,2,15],[],[0,1,19,2,5],[],[5,1,0,9,2,19],[],[0,1,7,6,2,19],[0,9,5,8],
  [1,0,5,2,8,7],[19,4,2],[],[0,1,2,7,10,9,19],[2,7,0,1,9],[],[1,8],[1,2],[1,0,7,8,9,2,5,4,14,19],[2,7,5,0,9,1,8,4],[0,6,2,1,9,19,7],
  [0,1,7,6,2,4,9],[],[],[1,8,0,4],[0,9,1,19,4],[0,7,6],[2],[0,1,7,2,5,9,11,8],[2],[5,1,0,2,10,9],[],[7,1,0,6,9,2,8],[0,7,2]]

def creditAdvice05 := bank creditData05

def creditSites05 : List (Fin 232) := [6,11,22,33,42,53,70]

def test05 := test (root 0 5) creditAdvice05

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def creditData35 : Array (List (Fin 23)) := #[[8,0,1,9,2,4],[0,1,5],[0,1,2],[0,1,5,8,7,2,6,11,10,4],[6,0,1,4,5,10,11,7,15],[0,7,4,2,9,11],[6,0],[],[0,1,5,9,8,11],[0,1,3,6,10],[4,1,9,0,12],
  [0],[8,12,2],[0,9,6],[0],[0,1,9,7,2,5,13,8],[6,0,7,12],[2,0,15,7,11,4],[0,1],[1,9,0,11,8,2,5,3],[0],[1,0,9],[],[0,1,2,4,8,9],[1,11,22,8,2],
  [0,2,7,9,4],[8,9,10],[0,6,15,7,1,11],[8,6],[0,6,2],[1,5,9,11],[4],[0],[0,6,9,3,2,5],[5,2,11,4,9,7],[1],[7,9,0,6,2],[11],[0,1,11,7],[1,5,9],
  [0,1,2,9,6],[],[],[0,7,1,5,11,6,9],[1],[],[2,0,4,1,9,5,7,14,10,6,8],[1,2,0,11,9,5,4,6,7,15,8],[1,2,5,6,9,7,12],[0,9,5,11,8,7,1,2,6],[1,0],
  [1,0,8,2,9,4],[5,1,0,11,7,2],[],[9,1,4,0,5,15,7,6,2,11,8],[],[1,0,5,2,9,3],[1,0,7,5],[1,8,2],[0,2,9,1],[1,5,2,11,0],[1,0,6],[8],[2,4],
  [0,10,2,9,3],[1,9],[4,0],[5,1,11],[9,10,6,0,14,2],[1,0,2,5,9,8],[4,2,0,8],[0,6],[0,1,6,9],[2],[0],[],[],[2,4,8,1],[9,0,1,11,2,4,5,6,8,15,3],[],
  [1,0,5,2,4,11,8,3],[2,0,9,6,7],[0,1,8],[9],[10,0],[0,1,3],[0,1,8,4,15],[2,9,0,1,8,6,11,4,15],[],[0,2,4,7,6,9],[1,4,8,2,6],[1,4,2,9],[],
  [0,1,4,15,2,6,9,8,11],[2,0,1],[6,0],[1,0,11],[],[2,6,0,8],[4,7,0,6,2,10],[4,2,0,1,5,7,10,14,6],[1,6,9],[6,4],[0,1],[0,5,1,2,9,8,4,7,6,11,15],
  [1,0,8],[9,11,2],[1,0,15,2,9,4,6],[1,0,11,6,2,15,9,7,4],[],[1,0,7,10,2,5],[0,1,9,2,7,11,6,10],[0,2,9],[0,2,1,9,7,10,11],[0,1,4,2,8,9,15,5],[],
  [1,9,8,5,0],[0,7,1,2,11,8],[1,8,11,0,2,9,4,6],[9,1,8,5,0],[5,0,1,2,6,10,8,11,3],[2,9,4,6,8,1],[0,11],[0,9,6],[1,0,11,10,2,7,9,5,6],
  [2,0,1,9,4,15],[0,5,1,2,7,4],[0,8],[1,0,9,2,5,7,8,14,6],[2,9,0],[],[6,1,0],[4,15],[0],[9],[0,7,6,1,3,4],[1,0,9,6,10],[4,5,1,9],[1,9,5,2],
  [0,1,2,6,12,8],[1,8,0,5],[1,2,0,9,4,6,3,5,15,14],[2,5,0,1,7,4,15,8],[5,9,0,4,1],[4,2,9,10],[1,0,5,2,4,11,7,9],[15,5,1],[1,9,2,0,5,7],[15],
  [1,0,8,5,2,9],[1,0,7],[8,0,1],[8,1],[2,7,0,15,9],[1,0,2,11,9,5],[9,1,0,2,4],[0,7,2,9,11],[9,0,1,11,2,4,15],[9,6,15,4,2,8,0],[0,7,1,2,9,3],
  [2,0,4,7,9],[0,6,9],[9,2,0,4,5],[0,15,4,2,8,11,1],[],[4,5,8],[],[9,4,2,6,0,15],[9,2,6,0,4,1,5,11],[0,7,2,9],[5,2,8,1,9],[11,1],[9,8,13],
  [2,4,0,1,9,7,5,6,15,3],[1,0,9,2,11,5],[9,8,7,5,0,1,2,11],[],[0],[0,1,8,9,2,4,5,11,6,7],[1],[],[0,9],[6,0,1],[1,5,11,9,0],[],[],[1,9,4,13,2,7],
  [],[11,5,8],[0,9,1],[0,9,2,6,4],[0],[],[0,9,1,7,2,6,11],[8,0],[0],[0],[],[],[],[0,8],[2,0,6,11,1],[0,7,1,9,5,3,2],[0,7,1,9,6],[5],
  [7,6,15,0,2,1,4,8],[1,7,9,4,8,0,2],[4],[1,7,0,8,9,2],[0,5],[2,1,5,9,4],[0],[0,1,2,9,7],[0,6,1,7],[0,5,2,7,9],[0,1,10,9,6,8,4],[1,0,7,2,9,8,5],
  [1,5,6,2,0,11,8,10,7],[4,0],[4,5],[2,10,6,15],[],[1,5,2],[2,0,9,7,10,6],[4,1,8],[9,0,2,1,7,15,5,11,6,8,4],[0,7],[1,0,5,9,7,8,2,14,4],
  [2,0,7,9,11,10],[11],[1,8,4,5,0],[0,7,9,2],[2,9,0,11,5,4,1,8],[9],[1,0],[6],[2],[9],[4],[2,1,4,9,0,11,10],[],[1,0],[0,1,5,11,9],
  [0,6,2,5,1,3,12],[0,4],[9,7,0,1,5],[0,9,1,2,15,8,4],[5,6,1,9],[0,6,9,1,2,7],[4],[0,1,6],[0,1,5,2,9,3],[],[9],[],[0,7,1,11,2,13],
  [0,1,8,4,7,10,9,5,2],[2,9,4,0],[0,9,5,1,2,7,15,11,14,4,6,8],[],[],[1,9,0,2,6,7],[4],[0,2],[11,0,4,6],[0,4,2],[1,0,5,2,6,9,4,8],[0,1,9,2],[],
  [4,1,5,9],[2,1,8],[1,2],[0,7,2,9,1,11],[1,11,4,0],[2,9,4],[5,0,1,11,10,6,2],[],[0,1,9,11,2,5,6,10],[1,0,9,5,2,8,7,4,11],[2,0],[7],
  [0,1,6,5,2,8,10],[],[4,15],[9,7,0,11,1,2,6,10],[0,7,9,11],[1,8,0,2,4],[0,1],[],[0,1,7,2,9,11],[9,1,0,4,6,8,5,2,15,11],[1],[9],[],[5,0,1,2,9,3],
  [1,0,5,2,3,7,4,6,12],[0,6,9,2,1,10,11],[0,7,6],[7,0,1,2,9,3],[9,2,0,1,6,3,11,5],[7,0,6,4,2,9,15],[0],[],[],[5,1,8],[9,2,0,14,15,4],
  [1,0,5,4,8,9],[0,1,11,6,7],[0,1,3],[2,1,9,4],[9,5,4,13,2,7,1,0],[0,15,1,2,4,9,7,8],[1,5,11,9,2,0],[0,7,9],[0,1,6,7,2,5,3],[0,1,8,9,5,6],
  [0,6,1,11,10],[0,7,1,6,9,8],[0],[0,2,1,9,4,7,6,8,11],[0,1,9,2,15,6,11,14],[2,4,8,0,7,1,6,11],[2,0,4,9],[0,9],[11,0],[0,1,6,2,7,8,9],[0,1],
  [0,6,10,1,4,2,8,9],[1,8,5,0],[5,1,10,8],[3],[0,10,13,1],[15,1,9,5,0,2,14,4,6,8],[5,1,11,3],[0,1,8,4,2,11,6,15,13],[0,9,6,7],
  [1,6,11,0,4,9,15,2,5],[0,9,6,2],[1,0,2,5,14,8,7],[4,0,2,7,1],[0,6,9],[],[0,8,1,4],[5,0],[1,9,11,4,8,2],[5,1,11,8,7,0,2],[1,0,2,9,4,8,6,15],
  [4,9,0],[13,0,1],[0,7,10,6],[1,0,6,2,11],[2,9,1,6],[0,8],[],[2],[],[2,9,1,0,15,6,11,8,4],[5,1,8,11,2],[1,5],[0,4,1],[9,1,3],[1],[0,5,1,4,8],
  [6],[1,2],[],[0,10,1,7,2,6],[0,2,1,10,7],[],[6,0],[],[0],[6,0,5,8,15,2,4,1],[9,1],[1,5,8,6,11,0,12,2],[0,6,2,1,15,9,10],[7,10,0,9,1,4],
  [0,6,9,1,4,5,2,8],[],[2],[0,1,2,5,4,9,10],[2],[4,9,0],[5,1,11],[0,2,7,5,9],[2,8,4,5,1,14,7,0,15],[],[6,0,2,9,10],[0,2,9,6,1,5,13],[1,9,8,4,5],
  [1,6,0,4,8],[],[0,9,1,2,14,7],[1,4,0,2,5],[5,2,6,10,8,1],[0,6,9,7,11],[],[0,1,4,6],[1,0,9,2,5,3],[9,7,13],[7,1],[0,7,1,2,11,9,6],[1],[6,0,1],
  [0,1],[0,1,9,2,6,7,11],[1,5,0,8,11,2],[0,15,1,2,8,4],[0],[0,8,1,4],[0,1,9,2,15,11,8],[0,1,5,7,2,11,10],[1,6,0],[1,0,10,2],
  [1,11,6,8,9,10,2,0,7],[0],[0],[9],[0,1,4,8],[0,1,9,2,7,8],[2],[0,9,1,7,2,11],[1,5,2,9],[1,0,5,2,8,11,15],[0,1,15,8,2],[1,8],[0],[1,9,2],
  [0,1,2],[2],[1,0,11,2,5,6,7,9,15,4],[9,2,4,6,8,15,11],[9,0,1,2,4],[0],[9,2,15,11,4,0],[0,1,2,6,9],[1,0,11,2,4],[1,8],[0],[0,9,10,6],
  [0,2,9,1,15,14],[0],[0,6,1,10,2,4,8],[1,4,0,8,6,2],[1],[9,0,1,6,8,7,4,11],[0,7,2,1,6],[0,6,9,11,8],[0,7,9,15,10,2],[0,6,7],[9,1,8],
  [0,2,9,6,1,4,11,8],[0,7,6,1,2,4,5,8,9,11,15],[1,0,4,5,11,2,14,10,15],[2,9],[9,0,8,1],[9,11,4,0],[0,1,9,2,6,3],[0,1,2,9,7,8],[0,6],
  [0,9,6,4,1,8,2,15,14,7],[5,1],[0,2],[0],[5,11,6,0,3],[8,1,0,11,9,2,7,4],[2,4,1,9,0,5,8,15,6,11],[7,1,0,6],[1,0,9,6,8],[9,5],
  [0,1,2,9,8,15,7,5,4,11,6,14],[1,0,2,10,9,11,4,6],[0,1,6,4,2,8,15],[0],[1,8,4,0],[0,1,2,15],[4,9,0],[1,9,0,6,12,2],[9,2,4,0,6,1,5],
  [0,5,1,7,9,2,11,14],[],[0],[1,0,11,12],[1,0,8,6],[0,9,14,4,13,11,2,7,8,15],[],[],[9,0,2,1,4,11,15],[],[9,6,0,5,2,8,4,15,7,1,11,14],[0,7,2,1,6],
  [1,5,2,9,11,0],[1],[6,0,7,4,1],[],[0,8,5],[4,1,5,0,9],[0,8,1,6,10,2],[9,0,15,11,1,7,4,10],[0,6,1,9],[1,5,11,8,2,0,9],[5,0,1,2,9,3],[10],
  [0,1,2,9,5,7,4,14,11,6,8],[6,0,15,10,9,2,4],[5,3],[2,4,9,11,10,5],[0,10],[10,0,7,9],[1,2,5,0,4,11,9,7],[7,4],[1,0,8,2,5,4,9,7],
  [0,1,2,6,9,8,11],[6,3],[6,0,10,8,5,1],[4,1,5,2,8],[5,1,2,0,8,9,11,6],[9,2,0,7,4,10,8,1],[10,0],[5],[1,0,7,15,9,10,2],[1,5,4,9,0],
  [0,2,6,1,9,7,10,8,12],[6,0],[0,1,9],[0,1,9,2,7,5,4],[2],[4,8,1,15],[0,6,1],[0,1,9],[5,0,2],[],[0,7,2,6,12,1],[8,1],[1,8,5,11,0,2],[8,0,1],
  [1,0,11,2,5],[6],[9,5],[0,9,4,15,2],[2,4,8],[0,1,15,2,3,9,4,5],[1,9,0,2,8,15,11,4,6,7],[0,1,2,5,11,9,6,10],[1,15,0,9,2,4,11,5,6],
  [5,0,1,2,8,9,6,7,11],[9,4,11,1],[1,0,4,8,2,11,9],[0,7,9,5,2,11],[1],[0,1,11,5,9,8,2],[1,0,5,2,9,8],[15,2],[0,4,1],[1,7,0,8,2,4],[2,9,4,14],
  [0,1,2,9,15,7,10,6],[1,4,0,2,9,11],[0,8,6,1],[],[1,0,6,11,7],[],[0],[0,8,1,6,7],[],[0,1,15,2,4,10],[0,1,8],[9,0,1,2,6],[1,8,0,6,11],[6,0,10,2],
  [0,8,1,2,9,7,4,6],[],[2,9,0],[],[1,0,2,9,5,6],[1,8,11],[1,0,8,2,9,4],[2],[0,6],[0,6,1,10,4,9,8],[8,0,1,5],[0,1,11,9,2,8,7,6,12],[0,1],
  [0,11,1,6,9,8],[],[9,11,4],[1,8,9],[2,15],[],[9,4,11,2,0,15],[],[0,1],[9,2,5,4,15,14,3],[],[0,6,2,7,4,9],[4,9,7,2,11],[4,0],[0,6,1,15,4,2,10],
  [9,2,4],[2,15,4],[1],[0,7,9,1,2,6,8,15,13],[],[2,0,10,9],[2,1,4,15,0,6,8,9,5],[0,8,4,11,7,2,1],[],[1,4,0,8],[1],[1,4,0,6,2,9,8],[10,7,0,6,9],
  [1,0,2,11,9,7,8],[4],[5,0,2,1,4,10,6,11],[1,0],[0],[9,2],[2,1,4,0,9,15,5,7],[0,7],[1],[1,9,2,0,5],[2,1,4,5,9],[],[1,4,0,2,9,8],[0,1,9,10],
  [4,0,7,11,9],[11,0,1,5,6],[],[8,7,9,2,1,10,0,6],[1,0,6,9,12],[0,7,1,2,9,6],[0,1,6],[1,8],[],[],[0,9,2,7,1,5,10],[2],[],[],[0,10,1,2,6],[6,0],
  [1,9],[0,1,6,11,2,8,9,10],[1,2,4,9,8,6,11],[0,1,9],[1,0,6],[1,8,4],[0,11],[6,0,15,4,11],[5,0,1],[],[0,7,1,10,6],[0,6,2],[2],
  [1,0,6,15,4,2,8,5,11,9,7],[],[],[2,5,9,1,3],[0,6,2,1,8,4],[0,6,4,8],[9,2,11],[1],[0,6,1],[9,0],[4,2,1,0,5,8,7,15],[1,2,9],[0,7,1,9,2,5,14,11],
  [9,8,4,2,1],[1,11,5],[2,15,4,9],[4,2,8,1],[],[13,8],[0,11,1],[0,1,2,6,4,9,8,15,11],[2,0,9,1,15,6,8,4,11],[0,1,5,9,6,8,4,7],[0,6],[0,9],
  [1,8,0,5,2,7,9,4,6],[],[],[],[7,0,6,9,1],[1,5,2,9,7],[],[0,11,2,7,1,9,8,4],[1,0,11,6,5,10,2],[0,9,6],[0,7,1,6,8],[],[6,0],[5,0,7,9,1],
  [0,7,1,9,10],[],[0,6,11,9,2,10],[9,1,0,2,11,6,4,8],[0,1,8,15,9,2,5],[0,6,9,2,1,7,11],[0,1,11,9,2,7,8,5],[0,6,4],[],[9,1,0,5,2,8],
  [0,7,5,2,1,9,11,8],[2],[4,0,1,2,5,9,14,10,8,6,11,3],[],[1,0,15,2,5,4,9,7,6,8],[1,4,8,9],[1,2,9],[1,9,8,4,5,2],[0,4,9],[1,5,0,8],[9,1,11,14],
  [1],[0,6,9,1,2,12,8],[0,7,1,2,9,6,5,11,3],[1],[0,1,2,6,15,10],[9,2,4,6,0,1],[1,14],[2,9,0,1,11,4],[0,1,12,8,11,6],[5,1,0,9,10,2,3,6],[1],
  [0,1,8,2,9],[1,9,6],[1,6],[6,0,9,7,11,2],[0,2,1,5,8,10,9,11],[0,1,5,4,9,2,6,15],[0,1,7,5,9,2,10],[1,8,0,7,9,13],[9,2,0,4,6,1,8,15,11],
  [0,1,11,9,2,5],[],[5,1,4,2,15],[],[2,0,7,10,9],[1,2,4],[1],[1,0,6,2,9,4,11,5,8],[0],[0,1],[2,9,4],[10,9,6,0,1],[5,0,1,9],[5,1,9,8,11,2,0],
  [15,2,0,4,1,9,6,8],[1,0,6,8,4],[7,9,6,0],[2,1,4,0,5,9],[1,8,0,9,2,7],[2,0,9,1,4,6,8,15,11],[9,0,1,5,4,2,6,7,11,15,14],[1,4],[],[1,5,0,2],
  [9,4,0,7,11,6,1,2],[0,6,1,4],[1,8,6],[1],[0,9,1,2,7,6,11],[6],[1,15,0,2,6,4],[6,10,9,0,11,1],[1],[1,0,9,5],[0],[0,1,5,2,7,14,9,10],
  [7,0,6,2,9,1,8],[0,6],[0,2,7,1,5,4,9,15,6,8,11],[9,11,1,15,8,6,21],[0,6,9,10,1,2],[1,11,15,2,6,5,9,4],[8,1],[0],[10,0,4],[0,5],[7,11],[0,2],
  [9],[2,9,4,1,15],[4,1,3],[6],[0,15,1,9,2,6,8,4],[1,0],[],[],[],[0,7,5,2,9],[1],[10,0],[4,9,10,7,5],[9,0,2,12],[4,1,9,0,2,8,3,5],[],[0,9,2,7],
  [2,0,4,9,11,10],[4,1,2,10],[9,0,6,4,1,15,2,7],[8],[0,9,1,2,15,7,8,4],[0,5,9,6,2,1,7,10],[0,6,8,1],[1,0,4,2,9,6,10,15,11,8,7,5],[4,2],[0,4,9,3],
  [1],[1,8,5,2],[1,0,2,5,9,11,8],[0],[2,1],[2,1,5,11,9],[9],[2,5,9,14,15,4,7,0,1,6,11],[],[1,0,8,2,9,4,7],[1,4,8,0],[0,7,2,9,1,5,8],[],
  [2,9,5,4,0,1,6,8,15,11],[0,6],[0,1,7,5,9,4,2,11,8],[0,1,3],[1,15,0,2,4,6],[7,4,9],[4,2],[5,1,8,0],[1,7,0],[0,6,1],[1,0,5,9,2,6,7,4,15,13],[],
  [10],[5],[0,1,6,2,4,9,11],[11,9,4],[0,9,7,1,2,12,6],[8],[],[0,2,1,5,7,14,9],[0],[2,4,9,5,15],[0,9,1,2,5],[1,0,5,11,2,10,6],[1,2,0,7,5,8,6,9],
  [0,12,11,2,5,3],[2,9,4,0,15],[0,1,6,4,9,2,11,3],[],[8,1,0],[0],[6,4],[0,1,6,8,10,2,4],[0,6,1],[],[14],[11,1],[4,0,1,2,10],
  [9,0,1,6,2,8,15,11,4],[11,1,0,9,2,3],[0,2,7,9,5,11,1,3,8],[9,0,2,15,1,7,11,3],[10,1,0],[8,1,4,9,0],[1,0,9,8,5,11,2,6,7,4],[9,0,1,5,2,7,6],
  [9,2,0,1,4],[1,9,4,5,2],[7,9,1,0,4,10,2,5],[0,9,7,6,2],[2,7,0,1,4,9,10],[11,2,0],[7,1,0,2,6],[2,9,4],[0,1,8],[6,0,1,9,4,2],[0,7,12,1,9,6,2],
  [0,6,1,2,9,4,7,15,11,8],[1,0,2,11,9,5],[0,7,2,1],[0,14,6],[6,0,9,10,4,1,5],[2],[6,7,9,0],[5,4,2,15],[0,7,9,2,4,8,10,1,15],[0],[0,1],
  [0,5,9,1,2,6,10],[0,1,5,2,9,15,4,6,3,7],[0,6,1,14,7,2,9,10,22,8],[8,0],[6,9],[],[9,2,4,0,15],[4,1,2,5,0,9,7,8,10],[5,2,0,1,3],[0,1,4,9,6,8,2],
  [0,7,9,1,4,2],[0,9,2,1,15,4,8],[],[1,0,9],[9,6,1,7,0,4,2,15,14],[0,1,2,7,13,8],[1,8],[0,1,5,8,2,7,9,3],[1,0,8,5,15],[2,0,1,15,9,4,14,8],
  [1,5,2],[],[0,1,2,9,12,6],[4,2,9,10,1,8,0],[2,9,15,11],[2,9],[],[1],[0,4,7,1],[0,5,11],[0,7,1],[1,0],[2,6],[9,2,4,15,14],[1,7,9,0,6],[0],[1],
  [],[],[0,2,4,10,1,9,6,11],[1,5,0],[0,7,9,10],[0,6,1,9,10,4,8],[5,2],[5,11,1,8],[1,8],[1,0,5,9,6,21],[0,6,9,1,10],[7,0,6,5,1],[0],
  [1,5,2,11,0,7],[2,0],[1,9,5,8],[1,4,0,8],[0,2],[2,4,1,8],[0],[1,4,0,8,6],[],[1,4,8],[1,9,0,2,8],[7,1,13,2,6,0],[9,15,1,11,4],[],[0,9,2,1,7],
  [1,5,4,11,8],[],[14,15,2,11,0,8],[9,15,2,1,0,5],[6],[7,0,5,2,9,4],[2,6,0,10],[],[],[1,2,5,9],[0,6,1,8,9,4],[],[1,4,0,9,8,6,5,11],
  [0,9,2,1,6,4,11,15,8],[0,9,2,1,7,5],[1,0,6],[],[9,6,5,0,2,7],[1,0,2,5,7,4,9],[0,5,1,2,9],[],[0,9,7,1,5],[],[],[2,9,4,15,6,8,0],[0],[1,15],
  [1,2,0,9,5,10,8],[],[9],[9,5,1,15,7,11,2],[1,0,4,8],[1,11,5,0],[6,0],[0],[2],[8,0,4,9,2,6],[1,4,8],[5,0,1,8,7],[5,9,1],[15,14,9,2,1,0],[4],
  [1,0,4,2,8,6,11,9,15],[7,9,0,6,15],[0],[0,1,7,2,9],[0,1,7,9,2,4],[],[0],[0,2,9,4,15,1,7,8],[0,7],[2,0],[4,8,1],[0,1,3,5,6],
  [1,9,8,5,2,4,6,15,11],[0,6,10],[1,2,9,0,11,7,6],[1,0,5,9,2],[0,9,6],[],[9,2,11,6,15],[9,0,1],[0,1,8,4,6,2],[9,2,8,15,1],[0,1,9,7],
  [0,1,9,2,5,4,7,6,3,11,14]]

def creditAdvice35 := bank creditData35

def creditSites35 : List (Fin 232) := [0,11,22,33,42,57,70]

def test35 := test (root 3 5) creditAdvice35
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths05_000 : List (List ℕ) := [[0],[1],[2],[3],[4]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_000 : ∀ i : Fin 5, test05 (paths05_000.getD i.val []) = false := by decide +kernel

def paths05_001 : List (List ℕ) := [[5],[6]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_001 : ∀ i : Fin 2, test05 (paths05_001.getD i.val []) = false := by decide +kernel

def paths05_002 : List (List ℕ) := [[7],[8]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_002 : ∀ i : Fin 2, test05 (paths05_002.getD i.val []) = false := by decide +kernel

def paths05_003 : List (List ℕ) := [[9],[10],[11,0],[11,1],[11,2],[11,3],[11,4],[11,5],[11,6],[11,7]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_003 : ∀ i : Fin 10, test05 (paths05_003.getD i.val []) = false := by decide +kernel

def paths05_004 : List (List ℕ) := [[11,8],[11,9],[11,10],[11,11],[11,12],[11,13],[11,14],[11,15],[11,16],[11,17],[11,18],[11,19],[11,20],[11,21],[11,22],[11,23],[11,24],[11,25],[11,26],[11,27],[11,28],[11,29],[11,30],[11,31]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_004 : ∀ i : Fin 24, test05 (paths05_004.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths05_005 : List (List ℕ) := [[11,32],[11,33],[11,34],[11,35],[11,36],[12],[13],[14]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_005 : ∀ i : Fin 8, test05 (paths05_005.getD i.val []) = false := by decide +kernel

def paths05_006 : List (List ℕ) := [[15],[16],[17],[18],[19]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_006 : ∀ i : Fin 5, test05 (paths05_006.getD i.val []) = false := by decide +kernel

def paths05_007 : List (List ℕ) := [[20],[21]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_007 : ∀ i : Fin 2, test05 (paths05_007.getD i.val []) = false := by decide +kernel

def paths05_008 : List (List ℕ) := [[22],[23],[24],[25,0],[25,1],[25,2],[25,3],[25,4],[25,5],[25,6],[25,7],[25,8],[25,9],[25,10]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_008 : ∀ i : Fin 14, test05 (paths05_008.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths05_009 : List (List ℕ) := [[25,11],[25,12],[25,13],[25,14],[25,15],[25,16],[25,17],[25,18],[25,19],[25,20],[25,21],[25,22],[25,23],[25,24],[25,25],[25,26],[25,27],[25,28],[25,29],[25,30],[25,31],[25,32],[25,33],[25,34]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_009 : ∀ i : Fin 24, test05 (paths05_009.getD i.val []) = false := by decide +kernel

def paths05_010 : List (List ℕ) := [[25,35],[25,36],[25,37],[25,38],[25,39],[25,40],[25,41],[25,42],[25,43],[25,44],[25,45],[25,46],[26],[27]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_010 : ∀ i : Fin 14, test05 (paths05_010.getD i.val []) = false := by decide +kernel

def paths05_011 : List (List ℕ) := [[28],[29]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_011 : ∀ i : Fin 2, test05 (paths05_011.getD i.val []) = false := by decide +kernel

def paths05_012 : List (List ℕ) := [[30],[31,0],[31,1],[31,2],[31,3],[31,4],[31,5],[31,6],[31,7],[31,8],[31,9],[31,10],[31,11],[31,12]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_012 : ∀ i : Fin 14, test05 (paths05_012.getD i.val []) = false := by decide +kernel

def paths05_013 : List (List ℕ) := [[31,13],[31,14],[31,15],[31,16],[31,17],[31,18],[31,19],[31,20],[31,21],[31,22],[31,23],[31,24],[31,25],[31,26],[31,27],[32],[33]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_013 : ∀ i : Fin 17, test05 (paths05_013.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths05_014 : List (List ℕ) := [[34],[35],[36]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_014 : ∀ i : Fin 3, test05 (paths05_014.getD i.val []) = false := by decide +kernel

def paths05_015 : List (List ℕ) := [[37],[38],[39]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_015 : ∀ i : Fin 3, test05 (paths05_015.getD i.val []) = false := by decide +kernel

def paths05_016 : List (List ℕ) := [[40]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_016 : ∀ i : Fin 1, test05 (paths05_016.getD i.val []) = false := by decide +kernel

def paths05_017 : List (List ℕ) := [[41],[42],[43]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_017 : ∀ i : Fin 3, test05 (paths05_017.getD i.val []) = false := by decide +kernel

def paths05_018 : List (List ℕ) := [[44],[45]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_018 : ∀ i : Fin 2, test05 (paths05_018.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths05_019 : List (List ℕ) := [[46],[47],[48,0],[48,1]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_019 : ∀ i : Fin 4, test05 (paths05_019.getD i.val []) = false := by decide +kernel

def paths05_020 : List (List ℕ) := [[48,2],[48,3],[48,4],[48,5],[48,6],[48,7],[48,8],[48,9],[48,10],[48,11],[48,12],[48,13],[48,14],[48,15],[48,16],[48,17],[48,18],[48,19],[48,20],[48,21],[48,22],[48,23],[48,24],[48,25]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_020 : ∀ i : Fin 24, test05 (paths05_020.getD i.val []) = false := by decide +kernel

def paths05_021 : List (List ℕ) := [[48,26],[48,27],[48,28],[48,29],[48,30],[49],[50],[51],[52,0],[52,1],[52,2],[52,3],[52,4],[52,5]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_021 : ∀ i : Fin 14, test05 (paths05_021.getD i.val []) = false := by decide +kernel

def paths05_022 : List (List ℕ) := [[52,6],[52,7],[52,8],[52,9],[52,10],[52,11],[52,12],[52,13],[52,14],[52,15],[52,16],[52,17],[52,18],[52,19],[52,20],[52,21],[52,22],[52,23],[52,24],[52,25],[52,26],[52,27],[52,28],[52,29]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_022 : ∀ i : Fin 24, test05 (paths05_022.getD i.val []) = false := by decide +kernel

def paths05_023 : List (List ℕ) := [[52,30],[52,31],[52,32],[52,33],[52,34],[52,35],[52,36],[52,37],[52,38],[53,0],[53,1],[53,2],[53,3],[53,4],[53,5],[53,6],[53,7],[53,8],[53,9],[53,10],[53,11],[53,12],[53,13],[53,14]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_023 : ∀ i : Fin 24, test05 (paths05_023.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths05_024 : List (List ℕ) := [[53,15],[53,16],[53,17],[53,18],[53,19],[53,20],[53,21],[53,22],[53,23],[53,24],[53,25],[53,26],[53,27],[53,28],[53,29],[53,30],[53,31],[53,32],[53,33],[54]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_024 : ∀ i : Fin 20, test05 (paths05_024.getD i.val []) = false := by decide +kernel

def paths05_025 : List (List ℕ) := [[55]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_025 : ∀ i : Fin 1, test05 (paths05_025.getD i.val []) = false := by decide +kernel

def paths05_026 : List (List ℕ) := [[56]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_026 : ∀ i : Fin 1, test05 (paths05_026.getD i.val []) = false := by decide +kernel

def paths05_027 : List (List ℕ) := [[57],[58]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_027 : ∀ i : Fin 2, test05 (paths05_027.getD i.val []) = false := by decide +kernel

def paths05_028 : List (List ℕ) := [[59]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_028 : ∀ i : Fin 1, test05 (paths05_028.getD i.val []) = false := by decide +kernel

def paths05_029 : List (List ℕ) := [[60]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_029 : ∀ i : Fin 1, test05 (paths05_029.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths05_030 : List (List ℕ) := [[61],[62],[63]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_030 : ∀ i : Fin 3, test05 (paths05_030.getD i.val []) = false := by decide +kernel

def paths05_031 : List (List ℕ) := [[64],[65,0],[65,1],[65,2],[65,3],[65,4],[65,5],[65,6],[65,7],[65,8],[65,9],[65,10],[65,11],[65,12],[65,13],[65,14],[65,15]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_031 : ∀ i : Fin 17, test05 (paths05_031.getD i.val []) = false := by decide +kernel

def paths05_032 : List (List ℕ) := [[65,16],[65,17],[65,18],[65,19],[65,20],[65,21],[65,22],[65,23],[65,24],[65,25],[65,26],[65,27],[65,28],[65,29],[65,30],[65,31],[65,32],[65,33],[65,34],[65,35],[65,36],[65,37],[65,38],[65,39]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_032 : ∀ i : Fin 24, test05 (paths05_032.getD i.val []) = false := by decide +kernel

def paths05_033 : List (List ℕ) := [[65,40],[65,41],[65,42],[65,43],[65,44],[65,45]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked05_033 : ∀ i : Fin 6, test05 (paths05_033.getD i.val []) = false := by decide +kernel

def paths35_000 : List (List ℕ) := [[0],[1]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_000 : ∀ i : Fin 2, test35 (paths35_000.getD i.val []) = false := by decide +kernel

def paths35_001 : List (List ℕ) := [[2],[3]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_001 : ∀ i : Fin 2, test35 (paths35_001.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths35_002 : List (List ℕ) := [[4],[5],[6,0],[6,1],[6,2],[6,3],[6,4],[6,5],[6,6],[6,7],[6,8]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_002 : ∀ i : Fin 11, test35 (paths35_002.getD i.val []) = false := by decide +kernel

def paths35_003 : List (List ℕ) := [[6,9],[6,10],[6,11],[6,12],[6,13],[6,14],[6,15],[6,16],[6,17],[6,18],[6,19],[6,20],[6,21],[6,22],[6,23],[6,24],[6,25]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_003 : ∀ i : Fin 17, test35 (paths35_003.getD i.val []) = false := by decide +kernel

def paths35_004 : List (List ℕ) := [[6,26],[6,27],[6,28],[6,29],[6,30],[6,31],[6,32],[6,33],[6,34],[6,35],[6,36]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_004 : ∀ i : Fin 11, test35 (paths35_004.getD i.val []) = false := by decide +kernel

def paths35_005 : List (List ℕ) := [[7]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_005 : ∀ i : Fin 1, test35 (paths35_005.getD i.val []) = false := by decide +kernel

def paths35_006 : List (List ℕ) := [[8],[9]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_006 : ∀ i : Fin 2, test35 (paths35_006.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths35_007 : List (List ℕ) := [[10],[11]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_007 : ∀ i : Fin 2, test35 (paths35_007.getD i.val []) = false := by decide +kernel

def paths35_008 : List (List ℕ) := [[12],[13]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_008 : ∀ i : Fin 2, test35 (paths35_008.getD i.val []) = false := by decide +kernel

def paths35_009 : List (List ℕ) := [[14],[15],[16],[17,0],[17,1],[17,2],[17,3],[17,4]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_009 : ∀ i : Fin 8, test35 (paths35_009.getD i.val []) = false := by decide +kernel

def paths35_010 : List (List ℕ) := [[17,5],[17,6],[17,7],[17,8],[17,9],[17,10],[17,11],[17,12],[17,13],[17,14],[17,15],[17,16],[17,17],[17,18],[17,19],[17,20],[17,21],[17,22],[17,23],[17,24]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_010 : ∀ i : Fin 20, test35 (paths35_010.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths35_011 : List (List ℕ) := [[17,25],[17,26],[17,27],[17,28],[17,29],[17,30],[17,31],[17,32],[17,33],[17,34],[17,35],[17,36]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_011 : ∀ i : Fin 12, test35 (paths35_011.getD i.val []) = false := by decide +kernel

def paths35_012 : List (List ℕ) := [[18]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_012 : ∀ i : Fin 1, test35 (paths35_012.getD i.val []) = false := by decide +kernel

def paths35_013 : List (List ℕ) := [[19],[20]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_013 : ∀ i : Fin 2, test35 (paths35_013.getD i.val []) = false := by decide +kernel

def paths35_014 : List (List ℕ) := [[21],[22]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_014 : ∀ i : Fin 2, test35 (paths35_014.getD i.val []) = false := by decide +kernel

def paths35_015 : List (List ℕ) := [[23],[24,0],[24,1],[24,2]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_015 : ∀ i : Fin 4, test35 (paths35_015.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths35_016 : List (List ℕ) := [[24,3],[24,4],[24,5],[24,6],[24,7],[24,8],[24,9],[24,10],[24,11],[24,12],[24,13],[24,14],[24,15],[24,16],[24,17],[24,18],[24,19],[24,20],[24,21],[24,22],[24,23],[24,24],[24,25],[24,26]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_016 : ∀ i : Fin 24, test35 (paths35_016.getD i.val []) = false := by decide +kernel

def paths35_017 : List (List ℕ) := [[24,27],[25,0],[25,1],[25,2],[25,3],[25,4],[25,5],[25,6],[25,7],[25,8],[25,9],[25,10],[25,11],[25,12],[25,13],[25,14],[25,15],[25,16],[25,17]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_017 : ∀ i : Fin 19, test35 (paths35_017.getD i.val []) = false := by decide +kernel

def paths35_018 : List (List ℕ) := [[25,18],[25,19],[25,20],[25,21],[25,22],[25,23],[25,24],[25,25],[25,26],[25,27],[25,28],[25,29],[25,30],[25,31],[25,32],[25,33],[25,34],[25,35],[25,36],[25,37],[25,38],[25,39],[25,40],[25,41]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_018 : ∀ i : Fin 24, test35 (paths35_018.getD i.val []) = false := by decide +kernel

def paths35_019 : List (List ℕ) := [[25,42],[25,43],[25,44],[25,45],[25,46],[25,47],[25,48],[25,49],[25,50],[26]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_019 : ∀ i : Fin 10, test35 (paths35_019.getD i.val []) = false := by decide +kernel

def paths35_020 : List (List ℕ) := [[27]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_020 : ∀ i : Fin 1, test35 (paths35_020.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths35_021 : List (List ℕ) := [[28],[29,0],[29,1],[29,2],[29,3],[29,4],[29,5],[29,6],[29,7],[29,8],[29,9],[29,10],[29,11]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_021 : ∀ i : Fin 13, test35 (paths35_021.getD i.val []) = false := by decide +kernel

def paths35_022 : List (List ℕ) := [[29,12],[29,13],[29,14],[29,15],[29,16],[29,17],[29,18],[29,19],[29,20],[29,21],[29,22],[29,23],[29,24],[29,25],[29,26],[29,27]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_022 : ∀ i : Fin 16, test35 (paths35_022.getD i.val []) = false := by decide +kernel

def paths35_023 : List (List ℕ) := [[30],[31],[32]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_023 : ∀ i : Fin 3, test35 (paths35_023.getD i.val []) = false := by decide +kernel

def paths35_024 : List (List ℕ) := [[33],[34],[35,0],[35,1],[35,2],[35,3],[35,4],[35,5],[35,6],[35,7],[35,8],[35,9],[35,10],[35,11],[35,12],[35,13],[35,14],[35,15]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_024 : ∀ i : Fin 18, test35 (paths35_024.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths35_025 : List (List ℕ) := [[35,16],[35,17],[35,18],[35,19],[35,20],[35,21],[35,22],[35,23],[35,24],[35,25],[35,26],[35,27],[35,28],[35,29],[35,30],[35,31],[35,32],[35,33],[35,34],[35,35]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_025 : ∀ i : Fin 20, test35 (paths35_025.getD i.val []) = false := by decide +kernel

def paths35_026 : List (List ℕ) := [[36],[37],[38,0],[38,1],[38,2],[38,3]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_026 : ∀ i : Fin 6, test35 (paths35_026.getD i.val []) = false := by decide +kernel

def paths35_027 : List (List ℕ) := [[38,4],[38,5],[38,6],[38,7],[38,8],[38,9],[38,10],[38,11],[38,12],[38,13],[38,14],[38,15],[38,16],[38,17],[38,18],[38,19],[38,20],[38,21],[38,22],[38,23],[38,24],[38,25],[38,26],[38,27]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_027 : ∀ i : Fin 24, test35 (paths35_027.getD i.val []) = false := by decide +kernel

def paths35_028 : List (List ℕ) := [[38,28],[38,29],[39],[40]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_028 : ∀ i : Fin 4, test35 (paths35_028.getD i.val []) = false := by decide +kernel

def paths35_029 : List (List ℕ) := [[41]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_029 : ∀ i : Fin 1, test35 (paths35_029.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths35_030 : List (List ℕ) := [[42]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_030 : ∀ i : Fin 1, test35 (paths35_030.getD i.val []) = false := by decide +kernel

def paths35_031 : List (List ℕ) := [[43],[44,0],[44,1],[44,2],[44,3],[44,4],[44,5],[44,6],[44,7],[44,8],[44,9],[44,10],[44,11]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_031 : ∀ i : Fin 13, test35 (paths35_031.getD i.val []) = false := by decide +kernel

def paths35_032 : List (List ℕ) := [[44,12],[44,13],[44,14],[44,15],[44,16],[44,17],[44,18],[44,19],[44,20],[44,21],[44,22],[44,23],[44,24],[44,25],[44,26],[44,27]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_032 : ∀ i : Fin 16, test35 (paths35_032.getD i.val []) = false := by decide +kernel

def paths35_033 : List (List ℕ) := [[45],[46],[47]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_033 : ∀ i : Fin 3, test35 (paths35_033.getD i.val []) = false := by decide +kernel

def paths35_034 : List (List ℕ) := [[48],[49,0],[49,1],[49,2],[49,3],[49,4],[49,5],[49,6],[49,7],[49,8],[49,9],[49,10],[49,11],[49,12],[49,13],[49,14],[49,15],[49,16],[49,17],[49,18],[49,19],[49,20],[49,21],[49,22]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_034 : ∀ i : Fin 24, test35 (paths35_034.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths35_035 : List (List ℕ) := [[49,23],[49,24],[49,25],[49,26],[49,27],[49,28],[49,29],[49,30],[49,31],[49,32],[49,33],[49,34],[49,35]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_035 : ∀ i : Fin 13, test35 (paths35_035.getD i.val []) = false := by decide +kernel

def paths35_036 : List (List ℕ) := [[50],[51,0],[51,1],[51,2],[51,3]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_036 : ∀ i : Fin 5, test35 (paths35_036.getD i.val []) = false := by decide +kernel

def paths35_037 : List (List ℕ) := [[51,4],[51,5],[51,6],[51,7],[51,8],[51,9],[51,10],[51,11],[51,12],[51,13],[51,14],[51,15]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_037 : ∀ i : Fin 12, test35 (paths35_037.getD i.val []) = false := by decide +kernel

def paths35_038 : List (List ℕ) := [[51,16],[51,17],[51,18],[51,19],[51,20],[51,21],[51,22],[52]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_038 : ∀ i : Fin 8, test35 (paths35_038.getD i.val []) = false := by decide +kernel

def paths35_039 : List (List ℕ) := [[53],[54]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_039 : ∀ i : Fin 2, test35 (paths35_039.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths35_040 : List (List ℕ) := [[55],[56]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_040 : ∀ i : Fin 2, test35 (paths35_040.getD i.val []) = false := by decide +kernel

def paths35_041 : List (List ℕ) := [[57]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_041 : ∀ i : Fin 1, test35 (paths35_041.getD i.val []) = false := by decide +kernel

def paths35_042 : List (List ℕ) := [[58]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_042 : ∀ i : Fin 1, test35 (paths35_042.getD i.val []) = false := by decide +kernel

def paths35_043 : List (List ℕ) := [[59],[60]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_043 : ∀ i : Fin 2, test35 (paths35_043.getD i.val []) = false := by decide +kernel

def paths35_044 : List (List ℕ) := [[61],[62]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_044 : ∀ i : Fin 2, test35 (paths35_044.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths35_045 : List (List ℕ) := [[63],[64,0],[64,1],[64,2],[64,3],[64,4],[64,5],[64,6],[64,7],[64,8],[64,9],[64,10],[64,11],[64,12],[64,13]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_045 : ∀ i : Fin 15, test35 (paths35_045.getD i.val []) = false := by decide +kernel

def paths35_046 : List (List ℕ) := [[64,14],[64,15],[64,16],[64,17],[64,18],[64,19],[64,20],[64,21],[64,22],[64,23],[64,24],[64,25],[64,26],[64,27],[64,28]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_046 : ∀ i : Fin 15, test35 (paths35_046.getD i.val []) = false := by decide +kernel

def paths35_047 : List (List ℕ) := [[64,29],[64,30],[64,31],[64,32],[64,33],[64,34],[64,35],[64,36],[64,37],[64,38],[64,39],[64,40],[64,41],[64,42],[64,43],[64,44],[64,45],[64,46],[64,47],[64,48]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_047 : ∀ i : Fin 20, test35 (paths35_047.getD i.val []) = false := by decide +kernel

def paths35_048 : List (List ℕ) := [[64,49],[64,50],[64,51],[64,52],[64,53],[64,54],[64,55],[64,56],[64,57],[64,58],[64,59],[64,60],[64,61],[65,0],[65,1],[65,2],[65,3],[65,4],[65,5]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_048 : ∀ i : Fin 19, test35 (paths35_048.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

def paths35_049 : List (List ℕ) := [[65,6],[65,7],[65,8],[65,9],[65,10],[65,11],[65,12],[65,13],[65,14],[65,15],[65,16],[65,17],[65,18],[65,19],[65,20],[65,21],[65,22],[65,23],[65,24],[65,25],[65,26],[65,27],[65,28],[65,29]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_049 : ∀ i : Fin 24, test35 (paths35_049.getD i.val []) = false := by decide +kernel

def paths35_050 : List (List ℕ) := [[65,30],[65,31],[65,32],[65,33],[65,34],[65,35],[65,36],[65,37],[65,38],[65,39],[65,40],[65,41],[65,42],[65,43],[65,44],[65,45],[65,46],[65,47],[65,48],[65,49],[65,50],[65,51],[65,52],[65,53]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked35_050 : ∀ i : Fin 24, test35 (paths35_050.getD i.val []) = false := by decide +kernel
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

open C4RCheck GiftTheta PEqualNP.Outside.L_meta_3237_aux.PathCheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead05_11 : test05 [11] = false := by
  apply close _ _ _ 37 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked05_003 2
  · exact checked05_003 3
  · exact checked05_003 4
  · exact checked05_003 5
  · exact checked05_003 6
  · exact checked05_003 7
  · exact checked05_003 8
  · exact checked05_003 9
  · exact checked05_004 0
  · exact checked05_004 1
  · exact checked05_004 2
  · exact checked05_004 3
  · exact checked05_004 4
  · exact checked05_004 5
  · exact checked05_004 6
  · exact checked05_004 7
  · exact checked05_004 8
  · exact checked05_004 9
  · exact checked05_004 10
  · exact checked05_004 11
  · exact checked05_004 12
  · exact checked05_004 13
  · exact checked05_004 14
  · exact checked05_004 15
  · exact checked05_004 16
  · exact checked05_004 17
  · exact checked05_004 18
  · exact checked05_004 19
  · exact checked05_004 20
  · exact checked05_004 21
  · exact checked05_004 22
  · exact checked05_004 23
  · exact checked05_005 0
  · exact checked05_005 1
  · exact checked05_005 2
  · exact checked05_005 3
  · exact checked05_005 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead05_25 : test05 [25] = false := by
  apply close _ _ _ 47 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked05_008 3
  · exact checked05_008 4
  · exact checked05_008 5
  · exact checked05_008 6
  · exact checked05_008 7
  · exact checked05_008 8
  · exact checked05_008 9
  · exact checked05_008 10
  · exact checked05_008 11
  · exact checked05_008 12
  · exact checked05_008 13
  · exact checked05_009 0
  · exact checked05_009 1
  · exact checked05_009 2
  · exact checked05_009 3
  · exact checked05_009 4
  · exact checked05_009 5
  · exact checked05_009 6
  · exact checked05_009 7
  · exact checked05_009 8
  · exact checked05_009 9
  · exact checked05_009 10
  · exact checked05_009 11
  · exact checked05_009 12
  · exact checked05_009 13
  · exact checked05_009 14
  · exact checked05_009 15
  · exact checked05_009 16
  · exact checked05_009 17
  · exact checked05_009 18
  · exact checked05_009 19
  · exact checked05_009 20
  · exact checked05_009 21
  · exact checked05_009 22
  · exact checked05_009 23
  · exact checked05_010 0
  · exact checked05_010 1
  · exact checked05_010 2
  · exact checked05_010 3
  · exact checked05_010 4
  · exact checked05_010 5
  · exact checked05_010 6
  · exact checked05_010 7
  · exact checked05_010 8
  · exact checked05_010 9
  · exact checked05_010 10
  · exact checked05_010 11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead05_31 : test05 [31] = false := by
  apply close _ _ _ 28 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked05_012 1
  · exact checked05_012 2
  · exact checked05_012 3
  · exact checked05_012 4
  · exact checked05_012 5
  · exact checked05_012 6
  · exact checked05_012 7
  · exact checked05_012 8
  · exact checked05_012 9
  · exact checked05_012 10
  · exact checked05_012 11
  · exact checked05_012 12
  · exact checked05_012 13
  · exact checked05_013 0
  · exact checked05_013 1
  · exact checked05_013 2
  · exact checked05_013 3
  · exact checked05_013 4
  · exact checked05_013 5
  · exact checked05_013 6
  · exact checked05_013 7
  · exact checked05_013 8
  · exact checked05_013 9
  · exact checked05_013 10
  · exact checked05_013 11
  · exact checked05_013 12
  · exact checked05_013 13
  · exact checked05_013 14

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead05_48 : test05 [48] = false := by
  apply close _ _ _ 31 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked05_019 2
  · exact checked05_019 3
  · exact checked05_020 0
  · exact checked05_020 1
  · exact checked05_020 2
  · exact checked05_020 3
  · exact checked05_020 4
  · exact checked05_020 5
  · exact checked05_020 6
  · exact checked05_020 7
  · exact checked05_020 8
  · exact checked05_020 9
  · exact checked05_020 10
  · exact checked05_020 11
  · exact checked05_020 12
  · exact checked05_020 13
  · exact checked05_020 14
  · exact checked05_020 15
  · exact checked05_020 16
  · exact checked05_020 17
  · exact checked05_020 18
  · exact checked05_020 19
  · exact checked05_020 20
  · exact checked05_020 21
  · exact checked05_020 22
  · exact checked05_020 23
  · exact checked05_021 0
  · exact checked05_021 1
  · exact checked05_021 2
  · exact checked05_021 3
  · exact checked05_021 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead05_52 : test05 [52] = false := by
  apply close _ _ _ 39 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked05_021 8
  · exact checked05_021 9
  · exact checked05_021 10
  · exact checked05_021 11
  · exact checked05_021 12
  · exact checked05_021 13
  · exact checked05_022 0
  · exact checked05_022 1
  · exact checked05_022 2
  · exact checked05_022 3
  · exact checked05_022 4
  · exact checked05_022 5
  · exact checked05_022 6
  · exact checked05_022 7
  · exact checked05_022 8
  · exact checked05_022 9
  · exact checked05_022 10
  · exact checked05_022 11
  · exact checked05_022 12
  · exact checked05_022 13
  · exact checked05_022 14
  · exact checked05_022 15
  · exact checked05_022 16
  · exact checked05_022 17
  · exact checked05_022 18
  · exact checked05_022 19
  · exact checked05_022 20
  · exact checked05_022 21
  · exact checked05_022 22
  · exact checked05_022 23
  · exact checked05_023 0
  · exact checked05_023 1
  · exact checked05_023 2
  · exact checked05_023 3
  · exact checked05_023 4
  · exact checked05_023 5
  · exact checked05_023 6
  · exact checked05_023 7
  · exact checked05_023 8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead05_53 : test05 [53] = false := by
  apply close _ _ _ 34 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked05_023 9
  · exact checked05_023 10
  · exact checked05_023 11
  · exact checked05_023 12
  · exact checked05_023 13
  · exact checked05_023 14
  · exact checked05_023 15
  · exact checked05_023 16
  · exact checked05_023 17
  · exact checked05_023 18
  · exact checked05_023 19
  · exact checked05_023 20
  · exact checked05_023 21
  · exact checked05_023 22
  · exact checked05_023 23
  · exact checked05_024 0
  · exact checked05_024 1
  · exact checked05_024 2
  · exact checked05_024 3
  · exact checked05_024 4
  · exact checked05_024 5
  · exact checked05_024 6
  · exact checked05_024 7
  · exact checked05_024 8
  · exact checked05_024 9
  · exact checked05_024 10
  · exact checked05_024 11
  · exact checked05_024 12
  · exact checked05_024 13
  · exact checked05_024 14
  · exact checked05_024 15
  · exact checked05_024 16
  · exact checked05_024 17
  · exact checked05_024 18

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead05_65 : test05 [65] = false := by
  apply close _ _ _ 46 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked05_031 1
  · exact checked05_031 2
  · exact checked05_031 3
  · exact checked05_031 4
  · exact checked05_031 5
  · exact checked05_031 6
  · exact checked05_031 7
  · exact checked05_031 8
  · exact checked05_031 9
  · exact checked05_031 10
  · exact checked05_031 11
  · exact checked05_031 12
  · exact checked05_031 13
  · exact checked05_031 14
  · exact checked05_031 15
  · exact checked05_031 16
  · exact checked05_032 0
  · exact checked05_032 1
  · exact checked05_032 2
  · exact checked05_032 3
  · exact checked05_032 4
  · exact checked05_032 5
  · exact checked05_032 6
  · exact checked05_032 7
  · exact checked05_032 8
  · exact checked05_032 9
  · exact checked05_032 10
  · exact checked05_032 11
  · exact checked05_032 12
  · exact checked05_032 13
  · exact checked05_032 14
  · exact checked05_032 15
  · exact checked05_032 16
  · exact checked05_032 17
  · exact checked05_032 18
  · exact checked05_032 19
  · exact checked05_032 20
  · exact checked05_032 21
  · exact checked05_032 22
  · exact checked05_032 23
  · exact checked05_033 0
  · exact checked05_033 1
  · exact checked05_033 2
  · exact checked05_033 3
  · exact checked05_033 4
  · exact checked05_033 5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead05_root : test05 [] = false := by
  apply close _ _ _ 66 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked05_000 0
  · exact checked05_000 1
  · exact checked05_000 2
  · exact checked05_000 3
  · exact checked05_000 4
  · exact checked05_001 0
  · exact checked05_001 1
  · exact checked05_002 0
  · exact checked05_002 1
  · exact checked05_003 0
  · exact checked05_003 1
  · exact dead05_11
  · exact checked05_005 5
  · exact checked05_005 6
  · exact checked05_005 7
  · exact checked05_006 0
  · exact checked05_006 1
  · exact checked05_006 2
  · exact checked05_006 3
  · exact checked05_006 4
  · exact checked05_007 0
  · exact checked05_007 1
  · exact checked05_008 0
  · exact checked05_008 1
  · exact checked05_008 2
  · exact dead05_25
  · exact checked05_010 12
  · exact checked05_010 13
  · exact checked05_011 0
  · exact checked05_011 1
  · exact checked05_012 0
  · exact dead05_31
  · exact checked05_013 15
  · exact checked05_013 16
  · exact checked05_014 0
  · exact checked05_014 1
  · exact checked05_014 2
  · exact checked05_015 0
  · exact checked05_015 1
  · exact checked05_015 2
  · exact checked05_016 0
  · exact checked05_017 0
  · exact checked05_017 1
  · exact checked05_017 2
  · exact checked05_018 0
  · exact checked05_018 1
  · exact checked05_019 0
  · exact checked05_019 1
  · exact dead05_48
  · exact checked05_021 5
  · exact checked05_021 6
  · exact checked05_021 7
  · exact dead05_52
  · exact dead05_53
  · exact checked05_024 19
  · exact checked05_025 0
  · exact checked05_026 0
  · exact checked05_027 0
  · exact checked05_027 1
  · exact checked05_028 0
  · exact checked05_029 0
  · exact checked05_030 0
  · exact checked05_030 1
  · exact checked05_030 2
  · exact checked05_031 0
  · exact dead05_65

theorem creditClosed05 : Credit7.guided (root 0 5) creditAdvice05 10 3 (root 0 5) [] = false :=
  root_closed _ _ dead05_root

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead35_6 : test35 [6] = false := by
  apply close _ _ _ 37 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked35_002 2
  · exact checked35_002 3
  · exact checked35_002 4
  · exact checked35_002 5
  · exact checked35_002 6
  · exact checked35_002 7
  · exact checked35_002 8
  · exact checked35_002 9
  · exact checked35_002 10
  · exact checked35_003 0
  · exact checked35_003 1
  · exact checked35_003 2
  · exact checked35_003 3
  · exact checked35_003 4
  · exact checked35_003 5
  · exact checked35_003 6
  · exact checked35_003 7
  · exact checked35_003 8
  · exact checked35_003 9
  · exact checked35_003 10
  · exact checked35_003 11
  · exact checked35_003 12
  · exact checked35_003 13
  · exact checked35_003 14
  · exact checked35_003 15
  · exact checked35_003 16
  · exact checked35_004 0
  · exact checked35_004 1
  · exact checked35_004 2
  · exact checked35_004 3
  · exact checked35_004 4
  · exact checked35_004 5
  · exact checked35_004 6
  · exact checked35_004 7
  · exact checked35_004 8
  · exact checked35_004 9
  · exact checked35_004 10

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead35_17 : test35 [17] = false := by
  apply close _ _ _ 37 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked35_009 3
  · exact checked35_009 4
  · exact checked35_009 5
  · exact checked35_009 6
  · exact checked35_009 7
  · exact checked35_010 0
  · exact checked35_010 1
  · exact checked35_010 2
  · exact checked35_010 3
  · exact checked35_010 4
  · exact checked35_010 5
  · exact checked35_010 6
  · exact checked35_010 7
  · exact checked35_010 8
  · exact checked35_010 9
  · exact checked35_010 10
  · exact checked35_010 11
  · exact checked35_010 12
  · exact checked35_010 13
  · exact checked35_010 14
  · exact checked35_010 15
  · exact checked35_010 16
  · exact checked35_010 17
  · exact checked35_010 18
  · exact checked35_010 19
  · exact checked35_011 0
  · exact checked35_011 1
  · exact checked35_011 2
  · exact checked35_011 3
  · exact checked35_011 4
  · exact checked35_011 5
  · exact checked35_011 6
  · exact checked35_011 7
  · exact checked35_011 8
  · exact checked35_011 9
  · exact checked35_011 10
  · exact checked35_011 11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead35_24 : test35 [24] = false := by
  apply close _ _ _ 28 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked35_015 1
  · exact checked35_015 2
  · exact checked35_015 3
  · exact checked35_016 0
  · exact checked35_016 1
  · exact checked35_016 2
  · exact checked35_016 3
  · exact checked35_016 4
  · exact checked35_016 5
  · exact checked35_016 6
  · exact checked35_016 7
  · exact checked35_016 8
  · exact checked35_016 9
  · exact checked35_016 10
  · exact checked35_016 11
  · exact checked35_016 12
  · exact checked35_016 13
  · exact checked35_016 14
  · exact checked35_016 15
  · exact checked35_016 16
  · exact checked35_016 17
  · exact checked35_016 18
  · exact checked35_016 19
  · exact checked35_016 20
  · exact checked35_016 21
  · exact checked35_016 22
  · exact checked35_016 23
  · exact checked35_017 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead35_25 : test35 [25] = false := by
  apply close _ _ _ 51 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked35_017 1
  · exact checked35_017 2
  · exact checked35_017 3
  · exact checked35_017 4
  · exact checked35_017 5
  · exact checked35_017 6
  · exact checked35_017 7
  · exact checked35_017 8
  · exact checked35_017 9
  · exact checked35_017 10
  · exact checked35_017 11
  · exact checked35_017 12
  · exact checked35_017 13
  · exact checked35_017 14
  · exact checked35_017 15
  · exact checked35_017 16
  · exact checked35_017 17
  · exact checked35_017 18
  · exact checked35_018 0
  · exact checked35_018 1
  · exact checked35_018 2
  · exact checked35_018 3
  · exact checked35_018 4
  · exact checked35_018 5
  · exact checked35_018 6
  · exact checked35_018 7
  · exact checked35_018 8
  · exact checked35_018 9
  · exact checked35_018 10
  · exact checked35_018 11
  · exact checked35_018 12
  · exact checked35_018 13
  · exact checked35_018 14
  · exact checked35_018 15
  · exact checked35_018 16
  · exact checked35_018 17
  · exact checked35_018 18
  · exact checked35_018 19
  · exact checked35_018 20
  · exact checked35_018 21
  · exact checked35_018 22
  · exact checked35_018 23
  · exact checked35_019 0
  · exact checked35_019 1
  · exact checked35_019 2
  · exact checked35_019 3
  · exact checked35_019 4
  · exact checked35_019 5
  · exact checked35_019 6
  · exact checked35_019 7
  · exact checked35_019 8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead35_29 : test35 [29] = false := by
  apply close _ _ _ 28 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked35_021 1
  · exact checked35_021 2
  · exact checked35_021 3
  · exact checked35_021 4
  · exact checked35_021 5
  · exact checked35_021 6
  · exact checked35_021 7
  · exact checked35_021 8
  · exact checked35_021 9
  · exact checked35_021 10
  · exact checked35_021 11
  · exact checked35_021 12
  · exact checked35_022 0
  · exact checked35_022 1
  · exact checked35_022 2
  · exact checked35_022 3
  · exact checked35_022 4
  · exact checked35_022 5
  · exact checked35_022 6
  · exact checked35_022 7
  · exact checked35_022 8
  · exact checked35_022 9
  · exact checked35_022 10
  · exact checked35_022 11
  · exact checked35_022 12
  · exact checked35_022 13
  · exact checked35_022 14
  · exact checked35_022 15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead35_35 : test35 [35] = false := by
  apply close _ _ _ 36 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked35_024 2
  · exact checked35_024 3
  · exact checked35_024 4
  · exact checked35_024 5
  · exact checked35_024 6
  · exact checked35_024 7
  · exact checked35_024 8
  · exact checked35_024 9
  · exact checked35_024 10
  · exact checked35_024 11
  · exact checked35_024 12
  · exact checked35_024 13
  · exact checked35_024 14
  · exact checked35_024 15
  · exact checked35_024 16
  · exact checked35_024 17
  · exact checked35_025 0
  · exact checked35_025 1
  · exact checked35_025 2
  · exact checked35_025 3
  · exact checked35_025 4
  · exact checked35_025 5
  · exact checked35_025 6
  · exact checked35_025 7
  · exact checked35_025 8
  · exact checked35_025 9
  · exact checked35_025 10
  · exact checked35_025 11
  · exact checked35_025 12
  · exact checked35_025 13
  · exact checked35_025 14
  · exact checked35_025 15
  · exact checked35_025 16
  · exact checked35_025 17
  · exact checked35_025 18
  · exact checked35_025 19

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead35_38 : test35 [38] = false := by
  apply close _ _ _ 30 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked35_026 2
  · exact checked35_026 3
  · exact checked35_026 4
  · exact checked35_026 5
  · exact checked35_027 0
  · exact checked35_027 1
  · exact checked35_027 2
  · exact checked35_027 3
  · exact checked35_027 4
  · exact checked35_027 5
  · exact checked35_027 6
  · exact checked35_027 7
  · exact checked35_027 8
  · exact checked35_027 9
  · exact checked35_027 10
  · exact checked35_027 11
  · exact checked35_027 12
  · exact checked35_027 13
  · exact checked35_027 14
  · exact checked35_027 15
  · exact checked35_027 16
  · exact checked35_027 17
  · exact checked35_027 18
  · exact checked35_027 19
  · exact checked35_027 20
  · exact checked35_027 21
  · exact checked35_027 22
  · exact checked35_027 23
  · exact checked35_028 0
  · exact checked35_028 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead35_44 : test35 [44] = false := by
  apply close _ _ _ 28 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked35_031 1
  · exact checked35_031 2
  · exact checked35_031 3
  · exact checked35_031 4
  · exact checked35_031 5
  · exact checked35_031 6
  · exact checked35_031 7
  · exact checked35_031 8
  · exact checked35_031 9
  · exact checked35_031 10
  · exact checked35_031 11
  · exact checked35_031 12
  · exact checked35_032 0
  · exact checked35_032 1
  · exact checked35_032 2
  · exact checked35_032 3
  · exact checked35_032 4
  · exact checked35_032 5
  · exact checked35_032 6
  · exact checked35_032 7
  · exact checked35_032 8
  · exact checked35_032 9
  · exact checked35_032 10
  · exact checked35_032 11
  · exact checked35_032 12
  · exact checked35_032 13
  · exact checked35_032 14
  · exact checked35_032 15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead35_49 : test35 [49] = false := by
  apply close _ _ _ 36 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked35_034 1
  · exact checked35_034 2
  · exact checked35_034 3
  · exact checked35_034 4
  · exact checked35_034 5
  · exact checked35_034 6
  · exact checked35_034 7
  · exact checked35_034 8
  · exact checked35_034 9
  · exact checked35_034 10
  · exact checked35_034 11
  · exact checked35_034 12
  · exact checked35_034 13
  · exact checked35_034 14
  · exact checked35_034 15
  · exact checked35_034 16
  · exact checked35_034 17
  · exact checked35_034 18
  · exact checked35_034 19
  · exact checked35_034 20
  · exact checked35_034 21
  · exact checked35_034 22
  · exact checked35_034 23
  · exact checked35_035 0
  · exact checked35_035 1
  · exact checked35_035 2
  · exact checked35_035 3
  · exact checked35_035 4
  · exact checked35_035 5
  · exact checked35_035 6
  · exact checked35_035 7
  · exact checked35_035 8
  · exact checked35_035 9
  · exact checked35_035 10
  · exact checked35_035 11
  · exact checked35_035 12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead35_51 : test35 [51] = false := by
  apply close _ _ _ 23 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked35_036 1
  · exact checked35_036 2
  · exact checked35_036 3
  · exact checked35_036 4
  · exact checked35_037 0
  · exact checked35_037 1
  · exact checked35_037 2
  · exact checked35_037 3
  · exact checked35_037 4
  · exact checked35_037 5
  · exact checked35_037 6
  · exact checked35_037 7
  · exact checked35_037 8
  · exact checked35_037 9
  · exact checked35_037 10
  · exact checked35_037 11
  · exact checked35_038 0
  · exact checked35_038 1
  · exact checked35_038 2
  · exact checked35_038 3
  · exact checked35_038 4
  · exact checked35_038 5
  · exact checked35_038 6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead35_64 : test35 [64] = false := by
  apply close _ _ _ 62 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked35_045 1
  · exact checked35_045 2
  · exact checked35_045 3
  · exact checked35_045 4
  · exact checked35_045 5
  · exact checked35_045 6
  · exact checked35_045 7
  · exact checked35_045 8
  · exact checked35_045 9
  · exact checked35_045 10
  · exact checked35_045 11
  · exact checked35_045 12
  · exact checked35_045 13
  · exact checked35_045 14
  · exact checked35_046 0
  · exact checked35_046 1
  · exact checked35_046 2
  · exact checked35_046 3
  · exact checked35_046 4
  · exact checked35_046 5
  · exact checked35_046 6
  · exact checked35_046 7
  · exact checked35_046 8
  · exact checked35_046 9
  · exact checked35_046 10
  · exact checked35_046 11
  · exact checked35_046 12
  · exact checked35_046 13
  · exact checked35_046 14
  · exact checked35_047 0
  · exact checked35_047 1
  · exact checked35_047 2
  · exact checked35_047 3
  · exact checked35_047 4
  · exact checked35_047 5
  · exact checked35_047 6
  · exact checked35_047 7
  · exact checked35_047 8
  · exact checked35_047 9
  · exact checked35_047 10
  · exact checked35_047 11
  · exact checked35_047 12
  · exact checked35_047 13
  · exact checked35_047 14
  · exact checked35_047 15
  · exact checked35_047 16
  · exact checked35_047 17
  · exact checked35_047 18
  · exact checked35_047 19
  · exact checked35_048 0
  · exact checked35_048 1
  · exact checked35_048 2
  · exact checked35_048 3
  · exact checked35_048 4
  · exact checked35_048 5
  · exact checked35_048 6
  · exact checked35_048 7
  · exact checked35_048 8
  · exact checked35_048 9
  · exact checked35_048 10
  · exact checked35_048 11
  · exact checked35_048 12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead35_65 : test35 [65] = false := by
  apply close _ _ _ 54 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked35_048 13
  · exact checked35_048 14
  · exact checked35_048 15
  · exact checked35_048 16
  · exact checked35_048 17
  · exact checked35_048 18
  · exact checked35_049 0
  · exact checked35_049 1
  · exact checked35_049 2
  · exact checked35_049 3
  · exact checked35_049 4
  · exact checked35_049 5
  · exact checked35_049 6
  · exact checked35_049 7
  · exact checked35_049 8
  · exact checked35_049 9
  · exact checked35_049 10
  · exact checked35_049 11
  · exact checked35_049 12
  · exact checked35_049 13
  · exact checked35_049 14
  · exact checked35_049 15
  · exact checked35_049 16
  · exact checked35_049 17
  · exact checked35_049 18
  · exact checked35_049 19
  · exact checked35_049 20
  · exact checked35_049 21
  · exact checked35_049 22
  · exact checked35_049 23
  · exact checked35_050 0
  · exact checked35_050 1
  · exact checked35_050 2
  · exact checked35_050 3
  · exact checked35_050 4
  · exact checked35_050 5
  · exact checked35_050 6
  · exact checked35_050 7
  · exact checked35_050 8
  · exact checked35_050 9
  · exact checked35_050 10
  · exact checked35_050 11
  · exact checked35_050 12
  · exact checked35_050 13
  · exact checked35_050 14
  · exact checked35_050 15
  · exact checked35_050 16
  · exact checked35_050 17
  · exact checked35_050 18
  · exact checked35_050 19
  · exact checked35_050 20
  · exact checked35_050 21
  · exact checked35_050 22
  · exact checked35_050 23

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dead35_root : test35 [] = false := by
  apply close _ _ _ 66 (by decide +kernel) (by decide +kernel)
  intro i; fin_cases i
  · exact checked35_000 0
  · exact checked35_000 1
  · exact checked35_001 0
  · exact checked35_001 1
  · exact checked35_002 0
  · exact checked35_002 1
  · exact dead35_6
  · exact checked35_005 0
  · exact checked35_006 0
  · exact checked35_006 1
  · exact checked35_007 0
  · exact checked35_007 1
  · exact checked35_008 0
  · exact checked35_008 1
  · exact checked35_009 0
  · exact checked35_009 1
  · exact checked35_009 2
  · exact dead35_17
  · exact checked35_012 0
  · exact checked35_013 0
  · exact checked35_013 1
  · exact checked35_014 0
  · exact checked35_014 1
  · exact checked35_015 0
  · exact dead35_24
  · exact dead35_25
  · exact checked35_019 9
  · exact checked35_020 0
  · exact checked35_021 0
  · exact dead35_29
  · exact checked35_023 0
  · exact checked35_023 1
  · exact checked35_023 2
  · exact checked35_024 0
  · exact checked35_024 1
  · exact dead35_35
  · exact checked35_026 0
  · exact checked35_026 1
  · exact dead35_38
  · exact checked35_028 2
  · exact checked35_028 3
  · exact checked35_029 0
  · exact checked35_030 0
  · exact checked35_031 0
  · exact dead35_44
  · exact checked35_033 0
  · exact checked35_033 1
  · exact checked35_033 2
  · exact checked35_034 0
  · exact dead35_49
  · exact checked35_036 0
  · exact dead35_51
  · exact checked35_038 7
  · exact checked35_039 0
  · exact checked35_039 1
  · exact checked35_040 0
  · exact checked35_040 1
  · exact checked35_041 0
  · exact checked35_042 0
  · exact checked35_043 0
  · exact checked35_043 1
  · exact checked35_044 0
  · exact checked35_044 1
  · exact checked35_045 0
  · exact dead35_64
  · exact dead35_65

theorem creditClosed35 : Credit7.guided (root 3 5) creditAdvice35 10 3 (root 3 5) [] = false :=
  root_closed _ _ dead35_root
end PEqualNP.Outside.L_meta_3237_aux.GiftTheta.CreditPath

namespace PEqualNP.Outside.L_meta_3237_aux.GiftLeaf
open C4RCheck C4RLive ThetaSigned SignedCofactor C4Small
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def sig {n : Nat} (a b : Fin n) (x : Fin n → Bool) := x a || x b
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def col {n : Nat} (cols : List W) (a b : Fin n) := (cols.getD a.val 0) ||| (cols.getD b.val 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def init {n : Nat} (cols : List W) (a b : Fin n) := canon (col cols a b) :: signals cols
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def need {n : Nat} (cols : List W) (a b : Fin n) (sites : List (Fin 232)) :=
  (signals cols).all fun u => sites.any fun i => (init cols a b).all fun w =>
    (w.getLsbD i.val == w.getLsbD (232+i.val)) || w == u
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rep {n : Nat} (cols : List W) (len : cols.length=n) (a b : Fin n) :
    representsPool (columnPick (n:=n) cols) (plus (literals n) (sig a b)) (init cols a b).toFinset := by
  intro f h
  have rootEq : (init cols a b).toFinset = insert (canon (col cols a b)) (signals cols).toFinset := by
    simp only [init,List.toFinset_cons]
  rw [rootEq]
  rcases h with old|rfl|rfl
  · obtain ⟨w,ok,eq⟩ := columnGood cols len f old
    exact ⟨w,ok.imp_right (Finset.mem_insert_of_mem),eq⟩
  · exact ⟨col cols a b,Or.inr (Finset.mem_insert_self ..),fun r => by simp [col,sig,columnPick,wordBit]⟩
  · refine ⟨~~~(col cols a b),Or.inr ?_,fun r => ?_⟩
    · rw [canon_neg]; exact Finset.mem_insert_self ..
    · simp [col,sig,columnPick,wordBit,inv]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower {n cap extra k : Nat} (es : List (Fin n × Fin n)) (cols : List W) (a b : Fin n)
    (sites : List (Fin 232)) (len : cols.length=n) (correct : edgeWord es cols = goal)
    (necessary : need cols a b sites=true) (nd : (signals cols).Nodup)
    (nd' : (init cols a b).Nodup) (room : extra+(signals cols).length=cap+1)
    (plain : optimized cap extra (signals cols)=false)
    (withGift : (cap+1 < (init cols a b).length) ∨ (∃ extra', extra'+(init cols a b).length=cap+1 ∧
      optimized cap extra' (init cols a b)=false))
    (hr : Run (plus (literals n) (sig a b)) k (edgeFunc es)) : cap+1≤k := by
  by_contra! low
  have matchRows (r : Fin 464) : edgeFunc es (columnPick cols r)=wordBit r goal := by rw [edgeRows,correct]
  obtain ⟨s,hs,liveK⟩ := compress (anyBuild _ matchRows hr _ (rep cols len a b))
  have rootEq : (init cols a b).toFinset = insert (canon (col cols a b)) (signals cols).toFinset := by
    simp only [init,List.toFinset_cons]
  have must : (signals cols).toFinset ⊆ s := by
    intro u hu
    obtain ⟨i,_,all⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary u (List.mem_toFinset.mp hu))
    obtain ⟨w,hw,hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) liveK
    have eq := List.all_eq_true.mp all w (List.mem_toFinset.mp (hs hw))
    simp only [Bool.or_eq_true,beq_iff_eq] at eq
    exact eq.resolve_left hd ▸ hw
  have padded : live basicOps goal cap s := by
    have pad (m : Nat) (le : k ≤ m) : live basicOps goal m s := by
      induction le with
      | refl => exact liveK
      | step _ ih => exact Or.inl ih
    exact pad _ (by omega)
  by_cases gift : canon (col cols a b) ∈ s
  · have eq : s=(init cols a b).toFinset :=
    Finset.Subset.antisymm hs (rootEq ▸ Finset.insert_subset gift must)
    rw [eq] at padded
    rcases withGift with impossible|⟨t,delta,cert⟩
    · have hcard := live_card padded
      rw [List.toFinset_card_of_nodup nd'] at hcard
      omega
    · exact Bool.noConfusion (cert.symm.trans (optimized_complete cap _ t nd' delta padded))
  · have sub : s⊆(signals cols).toFinset := by
      intro w hw
      have incl : w ∈ insert (canon (col cols a b)) (signals cols).toFinset := by
        rw [←rootEq]; exact hs hw
      exact (Finset.mem_insert.1 incl).resolve_left (fun eq => gift (eq ▸ hw))
    rw [Finset.Subset.antisymm sub must] at padded
    exact Bool.noConfusion (plain.symm.trans (optimized_complete cap _ extra nd room padded))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower0_0_3 {k : Nat} (h : Run (plus (literals 5) (sig 0 3)) k (edgeFunc C4Small.Leaf0.es)) :
    7 ≤ k := lower (cap:=6) (extra:=2) C4Small.Leaf0.es C4Small.Leaf0.cols 0 3 [12, 13, 0, 1, 3]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) C4Small.Leaf0.scan (Or.inr ⟨1,by decide +kernel,by decide +kernel⟩) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower0_1_3 {k : Nat} (h : Run (plus (literals 5) (sig 1 3)) k (edgeFunc C4Small.Leaf0.es)) :
    7 ≤ k := lower (cap:=6) (extra:=2) C4Small.Leaf0.es C4Small.Leaf0.cols 1 3 [7, 13, 0, 2, 3]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) C4Small.Leaf0.scan (Or.inr ⟨1,by decide +kernel,by decide +kernel⟩) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower1_0_4 {k : Nat} (h : Run (plus (literals 6) (sig 0 4)) k (edgeFunc C4Small.Leaf1.es)) :
    8 ≤ k := lower (cap:=7) (extra:=2) C4Small.Leaf1.es C4Small.Leaf1.cols 0 4 [22, 0, 13, 4, 1, 3]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) C4Small.Leaf1.scan (Or.inr ⟨1,by decide +kernel,by decide +kernel⟩) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower2_0_2 {k : Nat} (h : Run (plus (literals 4) (sig 0 2)) k (edgeFunc C4Small.Leaf2.es)) :
    4 ≤ k := lower (cap:=3) (extra:=0) C4Small.Leaf2.es C4Small.Leaf2.cols 0 2 [5, 9, 0, 1]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) C4Small.Leaf2.scan (Or.inl (by decide +kernel)) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower2_0_3 {k : Nat} (h : Run (plus (literals 4) (sig 0 3)) k (edgeFunc C4Small.Leaf2.es)) :
    4 ≤ k := lower (cap:=3) (extra:=0) C4Small.Leaf2.es C4Small.Leaf2.cols 0 3 [8, 9, 0, 1]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) C4Small.Leaf2.scan (Or.inl (by decide +kernel)) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower2_1_3 {k : Nat} (h : Run (plus (literals 4) (sig 1 3)) k (edgeFunc C4Small.Leaf2.es)) :
    4 ≤ k := lower (cap:=3) (extra:=0) C4Small.Leaf2.es C4Small.Leaf2.cols 1 3 [5, 9, 0, 2]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) C4Small.Leaf2.scan (Or.inl (by decide +kernel)) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower3_1_5 {k : Nat} (h : Run (plus (literals 6) (sig 1 5)) k (edgeFunc C4Small.Leaf3.es)) :
    7 ≤ k := lower (cap:=6) (extra:=1) C4Small.Leaf3.es C4Small.Leaf3.cols 1 5 [1, 38, 22, 39, 3, 2]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) C4Small.Leaf3.scan (Or.inr ⟨0,by decide +kernel,by decide +kernel⟩) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower3_3_5 {k : Nat} (h : Run (plus (literals 6) (sig 3 5)) k (edgeFunc C4Small.Leaf3.es)) :
    7 ≤ k := lower (cap:=6) (extra:=1) C4Small.Leaf3.es C4Small.Leaf3.cols 3 5 [1, 0, 22, 39, 3, 9]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) C4Small.Leaf3.scan (Or.inr ⟨0,by decide +kernel,by decide +kernel⟩) h
end PEqualNP.Outside.L_meta_3237_aux.GiftLeaf

namespace PEqualNP.Outside.L_meta_3237_aux.CreditFaces
open C4Base ThetaSigned C4RCheck C4RLive SignedCofactor
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pullFace (a b : Fin 7) (i : Fin 23) {n : Nat}
    (idx : Fin 7 → Option (Fin n)) (Q : Set (Wire (Fin n → Bool))) (cl : Closed Q)
    (raw : literals n ⊆ Q)
    (hs : (fun x => GiftTheta.seed a b (pin (C4Lite.faceAt i).fixed (C4Lite.faceAt i).values
      (C4Lite.insertVars idx x))) ∈ Q)
    (es : List (Fin n × Fin n))
    (eq : ∀ x, C4Base.nine (pin (C4Lite.faceAt i).fixed (C4Lite.faceAt i).values
      (C4Lite.insertVars idx x)) = C4Small.edgeFunc es x)
    (lb : ∀ k, Run Q k (C4Small.edgeFunc es) → (C4Lite.faceAt i).lower ≤ k) :
    Credit7.Valid a b (C4Lite.faceAt i) := by
  have h := C4Lite.valid i
  refine ⟨h.1,h.2.1,?_⟩
  intro k run
  have hr := C4Lite.pull run (C4Lite.insertVars idx) Q (by
    rintro g (old|rfl|rfl)
    · exact raw (C4Lite.pullSmall idx g old)
    · exact hs
    · exact cl.2 _ hs)
  rw [funext eq] at hr
  exact lb k hr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_0 : Credit7.Valid 0 5 (C4Lite.faceAt 0) := by
  apply pullFace 0 5 0 C4Lite.selector0 (literals 5) (literals_closed _) (fun _ h => h) _ C4Small.Leaf0.es (by decide +kernel) (fun _ h => C4Small.Leaf0.lower h)
  exact Or.inr ⟨3,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 0).fixed (C4Lite.faceAt 0).values (C4Lite.insertVars C4Lite.selector0 x)) = x 3))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_1 : Credit7.Valid 0 5 (C4Lite.faceAt 1) := by
  apply pullFace 0 5 1 C4Lite.selector1 (plus (literals 5) (GiftLeaf.sig 0 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf0.es (by decide +kernel) (fun _ h => GiftLeaf.lower0_0_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 1).fixed (C4Lite.faceAt 1).values (C4Lite.insertVars C4Lite.selector1 x)) = GiftLeaf.sig 0 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_2 : Credit7.Valid 0 5 (C4Lite.faceAt 2) := by
  apply pullFace 0 5 2 C4Lite.selector2 (plus (literals 6) (GiftLeaf.sig 0 4)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf1.es (by decide +kernel) (fun _ h => GiftLeaf.lower1_0_4 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 2).fixed (C4Lite.faceAt 2).values (C4Lite.insertVars C4Lite.selector2 x)) = GiftLeaf.sig 0 4 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_3 : Credit7.Valid 0 5 (C4Lite.faceAt 3) := by
  apply pullFace 0 5 3 C4Lite.selector3 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨2,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 3).fixed (C4Lite.faceAt 3).values (C4Lite.insertVars C4Lite.selector3 x)) = x 2))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_4 : Credit7.Valid 0 5 (C4Lite.faceAt 4) := by
  apply pullFace 0 5 4 C4Lite.selector4 (plus (literals 4) (GiftLeaf.sig 0 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_0_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 4).fixed (C4Lite.faceAt 4).values (C4Lite.insertVars C4Lite.selector4 x)) = GiftLeaf.sig 0 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_5 : Credit7.Valid 0 5 (C4Lite.faceAt 5) := by
  apply pullFace 0 5 5 C4Lite.selector5 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨1,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 5).fixed (C4Lite.faceAt 5).values (C4Lite.insertVars C4Lite.selector5 x)) = x 1))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_6 : Credit7.Valid 0 5 (C4Lite.faceAt 6) := by
  apply pullFace 0 5 6 C4Lite.selector6 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨3,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 6).fixed (C4Lite.faceAt 6).values (C4Lite.insertVars C4Lite.selector6 x)) = x 3))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_7 : Credit7.Valid 0 5 (C4Lite.faceAt 7) := by
  apply pullFace 0 5 7 C4Lite.selector7 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inl ⟨true,funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 7).fixed (C4Lite.faceAt 7).values (C4Lite.insertVars C4Lite.selector7 x)) = true)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_8 : Credit7.Valid 0 5 (C4Lite.faceAt 8) := by
  apply pullFace 0 5 8 C4Lite.selector8 (plus (literals 4) (GiftLeaf.sig 0 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_0_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 8).fixed (C4Lite.faceAt 8).values (C4Lite.insertVars C4Lite.selector8 x)) = GiftLeaf.sig 0 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_9 : Credit7.Valid 0 5 (C4Lite.faceAt 9) := by
  apply pullFace 0 5 9 C4Lite.selector9 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inl ⟨false,funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 9).fixed (C4Lite.faceAt 9).values (C4Lite.insertVars C4Lite.selector9 x)) = false)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_10 : Credit7.Valid 0 5 (C4Lite.faceAt 10) := by
  apply pullFace 0 5 10 C4Lite.selector10 (plus (literals 4) (GiftLeaf.sig 1 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_1_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 10).fixed (C4Lite.faceAt 10).values (C4Lite.insertVars C4Lite.selector10 x)) = GiftLeaf.sig 1 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_11 : Credit7.Valid 0 5 (C4Lite.faceAt 11) := by
  apply pullFace 0 5 11 C4Lite.selector11 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨1,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 11).fixed (C4Lite.faceAt 11).values (C4Lite.insertVars C4Lite.selector11 x)) = x 1))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_12 : Credit7.Valid 0 5 (C4Lite.faceAt 12) := by
  apply pullFace 0 5 12 C4Lite.selector12 (plus (literals 4) (GiftLeaf.sig 1 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_1_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 12).fixed (C4Lite.faceAt 12).values (C4Lite.insertVars C4Lite.selector12 x)) = GiftLeaf.sig 1 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_13 : Credit7.Valid 0 5 (C4Lite.faceAt 13) := by
  apply pullFace 0 5 13 C4Lite.selector13 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨3,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 13).fixed (C4Lite.faceAt 13).values (C4Lite.insertVars C4Lite.selector13 x)) = x 3))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_14 : Credit7.Valid 0 5 (C4Lite.faceAt 14) := by
  apply pullFace 0 5 14 C4Lite.selector14 (literals 6) (literals_closed _) (fun _ h => h) _ C4Small.Leaf3.es (by decide +kernel) (fun _ h => C4Small.Leaf3.lower h)
  exact Or.inr ⟨0,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 14).fixed (C4Lite.faceAt 14).values (C4Lite.insertVars C4Lite.selector14 x)) = x 0))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_15 : Credit7.Valid 0 5 (C4Lite.faceAt 15) := by
  apply pullFace 0 5 15 C4Lite.selector15 (plus (literals 6) (GiftLeaf.sig 1 5)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf3.es (by decide +kernel) (fun _ h => GiftLeaf.lower3_1_5 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 15).fixed (C4Lite.faceAt 15).values (C4Lite.insertVars C4Lite.selector15 x)) = GiftLeaf.sig 1 5 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_16 : Credit7.Valid 0 5 (C4Lite.faceAt 16) := by
  apply pullFace 0 5 16 C4Lite.selector16 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨2,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 16).fixed (C4Lite.faceAt 16).values (C4Lite.insertVars C4Lite.selector16 x)) = x 2))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_17 : Credit7.Valid 0 5 (C4Lite.faceAt 17) := by
  apply pullFace 0 5 17 C4Lite.selector17 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨2,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 17).fixed (C4Lite.faceAt 17).values (C4Lite.insertVars C4Lite.selector17 x)) = x 2))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_18 : Credit7.Valid 0 5 (C4Lite.faceAt 18) := by
  apply pullFace 0 5 18 C4Lite.selector18 (plus (literals 4) (GiftLeaf.sig 0 2)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_0_2 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 18).fixed (C4Lite.faceAt 18).values (C4Lite.insertVars C4Lite.selector18 x)) = GiftLeaf.sig 0 2 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_19 : Credit7.Valid 0 5 (C4Lite.faceAt 19) := by
  apply pullFace 0 5 19 C4Lite.selector19 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inl ⟨false,funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 19).fixed (C4Lite.faceAt 19).values (C4Lite.insertVars C4Lite.selector19 x)) = false)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_20 : Credit7.Valid 0 5 (C4Lite.faceAt 20) := by
  apply pullFace 0 5 20 C4Lite.selector20 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨1,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 20).fixed (C4Lite.faceAt 20).values (C4Lite.insertVars C4Lite.selector20 x)) = x 1))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_21 : Credit7.Valid 0 5 (C4Lite.faceAt 21) := by
  apply pullFace 0 5 21 C4Lite.selector21 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨3,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 21).fixed (C4Lite.faceAt 21).values (C4Lite.insertVars C4Lite.selector21 x)) = x 3))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v05_22 : Credit7.Valid 0 5 (C4Lite.faceAt 22) := by
  apply pullFace 0 5 22 C4Lite.selector22 (plus (literals 4) (GiftLeaf.sig 0 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_0_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 0 5 (pin (C4Lite.faceAt 22).fixed (C4Lite.faceAt 22).values (C4Lite.insertVars C4Lite.selector22 x)) = GiftLeaf.sig 0 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid05 (i : Fin 23) : Credit7.Valid 0 5 (C4Lite.faceAt i) := by
  fin_cases i
  · exact v05_0
  · exact v05_1
  · exact v05_2
  · exact v05_3
  · exact v05_4
  · exact v05_5
  · exact v05_6
  · exact v05_7
  · exact v05_8
  · exact v05_9
  · exact v05_10
  · exact v05_11
  · exact v05_12
  · exact v05_13
  · exact v05_14
  · exact v05_15
  · exact v05_16
  · exact v05_17
  · exact v05_18
  · exact v05_19
  · exact v05_20
  · exact v05_21
  · exact v05_22

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_0 : Credit7.Valid 3 5 (C4Lite.faceAt 0) := by
  apply pullFace 3 5 0 C4Lite.selector0 (plus (literals 5) (GiftLeaf.sig 1 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf0.es (by decide +kernel) (fun _ h => GiftLeaf.lower0_1_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 0).fixed (C4Lite.faceAt 0).values (C4Lite.insertVars C4Lite.selector0 x)) = GiftLeaf.sig 1 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_1 : Credit7.Valid 3 5 (C4Lite.faceAt 1) := by
  apply pullFace 3 5 1 C4Lite.selector1 (plus (literals 5) (GiftLeaf.sig 1 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf0.es (by decide +kernel) (fun _ h => GiftLeaf.lower0_1_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 1).fixed (C4Lite.faceAt 1).values (C4Lite.insertVars C4Lite.selector1 x)) = GiftLeaf.sig 1 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_2 : Credit7.Valid 3 5 (C4Lite.faceAt 2) := by
  apply pullFace 3 5 2 C4Lite.selector2 (literals 6) (literals_closed _) (fun _ h => h) _ C4Small.Leaf1.es (by decide +kernel) (fun _ h => C4Small.Leaf1.lower h)
  exact Or.inr ⟨4,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 2).fixed (C4Lite.faceAt 2).values (C4Lite.insertVars C4Lite.selector2 x)) = x 4))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_3 : Credit7.Valid 3 5 (C4Lite.faceAt 3) := by
  apply pullFace 3 5 3 C4Lite.selector3 (plus (literals 4) (GiftLeaf.sig 0 2)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_0_2 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 3).fixed (C4Lite.faceAt 3).values (C4Lite.insertVars C4Lite.selector3 x)) = GiftLeaf.sig 0 2 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_4 : Credit7.Valid 3 5 (C4Lite.faceAt 4) := by
  apply pullFace 3 5 4 C4Lite.selector4 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨3,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 4).fixed (C4Lite.faceAt 4).values (C4Lite.insertVars C4Lite.selector4 x)) = x 3))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_5 : Credit7.Valid 3 5 (C4Lite.faceAt 5) := by
  apply pullFace 3 5 5 C4Lite.selector5 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨2,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 5).fixed (C4Lite.faceAt 5).values (C4Lite.insertVars C4Lite.selector5 x)) = x 2))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_6 : Credit7.Valid 3 5 (C4Lite.faceAt 6) := by
  apply pullFace 3 5 6 C4Lite.selector6 (plus (literals 4) (GiftLeaf.sig 1 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_1_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 6).fixed (C4Lite.faceAt 6).values (C4Lite.insertVars C4Lite.selector6 x)) = GiftLeaf.sig 1 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_7 : Credit7.Valid 3 5 (C4Lite.faceAt 7) := by
  apply pullFace 3 5 7 C4Lite.selector7 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨2,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 7).fixed (C4Lite.faceAt 7).values (C4Lite.insertVars C4Lite.selector7 x)) = x 2))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_8 : Credit7.Valid 3 5 (C4Lite.faceAt 8) := by
  apply pullFace 3 5 8 C4Lite.selector8 (plus (literals 4) (GiftLeaf.sig 1 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_1_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 8).fixed (C4Lite.faceAt 8).values (C4Lite.insertVars C4Lite.selector8 x)) = GiftLeaf.sig 1 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_9 : Credit7.Valid 3 5 (C4Lite.faceAt 9) := by
  apply pullFace 3 5 9 C4Lite.selector9 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inl ⟨false,funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 9).fixed (C4Lite.faceAt 9).values (C4Lite.insertVars C4Lite.selector9 x)) = false)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_10 : Credit7.Valid 3 5 (C4Lite.faceAt 10) := by
  apply pullFace 3 5 10 C4Lite.selector10 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨3,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 10).fixed (C4Lite.faceAt 10).values (C4Lite.insertVars C4Lite.selector10 x)) = x 3))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_11 : Credit7.Valid 3 5 (C4Lite.faceAt 11) := by
  apply pullFace 3 5 11 C4Lite.selector11 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inl ⟨false,funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 11).fixed (C4Lite.faceAt 11).values (C4Lite.insertVars C4Lite.selector11 x)) = false)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_12 : Credit7.Valid 3 5 (C4Lite.faceAt 12) := by
  apply pullFace 3 5 12 C4Lite.selector12 (plus (literals 4) (GiftLeaf.sig 0 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_0_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 12).fixed (C4Lite.faceAt 12).values (C4Lite.insertVars C4Lite.selector12 x)) = GiftLeaf.sig 0 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_13 : Credit7.Valid 3 5 (C4Lite.faceAt 13) := by
  apply pullFace 3 5 13 C4Lite.selector13 (plus (literals 4) (GiftLeaf.sig 0 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_0_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 13).fixed (C4Lite.faceAt 13).values (C4Lite.insertVars C4Lite.selector13 x)) = GiftLeaf.sig 0 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_14 : Credit7.Valid 3 5 (C4Lite.faceAt 14) := by
  apply pullFace 3 5 14 C4Lite.selector14 (literals 6) (literals_closed _) (fun _ h => h) _ C4Small.Leaf3.es (by decide +kernel) (fun _ h => C4Small.Leaf3.lower h)
  exact Or.inr ⟨3,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 14).fixed (C4Lite.faceAt 14).values (C4Lite.insertVars C4Lite.selector14 x)) = x 3))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_15 : Credit7.Valid 3 5 (C4Lite.faceAt 15) := by
  apply pullFace 3 5 15 C4Lite.selector15 (plus (literals 6) (GiftLeaf.sig 3 5)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf3.es (by decide +kernel) (fun _ h => GiftLeaf.lower3_3_5 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 15).fixed (C4Lite.faceAt 15).values (C4Lite.insertVars C4Lite.selector15 x)) = GiftLeaf.sig 3 5 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_16 : Credit7.Valid 3 5 (C4Lite.faceAt 16) := by
  apply pullFace 3 5 16 C4Lite.selector16 (plus (literals 4) (GiftLeaf.sig 0 2)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_0_2 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 16).fixed (C4Lite.faceAt 16).values (C4Lite.insertVars C4Lite.selector16 x)) = GiftLeaf.sig 0 2 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_17 : Credit7.Valid 3 5 (C4Lite.faceAt 17) := by
  apply pullFace 3 5 17 C4Lite.selector17 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨2,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 17).fixed (C4Lite.faceAt 17).values (C4Lite.insertVars C4Lite.selector17 x)) = x 2))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_18 : Credit7.Valid 3 5 (C4Lite.faceAt 18) := by
  apply pullFace 3 5 18 C4Lite.selector18 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨2,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 18).fixed (C4Lite.faceAt 18).values (C4Lite.insertVars C4Lite.selector18 x)) = x 2))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_19 : Credit7.Valid 3 5 (C4Lite.faceAt 19) := by
  apply pullFace 3 5 19 C4Lite.selector19 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨2,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 19).fixed (C4Lite.faceAt 19).values (C4Lite.insertVars C4Lite.selector19 x)) = x 2))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_20 : Credit7.Valid 3 5 (C4Lite.faceAt 20) := by
  apply pullFace 3 5 20 C4Lite.selector20 (literals 4) (literals_closed _) (fun _ h => h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => C4Small.Leaf2.lower h)
  exact Or.inr ⟨2,Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 20).fixed (C4Lite.faceAt 20).values (C4Lite.insertVars C4Lite.selector20 x)) = x 2))⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_21 : Credit7.Valid 3 5 (C4Lite.faceAt 21) := by
  apply pullFace 3 5 21 C4Lite.selector21 (plus (literals 4) (GiftLeaf.sig 1 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_1_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 21).fixed (C4Lite.faceAt 21).values (C4Lite.insertVars C4Lite.selector21 x)) = GiftLeaf.sig 1 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v35_22 : Credit7.Valid 3 5 (C4Lite.faceAt 22) := by
  apply pullFace 3 5 22 C4Lite.selector22 (plus (literals 4) (GiftLeaf.sig 1 3)) (plus_closed (literals_closed _) _) (fun _ h => Or.inl h) _ C4Small.Leaf2.es (by decide +kernel) (fun _ h => GiftLeaf.lower2_1_3 h)
  exact Or.inr (Or.inl (funext (by decide +kernel : ∀ x, GiftTheta.seed 3 5 (pin (C4Lite.faceAt 22).fixed (C4Lite.faceAt 22).values (C4Lite.insertVars C4Lite.selector22 x)) = GiftLeaf.sig 1 3 x)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem valid35 (i : Fin 23) : Credit7.Valid 3 5 (C4Lite.faceAt i) := by
  fin_cases i
  · exact v35_0
  · exact v35_1
  · exact v35_2
  · exact v35_3
  · exact v35_4
  · exact v35_5
  · exact v35_6
  · exact v35_7
  · exact v35_8
  · exact v35_9
  · exact v35_10
  · exact v35_11
  · exact v35_12
  · exact v35_13
  · exact v35_14
  · exact v35_15
  · exact v35_16
  · exact v35_17
  · exact v35_18
  · exact v35_19
  · exact v35_20
  · exact v35_21
  · exact v35_22
end PEqualNP.Outside.L_meta_3237_aux.CreditFaces

namespace PEqualNP.Outside.L_meta_3237_aux.GiftTheta

open C4Base ThetaSigned C4RCheck C4RLive

theorem bank_credit_valid (a b : Fin 7) (table : Array (List (Fin 23)))
    (facts : ∀ i, Credit7.Valid a b (C4Lite.faceAt i)) :
    ∀ ws hist, ∀ c ∈ bank table ws hist, Credit7.Valid a b c := by
  intro ws hist c hc
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
  exact facts i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower_credit (a b : Fin 7) (sites : List (Fin 232)) (need : necessary a b sites)
    (nd : (root a b).Nodup) (ad : Advice)
    (valid : ∀ ws hist, ∀ c ∈ ad ws hist, Credit7.Valid a b c)
    (closed : Credit7.guided (root a b) ad 10 3 (root a b) [] = false)
    {k : ℕ} (h : ThetaSigned.Run (given a b) k C4Base.nine) : 11 ≤ k := by
  by_contra! low
  rcases seed_roots a b sites need h with raw | giftRun
  · exact (Nat.not_lt_of_ge (raw_lower raw)) low
  · have start : Credit7.seen (root a b) [] = (root a b).toFinset := by simp [Credit7.seen]
    have cert := Credit7.guided_complete a b ad valid 10 (root a b) [] 3 nd (by rfl)
      (start ▸ History.initial) (start ▸ Finset.Subset.refl _) (pad_live (by omega) giftRun)
    exact Bool.noConfusion (cert.symm.trans closed)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower05 {k} (h : ThetaSigned.Run
    (ThetaSigned.plus C4Base.small (fun y : C4Base.Y => y 0 || y 5)) k C4Base.nine) : 11 ≤ k :=
  lower_credit 0 5 CreditPath.creditSites05 (by unfold necessary; decide +kernel) (by decide +kernel)
    CreditPath.creditAdvice05 (bank_credit_valid 0 5 CreditPath.creditData05 CreditFaces.valid05)
    CreditPath.creditClosed05 h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower35 {k} (h : ThetaSigned.Run
    (ThetaSigned.plus C4Base.small (fun y : C4Base.Y => y 3 || y 5)) k C4Base.nine) : 11 ≤ k :=
  lower_credit 3 5 CreditPath.creditSites35 (by unfold necessary; decide +kernel) (by decide +kernel)
    CreditPath.creditAdvice35 (bank_credit_valid 3 5 CreditPath.creditData35 CreditFaces.valid35)
    CreditPath.creditClosed35 h


end PEqualNP.Outside.L_meta_3237_aux.GiftTheta

open PEqualNP.Outside.L_meta_3237_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_3237 :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[(0 : ℕ)]? = Option.some x4 → (∃ (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == Bool.true && x8 == x6) ∧ [x4.left, x4.right] ≤ [[(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.left x4.left, [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.right x4.right]) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C phase signed firstGate correct
  have hr := Gift9.binary_run C phase signed correct
  apply Gift9.lower_from_faces _ _ hr
  · apply GiftFaces.all_valid
    · exact fun _ h => C4Lite.signed_lower h
    · exact fun _ h => GiftTheta.lower05 h
    · exact fun _ h => GiftTheta.lower35 h
  · intro k liveRun
    by_contra! low
    have facts := P2828Raw.allValid (fun _ h => C4Lite.signed_lower h)
    have pad {a : Finset P2828Check.W} (t : Nat) (le : k ≤ t)
        (hl : P2828Live.live P2828Check.basicOps P2828Check.goal k a) :
        P2828Live.live P2828Check.basicOps P2828Check.goal t a := by
      induction le with
      | refl => exact hl
      | step _ ih => exact Or.inl ih
    have ok (s h : List P2828Check.W) (c : P2828Check.Face) (hc : c ∈ P2828Raw.advice s h) : c.Valid := by
      obtain ⟨i,_,rfl⟩ := List.mem_map.1 hc
      exact facts i
    have start : P2828Check.allSeen [] = P2828Check.inputs.toFinset := by simp [P2828Check.allSeen]
    have chk := P2828Check.guided_complete P2828Raw.advice ok 13 P2828Check.inputs [] 5
      (by decide) (by decide) (start ▸ P2828Live.History.initial) (start ▸ Finset.Subset.refl _)
      (pad 13 (by omega) liveRun)
    exact Bool.noConfusion (chk.symm.trans P2828Raw.firstScan)
