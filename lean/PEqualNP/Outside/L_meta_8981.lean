import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_8981

def run (gs : List Gate) (xs : List Bool) : List Bool :=
  (⟨gs, 0⟩ : Circuit).wires xs

theorem run_append (a b : List Gate) (xs : List Bool) :
    run (a ++ b) xs = run b (run a xs) := by
  simp [run, Circuit.wires, List.foldl_append]

theorem run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    change (run gs (xs ++ [_])).length = _
    rw [ih]
    simp
    omega

theorem keep (gs : List Gate) (xs : List Bool) (i : Nat) (hi : i < xs.length) :
    (run gs xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (xs ++ [_])).getD i false = _
    rw [ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

-- The new OR gates all read the tape that was present before this batch.
def batch (a b : Nat → Nat) : Nat → List Gate
  | 0 => []
  | k+1 => batch a b k ++ [⟨.or, [a k, b k]⟩]

theorem batch_length (a b : Nat → Nat) (m : Nat) : (batch a b m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [batch, ih]

theorem batch_mono (a b : Nat → Nat) (m : Nat) :
    Monotone2 (⟨batch a b m, 0⟩ : Circuit) := by
  induction m with
  | zero => simp [Monotone2, batch]
  | succ m ih =>
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact ih g hg
    · obtain rfl : g = _ := List.mem_singleton.mp hg
      simp

theorem batch_read (a b : Nat → Nat) (xs : List Bool) (m : Nat)
    (valid : ∀ j < m, a j < xs.length ∧ b j < xs.length) (j : Nat) (hj : j < m) :
    (run (batch a b m) xs).getD (xs.length+j) false =
      (xs.getD (a j) false || xs.getD (b j) false) := by
  induction m with
  | zero => omega
  | succ m ih =>
    let old := run (batch a b m) xs
    have hlen : old.length = xs.length+m := by simp [old, run_length, batch_length]
    rw [batch, run_append]
    change (old ++ [_]).getD _ false = _
    by_cases eq : j = m
    · subst j
      rw [← hlen, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      change (old.getD (a m) false || (old.getD (b m) false || false)) = _
      obtain ⟨ha,hb⟩ := valid m (by omega)
      dsimp only [old]
      rw [keep _ _ _ ha, keep _ _ _ hb, Bool.or_false]
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact ih (fun t h => valid t (by omega)) (by omega)

-- Port zero is the block activity bit. The other ports come in false/true pairs.
def lit (i : Nat) (b : Bool) : Nat := 1+2*i+b.toNat

def combine (left right : Nat → Nat) (base j : Nat) : Nat :=
  if j = 1 then left 0 else if j = 2 then right 0
  else if j = 0 then base else base+(j-2)

theorem lit_succ (i : Nat) (b : Bool) : lit (i+1) b = lit i b+2 := by
  simp [lit]; omega

theorem combine_succ (a b : Nat → Nat) (base i : Nat) (z : Bool) :
    combine a b base (lit (i+1) z) = base+lit i z := by
  have h : 0 < lit i z := by simp [lit]
  rw [lit_succ]
  unfold combine
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  omega

theorem split_eq (v j d : Nat) (hd : d < 2) (live : Bool) :
    decide (2*j+d = v ∧ live = true) =
      decide (j = v/2 ∧ decide (v % 2=d ∧ live = true) = true) := by
  by_cases eq : 2*j+d = v
  · have div : j = v/2 := by omega
    have rem : v % 2 = d := by omega
    simp [div,rem]; omega
  · by_cases div : j = v/2
    · have rem : v % 2 ≠ d := by omega
      simp [eq,rem]
    · simp [eq,div]

theorem merge_bits (v : Nat) (q live : Bool) :
    (decide (q=true ∧ decide (v % 2=0 ∧ live=true)=true) ||
      decide (q=true ∧ decide (v % 2=1 ∧ live=true)=true)) =
        decide (q=true ∧ live=true) := by
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;>
    cases q <;> cases live <;> simp [h]

-- Split a block into its even and odd positions. Their activity ports give bit zero.
-- Joining their corresponding ports gives every higher bit and the new activity bit.
-- Retaining the linear term in the budget pays for all joins in the induction.
theorem make (k base : Nat) (f : Nat → Nat) (valid : ∀ j < 2^k, f j < base) :
    ∃ (gs : List Gate) (p : Nat → Nat),
      Monotone2 (⟨gs, 0⟩ : Circuit) ∧
      gs.length+(2*k+3) ≤ 3*2^k ∧
      (∀ j < 2*k+1, p j < base+gs.length) ∧
      ∀ xs : List Bool, xs.length = base → ∀ v < 2^k, ∀ live : Bool,
        (∀ j < 2^k, xs.getD (f j) false = decide (j=v ∧ live=true)) →
        (run gs xs).getD (p 0) false = live ∧
        ∀ i < k, ∀ b : Bool, (run gs xs).getD (p (lit i b)) false =
          decide (v.testBit i=b ∧ live=true) := by
  induction k generalizing base f with
  | zero =>
    refine ⟨[], fun _ => f 0, ?_, by decide, ?_, ?_⟩
    · simp [Monotone2]
    · intro j hj; simpa using valid 0 (by decide)
    · intro xs hx v hv live rows
      have vz : v=0 := by simp at hv; omega
      subst v
      refine ⟨?_, by omega⟩
      simpa [run, Circuit.wires] using rows 0 (by decide)
  | succ k ih =>
    have pow : 2^(k+1) = 2^k*2 := pow_succ _ _
    obtain ⟨gl, a, ml, sl, va, sa⟩ := ih base (fun j => f (2*j))
      (fun j hj => valid _ (by rw [pow]; omega))
    obtain ⟨gr, b, mr, sr, vb, sb⟩ := ih (base+gl.length) (fun j => f (2*j+1))
      (fun j hj => by have := valid (2*j+1) (by rw [pow]; omega); omega)
    let start := base + gl.length + gr.length
    let m := 2*k+1
    refine ⟨gl ++ gr ++ batch a b m, combine a b start, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · rcases List.mem_append.mp hg with hg | hg
        · exact ml g hg
        · exact mr g hg
      · exact batch_mono a b m g hg
    · simp only [List.length_append, batch_length, m, pow]
      omega
    · intro j hj
      have al := va 0 (by omega)
      have br := vb 0 (by omega)
      simp only [List.length_append, batch_length, combine, start, m]
      split <;> (try split) <;> (try split) <;> omega
    · intro xs hx v hv live row
      have small : v/2 < 2^k := by rw [pow] at hv; omega
      let ys := run gl xs
      let zs := run gr ys
      have ly : ys.length = base+gl.length := by simp [ys,run_length,hx]
      have lz : zs.length = start := by simp [zs,run_length,ly,start]
      let even := decide (v % 2=0 ∧ live=true)
      let odd := decide (v % 2=1 ∧ live=true)
      have left := sa xs hx (v/2) small even (by
        intro j hj
        rw [row _ (by rw [pow]; omega)]
        simpa [even] using split_eq v j 0 (by decide) live)
      have right := sb ys ly (v/2) small odd (by
        intro j hj
        have hj' : 2*j+1 < 2^(k+1) := by rw [pow]; omega
        rw [show ys.getD (f (2*j+1)) false = xs.getD (f (2*j+1)) false from
          keep gl xs _ (hx ▸ valid _ hj'), row _ hj']
        exact split_eq v j 1 (by decide) live)
      have stable (j : Nat) (hj : j < m) : zs.getD (a j) false = ys.getD (a j) false :=
        keep gr ys _ (ly ▸ va j hj)
      have joined (j : Nat) (hj : j < m) :
          (run (batch a b m) zs).getD (start+j) false =
            (ys.getD (a j) false || zs.getD (b j) false) := by
        rw [← lz, batch_read _ _ _ _ (fun t ht => by
          have aok := va t ht; have bok := vb t ht
          dsimp [start] at lz; omega) j hj, stable j hj]
      rw [run_append, run_append]
      change (run (batch a b m) zs).getD _ false = _ ∧ _
      constructor
      · change (run (batch a b m) zs).getD start false = live
        have h := joined 0 (by dsimp [m]; omega)
        have ha0 : ys.getD (a 0) false = even := left.1
        have hb0 : zs.getD (b 0) false = odd := right.1
        simp only [Nat.add_zero, ha0, hb0] at h
        rw [h]
        rcases Nat.mod_two_eq_zero_or_one v with r | r <;> cases live <;> simp [even,odd,r]
      · intro i hi y
        cases i with
        | zero =>
          have a0 := va 0 (by omega)
          have b0 := vb 0 (by omega)
          have ja : (run (batch a b m) zs).getD (a 0) false = even := by
            rw [keep _ _ _ (by dsimp [start] at lz; omega), stable 0 (by dsimp [m]; omega)]
            exact left.1
          have jb : (run (batch a b m) zs).getD (b 0) false = odd := by
            rw [keep _ _ _ (by dsimp [start] at lz; omega)]
            exact right.1
          cases y
          · change (run (batch a b m) zs).getD (a 0) false = _
            rw [ja]; rcases Nat.mod_two_eq_zero_or_one v with r | r <;> simp [even,Nat.testBit_zero,r]
          · change (run (batch a b m) zs).getD (b 0) false = _
            rw [jb]; simp [odd,Nat.testBit_zero]
        | succ i =>
          have ik : i < k := by omega
          have jid : lit i y < m := by cases y <;> simp [lit,m] <;> omega
          rw [combine_succ, joined _ jid, left.2 i ik y, right.2 i ik y, Nat.testBit_succ]
          simpa only [even, odd, decide_eq_true_eq] using merge_bits v (decide ((v/2).testBit i=y)) live

end PEqualNP.Outside.L_meta_8981

theorem PEqualNP.Outside.L_meta_8981 : ∀ (n l : ℕ), ∃ gs : List PEqualNP.CircuitLowerBounds.Gate, PEqualNP.MetaComplexity.Monotone2 (⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ gs.length ≤ 3 * 2 ^ l ∧ ∃ w : Fin l → Bool → ℕ, ∀ (u : Fin n) (v : Fin (2 ^ l)) (i : Fin l) (b : Bool), ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (PEqualNP.Represents.oneEach u v)).getD (w i b) false = decide ((v : ℕ).testBit i = b) := by
  intro n l
  obtain ⟨gs, p, legal, cost, _, spec⟩ := PEqualNP.Outside.L_meta_8981.make l
    (n + 2^l) (fun j => n+j) (fun j hj => by omega)
  refine ⟨gs, legal, by omega, fun i b => p (PEqualNP.Outside.L_meta_8981.lit i b), ?_⟩
  intro u v i b
  have result := spec (PEqualNP.Represents.oneEach u v)
    (by simp [PEqualNP.Represents.oneEach]) v v.isLt true (by
      intro j hj
      simp [PEqualNP.Represents.oneEach, List.getD_eq_getElem?_getD, hj, Fin.ext_iff])
  simpa [PEqualNP.Outside.L_meta_8981.run] using result.2 i i.isLt b
