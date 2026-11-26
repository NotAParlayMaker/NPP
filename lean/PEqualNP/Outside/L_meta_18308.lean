import PEqualNP.Outside.L_meta_17341

-- The restricted truth tables, live-wire checker and soundness lemmas come from L_meta_17341.
namespace PEqualNP.Outside.L_meta_18308_aux
open PEqualNP.Outside.L_meta_17341
def gate : Gt := (false, 0, 6)
def extra : List (ℕ × ℕ) := [(1,12),(64,12),(256,12)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma r0 : okR topC [] (pr rawT 1) (1,12) = true := by decide +kernel
lemma b0 : Imp [] 1 12 := okR_imp topC_ok (x := (_,12)) (Or.inl rfl) r0 (fun y hy => ai3 y (List.mem_of_mem_filter hy))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma r1 : okR topC [] (pr rawT 64) (64,12) = true := by decide +kernel
lemma b1 : Imp [] 64 12 := okR_imp topC_ok (x := (_,12)) (Or.inl rfl) r1 (fun y hy => ai3 y (List.mem_of_mem_filter hy))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma r2 : okR topC [] (pr rawT 256) (256,12) = true := by decide +kernel
lemma b2 : Imp [] 256 12 := okR_imp topC_ok (x := (_,12)) (Or.inl rfl) r2 (fun y hy => ai3 y (List.mem_of_mem_filter hy))
def tbl := extra ++ rawT
lemma bounds : ∀ y ∈ tbl, Imp [] y.1 y.2 := by
  intro y hy
  rcases List.mem_append.mp hy with h|h
  · simp only [extra, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl
    · exact b0
    · exact b1
    · exact b2
  · exact ai3 y h
def selected : List ℕ := [4, 8, 1, 16, 64, 2, 17, 32, 68, 72, 128, 256, 5, 9, 12, 20, 24, 132, 264, 32768, 6, 10, 18, 33, 34, 36, 40, 65]
abbrev Retains (owned : List ℕ) := ∀ y ∈ tbl, y.1 ∈ owned → Imp [gate] y.1 y.2
lemma noOwned : Retains [] := own0
lemma keepBound {z b : ℕ} {owned : List ℕ} (prev : Retains owned)
    (mem : (z,b) ∈ tbl) (unique : tbl.all (fun x => !Nat.beq x.1 z || Nat.beq x.2 b) = true)
    (check : okR topC [gate] (tabE gate owned (pr tbl z)) (z,b) = true) : Retains (z :: owned) := by
  apply ownOne (c := z) (L := b) _ unique prev
  apply okR_imp topC_ok (x := (z,b)) (Or.inr ⟨gate,rfl,by decide,by decide,bounds (z,b) mem⟩) check
  exact tabE_ok (fun y hy => bounds y (List.mem_of_mem_filter hy)) (fun y hy h => prev y (List.mem_of_mem_filter hy) h)
def owned0 : List ℕ := []
def owned1 := 132 :: owned0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma keep0 : Retains owned1 := keepBound (z := 132) (b := 10) noOwned (by decide +kernel) (by decide +kernel) (by decide +kernel)
def owned2 := 264 :: owned1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma keep1 : Retains owned2 := keepBound (z := 264) (b := 11) keep0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def owned3 := 136 :: owned2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma keep2 : Retains owned3 := keepBound (z := 136) (b := 10) keep1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def owned4 := 144 :: owned3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma keep3 : Retains owned4 := keepBound (z := 144) (b := 10) keep2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def owned5 := 260 :: owned4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma keep4 : Retains owned5 := keepBound (z := 260) (b := 10) keep3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def owned6 := 48 :: owned5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma keep5 : Retains owned6 := keepBound (z := 48) (b := 9) keep4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def owned7 := 4 :: owned6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma keep6 : Retains owned7 := keepBound (z := 4) (b := 13) keep5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def owned8 := 16 :: owned7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma keep7 : Retains owned8 := keepBound (z := 16) (b := 13) keep6 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def owned9 := 2 :: owned8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma keep8 : Retains owned9 := keepBound (z := 2) (b := 12) keep7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def owned10 := 32 :: owned9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma keep9 : Retains owned10 := keepBound (z := 32) (b := 12) keep8 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def owned11 := 128 :: owned10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma keep10 : Retains owned11 := keepBound (z := 128) (b := 12) keep9 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def owned12 := 256 :: owned11
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma keep11 : Retains owned12 := keepBound (z := 256) (b := 12) keep10 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def owned13 := 2048 :: owned12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma keep12 : Retains owned13 := keepBound (z := 2048) (b := 10) keep11 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def projections := tabE gate owned13 (pick tbl selected)
lemma projected : ∀ y ∈ projections, Imp [gate] y.1 y.2 := rootQ bounds keep12
def bucket0 : ℕ × ℕ := (0, 1)
def bucket1 : ℕ × ℕ := (((17179869184 * 2 ^ 56 + 281474976710656) * 2 ^ 56 + 0), 0)
def bucket2 : ℕ × ℕ := (((137439477760 * 2 ^ 56 + 0) * 2 ^ 56 + 0), 0)
def bucket3 : ℕ × ℕ := ((((256 * 2 ^ 56 + 274877906944) * 2 ^ 56 + 0) * 2 ^ 56 + 0), 0)
def bucket4 : ℕ × ℕ := (((35184372088832 * 2 ^ 56 + 65536) * 2 ^ 56 + 8), 0)
def bucket5 : ℕ × ℕ := (((9007199254740992 * 2 ^ 56 + 8388608) * 2 ^ 56 + 32), 0)
def bucket6 : ℕ × ℕ := ((((4096 * 2 ^ 56 + 0) * 2 ^ 56 + 134217728) * 2 ^ 56 + 128), 0)
def bucket7 : ℕ × ℕ := ((((32768 * 2 ^ 56 + 0) * 2 ^ 56 + 68719476736) * 2 ^ 56 + 16384), 0)
def bucket8 : ℕ × ℕ := ((((16777216 * 2 ^ 56 + 0) * 2 ^ 56 + 36028797018963968) * 2 ^ 56 + 536870912), 0)
def bucket9 : ℕ × ℕ := ((((134217728 * 2 ^ 56 + 1) * 2 ^ 56 + 0) * 2 ^ 56 + 4294967296), 0)
def bucket10 : ℕ × ℕ := ((((1073741824 * 2 ^ 56 + 16) * 2 ^ 56 + 0) * 2 ^ 56 + 274877906944), 0)
def bucket11 : ℕ × ℕ := ((((4294967296 * 2 ^ 56 + 2048) * 2 ^ 56 + 0) * 2 ^ 56 + 1099511627776), 0)
def bucket12 : ℕ × ℕ := ((((2199023255552 * 2 ^ 56 + 4096) * 2 ^ 56 + 0) * 2 ^ 56 + 1125899906842624), 0)
def bucket13 : ℕ × ℕ := ((((4398046511104 * 2 ^ 56 + 16384) * 2 ^ 56 + 0) * 2 ^ 56 + 4503599627370496), 0)
def bucket14 : ℕ × ℕ := ((((63766154669823 * 2 ^ 56 + 63014778699229166) * 2 ^ 56 + 35747253180071927) * 2 ^ 56 + 66426715282325335), 0)
def bucket15 : ℕ × ℕ := (((67108864 * 2 ^ 56 + 8) * 2 ^ 56 + 0), 0)
def bucket16 : ℕ × ℕ := (((2147483648 * 2 ^ 56 + 32768) * 2 ^ 56 + 0), 0)
def buckets : List (ℕ × ℕ) := [bucket0, bucket1, bucket2, bucket3, bucket4, bucket5, bucket6, bucket7, bucket8, bucket9, bucket10, bucket11, bucket12, bucket13, bucket14, bucket15, bucket16]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma coverBuckets : mFull buckets = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_0 : chkG topC [gate] projections (1,0) 0 14 0 bucket0.1 bucket0.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_1 : chkG topC [gate] projections (1,0) 0 14 0 bucket1.1 bucket1.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_2 : chkG topC [gate] projections (1,0) 0 14 0 bucket2.1 bucket2.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_3 : chkG topC [gate] projections (1,0) 0 14 0 bucket3.1 bucket3.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_4 : chkG topC [gate] projections (1,0) 0 14 0 bucket4.1 bucket4.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_5 : chkG topC [gate] projections (1,0) 0 14 0 bucket5.1 bucket5.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_6 : chkG topC [gate] projections (1,0) 0 14 0 bucket6.1 bucket6.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_7 : chkG topC [gate] projections (1,0) 0 14 0 bucket7.1 bucket7.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_8 : chkG topC [gate] projections (1,0) 0 14 0 bucket8.1 bucket8.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_9 : chkG topC [gate] projections (1,0) 0 14 0 bucket9.1 bucket9.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_10 : chkG topC [gate] projections (1,0) 0 14 0 bucket10.1 bucket10.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_11 : chkG topC [gate] projections (1,0) 0 14 0 bucket11.1 bucket11.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_12 : chkG topC [gate] projections (1,0) 0 14 0 bucket12.1 bucket12.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_13 : chkG topC [gate] projections (1,0) 0 14 0 bucket13.1 bucket13.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_14 : chkG topC [gate] projections (1,0) 0 14 0 bucket14.1 bucket14.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_15 : chkG topC [gate] projections (1,0) 0 14 0 bucket15.1 bucket15.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase0_16 : chkG topC [gate] projections (1,0) 0 14 0 bucket16.1 bucket16.2 = false := by decide +kernel
lemma case0 : ∀ p ∈ buckets, chkG topC [gate] projections (1,0) 0 14 0 p.1 p.2 = false := by
  intro p hp
  simp only [buckets,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact noCase0_0
  · exact noCase0_1
  · exact noCase0_2
  · exact noCase0_3
  · exact noCase0_4
  · exact noCase0_5
  · exact noCase0_6
  · exact noCase0_7
  · exact noCase0_8
  · exact noCase0_9
  · exact noCase0_10
  · exact noCase0_11
  · exact noCase0_12
  · exact noCase0_13
  · exact noCase0_14
  · exact noCase0_15
  · exact noCase0_16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_0 : chkG topC [gate] projections (1,0) 0 14 1 bucket0.1 bucket0.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_1 : chkG topC [gate] projections (1,0) 0 14 1 bucket1.1 bucket1.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_2 : chkG topC [gate] projections (1,0) 0 14 1 bucket2.1 bucket2.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_3 : chkG topC [gate] projections (1,0) 0 14 1 bucket3.1 bucket3.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_4 : chkG topC [gate] projections (1,0) 0 14 1 bucket4.1 bucket4.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_5 : chkG topC [gate] projections (1,0) 0 14 1 bucket5.1 bucket5.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_6 : chkG topC [gate] projections (1,0) 0 14 1 bucket6.1 bucket6.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_7 : chkG topC [gate] projections (1,0) 0 14 1 bucket7.1 bucket7.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_8 : chkG topC [gate] projections (1,0) 0 14 1 bucket8.1 bucket8.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_9 : chkG topC [gate] projections (1,0) 0 14 1 bucket9.1 bucket9.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_10 : chkG topC [gate] projections (1,0) 0 14 1 bucket10.1 bucket10.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_11 : chkG topC [gate] projections (1,0) 0 14 1 bucket11.1 bucket11.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_12 : chkG topC [gate] projections (1,0) 0 14 1 bucket12.1 bucket12.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_13 : chkG topC [gate] projections (1,0) 0 14 1 bucket13.1 bucket13.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_14 : chkG topC [gate] projections (1,0) 0 14 1 bucket14.1 bucket14.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_15 : chkG topC [gate] projections (1,0) 0 14 1 bucket15.1 bucket15.2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma noCase1_16 : chkG topC [gate] projections (1,0) 0 14 1 bucket16.1 bucket16.2 = false := by decide +kernel
lemma case1 : ∀ p ∈ buckets, chkG topC [gate] projections (1,0) 0 14 1 p.1 p.2 = false := by
  intro p hp
  simp only [buckets,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact noCase1_0
  · exact noCase1_1
  · exact noCase1_2
  · exact noCase1_3
  · exact noCase1_4
  · exact noCase1_5
  · exact noCase1_6
  · exact noCase1_7
  · exact noCase1_8
  · exact noCase1_9
  · exact noCase1_10
  · exact noCase1_11
  · exact noCase1_12
  · exact noCase1_13
  · exact noCase1_14
  · exact noCase1_15
  · exact noCase1_16
def rest : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma otherCases : chkT topC [gate] projections (1,0) 0 14 rest FF 1 = false := by decide +kernel
lemma cost : Imp [gate] 0 15 := by
  apply rootT topC_ok (F := []) (Q := projections) (fb := (1,0)) (K := 14)
    (Ms := [(0,buckets),(1,buckets)]) (tt := [rest]) (by decide) (by decide)
    (by decide) base projected (by decide +kernel) (by decide +kernel) (by simp)
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact ⟨coverBuckets,case0⟩
    · exact ⟨coverBuckets,case1⟩
  · intro ts h
    rw [List.mem_singleton.mp h]
    exact otherCases
  · decide +kernel
end PEqualNP.Outside.L_meta_18308_aux

open PEqualNP.Outside.L_meta_17341 PEqualNP.Outside.L_meta_18308_aux in
theorem PEqualNP.Outside.L_meta_18308 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)) → 16 ≤ C.size := by
  intro D legal first correct
  have vals : ∀ x, D.eval (List.ofFn x) = f x := fun x => congrFun correct x
  obtain ⟨q,size,sol⟩ := bridge1 D legal vals gate (fun y => y 0 && y 6) first (fun _ => true) rfl
    (fun k _ => by rw [tw_op (e := gate) (by decide),op_bit]; rfl)
  by_contra! small
  exact cost q (by omega) sol
