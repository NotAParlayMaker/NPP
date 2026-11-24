import Mathlib.Data.Set.Basic

namespace PEqualNP.Outside.L_meta_1402

private abbrev Input := Fin 10 → Bool
private abbrev Fn := Input → Bool
private def rows : List ℕ := [3, 17, 65, 513, 6, 34, 130, 12, 68, 260, 24, 136, 520, 48, 272, 96, 544, 192, 384, 768, 165, 330, 660, 297, 594]
private def base : List ℕ := [9437199, 18874481, 5243792, 10493056, 20997122, 9543712, 19038468, 5638208, 11289088, 21565448]
private def chunk0 : List ℕ := [1, 2, 4, 8, 16]
private def chunk1 : List ℕ := [32, 64, 128, 256, 512]
private def chunk2 : List ℕ := [1024, 2048, 4096, 8192, 16384]
private def chunk3 : List ℕ := [32768, 65536, 131072, 262144, 524288]
private def chunk4 : List ℕ := [1048576, 2097152, 4194304, 5242880, 5243792]
private def chunk5 : List ℕ := [5638208, 5639120, 8388608, 9437184, 9437199]
private def chunk6 : List ℕ := [9543712, 9543727, 10485760, 10493056, 11289088]
private def chunk7 : List ℕ := [11296384, 11541647, 11648160, 12337679, 12444192]
private def chunk8 : List ℕ := [13632415, 13738928, 14026831, 14133344, 15736720]
private def chunk9 : List ℕ := [16129216, 16532368, 16665152, 16777216, 18874368]
private def chunk10 : List ℕ := [18874481, 19038468, 19038581, 20971520, 20997122]
private def chunk11 : List ℕ := [21565448, 21591050, 22046610, 22441026, 22614936]
private def chunk12 : List ℕ := [23009352, 23094387, 23258374, 23662713, 23826700]
private def chunk13 : List ℕ := [24118257, 24282004, 24512625, 24545604, 27270385]
private def chunk14 : List ℕ := [27434372, 28066417, 28230404, 28311679, 28418161]
private def chunk15 : List ℕ := [28475663, 28549412, 30434319, 30532642, 31002639]
private def chunk16 : List ℕ := [31043624, 31489154, 32054408, 32269826, 32330248]
private def one : List ℕ := (chunk0 ++ (chunk1 ++ (chunk2 ++ (chunk3 ++ (chunk4 ++ (chunk5 ++ (chunk6 ++ (chunk7 ++ (chunk8 ++ (chunk9 ++ (chunk10 ++ (chunk11 ++ (chunk12 ++ (chunk13 ++ (chunk14 ++ (chunk15 ++ chunk16))))))))))))))))
private def input (i : Fin 25) : Input := fun v => (rows.getD i.val 0).testBit v.val
private def rep (f : Fn) (a : ℕ) := ∀ i : Fin 25, f (input i) = a.testBit i.val

private theorem vars : ∀ j : Fin 10, ∃ a ∈ base, rep (fun x => x j) a := by
  intro j
  refine ⟨base.getD j.val 0, ?_, ?_⟩
  · exact (by decide +kernel : ∀ i : Fin 10, base.getD i.val 0 ∈ base) j
  · exact (by decide +kernel : ∀ i : Fin 10, ∀ r : Fin 25,
      input r i = (base.getD i.val 0).testBit r.val) j

private theorem repAnd {f g : Fn} {a b : ℕ} (h : rep f a) (k : rep g b) :
    rep (fun x => f x && g x) (a &&& b) := by
  intro i
  simp only [h i, k i, Nat.testBit_and]
private theorem repOr {f g : Fn} {a b : ℕ} (h : rep f a) (k : rep g b) :
    rep (fun x => f x || g x) (a ||| b) := by
  intro i
  simp only [h i, k i, Nat.testBit_or]

private def count (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k+1 => count f k + (if f k then 1 else 0)

private theorem bounded (f : ℕ → Bool) (k : ℕ) : count f k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [count]; split <;> omega

private theorem monoCount {f g : ℕ → Bool} (h : ∀ i, f i = true → g i = true)
    (k : ℕ) : count f k ≤ count g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hh := h k
    simp only [count]
    by_cases hf : f k = true <;> by_cases hg : g k = true <;> simp_all <;> omega

private theorem unionCount (f g : ℕ → Bool) (k : ℕ) :
    count (fun i => f i || g i) k ≤ count f k + count g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [count]
    by_cases hf : f k = true <;> by_cases hg : g k = true <;> simp [Bool.or_eq_true,hf,hg] <;> omega

private def p (a : ℕ) := count (fun i => a.testBit i) 20
private def n (a : ℕ) := count (fun i => !(a.testBit (20+i))) 5
private abbrev level2 (a : ℕ) := p a ≤ 16 ∧ (n a = 5 → p a ≤ 4) ∧ (3 ≤ n a → p a ≤ 9)
private abbrev level3 (a : ℕ) := (n a = 5 → p a ≤ 9) ∧ (p a = 20 → n a ≤ 2)
private abbrev level4 (a : ℕ) := p a < 20 ∨ n a < 5

private theorem splitCounts (a b : ℕ) :
    p (a &&& b) ≤ p a ∧ p (a &&& b) ≤ p b ∧ n (a &&& b) ≤ n a + n b ∧
    n (a ||| b) ≤ n a ∧ n (a ||| b) ≤ n b ∧ p (a ||| b) ≤ p a + p b := by
  refine ⟨monoCount (fun i hi => ?_) 20, monoCount (fun i hi => ?_) 20, ?_,
    monoCount (fun i hi => ?_) 5, monoCount (fun i hi => ?_) 5, ?_⟩
  · exact (Bool.and_eq_true_iff.mp ((Nat.testBit_and ..) ▸ hi)).1
  · exact (Bool.and_eq_true_iff.mp ((Nat.testBit_and ..) ▸ hi)).2
  · simpa only [n, Nat.testBit_and, Bool.not_and] using
      unionCount (fun i => !(a.testBit (20+i))) (fun i => !(b.testBit (20+i))) 5
  · simp only [Nat.testBit_or, Bool.not_or, Bool.and_eq_true] at hi
    exact hi.1
  · simp only [Nat.testBit_or, Bool.not_or, Bool.and_eq_true] at hi
    exact hi.2
  · simpa only [p, Nat.testBit_or] using unionCount a.testBit b.testBit 20

private theorem first (a b : ℕ) (ha : a ∈ base) (hb : b ∈ base) :
    (a &&& b) ∈ one ∧ (a ||| b) ∈ one := by
  have h : base.all (fun x => base.all (fun y => decide ((x &&& y) ∈ one ∧ (x ||| y) ∈ one))) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h _ ha) _ hb)

private def checked (xs : List ℕ) : Bool := xs.all (fun a => one.all (fun b => decide (level2 (a &&& b) ∧ level2 (a ||| b))))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert0 : checked chunk0 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert1 : checked chunk1 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert2 : checked chunk2 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert3 : checked chunk3 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert4 : checked chunk4 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert5 : checked chunk5 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert6 : checked chunk6 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert7 : checked chunk7 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert8 : checked chunk8 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert9 : checked chunk9 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert10 : checked chunk10 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert11 : checked chunk11 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert12 : checked chunk12 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert13 : checked chunk13 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert14 : checked chunk14 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert15 : checked chunk15 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem cert16 : checked chunk16 = true := by decide +kernel


private theorem second (a b : ℕ) (ha : a ∈ one) (hb : b ∈ one) :
    level2 (a &&& b) ∧ level2 (a ||| b) := by
  simp only [one, List.mem_append] at ha
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert0 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert1 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert2 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert3 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert4 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert5 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert6 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert7 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert8 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert9 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert10 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert11 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert12 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert13 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert14 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert15 a ha) b hb)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp cert16 a ha) b hb)

private theorem third (a b : ℕ) (ha : level2 a) (hb : level2 b) :
    level3 (a &&& b) ∧ level3 (a ||| b) := by
  have hs := splitCounts a b
  have na : n a ≤ 5 := bounded _ _
  have nb : n b ≤ 5 := bounded _ _
  unfold level2 at ha hb
  unfold level3
  omega

private theorem fourth (a b : ℕ) (ha : level3 a) (hb : level3 b) :
    level4 (a &&& b) ∧ level4 (a ||| b) := by
  have hs := splitCounts a b
  have na : n a ≤ 5 := bounded _ _
  have nb : n b ≤ 5 := bounded _ _
  have pa : p a ≤ 20 := bounded _ _
  have pb : p b ≤ 20 := bounded _ _
  unfold level3 at ha hb
  unfold level4
  omega

private def stage : ℕ → ℕ → Prop
  | 0, a => a ∈ base
  | 1, a => a ∈ one
  | 2, a => level2 a
  | 3, a => level3 a
  | 4, a => level4 a
  | _+5, _ => True

private theorem step (k a b : ℕ) (ha : stage k a) (hb : stage k b) :
    stage (k+1) (a &&& b) ∧ stage (k+1) (a ||| b) := by
  match k with
  | 0 => exact first a b ha hb
  | 1 => exact second a b ha hb
  | 2 => exact third a b ha hb
  | 3 => exact fourth a b ha hb
  | 4 => exact ⟨trivial,trivial⟩
  | _+5 => exact ⟨trivial,trivial⟩

private def target (z : Input) : Bool := ((z 0 || z 5) && (z 1 || z 6)) || ((z 1 || z 6) && (z 2 || z 7)) || ((z 2 || z 7) && (z 3 || z 8)) || ((z 3 || z 8) && (z 4 || z 9)) || ((z 4 || z 9) && (z 0 || z 5))

private theorem reject (a : ℕ) (h : rep target a) : ¬level4 a := by
  have ht : ∀ i : Fin 25, target (input i) = decide (i.val < 20) := by decide +kernel
  have bits (i : ℕ) (hi : i < 25) : a.testBit i = decide (i < 20) :=
    (h ⟨i,hi⟩).symm.trans (ht ⟨i,hi⟩)
  have cp : ∀ k ≤ 20, count a.testBit k = k := by
    intro k
    induction k with
    | zero => simp [count]
    | succ k ih => intro hk; simp [count, ih (by omega), bits k (by omega), show k < 20 by omega]
  have cn : ∀ k ≤ 5, count (fun i => !(a.testBit (20+i))) k = k := by
    intro k
    induction k with
    | zero => simp [count]
    | succ k ih => intro hk; simp [count, ih (by omega), bits (20+k) (by omega)]
  have hp : p a = 20 := cp _ (by decide)
  have hn : n a = 5 := cn _ (by decide)
  simp [level4,hp,hn]

end PEqualNP.Outside.L_meta_1402

open PEqualNP.Outside.L_meta_1402 in
theorem PEqualNP.Outside.L_meta_1402 : ¬ (∀ T : ℕ → Set ((Fin 10 → Bool) → Bool), (∀ i : Fin 10, (fun x : Fin 10 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 10 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 10 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 10 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 10 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 10 → Bool => ((z 0 || z 5) && (z 1 || z 6)) || ((z 1 || z 6) && (z 2 || z 7)) || ((z 2 || z 7) && (z 3 || z 8)) || ((z 3 || z 8) && (z 4 || z 9)) || ((z 4 || z 9) && (z 0 || z 5))) ∈ T 4) := by
  intro claimed
  let T : ℕ → Set Fn := fun k => {f | ∃ a, rep f a ∧ stage k a}
  have bad := claimed T (by
    intro i
    obtain ⟨a,ha,hr⟩ := vars i
    exact ⟨a,hr,ha⟩) (by
    rintro k f ⟨a,hr,ha⟩
    exact ⟨a,hr,by simpa using (step k a a ha ha).1⟩) (by
    rintro k f g ⟨a,hf,ha⟩ ⟨b,hg,hb⟩
    obtain ⟨h1,h2⟩ := step k a b ha hb
    exact ⟨⟨_,repAnd hf hg,h1⟩,⟨_,repOr hf hg,h2⟩⟩)
  obtain ⟨a,hr,ha⟩ := bad
  exact reject a hr ha
