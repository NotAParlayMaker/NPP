import Mathlib
import PEqualNP.Defs

open PEqualNP.ProofComplexity

namespace PEqualNP.Outside.L_pcx_095

abbrev V : Type := (Fin 6 × Fin 3) ⊕ Fin 6

def idx : V → ℕ := Sum.elim (fun p => 3 * p.1.val + p.2.val) (fun e => 18 + e.val)

def code (l : V × Bool) : ℕ := 2 * idx l.1 + (if l.2 then 1 else 0)

def cl (m : ℕ) : Clause V := Finset.univ.filter (fun l => m.testBit (code l) = true)

def pop (m : ℕ) : ℕ := ((List.range 48).filter (fun i => m.testBit i)).length

def rs (m n v : ℕ) : ℕ := (m ^^^ 2 ^ (2 * v + 1)) ||| (n ^^^ 2 ^ (2 * v))

lemma idx_inj : ∀ a b : V, idx a = idx b → a = b := by decide +kernel
lemma idx_lt : ∀ a : V, idx a < 24 := by decide +kernel
lemma code_inj : ∀ a b : V × Bool, code a = code b → a = b := by
  rintro ⟨a, s⟩ ⟨b, t⟩ h
  have hi : idx a = idx b := by
    cases s <;> cases t <;> simp [code] at h <;> omega
  have := idx_inj a b hi
  subst this
  cases s <;> cases t <;> simp [code] at h <;> rfl
lemma code_lt : ∀ a : V × Bool, code a < 48 := by decide +kernel
lemma code_surj : ∀ i : Fin 48, ∃ a : V × Bool, code a = i.val := by decide +kernel
lemma idx_surj : ∀ i : Fin 24, ∃ a : V, idx a = i.val := by decide +kernel

lemma mem_cl (m : ℕ) (l : V × Bool) : l ∈ cl m ↔ m.testBit (code l) = true := by
  simp [cl]

lemma card_cl (m : ℕ) : (cl m).card = pop m := by
  have h : (cl m).image code = ((List.range 48).filter (fun i => m.testBit i)).toFinset := by
    ext i
    simp only [Finset.mem_image, mem_cl, List.mem_toFinset, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨code_lt a, ha⟩
    · rintro ⟨hi, hb⟩
      obtain ⟨a, ha⟩ := code_surj ⟨i, hi⟩
      simp only at ha
      exact ⟨a, by rw [ha]; exact hb, ha⟩
  have h2 : ((cl m).image code).card = (cl m).card :=
    Finset.card_image_of_injective _ (fun a b hab => code_inj a b hab)
  rw [← h2, h, List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range)]
  rfl

lemma testBit_flip (m i j : ℕ) (hi : m.testBit i = true) :
    (m ^^^ 2 ^ i).testBit j = true ↔ j ≠ i ∧ m.testBit j = true := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h; simp [hi]
  · have h' : j ≠ i := fun e => h e.symm
    simp [h, h']

lemma cl_flip (m : ℕ) (l : V × Bool) (hl : m.testBit (code l) = true) :
    cl (m ^^^ 2 ^ code l) = (cl m).erase l := by
  ext x
  rw [mem_cl, testBit_flip _ _ _ hl, Finset.mem_erase, mem_cl]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun e => h1 (by rw [e]), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun e => h1 (code_inj _ _ e), h2⟩

lemma code_pos (v : V) : code (v, true) = 2 * idx v + 1 := by simp [code]
lemma code_neg (v : V) : code (v, false) = 2 * idx v := by simp [code]

lemma cl_rs (m n : ℕ) (v : V) (hm : m.testBit (2 * idx v + 1) = true)
    (hn : n.testBit (2 * idx v) = true) :
    cl (rs m n (idx v)) = (cl m).erase (v, true) ∪ (cl n).erase (v, false) := by
  rw [← cl_flip m (v, true) (by rw [code_pos]; exact hm),
    ← cl_flip n (v, false) (by rw [code_neg]; exact hn), code_pos, code_neg]
  ext x
  rw [Finset.mem_union, mem_cl, mem_cl, mem_cl, rs, Nat.testBit_or, Bool.or_eq_true]

def ax1 (v : Fin 6) : ℕ := 42 * 2 ^ (6 * v.val)
def ax2 (u v : Fin 6) (a b c : Bool) : ℕ :=
  2 ^ (6 * (if a then v.val else u.val) + 1) ||| 2 ^ (6 * (if b then v.val else u.val) + 3)
    ||| 2 ^ (6 * (if c then v.val else u.val) + 5)
def ends : Fin 6 → Fin 6 × Fin 6 := ![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)]
def ax3 (e : Fin 6) (t : Fin 3) : ℕ :=
  2 ^ (36 + 2 * e.val) ||| 2 ^ (6 * (ends e).1.val + 2 * t.val)
    ||| 2 ^ (6 * (ends e).2.val + 2 * t.val)
def bt (i j e : Fin 6) : ℕ :=
  if (ends e).1 ≠ i ∧ (ends e).1 ≠ j ∧ (ends e).2 ≠ i ∧ (ends e).2 ≠ j then
    2 ^ (37 + 2 * e.val) else 0
def ax4 (i j : Fin 6) : ℕ :=
  bt i j 0 ||| bt i j 1 ||| bt i j 2 ||| bt i j 3 ||| bt i j 4 ||| bt i j 5

def F : Set (Clause V) := {C6 | ∃ v7 : Fin 6, C6 = Finset.univ.image (fun t8 : Fin 3 => ((Sum.inl (v7, t8) : (Fin 6 × Fin 3) ⊕ Fin 6), true))} ∪ {C9 | ∃ (u10 v11 : Fin 6) (f12 : Fin 3 → Bool), u10 ≠ v11 ∧ ¬ (u10 ≠ v11 ∧ u10.val / 3 = v11.val / 3) ∧ C9 = Finset.univ.image (fun t13 : Fin 3 => ((Sum.inl (if f12 t13 = true then v11 else u10, t13) : (Fin 6 × Fin 3) ⊕ Fin 6), true))} ∪ {C14 | ∃ (e15 : Fin 6) (t16 : Fin 3), C14 = {((Sum.inr e15 : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).1, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).2, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false)}} ∪ {C17 | ∃ S18 : Finset (Fin 6), S18.card = 2 ∧ C17 = (Finset.univ.filter (fun e19 : Fin 6 => ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).1 ∉ S18 ∧ ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).2 ∉ S18)).image (fun e20 : Fin 6 => ((Sum.inr e20 : (Fin 6 × Fin 3) ⊕ Fin 6), true))}

lemma cl1 : ∀ v7 : Fin 6, cl (ax1 v7) = Finset.univ.image (fun t8 : Fin 3 => ((Sum.inl (v7, t8) : (Fin 6 × Fin 3) ⊕ Fin 6), true)) := by
  decide +kernel

lemma cl2 : ∀ (u v : Fin 6) (a b c : Bool), cl (ax2 u v a b c) = Finset.univ.image (fun t13 : Fin 3 => ((Sum.inl (if (![a, b, c] : Fin 3 → Bool) t13 = true then v else u, t13) : (Fin 6 × Fin 3) ⊕ Fin 6), true)) := by
  decide +kernel

lemma cl3 : ∀ (e15 : Fin 6) (t16 : Fin 3), cl (ax3 e15 t16) = {((Sum.inr e15 : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).1, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).2, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false)} := by
  decide +kernel

lemma cl4 : ∀ i j : Fin 6, cl (ax4 i j) = (Finset.univ.filter (fun e19 : Fin 6 => ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).1 ∉ ({i, j} : Finset (Fin 6)) ∧ ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).2 ∉ ({i, j} : Finset (Fin 6)))).image (fun e20 : Fin 6 => ((Sum.inr e20 : (Fin 6 × Fin 3) ⊕ Fin 6), true)) := by
  decide +kernel

lemma fun_eq (f : Fin 3 → Bool) : f = ![f 0, f 1, f 2] := by
  ext i; fin_cases i <;> rfl

def isAx (m : ℕ) : Prop :=
  (∃ v, m = ax1 v) ∨ (∃ u v a b c, (u ≠ v ∧ ¬ (u ≠ v ∧ u.val / 3 = v.val / 3)) ∧ m = ax2 u v a b c)
    ∨ (∃ e t, m = ax3 e t) ∨ (∃ i j, i ≠ j ∧ m = ax4 i j)

lemma mem_F (C : Clause V) : C ∈ F ↔ ∃ m, isAx m ∧ C = cl m := by
  constructor
  · rintro (((⟨v, rfl⟩ | ⟨u, v, f, h1, h2, rfl⟩) | ⟨e, t, rfl⟩) | ⟨S, hS, rfl⟩)
    · exact ⟨_, Or.inl ⟨v, rfl⟩, (cl1 v).symm⟩
    · refine ⟨_, Or.inr (Or.inl ⟨u, v, f 0, f 1, f 2, ⟨h1, h2⟩, rfl⟩), ?_⟩
      rw [cl2, ← fun_eq f]
    · exact ⟨_, Or.inr (Or.inr (Or.inl ⟨e, t, rfl⟩)), (cl3 e t).symm⟩
    · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hS
      exact ⟨_, Or.inr (Or.inr (Or.inr ⟨i, j, hij, rfl⟩)), (cl4 i j).symm⟩
  · rintro ⟨m, (⟨v, rfl⟩ | ⟨u, v, a, b, c, ⟨h1, h2⟩, rfl⟩ | ⟨e, t, rfl⟩ | ⟨i, j, hij, rfl⟩), rfl⟩
    · exact Or.inl (Or.inl (Or.inl ⟨v, cl1 v⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨u, v, ![a, b, c], h1, h2, cl2 u v a b c⟩))
    · exact Or.inl (Or.inr ⟨e, t, cl3 e t⟩)
    · exact Or.inr ⟨{i, j}, Finset.card_pair hij, cl4 i j⟩

def K : List ℕ :=
  [42, 2688, 172032, 524328, 526848, 688128,
   2097186, 2099328, 2236416, 2621472, 2623488, 2752512,
   8388618, 8389248, 8429568, 8912904, 8913408, 8945664,
   10485762, 10485888, 10493952, 11010048, 33554472, 33556992,
   33718272, 134217762, 134219904, 134356992, 167772192, 167774208,
   167903232, 536870922, 536871552, 536911872, 570425352, 570425856,
   570458112, 671088642, 671088768, 671096832, 704643072, 2147483688,
   2147486208, 2147647488, 8589934626, 8589936768, 8590073856, 10737418272,
   10737420288, 10737549312, 34359738378, 34359739008, 34359779328, 36507222024,
   36507222528, 36507254784, 42949672962, 42949673088, 42949681152, 45097156608,
   68719476801, 68719476996, 68719477776, 274877911104, 274877923584, 274877973504,
   1099511631873, 1099511644164, 1099511693328, 2886218022912, 4398063550464, 4398114668544,
   4398319140864, 8933531975680, 9345848836096, 10995116277760, 17593276563456, 17596548120576,
   17609634349056, 35321811042304, 35734127902720, 37383395344384, 70369818181632, 70373040193536,
   70385928241152, 140874927308800, 141287244169216, 142936511610880, 184717953466368, 8796093022273,
   8796093022468, 8796093023248, 137455992832, 137507110912, 137711583232, 8796093026368,
   8796093038848, 8796093088768, 549772853248, 549823971328, 550028443648, 8796093026305,
   8796093038596, 8796093087760, 2199040294912, 2199091412992, 2199295885312, 35184372088897,
   35184372089092, 35184372089872, 138529472512, 141801029632, 154887258112, 35184372092992,
   35184372105472, 35184372155392, 550846332928, 554117890048, 567204118528, 35184372092929,
   35184372105220, 35184372154384, 2200113774592, 2203385331712, 2216471560192, 140737488355393,
   140737488355588, 140737488356368, 138512957440, 141734969344, 154623016960, 140737488359488,
   140737488371968, 140737488421888, 550829817856, 554051829760, 566939877376, 140737488359425,
   140737488371716, 140737488420880, 2200097259520, 2203319271424, 2216207319040]

def meets (m n : ℕ) : ℕ := ((m >>> 1) &&& n) &&& 93824992236885

def pairOk (m n : ℕ) : Bool :=
  (meets m n == 0) || (List.range 24).all (fun v =>
    !(m.testBit (2 * v + 1) && n.testBit (2 * v)) || K.contains (rs m n v) || Nat.ble 4 (pop (rs m n v)))

lemma K_closed : K.all (fun m => K.all (fun n => pairOk m n)) = true := by decide +kernel

lemma K_nonempty : K.all (fun m => !(pop m == 0)) = true := by decide +kernel

lemma K1 : ∀ v, ax1 v ∈ K := by decide +kernel
lemma K2 : ∀ (u v : Fin 6) (a b c : Bool), (u ≠ v ∧ ¬ (u ≠ v ∧ u.val / 3 = v.val / 3)) → ax2 u v a b c ∈ K := by
  decide +kernel
lemma K3 : ∀ e t, ax3 e t ∈ K := by decide +kernel
lemma K4 : ∀ i j, i ≠ j → ax4 i j ∈ K := by decide +kernel

lemma isAx_K (m : ℕ) (h : isAx m) : m ∈ K := by
  rcases h with ⟨v, rfl⟩ | ⟨u, v, a, b, c, h, rfl⟩ | ⟨e, t, rfl⟩ | ⟨i, j, hij, rfl⟩
  · exact K1 v
  · exact K2 u v a b c h
  · exact K3 e t
  · exact K4 i j hij

lemma mask_bit : ∀ v : Fin 24, (93824992236885 : ℕ).testBit (2 * v.val) = true := by decide +kernel

lemma step (m n : ℕ) (hm : m ∈ K) (hn : n ∈ K) (v : V) (h1 : m.testBit (2 * idx v + 1) = true)
    (h2 : n.testBit (2 * idx v) = true) (hc : pop (rs m n (idx v)) ≤ 3) : rs m n (idx v) ∈ K := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp K_closed m hm) n hn
  rw [pairOk, Bool.or_eq_true] at h
  rcases h with h | h
  · exfalso
    have h0 : meets m n = 0 := by simpa using h
    have hb : (meets m n).testBit (2 * idx v) = true := by
      rw [meets, Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_comm 1, h1, h2,
        mask_bit ⟨idx v, idx_lt v⟩]
      rfl
    rw [h0] at hb
    simp at hb
  · have hv := List.all_eq_true.mp h (idx v) (List.mem_range.mpr (idx_lt v))
    rw [h1, h2] at hv
    simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hv
    rcases hv with hv | hv
    · simpa using hv
    · have := Nat.le_of_ble_eq_true hv
      omega

lemma lower (π : List (Clause V)) (hd : IsDerivation F π) (hw : ∀ D ∈ π, D.card ≤ 3) :
    ∀ D ∈ π, ∃ m ∈ K, D = cl m := by
  induction hd with
  | nil => intro D hD; simp at hD
  | @ax π C _ hC ih =>
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · obtain ⟨m, hm, rfl⟩ := (mem_F _).mp hC
      exact ⟨m, isAx_K m hm, rfl⟩
    · exact ih (fun E hE => hw E (List.mem_cons_of_mem _ hE)) D hD
  | @res π A B R _ hA hB hr ih =>
    have ih' := ih (fun E hE => hw E (List.mem_cons_of_mem _ hE))
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · obtain ⟨m, hm, rfl⟩ := ih' A hA
      obtain ⟨n, hn, rfl⟩ := ih' B hB
      obtain ⟨v, hv1, hv2, hR⟩ := hr
      rw [mem_cl, code_pos] at hv1
      rw [mem_cl, code_neg] at hv2
      have hR' : D = cl (rs m n (idx v)) := by rw [cl_rs m n v hv1 hv2]; exact hR
      refine ⟨_, step m n hm hn v hv1 hv2 ?_, hR'⟩
      rw [← card_cl, ← hR']
      exact hw D List.mem_cons_self
    · exact ih' D hD

def Ax : List ℕ :=
  (List.finRange 6).map ax1
  ++ ((List.finRange 6).flatMap fun u => (List.finRange 6).flatMap fun v =>
      [true, false].flatMap fun a => [true, false].flatMap fun b => [true, false].flatMap fun c =>
      if u ≠ v ∧ ¬ (u ≠ v ∧ u.val / 3 = v.val / 3) then [ax2 u v a b c] else [])
  ++ ((List.finRange 6).flatMap fun e => (List.finRange 3).map fun t => ax3 e t)
  ++ ((List.finRange 6).flatMap fun i => (List.finRange 6).flatMap fun j =>
      if i ≠ j then [ax4 i j] else [])

lemma Ax_isAx (m : ℕ) (h : m ∈ Ax) : isAx m := by
  rw [Ax, List.mem_append, List.mem_append, List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨v, rfl⟩
  · obtain ⟨u, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨v, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨a, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨b, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨c, _, h⟩ := List.mem_flatMap.mp h
    split_ifs at h with hc
    · rw [List.mem_singleton] at h
      exact Or.inr (Or.inl ⟨u, v, a, b, c, hc, h⟩)
    · simp at h
  · obtain ⟨e, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
    exact Or.inr (Or.inr (Or.inl ⟨e, t, rfl⟩))
  · obtain ⟨i, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨j, _, h⟩ := List.mem_flatMap.mp h
    split_ifs at h with hc
    · rw [List.mem_singleton] at h
      exact Or.inr (Or.inr (Or.inr ⟨i, j, hc, h⟩))
    · simp at h

def P : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 8589934592, 4294967296, 16), (4294967296, 4429185024, 4362076160, 13),
   (4362076160, 8800455098368, 4402408587264, 21), (4402408587264, 141801029632, 4466833096704, 18),
   (4466833096704, 4466866651136, 4466849873920, 12), (4466849873920, 4466784862208, 4398114668544, 10),
   (4466784862208, 68722098176, 4398063550464, 9), (68722098176, 2623488, 68722099200, 5),
   (68722099200, 2621472, 68719477776, 2), (2621472, 0, 0, 24),
   (2623488, 0, 0, 24), (4466866651136, 4466841485312, 4466803736576, 11),
   (4466803736576, 69289902080, 4398319140864, 14), (4466841485312, 68729962496, 4398114668544, 10),
   (4398114668544, 0, 0, 24), (141801029632, 35321811042304, 17596548120576, 22),
   (8800455098368, 8796095119360, 8800456146944, 10), (8800456146944, 149537943453696, 70373040193536, 23),
   (149537943453696, 184717953466368, 17596548120576, 22), (17596548120576, 0, 0, 24),
   (184717953466368, 0, 0, 24), (8796095119360, 8796095250432, 8796095184896, 8),
   (8796095184896, 8796095185024, 8796095184960, 3), (8796095184960, 8796095119456, 8796093087760, 2),
   (8796095119456, 8933531975680, 68721573984, 18), (68721573984, 2097186, 68719476801, 0),
   (8796095185024, 9345848836096, 274880069760, 19), (274880069760, 2099328, 274877973504, 5),
   (8796095250432, 8796095250464, 8796095250448, 2), (8796095250448, 8796095119504, 8796095250496, 3),
   (8796095250496, 9345848836096, 274880135232, 19), (274880135232, 2236416, 274877911104, 6),
   (8796095119504, 8933531975680, 68721574032, 18), (68721574032, 2099328, 68719477776, 5),
   (2099328, 0, 0, 24), (8796095250464, 10995116277760, 1099513856032, 20),
   (1099513856032, 2236416, 1099513729056, 6), (1099513729056, 2097186, 1099511631873, 0),
   (2097186, 0, 0, 24), (2236416, 0, 0, 24),
   (4429185024, 554184998912, 275012124672, 19), (275012124672, 9071105146880, 4673058635776, 21),
   (4673058635776, 4673059160064, 4673058897920, 9), (4673058897920, 275045679104, 4398063550464, 12),
   (4398063550464, 0, 0, 24), (275045679104, 167903232, 275045744640, 8),
   (275045744640, 167774208, 274877973504, 5), (167774208, 0, 0, 24),
   (167903232, 0, 0, 24), (4673059160064, 274886819840, 4673062830080, 11),
   (4673062830080, 275548995584, 4398319140864, 14), (275548995584, 671096832, 275548999680, 6),
   (275548999680, 671088768, 274877911104, 3), (274886819840, 8945664, 274886836224, 7),
   (274886836224, 8913408, 274877923584, 4), (8913408, 0, 0, 24),
   (8945664, 0, 0, 24), (9071105146880, 8796227371008, 9071105212416, 8),
   (9071105212416, 275012190336, 8796227305536, 3), (8796227305536, 8796227240032, 8796093087760, 2),
   (8796093087760, 10995116277760, 1099511693328, 20), (8796227240032, 8933531975680, 68853694560, 18),
   (68853694560, 134217762, 68719476801, 0), (275012190336, 134219904, 274877973504, 5),
   (8796227371008, 8796227371040, 8796227371024, 2), (8796227371024, 8796227240080, 8796227371072, 3),
   (8796227371072, 9345848836096, 275012255808, 19), (275012255808, 134356992, 274877911104, 6),
   (8796227240080, 8933531975680, 68853694608, 18), (68853694608, 134219904, 68719477776, 5),
   (134219904, 0, 0, 24), (8933531975680, 0, 0, 24),
   (8796227371040, 10995116277760, 1099645976608, 20), (1099645976608, 134356992, 1099645849632, 6),
   (1099645849632, 134217762, 1099511631873, 0), (134217762, 0, 0, 24),
   (134356992, 0, 0, 24), (10995116277760, 0, 0, 24),
   (554184998912, 2753208254464, 1653696626688, 20), (1653696626688, 1653570797568, 1649405853696, 11),
   (1649405853696, 1100182716416, 550028443648, 14), (1100182716416, 671096832, 1100182720512, 6),
   (1100182720512, 671088642, 1099511631873, 0), (671096832, 0, 0, 24),
   (1653570797568, 1099522113536, 554051829760, 10), (1099522113536, 10493952, 1099522117632, 6),
   (1099522117632, 10485762, 1099511631873, 0), (10493952, 0, 0, 24),
   (2753208254464, 2886218022912, 622904475648, 18), (622904475648, 622778646528, 618613702656, 11),
   (618613702656, 69390565376, 550028443648, 14), (550028443648, 9345848836096, 4398319140864, 21),
   (4398319140864, 0, 0, 24), (9345848836096, 0, 0, 24),
   (69390565376, 671088768, 69390565440, 3), (69390565440, 671088642, 68719476801, 0),
   (671088642, 0, 0, 24), (671088768, 0, 0, 24),
   (622778646528, 68729962496, 554051829760, 10), (554051829760, 141287244169216, 70373040193536, 23),
   (70373040193536, 0, 0, 24), (141287244169216, 0, 0, 24),
   (68729962496, 10485888, 68729962560, 3), (68729962560, 10485762, 68719476801, 0),
   (10485762, 0, 0, 24), (10485888, 0, 0, 24),
   (8589934592, 2207613190144, 1108101562368, 20), (1108101562368, 36292473651200, 18700287606784, 22),
   (18700287606784, 18700321161216, 18700304384000, 12), (18700304384000, 1110249046016, 17593276563456, 15),
   (1110249046016, 10737549312, 1110249111552, 8), (1110249111552, 10737418272, 1099511693328, 2),
   (18700321161216, 1100082053120, 18700556042240, 14), (18700556042240, 1142461300736, 17609634349056, 17),
   (1142461300736, 42949681152, 1142461304832, 6), (1142461304832, 42949672962, 1099511631873, 0),
   (1100082053120, 570458112, 1100082069504, 7), (1100082069504, 570425352, 1099511644164, 1),
   (1099511644164, 0, 0, 24), (36292473651200, 36292473651202, 36292473651201, 0),
   (36292473651201, 1108101693441, 35192962088961, 8), (35192962088961, 35192962025473, 35184372155392, 5),
   (35184372155392, 35734127902720, 274877973504, 19), (35192962025473, 35321811042304, 77309413377, 18),
   (77309413377, 8589936768, 68719476801, 3), (1108101693441, 8590073856, 1099511631873, 6),
   (1099511631873, 0, 0, 24), (36292473651202, 1108101570562, 35192962027522, 6),
   (35192962027522, 35192962029568, 35192962024450, 5), (35192962024450, 35321811042304, 77309412354, 18),
   (77309412354, 8589934626, 68719477776, 2), (35321811042304, 0, 0, 24),
   (35192962029568, 35734127902720, 283467847680, 19), (283467847680, 8589936768, 274877911104, 3),
   (8589936768, 0, 0, 24), (1108101570562, 8590073856, 1108101627906, 8),
   (1108101627906, 8589934626, 1099511693328, 2), (1099511693328, 0, 0, 24),
   (8589934626, 0, 0, 24), (8590073856, 0, 0, 24),
   (2207613190144, 2757369004032, 2482491097088, 19), (2482491097088, 2482524651520, 2482507874304, 12),
   (2482507874304, 285615325184, 2200113774592, 15), (2200113774592, 37383395344384, 17593276563456, 22),
   (285615325184, 10737549312, 285615390720, 8), (285615390720, 10737420288, 274877973504, 5),
   (274877973504, 0, 0, 24), (10737549312, 0, 0, 24),
   (2482524651520, 275448332288, 2482759532544, 14), (2482759532544, 317827579904, 2216471560192, 17),
   (2216471560192, 37383395344384, 17609634349056, 22), (37383395344384, 0, 0, 24),
   (317827579904, 42949681152, 317827584000, 6), (317827584000, 42949673088, 274877911104, 3),
   (274877911104, 0, 0, 24), (42949681152, 0, 0, 24),
   (275448332288, 570458112, 275448348672, 7), (275448348672, 570425856, 274877923584, 4),
   (274877923584, 0, 0, 24), (570458112, 0, 0, 24),
   (2757369004032, 2886218022912, 627065225216, 18), (627065225216, 627098779648, 627082002432, 12),
   (627082002432, 79456894976, 550846332928, 15), (550846332928, 35734127902720, 17593276563456, 22),
   (17593276563456, 0, 0, 24), (79456894976, 10737420288, 79456896000, 5),
   (79456896000, 10737418272, 68719477776, 2), (68719477776, 0, 0, 24),
   (10737418272, 0, 0, 24), (10737420288, 0, 0, 24),
   (627098779648, 69289902080, 627333660672, 14), (627333660672, 111669149696, 567204118528, 17),
   (567204118528, 35734127902720, 17609634349056, 22), (17609634349056, 0, 0, 24),
   (35734127902720, 0, 0, 24), (111669149696, 42949673088, 111669149760, 3),
   (111669149760, 42949672962, 68719476801, 0), (68719476801, 0, 0, 24),
   (42949672962, 0, 0, 24), (42949673088, 0, 0, 24),
   (69289902080, 570425856, 69289902336, 4), (69289902336, 570425352, 68719476996, 1),
   (68719476996, 0, 0, 24), (570425352, 0, 0, 24),
   (570425856, 0, 0, 24), (2886218022912, 0, 0, 24)]

def chk : List (ℕ × ℕ × ℕ × ℕ) → Bool
  | [] => true
  | (m, a, b, v) :: rest =>
    chk rest && (Ax.contains m || (Nat.ble (v + 1) 24 && (rest.map Prod.fst).contains a &&
      (rest.map Prod.fst).contains b && a.testBit (2 * v + 1) && b.testBit (2 * v) &&
      Nat.beq m (rs a b v)))

lemma chk_sound : ∀ l, chk l = true → IsDerivation F (l.map (fun p => cl p.1)) := by
  intro l
  induction l with
  | nil => intro _; exact IsDerivation.nil
  | cons p rest ih =>
    obtain ⟨m, a, b, v⟩ := p
    intro h
    rw [chk, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hd := ih h1
    rw [List.map_cons]
    rcases h2 with h2 | h2
    · exact IsDerivation.ax hd ((mem_F _).mpr ⟨m, Ax_isAx m (by simpa using h2), rfl⟩)
    · simp only [Bool.and_eq_true] at h2
      obtain ⟨⟨⟨⟨⟨hv, ha⟩, hb⟩, hab⟩, hbb⟩, hm⟩ := h2
      have hv' : v < 24 := Nat.le_of_ble_eq_true hv
      obtain ⟨w, hw⟩ := idx_surj ⟨v, hv'⟩
      simp only at hw
      subst hw
      have hm' : m = rs a b (idx w) := Nat.eq_of_beq_eq_true hm
      have mem : ∀ x, (rest.map Prod.fst).contains x = true →
          cl x ∈ rest.map (fun p => cl p.1) := by
        intro x hx
        have hx' : x ∈ rest.map Prod.fst := by simpa only [List.contains_iff_mem] using hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx'
        exact List.mem_map.mpr ⟨q, hq, rfl⟩
      refine IsDerivation.res hd (mem a ha) (mem b hb) ⟨w, ?_, ?_, ?_⟩
      · rw [mem_cl, code_pos]; exact hab
      · rw [mem_cl, code_neg]; exact hbb
      · rw [hm', cl_rs a b w hab hbb]

lemma P_chk : chk P = true := by decide +kernel
lemma P_width : P.all (fun p => Nat.ble (pop p.1) 4) = true := by decide +kernel
lemma P_empty : (P.map Prod.fst).contains 0 = true := by decide +kernel

lemma cl_zero : cl 0 = ∅ := by
  ext x; simp [mem_cl]

lemma upper : ∃ π, IsRefutation F π ∧ ∀ D ∈ π, D.card ≤ 4 := by
  refine ⟨P.map (fun p => cl p.1), ⟨chk_sound P P_chk, ?_⟩, ?_⟩
  · have h0 : (0 : ℕ) ∈ P.map Prod.fst := by simpa only [List.contains_iff_mem] using P_empty
    obtain ⟨q, hq, hq0⟩ := List.mem_map.mp h0
    exact List.mem_map.mpr ⟨q, hq, by rw [hq0]; exact cl_zero⟩
  · intro D hD
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hD
    rw [card_cl]
    exact Nat.le_of_ble_eq_true (List.all_eq_true.mp P_width q hq)

lemma no_three : ¬ ∃ π, IsRefutation F π ∧ ∀ D ∈ π, D.card ≤ 3 := by
  rintro ⟨π, ⟨hd, he⟩, hw⟩
  obtain ⟨m, hm, h⟩ := lower π hd hw ∅ he
  have h1 : pop m = 0 := by rw [← card_cl, ← h]; rfl
  have h2 := List.all_eq_true.mp K_nonempty m hm
  rw [h1] at h2
  simp at h2

end PEqualNP.Outside.L_pcx_095

set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.L_pcx_095 : (∀ F1 : Set (PEqualNP.ProofComplexity.Clause ((Fin 6 × Fin 3) ⊕ Fin 6)), F1 = {C6 | ∃ v7 : Fin 6, C6 = Finset.univ.image (fun t8 : Fin 3 => ((Sum.inl (v7, t8) : (Fin 6 × Fin 3) ⊕ Fin 6), true))} ∪ {C9 | ∃ (u10 v11 : Fin 6) (f12 : Fin 3 → Bool), u10 ≠ v11 ∧ ¬ (u10 ≠ v11 ∧ u10.val / 3 = v11.val / 3) ∧ C9 = Finset.univ.image (fun t13 : Fin 3 => ((Sum.inl (if f12 t13 = true then v11 else u10, t13) : (Fin 6 × Fin 3) ⊕ Fin 6), true))} ∪ {C14 | ∃ (e15 : Fin 6) (t16 : Fin 3), C14 = {((Sum.inr e15 : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).1, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false), ((Sum.inl (((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e15).2, t16) : (Fin 6 × Fin 3) ⊕ Fin 6), false)}} ∪ {C17 | ∃ S18 : Finset (Fin 6), S18.card = 2 ∧ C17 = (Finset.univ.filter (fun e19 : Fin 6 => ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).1 ∉ S18 ∧ ((![(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : Fin 6 → Fin 6 × Fin 6) e19).2 ∉ S18)).image (fun e20 : Fin 6 => ((Sum.inr e20 : (Fin 6 × Fin 3) ⊕ Fin 6), true))} → (∃ π2, PEqualNP.ProofComplexity.IsRefutation F1 π2 ∧ ∀ D3 ∈ π2, D3.card ≤ 4) ∧ ¬ ∃ π4, PEqualNP.ProofComplexity.IsRefutation F1 π4 ∧ ∀ D5 ∈ π4, D5.card ≤ 3) := by
  intro F1 hF
  have h : F1 = PEqualNP.Outside.L_pcx_095.F := hF
  rw [h]
  exact ⟨PEqualNP.Outside.L_pcx_095.upper, PEqualNP.Outside.L_pcx_095.no_three⟩
