import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_145_aux
open PEqualNP.MetaComplexity
variable {n : ℕ}
def occ : DMFormula n → Fin n → ℕ
  | .lit i _ => fun k => if k = i then 1 else 0
  | .and a b => fun k => occ a k + occ b k
  | .or a b => fun k => occ a k + occ b k
theorem leaves_eq (φ : DMFormula n) : φ.leaves = ∑ k, occ φ k := by
  induction φ with
  | lit i b => simp [DMFormula.leaves, occ]
  | and a b iha ihb => simp [DMFormula.leaves, occ, iha, ihb, Finset.sum_add_distrib]
  | or a b iha ihb => simp [DMFormula.leaves, occ, iha, ihb, Finset.sum_add_distrib]

theorem eval_congr (φ : DMFormula n) (x y : Fin n → Bool)
    (h : ∀ k, 1 ≤ occ φ k → x k = y k) : φ.eval x = φ.eval y := by
  induction φ with
  | lit i b =>
    simp only [DMFormula.eval]
    rw [h i (by simp [occ])]
  | and a b iha ihb =>
    simp only [DMFormula.eval]
    rw [iha (fun k hk => h k (by simp [occ]; omega)), ihb (fun k hk => h k (by simp [occ]; omega))]
  | or a b iha ihb =>
    simp only [DMFormula.eval]
    rw [iha (fun k hk => h k (by simp [occ]; omega)), ihb (fun k hk => h k (by simp [occ]; omega))]
def rangeBlock (lo k n : ℕ) (h : lo+k ≤ n) : Finset (Fin n) :=
  Finset.univ.map ⟨fun i : Fin k => ⟨lo+i.val, by omega⟩, by intro i j hij; apply Fin.ext; exact Nat.add_left_cancel (congrArg Fin.val hij)⟩

theorem rangeBlock_card (lo k : ℕ) (h : lo+k ≤ n) : (rangeBlock lo k n h).card = k := by
  simp [rangeBlock]
theorem rangeBlock_bounds {lo k : ℕ} {h : lo+k ≤ n} {i : Fin n} (hi : i ∈ rangeBlock lo k n h) :
    lo ≤ i.val ∧ i.val < lo+k := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
  change lo ≤ lo+j.val ∧ lo+j.val < lo+k
  omega
theorem uniqueBlock (F : DMFormula n) (pos : ∀ i, 1 ≤ occ F i) (B : Finset (Fin n))
    (hlt : F.leaves < n+B.card) : ∃ i ∈ B, occ F i = 1 := by
  by_contra! hn
  have each (i : Fin n) : 1 + (if i ∈ B then 1 else 0) ≤ occ F i := by
    have := pos i
    split_ifs with hi
    · have := hn i hi
      omega
    · omega
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun i _ => each i)
  rw [← leaves_eq] at hh
  simp [Finset.sum_add_distrib] at hh
  omega
theorem middleSingles {ka kb kc kd : ℕ} (F : DMFormula (ka+kb+kc+kd))
    (pos : ∀ i, 1 ≤ occ F i) (hlt : F.leaves < ka+kb+kc+kd + min kb kc) :
    (∃ b, ka ≤ b.val ∧ b.val < ka+kb ∧ occ F b = 1) ∧
    (∃ c, ka+kb ≤ c.val ∧ c.val < ka+kb+kc ∧ occ F c = 1) := by
  constructor
  · let B := rangeBlock ka kb (ka+kb+kc+kd) (by omega)
    have hcard : B.card = kb := rangeBlock_card _ _ _
    obtain ⟨b,hb,ho⟩ := uniqueBlock F pos B (by omega)
    exact ⟨b,(rangeBlock_bounds hb).1,(rangeBlock_bounds hb).2,ho⟩
  · let B := rangeBlock (ka+kb) kc (ka+kb+kc+kd) (by omega)
    have hcard : B.card = kc := rangeBlock_card _ _ _
    obtain ⟨b,hb,ho⟩ := uniqueBlock F pos B (by omega)
    exact ⟨b,(rangeBlock_bounds hb).1,(rangeBlock_bounds hb).2,ho⟩
end PEqualNP.Outside.L_meta_145_aux

namespace PEqualNP.Outside.L_meta_145_aux
open MetaComplexity

def pin {n : ℕ} (b c : Fin n) (z : Fin n → Bool) (u v : Bool) (i : Fin n) : Bool :=
  if i=b then u else if i=c then v else z i

private def pack (f : Bool → Bool → Bool → Bool) : BitVec 8 :=
  BitVec.ofBoolListLE [f false false false, f false false true, f false true false, f false true true,
    f true false false, f true false true, f true true false, f true true true]

private theorem pack_and (f g : Bool → Bool → Bool → Bool) :
    pack (fun a b c => f a b c && g a b c) = pack f &&& pack g := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp only [pack, BitVec.getLsbD_and, BitVec.getLsbD_ofBoolListLE] <;> rfl

private theorem pack_or (f g : Bool → Bool → Bool → Bool) :
    pack (fun a b c => f a b c || g a b c) = pack f ||| pack g := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp only [pack, BitVec.getLsbD_or, BitVec.getLsbD_ofBoolListLE] <;> rfl

private def trace {n : ℕ} (F : DMFormula n) (b c : Fin n) (z₀ z₁ : Fin n → Bool) :=
  pack fun r u v => F.eval (pin b c (if r then z₁ else z₀) u v)

-- The four lists record the eight-bit truth tables obtained using zero or one
-- occurrence of each distinguished literal, with two possible background assignments.
private def bucket : ℕ → ℕ → List (BitVec 8)
  | 0, 0 => [0, 15, 240, 255]
  | 1, 0 => [0, 3, 12, 15, 48, 51, 63, 192, 204, 207, 240, 243, 252, 255]
  | 0, 1 => [0, 5, 10, 15, 80, 85, 95, 160, 170, 175, 240, 245, 250, 255]
  | _, _ => [0, 1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 31, 32, 34, 35, 42, 47, 48, 49, 50, 51, 53, 55, 58, 59, 63, 64, 68, 69, 76, 79, 80, 81, 83, 84, 85, 87, 92, 93, 95, 112, 115, 117, 119, 127, 128, 136, 138, 140, 143, 160, 162, 163, 168, 170, 171, 172, 174, 175, 176, 179, 186, 187, 191, 192, 196, 197, 200, 202, 204, 205, 206, 207, 208, 213, 220, 221, 223, 224, 234, 236, 238, 239, 240, 241, 242, 243, 244, 245, 247, 248, 250, 251, 252, 253, 254, 255]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
private theorem closed : ∀ i j k l : Fin 2, (i:ℕ)+k ≤ 1 → (j:ℕ)+l ≤ 1 →
    ∀ v ∈ bucket i j, ∀ w ∈ bucket k l,
      v &&& w ∈ bucket ((i:ℕ)+k) ((j:ℕ)+l) ∧
      v ||| w ∈ bucket ((i:ℕ)+k) ((j:ℕ)+l) := by decide


private theorem combine {i j k l : ℕ} {v w : BitVec 8} (h₁ : i+k ≤ 1) (h₂ : j+l ≤ 1)
    (hv : v ∈ bucket i j) (hw : w ∈ bucket k l) :
    v &&& w ∈ bucket (i+k) (j+l) ∧ v ||| w ∈ bucket (i+k) (j+l) :=
  closed ⟨i,by omega⟩ ⟨j,by omega⟩ ⟨k,by omega⟩ ⟨l,by omega⟩ h₁ h₂ v hv w hw

private theorem trace_mem {n : ℕ} (F : DMFormula n) (b c : Fin n) (z₀ z₁ : Fin n → Bool)
    (hne : b ≠ c) (hb : occ F b ≤ 1) (hc : occ F c ≤ 1) :
    trace F b c z₀ z₁ ∈ bucket (occ F b) (occ F c) := by
  induction F with
  | lit i sign =>
    by_cases hi : i = b
    · subst i
      cases sign <;> simp [occ, trace, pin, DMFormula.eval, Ne.symm hne] <;> decide
    · by_cases hj : i = c
      · subst i
        cases sign <;> simp [occ,trace,pin,DMFormula.eval,hne,hi] <;> decide
      · have H : ∀ s u v : Bool, pack (fun r _ _ => if s then (if r then v else u)
            else !(if r then v else u)) ∈ bucket 0 0 := by decide
        have E : (fun r u v => (DMFormula.lit i sign).eval
              (pin b c (if r then z₁ else z₀) u v)) =
            (fun (r u v : Bool) => if sign then (if r then z₁ i else z₀ i)
              else !(if r then z₁ i else z₀ i)) := by
          funext r u v
          cases r <;> simp [DMFormula.eval,pin,hi,hj]
        simpa only [trace, E, occ, ite_eq_right (Ne.symm hi), ite_eq_right (Ne.symm hj)] using
          H sign (z₀ i) (z₁ i)
  | and A B ihA ihB =>
    simp only [occ] at hb hc ⊢
    have HA := ihA (by omega) (by omega)
    have HB := ihB (by omega) (by omega)
    have eq : trace (.and A B) b c z₀ z₁ = trace A b c z₀ z₁ &&& trace B b c z₀ z₁ :=
      pack_and _ _
    rw [eq]
    exact (combine hb hc HA HB).1
  | or A B ihA ihB =>
    simp only [occ] at hb hc ⊢
    have HA := ihA (by omega) (by omega)
    have HB := ihB (by omega) (by omega)
    have eq : trace (.or A B) b c z₀ z₁ = trace A b c z₀ z₁ ||| trace B b c z₀ z₁ :=
      pack_or _ _
    rw [eq]
    exact (combine hb hc HA HB).2

theorem no_switch {n : ℕ} (F : DMFormula n) (b c : Fin n) (z₀ z₁ : Fin n → Bool)
    (hne : b ≠ c) (hb : occ F b ≤ 1) (hc : occ F c ≤ 1)
    (h₀ : ∀ u v : Bool, F.eval (pin b c z₀ u v) = (u && v))
    (h₁ : ∀ u v : Bool, F.eval (pin b c z₁ u v) = (u || v)) : False := by
  have ht := trace_mem F b c z₀ z₁ hne hb hc
  have table : trace F b c z₀ z₁ = 232 := by
    change BitVec.ofBoolListLE [
      F.eval (pin b c z₀ false false),
      F.eval (pin b c z₀ false true),
      F.eval (pin b c z₀ true false),
      F.eval (pin b c z₀ true true),
      F.eval (pin b c z₁ false false),
      F.eval (pin b c z₁ false true),
      F.eval (pin b c z₁ true false),
      F.eval (pin b c z₁ true true)] = 232
    rw [h₀,h₀,h₀,h₀,h₁,h₁,h₁,h₁]
    rfl
  rw [table] at ht
  have absent : ∀ i j : Fin 2, (232 : BitVec 8) ∉ bucket i j := by decide
  exact absent ⟨_,by omega⟩ ⟨_,by omega⟩ ht

end PEqualNP.Outside.L_meta_145_aux
namespace PEqualNP.Outside.L_meta_145_aux

def pathFun (a b c d : ℕ) (x : Fin (a+b+c+d) → Bool) := decide
  (((∃ i, i.val < a ∧ x i = true) ∧ (∃ i, a ≤ i.val ∧ i.val < a+b ∧ x i = true)) ∨
   ((∃ i, a ≤ i.val ∧ i.val < a+b ∧ x i = true) ∧ (∃ i, a+b ≤ i.val ∧ i.val < a+b+c ∧ x i = true)) ∨
   ((∃ i, a+b ≤ i.val ∧ i.val < a+b+c ∧ x i = true) ∧ (∃ i, a+b+c ≤ i.val ∧ x i = true)))

private def frame {n : ℕ} (A B C D : Fin n) (w u v t : Bool) (i : Fin n) : Bool :=
  (decide (i=B) && u) || (decide (i=C) && v) || (decide (i=A) && w) || (decide (i=D) && t)

private theorem hitFrame {n} (P : Fin n → Prop) (A B C D : Fin n) (w u v t : Bool) :
    (∃ i, P i ∧ frame A B C D w u v t i = true) ↔
    (P B ∧ u = true) ∨ (P C ∧ v = true) ∨ (P A ∧ w = true) ∨ (P D ∧ t = true) := by
  simp only [frame,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  aesop

private theorem path_frame {a b c d : ℕ} (A B C D : Fin (a+b+c+d))
    (hA : A.val < a) (hB : a ≤ B.val ∧ B.val < a+b)
    (hC : a+b ≤ C.val ∧ C.val < a+b+c) (hD : a+b+c ≤ D.val)
    (w u v t : Bool) :
    pathFun a b c d (frame A B C D w u v t) = ((w && u) || (u && v) || (v && t)) := by
  let X := frame A B C D w u v t
  have Aeq : (∃ i, i.val < a ∧ X i = true) ↔ w = true := by
    rw [hitFrame (fun i => i.val < a)]; simp [hA,show ¬B.val<a by omega,show ¬C.val<a by omega,show ¬D.val<a by omega]
  have Beq : (∃ i, a ≤ i.val ∧ i.val < a+b ∧ X i = true) ↔ u = true := by
    simp only [←and_assoc]
    rw [hitFrame (fun i => a ≤ i.val ∧ i.val < a+b)]
    simp [hB,show ¬a≤A.val by omega,show ¬C.val<a+b by omega,show ¬D.val<a+b by omega]
  have Ceq : (∃ i, a+b ≤ i.val ∧ i.val < a+b+c ∧ X i = true) ↔ v = true := by
    simp only [←and_assoc]
    rw [hitFrame (fun i => a+b ≤ i.val ∧ i.val < a+b+c)]
    simp [hC,show ¬a+b≤A.val by omega,show ¬a+b≤B.val by omega,show ¬D.val<a+b+c by omega]
  have Deq : (∃ i, a+b+c ≤ i.val ∧ X i = true) ↔ t = true := by
    rw [hitFrame (fun i => a+b+c ≤ i.val)]
    simp [hD,show ¬a+b+c≤A.val by omega,show ¬a+b+c≤B.val by omega,show ¬a+b+c≤C.val by omega]
  unfold pathFun
  dsimp only [X] at Aeq Beq Ceq Deq
  simp only [Aeq,Beq,Ceq,Deq]
  cases w <;> cases u <;> cases v <;> cases t <;> decide

theorem path_switch {a b c d : ℕ} (ha : 1≤a) (hd : 1≤d)
    (B C : Fin (a+b+c+d)) (hB : a ≤ B.val ∧ B.val < a+b)
    (hC : a+b ≤ C.val ∧ C.val < a+b+c) :
    ∃ z₀ z₁ : Fin (a+b+c+d) → Bool,
      (∀ u v : Bool, pathFun a b c d (fun i => if i=B then u else if i=C then v else z₀ i) = (u && v)) ∧
      (∀ u v : Bool, pathFun a b c d (fun i => if i=B then u else if i=C then v else z₁ i) = (u || v)) := by
  let A : Fin (a+b+c+d) := ⟨0,by omega⟩
  let D : Fin (a+b+c+d) := ⟨a+b+c,by omega⟩
  have hA : A.val < a := by dsimp [A]; omega
  have hD : a+b+c ≤ D.val := by rfl
  have hBC : B ≠ C := by intro e; have := congrArg Fin.val e; omega
  have hBA : B ≠ A := by intro e; have := congrArg Fin.val e; omega
  have hBD : B ≠ D := by intro e; have := congrArg Fin.val e; omega
  have hCA : C ≠ A := by intro e; have := congrArg Fin.val e; omega
  have hCD : C ≠ D := by intro e; have := congrArg Fin.val e; omega
  have eqf (k u v : Bool) :
      (fun i => if i=B then u else if i=C then v else frame A B C D k false false k i) =
      frame A B C D k u v k := by
    funext i
    by_cases h₁ : i = B
    · subst i; simp [frame,hBC,hBA,hBD]
    by_cases h₂ : i = C
    · subst i; simp [frame,hBC.symm,hCA,hCD]
    · simp [h₁,h₂,frame]
  refine ⟨frame A B C D false false false false, frame A B C D true false false true,?_,?_⟩
  · intro u v; rw [eqf, path_frame A B C D hA hB hC hD]; simp
  · intro u v; rw [eqf, path_frame A B C D hA hB hC hD]; cases u <;> cases v <;> rfl

theorem path_sensitive {a b c d : ℕ} (ha : 1≤a) (hb : 1≤b) (hc : 1≤c) (hd : 1≤d)
    (i : Fin (a+b+c+d)) :
    ∃ x y : Fin (a+b+c+d) → Bool, (∀ j, j ≠ i → x j = y j) ∧
      pathFun a b c d x ≠ pathFun a b c d y := by
  let A : Fin (a+b+c+d) := ⟨0,by omega⟩
  let B : Fin (a+b+c+d) := ⟨a,by omega⟩
  let C : Fin (a+b+c+d) := ⟨a+b,by omega⟩
  let D : Fin (a+b+c+d) := ⟨a+b+c,by omega⟩
  have hA : A.val < a := by dsimp [A]; omega
  have hB : a ≤ B.val ∧ B.val < a+b := by dsimp [B]; omega
  have hC : a+b ≤ C.val ∧ C.val < a+b+c := by dsimp [C]; omega
  have hD : a+b+c ≤ D.val := by rfl
  by_cases h₁ : i.val < a
  · refine ⟨frame i B C D false true false false,frame i B C D true true false false,?_,?_⟩
    · intro j hj; simp [frame,hj]
    · simp [path_frame i B C D h₁ hB hC hD]
  by_cases h₂ : i.val < a+b
  · have hh : a ≤ i.val ∧ i.val < a+b := by omega
    refine ⟨frame A i C D true false false false,frame A i C D true true false false,?_,?_⟩
    · intro j hj; simp [frame,hj]
    · simp [path_frame A i C D hA hh hC hD]
  by_cases h₃ : i.val < a+b+c
  · have hh : a+b ≤ i.val ∧ i.val < a+b+c := by omega
    refine ⟨frame A B i D false false false true,frame A B i D false false true true,?_,?_⟩
    · intro j hj; simp [frame,hj]
    · simp [path_frame A B i D hA hB hh hD]
  · have hh : a+b+c ≤ i.val := by omega
    refine ⟨frame A B C i false false true false,frame A B C i false false true true,?_,?_⟩
    · intro j hj; simp [frame,hj]
    · simp [path_frame A B C i hA hB hC hh]

end PEqualNP.Outside.L_meta_145_aux

namespace PEqualNP.Outside.L_meta_145
open PEqualNP.MetaComplexity

private lemma block {n : ℕ} (off k : ℕ) (hk : 1 ≤ k) (hn : off+k ≤ n) :
    ∃ F : DMFormula n, F.leaves = k ∧ ∀ x,
      F.eval x = true ↔ ∃ i : Fin n, off ≤ i.val ∧ i.val < off+k ∧ x i = true := by
  induction k with
  | zero => omega
  | succ k ih =>
    let i : Fin n := ⟨off+k,by omega⟩
    by_cases hz : k = 0
    · subst k
      refine ⟨.lit i true,rfl,fun x => ?_⟩
      change x i = true ↔ _
      constructor
      · exact fun h => ⟨i,by simp [i], by simp [i],h⟩
      · rintro ⟨j,hlo,hhi,hj⟩
        suffices j = i by simpa [← this] using hj
        apply Fin.ext
        change j.val = off+0
        omega
    · obtain ⟨F,hF,he⟩ := ih (by omega) (by omega)
      refine ⟨.or F (.lit i true), by simp [DMFormula.leaves,hF],fun x => ?_⟩
      simp only [DMFormula.eval, ite_true, Bool.or_eq_true, he]
      constructor
      · rintro (⟨j,hl,hu,hx⟩|hx)
        · exact ⟨j,hl,by omega,hx⟩
        · exact ⟨i,by simp [i],by simp [i],hx⟩
      · rintro ⟨j,hl,hu,hx⟩
        by_cases h : j.val < off+k
        · exact Or.inl ⟨j,hl,h,hx⟩
        · have e : j = i := Fin.ext (show j.val = off+k by omega)
          exact Or.inr (e ▸ hx)

private lemma logicB (a b c d : Prop) : ((a ∧ b) ∨ c ∧ (b ∨ d)) ↔ (a ∧ b) ∨ (b ∧ c) ∨ (c ∧ d) := by tauto

private lemma logicC (a b c d : Prop) : ((b ∧ (a ∨ c)) ∨ c ∧ d) ↔ (a ∧ b) ∨ (b ∧ c) ∨ (c ∧ d) := by tauto

theorem upper : ∀ (ka kb kc kd s : ℕ), 1 ≤ ka → 1 ≤ kb → 1 ≤ kc → 1 ≤ kd → ka + kb + kc + kd + min kb kc ≤ s → PEqualNP.MetaComplexity.HasLeafSize (ka + kb + kc + kd) (fun x : Fin (ka + kb + kc + kd) → Bool => decide (((∃ i : Fin (ka + kb + kc + kd), i.val < ka ∧ x i = true) ∧ (∃ i : Fin (ka + kb + kc + kd), ka ≤ i.val ∧ i.val < ka + kb ∧ x i = true)) ∨ ((∃ i : Fin (ka + kb + kc + kd), ka ≤ i.val ∧ i.val < ka + kb ∧ x i = true) ∧ (∃ i : Fin (ka + kb + kc + kd), ka + kb ≤ i.val ∧ i.val < ka + kb + kc ∧ x i = true)) ∨ ((∃ i : Fin (ka + kb + kc + kd), ka + kb ≤ i.val ∧ i.val < ka + kb + kc ∧ x i = true) ∧ (∃ i : Fin (ka + kb + kc + kd), ka + kb + kc ≤ i.val ∧ x i = true)))) s := by
  intro a b c d s ha hb hc hd hs
  let n := a+b+c+d
  obtain ⟨A,hA,eA⟩ := block (n:=n) 0 a ha (by dsimp [n]; omega)
  obtain ⟨B,hB,eB⟩ := block (n:=n) a b hb (by dsimp [n]; omega)
  obtain ⟨C,hC,eC⟩ := block (n:=n) (a+b) c hc (by dsimp [n]; omega)
  obtain ⟨D,hD,eD⟩ := block (n:=n) (a+b+c) d hd (by dsimp [n]; omega)
  have ea (x) : A.eval x = true ↔ ∃ i : Fin n, i.val < a ∧ x i = true := by simpa using eA x
  have ed (x) : D.eval x = true ↔ ∃ i : Fin n, a+b+c ≤ i.val ∧ x i = true := by
    simpa only [← show n = a+b+c+d from rfl, Fin.isLt, true_and] using eD x
  by_cases h : b ≤ c
  · refine ⟨.or (.and A B) (.and C (.or B D)), ?_, fun x => ?_⟩
    · simp only [DMFormula.leaves,hA,hB,hC,hD]
      omega
    · apply Bool.eq_iff_iff.mpr
      simp only [DMFormula.eval,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,ea,eB,eC,ed]
      exact logicB _ _ _ _
  · refine ⟨.or (.and B (.or A C)) (.and C D), ?_, fun x => ?_⟩
    · simp only [DMFormula.leaves,hA,hB,hC,hD]
      omega
    · apply Bool.eq_iff_iff.mpr
      simp only [DMFormula.eval,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,ea,eB,eC,ed]
      exact logicC _ _ _ _

end PEqualNP.Outside.L_meta_145
open PEqualNP.Outside.L_meta_145_aux
theorem PEqualNP.Outside.L_meta_145 : ∀ (ka kb kc kd s : ℕ), 1 ≤ ka → 1 ≤ kb → 1 ≤ kc → 1 ≤ kd → (PEqualNP.MetaComplexity.HasLeafSize (ka + kb + kc + kd) (fun x : Fin (ka + kb + kc + kd) → Bool => decide (((∃ i : Fin (ka + kb + kc + kd), i.val < ka ∧ x i = true) ∧ (∃ i : Fin (ka + kb + kc + kd), ka ≤ i.val ∧ i.val < ka + kb ∧ x i = true)) ∨ ((∃ i : Fin (ka + kb + kc + kd), ka ≤ i.val ∧ i.val < ka + kb ∧ x i = true) ∧ (∃ i : Fin (ka + kb + kc + kd), ka + kb ≤ i.val ∧ i.val < ka + kb + kc ∧ x i = true)) ∨ ((∃ i : Fin (ka + kb + kc + kd), ka + kb ≤ i.val ∧ i.val < ka + kb + kc ∧ x i = true) ∧ (∃ i : Fin (ka + kb + kc + kd), ka + kb + kc ≤ i.val ∧ x i = true)))) s ↔ ka + kb + kc + kd + min kb kc ≤ s) := by
  intro a b c d s ha hb hc hd
  constructor
  · rintro ⟨F,hs,he⟩
    change ∀ x, F.eval x = pathFun a b c d x at he
    by_contra! hlt
    have hp (i) : 1 ≤ occ F i := by
      by_contra! hz
      obtain ⟨x,y,hxy,hne⟩ := path_sensitive ha hb hc hd i
      apply hne
      rw [← he, ← he]
      apply eval_congr
      intro j hj
      exact hxy j (fun h => by subst j; omega)
    obtain ⟨⟨B,hB₁,hB₂,hBo⟩,⟨C,hC₁,hC₂,hCo⟩⟩ := middleSingles F hp (by omega)
    obtain ⟨z₀,z₁,h₀,h₁⟩ := path_switch ha hd B C ⟨hB₁,hB₂⟩ ⟨hC₁,hC₂⟩
    apply no_switch F B C z₀ z₁ (fun h => by subst C; omega) hBo.le hCo.le
    · intro u v; rw [he]; exact h₀ u v
    · intro u v; rw [he]; exact h₁ u v
  · exact PEqualNP.Outside.L_meta_145.upper a b c d s ha hb hc hd
