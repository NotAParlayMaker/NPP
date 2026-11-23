import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_264_counts
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
end PEqualNP.Outside.L_meta_264_counts

namespace PEqualNP.Outside.L_meta_264_counts
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

end PEqualNP.Outside.L_meta_264_counts
namespace PEqualNP.Outside.L_meta_264
open MetaComplexity PEqualNP.Outside.L_meta_264_counts

def target264 (x : Fin 7 → Bool) := x 0 && x 1 || x 1 && x 2 || x 0 && x 2 ||
  x 0 && x 3 || x 1 && x 4 || x 2 && x 5 || x 5 && x 6

private def asgn (m : ℕ) (i : Fin 7) := m.testBit i.val
private def conflict : Fin 4 → Fin 7 × Fin 7 × ℕ := ![(0,1,4),(0,2,2),(1,2,1),(2,5,65)]

theorem quotas264 (F : DMFormula 7) (he : ∀ x, F.eval x = target264 x) (hl : F.leaves ≤ 9) :
    occ F = ![2,1,2,1,1,1,1] ∨ occ F = ![1,2,2,1,1,1,1] := by
  have pos (i : Fin 7) : 1 ≤ occ F i := by
    have wit : ∀ j : Fin 7, ∃ w : Fin 7, target264 (fun k => decide (k=w ∨ k=j)) ≠
        target264 (fun k => decide (k=w)) := by decide
    obtain ⟨w,hw⟩ := wit i
    by_contra! h
    apply hw
    rw [← he, ← he]
    apply eval_congr
    intro k hk
    have ne : k ≠ i := by rintro rfl; omega
    simp [ne]
  have frame : ∀ i : Fin 4, ∀ a b : Bool,
      let t := conflict i
      target264 (pin t.1 t.2.1 (asgn 0) a b) = (a && b) ∧
      target264 (pin t.1 t.2.1 (asgn t.2.2) a b) = (a || b) := by decide
  have rep (i : Fin 4) : 2 ≤ occ F (conflict i).1 ∨ 2 ≤ occ F (conflict i).2.1 := by
    by_contra! h
    apply no_switch F _ _ (asgn 0) (asgn (conflict i).2.2)
      ((by decide : ∀ j : Fin 4, (conflict j).1 ≠ (conflict j).2.1) i) (by omega) (by omega)
    · intro a b; rw [he]; exact (frame i a b).1
    · intro a b; rw [he]; exact (frame i a b).2
  have h01 : 2 ≤ occ F 0 ∨ 2 ≤ occ F 1 := rep 0
  have h02 : 2 ≤ occ F 0 ∨ 2 ≤ occ F 2 := rep 1
  have h12 : 2 ≤ occ F 1 ∨ 2 ≤ occ F 2 := rep 2
  have h25 : 2 ≤ occ F 2 ∨ 2 ≤ occ F 5 := rep 3
  have p0 := pos 0
  have p1 := pos 1
  have p2 := pos 2
  have p3 := pos 3
  have p4 := pos 4
  have p5 := pos 5
  have p6 := pos 6
  rw [leaves_eq, Fin.sum_univ_seven] at hl
  by_cases h : 2 ≤ occ F 0
  · left; funext i; fin_cases i <;> simp <;> omega
  · right; funext i; fin_cases i <;> simp <;> omega

end PEqualNP.Outside.L_meta_264
namespace PEqualNP.Outside.L_meta_264_aux
open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_264_counts (occ)

def target (x : Fin 7 → Bool) := x 0 && x 1 || x 1 && x 2 || x 0 && x 2 ||
  x 0 && x 3 || x 1 && x 4 || x 2 && x 5 || x 5 && x 6
def allowed (d i : Fin 7) (sign : Bool) : Prop := sign = true ∨ i=d ∨ i=2
def admiss (d : Fin 7) : DMFormula 7 → Prop
  | .lit i sign => allowed d i sign
  | .and A B | .or A B => admiss d A ∧ admiss d B

private def literals {n} (i : Fin n) (sign : Bool) : DMFormula n → ℕ
  | .lit j s => if i=j ∧ sign=s then 1 else 0
  | .and A B | .or A B => literals i sign A + literals i sign B

private theorem occ_split {n} (F : DMFormula n) (i : Fin n) :
    occ F i = literals i true F + literals i false F := by
  induction F with
  | lit j s => cases s <;> by_cases h : i=j <;> simp [h,occ,literals]
  | and A B ha hb => simp only [occ,literals,ha,hb]; omega
  | or A B ha hb => simp only [occ,literals,ha,hb]; omega

private theorem antitone_at {n} (F : DMFormula n) (i : Fin n) (h : literals i true F = 0)
    (x : Fin n → Bool) : F.eval (Function.update x i true) ≤ F.eval (Function.update x i false) := by
  induction F with
  | lit j s =>
    by_cases eq : j=i
    · subst j; cases s <;> simp_all [literals,DMFormula.eval]
    · simp [DMFormula.eval,Function.update_of_ne eq]
  | and A B ha hb =>
    simp only [literals,Nat.add_eq_zero_iff] at h
    exact (show ∀ a b c d : Bool, a ≤ b → c ≤ d → (a && c) ≤ (b && d) by decide) _ _ _ _ (ha h.1) (hb h.2)
  | or A B ha hb =>
    simp only [literals,Nat.add_eq_zero_iff] at h
    exact (show ∀ a b c d : Bool, a ≤ b → c ≤ d → (a || c) ≤ (b || d) by decide) _ _ _ _ (ha h.1) (hb h.2)

private theorem needed : ∀ i : Fin 7, ∃ x : Fin 7 → Bool,
    target (Function.update x i false) = false ∧ target (Function.update x i true) = true := by decide

private theorem positive_needed (F : DMFormula 7) (he : ∀ x, F.eval x = target x) (i : Fin 7) :
    1 ≤ literals i true F := by
  by_contra! hn
  obtain ⟨x,hf,ht⟩ := needed i
  have dis := antitone_at F i (by omega) x
  rw [he,he,ht,hf] at dis
  exact (by decide : ¬true ≤ false) dis

private theorem admiss_of_neg (F : DMFormula 7) (d : Fin 7)
    (h : ∀ i, i ≠ d → i ≠ 2 → literals i false F = 0) : admiss d F := by
  induction F with
  | lit i s =>
    by_cases hd : i=d
    · exact Or.inr (Or.inl hd)
    by_cases h₂ : i=2
    · exact Or.inr (Or.inr h₂)
    have hn := h i hd h₂
    cases s <;> simp_all [literals,admiss,allowed]
  | and A B ha hb =>
    simp only [literals,Nat.add_eq_zero_iff] at h
    exact ⟨ha (fun i hd h₂ => (h i hd h₂).1),hb (fun i hd h₂ => (h i hd h₂).2)⟩
  | or A B ha hb =>
    simp only [literals,Nat.add_eq_zero_iff] at h
    exact ⟨ha (fun i hd h₂ => (h i hd h₂).1),hb (fun i hd h₂ => (h i hd h₂).2)⟩

theorem admiss_of_counts (F : DMFormula 7) (d : Fin 7)
    (cnt : ∀ i, i ≠ d → i ≠ 2 → occ F i ≤ 1)
    (he : ∀ x, F.eval x = target x) : admiss d F := by
  apply admiss_of_neg
  intro i hd h₂
  have hl := cnt i hd h₂
  have hp := positive_needed F he i
  rw [occ_split] at hl
  omega

end PEqualNP.Outside.L_meta_264_aux

namespace PEqualNP.Outside.L_meta_264_aux
open MetaComplexity

-- Interchanging vertices 0 and 1 also interchanges their pendant vertices 3 and 4.
private def coord (d i : Fin 7) : Fin 7 :=
  if d=0 then i else (![1,0,2,4,3,5,6] : Fin 7 → Fin 7) i

private def positive (d r : Fin 7) (i : Fin 7) := (![3,6,5,9,18,36,96] : Fin 7 → ℕ) r |>.testBit (coord d i).val
private def negative (d : Fin 7) (c : Fin 4) (i : Fin 7) := (![42,49,56,92] : Fin 4 → ℕ) c |>.testBit (coord d i).val

-- Each table row packs the 16 column-subset weights, with four bits per weight.
private def packed : Array ℕ := #[
  0,
  2382722035308634384,
  2387225703387042064,
  3544668469064708384,
  2454780728589750544,
  3679778519485854224,
  3689067334897570064,
  5994945529038123552,
  2454780728874967312,
  3679778519502631440,
  4842006432262009376,
  5994945529323340320,
  3679778519502631440,
  4904776310130295568,
  6067004222604456480,
  7219943319682564896,
  2387225703656530192,
  3544668469065756960,
  3544668469065756960,
  4702111234474983728,
  4842006432246280736,
  5994945529307611680,
  5999449197386019360,
  7152388294448398896,
  4842006428236530208,
  5994945525297857056,
  5999449197940724272,
  7152388295002051120,
  6067004223159161632,
  7219943320220488480,
  7224446988299948848,
  8377386085361275696,
  2459565871913308432,
  4842287907221942816,
  3689348809874280720,
  5999730672361681440,
  3689348809874280720,
  6067285697564389920,
  4919131747835253008,
  7225009941975806496,
  4914346600788275744,
  6139344391415939872,
  6144129538749248032,
  7297068635827356448,
  6139343291619095072,
  7364341082246759200,
  7369126229580067360,
  8522065326658175776,
  4846791575569838368,
  6004234340979065392,
  6004234271990100256,
  7161677037399327280,
  6076574513530810912,
  7229513610593190448,
  7234017209951072800,
  8386956307013452336,
  7301571200638210608,
  8454511397211165488,
  8459015000865067568,
  9611954097926394672,
  8526568995275625264,
  9679508092336952112,
  9684011691695887152,
  10836933196571169584,
  2459565871913308432,
  4842287902926975520,
  4846791575300350240,
  6004234340978016816,
  4914346600503058976,
  6139344391399162656,
  6148633206810878496,
  8454511400951431984,
  4914345496981680672,
  6139343287609344800,
  7301571200368722480,
  8454510297430053680,
  6139344391415939872,
  7364342182043604000,
  8526570094517764912,
  9679509191595873328,
  4846790403043766560,
  6004234267964621360,
  6004234340979065136,
  7161677106388292160,
  7301571131633517104,
  8454511328206476080,
  8459015069299327536,
  9611954166361707328,
  7301570028112138800,
  8454492632499049264,
  8459013966047437376,
  9611953063108764480,
  8526568922546398000,
  9679509119119352880,
  9684012860213257024,
  10836951957274584128,
  3689347706354016544,
  6072069741662650928,
  4919130644314988832,
  7229512506802389552,
  4919131743826616864,
  7297068631516726064,
  6148914681787589152,
  8454792875928142640,
  6144128435228983856,
  7369126225856647984,
  7373911373189956144,
  8526850470268064560,
  7369126225571431216,
  8594124016199095344,
  8598909163532403504,
  9751848260610511920,
  6076573410010546480,
  7234016175419773504,
  7234016106430808368,
  8391458871840035392,
  7306357447483146800,
  8459296544545526592,
  8463800143903408688,
  9616739240965788480,
  8531353035078918720,
  9684293231651873600,
  9688796835305775680,
  10841735932367102784,
  9756351929227961152,
  10909291026289288256,
  10913794625648223040,
  12066716130523505728]
private def wt (a : BitVec 7) (b : BitVec 4) :=
  (packed[a.toNat]! >>> (4*b.toNat)) &&& 15

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem hsplit : ∀ a b : BitVec 7, a &&& b = 0 → ∀ c : BitVec 4,
    wt (a ||| b) c ≤ wt a c + wt b c := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem vsplit : ∀ a b : BitVec 4, a &&& b = 0 → ∀ r : BitVec 7,
    wt r (a ||| b) ≤ wt r a + wt r b := by decide +kernel

private def keep {w : ℕ} (a : BitVec w) (p : Fin w → Bool) : BitVec w :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin w => a.getLsbD i.val && p i)).cast (by simp)

private theorem keep_bit {w} (a : BitVec w) (p : Fin w → Bool) (i : Fin w) :
    (keep a p).getLsbD i = (a.getLsbD i && p i) := by
  simp only [keep,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt]

private theorem split_keep {w} (a : BitVec w) (p : Fin w → Bool) :
    keep a p ||| keep a (fun i => !p i) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin w := ⟨j,hj⟩
  change (keep a p ||| keep a (fun i => !p i)).getLsbD i = a.getLsbD i
  rw [BitVec.getLsbD_or,keep_bit,keep_bit]
  cases a.getLsbD i <;> cases p i <;> rfl

private theorem disjoint_keep {w} (a : BitVec w) (p : Fin w → Bool) :
    keep a p &&& keep a (fun i => !p i) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin w := ⟨j,hj⟩
  change (keep a p &&& keep a (fun i => !p i)).getLsbD i = (0 : BitVec w).getLsbD i
  rw [BitVec.getLsbD_and,keep_bit,keep_bit]
  cases a.getLsbD i <;> cases p i <;> simp

private def separates (d : Fin 7) (F : DMFormula 7) (a : BitVec 7) (b : BitVec 4) : Prop :=
  (∀ i : Fin 7, a.getLsbD i = true → F.eval (positive d i) = true) ∧
  (∀ j : Fin 4, b.getLsbD j = true → F.eval (negative d j) = false)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem leaf_bound : ∀ (d i : Fin 7) (s : Bool), (d=0 ∨ d=1) → allowed d i s →
    ∀ a b, separates d (.lit i s) a b → wt a b ≤ 1 := by
  unfold allowed separates; decide +kernel


private theorem formula_bound (d : Fin 7) (hd : d=0 ∨ d=1) (F : DMFormula 7)
    (h : admiss d F) (a : BitVec 7) (b : BitVec 4) (hs : separates d F a b) :
    wt a b ≤ F.leaves := by
  induction F generalizing a b with
  | lit i s => exact leaf_bound d i s hd h a b hs
  | and A B iA iB =>
    let p (i : Fin 4) := A.eval (negative d i)
    have ha : separates d A a (keep b (fun i => !p i)) := by
      constructor
      · intro i hi
        exact (Bool.and_eq_true_iff.mp (hs.1 i hi)).1
      · intro i hi
        rw [keep_bit] at hi
        simpa [p] using (Bool.and_eq_true_iff.mp hi).2
    have hb : separates d B a (keep b p) := by
      constructor
      · intro i hi
        exact (Bool.and_eq_true_iff.mp (hs.1 i hi)).2
      · intro i hi
        rw [keep_bit] at hi
        obtain ⟨hbit,hp⟩ := Bool.and_eq_true_iff.mp hi
        have hh := hs.2 i hbit
        change (p i && B.eval (negative d i)) = false at hh
        simpa [hp] using hh
    have k := vsplit (keep b p) (keep b (fun i => !p i)) (disjoint_keep ..) a
    rw [split_keep] at k
    have l := iA h.1 _ _ ha
    have r := iB h.2 _ _ hb
    change wt a b ≤ A.leaves+B.leaves
    omega
  | or A B iA iB =>
    let p (i : Fin 7) := A.eval (positive d i)
    have ha : separates d A (keep a p) b := by
      constructor
      · intro i hi
        rw [keep_bit] at hi
        exact (Bool.and_eq_true_iff.mp hi).2
      · intro i hi
        exact (Bool.or_eq_false_iff.mp (hs.2 i hi)).1
    have hb : separates d B (keep a (fun i => !p i)) b := by
      constructor
      · intro i hi
        rw [keep_bit] at hi
        obtain ⟨hbit,hp⟩ := Bool.and_eq_true_iff.mp hi
        have hh := hs.1 i hbit
        change (p i || B.eval (positive d i)) = true at hh
        cases he : p i <;> simp_all
      · intro i hi
        exact (Bool.or_eq_false_iff.mp (hs.2 i hi)).2
    have k := hsplit (keep a p) (keep a (fun i => !p i)) (disjoint_keep ..) b
    rw [split_keep] at k
    have l := iA h.1 _ _ ha
    have r := iB h.2 _ _ hb
    change wt a b ≤ A.leaves+B.leaves
    omega

set_option maxRecDepth 12000 in
theorem kw_lower (d : Fin 7) (hd : d=0 ∨ d=1) (F : DMFormula 7) (h : admiss d F)
    (he : ∀ x, F.eval x = target x) : 10 ≤ F.leaves := by
  have pos : ∀ t : Fin 7, (t=0 ∨ t=1) → ∀ i, target (positive t i) = true := by decide
  have neg : ∀ t : Fin 7, (t=0 ∨ t=1) → ∀ i, target (negative t i) = false := by decide
  have pr := formula_bound d hd F h 127 15
    ⟨fun i _ => (he _).trans (pos _ hd i),fun i _ => (he _).trans (neg _ hd i)⟩
  exact (by decide : wt 127 15 = 10) ▸ pr

end PEqualNP.Outside.L_meta_264_aux

namespace PEqualNP.Outside.L_meta_264
open MetaComplexity

private def pos (i : Fin 7) := DMFormula.lit i true
private def starFormula : DMFormula 7 :=
  .or (.and (pos 0) (.or (pos 1) (.or (pos 2) (pos 3))))
    (.or (.and (pos 1) (.or (pos 2) (pos 4)))
         (.and (pos 5) (.or (pos 2) (pos 6))))

theorem upper (s : ℕ) (h : 10 ≤ s) : HasLeafSize 7
    (fun x : Fin 7 → Bool => x 0 && x 1 || x 1 && x 2 || x 0 && x 2 || x 0 && x 3 ||
       x 1 && x 4 || x 2 && x 5 || x 5 && x 6) s :=
  ⟨starFormula, h, by decide +kernel⟩

end PEqualNP.Outside.L_meta_264
open PEqualNP.Outside.L_meta_264_aux PEqualNP.Outside.L_meta_264_counts
theorem PEqualNP.Outside.L_meta_264 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 7 (fun x : Fin 7 → Bool => x 0 && x 1 || x 1 && x 2 || x 0 && x 2 || x 0 && x 3 || x 1 && x 4 || x 2 && x 5 || x 5 && x 6) s ↔ 10 ≤ s := by
  intro s
  constructor
  · rintro ⟨F,hle,he⟩
    by_contra! hs
    obtain h | h := PEqualNP.Outside.L_meta_264.quotas264 F he (by omega)
    · have hp : admiss 0 F := by
        apply admiss_of_counts F 0 _ he
        rw [h]; decide
      have := kw_lower 0 (Or.inl rfl) F hp he
      omega
    · have hp : admiss 1 F := by
        apply admiss_of_counts F 1 _ he
        rw [h]; decide
      have := kw_lower 1 (Or.inr rfl) F hp he
      omega
  · exact PEqualNP.Outside.L_meta_264.upper s
