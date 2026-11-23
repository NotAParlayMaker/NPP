import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_263
open PEqualNP.MetaComplexity
-- The six edge points (ones) and the five maximal zeros of the butterfly, bit 5 * point + input.
def xs (a : Fin 6) (i : Fin 5) : Bool := Nat.beq ((823433379 >>> (5 * a.val + i.val)) % 2) 1
def ys (b : Fin 5) (i : Fin 5) : Bool := Nat.beq ((21383489 >>> (5 * b.val + i.val)) % 2) 1
-- mu S T: least weighted leaf count (centre leaf 1, other leaf 2) of a formula true on the
-- ones in S and false on the zeros in T. Four bits per entry.
def tab : ℕ := 1081640675604380936375068103473484251966627922125534663254699944235957989562506692174691244616946819957220220241251332135858247418464617154209418396295211597144779797272135746875736713927714094675079912075791466609261593560266089832309964934160110808520393077151900392839048253591731328592727754926686380491665774700354787194468092330122908623671499405270868074193681071623515511845937058219867470893346499151959263024033745639421891756728302696570616235286832717960700750437884065074979193042998367935496928791046503534808026127572867012440042463623977683814514574266841827419611335817001501661070812321449588407640291851981690693330961459265902351533599891588434440660528282818584856251099239579267338296176157315767885634193247280324794991676306339484882045207616006186217774714309679791404097692157820493135117209596509438193855093150029523357226915866001417608204938353431713132090829197156246812794650162627419416463340484087544109414507987147704333822243079961212198680750029121166586593006714893499210016134797076747004887718155137324244503773232989394143501910061677105140957522693881795537882700947415356702452207378266931568612148484985153420749803332099818141304754937446069634539186301365617835054124041538636549290870885108768359012850687887156111420800572996108274545800975627572677870493151564591045581420245265430965613783369195666946794238762894436994431201396586385785502563444009448292999898343044154023881443313544858791522273650344320582100936704231796980325437144899052565691293504516894680695387039973090954965155463075722338802858178187891824126314823529042208758819577871621456384688253806580728443482059363488444522984941177843806967141902093622718594598776533367191746086932760997715671400609210166476455563012231451649698475517650907659275795108322479417271508070004642348208286422951022731221618931231194114376315888973598382127629896616502361021230741735337002145869943306042733511562346702693903157310711751187314395413346189916180358160031361226429009026881017215773719299714752439467913071567935220845120622771154134641328491545851120483893999198235112232564069334525440590554365115913579384610586627315098538194978700064095844079200660592010243536385615950664984103771735838780041949060070926241129253780631924230827447616511356421065931259400783575878061776694240950876475544276478469505118757465985000969262758821942864023010310584126547603729671842176033920940443337584374050911201645403482566741833005582123474380996521354067968
def mu (s0 s1 s2 s3 s4 s5 t0 t1 t2 t3 t4 : Bool) : ℕ :=
  (tab >>> (4 * (1 * s0.toNat + 2 * s1.toNat + 4 * s2.toNat + 8 * s3.toNat + 16 * s4.toNat + 32 * s5.toNat + 64 * t0.toNat + 128 * t1.toNat + 256 * t2.toNat + 512 * t3.toNat + 1024 * t4.toNat))) % 16
def muV (S : Fin 6 → Bool) (T : Fin 5 → Bool) : ℕ :=
  mu (S 0) (S 1) (S 2) (S 3) (S 4) (S 5) (T 0) (T 1) (T 2) (T 3) (T 4)
def wt : DMFormula 5 → ℕ
  | DMFormula.lit j _ => if j = 0 then 1 else 2
  | DMFormula.and A B => wt A + wt B
  | DMFormula.or A B => wt A + wt B
def cnt (i : Fin 5) : DMFormula 5 → ℕ
  | DMFormula.lit j _ => if j = i then 1 else 0
  | DMFormula.and A B => cnt i A + cnt i B
  | DMFormula.or A B => cnt i A + cnt i B
set_option maxRecDepth 100000 in
lemma leaf_ok : ∀ (i : Fin 5) (s s0 s1 s2 s3 s4 s5 t0 t1 t2 t3 t4 : Bool),
    (s0 = true → (DMFormula.lit i s).eval (xs 0) = true) →
    (s1 = true → (DMFormula.lit i s).eval (xs 1) = true) →
    (s2 = true → (DMFormula.lit i s).eval (xs 2) = true) →
    (s3 = true → (DMFormula.lit i s).eval (xs 3) = true) →
    (s4 = true → (DMFormula.lit i s).eval (xs 4) = true) →
    (s5 = true → (DMFormula.lit i s).eval (xs 5) = true) →
    (t0 = true → (DMFormula.lit i s).eval (ys 0) = false) →
    (t1 = true → (DMFormula.lit i s).eval (ys 1) = false) →
    (t2 = true → (DMFormula.lit i s).eval (ys 2) = false) →
    (t3 = true → (DMFormula.lit i s).eval (ys 3) = false) →
    (t4 = true → (DMFormula.lit i s).eval (ys 4) = false) →
    mu s0 s1 s2 s3 s4 s5 t0 t1 t2 t3 t4 ≤ (if i = 0 then 1 else 2) := by
  decide +kernel
set_option maxRecDepth 100000 in
lemma and_ok : ∀ (s0 s1 s2 s3 s4 s5 t0 t1 t2 t3 t4 m0 m1 m2 m3 m4 : Bool),
    mu s0 s1 s2 s3 s4 s5 t0 t1 t2 t3 t4 ≤ mu s0 s1 s2 s3 s4 s5 (t0 && m0) (t1 && m1) (t2 && m2) (t3 && m3) (t4 && m4) + mu s0 s1 s2 s3 s4 s5 (t0 && !m0) (t1 && !m1) (t2 && !m2) (t3 && !m3) (t4 && !m4) := by
  decide +kernel
set_option maxRecDepth 100000 in
lemma or_ok : ∀ (s0 s1 s2 s3 s4 s5 t0 t1 t2 t3 t4 m0 m1 m2 m3 m4 m5 : Bool),
    mu s0 s1 s2 s3 s4 s5 t0 t1 t2 t3 t4 ≤ mu (s0 && m0) (s1 && m1) (s2 && m2) (s3 && m3) (s4 && m4) (s5 && m5) t0 t1 t2 t3 t4 + mu (s0 && !m0) (s1 && !m1) (s2 && !m2) (s3 && !m3) (s4 && !m4) (s5 && !m5) t0 t1 t2 t3 t4 := by
  decide +kernel
lemma main (φ : DMFormula 5) : ∀ (S : Fin 6 → Bool) (T : Fin 5 → Bool),
    (∀ a, S a = true → φ.eval (xs a) = true) → (∀ b, T b = true → φ.eval (ys b) = false) →
    muV S T ≤ wt φ := by
  induction φ with
  | lit i s =>
    intro S T hS hT
    exact leaf_ok i s (S 0) (S 1) (S 2) (S 3) (S 4) (S 5) (T 0) (T 1) (T 2) (T 3) (T 4)
      (hS 0) (hS 1) (hS 2) (hS 3) (hS 4) (hS 5) (hT 0) (hT 1) (hT 2) (hT 3) (hT 4)
  | and A B ihA ihB =>
    intro S T hS hT
    have h1 := ihB S (fun b => T b && A.eval (ys b))
      (fun a ha => by have h := hS a ha; simp only [DMFormula.eval, Bool.and_eq_true] at h; exact h.2)
      (fun b hb => by
        simp only [Bool.and_eq_true] at hb
        have h := hT b hb.1
        simp only [DMFormula.eval, hb.2, Bool.true_and] at h
        exact h)
    have h2 := ihA S (fun b => T b && !A.eval (ys b))
      (fun a ha => by have h := hS a ha; simp only [DMFormula.eval, Bool.and_eq_true] at h; exact h.1)
      (fun b hb => by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
        exact hb.2)
    have h3 := and_ok (S 0) (S 1) (S 2) (S 3) (S 4) (S 5) (T 0) (T 1) (T 2) (T 3) (T 4) (A.eval (ys 0)) (A.eval (ys 1)) (A.eval (ys 2)) (A.eval (ys 3)) (A.eval (ys 4))
    simp only [muV] at h1 h2 ⊢
    simp only [wt]
    omega
  | or A B ihA ihB =>
    intro S T hS hT
    have h1 := ihA (fun a => S a && A.eval (xs a)) T
      (fun a ha => by
        simp only [Bool.and_eq_true] at ha
        exact ha.2)
      (fun b hb => by have h := hT b hb; simp only [DMFormula.eval, Bool.or_eq_false_iff] at h; exact h.1)
    have h2 := ihB (fun a => S a && !A.eval (xs a)) T
      (fun a ha => by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
        have h := hS a ha.1
        simp only [DMFormula.eval, ha.2, Bool.false_or] at h
        exact h)
      (fun b hb => by have h := hT b hb; simp only [DMFormula.eval, Bool.or_eq_false_iff] at h; exact h.2)
    have h3 := or_ok (S 0) (S 1) (S 2) (S 3) (S 4) (S 5) (T 0) (T 1) (T 2) (T 3) (T 4) (A.eval (xs 0)) (A.eval (xs 1)) (A.eval (xs 2)) (A.eval (xs 3)) (A.eval (xs 4)) (A.eval (xs 5))
    simp only [muV] at h1 h2 ⊢
    simp only [wt]
    omega
lemma cnt_eq (i : Fin 5) (φ : DMFormula 5) :
    DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin 5) (_ : Bool) => if j = i then 1 else 0)
      (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = cnt i φ := by
  induction φ with
  | lit j b => rfl
  | and A B ha hb => exact congrArg₂ (· + ·) ha hb
  | or A B ha hb => exact congrArg₂ (· + ·) ha hb
lemma wt_eq (φ : DMFormula 5) :
    wt φ = cnt 0 φ + 2 * (cnt 1 φ + cnt 2 φ + cnt 3 φ + cnt 4 φ) := by
  induction φ with
  | lit j b => fin_cases j <;> simp [wt, cnt]
  | and A B ha hb => simp only [wt, cnt]; omega
  | or A B ha hb => simp only [wt, cnt]; omega
lemma full_val : muV (fun _ => true) (fun _ => true) = 15 := by
  decide +kernel
lemma ones_ok : ∀ a : Fin 6, (xs a 0 && xs a 1 || xs a 0 && xs a 2 || xs a 1 && xs a 2 || xs a 0 && xs a 3 || xs a 0 && xs a 4 || xs a 3 && xs a 4) = true := by
  decide +kernel
lemma zeros_ok : ∀ b : Fin 5, (ys b 0 && ys b 1 || ys b 0 && ys b 2 || ys b 1 && ys b 2 || ys b 0 && ys b 3 || ys b 0 && ys b 4 || ys b 3 && ys b 4) = false := by
  decide +kernel
end PEqualNP.Outside.L_meta_263

theorem PEqualNP.Outside.L_meta_263 : ∀ φ : PEqualNP.MetaComplexity.DMFormula 5, (∀ x : Fin 5 → Bool, φ.eval x = (x 0 && x 1 || x 0 && x 2 || x 1 && x 2 || x 0 && x 3 || x 0 && x 4 || x 3 && x 4)) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin 5) (_ : Bool) => if j = 1 then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ + PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin 5) (_ : Bool) => if j = 2 then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 3 → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin 5) (_ : Bool) => if j = 3 then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ + PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin 5) (_ : Bool) => if j = 4 then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 3 → 3 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin 5) (_ : Bool) => if j = 0 then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ := by
  intro φ hφ h12 h34
  have hm := PEqualNP.Outside.L_meta_263.main φ (fun _ => true) (fun _ => true)
    (fun a _ => by rw [hφ]; exact PEqualNP.Outside.L_meta_263.ones_ok a)
    (fun b _ => by rw [hφ]; exact PEqualNP.Outside.L_meta_263.zeros_ok b)
  rw [PEqualNP.Outside.L_meta_263.full_val, PEqualNP.Outside.L_meta_263.wt_eq] at hm
  rw [PEqualNP.Outside.L_meta_263.cnt_eq 1 φ, PEqualNP.Outside.L_meta_263.cnt_eq 2 φ] at h12
  rw [PEqualNP.Outside.L_meta_263.cnt_eq 3 φ, PEqualNP.Outside.L_meta_263.cnt_eq 4 φ] at h34
  rw [PEqualNP.Outside.L_meta_263.cnt_eq 0 φ]
  omega
