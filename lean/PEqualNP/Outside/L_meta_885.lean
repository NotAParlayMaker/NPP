import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_885

open PEqualNP.CircuitLowerBounds

private lemma missed_bound {n m q : ℕ} (S : Fin m → Finset (Fin n))
    (hp : ∀ p r : Fin n, p ≠ r → ∃ i, p ∈ S i ∧ r ∈ S i)
    (hd : ∀ p : Fin n, (Finset.univ.filter fun i : Fin m => p ∈ S i).card = q + 1)
    (B : Finset (Fin n)) :
    m ≤ (Finset.univ.filter fun i : Fin m => Disjoint (S i) B).card + (B.card * q + 1) := by
  classical
  let lines (p : Fin n) := (Finset.univ.filter fun i : Fin m => p ∈ S i)
  let hits := (Finset.univ : Finset (Fin m)).filter fun i => ¬ Disjoint (S i) B
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun i => Disjoint (S i) B)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  change _ + hits.card = m at hsum
  suffices h : hits.card ≤ B.card * q + 1 by omega
  by_cases hB : B.Nonempty
  · obtain ⟨p, hpB⟩ := hB
    let more := (B.erase p).biUnion fun r => lines r \ lines p
    have hsub : hits ⊆ lines p ∪ more := by
      intro i hi
      have hne := (Finset.mem_filter.mp hi).2
      obtain ⟨r, hrS, hrB⟩ := Finset.not_disjoint_iff.mp hne
      by_cases hip : i ∈ lines p
      · exact Finset.mem_union_left _ hip
      · have hrp : r ≠ p := by
          intro e
          subst r
          exact hip (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrS⟩)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨r, Finset.mem_erase.mpr ⟨hrp, hrB⟩,
            Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrS⟩, hip⟩⟩)
    have hmore : more.card ≤ (B.erase p).card * q := by
      apply le_trans Finset.card_biUnion_le
      trans ∑ _r ∈ B.erase p, q
      · apply Finset.sum_le_sum
        intro r hr
        obtain ⟨i, hpi, hri⟩ := hp p r (Ne.symm (Finset.mem_erase.mp hr).1)
        have hlp : i ∈ lines p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi⟩
        have hlr : i ∈ lines r := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hri⟩
        have hle : (lines r \ lines p).card ≤ ((lines r).erase i).card := by
          apply Finset.card_le_card
          intro j hj
          obtain ⟨hjR, hjP⟩ := Finset.mem_sdiff.mp hj
          exact Finset.mem_erase.mpr ⟨fun e => hjP (e ▸ hlp), hjR⟩
        have hcard : (lines r).card = q + 1 := hd r
        rwa [Finset.card_erase_of_mem hlr, hcard, Nat.add_sub_cancel] at hle
      · simp
    calc
      hits.card ≤ (lines p ∪ more).card := Finset.card_le_card hsub
      _ ≤ (lines p).card + more.card := Finset.card_union_le _ _
      _ ≤ (q + 1) + (B.erase p).card * q := Nat.add_le_add (hd p).le hmore
      _ = B.card * q + 1 := by
        have hc := Finset.card_erase_add_one hpB
        rw [← hc, Nat.add_mul]
        omega
  · have hb : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    simp [hits, hb]

open PEqualNP.CircuitLowerBounds

def H270 : Prop :=
  ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size

def H669 : Prop :=
  ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))

theorem fn_family_reindex (n m q : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (hcard : ∀ i : Fin m, (S i).card = q + 1)
    (hmeet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∃ (m' : ℕ) (e : Fin m' → Fin m),
      m' = (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card ∧
      Function.Injective e ∧
      (∀ w : Fin m, Disjoint (S w) y ↔ ∃ i : Fin m', e i = w) ∧
      (∀ i : Fin m', (S (e i)).card = q + 1) ∧
      (∀ i j : Fin m', i ≠ j → (S (e i) ∩ S (e j)).card ≤ 1) := by
  classical
  set F := Finset.univ.filter (fun w : Fin m => Disjoint (S w) y) with hF
  let f := F.orderEmbOfFin (rfl : F.card = F.card)
  refine ⟨F.card, fun i => f i, rfl, f.injective, ?_, fun i => hcard _, ?_⟩
  · intro w
    have hr : Set.range f = (F : Set (Fin m)) := Finset.range_orderEmbOfFin F rfl
    constructor
    · intro hw
      have : w ∈ (F : Set (Fin m)) := by simp [hF, hw]
      rw [← hr] at this
      exact this
    · rintro ⟨i, rfl⟩
      have : f i ∈ (F : Set (Fin m)) := hr ▸ Set.mem_range_self i
      simpa [hF] using this
  · intro i j hij
    exact hmeet _ _ (fun h => hij (f.injective h))

def fnb_force {n : ℕ} (y : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ y then true else if i ∈ (∅ : Finset (Fin n)) then false else x i

theorem fnb_card_single {n : ℕ} (p : Fin n) :
    (Finset.univ.filter (fun q : Fin n => decide (q = p) = true)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at ha hc
  rw [ha, hc]

private lemma count_window {n m q K : ℕ} (hcharge : H270) (hrestrict : H669)
    (S : Fin m → Finset (Fin n)) (B : Finset (Fin n)) (L : List Gate) (out : Fin m → ℕ)
    (hcard : ∀ i, (S i).card = q + 1) (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hK : 1 ≤ K) (hq : 1 ≤ q)
    (hgates : ∀ g ∈ L, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (heval : ∀ i, Disjoint (S i) B → ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card ≤ K →
      Circuit.eval ⟨L, out i⟩ (List.ofFn (fnb_force B x)) = decide (∃ p ∈ S i, x p = true)) :
    (Finset.univ.filter (fun i : Fin m => Disjoint (S i) B)).card * min K q ≤ L.length := by
  classical
  obtain ⟨L', r, hgate', hlen, hcomp⟩ := hrestrict n L B ∅ hgates
  obtain ⟨m', e, hm', _, hiff, hcard', hpair'⟩ := fn_family_reindex n m q S B hcard hpair
  have hc : ∀ i : Fin m', ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card ≤ K →
      Circuit.eval ⟨L', r (out (e i))⟩ (List.ofFn x) = decide (∃ p ∈ S (e i), x p = true) := by
    intro i x hx
    have hdisj := (hiff (e i)).2 ⟨i, rfl⟩
    have hne : ∃ x x' : Fin n → Bool,
        Circuit.eval ⟨L, out (e i)⟩ (List.ofFn (fnb_force B x)) ≠
          Circuit.eval ⟨L, out (e i)⟩ (List.ofFn (fnb_force B x')) := by
      obtain ⟨p, hp⟩ : (S (e i)).Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      refine ⟨fun _ => false, fun a => decide (a = p), ?_⟩
      rw [heval (e i) hdisj _ (by simp), heval (e i) hdisj _ ((fnb_card_single p).trans hK)]
      simp [hp]
    exact (hcomp (out (e i)) hne x).trans (heval (e i) hdisj x hx)
  have h := hcharge n m' K (fun i => S (e i)) ⟨L', 0⟩ (fun i => r (out (e i)))
    (fun _ => min K q) hpair' (fun i => by rw [hcard']; omega) hgate'
    (fun i p => by
      change Circuit.eval ⟨L', r (out (e i))⟩ _ = true ↔ _
      rw [hc i _ ((fnb_card_single p).trans hK)]
      simp)
    (fun i x hx hz => by
      change Circuit.eval ⟨L', r (out (e i))⟩ _ = false
      rw [hc i x hx]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro p hp
      simp [hz p hp])
    (fun _ => min_le_left _ _) (fun i => by rw [hcard']; exact Nat.add_le_add_right (min_le_right _ _) _)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Circuit.size] at h
  exact hm' ▸ h.trans hlen

def indicator {n : ℕ} (B : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∈ B)

lemma stability_indicator_le {n : ℕ} {A B : Finset (Fin n)} (h : A ⊆ B) :
    indicator A ≤ indicator B := by
  intro p
  change indicator A p ≤ indicator B p
  by_cases hp : p ∈ A
  · simp [indicator, hp, h hp]
  · simp [indicator, hp]

lemma stableBudget {n : ℕ} {ι : Type} (J : Finset ι)
    (f : ι → (Fin n → Bool) → Bool) (hm : ∀ j ∈ J, Monotone (f j))
    (k t : ℕ) (ht : 1 ≤ t) (hcard : J.card ≤ t) :
    (∃ B : Finset (Fin n), B.card ≤ (t - 1) * k ∧
      ∀ j ∈ J, ∀ X : Finset (Fin n), B ⊆ X → (X \ B).card ≤ k →
        f j (indicator X) = f j (indicator B)) ∨
    (∃ B : Finset (Fin n), B.card ≤ t * k ∧
      ∀ j ∈ J, ∀ X : Finset (Fin n), B ⊆ X →
        f j (indicator X) = f j (indicator B)) := by
  classical
  let R (B : Finset (Fin n)) : Finset ι := J.filter (fun j => f j (indicator B) = false)
  have hR (B : Finset (Fin n)) (j : ι) :
      j ∈ R B ↔ j ∈ J ∧ f j (indicator B) = false := by
    simp only [R, Finset.mem_filter]
  have hle {B X : Finset (Fin n)} (hBX : B ⊆ X) {j : ι} (hj : j ∈ J) :
      f j (indicator B) ≤ f j (indicator X) :=
    hm j hj (stability_indicator_le hBX)
  have hRsub {B X : Finset (Fin n)} (hBX : B ⊆ X) : R X ⊆ R B := by
    intro j hj
    obtain ⟨hjJ, hjX⟩ := (hR X j).mp hj
    apply (hR B j).mpr
    have h := hle hBX hjJ
    rw [hjX] at h
    exact ⟨hjJ, Bool.eq_false_of_le_false h⟩
  have hrise (a b : Bool) (hab : a ≤ b) (hne : b ≠ a) : a = false ∧ b = true := by
    cases a with
    | false =>
      cases b with
      | false => exact (hne rfl).elim
      | true => exact ⟨rfl, rfl⟩
    | true => exact (hne (Bool.eq_true_of_true_le hab)).elim
  let Window (B : Finset (Fin n)) : Prop :=
    ∀ j ∈ J, ∀ X : Finset (Fin n), B ⊆ X → (X \ B).card ≤ k →
      f j (indicator X) = f j (indicator B)
  let Cone (B : Finset (Fin n)) : Prop :=
    ∀ j ∈ J, ∀ X : Finset (Fin n), B ⊆ X → f j (indicator X) = f j (indicator B)
  have finish : ∀ r (B : Finset (Fin n)), (R B).card = r → B.card ≤ (t - r) * k →
      (∃ C : Finset (Fin n), C.card ≤ (t - 1) * k ∧ Window C) ∨
      (∃ C : Finset (Fin n), C.card ≤ t * k ∧ Cone C) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro B hr hB
      by_cases hzero : r = 0
      · right
        rw [hzero, Nat.sub_zero] at hB
        have hRempty : R B = ∅ := Finset.card_eq_zero.mp (hr.trans hzero)
        refine ⟨B, hB, ?_⟩
        change ∀ j ∈ J, ∀ X : Finset (Fin n), B ⊆ X →
          f j (indicator X) = f j (indicator B)
        intro j hj X hBX
        have htrue : f j (indicator B) = true := by
          cases hb : f j (indicator B) with
          | true => rfl
          | false =>
            have hjR := (hR B j).mpr ⟨hj, hb⟩
            rw [hRempty] at hjR
            exact (Finset.notMem_empty j hjR).elim
        have h := hle hBX hj
        rw [htrue] at h ⊢
        exact Bool.eq_true_of_true_le h
      · by_cases hbad : ∃ j ∈ J, ∃ X : Finset (Fin n), B ⊆ X ∧ (X \ B).card ≤ k ∧
          f j (indicator X) ≠ f j (indicator B)
        · obtain ⟨j, hj, X, hBX, hdiff, hne⟩ := hbad
          obtain ⟨hjB, hjX⟩ := hrise _ _ (hle hBX hj) hne
          have hjRB : j ∈ R B := (hR B j).mpr ⟨hj, hjB⟩
          have hjRX : j ∉ R X := by
            intro hjR
            have h := ((hR X j).mp hjR).2
            rw [hjX] at h
            contradiction
          have hlt : (R X).card < r := by
            rw [← hr]
            exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset (hRsub hBX)).mpr
              ⟨j, hjRB, hjRX⟩)
          have hrle : r ≤ t := by
            have hRJ : R B ⊆ J := by
              intro i hi
              exact ((hR B i).mp hi).1
            rw [← hr]
            exact (Finset.card_le_card hRJ).trans hcard
          have hsteps : t - r + 1 ≤ t - (R X).card := by omega
          have hX : X.card ≤ (t - (R X).card) * k := calc
            X.card ≤ B.card + k := by
              have h := Finset.card_sdiff_add_card_eq_card hBX
              omega
            _ ≤ (t - r) * k + k := Nat.add_le_add_right hB k
            _ = (t - r + 1) * k := by rw [Nat.add_mul, Nat.one_mul]
            _ ≤ (t - (R X).card) * k := Nat.mul_le_mul_right k hsteps
          exact ih _ hlt X rfl hX
        · left
          have hsteps : t - r ≤ t - 1 := by omega
          refine ⟨B, hB.trans (Nat.mul_le_mul_right k hsteps), ?_⟩
          change ∀ j ∈ J, ∀ X : Finset (Fin n), B ⊆ X → (X \ B).card ≤ k →
            f j (indicator X) = f j (indicator B)
          intro j hj X hBX hdiff
          by_contra hne
          exact hbad ⟨j, hj, X, hBX, hdiff, hne⟩
  exact finish (R ∅).card ∅ rfl (by simp)

open PEqualNP.CircuitLowerBounds

def readWire {n : ℕ} (L : List Gate) (j : Fin L.length) (x : Fin n → Bool) : Bool :=
  ((L.get j).inputs.map (fun i =>
    (Circuit.wires ⟨L.take j.val, 0⟩ (List.ofFn x)).getD i false)).headD false

private def replaceGate (g : Gate) (b : Bool) : Gate :=
  match g.op with
  | .not => if b then ⟨.or, []⟩ else ⟨.and, []⟩
  | _ => g

def replaceNot {n : ℕ} (L : List Gate) (base : Fin n → Bool) : List Gate :=
  List.ofFn (fun j : Fin L.length => replaceGate (L.get j) (readWire L j base))

lemma replace_length {n : ℕ} (L : List Gate) (base : Fin n → Bool) :
    (replaceNot L base).length = L.length := by
  simp only [replaceNot, List.length_ofFn]

lemma replace_ops {n : ℕ} (L : List Gate) (base : Fin n → Bool)
    (hops : ∀ g ∈ L, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ replaceNot L base, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  unfold replaceNot at hg
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  obtain ⟨hop, hlen⟩ := hops _ (List.get_mem L j)
  rcases hop with h | h | h
  · simp only [replaceGate, h]
    exact ⟨Or.inl trivial, hlen⟩
  · simp only [replaceGate, h]
    exact ⟨Or.inr trivial, hlen⟩
  · simp only [replaceGate, h]
    cases readWire L j base <;> simp

private lemma replace_gate_eval (g : Gate) (b : Bool) (w : List Bool)
    (h : g.op = GateOp.not → (g.inputs.map (fun i => w.getD i false)).headD false = b) :
    (replaceGate g b).op.eval ((replaceGate g b).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  cases hg : g.op <;> simp only [replaceGate, hg]
  have hb := h hg
  cases b <;> simp only [GateOp.eval, hb, List.map_nil, List.all_nil, List.any_nil,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]

private lemma replace_wires_snoc (L : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨L ++ [g], 0⟩ x = Circuit.wires ⟨L, 0⟩ x ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨L, 0⟩ x).getD i false)] := by
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma replace_eval {n : ℕ} (L : List Gate) (base x : Fin n → Bool)
    (hx : ∀ j : Fin L.length, (L.get j).op = GateOp.not →
      readWire L j x = readWire L j base) (o : ℕ) :
    Circuit.eval ⟨replaceNot L base, o⟩ (List.ofFn x) =
      Circuit.eval ⟨L, o⟩ (List.ofFn x) := by
  have hp : ∀ k, k ≤ L.length →
      Circuit.wires ⟨(replaceNot L base).take k, 0⟩ (List.ofFn x) =
        Circuit.wires ⟨L.take k, 0⟩ (List.ofFn x) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hi : k < L.length := by omega
      have hi' : k < (replaceNot L base).length := by
        simpa only [replace_length] using hi
      let j : Fin L.length := ⟨k, hi⟩
      have hold : L.take (k + 1) = L.take k ++ [L.get j] := by
        simpa only [List.get_eq_getElem, j] using (List.take_succ_eq_append_getElem hi)
      have hget : (replaceNot L base)[k]'hi' =
          replaceGate (L.get j) (readWire L j base) := by
        simp only [replaceNot, List.getElem_ofFn, j]
      have hnew := List.take_succ_eq_append_getElem hi'
      rw [hget] at hnew
      rw [hnew, hold, replace_wires_snoc, replace_wires_snoc, ih (Nat.le_of_lt hi)]
      have hv := replace_gate_eval (L.get j) (readWire L j base)
        (Circuit.wires ⟨L.take k, 0⟩ (List.ofFn x)) (fun hj => hx j hj)
      rw [hv]
  have h := hp L.length le_rfl
  have hlen : (replaceNot L base).length ≤ L.length := (replace_length L base).le
  rw [List.take_of_length_le hlen, List.take_of_length_le (Nat.le_refl L.length)] at h
  change (Circuit.wires ⟨replaceNot L base, 0⟩ (List.ofFn x)).getD o false =
    (Circuit.wires ⟨L, 0⟩ (List.ofFn x)).getD o false
  rw [h]

open PEqualNP.CircuitLowerBounds

private lemma charge_stable {n m q K : ℕ} (hcharge : H270) (hrestrict : H669)
    (S : Fin m → Finset (Fin n)) (B : Finset (Fin n)) (L : List Gate) (out : Fin m → ℕ)
    (hcard : ∀ i, (S i).card = q + 1) (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hK : 1 ≤ K) (hq : 1 ≤ q)
    (hgates : ∀ g ∈ L, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ i (x : Fin n → Bool),
      Circuit.eval ⟨L, out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true))
    (hstable : ∀ j : Fin L.length, (L.get j).op = GateOp.not → ∀ X : Finset (Fin n),
      B ⊆ X → (X \ B).card ≤ K → readWire L j (indicator X) = readWire L j (indicator B)) :
    (Finset.univ.filter (fun i : Fin m => Disjoint (S i) B)).card * min K q ≤ L.length := by
  classical
  rw [← replace_length L (indicator B)]
  apply count_window hcharge hrestrict S B (replaceNot L (indicator B)) out hcard hpair hK hq
    (replace_ops L (indicator B) hgates)
  intro i hi x hx
  let X := Finset.univ.filter fun p => fnb_force B x p = true
  have hBX : B ⊆ X := by
    intro p hp
    simp [X, fnb_force, hp]
  have hXB : (X \ B).card ≤ K := by
    refine (Finset.card_le_card ?_).trans hx
    intro p hp
    obtain ⟨hpX, hpB⟩ := Finset.mem_sdiff.mp hp
    simpa [X, fnb_force, hpB] using hpX
  have hX : indicator X = fnb_force B x := by
    funext p
    cases h : fnb_force B x p <;> simp [indicator, X, h]
  rw [replace_eval L (indicator B) (fnb_force B x)
    (fun j hj => hX ▸ hstable j hj X hBX hXB), heval]
  simp only [decide_eq_decide]
  have hf : ∀ p ∈ S i, fnb_force B x p = x p := by
    intro p hp
    simp [fnb_force, Finset.disjoint_left.mp hi hp]
  exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, (hf p hp).symm ▸ h⟩,
    fun ⟨p, hp, h⟩ => ⟨p, hp, (hf p hp).trans h⟩⟩

private lemma finish_count {m missed c cost bound : ℕ} (hm : m ≤ missed + cost)
    (hbound : bound + c * cost ≤ c * m) : bound ≤ missed * c := by
  have h := Nat.mul_le_mul_left c hm
  rw [Nat.mul_add] at h
  rw [Nat.mul_comm missed c]
  omega

end PEqualNP.Outside.L_meta_885

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_885

theorem PEqualNP.Outside.L_meta_885 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (nP mL qO : ℕ) (Fam : Fin mL → Finset (Fin nP)), (∀ i1 : Fin mL, (Fam i1).card = qO + 1) → (∀ i7 i8 : Fin mL, i7 ≠ i8 → (Fam i7 ∩ Fam i8).card ≤ 1) → (∀ p1 p2 : Fin nP, p1 ≠ p2 → ∃ i3 : Fin mL, p1 ∈ Fam i3 ∧ p2 ∈ Fam i3) → (∀ p3 : Fin nP, (Finset.univ.filter (fun i4 : Fin mL => p3 ∈ Fam i4)).card = qO + 1) → ∀ (tN kW : ℕ) (L : List PEqualNP.CircuitLowerBounds.Gate) (outW : Fin mL → ℕ), 1 ≤ tN → 1 ≤ kW → (∀ g1 ∈ L, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g1.inputs.length ≤ 2) → Set.ncard {i5 : Fin L.length | (L.get i5).op = PEqualNP.CircuitLowerBounds.GateOp.not} ≤ tN → (∀ (j1 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), L[j1]? = some g2 → g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → Monotone (fun x1 : Fin nP → Bool => (g2.inputs.map (fun i6 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨L.take j1, 0⟩ (List.ofFn x1)).getD i6 false)).headD false)) → (∀ (w1 : Fin mL) (x2 : Fin nP → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨L, outW w1⟩ (List.ofFn x2) = decide (∃ v1 ∈ Fam w1, x2 v1 = true)) → ∀ Kb : ℕ, ((tN = 1 ∧ Kb ≤ kW * mL ∧ Kb ≤ qO * mL) ∨ (Kb + kW * (tN * kW * qO + 1) ≤ kW * mL + kW * kW * qO ∧ Kb + qO * (tN * kW * qO + 1) ≤ qO * mL + qO * kW * qO)) → Kb + qO * (tN * kW * qO + 1) ≤ qO * mL → Kb ≤ L.length := by
  classical
  intro hcharge hrestrict n m q S hs hp hpoints hdegree t k L out ht hk hg hnot hmono heval bound hsplit hfull
  by_cases hq0 : q = 0
  · simp [hq0] at hfull
    omega
  have hq : 1 ≤ q := by omega
  let J := (Finset.univ : Finset (Fin L.length)).filter fun j => (L.get j).op = GateOp.not
  have jmem (j : Fin L.length) : j ∈ J ↔ (L.get j).op = GateOp.not := by simp [J]
  have jcard : J.card ≤ t := by
    have heq : (J : Set (Fin L.length)) = {j | (L.get j).op = GateOp.not} := by
      ext j
      exact jmem j
    rwa [← heq, Set.ncard_coe_finset] at hnot
  have jmono : ∀ j ∈ J, Monotone (readWire (n := n) L j) := by
    intro j hj
    exact hmono j.val (L.get j) (getElem?_pos L j.val j.isLt) ((jmem j).mp hj)
  rcases stableBudget J (readWire (n := n) L) jmono k t ht jcard with h | h
  · obtain ⟨B, hB, hstable⟩ := h
    refine le_trans ?_ (charge_stable hcharge hrestrict S B L out hs hp hk hq hg heval
      (fun j hj => hstable j ((jmem j).mpr hj)))
    rcases hsplit with ⟨rfl, hbK, hbQ⟩ | ⟨hbK, hbQ⟩
    · have hz : B = ∅ := Finset.card_eq_zero.mp (by simpa using hB)
      rw [hz, show (Finset.univ.filter (fun i : Fin m => Disjoint (S i) (∅ : Finset (Fin n)))).card = m by simp]
      rcases le_total k q with h | h
      · simpa [min_eq_left h, Nat.mul_comm] using hbK
      · simpa [min_eq_right h, Nat.mul_comm] using hbQ
    · have hm := missed_bound S hpoints hdegree B
      have hkill : B.card * q + 1 ≤ (t - 1) * k * q + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_right q hB) 1
      have hsum : t * k * q + 1 = ((t - 1) * k * q + 1) + k * q := by
        have he : t - 1 + 1 = t := Nat.sub_add_cancel ht
        calc t * k * q + 1 = (t - 1 + 1) * k * q + 1 := by rw [he]
             _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
      rw [hsum, Nat.mul_add] at hbK hbQ
      rcases le_total k q with h | h
      · rw [min_eq_left h]
        apply finish_count hm
        have hmul := Nat.mul_le_mul_left k hkill
        rw [← Nat.mul_assoc] at hbK
        omega
      · rw [min_eq_right h]
        apply finish_count hm
        have hmul := Nat.mul_le_mul_left q hkill
        rw [← Nat.mul_assoc] at hbQ
        omega
  · obtain ⟨B, hB, hstable⟩ := h
    have hb := charge_stable hcharge hrestrict (K := q) S B L out hs hp hq hq hg heval
      (fun j hj X hBX _ => hstable j ((jmem j).mpr hj) X hBX)
    rw [min_self] at hb
    refine le_trans (finish_count (missed_bound S hpoints hdegree B) ?_) hb
    have hkill := Nat.mul_le_mul_left q (Nat.add_le_add_right (Nat.mul_le_mul_right q hB) 1)
    omega
