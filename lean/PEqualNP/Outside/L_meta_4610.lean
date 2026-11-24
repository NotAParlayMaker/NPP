import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4610

def SLP (B P : List ℕ) : Prop :=
  ∀ (i : Fin P.length), ∃ a ∈ B ++ List.take (↑i) P, ∃ b ∈ B ++ List.take (↑i) P,
    P.get i = a &&& b ∨ P.get i = a ||| b

def Good (L : List ℕ) (m r : ℕ) : Prop :=
  ∀ (k : ℕ), ∃ (j : ℕ), m.testBit j = true ∧ r.testBit j = r.testBit k ∧ ∀ v ∈ L,
    if r.testBit k = true then v.testBit j = true → v.testBit k = true
    else v.testBit k = true → v.testBit j = true

def Mono (L : List ℕ) (u : ℕ) : Prop :=
  ∀ j k : ℕ, (∀ v ∈ L, v.testBit j = true → v.testBit k = true) →
    u.testBit j = true → u.testBit k = true

lemma mono_base {L : List ℕ} {v : ℕ} (hv : v ∈ L) : Mono L v :=
  fun _ _ h hj => h v hv hj

lemma mono_and {L : List ℕ} {a b : ℕ} (ha : Mono L a) (hb : Mono L b) : Mono L (a &&& b) := by
  intro j k h hj
  simp only [Nat.testBit_and, Bool.and_eq_true] at hj ⊢
  exact ⟨ha j k h hj.1, hb j k h hj.2⟩

lemma mono_or {L : List ℕ} {a b : ℕ} (ha : Mono L a) (hb : Mono L b) : Mono L (a ||| b) := by
  intro j k h hj
  simp only [Nat.testBit_or, Bool.or_eq_true] at hj ⊢
  rcases hj with hj | hj
  · exact Or.inl (ha j k h hj)
  · exact Or.inr (hb j k h hj)

lemma slp_init {B P : List ℕ} {p : ℕ} (h : SLP B (P ++ [p])) :
    SLP B P ∧ ∃ a ∈ B ++ P, ∃ b ∈ B ++ P, p = a &&& b ∨ p = a ||| b := by
  refine ⟨fun i => ?_, ?_⟩
  · have hi := i.2
    obtain ⟨a, ha, b, hb, hab⟩ := h ⟨i.1, by simp⟩
    have ht : List.take i.1 (P ++ [p]) = List.take i.1 P :=
      List.take_append_of_le_length (by omega)
    have hg : (P ++ [p]).get ⟨i.1, by simp⟩ = P.get i := by
      simp [hi]
    change a ∈ B ++ List.take i.1 (P ++ [p]) at ha
    change b ∈ B ++ List.take i.1 (P ++ [p]) at hb
    rw [ht] at ha hb
    rw [hg] at hab
    exact ⟨a, ha, b, hb, hab⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := h ⟨P.length, by simp⟩
    have ht : List.take P.length (P ++ [p]) = P := by simp
    have hg : (P ++ [p]).get ⟨P.length, by simp⟩ = p := by
      simp
    change a ∈ B ++ List.take P.length (P ++ [p]) at ha
    change b ∈ B ++ List.take P.length (P ++ [p]) at hb
    rw [ht] at ha hb
    rw [hg] at hab
    exact ⟨a, ha, b, hb, hab⟩

lemma slp_snoc {B P : List ℕ} {p : ℕ} (h : SLP B P)
    (hp : ∃ a ∈ B ++ P, ∃ b ∈ B ++ P, p = a &&& b ∨ p = a ||| b) : SLP B (P ++ [p]) := by
  intro i
  have hi : i.1 < P.length + 1 := by simpa using i.2
  rcases Nat.lt_or_ge i.1 P.length with hlt | hge
  · obtain ⟨a, ha, b, hb, hab⟩ := h ⟨i.1, hlt⟩
    have ht : List.take i.1 (P ++ [p]) = List.take i.1 P :=
      List.take_append_of_le_length (by omega)
    have hg : (P ++ [p]).get i = P.get ⟨i.1, hlt⟩ := by
      simp [hlt]
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [ht]; exact ha
    · rw [ht]; exact hb
    · rw [hg]; exact hab
  · have he : i.1 = P.length := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := hp
    have ht : List.take i.1 (P ++ [p]) = P := by rw [he]; simp
    have hg : (P ++ [p]).get i = p := by
      simp [he]
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [ht]; exact ha
    · rw [ht]; exact hb
    · rw [hg]; exact hab

lemma lift (L : List ℕ) (m : ℕ) (P : List ℕ) (hP : SLP (L.map (fun x => x &&& m)) P) :
    ∃ Q : List ℕ, Q.length = P.length ∧ SLP L Q ∧
      ∀ w ∈ L.map (fun x => x &&& m) ++ P, ∃ u ∈ L ++ Q, u &&& m = w ∧ Mono L u := by
  induction P using List.reverseRecOn with
  | nil =>
    refine ⟨[], rfl, fun i => (Nat.not_lt_zero _ i.2).elim, ?_⟩
    intro w hw
    simp only [List.append_nil, List.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨v, by simpa using hv, rfl, mono_base hv⟩
  | append_singleton P p ih =>
    obtain ⟨hP0, a, ha, b, hb, hab⟩ := slp_init hP
    obtain ⟨Q, hQl, hQ, hlift⟩ := ih hP0
    obtain ⟨a', ha'm, ha'e, ha'M⟩ := hlift a ha
    obtain ⟨b', hb'm, hb'e, hb'M⟩ := hlift b hb
    have key : ∃ q : ℕ, (q = a' &&& b' ∨ q = a' ||| b') ∧ q &&& m = p ∧ Mono L q := by
      rcases hab with h | h
      · refine ⟨a' &&& b', Or.inl rfl, ?_, mono_and ha'M hb'M⟩
        rw [h, ← ha'e, ← hb'e]
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [Nat.testBit_and]
        generalize a'.testBit i = x
        generalize b'.testBit i = y
        generalize m.testBit i = z
        cases x <;> cases y <;> cases z <;> rfl
      · refine ⟨a' ||| b', Or.inr rfl, ?_, mono_or ha'M hb'M⟩
        rw [h, ← ha'e, ← hb'e]
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [Nat.testBit_and, Nat.testBit_or]
        generalize a'.testBit i = x
        generalize b'.testBit i = y
        generalize m.testBit i = z
        cases x <;> cases y <;> cases z <;> rfl
    obtain ⟨q, hq, hqm, hqM⟩ := key
    refine ⟨Q ++ [q], by simp [hQl], slp_snoc hQ ⟨a', ha'm, b', hb'm, hq⟩, ?_⟩
    intro w hw
    rw [← List.append_assoc, List.mem_append] at hw
    rcases hw with hw | hw
    · obtain ⟨u, hu, hu1, hu2⟩ := hlift w hw
      exact ⟨u, by rw [← List.append_assoc]; exact List.mem_append_left _ hu, hu1, hu2⟩
    · rw [List.mem_singleton] at hw
      subst hw
      exact ⟨q, by simp, hqm, hqM⟩

theorem main (L : List ℕ) (m r : ℕ) (P : List ℕ) (hm : Good L m r)
    (hP : SLP (L.map (fun x => x &&& m)) P)
    (hr : r &&& m ∈ L.map (fun x => x &&& m) ++ P) :
    ∃ Q : List ℕ, Q.length ≤ P.length ∧ SLP L Q ∧ r ∈ L ++ Q := by
  obtain ⟨Q, hl, hQ, hlift⟩ := lift L m P hP
  obtain ⟨u, hu, hum, huM⟩ := hlift _ hr
  have hur : u = r := by
    apply Nat.eq_of_testBit_eq
    intro k
    obtain ⟨j, hjm, hjr, hjv⟩ := hm k
    have huj : u.testBit j = r.testBit j := by
      have h1 := congrArg (fun z => z.testBit j) hum
      simp only [Nat.testBit_and, hjm, Bool.and_true] at h1
      exact h1
    by_cases hrk : r.testBit k = true
    · rw [hrk] at hjr
      have hv' : ∀ v ∈ L, v.testBit j = true → v.testBit k = true := by
        intro v hvL
        have h2 := hjv v hvL
        simp only [hrk, ↓reduceIte] at h2
        exact h2
      rw [hrk]
      exact huM j k hv' (huj.trans hjr)
    · have hrk' : r.testBit k = false := by simpa using hrk
      rw [hrk'] at hjr
      have hv' : ∀ v ∈ L, v.testBit k = true → v.testBit j = true := by
        intro v hvL
        have h2 := hjv v hvL
        simp only [hrk] at h2
        exact h2
      rw [hrk']
      by_contra hc
      have hc' : u.testBit k = true := by simpa using hc
      have h3 := huM k j hv' hc'
      rw [huj, hjr] at h3
      exact absurd h3 (by simp)
  refine ⟨Q, hl.le, hQ, ?_⟩
  rw [← hur]
  exact hu

end PEqualNP.Outside.L_meta_4610

theorem PEqualNP.Outside.L_meta_4610 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; have x2 : List ℕ → ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 x4 : ℕ) => ∀ (x5 : ℕ), ∃ (x6 : ℕ), x3.testBit x6 = Bool.true ∧ x4.testBit x6 = x4.testBit x5 ∧ ∀ x7 ∈ x2, if x4.testBit x5 = Bool.true then x7.testBit x6 = Bool.true → x7.testBit x5 = Bool.true else x7.testBit x5 = Bool.true → x7.testBit x6 = Bool.true; ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ),   x2 x3 x4 x5 →     have x8 : List ℕ := List.map (fun (x8 : ℕ) => x8 &&& x4) x3;     x1 x8 x6 → x5 &&& x4 ∈ x8 ++ x6 → ∃ (x11 : List ℕ), x11.length ≤ x6.length ∧ x1 x3 x11 ∧ x5 ∈ x3 ++ x11 := by
  show ∀ (L : List ℕ) (m r : ℕ) (P : List ℕ), PEqualNP.Outside.L_meta_4610.Good L m r →
    PEqualNP.Outside.L_meta_4610.SLP (L.map (fun x8 => x8 &&& m)) P →
    r &&& m ∈ L.map (fun x8 => x8 &&& m) ++ P →
    ∃ Q : List ℕ, Q.length ≤ P.length ∧ PEqualNP.Outside.L_meta_4610.SLP L Q ∧ r ∈ L ++ Q
  intro L m r P hm hP hr
  exact PEqualNP.Outside.L_meta_4610.main L m r P hm hP hr
