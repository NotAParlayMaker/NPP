import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1441
open PEqualNP.CircuitLowerBounds

noncomputable def mMono (N low z : ℕ) : ℕ :=
  Nat.land (Nat.mod z (low + 1)) (Nat.xor (Nat.shiftRight z N) low)

noncomputable def mGen (N low z : ℕ) : ℕ :=
  Nat.xor (Nat.mod z (low + 1)) (Nat.shiftRight z N)

noncomputable def mk (N low : ℕ) (nn : Bool) (z : ℕ) : ℕ := cond nn (mGen N low z) (mMono N low z)

noncomputable def scan (bit : ℕ) (k : ℕ → Bool) (ms : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) false
    (fun m _ ih => @Nat.rec (fun _ => Bool) ih (fun _ _ => k m || ih) (Nat.land m bit)) ms

noncomputable def cover (low : ℕ) (ms : List ℕ) : ℕ → ℕ → Bool :=
  @Nat.rec (fun _ => ℕ → Bool)
    (fun need => Nat.beq need 0)
    (fun _ cb need =>
      @Nat.rec (fun _ => Bool) true
        (fun _ _ =>
          scan (Nat.land need (Nat.xor need (need - 1))) (fun m => cb (Nat.land need (Nat.xor m low))) ms)
        need)

noncomputable def memb (z : ℕ) (ws : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) false (fun w _ ih => Nat.beq w z || ih) ws

noncomputable def remv (a : ℕ) (un : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [] (fun u _ ih => cond (Nat.beq u a) ih (u :: ih)) un

noncomputable def len (l : List ℕ) : ℕ := @List.rec ℕ (fun _ => ℕ) 0 (fun _ _ ih => ih + 1) l

noncomputable def mapMk (N low : ℕ) (nn : Bool) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [] (fun w _ ih => mk N low nn w :: ih) l

noncomputable def need0 (N low : ℕ) (nn : Bool) (un : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) low (fun u _ ih => Nat.land ih (Nat.xor (mk N low nn u) low)) un

noncomputable def inner (h : ℕ → ℕ → ℕ → Bool) (a : ℕ) (rest : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) false
    (fun b _ ih => h a b (Nat.land a b) || (h a b (Nat.lor a b) || ih)) rest

noncomputable def outer (h : ℕ → ℕ → ℕ → Bool) (ws : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) false (fun a rest ih => inner h a rest || ih) ws

noncomputable def notAll (g : ℕ → Bool) (nc : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) false (fun a _ ih => g a || ih) nc

noncomputable def notZ (N low full zt : ℕ)
    (sk : List ℕ → List ℕ → List ℕ → Bool → ℕ → List ℕ → List ℕ → Bool)
    (ws un : List ℕ) (v0 : ℕ) (fresh : List ℕ) (a z : ℕ) : Bool :=
  !(Nat.beq z 0 || (Nat.beq z full || memb z ws)) &&
    (Nat.beq z zt ||
      sk (z :: ws) (mapMk N low false (z :: ws)) (z :: remv a un) false v0 (z :: fresh) [])

noncomputable def stepNot (N low full zt : ℕ)
    (sk : List ℕ → List ℕ → List ℕ → Bool → ℕ → List ℕ → List ℕ → Bool)
    (ws un : List ℕ) (v0 : ℕ) (fresh : List ℕ) (a : ℕ) : Bool :=
  notZ N low full zt sk ws un v0 fresh a (Nat.xor full a)

noncomputable def stepBin (N low full zt : ℕ)
    (sk : List ℕ → List ℕ → List ℕ → Bool → ℕ → List ℕ → List ℕ → Bool)
    (ws ms un : List ℕ) (nn : Bool) (v0 : ℕ) (fresh : List ℕ) (a b z : ℕ) : Bool :=
  (Nat.ble v0 z || (memb a fresh || memb b fresh)) &&
    (!(Nat.beq z 0 || Nat.beq z full) &&
      (Nat.beq z zt ||
        (!(memb z ws) &&
          sk (z :: ws) (mk N low nn z :: ms) (z :: remv b (remv a un)) nn (z + 1) (z :: []) (z :: []))))

noncomputable def search (N low full zt : ℕ) :
    ℕ → List ℕ → List ℕ → List ℕ → Bool → ℕ → List ℕ → List ℕ → Bool :=
  @Nat.rec (fun _ => List ℕ → List ℕ → List ℕ → Bool → ℕ → List ℕ → List ℕ → Bool)
    (fun _ _ _ _ _ _ _ => false)
    (fun k sk ws ms un nn v0 fresh nc =>
      Nat.ble (len un) (cond nn (k + 1) (k + 2)) &&
      (cover low ms (cond nn (k + 1) (k + 2) - len un) (need0 N low nn un) &&
        (cond nn (notAll (stepNot N low full zt sk ws un v0 fresh) nc) false
          || outer (stepBin N low full zt sk ws ms un nn v0 fresh) ws)))


-- the pair positions of a target, the expansion of a table, the root of the search
def trues (T : ℕ) : List ℕ := (List.range 32).filter fun p => Nat.testBit T p
def falses (T : ℕ) : List ℕ := (List.range 32).filter fun p => !Nat.testBit T p
def pis (T : ℕ) : List ℕ :=
  ((trues T).flatMap fun p => (falses T).map fun _ => p) ++
  ((trues T).flatMap fun _ => (falses T).map fun q => q)
def expand (pi : List ℕ) (t : ℕ) : ℕ := pi.foldr (fun p acc => Nat.bit (Nat.testBit t p) acc) 0
def base32 : List ℕ := [0xAAAAAAAA, 0xCCCCCCCC, 0xF0F0F0F0, 0xFF00FF00, 0xFFFF0000]
def pN (T : ℕ) : ℕ := (trues T).length * (falses T).length
def pLow (T : ℕ) : ℕ := 2 ^ pN T - 1
def pFull (T : ℕ) : ℕ := 2 ^ (2 * pN T) - 1
def ev (T i : ℕ) : ℕ := expand (pis T) (base32.getD i 0)
def rootWs (T : ℕ) : List ℕ := [ev T 0, ev T 1, ev T 2, ev T 3, ev T 4]

noncomputable def sAt (T k : ℕ) : List ℕ → List ℕ → List ℕ → Bool → ℕ → List ℕ → List ℕ → Bool :=
  search (pN T) (pLow T) (pFull T) (pLow T) k

noncomputable def notAt (T k i : ℕ) : Bool :=
  stepNot (pN T) (pLow T) (pFull T) (pLow T) (sAt T k) (rootWs T) [] 0 [] (ev T i)

noncomputable def binAt (T k i j : ℕ) (o : Bool) : Bool :=
  stepBin (pN T) (pLow T) (pFull T) (pLow T) (sAt T k) (rootWs T)
    (mapMk (pN T) (pLow T) true (rootWs T)) [] true 0 []
    (ev T i) (ev T j) (cond o (Nat.lor (ev T i) (ev T j)) (Nat.land (ev T i) (ev T j)))

noncomputable def rootRun (T k : ℕ) : Bool :=
  sAt T k (rootWs T) (mapMk (pN T) (pLow T) true (rootWs T)) [] true 0 [] (rootWs T)

noncomputable def rootRun0 (T k : ℕ) : Bool :=
  sAt T k (rootWs T) (mapMk (pN T) (pLow T) false (rootWs T)) [] false 0 [] []

theorem land_eq (a b : ℕ) : Nat.land a b = a &&& b := rfl
theorem lor_eq (a b : ℕ) : Nat.lor a b = a ||| b := rfl
theorem xor_eq (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
theorem shr_eq (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
theorem mod_eq (a b : ℕ) : Nat.mod a b = a % b := rfl
theorem pow_eq (a b : ℕ) : Nat.pow a b = a ^ b := rfl

theorem beq_iff (a b : ℕ) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem beq_false_iff (a b : ℕ) : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, beq_iff]

theorem ble_iff (a b : ℕ) : Nat.ble a b = true ↔ a ≤ b :=
  ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩

theorem memb_nil (z : ℕ) : memb z [] = false := rfl
theorem memb_cons (z w : ℕ) (ws : List ℕ) : memb z (w :: ws) = (Nat.beq w z || memb z ws) := rfl

theorem memb_iff (z : ℕ) (ws : List ℕ) : memb z ws = true ↔ z ∈ ws := by
  induction ws with
  | nil => rw [memb_nil]; simp
  | cons w ws ih =>
    rw [memb_cons, Bool.or_eq_true, ih, beq_iff, List.mem_cons]
    exact ⟨fun h => h.imp Eq.symm id, fun h => h.imp Eq.symm id⟩

theorem memb_false_iff (z : ℕ) (ws : List ℕ) : memb z ws = false ↔ z ∉ ws := by
  rw [← Bool.not_eq_true, memb_iff]

theorem remv_nil (a : ℕ) : remv a [] = [] := rfl
theorem remv_cons (a u : ℕ) (un : List ℕ) :
    remv a (u :: un) = cond (Nat.beq u a) (remv a un) (u :: remv a un) := rfl

theorem remv_eq (a : ℕ) (un : List ℕ) : remv a un = un.filter (fun u => decide (u ≠ a)) := by
  induction un with
  | nil => rfl
  | cons u un ih =>
    rw [remv_cons, ih]
    by_cases h : u = a
    · have hb : Nat.beq u a = true := (beq_iff u a).2 h
      rw [hb]; simp [h]
    · have hb : Nat.beq u a = false := (beq_false_iff u a).2 h
      rw [hb]; simp [h]

theorem mem_remv (x a : ℕ) (un : List ℕ) : x ∈ remv a un ↔ x ∈ un ∧ x ≠ a := by
  rw [remv_eq]; simp

theorem nodup_remv (a : ℕ) (un : List ℕ) (h : un.Nodup) : (remv a un).Nodup := by
  rw [remv_eq]; exact h.filter _

theorem len_eq (l : List ℕ) : len l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : len (a :: l) = len l + 1 := rfl
    rw [e, ih]; rfl

theorem mapMk_eq (N low : ℕ) (nn : Bool) (l : List ℕ) : mapMk N low nn l = l.map (mk N low nn) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : mapMk N low nn (a :: l) = mk N low nn a :: mapMk N low nn l := rfl
    rw [e, ih]; rfl

theorem notAll_nil (g : ℕ → Bool) : notAll g [] = false := rfl
theorem notAll_cons (g : ℕ → Bool) (a : ℕ) (nc : List ℕ) : notAll g (a :: nc) = (g a || notAll g nc) := rfl

theorem notAll_iff (g : ℕ → Bool) (nc : List ℕ) : notAll g nc = true ↔ ∃ a ∈ nc, g a = true := by
  induction nc with
  | nil => rw [notAll_nil]; simp
  | cons a nc ih => rw [notAll_cons, Bool.or_eq_true, ih]; simp

theorem inner_nil (h : ℕ → ℕ → ℕ → Bool) (a : ℕ) : inner h a [] = false := rfl
theorem inner_cons (h : ℕ → ℕ → ℕ → Bool) (a b : ℕ) (rest : List ℕ) :
    inner h a (b :: rest) = (h a b (Nat.land a b) || (h a b (Nat.lor a b) || inner h a rest)) := rfl

theorem inner_iff (h : ℕ → ℕ → ℕ → Bool) (a : ℕ) (rest : List ℕ) :
    inner h a rest = true ↔
      ∃ b ∈ rest, h a b (Nat.land a b) = true ∨ h a b (Nat.lor a b) = true := by
  induction rest with
  | nil => rw [inner_nil]; simp
  | cons b rest ih =>
    rw [inner_cons, Bool.or_eq_true, Bool.or_eq_true, ih]
    simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

theorem outer_nil (h : ℕ → ℕ → ℕ → Bool) : outer h [] = false := rfl
theorem outer_cons (h : ℕ → ℕ → ℕ → Bool) (w : ℕ) (ws : List ℕ) :
    outer h (w :: ws) = (inner h w ws || outer h ws) := rfl

theorem outer_of_sublist (h : ℕ → ℕ → ℕ → Bool) (ws : List ℕ) (a b : ℕ)
    (hs : List.Sublist [a, b] ws)
    (hh : h a b (Nat.land a b) = true ∨ h a b (Nat.lor a b) = true) : outer h ws = true := by
  induction ws with
  | nil => cases hs
  | cons w ws ih =>
    rw [outer_cons, Bool.or_eq_true]
    cases hs with
    | cons _ hs' => exact Or.inr (ih hs')
    | cons_cons _ hs' =>
      left
      rw [inner_iff]
      exact ⟨b, List.singleton_sublist.1 hs', hh⟩

theorem pair_sublist (ws : List ℕ) (a b : ℕ) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a ≠ b) :
    List.Sublist [a, b] ws ∨ List.Sublist [b, a] ws := by
  induction ws with
  | nil => cases ha
  | cons w ws ih =>
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with h | hb'
      · exact absurd h.symm hab
      · exact Or.inl (List.Sublist.cons_cons _ (List.singleton_sublist.2 hb'))
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact Or.inr (List.Sublist.cons_cons _ (List.singleton_sublist.2 ha'))
      · rcases ih ha' hb' with h | h
        · exact Or.inl (List.Sublist.cons _ h)
        · exact Or.inr (List.Sublist.cons _ h)

theorem search_zero (N low full zt : ℕ) (ws ms un : List ℕ) (nn : Bool) (v0 : ℕ) (fresh nc : List ℕ) :
    search N low full zt 0 ws ms un nn v0 fresh nc = false := rfl

theorem search_succ (N low full zt k : ℕ) (ws ms un : List ℕ) (nn : Bool) (v0 : ℕ) (fresh nc : List ℕ) :
    search N low full zt (k + 1) ws ms un nn v0 fresh nc =
      (Nat.ble (len un) (cond nn (k + 1) (k + 2)) &&
      (cover low ms (cond nn (k + 1) (k + 2) - len un) (need0 N low nn un) &&
        (cond nn (notAll (stepNot N low full zt (search N low full zt k) ws un v0 fresh) nc) false
          || outer (stepBin N low full zt (search N low full zt k) ws ms un nn v0 fresh) ws))) := rfl

theorem pow_sub_add (N : ℕ) : 2 ^ N - 1 + 1 = 2 ^ N := Nat.sub_add_cancel Nat.one_le_two_pow

theorem mGen_bit (N z i : ℕ) (hi : i < N) :
    (mGen N (2 ^ N - 1) z).testBit i = (z.testBit i ^^ z.testBit (N + i)) := by
  unfold mGen
  rw [mod_eq, shr_eq, xor_eq, pow_sub_add, Nat.testBit_xor, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  simp [hi]

theorem mMono_bit (N z i : ℕ) (hi : i < N) :
    (mMono N (2 ^ N - 1) z).testBit i = (z.testBit i && !z.testBit (N + i)) := by
  unfold mMono
  rw [land_eq, mod_eq, shr_eq, xor_eq, pow_sub_add, Nat.testBit_and, Nat.testBit_mod_two_pow,
    Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  simp [hi]

theorem need0_nil (N low : ℕ) (nn : Bool) : need0 N low nn [] = low := rfl
theorem need0_cons (N low : ℕ) (nn : Bool) (u : ℕ) (un : List ℕ) :
    need0 N low nn (u :: un) = Nat.land (need0 N low nn un) (Nat.xor (mk N low nn u) low) := rfl

theorem need0_bit (N : ℕ) (nn : Bool) (un : List ℕ) (i : ℕ) :
    (need0 N (2 ^ N - 1) nn un).testBit i = true ↔
      i < N ∧ ∀ u ∈ un, (mk N (2 ^ N - 1) nn u).testBit i = false := by
  induction un with
  | nil => rw [need0_nil, Nat.testBit_two_pow_sub_one]; simp
  | cons u un ih =>
    rw [need0_cons, land_eq, xor_eq, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
      Bool.and_eq_true, ih]
    constructor
    · rintro ⟨⟨hi, h⟩, hx⟩
      refine ⟨hi, ?_⟩
      intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · simpa [hi] using hx
      · exact h v hv
    · rintro ⟨hi, h⟩
      refine ⟨⟨hi, fun v hv => h v (List.mem_cons_of_mem _ hv)⟩, ?_⟩
      have := h u List.mem_cons_self
      simp [hi, this]

theorem scan_nil (bit : ℕ) (k : ℕ → Bool) : scan bit k [] = false := rfl
theorem scan_cons (bit : ℕ) (k : ℕ → Bool) (m : ℕ) (ms : List ℕ) :
    scan bit k (m :: ms) =
      @Nat.rec (fun _ => Bool) (scan bit k ms) (fun _ _ => k m || scan bit k ms) (Nat.land m bit) := rfl

theorem scan_true (bit : ℕ) (k : ℕ → Bool) (ms : List ℕ) (m : ℕ) (hm : m ∈ ms)
    (hb : Nat.land m bit ≠ 0) (hk : k m = true) : scan bit k ms = true := by
  induction ms with
  | nil => cases hm
  | cons m' ms ih =>
    rw [scan_cons]
    rcases List.mem_cons.1 hm with rfl | hm'
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hb
      rw [hn]
      show (k m || scan bit k ms) = true
      rw [hk]; rfl
    · have h := ih hm'
      cases hc : Nat.land m' bit with
      | zero => exact h
      | succ n =>
        show (k m' || scan bit k ms) = true
        rw [h]; simp

theorem cover_zero (low : ℕ) (ms : List ℕ) (need : ℕ) : cover low ms 0 need = Nat.beq need 0 := rfl
theorem cover_succ (low : ℕ) (ms : List ℕ) (b need : ℕ) :
    cover low ms (b + 1) need =
      @Nat.rec (fun _ => Bool) true
        (fun _ _ =>
          scan (Nat.land need (Nat.xor need (need - 1)))
            (fun m => cover low ms b (Nat.land need (Nat.xor m low))) ms)
        need := rfl

-- the bits of x that x - 1 does not have: never empty for x > 0
theorem iso_ne_zero (x : ℕ) (hx : x ≠ 0) : x &&& (x ^^^ (x - 1)) ≠ 0 := by
  intro h
  have hall : ∀ i, x.testBit i = true → (x - 1).testBit i = true := by
    intro i hi
    have := congrArg (fun y => y.testBit i) h
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, hi, Bool.true_and] at this
    cases hb : (x - 1).testBit i with
    | true => rfl
    | false => rw [hb] at this; simp at this
  have he : x &&& (x - 1) = x := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : x.testBit i with
    | false => rfl
    | true => rw [hall i hi]; rfl
  have hle : x &&& (x - 1) ≤ x - 1 := Nat.and_le_right
  rw [he] at hle
  omega

theorem cover_complete (N : ℕ) (ms : List ℕ) :
    ∀ (b need : ℕ) (L : List ℕ), L.length ≤ b → (∀ m ∈ L, m ∈ ms) →
      (∀ i, need.testBit i = true → i < N ∧ ∃ m ∈ L, m.testBit i = true) →
      cover (2 ^ N - 1) ms b need = true := by
  intro b
  induction b with
  | zero =>
    intro need L hL _ hc
    have hLnil : L = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hL)
    subst hLnil
    rw [cover_zero, beq_iff]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_contra h
    obtain ⟨_, m, hm, _⟩ := hc i (by simpa using h)
    cases hm
  | succ b ih =>
    intro need L hL hms hc
    rw [cover_succ]
    rcases Nat.eq_zero_or_pos need with h0 | hpos
    · subst h0; rfl
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hpos)
      subst hn
      show scan (Nat.land (n + 1) (Nat.xor (n + 1) (n + 1 - 1)))
        (fun m => cover (2 ^ N - 1) ms b (Nat.land (n + 1) (Nat.xor m (2 ^ N - 1)))) ms = true
      have hiso := iso_ne_zero (n + 1) (Nat.succ_ne_zero n)
      obtain ⟨i0, hi0, _⟩ := Nat.exists_most_significant_bit hiso
      have hbit : (n + 1).testBit i0 = true := by
        rw [Nat.testBit_and, Bool.and_eq_true] at hi0
        exact hi0.1
      obtain ⟨_, m0, hm0, hm0b⟩ := hc _ hbit
      apply scan_true _ _ _ m0 (hms m0 hm0)
      · rw [land_eq, land_eq, xor_eq]
        intro hz
        have := congrArg (fun y => y.testBit i0) hz
        simp only [Nat.testBit_and, Nat.zero_testBit, hm0b, Bool.true_and] at this
        rw [Nat.testBit_and] at hi0
        rw [hi0] at this
        exact Bool.noConfusion this
      · apply ih _ (L.erase m0)
        · rw [List.length_erase_of_mem hm0]; omega
        · intro m hm; exact hms m (List.mem_of_mem_erase hm)
        · intro i hi
          rw [land_eq, xor_eq, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
            Bool.and_eq_true] at hi
          obtain ⟨hi1, hi2⟩ := hi
          obtain ⟨hiN', m, hm, hmb⟩ := hc i hi1
          refine ⟨hiN', m, ?_, hmb⟩
          have hne : m ≠ m0 := by
            rintro rfl
            simp [hiN', hmb] at hi2
          exact (List.mem_erase_of_ne hne).2 hm

abbrev Step := Bool × ℕ × ℕ × ℕ

def okStep (full : ℕ) (s : Step) : Prop :=
  (s.1 = true → s.2.2.1 = s.2.1 ∧ s.2.2.2 = Nat.xor full s.2.1) ∧
  (s.1 = false → s.2.2.2 = Nat.land s.2.1 s.2.2.1 ∨ s.2.2.2 = Nat.lor s.2.1 s.2.2.1)

def Valid (full : ℕ) : List ℕ → List Step → Prop
  | _, [] => True
  | W, s :: D => okStep full s ∧ s.2.1 ∈ W ∧ s.2.2.1 ∈ W ∧ s.2.2.2 ∉ W ∧ s.2.2.2 ≠ 0 ∧ s.2.2.2 ≠ full ∧
      Valid full (s.2.2.2 :: W) D

def reads (D : List Step) (x : ℕ) : Prop := ∃ t ∈ D, t.2.1 = x ∨ t.2.2.1 = x

def Used (zt : ℕ) : List Step → Prop
  | [] => True
  | s :: D => (s.2.2.2 = zt ∨ reads D s.2.2.2) ∧ Used zt D

def outs (D : List Step) : List ℕ := D.map (fun s => s.2.2.2)
def nots (D : List Step) : ℕ := D.countP (fun s => s.1)
def bins (D : List Step) : ℕ := D.countP (fun s => !s.1)

def del (t : Step) : List Step → List Step
  | [] => []
  | s :: D => if s = t then D else s :: del t D

theorem valid_cons (full : ℕ) (W : List ℕ) (s : Step) (D : List Step) :
    Valid full W (s :: D) ↔ (okStep full s ∧ s.2.1 ∈ W ∧ s.2.2.1 ∈ W ∧ s.2.2.2 ∉ W ∧ s.2.2.2 ≠ 0 ∧
      s.2.2.2 ≠ full ∧ Valid full (s.2.2.2 :: W) D) := Iff.rfl

theorem used_cons (zt : ℕ) (s : Step) (D : List Step) :
    Used zt (s :: D) ↔ ((s.2.2.2 = zt ∨ reads D s.2.2.2) ∧ Used zt D) := Iff.rfl

theorem reads_cons (s : Step) (D : List Step) (x : ℕ) :
    reads (s :: D) x ↔ (s.2.1 = x ∨ s.2.2.1 = x) ∨ reads D x := by
  unfold reads; simp

theorem outs_cons (s : Step) (D : List Step) : outs (s :: D) = s.2.2.2 :: outs D := rfl

theorem mem_outs (D : List Step) (z : ℕ) : z ∈ outs D ↔ ∃ t ∈ D, t.2.2.2 = z := by
  unfold outs; simp

theorem nots_cons (s : Step) (D : List Step) : nots (s :: D) = nots D + (if s.1 = true then 1 else 0) := by
  unfold nots; rw [List.countP_cons]

theorem bins_cons (s : Step) (D : List Step) : bins (s :: D) = bins D + (if s.1 = true then 0 else 1) := by
  unfold bins; rw [List.countP_cons]; cases s.1 <;> simp

theorem nots_add_bins (D : List Step) : nots D + bins D = D.length := by
  induction D with
  | nil => rfl
  | cons s D ih =>
    rw [nots_cons, bins_cons, List.length_cons]
    cases s.1 <;> simp <;> omega

theorem valid_congr (full : ℕ) : ∀ (D : List Step) (W1 W2 : List ℕ), (∀ x, x ∈ W1 ↔ x ∈ W2) →
    Valid full W1 D → Valid full W2 D := by
  intro D
  induction D with
  | nil => intro _ _ _ _; trivial
  | cons s D ih =>
    intro W1 W2 h hv
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := (valid_cons full W1 s D).1 hv
    refine (valid_cons full W2 s D).2 ⟨h1, (h _).1 h2, (h _).1 h3, fun hc => h4 ((h _).2 hc), h5, h6, ?_⟩
    apply ih (s.2.2.2 :: W1) (s.2.2.2 :: W2) _ h7
    intro x
    simp only [List.mem_cons]
    rw [h x]

theorem valid_mem (full : ℕ) : ∀ (D : List Step) (W : List ℕ), Valid full W D → ∀ t ∈ D,
    okStep full t ∧ t.2.2.2 ∉ W ∧ t.2.2.2 ≠ 0 ∧ t.2.2.2 ≠ full := by
  intro D
  induction D with
  | nil => intro _ _ t ht; cases ht
  | cons s D ih =>
    intro W hv t ht
    obtain ⟨h1, _, _, h4, h5, h6, h7⟩ := (valid_cons full W s D).1 hv
    rcases List.mem_cons.1 ht with rfl | ht'
    · exact ⟨h1, h4, h5, h6⟩
    · obtain ⟨a, b, c, d⟩ := ih _ h7 t ht'
      exact ⟨a, fun hc => b (List.mem_cons_of_mem _ hc), c, d⟩

theorem valid_ne_head (full : ℕ) (D : List Step) (W : List ℕ) (x : ℕ) (hv : Valid full (x :: W) D)
    (t : Step) (ht : t ∈ D) : t.2.2.2 ≠ x := by
  intro h
  exact (valid_mem full D _ hv t ht).2.1 (h ▸ List.mem_cons_self)

theorem valid_nodup (full : ℕ) : ∀ (D : List Step) (W : List ℕ), Valid full W D → (outs D).Nodup := by
  intro D
  induction D with
  | nil => intro _ _; exact List.nodup_nil
  | cons s D ih =>
    intro W hv
    obtain ⟨_, _, _, _, _, _, h7⟩ := (valid_cons full W s D).1 hv
    rw [outs_cons, List.nodup_cons]
    refine ⟨?_, ih _ h7⟩
    intro hm
    obtain ⟨t, ht, hz⟩ := (mem_outs D _).1 hm
    exact valid_ne_head full D W _ h7 t ht hz

theorem step_eq_of_out (full : ℕ) (D : List Step) (W : List ℕ) (hv : Valid full W D) (t t' : Step)
    (ht : t ∈ D) (ht' : t' ∈ D) (h : t.2.2.2 = t'.2.2.2) : t = t' :=
  List.inj_on_of_nodup_map (valid_nodup full D W hv) ht ht' h

theorem del_cons (t s : Step) (D : List Step) : del t (s :: D) = if s = t then D else s :: del t D := rfl

theorem mem_of_mem_del (t x : Step) : ∀ D : List Step, x ∈ del t D → x ∈ D := by
  intro D
  induction D with
  | nil => intro h; cases h
  | cons s D ih =>
    intro h
    rw [del_cons] at h
    by_cases hs : s = t
    · rw [if_pos hs] at h; exact List.mem_cons_of_mem _ h
    · rw [if_neg hs] at h
      rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h')

theorem mem_del_of_ne (t x : Step) (hx : x ≠ t) : ∀ D : List Step, x ∈ D → x ∈ del t D := by
  intro D
  induction D with
  | nil => intro h; cases h
  | cons s D ih =>
    intro h
    rw [del_cons]
    by_cases hs : s = t
    · rw [if_pos hs]
      rcases List.mem_cons.1 h with rfl | h'
      · exact absurd hs hx
      · exact h'
    · rw [if_neg hs]
      rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h')

theorem length_del (t : Step) : ∀ D : List Step, t ∈ D → (del t D).length + 1 = D.length := by
  intro D
  induction D with
  | nil => intro h; cases h
  | cons s D ih =>
    intro h
    rw [del_cons]
    by_cases hs : s = t
    · rw [if_pos hs]; rfl
    · rw [if_neg hs, List.length_cons, List.length_cons]
      rcases List.mem_cons.1 h with rfl | h'
      · exact absurd rfl hs
      · rw [ih h']

theorem nots_del (t : Step) : ∀ D : List Step, t ∈ D →
    nots (del t D) + (if t.1 = true then 1 else 0) = nots D := by
  intro D
  induction D with
  | nil => intro h; cases h
  | cons s D ih =>
    intro h
    rw [del_cons]
    by_cases hs : s = t
    · rw [if_pos hs, nots_cons, hs]
    · rw [if_neg hs, nots_cons, nots_cons]
      rcases List.mem_cons.1 h with rfl | h'
      · exact absurd rfl hs
      · rw [← ih h']; omega

theorem valid_del (full : ℕ) : ∀ (D : List Step) (W : List ℕ) (t : Step), Valid full W D → t ∈ D →
    t.2.1 ∈ W → t.2.2.1 ∈ W → Valid full (t.2.2.2 :: W) (del t D) := by
  intro D
  induction D with
  | nil => intro _ _ _ ht; cases ht
  | cons s D ih =>
    intro W t hv ht ha hb
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := (valid_cons full W s D).1 hv
    rw [del_cons]
    by_cases hs : s = t
    · rw [if_pos hs]; rw [← hs]; exact h7
    · rw [if_neg hs]
      have ht' : t ∈ D := by
        rcases List.mem_cons.1 ht with rfl | h'
        · exact absurd rfl hs
        · exact h'
      have hne : t.2.2.2 ≠ s.2.2.2 := valid_ne_head full D W _ h7 t ht'
      refine (valid_cons full _ s _).2 ⟨h1, List.mem_cons_of_mem _ h2, List.mem_cons_of_mem _ h3, ?_, h5, h6, ?_⟩
      · intro hc
        rcases List.mem_cons.1 hc with h | h
        · exact hne h.symm
        · exact h4 h
      · have := ih (s.2.2.2 :: W) t h7 ht' (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb)
        apply valid_congr full _ _ _ _ this
        intro x
        simp only [List.mem_cons]
        tauto

theorem used_del (full zt : ℕ) : ∀ (D : List Step) (W : List ℕ) (t : Step), Valid full W D → Used zt D →
    t ∈ D → t.2.1 ∈ W → t.2.2.1 ∈ W → Used zt (del t D) := by
  intro D
  induction D with
  | nil => intro _ _ _ _ ht; cases ht
  | cons s D ih =>
    intro W t hv hu ht ha hb
    obtain ⟨_, _, _, h4, _, _, h7⟩ := (valid_cons full W s D).1 hv
    obtain ⟨hu1, hu2⟩ := (used_cons zt s D).1 hu
    rw [del_cons]
    by_cases hs : s = t
    · rw [if_pos hs]; exact hu2
    · rw [if_neg hs]
      have ht' : t ∈ D := by
        rcases List.mem_cons.1 ht with rfl | h'
        · exact absurd rfl hs
        · exact h'
      refine (used_cons zt s _).2 ⟨?_, ih (s.2.2.2 :: W) t h7 hu2 ht' (List.mem_cons_of_mem _ ha)
        (List.mem_cons_of_mem _ hb)⟩
      rcases hu1 with h | ⟨t', ht'D, hr⟩
      · exact Or.inl h
      · right
        refine ⟨t', mem_del_of_ne t t' ?_ D ht'D, hr⟩
        rintro rfl
        rcases hr with h | h
        · exact h4 (h ▸ ha)
        · exact h4 (h ▸ hb)

theorem used_reads (zt : ℕ) : ∀ (D : List Step) (t : Step), Used zt D → t ∈ D →
    t.2.2.2 = zt ∨ reads D t.2.2.2 := by
  intro D
  induction D with
  | nil => intro _ _ ht; cases ht
  | cons s D ih =>
    intro t hu ht
    obtain ⟨hu1, hu2⟩ := (used_cons zt s D).1 hu
    rcases List.mem_cons.1 ht with rfl | ht'
    · rcases hu1 with h | h
      · exact Or.inl h
      · exact Or.inr ((reads_cons _ D _).2 (Or.inr h))
    · rcases ih t hu2 ht' with h | h
      · exact Or.inl h
      · exact Or.inr ((reads_cons s D _).2 (Or.inr h))

open Classical in
noncomputable def needSet (zt : ℕ) : List Step → Finset ℕ
  | [] => {zt}
  | s :: D => if s.2.2.2 ∈ needSet zt D then (needSet zt D).erase s.2.2.2 ∪ {s.2.1, s.2.2.1} else needSet zt D

theorem needSet_nil (zt : ℕ) : needSet zt [] = {zt} := rfl

theorem needSet_cons (zt : ℕ) (s : Step) (D : List Step) :
    needSet zt (s :: D) =
      if s.2.2.2 ∈ needSet zt D then (needSet zt D).erase s.2.2.2 ∪ {s.2.1, s.2.2.1} else needSet zt D := by
  simp only [needSet]

theorem needSet_card (zt : ℕ) : ∀ D : List Step, (∀ t ∈ D, t.1 = true → t.2.2.1 = t.2.1) →
    (needSet zt D).card ≤ 1 + bins D := by
  intro D
  induction D with
  | nil => intro _; rw [needSet_nil]; simp [bins]
  | cons s D ih =>
    intro h
    have ih' := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    rw [needSet_cons, bins_cons]
    by_cases hz : s.2.2.2 ∈ needSet zt D
    · rw [if_pos hz]
      have h1 : ((needSet zt D).erase s.2.2.2).card + 1 = (needSet zt D).card :=
        Finset.card_erase_add_one hz
      have h2 := Finset.card_union_le ((needSet zt D).erase s.2.2.2) {s.2.1, s.2.2.1}
      by_cases hk : s.1 = true
      · have hb := h s List.mem_cons_self hk
        rw [hb] at h2 ⊢
        have h3 : ({s.2.1, s.2.1} : Finset ℕ).card ≤ 1 := by simp
        rw [if_pos hk]; omega
      · have h3 : ({s.2.1, s.2.2.1} : Finset ℕ).card ≤ 2 := Finset.card_le_two
        rw [if_neg hk]; omega
    · rw [if_neg hz]
      by_cases hk : s.1 = true
      · rw [if_pos hk]; omega
      · rw [if_neg hk]; omega

theorem needSet_keep (zt : ℕ) (s : Step) (D : List Step) (x : ℕ) (hx : x ∈ needSet zt D)
    (hne : x ≠ s.2.2.2) : x ∈ needSet zt (s :: D) := by
  rw [needSet_cons]
  by_cases hz : s.2.2.2 ∈ needSet zt D
  · rw [if_pos hz]
    exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hx⟩)
  · rw [if_neg hz]; exact hx

theorem zt_mem_needSet (zt : ℕ) : ∀ D : List Step, zt ∉ outs D → zt ∈ needSet zt D := by
  intro D
  induction D with
  | nil => intro _; rw [needSet_nil]; exact Finset.mem_singleton_self zt
  | cons s D ih =>
    intro h
    rw [outs_cons, List.mem_cons, not_or] at h
    exact needSet_keep zt s D zt (ih h.2) h.1

theorem reads_mem_needSet (zt : ℕ) : ∀ D : List Step, (outs D).Nodup → Used zt D →
    ∀ x, x ∉ outs D → reads D x → x ∈ needSet zt D := by
  intro D
  induction D with
  | nil => intro _ _ x _ hr; obtain ⟨t, ht, _⟩ := hr; cases ht
  | cons s D ih =>
    intro hnd hu x hx hr
    rw [outs_cons, List.nodup_cons] at hnd
    obtain ⟨hu1, hu2⟩ := (used_cons zt s D).1 hu
    rw [outs_cons, List.mem_cons, not_or] at hx
    have hz : s.2.2.2 ∈ needSet zt D := by
      rcases hu1 with h | h
      · rw [h]; exact zt_mem_needSet zt D (h ▸ hnd.1)
      · exact ih hnd.2 hu2 _ hnd.1 h
    rw [needSet_cons, if_pos hz]
    rcases (reads_cons s D x).1 hr with h | h
    · apply Finset.mem_union_right
      rcases h with h | h
      · rw [h]; simp
      · rw [h]; simp
    · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hx.1, ih hnd.2 hu2 x hx.2 h⟩)

theorem prop_outs (full : ℕ) (P : ℕ → Prop) : ∀ (D : List Step) (W : List ℕ), Valid full W D →
    (∀ x ∈ W, reads D x → P x) →
    (∀ t ∈ D, P t.2.1 → P t.2.2.1 → P t.2.2.2) → ∀ t ∈ D, P t.2.2.2 := by
  intro D
  induction D with
  | nil => intro _ _ _ _ t ht; cases ht
  | cons s D ih =>
    intro W hv hW hstep t ht
    obtain ⟨_, h2, h3, _, _, _, h7⟩ := (valid_cons full W s D).1 hv
    have hs : P s.2.2.2 :=
      hstep s List.mem_cons_self (hW _ h2 ((reads_cons s D _).2 (Or.inl (Or.inl rfl))))
        (hW _ h3 ((reads_cons s D _).2 (Or.inl (Or.inr rfl))))
    rcases List.mem_cons.1 ht with rfl | ht'
    · exact hs
    · apply ih (s.2.2.2 :: W) h7 _ (fun t' ht'' => hstep t' (List.mem_cons_of_mem _ ht'')) t ht'
      intro x hx hr
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact hs
      · exact hW x hx' ((reads_cons s D x).2 (Or.inr hr))

theorem nots_zero (D : List Step) (h : nots D = 0) : ∀ t ∈ D, t.1 = false := by
  induction D with
  | nil => intro t ht; cases ht
  | cons s D ih =>
    rw [nots_cons] at h
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht'
    · by_contra hc
      have : t.1 = true := by simpa using hc
      rw [if_pos this] at h; omega
    · exact ih (by omega) t ht'

-- the wires of W that the derivation reads are few, and they separate every pair
theorem ycard (full zt : ℕ) (W : List ℕ) (D : List Step) (hv : Valid full W D) (hu : Used zt D)
    (Y : Finset ℕ) (hY : ∀ y ∈ Y, y ∈ W ∧ reads D y) : Y.card ≤ 1 + bins D := by
  have hsub : Y ⊆ needSet zt D := by
    intro y hy
    obtain ⟨hyW, hyr⟩ := hY y hy
    apply reads_mem_needSet zt D (valid_nodup full D W hv) hu y _ hyr
    intro hc
    obtain ⟨t, ht, hz⟩ := (mem_outs D y).1 hc
    exact (valid_mem full D W hv t ht).2.1 (hz ▸ hyW)
  have hok : ∀ t ∈ D, t.1 = true → t.2.2.1 = t.2.1 := fun t ht hk =>
    ((valid_mem full D W hv t ht).1.1 hk).1
  exact (Finset.card_le_card hsub).trans (needSet_card zt D hok)

theorem separated (N : ℕ) (nn : Bool) (W : List ℕ) (D : List Step)
    (hv : Valid (2 ^ (2 * N) - 1) W D) (hz : 2 ^ N - 1 ∈ outs D)
    (hn : nots D = cond nn 1 0) (i : ℕ) (hi : i < N) :
    ∃ y ∈ W, reads D y ∧ (mk N (2 ^ N - 1) nn y).testBit i = true := by
  by_contra hcon
  have hcon' : ∀ y ∈ W, reads D y → (mk N (2 ^ N - 1) nn y).testBit i = false := by
    intro y hy hr
    by_contra hb
    exact hcon ⟨y, hy, hr, by simpa using hb⟩
  obtain ⟨t, ht, htz⟩ := (mem_outs D _).1 hz
  have hlow1 : (2 ^ N - 1).testBit i = true := by rw [Nat.testBit_two_pow_sub_one]; simp [hi]
  have hlow2 : (2 ^ N - 1).testBit (N + i) = false := by rw [Nat.testBit_two_pow_sub_one]; simp
  have hfull1 : (2 ^ (2 * N) - 1).testBit i = true := by
    rw [Nat.testBit_two_pow_sub_one]; simp; omega
  have hfull2 : (2 ^ (2 * N) - 1).testBit (N + i) = true := by
    rw [Nat.testBit_two_pow_sub_one]; simp; omega
  cases nn with
  | false =>
    have hall := nots_zero D hn
    have key := prop_outs (2 ^ (2 * N) - 1) (fun z => z.testBit i = true → z.testBit (N + i) = true) D W hv
      (by
        intro x hx hr
        have := hcon' x hx hr
        simp only [mk, cond] at this
        rw [mMono_bit N x i hi] at this
        intro h1
        simpa [h1] using this)
      (by
        intro s hs ha hb
        have hk := hall s hs
        have hok := (valid_mem _ D W hv s hs).1.2 hk
        rcases hok with h | h
        · rw [h, land_eq, Nat.testBit_and, Nat.testBit_and]
          intro h1
          simp only [Bool.and_eq_true] at h1 ⊢
          exact ⟨ha h1.1, hb h1.2⟩
        · rw [h, lor_eq, Nat.testBit_or, Nat.testBit_or]
          intro h1
          simp only [Bool.or_eq_true] at h1 ⊢
          exact h1.imp ha hb)
      t ht
    rw [htz] at key
    have := key hlow1
    rw [hlow2] at this
    exact Bool.false_ne_true this
  | true =>
    have key := prop_outs (2 ^ (2 * N) - 1) (fun z => z.testBit i = z.testBit (N + i)) D W hv
      (by
        intro x hx hr
        have := hcon' x hx hr
        simp only [mk, cond] at this
        rw [mGen_bit N x i hi] at this
        simpa using this)
      (by
        intro s hs ha hb
        have hok := (valid_mem _ D W hv s hs).1
        by_cases hk : s.1 = true
        · rw [(hok.1 hk).2, xor_eq, Nat.testBit_xor, Nat.testBit_xor, hfull1, hfull2, ha]
        · have hk' : s.1 = false := by simpa using hk
          rcases hok.2 hk' with h | h
          · rw [h, land_eq, Nat.testBit_and, Nat.testBit_and, ha, hb]
          · rw [h, lor_eq, Nat.testBit_or, Nat.testBit_or, ha, hb])
      t ht
    rw [htz, hlow1, hlow2] at key
    exact Bool.false_ne_true key.symm

def Inv (N k : ℕ) (ws ms un : List ℕ) (nn : Bool) (v0 : ℕ) (fresh nc : List ℕ) : Prop :=
  ∃ D : List Step,
    D.length ≤ k ∧ Valid (2 ^ (2 * N) - 1) ws D ∧ nots D = cond nn 1 0 ∧ (2 ^ N - 1) ∈ outs D ∧
    (∀ u ∈ un, reads D u) ∧ Used (2 ^ N - 1) D ∧
    (∀ t ∈ D, t.1 = false → t.2.1 ∈ ws → t.2.2.1 ∈ ws →
      v0 ≤ t.2.2.2 ∨ t.2.1 ∈ fresh ∨ t.2.2.1 ∈ fresh) ∧
    (nn = true → ∀ t ∈ D, t.1 = true → t.2.1 ∈ ws → t.2.1 ∈ nc) ∧
    ms = ws.map (mk N (2 ^ N - 1) nn) ∧ (∀ u ∈ un, u ∈ ws) ∧ un.Nodup

theorem prune_ok (N k : ℕ) (ws un : List ℕ) (nn : Bool) (D : List Step)
    (h1 : D.length ≤ k + 1) (hv : Valid (2 ^ (2 * N) - 1) ws D) (h3 : nots D = cond nn 1 0)
    (h4 : (2 ^ N - 1) ∈ outs D) (h5 : ∀ u ∈ un, reads D u) (h6 : Used (2 ^ N - 1) D)
    (h10 : ∀ u ∈ un, u ∈ ws) (h12 : un.Nodup) :
    un.length ≤ cond nn (k + 1) (k + 2) ∧
    cover (2 ^ N - 1) (ws.map (mk N (2 ^ N - 1) nn)) (cond nn (k + 1) (k + 2) - un.length)
      (need0 N (2 ^ N - 1) nn un) = true := by
  classical
  have hYf : ∀ y ∈ ws.toFinset.filter (fun y => reads D y), y ∈ ws ∧ reads D y := by
    intro y hy
    rw [Finset.mem_filter, List.mem_toFinset] at hy
    exact hy
  have hcard := ycard _ _ ws D hv h6 _ hYf
  have hb : 1 + bins D ≤ cond nn (k + 1) (k + 2) := by
    have := nots_add_bins D
    cases nn <;> simp at h3 ⊢ <;> omega
  have hsub : un.toFinset ⊆ ws.toFinset.filter (fun y => reads D y) := by
    intro u hu
    rw [List.mem_toFinset] at hu
    exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 (h10 u hu), h5 u hu⟩
  have hunc : un.toFinset.card = un.length := List.toFinset_card_of_nodup h12
  have hle := Finset.card_le_card hsub
  refine ⟨by omega, ?_⟩
  have hR := Finset.card_sdiff_add_card_eq_card hsub
  apply cover_complete N _ _ _
    (((ws.toFinset.filter (fun y => reads D y)) \ un.toFinset).toList.map (mk N (2 ^ N - 1) nn))
  · rw [List.length_map, Finset.length_toList]; omega
  · intro m hm
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hm
    rw [Finset.mem_toList, Finset.mem_sdiff] at hy
    exact List.mem_map.2 ⟨y, (hYf y hy.1).1, rfl⟩
  · intro i hi
    obtain ⟨hiN, hun⟩ := (need0_bit N nn un i).1 hi
    obtain ⟨y, hyW, hyr, hyb⟩ := separated N nn ws D hv h4 h3 i hiN
    refine ⟨hiN, mk N (2 ^ N - 1) nn y, ?_, hyb⟩
    apply List.mem_map.2 ⟨y, ?_, rfl⟩
    rw [Finset.mem_toList, Finset.mem_sdiff]
    refine ⟨Finset.mem_filter.2 ⟨List.mem_toFinset.2 hyW, hyr⟩, ?_⟩
    intro hc
    rw [List.mem_toFinset] at hc
    have := hun y hc
    rw [this] at hyb
    exact Bool.false_ne_true hyb

theorem del_facts (full zt : ℕ) (ws : List ℕ) (D : List Step) (t : Step)
    (hv : Valid full ws D) (hu : Used zt D) (ht : t ∈ D) (ha : t.2.1 ∈ ws) (hb : t.2.2.1 ∈ ws)
    (hz4 : zt ∈ outs D) (hne : t.2.2.2 ≠ zt) :
    Valid full (t.2.2.2 :: ws) (del t D) ∧ Used zt (del t D) ∧ zt ∈ outs (del t D) ∧
    reads (del t D) t.2.2.2 ∧
    (∀ u, reads D u → u ≠ t.2.1 → u ≠ t.2.2.1 → reads (del t D) u) ∧
    (del t D).length + 1 = D.length := by
  have hzW : t.2.2.2 ∉ ws := (valid_mem full D ws hv t ht).2.1
  refine ⟨valid_del full D ws t hv ht ha hb, used_del full zt D ws t hv hu ht ha hb, ?_, ?_, ?_,
    length_del t D ht⟩
  · obtain ⟨t', ht', hz⟩ := (mem_outs D zt).1 hz4
    refine (mem_outs _ zt).2 ⟨t', mem_del_of_ne t t' ?_ D ht', hz⟩
    intro e
    rw [e] at hz
    exact hne hz
  · rcases used_reads zt D t hu ht with h | ⟨t', ht', hr⟩
    · exact absurd h hne
    · refine ⟨t', mem_del_of_ne t t' ?_ D ht', hr⟩
      intro e
      rw [e] at hr
      rcases hr with h | h
      · exact hzW (h ▸ ha)
      · exact hzW (h ▸ hb)
  · rintro u ⟨t', ht', hr⟩ h1 h2
    refine ⟨t', mem_del_of_ne t t' ?_ D ht', hr⟩
    intro e
    rw [e] at hr
    rcases hr with h | h
    · exact h1 h.symm
    · exact h2 h.symm

theorem exists_ready (full : ℕ) (ws : List ℕ) (D : List Step) (hv : Valid full ws D) (hne : D ≠ []) :
    ∃ s ∈ D, s.2.1 ∈ ws ∧ s.2.2.1 ∈ ws := by
  cases D with
  | nil => exact absurd rfl hne
  | cons s D =>
    obtain ⟨_, h2, h3, _⟩ := (valid_cons full ws s D).1 hv
    exact ⟨s, List.mem_cons_self, h2, h3⟩

theorem nots_pos (D : List Step) (t : Step) (ht : t ∈ D) (hk : t.1 = true) : 1 ≤ nots D := by
  unfold nots
  exact List.countP_pos_iff.2 ⟨t, ht, hk⟩

theorem search_complete (N : ℕ) :
    ∀ (k : ℕ) (ws ms un : List ℕ) (nn : Bool) (v0 : ℕ) (fresh nc : List ℕ),
      Inv N k ws ms un nn v0 fresh nc →
      search N (2 ^ N - 1) (2 ^ (2 * N) - 1) (2 ^ N - 1) k ws ms un nn v0 fresh nc = true := by
  intro k
  induction k with
  | zero =>
    rintro ws ms un nn v0 fresh nc ⟨D, h1, _, _, h4, _⟩
    have hD : D = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 h1)
    subst hD
    simp [outs] at h4
  | succ k ih =>
    rintro ws ms un nn v0 fresh nc ⟨D, h1, hv, h3, h4, h5, h6, h7, h8, h9, h10, h12⟩
    classical
    subst h9
    obtain ⟨hp1, hp2⟩ := prune_ok N k ws un nn D h1 hv h3 h4 h5 h6 h10 h12
    rw [search_succ, len_eq, (ble_iff _ _).2 hp1, hp2]
    simp only [Bool.true_and]
    have hDne : D ≠ [] := by
      intro h
      rw [h] at h4
      simp [outs] at h4
    by_cases hA : nn = true ∧ ∃ t ∈ D, t.1 = true ∧ t.2.1 ∈ ws
    · obtain ⟨hnn, t, ht, hk, ha⟩ := hA
      subst hnn
      obtain ⟨hok, hzW, hz0, hzf⟩ := valid_mem _ D ws hv t ht
      obtain ⟨hab, hz⟩ := hok.1 hk
      have hb : t.2.2.1 ∈ ws := by rw [hab]; exact ha
      rw [Bool.or_eq_true]
      left
      show notAll _ nc = true
      rw [notAll_iff]
      refine ⟨t.2.1, h8 rfl t ht hk ha, ?_⟩
      unfold stepNot notZ
      rw [← hz, (beq_false_iff _ _).2 hz0, (beq_false_iff _ _).2 hzf, (memb_false_iff _ _).2 hzW]
      simp only [Bool.or_false, Bool.not_false, Bool.true_and]
      by_cases hzt : t.2.2.2 = 2 ^ N - 1
      · rw [(beq_iff _ _).2 hzt]; rfl
      · rw [Bool.or_eq_true]
        right
        obtain ⟨dv, du, dz, dr, de, dl⟩ := del_facts _ _ ws D t hv h6 ht ha hb h4 hzt
        apply ih
        refine ⟨del t D, by omega, dv, ?_, dz, ?_, du, ?_, ?_, ?_, ?_, ?_⟩
        · have := nots_del t D ht
          rw [if_pos hk] at this
          simp at h3 ⊢
          omega
        · intro u hu
          rcases List.mem_cons.1 hu with rfl | hu
          · exact dr
          · obtain ⟨hu1, hu2⟩ := (mem_remv _ _ _).1 hu
            exact de u (h5 u hu1) hu2 (by rw [hab]; exact hu2)
        · intro t' ht' hk' ha' hb'
          rcases List.mem_cons.1 ha' with e | ha''
          · exact Or.inr (Or.inl (by rw [e]; exact List.mem_cons_self))
          · rcases List.mem_cons.1 hb' with e | hb''
            · exact Or.inr (Or.inr (by rw [e]; exact List.mem_cons_self))
            · rcases h7 t' (mem_of_mem_del t t' D ht') hk' ha'' hb'' with h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
              · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))
        · intro h; cases h
        · exact mapMk_eq _ _ _ _
        · intro u hu
          rcases List.mem_cons.1 hu with rfl | hu
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (h10 u ((mem_remv _ _ _).1 hu).1)
        · exact List.nodup_cons.2
            ⟨fun hc => hzW (h10 _ ((mem_remv _ _ _).1 hc).1), nodup_remv _ _ h12⟩
    · rw [Bool.or_eq_true]
      right
      obtain ⟨s0, hs0, hs0a, hs0b⟩ := exists_ready _ ws D hv hDne
      have hs0k : s0.1 = false := by
        by_contra hc
        have hc' : s0.1 = true := by simpa using hc
        have hpos := nots_pos D s0 hs0 hc'
        have hnn : nn = true := by
          cases nn with
          | true => rfl
          | false => simp at h3; omega
        exact hA ⟨hnn, s0, hs0, hc', hs0a⟩
      have hSne : (D.toFinset.filter
          (fun t : Step => t.1 = false ∧ t.2.1 ∈ ws ∧ t.2.2.1 ∈ ws)).Nonempty :=
        ⟨s0, Finset.mem_filter.2 ⟨List.mem_toFinset.2 hs0, hs0k, hs0a, hs0b⟩⟩
      obtain ⟨t, htS, hmin⟩ := Finset.exists_min_image _ (fun t : Step => t.2.2.2) hSne
      rw [Finset.mem_filter, List.mem_toFinset] at htS
      obtain ⟨ht, hk, ha, hb⟩ := htS
      obtain ⟨hok, hzW, hz0, hzf⟩ := valid_mem _ D ws hv t ht
      have hz := hok.2 hk
      have hne : t.2.1 ≠ t.2.2.1 := by
        intro e
        rcases hz with h | h
        · rw [e, land_eq, Nat.and_self] at h
          exact hzW (h ▸ hb)
        · rw [e, lor_eq, Nat.or_self] at h
          exact hzW (h ▸ hb)
      have key : ∀ a b : ℕ, ((a = t.2.1 ∧ b = t.2.2.1) ∨ (a = t.2.2.1 ∧ b = t.2.1)) →
          stepBin N (2 ^ N - 1) (2 ^ (2 * N) - 1) (2 ^ N - 1)
            (search N (2 ^ N - 1) (2 ^ (2 * N) - 1) (2 ^ N - 1) k) ws
            (ws.map (mk N (2 ^ N - 1) nn)) un nn v0 fresh a b t.2.2.2 = true := by
        intro a b hab'
        have hfr : v0 ≤ t.2.2.2 ∨ a ∈ fresh ∨ b ∈ fresh := by
          rcases h7 t ht hk ha hb with h | h | h
          · exact Or.inl h
          · rcases hab' with ⟨e1, _⟩ | ⟨_, e2⟩
            · exact Or.inr (Or.inl (e1 ▸ h))
            · exact Or.inr (Or.inr (e2 ▸ h))
          · rcases hab' with ⟨_, e2⟩ | ⟨e1, _⟩
            · exact Or.inr (Or.inr (e2 ▸ h))
            · exact Or.inr (Or.inl (e1 ▸ h))
        have c1 : (Nat.ble v0 t.2.2.2 || (memb a fresh || memb b fresh)) = true := by
          rcases hfr with h | h | h
          · rw [(ble_iff _ _).2 h]; rfl
          · rw [(memb_iff _ _).2 h]; simp
          · rw [(memb_iff _ _).2 h]; simp
        unfold stepBin
        rw [c1, (beq_false_iff _ _).2 hz0, (beq_false_iff _ _).2 hzf]
        simp only [Bool.or_false, Bool.not_false, Bool.true_and]
        by_cases hzt : t.2.2.2 = 2 ^ N - 1
        · rw [(beq_iff _ _).2 hzt]; rfl
        · rw [(beq_false_iff _ _).2 hzt, (memb_false_iff _ _).2 hzW]
          simp only [Bool.false_or, Bool.not_false, Bool.true_and]
          obtain ⟨dv, du, dz, dr, de, dl⟩ := del_facts _ _ ws D t hv h6 ht ha hb h4 hzt
          apply ih
          refine ⟨del t D, by omega, dv, ?_, dz, ?_, du, ?_, ?_, rfl, ?_, ?_⟩
          · have := nots_del t D ht
            rw [hk] at this
            simp at this
            omega
          · intro u hu
            rcases List.mem_cons.1 hu with rfl | hu
            · exact dr
            · obtain ⟨hu1, hub⟩ := (mem_remv _ _ _).1 hu
              obtain ⟨hu2, hua⟩ := (mem_remv _ _ _).1 hu1
              rcases hab' with ⟨e1, e2⟩ | ⟨e1, e2⟩
              · exact de u (h5 u hu2) (e1 ▸ hua) (e2 ▸ hub)
              · exact de u (h5 u hu2) (e2 ▸ hub) (e1 ▸ hua)
          · intro t' ht' hk' ha' hb'
            rcases List.mem_cons.1 ha' with e | ha''
            · exact Or.inr (Or.inl (by rw [e]; exact List.mem_cons_self))
            · rcases List.mem_cons.1 hb' with e | hb''
              · exact Or.inr (Or.inr (by rw [e]; exact List.mem_cons_self))
              · left
                have hmem : t' ∈ D := mem_of_mem_del t t' D ht'
                have h1' := hmin t' (Finset.mem_filter.2 ⟨List.mem_toFinset.2 hmem, hk', ha'', hb''⟩)
                have h2' : t'.2.2.2 ≠ t.2.2.2 := fun e =>
                  (valid_mem _ _ _ dv t' ht').2.1 (e ▸ List.mem_cons_self)
                have h1'' : t.2.2.2 ≤ t'.2.2.2 := h1'
                omega
          · intro hnn t' ht' hk' ha'
            rcases List.mem_cons.1 ha' with e | ha''
            · rw [e]; exact List.mem_cons_self
            · exact absurd ⟨hnn, t', mem_of_mem_del t t' D ht', hk', ha''⟩ hA
          · intro u hu
            rcases List.mem_cons.1 hu with rfl | hu
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _
                (h10 u ((mem_remv _ _ _).1 ((mem_remv _ _ _).1 hu).1).1)
          · exact List.nodup_cons.2
              ⟨fun hc => hzW (h10 _ ((mem_remv _ _ _).1 ((mem_remv _ _ _).1 hc).1).1),
                nodup_remv _ _ (nodup_remv _ _ h12)⟩
      rcases pair_sublist ws t.2.1 t.2.2.1 ha hb hne with hs | hs
      · apply outer_of_sublist _ ws t.2.1 t.2.2.1 hs
        rcases hz with h | h
        · left; rw [← h]; exact key _ _ (Or.inl ⟨rfl, rfl⟩)
        · right; rw [← h]; exact key _ _ (Or.inl ⟨rfl, rfl⟩)
      · apply outer_of_sublist _ ws t.2.2.1 t.2.1 hs
        rcases hz with h | h
        · left
          have e : Nat.land t.2.2.1 t.2.1 = t.2.2.2 := by
            rw [h, land_eq, land_eq, Nat.and_comm]
          rw [e]; exact key _ _ (Or.inr ⟨rfl, rfl⟩)
        · right
          have e : Nat.lor t.2.2.1 t.2.1 = t.2.2.2 := by
            rw [h, lor_eq, lor_eq, Nat.or_comm]
          rw [e]; exact key _ _ (Or.inr ⟨rfl, rfl⟩)

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

def gz (full : ℕ) (w : List ℕ) (g : Gate) : ℕ :=
  match g.op with
  | GateOp.and => (g.inputs.map fun i => w.getD i 0).foldr Nat.land full
  | GateOp.or => (g.inputs.map fun i => w.getD i 0).foldr Nat.lor 0
  | GateOp.not => Nat.xor full ((g.inputs.map fun i => w.getD i 0).headD 0)
  | _ => 0

def zrun (full : ℕ) (gates : List Gate) (w : List ℕ) : List ℕ :=
  gates.foldl (fun w g => w ++ [gz full w g]) w

theorem zrun_nil (full : ℕ) (w : List ℕ) : zrun full [] w = w := rfl
theorem zrun_cons (full : ℕ) (g : Gate) (gates : List Gate) (w : List ℕ) :
    zrun full (g :: gates) w = zrun full gates (w ++ [gz full w g]) := rfl

theorem getD_snoc {α : Type} (l : List α) (a d : α) (j : ℕ) :
    (l ++ [a]).getD j d = if j < l.length then l.getD j d else if j = l.length then a else d := by
  by_cases h1 : j < l.length
  · rw [if_pos h1, List.getD_append _ _ _ _ h1]
  · rw [if_neg h1]
    by_cases h2 : j = l.length
    · rw [if_pos h2, h2, List.getD_append_right _ _ _ _ (le_refl _)]; simp
    · rw [if_neg h2, List.getD_append_right _ _ _ _ (by omega)]
      obtain ⟨m, hm⟩ : ∃ m, j - l.length = m + 1 := ⟨j - l.length - 1, by omega⟩
      rw [hm]; simp

theorem gate_bit (full k : ℕ) (hf : full.testBit k = true) (wb : List Bool) (wz : List ℕ)
    (hR : ∀ j, wb.getD j false = (wz.getD j 0).testBit k) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    g.op.eval (g.inputs.map fun i => wb.getD i false) = (gz full wz g).testBit k := by
  have hand : ∀ l : List ℕ, ((l.map fun i => wb.getD i false).all id) =
      ((l.map fun i => wz.getD i 0).foldr Nat.land full).testBit k := by
    intro l
    induction l with
    | nil => simp [hf]
    | cons i l ih =>
      simp only [List.map_cons, List.all_cons, List.foldr_cons, id]
      rw [land_eq, Nat.testBit_and, ← ih, hR i]
  have hor : ∀ l : List ℕ, ((l.map fun i => wb.getD i false).any id) =
      ((l.map fun i => wz.getD i 0).foldr Nat.lor 0).testBit k := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.any_cons, List.foldr_cons, id]
      rw [lor_eq, Nat.testBit_or, ← ih, hR i]
  unfold gz
  rcases hop with h | h | h
  · rw [h]; exact hand _
  · rw [h]; exact hor _
  · rw [h]
    show (!((g.inputs.map fun i => wb.getD i false).headD false)) =
      (Nat.xor full ((g.inputs.map fun i => wz.getD i 0).headD 0)).testBit k
    cases g.inputs with
    | nil => simp [xor_eq, hf]
    | cons i l =>
      simp only [List.map_cons, List.headD_cons]
      rw [xor_eq, Nat.testBit_xor, hf, hR i]; simp

theorem run_bits (full k : ℕ) (hf : full.testBit k = true) :
    ∀ (gates : List Gate), (∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    ∀ (wb : List Bool) (wz : List ℕ), wb.length = wz.length →
      (∀ j, wb.getD j false = (wz.getD j 0).testBit k) →
      ∀ j, ((gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wb).getD j
        false) = ((zrun full gates wz).getD j 0).testBit k := by
  intro gates
  induction gates with
  | nil => intro _ wb wz _ hR j; exact hR j
  | cons g gates ih =>
    intro hops wb wz hlen hR j
    rw [List.foldl_cons, zrun_cons]
    apply ih (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
    · rw [List.length_append, List.length_append, hlen]; rfl
    · intro j'
      rw [getD_snoc, getD_snoc, hlen]
      have hg := gate_bit full k hf wb wz hR g (hops g List.mem_cons_self)
      by_cases h1 : j' < wz.length
      · rw [if_pos h1, if_pos h1]; exact hR j'
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : j' = wz.length
        · rw [if_pos h2, if_pos h2]; exact hg
        · rw [if_neg h2, if_neg h2]; simp

theorem expand_nil (t : ℕ) : expand [] t = 0 := rfl
theorem expand_cons (p : ℕ) (pi : List ℕ) (t : ℕ) :
    expand (p :: pi) t = Nat.bit (Nat.testBit t p) (expand pi t) := rfl

theorem expand_bit (t : ℕ) : ∀ (pi : List ℕ) (k : ℕ),
    (expand pi t).testBit k = (decide (k < pi.length) && t.testBit (pi.getD k 0)) := by
  intro pi
  induction pi with
  | nil => intro k; rw [expand_nil]; simp
  | cons p pi ih =>
    intro k
    rw [expand_cons]
    cases k with
    | zero => rw [Nat.testBit_bit_zero]; simp
    | succ k => rw [Nat.testBit_bit_succ, ih k]; simp

theorem expand_lt (t : ℕ) (pi : List ℕ) : expand pi t < 2 ^ pi.length := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [expand_bit]
  have : ¬ i < pi.length := by omega
  simp [this]

theorem lt_of_bits (n x : ℕ) (hx : x < 2 ^ n) (i : ℕ) (hi : n ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

theorem gz_lt (n : ℕ) (w : List ℕ) (hw : ∀ x ∈ w, x < 2 ^ n) (g : Gate) : gz (2 ^ n - 1) w g < 2 ^ n := by
  have hpos : 0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)
  have hfull : 2 ^ n - 1 < 2 ^ n := by omega
  have hget : ∀ i, w.getD i 0 < 2 ^ n := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases h : w[i]? with
    | none => simpa using hpos
    | some x => simpa using hw x (List.mem_of_getElem? h)
  have hand : ∀ l : List ℕ, (l.map fun i => w.getD i 0).foldr Nat.land (2 ^ n - 1) < 2 ^ n := by
    intro l
    induction l with
    | nil => simpa using hfull
    | cons i l ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [land_eq]
      exact Nat.and_lt_two_pow _ ih
  have hor : ∀ l : List ℕ, (l.map fun i => w.getD i 0).foldr Nat.lor 0 < 2 ^ n := by
    intro l
    induction l with
    | nil => simpa using hpos
    | cons i l ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [lor_eq]
      exact Nat.or_lt_two_pow (hget i) ih
  unfold gz
  cases g.op with
  | and => exact hand _
  | or => exact hor _
  | not =>
    show Nat.xor (2 ^ n - 1) ((g.inputs.map fun i => w.getD i 0).headD 0) < 2 ^ n
    rw [xor_eq]
    apply Nat.xor_lt_two_pow hfull
    cases g.inputs with
    | nil => simpa using hpos
    | cons i l => simpa using hget i
  | mod m => exact hpos
  | maj => exact hpos

theorem zrun_lt (n : ℕ) : ∀ (gates : List Gate) (w : List ℕ), (∀ x ∈ w, x < 2 ^ n) →
    ∀ x ∈ zrun (2 ^ n - 1) gates w, x < 2 ^ n := by
  intro gates
  induction gates with
  | nil => intro w hw x hx; exact hw x hx
  | cons g gates ih =>
    intro w hw x hx
    rw [zrun_cons] at hx
    apply ih (w ++ [gz (2 ^ n - 1) w g]) _ x hx
    intro y hy
    rcases List.mem_append.1 hy with h | h
    · exact hw y h
    · rw [List.mem_singleton] at h; rw [h]; exact gz_lt n w hw g

theorem base_bits : ∀ x : Fin 5 → Bool, ∀ j : Fin 5,
    (List.ofFn x).getD j.val false =
      (base32.getD j.val 0).testBit (∑ i : Fin 5, if x i = true then 2 ^ (i : ℕ) else 0) := by decide

theorem idx_of : ∀ p : Fin 32,
    (∑ i : Fin 5, if Nat.testBit p.val i = true then 2 ^ (i : ℕ) else 0) = p.val := by decide

theorem root_bits (T : ℕ) (x : Fin 5 → Bool) (k : ℕ) (hk : k < (pis T).length)
    (hp : (pis T).getD k 0 = ∑ i : Fin 5, if x i = true then 2 ^ (i : ℕ) else 0) :
    ∀ j, (List.ofFn x).getD j false = ((rootWs T).getD j 0).testBit k := by
  intro j
  by_cases hj : j < 5
  · have hb := base_bits x ⟨j, hj⟩
    simp only at hb
    rw [hb]
    have he : (rootWs T).getD j 0 = ev T j := by
      unfold rootWs
      interval_cases j <;> rfl
    rw [he]
    unfold ev
    rw [expand_bit, hp]
    simp [hk]
  · have h1 : (List.ofFn x).getD j false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
    have h2 : (rootWs T).getD j 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [rootWs]; omega)]; rfl
    rw [h1, h2, Nat.zero_testBit]

theorem root_lt (T : ℕ) : ∀ x ∈ rootWs T, x < 2 ^ (pis T).length := by
  intro x hx
  unfold rootWs at hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact expand_lt _ _

theorem mem_of_getD (l : List ℕ) (o v : ℕ) (h : l.getD o 0 = v) (hv : v ≠ 0) : v ∈ l := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hc : l[o]? with
  | none => rw [hc] at h; exact absurd h.symm hv
  | some y =>
    rw [hc] at h
    have : y = v := h
    exact this ▸ List.mem_of_getElem? hc

theorem out_eq (T : ℕ) (hlen : (pis T).length = 2 * pN T) (hpi : ∀ p ∈ pis T, p < 32)
    (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (h3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i = true then 2 ^ (i : ℕ) else 0)) :
    (zrun (pFull T) gates (rootWs T)).getD o 0 = expand (pis T) T := by
  have hfull : pFull T = 2 ^ (pis T).length - 1 := by unfold pFull; rw [hlen]
  have hbound : ∀ x ∈ zrun (pFull T) gates (rootWs T), x < 2 ^ (pis T).length := by
    rw [hfull]; exact zrun_lt _ gates _ (root_lt T)
  have hgl : (zrun (pFull T) gates (rootWs T)).getD o 0 < 2 ^ (pis T).length := by
    rw [List.getD_eq_getElem?_getD]
    cases hc : (zrun (pFull T) gates (rootWs T))[o]? with
    | none => simpa using Nat.pos_of_ne_zero (by positivity)
    | some y => simpa using hbound y (List.mem_of_getElem? hc)
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < (pis T).length
  · have hp32 : (pis T).getD k 0 < 32 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact hpi _ (List.getElem_mem hk)
    have hidx := idx_of ⟨(pis T).getD k 0, hp32⟩
    simp only at hidx
    have h3' := h3 (fun i : Fin 5 => Nat.testBit ((pis T).getD k 0) i)
    rw [hidx] at h3'
    have hfk : (pFull T).testBit k = true := by
      rw [hfull, Nat.testBit_two_pow_sub_one]; simp [hk]
    have hrun := run_bits (pFull T) k hfk gates hops
      (List.ofFn (fun i : Fin 5 => Nat.testBit ((pis T).getD k 0) i)) (rootWs T)
      (by simp [rootWs])
      (root_bits T _ k hk hidx.symm) o
    rw [expand_bit]
    simp only [hk, decide_true, Bool.true_and]
    rw [← h3', ← hrun]
    rfl
  · rw [lt_of_bits _ _ hgl k (by omega), lt_of_bits _ _ (expand_lt T (pis T)) k (by omega)]

theorem isNotOp_iff (op : GateOp) : isNotOp op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNotOp]

def nNot (gates : List Gate) : ℕ := gates.countP (fun g => isNotOp g.op)
def nBin (gates : List Gate) : ℕ := gates.countP (fun g => !isNotOp g.op)

theorem nNot_cons (g : Gate) (gates : List Gate) :
    nNot (g :: gates) = nNot gates + (if isNotOp g.op = true then 1 else 0) := by
  unfold nNot; rw [List.countP_cons]

theorem nBin_cons (g : Gate) (gates : List Gate) :
    nBin (g :: gates) = nBin gates + (if isNotOp g.op = true then 0 else 1) := by
  unfold nBin; rw [List.countP_cons]; cases isNotOp g.op <;> simp

theorem nNot_add_nBin (gates : List Gate) : nNot gates + nBin gates = gates.length := by
  induction gates with
  | nil => rfl
  | cons g gates ih =>
    rw [nNot_cons, nBin_cons, List.length_cons]
    cases isNotOp g.op <;> simp <;> omega

theorem count_not_le_one : ∀ gates : List Gate,
    (∀ i j : Fin gates.length, (gates.get i).op = GateOp.not → (gates.get j).op = GateOp.not → i = j) →
    nNot gates ≤ 1 := by
  intro gates
  induction gates with
  | nil => intro _; simp [nNot]
  | cons g gates ih =>
    intro h
    have ih' : nNot gates ≤ 1 := by
      apply ih
      intro i j hi hj
      have := h i.succ j.succ (by simpa using hi) (by simpa using hj)
      exact Fin.succ_inj.1 this
    rw [nNot_cons]
    by_cases hg : isNotOp g.op = true
    · rw [if_pos hg]
      have hz : nNot gates = 0 := by
        unfold nNot
        rw [List.countP_eq_zero]
        intro g' hg' hn
        obtain ⟨k, hk⟩ := List.mem_iff_get.1 hg'
        have := h ⟨0, by simp⟩ k.succ ((isNotOp_iff _).1 hg)
          (by
            have e : (g :: gates).get k.succ = gates.get k := rfl
            rw [e, hk]; exact (isNotOp_iff _).1 hn)
        exact absurd (congrArg Fin.val this) (by simp)
      omega
    · rw [if_neg hg]; omega

theorem getD_mem_or (w : List ℕ) (i : ℕ) : w.getD i 0 ∈ w ∨ w.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => right; rfl
  | some x => left; exact List.mem_of_getElem? h

theorem and_full (n x : ℕ) (hx : x < 2 ^ n) : x &&& (2 ^ n - 1) = x := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]

theorem full_and (n x : ℕ) (hx : x < 2 ^ n) : (2 ^ n - 1) &&& x = x := by
  rw [Nat.and_comm]; exact and_full n x hx

theorem or_full (n x : ℕ) (hx : x < 2 ^ n) : x ||| (2 ^ n - 1) = 2 ^ n - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < n
  · simp [hi]
  · simp [hi, lt_of_bits n x hx i (by omega)]

theorem full_or (n x : ℕ) (hx : x < 2 ^ n) : (2 ^ n - 1) ||| x = 2 ^ n - 1 := by
  rw [Nat.or_comm]; exact or_full n x hx

theorem bin_land (n : ℕ) (W : List ℕ) (a b : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (ca : a ∈ W ∨ a = 0 ∨ a = 2 ^ n - 1) (cb : b ∈ W ∨ b = 0 ∨ b = 2 ^ n - 1) :
    (a &&& b ∈ W ∨ a &&& b = 0 ∨ a &&& b = 2 ^ n - 1) ∨ (a ∈ W ∧ b ∈ W) := by
  rcases ca with h | rfl | rfl
  · rcases cb with h' | rfl | rfl
    · exact Or.inr ⟨h, h'⟩
    · left; right; left; exact Nat.and_zero a
    · left; left; rw [and_full n a ha]; exact h
  · left; right; left; exact Nat.zero_and b
  · left; rw [full_and n b hb]; exact cb

theorem bin_lor (n : ℕ) (W : List ℕ) (a b : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (ca : a ∈ W ∨ a = 0 ∨ a = 2 ^ n - 1) (cb : b ∈ W ∨ b = 0 ∨ b = 2 ^ n - 1) :
    (a ||| b ∈ W ∨ a ||| b = 0 ∨ a ||| b = 2 ^ n - 1) ∨ (a ∈ W ∧ b ∈ W) := by
  rcases ca with h | rfl | rfl
  · rcases cb with h' | rfl | rfl
    · exact Or.inr ⟨h, h'⟩
    · left; left; rw [Nat.or_zero]; exact h
    · left; right; right; exact or_full n a ha
  · left; rw [Nat.zero_or]; exact cb
  · left; right; right; exact full_or n b hb

theorem un_xor (n : ℕ) (W : List ℕ) (a : ℕ)
    (ca : a ∈ W ∨ a = 0 ∨ a = 2 ^ n - 1) :
    ((2 ^ n - 1) ^^^ a ∈ W ∨ (2 ^ n - 1) ^^^ a = 0 ∨ (2 ^ n - 1) ^^^ a = 2 ^ n - 1) ∨ a ∈ W := by
  rcases ca with h | rfl | rfl
  · exact Or.inr h
  · left; right; right; exact Nat.xor_zero _
  · left; right; left; exact Nat.xor_self _

theorem list_le_two (l : List ℕ) (h : l.length ≤ 2) :
    l = [] ∨ (∃ i, l = [i]) ∨ ∃ i j, l = [i, j] := by
  match l, h with
  | [], _ => exact Or.inl rfl
  | [i], _ => exact Or.inr (Or.inl ⟨i, rfl⟩)
  | [i, j], _ => exact Or.inr (Or.inr ⟨i, j, rfl⟩)
  | _ :: _ :: _ :: _, h => simp at h

theorem gate_step (n : ℕ) (w W : List ℕ) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (hlen : g.inputs.length ≤ 2)
    (hw : ∀ x ∈ w, x < 2 ^ n) (hW : ∀ x ∈ w, x ∈ W ∨ x = 0 ∨ x = 2 ^ n - 1) :
    (gz (2 ^ n - 1) w g ∈ W ∨ gz (2 ^ n - 1) w g = 0 ∨ gz (2 ^ n - 1) w g = 2 ^ n - 1) ∨
    (isNotOp g.op = false ∧ ∃ a ∈ W, ∃ b ∈ W,
      gz (2 ^ n - 1) w g = Nat.land a b ∨ gz (2 ^ n - 1) w g = Nat.lor a b) ∨
    (isNotOp g.op = true ∧ ∃ a ∈ W, gz (2 ^ n - 1) w g = Nat.xor (2 ^ n - 1) a) := by
  have hpos : 0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)
  have hlt : ∀ i, w.getD i 0 < 2 ^ n := by
    intro i
    rcases getD_mem_or w i with h | h
    · exact hw _ h
    · rw [h]; exact hpos
  have hc : ∀ i, w.getD i 0 ∈ W ∨ w.getD i 0 = 0 ∨ w.getD i 0 = 2 ^ n - 1 := by
    intro i
    rcases getD_mem_or w i with h | h
    · exact hW _ h
    · exact Or.inr (Or.inl h)
  obtain ⟨op, inputs⟩ := g
  dsimp only at hop hlen
  have handTwo : ∀ i j, gz (2 ^ n - 1) w ⟨GateOp.and, [i, j]⟩ = w.getD i 0 &&& w.getD j 0 := by
    intro i j
    show Nat.land (w.getD i 0) (Nat.land (w.getD j 0) (2 ^ n - 1)) = _
    rw [land_eq, land_eq, and_full n _ (hlt j)]
  have handOne : ∀ i, gz (2 ^ n - 1) w ⟨GateOp.and, [i]⟩ = w.getD i 0 := by
    intro i
    show Nat.land (w.getD i 0) (2 ^ n - 1) = _
    rw [land_eq, and_full n _ (hlt i)]
  have horTwo : ∀ i j, gz (2 ^ n - 1) w ⟨GateOp.or, [i, j]⟩ = w.getD i 0 ||| w.getD j 0 := by
    intro i j
    show Nat.lor (w.getD i 0) (Nat.lor (w.getD j 0) 0) = _
    rw [lor_eq, lor_eq, Nat.or_zero]
  have horOne : ∀ i, gz (2 ^ n - 1) w ⟨GateOp.or, [i]⟩ = w.getD i 0 := by
    intro i
    show Nat.lor (w.getD i 0) 0 = _
    rw [lor_eq, Nat.or_zero]
  have hnotCons : ∀ i l, gz (2 ^ n - 1) w ⟨GateOp.not, i :: l⟩ = (2 ^ n - 1) ^^^ w.getD i 0 := by
    intro i l; rfl
  have hnotCase : ∀ i l,
      (gz (2 ^ n - 1) w ⟨GateOp.not, i :: l⟩ ∈ W ∨ gz (2 ^ n - 1) w ⟨GateOp.not, i :: l⟩ = 0 ∨
        gz (2 ^ n - 1) w ⟨GateOp.not, i :: l⟩ = 2 ^ n - 1) ∨
      (isNotOp GateOp.not = false ∧ ∃ a ∈ W, ∃ b ∈ W,
        gz (2 ^ n - 1) w ⟨GateOp.not, i :: l⟩ = Nat.land a b ∨
        gz (2 ^ n - 1) w ⟨GateOp.not, i :: l⟩ = Nat.lor a b) ∨
      (isNotOp GateOp.not = true ∧ ∃ a ∈ W,
        gz (2 ^ n - 1) w ⟨GateOp.not, i :: l⟩ = Nat.xor (2 ^ n - 1) a) := by
    intro i l
    rw [hnotCons]
    rcases un_xor n W _ (hc i) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨rfl, _, h, rfl⟩)
  rcases hop with rfl | rfl | rfl
  · rcases list_le_two inputs hlen with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
    · exact Or.inl (Or.inr (Or.inr rfl))
    · rw [handOne]; exact Or.inl (hc i)
    · rw [handTwo]
      rcases bin_land n W _ _ (hlt i) (hlt j) (hc i) (hc j) with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨rfl, _, h1, _, h2, Or.inl rfl⟩)
  · rcases list_le_two inputs hlen with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
    · exact Or.inl (Or.inr (Or.inl rfl))
    · rw [horOne]; exact Or.inl (hc i)
    · rw [horTwo]
      rcases bin_lor n W _ _ (hlt i) (hlt j) (hc i) (hc j) with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨rfl, _, h1, _, h2, Or.inr rfl⟩)
  · rcases list_le_two inputs hlen with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
    · left; right; right
      show Nat.xor (2 ^ n - 1) 0 = 2 ^ n - 1
      exact Nat.xor_zero _
    · exact hnotCase i []
    · exact hnotCase i [j]

theorem extract (n zt : ℕ) (hz0 : zt ≠ 0) (hzf : zt ≠ 2 ^ n - 1) :
    ∀ (gates : List Gate) (w W : List ℕ),
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ x ∈ w, x < 2 ^ n) → (∀ x ∈ w, x ∈ W ∨ x = 0 ∨ x = 2 ^ n - 1) →
      zt ∈ zrun (2 ^ n - 1) gates w →
      ∃ D : List Step, Valid (2 ^ n - 1) W D ∧ (zt ∈ W ∨ zt ∈ outs D) ∧ nots D ≤ nNot gates ∧
        bins D ≤ nBin gates := by
  intro gates
  induction gates with
  | nil =>
    intro w W _ _ hW hz
    rw [zrun_nil] at hz
    refine ⟨[], trivial, Or.inl ?_, Nat.zero_le _, Nat.zero_le _⟩
    rcases hW zt hz with h | h | h
    · exact h
    · exact absurd h hz0
    · exact absurd h hzf
  | cons g gates ih =>
    intro w W hg hw hW hz
    rw [zrun_cons] at hz
    have hg' := fun g' hg'' => hg g' (List.mem_cons_of_mem _ hg'')
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    have hw' : ∀ x ∈ w ++ [gz (2 ^ n - 1) w g], x < 2 ^ n := by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact hw x h
      · rw [List.mem_singleton] at h; rw [h]; exact gz_lt n w hw g
    have same : (gz (2 ^ n - 1) w g ∈ W ∨ gz (2 ^ n - 1) w g = 0 ∨ gz (2 ^ n - 1) w g = 2 ^ n - 1) →
        ∃ D : List Step, Valid (2 ^ n - 1) W D ∧ (zt ∈ W ∨ zt ∈ outs D) ∧ nots D ≤ nNot (g :: gates) ∧
          bins D ≤ nBin (g :: gates) := by
      intro hsame
      obtain ⟨D, d1, d2, d3, d4⟩ := ih (w ++ [gz (2 ^ n - 1) w g]) W hg' hw'
        (by
          intro x hx
          rcases List.mem_append.1 hx with h | h
          · exact hW x h
          · rw [List.mem_singleton] at h; rw [h]; exact hsame) hz
      refine ⟨D, d1, d2, ?_, ?_⟩
      · rw [nNot_cons]; omega
      · rw [nBin_cons]; omega
    have fresh : ∀ s : Step, okStep (2 ^ n - 1) s → s.2.1 ∈ W → s.2.2.1 ∈ W →
        s.2.2.2 = gz (2 ^ n - 1) w g → (s.1 = true ↔ isNotOp g.op = true) →
        ∃ D : List Step, Valid (2 ^ n - 1) W D ∧ (zt ∈ W ∨ zt ∈ outs D) ∧ nots D ≤ nNot (g :: gates) ∧
          bins D ≤ nBin (g :: gates) := by
      intro s hok ha hb hsz hkind
      by_cases hsame : gz (2 ^ n - 1) w g ∈ W ∨ gz (2 ^ n - 1) w g = 0 ∨ gz (2 ^ n - 1) w g = 2 ^ n - 1
      · exact same hsame
      · rw [not_or, not_or] at hsame
        obtain ⟨D, d1, d2, d3, d4⟩ := ih (w ++ [gz (2 ^ n - 1) w g]) (gz (2 ^ n - 1) w g :: W) hg' hw'
          (by
            intro x hx
            rcases List.mem_append.1 hx with h | h
            · rcases hW x h with h' | h' | h'
              · exact Or.inl (List.mem_cons_of_mem _ h')
              · exact Or.inr (Or.inl h')
              · exact Or.inr (Or.inr h')
            · rw [List.mem_singleton] at h; rw [h]; exact Or.inl List.mem_cons_self) hz
        refine ⟨s :: D, ?_, ?_, ?_, ?_⟩
        · refine (valid_cons _ W s D).2 ⟨hok, ha, hb, ?_, ?_, ?_, ?_⟩
          · rw [hsz]; exact hsame.1
          · rw [hsz]; exact hsame.2.1
          · rw [hsz]; exact hsame.2.2
          · rw [hsz]; exact d1
        · rcases d2 with h | h
          · rcases List.mem_cons.1 h with h' | h'
            · right; rw [outs_cons, h', hsz]; exact List.mem_cons_self
            · exact Or.inl h'
          · right; rw [outs_cons]; exact List.mem_cons_of_mem _ h
        · rw [nots_cons, nNot_cons]
          by_cases hk : s.1 = true
          · rw [if_pos hk, if_pos (hkind.1 hk)]; omega
          · rw [if_neg hk, if_neg (fun h => hk (hkind.2 h))]; omega
        · rw [bins_cons, nBin_cons]
          by_cases hk : s.1 = true
          · rw [if_pos hk, if_pos (hkind.1 hk)]; omega
          · rw [if_neg hk, if_neg (fun h => hk (hkind.2 h))]; omega
    rcases gate_step n w W g hop hlen hw hW with h | ⟨hk, a, ha, b, hb, hab⟩ | ⟨hk, a, ha, hab⟩
    · exact same h
    · have hok : okStep (2 ^ n - 1) (false, a, b, gz (2 ^ n - 1) w g) :=
        ⟨fun h => Bool.noConfusion h, fun _ => hab⟩
      have hkind : ((false, a, b, gz (2 ^ n - 1) w g) : Step).1 = true ↔ isNotOp g.op = true := by
        rw [hk]
      exact fresh (false, a, b, gz (2 ^ n - 1) w g) hok ha hb rfl hkind
    · have hok : okStep (2 ^ n - 1) (true, a, a, gz (2 ^ n - 1) w g) :=
        ⟨fun _ => ⟨rfl, hab⟩, fun h => Bool.noConfusion h⟩
      have hkind : ((true, a, a, gz (2 ^ n - 1) w g) : Step).1 = true ↔ isNotOp g.op = true := by
        rw [hk]
      exact fresh (true, a, a, gz (2 ^ n - 1) w g) hok ha ha rfl hkind

theorem valid_strengthen (full x : ℕ) : ∀ (D : List Step) (W : List ℕ), Valid full (x :: W) D →
    ¬ reads D x → Valid full W D := by
  intro D
  induction D with
  | nil => intro _ _ _; trivial
  | cons t D ih =>
    intro W hv hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := (valid_cons full _ t D).1 hv
    rw [reads_cons, not_or, not_or] at hr
    obtain ⟨⟨hra, hrb⟩, hrD⟩ := hr
    have ha : t.2.1 ∈ W := by
      rcases List.mem_cons.1 h2 with h | h
      · exact absurd h hra
      · exact h
    have hb : t.2.2.1 ∈ W := by
      rcases List.mem_cons.1 h3 with h | h
      · exact absurd h hrb
      · exact h
    refine (valid_cons full W t D).2 ⟨h1, ha, hb, fun hc => h4 (List.mem_cons_of_mem _ hc), h5, h6, ?_⟩
    apply ih (t.2.2.2 :: W) _ hrD
    apply valid_congr full D _ _ _ h7
    intro y
    simp only [List.mem_cons]
    tauto

theorem shrink (full zt : ℕ) : ∀ (D : List Step) (W : List ℕ), Valid full W D → zt ∈ outs D →
    ¬ Used zt D →
    ∃ D' : List Step, Valid full W D' ∧ zt ∈ outs D' ∧ D'.length < D.length ∧ nots D' ≤ nots D ∧
      bins D' ≤ bins D := by
  intro D
  induction D with
  | nil => intro _ _ hz _; simp [outs] at hz
  | cons s D ih =>
    intro W hv hz hu
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := (valid_cons full W s D).1 hv
    rw [outs_cons, List.mem_cons] at hz
    by_cases hA : s.2.2.2 = zt ∨ reads D s.2.2.2
    · have huD : ¬ Used zt D := fun h => hu ((used_cons zt s D).2 ⟨hA, h⟩)
      by_cases hzD : zt ∈ outs D
      · obtain ⟨D', d1, d2, d3, d4, d5⟩ := ih (s.2.2.2 :: W) h7 hzD huD
        refine ⟨s :: D', (valid_cons full W s D').2 ⟨h1, h2, h3, h4, h5, h6, d1⟩, ?_, ?_, ?_, ?_⟩
        · rw [outs_cons]; exact List.mem_cons_of_mem _ d2
        · simp only [List.length_cons]; omega
        · rw [nots_cons, nots_cons]; omega
        · rw [bins_cons, bins_cons]; omega
      · have hzs : zt = s.2.2.2 := by
          rcases hz with h | h
          · exact h
          · exact absurd h hzD
        have hDne : D ≠ [] := by
          intro h
          rw [h] at huD
          exact huD trivial
        refine ⟨[s], (valid_cons full W s []).2 ⟨h1, h2, h3, h4, h5, h6, trivial⟩, ?_, ?_, ?_, ?_⟩
        · rw [outs_cons, hzs]; exact List.mem_cons_self
        · cases D with
          | nil => exact absurd rfl hDne
          | cons t D => simp
        · rw [nots_cons, nots_cons]
          have : nots ([] : List Step) = 0 := rfl
          omega
        · rw [bins_cons, bins_cons]
          have : bins ([] : List Step) = 0 := rfl
          omega
    · rw [not_or] at hA
      refine ⟨D, valid_strengthen full _ D W h7 hA.2, ?_, ?_, ?_, ?_⟩
      · rcases hz with h | h
        · exact absurd h.symm hA.1
        · exact h
      · simp
      · rw [nots_cons]; omega
      · rw [bins_cons]; omega

theorem exists_used (full zt : ℕ) (W : List ℕ) : ∀ (m : ℕ) (D : List Step), D.length ≤ m →
    Valid full W D → zt ∈ outs D →
    ∃ D' : List Step, Valid full W D' ∧ zt ∈ outs D' ∧ Used zt D' ∧ nots D' ≤ nots D ∧
      bins D' ≤ bins D := by
  intro m
  induction m with
  | zero =>
    intro D hl _ hz
    have : D = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hl)
    rw [this] at hz
    simp [outs] at hz
  | succ m ih =>
    intro D hl hv hz
    by_cases hu : Used zt D
    · exact ⟨D, hv, hz, hu, le_refl _, le_refl _⟩
    · obtain ⟨D1, a1, a2, a3, a4, a5⟩ := shrink full zt D W hv hz hu
      obtain ⟨D2, b1, b2, b3, b4, b5⟩ := ih D1 (by omega) a1 a2
      exact ⟨D2, b1, b2, b3, by omega, by omega⟩

theorem rootRun_eq (T k : ℕ) :
    rootRun T k = search (pN T) (2 ^ pN T - 1) (2 ^ (2 * pN T) - 1) (2 ^ pN T - 1) k (rootWs T)
      ((rootWs T).map (mk (pN T) (2 ^ pN T - 1) true)) [] true 0 [] (rootWs T) := by
  unfold rootRun sAt pLow pFull
  rw [mapMk_eq]

theorem rootRun0_eq (T k : ℕ) :
    rootRun0 T k = search (pN T) (2 ^ pN T - 1) (2 ^ (2 * pN T) - 1) (2 ^ pN T - 1) k (rootWs T)
      ((rootWs T).map (mk (pN T) (2 ^ pN T - 1) false)) [] false 0 [] [] := by
  unfold rootRun0 sAt pLow pFull
  rw [mapMk_eq]

-- any list with at least one NOT gate (and at most one) that computes T has at least F + 2 gates
theorem lower (T F : ℕ) (hlen : (pis T).length = 2 * pN T) (hpi : ∀ p ∈ pis T, p < 32)
    (hT : expand (pis T) T = pLow T) (hnr : pLow T ∉ rootWs T) (hl0 : pLow T ≠ 0)
    (hlf : pLow T ≠ pFull T)
    (h1 : rootRun T (F + 1) = false) (h0 : rootRun0 T F = false)
    (gates : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : nNot gates = 1)
    (h3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i = true then 2 ^ (i : ℕ) else 0)) :
    F + 2 ≤ gates.length := by
  have hout := out_eq T hlen hpi gates o (fun g h => (hg g h).1) h3
  rw [hT] at hout
  have hmem : pLow T ∈ zrun (pFull T) gates (rootWs T) := mem_of_getD _ o _ hout hl0
  have hfull : pFull T = 2 ^ (2 * pN T) - 1 := rfl
  have hlow : pLow T = 2 ^ pN T - 1 := rfl
  rw [hfull] at hmem
  have hrl : ∀ x ∈ rootWs T, x < 2 ^ (2 * pN T) := by
    intro x hx
    have := root_lt T x hx
    rw [hlen] at this
    exact this
  obtain ⟨D, d1, d2, d3, d4⟩ := extract (2 * pN T) (pLow T) hl0 (by rw [← hfull]; exact hlf) gates
    (rootWs T) (rootWs T) hg hrl (fun x hx => Or.inl hx) hmem
  have hzo : pLow T ∈ outs D := by
    rcases d2 with h | h
    · exact absurd h hnr
    · exact h
  obtain ⟨D', e1, e2, e3, e4, e5⟩ := exists_used _ (pLow T) (rootWs T) D.length D (le_refl _) d1 hzo
  have hsum := nNot_add_nBin gates
  have hsum' := nots_add_bins D'
  by_contra hcon
  have hK : gates.length ≤ F + 1 := by omega
  rw [hlow] at e2 e3
  by_cases hn : nots D' = 0
  · have hI : Inv (pN T) F (rootWs T) ((rootWs T).map (mk (pN T) (2 ^ pN T - 1) false)) [] false 0 [] [] := by
      refine ⟨D', by omega, e1, by simpa using hn, e2, ?_, e3, ?_, ?_, rfl, ?_, List.nodup_nil⟩
      · intro u hu; cases hu
      · intro t _ _ _ _; exact Or.inl (Nat.zero_le _)
      · intro h; cases h
      · intro u hu; cases hu
    have := search_complete (pN T) F _ _ _ _ _ _ _ hI
    rw [← rootRun0_eq, h0] at this
    exact Bool.false_ne_true this
  · have hn1 : nots D' = 1 := by omega
    have hI : Inv (pN T) (F + 1) (rootWs T) ((rootWs T).map (mk (pN T) (2 ^ pN T - 1) true)) [] true 0 []
        (rootWs T) := by
      refine ⟨D', by omega, e1, by simpa using hn1, e2, ?_, e3, ?_, ?_, rfl, ?_, List.nodup_nil⟩
      · intro u hu; cases hu
      · intro t _ _ _ _; exact Or.inl (Nat.zero_le _)
      · intro _ t _ _ ha; exact ha
      · intro u hu; cases hu
    have := search_complete (pN T) (F + 1) _ _ _ _ _ _ _ hI
    rw [← rootRun_eq, h1] at this
    exact Bool.false_ne_true this

-- the root of the one-NOT search, split into its 25 first steps
theorem notAll_five (g : ℕ → Bool) (a b c d e : ℕ) :
    notAll g [a, b, c, d, e] = (g a || (g b || (g c || (g d || (g e || false))))) := rfl

theorem outer_five (h : ℕ → ℕ → ℕ → Bool) (a b c d e : ℕ) :
    outer h [a, b, c, d, e] =
      ((h a b (Nat.land a b) || (h a b (Nat.lor a b) || (h a c (Nat.land a c) || (h a c (Nat.lor a c) ||
        (h a d (Nat.land a d) || (h a d (Nat.lor a d) || (h a e (Nat.land a e) || (h a e (Nat.lor a e) ||
          false)))))))) ||
      ((h b c (Nat.land b c) || (h b c (Nat.lor b c) || (h b d (Nat.land b d) || (h b d (Nat.lor b d) ||
        (h b e (Nat.land b e) || (h b e (Nat.lor b e) || false)))))) ||
      ((h c d (Nat.land c d) || (h c d (Nat.lor c d) || (h c e (Nat.land c e) || (h c e (Nat.lor c e) ||
        false)))) ||
      ((h d e (Nat.land d e) || (h d e (Nat.lor d e) || false)) || (false || false))))) := rfl

theorem root_split (T k : ℕ)
    (n0 : notAt T k 0 = false)
    (n1 : notAt T k 1 = false)
    (n2 : notAt T k 2 = false)
    (n3 : notAt T k 3 = false)
    (n4 : notAt T k 4 = false)
    (b01a : binAt T k 0 1 false = false) (b01o : binAt T k 0 1 true = false)
    (b02a : binAt T k 0 2 false = false) (b02o : binAt T k 0 2 true = false)
    (b03a : binAt T k 0 3 false = false) (b03o : binAt T k 0 3 true = false)
    (b04a : binAt T k 0 4 false = false) (b04o : binAt T k 0 4 true = false)
    (b12a : binAt T k 1 2 false = false) (b12o : binAt T k 1 2 true = false)
    (b13a : binAt T k 1 3 false = false) (b13o : binAt T k 1 3 true = false)
    (b14a : binAt T k 1 4 false = false) (b14o : binAt T k 1 4 true = false)
    (b23a : binAt T k 2 3 false = false) (b23o : binAt T k 2 3 true = false)
    (b24a : binAt T k 2 4 false = false) (b24o : binAt T k 2 4 true = false)
    (b34a : binAt T k 3 4 false = false) (b34o : binAt T k 3 4 true = false) :
    rootRun T (k + 1) = false := by
  have hN : ∀ i, notAt T k i = false →
      stepNot (pN T) (pLow T) (pFull T) (pLow T) (search (pN T) (pLow T) (pFull T) (pLow T) k)
        (rootWs T) [] 0 [] (ev T i) = false := fun _ h => h
  have hA : ∀ {i j : ℕ}, binAt T k i j false = false →
      stepBin (pN T) (pLow T) (pFull T) (pLow T) (search (pN T) (pLow T) (pFull T) (pLow T) k)
        (rootWs T) (mapMk (pN T) (pLow T) true (rootWs T)) [] true 0 []
        (ev T i) (ev T j) (Nat.land (ev T i) (ev T j)) = false := fun h => h
  have hO : ∀ {i j : ℕ}, binAt T k i j true = false →
      stepBin (pN T) (pLow T) (pFull T) (pLow T) (search (pN T) (pLow T) (pFull T) (pLow T) k)
        (rootWs T) (mapMk (pN T) (pLow T) true (rootWs T)) [] true 0 []
        (ev T i) (ev T j) (Nat.lor (ev T i) (ev T j)) = false := fun h => h
  have hNot : notAll (stepNot (pN T) (pLow T) (pFull T) (pLow T)
      (search (pN T) (pLow T) (pFull T) (pLow T) k) (rootWs T) [] 0 []) (rootWs T) = false := by
    show notAll (stepNot (pN T) (pLow T) (pFull T) (pLow T)
      (search (pN T) (pLow T) (pFull T) (pLow T) k) (rootWs T) [] 0 [])
      [ev T 0, ev T 1, ev T 2, ev T 3, ev T 4] = false
    rw [notAll_five, hN 0 n0, hN 1 n1, hN 2 n2, hN 3 n3, hN 4 n4]
    rfl
  have hOut : outer (stepBin (pN T) (pLow T) (pFull T) (pLow T)
      (search (pN T) (pLow T) (pFull T) (pLow T) k) (rootWs T)
      (mapMk (pN T) (pLow T) true (rootWs T)) [] true 0 []) (rootWs T) = false := by
    show outer (stepBin (pN T) (pLow T) (pFull T) (pLow T)
      (search (pN T) (pLow T) (pFull T) (pLow T) k) (rootWs T)
      (mapMk (pN T) (pLow T) true (rootWs T)) [] true 0 [])
      [ev T 0, ev T 1, ev T 2, ev T 3, ev T 4] = false
    rw [outer_five, hA b01a, hO b01o, hA b02a, hO b02o, hA b03a, hO b03o, hA b04a, hO b04o, hA b12a, hO b12o, hA b13a, hO b13o, hA b14a, hO b14o, hA b23a, hO b23o, hA b24a, hO b24o, hA b34a, hO b34o]
    rfl
  unfold rootRun sAt
  rw [search_succ, hNot, hOut]
  simp

theorem f1_feeaeac0 : (pis 0xfeeaeac0).length = 2 * pN 0xfeeaeac0 := by decide +kernel
theorem f2_feeaeac0 : ∀ p ∈ pis 0xfeeaeac0, p < 32 := by decide +kernel
theorem f3_feeaeac0 : expand (pis 0xfeeaeac0) 0xfeeaeac0 = pLow 0xfeeaeac0 := by decide +kernel
theorem f4_feeaeac0 : pLow 0xfeeaeac0 ∉ rootWs 0xfeeaeac0 := by decide +kernel
theorem f5_feeaeac0 : pLow 0xfeeaeac0 ≠ 0 := by decide +kernel
theorem f6_feeaeac0 : pLow 0xfeeaeac0 ≠ pFull 0xfeeaeac0 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_feeaeac0 : rootRun0 0xfeeaeac0 6 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem r1_feeaeac0 : rootRun 0xfeeaeac0 (6 + 1) = false := by decide +kernel
theorem tgt_feeaeac0 (gates : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : nNot gates = 1)
    (h3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit 0xfeeaeac0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Nat.testBit 0xfeeaeac0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  have hlow := lower 0xfeeaeac0 6 f1_feeaeac0 f2_feeaeac0 f3_feeaeac0 f4_feeaeac0 f5_feeaeac0 f6_feeaeac0 r1_feeaeac0 r0_feeaeac0 gates o hg hone h3
  refine ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.or, [5, 11]⟩], 12, ?_, ?_, ?_⟩
  · simp
  · simp only [List.length_cons, List.length_nil]
    omega
  · decide

theorem f1_eeeaeaaa : (pis 0xeeeaeaaa).length = 2 * pN 0xeeeaeaaa := by decide +kernel
theorem f2_eeeaeaaa : ∀ p ∈ pis 0xeeeaeaaa, p < 32 := by decide +kernel
theorem f3_eeeaeaaa : expand (pis 0xeeeaeaaa) 0xeeeaeaaa = pLow 0xeeeaeaaa := by decide +kernel
theorem f4_eeeaeaaa : pLow 0xeeeaeaaa ∉ rootWs 0xeeeaeaaa := by decide +kernel
theorem f5_eeeaeaaa : pLow 0xeeeaeaaa ≠ 0 := by decide +kernel
theorem f6_eeeaeaaa : pLow 0xeeeaeaaa ≠ pFull 0xeeeaeaaa := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_eeeaeaaa : rootRun0 0xeeeaeaaa 4 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem r1_eeeaeaaa : rootRun 0xeeeaeaaa (4 + 1) = false := by decide +kernel
theorem tgt_eeeaeaaa (gates : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : nNot gates = 1)
    (h3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit 0xeeeaeaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Nat.testBit 0xeeeaeaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  have hlow := lower 0xeeeaeaaa 4 f1_eeeaeaaa f2_eeeaeaaa f3_eeeaeaaa f4_eeeaeaaa f5_eeeaeaaa f6_eeeaeaaa r1_eeeaeaaa r0_eeeaeaaa gates o hg hone h3
  refine ⟨[⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.or, [0, 9]⟩], 10, ?_, ?_, ?_⟩
  · simp
  · simp only [List.length_cons, List.length_nil]
    omega
  · decide

theorem f1_eeeaeae8 : (pis 0xeeeaeae8).length = 2 * pN 0xeeeaeae8 := by decide +kernel
theorem f2_eeeaeae8 : ∀ p ∈ pis 0xeeeaeae8, p < 32 := by decide +kernel
theorem f3_eeeaeae8 : expand (pis 0xeeeaeae8) 0xeeeaeae8 = pLow 0xeeeaeae8 := by decide +kernel
theorem f4_eeeaeae8 : pLow 0xeeeaeae8 ∉ rootWs 0xeeeaeae8 := by decide +kernel
theorem f5_eeeaeae8 : pLow 0xeeeaeae8 ≠ 0 := by decide +kernel
theorem f6_eeeaeae8 : pLow 0xeeeaeae8 ≠ pFull 0xeeeaeae8 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_eeeaeae8 : rootRun0 0xeeeaeae8 6 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem r1_eeeaeae8 : rootRun 0xeeeaeae8 (6 + 1) = false := by decide +kernel
theorem tgt_eeeaeae8 (gates : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : nNot gates = 1)
    (h3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit 0xeeeaeae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Nat.testBit 0xeeeaeae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  have hlow := lower 0xeeeaeae8 6 f1_eeeaeae8 f2_eeeaeae8 f3_eeeaeae8 f4_eeeaeae8 f5_eeeaeae8 f6_eeeaeae8 r1_eeeaeae8 r0_eeeaeae8 gates o hg hone h3
  refine ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12, ?_, ?_, ?_⟩
  · simp
  · simp only [List.length_cons, List.length_nil]
    omega
  · decide

theorem f1_eeeaece8 : (pis 0xeeeaece8).length = 2 * pN 0xeeeaece8 := by decide +kernel
theorem f2_eeeaece8 : ∀ p ∈ pis 0xeeeaece8, p < 32 := by decide +kernel
theorem f3_eeeaece8 : expand (pis 0xeeeaece8) 0xeeeaece8 = pLow 0xeeeaece8 := by decide +kernel
theorem f4_eeeaece8 : pLow 0xeeeaece8 ∉ rootWs 0xeeeaece8 := by decide +kernel
theorem f5_eeeaece8 : pLow 0xeeeaece8 ≠ 0 := by decide +kernel
theorem f6_eeeaece8 : pLow 0xeeeaece8 ≠ pFull 0xeeeaece8 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_eeeaece8 : rootRun0 0xeeeaece8 4 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem r1_eeeaece8 : rootRun 0xeeeaece8 (4 + 1) = false := by decide +kernel
theorem tgt_eeeaece8 (gates : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : nNot gates = 1)
    (h3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit 0xeeeaece8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Nat.testBit 0xeeeaece8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  have hlow := lower 0xeeeaece8 4 f1_eeeaece8 f2_eeeaece8 f3_eeeaece8 f4_eeeaece8 f5_eeeaece8 f6_eeeaece8 r1_eeeaece8 r0_eeeaece8 gates o hg hone h3
  refine ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [5, 9]⟩], 10, ?_, ?_, ?_⟩
  · simp
  · simp only [List.length_cons, List.length_nil]
    omega
  · decide

theorem f1_eeeaeee0 : (pis 0xeeeaeee0).length = 2 * pN 0xeeeaeee0 := by decide +kernel
theorem f2_eeeaeee0 : ∀ p ∈ pis 0xeeeaeee0, p < 32 := by decide +kernel
theorem f3_eeeaeee0 : expand (pis 0xeeeaeee0) 0xeeeaeee0 = pLow 0xeeeaeee0 := by decide +kernel
theorem f4_eeeaeee0 : pLow 0xeeeaeee0 ∉ rootWs 0xeeeaeee0 := by decide +kernel
theorem f5_eeeaeee0 : pLow 0xeeeaeee0 ≠ 0 := by decide +kernel
theorem f6_eeeaeee0 : pLow 0xeeeaeee0 ≠ pFull 0xeeeaeee0 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_eeeaeee0 : rootRun0 0xeeeaeee0 3 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem r1_eeeaeee0 : rootRun 0xeeeaeee0 (3 + 1) = false := by decide +kernel
theorem tgt_eeeaeee0 (gates : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : nNot gates = 1)
    (h3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit 0xeeeaeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Nat.testBit 0xeeeaeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  have hlow := lower 0xeeeaeee0 3 f1_eeeaeee0 f2_eeeaeee0 f3_eeeaeee0 f4_eeeaeee0 f5_eeeaeee0 f6_eeeaeee0 r1_eeeaeee0 r0_eeeaeee0 gates o hg hone h3
  refine ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [7, 8]⟩], 9, ?_, ?_, ?_⟩
  · simp
  · simp only [List.length_cons, List.length_nil]
    omega
  · decide

theorem f1_fee8eae8 : (pis 0xfee8eae8).length = 2 * pN 0xfee8eae8 := by decide +kernel
theorem f2_fee8eae8 : ∀ p ∈ pis 0xfee8eae8, p < 32 := by decide +kernel
theorem f3_fee8eae8 : expand (pis 0xfee8eae8) 0xfee8eae8 = pLow 0xfee8eae8 := by decide +kernel
theorem f4_fee8eae8 : pLow 0xfee8eae8 ∉ rootWs 0xfee8eae8 := by decide +kernel
theorem f5_fee8eae8 : pLow 0xfee8eae8 ≠ 0 := by decide +kernel
theorem f6_fee8eae8 : pLow 0xfee8eae8 ≠ pFull 0xfee8eae8 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_fee8eae8 : rootRun0 0xfee8eae8 6 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem r1_fee8eae8 : rootRun 0xfee8eae8 (6 + 1) = false := by decide +kernel
theorem tgt_fee8eae8 (gates : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : nNot gates = 1)
    (h3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit 0xfee8eae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Nat.testBit 0xfee8eae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  have hlow := lower 0xfee8eae8 6 f1_fee8eae8 f2_fee8eae8 f3_fee8eae8 f4_fee8eae8 f5_fee8eae8 f6_fee8eae8 r1_fee8eae8 r0_fee8eae8 gates o hg hone h3
  refine ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [10, 11]⟩], 12, ?_, ?_, ?_⟩
  · simp
  · simp only [List.length_cons, List.length_nil]
    omega
  · decide

theorem f1_fee8eee0 : (pis 0xfee8eee0).length = 2 * pN 0xfee8eee0 := by decide +kernel
theorem f2_fee8eee0 : ∀ p ∈ pis 0xfee8eee0, p < 32 := by decide +kernel
theorem f3_fee8eee0 : expand (pis 0xfee8eee0) 0xfee8eee0 = pLow 0xfee8eee0 := by decide +kernel
theorem f4_fee8eee0 : pLow 0xfee8eee0 ∉ rootWs 0xfee8eee0 := by decide +kernel
theorem f5_fee8eee0 : pLow 0xfee8eee0 ≠ 0 := by decide +kernel
theorem f6_fee8eee0 : pLow 0xfee8eee0 ≠ pFull 0xfee8eee0 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_fee8eee0 : rootRun0 0xfee8eee0 6 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem r1_fee8eee0 : rootRun 0xfee8eee0 (6 + 1) = false := by decide +kernel
theorem tgt_fee8eee0 (gates : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : nNot gates = 1)
    (h3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit 0xfee8eee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Nat.testBit 0xfee8eee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  have hlow := lower 0xfee8eee0 6 f1_fee8eee0 f2_fee8eee0 f3_fee8eee0 f4_fee8eee0 f5_fee8eee0 f6_fee8eee0 r1_fee8eee0 r0_fee8eee0 gates o hg hone h3
  refine ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [10, 11]⟩], 12, ?_, ?_, ?_⟩
  · simp
  · simp only [List.length_cons, List.length_nil]
    omega
  · decide

theorem f1_feeaeaa8 : (pis 0xfeeaeaa8).length = 2 * pN 0xfeeaeaa8 := by decide +kernel
theorem f2_feeaeaa8 : ∀ p ∈ pis 0xfeeaeaa8, p < 32 := by decide +kernel
theorem f3_feeaeaa8 : expand (pis 0xfeeaeaa8) 0xfeeaeaa8 = pLow 0xfeeaeaa8 := by decide +kernel
theorem f4_feeaeaa8 : pLow 0xfeeaeaa8 ∉ rootWs 0xfeeaeaa8 := by decide +kernel
theorem f5_feeaeaa8 : pLow 0xfeeaeaa8 ≠ 0 := by decide +kernel
theorem f6_feeaeaa8 : pLow 0xfeeaeaa8 ≠ pFull 0xfeeaeaa8 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_feeaeaa8 : rootRun0 0xfeeaeaa8 7 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem n0_feeaeaa8 : notAt 0xfeeaeaa8 7 0 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem n1_feeaeaa8 : notAt 0xfeeaeaa8 7 1 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem n2_feeaeaa8 : notAt 0xfeeaeaa8 7 2 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem n3_feeaeaa8 : notAt 0xfeeaeaa8 7 3 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem n4_feeaeaa8 : notAt 0xfeeaeaa8 7 4 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b01a_feeaeaa8 : binAt 0xfeeaeaa8 7 0 1 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b01o_feeaeaa8 : binAt 0xfeeaeaa8 7 0 1 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b02a_feeaeaa8 : binAt 0xfeeaeaa8 7 0 2 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b02o_feeaeaa8 : binAt 0xfeeaeaa8 7 0 2 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b03a_feeaeaa8 : binAt 0xfeeaeaa8 7 0 3 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b03o_feeaeaa8 : binAt 0xfeeaeaa8 7 0 3 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b04a_feeaeaa8 : binAt 0xfeeaeaa8 7 0 4 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b04o_feeaeaa8 : binAt 0xfeeaeaa8 7 0 4 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b12a_feeaeaa8 : binAt 0xfeeaeaa8 7 1 2 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b12o_feeaeaa8 : binAt 0xfeeaeaa8 7 1 2 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b13a_feeaeaa8 : binAt 0xfeeaeaa8 7 1 3 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b13o_feeaeaa8 : binAt 0xfeeaeaa8 7 1 3 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b14a_feeaeaa8 : binAt 0xfeeaeaa8 7 1 4 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b14o_feeaeaa8 : binAt 0xfeeaeaa8 7 1 4 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b23a_feeaeaa8 : binAt 0xfeeaeaa8 7 2 3 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b23o_feeaeaa8 : binAt 0xfeeaeaa8 7 2 3 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b24a_feeaeaa8 : binAt 0xfeeaeaa8 7 2 4 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b24o_feeaeaa8 : binAt 0xfeeaeaa8 7 2 4 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b34a_feeaeaa8 : binAt 0xfeeaeaa8 7 3 4 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b34o_feeaeaa8 : binAt 0xfeeaeaa8 7 3 4 true = false := by decide +kernel
theorem r1_feeaeaa8 : rootRun 0xfeeaeaa8 (7 + 1) = false :=
  root_split 0xfeeaeaa8 7 n0_feeaeaa8 n1_feeaeaa8 n2_feeaeaa8 n3_feeaeaa8 n4_feeaeaa8 b01a_feeaeaa8 b01o_feeaeaa8 b02a_feeaeaa8 b02o_feeaeaa8 b03a_feeaeaa8 b03o_feeaeaa8 b04a_feeaeaa8 b04o_feeaeaa8 b12a_feeaeaa8 b12o_feeaeaa8 b13a_feeaeaa8 b13o_feeaeaa8 b14a_feeaeaa8 b14o_feeaeaa8 b23a_feeaeaa8 b23o_feeaeaa8 b24a_feeaeaa8 b24o_feeaeaa8 b34a_feeaeaa8 b34o_feeaeaa8
theorem tgt_feeaeaa8 (gates : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : nNot gates = 1)
    (h3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit 0xfeeaeaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Nat.testBit 0xfeeaeaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  have hlow := lower 0xfeeaeaa8 7 f1_feeaeaa8 f2_feeaeaa8 f3_feeaeaa8 f4_feeaeaa8 f5_feeaeaa8 f6_feeaeaa8 r1_feeaeaa8 r0_feeaeaa8 gates o hg hone h3
  refine ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [11, 12]⟩], 13, ?_, ?_, ?_⟩
  · simp
  · simp only [List.length_cons, List.length_nil]
    omega
  · decide

theorem f1_feeaeac8 : (pis 0xfeeaeac8).length = 2 * pN 0xfeeaeac8 := by decide +kernel
theorem f2_feeaeac8 : ∀ p ∈ pis 0xfeeaeac8, p < 32 := by decide +kernel
theorem f3_feeaeac8 : expand (pis 0xfeeaeac8) 0xfeeaeac8 = pLow 0xfeeaeac8 := by decide +kernel
theorem f4_feeaeac8 : pLow 0xfeeaeac8 ∉ rootWs 0xfeeaeac8 := by decide +kernel
theorem f5_feeaeac8 : pLow 0xfeeaeac8 ≠ 0 := by decide +kernel
theorem f6_feeaeac8 : pLow 0xfeeaeac8 ≠ pFull 0xfeeaeac8 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_feeaeac8 : rootRun0 0xfeeaeac8 7 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem n0_feeaeac8 : notAt 0xfeeaeac8 7 0 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem n1_feeaeac8 : notAt 0xfeeaeac8 7 1 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem n2_feeaeac8 : notAt 0xfeeaeac8 7 2 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem n3_feeaeac8 : notAt 0xfeeaeac8 7 3 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem n4_feeaeac8 : notAt 0xfeeaeac8 7 4 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b01a_feeaeac8 : binAt 0xfeeaeac8 7 0 1 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b01o_feeaeac8 : binAt 0xfeeaeac8 7 0 1 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b02a_feeaeac8 : binAt 0xfeeaeac8 7 0 2 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b02o_feeaeac8 : binAt 0xfeeaeac8 7 0 2 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b03a_feeaeac8 : binAt 0xfeeaeac8 7 0 3 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b03o_feeaeac8 : binAt 0xfeeaeac8 7 0 3 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b04a_feeaeac8 : binAt 0xfeeaeac8 7 0 4 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b04o_feeaeac8 : binAt 0xfeeaeac8 7 0 4 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b12a_feeaeac8 : binAt 0xfeeaeac8 7 1 2 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b12o_feeaeac8 : binAt 0xfeeaeac8 7 1 2 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b13a_feeaeac8 : binAt 0xfeeaeac8 7 1 3 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b13o_feeaeac8 : binAt 0xfeeaeac8 7 1 3 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b14a_feeaeac8 : binAt 0xfeeaeac8 7 1 4 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b14o_feeaeac8 : binAt 0xfeeaeac8 7 1 4 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b23a_feeaeac8 : binAt 0xfeeaeac8 7 2 3 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b23o_feeaeac8 : binAt 0xfeeaeac8 7 2 3 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b24a_feeaeac8 : binAt 0xfeeaeac8 7 2 4 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b24o_feeaeac8 : binAt 0xfeeaeac8 7 2 4 true = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b34a_feeaeac8 : binAt 0xfeeaeac8 7 3 4 false = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem b34o_feeaeac8 : binAt 0xfeeaeac8 7 3 4 true = false := by decide +kernel
theorem r1_feeaeac8 : rootRun 0xfeeaeac8 (7 + 1) = false :=
  root_split 0xfeeaeac8 7 n0_feeaeac8 n1_feeaeac8 n2_feeaeac8 n3_feeaeac8 n4_feeaeac8 b01a_feeaeac8 b01o_feeaeac8 b02a_feeaeac8 b02o_feeaeac8 b03a_feeaeac8 b03o_feeaeac8 b04a_feeaeac8 b04o_feeaeac8 b12a_feeaeac8 b12o_feeaeac8 b13a_feeaeac8 b13o_feeaeac8 b14a_feeaeac8 b14o_feeaeac8 b23a_feeaeac8 b23o_feeaeac8 b24a_feeaeac8 b24o_feeaeac8 b34a_feeaeac8 b34o_feeaeac8
theorem tgt_feeaeac8 (gates : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : nNot gates = 1)
    (h3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit 0xfeeaeac8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Nat.testBit 0xfeeaeac8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  have hlow := lower 0xfeeaeac8 7 f1_feeaeac8 f2_feeaeac8 f3_feeaeac8 f4_feeaeac8 f5_feeaeac8 f6_feeaeac8 r1_feeaeac8 r0_feeaeac8 gates o hg hone h3
  refine ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [11, 12]⟩], 13, ?_, ?_, ?_⟩
  · simp
  · simp only [List.length_cons, List.length_nil]
    omega
  · decide

theorem f1_feeaece0 : (pis 0xfeeaece0).length = 2 * pN 0xfeeaece0 := by decide +kernel
theorem f2_feeaece0 : ∀ p ∈ pis 0xfeeaece0, p < 32 := by decide +kernel
theorem f3_feeaece0 : expand (pis 0xfeeaece0) 0xfeeaece0 = pLow 0xfeeaece0 := by decide +kernel
theorem f4_feeaece0 : pLow 0xfeeaece0 ∉ rootWs 0xfeeaece0 := by decide +kernel
theorem f5_feeaece0 : pLow 0xfeeaece0 ≠ 0 := by decide +kernel
theorem f6_feeaece0 : pLow 0xfeeaece0 ≠ pFull 0xfeeaece0 := by decide +kernel
set_option maxHeartbeats 0 in
theorem r0_feeaece0 : rootRun0 0xfeeaece0 6 = false := by decide +kernel
set_option maxHeartbeats 0 in
theorem r1_feeaece0 : rootRun 0xfeeaece0 (6 + 1) = false := by decide +kernel
theorem tgt_feeaece0 (gates : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : nNot gates = 1)
    (h3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit 0xfeeaece0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Nat.testBit 0xfeeaece0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  have hlow := lower 0xfeeaece0 6 f1_feeaece0 f2_feeaece0 f3_feeaece0 f4_feeaece0 f5_feeaece0 f6_feeaece0 r1_feeaece0 r0_feeaece0 gates o hg hone h3
  refine ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.and, [5, 9]⟩, ⟨GateOp.or, [10, 11]⟩], 12, ?_, ?_, ?_⟩
  · simp
  · simp only [List.length_cons, List.length_nil]
    omega
  · decide


theorem no_not (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h0 : nNot gates = 0) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hgm
  obtain ⟨hop, hlen⟩ := hg g hgm
  refine ⟨?_, hlen⟩
  unfold nNot at h0
  rw [List.countP_eq_zero] at h0
  have hn := h0 g hgm
  rcases hop with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd ((isNotOp_iff g.op).2 h) hn

theorem main : ∀ T ∈ ({0xfeeaeac0, 0xeeeaeaaa, 0xeeeaeae8, 0xeeeaece8, 0xeeeaeee0, 0xfee8eae8, 0xfee8eee0, 0xfeeaeaa8, 0xfeeaeac8, 0xfeeaece0} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T hT gates o hg h2 h3
  by_cases h0 : nNot gates = 0
  · exact ⟨gates, o, no_not gates hg h0, le_refl _, h3⟩
  · have hone : nNot gates = 1 := by
      have := count_not_le_one gates h2
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tgt_feeaeac0 gates o hg hone h3
    · exact tgt_eeeaeaaa gates o hg hone h3
    · exact tgt_eeeaeae8 gates o hg hone h3
    · exact tgt_eeeaece8 gates o hg hone h3
    · exact tgt_eeeaeee0 gates o hg hone h3
    · exact tgt_fee8eae8 gates o hg hone h3
    · exact tgt_fee8eee0 gates o hg hone h3
    · exact tgt_feeaeaa8 gates o hg hone h3
    · exact tgt_feeaeac8 gates o hg hone h3
    · exact tgt_feeaece0 gates o hg hone h3

end PEqualNP.Outside.L_meta_1441

theorem PEqualNP.Outside.L_meta_1441 : ∀ T ∈ ({0xfeeaeac0, 0xeeeaeaaa, 0xeeeaeae8, 0xeeeaece8, 0xeeeaeee0, 0xfee8eae8, 0xfee8eee0, 0xfeeaeaa8, 0xfeeaeac8, 0xfeeaece0} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_1441.main
