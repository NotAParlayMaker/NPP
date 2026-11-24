import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Nodup
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2956

-- Each wire is recorded on two lists of input rows. A signal and its complement have the
-- same representative, so the count below charges only binary gates.
abbrev Wire (n : ℕ) := BitVec n × BitVec n

def flip {n : ℕ} (a : Wire n) : Wire n := (~~~a.1, ~~~a.2)
def meet {n : ℕ} (a b : Wire n) : Wire n := (a.1 &&& b.1, a.2 &&& b.2)
def phase {n : ℕ} (s : Bool) (a : Wire n) : Wire n := if s then flip a else a
def norm {n : ℕ} (a : Wire n) : Wire n := phase (a.2.getLsbD 0) a
def combine {n : ℕ} (s t : Bool) (a b : Wire n) : Wire n :=
  norm (meet (phase s a) (phase t b))
def goal (n : ℕ) : Wire n := (BitVec.allOnes n ^^^ 1, 0)

lemma flip_flip {n : ℕ} (a : Wire n) : flip (flip a) = a := by
  cases a
  simp [flip]

lemma phase_phase {n : ℕ} (s t : Bool) (a : Wire n) :
    phase s (phase t a) = phase (s ^^ t) a := by
  cases s <;> cases t <;> simp [phase, flip_flip]

lemma norm_phase {n : ℕ} (hn : 0 < n) (s : Bool) (a : Wire n) :
    norm (phase s a) = norm a := by
  cases s
  · rfl
  simp only [norm, phase, ite_true]
  change phase ((flip a).2.getLsbD 0) (flip a) = phase (a.2.getLsbD 0) a
  have h : (flip a).2.getLsbD 0 = !a.2.getLsbD 0 := by
    simp [flip, hn]
  rw [h]
  cases a.2.getLsbD 0 <;> simp [phase, flip_flip]

lemma norm_norm {n : ℕ} (hn : 0 < n) (a : Wire n) : norm (norm a) = norm a :=
  norm_phase hn _ _

lemma norm_zero {n : ℕ} : norm ((0, 0) : Wire n) = (0, 0) := by
  simp [norm, phase]

lemma norm_goal {n : ℕ} : norm (goal n) = goal n := by
  simp [norm, phase, goal]

lemma goal_nonzero {n : ℕ} (hn : 1 < n) : goal n ≠ (0, 0) := by
  intro h
  have bits := congrArg (fun a : Wire n => a.1.getLsbD 1) h
  simp [goal, hn] at bits

lemma meet_comm {n : ℕ} (a b : Wire n) : meet a b = meet b a := by
  simp [meet, BitVec.and_comm]

lemma combine_comm {n : ℕ} (s t : Bool) (a b : Wire n) :
    combine s t a b = combine t s b a := by
  unfold combine
  rw [meet_comm]

lemma combine_zero {n : ℕ} (hn : 0 < n) (s t : Bool) (b : Wire n) :
    combine s t (0, 0) b = (0, 0) ∨ combine s t (0, 0) b = norm b := by
  cases s
  · left
    simpa [combine, phase, meet] using (norm_zero (n := n))
  · right
    simpa [combine, phase, flip, meet, BitVec.allOnes_and] using norm_phase hn t b

lemma combine_same {n : ℕ} (hn : 0 < n) (s t : Bool) (a : Wire n) :
    combine s t a a = (0, 0) ∨ combine s t a a = norm a := by
  cases s <;> cases t
  · right
    simp [combine, phase, meet]
  · left
    simpa [combine, phase, meet, flip] using (norm_zero (n := n))
  · left
    simpa [combine, phase, meet, flip] using (norm_zero (n := n))
  · right
    simpa [combine, phase, meet, flip] using norm_phase hn true a

lemma combine_normed {n : ℕ} (a b : Wire n) (s t : Bool) :
    combine s t (norm a) (norm b) =
      combine (s ^^ a.2.getLsbD 0) (t ^^ b.2.getLsbD 0) a b := by
  simp only [combine, norm]
  rw [phase_phase, phase_phase]

-- A live set records exactly the signals needed by the remaining gates.
def Live {n : ℕ} : ℕ → Finset (Wire n) → Prop
  | 0, S => S = {goal n}
  | k + 1, S =>
    ∃ (a b : Wire n) (s t : Bool) (U : Finset (Wire n)),
      a ≠ (0, 0) ∧ b ≠ (0, 0) ∧ norm a = a ∧ norm b = b ∧ a ≠ b ∧
      let z := combine s t a b
      z ∉ insert a (insert b U) ∧ S = insert a (insert b U) ∧ Live k (insert z U)

lemma live_proper {n k : ℕ} (hn : 1 < n) {S : Finset (Wire n)} (h : Live k S) :
    ∀ a ∈ S, a ≠ (0, 0) ∧ norm a = a := by
  induction k generalizing S with
  | zero =>
    change S = {goal n} at h
    subst S
    intro a ha
    rw [Finset.mem_singleton.mp ha]
    exact ⟨goal_nonzero hn, norm_goal⟩
  | succ k ih =>
    obtain ⟨a, b, s, t, U, ha, hb, hna, hnb, _, _, rfl, ht⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨ha, hna⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hb, hnb⟩
    exact ih ht x (Finset.mem_insert_of_mem hx)

def represented {n : ℕ} (W : Finset (Wire n)) (x : Wire n) : Prop :=
  x = (0, 0) ∨ x ∈ W

def supplied {n : ℕ} (W : Finset (Wire n)) (x : Wire n) : Prop :=
  represented W x ∨
    ∃ (a b : Wire n) (s t : Bool), a ∈ W ∧ b ∈ W ∧
      a ≠ (0, 0) ∧ b ≠ (0, 0) ∧ norm a = a ∧ norm b = b ∧ a ≠ b ∧ x = combine s t a b

lemma supplied_combine {n : ℕ} (hn : 0 < n) (W : Finset (Wire n)) {a b : Wire n}
    (ha : represented W a) (hb : represented W b)
    (hna : norm a = a) (hnb : norm b = b) (s t : Bool) :
    supplied W (combine s t a b) := by
  by_cases az : a = (0, 0)
  · subst a
    apply Or.inl
    rcases combine_zero hn s t b with h | h
    · exact Or.inl h
    · rwa [h, hnb]
  by_cases bz : b = (0, 0)
  · subst b
    rw [combine_comm]
    apply Or.inl
    rcases combine_zero hn t s a with h | h
    · exact Or.inl h
    · rwa [h, hna]
  by_cases hab : a = b
  · subst b
    apply Or.inl
    rcases combine_same hn s t a with h | h
    · exact Or.inl h
    · rwa [h, hna]
  exact Or.inr ⟨a, b, s, t, ha.resolve_left az, hb.resolve_left bz, az, bz, hna, hnb, hab, rfl⟩

lemma pull_gate {n k : ℕ} (hn : 1 < n) {S W : Finset (Wire n)} {z : Wire n}
    (h : Live k S) (hS : S ⊆ insert z W) (hz : supplied W z) :
    ∃ l ≤ k + 1, ∃ T ⊆ W, Live l T := by
  by_cases hW : z ∈ W
  · refine ⟨k, by omega, S, ?_, h⟩
    simpa [Finset.insert_eq_of_mem hW] using hS
  by_cases hZ : z ∈ S
  · have hNZ := (live_proper hn h z hZ).1
    rcases hz with hz | ⟨a, b, s, t, ha, hb, haz, hbz, hna, hnb, hab, rfl⟩
    · exact ((hz.resolve_left hNZ |> hW)).elim
    let U := S.erase (combine s t a b)
    have hU : U ⊆ W := by
      intro x hx
      have hne := (Finset.mem_erase.mp hx).1
      exact (Finset.mem_insert.mp (hS (Finset.mem_of_mem_erase hx))).resolve_left hne
    refine ⟨k + 1, le_rfl, insert a (insert b U), ?_, ?_⟩
    · simpa [Finset.insert_subset_iff, ha, hb] using hU
    · exact ⟨a, b, s, t, U, haz, hbz, hna, hnb, hab, fun hw =>
        hW ((Finset.insert_subset_iff.mpr ⟨ha, Finset.insert_subset_iff.mpr ⟨hb, hU⟩⟩) hw),
        rfl, by simpa [U, Finset.insert_erase hZ] using h⟩
  refine ⟨k, by omega, S, ?_, h⟩
  intro a ha
  exact (Finset.mem_insert.mp (hS ha)).resolve_left (fun heq => hZ (heq ▸ ha))

lemma skip_gate {n k : ℕ} (hn : 1 < n) {S W : Finset (Wire n)} {z : Wire n}
    (h : Live k S) (hS : S ⊆ insert z W) (hz : represented W z) : S ⊆ W := by
  intro a ha
  rcases Finset.mem_insert.mp (hS ha) with rfl | haW
  · exact hz.resolve_left (live_proper hn h a ha).1
  · exact haW


def project {n : ℕ} (m : ℕ) (a : Wire n) : Wire m :=
  (a.1.setWidth m, a.2.setWidth m)

lemma bit_project {n m i : ℕ} (hi : i < m) (a : Wire n) :
    (project m a).1.getLsbD i = a.1.getLsbD i ∧
    (project m a).2.getLsbD i = a.2.getLsbD i := by
  simp [project, hi]

lemma project_flip {n m : ℕ} (hmn : m ≤ n) (a : Wire n) :
    project m (flip a) = flip (project m a) := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · rw [(bit_project hi _).1]
    simp [flip, project, hi, show i < n by omega]
  · rw [(bit_project hi _).2]
    simp [flip, project, hi, show i < n by omega]

lemma project_meet {n m : ℕ} (a b : Wire n) :
    project m (meet a b) = meet (project m a) (project m b) := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · rw [(bit_project hi _).1]
    simp [meet, project, hi]
  · rw [(bit_project hi _).2]
    simp [meet, project, hi]

lemma project_phase {n m : ℕ} (hmn : m ≤ n) (s : Bool) (a : Wire n) :
    project m (phase s a) = phase s (project m a) := by
  cases s <;> simp [phase, project_flip hmn]

lemma project_norm {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) (a : Wire n) :
    project m (norm a) = norm (project m a) := by
  simp only [norm, project_phase hmn, (bit_project hm a).2]

lemma project_combine {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) (s t : Bool) (a b : Wire n) :
    project m (combine s t a b) = combine s t (project m a) (project m b) := by
  simp only [combine, project_norm hm hmn, project_meet, project_phase hmn]

lemma project_goal {n m : ℕ} (hmn : m ≤ n) :
    project m (goal n) = goal m := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [project, goal, hi, show i < n by omega, BitVec.getLsbD_ofNat]
  · simp [project, goal]


def join {n : ℕ} (a b : Wire n) : Wire n := flip (meet (flip a) (flip b))

def readBit {n : ℕ} (s : Bool) (i : ℕ) (a : Wire n) : Bool :=
  (if s then a.1 else a.2).getLsbD i

lemma read_flip {n i : ℕ} (hi : i < n) (s : Bool) (a : Wire n) :
    readBit s i (flip a) = !(readBit s i a) := by
  cases s <;> simp [readBit, flip, hi]

lemma read_meet {n i : ℕ} (s : Bool) (a b : Wire n) :
    readBit s i (meet a b) = (readBit s i a && readBit s i b) := by
  cases s <;> simp [readBit, meet]

lemma read_join {n i : ℕ} (hi : i < n) (s : Bool) (a b : Wire n) :
    readBit s i (join a b) = (readBit s i a || readBit s i b) := by
  rw [join, read_flip hi, read_meet, read_flip hi, read_flip hi]
  cases readBit s i a <;> cases readBit s i b <;> rfl

lemma read_zero {n i : ℕ} (s : Bool) :
    readBit (n := n) s i (0, 0) = false := by cases s <;> simp [readBit]

lemma read_phase {n i : ℕ} (hi : i < n) (s t : Bool) (a : Wire n) :
    readBit s i (phase t a) = (readBit s i a ^^ t) := by
  cases t <;> simp [phase, read_flip hi]

lemma read_default {n i : ℕ} (s : Bool) (w : List (Wire n)) (j : ℕ) :
    (w.map (readBit s i)).getD j false = readBit s i (w.getD j (0, 0)) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (read_zero s).symm
  | some a => rfl

def gateValue {n : ℕ} (w : List (Wire n)) (g : Gate) : Wire n :=
  match g.op with
  | .and => (g.inputs.map fun j => w.getD j (0, 0)).foldr meet (flip (0, 0))
  | .or => (g.inputs.map fun j => w.getD j (0, 0)).foldr join (0, 0)
  | .not => flip (w.getD (g.inputs.headD w.length) (0, 0))
  | _ => (0, 0)

lemma gate_not_value {n : ℕ} (w : List (Wire n)) (l : List ℕ) :
    gateValue w ⟨.not, l⟩ = flip ((l.map fun j => w.getD j (0, 0)).headD (0, 0)) := by
  cases l <;> simp [gateValue]

lemma gate_bit {n i : ℕ} (hi : i < n) (s : Bool) (w : List (Wire n)) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    readBit s i (gateValue w g) =
      g.op.eval (g.inputs.map fun j => (w.map (readBit s i)).getD j false) := by
  obtain ⟨op, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [read_default]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => simp [gateValue, GateOp.eval, read_flip hi]; exact read_zero s
    | cons a l ih =>
      change readBit s i (meet (w.getD a (0, 0)) (gateValue w ⟨.and, l⟩)) =
        (readBit s i (w.getD a (0, 0)) && _)
      rw [read_meet, ih]; rfl
  · induction l with
    | nil => exact read_zero s
    | cons a l ih =>
      change readBit s i (join (w.getD a (0, 0)) (gateValue w ⟨.or, l⟩)) =
        (readBit s i (w.getD a (0, 0)) || _)
      rw [read_join hi, ih]; rfl
  · rw [gate_not_value, read_flip hi]
    cases l with
    | nil => simp [GateOp.eval]; exact read_zero s
    | cons a l => rfl

def record {n : ℕ} (gs : List Gate) (w : List (Wire n)) : List (Wire n) :=
  gs.foldl (fun w g => w ++ [gateValue w g]) w

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w

lemma run_bits {n i : ℕ} (hi : i < n) (s : Bool) (gs : List Gate) (w : List (Wire n))
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (record gs w).map (readBit s i) = run gs (w.map (readBit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (record gs (w ++ [gateValue w g])).map (readBit s i) =
      run gs (w.map (readBit s i) ++ [g.op.eval (g.inputs.map fun j =>
        (w.map (readBit s i)).getD j false)])
    rw [ih _ (fun a ha => h a (List.mem_cons_of_mem g ha)), List.map_append,
      List.map_singleton, gate_bit hi s w g (h g (by simp))]

def signals {n : ℕ} (w : List (Wire n)) : Finset (Wire n) :=
  (w.map norm).toFinset

lemma get_signal {n : ℕ} (w : List (Wire n)) (j : ℕ) :
    represented (signals w) (norm (w.getD j (0, 0))) := by
  by_cases h : j < w.length
  · right
    simp only [signals, List.mem_toFinset, List.mem_map]
    rw [List.getD_eq_getElem _ _ h]
    exact ⟨_, List.getElem_mem h, rfl⟩
  · left
    rw [List.getD_eq_default _ _ (by omega)]
    exact norm_zero

lemma join_zero {n : ℕ} (a : Wire n) : join a (0, 0) = a := by
  simp [join, meet, flip]
lemma meet_one {n : ℕ} (a : Wire n) : meet a (flip (0, 0)) = a := by
  simp [meet, flip]
lemma meet_flip_zero {n : ℕ} (a : Wire n) : meet (flip (0, 0)) a = a := by
  rw [meet_comm, meet_one]
lemma norm_one {n : ℕ} (hn : 0 < n) : norm (flip ((0, 0) : Wire n)) = (0, 0) := by
  rw [show flip ((0, 0) : Wire n) = phase true (0, 0) from rfl, norm_phase hn]
  exact norm_zero

lemma meet_supplied {n : ℕ} (hn : 0 < n) (w : List (Wire n)) (i j : ℕ) :
    supplied (signals w) (norm (meet (w.getD i (0, 0)) (w.getD j (0, 0)))) := by
  let a := w.getD i (0, 0)
  let b := w.getD j (0, 0)
  have h := supplied_combine hn (signals w) (get_signal w i) (get_signal w j)
    (norm_norm hn a) (norm_norm hn b) (a.2.getLsbD 0) (b.2.getLsbD 0)
  rw [combine_normed, Bool.xor_self, Bool.xor_self] at h
  exact h

lemma join_supplied {n : ℕ} (hn : 0 < n) (w : List (Wire n)) (i j : ℕ) :
    supplied (signals w) (norm (join (w.getD i (0, 0)) (w.getD j (0, 0)))) := by
  let a := w.getD i (0, 0)
  let b := w.getD j (0, 0)
  have h := supplied_combine hn (signals w) (get_signal w i) (get_signal w j)
    (norm_norm hn a) (norm_norm hn b)
    (!(a.2.getLsbD 0)) (!(b.2.getLsbD 0))
  have hb (x : Bool) : (!x ^^ x) = true := by cases x <;> rfl
  rw [combine_normed, hb, hb] at h
  rw [join, show flip (meet (flip a) (flip b)) = phase true (meet (flip a) (flip b)) from rfl,
    norm_phase hn]
  exact h

def charged (g : Gate) : Bool :=
  match g.op with
  | .not => false
  | _ => true

lemma not_represented {n : ℕ} (hn : 0 < n) (w : List (Wire n)) (l : List ℕ) :
    represented (signals w) (norm (gateValue w ⟨.not, l⟩)) := by
  change represented (signals w) (norm (phase true (w.getD (l.headD w.length) (0,0))))
  rw [norm_phase hn]
  exact get_signal w _

lemma gate_supplied {n : ℕ} (hn : 0 < n) (w : List (Wire n)) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    supplied (signals w) (norm (gateValue w g)) := by
  obtain ⟨op, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with ⟨rfl | rfl | rfl, hl⟩
  · cases l with
    | nil => exact Or.inl (Or.inl (norm_one hn))
    | cons i l =>
      cases l with
      | nil =>
        apply Or.inl
        change represented (signals w) (norm (meet (w.getD i (0,0)) (flip (0,0))))
        rw [meet_one]
        exact get_signal w i
      | cons j l =>
        cases l with
        | nil =>
          change supplied (signals w)
            (norm (meet (w.getD i (0,0)) (meet (w.getD j (0,0)) (flip (0,0)))))
          rw [meet_one]
          exact meet_supplied hn w i j
        | cons a l => simp at hl
  · cases l with
    | nil => exact Or.inl (Or.inl norm_zero)
    | cons i l =>
      cases l with
      | nil =>
        apply Or.inl
        change represented (signals w) (norm (join (w.getD i (0,0)) (0,0)))
        rw [join_zero]
        exact get_signal w i
      | cons j l =>
        cases l with
        | nil =>
          change supplied (signals w)
            (norm (join (w.getD i (0,0)) (join (w.getD j (0,0)) (0,0))))
          rw [join_zero]
          exact join_supplied hn w i j
        | cons a l => simp at hl
  · exact Or.inl (not_represented (by omega) w l)

lemma signals_snoc {n : ℕ} (w : List (Wire n)) (a : Wire n) :
    signals (w ++ [a]) = insert (norm a) (signals w) := by
  ext x
  simp only [signals, List.map_append, List.map_singleton, List.mem_toFinset,
    List.mem_append, List.mem_singleton, Finset.mem_insert]
  tauto

lemma trace {n : ℕ} (hn : 1 < n) (gs : List Gate) (w : List (Wire n))
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) (hout : goal n ∈ signals (record gs w)) :
    ∃ k ≤ gs.countP charged, ∃ S ⊆ signals w, Live k S := by
  induction gs generalizing w with
  | nil =>
    exact ⟨0, by simp, {goal n}, Finset.singleton_subset_iff.mpr hout, rfl⟩
  | cons g gs ih =>
    change goal n ∈ signals (record gs (w ++ [gateValue w g])) at hout
    obtain ⟨k, hk, S, hS, hLive⟩ := ih _ (fun a ha => h a (List.mem_cons_of_mem g ha)) hout
    rw [signals_snoc] at hS
    by_cases hnot : g.op = .not
    · have hw : represented (signals w) (norm (gateValue w g)) := by
        obtain ⟨op, l⟩ := g
        change op = .not at hnot
        subst op
        exact not_represented (by omega) w l
      have he : charged g = false := by simp [charged, hnot]
      exact ⟨k, by simpa [List.countP_cons, he] using hk, S, skip_gate hn hLive hS hw, hLive⟩
    · have he : charged g = true := by
        cases e : g.op <;> simp_all [charged]
      obtain ⟨j, hj, T, hT, hRun⟩ := pull_gate hn hLive hS (gate_supplied (by omega) w g (h g (by simp)))
      refine ⟨j, ?_, T, hT, hRun⟩
      simp only [List.countP_cons, he, ite_true]
      omega


def sep {n : ℕ} (a : Wire n) : BitVec n := a.1 ^^^ a.2

def cov {n : ℕ} : List (Wire n) → BitVec n
  | [] => 0
  | a :: xs => sep a ||| cov xs

lemma combine_agree {n i : ℕ} (hi : i < n) (s t : Bool) (a b : Wire n)
    (ha : a.1.getLsbD i = a.2.getLsbD i) (hb : b.1.getLsbD i = b.2.getLsbD i) :
    (combine s t a b).1.getLsbD i = (combine s t a b).2.getLsbD i := by
  have resp_phase : ∀ p : Bool, ∀ x : Wire n,
      x.1.getLsbD i = x.2.getLsbD i →
      (phase p x).1.getLsbD i = (phase p x).2.getLsbD i := by
    intro p x hx
    cases p
    · exact hx
    · simpa only [phase, ite_true, flip, Prod.fst, Prod.snd,
        BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and] using congrArg Bool.not hx
  apply resp_phase
  simp [meet, resp_phase _ _ ha, resp_phase _ _ hb]

lemma live_separates {n k i : ℕ} (hi : i < n) (h0 : 0 < i) {S : Finset (Wire n)} (h : Live k S) :
    ∃ a ∈ S, a.1.getLsbD i ≠ a.2.getLsbD i := by
  induction k generalizing S with
  | zero =>
    change S = {goal n} at h
    subst S
    exact ⟨goal n, by simp, by simp [goal, hi, show i ≠ 0 by omega]⟩
  | succ k ih =>
    by_contra! ha
    obtain ⟨a, b, s, t, U, _, _, _, _, _, _, rfl, ht⟩ := h
    obtain ⟨c, hc, hd⟩ := ih ht
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hd (combine_agree hi s t a b (ha _ (by simp)) (ha _ (by simp)))
    · exact hd (ha _ (by simp [hc]))

lemma cov_bit {n i : ℕ} (w : List (Wire n)) :
    (cov w).getLsbD i = true ↔ ∃ a ∈ w, a.1.getLsbD i ≠ a.2.getLsbD i := by
  induction w with
  | nil => simp [cov]
  | cons a w ih =>
    simp only [cov, BitVec.getLsbD_or, sep, BitVec.getLsbD_xor, Bool.or_eq_true,
      bne_iff_ne, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨b, hb, h⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr hb, h⟩
    · rintro ⟨b, (rfl | hb), h⟩
      · exact Or.inl h
      · exact Or.inr ⟨b, hb, h⟩

lemma live_cov {n k : ℕ} {w : List (Wire n)} (h : Live k w.toFinset) :
    cov w ||| 1 = BitVec.allOnes n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_allOnes, decide_eq_true hi, BitVec.getLsbD_or]
  by_cases h0 : i = 0
  · subst i; simp [hi]
  · rw [Bool.or_eq_true]
    left
    rw [cov_bit]
    simpa using live_separates hi (Nat.pos_of_ne_zero h0) h

lemma live_card {n k : ℕ} {S : Finset (Wire n)} (h : Live k S) : S.card ≤ k + 1 := by
  induction k generalizing S with
  | zero =>
    change S = {goal n} at h
    simp [h]
  | succ k ih =>
    obtain ⟨a, b, s, t, U, _, _, _, _, _, hf, rfl, ht⟩ := h
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    have q := ih ht
    rw [Finset.card_insert_of_notMem (fun h => hf (by simp [h]))] at q
    omega

lemma all_required {n k : ℕ} {w : List (Wire n)}
    (hc : w.all (fun a => (cov (w.erase a) ||| 1) != BitVec.allOnes n) = true)
    {S : Finset (Wire n)} (hS : S ⊆ w.toFinset) (h : Live k S) : S = w.toFinset := by
  apply Finset.Subset.antisymm hS
  intro a ha
  by_contra hnot
  have hbad := List.all_eq_true.mp hc a (List.mem_toFinset.mp ha)
  have hcov : cov (w.erase a) ||| 1 = BitVec.allOnes n := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_allOnes, decide_eq_true hi, BitVec.getLsbD_or]
    by_cases h0 : i = 0
    · subst i; simp [hi]
    rw [Bool.or_eq_true]
    left
    rw [cov_bit]
    obtain ⟨b, hB, hd⟩ := live_separates hi (Nat.pos_of_ne_zero h0) h
    have hne : b ≠ a := fun e => hnot (e ▸ hB)
    exact ⟨b, (List.mem_erase_of_ne hne).mpr (List.mem_toFinset.mp (hS hB)), hd⟩
  exact (bne_iff_ne.mp hbad) hcov

-- Projection can remove binary steps when a required wire becomes constant.

def sampleBits (m : ℕ) (f : Fin m → Bool) : BitVec m :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by rw [List.length_ofFn])

lemma sampleBits_bit {m : ℕ} (f : Fin m → Bool) (i : Fin m) :
    (sampleBits m f).getLsbD i = f i := by
  simp only [sampleBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  have hi : i.val < (List.ofFn f).length := by simpa only [List.length_ofFn] using i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_ofFn hi

def selectRows {n m : ℕ} (rows : Fin m → Fin n) (a : Wire n) : Wire m :=
  (sampleBits m fun i => a.1.getLsbD (rows i), sampleBits m fun i => a.2.getLsbD (rows i))

lemma select_bit {n m : ℕ} (rows : Fin m → Fin n) (a : Wire n) (i : Fin m) :
    (selectRows rows a).1.getLsbD i = a.1.getLsbD (rows i) ∧
    (selectRows rows a).2.getLsbD i = a.2.getLsbD (rows i) := by
  exact ⟨sampleBits_bit _ i, sampleBits_bit _ i⟩

lemma select_phase {n m : ℕ} (rows : Fin m → Fin n) (s : Bool) (a : Wire n) :
    selectRows rows (phase s a) = phase s (selectRows rows a) := by
  cases s
  · rfl
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · rw [(select_bit rows _ ⟨i, hi⟩).1]
    change  (~~~a.1).getLsbD (rows ⟨i, hi⟩) = (~~~(selectRows rows a).1).getLsbD i
    simp only [BitVec.getLsbD_not, (rows ⟨i, hi⟩).isLt, hi, decide_true, Bool.true_and]
    exact congrArg Bool.not (select_bit rows _ ⟨i, hi⟩).1.symm
  · rw [(select_bit rows _ ⟨i, hi⟩).2]
    change (~~~a.2).getLsbD (rows ⟨i, hi⟩) = (~~~(selectRows rows a).2).getLsbD i
    simp only [BitVec.getLsbD_not, (rows ⟨i, hi⟩).isLt, hi, decide_true, Bool.true_and]
    exact congrArg Bool.not (select_bit rows _ ⟨i, hi⟩).2.symm

lemma select_meet {n m : ℕ} (rows : Fin m → Fin n) (a b : Wire n) :
    selectRows rows (meet a b) = meet (selectRows rows a) (selectRows rows b) := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · rw [(select_bit rows _ ⟨i, hi⟩).1]
    simp only [meet, BitVec.getLsbD_and, (select_bit rows a ⟨i, hi⟩).1,
      (select_bit rows b ⟨i, hi⟩).1]
  · rw [(select_bit rows _ ⟨i, hi⟩).2]
    simp only [meet, BitVec.getLsbD_and, (select_bit rows a ⟨i, hi⟩).2,
      (select_bit rows b ⟨i, hi⟩).2]

lemma select_norm {n m : ℕ} (rows : Fin m → Fin n) (hm : 0 < m)
    (hfirst : (rows ⟨0, hm⟩).val = 0) (a : Wire n) :
    selectRows rows (norm a) = norm (selectRows rows a) := by
  simp only [norm, select_phase]
  rw [(select_bit rows a ⟨0, hm⟩).2, hfirst]

lemma select_combine {n m : ℕ} (rows : Fin m → Fin n) (hm : 0 < m)
    (hfirst : (rows ⟨0, hm⟩).val = 0) (s t : Bool) (a b : Wire n) :
    selectRows rows (combine s t a b) = combine s t (selectRows rows a) (selectRows rows b) := by
  simp only [combine, select_norm rows hm hfirst, select_meet, select_phase]

lemma select_goal {n m : ℕ} (rows : Fin m → Fin n)
    (hzero : ∀ i : Fin m, (rows i).val = 0 ↔ i.val = 0) :
    selectRows rows (goal n) = goal m := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · rw [(select_bit rows _ ⟨i, hi⟩).1]
    have h := hzero ⟨i, hi⟩
    have hm := (rows ⟨i, hi⟩).isLt
    simp only [goal, BitVec.getLsbD_xor, BitVec.getLsbD_allOnes, hm, hi, decide_true,
      Prod.fst, BitVec.getLsbD_one, Fin.val_mk, Bool.true_xor]
    have eq : decide ((rows ⟨i, hi⟩).val = 0) = decide (i = 0) := decide_eq_decide.mpr h
    have hpos : 0 < m := by omega
    have hnpos : 0 < n := by omega
    simp [eq, hnpos, hpos]
  · rw [(select_bit rows _ ⟨i, hi⟩).2]
    simp [goal]

abbrev Lower {n : ℕ} (q : ℕ) (S : Finset (Wire n)) : Prop :=
  ∀ j T, T ⊆ S → Live j T → q ≤ j

def vanished {n m : ℕ} (ρ : Wire n → Wire m) (S : Finset (Wire n)) : ℕ :=
  (S.filter fun a => ρ a = (0, 0)).card

lemma vanished_insert {n m : ℕ} (ρ : Wire n → Wire m) (a : Wire n)
    (U : Finset (Wire n)) :
    vanished ρ (insert a U) ≤ vanished ρ U + if ρ a = (0, 0) then 1 else 0 := by
  by_cases h : ρ a = (0, 0)
  · simpa only [vanished, Finset.filter_insert, h, ite_true] using
      Finset.card_insert_le a (U.filter fun u => ρ u = (0, 0))
  · simp only [vanished, Finset.filter_insert, h, ite_false, Nat.add_zero, le_rfl]

lemma vanished_insert_eq {n m : ℕ} (ρ : Wire n → Wire m) (a : Wire n)
    (U : Finset (Wire n)) (ha : a ∉ U) :
    vanished ρ (insert a U) =
      vanished ρ U + if ρ a = (0, 0) then 1 else 0 := by
  by_cases h : ρ a = (0, 0)
  · have h' : a ∉ U.filter (fun u => ρ u = (0, 0)) := by simp [ha]
    simp only [vanished, Finset.filter_insert, h, ite_true, Finset.card_insert_of_notMem h']
  · simp only [vanished, Finset.filter_insert, h, ite_false, Nat.add_zero, le_rfl]

lemma lift_step {n m : ℕ} (hm : 1 < m) (ρ : Wire n → Wire m)
    (hcomb : ∀ s t a b, ρ (combine s t a b) = combine s t (ρ a) (ρ b))
    (hnorm : ∀ a, ρ (norm a) = norm (ρ a))
    {a b : Wire n} {s t : Bool} {U : Finset (Wire n)}
    (hna : norm a = a) (hnb : norm b = b)
    {j : ℕ} {T : Finset (Wire m)}
    (hT : T ⊆ (insert (combine s t a b) U).image ρ) (hRun : Live j T) :
    let z := combine s t a b
    let free := ρ a = (0, 0) ∨ ρ b = (0, 0) ∨ ρ z = (0, 0)
    ∃ l ≤ j + (if free then 0 else 1), ∃ V ⊆ (insert a (insert b U)).image ρ, Live l V := by
  let z := combine s t a b
  let W := (insert a (insert b U)).image ρ
  have ha : ρ a ∈ W := Finset.mem_image_of_mem ρ (by simp)
  have hb : ρ b ∈ W := Finset.mem_image_of_mem ρ (by simp)
  have hna' : norm (ρ a) = ρ a := by rw [← hnorm, hna]
  have hnb' : norm (ρ b) = ρ b := by rw [← hnorm, hnb]
  have hW : T ⊆ insert (ρ z) W := by
    rw [Finset.image_insert] at hT
    apply hT.trans (Finset.insert_subset_insert _ _)
    apply Finset.image_mono
    exact fun _ hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  change ∃ l ≤ j + (if ρ a = (0,0) ∨ ρ b = (0,0) ∨ ρ z = (0,0) then 0 else 1),
    ∃ V ⊆ W, Live l V
  by_cases hc : ρ a = (0, 0) ∨ ρ b = (0, 0) ∨ ρ z = (0, 0)
  · have hp : represented W (ρ z) := by
      rcases hc with hz | hz | hz
      · have e : ρ z = combine s t (0, 0) (ρ b) := by simp [z, hcomb, hz]
        rcases combine_zero (by omega) s t (ρ b) with h | h
        · exact Or.inl (e.trans h)
        · exact Or.inr (by rwa [e, h, hnb'])
      · have e : ρ z = combine t s (0, 0) (ρ a) := by simp [z, hcomb, hz, combine_comm s t]
        rcases combine_zero (by omega) t s (ρ a) with h | h
        · exact Or.inl (e.trans h)
        · exact Or.inr (by rwa [e, h, hna'])
      · exact Or.inl hz
    exact ⟨j, by simp only [hc, ite_true, Nat.add_zero, le_rfl], T, skip_gate hm hRun hW hp, hRun⟩
  · have hp : supplied W (ρ z) := by
      dsimp only [z]
      rw [hcomb]
      exact supplied_combine (by omega) W (.inr ha) (.inr hb) hna' hnb' s t
    simpa only [hc, ite_false] using pull_gate hm hRun hW hp

lemma both_zero {n : ℕ} (hn : 0 < n) (s t : Bool) :
    combine s t ((0, 0) : Wire n) (0, 0) = (0, 0) := by
  rcases combine_zero hn s t ((0,0) : Wire n) with h | h
  · exact h
  · exact h.trans norm_zero

lemma live_project_count {n m k : ℕ} (hm : 1 < m) (ρ : Wire n → Wire m)
    (hgoal : ρ (goal n) = goal m)
    (hcomb : ∀ s t a b, ρ (combine s t a b) = combine s t (ρ a) (ρ b))
    (hnorm : ∀ a, ρ (norm a) = norm (ρ a))
    {S : Finset (Wire n)} (h : Live k S) :
    ∃ l, ∃ T ⊆ S.image ρ, Live l T ∧ l + vanished ρ S ≤ k := by
  induction k generalizing S with
  | zero =>
    change S = {goal n} at h
    subst S
    refine ⟨0, {goal m}, ?_, rfl, ?_⟩
    · simp [hgoal]
    · simp only [vanished, Finset.filter_singleton, hgoal, goal_nonzero hm, ite_false, Finset.card_empty, Nat.add_zero, le_rfl]
  | succ k ih =>
    obtain ⟨a, b, s, t, U, _, _, hna, hnb, _, hf, rfl, ht⟩ := h
    obtain ⟨j, T, hT, hRun, hCost⟩ := ih ht
    let z := combine s t a b
    obtain ⟨l, hl, V, hV, hLive⟩ := lift_step hm ρ hcomb hnorm hna hnb hT hRun
    refine ⟨l, V, hV, hLive, ?_⟩
    have hu : z ∉ U := fun h => hf (by simp [z, h])
    have hz := vanished_insert_eq ρ z U hu
    have ha := vanished_insert ρ a (insert b U)
    have hb := vanished_insert ρ b U
    change j + vanished ρ (insert z U) ≤ k at hCost
    change l ≤ j + (if ρ a = (0,0) ∨ ρ b = (0,0) ∨ ρ z = (0,0) then 0 else 1) at hl
    by_cases a0 : ρ a = (0, 0) <;> by_cases b0 : ρ b = (0, 0)
    · have z0 : ρ z = (0, 0) := by dsimp only [z]; rw [hcomb, a0, b0]; exact both_zero (by omega) s t
      simp only [a0, b0, z0, ite_true, true_or, Nat.add_zero] at ha hb hz hl
      omega
    · by_cases z0 : ρ z = (0, 0) <;>
        simp only [a0, b0, z0, ite_true, ite_false, true_or, false_or, or_false, or_true, Nat.add_zero] at ha hb hz hl <;> omega
    · by_cases z0 : ρ z = (0, 0) <;>
        simp only [a0, b0, z0, ite_true, ite_false, true_or, false_or, or_false, or_true, Nat.add_zero] at ha hb hz hl <;> omega
    · by_cases z0 : ρ z = (0, 0) <;>
        simp only [a0, b0, z0, ite_true, ite_false, true_or, false_or, or_false, or_true, Nat.add_zero] at ha hb hz hl <;> omega


-- Lower bounds on projected live sets let the search discard branches early.

abbrev Probe (n : ℕ) := BitVec n × ℕ

def falls {n : ℕ} (mask : BitVec n) (a : Wire n) : Bool :=
  ((a.1 ||| a.2) &&& mask) == 0

def advance {n : ℕ} (ps : List (Probe n)) (a b z : Wire n) : List (Probe n) :=
  ps.map fun p =>
    (p.1, if falls p.1 a || falls p.1 b || falls p.1 z then p.2 else p.2 - 1)

def fits {n : ℕ} (k : ℕ) (ps : List (Probe n)) (w : List (Wire n)) : Bool :=
  ps.all fun p => p.2 + w.countP (falls p.1) ≤ k

def MaskOf {n m : ℕ} (mask : BitVec n) (rows : Fin m → Fin n) : Prop :=
  ∀ i : Fin n, mask.getLsbD i = true ↔ ∃ j, rows j = i

def Monitor {n : ℕ} (ps : List (Probe n)) (S : Finset (Wire n)) : Prop :=
  ∀ p ∈ ps, ∃ (m : ℕ), 1 < m ∧ ∃ rows : Fin m → Fin n,
    (∀ i : Fin m, (rows i).val = 0 ↔ i.val = 0) ∧ MaskOf p.1 rows ∧ Lower p.2 (S.image (selectRows rows))

lemma zero_bit (n i : ℕ) : (0 : BitVec n).getLsbD i = false := by
  simp

lemma falls_spec {n m : ℕ} {mask : BitVec n} {rows : Fin m → Fin n}
    (h : MaskOf mask rows) (a : Wire n) :
    falls mask a = true ↔ selectRows rows a = (0, 0) := by
  unfold falls
  rw [beq_iff_eq]
  constructor
  · intro hz
    have bits (j : Fin m) :
        a.1.getLsbD (rows j) = false ∧ a.2.getLsbD (rows j) = false := by
      have hm := (h (rows j)).2 ⟨j, rfl⟩
      have e := congrArg (fun v : BitVec n => v.getLsbD (rows j)) hz
      simpa only [BitVec.getLsbD_and, BitVec.getLsbD_or, hm, Bool.and_true,
        zero_bit, Bool.or_eq_false_iff] using e
    apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
    · simpa only [Prod.fst, zero_bit] using ((select_bit rows a ⟨i, hi⟩).1).trans (bits ⟨i, hi⟩).1
    · simpa only [Prod.snd, zero_bit] using ((select_bit rows a ⟨i, hi⟩).2).trans (bits ⟨i, hi⟩).2
  · intro hz
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, zero_bit]
    cases hm : mask.getLsbD i
    · exact Bool.and_false _
    · obtain ⟨j, hj⟩ := (h ⟨i, hi⟩).1 hm
      have hb := select_bit rows a j
      rw [hz, hj] at hb
      simp only [← hb.1, ← hb.2, Prod.fst, Prod.snd, zero_bit, Bool.or_self, Bool.false_and]

lemma monitor_step {n : ℕ} {ps : List (Probe n)} {a b : Wire n}
    {s t : Bool} {U : Finset (Wire n)}
    (hna : norm a = a) (hnb : norm b = b)
    (h : Monitor ps (insert a (insert b U))) :
    Monitor (advance ps a b (combine s t a b)) (insert (combine s t a b) U) := by
  intro p hp
  unfold advance at hp
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hp
  obtain ⟨m, hm, rows, first, mask, low⟩ := h p hp' 
  refine ⟨m, hm, rows, first, mask, ?_⟩
  intro j T hT hRun
  have h0 : 0 < m := by omega
  have hf := (first ⟨0,h0⟩).2 rfl
  obtain ⟨l, hl, V, hV, hr⟩ :=
    lift_step hm (selectRows rows) (select_combine rows h0 hf)
      (select_norm rows h0 hf) hna hnb hT hRun
  have hb := low l V hV hr
  dsimp only
  split
  · rename_i hfree
    have hzero : selectRows rows a = (0, 0) ∨ selectRows rows b = (0, 0) ∨
        selectRows rows (combine s t a b) = (0, 0) := by
      simpa only [Bool.or_eq_true, falls_spec mask, or_assoc] using hfree
    simp only [hzero, ite_true, Nat.add_zero] at hl
    omega
  · split at hl <;> omega

lemma count_falls {n m : ℕ} {p : Probe n} {rows : Fin m → Fin n}
    (mask : MaskOf p.1 rows) {w : List (Wire n)} (hn : w.Nodup) :
    w.countP (falls p.1) = vanished (selectRows rows) w.toFinset := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hn.filter _)]
  unfold vanished
  congr 1
  ext a
  simp only [List.mem_toFinset, List.mem_filter, falls_spec mask, Finset.mem_filter]

lemma live_fits {n k : ℕ} {ps : List (Probe n)} {w : List (Wire n)}
    (hn : w.Nodup) (hl : Live k w.toFinset) (hM : Monitor ps w.toFinset) :
    fits k ps w = true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨m, hm, rows, first, mask, low⟩ := hM p hp
  have h0 : 0 < m := by omega
  have hf := (first ⟨0,h0⟩).2 rfl
  obtain ⟨l, T, hT, hr, hCost⟩ := live_project_count hm (selectRows rows)
    (select_goal rows first) (select_combine rows h0 hf) (select_norm rows h0 hf) hl
  have hlow := low l T hT hr
  apply decide_eq_true
  rw [count_falls mask hn]
  omega


-- Enumerate a binary step and the possible choices of operands to retain.

def keep {α : Type} (b : Bool) (a : α) (xs : List α) : List α :=
  if b then a :: xs else xs

def phases : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

def ordered {n : ℕ} (a b : Wire n) : Prop :=
  a.1.toNat < b.1.toNat ∨ (a.1 = b.1 ∧ a.2.toNat < b.2.toNat)

def phaseCandidate {n : ℕ} (k : ℕ) (ps : List (Probe n)) (xs : List (Wire n))
    (a b : Wire n) (r : List (Wire n)) (c : BitVec n)
    (f : List (Probe n) → List (Wire n) → Bool) (p : Bool × Bool) : Bool :=
  let z := combine p.1 p.2 a b
  if z == (0, 0) || xs.contains z then false else
    let ps' := advance ps a b z
    let g := c ||| sep z
    let sa := sep a
    let sb := sep b
    let len := xs.length
    let accept := fun cover w =>
      (cover ||| 1) == BitVec.allOnes n && fits k ps' w && f ps' w
    accept g (z :: r) ||
    (len ≤ k + 1 && (accept (g ||| sa) (z :: a :: r) ||
      accept (g ||| sb) (z :: b :: r))) ||
    (len ≤ k && accept (g ||| sa ||| sb) (z :: a :: b :: r))


def candidates {n : ℕ} (k : ℕ) (ps : List (Probe n)) (xs : List (Wire n))
    (a b : Wire n) (r : List (Wire n)) (f : List (Probe n) → List (Wire n) → Bool) : Bool :=
  let c := cov r
  phases.any (phaseCandidate k ps xs a b r c f)

def scan {n : ℕ} (k : ℕ) (ps : List (Probe n)) (xs : List (Wire n))
    (f : List (Probe n) → List (Wire n) → Bool) : Bool :=
  xs.any fun a =>
    let rest := xs.erase a
    rest.any fun b =>
      if a.1.toNat < b.1.toNat ∨ (a.1 = b.1 ∧ a.2.toNat < b.2.toNat) then
        candidates k ps xs a b (rest.erase b) f
      else false

def search {n : ℕ} : ℕ → List (Probe n) → List (Wire n) → Bool
  | 0, _, xs => xs.contains (goal n)
  | k + 1, ps, xs =>
    xs.contains (goal n) ||
      (xs.length ≤ k + 2 && scan k ps xs (search k))


lemma ordered_or {n : ℕ} {a b : Wire n} (h : a ≠ b) :
    ordered a b ∨ ordered b a := by
  rcases lt_trichotomy a.1.toNat b.1.toNat with hab | eq | hba
  · exact .inl (.inl hab)
  · have eq1 : a.1 = b.1 := BitVec.eq_of_toNat_eq eq
    rcases lt_trichotomy a.2.toNat b.2.toNat with hab | eq | hba
    · exact .inl (.inr ⟨eq1, hab⟩)
    · exact (h (Prod.ext eq1 (BitVec.eq_of_toNat_eq eq))).elim
    · exact .inr (.inr ⟨eq1.symm, hba⟩)
  · exact .inr (.inl hba)

lemma expose {n j : ℕ} {S : Finset (Wire n)} (h : Live (j + 1) S) :
    ∃ (a b : Wire n) (s t : Bool) (U : Finset (Wire n)),
      norm a = a ∧ norm b = b ∧ a ≠ b ∧ ordered a b ∧
      let z := combine s t a b
      z ∉ S ∧ S = insert a (insert b U) ∧ Live j (insert z U) := by
  obtain ⟨a, b, s, t, U, _, _, hna, hnb, hab, hf, rfl, ht⟩ := h
  rcases ordered_or hab with h | h
  · exact ⟨a, b, s, t, U, hna, hnb, hab, h, hf, rfl, ht⟩
  · refine ⟨b, a, t, s, U, hnb, hna, hab.symm, h, ?_, Finset.insert_comm _ _ _, ?_⟩
    · rwa [combine_comm]
    · rwa [combine_comm]

lemma drop_prepare {n : ℕ} {xs : List (Wire n)} (hx : xs.Nodup)
    {a b : Wire n} {U : Finset (Wire n)} (hab : a ≠ b)
    (he : xs.toFinset = insert a (insert b U)) :
    let r := (xs.erase a).erase b
    let tail := keep (decide (a ∈ U)) a (keep (decide (b ∈ U)) b r)
    tail.Nodup ∧ tail.toFinset = U := by
  let r := (xs.erase a).erase b
  let tail := keep (decide (a ∈ U)) a (keep (decide (b ∈ U)) b r)
  have hr : ∀ y, y ∈ r ↔ y ≠ a ∧ y ≠ b ∧ y ∈ U := by
    intro y
    simp only [r, (hx.erase _).mem_erase_iff, hx.mem_erase_iff, ← List.mem_toFinset, he, Finset.mem_insert]
    tauto
  have ha : a ∉ r := fun h => ((hr a).1 h).1 rfl
  have hb : b ∉ r := fun h => ((hr b).1 h).2.1 rfl
  have hrn : r.Nodup := (hx.erase _).erase _
  have mem_keep (flag : Bool) (a x : Wire n) (l : List (Wire n)) :
      x ∈ keep flag a l ↔ (flag = true ∧ x = a) ∨ x ∈ l := by
    cases flag <;> simp [keep]
  have memb : ∀ y, y ∈ tail ↔ y ∈ U := by
    intro y
    simp only [tail, mem_keep, decide_eq_true_eq, hr]
    by_cases h1 : y = a
    · subst y
      simp [hab]
    by_cases h2 : y = b
    · subst y
      simp [hab.symm]
    simp [h1, h2]
  refine ⟨?_, ?_⟩
  · change tail.Nodup
    unfold tail
    by_cases h1 : a ∈ U <;> by_cases h2 : b ∈ U <;>
      simp only [keep, h1, h2, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false,
        List.nodup_cons, List.mem_cons, not_or, ha, hb, hab, hrn, not_false_eq_true,
        true_and, and_self]
  · ext y
    exact (List.mem_toFinset).trans (memb y)

lemma scan_step {n k : ℕ} (hn : 1 < n)
    (ps : List (Probe n)) (xs : List (Wire n)) (hx : xs.Nodup)
    {a b : Wire n} {s t : Bool} {U : Finset (Wire n)}
    (hord : ordered a b) (hab : a ≠ b) (hna : norm a = a) (hnb : norm b = b)
    (he : xs.toFinset = insert a (insert b U)) (hf : combine s t a b ∉ xs.toFinset)
    {j : ℕ} (hj : j ≤ k) (ht : Live j (insert (combine s t a b) U))
    (hM : Monitor ps xs.toFinset)
    (f : List (Probe n) → List (Wire n) → Bool)
    (hF : ∀ (bs : List (Probe n)) (w : List (Wire n)), w.Nodup →
      Live j w.toFinset → Monitor bs w.toFinset → f bs w = true) :
    scan k ps xs f = true := by
  let z := combine s t a b
  let r := (xs.erase a).erase b
  let w := z :: keep (decide (a ∈ U)) a (keep (decide (b ∈ U)) b r)
  let bs := advance ps a b z
  obtain ⟨htn, hte⟩ := drop_prepare hx hab he
  have ha : a ∈ xs := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have hb : b ∈ xs := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hr : b ∈ xs.erase a := hx.mem_erase_iff.mpr ⟨hab.symm, hb⟩
  have hw : w.toFinset = insert z U := by
    rw [show w = z :: _ from rfl, List.toFinset_cons, hte]
  have hwnd : w.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, htn⟩
    intro h
    apply hf
    rw [he]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hte ▸ List.mem_toFinset.mpr h))
  have hRun : Live j w.toFinset := hw ▸ ht
  have hMw : Monitor bs w.toFinset := by
    rw [hw]
    exact monitor_step hna hnb (he ▸ hM)
  have hc := live_cov hRun
  have hfit : fits k bs w = true := by
    have h := live_fits hwnd hRun hMw
    apply List.all_eq_true.mpr
    intro p hp
    have e := decide_eq_true_eq.mp (List.all_eq_true.mp h p hp)
    exact decide_eq_true (le_trans e hj)
  have hres := hF bs w hwnd hRun hMw
  have hlen : w.length ≤ k + 1 := by
    have e := live_card hRun
    rw [List.toFinset_card_of_nodup hwnd] at e
    omega
  have hrlen : r.length = xs.length - 2 := by
    dsimp only [r]
    rw [List.length_erase_of_mem hr, List.length_erase_of_mem ha]
    omega
  have hz0 : z ≠ (0, 0) := (live_proper hn ht z (show z ∈ insert z U by exact Finset.mem_insert_self _ _)).1
  have hz : z ∉ xs := fun hm => hf (List.mem_toFinset.mpr hm)
  have hphase : (s,t) ∈ phases := by cases s <;> cases t <;> decide
  apply List.any_eq_true.mpr
  refine ⟨a, ha, List.any_eq_true.mpr ⟨b, hr, ?_⟩⟩
  change (if a.1.toNat < b.1.toNat ∨ (a.1 = b.1 ∧ a.2.toNat < b.2.toNat) then
    candidates k ps xs a b r f else false) = true
  rw [ite_eq_left (show a.1.toNat < b.1.toNat ∨ (a.1 = b.1 ∧ a.2.toNat < b.2.toNat) from hord)]
  apply List.any_eq_true.mpr
  refine ⟨(s,t), hphase, ?_⟩
  change phaseCandidate k ps xs a b r (cov r) f (s,t) = true
  unfold phaseCandidate
  simp only [Prod.fst, Prod.snd]
  change (if z == (0, 0) || xs.contains z then false else _) = true
  have iftest : (z == (0, 0) || xs.contains z) = false := by
    have hc : xs.contains z = false := Bool.eq_false_iff.mpr (fun h => hz (List.contains_iff_mem.mp h))
    simp only [beq_false_of_ne hz0, hc, Bool.false_or]
  rw [iftest]
  simp only [Bool.false_eq_true, ite_false]
  have hlenxs : 2 ≤ xs.length := by
    have h1 := List.length_pos_of_mem ha
    have h2 := List.length_pos_of_mem hr
    rw [List.length_erase_of_mem ha] at h2
    omega
  unfold w at hc hfit hres hlen
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  by_cases h1 : a ∈ U <;> by_cases h2 : b ∈ U
  · simp only [h1, h2, decide_true, keep, ite_true, List.length_cons] at hc hfit hres hlen
    have hsz : xs.length ≤ k := by omega
    have hh : cov r ||| sep z ||| sep a ||| sep b ||| 1 = BitVec.allOnes n := by
      convert hc using 1
      simp only [cov]
      ac_rfl
    exact Or.inr ⟨hsz, ⟨hh, hfit⟩, hres⟩
  · simp only [h1, h2, decide_true, decide_false, keep, Bool.false_eq_true, ite_true, ite_false, List.length_cons]
      at hc hfit hres hlen
    have hsz : xs.length ≤ k + 1 := by omega
    have hh : cov r ||| sep z ||| sep a ||| 1 = BitVec.allOnes n := by
      convert hc using 1
      simp only [cov]
      ac_rfl
    exact Or.inl (Or.inr ⟨hsz, Or.inl ⟨⟨hh, hfit⟩, hres⟩⟩)
  · simp only [h1, h2, decide_true, decide_false, keep, Bool.false_eq_true, ite_true, ite_false, List.length_cons]
      at hc hfit hres hlen
    have hsz : xs.length ≤ k + 1 := by omega
    have hh : cov r ||| sep z ||| sep b ||| 1 = BitVec.allOnes n := by
      convert hc using 1
      simp only [cov]
      ac_rfl
    exact Or.inl (Or.inr ⟨hsz, Or.inr ⟨⟨hh, hfit⟩, hres⟩⟩)
  · simp only [h1, h2, decide_false, keep, Bool.false_eq_true, ite_false] at hc hfit hres
    have hh : cov r ||| sep z ||| 1 = BitVec.allOnes n := by
      convert hc using 1
      simp only [cov]
      ac_rfl
    exact Or.inl (Or.inl ⟨⟨hh, hfit⟩, hres⟩)

lemma search_complete {n k : ℕ} (hn : 1 < n) {ps : List (Probe n)} {xs : List (Wire n)}
    (hx : xs.Nodup) (hM : Monitor ps xs.toFinset) {j : ℕ} (hj : j ≤ k)
    (h : Live j xs.toFinset) : search k ps xs = true := by
  induction k generalizing j xs ps with
  | zero =>
    have e : j = 0 := by omega
    subst j
    change xs.toFinset = {goal n} at h
    have m : goal n ∈ xs := List.mem_toFinset.mp (h.symm ▸ Finset.mem_singleton_self _)
    simpa only [search, List.contains_iff_mem] using m
  | succ k ih =>
    by_cases hzero : j = 0
    · subst j
      change xs.toFinset = {goal n} at h
      have m : goal n ∈ xs := List.mem_toFinset.mp (h.symm ▸ Finset.mem_singleton_self _)
      simp [search, m]
    cases j with
    | zero => contradiction
    | succ j =>
      have hcard := live_card h
      rw [List.toFinset_card_of_nodup hx] at hcard
      have hsize : xs.length ≤ k + 2 := by omega
      simp only [search, Bool.or_eq_true, Bool.and_eq_true]
      right
      refine ⟨decide_eq_true hsize, ?_⟩
      obtain ⟨a, b, s, t, U, hna, hnb, hab, hord, hf, he, ht⟩ := expose h
      exact scan_step hn ps xs hx hord hab hna hnb he hf (by omega) ht hM (search k)
        (fun bs w hnd hr hm => ih hnd hm (by omega) hr)

lemma lower_checked {n k : ℕ} (hn : 1 < n) (ps : List (Probe n)) (xs : List (Wire n))
    (hx : xs.Nodup) (hc : xs.all (fun a => (cov (xs.erase a) ||| 1) != BitVec.allOnes n) = true)
    (hM : Monitor ps xs.toFinset) (hb : search k ps xs = false) :
    Lower (k + 1) xs.toFinset := by
  intro j S hS h
  by_contra! hj
  have hep := all_required hc hS h
  subst S
  have e := search_complete hn hx hM (show j ≤ k by omega) h
  rw [e] at hb
  contradiction


-- The columns encode adjacent positive and negative rows. Row zero is the all-false anchor.
def rootRaw : List (Wire 88) :=
  [(0x4b2012319819e3287cfce6, 0x4b201231901163284894a4),
   (0x3a60c21926043f9327fe, 0x1260c209040405122252),
   (0x83c48303e6387831e3c738, 0x8284830146387830e1c528),
   (0xc0703fc07c07fc1fc07c0, 0x703a805805681fc07c0),
   (0xf007fc0007ff8001fff800, 0xa007c80007ee8001b76800),
   (0xfff8000007fffffe000000, 0xffe80000027ba97a000000),
   (0xfffffffff8000000000000, 0x5d783456b8000000000000)]

def root : List (Wire 88) := rootRaw.map norm

def rows1 : Fin 49 → Fin 88 := ![0, 3, 4, 8, 9, 16, 17, 23, 24, 25, 26, 28, 30, 31, 34, 35, 36, 41, 42, 45, 46, 47, 48, 49, 50, 53, 54, 57, 58, 59, 62, 63, 64, 66, 67, 69, 70, 71, 72, 73, 74, 75, 76, 78, 79, 82, 84, 85, 87]

def subRaw1 : List (Wire 49) :=
  [(0x698c84e4ffe, 0x498c8444554),
   (0x119210f8989fe, 0x11121058988aa),
   (0x21c1f1f1f198, 0x1c1a1616198),
   (0x1c1fe01fe01e0, 0x181f401fe01e0),
   (0x1fe0001fffe00, 0x1fa00009a9a00),
   (0x1fffffe000000, 0x6e0a5a000000)]

def subRoot1 : List (Wire 49) := subRaw1.map norm

lemma subMask1 : MaskOf 0xb4dfedce67e61cd7830319 rows1 := by unfold MaskOf; decide +kernel

def rows4 : Fin 49 → Fin 88 := ![0, 1, 2, 6, 7, 11, 12, 13, 18, 19, 20, 25, 26, 27, 30, 31, 32, 33, 34, 39, 40, 41, 42, 46, 47, 48, 51, 52, 58, 59, 60, 61, 62, 63, 66, 67, 68, 69, 70, 72, 73, 75, 76, 77, 82, 83, 84, 85, 86]

def subRaw4 : List (Wire 49) :=
  [(0x12810cc1b27fe, 0x12810c8132254),
   (0xf630e643c9e, 0x5630644148a),
   (0x3183f387c718, 0x182a3068718),
   (0x1c1fc03f807e0, 0x81c803e805a0),
   (0x1fe0003fff800, 0x1fa0000b96800),
   (0x1fffffc000000, 0x17e355c000000)]

def subRoot4 : List (Wire 49) := subRaw4.map norm

lemma subMask4 : MaskOf 0x7c3b7cfc19c787ce1c38c7 rows4 := by unfold MaskOf; decide +kernel

def rows8 : Fin 49 → Fin 88 := ![0, 1, 2, 3, 4, 5, 11, 12, 13, 14, 15, 16, 17, 25, 26, 27, 28, 29, 39, 40, 41, 42, 43, 44, 45, 51, 52, 53, 54, 55, 56, 57, 66, 67, 68, 69, 70, 71, 75, 76, 77, 78, 79, 80, 81, 84, 85, 86, 87]

def subRaw8 : List (Wire 49) :=
  [(0x990466ce87e6, 0x9904648a84a4),
   (0x1d88733f93e, 0x9882205112),
   (0x11e20f9c31e38, 0x1142051c30e28),
   (0x1e03f01fc1fc0, 0x1403201741b40),
   (0x1ffc001ffe000, 0x1ff4001dfa000),
   (0x1fffffe000000, 0xabcdae000000)]

def subRoot8 : List (Wire 49) := subRaw8.map norm

lemma subMask8 : MaskOf 0xf3f8fc03f83f803e03f83f rows8 := by unfold MaskOf; decide +kernel

def rows16 : Fin 49 → Fin 88 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 75, 76, 77, 78, 79, 80, 81, 82, 83]

def subRaw16 : List (Wire 49) :=
  [(0x1648c678ca4e6, 0x1648c658ca4a4),
   (0x7308610fffe, 0x23082101252),
   (0x78c0f9e0c738, 0x50c051e0c528),
   (0x180ff01ff07c0, 0xea015a07c0),
   (0x1ff0001fff800, 0x1fd0000a5e800),
   (0x1fffffe000000, 0x1af15ae000000)]

def subRoot16 : List (Wire 49) := subRaw16.map norm

lemma subMask16 : MaskOf 0xff803fff8007ffe0007ff rows16 := by unfold MaskOf; decide +kernel

def rows32 : Fin 49 → Fin 88 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74]

def subRaw32 : List (Wire 49) :=
  [(0x48c667cfce6, 0x48c644894a4),
   (0x9830879327fe, 0x983083122252),
   (0x120c0f9e3c738, 0x120c050e1c528),
   (0x1c0ff01fc07c0, 0x1c0ea01fc07c0),
   (0x1ff0001fff800, 0x1f20001b76800),
   (0x1fffffe000000, 0xd15ae000000)]

def subRoot32 : List (Wire 49) := subRaw32.map norm

lemma subMask32 : MaskOf 0x7fffff8000001ffffff rows32 := by unfold MaskOf; decide +kernel

def rows2 : Fin 51 → Fin 88 := ![0, 11, 12, 14, 15, 18, 19, 21, 22, 30, 31, 32, 33, 35, 36, 37, 38, 39, 40, 43, 44, 46, 47, 49, 50, 53, 54, 55, 56, 58, 59, 60, 61, 64, 65, 66, 67, 68, 71, 72, 74, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87]

def subRaw2 : List (Wire 51) :=
  [(0x25825981f99fe, 0x2582598159954),
   (0x41f461f99e198, 0x415461599e198),
   (0x6187e1e1ffe0, 0x187414155e0),
   (0x781f801fe01fe, 0x501d001ea00aa),
   (0x7fe0001fffe00, 0x7fe0000beaa00),
   (0x7fffffe000000, 0x2ea28aa000000)]

def subRoot2 : List (Wire 51) := subRaw2.map norm

lemma subMask2 : MaskOf 0xffc59f3de6d9fbc06cd801 rows2 := by unfold MaskOf; decide +kernel

def rows64 : Fin 51 → Fin 88 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]

def subRaw64 : List (Wire 51) :=
  [(0x19e3287cfce6, 0x1163284894a4),
   (0x126043f9327fe, 0x1040405122252),
   (0x6387831e3c738, 0x6387830e1c528),
   (0x7c07fc1fc07c0, 0x5805681fc07c0),
   (0x7ff8001fff800, 0x7ee8001b76800),
   (0x7fffffe000000, 0x27ba97a000000)]

def subRoot64 : List (Wire 51) := subRaw64.map norm

lemma subMask64 : MaskOf 0x7ffffffffffff rows64 := by unfold MaskOf; decide +kernel

def rows17 : Fin 26 → Fin 88 := ![0, 3, 4, 8, 9, 25, 26, 28, 30, 31, 34, 35, 36, 53, 54, 57, 58, 59, 62, 63, 64, 75, 76, 78, 79, 82]

def subRaw17 : List (Wire 26) :=
  [(0x6c84fe, 0x4c8454),
   (0x190f89e, 0x110588a),
   (0x21f1f18, 0x1a1618),
   (0x3e01fe0, 0x3a009a0),
   (0x3ffe000, 0x2e5a000)]

def subRoot17 : List (Wire 26) := subRaw17.map norm

lemma subMask17 : MaskOf 0x4d801ce60001cd6000319 rows17 := by unfold MaskOf; decide +kernel

def rows40 : Fin 26 → Fin 88 := ![0, 1, 2, 3, 4, 5, 11, 12, 13, 14, 15, 16, 17, 51, 52, 53, 54, 55, 56, 57, 66, 67, 68, 69, 70, 71]

def subRaw40 : List (Wire 26) :=
  [(0x4667e6, 0x4644a4),
   (0x188793e, 0x1883112),
   (0x20f9e38, 0x2050e28),
   (0x3f01fc0, 0x3201b40),
   (0x3ffe000, 0xdae000)]

def subRoot40 : List (Wire 26) := subRaw40.map norm

lemma subMask40 : MaskOf 0xfc03f800000003f83f rows40 := by unfold MaskOf; decide +kernel

def rows7 : Fin 13 → Fin 88 := ![0, 30, 31, 46, 47, 58, 59, 66, 67, 72, 82, 84, 85]

def subRaw7 : List (Wire 13) :=
  [(0x67e, 0x254),
   (0x1b98, 0x1318),
   (0x1c1e, 0x1c0a),
   (0x1fe0, 0xca0)]

def subRoot7 : List (Wire 13) := subRaw7.map norm

lemma subMask7 : MaskOf 0x34010c0c00c000c0000001 rows7 := by unfold MaskOf; decide +kernel

def rows84 : Fin 13 → Fin 88 := ![0, 1, 2, 6, 7, 25, 26, 27, 30, 31, 32, 33, 34]

def subRaw84 : List (Wire 13) :=
  [(0xc9e, 0xc94),
   (0x10fe, 0x104a),
   (0x1f18, 0x1a18),
   (0x1fe0, 0x5a0)]

def subRoot84 : List (Wire 13) := subRaw84.map norm

lemma subMask84 : MaskOf 0x7ce0000c7 rows84 := by unfold MaskOf; decide +kernel

def rows38 : Fin 13 → Fin 88 := ![0, 11, 12, 18, 19, 58, 59, 60, 61, 66, 67, 68, 72]

def subRaw38 : List (Wire 13) :=
  [(0x99e, 0x994),
   (0x11f8, 0x1158),
   (0x1e1e, 0x140a),
   (0x1fe0, 0xaa0)]

def subRoot38 : List (Wire 13) := subRaw38.map norm

lemma subMask38 : MaskOf 0x11c3c000000000c1801 rows38 := by unfold MaskOf; decide +kernel

def rows76 : Fin 13 → Fin 88 := ![0, 1, 2, 11, 12, 13, 25, 26, 27, 39, 40, 41, 42]

def subRaw76 : List (Wire 13) :=
  [(0x73e, 0x514),
   (0x19e6, 0x10a2),
   (0x1e38, 0x1a28),
   (0x1fc0, 0xf40)]

def subRoot76 : List (Wire 13) := subRaw76.map norm

lemma subMask76 : MaskOf 0x7800e003807 rows76 := by unfold MaskOf; decide +kernel

def probes : List (Probe 88) :=
  [(0xb4dfedce67e61cd7830319, 8),
   (0x7c3b7cfc19c787ce1c38c7, 8),
   (0xf3f8fc03f83f803e03f83f, 8),
   (0xff803fff8007ffe0007ff, 8),
   (0x7fffff8000001ffffff, 8),
   (0xffc59f3de6d9fbc06cd801, 7),
   (0x7ffffffffffff, 7),
   (0x4d801ce60001cd6000319, 7),
   (0xfc03f800000003f83f, 7),
   (0x34010c0c00c000c0000001, 4),
   (0x7ce0000c7, 4),
   (0x11c3c000000000c1801, 4),
   (0x7800e003807, 4)]

-- Split the finite checks after the first two steps to bound peak memory.

abbrev State (n : ℕ) := List (Probe n) × List (Wire n)

def whenFits {α : Type} (ok : Bool) (a : α) : List α :=
  if ok then [a] else []

lemma any_whenFits {α : Type} (ok : Bool) (a : α) (f : α → Bool) :
    (whenFits ok a).any f = (ok && f a) := by
  cases ok <;> simp [whenFits]

def phaseEntries {n : ℕ} (k : ℕ) (ps : List (Probe n)) (xs : List (Wire n))
    (a b : Wire n) (r : List (Wire n)) (c : BitVec n) (p : Bool × Bool) : List (State n) :=
  let z := combine p.1 p.2 a b
  if z == (0, 0) || xs.contains z then [] else
    let ps' := advance ps a b z
    let g := c ||| sep z
    let sa := sep a
    let sb := sep b
    let len := xs.length
    let accept := fun cover w =>
      (cover ||| 1) == BitVec.allOnes n && fits k ps' w
    whenFits (accept g (z :: r)) (ps', z :: r) ++
    (if len ≤ k + 1 then
      whenFits (accept (g ||| sa) (z :: a :: r)) (ps', z :: a :: r) ++
      whenFits (accept (g ||| sb) (z :: b :: r)) (ps', z :: b :: r)
      else []) ++
    (if len ≤ k then
      whenFits (accept (g ||| sa ||| sb) (z :: a :: b :: r)) (ps', z :: a :: b :: r)
      else [])

lemma phase_entries {n : ℕ} (k : ℕ) (ps : List (Probe n)) (xs : List (Wire n))
    (a b : Wire n) (r : List (Wire n)) (c : BitVec n)
    (f : List (Probe n) → List (Wire n) → Bool) (p : Bool × Bool) :
    phaseCandidate k ps xs a b r c f p =
      (phaseEntries k ps xs a b r c p).any (fun st => f st.1 st.2) := by
  dsimp only [phaseCandidate, phaseEntries]
  split
  · rfl
  · by_cases h1 : xs.length ≤ k + 1 <;> by_cases h2 : xs.length ≤ k <;>
      simp [h1, h2, List.any_append, any_whenFits, Bool.or_assoc]

def scanEntries {n : ℕ} (k : ℕ) (ps : List (Probe n)) (xs : List (Wire n)) : List (State n) :=
  xs.flatMap fun a =>
    let rest := xs.erase a
    rest.flatMap fun b =>
      if a.1.toNat < b.1.toNat ∨ (a.1 = b.1 ∧ a.2.toNat < b.2.toNat) then
        let r := rest.erase b
        phases.flatMap (phaseEntries k ps xs a b r (cov r))
      else []

lemma scan_entries {n : ℕ} (k : ℕ) (ps : List (Probe n)) (xs : List (Wire n))
    (f : List (Probe n) → List (Wire n) → Bool) :
    scan k ps xs f = (scanEntries k ps xs).any (fun st => f st.1 st.2) := by
  unfold scan scanEntries
  simp only [List.any_flatMap]
  congr 1
  funext a
  congr 1
  funext b
  split
  · simp only [candidates, List.any_flatMap]
    congr 1
    funext p
    exact phase_entries _ _ _ _ _ _ _ _ _
  · rfl

def firstEntries (i j : Fin 7) (p : Bool × Bool) : List (State 88) :=
  let a := root.getD i.val (0, 0)
  let b := root.getD j.val (0, 0)
  let r := (root.erase a).erase b
  if a.1.toNat < b.1.toNat ∨ (a.1 = b.1 ∧ a.2.toNat < b.2.toNat) then
    phaseEntries 9 probes root a b r (cov r) p
  else []

def secondEntries (i j : Fin 7) (p : Bool × Bool) : List (State 88) :=
  (firstEntries i j p).flatMap fun st => scanEntries 8 st.1 st.2

def phaseDone (i j : Fin 7) (p : Bool × Bool) : Bool :=
  let a := root.getD i.val (0, 0)
  let b := root.getD j.val (0, 0)
  let r := (root.erase a).erase b
  if a.1.toNat < b.1.toNat ∨ (a.1 = b.1 ∧ a.2.toNat < b.2.toNat) then
    !phaseCandidate 9 probes root a b r (cov r) (search 9) p
  else true

def passed (st : State 88) : Bool := !search 8 st.1 st.2

def chunk (i j : Fin 7) (p : Bool × Bool) (offset len : ℕ) : Bool :=
  (((secondEntries i j p).drop offset).take len).all passed

lemma take_sum {α : Type} (l : List α) (a b : ℕ) :
    l.take (a + b) = l.take a ++ (l.drop a).take b := by
  induction a generalizing l with
  | zero => simp
  | succ a ih =>
    cases l with
    | nil => simp
    | cons x l => simp [Nat.succ_add, ih]

lemma chunk_join {i j : Fin 7} {p : Bool × Bool} {off a b : ℕ}
    (ha : chunk i j p off a = true) (hb : chunk i j p (off + a) b = true) :
    chunk i j p off (a + b) = true := by
  unfold chunk at ha hb ⊢
  rw [take_sum, List.drop_drop, List.all_append, ha, hb]
  rfl

lemma phase_split {i j : Fin 7} {p : Bool × Bool} {len : ℕ}
    (h1 : (firstEntries i j p).all (fun st => !(st.2.contains (goal 88))) = true)
    (hlen : (secondEntries i j p).length ≤ len) (h2 : chunk i j p 0 len = true) :
    phaseDone i j p = true := by
  have fall : (secondEntries i j p).all passed = true := by
    simpa only [chunk, List.drop_zero, List.take_of_length_le hlen] using h2
  have hbad (st : State 88) (hs : st ∈ firstEntries i j p) :
      search 9 st.1 st.2 = false := by
    have h0 : st.2.contains (goal 88) = false := by
      simpa only [Bool.not_eq_true'] using List.all_eq_true.mp h1 st hs
    have hnext : scan 8 st.1 st.2 (search 8) = false := by
      rw [scan_entries]
      apply Bool.eq_false_iff.mpr
      intro he
      obtain ⟨w, hw, ht⟩ := List.any_eq_true.mp he
      have hit : w ∈ secondEntries i j p := List.mem_flatMap.mpr ⟨st, hs, hw⟩
      have hclear := List.all_eq_true.mp fall w hit
      change !search 8 w.1 w.2 = true at hclear
      rw [ht] at hclear
      exact Bool.noConfusion hclear
    rw [search, h0, hnext]
    simp
  dsimp only [phaseDone]
  split
  · rename_i ho
    rw [phase_entries]
    rw [Bool.not_eq_true']
    apply Bool.eq_false_iff.mpr
    intro hx
    obtain ⟨st, hm, hh⟩ := List.any_eq_true.mp hx
    have hs : st ∈ firstEntries i j p := by simpa only [firstEntries, ho, ite_true] using hm
    have hfalse := hbad st hs
    rw [hfalse] at hh
    exact Bool.noConfusion hh
  · rfl


lemma lower_restrict {n m q : ℕ} (hm : 1 < m) {S : Finset (Wire n)} {T : Finset (Wire m)}
    (rows : Fin m → Fin n) (hzero : ∀ i : Fin m, (rows i).val = 0 ↔ i.val = 0)
    (hset : S.image (selectRows rows) = T) (h : Lower q T) :
    Lower q S := by
  intro j V hV hRun
  have hp : 0 < m := by omega
  have hz := (hzero ⟨0, hp⟩).2 rfl
  obtain ⟨l, U, hU, hLive, hbound⟩ := live_project_count hm (selectRows rows)
    (select_goal rows hzero) (select_combine rows hp hz) (select_norm rows hp hz) hRun
  have sub : U ⊆ T := by rw [← hset]; exact hU.trans (Finset.image_mono _ hV)
  have loc := h l U sub hLive
  omega

def reuseRows8 : Fin 49 → Fin 49 := ![0, 7, 6, 10, 9, 19, 18, 23, 22, 32, 33, 34, 27, 28, 37, 29, 30, 45, 46, 47, 41, 42, 48, 43, 44, 1, 2, 8, 4, 3, 12, 11, 5, 14, 13, 21, 20, 15, 16, 24, 17, 35, 36, 25, 26, 31, 39, 38, 40]

lemma reuseZero8 : ∀ i : Fin 49, (reuseRows8 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reuseImage8 : subRoot8.toFinset.image (selectRows reuseRows8) = subRoot1.toFinset := by
  decide +kernel

def reuseRows16 : Fin 49 → Fin 49 := ![0, 16, 17, 21, 22, 18, 19, 23, 24, 32, 33, 47, 27, 28, 38, 43, 44, 34, 35, 48, 29, 30, 39, 45, 46, 12, 11, 20, 4, 3, 9, 8, 14, 1, 2, 6, 7, 13, 5, 10, 15, 36, 37, 41, 40, 31, 25, 26, 42]

lemma reuseZero16 : ∀ i : Fin 49, (reuseRows16 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reuseImage16 : subRoot16.toFinset.image (selectRows reuseRows16) = subRoot1.toFinset := by
  decide +kernel

def reuseRows32 : Fin 49 → Fin 49 := ![0, 11, 12, 14, 15, 18, 19, 21, 22, 1, 2, 13, 4, 3, 5, 17, 16, 6, 7, 20, 9, 8, 10, 24, 23, 40, 41, 42, 27, 28, 29, 30, 45, 32, 33, 34, 35, 46, 38, 39, 48, 25, 26, 43, 44, 31, 36, 37, 47]

lemma reuseZero32 : ∀ i : Fin 49, (reuseRows32 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reuseImage32 : subRoot32.toFinset.image (selectRows reuseRows32) = subRoot1.toFinset := by
  decide +kernel

def reuseRows64 : Fin 51 → Fin 51 := ![0, 30, 31, 35, 36, 32, 33, 37, 38, 11, 12, 18, 19, 14, 15, 21, 22, 46, 47, 49, 50, 39, 40, 43, 44, 4, 3, 9, 8, 1, 2, 6, 7, 5, 10, 26, 25, 34, 28, 27, 29, 17, 16, 24, 23, 13, 20, 42, 41, 48, 45]

lemma reuseZero64 : ∀ i : Fin 51, (reuseRows64 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reuseImage64 : subRoot64.toFinset.image (selectRows reuseRows64) = subRoot2.toFinset := by
  decide +kernel

def reuseRows40 : Fin 26 → Fin 26 := ![0, 1, 2, 13, 14, 6, 7, 8, 21, 20, 22, 24, 23, 3, 4, 5, 16, 15, 18, 17, 19, 9, 10, 11, 12, 25]

lemma reuseZero40 : ∀ i : Fin 26, (reuseRows40 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reuseImage40 : subRoot40.toFinset.image (selectRows reuseRows40) = subRoot17.toFinset := by
  decide +kernel

def reuseRows84 : Fin 13 → Fin 13 := ![0, 2, 1, 4, 3, 5, 6, 8, 9, 12, 7, 10, 11]

lemma reuseZero84 : ∀ i : Fin 13, (reuseRows84 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reuseImage84 : subRoot84.toFinset.image (selectRows reuseRows84) = subRoot7.toFinset := by
  decide +kernel

def reuseRows38 : Fin 13 → Fin 13 := ![0, 2, 1, 4, 3, 9, 10, 5, 6, 12, 11, 7, 8]

lemma reuseZero38 : ∀ i : Fin 13, (reuseRows38 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reuseImage38 : subRoot38.toFinset.image (selectRows reuseRows38) = subRoot7.toFinset := by
  decide +kernel

def reuseRows76 : Fin 13 → Fin 13 := ![0, 3, 4, 9, 10, 1, 2, 7, 6, 8, 5, 12, 11]

lemma reuseZero76 : ∀ i : Fin 13, (reuseRows76 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma reuseImage76 : subRoot76.toFinset.image (selectRows reuseRows76) = subRoot7.toFinset := by
  decide +kernel


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma subChecked1 : search 7 [] subRoot1 = false := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma subChecked4 : search 7 [] subRoot4 = false := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma subChecked2 : search 6 [] subRoot2 = false := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma subChecked17 : search 6 [] subRoot17 = false := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma subChecked7 : search 3 [] subRoot7 = false := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_2_tt_0 : chunk 0 2 (true, true) 0 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_2_tt_4 : chunk 0 2 (true, true) 4 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_2_tt_8 : chunk 0 2 (true, true) 8 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_2_tt_12 : chunk 0 2 (true, true) 12 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_2_tt_16 : chunk 0 2 (true, true) 16 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_2_tt_20 : chunk 0 2 (true, true) 20 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_2_tt_24 : chunk 0 2 (true, true) 24 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_2_tt_28 : chunk 0 2 (true, true) 28 1 = true := by decide +kernel

lemma checked_0_2_tt : phaseDone 0 2 (true, true) = true := by
  apply phase_split (len := 29) (by decide +kernel) (by decide +kernel)
  exact (chunk_join (off := 0) (a := 16) (b := 13) (chunk_join (off := 0) (a := 8) (b := 8) (chunk_join (off := 0) (a := 4) (b := 4) slice_0_2_tt_0 slice_0_2_tt_4) (chunk_join (off := 8) (a := 4) (b := 4) slice_0_2_tt_8 slice_0_2_tt_12)) (chunk_join (off := 16) (a := 8) (b := 5) (chunk_join (off := 16) (a := 4) (b := 4) slice_0_2_tt_16 slice_0_2_tt_20) (chunk_join (off := 24) (a := 4) (b := 1) slice_0_2_tt_24 slice_0_2_tt_28)))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_5_tt_0 : chunk 0 5 (true, true) 0 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_5_tt_4 : chunk 0 5 (true, true) 4 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_5_tt_8 : chunk 0 5 (true, true) 8 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_5_tt_12 : chunk 0 5 (true, true) 12 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_5_tt_16 : chunk 0 5 (true, true) 16 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_5_tt_20 : chunk 0 5 (true, true) 20 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_5_tt_24 : chunk 0 5 (true, true) 24 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_5_tt_28 : chunk 0 5 (true, true) 28 4 = true := by decide +kernel

lemma checked_0_5_tt : phaseDone 0 5 (true, true) = true := by
  apply phase_split (len := 32) (by decide +kernel) (by decide +kernel)
  exact (chunk_join (off := 0) (a := 16) (b := 16) (chunk_join (off := 0) (a := 8) (b := 8) (chunk_join (off := 0) (a := 4) (b := 4) slice_0_5_tt_0 slice_0_5_tt_4) (chunk_join (off := 8) (a := 4) (b := 4) slice_0_5_tt_8 slice_0_5_tt_12)) (chunk_join (off := 16) (a := 8) (b := 8) (chunk_join (off := 16) (a := 4) (b := 4) slice_0_5_tt_16 slice_0_5_tt_20) (chunk_join (off := 24) (a := 4) (b := 4) slice_0_5_tt_24 slice_0_5_tt_28)))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tf_0 : chunk 0 6 (true, false) 0 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tf_4 : chunk 0 6 (true, false) 4 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tf_8 : chunk 0 6 (true, false) 8 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tf_12 : chunk 0 6 (true, false) 12 1 = true := by decide +kernel

lemma checked_0_6_tf : phaseDone 0 6 (true, false) = true := by
  apply phase_split (len := 13) (by decide +kernel) (by decide +kernel)
  exact (chunk_join (off := 0) (a := 8) (b := 5) (chunk_join (off := 0) (a := 4) (b := 4) slice_0_6_tf_0 slice_0_6_tf_4) (chunk_join (off := 8) (a := 4) (b := 1) slice_0_6_tf_8 slice_0_6_tf_12))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tt_0 : chunk 0 6 (true, true) 0 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tt_4 : chunk 0 6 (true, true) 4 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tt_8 : chunk 0 6 (true, true) 8 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tt_12 : chunk 0 6 (true, true) 12 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tt_16 : chunk 0 6 (true, true) 16 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tt_20 : chunk 0 6 (true, true) 20 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tt_24 : chunk 0 6 (true, true) 24 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tt_28 : chunk 0 6 (true, true) 28 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tt_32 : chunk 0 6 (true, true) 32 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tt_36 : chunk 0 6 (true, true) 36 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_0_6_tt_40 : chunk 0 6 (true, true) 40 1 = true := by decide +kernel

lemma checked_0_6_tt : phaseDone 0 6 (true, true) = true := by
  apply phase_split (len := 41) (by decide +kernel) (by decide +kernel)
  exact (chunk_join (off := 0) (a := 20) (b := 21) (chunk_join (off := 0) (a := 8) (b := 12) (chunk_join (off := 0) (a := 4) (b := 4) slice_0_6_tt_0 slice_0_6_tt_4) (chunk_join (off := 8) (a := 4) (b := 8) slice_0_6_tt_8 (chunk_join (off := 12) (a := 4) (b := 4) slice_0_6_tt_12 slice_0_6_tt_16))) (chunk_join (off := 20) (a := 12) (b := 9) (chunk_join (off := 20) (a := 4) (b := 8) slice_0_6_tt_20 (chunk_join (off := 24) (a := 4) (b := 4) slice_0_6_tt_24 slice_0_6_tt_28)) (chunk_join (off := 32) (a := 4) (b := 5) slice_0_6_tt_32 (chunk_join (off := 36) (a := 4) (b := 1) slice_0_6_tt_36 slice_0_6_tt_40))))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_0_ft_0 : chunk 1 0 (false, true) 0 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_0_ft_4 : chunk 1 0 (false, true) 4 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_0_ft_8 : chunk 1 0 (false, true) 8 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_0_ft_12 : chunk 1 0 (false, true) 12 1 = true := by decide +kernel

lemma checked_1_0_ft : phaseDone 1 0 (false, true) = true := by
  apply phase_split (len := 13) (by decide +kernel) (by decide +kernel)
  exact (chunk_join (off := 0) (a := 8) (b := 5) (chunk_join (off := 0) (a := 4) (b := 4) slice_1_0_ft_0 slice_1_0_ft_4) (chunk_join (off := 8) (a := 4) (b := 1) slice_1_0_ft_8 slice_1_0_ft_12))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_0_tt_0 : chunk 1 0 (true, true) 0 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_0_tt_4 : chunk 1 0 (true, true) 4 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_0_tt_8 : chunk 1 0 (true, true) 8 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_0_tt_12 : chunk 1 0 (true, true) 12 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_0_tt_16 : chunk 1 0 (true, true) 16 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_0_tt_20 : chunk 1 0 (true, true) 20 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_0_tt_24 : chunk 1 0 (true, true) 24 4 = true := by decide +kernel

lemma checked_1_0_tt : phaseDone 1 0 (true, true) = true := by
  apply phase_split (len := 28) (by decide +kernel) (by decide +kernel)
  exact (chunk_join (off := 0) (a := 12) (b := 16) (chunk_join (off := 0) (a := 4) (b := 8) slice_1_0_tt_0 (chunk_join (off := 4) (a := 4) (b := 4) slice_1_0_tt_4 slice_1_0_tt_8)) (chunk_join (off := 12) (a := 8) (b := 8) (chunk_join (off := 12) (a := 4) (b := 4) slice_1_0_tt_12 slice_1_0_tt_16) (chunk_join (off := 20) (a := 4) (b := 4) slice_1_0_tt_20 slice_1_0_tt_24)))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_ft_0 : chunk 1 2 (false, true) 0 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_ft_4 : chunk 1 2 (false, true) 4 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_ft_8 : chunk 1 2 (false, true) 8 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_ft_12 : chunk 1 2 (false, true) 12 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_ft_16 : chunk 1 2 (false, true) 16 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_ft_20 : chunk 1 2 (false, true) 20 2 = true := by decide +kernel

lemma checked_1_2_ft : phaseDone 1 2 (false, true) = true := by
  apply phase_split (len := 22) (by decide +kernel) (by decide +kernel)
  exact (chunk_join (off := 0) (a := 12) (b := 10) (chunk_join (off := 0) (a := 4) (b := 8) slice_1_2_ft_0 (chunk_join (off := 4) (a := 4) (b := 4) slice_1_2_ft_4 slice_1_2_ft_8)) (chunk_join (off := 12) (a := 4) (b := 6) slice_1_2_ft_12 (chunk_join (off := 16) (a := 4) (b := 2) slice_1_2_ft_16 slice_1_2_ft_20)))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_tt_0 : chunk 1 2 (true, true) 0 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_tt_4 : chunk 1 2 (true, true) 4 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_tt_8 : chunk 1 2 (true, true) 8 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_tt_12 : chunk 1 2 (true, true) 12 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_tt_16 : chunk 1 2 (true, true) 16 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_tt_20 : chunk 1 2 (true, true) 20 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_tt_24 : chunk 1 2 (true, true) 24 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_tt_28 : chunk 1 2 (true, true) 28 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_2_tt_32 : chunk 1 2 (true, true) 32 4 = true := by decide +kernel

lemma checked_1_2_tt : phaseDone 1 2 (true, true) = true := by
  apply phase_split (len := 36) (by decide +kernel) (by decide +kernel)
  exact (chunk_join (off := 0) (a := 16) (b := 20) (chunk_join (off := 0) (a := 8) (b := 8) (chunk_join (off := 0) (a := 4) (b := 4) slice_1_2_tt_0 slice_1_2_tt_4) (chunk_join (off := 8) (a := 4) (b := 4) slice_1_2_tt_8 slice_1_2_tt_12)) (chunk_join (off := 16) (a := 8) (b := 12) (chunk_join (off := 16) (a := 4) (b := 4) slice_1_2_tt_16 slice_1_2_tt_20) (chunk_join (off := 24) (a := 4) (b := 8) slice_1_2_tt_24 (chunk_join (off := 28) (a := 4) (b := 4) slice_1_2_tt_28 slice_1_2_tt_32))))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_ff_0 : chunk 1 6 (false, false) 0 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_ff_4 : chunk 1 6 (false, false) 4 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_ff_8 : chunk 1 6 (false, false) 8 2 = true := by decide +kernel

lemma checked_1_6_ff : phaseDone 1 6 (false, false) = true := by
  apply phase_split (len := 10) (by decide +kernel) (by decide +kernel)
  exact (chunk_join (off := 0) (a := 4) (b := 6) slice_1_6_ff_0 (chunk_join (off := 4) (a := 4) (b := 2) slice_1_6_ff_4 slice_1_6_ff_8))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_ft_0 : chunk 1 6 (false, true) 0 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_ft_4 : chunk 1 6 (false, true) 4 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_ft_8 : chunk 1 6 (false, true) 8 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_ft_12 : chunk 1 6 (false, true) 12 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_ft_16 : chunk 1 6 (false, true) 16 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_ft_20 : chunk 1 6 (false, true) 20 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_ft_24 : chunk 1 6 (false, true) 24 1 = true := by decide +kernel

lemma checked_1_6_ft : phaseDone 1 6 (false, true) = true := by
  apply phase_split (len := 25) (by decide +kernel) (by decide +kernel)
  exact (chunk_join (off := 0) (a := 12) (b := 13) (chunk_join (off := 0) (a := 4) (b := 8) slice_1_6_ft_0 (chunk_join (off := 4) (a := 4) (b := 4) slice_1_6_ft_4 slice_1_6_ft_8)) (chunk_join (off := 12) (a := 8) (b := 5) (chunk_join (off := 12) (a := 4) (b := 4) slice_1_6_ft_12 slice_1_6_ft_16) (chunk_join (off := 20) (a := 4) (b := 1) slice_1_6_ft_20 slice_1_6_ft_24)))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_0 : chunk 1 6 (true, true) 0 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_4 : chunk 1 6 (true, true) 4 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_8 : chunk 1 6 (true, true) 8 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_12 : chunk 1 6 (true, true) 12 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_16 : chunk 1 6 (true, true) 16 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_20 : chunk 1 6 (true, true) 20 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_24 : chunk 1 6 (true, true) 24 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_28 : chunk 1 6 (true, true) 28 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_32 : chunk 1 6 (true, true) 32 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_36 : chunk 1 6 (true, true) 36 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_40 : chunk 1 6 (true, true) 40 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_44 : chunk 1 6 (true, true) 44 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_48 : chunk 1 6 (true, true) 48 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_1_6_tt_52 : chunk 1 6 (true, true) 52 3 = true := by decide +kernel

lemma checked_1_6_tt : phaseDone 1 6 (true, true) = true := by
  apply phase_split (len := 55) (by decide +kernel) (by decide +kernel)
  exact (chunk_join (off := 0) (a := 28) (b := 27) (chunk_join (off := 0) (a := 12) (b := 16) (chunk_join (off := 0) (a := 4) (b := 8) slice_1_6_tt_0 (chunk_join (off := 4) (a := 4) (b := 4) slice_1_6_tt_4 slice_1_6_tt_8)) (chunk_join (off := 12) (a := 8) (b := 8) (chunk_join (off := 12) (a := 4) (b := 4) slice_1_6_tt_12 slice_1_6_tt_16) (chunk_join (off := 20) (a := 4) (b := 4) slice_1_6_tt_20 slice_1_6_tt_24))) (chunk_join (off := 28) (a := 12) (b := 15) (chunk_join (off := 28) (a := 4) (b := 8) slice_1_6_tt_28 (chunk_join (off := 32) (a := 4) (b := 4) slice_1_6_tt_32 slice_1_6_tt_36)) (chunk_join (off := 40) (a := 8) (b := 7) (chunk_join (off := 40) (a := 4) (b := 4) slice_1_6_tt_40 slice_1_6_tt_44) (chunk_join (off := 48) (a := 4) (b := 3) slice_1_6_tt_48 slice_1_6_tt_52))))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_3_0_tt_0 : chunk 3 0 (true, true) 0 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_3_0_tt_4 : chunk 3 0 (true, true) 4 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_3_0_tt_8 : chunk 3 0 (true, true) 8 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_3_0_tt_12 : chunk 3 0 (true, true) 12 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_3_0_tt_16 : chunk 3 0 (true, true) 16 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_3_0_tt_20 : chunk 3 0 (true, true) 20 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_3_0_tt_24 : chunk 3 0 (true, true) 24 4 = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma slice_3_0_tt_28 : chunk 3 0 (true, true) 28 2 = true := by decide +kernel

lemma checked_3_0_tt : phaseDone 3 0 (true, true) = true := by
  apply phase_split (len := 30) (by decide +kernel) (by decide +kernel)
  exact (chunk_join (off := 0) (a := 16) (b := 14) (chunk_join (off := 0) (a := 8) (b := 8) (chunk_join (off := 0) (a := 4) (b := 4) slice_3_0_tt_0 slice_3_0_tt_4) (chunk_join (off := 8) (a := 4) (b := 4) slice_3_0_tt_8 slice_3_0_tt_12)) (chunk_join (off := 16) (a := 8) (b := 6) (chunk_join (off := 16) (a := 4) (b := 4) slice_3_0_tt_16 slice_3_0_tt_20) (chunk_join (off := 24) (a := 4) (b := 2) slice_3_0_tt_24 slice_3_0_tt_28)))

lemma lower_zero {n q : ℕ} (hn : 1 < n) {S : Finset (Wire n)} (h : Lower q S) :
    Lower q (insert (0, 0) S) := by
  intro j T hT ht
  apply h j T _ ht
  intro a ha
  exact (Finset.mem_insert.mp (hT ha)).resolve_left (live_proper hn ht a ha).1

lemma subInputLower1 : Lower 8 subRoot1.toFinset :=
  lower_checked (k := 7) (by decide) [] subRoot1 (by decide +kernel) (by decide +kernel)
    (by simp [Monitor]) subChecked1

lemma subInputLower4 : Lower 8 subRoot4.toFinset :=
  lower_checked (k := 7) (by decide) [] subRoot4 (by decide +kernel) (by decide +kernel)
    (by simp [Monitor]) subChecked4

lemma subInputLower8 : Lower 8 subRoot8.toFinset :=
  lower_restrict (by decide) reuseRows8 reuseZero8 reuseImage8 subInputLower1

lemma subInputLower16 : Lower 8 subRoot16.toFinset :=
  lower_restrict (by decide) reuseRows16 reuseZero16 reuseImage16 subInputLower1

lemma subInputLower32 : Lower 8 subRoot32.toFinset :=
  lower_restrict (by decide) reuseRows32 reuseZero32 reuseImage32 subInputLower1

lemma subInputLower2 : Lower 7 subRoot2.toFinset :=
  lower_checked (k := 6) (by decide) [] subRoot2 (by decide +kernel) (by decide +kernel)
    (by simp [Monitor]) subChecked2

lemma subInputLower64 : Lower 7 subRoot64.toFinset :=
  lower_restrict (by decide) reuseRows64 reuseZero64 reuseImage64 subInputLower2

lemma subInputLower17 : Lower 7 subRoot17.toFinset :=
  lower_checked (k := 6) (by decide) [] subRoot17 (by decide +kernel) (by decide +kernel)
    (by simp [Monitor]) subChecked17

lemma subInputLower40 : Lower 7 subRoot40.toFinset :=
  lower_restrict (by decide) reuseRows40 reuseZero40 reuseImage40 subInputLower17

lemma subInputLower7 : Lower 4 subRoot7.toFinset :=
  lower_checked (k := 3) (by decide) [] subRoot7 (by decide +kernel) (by decide +kernel)
    (by simp [Monitor]) subChecked7

lemma subInputLower84 : Lower 4 subRoot84.toFinset :=
  lower_restrict (by decide) reuseRows84 reuseZero84 reuseImage84 subInputLower7

lemma subInputLower38 : Lower 4 subRoot38.toFinset :=
  lower_restrict (by decide) reuseRows38 reuseZero38 reuseImage38 subInputLower7

lemma subInputLower76 : Lower 4 subRoot76.toFinset :=
  lower_restrict (by decide) reuseRows76 reuseZero76 reuseImage76 subInputLower7

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectRoot1 : root.toFinset.image (selectRows rows1) = insert (0, 0) subRoot1.toFinset := by
  decide +kernel

lemma subLower1 : Lower 8 (root.toFinset.image (selectRows rows1)) :=
  projectRoot1.symm ▸ lower_zero (by decide) subInputLower1

lemma probe1 : ∀ i : Fin 49, (rows1 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectRoot4 : root.toFinset.image (selectRows rows4) = insert (0, 0) subRoot4.toFinset := by
  decide +kernel

lemma subLower4 : Lower 8 (root.toFinset.image (selectRows rows4)) :=
  projectRoot4.symm ▸ lower_zero (by decide) subInputLower4

lemma probe4 : ∀ i : Fin 49, (rows4 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectRoot8 : root.toFinset.image (selectRows rows8) = insert (0, 0) subRoot8.toFinset := by
  decide +kernel

lemma subLower8 : Lower 8 (root.toFinset.image (selectRows rows8)) :=
  projectRoot8.symm ▸ lower_zero (by decide) subInputLower8

lemma probe8 : ∀ i : Fin 49, (rows8 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectRoot16 : root.toFinset.image (selectRows rows16) = insert (0, 0) subRoot16.toFinset := by
  decide +kernel

lemma subLower16 : Lower 8 (root.toFinset.image (selectRows rows16)) :=
  projectRoot16.symm ▸ lower_zero (by decide) subInputLower16

lemma probe16 : ∀ i : Fin 49, (rows16 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectRoot32 : root.toFinset.image (selectRows rows32) = insert (0, 0) subRoot32.toFinset := by
  decide +kernel

lemma subLower32 : Lower 8 (root.toFinset.image (selectRows rows32)) :=
  projectRoot32.symm ▸ lower_zero (by decide) subInputLower32

lemma probe32 : ∀ i : Fin 49, (rows32 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectRoot2 : root.toFinset.image (selectRows rows2) = insert (0, 0) subRoot2.toFinset := by
  decide +kernel

lemma subLower2 : Lower 7 (root.toFinset.image (selectRows rows2)) :=
  projectRoot2.symm ▸ lower_zero (by decide) subInputLower2

lemma probe2 : ∀ i : Fin 51, (rows2 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectRoot64 : root.toFinset.image (selectRows rows64) = insert (0, 0) subRoot64.toFinset := by
  decide +kernel

lemma subLower64 : Lower 7 (root.toFinset.image (selectRows rows64)) :=
  projectRoot64.symm ▸ lower_zero (by decide) subInputLower64

lemma probe64 : ∀ i : Fin 51, (rows64 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectRoot17 : root.toFinset.image (selectRows rows17) = insert (0, 0) subRoot17.toFinset := by
  decide +kernel

lemma subLower17 : Lower 7 (root.toFinset.image (selectRows rows17)) :=
  projectRoot17.symm ▸ lower_zero (by decide) subInputLower17

lemma probe17 : ∀ i : Fin 26, (rows17 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectRoot40 : root.toFinset.image (selectRows rows40) = insert (0, 0) subRoot40.toFinset := by
  decide +kernel

lemma subLower40 : Lower 7 (root.toFinset.image (selectRows rows40)) :=
  projectRoot40.symm ▸ lower_zero (by decide) subInputLower40

lemma probe40 : ∀ i : Fin 26, (rows40 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectRoot7 : root.toFinset.image (selectRows rows7) = insert (0, 0) subRoot7.toFinset := by
  decide +kernel

lemma subLower7 : Lower 4 (root.toFinset.image (selectRows rows7)) :=
  projectRoot7.symm ▸ lower_zero (by decide) subInputLower7

lemma probe7 : ∀ i : Fin 13, (rows7 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectRoot84 : root.toFinset.image (selectRows rows84) = insert (0, 0) subRoot84.toFinset := by
  decide +kernel

lemma subLower84 : Lower 4 (root.toFinset.image (selectRows rows84)) :=
  projectRoot84.symm ▸ lower_zero (by decide) subInputLower84

lemma probe84 : ∀ i : Fin 13, (rows84 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectRoot38 : root.toFinset.image (selectRows rows38) = insert (0, 0) subRoot38.toFinset := by
  decide +kernel

lemma subLower38 : Lower 4 (root.toFinset.image (selectRows rows38)) :=
  projectRoot38.symm ▸ lower_zero (by decide) subInputLower38

lemma probe38 : ∀ i : Fin 13, (rows38 i).val = 0 ↔ i.val = 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectRoot76 : root.toFinset.image (selectRows rows76) = insert (0, 0) subRoot76.toFinset := by
  decide +kernel

lemma subLower76 : Lower 4 (root.toFinset.image (selectRows rows76)) :=
  projectRoot76.symm ▸ lower_zero (by decide) subInputLower76

lemma probe76 : ∀ i : Fin 13, (rows76 i).val = 0 ↔ i.val = 0 := by decide +kernel

lemma root_monitor : Monitor probes root.toFinset := by
  intro p hp
  simp only [probes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨49, by decide, rows1, probe1, subMask1, subLower1⟩
  · exact ⟨49, by decide, rows4, probe4, subMask4, subLower4⟩
  · exact ⟨49, by decide, rows8, probe8, subMask8, subLower8⟩
  · exact ⟨49, by decide, rows16, probe16, subMask16, subLower16⟩
  · exact ⟨49, by decide, rows32, probe32, subMask32, subLower32⟩
  · exact ⟨51, by decide, rows2, probe2, subMask2, subLower2⟩
  · exact ⟨51, by decide, rows64, probe64, subMask64, subLower64⟩
  · exact ⟨26, by decide, rows17, probe17, subMask17, subLower17⟩
  · exact ⟨26, by decide, rows40, probe40, subMask40, subLower40⟩
  · exact ⟨13, by decide, rows7, probe7, subMask7, subLower7⟩
  · exact ⟨13, by decide, rows84, probe84, subMask84, subLower84⟩
  · exact ⟨13, by decide, rows38, probe38, subMask38, subLower38⟩
  · exact ⟨13, by decide, rows76, probe76, subMask76, subLower76⟩



-- Row permutations preserve live sets and the number of binary steps.
lemma rows_zero {n m : ℕ} (rs : Fin m → Fin n) :
    selectRows rs (0, 0) = (0, 0) := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · rw [(select_bit rs _ ⟨i,hi⟩).1]
    exact (zero_bit _ _).trans (zero_bit _ _).symm
  · rw [(select_bit rs _ ⟨i,hi⟩).2]
    exact (zero_bit _ _).trans (zero_bit _ _).symm

lemma rows_injective {n m : ℕ} (rs : Fin m → Fin n) (surj : Function.Surjective rs) :
    Function.Injective (selectRows rs) := by
  intro a b e
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · obtain ⟨j, hj⟩ := surj ⟨i,hi⟩
    have he := congrArg (fun w : Wire m => w.1.getLsbD j.val) e
    rw [(select_bit rs a j).1, (select_bit rs b j).1, hj] at he
    exact he
  · obtain ⟨j, hj⟩ := surj ⟨i,hi⟩
    have he := congrArg (fun w : Wire m => w.2.getLsbD j.val) e
    rw [(select_bit rs a j).2, (select_bit rs b j).2, hj] at he
    exact he

lemma live_reindex {n m k : ℕ} (hm : 0 < m) (rs : Fin m → Fin n)
    (surj : Function.Surjective rs)
    (hz : ∀ i : Fin m, (rs i).val = 0 ↔ i.val = 0)
    {S : Finset (Wire n)} (h : Live k S) : Live k (S.image (selectRows rs)) := by
  have hz0 := (hz ⟨0,hm⟩).2 rfl
  have inj := rows_injective rs surj
  induction k generalizing S with
  | zero =>
    change S = {goal n} at h
    subst S
    change ({goal n} : Finset (Wire n)).image (selectRows rs) = {goal m}
    rw [Finset.image_singleton, select_goal rs hz]
  | succ k ih =>
    obtain ⟨a,b,s,t,U,ha,hb,hna,hnb,hab,hfresh,rfl,ht⟩ := h
    let f := selectRows rs
    let z := combine s t (f a) (f b)
    have hZ : selectRows rs (combine s t a b) = z := select_combine rs hm hz0 s t a b
    have ht' := ih ht
    rw [Finset.image_insert, hZ] at ht'
    simp only [Finset.image_insert]
    refine ⟨f a, f b, s, t, U.image f, ?_, ?_, ?_, ?_, inj.ne hab, ?_, rfl, ht'⟩
    · intro he
      exact ha (inj (he.trans (rows_zero rs).symm))
    · intro he
      exact hb (inj (he.trans (rows_zero rs).symm))
    · change norm (selectRows rs a) = selectRows rs a
      rw [← select_norm rs hm hz0, hna]
    · change norm (selectRows rs b) = selectRows rs b
      rw [← select_norm rs hm hz0, hnb]
    · intro he
      apply hfresh
      have hf : selectRows rs (combine s t a b) ∈ (insert a (insert b U)).image (selectRows rs) := by
        rwa [Finset.image_insert, Finset.image_insert, hZ]
      exact (Finset.mem_image.mp hf).elim fun v hv => (inj hv.2) ▸ hv.1

def Dead {n : ℕ} (k : ℕ) (S : Finset (Wire n)) : Prop :=
  ∀ j ≤ k, ¬ Live j S

lemma dead_reindex {n m k : ℕ} (hm : 0 < m) (rs : Fin m → Fin n)
    (surj : Function.Surjective rs)
    (hz : ∀ i : Fin m, (rs i).val = 0 ↔ i.val = 0)
    {S : Finset (Wire n)} {T : Finset (Wire m)}
    (hset : S.image (selectRows rs) = T) (h : Dead k T) : Dead k S := by
  intro j hj hLive
  exact h j hj (hset ▸ live_reindex hm rs surj hz hLive)

def firstState (i j : Fin 7) (p : Bool × Bool) : State 88 :=
  (firstEntries i j p).getD 0 ([], [])

lemma phase_false_on {i j : Fin 7} {p : Bool × Bool} {st : State 88}
    (hphase : phaseDone i j p = true) (h : st ∈ firstEntries i j p) :
    search 9 st.1 st.2 = false := by
  dsimp only [firstEntries] at h
  dsimp only [phaseDone] at hphase
  split at h
  · rename_i ho
    rw [ite_eq_left ho, phase_entries, Bool.not_eq_true'] at hphase
    apply Bool.eq_false_iff.mpr
    intro he
    have hc := (List.any_eq_true (p := fun st : State 88 => search 9 st.1 st.2)).mpr ⟨st, h, he⟩
    rw [hphase] at hc
    exact Bool.noConfusion hc
  · exact (List.not_mem_nil h).elim

def FirstFacts (i j : Fin 7) (p : Bool × Bool) : Prop :=
  let a := root.getD i.val (0,0)
  let b := root.getD j.val (0,0)
  let z := combine p.1 p.2 a b
  let st := firstState i j p
  let U := (st.2.erase z).toFinset
  st ∈ firstEntries i j p ∧ st.2.Nodup ∧ norm a = a ∧ norm b = b ∧
    root.toFinset = insert a (insert b U) ∧ st.1 = advance probes a b z ∧
    st.2.toFinset = insert z U

lemma dead_first (i j : Fin 7) (p : Bool × Bool)
    (base : Monitor probes root.toFinset) (hcheck : phaseDone i j p = true)
    (facts : FirstFacts i j p) : Dead 9 (firstState i j p).2.toFinset := by
  dsimp only [FirstFacts] at facts
  obtain ⟨hmem, hnd, hna, hnb, hbase, ht, hs⟩ := facts
  have hM : Monitor (firstState i j p).1 (firstState i j p).2.toFinset := by
    rw [ht, hs]
    exact monitor_step hna hnb (hbase ▸ base)
  have hf := phase_false_on hcheck hmem
  intro k hk hLive
  have hhit := search_complete (by decide : 1 < 88) hnd hM hk hLive
  rw [hf] at hhit
  exact Bool.noConfusion hhit

lemma lower_from_children
    (hw : root.Nodup)
    (req : root.all (fun a => (cov (root.erase a) ||| 1) != BitVec.allOnes 88) = true)
    (hM : Monitor probes root.toFinset)
    (dead : ∀ st ∈ scanEntries 9 probes root, Dead 9 st.2.toFinset) :
    Lower 11 root.toFinset := by
  intro j S hS hLive
  have hEq := all_required req hS hLive
  subst S
  by_contra! hj
  have hcard := live_card hLive
  have hnum : root.toFinset.card = 7 := by decide +kernel
  rw [hnum] at hcard
  cases j with
  | zero => omega
  | succ j =>
    obtain ⟨a,b,s,t,U,hna,hnb,hab,hord,hf,he,ht⟩ := expose hLive
    classical
    let f : List (Probe 88) → List (Wire 88) → Bool := fun ps w =>
      decide (w.Nodup ∧ Live j w.toFinset ∧ Monitor ps w.toFinset)
    have hF : ∀ ps w, w.Nodup → Live j w.toFinset → Monitor ps w.toFinset → f ps w = true := by
      intro ps w hn hl hm
      exact decide_eq_true ⟨hn,hl,hm⟩
    have hscan := scan_step (by decide : 1 < 88) probes root hw hord hab hna hnb
      he hf (by omega : j ≤ 9) ht hM f hF
    rw [scan_entries] at hscan
    obtain ⟨st,hst,hf⟩ := List.any_eq_true.mp hscan
    have e : st.2.Nodup ∧ Live j st.2.toFinset ∧ Monitor st.1 st.2.toFinset :=
      of_decide_eq_true hf
    exact dead st hst j (by omega) e.2.1

def symmetry0 : Fin 88 → Fin 88 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87]

lemma surjective0 : Function.Surjective symmetry0 := by
  unfold Function.Surjective
  decide +kernel

lemma symmetryZero0 : ∀ i : Fin 88, (symmetry0 i).val = 0 ↔ i.val = 0 := by
  decide +kernel

def symmetry1 : Fin 88 → Fin 88 := ![0, 58, 59, 54, 53, 64, 60, 61, 56, 55, 65, 30, 31, 82, 35, 36, 79, 78, 32, 33, 83, 37, 38, 81, 80, 67, 66, 72, 71, 74, 11, 12, 18, 19, 68, 14, 15, 21, 22, 46, 47, 85, 84, 49, 50, 87, 39, 40, 86, 43, 44, 62, 63, 4, 3, 9, 8, 57, 1, 2, 6, 7, 51, 52, 5, 10, 26, 25, 34, 76, 75, 28, 27, 77, 29, 70, 69, 73, 17, 16, 24, 23, 13, 20, 42, 41, 48, 45]

lemma surjective1 : Function.Surjective symmetry1 := by
  unfold Function.Surjective
  decide +kernel

lemma symmetryZero1 : ∀ i : Fin 88, (symmetry1 i).val = 0 ↔ i.val = 0 := by
  decide +kernel

def symmetry2 : Fin 88 → Fin 88 := ![0, 66, 67, 54, 53, 71, 84, 85, 79, 78, 87, 12, 11, 68, 15, 14, 56, 55, 40, 39, 86, 44, 43, 81, 80, 59, 58, 72, 64, 74, 31, 30, 47, 46, 82, 36, 35, 50, 49, 19, 18, 61, 60, 22, 21, 65, 33, 32, 83, 38, 37, 69, 70, 4, 3, 17, 16, 57, 26, 25, 42, 41, 76, 75, 28, 45, 1, 2, 13, 51, 52, 5, 27, 77, 29, 63, 62, 73, 9, 8, 24, 23, 34, 48, 6, 7, 20, 10]

lemma surjective2 : Function.Surjective symmetry2 := by
  unfold Function.Surjective
  decide +kernel

lemma symmetryZero2 : ∀ i : Fin 88, (symmetry2 i).val = 0 ↔ i.val = 0 := by
  decide +kernel

def symmetry3 : Fin 88 → Fin 88 := ![0, 26, 25, 3, 4, 28, 42, 41, 16, 17, 45, 31, 30, 34, 36, 35, 8, 9, 47, 46, 48, 50, 49, 23, 24, 2, 1, 27, 5, 29, 12, 11, 40, 39, 13, 15, 14, 44, 43, 33, 32, 7, 6, 38, 37, 10, 19, 18, 20, 22, 21, 76, 75, 53, 54, 78, 79, 57, 66, 67, 84, 85, 69, 70, 71, 87, 58, 59, 82, 62, 63, 64, 72, 73, 74, 52, 51, 77, 55, 56, 80, 81, 68, 86, 60, 61, 83, 65]

lemma surjective3 : Function.Surjective symmetry3 := by
  unfold Function.Surjective
  decide +kernel

lemma symmetryZero3 : ∀ i : Fin 88, (symmetry3 i).val = 0 ↔ i.val = 0 := by
  decide +kernel

lemma inactive_0_2_tt : Dead 9 (firstState 0 2 (true, true)).2.toFinset :=
  dead_first 0 2 (true, true) root_monitor checked_0_2_tt (by unfold FirstFacts; decide +kernel)

lemma inactive_0_5_tt : Dead 9 (firstState 0 5 (true, true)).2.toFinset :=
  dead_first 0 5 (true, true) root_monitor checked_0_5_tt (by unfold FirstFacts; decide +kernel)

lemma inactive_0_6_tf : Dead 9 (firstState 0 6 (true, false)).2.toFinset :=
  dead_first 0 6 (true, false) root_monitor checked_0_6_tf (by unfold FirstFacts; decide +kernel)

lemma inactive_0_6_tt : Dead 9 (firstState 0 6 (true, true)).2.toFinset :=
  dead_first 0 6 (true, true) root_monitor checked_0_6_tt (by unfold FirstFacts; decide +kernel)

lemma inactive_1_0_ft : Dead 9 (firstState 1 0 (false, true)).2.toFinset :=
  dead_first 1 0 (false, true) root_monitor checked_1_0_ft (by unfold FirstFacts; decide +kernel)

lemma inactive_1_0_tt : Dead 9 (firstState 1 0 (true, true)).2.toFinset :=
  dead_first 1 0 (true, true) root_monitor checked_1_0_tt (by unfold FirstFacts; decide +kernel)

lemma inactive_1_2_ft : Dead 9 (firstState 1 2 (false, true)).2.toFinset :=
  dead_first 1 2 (false, true) root_monitor checked_1_2_ft (by unfold FirstFacts; decide +kernel)

lemma inactive_1_2_tt : Dead 9 (firstState 1 2 (true, true)).2.toFinset :=
  dead_first 1 2 (true, true) root_monitor checked_1_2_tt (by unfold FirstFacts; decide +kernel)

lemma inactive_1_6_ff : Dead 9 (firstState 1 6 (false, false)).2.toFinset :=
  dead_first 1 6 (false, false) root_monitor checked_1_6_ff (by unfold FirstFacts; decide +kernel)

lemma inactive_1_6_ft : Dead 9 (firstState 1 6 (false, true)).2.toFinset :=
  dead_first 1 6 (false, true) root_monitor checked_1_6_ft (by unfold FirstFacts; decide +kernel)

lemma inactive_1_6_tt : Dead 9 (firstState 1 6 (true, true)).2.toFinset :=
  dead_first 1 6 (true, true) root_monitor checked_1_6_tt (by unfold FirstFacts; decide +kernel)

lemma inactive_3_0_tt : Dead 9 (firstState 3 0 (true, true)).2.toFinset :=
  dead_first 3 0 (true, true) root_monitor checked_3_0_tt (by unfold FirstFacts; decide +kernel)


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_2_4_tt :
    (firstState 2 4 (true, true)).2.toFinset.image (selectRows symmetry2) =
      (firstState 0 2 (true, true)).2.toFinset := by
  decide +kernel

lemma inactive_2_4_tt : Dead 9 (firstState 2 4 (true, true)).2.toFinset :=
  dead_reindex (by decide) symmetry2 surjective2 symmetryZero2
    rotation_2_4_tt inactive_0_2_tt


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_2_5_tt :
    (firstState 2 5 (true, true)).2.toFinset.image (selectRows symmetry3) =
      (firstState 0 2 (true, true)).2.toFinset := by
  decide +kernel

lemma inactive_2_5_tt : Dead 9 (firstState 2 5 (true, true)).2.toFinset :=
  dead_reindex (by decide) symmetry3 surjective3 symmetryZero3
    rotation_2_5_tt inactive_0_2_tt


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_3_2_tt :
    (firstState 3 2 (true, true)).2.toFinset.image (selectRows symmetry1) =
      (firstState 0 2 (true, true)).2.toFinset := by
  decide +kernel

lemma inactive_3_2_tt : Dead 9 (firstState 3 2 (true, true)).2.toFinset :=
  dead_reindex (by decide) symmetry1 surjective1 symmetryZero1
    rotation_3_2_tt inactive_0_2_tt


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_3_4_tt :
    (firstState 3 4 (true, true)).2.toFinset.image (selectRows symmetry1) =
      (firstState 0 5 (true, true)).2.toFinset := by
  decide +kernel

lemma inactive_3_4_tt : Dead 9 (firstState 3 4 (true, true)).2.toFinset :=
  dead_reindex (by decide) symmetry1 surjective1 symmetryZero1
    rotation_3_4_tt inactive_0_5_tt


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_1_3_ft :
    (firstState 1 3 (false, true)).2.toFinset.image (selectRows symmetry1) =
      (firstState 0 6 (true, false)).2.toFinset := by
  decide +kernel

lemma inactive_1_3_ft : Dead 9 (firstState 1 3 (false, true)).2.toFinset :=
  dead_reindex (by decide) symmetry1 surjective1 symmetryZero1
    rotation_1_3_ft inactive_0_6_tf


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_1_4_ft :
    (firstState 1 4 (false, true)).2.toFinset.image (selectRows symmetry2) =
      (firstState 0 6 (true, false)).2.toFinset := by
  decide +kernel

lemma inactive_1_4_ft : Dead 9 (firstState 1 4 (false, true)).2.toFinset :=
  dead_reindex (by decide) symmetry2 surjective2 symmetryZero2
    rotation_1_4_ft inactive_0_6_tf


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_5_6_tf :
    (firstState 5 6 (true, false)).2.toFinset.image (selectRows symmetry3) =
      (firstState 0 6 (true, false)).2.toFinset := by
  decide +kernel

lemma inactive_5_6_tf : Dead 9 (firstState 5 6 (true, false)).2.toFinset :=
  dead_reindex (by decide) symmetry3 surjective3 symmetryZero3
    rotation_5_6_tf inactive_0_6_tf


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_1_3_tt :
    (firstState 1 3 (true, true)).2.toFinset.image (selectRows symmetry1) =
      (firstState 0 6 (true, true)).2.toFinset := by
  decide +kernel

lemma inactive_1_3_tt : Dead 9 (firstState 1 3 (true, true)).2.toFinset :=
  dead_reindex (by decide) symmetry1 surjective1 symmetryZero1
    rotation_1_3_tt inactive_0_6_tt


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_1_4_tt :
    (firstState 1 4 (true, true)).2.toFinset.image (selectRows symmetry2) =
      (firstState 0 6 (true, true)).2.toFinset := by
  decide +kernel

lemma inactive_1_4_tt : Dead 9 (firstState 1 4 (true, true)).2.toFinset :=
  dead_reindex (by decide) symmetry2 surjective2 symmetryZero2
    rotation_1_4_tt inactive_0_6_tt


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_5_6_tt :
    (firstState 5 6 (true, true)).2.toFinset.image (selectRows symmetry3) =
      (firstState 0 6 (true, true)).2.toFinset := by
  decide +kernel

lemma inactive_5_6_tt : Dead 9 (firstState 5 6 (true, true)).2.toFinset :=
  dead_reindex (by decide) symmetry3 surjective3 symmetryZero3
    rotation_5_6_tt inactive_0_6_tt


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_1_5_ft :
    (firstState 1 5 (false, true)).2.toFinset.image (selectRows symmetry3) =
      (firstState 1 0 (false, true)).2.toFinset := by
  decide +kernel

lemma inactive_1_5_ft : Dead 9 (firstState 1 5 (false, true)).2.toFinset :=
  dead_reindex (by decide) symmetry3 surjective3 symmetryZero3
    rotation_1_5_ft inactive_1_0_ft


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_3_6_tf :
    (firstState 3 6 (true, false)).2.toFinset.image (selectRows symmetry1) =
      (firstState 1 0 (false, true)).2.toFinset := by
  decide +kernel

lemma inactive_3_6_tf : Dead 9 (firstState 3 6 (true, false)).2.toFinset :=
  dead_reindex (by decide) symmetry1 surjective1 symmetryZero1
    rotation_3_6_tf inactive_1_0_ft


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_4_6_tf :
    (firstState 4 6 (true, false)).2.toFinset.image (selectRows symmetry2) =
      (firstState 1 0 (false, true)).2.toFinset := by
  decide +kernel

lemma inactive_4_6_tf : Dead 9 (firstState 4 6 (true, false)).2.toFinset :=
  dead_reindex (by decide) symmetry2 surjective2 symmetryZero2
    rotation_4_6_tf inactive_1_0_ft


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_1_5_tt :
    (firstState 1 5 (true, true)).2.toFinset.image (selectRows symmetry3) =
      (firstState 1 0 (true, true)).2.toFinset := by
  decide +kernel

lemma inactive_1_5_tt : Dead 9 (firstState 1 5 (true, true)).2.toFinset :=
  dead_reindex (by decide) symmetry3 surjective3 symmetryZero3
    rotation_1_5_tt inactive_1_0_tt


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_3_6_tt :
    (firstState 3 6 (true, true)).2.toFinset.image (selectRows symmetry1) =
      (firstState 1 0 (true, true)).2.toFinset := by
  decide +kernel

lemma inactive_3_6_tt : Dead 9 (firstState 3 6 (true, true)).2.toFinset :=
  dead_reindex (by decide) symmetry1 surjective1 symmetryZero1
    rotation_3_6_tt inactive_1_0_tt


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_4_6_tt :
    (firstState 4 6 (true, true)).2.toFinset.image (selectRows symmetry2) =
      (firstState 1 0 (true, true)).2.toFinset := by
  decide +kernel

lemma inactive_4_6_tt : Dead 9 (firstState 4 6 (true, true)).2.toFinset :=
  dead_reindex (by decide) symmetry2 surjective2 symmetryZero2
    rotation_4_6_tt inactive_1_0_tt


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_2_6_tf :
    (firstState 2 6 (true, false)).2.toFinset.image (selectRows symmetry1) =
      (firstState 1 2 (false, true)).2.toFinset := by
  decide +kernel

lemma inactive_2_6_tf : Dead 9 (firstState 2 6 (true, false)).2.toFinset :=
  dead_reindex (by decide) symmetry1 surjective1 symmetryZero1
    rotation_2_6_tf inactive_1_2_ft


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_2_6_tt :
    (firstState 2 6 (true, true)).2.toFinset.image (selectRows symmetry1) =
      (firstState 1 2 (true, true)).2.toFinset := by
  decide +kernel

lemma inactive_2_6_tt : Dead 9 (firstState 2 6 (true, true)).2.toFinset :=
  dead_reindex (by decide) symmetry1 surjective1 symmetryZero1
    rotation_2_6_tt inactive_1_2_tt


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_1_6_tf :
    (firstState 1 6 (true, false)).2.toFinset.image (selectRows symmetry1) =
      (firstState 1 6 (false, true)).2.toFinset := by
  decide +kernel

lemma inactive_1_6_tf : Dead 9 (firstState 1 6 (true, false)).2.toFinset :=
  dead_reindex (by decide) symmetry1 surjective1 symmetryZero1
    rotation_1_6_tf inactive_1_6_ft


set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma rotation_4_5_tt :
    (firstState 4 5 (true, true)).2.toFinset.image (selectRows symmetry2) =
      (firstState 3 0 (true, true)).2.toFinset := by
  decide +kernel

lemma inactive_4_5_tt : Dead 9 (firstState 4 5 (true, true)).2.toFinset :=
  dead_reindex (by decide) symmetry2 surjective2 symmetryZero2
    rotation_4_5_tt inactive_3_0_tt

def oneStepStates : List (State 88) :=
  [firstState 0 2 (true, true),
   firstState 0 5 (true, true),
   firstState 0 6 (true, false),
   firstState 0 6 (true, true),
   firstState 1 0 (false, true),
   firstState 1 0 (true, true),
   firstState 1 2 (false, true),
   firstState 1 2 (true, true),
   firstState 1 3 (false, true),
   firstState 1 3 (true, true),
   firstState 1 4 (false, true),
   firstState 1 4 (true, true),
   firstState 1 5 (false, true),
   firstState 1 5 (true, true),
   firstState 1 6 (false, false),
   firstState 1 6 (false, true),
   firstState 1 6 (true, false),
   firstState 1 6 (true, true),
   firstState 2 4 (true, true),
   firstState 2 5 (true, true),
   firstState 2 6 (true, false),
   firstState 2 6 (true, true),
   firstState 3 0 (true, true),
   firstState 3 2 (true, true),
   firstState 3 4 (true, true),
   firstState 3 6 (true, false),
   firstState 3 6 (true, true),
   firstState 4 5 (true, true),
   firstState 4 6 (true, false),
   firstState 4 6 (true, true),
   firstState 5 6 (true, false),
   firstState 5 6 (true, true)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
lemma initial_states : scanEntries 9 probes root = oneStepStates := by
  decide +kernel

lemma dead_first_states : ∀ st ∈ scanEntries 9 probes root, Dead 9 st.2.toFinset := by
  intro st hs
  rw [initial_states] at hs
  simp only [oneStepStates, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inactive_0_2_tt
  · exact inactive_0_5_tt
  · exact inactive_0_6_tf
  · exact inactive_0_6_tt
  · exact inactive_1_0_ft
  · exact inactive_1_0_tt
  · exact inactive_1_2_ft
  · exact inactive_1_2_tt
  · exact inactive_1_3_ft
  · exact inactive_1_3_tt
  · exact inactive_1_4_ft
  · exact inactive_1_4_tt
  · exact inactive_1_5_ft
  · exact inactive_1_5_tt
  · exact inactive_1_6_ff
  · exact inactive_1_6_ft
  · exact inactive_1_6_tf
  · exact inactive_1_6_tt
  · exact inactive_2_4_tt
  · exact inactive_2_5_tt
  · exact inactive_2_6_tf
  · exact inactive_2_6_tt
  · exact inactive_3_0_tt
  · exact inactive_3_2_tt
  · exact inactive_3_4_tt
  · exact inactive_3_6_tf
  · exact inactive_3_6_tt
  · exact inactive_4_5_tt
  · exact inactive_4_6_tf
  · exact inactive_4_6_tt
  · exact inactive_5_6_tf
  · exact inactive_5_6_tt

lemma theta_lower : Lower 11 root.toFinset :=
  lower_from_children (by decide +kernel) (by decide +kernel) root_monitor dead_first_states

def inputRaw (j : Fin 9) : Wire 90 :=
  (
    (![
      0x20000000000000000000000, 0x4b2012319819e3287cfce6, 0x2003a60c21926043f9327fe, 0x183c48303e6387831e3c738, 0x30000000000000000000000,
      0xc0703fc07c07fc1fc07c0, 0xf007fc0007ff8001fff800, 0xfff8000007fffffe000000, 0xfffffffff8000000000000
    ] : Fin 9 → BitVec 90) j,
    (![
      0x0, 0x4b201231901163284894a4, 0x2001260c209040405122252, 0x18284830146387830e1c528, 0x20000000000000000000000,
      0x703a805805681fc07c0, 0xa007c80007ee8001b76800, 0xffe80000027ba97a000000, 0x5d783456b8000000000000
    ] : Fin 9 → BitVec 90) j)

-- Two extra row pairs witness dependence on vertices zero and four. The ordinary rows
-- have both vertices fixed to false.

def edgeTable (x : Fin 9 → Bool) : Bool :=
  ([(18440827511444797640 : ℕ), (18441957826578283724 : ℕ), (18446744073709222136 : ℕ),
    (18446744073709485308 : ℕ), (18446744073708175304 : ℕ), (18446744073709551615 : ℕ),
    (18446744073709223928 : ℕ), (18446744073709551615 : ℕ)].getD (tableIndex x / 64) 0).testBit
      (tableIndex x % 64)

def sample (s : Bool) (i : Fin 90) (j : Fin 9) : Bool :=
  readBit s i.val (inputRaw j)

def inputs : List (Wire 90) := List.ofFn inputRaw ++ [inputRaw 2]

lemma sample_inputs (s : Bool) (i : Fin 90) :
    inputs.map (readBit s i.val) = List.ofFn (sample s i) ++ [sample s i 2] := by
  simp only [inputs, sample, List.map_append, List.map_ofFn, List.map_singleton, Function.comp_def]
  rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma sample_ok : ∀ (s : Bool) (i : Fin 90),
    (sample s i 0 = false ∨ sample s i 2 = true) ∧
      edgeTable (sample s i) = readBit s i.val (goal 90) := by
  decide +kernel

lemma run_front (l : List Gate) (w : List Bool) :
    ∃ tail, run l w = w ++ tail := by
  induction l generalizing w with
  | nil => exact ⟨[], by simp [run]⟩
  | cons g l ih =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht⟩ := ih (w ++ [v])
    exact ⟨v :: t, by simpa only [run, List.foldl_cons, List.append_assoc,
      List.singleton_append] using ht⟩

lemma tail_agrees {g : Gate} {gs : List Gate} {out : ℕ}
    (hfirst : ∀ x : Fin 9 → Bool,
      ((⟨g :: gs, out⟩ : Circuit).wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (he : ∀ x : Fin 9 → Bool, (⟨g :: gs, out⟩ : Circuit).eval (List.ofFn x) = edgeTable x)
    (x : Fin 9 → Bool) (hx : x 0 = false ∨ x 2 = true) :
    (run gs (List.ofFn x ++ [x 2])).getD out false = edgeTable x := by
  let v := g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
  let w := List.ofFn x ++ [v]
  have h0 := hfirst x
  change (run gs w).getD 9 false = (x 0 || x 2) at h0
  obtain ⟨t, ht⟩ := run_front gs w
  have hw : w.length = 10 := by simp [w]
  rw [ht, List.getD_append _ _ _ _ (by omega)] at h0
  have hv : w.getD 9 false = v := by
    change (List.ofFn x ++ [v]).getD 9 false = v
    have hn : (List.ofFn x).length = 9 := by simp
    rw [List.getD_append_right _ _ _ _ (le_of_eq hn), hn]
    rfl
  rw [hv] at h0
  have h2 : v = x 2 := by rw [h0]; rcases hx with h | h <;> simp [h]
  have e := he x
  change (run gs (List.ofFn x ++ [v])).getD out false = edgeTable x at e
  rwa [h2] at e

lemma tail_reaches {gs : List Gate} {out : ℕ}
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (he : ∀ (x : Fin 9 → Bool), x 0 = false ∨ x 2 = true →
      (run gs (List.ofFn x ++ [x 2])).getD out false = edgeTable x) :
    goal 90 ∈ signals (record gs inputs) := by
  let r := (record gs inputs).getD out (0, 0)
  have hb (s : Bool) (i : Fin 90) : readBit s i.val r = readBit s i.val (goal 90) := by
    rw [← read_default s (record gs inputs) out, run_bits i.isLt s gs inputs hfan,
      sample_inputs, he _ (sample_ok s i).1, (sample_ok s i).2]
  have e : r = goal 90 := by
    apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
    · exact hb true ⟨i, hi⟩
    · exact hb false ⟨i, hi⟩
  have h := get_signal (record gs inputs) out
  change represented (signals (record gs inputs)) (norm r) at h
  rw [e, norm_goal] at h
  exact h.resolve_left (goal_nonzero (by decide))

lemma two_uncharged (gs : List Gate) (i j : Fin gs.length) (hn : i ≠ j)
    (hi : (gs.get i).op = .not) (hj : (gs.get j).op = .not) :
    gs.countP charged + 2 ≤ gs.length := by
  let g : Gate := ⟨.and, []⟩
  let first := gs.set i.val g
  have ij : i.val ≠ j.val := fun h => hn (Fin.ext h)
  have hj' : j.val < first.length := by simp [first]
  have unchanged : first[j.val].op = .not := by
    rw [show first[j.val] = gs[j.val] from List.getElem_set_ne ij hj']
    exact hj
  have c1 : first.countP charged = gs.countP charged + 1 := by
    have e : charged gs[i.val] = false := by simp [charged, ← List.get_eq_getElem, hi]
    simp only [first, List.countP_set i.isLt, e, show charged g = true from rfl, ite_true, Bool.false_eq_true, ite_false, Nat.sub_zero]
  have c2 : (first.set j.val g).countP charged = first.countP charged + 1 := by
    have e : charged first[j.val] = false := by simp [charged, unchanged]
    simp only [List.countP_set hj', e, show charged g = true from rfl, ite_true, Bool.false_eq_true, ite_false, Nat.sub_zero]
  have h := List.countP_le_length (p := charged) (l := first.set j.val g)
  rw [c2, c1, List.length_set, show first.length = gs.length from List.length_set] at h
  omega

def rawAfterZero : List (Wire 89) := (inputs.map norm).map (project 89)

lemma one_live {n k i : ℕ} (hi : i < n) (hi0 : 0 < i) {w : List (Wire n)}
    {S : Finset (Wire n)} (hS : S ⊆ w.toFinset) (h : Live k S) (u : Wire n)
    (hall : w.all (fun a => !((sep a).getLsbD i) || a == u) = true) :
    u ∈ S := by
  obtain ⟨a, ha, hdiff⟩ := live_separates hi hi0 h
  have hbar : (sep a).getLsbD i = true := by
    rw [sep, BitVec.getLsbD_xor, bne_iff_ne]
    exact hdiff
  have e := List.all_eq_true.mp hall a (List.mem_toFinset.mp (hS ha))
  simp only [hbar, Bool.not_true, Bool.false_or, beq_iff_eq] at e
  exact e ▸ ha

lemma after_zero_set :
    (signals inputs).image (project 89) = rawAfterZero.toFinset := by
  ext a
  simp only [signals, rawAfterZero, Finset.mem_image, List.mem_toFinset, List.mem_map]

lemma small_theta (htheta : Lower 11 root.toFinset) {k : ℕ} {S : Finset (Wire 90)} (hk : k ≤ 12)
    (hs : S ⊆ signals inputs) (h : Live k S) : False := by
  have h0 : norm (inputRaw 0) ∈ S :=
    one_live (i := 89) (by decide) (by decide) hs h _ (by decide +kernel : _)
  have v0 : 1 ≤ vanished (project 89) S := by
    exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨h0, by decide +kernel⟩⟩
  obtain ⟨j, U, hu, hl, hcost⟩ := live_project_count (by decide) (project 89)
    (project_goal (by decide)) (project_combine (by decide) (by decide))
    (project_norm (by decide) (by decide)) h
  have subU : U ⊆ rawAfterZero.toFinset := by
    rw [← after_zero_set]
    exact hu.trans (Finset.image_mono (project 89) hs)
  have h4 : project 89 (norm (inputRaw 4)) ∈ U :=
    one_live (i := 88) (by decide) (by decide) subU hl _ (by decide +kernel : _)
  have v4 : 1 ≤ vanished (project 88) U := by
    exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨h4, by decide +kernel⟩⟩
  obtain ⟨l, T, ht, hrun, hcost'⟩ := live_project_count (by decide) (project 88)
    (project_goal (by decide)) (project_combine (by decide) (by decide))
    (project_norm (by decide) (by decide)) hl
  have hroot : rawAfterZero.toFinset.image (project 88) ⊆ insert (0, 0) root.toFinset := by
    decide +kernel
  have subT := ht.trans ((Finset.image_mono (project 88) subU).trans hroot)
  have lower := lower_zero (n := 88) (by decide) htheta l T subT hrun
  omega

lemma exclude (htheta : Lower 11 root.toFinset) (C : Circuit) (hlen : C.gates.length = 15) (hfan : FanInTwo C)
    (hpq : ∃ p q : Fin C.gates.length, p < q ∧ 1 ≤ p.val ∧
      (C.gates.get p).op = .not ∧ (C.gates.get q).op = .not)
    (first : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeTable x) : False := by
  obtain ⟨gs, out⟩ := C
  cases gs with
  | nil => simp at hlen
  | cons g gs =>
    obtain ⟨p, q, hpq, hp1, hp, hq⟩ := hpq
    change p.val < q.val at hpq
    have hpv : p.val < gs.length + 1 := p.isLt
    have hqv : q.val < gs.length + 1 := q.isLt
    let i : Fin gs.length := ⟨p.val-1, by omega⟩
    let j : Fin gs.length := ⟨q.val-1, by omega⟩
    have hget (v : Fin (g :: gs).length) (a : Fin gs.length) (ha : v.val = a.val + 1) :
        (g :: gs).get v = gs.get a := by simp [List.get_eq_getElem, ha]
    have hi : (gs.get i).op = .not := by rwa [← hget p i (by dsimp [i]; omega)]
    have hj : (gs.get j).op = .not := by rwa [← hget q j (by dsimp [j]; omega)]
    have hne : i ≠ j := fun e => by have h := congrArg Fin.val e; dsimp [i,j] at h; omega
    have hcount := two_uncharged gs i j hne hi hj
    have hgs (g' : Gate) (hg' : g' ∈ gs) := hfan g' (List.mem_cons_of_mem g hg')
    have hhit := tail_reaches (fun g' hg' => (hgs g' hg').1) (tail_agrees first he)
    obtain ⟨k, hk, S, hs, hr⟩ := trace (by decide) gs inputs hgs hhit
    simp only [List.length_cons] at hlen
    exact small_theta htheta (by omega) hs hr

end PEqualNP.Outside.L_meta_2956

theorem PEqualNP.Outside.L_meta_2956 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.gates.length = (15 : ℕ) → PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x4 : Fin x1.gates.length) (x5 : Fin x1.gates.length), x4 < x5 ∧ (4 : ℕ) ≤ ↑x4 ∧ ↑x4 ≤ (7 : ℕ) ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x6 : Fin x1.gates.length), (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not → x6 = x4 ∨ x6 = x5) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → ∃ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6) ≠ ([(18440827511444797640 : ℕ), (18441957826578283724 : ℕ), (18446744073709222136 : ℕ), (18446744073709485308 : ℕ), (18446744073708175304 : ℕ), (18446744073709551615 : ℕ), (18446744073709223928 : ℕ), (18446744073709551615 : ℕ)].getD (PEqualNP.MetaComplexity.tableIndex x6 / (64 : ℕ)) (0 : ℕ)).testBit (PEqualNP.MetaComplexity.tableIndex x6 % (64 : ℕ)) := by
  intro C hlen hfan hnot first
  obtain ⟨p, q, hpq, hp4, _, hp, hq, _⟩ := hnot
  by_contra! h
  exact PEqualNP.Outside.L_meta_2956.exclude PEqualNP.Outside.L_meta_2956.theta_lower
    C hlen hfan ⟨p, q, hpq, by omega, hp, hq⟩ first h
