import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3899

def perm : ℕ → ℕ := fun i => [1, 0, 5, 8, 6, 2, 4, 7, 3].getD i i

def pin (i : ℕ) : Fin 24 :=
  if h : i < 24 then ⟨i, h⟩ else 23

def encodeOne (g : BinaryGate) (a b : Bool) : Fin 24 × Fin 24 × Bool × Bool :=
  ⟨pin g.left, ⟨pin g.right, (a, b)⟩⟩

def encStep (w : List Bool) (c : Fin 24 × Fin 24 × Bool × Bool) : List Bool :=
  w ++ [w.getD c.1 false == c.2.2.1 && w.getD c.2.1 false == c.2.2.2]

def binStep (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

def outIdx (len out : ℕ) : Fin 24 :=
  if out < len then pin out else ⟨10, by decide⟩

lemma pin_val (i : ℕ) : (pin i : ℕ) = if i < 24 then i else 23 := by
  unfold pin
  split <;> rfl

lemma pin_read (w : List Bool) (i : ℕ) (hn : w.length ≤ 23) :
    w.getD (pin i) false = w.getD i false := by
  unfold pin
  split
  · rfl
  · rename_i hi
    have h₁ : w.length ≤ i := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h₁, List.getElem?_eq_none hn]

lemma enc_gate (w : List Bool) (g : BinaryGate) (a b : Bool)
    (hw : w.length ≤ 23) (hop : g.op = fun u v => u == a && v == b) :
    encStep w (encodeOne g a b) = binStep w g := by
  simp only [encStep, encodeOne, binStep]
  rw [hop, pin_read w g.left hw, pin_read w g.right hw]

lemma foldl_bin_length (gs : List BinaryGate) (w : List Bool) :
    (gs.foldl (fun w g => binStep w g) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, binStep, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma foldl_bin_getD (gs : List BinaryGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => binStep w g) w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (binStep w g).length := by
      rw [binStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (binStep w g) hi', binStep]
    exact List.getD_append w _ false i hi

lemma perm_ge (i : ℕ) (hi : 9 ≤ i) : perm i = i := by
  dsimp [perm, List.getD]
  rw [List.getElem?_eq_none (by simp; omega)]
  rfl

lemma lex_pair (a b c d : ℕ) :
    List.Lex (· < ·) [a, b] [c, d] ↔ a < c ∨ a = c ∧ b < d := by
  constructor
  · intro h
    cases h with
    | rel hac => exact Or.inl hac
    | cons htail =>
      cases htail with
      | rel hbd => exact Or.inr ⟨rfl, hbd⟩
      | cons himp => cases himp
  · rintro (hac | ⟨rfl, hbd⟩)
    · exact List.Lex.rel hac
    · exact List.Lex.cons (List.Lex.rel hbd)

lemma pair_le_iff (a b c d : ℕ) :
    [a, b] ≤ [c, d] ↔ a < c ∨ a = c ∧ b ≤ d := by
  constructor
  · intro h
    rcases le_iff_lt_or_eq.mp h with hlt | heq
    · rcases (lex_pair a b c d).mp hlt with hac | ⟨hac, hbd⟩
      · exact Or.inl hac
      · exact Or.inr ⟨hac, le_of_lt hbd⟩
    · have hac : a = c := by
        simpa using congrArg (fun l : List ℕ => l.getD 0 0) heq
      have hbd : b = d := by
        simpa using congrArg (fun l : List ℕ => l.getD 1 0) heq
      exact Or.inr ⟨hac, le_of_eq hbd⟩
  · rintro (hac | ⟨rfl, hle⟩)
    · exact le_of_lt ((lex_pair a b c d).mpr (Or.inl hac))
    · rcases le_iff_lt_or_eq.mp hle with hbd | heq
      · exact le_of_lt ((lex_pair a b a d).mpr (Or.inr ⟨rfl, hbd⟩))
      · exact le_of_eq (by simp [heq])

lemma head_order (l r : ℕ) (h : [l, r] ≤ [perm l, perm r]) :
    [(pin l : ℕ), (pin r : ℕ)] ≤ [perm (pin l : ℕ), perm (pin r : ℕ)] := by
  by_cases hl : l < 24
  · by_cases hr : r < 24
    · have hpl : (pin l : ℕ) = l := by rw [pin_val]; split_ifs; omega
      have hpr : (pin r : ℕ) = r := by rw [pin_val]; split_ifs; omega
      simpa [hpl, hpr] using h
    · have hpl : (pin l : ℕ) = l := by rw [pin_val]; split_ifs; omega
      have hpr : (pin r : ℕ) = 23 := by rw [pin_val]; split_ifs; rfl
      have hpermr : perm r = r := perm_ge r (by omega)
      have hperm23 : perm 23 = 23 := perm_ge 23 (by omega)
      have hl_le : l ≤ perm l := by
        have h' : [l, r] ≤ [perm l, r] := by simpa [hpermr] using h
        rcases (pair_le_iff l r (perm l) r).mp h' with hlt | ⟨heq, -⟩
        · exact le_of_lt hlt
        · exact le_of_eq heq
      rw [hpl, hpr, hperm23]
      rcases lt_or_eq_of_le hl_le with hlt | heq
      · exact (pair_le_iff l 23 (perm l) 23).mpr (Or.inl hlt)
      · exact le_of_eq (congrArg (fun z => [z, 23]) heq)
  · by_cases hr : r < 24
    · have hpl : (pin l : ℕ) = 23 := by rw [pin_val]; split_ifs; rfl
      have hpr : (pin r : ℕ) = r := by rw [pin_val]; split_ifs; omega
      have hperml : perm l = l := perm_ge l (by omega)
      have hperm23 : perm 23 = 23 := perm_ge 23 (by omega)
      have hr_le : r ≤ perm r := by
        have h' : [l, r] ≤ [l, perm r] := by simpa [hperml] using h
        rcases (pair_le_iff l r l (perm r)).mp h' with hlt | ⟨-, hle⟩
        · exact absurd hlt (lt_irrefl l)
        · exact hle
      rw [hpl, hpr, hperm23]
      exact (pair_le_iff 23 r 23 (perm r)).mpr (Or.inr ⟨rfl, hr_le⟩)
    · have hpl : (pin l : ℕ) = 23 := by rw [pin_val]; split_ifs; rfl
      have hpr : (pin r : ℕ) = 23 := by rw [pin_val]; split_ifs; rfl
      have hperm23 : perm 23 = 23 := perm_ge 23 (by omega)
      exact le_of_eq (by rw [hpl, hpr, hperm23])

lemma lit_unique (a b a' b' : Bool)
    (h : (fun u v => u == a && v == b) = (fun u v => u == a' && v == b')) :
    a = a' ∧ b = b' := by
  have h1 := congrFun (congrFun h false) false
  have h2 := congrFun (congrFun h false) true
  have h3 := congrFun (congrFun h true) false
  have h4 := congrFun (congrFun h true) true
  revert h1 h2 h3 h4
  cases a <;> cases b <;> cases a' <;> cases b' <;> decide

lemma compileAux (gs : List BinaryGate) (n : ℕ) (hle : n + gs.length ≤ 24)
    (sign : ∀ g ∈ gs, ∃ a b : Bool, g.op = fun u v => u == a && v == b) :
    ∃ cs : List (Fin 24 × Fin 24 × Bool × Bool),
      cs.length = gs.length ∧
      (∀ w : List Bool, w.length = n →
        cs.foldl encStep w = gs.foldl (fun w g => binStep w g) w) ∧
      (∀ (g : BinaryGate) (t : List BinaryGate) (a b : Bool),
        gs = g :: t → g.op = (fun u v => u == a && v == b) →
          cs.head? = some (encodeOne g a b)) := by
  induction gs generalizing n with
  | nil =>
    refine ⟨[], rfl, ?_, ?_⟩
    · intro w hw
      rfl
    · intro g t a b hgs hop
      cases hgs
  | cons g gs ih =>
    have hle' : n + 1 + gs.length ≤ 24 := by
      simp only [List.length_cons] at hle
      omega
    obtain ⟨cs, hlen, he, -⟩ :=
      ih (n + 1) hle' (fun t ht => sign t (List.mem_cons_of_mem g ht))
    obtain ⟨a, b, hop⟩ := sign g List.mem_cons_self
    refine ⟨encodeOne g a b :: cs, ?_, ?_, ?_⟩
    · simp [hlen]
    · intro w hw
      have hwlen : w.length ≤ 23 := by
        simp only [List.length_cons] at hle
        omega
      have hblen : (binStep w g).length = n + 1 := by
        simp [binStep, hw]
      simp only [List.foldl_cons]
      rw [enc_gate w g a b hwlen hop]
      exact he (binStep w g) hblen
    · intro g' t a' b' hgs hop'
      cases hgs
      rcases lit_unique a b a' b' (hop.symm.trans hop') with ⟨rfl, rfl⟩
      rfl

lemma outIdx_read (w : List Bool) (out : ℕ) (hlen : w.length ≤ 24)
    (h10 : w.getD 10 false = false) :
    w.getD (outIdx w.length out) false = w.getD out false := by
  unfold outIdx
  split_ifs with hlt
  · have hlt24 : out < 24 := by omega
    rw [pin_val]
    simp [hlt24]
  · have hge : w.length ≤ out := by omega
    rw [List.getD_eq_default (hn := hge)]
    exact h10

lemma eval_get (gates : List BinaryGate) (output : ℕ) (x : List Bool) :
    (BinaryCircuit.mk gates output).eval x =
      (gates.foldl (fun w g => binStep w g) x).getD output false := by
  unfold BinaryCircuit.eval BinaryCircuit.wires binStep
  rfl

end PEqualNP.Outside.L_meta_3899

theorem PEqualNP.Outside.L_meta_3899 : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit),   x1.size ≤ (13 : ℕ) →     (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) →       (∀ (x4 : PEqualNP.MetaComplexity.BinaryGate),           x1.gates[(0 : ℕ)]? = Option.some x4 →             (∃ (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == Bool.false && x8 == x6) ∧               have x6 : ℕ → ℕ := fun (x6 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x6 x6;               [x4.left, x4.right] ≤ [x6 x4.left, x6 x4.right]) →         ∃ (x5 : List (Fin (24 : ℕ) × Fin (24 : ℕ) × Bool × Bool)) (x6 : Fin (24 : ℕ)),           x5.length = x1.size ∧             (∀ x7 ∈ x5.head?.toList,                 x7.2.2.1 = Bool.false ∧                   have x9 : ℕ → ℕ := fun (x9 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x9 x9;                   [↑x7.1, ↑x7.2.1] ≤ [x9 ↑x7.1, x9 ↑x7.2.1]) ∧               ∀ (x7 : List Bool), x7.length = (11 : ℕ) → x7.getD (10 : ℕ) Bool.false = Bool.false → (List.foldl (fun (x10 : List Bool) (x11 : Fin (24 : ℕ) × Fin (24 : ℕ) × Bool × Bool) => x10 ++ [x10.getD (↑x11.1) Bool.false == x11.2.2.1 && x10.getD (↑x11.2.1) Bool.false == x11.2.2.2]) x7 x5).getD (↑x6) Bool.false = x1.eval x7 := by
  intro C hsz hsign hcanon
  cases C with
  | mk gates output =>
    have hsz' : gates.length ≤ 13 := by simpa [BinaryCircuit.size] using hsz
    have hbound : 11 + gates.length ≤ 24 := by omega
    obtain ⟨cs, hlen, heval, hhead⟩ :=
      PEqualNP.Outside.L_meta_3899.compileAux gates 11 hbound hsign
    refine ⟨cs, PEqualNP.Outside.L_meta_3899.outIdx (11 + gates.length) output, ?_, ?_, ?_⟩
    · simpa [BinaryCircuit.size] using hlen
    · intro c hc
      cases gates with
      | nil =>
        have hcs : cs = [] := List.eq_nil_of_length_eq_zero hlen
        subst hcs
        cases hc
      | cons g gs =>
        obtain ⟨a, b, hop⟩ := hsign g (by simp)
        have hh :
            cs.head? = some (PEqualNP.Outside.L_meta_3899.encodeOne g a b) :=
          hhead g gs a b rfl hop
        simp only [hh, Option.toList_some, List.mem_singleton] at hc
        subst hc
        rcases hcanon g (by simp) with ⟨⟨b1, hop1⟩, hord⟩
        have ha : a = Bool.false :=
          (PEqualNP.Outside.L_meta_3899.lit_unique a b Bool.false b1
            (hop.symm.trans hop1)).1
        refine ⟨?_, ?_⟩
        · simpa [PEqualNP.Outside.L_meta_3899.encodeOne] using ha
        · dsimp [PEqualNP.Outside.L_meta_3899.encodeOne]
          exact PEqualNP.Outside.L_meta_3899.head_order g.left g.right hord
    · intro x hx hz
      have hfold :
          List.foldl (fun (x10 : List Bool) (x11 : Fin 24 × Fin 24 × Bool × Bool) =>
            x10 ++ [x10.getD (↑x11.1) Bool.false == x11.2.2.1 &&
              x10.getD (↑x11.2.1) Bool.false == x11.2.2.2]) x cs =
            cs.foldl PEqualNP.Outside.L_meta_3899.encStep x := by
        rfl
      rw [hfold]
      rw [heval x hx]
      rw [PEqualNP.Outside.L_meta_3899.eval_get]
      have hlenw :
          (gates.foldl (fun w g => PEqualNP.Outside.L_meta_3899.binStep w g) x).length =
            11 + gates.length := by
        simpa [hx] using PEqualNP.Outside.L_meta_3899.foldl_bin_length gates x
      have h10 :
          (gates.foldl (fun w g => PEqualNP.Outside.L_meta_3899.binStep w g) x).getD 10
            false = false := by
        have hi : 10 < x.length := by omega
        rw [PEqualNP.Outside.L_meta_3899.foldl_bin_getD gates x 10 hi]
        exact hz
      rw [← hlenw]
      exact PEqualNP.Outside.L_meta_3899.outIdx_read _ output
        (by rw [hlenw]; omega) h10
