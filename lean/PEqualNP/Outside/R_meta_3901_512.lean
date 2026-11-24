import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 400000 in
theorem PEqualNP.Outside.R_meta_3901_512
    (len12 :
      ∀ (gs : List (Fin 24 × Fin 24 × Bool × Bool)), gs.length ≤ 12 →
        ∀ (out : Fin 24) (pol : Bool),
          ∃ (x : Fin 512),
            let bits : Fin 9 → Bool := fun i => (BitVec.ofNat 9 x.val).getLsbD i.val
            let init : List Bool := List.ofFn bits ++ [bits 0 || bits 1, false]
            ((gs.foldl (fun ws g => ws ++ [(ws.getD g.1.val false == g.2.2.1) && (ws.getD g.2.1.val false == g.2.2.2)]) init).getD out.val false != pol) ≠
              ([(18440827511444797640 : ℕ), (18441957826578283724 : ℕ), (18446744073709222136 : ℕ), (18446744073709485308 : ℕ), (18446744073708175304 : ℕ), (18446744073709551615 : ℕ), (18446744073709223928 : ℕ), (18446744073709551615 : ℕ)].getD (x.val / 64) 0).testBit (x.val % 64))
    (head_uses9 :
      let sym : ℕ → ℕ := fun i => [1, 0, 5, 8, 6, 2, 4, 7, 3].getD i i
      ∀ (g0 : Fin 24 × Fin 24 × Bool × Bool) (rest : List (Fin 24 × Fin 24 × Bool × Bool)),
        rest.length = 12 → g0.2.2.1 = false →
        g0.1.val < 10 → g0.2.1.val < 10 → g0.1.val ≠ g0.2.1.val →
        (g0.1.val = 9 ∨ g0.2.1.val = 9) →
        [g0.1.val, g0.2.1.val] ≤ [sym g0.1.val, sym g0.2.1.val] →
        ∀ (out : Fin 24) (pol : Bool),
          ∃ (x : Fin 512),
            let bits : Fin 9 → Bool := fun i => (BitVec.ofNat 9 x.val).getLsbD i.val
            let init : List Bool := List.ofFn bits ++ [bits 0 || bits 1, false]
            (((g0 :: rest).foldl (fun ws g => ws ++ [(ws.getD g.1.val false == g.2.2.1) && (ws.getD g.2.1.val false == g.2.2.2)]) init).getD out.val false != pol) ≠
              ([(18440827511444797640 : ℕ), (18441957826578283724 : ℕ), (18446744073709222136 : ℕ), (18446744073709485308 : ℕ), (18446744073708175304 : ℕ), (18446744073709551615 : ℕ), (18446744073709223928 : ℕ), (18446744073709551615 : ℕ)].getD (x.val / 64) 0).testBit (x.val % 64))
    (head_inputs :
      let sym : ℕ → ℕ := fun i => [1, 0, 5, 8, 6, 2, 4, 7, 3].getD i i
      ∀ (g0 : Fin 24 × Fin 24 × Bool × Bool) (rest : List (Fin 24 × Fin 24 × Bool × Bool)),
        rest.length = 12 → g0.2.2.1 = false →
        g0.1.val < 9 → g0.2.1.val < 9 → g0.1.val ≠ g0.2.1.val →
        [g0.1.val, g0.2.1.val] ≤ [sym g0.1.val, sym g0.2.1.val] →
        ∀ (out : Fin 24) (pol : Bool),
          ∃ (x : Fin 512),
            let bits : Fin 9 → Bool := fun i => (BitVec.ofNat 9 x.val).getLsbD i.val
            let init : List Bool := List.ofFn bits ++ [bits 0 || bits 1, false]
            (((g0 :: rest).foldl (fun ws g => ws ++ [(ws.getD g.1.val false == g.2.2.1) && (ws.getD g.2.1.val false == g.2.2.2)]) init).getD out.val false != pol) ≠
              ([(18440827511444797640 : ℕ), (18441957826578283724 : ℕ), (18446744073709222136 : ℕ), (18446744073709485308 : ℕ), (18446744073708175304 : ℕ), (18446744073709551615 : ℕ), (18446744073709223928 : ℕ), (18446744073709551615 : ℕ)].getD (x.val / 64) 0).testBit (x.val % 64)) :
    ∀ (x1 : List (Fin (24 : ℕ) × Fin (24 : ℕ) × Bool × Bool)),   x1.length ≤ (13 : ℕ) →     (∀ x3 ∈ x1.head?.toList,         x3.2.2.1 = Bool.false ∧           have x5 : ℕ → ℕ := fun (x5 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x5 x5;           [↑x3.1, ↑x3.2.1] ≤ [x5 ↑x3.1, x5 ↑x3.2.1]) →       ∀ (x4 : Fin (24 : ℕ)) (x5 : Bool),         ∃ (x6 : Fin (512 : ℕ)),           have x7 : Fin (9 : ℕ) → Bool := fun (x7 : Fin (9 : ℕ)) => (BitVec.ofNat (9 : ℕ) ↑x6).getLsbD ↑x7;           have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)), Bool.false];           ((List.foldl (fun (x9 : List Bool) (x10 : Fin (24 : ℕ) × Fin (24 : ℕ) × Bool × Bool) => x9 ++ [x9.getD (↑x10.1) Bool.false == x10.2.2.1 && x9.getD (↑x10.2.1) Bool.false == x10.2.2.2]) x8 x1).getD (↑x4) Bool.false != x5) ≠ ([(18440827511444797640 : ℕ), (18441957826578283724 : ℕ), (18446744073709222136 : ℕ), (18446744073709485308 : ℕ), (18446744073708175304 : ℕ), (18446744073709551615 : ℕ), (18446744073709223928 : ℕ), (18446744073709551615 : ℕ)].getD (↑x6 / (64 : ℕ)) (0 : ℕ)).testBit (↑x6 % (64 : ℕ)) := by
  intro gs hlen hhead out pol
  by_cases hle12 : gs.length ≤ 12
  · exact len12 gs hle12 out pol
  · cases gs with
    | nil => simp at hle12
    | cons g0 rest =>
      have hrestLen : rest.length = 12 := by simp at hlen hle12; omega
      have hg0 : g0.2.2.1 = false ∧
          [g0.1.val, g0.2.1.val] ≤
            [([1, 0, 5, 8, 6, 2, 4, 7, 3] : List ℕ).getD g0.1.val g0.1.val,
             ([1, 0, 5, 8, 6, 2, 4, 7, 3] : List ℕ).getD g0.2.1.val g0.2.1.val] :=
        hhead g0 (by simp)
      by_cases hgen : g0.1.val < 10 ∧ g0.2.1.val < 10 ∧ g0.1.val ≠ g0.2.1.val
      · obtain ⟨ha10, hb10, hab⟩ := hgen
        by_cases h9 : g0.1.val = 9 ∨ g0.2.1.val = 9
        · exact head_uses9 g0 rest hrestLen hg0.1 ha10 hb10 hab h9 hg0.2 out pol
        · push Not at h9
          exact head_inputs g0 rest hrestLen hg0.1 (by omega) (by omega) hab hg0.2 out pol
      · -- g0 is degenerate (reads wire >= 10 or reads the same wire twice):
        -- its output on any 11-element init list with init[10] = false equals (init.getD rep.val false != flip)
        -- for some rep : Fin 24 with rep.val ≤ 10 and flip : Bool!
        have hdeg : ∃ (rep : Fin 24) (flip : Bool), rep.val ≤ 10 ∧
            ∀ (ws : List Bool), ws.length = 11 → ws.getD 10 false = false →
              ((ws.getD g0.1.val false == g0.2.2.1) && (ws.getD g0.2.1.val false == g0.2.2.2)) =
                (ws.getD rep.val false != flip) := by
          have hoob : ∀ (ws : List Bool) (i : ℕ), ws.length = 11 → ws.getD 10 false = false → 10 ≤ i → ws.getD i false = false := by
            intro ws i h11 hw10 hi
            by_cases heq : i = 10
            · subst heq; exact hw10
            · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
          by_cases ha : 10 ≤ g0.1.val
          · by_cases hb : 10 ≤ g0.2.1.val
            · refine ⟨⟨10, by omega⟩, (false == g0.2.2.1) && (false == g0.2.2.2), le_rfl, fun ws h11 hw10 => ?_⟩
              rw [hoob ws g0.1.val h11 hw10 ha, hoob ws g0.2.1.val h11 hw10 hb, hw10]
              cases g0.2.2.1 <;> cases g0.2.2.2 <;> rfl
            · -- g0.1.val >= 10, g0.2.1.val < 10; remember g0.2.2.1 = false so (false == false) = true!
              refine ⟨g0.2.1, !g0.2.2.2, by omega, fun ws h11 hw10 => ?_⟩
              rw [hoob ws g0.1.val h11 hw10 ha, hg0.1]
              cases ws.getD g0.2.1.val false <;> cases g0.2.2.2 <;> rfl
          · by_cases hb : 10 ≤ g0.2.1.val
            · cases hpb : g0.2.2.2
              · -- (ws[a] == false) && (false == false) = !ws[a] = (ws[a] != true)
                refine ⟨g0.1, true, by omega, fun ws h11 hw10 => ?_⟩
                rw [hoob ws g0.2.1.val h11 hw10 hb, hg0.1]
                cases ws.getD g0.1.val false <;> rfl
              · -- (ws[a] == false) && (false == true) = false = (ws[10] != false)
                refine ⟨⟨10, by omega⟩, false, le_rfl, fun ws h11 hw10 => ?_⟩
                rw [hoob ws g0.2.1.val h11 hw10 hb, hw10]; simp
            · -- a < 10 and b < 10, so by ¬ hgen we have a = b!
              have hab : g0.1.val = g0.2.1.val := by omega
              cases hpb : g0.2.2.2
              · refine ⟨g0.1, true, by omega, fun ws _ _ => ?_⟩
                rw [hab, hg0.1]; cases ws.getD g0.2.1.val false <;> rfl
              · refine ⟨⟨10, by omega⟩, false, le_rfl, fun ws _ hw10 => ?_⟩
                rw [hab, hg0.1, hw10]; cases ws.getD g0.2.1.val false <;> rfl
        obtain ⟨rep, flip, hrep10, hrepEq⟩ := hdeg
        -- Redirect wire 11 to (rep, flip) and shift wires > 11 down by 1!
        let rwWire : Fin 24 → Fin 24 := fun i =>
          if i.val = 11 then rep
          else if 11 < i.val then ⟨i.val - 1, by omega⟩
          else i
        let rwPol : Fin 24 → Bool → Bool := fun i p =>
          if i.val = 11 then (p != flip) else p
        let rwGate : (Fin 24 × Fin 24 × Bool × Bool) → (Fin 24 × Fin 24 × Bool × Bool) := fun g =>
          (rwWire g.1, rwWire g.2.1, rwPol g.1 g.2.2.1, rwPol g.2.1 g.2.2.2)
        let rest' := rest.map rwGate
        have hlen' : rest'.length ≤ 12 := by simp [rest', hrestLen]
        let out' := rwWire out
        let pol' := rwPol out pol
        obtain ⟨x, hx⟩ := len12 rest' hlen' out' pol'
        refine ⟨x, ?_⟩
        -- Show the redirected 12-gate circuit evaluates identically to (g0 :: rest) at out!
        let step : List Bool → (Fin 24 × Fin 24 × Bool × Bool) → List Bool := fun ws g =>
          ws ++ [(ws.getD g.1.val false == g.2.2.1) && (ws.getD g.2.1.val false == g.2.2.2)]
        let bits : Fin 9 → Bool := fun i => (BitVec.ofNat 9 x.val).getLsbD i.val
        let init : List Bool := List.ofFn bits ++ [bits 0 || bits 1, false]
        have hinitLen : init.length = 11 := by simp [init]
        have hinit10 : init.getD 10 false = false := by
          dsimp only [init]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp
        have hfold_sim : ∀ (ls : List (Fin 24 × Fin 24 × Bool × Bool)) (w1 w2 : List Bool),
            w1.length = w2.length + 1 → 11 ≤ w2.length →
            (∀ i : Fin 24, w1.getD i.val false = (w2.getD (rwWire i).val false != (if i.val = 11 then flip else false))) →
            ∀ i : Fin 24,
              (ls.foldl step w1).getD i.val false =
                (((ls.map rwGate).foldl step w2).getD (rwWire i).val false != (if i.val = 11 then flip else false)) := by
          intro ls; induction ls with
          | nil => intro w1 w2 _ _ hinv; exact hinv
          | cons g r ih =>
            intro w1 w2 hlenW h11W hinv
            simp only [List.map_cons, List.foldl_cons]
            have hbit : ∀ (u : Fin 24) (pu : Bool),
                (w1.getD u.val false == pu) = (w2.getD (rwWire u).val false == rwPol u pu) := by
              intro u pu
              rw [hinv u]; dsimp only [rwPol]
              by_cases hu : u.val = 11
              · rw [if_pos hu, if_pos hu]; cases w2.getD (rwWire u).val false <;> cases flip <;> cases pu <;> rfl
              · rw [if_neg hu, if_neg hu]; simp
            have hval : ((w1.getD g.1.val false == g.2.2.1) && (w1.getD g.2.1.val false == g.2.2.2)) =
                ((w2.getD (rwGate g).1.val false == (rwGate g).2.2.1) &&
                 (w2.getD (rwGate g).2.1.val false == (rwGate g).2.2.2)) := by
              dsimp only [rwGate]; rw [hbit g.1 g.2.2.1, hbit g.2.1 g.2.2.2]
            apply ih (step w1 g) (step w2 (rwGate g)) (by simp [step, hlenW]) (by simp [step]; omega)
            intro i
            dsimp only [step]
            rw [← hval]
            by_cases hi : i.val = 11
            · rw [if_pos hi]
              have hlt1 : i.val < w1.length := by omega
              have hlt2 : (rwWire i).val < w2.length := by dsimp only [rwWire]; rw [if_pos hi]; omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1,
                  List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
              simpa [List.getD_eq_getElem?_getD, hi] using hinv i
            · rw [if_neg hi, Bool.bne_false]
              by_cases hgt : 11 < i.val
              · have hrw : (rwWire i).val = i.val - 1 := by dsimp only [rwWire]; rw [if_neg hi, if_pos hgt]
                rw [hrw]
                by_cases hlt1 : i.val < w1.length
                · have hlt2 : i.val - 1 < w2.length := by omega
                  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1,
                      List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
                  simpa [List.getD_eq_getElem?_getD, hi, hrw] using hinv i
                · by_cases heq1 : i.val = w1.length
                  · simp only [List.getD_eq_getElem?_getD]
                    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
                    simp [heq1, hlenW]
                  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
                        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
              · have hrw : (rwWire i).val = i.val := by dsimp only [rwWire]; rw [if_neg hi, if_neg hgt]
                rw [hrw]
                have hlt1 : i.val < w1.length := by omega
                have hlt2 : i.val < w2.length := by omega
                rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1,
                    List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
                simpa [List.getD_eq_getElem?_getD, hi, hrw] using hinv i
        have hstep0 : ∀ i : Fin 24,
            (step init g0).getD i.val false =
              (init.getD (rwWire i).val false != (if i.val = 11 then flip else false)) := by
          intro i
          dsimp only [step]
          by_cases hi : i.val = 11
          · rw [if_pos hi]
            have hrw : (rwWire i).val = rep.val := by dsimp only [rwWire]; rw [if_pos hi]
            rw [hrw, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
            simp only [hi, hinitLen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            exact hrepEq init hinitLen hinit10
          · rw [if_neg hi, Bool.bne_false]
            by_cases hgt : 11 < i.val
            · have hrw : (rwWire i).val = i.val - 1 := by dsimp only [rwWire]; rw [if_neg hi, if_pos hgt]
              rw [hrw, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hinitLen]; omega),
                  List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hinitLen]; omega)]
            · have hrw : (rwWire i).val = i.val := by dsimp only [rwWire]; rw [if_neg hi, if_neg hgt]
              rw [hrw, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
              rfl
        have hsim := hfold_sim rest (step init g0) init (by simp [step, hinitLen]) (by omega) hstep0 out
        have heqOut : (((g0 :: rest).foldl step init).getD out.val false != pol) =
            ((rest'.foldl step init).getD out'.val false != pol') := by
          simp only [List.foldl_cons]
          rw [hsim]
          dsimp only [out', pol', rwPol]
          by_cases ho : out.val = 11
          · rw [if_pos ho, if_pos ho]
            cases (rest'.foldl step init).getD (rwWire out).val false <;> cases flip <;> cases pol <;> rfl
          · rw [if_neg ho, if_neg ho]; simp [rest']
        change (((g0 :: rest).foldl step init).getD out.val false != pol) ≠ _
        rw [heqOut]
        exact hx
