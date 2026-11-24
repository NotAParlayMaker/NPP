import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4233

def tbl : List ℕ := [(4665232155738143 : ℕ), (13518504604999695 : ℕ), (725368754528096277 : ℕ), (730724029253162005 : ℕ), (866973350870287389 : ℕ), (875963053248350355 : ℕ), (884986756446568478 : ℕ), (903000063497490454 : ℕ), (954792603833647132 : ℕ), (1012212425860929682 : ℕ), (1041183516279060867 : ℕ), (1062218301194542225 : ℕ), (1078371242023506996 : ℕ), (1142983005070916482 : ℕ), (1099479117384 : ℕ)]

def proj (x1 : Fin (26 : ℕ) → Bool) (x2 : Fin (20 : ℕ)) : Bool :=
  if ↑x2 < (17 : ℕ) then x1 (Fin.ofNat (26 : ℕ) (if ↑x2 < (5 : ℕ) then ↑x2 else if ↑x2 < (14 : ℕ) then ↑x2 + (8 : ℕ) else ↑x2 + (9 : ℕ))) else Decidable.decide (↑x2 ≠ (18 : ℕ)) && (x1 (16 : Fin (26 : ℕ)) || x1 (18 : Fin (26 : ℕ))) || Decidable.decide (↑x2 ≠ (17 : ℕ)) && (x1 (19 : Fin (26 : ℕ)) || x1 (23 : Fin (26 : ℕ)))

abbrev incP (x2 x3 : Fin (13 : ℕ)) : Prop :=
  ∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4

abbrev Concl (x3 : Fin 26 → Bool) : Prop :=
  ∃ (x6 : Fin (44 : ℕ)), ∀ (x7 : Fin (20 : ℕ)), proj x3 x7 = Bool.true → (tbl.getD (↑x6 / (3 : ℕ)) (0 : ℕ)).testBit ((20 : ℕ) * (↑x6 % (3 : ℕ)) + ↑x7) = Bool.true

def ddN (k : Fin 4) : ℕ := [0, 1, 3, 9].getD k.val 0

def incN (p t : ℕ) : Bool :=
  let d := (p + 13 - t) % 13
  (d == 0) || (d == 1) || (d == 3) || (d == 9)

-- the largest input whose points are the chosen points of line l
def MA (l : ℕ) (b : Fin 4 → Bool) (i : Fin 26) : Bool :=
  if i.val < 13 then (List.finRange 4).any (fun k => b k && (i.val == (l + ddN k) % 13))
  else (List.finRange 4).all (fun k => !(b k) || !(incN ((l + ddN k) % 13) (i.val - 13)))

-- the largest input whose lines are the chosen lines through point q
def MB (q : ℕ) (b : Fin 4 → Bool) (i : Fin 26) : Bool :=
  if i.val < 13 then (List.finRange 4).all (fun k => !(b k) || !(incN i.val ((q + 13 - ddN k) % 13)))
  else (List.finRange 4).any (fun k => b k && (i.val - 13 == (q + 13 - ddN k) % 13))

set_option maxRecDepth 100000 in
theorem keyA : ∀ l : Fin 13, ∀ b0 b1 b2 b3 : Bool, Concl (MA l.val ![b0, b1, b2, b3]) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem keyB : ∀ q : Fin 13, ∀ b0 b1 b2 b3 : Bool, Concl (MB q.val ![b0, b1, b2, b3]) := by
  decide +kernel

theorem inc_iff : ∀ p t : Fin 13, incP p t ↔ incN p.val t.val = true := by
  decide

theorem inc_pt : ∀ p l : Fin 13, incP p l → ∃ k : Fin 4, p.val = (l.val + ddN k) % 13 := by
  decide

theorem inc_ln : ∀ q t : Fin 13, incP q t → ∃ k : Fin 4, t.val = (q.val + 13 - ddN k) % 13 := by
  decide

theorem ddN_lt (k : Fin 4) : ddN k ≤ 9 := by
  fin_cases k <;> decide

theorem proj_mono (x y : Fin 26 → Bool) (h : ∀ i, x i = true → y i = true) (k : Fin 20)
    (hk : proj x k = true) : proj y k = true := by
  unfold proj at hk ⊢
  split
  · rename_i hlt
    rw [if_pos hlt] at hk
    exact h _ hk
  · rename_i hlt
    rw [if_neg hlt] at hk
    have h16 := h 16
    have h18 := h 18
    have h19 := h 19
    have h23 := h 23
    revert hk h16 h18 h19 h23
    cases x 16 <;> cases x 18 <;> cases x 19 <;> cases x 23 <;>
      cases y 16 <;> cases y 18 <;> cases y 19 <;> cases y 23 <;> simp <;> omega

theorem concl_mono (x y : Fin 26 → Bool) (h : ∀ i, x i = true → y i = true) (hy : Concl y) :
    Concl x := by
  obtain ⟨j, hj⟩ := hy
  exact ⟨j, fun k hk => hj k (proj_mono x y h k hk)⟩

theorem bfun (b : Fin 4 → Bool) : b = ![b 0, b 1, b 2, b 3] := by
  funext k
  fin_cases k <;> rfl

theorem core (x3 : Fin 26 → Bool)
    (hind : ∀ (x4 x5 : Fin (13 : ℕ)), x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true →
      x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true → ¬incP x4 x5)
    (hdeg : (∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), x3 (Fin.castAdd (13 : ℕ) x6) = Bool.true →
      incP x6 x5) ∨ ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)),
      x3 (Fin.natAdd (13 : ℕ) x6) = Bool.true → incP x5 x6) :
    Concl x3 := by
  rcases hdeg with ⟨l, hl⟩ | ⟨q, hq⟩
  · let b : Fin 4 → Bool := fun k => x3 ⟨(l.val + ddN k) % 13, by omega⟩
    have hle : ∀ i, x3 i = true → MA l.val b i = true := by
      intro i hi
      unfold MA
      by_cases h : i.val < 13
      · rw [if_pos h]
        have hc : Fin.castAdd 13 (⟨i.val, h⟩ : Fin 13) = i := Fin.ext rfl
        obtain ⟨k, hk⟩ := inc_pt _ l (hl ⟨i.val, h⟩ (by rw [hc]; exact hi))
        rw [List.any_eq_true]
        refine ⟨k, List.mem_finRange k, ?_⟩
        have hbk : b k = true := by
          have e : (⟨(l.val + ddN k) % 13, by omega⟩ : Fin 26) = i := Fin.ext (by simp at hk; simp [← hk])
          show x3 _ = true
          rw [e]; exact hi
        rw [hbk, Bool.true_and, beq_iff_eq]
        simpa using hk
      · rw [if_neg h, List.all_eq_true]
        intro k _
        cases hbk : b k
        · rfl
        · have hp : x3 (Fin.castAdd 13 (⟨(l.val + ddN k) % 13, by omega⟩ : Fin 13)) = true := hbk
          have hc : Fin.natAdd 13 (⟨i.val - 13, by omega⟩ : Fin 13) = i := Fin.ext (by simp; omega)
          have hn := hind _ ⟨i.val - 13, by omega⟩ hp (by rw [hc]; exact hi)
          rw [inc_iff] at hn
          simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true']
          simpa using hn
    apply concl_mono x3 (MA l.val b) hle
    rw [bfun b]
    exact keyA l _ _ _ _
  · let b : Fin 4 → Bool := fun k => x3 ⟨13 + (q.val + 13 - ddN k) % 13, by omega⟩
    have hle : ∀ i, x3 i = true → MB q.val b i = true := by
      intro i hi
      unfold MB
      by_cases h : i.val < 13
      · rw [if_pos h, List.all_eq_true]
        intro k _
        cases hbk : b k
        · rfl
        · have ht : x3 (Fin.natAdd 13 (⟨(q.val + 13 - ddN k) % 13, by omega⟩ : Fin 13)) = true := hbk
          have hc : Fin.castAdd 13 (⟨i.val, h⟩ : Fin 13) = i := Fin.ext rfl
          have hn := hind ⟨i.val, h⟩ _ (by rw [hc]; exact hi) ht
          rw [inc_iff] at hn
          simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true']
          simpa using hn
      · rw [if_neg h]
        have hc : Fin.natAdd 13 (⟨i.val - 13, by omega⟩ : Fin 13) = i := Fin.ext (by simp; omega)
        obtain ⟨k, hk⟩ := inc_ln q _ (hq ⟨i.val - 13, by omega⟩ (by rw [hc]; exact hi))
        rw [List.any_eq_true]
        refine ⟨k, List.mem_finRange k, ?_⟩
        have hbk : b k = true := by
          have e : (⟨13 + (q.val + 13 - ddN k) % 13, by omega⟩ : Fin 26) = i :=
            Fin.ext (by simp at hk; simp [← hk]; omega)
          show x3 _ = true
          rw [e]; exact hi
        rw [hbk, Bool.true_and, beq_iff_eq]
        simpa using hk
    apply concl_mono x3 (MB q.val b) hle
    rw [bfun b]
    exact keyB q _ _ _ _

end PEqualNP.Outside.L_meta_4233

theorem PEqualNP.Outside.L_meta_4233 : have x1 : (Fin (26 : ℕ) → Bool) → Fin (20 : ℕ) → Bool := fun (x1 : Fin (26 : ℕ) → Bool) (x2 : Fin (20 : ℕ)) => if ↑x2 < (17 : ℕ) then x1 (Fin.ofNat (26 : ℕ) (if ↑x2 < (5 : ℕ) then ↑x2 else if ↑x2 < (14 : ℕ) then ↑x2 + (8 : ℕ) else ↑x2 + (9 : ℕ))) else Decidable.decide (↑x2 ≠ (18 : ℕ)) && (x1 (16 : Fin (26 : ℕ)) || x1 (18 : Fin (26 : ℕ))) || Decidable.decide (↑x2 ≠ (17 : ℕ)) && (x1 (19 : Fin (26 : ℕ)) || x1 (23 : Fin (26 : ℕ))); have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4; ∀ (x3 : Fin (26 : ℕ) → Bool), (∀ (x4 x5 : Fin (13 : ℕ)), x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true → x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true → ¬x2 x4 x5) → ((∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), x3 (Fin.castAdd (13 : ℕ) x6) = Bool.true → x2 x6 x5) ∨ ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), x3 (Fin.natAdd (13 : ℕ) x6) = Bool.true → x2 x5 x6) → ∃ (x6 : Fin (44 : ℕ)), ∀ (x7 : Fin (20 : ℕ)), x1 x3 x7 = Bool.true → ([(4665232155738143 : ℕ), (13518504604999695 : ℕ), (725368754528096277 : ℕ), (730724029253162005 : ℕ), (866973350870287389 : ℕ), (875963053248350355 : ℕ), (884986756446568478 : ℕ), (903000063497490454 : ℕ), (954792603833647132 : ℕ), (1012212425860929682 : ℕ), (1041183516279060867 : ℕ), (1062218301194542225 : ℕ), (1078371242023506996 : ℕ), (1142983005070916482 : ℕ), (1099479117384 : ℕ)].getD (↑x6 / (3 : ℕ)) (0 : ℕ)).testBit ((20 : ℕ) * (↑x6 % (3 : ℕ)) + ↑x7) = Bool.true := by
  dsimp only
  exact fun x3 hind hdeg => PEqualNP.Outside.L_meta_4233.core x3 hind hdeg
