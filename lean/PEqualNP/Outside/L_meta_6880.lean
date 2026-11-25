import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6880

def Sset (s : ℕ) : Finset (Fin 13) := Finset.univ.filter (fun p => s.testBit p.val = true)

theorem mem_S (s : ℕ) (p : Fin 13) : p ∈ Sset s ↔ s.testBit p.val = true := by
  simp [Sset]

def W : List (ℕ × ℕ) := [(7, 7405575), (56, 59244600), (4416, 192832), (3712, 33885824), (148, 12853396), (609, 17842785), (5130, 2757642), (2313, 4737289), (4626, 9474578), (1316, 16852260), (194, 39878850), (6148, 1456132), (1041, 17597457), (4264, 10506408), (780, 25297676), (2160, 34613360), (2306, 4917506), (897, 115585), (1096, 52560968), (4105, 2904073), (546, 43057698), (340, 20980052), (6176, 1603616), (5312, 2143424), (2568, 33966600), (274, 13140242), (13, 23330829), (1059, 2688035), (2118, 5376070), (164, 10559652), (1792, 17008384), (2200, 38013080), (533, 18088469), (4400, 8925488), (4736, 8704640), (2208, 33646752), (4161, 3199041), (1602, 33719874), (2067, 5769235), (1157, 2425989), (3088, 34352144), (4102, 11669510), (328, 21119304), (390, 12648838), (2496, 4221376), (100, 19931236), (800, 25248544), (1066, 36176938), (1168, 33858704), (2565, 1378821), (3328, 732416), (4362, 9048330), (81, 22052945), (201, 6308041), (6720, 1202752), (536, 58982936), (4113, 1871889), (5132, 2495500), (1027, 2720771), (1136, 50340976), (548, 26280484), (2562, 34802178), (7172, 408580), (74, 39977034), (281, 21496089), (658, 41976466), (41, 19415081), (104, 52445288), (133, 6619269), (1048, 51119128), (1296, 17343760), (2081, 1656865), (4116, 9711636)]

def good (s M : ℕ) : Bool :=
  decide (∀ p : Fin 13, ¬ s.testBit p.val = true → ∃ l : Fin 13, (∀ q : Fin 13, s.testBit q.val = true → ¬(q = l ∨ q = l + 1 ∨ q = l + 3 ∨ q = l + 9)) ∧ (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) &&
  decide (¬ ∃ l : Fin 13, ∀ q : Fin 13, s.testBit q.val = true → (q = l ∨ q = l + 1 ∨ q = l + 3 ∨ q = l + 9)) &&
  decide (¬ ∃ p : Fin 13, ∀ l : Fin 13, (∀ q : Fin 13, s.testBit q.val = true → ¬(q = l ∨ q = l + 1 ∨ q = l + 3 ∨ q = l + 9)) → (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) &&
  decide (∀ p : Fin 13, M.testBit p.val = s.testBit p.val) &&
  decide (∀ l : Fin 13, M.testBit (13 + l.val) = true ↔ (∀ q : Fin 13, s.testBit q.val = true → ¬(q = l ∨ q = l + 1 ∨ q = l + 3 ∨ q = l + 9)))

set_option maxRecDepth 100000 in
theorem allgood : W.all (fun w => good w.1 w.2) = true := by decide +kernel

def X2 (u v : Fin 26) : Bool := decide (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + 26 - v.val) % 13 ∈ [0, 1, 3, 9])

def chkT : Bool := (List.finRange 26).all fun x5 => (List.finRange 26).all fun x6 => (List.finRange 26).all fun x7 =>
  (decide (x6 = x5) || decide (x7 = x5) || X2 x6 x7 || X2 x7 x6 ||
    W.any fun w => w.2.testBit x6.val && w.2.testBit x7.val && !w.2.testBit x5.val)

set_option maxRecDepth 100000 in
theorem chkT_true : chkT = true := by decide +kernel

theorem pick (x5 x6 x7 : Fin 26) (h6 : x6 ≠ x5) (h7 : x7 ≠ x5)
    (hn : ¬((x6.val < 13 ∧ 13 ≤ x7.val ∧ (x6.val + 26 - x7.val) % 13 ∈ [0, 1, 3, 9]) ∨
      (x7.val < 13 ∧ 13 ≤ x6.val ∧ (x7.val + 26 - x6.val) % 13 ∈ [0, 1, 3, 9]))) :
    ∃ w ∈ W, w.2.testBit x6.val = true ∧ w.2.testBit x7.val = true ∧ w.2.testBit x5.val = false := by
  have h := chkT_true
  unfold chkT at h
  simp only [List.all_eq_true] at h
  have h' := h x5 (List.mem_finRange _) x6 (List.mem_finRange _) x7 (List.mem_finRange _)
  simp only [Bool.or_eq_true, decide_eq_true_eq, X2, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h'
  rcases h' with ((((e | e) | e) | e) | ⟨w, hw, ⟨a, b⟩, c⟩)
  · exact absurd e h6
  · exact absurd e h7
  · exact absurd (Or.inl e) hn
  · exact absurd (Or.inr e) hn
  · exact ⟨w, hw, a, b, c⟩

theorem mem4 (s M : ℕ) (cp : ∀ p : Fin 13, M.testBit p.val = s.testBit p.val)
    (cl : ∀ l : Fin 13, M.testBit (13 + l.val) = true ↔ (∀ q : Fin 13, s.testBit q.val = true → ¬(q = l ∨ q = l + 1 ∨ q = l + 3 ∨ q = l + 9))) (v : Fin 26) :
    ((∃ x6 : Fin 13, s.testBit x6.val = true ∧ v = Fin.castAdd 13 x6) ∨
      ∃ x6 : Fin 13, v = Fin.natAdd 13 x6 ∧ (∀ q : Fin 13, s.testBit q.val = true → ¬(q = x6 ∨ q = x6 + 1 ∨ q = x6 + 3 ∨ q = x6 + 9))) ↔ M.testBit v.val = true := by
  have hv26 := v.isLt
  constructor
  · rintro (⟨p, hp, rfl⟩ | ⟨l, rfl, hl⟩)
    · show M.testBit p.val = true
      rw [cp p]
      exact hp
    · show M.testBit (13 + l.val) = true
      exact (cl l).2 hl
  · intro h
    by_cases hv : v.val < 13
    · left
      refine ⟨⟨v.val, hv⟩, ?_, Fin.ext rfl⟩
      rw [← cp ⟨v.val, hv⟩]
      exact h
    · right
      have hlt : v.val - 13 < 13 := by omega
      have e : 13 + (v.val - 13) = v.val := by omega
      refine ⟨⟨v.val - 13, hlt⟩, Fin.ext ?_, ?_⟩
      · show v.val = 13 + (v.val - 13)
        omega
      · apply (cl ⟨v.val - 13, hlt⟩).1
        show M.testBit (13 + (v.val - 13)) = true
        rw [e]
        exact h

end PEqualNP.Outside.L_meta_6880

theorem PEqualNP.Outside.L_meta_6880 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x2 x3 : Fin (26 : ℕ)) => ↑x2 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x3 ∧ (↑x2 + (26 : ℕ) - ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x1 x5 x4; have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (26 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (26 : ℕ) | (∃ x6 ∈ x4, x5 = Fin.castAdd (13 : ℕ) x6) ∨ ∃ (x6 : Fin (13 : ℕ)), x5 = Fin.natAdd (13 : ℕ) x6 ∧ x3 x4 x6}; ∀ (x5 x6 x7 : Fin (26 : ℕ)), x6 ≠ x5 → x7 ≠ x5 → ¬(x2 x6 x7 ∨ x2 x7 x6) → ∃ (x11 : Finset (Fin (13 : ℕ))), (∀ x12 ∉ x11, ∃ (x14 : Fin (13 : ℕ)), x3 x11 x14 ∧ x1 x12 x14) ∧ ((¬∃ (x12 : Fin (13 : ℕ)), ∀ x13 ∈ x11, x1 x13 x12) ∧ ¬∃ (x12 : Fin (13 : ℕ)), ∀ (x13 : Fin (13 : ℕ)), x3 x11 x13 → x1 x12 x13) ∧ x6 ∈ x4 x11 ∧ x7 ∈ x4 x11 ∧ x5 ∉ x4 x11 := by
  dsimp only
  intro x5 x6 x7 h6 h7 hn
  obtain ⟨w, hw, a, b, c⟩ := PEqualNP.Outside.L_meta_6880.pick x5 x6 x7 h6 h7 hn
  have hg := List.all_eq_true.1 PEqualNP.Outside.L_meta_6880.allgood w hw
  unfold PEqualNP.Outside.L_meta_6880.good at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, cp⟩, cl⟩ := hg
  refine ⟨PEqualNP.Outside.L_meta_6880.Sset w.1, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, PEqualNP.Outside.L_meta_6880.mem_S]
  refine ⟨c1, ⟨c2, c3⟩, ?_, ?_, ?_⟩
  · exact (PEqualNP.Outside.L_meta_6880.mem4 w.1 w.2 cp cl x6).2 a
  · exact (PEqualNP.Outside.L_meta_6880.mem4 w.1 w.2 cp cl x7).2 b
  · intro h
    have h2 := (PEqualNP.Outside.L_meta_6880.mem4 w.1 w.2 cp cl x5).1 h
    rw [c] at h2
    exact Bool.false_ne_true h2
