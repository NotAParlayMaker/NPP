import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4966_1
 (synthesize : let E := fun p l : Fin 25 => p.val < 12 ∧ 12 ≤ l.val ∧ (p.val+l.val+2)%13 ∈ ([0,1,3,9] : List ℕ) ∧ p.val ∉ ([0,2,8] : List ℕ)
∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 25 → ℕ) (f : ℕ), let W := fun (x : Fin 25 → Bool) (v : ℕ) => (C.wires (List.ofFn x)).getD v false
PEqualNP.MetaComplexity.Monotone2 C ∧
 C.size≤28 ∧
 (∀ p, o p<25+C.size) ∧
 f<25+C.size ∧
 (∀ x, (∀ p l, E p l → x p=true → x l=true → W x (o p)=true) ∧
    ((¬∃ p l, E p l ∧ x p=true ∧ x l=true) →
     (∀ p : Fin 25, p.val<12 → p.val ∉ ([0,2,8] : List ℕ) → x p=true → W x (o p)=false) ∧ W x f=(x 13 || x 15 || x 21))))
 (necessary : let E := fun p l : Fin 25 => p.val < 12 ∧ 12 ≤ l.val ∧ (p.val+l.val+2)%13 ∈ ([0,1,3,9] : List ℕ) ∧ p.val ∉ ([0,2,8] : List ℕ)
∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 25 → ℕ) (f : ℕ), let W := fun (x : Fin 25 → Bool) (v : ℕ) => (C.wires (List.ofFn x)).getD v false
PEqualNP.MetaComplexity.Monotone2 C →
 C.size≤28 →
 (∀ p, o p<25+C.size) →
 f<25+C.size →
 (∀ x, (∀ p l, E p l → x p=true → x l=true → W x (o p)=true) ∧
    ((¬∃ p l, E p l ∧ x p=true ∧ x l=true) →
     (∀ p : Fin 25, p.val<12 → p.val ∉ ([0,2,8] : List ℕ) → x p=true → W x (o p)=false) ∧ W x f=(x 13 || x 15 || x 21))) →
 ∃ p l, E p l ∧ W (fun j => decide (j=l)) (o p)=false) :
have x1 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x1 x2 : Fin (25 : ℕ)) => ↑x1 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x2 ∧ (↑x1 + ↑x2 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x1 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)]; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (25 : ℕ) → ℕ) (x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     x2.size ≤ (28 : ℕ) ∧       (∀ (x5 : Fin (25 : ℕ)), x3 x5 < (25 : ℕ) + x2.size) ∧         x4 < (25 : ℕ) + x2.size ∧           (∃ (x5 : Fin (25 : ℕ)) (x6 : Fin (25 : ℕ)), x1 x5 x6 ∧ (x2.wires (List.ofFn fun (x7 : Fin (25 : ℕ)) => Decidable.decide (x7 = x6))).getD (x3 x5) Bool.false = Bool.false) ∧             ∀ (x5 : Fin (25 : ℕ) → Bool),               have x6 : ℕ → Bool := fun (x6 : ℕ) => (x2.wires (List.ofFn x5)).getD x6 Bool.false;               (∀ (x7 x8 : Fin (25 : ℕ)), x1 x7 x8 → x5 x7 = Bool.true → x5 x8 = Bool.true → x6 (x3 x7) = Bool.true) ∧ ((¬∃ (x7 : Fin (25 : ℕ)) (x8 : Fin (25 : ℕ)), x1 x7 x8 ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true) → (∀ (x8 : Fin (25 : ℕ)), ↑x8 < (12 : ℕ) → ↑x8 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] → x5 x8 = Bool.true → x6 (x3 x8) = Bool.false) ∧ x6 x4 = (x5 (13 : Fin (25 : ℕ)) || x5 (15 : Fin (25 : ℕ)) || x5 (21 : Fin (25 : ℕ)))) := by
  obtain ⟨C,o,f,m,b,ro,rf,ct⟩ := synthesize
  exact ⟨C,o,f,m,b,ro,rf,necessary C o f m b ro rf ct,ct⟩
