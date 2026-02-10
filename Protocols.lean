abbrev Agent := String

inductive Message (σ : Nat) where
| empty : Message σ
| text : String → Message σ
| agent : Agent → Message σ
| symmetricKey : Agent → Agent → Message σ → Message σ
| publicKey : Agent → Message σ
| secretKey : Agent → Message σ
| encrypt : Message σ → Message σ → Message σ
| concat : Message σ → Message σ → Message σ
deriving Repr, BEq

notation " #μ " i => Message.empty i
notation " # " t " # " => Message.text t
notation " pk( " i " ) " => Message.publicKey i
notation " sk( " i " ) " => Message.secretKey i
notation " ⦃| " m " |⦄ " k  => Message.encrypt m k
notation " ag( " i " ) " => Message.agent i
notation " text( " t " ) " => Message.text t
notation m₁ " ‖ " m₂ => Message.concat m₁ m₂

inductive Action (σ : Nat) where
| send : Agent → Agent → Message σ → Action σ
| recv : Agent → Message σ → Action σ
| comp : Action σ → Action σ → Action σ
| reun : Action σ → Action σ → Action σ
deriving Repr, BEq

notation " send " i ", " j " ( " μ " ) " => Action.send i j μ
notation " recv " i " ( " μ " ) " => Action.recv i μ
notation α₁ " ; " α₂ => Action.comp α₁ α₂
notation α₁ " ∪∪ " α₂ => Action.reun α₁ α₂

inductive State (σ : Nat) where
| explicit : Agent → Message σ → State σ
| add : Agent → Message σ → State σ → State σ
deriving Repr, BEq

notation a " ▷ " μ => State.explicit a μ
notation a " ▷ " μ "⊔ " γ₁ => State.add a μ γ₁

inductive Formula (σ : Nat) where
| atom : Fin σ → Formula σ
| true : Formula σ
| neg : Formula σ → Formula σ
| imp : Formula σ → Formula σ → Formula σ
| believe : Agent → Formula σ → Formula σ
| explicit : Agent → Message σ → Formula σ
| state2form : State σ → Formula σ
| state : Formula σ → Formula σ
| action : Action σ → Formula σ → Formula σ
deriving Repr, BEq

notation " #ϕ " i => Formula.atom i
notation " ⊤ " => Formula.true
notation " ~ " φ => Formula.neg φ
notation " ⊥ " => (~⊤)
notation φ " ⟶ " ψ => Formula.imp φ ψ
notation φ " ⋁ " ψ => ((~φ) ⟶ ψ)
notation φ " ⋀ " ψ => ~((~φ) ⋁ (~ψ))
notation " 𝔹 " i " , " φ => Formula.believe i φ
notation " 𝕂 " i " , " φ => (𝔹 i, φ) ⋀ φ
notation " 𝕏 " i " , " m => Formula.explicit i m
notation " ι " γ => Formula.state2form γ
notation " ⟨ " γ " ⟩ " => Formula.state γ
notation " [ " α " ] " φ => Formula.action α φ

abbrev Context (σ : Nat) := List $ Formula σ

inductive Proof {σ : Nat} : Context σ → Formula σ → Prop
-- Hilbert basic
| ax { Γ } { p : Formula σ } (h : Γ.Mem p) : Proof Γ p
| pl₁ { Γ } { p q : Formula σ } : Proof Γ (p ⟶ (q ⟶ p))
| pl₂ { Γ } { p q r : Formula σ } : Proof Γ $ (p ⟶ (q ⟶ r)) ⟶ ((p ⟶ q) ⟶ (p ⟶ r))
| pl₃ { Γ } { p q : Formula σ } : Proof Γ $ ((~p) ⟶ ~q) ⟶ (q ⟶ p)
-- K axiom for programs
| Kα { Γ } { φ ψ : Formula σ } { α : Action σ } : Proof Γ $ ([α](φ ⟶ ψ)) ⟶ (([α]φ) ⟶ ([α]ψ))
-- Belief
| K𝔹 { Γ } { φ ψ : Formula σ } { a : Agent } : Proof Γ $ (𝔹 a, (φ ⟶ ψ)) ⟶ ((𝔹 a, φ) ⟶ (𝔹 a, ψ))
| D { Γ } { φ : Formula σ } {a : Agent} : Proof Γ $ (𝔹 a, φ) ⟶ ~(𝔹 a, (~φ))
| _4 { Γ } { φ : Formula σ } {a : Agent} : Proof Γ $ (𝔹 a, φ) ⟶ (𝔹 a, (𝔹 a, φ))
| _5 { Γ } { φ : Formula σ } {a : Agent} : Proof Γ $ (~(𝔹 a, φ)) ⟶ (𝔹 a, (~(𝔹 a, φ)))
-- Deduction rules
| MP { Γ } { p q : Formula σ } (hpq : Proof Γ $ p ⟶ q) (hp : Proof Γ p) : Proof Γ q
| NEC𝔹 { Γ } { φ : Formula σ } { a : Agent } (hφ : Proof Γ φ) : Proof Γ $ 𝔹 a, φ
| NECα { Γ } { φ : Formula σ } { α : Action σ } (hφ : Proof Γ φ) : Proof Γ $ [α]φ
-- Actions
| Acomp_left { Γ } {α₁ α₂ : Action σ } { φ : Formula σ } : Proof Γ $ ([α₁ ; α₂]φ) ⟶ [α₁]([α₂]φ)
| Acomp_right { Γ } {α₁ α₂ : Action σ } { φ : Formula σ } : Proof Γ $ ([α₁]([α₂]φ)) ⟶ ([α₁ ; α₂]φ)
-- States
| St₁_left { Γ } { γ₂ : State σ } { a b : Agent } { m₁ m₂ : Message σ } : Proof Γ $ ⟨ι (a ▷ m₁ ⊔ b ▷ m₂ ⊔ γ₂)⟩ ⟶ ⟨ι (b ▷ m₂ ⊔ a ▷ m₁ ⊔ γ₂)⟩
-- | St₁_right { Γ } { γ₁ γ₂ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ (ι (a ▷ m ⊔ (γ₁ ⊔ γ₂))) ⟶  ι (γ₁ ⊔ ((a ▷ m) ⊔ γ₂))
| St₂_left { Γ } { γ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ (ι (a ▷ m ⊔ (a ▷ m ⊔ γ))) ⟶  ι (a ▷ m ⊔ γ)
| St₂_right { Γ } { γ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ (ι (a ▷ m ⊔ γ)) ⟶ ι (a ▷ m ⊔ (a ▷ m ⊔ γ))
| St₃ { Γ } { γ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ ⟨ ι (a ▷ m ⊔ γ) ⟩  ⟶ 𝕏 a, m
-- theorems
--| St₁_left' { Γ } { γ₁ γ₂ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ ⟨ι (γ₁ ⊔ ((a ▷ m) ⊔ γ₂))⟩ ⟶  ⟨ι ((a ▷ m) ⊔ (γ₁ ⊔ γ₂))⟩
--| St₁_right' { Γ } { γ₁ γ₂ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ ⟨ι ((a ▷ m) ⊔ (γ₁ ⊔ γ₂))⟩ ⟶  ⟨ι (γ₁ ⊔ ((a ▷ m) ⊔ γ₂))⟩
| St₂_left' { Γ } { γ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ ⟨ι (a ▷ m ⊔ (a ▷ m ⊔ γ))⟩ ⟶  ⟨ι (a ▷ m ⊔ γ)⟩
| St₂_right' { Γ } { γ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ ⟨ι (a ▷ m ⊔ γ)⟩ ⟶ ⟨ι (a ▷ m ⊔ (a ▷ m ⊔ γ))⟩

notation Γ " ⊢ " φ => Proof Γ φ

/-
  **PROTOCOLS**
-/

open Formula
open Proof

inductive ProtocolProof { σ : Nat } : Context σ → Formula σ → Prop
-- an extension of standard proofs
| base { Γ } { φ } (proof : Proof Γ φ) : ProtocolProof Γ φ
-- messages
| X₁_left { Γ } { a : Agent } { m₁ m₂ : Message σ } : ProtocolProof Γ $ (𝕏 a, (m₁.concat m₂)) ⟶ ((𝕏 a, m₁) ⋀ (𝕏 a, m₂))
| X₁_right { Γ } { a : Agent }{ m₁ m₂ : Message σ } : ProtocolProof Γ $ ((𝕏 a, m₁) ⋀ (𝕏 a, m₂)) ⟶ (𝕏 a, (m₁.concat m₂))
| X₂_left { Γ } { a b : Agent } { k : Message σ } : ProtocolProof Γ $ (𝕏 a, (Message.symmetricKey a b k)) ⟶ (𝕏 b, (Message.symmetricKey b a k))
| X₂_right { Γ } { a b : Agent } { k : Message σ } : ProtocolProof Γ $ (𝕏 b, (Message.symmetricKey b a k)) ⟶ (𝕏 a, (Message.symmetricKey a b k))
| X₃ { Γ } { a b : Agent } { m : Message σ } : ProtocolProof Γ $ ((𝕏 a, ⦃|m|⦄ pk(b)) ⋀ (⟨ 𝕏 a, sk(b) ⟩)) ⟶ (𝕏 a, m)
| X₄ { Γ } { a b : Agent } { m : Message σ } : ProtocolProof Γ $ ((𝕏 a, ⦃|m|⦄ sk(b)) ⋀ (𝕏 a, pk(b))) ⟶ (𝕏 a, m)
| X₅ { Γ } { a : Agent } { m₁ m₂ : Message σ } : ProtocolProof Γ $ ((𝕏 a, m₁) ⋀ (𝕏 a, m₂)) ⟶ 𝕏 a, ⦃|m₁|⦄m₂
| X₆ { Γ } { a b : Agent } { m k : Message σ } : ProtocolProof Γ $ ((𝕏 a, ⦃|m|⦄ (Message.symmetricKey a b k)) ⋀ (𝕏 a, (Message.symmetricKey a b k))) ⟶ (𝕏 a, m)
| X₇ { Γ } { a : Agent } : ProtocolProof Γ $ (𝕏 a, ag(a))
-- protocol general hypotheses
| H₁ { Γ } { a b : Agent } {m : Message σ } { γ : State σ } : ProtocolProof Γ $ ⟨ ι (a ▷ m ⊔ γ) ⟩ ⟶ [send a,b(⦃| ag(a) ‖ m |⦄pk(b))]⟨ ι (a ▷ m ⊔ γ) ⟩
| H₂ { Γ } { a b : Agent } {m : Message σ } { γ : State σ } : ProtocolProof Γ $ ⟨ ι (a ▷ m ⊔ γ) ⟩ ⟶ [recv b(⦃| ag(a) ‖ m |⦄pk(b))]⟨ ι (b ▷ m ⊔ a ▷ m ⊔ γ) ⟩

notation Γ " ⊢ₚ " φ => ProtocolProof Γ φ

inductive OSSProof { σ : Nat } : Context σ → Formula σ → Prop
| base { Γ } { φ } (proof : ProtocolProof Γ φ) : OSSProof Γ φ
| S₁ { Γ } {a b : Agent } { m : Message σ } { γ : State σ } : OSSProof Γ $ ⟨ ι (a ▷ m ⊔ γ) ⟩ ⟶ [send a,b(⦃| ag(a) ‖  m |⦄pk(b))]𝔹 a, 𝕏 b, m
| S₂ { Γ } { a b : Agent } { m : Message σ } { γ : State σ } : OSSProof Γ $ ⟨ ι γ ⟩ ⟶ [recv b(⦃| ag(a) ‖  m |⦄pk(b))]𝔹 b, 𝕏 a, m

-- added to simplify
| MP { Γ } { p q : Formula σ } (hpq : OSSProof Γ $ p ⟶ q) (hp : OSSProof Γ p) : OSSProof Γ q
| NECα { Γ } { φ : Formula σ } { α : Action σ } (hφ : OSSProof Γ φ) : OSSProof Γ $ [α]φ

notation Γ " ⊢ₒₛₛ " φ => OSSProof Γ φ

inductive OSSEProof { σ : Nat } : Context σ → Formula σ → Prop
| base { Γ } { φ } (proof : OSSProof Γ φ) : OSSEProof Γ φ
-- axioms which define the adversary (de intrebat)
| H₁ₑ { Γ } { a b e : Agent } {m : Message σ } { γ : State σ } : OSSEProof Γ $ ⟨ ι (a ▷ m ⊔ γ) ⟩ ⟶ [send a,b(⦃| ag(a) ‖ m |⦄pk(b))]⟨ ι (e ▷ m ⊔ (a ▷ m ⊔ γ)) ⟩ -- nu am folosit-o
| H₂ₑ { Γ } { a b e : Agent } {m : Message σ } { γ : State σ } { α : Action σ } : OSSEProof Γ $ ⟨ ι (e ▷ m ⊔ γ) ⟩ ⟶ [α ; recv b(⦃| ag(a) ‖ m |⦄pk(b))]⟨ ι (b ▷ m ⊔ (e ▷ m ⊔ γ)) ⟩
| adv₁ { Γ } {a b e : Agent } { m : Message σ } { γ : State σ } { α : Action σ } : OSSEProof Γ $ ⟨ ι (e ▷ m ⊔ γ) ⟩ ⟶ [send e,b(⦃| ag(a) ‖  m |⦄pk(b)) ; α]𝕏 e, m
| adv₂ { Γ } {a b e : Agent } { m : Message σ } { γ : State σ } { α : Action σ } : OSSEProof Γ $ ⟨ ι (e ▷ m ⊔ γ) ⟩ ⟶ [send e,b(⦃| ag(a) ‖  m |⦄pk(b)) ; α]𝔹 e, 𝕏 b, m
-- de intrebat
| H₁' { Γ } { a b e : Agent } {m : Message σ } { γ : State σ } : OSSEProof Γ $ ⟨ ι (e ▷ m ⊔ γ) ⟩ ⟶ [send e,b(⦃| ag(a) ‖ m |⦄pk(b))]⟨ ι (e ▷ m ⊔ γ) ⟩

-- added to simplify
| MP { Γ } { p q : Formula σ } (hpq : OSSEProof Γ $ p ⟶ q) (hp : OSSEProof Γ p) : OSSEProof Γ q

notation Γ " ⊢ₒₛₛₑ " φ => OSSEProof Γ φ

def γᵢₙᵢₜ {σ : Nat} {i r : Agent} : State σ := r ▷ sk(r) ⊔ r ▷ pk(i) ⊔ r ▷ pk(r) ⊔ i ▷ pk(i) ⊔ i ▷ sk(i) ⊔ i ▷ pk(r)
def γᵢₙᵢₜₑ {σ : Nat} {i r e : Agent} : State σ := r ▷ sk(r) ⊔ r ▷ pk(i) ⊔ r ▷ pk(r) ⊔ r ▷ pk(e) ⊔
                                                 i ▷ pk(i) ⊔ i ▷ sk(i) ⊔ i ▷ pk(r) ⊔ i ▷ pk(e) ⊔
                                                 e ▷ sk(e) ⊔ e ▷ pk(e) ⊔ e ▷ pk(i) ⊔ e ▷ pk(r)

@[simp]
theorem pl_transitivity {σ : Nat} {p q r : Formula σ} { Γ : Context σ } :
  (Γ ⊢ (p ⟶ q)) → (Γ ⊢ (q ⟶ r)) → (Γ ⊢ (p ⟶ r)) := by
  intros hpq hqr
  have H₁ : Γ ⊢ (p ⟶ q ⟶ r) := Proof.MP Proof.pl₁ hqr
  have H₂ : Γ ⊢ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ (p ⟶ r)) := Proof.pl₂
  have H₃ : Γ ⊢ ((p ⟶ q) ⟶ (p ⟶ r)) := Proof.MP H₂ H₁
  exact Proof.MP H₃ hpq

@[simp]
theorem pl_transitivity_oss {σ : Nat} {p q r : Formula σ} { Γ : Context σ } :
  (Γ ⊢ₒₛₛ (p ⟶ q)) →
  (Γ ⊢ₒₛₛ (q ⟶ r)) →
  (Γ ⊢ₒₛₛ (p ⟶ r)) := by
  intros hpq hqr
  have h₁ : Γ ⊢ₒₛₛ (p ⟶ q ⟶ r) :=
    OSSProof.MP
      (OSSProof.base (ProtocolProof.base Proof.pl₁))
      hqr
  have h₂ : Γ ⊢ₒₛₛ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ (p ⟶ r)) :=
    OSSProof.base (ProtocolProof.base Proof.pl₂)
  have h₃ : Γ ⊢ₒₛₛ ((p ⟶ q) ⟶ (p ⟶ r)) :=
    OSSProof.MP h₂ h₁
  exact OSSProof.MP h₃ hpq

@[simp]
theorem pl_transitivity_osse {σ : Nat} {p q r : Formula σ} { Γ : Context σ } :
  (Γ ⊢ₒₛₛₑ (p ⟶ q)) →
  (Γ ⊢ₒₛₛₑ (q ⟶ r)) →
  (Γ ⊢ₒₛₛₑ (p ⟶ r)) := by
  intros hpq hqr
  have h₁ : Γ ⊢ₒₛₛₑ (p ⟶ q ⟶ r) :=
    OSSEProof.MP
      (OSSEProof.base $ OSSProof.base (ProtocolProof.base Proof.pl₁))
      hqr
  have h₂ : Γ ⊢ₒₛₛₑ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ (p ⟶ r)) :=
    OSSEProof.base $ OSSProof.base (ProtocolProof.base Proof.pl₂)
  have h₃ : Γ ⊢ₒₛₛₑ ((p ⟶ q) ⟶ (p ⟶ r)) :=
    OSSEProof.MP h₂ h₁
  exact OSSEProof.MP h₃ hpq

@[simp]
theorem pl2_aux {σ : Nat} {p q r : Formula σ} { Γ : Context σ } :
  (Γ ⊢ₒₛₛ (p ⟶ q)) →
  (Γ ⊢ₒₛₛ (p ⟶ q ⟶ r)) →
  (Γ ⊢ₒₛₛ (p ⟶ r)) := by
  intros hpq hpqr
  exact OSSProof.MP (OSSProof.MP (OSSProof.base (ProtocolProof.base Proof.pl₂)) hpqr) hpq

@[simp]
theorem pl2_aux_e {σ : Nat} {p q r : Formula σ} { Γ : Context σ } :
  (Γ ⊢ₒₛₛₑ (p ⟶ q)) →
  (Γ ⊢ₒₛₛₑ (p ⟶ q ⟶ r)) →
  (Γ ⊢ₒₛₛₑ (p ⟶ r)) := by
  intros hpq hpqr
  exact OSSEProof.MP (OSSEProof.MP (OSSEProof.base $ OSSProof.base (ProtocolProof.base Proof.pl₂)) hpqr) hpq

@[simp]
theorem dl_th_1 {σ : Nat} { p q r : Formula σ } { α : Action σ } { Γ : Context σ } :
  (Γ ⊢ₒₛₛ (p ⟶ ([α]q))) →
  (Γ ⊢ₒₛₛ (p ⟶ ([α]r))) →
  (Γ ⊢ₒₛₛ (p ⟶ ([α](q ⋀ r)))) := by
  intros hq hr
  have prop_formula : Γ ⊢ (q ⟶ r ⟶ q ⋀ r) := by
    admit
  have nec_formula : Γ ⊢ₒₛₛ ([α](q ⟶ (r ⟶ q ⋀ r))) ⟶ ([α]q) ⟶ ([α](r ⟶ q ⋀ r)) := OSSProof.base (ProtocolProof.base Proof.Kα)
  have h₀ : Γ ⊢ₒₛₛ ([α](q ⟶ (r ⟶ q ⋀ r))) := OSSProof.base (ProtocolProof.base (Proof.NECα prop_formula))
  have h₁ : Γ ⊢ₒₛₛ ([α]q) ⟶ ([α](r ⟶ q ⋀ r)) := OSSProof.MP nec_formula h₀
  have h₂ : Γ ⊢ₒₛₛ (p ⟶ ([α](r ⟶ q ⋀ r))) := pl_transitivity_oss hq h₁
  have nec_formula : Γ ⊢ₒₛₛ ([α](r ⟶ q ⋀ r)) ⟶ ([α](r)) ⟶ ([α](q ⋀ r)) := OSSProof.base (ProtocolProof.base Proof.Kα)
  have h₃ := pl_transitivity_oss h₂ nec_formula
  exact pl2_aux hr h₃

@[simp]
theorem dl_th_1_e {σ : Nat} { p q r : Formula σ } { α : Action σ } { Γ : Context σ } :
  (Γ ⊢ₒₛₛₑ (p ⟶ ([α]q))) →
  (Γ ⊢ₒₛₛₑ (p ⟶ ([α]r))) →
  (Γ ⊢ₒₛₛₑ (p ⟶ ([α](q ⋀ r)))) := by
  intros hq hr
  have prop_formula : Γ ⊢ (q ⟶ r ⟶ q ⋀ r) := by
    admit
  have nec_formula : Γ ⊢ₒₛₛₑ ([α](q ⟶ (r ⟶ q ⋀ r))) ⟶ ([α]q) ⟶ ([α](r ⟶ q ⋀ r)) := OSSEProof.base $ OSSProof.base (ProtocolProof.base Proof.Kα)
  have h₀ : Γ ⊢ₒₛₛₑ ([α](q ⟶ (r ⟶ q ⋀ r))) := OSSEProof.base $ OSSProof.base (ProtocolProof.base (Proof.NECα prop_formula))
  have h₁ : Γ ⊢ₒₛₛₑ ([α]q) ⟶ ([α](r ⟶ q ⋀ r)) := OSSEProof.MP nec_formula h₀
  have h₂ : Γ ⊢ₒₛₛₑ (p ⟶ ([α](r ⟶ q ⋀ r))) := pl_transitivity_osse hq h₁
  have nec_formula : Γ ⊢ₒₛₛₑ ([α](r ⟶ q ⋀ r)) ⟶ ([α](r)) ⟶ ([α](q ⋀ r)) := OSSEProof.base $ OSSProof.base (ProtocolProof.base Proof.Kα)
  have h₃ := pl_transitivity_osse h₂ nec_formula
  exact pl2_aux_e hr h₃

@[simp]
theorem dl_th_3 {σ : Nat} { p q : Formula σ } { α β : Action σ } { Γ : Context σ } :
  (Γ ⊢ₒₛₛ (p ⟶ [α]([β]q))) →
  (Γ ⊢ₒₛₛ (p ⟶ ([α ; β]q))) := by
  intro Hαβ
  exact pl_transitivity_oss Hαβ (OSSProof.base $ ProtocolProof.base $ Proof.Acomp_right)

@[simp]
theorem dl_th_4 {σ : Nat} { p q : Formula σ } { α β : Action σ } { Γ : Context σ } :
  (Γ ⊢ₒₛₛ (p ⟶ ([α ; β]q))) →
  (Γ ⊢ₒₛₛ (p ⟶ [α]([β]q))) := by
  intro Hαβ
  exact pl_transitivity_oss Hαβ (OSSProof.base $ ProtocolProof.base $ Proof.Acomp_left)

@[simp]
theorem reductio_ad_absurdum {σ : Nat} { p q : Formula σ } { Γ : Context σ } : (Γ ⊢ ((~q) ⟶ (~(p ⟶ p)))) → (Γ ⊢ q) := by
  intro H
  exact Proof.MP (Proof.MP Proof.pl₃ H) (Proof.MP (Proof.MP Proof.pl₂ Proof.pl₁) (@Proof.pl₁ _ _ p p))

@[simp]
theorem premises_comm {σ : Nat} { p q r : Formula σ } { Γ : Context σ } : (Γ ⊢ (p ⟶ (q ⟶ r))) → (Γ ⊢ (q ⟶ (p ⟶ r))) := by
  intro H
  exact Proof.MP (Proof.MP Proof.pl₂ (Proof.MP Proof.pl₁ (Proof.MP Proof.pl₂ H))) Proof.pl₁

@[simp]
theorem contradiction {σ : Nat} { p q : Formula σ } { Γ : Context σ } : Γ ⊢ (q ⟶ ((~q) ⟶ p)) :=
  premises_comm (pl_transitivity Proof.pl₁ Proof.pl₃)

@[simp]
theorem dne {σ : Nat} { p : Formula σ } { Γ : Context σ } : Γ ⊢ ((~(~p)) ⟶ p) := by admit

@[simp]
theorem rec_ax3 {σ : Nat} { p q : Formula σ } { Γ : Context σ }: Γ ⊢ (p ⟶ q) ⟶ ((~q) ⟶ (~p)) := by admit

@[simp]
theorem dl_th_2 {σ : Nat} { p q r : Formula σ } { α β : Action σ } { Γ : Context σ } :
  (Γ ⊢ₒₛₛ (p ⟶ ([α][β](q ⋀ r)))) →
  (Γ ⊢ₒₛₛ (p ⟶ ([α][β]r))) := by
  intros h
  have prop_formula : Γ ⊢ ((q ⋀ r) ⟶ r) := by
    have H₁ : Γ ⊢ ((~r) ⟶ ((~q) ⋁ (~r))) := Proof.pl₁
    let Hmp := Proof.MP rec_ax3 H₁
    exact (pl_transitivity Hmp (@dne _ r _))
  have nec_formula : Γ ⊢ₒₛₛ [α ; β]((q ⋀ r) ⟶ r) := OSSProof.base $ ProtocolProof.base (Proof.NECα prop_formula)
  let nec_formula_K := OSSProof.base $ ProtocolProof.base $ @Proof.Kα _ Γ (q ⋀ r) r (α ; β)
  let HMP := OSSProof.MP nec_formula_K nec_formula
  let Htrans := dl_th_3 h
  exact (pl_transitivity_oss Htrans (dl_th_4 HMP))


@[simp]
theorem pl_aux {σ : Nat} {p q r : Formula σ} { Γ : Context σ } :
  (Γ ⊢ₒₛₛ (p ⟶ q)) →
  (Γ ⊢ₒₛₛ (r ⋀ p) ⟶ (r ⋀ q)) := by
  intros hpq
  admit

theorem oss { σ : Nat } { Γ : Context σ } { i r : Agent } { nᵢ : Message σ } :
  Γ ⊢ₒₛₛ ⟨ ι (i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r)) ⟩
    ⟶ [(send i, r(⦃| ag(i) ‖ nᵢ |⦄pk(r))) ; (recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r)))](𝕂 r, 𝕏 i, nᵢ ) :=  by
  have H₁ : Γ ⊢ₒₛₛ ⟨ ι (i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ [send i,r(⦃| ag(i) ‖ nᵢ |⦄pk(r))](𝔹 i, 𝕏 r, nᵢ)
    := OSSProof.S₁
  have H₂ : Γ ⊢ₒₛₛ ⟨ ι (i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ [send i,r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]⟨ ι (i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r))⟩
    := OSSProof.base $ ProtocolProof.H₁
  have H₃ : Γ ⊢ₒₛₛ ⟨ ι (i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ [send i,r(⦃| ag(i) ‖ nᵢ |⦄pk(r))](𝔹 i,  𝕏 r, nᵢ ) ⋀ ⟨ ι (i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r))⟩
    := dl_th_1 H₁ H₂
  have H₄ : Γ ⊢ₒₛₛ ⟨ ι (i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))](𝔹 r, 𝕏 i, nᵢ )
    := OSSProof.S₂
  have H₅ : Γ ⊢ₒₛₛ ⟨ ι (i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]⟨ ι (r ▷ nᵢ ⊔ i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r))⟩
    := OSSProof.base $ ProtocolProof.H₂
  have H₆ : Γ ⊢ₒₛₛ ⟨ ι (i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))](𝔹 r, 𝕏 i, nᵢ ) ⋀ ⟨ ι (r ▷ nᵢ ⊔ i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r))⟩
    := dl_th_1 H₄ H₅
  have H₇ : Γ ⊢ₒₛₛ [send i,r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]⟨ ι (i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))](𝔹 r, 𝕏 i, nᵢ ) ⋀ ⟨ ι (r ▷ nᵢ ⊔ i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r))⟩
    := OSSProof.NECα H₆
  have H₈ : Γ ⊢ₒₛₛ ([send i,r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]⟨ ι (i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))](𝔹 r, 𝕏 i, nᵢ) ⋀ ⟨ ι (r ▷ nᵢ ⊔ i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r))⟩) ⟶
            ([send i,r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]⟨ ι (i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r)) ⟩) ⟶ ([send i,r(⦃| ag(i) ‖ nᵢ |⦄pk(r))][recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))](𝔹 r, 𝕏 i, nᵢ) ⋀ ⟨ ι (r ▷ nᵢ ⊔ i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r))⟩)
    := OSSProof.base $ ProtocolProof.base $ Proof.Kα
  have H₉ : Γ ⊢ₒₛₛ ⟨ι (r ▷ nᵢ ⊔ i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r))⟩ ⟶ ⟨ι (i ▷ nᵢ ⊔ r ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r))⟩
    := OSSProof.base $ ProtocolProof.base $ Proof.St₁_left
  have H₁₀ : Γ ⊢ₒₛₛ ⟨ι (i ▷ nᵢ ⊔ r ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r))⟩ ⟶ 𝕏 i, nᵢ
    := OSSProof.base $ ProtocolProof.base $ Proof.St₃
  have H₁₁ : Γ ⊢ₒₛₛ [send i,r(⦃| ag(i) ‖ nᵢ |⦄pk(r)) ; recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]((𝔹 r, 𝕏 i, nᵢ) ⋀ ⟨ ι (r ▷ nᵢ ⊔ i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r))⟩) ⟶ ((𝔹 r, 𝕏 i, nᵢ) ⋀ 𝕏 i, nᵢ)
    := OSSProof.NECα (pl_aux (pl_transitivity_oss H₉ H₁₀))
  let H₁₂ := OSSProof.base $ ProtocolProof.base $ @Proof.Kα _ Γ ((𝔹 r, 𝕏 i, nᵢ) ⋀ ⟨ ι (r ▷ nᵢ ⊔ i ▷ nᵢ ⊔ (@γᵢₙᵢₜ σ i r))⟩) ((𝔹 r, 𝕏 i, nᵢ) ⋀ 𝕏 i, nᵢ) (send i,r(⦃| ag(i) ‖ nᵢ |⦄pk(r)) ; recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r)))
  exact pl_transitivity_oss (dl_th_3 $ pl_transitivity_oss H₂ (OSSProof.MP H₈ H₇)) (OSSProof.MP H₁₂ H₁₁)

theorem oss_mitm { σ : Nat } { Γ : Context σ } { i r e : Agent } { nₑ : Message σ } :
  Γ ⊢ₒₛₛₑ ⟨ ι (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e)) ⟩
    ⟶ [(send e, r(⦃| ag(i) ‖ nₑ |⦄pk(r))) ; (recv r(⦃| ag(i) ‖ nₑ |⦄pk(r)))](((𝕂 e, 𝕏 r, nₑ) ⋀ (𝕏 e, nₑ)) ⋀ (𝔹 r, 𝕏 i, nₑ)) := by
  have H₁ : Γ ⊢ₒₛₛₑ ⟨ ι (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e)) ⟩ ⟶ [send e,r(⦃| ag(i) ‖ nₑ |⦄pk(r))]⟨ ι (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e)) ⟩
    := OSSEProof.H₁'
  have H₂ : Γ ⊢ₒₛₛ ⟨ ι (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e)) ⟩ ⟶ [(recv r(⦃| ag(i) ‖ nₑ |⦄pk(r)))](𝔹 r, 𝕏 i, nₑ)
    := OSSProof.S₂
  have H₃ : Γ ⊢ₒₛₛ [(send e, r(⦃| ag(i) ‖ nₑ |⦄pk(r)))]⟨ ι (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e)) ⟩ ⟶ [(recv r(⦃| ag(i) ‖ nₑ |⦄pk(r)))](𝔹 r, 𝕏 i, nₑ)
    := OSSProof.NECα H₂
  have H₄ : Γ ⊢ₒₛₛ ([(send e, r(⦃| ag(i) ‖ nₑ |⦄pk(r)))]⟨ ι (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e)) ⟩ ⟶ [(recv r(⦃| ag(i) ‖ nₑ |⦄pk(r)))](𝔹 r, 𝕏 i, nₑ)) ⟶
                  ([(send e, r(⦃| ag(i) ‖ nₑ |⦄pk(r)))]⟨ ι (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e)) ⟩) ⟶ ([(send e, r(⦃| ag(i) ‖ nₑ |⦄pk(r)))][(recv r(⦃| ag(i) ‖ nₑ |⦄pk(r)))](𝔹 r, 𝕏 i, nₑ))
    := OSSProof.base $ ProtocolProof.base $ Proof.Kα
  have H₅ : Γ ⊢ₒₛₛₑ ⟨ ι (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e)) ⟩ ⟶ [(send e, r(⦃| ag(i) ‖ nₑ |⦄pk(r))) ; (recv r(⦃| ag(i) ‖ nₑ |⦄pk(r)))]𝕏 e, nₑ
    := OSSEProof.adv₁
  have H₆ : Γ ⊢ₒₛₛₑ ⟨ ι (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e)) ⟩ ⟶ [(send e, r(⦃| ag(i) ‖ nₑ |⦄pk(r))) ; (recv r(⦃| ag(i) ‖ nₑ |⦄pk(r)))]𝔹 e, 𝕏 r, nₑ
    := OSSEProof.adv₂
  have H₇ : Γ ⊢ₒₛₛₑ ⟨ ι (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e)) ⟩ ⟶ [(send e, r(⦃| ag(i) ‖ nₑ |⦄pk(r))) ; (recv r(⦃| ag(i) ‖ nₑ |⦄pk(r)))]⟨ ι (r ▷ nₑ ⊔ (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e))) ⟩
    := OSSEProof.H₂ₑ
  have H₈ : Γ ⊢ₒₛₛ ⟨ ι (r ▷ nₑ ⊔ (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e))) ⟩ ⟶ 𝕏 r, nₑ
    := OSSProof.base $ ProtocolProof.base $ Proof.St₃
  have H₉ : Γ ⊢ₒₛₛ [(send e, r(⦃| ag(i) ‖ nₑ |⦄pk(r))) ; (recv r(⦃| ag(i) ‖ nₑ |⦄pk(r)))]⟨ ι (r ▷ nₑ ⊔ (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e))) ⟩ ⟶ 𝕏 r, nₑ
    := OSSProof.NECα H₈
  have H₁₀ : Γ ⊢ₒₛₛ ([(send e, r(⦃| ag(i) ‖ nₑ |⦄pk(r))) ; (recv r(⦃| ag(i) ‖ nₑ |⦄pk(r)))]⟨ ι (r ▷ nₑ ⊔ (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e))) ⟩ ⟶ 𝕏 r, nₑ) ⟶
                   ([(send e, r(⦃| ag(i) ‖ nₑ |⦄pk(r))) ; (recv r(⦃| ag(i) ‖ nₑ |⦄pk(r)))]⟨ ι (r ▷ nₑ ⊔ (e ▷ nₑ ⊔ (@γᵢₙᵢₜₑ σ i r e))) ⟩) ⟶
                   ([(send e, r(⦃| ag(i) ‖ nₑ |⦄pk(r))) ; (recv r(⦃| ag(i) ‖ nₑ |⦄pk(r)))] 𝕏 r, nₑ)
    := OSSProof.base $ ProtocolProof.base $ Proof.Kα
  exact dl_th_1_e (dl_th_1_e (dl_th_1_e H₆ (pl_transitivity_osse H₇ (OSSEProof.base $ OSSProof.MP H₁₀ H₉))) H₅) (pl_transitivity_osse H₁ (OSSEProof.base $ dl_th_3 $ OSSProof.MP H₄ H₃))

inductive NSProof { σ : Nat } : Context σ → Formula σ → Prop
| base { Γ } { φ } (proof : ProtocolProof Γ φ) : NSProof Γ φ

| S₁ { Γ } {a b : Agent } { m : Message σ } { γ : State σ } {α : Action σ} : NSProof Γ $ ⟨ ι (a ▷ m ⊔ γ) ⟩ ⟶ [send a,b(⦃| ag(a) ‖  m |⦄pk(b)); α]𝔹 a, (𝕏 b, m)
| S₂ { Γ } { a b : Agent } { m₁ m₂ : Message σ } { γ : State σ } {α : Action σ} : NSProof Γ $ ⟨ ι (b ▷ m₂ ⊔ γ) ⟩ ⋀ 𝔹 a, (𝕏 b, m₁) ⟶ [send b,a(⦃| m₁ ‖  m₂ |⦄pk(a))]𝔹 b, (𝕏 a, m₂)
| S₃ { Γ } { a b : Agent } { m₂ : Message σ } {α : Action σ} : NSProof Γ $ 𝔹 b, ⟨ 𝕏 a, m₂ ⟩ ⟶ [send a,b(⦃| m₂ |⦄pk(b)); α](𝕏 a, m₂)

| R₁ { Γ } {a b : Agent } { m : Message σ } { γ : State σ } {α : Action σ} : NSProof Γ $ ⟨ ι γ ⟩ ⟶ [α ; recv b(⦃| ag(a) ‖  m |⦄pk(b))]𝔹 b, (𝕏 a, m)
| R₁' { Γ } {a b : Agent } { m : Message σ } { γ : State σ } : NSProof Γ $ ⟨ ι γ ⟩ ⟶ [recv b(⦃| ag(a) ‖  m |⦄pk(b))]𝔹 b, (𝕏 a, m)
| R₂ { Γ } { a b : Agent } { m₁ m₂ : Message σ } { γ : State σ } : NSProof Γ $ ⟨ ι γ ⟩ ⟶ [recv b(⦃| ag(a) ‖  m₁ |⦄pk(b)); recv a(⦃| m₁ ‖  m₂ |⦄pk(a))]𝔹 a, (𝕏 b, (m₁ ‖ m₂))
| R₃ { Γ } { a b : Agent } { m₁ m₂ : Message σ } { γ : State σ } : NSProof Γ $ ⟨ ι γ ⟩ ⟶ [recv a(⦃| m₁ ‖  m₂ |⦄pk(a)); recv b(⦃| m₂ |⦄pk(b))]𝔹 b, (𝕏 a, m₂)

| MP { Γ } { p q : Formula σ } (hpq : NSProof Γ $ p ⟶ q) (hp : NSProof Γ p) : NSProof Γ q
| NECα { Γ } { φ : Formula σ } { α : Action σ } (hφ : NSProof Γ φ) : NSProof Γ $ [α]φ
| NEC𝔹 { Γ } { φ : Formula σ } { a : Agent } (hφ : NSProof Γ φ) : NSProof Γ $ 𝔹 a, φ

notation Γ " ⊢ₙₛ " φ => NSProof Γ φ

@[simp]
theorem pl_transitivity_ns {σ : Nat} {p q r : Formula σ} { Γ : Context σ } :
  (Γ ⊢ₙₛ (p ⟶ q)) →
  (Γ ⊢ₙₛ (q ⟶ r)) →
  (Γ ⊢ₙₛ (p ⟶ r)) := by
  intros hpq hqr
  have h₁ : Γ ⊢ₙₛ (p ⟶ q ⟶ r) :=
    NSProof.MP
      (NSProof.base (ProtocolProof.base Proof.pl₁))
      hqr
  have h₂ : Γ ⊢ₙₛ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ (p ⟶ r)) :=
    NSProof.base (ProtocolProof.base Proof.pl₂)
  have h₃ : Γ ⊢ₙₛ ((p ⟶ q) ⟶ (p ⟶ r)) :=
    NSProof.MP h₂ h₁
  exact NSProof.MP h₃ hpq

@[simp]
theorem pl2_aux_ns {σ : Nat} {p q r : Formula σ} { Γ : Context σ } :
  (Γ ⊢ₙₛ (p ⟶ q)) →
  (Γ ⊢ₙₛ (p ⟶ q ⟶ r)) →
  (Γ ⊢ₙₛ (p ⟶ r)) := by
  intros hpq hpqr
  exact NSProof.MP (NSProof.MP (NSProof.base (ProtocolProof.base Proof.pl₂)) hpqr) hpq

@[simp]
theorem dl_th_1_ns {σ : Nat} { p q r : Formula σ } { α : Action σ } { Γ : Context σ } :
  (Γ ⊢ₙₛ (p ⟶ ([α]q))) →
  (Γ ⊢ₙₛ (p ⟶ ([α]r))) →
  (Γ ⊢ₙₛ (p ⟶ ([α](q ⋀ r)))) := by
  intros hq hr
  have prop_formula : Γ ⊢ (q ⟶ r ⟶ q ⋀ r) := by
    admit
  have nec_formula : Γ ⊢ₙₛ ([α](q ⟶ (r ⟶ q ⋀ r))) ⟶ ([α]q) ⟶ ([α](r ⟶ q ⋀ r)) := NSProof.base $ (ProtocolProof.base Proof.Kα)
  have h₀ : Γ ⊢ₙₛ ([α](q ⟶ (r ⟶ q ⋀ r))) := NSProof.base (ProtocolProof.base (Proof.NECα prop_formula))
  have h₁ : Γ ⊢ₙₛ ([α]q) ⟶ ([α](r ⟶ q ⋀ r)) := NSProof.MP nec_formula h₀
  have h₂ : Γ ⊢ₙₛ (p ⟶ ([α](r ⟶ q ⋀ r))) := pl_transitivity_ns hq h₁
  have nec_formula : Γ ⊢ₙₛ ([α](r ⟶ q ⋀ r)) ⟶ ([α](r)) ⟶ ([α](q ⋀ r)) := NSProof.base (ProtocolProof.base Proof.Kα)
  have h₃ := pl_transitivity_ns h₂ nec_formula
  exact pl2_aux_ns hr h₃

theorem ns { σ : Nat } { Γ : Context σ } { i r : Agent } { nᵢ : Message σ } :
  Γ ⊢ₙₛ ⟨ ι (i ▷ nᵢ ⊔ @γᵢₙᵢₜ σ i r) ⟩
    ⟶ [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))](𝕂 r, (𝕏 i, nᵢ)) := by
  have H₁ : Γ ⊢ₙₛ ⟨ ι (i ▷ nᵢ ⊔ @γᵢₙᵢₜ σ i r) ⟩ ⟶ [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]𝔹 r, (𝕏 i, nᵢ)
    := NSProof.R₁'
  have H₂ : Γ ⊢ₙₛ ⟨ ι (i ▷ nᵢ ⊔ r ▷ nᵢ ⊔ @γᵢₙᵢₜ σ i r) ⟩ ⟶ 𝕏 i, nᵢ
    := NSProof.base $ ProtocolProof.base $ Proof.St₃
  let H₃ := @NSProof.NECα _ Γ (⟨ ι (i ▷ nᵢ ⊔ r ▷ nᵢ ⊔ @γᵢₙᵢₜ σ i r) ⟩ ⟶ 𝕏 i, nᵢ) (recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))) H₂
  let H₄ := NSProof.base $ ProtocolProof.base $ (@Proof.Kα _ Γ ⟨ ι (i ▷ nᵢ ⊔ r ▷ nᵢ ⊔ @γᵢₙᵢₜ σ i r) ⟩ (𝕏 i, nᵢ) (recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))))
  let H₅ := NSProof.MP H₄ H₃
  have H₆ : Γ ⊢ₙₛ ⟨ ι (i ▷ nᵢ ⊔ @γᵢₙᵢₜ σ i r) ⟩ ⟶ [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]⟨ ι (r ▷ nᵢ ⊔ i ▷ nᵢ ⊔ @γᵢₙᵢₜ σ i r) ⟩
     := NSProof.base $ ProtocolProof.H₂
  have H₇ : Γ ⊢ₙₛ ⟨ι (r ▷ nᵢ ⊔ i ▷ nᵢ ⊔ @γᵢₙᵢₜ σ i r)⟩ ⟶ ⟨ι (i ▷ nᵢ ⊔ r ▷ nᵢ ⊔ @γᵢₙᵢₜ σ i r)⟩
    := NSProof.base $ ProtocolProof.base $ Proof.St₁_left
  have H₈ := @NSProof.NECα _ Γ (⟨ι (r ▷ nᵢ ⊔ i ▷ nᵢ ⊔ @γᵢₙᵢₜ σ i r)⟩ ⟶ ⟨ι (i ▷ nᵢ ⊔ r ▷ nᵢ ⊔ @γᵢₙᵢₜ σ i r)⟩) (recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))) H₇
  have H₉ := NSProof.base $ ProtocolProof.base $ (@Proof.Kα _ Γ ⟨ι (r ▷ nᵢ ⊔ i ▷ nᵢ ⊔ @γᵢₙᵢₜ σ i r)⟩ ⟨ι (i ▷ nᵢ ⊔ r ▷ nᵢ ⊔ @γᵢₙᵢₜ σ i r)⟩ (recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))))
  have H₁₀ := NSProof.MP H₉ H₈
  let H₁₁ := pl_transitivity_ns (pl_transitivity_ns H₆ H₁₀) H₅
  exact (dl_th_1_ns H₁ H₁₁)

/-
  **AUTOMATED GENERATED MODEL**
-/

/-
  **Generate model**
-/

namespace hidden
def State (σ : Nat) := List (List $ Message σ)

def EmptyMessage (σ : Nat) : Message σ := Message.empty
def EmptyState {σ : Nat} : State σ := [[]]

structure AutomaticallyGeneratedModel (σ : Nat) where
  Agents : List Agent
  States : List $ State σ
  R𝕂 : List $ (Agent × List Nat)
  R𝔹 : List $ (Agent × List Nat)
  RPDLSend : List $ (Agent × Agent × Message σ × List Nat)
  RPDLRecv : List $ (Agent × Message σ × List Nat)
  RPDLGen : List $ (Agent × Message σ × List Nat)

def List.getAtIndex {α : Type} (list : List α) (i : Nat) : Option α :=
  match i with
  | 0 => list.head?
  | i' + 1 => List.getAtIndex (list.tail!) i'

def List.getAtIndex! {α : Type} (list : List α) (i : Nat) (default : α) : α :=
  match List.getAtIndex list i with
  | none => default
  | some result => result

def MessageContext (σ : Nat) := List $ Message σ

def DeductionClosureStep {σ : Nat} (Γ : MessageContext σ) (Γc : MessageContext σ) : MessageContext σ :=
  match Γ with
  | [] => []
  | (m :: tail) => match m with
    | ⦃|m'|⦄k => if Γc.contains k && !Γc.contains m' then m' :: m :: DeductionClosureStep tail Γc else m :: DeductionClosureStep tail Γc
    | m₁ ‖ m₂ =>
    if Γc.contains (m₁ ‖ m₂) then
      if Γc.contains m₁ then
        if Γc.contains m₂ then
          m :: DeductionClosureStep tail Γc
        else
          m :: m₂ :: DeductionClosureStep tail Γc
      else
        if Γc.contains m₂ then
          m :: m₁ :: DeductionClosureStep tail Γc
        else
          m :: m₁ :: m₂ :: DeductionClosureStep tail Γc
    else m :: DeductionClosureStep tail Γc
    | _ => m :: DeductionClosureStep tail Γc

set_option maxHeartbeats 800000

def DeductionClosure {σ : Nat} (Γ : MessageContext σ) : MessageContext σ :=
  let Γ₀ := DeductionClosureStep Γ Γ
  let Γ₁ := DeductionClosureStep Γ₀ Γ₀
  let Γ₂ := DeductionClosureStep Γ₁ Γ₁
  Γ₂


def MessageInfer {σ : Nat} (Γ : MessageContext σ) (m : Message σ) : Bool :=
  let Γ' := DeductionClosure Γ
  match m with
  | Message.empty => True
  | m₁ ‖ m₂ => Γ'.contains (m₁ ‖ m₂) || (Γ'.contains m₁ && Γ'.contains m₂)
  | ⦃|m₁|⦄m₂ => Γ'.contains (⦃|m₁|⦄m₂) || (Γ'.contains m₁ && Γ'.contains m₂)
  | sk(i) => Γ'.contains $ sk(i)
  | pk(i) => Γ'.contains $ pk(i)
  | ag(i) => Γ'.contains $ ag(i)
  | text(t) => Γ'.contains $ text(t)
  | Message.symmetricKey i j k => Γ'.contains $ Message.symmetricKey i j k

notation Γ " ⊢μ " m => MessageInfer Γ m

def AwarenessSatisfies {σ : Nat} (M : AutomaticallyGeneratedModel σ) (wIndex : Nat) (agent : Agent) (m : Message σ) : Bool :=
  let modelAgents : List Agent := M.Agents
  let numberOfAgents : Nat := modelAgents.length
  let zippedAgentList := List.zip modelAgents $ List.range numberOfAgents
  let agentStatePosition : Nat := List.getAtIndex! (List.map (fun (_, pos) => pos) (List.filter  (fun (ag, _) => ag == agent) zippedAgentList) ) 0 0
  let currentState : State σ := List.getAtIndex! M.States wIndex EmptyState
  let currentAgentState := List.getAtIndex! currentState agentStatePosition []
  currentAgentState ⊢μ m

def ModalKBStates {σ : Nat} (_ : AutomaticallyGeneratedModel σ) (wIndex : Nat) (agent : Agent) (relation : List $ (Agent × List Nat)) : List Nat :=
  let agentRelation : List $ List Nat := ((relation.filter (fun (ag, _) => ag == agent)).map (fun (_, y) => y)).filter (fun list => List.getAtIndex! list 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => List.getAtIndex! list 1 0)
  accessibleStates


def PDLSendStates {σ : Nat} (_ : AutomaticallyGeneratedModel σ) (wIndex : Nat) (i : Agent) (j : Agent) (m : Message σ) (relation : List $ (Agent × Agent × Message σ × List Nat)) : List Nat :=
  let agentRelation : List $ List Nat := ((relation.filter (fun (agi, agj, msg, _) => agi == i && agj == j && msg == m)).map (fun (_, _, _, y) => y)).filter (fun list => List.getAtIndex! list 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => List.getAtIndex! list 1 0)
  accessibleStates

def PDLRecvStates {σ : Nat} (_ : AutomaticallyGeneratedModel σ) (wIndex : Nat) (j : Agent) (m : Message σ) (relation : List $ (Agent × Message σ × List Nat)) : List Nat :=
  let agentRelation : List $ List Nat := ((relation.filter (fun (agj, msg, _) => agj == j && msg == m)).map (fun (_, _, y) => y)).filter (fun list => List.getAtIndex! list 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => List.getAtIndex! list 1 0)
  accessibleStates

def PDLGenStates {σ : Nat} (_ : AutomaticallyGeneratedModel σ) (wIndex : Nat) (j : Agent) (m : Message σ) (relation : List $ (Agent × Message σ × List Nat)) : List Nat :=
  let agentRelation : List $ List Nat := ((relation.filter (fun (agj, msg, _) => agj == j && msg == m)).map (fun (_, _, y) => y)).filter (fun list => List.getAtIndex! list 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => List.getAtIndex! list 1 0)
  accessibleStates

def SatisfiesAtState {σ : Nat} (M : AutomaticallyGeneratedModel σ) (φ : Formula σ) (wIndex : Nat) : Bool :=
  match φ with
  | Formula.atom _ => True
  | Formula.true => True
  | φ ⟶ ψ => (SatisfiesAtState M φ wIndex) → (SatisfiesAtState M ψ wIndex)
  | ~φ => !(SatisfiesAtState M φ wIndex)
  | 𝕏 agent, m => AwarenessSatisfies M wIndex agent m
  | 𝔹 agent, φ =>
    let accessibleStates := ModalKBStates M wIndex agent M.R𝔹
    let applySatisfaction := accessibleStates.map (fun accessibleState => SatisfiesAtState M φ accessibleState)
    applySatisfaction.foldr (fun x y => x && y) True
  | [send i, j(m)] φ =>
    let accessibleStates := PDLSendStates M wIndex i j m M.RPDLSend
    let applySatisfaction := accessibleStates.map (fun accessibleState => SatisfiesAtState M φ accessibleState)
    applySatisfaction.foldr (fun x y => x && y) True
  | [recv j(m)] φ =>
    let accessibleStates := PDLRecvStates M wIndex j m M.RPDLRecv
    let applySatisfaction := accessibleStates.map (fun accessibleState => SatisfiesAtState M φ accessibleState)
    applySatisfaction.foldr (fun x y => x && y) True
  | _ => True

notation M " at " w " ⊧ " φ => SatisfiesAtState M φ w

def Satisfies {σ : Nat} (M : AutomaticallyGeneratedModel σ) (φ : Formula σ) : Bool :=
  let allStates := List.range $ M.States.length
  let satisfiesAllStates := allStates.map (fun state => M at state ⊧ φ)
  satisfiesAllStates.foldr (fun x y => x && y) True

notation M " ⊧ " φ => Satisfies M φ


structure ProtocolAction (σ : Nat) where
  Sender: Agent
  Receiver: Agent
  Message: Message σ

instance EmptyProtocolAction {σ : Nat} : ProtocolAction σ :=
{
  Sender := "",
  Receiver := "",
  Message := Message.empty
}

structure Protocol (σ : Nat) where
  Agents : List Agent
  SymmetricKeys : List $ (Agent × Agent × Message σ)
  Specification : List $ ProtocolAction σ

def GetAllSubMessages {σ : Nat} (m : Message σ) : List $ Message σ :=
  match m with
  | Message.empty => []
  | text(t) => [text(t) ]
  | ag(i) => [ag(i) ]
  | Message.symmetricKey k i j => [Message.symmetricKey k i j]
  | pk(i) => [pk(i) ]
  | sk(i) => [sk(i) ]
  | ⦃|m|⦄k => GetAllSubMessages m ++ [k]
  | m₁ ‖ m₂ => GetAllSubMessages m₁ ++ GetAllSubMessages m₂

def GetAllMessagesFromList {σ : Nat} (list : List $ Message σ) : List $ Message σ :=
  match list with
  | [] => []
  | (message :: tail) =>
    match message with
    | Message.empty => tail
    | text(t) => text(t) :: tail
    | ag(i) => ag(i) :: tail
    | Message.symmetricKey k i j => (Message.symmetricKey k i j) :: tail
    | pk(i) => pk(i) :: tail
    | sk(i) => sk(i) :: tail
    | ⦃|m|⦄k => GetAllSubMessages (⦃|m|⦄k) ++ [⦃|m|⦄k] ++ tail
    | m₁ ‖ m₂ => GetAllSubMessages (m₁ ‖ m₂) ++ [m₁ ‖ m₂] ++ tail

def List.removeDuplicates {α : Type} [BEq α] (list : List α) : List α :=
  match list with
  | [] => []
  | (head :: tail) => if tail.contains head then tail else head :: tail


def AppendAgentNewKnowledge {σ : Nat} (P : Protocol σ) (agent : Agent) (currentState : State σ) (newKnowledge : List $ Message σ) : State σ :=
  let agentsNumber := P.Agents.length
  let agentsPositions := List.zip P.Agents $ List.range $ agentsNumber
  let agentPosition := List.getAtIndex! (List.map (fun (_, pos) => pos) (List.filter (fun (ag, _) => ag == agent) agentsPositions)) 0 0
  let stateForAgents := currentState.zip $ List.range $ agentsNumber
  let newState := stateForAgents.map (fun (ik, pos) =>
    if pos == agentPosition then List.removeDuplicates (List.append ik newKnowledge) else ik
  )
  newState

def getAtIndexAux! : List α → Nat → Nat → α → α := fun la currentIndex searchedIndex default =>
  match la with
  | [] => default
  | (x::xs) => if currentIndex == searchedIndex then x else getAtIndexAux! xs (currentIndex + 1) searchedIndex default

def getAtIndex! : List α → Nat → α → α := fun la index default => getAtIndexAux! la 0 index default

def BuildFromActions {σ : Nat} (P : Protocol σ) (currentStateIndex : Nat) (states : List $ State σ) (statesLeft : Nat)
  : (List $ State σ)
  × (List $ (Agent × Agent × Message σ × List Nat))
  × (List $ (Agent × Message σ × List Nat)) :=
  match statesLeft with
  | 0 => ([], [], [])
  | n + 1 =>
    let currentAction := List.getAtIndex! P.Specification currentStateIndex ({ Sender := "", Receiver := "", Message := Message.empty })
    let sender := currentAction.Sender
    let receiver := currentAction.Receiver
    let message := currentAction.Message
    let lastState := List.getAtIndex! states (states.length - 1) EmptyState
    let newState := AppendAgentNewKnowledge P sender lastState [message]

    let newUpdatedState :=
      if currentStateIndex != 0 then
        let lastAction := List.getAtIndex! P.Specification (currentStateIndex - 1) ({ Sender := "", Receiver := "", Message := Message.empty })
        let lastReceiver := lastAction.Receiver
        let lastMessage := lastAction.Message
        AppendAgentNewKnowledge P lastReceiver newState [lastMessage]
      else newState

    (newUpdatedState :: (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).fst,
    if message != Message.empty then
      ((sender, receiver, message, [currentStateIndex, currentStateIndex + 1]) :: (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).snd.fst)
    else (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).snd.fst,
    if message != Message.empty then
      ((receiver, message, [currentStateIndex, currentStateIndex + 1]) :: (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).snd.snd)
    else (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).snd.snd
    )

def BuildModel {σ : Nat} (P : Protocol σ) : AutomaticallyGeneratedModel σ :=
  let specification := P.Specification
  let agentsNumber := P.Agents.length
  let agentsPositions := List.zip P.Agents $ List.range $ agentsNumber

  let initialAction := getAtIndex! specification 0 EmptyProtocolAction
  let agentsInitialKnowledgeEmpty : List $ List $ Message σ := List.replicate agentsNumber []
  let initialAgentPosition := getAtIndex! ((agentsPositions.filter (fun (ag, _) => ag == initialAction.Sender)).map (fun (_, pos) => pos)) 0 0

  let agentsInitialKnowledge := ((agentsInitialKnowledgeEmpty.zip (List.range agentsNumber)).map (fun (ik, agentPos) =>
    if agentPos == initialAgentPosition then ik.append [initialAction.Message] else ik.append []))

  let agentsInitialKnowledgeKeys := (agentsInitialKnowledge.zip (List.range agentsNumber)).map (fun (ik, pos) =>
    let agentByPos := getAtIndex! ((agentsPositions.filter (fun ((_ : Agent), y) => y == pos)).map (fun ((x : Agent), (_ : Nat)) => x)) 0 ""
    let searchInSymmetricKeys := P.SymmetricKeys.filter (fun ((x : Agent), (y : Agent), (_ : Message σ)) => x == agentByPos || y == agentByPos)
    let key := if searchInSymmetricKeys.length > 0 then (getAtIndex! searchInSymmetricKeys 0 (("", "", Message.empty) : Agent × Agent × Message σ)).snd.snd else Message.empty
    let otherAgentsPublicKeys : List $ Message σ := (P.Agents.filter (fun ag => ag != agentByPos)).map (fun ag => pk(ag))
    if key != Message.empty then (ik.append [key, sk(agentByPos), pk(agentByPos) ]).append otherAgentsPublicKeys else (ik.append [sk(agentByPos), pk(agentByPos) ]).append otherAgentsPublicKeys
    )

  let initialState : State σ := agentsInitialKnowledgeKeys

  let result := BuildFromActions P 0 [initialState] (specification.length + 1)

  let states := result.fst
  let pdlRelationSend := result.snd.fst

  let firstOccuranceForEveryAgent := P.Agents.map (fun agent =>
    let firstState : Nat := getAtIndex! (getAtIndex! ((pdlRelationSend.filter (fun (ag, _, _, _) => ag == agent)).map (fun (_, _, _, ls) => ls)) 0 []) 0 0
    (agent, firstState)
  )

  let numberOfStates := states.length

  let knowledge_relation := firstOccuranceForEveryAgent.map (fun (ag, initialAgentState) =>
    let allStates := List.range numberOfStates
    let agentStates := (List.foldr (fun x y => x ++ y) [] $ (allStates.map (fun x => allStates.map (fun y => if x <= y then [x, y] else []))))
    let agentListFiltered := agentStates.filter (fun (list : List Nat) => getAtIndex! list 0 0 >= initialAgentState)
    (agentListFiltered.map (fun list => (ag, list))).filter (fun (_, list) => list != [])
  )

  let knowledge := List.foldr (fun x y => x ++ y) [] knowledge_relation

  let belief_relation := firstOccuranceForEveryAgent.map (fun (ag, initialAgentState) =>
    let allStates := List.range numberOfStates
    let agentStates := (List.foldr (fun x y => x ++ y) [] $ (allStates.map (fun x => allStates.map (fun y => if x < y then [x, y] else [])))) ++ ([[getAtIndex! allStates (allStates.length - 1) 0, getAtIndex! allStates (allStates.length - 1) 0]])
    let agentListFiltered := agentStates.filter (fun (list : List Nat) => getAtIndex! list 0 0 >= initialAgentState)
    (agentListFiltered.map (fun list => (ag, list))).filter (fun (_, list) => list != [])
  )

  let belief := List.foldr (fun x y => x ++ y) [] belief_relation

  {
    Agents := P.Agents,
    States := states,
    R𝕂 := knowledge,
    R𝔹 := belief,
    RPDLSend := pdlRelationSend,
    RPDLRecv := result.snd.snd,
    RPDLGen := []
  }


/-
  **OSS**
-/

section OSS
  instance OSS {σ : Nat} : Protocol σ :=
  {
    Agents := ["i", "r"]
    SymmetricKeys := []
    Specification := [
      { Sender := "i", Receiver := "r", Message := ⦃|#"i"# ‖ #"ni"#|⦄pk("r") }
    ]
  }

  def OSSModel {σ : Nat} : AutomaticallyGeneratedModel σ := BuildModel OSS

  #reduce OSSModel

  -- { Agents := ["i", "r"],
  -- States :=
  --   [[[ sk( "i" ) , pk( "i" ) , pk( "r" ) , ⦃| text( "i" ) ‖ text( "ni" ) |⦄ pk( "r" ) ],
  --       [ sk( "r" ) , pk( "r" ) , pk( "i" ) ]],
  --     [[ sk( "i" ) , pk( "i" ) , pk( "r" ) , ⦃| text( "i" ) ‖ text( "ni" ) |⦄ pk( "r" ) , Message.empty],
  --       [ sk( "r" ) , pk( "r" ) , pk( "i" ) , ⦃| text( "i" ) ‖ text( "ni" ) |⦄ pk( "r" ) ]]],
  -- R𝕂 := [("i", [0, 0]), ("i", [0, 1]), ("i", [1, 1]), ("r", [0, 0]), ("r", [0, 1]), ("r", [1, 1])],
  -- R𝔹 := [("i", [0, 1]), ("i", [1, 1]), ("r", [0, 1]), ("r", [1, 1])],
  -- RPDLSend := [("i", "r", ⦃| text( "i" ) ‖ text( "ni" ) |⦄ pk( "r" ) , [0, 1])],
  -- RPDLRecv := [("r", ⦃| text( "i" ) ‖ text( "ni" ) |⦄ pk( "r" ) , [0, 1])], RPDLGen := [] }

  #reduce OSSModel ⊧ 𝕏 "i", #"ni"#

  #reduce OSSModel ⊧ ~[recv "r"(⦃|#"i"# ‖ #"ni"#|⦄pk("r"))] (𝕏 "r", (⦃|#"i"# ‖ #"ni"#|⦄pk("r")))

  #reduce OSSModel ⊧ [recv "r"(⦃|#"i"# ‖ #"ni"#|⦄pk("r"))] ((𝕂 "i", 𝕏 "r", #"ni"#) ⋀ (𝕂 "r", 𝕏 "i", #"ni"#))



end OSS

section OSSE
  instance OSSE {σ : Nat} : Protocol σ :=
  {
    Agents := ["i", "r", "e"]
    SymmetricKeys := []
    Specification := [
      { Sender := "e", Receiver := "r", Message := ⦃|#"i"# ‖ #"ne"#|⦄pk("r") }
    ]
  }

  def OSSEModel {σ : Nat} : AutomaticallyGeneratedModel σ := BuildModel OSSE

  #reduce OSSEModel

  #reduce OSSEModel ⊧ [recv "r"(⦃|#"i"# ‖ #"ni"#|⦄pk("r"))] ((𝕂 "i", 𝕏 "r", #"ni"#) ⋀ (𝕂 "r", 𝕏 "i", #"ni"#))

end OSSE

/-
  **Needham Schroeder**
-/

section NeedhamSchroeder
  instance NeedhamSchroeder {σ : Nat} : Protocol σ :=
  {
    Agents := ["i", "r"]
    SymmetricKeys := []
    Specification := [
      { Sender := "i", Receiver := "r", Message := ⦃|ag("i") ‖ #"ni"#|⦄pk("r") },
      { Sender := "r", Receiver := "r", Message := ⦃|#"ni"# ‖ #"nr"# |⦄pk("i") },
      { Sender := "i", Receiver := "r", Message := ⦃|#"nr"#|⦄pk("r") }
    ]
  }

  def NeedhamSchroederModel {σ : Nat} : AutomaticallyGeneratedModel σ := BuildModel NeedhamSchroeder

  #reduce NeedhamSchroederModel

  #reduce NeedhamSchroederModel ⊧ [recv "r"(⦃|ag("i") ‖ #"ni"#|⦄pk("r"))] ((𝕂 "r", 𝕏 "i", #"ni"#) ⋀ (𝕂 "i", 𝕏 "r", #"ni"#))
  -- true

  -- #reduce NeedhamSchroederModel ⊧ [recv "r"(⦃|ag("i") ‖ #"ni"#|⦄pk("r"))] ([recv "i"(⦃|#"ni"# ‖ #"nr"# |⦄pk("i"))] 𝕂 "i", 𝕏 "r", #"nr"#)
  -- true

end NeedhamSchroeder

section NeedhamSchroederMitM
  instance NeedhamSchroederMitM {σ : Nat} : Protocol σ :=
  {
    Agents := ["i", "r", "e"]
    SymmetricKeys := []
    Specification := [
      { Sender := "i", Receiver := "e", Message := ⦃|ag("i") ‖ #"ni"#|⦄pk("e") },
      { Sender := "e", Receiver := "r", Message := ⦃|ag("i") ‖ #"ni"#|⦄pk("r") },
      { Sender := "r", Receiver := "e", Message := ⦃|#"ni"# ‖ #"nr"# |⦄pk("e") },
      { Sender := "e", Receiver := "i", Message := ⦃|#"ni"# ‖ #"nr"# |⦄pk("i") },
      { Sender := "i", Receiver := "e", Message := ⦃|#"nr"#|⦄pk("e") },
      { Sender := "e", Receiver := "r", Message := ⦃|#"nr"#|⦄pk("r") }
    ]
  }

  def NeedhamSchroederMitMModel {σ : Nat} : AutomaticallyGeneratedModel σ := BuildModel NeedhamSchroederMitM

  #reduce NeedhamSchroederMitMModel

  -- #reduce NeedhamSchroederMitMModel ⊧ [recv "r"(⦃|ag("i") ‖ #"ni"#|⦄pk("r"))] 𝕂 "r", 𝕏 "i", #"ni"#
  -- true

  -- #reduce NeedhamSchroederMitMModel ⊧ 𝕂 "i", 𝕏 "r", #"ni"#
  -- false
end NeedhamSchroederMitM
end hidden
