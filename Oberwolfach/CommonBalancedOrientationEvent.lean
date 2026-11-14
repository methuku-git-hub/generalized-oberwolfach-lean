module

public import Oberwolfach.BalancedOrientation
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! A balanced correction can be included in any existing common event
when the sampled direction bits have the fair product law. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def BalancedSampleOrientationEvent {V:Type} [Fintype V] [LinearOrder V]
    (G:SimpleGraph V) (α:ℝ) (σ:Sym2 V→Bool):Prop :=
  ∀ F:SimpleGraph V,(∀v,(F.degree v:ℝ)≤α*Fintype.card V/100)→
    ∃ M:V→V→ℕ,
      (∀x y,M x y+M y x=if G.Adj x y then 1 else 0) ∧
      (∀v,(∑w,M v w)=G.degree v/2 ∧ (∑w,M w v)=G.degree v/2) ∧
      (∀x y,M x y≠sampledOrientation G σ x y ∨ M y x≠sampledOrientation G σ y x→¬F.Adj x y) ∧
      ∀x,((Finset.univ.filter (fun y=>M x y≠sampledOrientation G σ x y ∨
        M y x≠sampledOrientation G σ y x)).card:ℝ)≤4*(Fintype.card V:ℝ)^(4/5:ℝ)

theorem finiteLaw_common_balanced_orientation
    {Ω V:Type} [Fintype Ω] [Fintype V] [LinearOrder V]
    (μ:FiniteLaw Ω) (bits:Ω→Sym2 V→Bool)
    (hbits:∀E:(Sym2 V→Bool)→Prop,μ.probability (fun z=>E (bits z))=
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin)).probability E)
    (α:ℝ) (hα:0<α) (q:ℕ) (G:SimpleGraph V)
    (hN:(Classical.choose (balancedOrientation_highProbability_pow.{0} hα q))≤Fintype.card V)
    (heven:∀v,Even (G.degree v))
    (hmin:∀v,(1/2+α)*(Fintype.card V:ℝ)≤G.degree v)
    (Good:Ω→Prop) (ε:ℝ) (hGood:1-ε≤μ.probability Good):
    1-ε-1/(Fintype.card V:ℝ)^q≤μ.probability
      (fun z=>Good z ∧ BalancedSampleOrientationEvent G α (bits z)):=by
  have hb:=Classical.choose_spec (balancedOrientation_highProbability_pow.{0} hα q) V hN G heven hmin
  have hb':1-1/(Fintype.card V:ℝ)^q≤μ.probability
      (fun z=>BalancedSampleOrientationEvent G α (bits z)):=by
    rw [hbits]
    exact hb
  exact finiteLaw_intersection_lower μ Good (fun z=>BalancedSampleOrientationEvent G α (bits z)) ε _ hGood hb'
end Oberwolfach
