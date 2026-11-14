module

public import Oberwolfach.OrdinaryWheelLikelySeparateCostsCertificate
public import Oberwolfach.OrdinaryGeneralSameSampleProbability

@[expose] public section
/-! The actual general-wheel reference and pairing event supplies the
    per-host probability certificate for the protected level chain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_general_reference_cover_certificate_separate
    (m:ℕ) (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (p ρ εsup τ ν η ell ζ βe βh loss budget deepBudget cost deepCost:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell)
    (μ:FiniteLaw (Sym2 (V⊕U)→Bool)) (hn:16≤Fintype.card V) (hloss:loss≤1/4)
    (hcost:budget≤cost) (hdeep:deepBudget≤deepCost)
    (hprob:1-(loss+2/(Fintype.card (V⊕U):ℝ))-
      (1/(Fintype.card V:ℝ)+1/(Fintype.card (V⊕U):ℝ))≤μ.probability (fun σ=>
      OrdinaryGeneralRootFirstCleanupSample m Q F H X T Z W η ell τ ν D p βe βh σ ∧
      OrdinaryGeneralFreshPairingSample m Q Qfactor F H Hfactor X Z p ρ ζ εsup σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W (m+1)
        budget deepBudget)):
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W (m+1) cost deepCost :=by
  let E:=fun σ:Sym2 (V⊕U)→Bool=>
    OrdinaryGeneralRootFirstCleanupSample m Q F H X T Z W η ell τ ν D p βe βh σ ∧
    OrdinaryGeneralFreshPairingSample m Q Qfactor F H Hfactor X Z p ρ ζ εsup σ ∧
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W (m+1)
      budget deepBudget
  refine ⟨μ,E,loss,budget,deepBudget,hn,hloss,hprob,?_,hcost,hdeep⟩
  intro σ hσ
  exact hσ.2.2
end Oberwolfach
