module

public import Oberwolfach.OrdinaryCombinedTriangleInputs

@[expose] public section
/-! The original simultaneous triangle host and absorber-input event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def ordinaryCombinedTriangleEvent (d k:ℕ) (P F:SimpleGraph V) (π:Equiv.Perm V)
    (θ α pstar βP ηP ηH βH c B pR pH:ℝ)
    (weight:OrdinaryCycle P 3→ℝ) (j:Color)
    (σ:RawWheelOutcome V U Γ Color):Prop :=
  let w:=ordinaryFullHostSeed (U:=U) P F 3 weight pR pH;

      ((∀ v:V,βH*Fintype.card V≤(Fintype.card {u:U // rawWheelSpokes π d σ j v u}:ℝ)) ∧
      ((∀ x y,P.Adj x y→¬F.Adj x y→
        |ordinaryPotentialLoad w (Sum.inl s(x,y)) ((rawWheelGraph P σ)\F) (rawWheelSpokes π d σ j)-1|≤ηH) ∧
       (∀ v u,|ordinaryPotentialLoad w (Sum.inr (v,u)) ((rawWheelGraph P σ)\F) (rawWheelSpokes π d σ j)-1|≤ηH)) ∧
      (∀ x y:V,x≠y→¬F.Adj x y→
        βH≤ordinaryIsolatorPotential P F (rawWheelSpokes π d σ j) k θ (α/4) x y (fun e=>σ (Sum.inl e))) ∧
      (∀ v:V,∀ u u':U,u≠u'→βH≤transferSurvivalSum 3 (by omega) P F
        (transferRootCompletedSpokes (rawWheelSpokes π d σ j) v) v u u' (fun e=>σ (Sum.inl e)))) ∧
      (ordinarySampledTriangleProfileProperty P F π d σ pstar pstar j βP ηP c B ∧
       Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) 3
         (fun (_:Unit)=>pairedAbsorberTemplate 3) βP ((ordinaryLocalCountCoeff 2 βP/2)^4)
         c (4*B/(pstar^3*(pstar*pstar)^2)) ηP) ∧
       (∀ T:Finset V,T.card≤9→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
         βP*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ)))
end Oberwolfach
