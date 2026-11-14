module

public import Oberwolfach.OrdinaryCombinedFullHostInputs

@[expose] public section
/-! The simultaneous event in the ordinary full-host experiment, named so
that the actual class law can be substituted without changing the event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def ordinaryCombinedHostEvent (m d k:ℕ) (hm:3≤m) (P F:SimpleGraph V) (π:Equiv.Perm V)
    (θ α pstar βP ηP row ηH βH c B pR pH:ℝ)
    (weight:OrdinaryCycle P (m+1)→ℝ) (s:U→Color→ℝ) (j:Color)
    (σ:RawWheelOutcome V U Γ Color):Prop :=
  let w:=ordinaryFullHostSeed (U:=U) P F (m+1) weight pR pH;

      ((∀ v:V,βH*Fintype.card V≤(Fintype.card {u:U // rawWheelSpokes π d σ j v u}:ℝ)) ∧
      ((∀ x y,P.Adj x y→¬F.Adj x y→
        |ordinaryPotentialLoad w (Sum.inl s(x,y)) ((rawWheelGraph P σ)\F) (rawWheelSpokes π d σ j)-1|≤ηH) ∧
       (∀ v u,|ordinaryPotentialLoad w (Sum.inr (v,u)) ((rawWheelGraph P σ)\F) (rawWheelSpokes π d σ j)-1|≤ηH)) ∧
      (∀ x y:V,x≠y→¬F.Adj x y→
        βH≤ordinaryIsolatorPotential P F (rawWheelSpokes π d σ j) k θ (α/4) x y (fun e=>σ (Sum.inl e))) ∧
      (∀ v:V,∀ u u':U,u≠u'→βH≤transferSurvivalSum (m+1) (by omega) P F
        (transferRootCompletedSpokes (rawWheelSpokes π d σ j) v) v u u' (fun e=>σ (Sum.inl e)))) ∧
      (ordinarySampledProfileProperty (r:=m+1) P F π d σ pstar pstar j βP ηP c B ∧
       Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) (m+1)
         (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) βP ((ordinaryLocalCountCoeff m βP/2)^(m+2))
         c (4*B/(pstar^(m+1)*(pstar*pstar)^m)) ηP) ∧
       RawOrdinaryRows P π d (m+7) Finset.univ pR s j (row*Fintype.card V) σ ∧
       (∀ T:Finset V,T.card≤m+7→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
         βP*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ)))
end Oberwolfach
