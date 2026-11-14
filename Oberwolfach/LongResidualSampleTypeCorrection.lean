module

public import Oberwolfach.LongResidualTypeProtectedCorrection
public import Oberwolfach.LongResidualMarkedDeviation
public import Oberwolfach.MarkedExpandedPhysicalLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance residualSampleTypeCorrectionDecEq : DecidableEq V := Classical.decEq V
local instance residualSampleTypeCorrectionArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=reservedCandidateArcDecEq P

theorem long_residual_sample_types_protected_correction
    (G Del Small Bad Loss:SimpleGraph V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Mhost:V→V→ℕ)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) Mhost≤Del)
    (hcover:Small≤longPhysicalStateGraph G ω {2,3}⊔Loss)
    (L:ℝ) (hLoss:∀v,((Del⊔Loss⊔Bad).degree v:ℝ)≤L)
    (p k p₂ k₂ u err:ℝ)
    (hdegrees:∀j v,|((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u j/2*G.degree v|≤err)
    (I:Finset V) (C:Finset (Finset V⊕(V×U))) (b:ℕ) (rho eta errTarget:ℝ)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hraw:∀v,|((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v:ℕ):ℝ)-(b:ℝ)|≤errTarget)
    (hbudget:errTarget+L≤eta*Fintype.card V)
    (hm₀:∀v,rho*Fintype.card V≤markedExpandedPhysicalProbability p k p₂ k₂ u 0/2*G.degree v-err-L-I.card-C.card)
    (hm₁:∀v,rho*Fintype.card V≤markedExpandedPhysicalProbability p k p₂ k₂ u 1/2*G.degree v-err-L-I.card-C.card):
    let P:=longResidualHostArc Mhost Small Bad
    let T₁:=longResidualInitialMarked G (fun e=>ω (Sum.inl e)) Mhost Small Bad
    ∃M:Finset {e:V×V // P e},
      (∀v,directedInCount P M v=b) ∧
      (∀e,e.val.1∈I→(e∈M↔e∈T₁)) ∧
      (∀e,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→(e∈M↔e∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ)≤
        (1+2/rho)*eta*Fintype.card V+(Fintype.card V:ℝ)^(3/5:ℝ)) :=by
  intro P T₁
  let b₀:=fun v=>markedExpandedPhysicalProbability p k p₂ k₂ u 0/2*G.degree v-err
  let b₁:=fun v=>markedExpandedPhysicalProbability p k p₂ k₂ u 1/2*G.degree v-err
  have h₀:∀v,b₀ v≤((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 0 x v:ℕ):ℝ):=by
    intro v;have h:=(abs_le.mp (hdegrees 0 v)).1;dsimp [b₀];linarith only [h]
  have h₁:∀v,b₁ v≤((∑x,sampledColourOrientation G (fun e=>ω (Sum.inl e)) 1 x v:ℕ):ℝ):=by
    intro v;have h:=(abs_le.mp (hdegrees 1 v)).1;dsimp [b₁];linarith only [h]
  have hdev:=long_residual_marked_deviation_from_sample G Del Small Bad Loss ω Mhost hcorrect hcover b errTarget L hraw hLoss
  apply long_residual_types_protected_correction G Del Small Bad Loss ω Mhost hcorrect hcover L hLoss b₀ b₁ h₀ h₁ I C b rho eta hrho heta hetaR
  · intro v;exact (hdev v).trans hbudget
  · exact hm₀
  · exact hm₁
end Oberwolfach
