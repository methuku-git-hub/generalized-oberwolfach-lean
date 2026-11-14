module

public import Oberwolfach.OrdinaryReferenceCutNormalization
public import Oberwolfach.GoodPlacementEvents
public import Oberwolfach.FiniteProductRegrouping

@[expose] public section
/-! Join any earlier triangle event to the original oriented rim and spoke
cut event, and normalize its cuts on that same sample and orientation coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def OrdinaryTriangleReferenceMatrixCuts (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (j:Color)
    (δ h:ℝ) (raw:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool):Prop:=
  (∀S:Finset V,∀T:Finset U,
    1-2*δ<(S.card:ℝ)/Fintype.card V+(T.card:ℝ)/Fintype.card U→
    2*h*min ((Fintype.card U:ℝ)*S.card) ((Fintype.card V:ℝ)*T.card)≤
      (bipartiteMatrixCut (fun v u=>if rawWheelSpokes π d raw j v u then 1 else 0) S T:ℝ)) ∧
  (∀S T:Finset V,
    1-2*δ<(S.card:ℝ)/Fintype.card V+(T.card:ℝ)/Fintype.card V→
    2*h*min ((Fintype.card V:ℝ)*S.card) ((Fintype.card V:ℝ)*T.card)≤
      (matrixCut (sampledOrientation (rawWheelGraph P raw\F) coins) S T:ℝ))

def OrdinaryTriangleReferenceNormalizedCuts (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (j:Color)
    (δ h:ℝ) (raw:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool):Prop:=
  BipartiteLargeCut (sampledOrientation (rawWheelGraph P raw\F) coins) δ (2*h) ∧
    BipartiteLargeCut (relationMultiplicity (rawWheelSpokes π d raw j)) δ (2*h)

theorem ordinary_triangle_reference_joint_probability
    (μ:FiniteLaw (RawWheelOutcome V U Γ Color)) (ν:FiniteLaw (Sym2 V→Bool))
    (E:RawWheelOutcome V U Γ Color→Prop) (a b:ℝ) (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (j:Color) (δ h:ℝ)
    (hn:0<Fintype.card V) (hu:0<Fintype.card U)
    (hE:1-a≤μ.probability E)
    (hC:1-b≤(μ.prod ν).probability (fun z=>OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2)):
    1-a-b≤(μ.prod ν).probability (fun z=>E z.1 ∧ OrdinaryTriangleReferenceNormalizedCuts P F π d j δ h z.1 z.2):=by
  have hE':1-a≤(μ.prod ν).probability (fun z=>E z.1):=by
    rw [finiteLaw_prod_first_probability]
    exact hE
  have hboth:1-a-b≤(μ.prod ν).probability (fun z=>E z.1 ∧ OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2):=
    (sub_le_sub_right hE' b).trans (finiteLaw_good_intersection (μ.prod ν) _ _ b hC)
  apply hboth.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,?_⟩
  apply ordinary_reference_matrix_cuts_normalized (rawWheelGraph P z.1) F (rawWheelSpokes π d z.1 j)
    z.2 δ (2*h) hn hu
  · intro S T hST
    convert hz.2.1 S T hST using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · exact hz.2.2
end Oberwolfach
