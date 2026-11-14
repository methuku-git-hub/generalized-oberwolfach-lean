module

public import Oberwolfach.OrdinaryTriangleReferenceJoint

@[expose] public section
/-! Attach the reference cut event to an arbitrary earlier event, including
matching information, when its raw-sample projection has the original law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color Ω:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_triangle_reference_with_projected_prior
    (μ:FiniteLaw Ω) (μraw:FiniteLaw (RawWheelOutcome V U Γ Color)) (ν:FiniteLaw (Sym2 V→Bool))
    (sample:Ω→RawWheelOutcome V U Γ Color) (hprojection:μ.map sample=μraw)
    (E:Ω→Prop) (a b:ℝ) (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (j:Color) (δ h:ℝ)
    (hn:0<Fintype.card V) (hu:0<Fintype.card U) (hE:1-a≤μ.probability E)
    (hC:1-b≤(μraw.prod ν).probability (fun z=>OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2)):
    1-a-b≤(μ.prod ν).probability (fun z=>E z.1 ∧
      OrdinaryTriangleReferenceNormalizedCuts P F π d j δ h (sample z.1) z.2):=by
  have hE':1-a≤(μ.prod ν).probability (fun z=>E z.1):=by
    rw [finiteLaw_prod_first_probability]
    exact hE
  have hC':1-b≤(μ.prod ν).probability
      (fun z=>OrdinaryTriangleReferenceMatrixCuts P F π d j δ h (sample z.1) z.2):=by
    rw [finiteLaw_prod_map_left_probability μ ν sample, hprojection]
    exact hC
  have hh:1-a-b≤(μ.prod ν).probability (fun z=>E z.1 ∧
      OrdinaryTriangleReferenceMatrixCuts P F π d j δ h (sample z.1) z.2):=
    (sub_le_sub_right hE' b).trans (finiteLaw_good_intersection (μ.prod ν) _ _ b hC')
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,?_⟩
  apply ordinary_reference_matrix_cuts_normalized (rawWheelGraph P (sample z.1)) F
    (rawWheelSpokes π d (sample z.1) j) z.2 δ (2*h) hn hu
  · intro S T hST
    convert hz.2.1 S T hST using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · exact hz.2.2
end Oberwolfach
