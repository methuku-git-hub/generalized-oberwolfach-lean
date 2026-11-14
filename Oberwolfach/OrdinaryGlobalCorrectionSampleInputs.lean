module

public import Oberwolfach.OrdinaryGlobalBalanceFromSample
public import Oberwolfach.OrdinaryTriangleReferenceJoint
public import Oberwolfach.OrdinaryEditedCutsFromSample

@[expose] public section
/-! The original row and global cut events supply every graph input to
protected sparse correction on the same sample and orientation coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_global_correction_sample_inputs
    (P F:SimpleGraph V) (D:ℕ) (hreg:P.IsRegularOfDegree D)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool)
    (pR pH tR tH L η δ h:ℝ) (s:U→Color→ℝ)
    (hn:0<Fintype.card V) (hu:0<Fintype.card U)
    (htR:0≤tR) (htH:0≤tH) (hL:0≤L)
    (hmean:pR*D=2*pH*Fintype.card U)
    (hrows:RawOrdinaryRows P π d 2 Finset.univ pR s j tR σ)
    (hcols:RawOrdinaryDomainIndices F π d 3 Finset.univ pH j tH σ)
    (hF:∀v,(F.degree v:ℝ)≤L) (hbudget:tR+2*tH+3*L≤η*Fintype.card V)
    (hcuts:OrdinaryTriangleReferenceMatrixCuts P F π d j δ h σ coins):
    let Q:=rawWheelGraph P σ\F;
    let H:=rawWheelSpokes π d σ j;
    let R:=ordinarySampledOrientedRelation Q coins;
    (∀x y,relationMultiplicity R x y+relationMultiplicity R y x=if Q.Adj x y then 1 else 0) ∧
    BipartiteLargeCut (relationMultiplicity R) δ (2*h) ∧
    BipartiteLargeCut (relationMultiplicity H) δ (2*h) ∧
    (∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤η*Fintype.card V):=by
  intro Q H R
  have hc:=ordinary_reference_matrix_cuts_normalized (rawWheelGraph P σ) F (rawWheelSpokes π d σ j)
    coins δ (2*h) hn hu
    (by intro S T hST;convert hcuts.1 S T hST using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro S T hST;convert hcuts.2 S T hST using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  refine ⟨?_,?_,hc.2,?_⟩
  · intro x y
    rw [←ordinary_sampled_orientation_as_relation]
    convert sampledOrientation_physical Q coins x y using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · rw [←ordinary_sampled_orientation_as_relation]
    exact hc.1
  · have hb:=ordinary_global_balance_from_sample P F D hreg π d j σ pR pH tR tH L η s
      htR htH hL hmean hrows hcols hF hbudget
    intro v
    convert hb v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
