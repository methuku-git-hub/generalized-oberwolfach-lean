module

public import Oberwolfach.MarkedVortexInnerBalanceScale
public import Oberwolfach.MarkedVortexInitialExtendedEquivs

@[expose] public section
/-! Select three error scales in order and compare the corrected first-level
balance with the size of the actual first protected vortex domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_first_balance_error_choices
    (r:ℕ) (ε η cap₁ cap₂ capRob:ℝ) (hε:0<ε) (hη:0<η)
    (hc₁:0<cap₁) (hc₂:0<cap₂) (hcRob:0<capRob):
    ∃ εBal ζBal ζCor:ℝ,0<εBal ∧ 0<ζBal ∧ 0<ζCor ∧
      εBal≤cap₁ ∧ ζBal≤cap₂ ∧ ζCor≤capRob ∧
      εBal+((r+4)+2:ℕ)*ζBal+((r+4)+2:ℕ)*(4*ζCor)≤η*ε/2 := by
  let c:ℝ:=((r+4)+2:ℕ)
  have hc:0<c:=by dsimp [c];positivity
  let e:=min cap₁ (η*ε/8)
  let z:=min cap₂ (η*ε/(8*c))
  let q:=min capRob (η*ε/(32*c))
  have he:0<e:=by dsimp [e];positivity
  have hz:0<z:=by dsimp [z];positivity
  have hq:0<q:=by dsimp [q];positivity
  have he':e≤η*ε/8:=min_le_right _ _
  have hz':z≤η*ε/(8*c):=min_le_right _ _
  have hq':q≤η*ε/(32*c):=min_le_right _ _
  have hz'':c*z≤η*ε/8:=by
    have hh:=mul_le_mul_of_nonneg_left hz' hc.le
    have hf:c*(η*ε/(8*c))=η*ε/8:=by field_simp
    linarith
  have hq'':c*(4*q)≤η*ε/8:=by
    have hh:=mul_le_mul_of_nonneg_left hq' hc.le
    have hf:c*(η*ε/(32*c))=η*ε/32:=by field_simp
    nlinarith
  refine ⟨e,z,q,he,hz,hq,min_le_left _ _,min_le_left _ _,min_le_left _ _,?_⟩
  have hp:0≤η*ε:=mul_nonneg hη.le hε.le
  dsimp [c] at hz'' hq''
  nlinarith

theorem marked_vortex_first_balance_from_ambient
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (π:Equiv.Perm V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (he:0<ε) (hm:0<m) (r d:ℕ) (η εBal ζBal ζCor:ℝ) (hη:0≤η)
    (hsmall:εBal+((r+4)+2:ℕ)*ζBal+((r+4)+2:ℕ)*(4*ζCor)≤η*ε/2)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hbal:MarkedLevelFiniteBalanceBound P π d (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1)
      (((εBal+((r+4)+2:ℕ)*ζBal)*Fintype.card V)+((r+4)+2:ℕ)*(4*(ζCor*Fintype.card V))) σ H):
    MarkedLevelFiniteBalanceBound P π d (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1)
      (η*(Q.extendedVertices 1).card) σ H := by
  have hsize:(ε/2)*(Fintype.card V:ℝ)≤(Q.extendedVertices 1).card:=by
    rw [Q.extendedVertices_eq (by have hh:=Q.length_pos;omega)]
    have hh:=(Q.consecutive_size_bounds he hm Q.length_pos).1
    rw [Q.initial] at hh
    simp only [Finset.card_univ] at hh
    nlinarith
  have hn:(0:ℝ)≤Fintype.card V:=by positivity
  have hb:=mul_le_mul_of_nonneg_right hsmall hn
  have hs:=mul_le_mul_of_nonneg_left hsize hη
  intro z j
  have hh:=hbal z j
  nlinarith
end Oberwolfach
