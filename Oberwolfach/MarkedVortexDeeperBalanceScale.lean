module

public import Oberwolfach.MarkedVortexFirstBalanceScale

@[expose] public section
/-! Choose the correction and sampling errors small enough for both the
first inner domain and the two-step deeper domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_inner_deeper_balance_error_choices
    (r:ℕ) (ε η cap₁ cap₂ capRob:ℝ) (hε:0<ε) (hη:0<η)
    (hc₁:0<cap₁) (hc₂:0<cap₂) (hcRob:0<capRob):
    ∃ εBal ζBal ζCor:ℝ,0<εBal ∧ 0<ζBal ∧ 0<ζCor ∧
      εBal≤cap₁ ∧ ζBal≤cap₂ ∧ ζCor≤capRob ∧
      εBal+((r+4)+2:ℕ)*ζBal+((r+4)+2:ℕ)*(4*ζCor)≤η*ε/2 ∧
      εBal+((r+4)+2:ℕ)*ζBal≤η/2 ∧
      ((r+4)+2:ℕ)*(4*ζCor)≤η*ε^2/8 := by
  let c:ℝ:=((r+4)+2:ℕ)
  have hc:0<c:=by dsimp [c];positivity
  let B:=min (η/4) (η*ε/8)
  have hB:0<B:=by dsimp [B];positivity
  let e:=min cap₁ (B/2)
  let z:=min cap₂ (B/(2*c))
  let q:=min capRob (min (η*ε/(16*c)) (η*ε^2/(32*c)))
  have he:0<e:=by dsimp [e];positivity
  have hz:0<z:=by dsimp [z];positivity
  have hq:0<q:=by dsimp [q];positivity
  have he':e≤B/2:=min_le_right _ _
  have hz':z≤B/(2*c):=min_le_right _ _
  have hq₁:q≤η*ε/(16*c):=(min_le_right _ _).trans (min_le_left _ _)
  have hq₂:q≤η*ε^2/(32*c):=(min_le_right _ _).trans (min_le_right _ _)
  have hz'':c*z≤B/2:=by
    have hh:=mul_le_mul_of_nonneg_left hz' hc.le
    have hf:c*(B/(2*c))=B/2:=by field_simp
    linarith
  have hq₁':c*(4*q)≤η*ε/4:=by
    have hh:=mul_le_mul_of_nonneg_left hq₁ hc.le
    have hf:c*(η*ε/(16*c))=η*ε/16:=by field_simp
    nlinarith
  have hq₂':c*(4*q)≤η*ε^2/8:=by
    have hh:=mul_le_mul_of_nonneg_left hq₂ hc.le
    have hf:c*(η*ε^2/(32*c))=η*ε^2/32:=by field_simp
    nlinarith
  have hB₁:B≤η/4:=min_le_left _ _
  have hB₂:B≤η*ε/8:=min_le_right _ _
  refine ⟨e,z,q,he,hz,hq,min_le_left _ _,min_le_left _ _,min_le_left _ _,?_,?_,?_⟩
  · dsimp [c] at hz'' hq₁';nlinarith [mul_nonneg hη.le hε.le]
  · dsimp [c] at hz'';linarith
  · simpa only [c] using hq₂'

theorem marked_vortex_deeper_balance_from_ambient
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (π:Equiv.Perm V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (he:0<ε) (hm:0<m) (hLen:1<Q.length) (r d:ℕ) (η εBal ζBal ζCor:ℝ) (hη:0≤η)
    (hbase:εBal+((r+4)+2:ℕ)*ζBal≤η/2)
    (hcor:((r+4)+2:ℕ)*(4*ζCor)≤η*ε^2/8)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hbal:MarkedLevelFiniteBalanceBound P π d (r+4) (Q.extendedVertices 2) (Q.extendedIndices 2)
      ((εBal+((r+4)+2:ℕ)*ζBal)*(Q.extendedVertices 2).card+((r+4)+2:ℕ)*(4*(ζCor*Fintype.card V))) σ H):
    MarkedLevelFiniteBalanceBound P π d (r+4) (Q.extendedVertices 2) (Q.extendedIndices 2)
      (η*(Q.extendedVertices 2).card) σ H := by
  have hsize:(ε^2/4)*(Fintype.card V:ℝ)≤(Q.extendedVertices 2).card:=by
    rw [Q.extendedVertices_eq (by omega:2≤Q.length)]
    have h0:=(Q.consecutive_size_bounds he hm Q.length_pos).1
    have h1:=(Q.consecutive_size_bounds he hm hLen).1
    rw [Q.initial] at h0
    simp only [Finset.card_univ] at h0
    have hh:=mul_le_mul_of_nonneg_left h0 (show 0≤ε/2 by positivity)
    nlinarith
  have hn:(0:ℝ)≤Fintype.card V:=by positivity
  have hi:(0:ℝ)≤(Q.extendedVertices 2).card:=by positivity
  have hb:=mul_le_mul_of_nonneg_right hbase hi
  have hc:=mul_le_mul_of_nonneg_right hcor hn
  have hs:=mul_le_mul_of_nonneg_left hsize (show 0≤η/2 by positivity)
  intro z j
  have hh:=hbal z j
  nlinarith
end Oberwolfach
