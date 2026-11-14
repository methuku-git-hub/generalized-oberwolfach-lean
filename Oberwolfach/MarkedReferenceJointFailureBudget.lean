module

public import Oberwolfach.JointEventPolynomialMargins

@[expose] public section
/-! Collect the explicit failure terms of the marked reference/absorber event
and an additional active-domain event on the same retained outcome. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedReferenceFixedFailure (χ χCommon χBal χNbr χLoad χLocal χConfig χActive:ℝ):ℝ:=
  χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig+2*χActive

theorem marked_reference_joint_failure_identity
    (n Q:ℕ) (Qreal χ χCommon χBal χNbr χLoad χLocal χConfig χActive:ℝ):
    1-χ-2/(n:ℝ)^Q-χCommon-(n:ℝ)^(-Qreal)-χBal-(n:ℝ)^(-Qreal)-
      2*χNbr-2*(n:ℝ)^(-Qreal)-χLoad-(n:ℝ)^(-Qreal)-χLocal-(n:ℝ)^(-Qreal)-
      χConfig-(n:ℝ)^(-Qreal)-2/(n:ℝ)^Q-1/(n:ℝ)^Q-2*χActive-2*(n:ℝ)^(-Qreal)=
    1-markedReferenceFixedFailure χ χCommon χBal χNbr χLoad χLocal χConfig χActive-
      5*(n:ℝ)^(-(Q:ℝ))-9*(n:ℝ)^(-Qreal):=by
  have hp:(n:ℝ)^(-(Q:ℝ))=1/(n:ℝ)^Q:=by
    rw [Real.rpow_neg (Nat.cast_nonneg n),Real.rpow_natCast,one_div]
  rw [hp]
  unfold markedReferenceFixedFailure
  ring

theorem marked_reference_joint_failure_positive_witness
    (Q:ℕ) (hQ:0<Q) (Qreal χ χCommon χBal χNbr χLoad χLocal χConfig χActive:ℝ)
    (hQr:0<Qreal)
    (herr:markedReferenceFixedFailure χ χCommon χBal χNbr χLoad χLocal χConfig χActive<1):
    ∃ N:ℕ,1≤N ∧ ∀ n:ℕ,N≤n→∀ {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (E:Ω→Prop),
      1-χ-2/(n:ℝ)^Q-χCommon-(n:ℝ)^(-Qreal)-χBal-(n:ℝ)^(-Qreal)-
      2*χNbr-2*(n:ℝ)^(-Qreal)-χLoad-(n:ℝ)^(-Qreal)-χLocal-(n:ℝ)^(-Qreal)-
      χConfig-(n:ℝ)^(-Qreal)-2/(n:ℝ)^Q-1/(n:ℝ)^Q-2*χActive-2*(n:ℝ)^(-Qreal)≤μ.probability E→
      ∃ ω,E ω ∧ 0<μ.mass ω:=by
  have hQ':0<(Q:ℝ):=by exact_mod_cast hQ
  obtain ⟨N,hN,hmain⟩:=joint_event_positive_mass_witness
    (markedReferenceFixedFailure χ χCommon χBal χNbr χLoad χLocal χConfig χActive) 5 9 Q Qreal herr hQ' hQr
  refine ⟨N,hN,?_⟩
  intro n hn Ω _ μ E hE
  apply hmain n hn μ E
  rw [←marked_reference_joint_failure_identity n Q Qreal χ χCommon χBal χNbr χLoad χLocal χConfig χActive]
  exact hE
end Oberwolfach
