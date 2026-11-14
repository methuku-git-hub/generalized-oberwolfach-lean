module

public import Oberwolfach.OrdinaryTwoDomainSamplingExtension

@[expose] public section
/-! Transfer a high-probability event on the common augmented sample to the
original two-domain law by exact projection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_two_domain_common_event_transfer (d:ℕ) (hd:2≤d)
    (pR pH:ℝ) (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH) (hpH1:pH≤1)
    (q:U→Γ→ℝ) (hq:∀u a,0≤q u a) (hQ:∀u,∑a,q u a≤1/8)
    (s:U→Color→ℝ) (hs:∀u a,0≤s u a)
    (hS:∀u,∑a,s u a≤ intervalUncoveredProbability d (∑a,q u a))
    (j:Color) (hj:∀u,s u j=pH) (bound:ℝ)
    (E:RawWheelOutcome V U Γ Color→Prop)
    (Ebig:RawWheelOutcome (V⊕U) (V⊕U) Γ Color→Prop):
    let Q:=ordinaryTwoDomainStart (V:=V) q
    let S:=ordinaryTwoDomainColour (V:=V) s j pH
    let h:=ordinary_two_domain_sampling_extension d pH hpH hpH1 q hq hQ s hs hS j hj
    let μ:=FiniteLaw.pi (rawWheelLaw (V:=V⊕U) (fun _=>pR) (fun _=>hpR) (fun _=>hpR1)
      d hd Q h.1 h.2.1 S h.2.2.1 h.2.2.2.1);
    bound≤μ.probability Ebig →
    (∀σ,Ebig σ→E (ordinaryRawRestrictPair Sum.inl Sum.inr σ)) →
    bound≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>pR) (fun _=>hpR) (fun _=>hpR1)
      d hd q hq hQ s hs hS)).probability E:=by
  intro Q S h μ hprob himp
  letI:LinearOrder (V⊕U):=LinearOrder.lift' (Fintype.equivFin (V⊕U)) (Fintype.equivFin (V⊕U)).injective
  have hmono:=finiteLaw_probability_mono μ Ebig (fun σ=>E (ordinaryRawRestrictPair Sum.inl Sum.inr σ)) himp
  have hproject:=ordinary_raw_pair_restriction_probability (V:=V⊕U) (W:=V) (U:=V⊕U) (Z:=U)
    Sum.inl Sum.inl_injective Sum.inr Sum.inr_injective pR hpR hpR1 d hd
    Q h.1 h.2.1 S h.2.2.1 h.2.2.2.1 E
  have heq:μ.probability (fun σ=>E (ordinaryRawRestrictPair Sum.inl Sum.inr σ))=
      (FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>pR) (fun _=>hpR) (fun _=>hpR1)
        d hd q hq hQ s hs hS)).probability E:=by
    convert hproject using 1 <;> simp only [μ,Q,S,ordinaryTwoDomainStart,ordinaryTwoDomainColour,Sum.elim_inr] <;> congr! <;> exact Subsingleton.elim _ _
  rw [heq] at hmono
  exact hprob.trans hmono
end Oberwolfach
