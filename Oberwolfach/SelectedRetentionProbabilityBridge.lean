module

public import Oberwolfach.ReferenceEventSevenTenths
public import Oberwolfach.RawMarkedRetention

@[expose] public section
/-! The high-probability reference event is an event in the very same
conditional retained law used by the enriched preparation. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_retention_probability_bridge
    (χ χCommon χBal χNbr qreal:ℝ) (Q:ℕ)
    (hbudget:χ+χCommon+χBal+2*χNbr<3/10) (hQ:0<Q) (hqreal:0<qreal):
    ∃ N:ℕ,1≤N ∧ ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],N≤Fintype.card V→
    ∀ (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (g:Γ)
      (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
      (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQsum:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ a,q u a))
      (E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d g→Prop),
    1-χ-2/(Fintype.card V:ℝ)^Q-χCommon-(Fintype.card V:ℝ)^(-qreal)-χBal-
      (Fintype.card V:ℝ)^(-qreal)-2*χNbr-2*(Fintype.card V:ℝ)^(-qreal)≤
        (rawMarkedRetentionLaw π d hd g p k hp hk hphys q hq hQsum s hs hS).probability E→
    (7:ℝ)/10≤
      ((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk hphys d hd q hq hQsum s hs hS)).sigma
        (fun σ=>startRetentionLaw (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g)
          (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g)) (startRetentionMinimum_le _))).probability E:=by
  obtain ⟨N,hN,hbound⟩:=reference_event_seven_tenths χ χCommon χBal χNbr qreal Q hbudget hQ hqreal
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn π d hd g p k hp hk hphys q hq hQsum s hs hS E hE
  exact hbound (Fintype.card V) hn (rawMarkedRetentionLaw π d hd g p k hp hk hphys q hq hQsum s hs hS) E hE
end Oberwolfach
