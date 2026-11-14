module

public import Oberwolfach.OrdinaryRawPairRestrictionGeometry
public import Oberwolfach.OrdinaryTwoDomainConflict
public import Oberwolfach.OrdinaryEmbeddedHostRecovery

@[expose] public section
/-! Restrict the augmented sampled rim graph to the original vertices and
recover its physical image exactly, including the forbidden graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_two_domain_sampled_rims
    (P F:SimpleGraph V) (π:Equiv.Perm V) (σ:Equiv.Perm (V⊕U)) (b D:ℕ)
    (hcomm:∀v,Sum.inl (π v)=σ (Sum.inl v))
    (hF:permutationConflictGraph π b≤F) (hD:∀v,F.degree v≤D)
    (sample:RawWheelOutcome (V⊕U) (V⊕U) Γ Color):
    let e:V↪V⊕U:=⟨Sum.inl,Sum.inl_injective⟩
    let f:U↪V⊕U:=⟨Sum.inr,Sum.inr_injective⟩
    let R:=rawWheelGraph P (ordinaryRawRestrictPair e f sample)\F
    let Rbig:=rawWheelGraph (P.map e) sample\ordinaryTwoDomainConflict F σ b;
    Rbig.comap e=R ∧ R.map e=Rbig:=by
  intro e f R Rbig
  letI:LinearOrder (V⊕U):=LinearOrder.lift' (Fintype.equivFin (V⊕U)) (Fintype.equivFin (V⊕U)).injective
  have hconf: (ordinaryTwoDomainConflict (U:=U) F σ b).comap e=F:=
    (ordinary_two_domain_conflict_properties F π σ b D hcomm hF hD).2.1
  have hp:(P.map e).comap e=P:=by
    ext v w
    exact SimpleGraph.map_adj_apply
  have hcom:Rbig.comap e=R:=by
    ext v w
    change (rawWheelGraph (P.map e) sample).Adj (e v) (e w) ∧
      ¬(ordinaryTwoDomainConflict F σ b).Adj (e v) (e w) ↔
      (rawWheelGraph P (ordinaryRawRestrictPair e f sample)).Adj v w ∧ ¬F.Adj v w
    have hr:=ordinaryRawRestrictPair_rim e f (P.map e) sample v w
    rw [hp] at hr
    have hf:(ordinaryTwoDomainConflict F σ b).Adj (e v) (e w)↔F.Adj v w:=by
      change ((ordinaryTwoDomainConflict F σ b).comap e).Adj v w↔_
      rw [hconf]
    exact and_congr hr.symm (not_congr hf)
  have hsupport:∀a c,Rbig.Adj a c→a∈Set.range e ∧ c∈Set.range e:=by
    intro a c hac
    have hh:(P.map e).Adj a c:=hac.1.1
    obtain ⟨v,w,_,hv,hw⟩:=(SimpleGraph.map_adj e P _ _).mp hh
    exact ⟨⟨v,hv⟩,⟨w,hw⟩⟩
  exact ⟨hcom,by rw [←hcom];exact graph_comap_map_of_supported e Rbig hsupport⟩
end Oberwolfach
