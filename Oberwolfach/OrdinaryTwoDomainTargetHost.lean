module

public import Oberwolfach.OrdinaryTwoDomainConflict

@[expose] public section
/-! An original forbidden-free rim host embeds into the auxiliary host
with its enlarged forbidden graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_two_domain_target_host (P F Q:SimpleGraph V)
    (π:Equiv.Perm V) (σ:Equiv.Perm (V⊕U)) (b D:ℕ)
    (hcomm:∀v,Sum.inl (π v)=σ (Sum.inl v))
    (hF:permutationConflictGraph π b≤F) (hD:∀v,F.degree v≤D) (hQ:Q≤P\F):
    Q.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U)≤
      (P.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U))\ordinaryTwoDomainConflict F σ b:=by
  intro a b' he
  let e:V↪V⊕U:=⟨Sum.inl,Sum.inl_injective⟩
  obtain ⟨v,w,hvw,rfl,rfl⟩:=(SimpleGraph.map_adj e Q _ _).mp he
  have hh:=hQ hvw
  refine ⟨SimpleGraph.map_adj_apply.mpr hh.1,?_⟩
  intro hf
  have hconf: (ordinaryTwoDomainConflict (U:=U) F σ b).comap e=F:=
    (ordinary_two_domain_conflict_properties F π σ b D hcomm hF hD).2.1
  have hf':((ordinaryTwoDomainConflict (U:=U) F σ b).comap e).Adj v w:=hf
  rw [hconf] at hf'
  exact hh.2 hf'
end Oberwolfach
