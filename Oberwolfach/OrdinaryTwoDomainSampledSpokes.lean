module

public import Oberwolfach.OrdinaryTwoDomainSpokeGraph
public import Oberwolfach.OrdinaryRawPairRestrictionGeometry

@[expose] public section
/-! The auxiliary sampled bipartite graph is precisely the physical graph
of the original sample's spokes on the chosen hub domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_two_domain_sampled_spokes (B:Finset U) (π:Equiv.Perm V) (σ:Equiv.Perm (V⊕U))
    (hcomm:∀v,Sum.inl (π v)=σ (Sum.inl v)) (d:ℕ)
    (sample:RawWheelOutcome (V⊕U) (V⊕U) Γ Color) (j:Color):
    let e:V↪V⊕U:=⟨Sum.inl,Sum.inl_injective⟩
    let f:U↪V⊕U:=⟨Sum.inr,Sum.inr_injective⟩
    let H:=fun v u=>u∈B∧rawWheelSpokes π d (ordinaryRawRestrictPair e f sample) j v u;
    bipartiteRelationGraph (ordinarySumRimSet (V:=V) (U:=U)) (ordinarySumHubSet (V:=V) B)
      (ordinary_sum_domains_disjoint B) (rawWheelSpokes σ d sample j)=ordinaryPhysicalSpokeGraph H:=by
  intro e f H
  letI:LinearOrder (V⊕U):=LinearOrder.lift' (Fintype.equivFin (V⊕U)) (Fintype.equivFin (V⊕U)).injective
  rw [ordinary_sum_bipartite_graph]
  congr 1
  funext v u
  apply propext
  have hh:=ordinaryRawRestrictPair_spoke e e.injective f σ π hcomm d sample j v u
  have hh':rawWheelSpokes σ d sample j (Sum.inl v) (Sum.inr u) ↔
      rawWheelSpokes π d (ordinaryRawRestrictPair e f sample) j v u:=by
    convert hh.symm using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  exact and_congr Iff.rfl hh' 
end Oberwolfach
