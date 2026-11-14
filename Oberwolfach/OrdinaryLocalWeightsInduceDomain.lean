module

public import Oberwolfach.OrdinaryLocalInducedWeights
public import Oberwolfach.OrdinaryLocalWeightsRestrictHost

@[expose] public section
/-! Transfer a local fractional cycle weighting onto the actual vertex
domain, retaining its pointwise bounds and weighted vertex degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}

theorem ordinary_local_weights_induce_domain
    (Q F:SimpleGraph V) (T:Finset V) (L U η:ℝ)
    (w:LocalOrdinaryCycle Q F T r→ℝ)
    (hbound:∀C,L≤w C ∧ w C≤U)
    (hload:∀v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices w v|≤η):
    ∃w':LocalOrdinaryCycle (Q.induce (T:Set V)) (F.induce (T:Set V)) Finset.univ r→ℝ,
      (∀C,L≤w' C ∧ w' C≤U) ∧
      (∀v,|1-hypergraphWeightedDegree localOrdinaryVertices w' v|≤η):=by
  obtain ⟨wr,hwr,hloads⟩:=ordinary_local_weights_restrict_host Q F T T (Finset.Subset.rfl) w
  let e:=ordinaryLocalInducedEquiv (r:=r) Q F T T (Finset.Subset.rfl)
  let wi:LocalOrdinaryCycle (Q.induce (T:Set V)) (F.induce (T:Set V))
      (ordinaryInducedLocalDomain T T) r→ℝ:=fun C=>wr (e C)
  have hb:∀C,L≤wi C ∧ wi C≤U:=by
    intro C
    rw [show wi C=wr (e C) from rfl,hwr]
    exact hbound _
  have hl:∀v,|1-hypergraphWeightedDegree localOrdinaryVertices wi v|≤η:=by
    intro v
    have heq:=ordinary_local_induced_weighted_degree Q F T T (Finset.Subset.rfl) wi v.val v.property
    have hw:(fun C:LocalOrdinaryCycle (spanningRestriction Q T) F T r=>wi (e.symm C))=wr:=by
      funext C
      simp only [wi,Equiv.apply_symm_apply]
    rw [hw,hloads] at heq
    rw [←heq]
    exact hload v.val v.property
  have hD:ordinaryInducedLocalDomain T T=Finset.univ:=by
    ext v
    simp [ordinaryInducedLocalDomain,v.property]
  have hex:∃w':LocalOrdinaryCycle (Q.induce (T:Set V)) (F.induce (T:Set V))
        (ordinaryInducedLocalDomain T T) r→ℝ,
      (∀C,L≤w' C ∧ w' C≤U) ∧
      (∀v,|1-hypergraphWeightedDegree localOrdinaryVertices w' v|≤η):=⟨wi,hb,hl⟩
  rw [hD] at hex
  exact hex
end Oberwolfach
