module

public import Oberwolfach.MarkedPackingEmbeddingInnerDegrees

@[expose] public section

/-! The active packing's inner degree bounds hold at every ambient root
after lifting. Roots outside the embedding image have zero incidence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K':Type}
  [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V'} {ktail' khead':K'→V'}
  {m b m' b':ℕ} {π:Equiv.Perm V} {π':Equiv.Perm V'}
  {H₀ HK:V→U→Prop} {H₀' HK':V'→U'→Prop}

theorem markedPackingResources_embedding_inner_bounds
    (f:V↪V') (g:U↪U')
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (N:Finset (MarkedWheel tail' head' ktail' khead' m' π' b' H₀' HK'))
    (he:N.biUnion markedWheelPhysicalResources=(M.biUnion markedWheelPhysicalResources).image (markedResourceEmbedding f g))
    (X:Finset V) (Z:Finset U) (I:Finset V') (J:Finset U')
    (hX:∀ x,f x∈I↔x∈X) (hZ:∀ u,g u∈J↔u∈Z)
    (c:ℝ) (hc:0≤c)
    (hR:∀ v,((spanningRestriction (markedPackingRimGraph M) X).degree v:ℝ)≤c)
    (hV:∀ v∈X,((Z.filter (markedPackingSpokes M v)).card:ℝ)≤c)
    (hU:∀ u∈Z,((X.filter (fun x=>markedPackingSpokes M x u)).card:ℝ)≤c):
    (∀ v,((spanningRestriction (markedPackingRimGraph N) I).degree v:ℝ)≤c)∧
    (∀ v∈I,((J.filter (markedPackingSpokes N v)).card:ℝ)≤c)∧
    (∀ u∈J,((I.filter (fun x=>markedPackingSpokes N x u)).card:ℝ)≤c):=by
  obtain ⟨hgraph,hspoke⟩:=markedPackingResources_embedding_graphs f g M N he
  obtain ⟨hdeg,hrow,hcol⟩:=markedPackingResources_embedding_inner_degrees f g M N he X Z I J hX hZ
  refine ⟨?_,?_,?_⟩
  · intro v
    by_cases hv:∃ x,f x=v
    · obtain ⟨x,rfl⟩:=hv
      rw [hdeg]
      exact hR x
    · have hn:(spanningRestriction (markedPackingRimGraph N) I).neighborFinset v=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have ha:=((spanningRestriction (markedPackingRimGraph N) I).mem_neighborFinset v y).mp hy
        have hg:=(spanningRestriction_adj _ I v y).mp ha
        rw [hgraph,SimpleGraph.map_adj] at hg
        obtain ⟨x,z,hxz,hx,hz⟩:=hg.1
        exact hv ⟨x,hx⟩
      rw [←SimpleGraph.card_neighborFinset_eq_degree,hn,Finset.card_empty,Nat.cast_zero]
      exact hc
  · intro v hvI
    by_cases hv:∃ x,f x=v
    · obtain ⟨x,rfl⟩:=hv
      rw [hrow]
      exact hV x ((hX x).mp hvI)
    · have hn:J.filter (markedPackingSpokes N v)=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        obtain ⟨x,z,hx,hz,hM⟩:=(hspoke v u).mp (Finset.mem_filter.mp hu).2
        exact hv ⟨x,hx⟩
      rw [hn,Finset.card_empty,Nat.cast_zero]
      exact hc
  · intro u huJ
    by_cases hu:∃ z,g z=u
    · obtain ⟨z,rfl⟩:=hu
      rw [hcol]
      exact hU z ((hZ z).mp huJ)
    · have hn:I.filter (fun x=>markedPackingSpokes N x u)=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨v,z,hv,hz,hM⟩:=(hspoke x u).mp (Finset.mem_filter.mp hx).2
        exact hu ⟨z,hz⟩
      rw [hn,Finset.card_empty,Nat.cast_zero]
      exact hc

end Oberwolfach
