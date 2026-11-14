module

public import Oberwolfach.OrdinaryEmbeddedPackingHosts

@[expose] public section
/-! Pull an actual row cover through the separate rim and hub embeddings.
Every rim, spoke, degree and disjointness condition is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W Z:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
  [DecidableEq V] [DecidableEq U] [DecidableEq W] [DecidableEq Z]

theorem ordinary_embedded_row_cover
    (φ:V↪W) (ψ:U↪Z) (G F:SimpleGraph V) (F':SimpleGraph W) (H:V→U→Prop) (r:ℕ)
    (hF:∀v w,F.Adj v w→F'.Adj (φ v) (φ w))
    (M:Finset (OrdinaryWheel (G.map φ) F' (ordinaryMappedSpokes H φ ψ) r))
    (x:V) (A:Finset V) (K:ℕ) (hcover:OrdinaryRowCover M (φ x) (A.image φ) K):
    OrdinaryRowCover (M.image (ordinaryEmbeddedWheelPullback φ ψ G F F' H r hF)) x A K:=by
  let pull:=ordinaryEmbeddedWheelPullback φ ψ G F F' H r hF
  let P:=M.image pull
  have hrim:(ordinaryWheelRimGraph P).map φ=ordinaryWheelRimGraph M:=
    (ordinary_embedded_packing_hosts φ ψ G F F' H r hF M).1
  have hspoke:ordinaryMappedSpokes (ordinaryPackingSpokes P) φ ψ=ordinaryPackingSpokes M:=
    (ordinary_embedded_packing_hosts φ ψ G F F' H r hF M).2
  change OrdinaryRowCover P x A K
  constructor
  · intro S hS T hT hST
    obtain ⟨S',hS',rfl⟩:=Finset.mem_image.mp hS
    obtain ⟨T',hT',rfl⟩:=Finset.mem_image.mp hT
    have hdis:=hcover.disjoint S' hS' T' hT' (fun he=>hST (congrArg pull he))
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have ha':(ordinaryPairResourceEmbedding φ ψ) a∈ordinaryWheelResources S':=by
      rw [←ordinaryEmbeddedWheelPullback_resources φ ψ G F F' H r hF S']
      exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
    have hb':(ordinaryPairResourceEmbedding φ ψ) a∈ordinaryWheelResources T':=by
      rw [←ordinaryEmbeddedWheelPullback_resources φ ψ G F F' H r hF T']
      exact Finset.mem_image.mpr ⟨a,hb,rfl⟩
    exact Finset.disjoint_left.mp hdis ha' hb'
  · intro S hS a ha
    obtain ⟨T,hT,rfl⟩:=Finset.mem_image.mp hS
    have hh:=ordinaryEmbeddedWheelPullback_rim φ ψ G F F' H r hF T
    have ha':φ a∈(ordinaryWheelRim T).support:=by
      rw [←hh,SimpleGraph.support_map]
      exact ⟨a,ha,rfl⟩
    rcases hcover.support T hT (φ a) ha' with he|he
    · exact Or.inl (φ.injective he)
    · obtain ⟨b,hb,he⟩:=Finset.mem_image.mp he
      exact Or.inr ((φ.injective he) ▸ hb)
  · intro a
    have hh:=hcover.rims (φ a)
    rw [←hrim,SimpleGraph.map_adj_apply,SimpleGraph.map_adj_apply] at hh
    exact hh
  · intro u
    have hh:=hcover.spokes (ψ u)
    rw [←hspoke,ordinaryMappedSpokes_apply,ordinaryMappedSpokes_apply] at hh
    exact hh
  · intro a hax
    have hh:=hcover.rimDegree (φ a) (fun he=>hax (φ.injective he))
    rw [←hrim,SimpleGraph.degree_map_apply] at hh
    convert hh using 1 <;> congr! <;> exact Subsingleton.elim _ _
  · intro a hax
    have hh:=hcover.rowDegree (φ a) (fun he=>hax (φ.injective he))
    rw [←hspoke,ordinaryMappedSpokes_row,Finset.card_image_of_injective _ ψ.injective] at hh
    exact hh
  · intro u
    have hh:=hcover.columnDegree (ψ u)
    rw [←hspoke,ordinaryMappedSpokes_column,Finset.card_image_of_injective _ φ.injective] at hh
    exact hh
end Oberwolfach
