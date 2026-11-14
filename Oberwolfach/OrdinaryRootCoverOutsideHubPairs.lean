module

public import Oberwolfach.OrdinaryRootCoverData

@[expose] public section
/-! Outside rim endpoints lose only a bounded number of inner hub
choices to the root cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_outside_hub_pairs (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (a c:V) (ha:a∉X) (hc:c∉X):
    ((Z.filter (fun u=>H a u∧H c u)).card:ℝ)-2*ell≤
      ((Z.filter (fun u=>(H a u∧¬D.spokes a u)∧(H c u∧¬D.spokes c u))).card:ℝ):=by
  let G:=ordinaryPhysicalGraph D.rim D.spokes
  have hrow (v:V) (hv:v∉X):((Z.filter (fun u=>D.spokes v u)).card:ℝ)≤ell:=by
    let Y:=Z.filter (fun u=>D.spokes v u)
    have hsub:Y.image (Sum.inr:U→V⊕U)⊆G.neighborFinset (Sum.inl v):=by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Finset.mem_filter.mp hu).2
    have hcard:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Sum.inr_injective,SimpleGraph.card_neighborFinset_eq_degree] at hcard
    have hcardR:(Y.card:ℝ)≤(G.degree (Sum.inl v):ℝ):=by exact_mod_cast hcard
    exact hcardR.trans (D.outside_degree (Sum.inl v) (by simpa [ordinaryInnerVertices_left] using hv))
  let Da:=Z.filter (fun u=>D.spokes a u)
  let Dc:=Z.filter (fun u=>D.spokes c u)
  let A:=Z.filter (fun u=>H a u∧H c u)
  let B:=Z.filter (fun u=>(H a u∧¬D.spokes a u)∧(H c u∧¬D.spokes c u))
  have hsub:A\B⊆Da∪Dc:=by
    intro u hu
    simp only [A,B,Da,Dc,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_union] at hu ⊢
    tauto
  have hd:(A\B).card≤Da.card+Dc.card:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hp:=Finset.card_sdiff_add_card_inter A B
  have hi:(A∩B).card≤B.card:=Finset.card_le_card Finset.inter_subset_right
  have hn:A.card≤B.card+Da.card+Dc.card:=by omega
  have hnR:(A.card:ℝ)≤(B.card:ℝ)+Da.card+Dc.card:=by exact_mod_cast hn
  have hDa:(Da.card:ℝ)≤ell:=hrow a ha
  have hDc:(Dc.card:ℝ)≤ell:=hrow c hc
  linarith only [hnR,hDa,hDc]
end Oberwolfach
