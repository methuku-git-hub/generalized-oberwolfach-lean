module

public import Oberwolfach.OrdinaryMixedIdealTarget
public import Oberwolfach.LongMixedHubSpokeCounts

@[expose] public section
/-! The ordinary contribution at a fixed hub-spoke root is precisely its
assigned coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I] [LinearOrder V] [DecidableEq U]

theorem ordinary_mixed_hub_root_target
    (m D p:ℝ) (a b:U→ℝ) (η:I→U→ℝ) (i:I) (u:U)
    (root:OrdinaryTypedResource V U) (hroot:root∈ordinaryCommonHubSpokeRoots u):
    ordinaryMixedIdealTarget m D p a b η (some i) root=η i u :=by
  unfold ordinaryCommonHubSpokeRoots ordinaryHubSpokeRoots at hroot
  obtain ⟨s,hs,hse⟩:=Finset.mem_map.mp hroot
  have hh:∃v,s=Sum.inr (v,u):=by
    simpa only [Finset.mem_image,Finset.mem_univ,true_and,eq_comm] using hs
  obtain ⟨v,rfl⟩:=hh
  have he:root=Sum.inr (false,v,u):=by
    simpa [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding] using hse.symm
  rw [he]
  rfl
end Oberwolfach
