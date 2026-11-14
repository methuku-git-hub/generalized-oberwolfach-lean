module

public import Oberwolfach.OrdinaryPhysicalPairHubRimPacksShape

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option maxRecDepth 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_physical_pair_hub_rim_packs_named {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    ordinaryPhysicalPairHubRimPacksShape (K:=K) π d m R H :=by
  unfold ordinaryPhysicalPairHubRimPacksShape
  intro RM state RR φ L hL AM AU len Q E S u v huv W Z hW hZ
  have hhubW (a:AM u):(W a).2.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).2.val:=
    (hW a).2.trans (ordinary_physical_marked_payload_hub π d m RM state L u a).symm
  have hhubZ (a:AM v):(Z a).2.val=(ordinaryPhysicalMarkedPayload π d m RM state L v a).2.val:=
    (hZ a).2.trans (ordinary_physical_marked_payload_hub π d m RM state L v a).symm
  apply mixed_wheel_rim_packs_disjoint (len u) (len v) (Finset.univ.image W) (Finset.univ.image Z) (Q u) (Q v)
  · intro X hX Y hY
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hX
    obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hY
    have hh:=ordinary_physical_restricted_marked_cross_hubs π d m R H L hL u v huv a b (W a) (Z b)
      (hW a).1 (hhubW a) (hZ b).1 (hhubZ b)
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro X hX b
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hX
    have hh:=ordinary_physical_restricted_mixed_cross_hubs π d m R H L hL u v a b (W a) (hW a).1 (hhubW a)
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro a Y hY
    obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hY
    have hh:=(ordinary_physical_restricted_mixed_cross_hubs π d m R H L hL v u b a (Z b) (hZ b).1 (hhubZ b)).symm
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro a b
    exact ordinary_physical_unmarked_wheels_cross_hubs π d m R H L hL u v huv a b
end Oberwolfach
