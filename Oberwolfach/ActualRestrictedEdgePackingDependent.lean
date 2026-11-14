module

public import Oberwolfach.ActualRestrictedEdgeCover
public import Oberwolfach.RestrictedPhysicalPacking

@[expose] public section
/-! Pairwise packing of complement-factor edges from the actual old and new
edge images, excluding the final path edges from the old family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_restricted_edge_images_packed_dependent
    {U V:Type} {K J:U→Type} [DecidableEq V] [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    {X:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (F:∀w,SimpleGraph (X w)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (a:∀w,ActualResidualData (K:=K w) (J:=J w) (F w))
    (hCycle:∀w,(a w).t.biUnion (fun j=>((a w).C j).support.toFinset)⊆(a w).Cembed)
    (D:∀w,Finset (X w)) (finalEdges:∀w,Finset (Sym2 (X w)))
    (fC:∀w,{x // x∉D w}↪V) (ψ:∀w,X w→V) (Φ:∀w,{x // x∈(a w).remaining}→V)
    (hold:∀w (x:{x // x∉D w}),x.val∈(a w).oldDomain→fC w x=ψ w x.val)
    (hnew:∀w (x:{x // x∉D w}) (hx:x.val∈(a w).remaining),fC w x=Φ w ⟨x.val,hx⟩)
    (Pack:Finset (Sym2 V)):
    let old:=fun w=>((a w).deletedEdges\finalEdges w).image (Sym2.map (ψ w))
    let new:=fun w=>(((a w).graph.induce (↑(a w).remaining:Set (X w))).edgeFinset).image (Sym2.map (Φ w))
    let remaining:=fun w=>(((F w).deleteEdges (↑(finalEdges w):Set (Sym2 (X w)))).induce {x | x∉D w}).edgeFinset.image (Sym2.map (fC w))
    (∀w z,w≠z→Disjoint (old w) (old z))→(∀w,old w⊆Pack)→
    (∀w z,w≠z→Disjoint (new w) (new z))→(∀w,Disjoint (new w) Pack)→
    ∀w z,w≠z→Disjoint (remaining w) (remaining z):=by
  intro old new remaining holdPair holdPack hnewPair hnewPack
  apply restricted_physical_packing_from_old_and_new remaining old new Pack ?_ holdPair holdPack hnewPair hnewPack
  intro w
  exact actual_restricted_edge_image_cover (F w) (hF w) (a w) (hCycle w) (D w) (finalEdges w)
    (fC w) (ψ w) (Φ w) (hold w) (hnew w)
end Oberwolfach
