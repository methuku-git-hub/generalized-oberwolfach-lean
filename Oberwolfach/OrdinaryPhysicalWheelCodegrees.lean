module

public import Oberwolfach.OrdinaryMixedPhysicalResourceFiber
public import Oberwolfach.EmbeddedOrdinaryPairBound
public import Oberwolfach.TypedMarkedLoadBounds

@[expose] public section
/-! Uniform physical codegrees for shifted and unshifted wheel families.
The bounds use the same physical rim-edge and spoke-pair universe. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_physical_pair_bound
    (π:Equiv.Perm V) (b m:ℕ) (hm:3≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (B:ℝ) (hB:0≤B) (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (e f:Sym2 V⊕(V×U)) (hef:e≠f):
    (∑W,if e∈(typedMarkedOccurrenceResources W).image (ordinaryMixedPhysicalResource π) ∧
      f∈(typedMarkedOccurrenceResources W).image (ordinaryMixedPhysicalResource π) then w W else 0)≤
      16*((m:ℝ)+1)^4*B/Fintype.card V := by
  have hh:=typedMarkedOmittedPair_uniform_bound hm hn hu w B hB hw
  have hK:0≤((m:ℝ)+1)^4*B/(Fintype.card V:ℝ):=by positivity
  letI : DecidableEq (V×V) := Classical.decEq _
  have hc:=physical_resource_pair_weight_bounded_fibers (ordinaryMixedPhysicalResource π)
    typedMarkedOccurrenceResources w (fun W=>(hw W).1) 4
    (ordinary_mixed_physical_resource_fiber_card π) _ hK hh e f hef
  convert hc using 1 <;> norm_num <;> ring

theorem ordinary_unshifted_physical_pair_bound
    (π:Equiv.Perm V) (b m:ℕ) (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ)
    (B:ℝ) (hB:0≤B) (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (e f:Sym2 V⊕(V×U)) (hef:e≠f):
    (∑W,if e∈((orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding).image (ordinaryMixedPhysicalResource π) ∧
      f∈((orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding).image (ordinaryMixedPhysicalResource π) then w W else 0)≤
      16*((m:ℝ)+1)^3*B/Fintype.card V := by
  have hh:=embedded_ordered_ordinary_pair_bound hm hn hu w B hB hw
  have hK:0≤((m:ℝ)+1)^3*B/(Fintype.card V:ℝ):=by positivity
  have hc:=physical_resource_pair_weight_bounded_fibers (ordinaryMixedPhysicalResource π)
    (fun W=>(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) w (fun W=>(hw W).1) 4
    (ordinary_mixed_physical_resource_fiber_card π) _ hK hh e f hef
  convert hc using 1 <;> norm_num <;> ring
end Oberwolfach
