module

public import Oberwolfach.OrderedOrdinaryNearFarRimPairs
public import Oberwolfach.OrderedOrdinaryNearFarSpokeRim
public import Oberwolfach.ResourceOmittedPairEmbedding
public import Oberwolfach.MarkedOrdinaryResourceLoads
public import Oberwolfach.LongRawHubContext

@[expose] public section
/-! Transfer ordinary near/far estimates into the mixed typed resource
universe without identifying or changing any resource type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longEmbeddedNearFarFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] {m b:ℕ} {π:Equiv.Perm (Fin n)}

theorem long_embedded_ordinary_rim_pair_near_far
    (hm:2≤m) (hn:0<n) (hu:Fintype.card U≤n)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(n:ℝ)^m) (x y a c:Fin n):
    resourceOmittedPairWeight (fun W=>(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding)
      w (ordinaryMarkedResourceEmbedding (Sum.inl (x,y))) (ordinaryMarkedResourceEmbedding (Sum.inl (a,c)))≤
      if a∈({x,y}:Finset (Fin n)) ∨ c∈({x,y}:Finset (Fin n)) then
        ((m:ℝ)+1)^4*B/(n:ℝ)
      else ((m:ℝ)+1)^4*B/(n:ℝ)^2 :=by
  rw [resource_omitted_pair_weight_map]
  simpa only [Fintype.card_fin] using ordered_ordinary_rim_pair_near_far hm (by simpa using hn)
    (by simpa using hu) w B hB (by simpa only [Fintype.card_fin] using hw) x y a c

theorem long_embedded_ordinary_spoke_rim_near_far
    (hm:2≤m) (hn:0<n)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(n:ℝ)^m) (v a c:Fin n) (u:U):
    resourceOmittedPairWeight (fun W=>(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding)
      w (ordinaryMarkedResourceEmbedding (Sum.inr (v,u))) (ordinaryMarkedResourceEmbedding (Sum.inl (a,c)))≤
      if a=v ∨ c=v then ((m:ℝ)+1)^3*B/(n:ℝ)
      else ((m:ℝ)+1)^3*B/(n:ℝ)^2 :=by
  rw [resource_omitted_pair_weight_map]
  simpa only [Fintype.card_fin] using ordered_ordinary_spoke_rim_pair_near_far hm (by simpa using hn)
    w B hB (by simpa only [Fintype.card_fin] using hw) v a c u
theorem long_embedded_ordinary_pair_marked_rim_zero
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ)
    (root:LongRawHubResource n U) (a c:Fin n):
    resourceOmittedPairWeight (fun W=>(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding)
      w root (Sum.inl (Sum.inr (a,c)))=0 :=by
  apply resource_omitted_pair_weight_map_outside_right
  intro q
  cases q with
  | inl e => simp [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding]
  | inr e => simp [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding]

theorem long_embedded_ordinary_pair_nonordinary_root_zero
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ)
    (root:LongRawHubResource n U)
    (hroot:∀a,ordinaryMarkedResourceEmbedding a≠root) (other:LongRawHubResource n U):
    resourceOmittedPairWeight (fun W=>(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding)
      w root other=0 :=by
  exact resource_omitted_pair_weight_map_outside _ _ ordinaryMarkedResourceEmbedding root other hroot
end Oberwolfach
