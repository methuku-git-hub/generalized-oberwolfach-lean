module

public import Oberwolfach.EndpointPhysicalParentWeights
public import Oberwolfach.EndpointTypedParentGeometry

@[expose] public section
/-! The physical parent matching weights supply the bounds required by the
separate-domain concentration theorems. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem endpoint_physical_parent_typed_bounds (P F:SimpleGraph V) (A X:Finset V)
    (weight:V→Sym2 (V⊕U)→ℝ) (data:EndpointPhysicalParentWeights P A X weight):
    (∀x∈X,∀v∈A∩P.neighborFinset x,∀w∈A∩P.neighborFinset x,
      0≤weight x s(Sum.inl v,Sum.inl w)∧weight x s(Sum.inl v,Sum.inl w)≤40/A.card) ∧
    (∀x∈X,∀v∈A∩P.neighborFinset x,∀w∈A∩P.neighborFinset x,
      ¬P.Adj v w→weight x s(Sum.inl v,Sum.inl w)=0) ∧
    (∀x∈X,∀e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet,
      0≤weight x (Sym2.map Sum.inl e)∧weight x (Sym2.map Sum.inl e)≤40/A.card):=by
  constructor
  · intro x hx v hv w hw
    have hv':Sum.inl v∈(A.image (Sum.inl:V→V⊕U))∩
        (ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x):=by
      rw [ordinary_endpoint_parent_neighbors]
      exact Finset.mem_image.mpr ⟨v,hv,rfl⟩
    have hw':Sum.inl w∈(A.image (Sum.inl:V→V⊕U))∩
        (ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x):=by
      rw [ordinary_endpoint_parent_neighbors]
      exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
    exact data.bounded x hx _ hv' _ hw'
  constructor
  · intro x hx v hv w hw h
    apply data.zero x hx
    simpa only [ordinaryPhysicalGraph] using h
  · intro x hx e he
    have he':Sym2.map (Sum.inl:V→V⊕U) e∈(endpointEligibleGraph
        (ordinaryPhysicalGraph P (fun _ _=>False)) (ordinaryPhysicalGraph F (fun _ _=>False))
        ((A.image Sum.inl)∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x))
        (Sum.inl x)).edgeSet:=(endpoint_typed_parent_eligible_edge P F A x e).mpr he
    have hh:=data.positive x hx (ordinaryPhysicalGraph F (fun _ _=>False)) _ he'
    exact ⟨(div_nonneg (by norm_num) (Nat.cast_nonneg _)).trans hh.1,hh.2⟩
end Oberwolfach
