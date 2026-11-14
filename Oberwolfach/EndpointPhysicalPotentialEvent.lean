module

public import Oberwolfach.EndpointTypedRawPhysicalBridge
public import Oberwolfach.EndpointTypedParentGeometry
public import Oberwolfach.EndpointTypedPhysicalTargets

@[expose] public section
/-! The two root-omitted estimates in the physical endpoint geometry,
for one fixed family of parent matching weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

structure EndpointPhysicalPotentialEvent (P F:SimpleGraph V) (A:Finset V) (B:Finset U) (X:Finset V)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (weight:V→Sym2 (V⊕U)→ℝ)
    (pR pH t:ℝ) (σ:RawWheelOutcome V U Γ Color):Prop where
  row:∀x∈X,∀v∈common (A.image Sum.inl) {Sum.inl x}
      (fun z=>((ordinaryPhysicalGraph P (fun _ _=>False))\
        (ordinaryPhysicalGraph F (fun _ _=>False))).neighborFinset z),
    |endpointRowPotential (ordinaryPhysicalGraph P (fun _ _=>False))
      (ordinaryPhysicalGraph (rawWheelGraph P σ) (fun _ _=>False))
      (ordinaryPhysicalGraph ⊥ (rawWheelSpokes π d σ j)) (ordinaryPhysicalGraph F (fun _ _=>False))
      (A.image Sum.inl) (B.image Sum.inr) (Sum.inl x) v (weight x) (B.card*pR^2*pH^3)-
      endpointEligibleRowWeight (ordinaryPhysicalGraph F (fun _ _=>False))
        ((A.image Sum.inl)∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x))
        (Sum.inl x) v (fun a b=>weight x s(a,b))|<t
  index:∀x∈X,∀u∈B,
    |endpointIndexPotential (ordinaryPhysicalGraph P (fun _ _=>False))
      (ordinaryPhysicalGraph (rawWheelGraph P σ) (fun _ _=>False))
      (ordinaryPhysicalGraph ⊥ (rawWheelSpokes π d σ j)) (ordinaryPhysicalGraph F (fun _ _=>False))
      (A.image Sum.inl) (Sum.inl x) (Sum.inr u) (weight x) (B.card*pR^2*pH^3)-
      pR/(B.card*pH)*(∑e∈(endpointEligibleGraph (ordinaryPhysicalGraph P (fun _ _=>False))
        (ordinaryPhysicalGraph F (fun _ _=>False))
        ((A.image Sum.inl)∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x))
        (Sum.inl x)).edgeFinset,weight x e)|<t

theorem endpoint_typed_potentials_to_physical (P F:SimpleGraph V) (A:Finset V) (B:Finset U) (X:Finset V)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (weight:V→Sym2 (V⊕U)→ℝ)
    (pR pH t:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (hrow:∀x∈X,∀v∈common A {x} (fun z=>(P\F).neighborFinset z),
      |rawOrdinaryPatternSum P π d
        (fun z:EndpointRowCandidates (endpointEligibleGraph P F (A∩P.neighborFinset x) x) A B v=>
          endpointRowResources x v z.val.2 z.val.1)
        (fun z=>weight x s(Sum.inl v,Sum.inl z.val.2)/(B.card*pR^2*pH^3)) j σ-
        endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun a b=>weight x s(Sum.inl a,Sum.inl b))|<t)
    (hindex:∀x∈X,∀u∈B,
      |rawOrdinaryPatternSum P π d
        (fun e:↥(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset=>endpointIndexResources x u e.val)
        (fun e=>weight x (Sym2.map Sum.inl e.val)/(B.card*pR^2*pH^3)) j σ-
        pR/(B.card*pH)*(∑e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,
          weight x (Sym2.map Sum.inl e))|<t):
    EndpointPhysicalPotentialEvent P F A B X π d j weight pR pH t σ:=by
  constructor
  · intro x hx v hv
    rw [endpoint_typed_parent_row_domain] at hv
    obtain ⟨v₀,hv₀,rfl⟩:=Finset.mem_image.mp hv
    have hh:=hrow x hx v₀ hv₀
    rw [endpoint_typed_raw_physical_row] at hh
    rw [←endpoint_typed_physical_row_target P F A x v₀ (weight x)] at hh
    exact hh
  · intro x hx u hu
    have hh:=hindex x hx u hu
    rw [endpoint_typed_raw_physical_index] at hh
    rw [←endpoint_typed_physical_edge_mass P F A x (weight x)] at hh
    exact hh
end Oberwolfach
