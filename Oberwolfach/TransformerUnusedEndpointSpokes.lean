module

public import Oberwolfach.TransformerActualData
public import Oberwolfach.OrdinaryPotentialLoads

@[expose] public section

/-! The hub assigned to a vertex attachment is different from the hub of
its own rim path. Spoke-path endpoints cannot occur on any rim path.
These are the actual non-overlap checks needed at the two reused labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem actual_shifted_hub_ne_own (G:SimpleGraph V)
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (hσ:∀ v w,σ v w≠w) (h:G.edgeFinset↪U)
    (d:Σ v,G.neighborSet v):
    transformerAssignedHub G σ h d≠h (rimIncidenceEquiv G d).1:=by
  have h1:(shiftedIncidenceEquiv G σ d).1=
      ⟨s(d.1,(σ d.1 d.2).val),SimpleGraph.mem_edgeFinset.mpr (σ d.1 d.2).property⟩:=
    Subtype.ext (shiftedIncidenceEquiv_edge G σ d)
  have h2:(rimIncidenceEquiv G d).1=
      ⟨s(d.1,d.2.val),SimpleGraph.mem_edgeFinset.mpr d.2.property⟩:=
    Subtype.ext (rimIncidenceEquiv_edge G d)
  simpa only [transformerAssignedHub,h1,h2] using shifted_hub_avoids_own_path G h σ hσ d.1 d.2

 theorem actual_attachment_spokes_unused (G Q F:SimpleGraph V) (H₀ H:V→U→Prop)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (hσ:∀ v w,σ v w≠w) (h:G.edgeFinset↪U)
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (R:Finset V) (havoid:∀ i,∀ v∈(p i).2.2.support,v∉R)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (r:ℕ) (W:G.edgeFinset→OrdinaryWheel Q F H r)
    (hhub:∀ e,ordinaryWheelHub (W e)=h e)
    (hsupport:∀ e,∀ v∈(ordinaryWheelRim (W e)).support,v∈R∨v∈(p (.inl e)).2.2.support):
    ∀ e d,
      Sum.inr (transformerRimEndpoint G Q H₀ p d,transformerAssignedHub G σ h d)∉ordinaryWheelResources (W e) ∧
      Sum.inr (transformerSpokeEndpoint G Q H₀ b p d,transformerAssignedHub G σ h d)∉ordinaryWheelResources (W e):=by
  intro e d
  have ha:=graphPathEndpoint_mem (p (.inl (rimIncidenceEquiv G d).1)) (rimIncidenceEquiv G d).2
  have hz:=graphPathEndpoint_mem (p (.inr (spokeEndpointEquiv G H₀ b d).1)) (spokeEndpointEquiv G H₀ b d).2
  change transformerRimEndpoint G Q H₀ p d∈_ at ha
  change transformerSpokeEndpoint G Q H₀ b p d∈_ at hz
  constructor
  · intro hmem
    have hs:=(ordinaryWheelResources_spoke (W e) _ _).mp hmem
    rw [hhub] at hs
    have hp:transformerRimEndpoint G Q H₀ p d∈(p (.inl e)).2.2.support:=
      (hsupport e _ hs.2).resolve_left (havoid _ _ ha)
    have he:e=(rimIncidenceEquiv G d).1:=by
      by_contra he
      exact Finset.disjoint_left.mp (hdis (.inl e) (.inl (rimIncidenceEquiv G d).1)
        (fun heq=>he (Sum.inl.inj heq))) (List.mem_toFinset.mpr hp) (List.mem_toFinset.mpr ha)
    exact actual_shifted_hub_ne_own G σ hσ h d (he ▸ hs.1.symm)
  · intro hmem
    have hs:=(ordinaryWheelResources_spoke (W e) _ _).mp hmem
    have hp:transformerSpokeEndpoint G Q H₀ b p d∈(p (.inl e)).2.2.support:=
      (hsupport e _ hs.2).resolve_left (havoid _ _ hz)
    exact Finset.disjoint_left.mp (hdis (.inl e) (.inr (spokeEndpointEquiv G H₀ b d).1)
      Sum.inl_ne_inr) (List.mem_toFinset.mpr hp) (List.mem_toFinset.mpr hz)

end Oberwolfach
