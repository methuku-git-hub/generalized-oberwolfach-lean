module

public import Oberwolfach.TransformerActualEndpoints
public import Oberwolfach.TransformerEndpointRealization
public import Oberwolfach.ShiftedTransformerHubIncidence

@[expose] public section

/-! The endpoint and hub maps used in the actual transformer. Each map
is determined by the selected paths and the incidence bijections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 def transformerRimEndpoint (G Q:SimpleGraph V) (H₀:V→U→Prop)
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (d:Σ v,G.neighborSet v):V:=
  graphPathEndpoint (p (.inl (rimIncidenceEquiv G d).1)) (rimIncidenceEquiv G d).2

 def transformerSpokeEndpoint (G Q:SimpleGraph V) (H₀:V→U→Prop)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (d:Σ v,G.neighborSet v):V:=
  graphPathEndpoint (p (.inr (spokeEndpointEquiv G H₀ b d).1)) (spokeEndpointEquiv G H₀ b d).2

 def transformerAssignedHub (G:SimpleGraph V) (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (h:G.edgeFinset↪U) (d:Σ v,G.neighborSet v):U:=
  h (shiftedIncidenceEquiv G σ d).1

 theorem actual_spoke_endpoint_adjacency (G Q:SimpleGraph V) (H₀:V→U→Prop) (φ:V→V)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (hends:∀ e:{e:V×U // H₀ e.1 e.2},
      Q.Adj e.val.1 (p (.inr e)).1 ∧ Q.Adj (φ e.val.1) (p (.inr e)).1 ∧
      Q.Adj e.val.1 (p (.inr e)).2.1 ∧ Q.Adj (φ e.val.1) (p (.inr e)).2.1):
    ∀ d:Σ v,G.neighborSet v,
      Q.Adj d.1 (transformerSpokeEndpoint G Q H₀ b p d) ∧
      Q.Adj (φ d.1) (transformerSpokeEndpoint G Q H₀ b p d):=by
  intro d
  have he:(spokeEndpointEquiv G H₀ b d).1.val.1=d.1:=rfl
  have hh:=hends (spokeEndpointEquiv G H₀ b d).1
  rw [he] at hh
  unfold transformerSpokeEndpoint graphPathEndpoint
  split_ifs
  · exact ⟨hh.1,hh.2.1⟩
  · exact ⟨hh.2.2.1,hh.2.2.2⟩

 theorem actual_shifted_root_hub_adjacency (G:SimpleGraph V) (H:V→U→Prop) (φ:V→V)
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (h:G.edgeFinset↪U)
    (hroot:∀ e,H e.val.out.1 (h e)∧H (φ e.val.out.1) (h e)∧
      H e.val.out.2 (h e)∧H (φ e.val.out.2) (h e)):
    ∀ d:Σ v,G.neighborSet v,
      H d.1 (transformerAssignedHub G σ h d)∧H (φ d.1) (transformerAssignedHub G σ h d):=by
  intro d
  have hd:=rimIncidenceEquiv_root G (incidenceShiftEquiv G σ d)
  change d.1=if (shiftedIncidenceEquiv G σ d).2=0 then
    (shiftedIncidenceEquiv G σ d).1.val.out.1 else (shiftedIncidenceEquiv G σ d).1.val.out.2 at hd
  have hh:=hroot (shiftedIncidenceEquiv G σ d).1
  change H d.1 (h (shiftedIncidenceEquiv G σ d).1)∧
    H (φ d.1) (h (shiftedIncidenceEquiv G σ d).1)
  rw [hd]
  split_ifs
  · exact ⟨hh.1,hh.2.1⟩
  · exact ⟨hh.2.2.1,hh.2.2.2⟩

 theorem actual_shifted_root_spokes_injective (G:SimpleGraph V) (φ:V→V)
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (h:G.edgeFinset↪U)
    (hφ:∀ v w,G.Adj v w→φ v≠φ w):
    Function.Injective (fun d:Σ v,G.neighborSet v=>(φ d.1,transformerAssignedHub G σ h d)):=by
  have he (d:Σ v,G.neighborSet v):(shiftedIncidenceEquiv G σ d).1=
      ⟨s(d.1,(σ d.1 d.2).val),SimpleGraph.mem_edgeFinset.mpr (σ d.1 d.2).property⟩:=
    Subtype.ext (shiftedIncidenceEquiv_edge G σ d)
  have hh:=shifted_hub_root_injective G h σ φ hφ
  simpa only [transformerAssignedHub,he] using hh

 theorem actual_shifted_endpoints_adjacent (G:SimpleGraph V) (H:V→U→Prop)
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (h:G.edgeFinset↪U)
    (a z:(Σ v,G.neighborSet v)→V)
    (hT:∀ e,∀ v∈transformerHubAttachments G σ a z e,H v (h e)):
    ∀ d,H (a d) (transformerAssignedHub G σ h d)∧H (z d) (transformerAssignedHub G σ h d):=by
  intro d
  have hh:=transformerHubAttachments_contains G σ a z d
  exact ⟨hT _ _ hh.1,hT _ _ hh.2⟩

end Oberwolfach
