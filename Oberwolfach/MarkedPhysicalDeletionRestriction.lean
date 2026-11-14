module

public import Oberwolfach.MarkedPotentialPhysicalDeletion
public import Oberwolfach.RawMarkedPairRestriction

@[expose] public section

/-! Restriction commutes with the actual later physical deletion. The
original raw states, orientations and fixed domain maps are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem rawMarkedRestrictPair_deleteRims
    (f:W→V) (g:Z→U) (σ:RawMarkedOutcome V U Γ Color) (D:SimpleGraph V):
    rawMarkedRestrictPair f g (rawMarkedDeleteRims σ D.edgeFinset)=
      rawMarkedDeleteRims (rawMarkedRestrictPair f g σ) (D.comap f).edgeFinset:=by
  funext a
  cases a with
  | inl e=>
    induction e using Sym2.inductionOn with
    | _ x y=>
      simp only [rawMarkedRestrictPair,rawMarkedRestrictVertices,rawMarkedRestrictHubs,
        rawMarkedVertexCoordinate,rawMarkedHubCoordinate,rawMarkedVertexState,rawMarkedHubState,
        rawMarkedDeleteRims,Sym2.map_mk,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,
        SimpleGraph.comap_adj]
  | inr z=>
    obtain ⟨u,i⟩:=z
    cases i with
    | inl x=>rfl
    | inr j=>cases j <;> rfl

theorem markedDeletePhysicalSpokes_restrict
    (f:W→V) (g:Z→U) (H:Bool→V→U→Prop) (D:SimpleGraph (V⊕U)):
    (fun b x z=>markedDeletePhysicalSpokes H D b (f x) (g z))=
      markedDeletePhysicalSpokes (fun b x z=>H b (f x) (g z)) (D.comap (Sum.map f g)):=by
  rfl

omit [LinearOrder V] [LinearOrder W] in
theorem graph_comap_degree_into_image [DecidableEq V] [DecidableEq W]
    (D:SimpleGraph V) (f:W↪V) (x:W):
    (D.comap f).degree x=(D.neighborFinset (f x)∩Finset.univ.image f).card:=by
  have he:((D.comap f).neighborFinset x).image f=D.neighborFinset (f x)∩Finset.univ.image f:=by
    ext y
    simp only [Finset.mem_image,Finset.mem_inter,SimpleGraph.mem_neighborFinset,
      SimpleGraph.comap_adj,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨z,hz,rfl⟩;exact ⟨hz,z,rfl⟩
    · rintro ⟨hy,z,rfl⟩;exact ⟨z,hy,rfl⟩
  rw [←he,Finset.card_image_of_injective _ f.injective,SimpleGraph.card_neighborFinset_eq_degree]

end Oberwolfach
