module

public import Oberwolfach.MarkedFullDomainValidStateRestriction
public import Oberwolfach.MarkedVortexRestrictionChain

@[expose] public section
/-! An ambient deletion state restricts to the actual initial vortex level,
with its original physical remainder unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_initial_valid_state
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d c:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (γ σloss:ℝ) (D₀:MarkedReferenceDeletion G π d σ)
    (hvalid:D₀.Valid H c (Q.extendedVertices 1) (Q.extendedIndices 1) γ σloss):
    ∃ T:MarkedReferenceDeletion (G.comap (markedVortexVertexEmbedding Q 0))
      (markedVortexPermutation Q π hπ 0) d
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σ),
      T.Valid (fun b x u=>H b x.val u.val) c (markedVortexInnerVertices Q 0)
        (markedVortexInnerHubs Q 0) γ σloss ∧
      T.removed.image (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding
        (markedVortexHubEmbedding Q 0))=D₀.removed ∧
      (T.remaining (fun b x u=>H b x.val u.val)).image
        (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0))=
      D₀.remaining H:=by
  let f:=markedVortexVertexEmbedding Q 0
  let g:=markedVortexHubEmbedding Q 0
  have hfull:Finset.univ.image f=Finset.univ:=by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
    have hx:x∈Q.extendedVertices 0:=by rw [Q.extendedVertices_eq (Nat.zero_le _),Q.initial];exact Finset.mem_univ x
    exact ⟨⟨x,hx⟩,rfl⟩
  have hfullU:Finset.univ.image g=Finset.univ:=by
    ext u
    simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
    have hu:u∈Q.extendedIndices 0:=by rw [Q.extendedIndices_eq (Nat.zero_le _),Q.indices_initial];exact Finset.mem_univ u
    exact ⟨⟨u,hu⟩,rfl⟩
  have hX:∀ x,f x∈Q.extendedVertices 1↔x∈markedVortexInnerVertices Q 0:=by
    intro x;simp [markedVortexInnerVertices,f,markedVortexVertexEmbedding]
  have hY:∀ u,g u∈Q.extendedIndices 1↔u∈markedVortexInnerHubs Q 0:=by
    intro u;simp [markedVortexInnerHubs,g,markedVortexHubEmbedding]
  exact marked_full_domain_valid_state_restriction f g π (markedVortexPermutation Q π hπ 0)
    (marked_vortex_permutation_compatibility Q π hπ 0).1 hfull hfullU G d c σ H
    (Q.extendedVertices 1) (Q.extendedIndices 1) (markedVortexInnerVertices Q 0)
    (markedVortexInnerHubs Q 0) hX hY γ σloss D₀ hvalid
end Oberwolfach
