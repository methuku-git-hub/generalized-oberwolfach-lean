module

public import Oberwolfach.MarkedVortexRestrictionChain
public import Oberwolfach.MarkedRestrictedNextStateExact

@[expose] public section
/-! Exact reindexing of a supported remainder to the next actual vortex
level, with both sides embedded in the original physical resource set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_next_state_exact
    (i:ℕ) (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let P:=fun j=>G.comap (markedVortexVertexEmbedding Q j)
    let ρ:=fun j=>markedVortexPermutation Q π hπ j
    let σj:=fun j=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q j) (markedVortexHubEmbedding Q j) σ
    let Hj:=fun j b (v:markedVortexVertexType Q j) (u:markedVortexHubType Q j)=>H b v.val u.val
    let E:=MarkedSampleArc (P i) (ρ i) (3*d) (fun e=>σj i (Sum.inl e)) false
    let K:=MarkedSampleArc (P i) (ρ i) (3*d) (fun e=>σj i (Sum.inl e)) true
    let f:=markedVortexNestedVertex Q i (i+1) (by omega)
    let g:=markedVortexNestedHub Q i (i+1) (by omega);
    ∀ (A:Finset (E⊕K)) (S:Finset (markedVortexVertexType Q i×markedVortexHubType Q i)),
    (∀ a∈A,Sum.elim (fun a:E=>a.val.1) (fun a:K=>a.val.1) a∈Finset.univ.image f∧
      Sum.elim (fun a:E=>a.val.2) (fun a:K=>a.val.2) a∈Finset.univ.image f)→
    (∀ z∈S,z.1∈Finset.univ.image f∧z.2∈Finset.univ.image g∧(Hj i false z.1 z.2∨Hj i true z.1 z.2))→
    ∃ T:MarkedReferenceDeletion (P (i+1)) (ρ (i+1)) d (σj (i+1)),
      (T.remaining (Hj (i+1))).image
        (markedResourceEmbedding (markedVortexVertexEmbedding Q (i+1)).toEmbedding (markedVortexHubEmbedding Q (i+1)))=
      (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        (ρ i) A S).image (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i)):=by
  intro P ρ σj Hj E K f g A S hA hS
  have hdec:(fun (a b:markedVortexVertexType Q i)=>Classical.propDecidable (a=b))=
      (fun (a b:markedVortexVertexType Q i)=>Subtype.instDecidableEq a b):=by
    apply Subsingleton.elim
  have hA':=hA
  have hS':=hS
  try rw [←hdec] at hA'
  try rw [←hdec] at hS'
  have hn:=marked_restricted_next_state_exact f g (ρ i) (ρ (i+1))
    (marked_vortex_nested_commutes Q π hπ i (i+1) (by omega)) (P i) d (σj i) (Hj i) A S hA' hS'
  try rw [hdec] at hn
  rw [←marked_vortex_nested_graph Q i (i+1) (by omega),
    marked_vortex_nested_raw_restriction Q i (i+1) (by omega) σ] at hn
  obtain ⟨T,hT⟩:=hn
  refine ⟨T,?_⟩
  have hcomp:=congrArg (fun L=>L.image
      (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i))) hT
  rw [Finset.image_image] at hcomp
  have hfun:(markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i)) ∘
      (markedResourceEmbedding f.toEmbedding g)=
      markedResourceEmbedding (markedVortexVertexEmbedding Q (i+1)).toEmbedding (markedVortexHubEmbedding Q (i+1)):=by
    funext z
    exact marked_vortex_ambient_resource_composition Q i (i+1) (by omega) z
  rw [hfun] at hcomp
  exact hcomp
end Oberwolfach
