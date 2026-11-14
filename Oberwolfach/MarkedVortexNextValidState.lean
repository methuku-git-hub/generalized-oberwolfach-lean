module

public import Oberwolfach.MarkedCoverDownNextValidState
public import Oberwolfach.MarkedVortexRestrictionChain

@[expose] public section
/-! Apply the cover-down's actual remainder and deletion estimates to the
next fixed vortex pair, obtaining a valid state and the exact ambient identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_cover_down_next_valid_state
    (i:ℕ) (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d c:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    letI : DecidableEq (markedVortexVertexType Q i):=fun a b=>Classical.propDecidable (a=b)
    letI : DecidableEq (markedVortexVertexType Q (i+1)):=fun a b=>Classical.propDecidable (a=b)
    let P:=fun j=>G.comap (markedVortexVertexEmbedding Q j)
    let ρ:=fun j=>markedVortexPermutation Q π hπ j
    let σj:=fun j=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q j) (markedVortexHubEmbedding Q j) σ
    let Hj:=fun j b (v:markedVortexVertexType Q j) (u:markedVortexHubType Q j)=>H b v.val u.val
    let E:=MarkedSampleArc (P i) (ρ i) (3*d) (fun e=>σj i (Sum.inl e)) false
    let K:=MarkedSampleArc (P i) (ρ i) (3*d) (fun e=>σj i (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:markedVortexVertexType Q i×markedVortexHubType Q i=>Hj i false z.1 z.2∨Hj i true z.1 z.2)
    let I:=markedVortexInnerVertices Q i
    let J:=markedVortexInnerHubs Q i
    let Tdeep:=markedVortexDeeperVertices Q i
    let Wdeep:=markedVortexDeeperHubs Q i;
    ∀ (AR:Finset (E⊕K)) (SR:Finset (markedVortexVertexType Q i×markedVortexHubType Q i)),
    SR⊆S→
    (∀ a∈AR,Sum.elim (fun a:E=>a.val.1) (fun a:K=>a.val.1) a∈I∧
      Sum.elim (fun a:E=>a.val.2) (fun a:K=>a.val.2) a∈I)→
    (∀ z∈SR,z.1∈I∧z.2∈J)→
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (Hj i true) AR SR c→
    ∀ γ σloss:ℝ,
    let B:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) Finset.univ S
    let L:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) AR SR
    let F:=B.filter (markedInnerResource I J)\L;
    F.filter (markedInnerResource Tdeep Wdeep)=∅→
    (∀ physical x,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) (Hj i false) (Hj i true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) (Hj i false) (Hj i true) e∈F)).card:ℝ)≤γ)→
    (∀ physical x,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) (Hj i false) (Hj i true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (ρ i) (Hj i false) (Hj i true) e∈F.filter (markedStarResource Tdeep Wdeep))).card:ℝ)≤σloss)→
    ∃ Tnext:MarkedReferenceDeletion (P (i+1)) (ρ (i+1)) d (σj (i+1)),
      Tnext.Valid (Hj (i+1)) c (markedVortexInnerVertices Q (i+1))
        (markedVortexInnerHubs Q (i+1)) γ σloss ∧
      (L.image (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i)))=
      (Tnext.remaining (Hj (i+1))).image
        (markedResourceEmbedding (markedVortexVertexEmbedding Q (i+1)).toEmbedding (markedVortexHubEmbedding Q (i+1))):=by
  intro P ρ σj Hj E K S I J Tdeep Wdeep AR SR hSRsub hAR hSR hdiv γ σloss B L F hDeep hInc hStar
  let f:=markedVortexNestedVertex Q i (i+1) (by omega)
  let g:=markedVortexNestedHub Q i (i+1) (by omega)
  have hEq:(fun (a b:markedVortexVertexType Q i)=>Classical.propDecidable (a=b))=
      (fun (a b:markedVortexVertexType Q i)=>Subtype.instDecidableEq a b):=by
    apply Subsingleton.elim
  have himg:=marked_vortex_nested_next_images Q i
  have hdeep:=marked_vortex_nested_next_deeper Q i
  have hI:=(marked_vortex_permutation_compatibility Q π hπ i).2.1
  try rw [←hEq] at himg
  try rw [←hEq] at hdeep
  try rw [←hEq] at hI
  have hh:=marked_cover_down_next_valid_state f g (ρ i) (ρ (i+1))
    (marked_vortex_nested_commutes Q π hπ i (i+1) (by omega)) (P i) d c (σj i) (Hj i)
    I Tdeep J Wdeep hI
    himg.1 himg.2 (markedVortexInnerVertices Q (i+1)) (markedVortexInnerHubs Q (i+1))
    hdeep.1 hdeep.2 AR SR hSRsub hAR hSR hdiv γ σloss hDeep hInc hStar
  rw [←marked_vortex_nested_graph Q i (i+1) (by omega),
    marked_vortex_nested_raw_restriction Q i (i+1) (by omega) σ] at hh
  obtain ⟨Tnext,hValid,hRemoved,hRemain⟩:=hh
  refine ⟨Tnext,hValid,?_⟩
  have hcomp:=congrArg (fun Z=>Z.image
    (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i))) hRemain
  have himage:((Tnext.remaining (Hj (i+1))).image (markedResourceEmbedding f.toEmbedding g)).image
      (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i))=
    (Tnext.remaining (Hj (i+1))).image
      (markedResourceEmbedding (markedVortexVertexEmbedding Q (i+1)).toEmbedding (markedVortexHubEmbedding Q (i+1))):=by
    ext z
    constructor
    · intro hz
      obtain ⟨x,hx,hxz⟩:=Finset.mem_image.mp hz
      obtain ⟨y,hy,hyx⟩:=Finset.mem_image.mp hx
      refine Finset.mem_image.mpr ⟨y,hy,?_⟩
      rw [←marked_vortex_ambient_resource_composition Q i (i+1) (by omega) y,hyx]
      exact hxz
    · intro hz
      obtain ⟨y,hy,hyz⟩:=Finset.mem_image.mp hz
      refine Finset.mem_image.mpr ⟨(markedResourceEmbedding f.toEmbedding g) y,?_,?_⟩
      · exact Finset.mem_image.mpr ⟨y,hy,rfl⟩
      · exact (marked_vortex_ambient_resource_composition Q i (i+1) (by omega) y).trans hyz
  try rw [←hEq] at himage
  exact hcomp.symm.trans himage
end Oberwolfach
