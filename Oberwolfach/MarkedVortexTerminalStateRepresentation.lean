module

public import Oberwolfach.MarkedVortexRestrictionChain
public import Oberwolfach.MarkedReferenceStateRemainder
public import Oberwolfach.MarkedFiniteVertexEmbedding
public import Oberwolfach.MarkedFiniteRemainderTransfer
public import Oberwolfach.MarkedFiniteResourcesEmbedding

@[expose] public section
/-! The remainder of a valid fixed-vortex deletion state lifts to the
original sample as the same typed arcs and spokes, with exact divisibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_valid_terminal_state_representation
    (i:ℕ) (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d c:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let P:=G.comap (markedVortexVertexEmbedding Q i)
    let ρ:=markedVortexPermutation Q π hπ i
    let σi:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ
    let Hi:=fun b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i)=>H b v.val u.val
    let E₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) false
    let K₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) true;
    ∀ (T:MarkedReferenceDeletion P ρ d σi)
      (X:Finset (markedVortexVertexType Q i)) (Z:Finset (markedVortexHubType Q i)) (γ σloss:ℝ),
    T.Valid Hi c X Z γ σloss→
    ∃ (A₀:Finset (E₀⊕K₀)) (S₀:Finset (V×U)),
      (∀ a∈A₀,Sum.elim (fun e:E₀=>e.val.1) (fun e:K₀=>e.val.1) a∈Q.extendedVertices i∧
        Sum.elim (fun e:E₀=>e.val.2) (fun e:K₀=>e.val.2) a∈Q.extendedVertices i)∧
      (∀ z∈S₀,z.1∈Q.extendedVertices i∧z.2∈Q.extendedIndices i∧(H false z.1 z.2∨H true z.1 z.2))∧
      MarkedRemainderDivisible (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) (H true) A₀ S₀ c∧
      (T.remaining Hi).image (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding
        (markedVortexHubEmbedding Q i))=
      markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) π A₀ S₀:=by
  intro P ρ σi Hi E₀ K₀ T X Z γ σloss hvalid
  let E:=MarkedSampleArc P ρ (3*d) (fun e=>σi (Sum.inl e)) false
  let K:=MarkedSampleArc P ρ (3*d) (fun e=>σi (Sum.inl e)) true
  let A:Finset (E⊕K):=Finset.univ\T.arcs
  let S:Finset (markedVortexVertexType Q i×markedVortexHubType Q i):=
    (Finset.univ.filter (fun z=>Hi false z.1 z.2∨Hi true z.1 z.2))\T.spokes
  let f:markedVortexVertexType Q i↪V:=(markedVortexVertexEmbedding Q i).toEmbedding
  let g:markedVortexHubType Q i↪U:=markedVortexHubEmbedding Q i
  let e:E↪E₀:=markedVortexAmbientSampleArcEmbedding Q i π hπ d σ false
  let k:K↪K₀:=markedVortexAmbientSampleArcEmbedding Q i π hπ d σ true
  let am:A→E₀⊕K₀:=fun a=>(e.sumMap k) a.val
  let A₀:=A.image (e.sumMap k)
  let S₀:=S.image (Prod.map f g)
  have hdec:(fun (a b:markedVortexVertexType Q i)=>Classical.propDecidable (a=b))=
      (fun (a b:markedVortexVertexType Q i)=>Subtype.instDecidableEq a b):=by
    apply Subsingleton.elim
  have hvalid':=hvalid
  try rw [←hdec] at hvalid'
  have hloc':=T.original_remainder_divisible Hi c X Z γ σloss hvalid'
  try rw [hdec] at hloc'
  have hloc:MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (Hi true) A S c:=
    hloc'
  have hvdiv:=marked_finite_remainder_vertex_image_divisible
    (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
    (Hi true) (H true) f g A S c (by intro z hz;rfl) hloc
  have hinj:Function.Injective am:=by intro a b h;exact Subtype.ext ((e.sumMap k).injective h)
  have htail (a:A):Sum.elim (fun e:E₀=>e.val.1) (fun e:K₀=>e.val.1) (am a)=
      Sum.elim (f∘fun e:E=>e.val.1) (f∘fun e:K=>e.val.1) a.val:=by
    rcases a with ⟨a,ha⟩;cases a <;> rfl
  have hhead (a:A):Sum.elim (fun e:E₀=>e.val.2) (fun e:K₀=>e.val.2) (am a)=
      Sum.elim (f∘fun e:E=>e.val.2) (f∘fun e:K=>e.val.2) a.val:=by
    rcases a with ⟨a,ha⟩;cases a <;> rfl
  have htype (a:A):markedArcType (am a)=markedArcType a.val:=by
    rcases a with ⟨a,ha⟩;cases a <;> rfl
  have hAeq:Finset.univ.image am=A₀:=by
    change Finset.univ.image am=A.image (e.sumMap k)
    ext z
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a,rfl⟩;exact ⟨a.val,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩;exact ⟨⟨a,ha⟩,rfl⟩
  have hdiv:=marked_finite_remainder_image_divisible A S₀ am hinj htail hhead htype
    (fun z hz=>Iff.rfl) hvdiv
  rw [hAeq] at hdiv
  have hres:(T.remaining Hi).image (markedResourceEmbedding f g)=
      markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) π A₀ S₀:=by
    have hrem:=T.remaining_eq Hi
    try rw [hdec] at hrem
    change T.remaining Hi=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) ρ A S at hrem
    calc
      _ = (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) ρ A S).image (markedResourceEmbedding f g) :=
          congrArg (fun Z=>Z.image (markedResourceEmbedding f g)) hrem
      _ = _ := markedFiniteResources_embedding _ _ _ _ _ _ _ _ f g ρ π
        (marked_vortex_permutation_compatibility Q π hπ i).1 e k
        (fun a=>rfl) (fun a=>rfl) (fun a=>rfl) (fun a=>rfl) A S
  refine ⟨A₀,S₀,?_,?_,hdiv,hres⟩
  · intro a ha
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp ha
    cases a with
    | inl e=>exact ⟨e.val.1.property,e.val.2.property⟩
    | inr e=>exact ⟨e.val.1.property,e.val.2.property⟩
  · intro z hz
    change z∈S.image (Prod.map f g) at hz
    obtain ⟨z0,hz0,hzeq⟩:=Finset.mem_image.mp hz
    have hh:Hi false z0.1 z0.2∨Hi true z0.1 z0.2:=by
      change z0∈(Finset.univ.filter (fun z=>Hi false z.1 z.2∨Hi true z.1 z.2))\T.spokes at hz0
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz0).1).2
    subst z
    exact ⟨z0.1.property,z0.2.property,hh⟩
end Oberwolfach
