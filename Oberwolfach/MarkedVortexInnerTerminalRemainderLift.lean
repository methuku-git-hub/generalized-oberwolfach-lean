module

public import Oberwolfach.MarkedVortexTerminalStateRepresentation

@[expose] public section
/-! Typed terminal remainders supported in the next vortex pair lift to the
original host, preserving divisibility and every physical resource. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_inner_terminal_remainder_lift
    (i:ℕ) (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d c:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let P:=G.comap (markedVortexVertexEmbedding Q i)
    let ρ:=markedVortexPermutation Q π hπ i
    let σi:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ
    let Hi:=fun b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i)=>H b v.val u.val
    let E:=MarkedSampleArc P ρ (3*d) (fun e=>σi (Sum.inl e)) false
    let K:=MarkedSampleArc P ρ (3*d) (fun e=>σi (Sum.inl e)) true
    let E₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) false
    let K₀:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) true;
    ∀ (A:Finset (E⊕K)) (S:Finset (markedVortexVertexType Q i×markedVortexHubType Q i)),
    (∀ a∈A,Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1) a∈markedVortexInnerVertices Q i ∧
      Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2) a∈markedVortexInnerVertices Q i)→
    (∀ z∈S,z.1∈markedVortexInnerVertices Q i∧z.2∈markedVortexInnerHubs Q i∧(Hi false z.1 z.2∨Hi true z.1 z.2))→
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (Hi true) A S c→
    ∃ (A₀:Finset (E₀⊕K₀)) (S₀:Finset (V×U)),
      (∀ a∈A₀,Sum.elim (fun e:E₀=>e.val.1) (fun e:K₀=>e.val.1) a∈Q.extendedVertices (i+1)∧
        Sum.elim (fun e:E₀=>e.val.2) (fun e:K₀=>e.val.2) a∈Q.extendedVertices (i+1))∧
      (∀ z∈S₀,z.1∈Q.extendedVertices (i+1)∧z.2∈Q.extendedIndices (i+1)∧(H false z.1 z.2∨H true z.1 z.2))∧
      MarkedRemainderDivisible (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) (H true) A₀ S₀ c∧
      (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) ρ A S).image
          (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i))=
      markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) π A₀ S₀ :=by
  intro P ρ σi Hi E K E₀ K₀ A S hA hS hloc
  let f:markedVortexVertexType Q i↪V:=(markedVortexVertexEmbedding Q i).toEmbedding
  let g:markedVortexHubType Q i↪U:=markedVortexHubEmbedding Q i
  let e:E↪E₀:=markedVortexAmbientSampleArcEmbedding Q i π hπ d σ false
  let k:K↪K₀:=markedVortexAmbientSampleArcEmbedding Q i π hπ d σ true
  let am:A→E₀⊕K₀:=fun a=>(e.sumMap k) a.val
  let A₀:=A.image (e.sumMap k)
  let S₀:=S.image (Prod.map f g)
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
  have hres: (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) ρ A S).image (markedResourceEmbedding f g)=
      markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) π A₀ S₀:=
    markedFiniteResources_embedding _ _ _ _ _ _ _ _ f g ρ π
        (marked_vortex_permutation_compatibility Q π hπ i).1 e k
        (fun a=>rfl) (fun a=>rfl) (fun a=>rfl) (fun a=>rfl) A S
  refine ⟨A₀,S₀,?_,?_,hdiv,hres⟩
  · intro aa haa
    obtain ⟨a0,ha0,rfl⟩:=Finset.mem_image.mp haa
    have ha:=hA a0 ha0
    cases a0 with
    | inl v=>exact ⟨(Finset.mem_filter.mp ha.1).2,(Finset.mem_filter.mp ha.2).2⟩
    | inr v=>exact ⟨(Finset.mem_filter.mp ha.1).2,(Finset.mem_filter.mp ha.2).2⟩
  · intro zz hzz
    change zz∈S.image (Prod.map f g) at hzz
    obtain ⟨z0,hz0,rfl⟩:=Finset.mem_image.mp hzz
    have hh:=hS z0 hz0
    exact ⟨(Finset.mem_filter.mp hh.1).2,(Finset.mem_filter.mp hh.2.1).2,hh.2.2⟩
end Oberwolfach
