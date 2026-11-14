module

public import Oberwolfach.MarkedReferenceTerminalRepresentation
public import Oberwolfach.MarkedAmbientTerminalRepresentation
public import Oberwolfach.MarkedReferenceLevelEmbedding
public import Oberwolfach.MarkedFiniteVertexEmbedding
public import Oberwolfach.MarkedFiniteResourcesEmbedding

@[expose] public section

/-! The terminal remainder lifts from the last reference to the first
reference as actual typed arcs and spokes. Its four balance equations and
its physical resource set are preserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}
variable (levels:ℕ → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
theorem marked_reference_terminal_transfer {count:ℕ} :
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    ∀ (chain:MarkedReferenceLevelChain levels count) (i:ℕ) (hi:i<count)
      (L:Finset (Finset (levels 0).VP⊕((levels 0).VP×(levels 0).UP))),
    MarkedReferenceTerminalRepresentation (levels i) (chain.intoV i).toEmbedding (chain.intoU i) L →
    MarkedAmbientTerminalRepresentation (levels 0) ((levels i).I.image (chain.intoV i))
      ((levels i).J.image (chain.intoU i)) L := by
  intro chain i hi L hL
  letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
  letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
  letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
  letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10
  let Ei:=MarkedSampleArc (levels i).PP (levels i).πP (3*d) (fun e=>(levels i).σBase (Sum.inl e)) false
  let Ki:=MarkedSampleArc (levels i).PP (levels i).πP (3*d) (fun e=>(levels i).σBase (Sum.inl e)) true
  let E₀:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) false
  let K₀:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) true
  let S₀:=Finset.univ.filter (fun z:(levels 0).VP×(levels 0).UP=>
    (levels 0).HBase false z.1 z.2∨(levels 0).HBase true z.1 z.2)
  let X:=(levels i).I.image (chain.intoV i)
  let Y:=(levels i).J.image (chain.intoU i)
  unfold MarkedAmbientTerminalRepresentation
  dsimp only
  unfold MarkedReferenceTerminalRepresentation at hL
  dsimp only at hL
  obtain ⟨AR,SR,hS,hAR,hSR,hdiv,hR⟩:=hL
  let f:=(chain.intoV i).toEmbedding
  let g:=chain.intoU i
  let e:=markedReferenceLevelArcEmbedding levels chain i hi false
  let k:=markedReferenceLevelArcEmbedding levels chain i hi true
  let em:=e.sumMap k
  let sm:=Prod.map f g
  let A:=AR.image em
  let S:=SR.image sm
  have he (a:Ei):(e a).val=(f a.val.1,f a.val.2):=
    markedReferenceLevelArcEmbedding_endpoints levels chain i hi false a
  have hk (a:Ki):(k a).val=(f a.val.1,f a.val.2):=
    markedReferenceLevelArcEmbedding_endpoints levels chain i hi true a
  have hHK (z:(levels i).VP×(levels i).UP):
      (levels 0).HBase true (f z.1) (g z.2)↔(levels i).HBase true z.1 z.2 := by
    rw [chain.ambientSpokes i hi]
    rfl
  have hvdiv:=marked_finite_remainder_vertex_image_divisible
    (fun e:Ei=>e.val.1) (fun e=>e.val.2) (fun e:Ki=>e.val.1) (fun e=>e.val.2)
    ((levels i).HBase true) ((levels 0).HBase true) f g AR SR (r+4) (fun z _=>hHK z) hdiv
  let am:AR → E₀⊕K₀:=fun a=>em a.val
  have ham:Function.Injective am:=by intro a b h;exact Subtype.ext (em.injective h)
  have htail (a:AR):Sum.elim (fun e:E₀=>e.val.1) (fun e:K₀=>e.val.1) (am a)=
      Sum.elim (f∘fun e:Ei=>e.val.1) (f∘fun e:Ki=>e.val.1) a.val:=by
    rcases a with ⟨a,ha⟩
    cases a with
    | inl v=>exact congrArg Prod.fst (he v)
    | inr v=>exact congrArg Prod.fst (hk v)
  have hhead (a:AR):Sum.elim (fun e:E₀=>e.val.2) (fun e:K₀=>e.val.2) (am a)=
      Sum.elim (f∘fun e:Ei=>e.val.2) (f∘fun e:Ki=>e.val.2) a.val:=by
    rcases a with ⟨a,ha⟩
    cases a with
    | inl v=>exact congrArg Prod.snd (he v)
    | inr v=>exact congrArg Prod.snd (hk v)
  have htype (a:AR):markedArcType (am a)=markedArcType a.val:=by
    rcases a with ⟨a,ha⟩
    cases a <;> rfl
  have hAeq:Finset.univ.image am=A:=by
    dsimp only [A]
    ext z
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨a.val,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  have hdiv0:=marked_finite_remainder_image_divisible AR S am ham htail hhead htype
    (fun z _=>Iff.rfl) hvdiv
  rw [hAeq] at hdiv0
  have hR0: L=markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) (levels 0).πP A S := by
    rw [hR]
    exact markedFiniteResources_embedding _ _ _ _ _ _ _ _ f g (levels i).πP (levels 0).πP
      (chain.ambientComm i hi) e k (fun a=>congrArg Prod.fst (he a)) (fun a=>congrArg Prod.snd (he a))
      (fun a=>congrArg Prod.fst (hk a)) (fun a=>congrArg Prod.snd (hk a)) AR SR
  refine ⟨A,S,?_,?_,?_,hdiv0,hR0⟩
  · intro z hz
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
    have hv':=(Finset.mem_filter.mp (hS hv)).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [chain.ambientSpokes i hi] at hv'
    exact hv'
  · intro a ha
    change a∈AR.image em at ha
    obtain ⟨a0,ha0,heq⟩:=Finset.mem_image.mp ha
    subst a
    obtain ⟨ha1,ha2⟩:=hAR a0 ha0
    cases a0 with
    | inl a=>
      constructor
      · exact Finset.mem_image.mpr ⟨a.val.1,ha1,(congrArg Prod.fst (he a)).symm⟩
      · exact Finset.mem_image.mpr ⟨a.val.2,ha2,(congrArg Prod.snd (he a)).symm⟩
    | inr a=>
      constructor
      · exact Finset.mem_image.mpr ⟨a.val.1,ha1,(congrArg Prod.fst (hk a)).symm⟩
      · exact Finset.mem_image.mpr ⟨a.val.2,ha2,(congrArg Prod.snd (hk a)).symm⟩
  · intro z hz
    change z∈SR.image sm at hz
    obtain ⟨z0,hz0,heq⟩:=Finset.mem_image.mp hz
    subst z
    obtain ⟨hz1,hz2⟩:=hSR z0 hz0
    exact ⟨Finset.mem_image.mpr ⟨z0.1,hz1,rfl⟩,Finset.mem_image.mpr ⟨z0.2,hz2,rfl⟩⟩

end Oberwolfach
