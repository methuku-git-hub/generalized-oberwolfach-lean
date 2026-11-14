module

public import Oberwolfach.MarkedNextSampleReferenceError
public import Oberwolfach.MarkedRestrictedReferenceResources
public import Oberwolfach.MarkedFiniteResourcePreimages
public import Oberwolfach.MarkedRestrictedFiniteRemainder
public import Oberwolfach.MarkedCanonicalRemainderState

@[expose] public section

/-! The actual divisible remainder is the canonical deletion of the next
fixed reference sample. This joins the exact occurrence reindexing with
the two incidence bounds needed by the next cover-down call. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_next_sample_canonical_remainder
    (f : W↪oV) (g : Z↪U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hf : ∀ x,f (ρ x)=π (f x)) (P : SimpleGraph V) (d m : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (I T : Finset V) (J Q : Finset U) (hI : ∀ x,π x∈I↔x∈I)
    (hfi : Finset.univ.image f=I) (hgj : Finset.univ.image g=J)
    (X : Finset W) (Y : Finset Z) (hX : ∀ x,f x∈T↔x∈X) (hY : ∀ u,g u∈Q↔u∈Y) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let σ₀ := rawMarkedRestrictPair f g σ
    let H₀ := fun b x u=>H b (f x) (g u)
    let E₀ := MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σ₀ (Sum.inl e)) false
    let K₀ := MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σ₀ (Sum.inl e)) true
    let B := markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ
      (Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2))
    let S₀ := Finset.univ.filter (fun z:W×Z=>H₀ false z.1 z.2∨H₀ true z.1 z.2)
    let B₀ := markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ Finset.univ S₀;
    ∀ (F : Finset (Finset V⊕(V×U))) (γ σloss : ℝ),F⊆B.filter (markedInnerResource I J)→
    F.filter (markedInnerResource T Q)=∅→
    (∀ physical x,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈F)).card:ℝ)≤γ)→
    (∀ physical x,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈F.filter (markedStarResource T Q))).card:ℝ)≤σloss)→
    ∀ (AR : Finset (E⊕K)) (SR : Finset (V×U)),
    (∀ a∈AR,Sum.elim (fun a:E=>a.val.1) (fun a:K=>a.val.1) a∈I ∧
      Sum.elim (fun a:E=>a.val.2) (fun a:K=>a.val.2) a∈I)→
    (∀ s∈SR,s.1∈I∧s.2∈J)→
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) AR SR m→
    markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π AR SR=B.filter (markedInnerResource I J)\F→
    ∃ F₀⊆B₀,∃ FA : Finset (E₀⊕K₀),∃ FS⊆S₀,
      markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ FA FS=F₀ ∧
      F₀.image (markedResourceEmbedding f.toEmbedding g)=F ∧
      (B₀\F₀).image (markedResourceEmbedding f.toEmbedding g)=B.filter (markedInnerResource I J)\F ∧
      F₀.filter (markedInnerResource X Y)=∅ ∧
      (∀ physical x,(((markedIncidentEdges (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ (H₀ false) (H₀ true) physical x).filter
        (fun e=>markedActivePhysical (fun e:E₀=>e.val.1) (fun e=>e.val.2)
          (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ (H₀ false) (H₀ true) e∈F₀)).card:ℝ)≤γ) ∧
      (∀ physical x,(((markedIncidentEdges (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ (H₀ false) (H₀ true) physical x).filter
        (fun e=>markedActivePhysical (fun e:E₀=>e.val.1) (fun e=>e.val.2)
          (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ (H₀ false) (H₀ true) e∈F₀.filter (markedStarResource X Y))).card:ℝ)≤σloss) ∧
      let σNext := rawMarkedDeleteRims σ₀ (markedSampleArcSetGraph (P.comap f) ρ d σ₀ FA).edgeFinset
      let HNext := markedDeletePhysicalSpokes H₀ (markedFiniteSpokeGraph FS)
      let ENext := MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σNext (Sum.inl e)) false
      let KNext := MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σNext (Sum.inl e)) true;
      MarkedRemainderDivisible (fun e:ENext=>e.val.1) (fun e=>e.val.2)
        (fun e:KNext=>e.val.1) (fun e=>e.val.2) (HNext true) Finset.univ
        (Finset.univ.filter (fun s:W×Z=>HNext false s.1 s.2∨HNext true s.1 s.2)) m := by
  intro E K σ₀ H₀ E₀ K₀ B S₀ B₀ F γ σloss hF hDeep hInc hStar AR SR hAR hSR hdiv hRemainOriginal
  obtain ⟨F₀,hF₀,FA,FS,hFS,hSets,hImage,hRemain,hEmpty,hBound,hStarBound⟩ :=
    marked_next_sample_reference_error f g π ρ hf P d σ H I T J Q hI hfi hgj X Y hX hY
      F γ σloss hF hDeep hInc hStar
  let e := markedRestrictedSampleArcEmbedding f g π ρ hf P d σ false
  let k := markedRestrictedSampleArcEmbedding f g π ρ hf P d σ true
  let AR₀ := Finset.univ.filter (fun a:E₀⊕K₀=>(e.sumMap k) a∈AR)
  let SR₀ := Finset.univ.filter (fun z:W×Z=>Prod.map f g z∈SR)
  obtain ⟨hd,hR,_⟩ := marked_restricted_finite_remainder f g π ρ hf P d m σ (H true) AR SR
    (by intro a ha;simpa only [hfi] using hAR a ha)
    (by intro s hs;simpa only [hfi,hgj] using hSR s hs) hdiv
  have hSmall : markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ AR₀ SR₀=B₀\F₀ := by
    apply Finset.image_injective (markedResourceEmbedding f.toEmbedding g).injective
    exact hR.trans (hRemainOriginal.trans hRemain.symm)
  have hSmall' : markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ AR₀ SR₀=
      B₀\markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ FA FS := by
    rw [hSets]
    exact hSmall
  have hNext := (marked_canonical_remainder_divisibility (P.comap f) ρ d m σ₀ H₀
    FA AR₀ FS SR₀ hd hSmall').2.2
  exact ⟨F₀,hF₀,FA,FS,hFS,hSets,hImage,hRemain,hEmpty,hBound,hStarBound,hNext⟩

end Oberwolfach
