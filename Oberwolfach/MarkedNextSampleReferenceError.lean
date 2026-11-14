module

public import Oberwolfach.MarkedReindexedFixedRemainder
public import Oberwolfach.MarkedRestrictedReferenceResources
public import Oberwolfach.MarkedFiniteResourcePreimages

@[expose] public section

/-! The actual next reference sample inherits the cover-down deletion
bounds under its specified row, hub and typed-arc maps. The error is the
newly removed inner resource set, not a sum of errors from earlier levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_next_sample_reference_error
    (f : W↪oV) (g : Z↪U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hf : ∀ x,f (ρ x)=π (f x)) (P : SimpleGraph V) (d : ℕ)
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
          (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ (H₀ false) (H₀ true) e∈F₀.filter (markedStarResource X Y))).card:ℝ)≤σloss) := by
  intro E K σ₀ H₀ E₀ K₀ B S₀ B₀ F γ σloss hF hDeep hInc hStar
  let e := markedRestrictedSampleArcEmbedding f g π ρ hf P d σ false
  let k := markedRestrictedSampleArcEmbedding f g π ρ hf P d σ true
  have hRef : B₀.image (markedResourceEmbedding f.toEmbedding g)=B.filter (markedInnerResource I J) :=
    marked_restricted_reference_resources f g π ρ hf P d σ H I J hI hfi hgj
  have hF' : F⊆B₀.image (markedResourceEmbedding f.toEmbedding g) := hRef.symm ▸ hF
  obtain ⟨F₀,hF₀,hFimage,hRemain,hEmpty,hBound,hStarBound⟩ := marked_reindexed_fixed_remainder
    (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
    (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
    ρ π f.toEmbedding g hf e k (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
    (H₀ false) (H₀ true) (H false) (H true) (fun _ _ h=>h) (fun _ _ h=>h)
    B₀ F hF' X Y T Q hX hY hDeep γ σloss hInc hStar
  let FA := Finset.univ.filter (fun a:E₀⊕K₀=>Sum.inl (markedPhysicalEdge
    (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ a)∈F₀)
  let FS := S₀.filter (fun s=>Sum.inr s∈F₀)
  obtain ⟨_,hFS,hSets⟩ := marked_finite_resource_preimages
    (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
    ρ Finset.univ S₀ F₀ hF₀
  rw [hRef] at hRemain
  exact ⟨F₀,hF₀,FA,FS,hFS,hSets,hFimage,hRemain,hEmpty,hBound,hStarBound⟩

end Oberwolfach
