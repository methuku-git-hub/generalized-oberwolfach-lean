module

public import Oberwolfach.MarkedNextSampleCanonicalRemainder
public import Oberwolfach.MarkedReferenceStateRemainder

@[expose] public section
/-! Full-domain relabelling preserves a valid deletion state, its physical
removed set and its remaining resource set, without resampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_full_domain_valid_state_restriction
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (hfull:Finset.univ.image f=Finset.univ)
    (hfullU:Finset.univ.image g=Finset.univ)
    (P:SimpleGraph V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (I:Finset V) (J:Finset U) (X:Finset W) (Y:Finset Z)
    (hX:∀ x,f x∈I↔x∈X) (hY:∀ u,g u∈J↔u∈Y)
    (γ σloss:ℝ) (D:MarkedReferenceDeletion P π d σ)
    (hvalid:D.Valid H m I J γ σloss):
    ∃ T:MarkedReferenceDeletion (P.comap f) ρ d (rawMarkedRestrictPair f g σ),
      T.Valid (fun b x u=>H b (f x) (g u)) m X Y γ σloss ∧
      T.removed.image (markedResourceEmbedding f.toEmbedding g)=D.removed ∧
      (T.remaining (fun b x u=>H b (f x) (g u))).image (markedResourceEmbedding f.toEmbedding g)=D.remaining H:=by
  let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
  let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
  let S:Finset (V×U):=Finset.univ.filter (fun z=>H false z.1 z.2∨H true z.1 z.2)
  let B:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ S
  let A:Finset (E⊕K):=Finset.univ\D.arcs
  let SR:Finset (V×U):=S\D.spokes
  have hfilter:B.filter (markedInnerResource Finset.univ Finset.univ)=B:=by
    ext z
    cases z with
    | inl e=>simp [markedInnerResource]
    | inr z=>simp [markedInnerResource]
  have hF:D.removed⊆B.filter (markedInnerResource Finset.univ Finset.univ):=by
    rw [hfilter]
    exact D.removed_subset H m I J γ σloss hvalid
  have hDiv:MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) A SR m:=
    D.original_remainder_divisible H m I J γ σloss hvalid
  have hRes:markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π A SR=B.filter (markedInnerResource Finset.univ Finset.univ)\D.removed:=by
    rw [hfilter]
    exact (D.remaining_eq H).symm
  have hh:=marked_next_sample_canonical_remainder f g π ρ hf P d m σ H
    Finset.univ I Finset.univ J (by simp) hfull hfullU X Y hX hY
    D.removed γ σloss hF hvalid.2.1 hvalid.2.2.1 hvalid.2.2.2.1 A SR
    (by intro a ha;simp) (by intro z hz;simp) hDiv hRes
  obtain ⟨F₀,hF₀,FA,FS,hFS,hsets,himage,hremain,hempty,hbound,hstar,hdivnext⟩:=hh
  let T:MarkedReferenceDeletion (P.comap f) ρ d (rawMarkedRestrictPair f g σ):=⟨FA,FS⟩
  refine ⟨T,?_,?_,?_⟩
  · change _ ∧ _ ∧ _ ∧ _ ∧ _
    change markedFiniteResources _ _ _ _ ρ FA FS=F₀ at hsets
    change T.removed=F₀ at hsets
    rw [hsets]
    exact ⟨hFS,hempty,hbound,hstar,hdivnext⟩
  · change T.removed.image _=D.removed
    change markedFiniteResources _ _ _ _ ρ FA FS=F₀ at hsets
    change T.removed=F₀ at hsets
    rw [hsets]
    exact himage
  · change (T.remaining _).image _=D.remaining H
    change markedFiniteResources _ _ _ _ ρ FA FS=F₀ at hsets
    change T.removed=F₀ at hsets
    change (_\T.removed).image _=D.remaining H
    rw [hsets]
    rw [hfilter] at hremain
    exact hremain
end Oberwolfach
