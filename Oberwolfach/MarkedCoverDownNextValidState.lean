module

public import Oberwolfach.MarkedCoverDownNextState
public import Oberwolfach.MarkedReferenceDeletionState

@[expose] public section
/-! The exact divisible cover-down remainder gives a valid state on the next
fixed sample, with both removed and remaining physical resources preserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_cover_down_next_valid_state
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
    ∀ (AR : Finset (E⊕K)) (SR : Finset (V×U)),
    SR⊆Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)→
    (∀ a∈AR,Sum.elim (fun a:E=>a.val.1) (fun a:K=>a.val.1) a∈I ∧
      Sum.elim (fun a:E=>a.val.2) (fun a:K=>a.val.2) a∈I)→
    (∀ s∈SR,s.1∈I∧s.2∈J)→
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) AR SR m→
    ∀ γ σloss : ℝ,
    let L := markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π AR SR
    let F := B.filter (markedInnerResource I J)\L;
    F.filter (markedInnerResource T Q)=∅→
    (∀ physical x,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈F)).card:ℝ)≤γ)→
    (∀ physical x,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈F.filter (markedStarResource T Q))).card:ℝ)≤σloss)→
    ∃ Tnext:MarkedReferenceDeletion (P.comap f) ρ d σ₀,
      Tnext.Valid H₀ m X Y γ σloss ∧
      Tnext.removed.image (markedResourceEmbedding f.toEmbedding g)=F ∧
      (Tnext.remaining H₀).image (markedResourceEmbedding f.toEmbedding g)=L:=by
  intro E K σ₀ H₀ E₀ K₀ B S₀ B₀ AR SR hSRsub hAR hSR hdiv γ σloss L F hDeep hInc hStar
  have hcomp:=marked_cover_remainder_fixed_inner_complement
    (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
    π _ I J hI AR SR hSRsub hAR hSR
  have hh:=marked_cover_down_next_state f g π ρ hf P d m σ H I T J Q hI hfi hgj X Y hX hY
    AR SR hSRsub hAR hSR hdiv γ σloss hDeep hInc hStar
  have hreidx:MarkedReindexedRemainder f g (P.comap f) ρ d m σ₀ H₀ X Y F
      (B.filter (markedInnerResource I J)\F) γ σloss:=hh
  obtain ⟨Tnext,hValid,hRemoved,hRemain⟩:=marked_reindexed_remainder_state
    f g (P.comap f) ρ d m σ₀ H₀ X Y F (B.filter (markedInnerResource I J)\F) γ σloss hreidx
  exact ⟨Tnext,hValid,hRemoved,hRemain.trans hcomp.2.2.symm⟩
end Oberwolfach
