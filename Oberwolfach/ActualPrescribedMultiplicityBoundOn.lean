module

public import Oberwolfach.ActualPrescribedImageExtendedHubs
public import Oberwolfach.ResidualActualFamilyForPositions

@[expose] public section
/-! The number of old prescribed images using one target vertex is bounded
by the actual sampled extended-interval hub count. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_multiplicity_on_le_extended_hubs
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] {J:U→Type} [∀w,DecidableEq (J w)]
    (π:Equiv.Perm (Fin n)) (d c:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r)
    (F:U→SimpleGraph (Fin n))
    (data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d σ false r Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}) (J:=J w) (F w))
    (ext:∀w,(retainedMarkedIndex π d σ false r Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Fin (c*d+5)↪Fin n)
    (ψ:∀w,Fin n→Fin n) (H:Finset U)
    (hc:∀w,(data w).c=c) (hd:∀w,(data w).d=d)
    (hsupp:∀w i,((data w).P i).support=List.ofFn (ext w i))
    (hmarker:∀w i (j:Fin (d+1)),bufferedMarker c d (ext w i) j∈(data w).prescribed→
      ψ w (bufferedMarker c d (ext w i) j)=(π^j.val) (retainedAndRawIntervalRoot π d σ false true r Jret w i)):
    ∀v,((H.filter (fun w=>v∈
      (residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)≤
      (rawIntervalExtendedAnyHubSet π d σ v ∩ H).card:=by
  intro v
  have hsub:H.filter (fun w=>v∈
      (residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))⊆
      rawIntervalExtendedAnyHubSet π d σ v ∩ H:=by
    intro w hw
    have hwH:w∈H:=(Finset.mem_filter.mp hw).1
    apply Finset.mem_inter.mpr
    refine ⟨?_,hwH⟩
    have hv: v∈(data w).prescribed.image (ψ w):=by
      obtain ⟨x,hx,hv⟩:=Finset.mem_image.mp (Finset.mem_filter.mp hw).2
      apply Finset.mem_image.mpr
      refine ⟨x.1,?_,hv⟩
      simpa [residualSubtypeSet] using hx
    apply actual_prescribed_image_in_extended_hubs π d c σ r Jret w
      (Function.Embedding.refl _) (Function.Embedding.refl _) (data w) (hc w) (hd w) (ext w) (ψ w) (hsupp w) ?_ v hv
    intro i j hj
    cases i with
    | inl i => simpa using hmarker w (Sum.inl i) j hj
    | inr i => simpa using hmarker w (Sum.inr i) j hj
  exact_mod_cast Finset.card_le_card hsub
end Oberwolfach
