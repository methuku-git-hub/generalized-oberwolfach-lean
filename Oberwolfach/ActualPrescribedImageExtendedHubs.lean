module

public import Oberwolfach.ActualPrescribedBufferedMarkers
public import Oberwolfach.RawIntervalExtendedHubsUpper
public import Oberwolfach.RetainedAndRawIntervalGeometry

@[expose] public section
/-! A prescribed old image comes from one of the actual extended sampled
intervals at that hub; this is the bridge to multiplicity bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_image_in_extended_hubs
    {n:ℕ} {U A B J:Type} [Fintype U] [DecidableEq U] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [DecidableEq J]
    (π:Equiv.Perm (Fin n)) (d c:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r) (w:U)
    (aIndex:A ↪ retainedMarkedIndex π d σ false r Jret w)
    (bIndex:B↪{a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})
    {F:SimpleGraph (Fin n)} (data:ActualResidualData (K:=A⊕B) (J:=J) F)
    (hc:data.c=c) (hd:data.d=d) (ext:∀i:A⊕B,Fin (c*d+5)↪Fin n) (ψ:Fin n→Fin n)
    (hsupp:∀i,(data.P i).support=List.ofFn (ext i))
    (hmarker:∀i (j:Fin (d+1)),bufferedMarker c d (ext i) j∈data.prescribed→
      ψ (bufferedMarker c d (ext i) j)=(π^j.val)
        (retainedAndRawIntervalRoot π d σ false true r Jret w (Sum.map aIndex bIndex i))):
    ∀v,v∈data.prescribed.image ψ→w∈rawIntervalExtendedAnyHubSet π d σ v:=by
  have hp:data.prescribed⊆Finset.univ.image (fun z:(A⊕B)×Fin (d+1)=>bufferedMarker c d (ext z.1) z.2):=by
    subst c
    subst d
    exact actual_prescribed_subset_buffered_markers data ext (fun i _=>hsupp i)
  intro v hv
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
  obtain ⟨⟨i,j⟩,_,hij⟩:=Finset.mem_image.mp (hp hx)
  subst x
  rw [hmarker i j hx]
  let a:=retainedAndRawIntervalRoot π d σ false true r Jret w (Sum.map aIndex bIndex i)
  have hw:(π^j.val) a∈permutationWindow π 0 d a:=by
    unfold permutationWindow
    apply Finset.mem_image.mpr
    refine ⟨⟨j.val,by omega⟩,Finset.mem_univ _,?_⟩
    rfl
  cases i with
  | inl i =>
    have hstart:rawIntervalColouredStart π d (fun e=>σ (w,e)) a false:=by
      exact (aIndex i).property.1
    apply Finset.mem_union_left
    simpa only [rawIntervalExtendedHubSet,Finset.mem_filter,Finset.mem_univ,true_and] using
      (show ∃b,rawIntervalColouredStart π d (fun e=>σ (w,e)) b false ∧ (π^j.val) a∈permutationWindow π 0 d b from ⟨a,hstart,hw⟩)
  | inr i =>
    have hstart:rawIntervalColouredStart π d (fun e=>σ (w,e)) a true:=by
      exact (bIndex i).property
    apply Finset.mem_union_right
    simpa only [rawIntervalExtendedHubSet,Finset.mem_filter,Finset.mem_univ,true_and] using
      (show ∃b,rawIntervalColouredStart π d (fun e=>σ (w,e)) b true ∧ (π^j.val) a∈permutationWindow π 0 d b from ⟨a,hstart,hw⟩)
end Oberwolfach
