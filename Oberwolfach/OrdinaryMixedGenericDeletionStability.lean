module

public import Oberwolfach.OrdinaryShiftedMarkedPatternDeletion
public import Oberwolfach.OrdinaryShiftedUnmarkedDeletionStability
public import Oberwolfach.OrdinaryMixedGenericFamily

@[expose] public section
/-! Both fixed seed families retain their root-load estimates after any
later bounded-degree physical rim deletion, on the original sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U I:Type} [Fintype U] [DecidableEq U] [Fintype I]

theorem ordinary_mixed_generic_deletion_stability
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hm:3≤m)
    (hn:0<n) (hu:Fintype.card U≤n) (f:I→ℕ) (hf:∀i,1≤f i)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (BM:ℝ) (hBM:0≤BM) (hwM:∀W,0≤wM W ∧ wM W≤BM/(n:ℝ)^m)
    (wO:∀i,OrderedOrdinaryWheel (U:=U) π (3*d) (f i+2)→ℝ)
    (BO:I→ℝ) (hBO:∀i,0≤BO i) (hwO:∀i W,0≤wO i W ∧ wO i W≤BO i/(n:ℝ)^(f i+1))
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (δ:ℝ) (hD:∀x,(D.degree x:ℝ)≤δ)
    (target:Option I→LongRawHubResource n U→ℝ):
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (f i+2))=>orderedOrdinaryResources W)
    let w:=ordinaryMixedGenericWeight wM wO
    let old:=typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let new:=typedMarkedResourceState (ordinaryShiftedPairRims P π d (rawMarkedDeleteRims raw D.edgeFinset))
      (rawMarkedPairSpokes π d (rawMarkedDeleteRims raw D.edgeFinset) g j)
    let C:Option I→ℝ:=fun i=>match i with
      | none=>22*((m:ℝ)+1)^4*BM
      | some i=>10*((f i:ℝ)+2)^4*BO i;
    ∀i root,|resourcePatternLoad (R i) (w i) (fun _ _=>true) root new-target i root|≤
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) root old-target i root|+C i*δ/(n:ℝ) :=by
  intro R w old new C i root
  have hδ:0≤δ:=(Nat.cast_nonneg (D.degree ⟨0,hn⟩)).trans (hD ⟨0,hn⟩)
  cases i with
  | none=>
    have hh:=ordinary_shifted_marked_pattern_deletion_stability P π d m hm (by simpa using hn) (by simpa using hu)
      wM BM hBM (by simpa using hwM) raw g j D δ hδ hD root
    have hs:rawMarkedPairSpokes π d (rawMarkedDeleteRims raw D.edgeFinset) g j=rawMarkedPairSpokes π d raw g j:=by
      funext a v u
      rfl
    have hRnone:R none=typedMarkedOccurrenceResources:=by
      funext W
      ext z
      simp only [R,ordinaryMixedGenericResources]
    have hwnone:w none=wM:=rfl
    have hnorm:|resourcePatternLoad typedMarkedOccurrenceResources wM (fun _ _=>true) root
        (typedMarkedResourceState (ordinaryShiftedPairRims P π d (rawMarkedDeleteRims raw D.edgeFinset)) (rawMarkedPairSpokes π d raw g j))-
      resourcePatternLoad typedMarkedOccurrenceResources wM (fun _ _=>true) root
        (typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j))|≤C none*δ/(n:ℝ):=by
      convert hh using 1 <;> (try simp only [C,Fintype.card_fin]) <;> (try ring) <;> congr! 5
    have hh':|resourcePatternLoad (R none) (w none) (fun _ _=>true) root new-
        resourcePatternLoad (R none) (w none) (fun _ _=>true) root old|≤C none*δ/(n:ℝ):=by
      rw [hRnone,hwnone]
      change |resourcePatternLoad typedMarkedOccurrenceResources wM (fun _ _=>true) root
        (typedMarkedResourceState (ordinaryShiftedPairRims P π d (rawMarkedDeleteRims raw D.edgeFinset)) (rawMarkedPairSpokes π d (rawMarkedDeleteRims raw D.edgeFinset) g j))-
        resourcePatternLoad typedMarkedOccurrenceResources wM (fun _ _=>true) root
        (typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j))|≤_
      rw [hs]
      exact hnorm
    have ht:=abs_sub_le (resourcePatternLoad (R none) (w none) (fun _ _=>true) root new)
      (resourcePatternLoad (R none) (w none) (fun _ _=>true) root old) (target none root)
    linarith
  | some i=>
    have hh:=ordinary_shifted_unmarked_load_deletion_stability P D π d raw g j (by have hh:=hf i;omega) hn hu
      (wO i) (BO i) (hBO i) (hwO i) root (target (some i) root) δ hD
    have hc:10*δ*(((f i+1:ℕ):ℝ)+1)^4*BO i/(n:ℝ)=C (some i)*δ/(n:ℝ):=by
      dsimp [C]
      push_cast
      ring
    rw [hc] at hh
    have hRsome:R (some i)=fun W=>(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding:=by
      funext W
      ext z
      simp only [R,ordinaryMixedGenericResources]
    have hwsome:w (some i)=wO i:=rfl
    rw [hRsome,hwsome]
    exact hh
end Oberwolfach
