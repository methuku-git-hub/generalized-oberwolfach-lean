module

public import Oberwolfach.OrdinaryMixedGenericDeletionStability
public import Oberwolfach.OrdinaryShiftedDeletedStateMonotone
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
variable {n:ℕ} {U I:Type} [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]

theorem ordinary_mixed_root_targets_after_deletion
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hm:3≤m)
    (hn:0<n) (hu:Fintype.card U≤n) (f:I→ℕ) (hf:∀i,1≤f i)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (BM:ℝ) (hBM:0≤BM) (hwM:∀W,0≤wM W ∧ wM W≤BM/(n:ℝ)^m)
    (wO:∀i,OrderedOrdinaryWheel (U:=U) π (3*d) (f i+2)→ℝ)
    (BO:I→ℝ) (hBO:∀i,0≤BO i) (hwO:∀i W,0≤wO i W ∧ wO i W≤BO i/(n:ℝ)^(f i+1))
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (δ:ℝ) (hD:∀x,(D.degree x:ℝ)≤δ)
    (target:Option I→LongRawHubResource n U→ℝ) (τ t:ℝ):
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
    (∀i root,old root=true→
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) root old-target i root|≤t+τ*target i root)→
    ∀i root,new root=true→
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) root new-target i root|≤
        (t+(∑j,C j)*δ/(n:ℝ))+τ*target i root :=by
  intro R w old new C hload i root hactive
  have hδ:0≤δ:=(Nat.cast_nonneg (D.degree ⟨0,hn⟩)).trans (hD ⟨0,hn⟩)
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hCold:∀i,0≤C i:=by
    intro i
    cases i with
    | none=>dsimp [C];positivity
    | some j=>dsimp [C];have hb:=hBO j;positivity
  have hC:(C i)≤∑j,C j:=Finset.single_le_sum (fun j _=>hCold j) (Finset.mem_univ i)
  have hscale:=mul_le_mul_of_nonneg_right hC (div_nonneg hδ hnR.le)
  have hold:old root=true:=ordinary_shifted_deleted_state_mono P π d raw g j D.edgeFinset root hactive
  have hchange:=ordinary_mixed_generic_deletion_stability P D π d m hm hn hu f hf wM BM hBM hwM wO BO hBO hwO raw g j δ hD target i root
  calc
    _ ≤ |resourcePatternLoad (R i) (w i) (fun _ _=>true) root old-target i root|+C i*δ/(n:ℝ):=hchange
    _ ≤ (t+τ*target i root)+(∑j,C j)*δ/(n:ℝ):=by
      apply add_le_add (hload i root hold)
      convert hscale using 1 <;> ring
    _ = _:=by ring
end Oberwolfach
