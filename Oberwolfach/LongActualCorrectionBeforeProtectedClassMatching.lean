module

public import Oberwolfach.MarkedProtectedCorrectionMatchingDeletion
public import Oberwolfach.LongClassProtectedMatchingAfterCorrection
public import Oberwolfach.LongEarlyMatchingListsForDeletion

@[expose] public section
/-! Choose the bounded correction first. Every subsequently supplied protected
class and orientation that avoid that correction admit the same matching-and-
list continuation after one bounded deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance lateProtectedActualFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)

theorem long_actual_correction_before_protected_class_matching
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r size a₀ b₀ e₀ f₀:ℕ)
    (εAbs ζ ξCorr:ℝ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (T:Finset (Fin n)) (W:Finset U)
    (K:ℕ) (θ D alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ):
    let V:=Fin n
    let ω:=z.1
    let σ:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false
    let Matching:=fun Del:SimpleGraph V=>LongEarlyMatchingListsForDeletion r K d θ D alpha γ eps Δ βList P π F hF weight w z T Del;
    (∀Del:SimpleGraph V,(∀v,(Del.degree v:ℝ)≤Δ*n)→Matching Del)→
    MarkedProtectedAbsorbableCorrectionWithBounds P π d r size a₀ b₀ e₀ f₀ εAbs ζ ξCorr σ H T W →
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∃(DA:Finset (E⊕K)) (DS:Finset (V×U)),DS⊆S ∧
      (∀v,((DA.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤
        8*(((r+4:ℕ):ℝ)+1)*ξCorr*Fintype.card V) ∧
      (∀v,((DS.filter (fun z=>v=z.1)).card:ℝ)≤4*(((r+4:ℕ):ℝ)+1)*ξCorr*Fintype.card V) ∧
      (∀u,((DS.filter (fun z=>u=z.2)).card:ℝ)≤4*(((r+4:ℕ):ℝ)+1)*ξCorr*Fintype.card V) ∧
      (DA.card:ℝ)≤8*(((r+4:ℕ):ℝ)+1)*ξCorr*(Fintype.card V:ℝ)^2 ∧
      (DS.card:ℝ)≤4*(((r+4:ℕ):ℝ)+1)*ξCorr*(Fintype.card V:ℝ)^2 ∧
      (markedFiniteResources tail head ktail khead π DA DS).filter (markedInnerResource T W)=∅ ∧
      (∀v,((markedSampleArcSetGraph P π d σ DA).degree v:ℝ)≤ζ*Fintype.card V) ∧
      (∀z,((markedFiniteSpokeGraph DS).degree z:ℝ)≤ζ*Fintype.card V) ∧
      (∀x∈T,∀y∈T,¬(markedSampleArcSetGraph P π d σ DA).Adj x y) ∧
      (∀x∈T,∀u∈W,¬(markedFiniteSpokeGraph DS).Adj (Sum.inl x) (Sum.inr u)) ∧
      (∀Protected:SimpleGraph V,(∀x y,Protected.Adj x y→x∈T ∧ y∈T)→
        ∀x y,(markedSampleArcSetGraph P π d σ DA).Adj x y→¬Protected.Adj x y) ∧
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ DA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) (r+4) ∧
    MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs ∧
    ∀(S Kbad Protected:SimpleGraph V) (M:V→V→ℕ) (ξ δ:ℝ),
      ζ+ξ+δ≤Δ→S≤P→Kbad≤S→(∀x y,M x y+M y x=if S.Adj x y then 1 else 0)→
      (∀v,((changed ((longPhysicalStateGraph P ω {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
      (∀v,((orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M).degree v:ℝ)≤δ*n)→
      (∀x y,Protected.Adj x y→(S.Adj x y↔(longPhysicalStateGraph P ω {0,1,2,3,4}).Adj x y))→
      (∀x y,(markedSampleArcSetGraph P π d σ DA).Adj x y→¬Protected.Adj x y)→
      (∀x y,(orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M).Adj x y→¬Protected.Adj x y)→
      ∃Del:SimpleGraph V,(markedSampleArcSetGraph P π d σ DA)≤Del ∧
        ((longPhysicalStateGraph P ω {0,1,2,3,4})\S)≤Del ∧
        orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del ∧
        (∀v,(Del.degree v:ℝ)≤Δ*n) ∧ (∀x y,Del.Adj x y→¬Protected.Adj x y) ∧
        (∀x y,rawSelectedPhysicalRelation P π d (fun e=>ω (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
        (∀x y,Kbad.Adj x y→M x y=1 ∨ M y x=1) ∧ (∀x y,M x y=1→P.Adj x y) ∧
        (∀x y,rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (ω e)) x y→¬Del.Adj x y→M x y=1) ∧ Matching Del
 := by
  intro V ω σ H Matching hMatching hCorr
  obtain ⟨DA,DS,hSub,hArc,hRow,hCol,hCardA,hCardS,hEmpty,hDegA,hDegS,hInnerA,hInnerS,hAvoid,hDiv,hAbs⟩ :=
    marked_protected_correction_matching_deletion P π d r size a₀ b₀ e₀ f₀ εAbs ζ ξCorr σ H T W hCorr
  refine ⟨DA,DS,hSub,hArc,hRow,hCol,hCardA,hCardS,hEmpty,hDegA,hDegS,hInnerA,hInnerS,hAvoid,hDiv,hAbs,?_⟩
  intro S Kbad Protected M ξ δ hsum hSP hKP hM hedit horient hAgree hDavoid hOrientProtected
  have hh:=long_class_protected_matching_after_correction P S Kbad (markedSampleArcSetGraph P π d σ DA) Protected π d ω M ξ δ ζ
  have hdec:instDecidableEqFin n=lateProtectedActualFin n:=Subsingleton.elim _ _
  have hdec6:instDecidableEqFin 6=lateProtectedActualFin 6:=Subsingleton.elim _ _
  try rw [hdec] at hh
  try rw [hdec6] at hh
  obtain ⟨Del,hD,hedits,hinc,hdegree,hDelProtect,hselected,hbad,hP,hmixed⟩ :=
    hh hSP hKP hM (by simpa only [Fintype.card_fin] using hedit)
      (by simpa only [Fintype.card_fin] using horient) hDegA hAgree hDavoid hOrientProtected
  have hdegree':∀v,(Del.degree v:ℝ)≤Δ*n:=by
    intro v
    have hv:=hdegree v
    simp only [Fintype.card_fin] at hv
    exact hv.trans (mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg n))
  exact ⟨Del,hD,hedits,hinc,hdegree',hDelProtect,hselected,hbad,hP,hmixed,hMatching Del hdegree'⟩
end Oberwolfach
