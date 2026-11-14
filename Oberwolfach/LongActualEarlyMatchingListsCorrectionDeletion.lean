module

public import Oberwolfach.MarkedCorrectionOrientedMatchingDeletion
public import Oberwolfach.LongEarlyMatchingListsForDeletion

@[expose] public section
/-! The selected correction and the early matching-and-list witnesses
coexist after one oriented physical deletion on the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance actualEarlyDeletionFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)
theorem long_actual_early_matching_lists_correction_deletion
    (Δ C ξmax:ℝ) (hΔ:0<Δ) (hC:0≤C) (hmax:0<ξmax):
    ∃ξcap:ℝ,0<ξcap ∧ ξcap≤ξmax ∧ ∃N:ℕ,∀n≥N,
    ∀(U:Type) [Fintype U] [DecidableEq U] [Nonempty (Fin n)],
    ∀(P S Kbad Protected:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r size a₀ b₀ e₀ f₀:ℕ)
      (εAbs ζCorr ξCorr:ℝ)
      (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n)) (W:Finset U)
      (M:Fin n→Fin n→ℕ) (K:ℕ) (θ D alpha γ eps βList:ℝ)
      (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (weight:(Fin (r+4+1)→Fin n)→ℝ)
      (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ),
    let V:=Fin n
    let ω:=z.1
    let σ:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false
    let Matching:=fun Del:SimpleGraph V=>LongEarlyMatchingListsForDeletion r K d θ D alpha γ eps Δ βList P π F hF weight w z T Del
    let S₀:=longPhysicalStateGraph P ω {0,1,2,3,4};
    ∀(ξ δ:ℝ),0≤ξ→ξ≤ξcap→ζCorr≤Δ/2→
    δ≤C*Real.sqrt ξ+5*(n:ℝ)^(-(1/5:ℝ))→
    S≤P→Kbad≤S→(∀x y,M x y+M y x=if S.Adj x y then 1 else 0)→
    (∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
    (∀v,((orientationDisagreementGraph S₀ (fun e=>(ω (Sum.inl e)).2) M).degree v:ℝ)≤δ*n)→
    (∀x y,Protected.Adj x y→x∈T ∧ y∈T)→
    (∀x y,Protected.Adj x y→(S.Adj x y↔S₀.Adj x y))→
    (∀x y,(orientationDisagreementGraph S₀ (fun e=>(ω (Sum.inl e)).2) M).Adj x y→¬Protected.Adj x y)→
    (∀Del:SimpleGraph V,(∀v,(Del.degree v:ℝ)≤Δ*n)→Matching Del)→
    MarkedProtectedAbsorbableCorrectionWithBounds P π d r size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr σ H T W →
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let spokeSet:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∃(DA:Finset (E⊕K)) (DS:Finset (V×U)),DS⊆spokeSet ∧
      (∀v,((DA.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤
        8*(((r+4:ℕ):ℝ)+1)*ξCorr*(n:ℕ)) ∧
      (∀v,((DS.filter (fun z=>v=z.1)).card:ℝ)≤4*(((r+4:ℕ):ℝ)+1)*ξCorr*(n:ℕ)) ∧
      (∀u,((DS.filter (fun z=>u=z.2)).card:ℝ)≤4*(((r+4:ℕ):ℝ)+1)*ξCorr*(n:ℕ)) ∧
      (DA.card:ℝ)≤8*(((r+4:ℕ):ℝ)+1)*ξCorr*((n:ℕ):ℝ)^2 ∧
      (DS.card:ℝ)≤4*(((r+4:ℕ):ℝ)+1)*ξCorr*((n:ℕ):ℝ)^2 ∧
      (markedFiniteResources tail head ktail khead π DA DS).filter (markedInnerResource T W)=∅ ∧
      (∀v,((markedSampleArcSetGraph P π d σ DA).degree v:ℝ)≤ζCorr*(n:ℕ)) ∧
      (∀z,((markedFiniteSpokeGraph DS).degree z:ℝ)≤ζCorr*(n:ℕ)) ∧
      (∀x∈T,∀y∈T,¬(markedSampleArcSetGraph P π d σ DA).Adj x y) ∧
      (∀x∈T,∀u∈W,¬(markedFiniteSpokeGraph DS).Adj (Sum.inl x) (Sum.inr u)) ∧
      (∀x y,(markedSampleArcSetGraph P π d σ DA).Adj x y→¬Protected.Adj x y) ∧
      (∃Del:SimpleGraph V,
        (markedSampleArcSetGraph P π d σ DA)≤Del ∧
        (S₀\S)≤Del ∧ orientationDisagreementGraph S₀ (fun e=>(ω (Sum.inl e)).2) M≤Del ∧
        (∀v,(Del.degree v:ℝ)≤Δ*(n:ℕ)) ∧
        (∀x y,Del.Adj x y→¬Protected.Adj x y) ∧
        (∀x y,rawSelectedPhysicalRelation P π d (fun e=>ω (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
        (∀x y,Kbad.Adj x y→M x y=1 ∨ M y x=1) ∧
        (∀x y,M x y=1→P.Adj x y) ∧
        (∀x y,rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (ω e)) x y→
          ¬Del.Adj x y→M x y=1) ∧ Matching Del) ∧
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ DA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) (r+4) ∧
    MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs := by
  obtain ⟨ξcap,hξcap,hξmax,N,hN⟩:=marked_correction_oriented_matching_deletion Δ C ξmax hΔ hC hmax
  refine ⟨ξcap,hξcap,hξmax,N,?_⟩
  intro n hn U _ _ _ P S Kbad Protected π d r size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr z T W M K θ D alpha γ eps βList F hF weight w V ω σ H Matching S₀
  intro ξ δ hξ hξcap hζ hδ hSP hKP hM hedit horient hProtected hAgree hOrientProtected hMatching hCorr
  have hh:=hN n hn U Bool Bool P S Kbad Protected π d r size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr ω H T W M Matching
  have hdec:correctionOrientedFin n=actualEarlyDeletionFin n:=Subsingleton.elim _ _
  have hdec6:correctionOrientedFin 6=actualEarlyDeletionFin 6:=Subsingleton.elim _ _
  try rw [hdec] at hh
  try rw [hdec6] at hh
  exact hh ξ δ hξ hξcap hζ hδ hSP hKP hM hedit horient hProtected hAgree hOrientProtected hMatching hCorr
end Oberwolfach
