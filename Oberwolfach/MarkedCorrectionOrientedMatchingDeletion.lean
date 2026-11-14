module

public import Oberwolfach.MarkedProtectedCorrectionMatchingDeletion
public import Oberwolfach.LongProtectedMatchingDeletionBudget

@[expose] public section
/-! The protected correction, balanced-orientation deletion, and every
matching continuation available for the resulting deletion use one sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance correctionOrientedFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)

theorem marked_correction_oriented_matching_deletion
    (Δ C ξmax:ℝ) (hΔ:0<Δ) (hC:0≤C) (hmax:0<ξmax):
    ∃ξcap:ℝ,0<ξcap ∧ ξcap≤ξmax ∧ ∃N:ℕ,∀n≥N,
    ∀(U Γ Color:Type) [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    ∀(P S Kbad Protected:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r size a₀ b₀ e₀ f₀:ℕ)
      (εAbs ζCorr ξCorr:ℝ)
      (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
      (H:Bool→Fin n→U→Prop) (T:Finset (Fin n)) (W:Finset U)
      (M:Fin n→Fin n→ℕ) (Matching:SimpleGraph (Fin n)→Prop),
    let V:=Fin n
    let σ:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (ω e)
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
  obtain ⟨ξcap,hξcap,hξmax,N,hN⟩ := long_protected_matching_deletion_with_budget Δ C ξmax hΔ hC hmax
  refine ⟨ξcap,hξcap,hξmax,N,?_⟩
  intro n hn U Γ Color _ _ _ _ P S Kbad Protected π d r size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr ω H T W M Matching V σ S₀
  intro ξ δ hξ hξcap hζ hδ hSP hKP hM hedit horient hProtected hAgree hOrientProtected hMatching hCorr
  obtain ⟨DA,DS,hSub,hArc,hRow,hCol,hCardA,hCardS,hEmpty,hDegA,hDegS,hInnerA,hInnerS,hAvoid,hDiv,hAbs⟩ :=
    marked_protected_correction_matching_deletion P π d r size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr σ H T W hCorr
  have hAvoid' := hAvoid Protected hProtected
  have hDel := hN n hn U Γ Color P S Kbad (markedSampleArcSetGraph P π d σ DA) Protected π d ω M
  have hdec:instDecidableEqFin n=correctionOrientedFin n:=Subsingleton.elim _ _
  try rw [hdec] at hDel
  have hdec6:instDecidableEqFin 6=correctionOrientedFin 6:=Subsingleton.elim _ _
  try rw [hdec6] at hDel
  obtain ⟨Del,hD,hedits,hinc,hdegree,hDelProtect,hselected,hbad,hP,hmixed⟩ :=
    hDel ξ δ ζCorr hξ hξcap hζ hδ hSP hKP hM hedit horient
      (by simpa only [Fintype.card_fin] using hDegA) hAgree hAvoid' hOrientProtected
  refine ⟨DA,DS,hSub,?_,?_,?_,?_,?_,hEmpty,?_,?_,hInnerA,hInnerS,hAvoid',?_,hDiv,hAbs⟩
  all_goals try simpa only [Fintype.card_fin] using hArc
  all_goals try simpa only [Fintype.card_fin] using hRow
  all_goals try simpa only [Fintype.card_fin] using hCol
  all_goals try simpa only [Fintype.card_fin] using hCardA
  all_goals try simpa only [Fintype.card_fin] using hCardS
  all_goals try simpa only [Fintype.card_fin] using hDegA
  all_goals try simpa only [Fintype.card_fin] using hDegS
  exact ⟨Del,hD,hedits,hinc,hdegree,hDelProtect,hselected,hbad,hP,hmixed,hMatching Del hdegree⟩
end Oberwolfach
