module

public import Oberwolfach.MarkedInnerProfilesAfterBothPackings
public import Oberwolfach.MarkedInnerFactorDeletionTolerance

@[expose] public section

/-! The inner sampled host retains its fixed coefficients and all three
factor inputs after the prescribed and deep packings. The error depends on
the prescribed packing alone, since deep wheels avoid the inner star. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color E K:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]
  {tail head:E→V} {ktail khead:K→V} {π₀:Equiv.Perm V} {m₀ b₀:ℕ} {H₀ HK:V→U→Prop}

theorem marked_inner_factor_inputs_after_both_packings
    (MD:Finset (MarkedWheel tail head ktail khead m₀ π₀ b₀ H₀ HK)) (A:Finset V) (B₀:Finset U)
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource A B₀)=∅)
    (f:W↪oV) (g:Z↪U) (hf:∀ x,f x∈A) (P:SimpleGraph V) (ρ:Equiv.Perm W) (d r:ℕ)
    (hn:0<Fintype.card W) (D τ aLo B:ℝ)
    (hDlo:(Fintype.card W:ℝ)/2≤D) (hDhi:D≤2*Fintype.card W)
    (p k s₀ pstar:ℝ) (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hB:0≤B)
    (weight:(Fin (r+4+1)→W)→ℝ)
    (hw:SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τ aLo B weight)
    (Q:Z→Γ→ℝ) (S:Z→Color→ℝ) (a:Γ) (c:Color)
    (t eta beta ζR ζS:ℝ) (hζR:0≤ζR) (hζS:0≤ζS)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hrows:MarkedRowsWithSpokes (P.comap f) ρ d 1 Finset.univ p k Q S a c ((t/4)*Fintype.card W)
      (rawMarkedRestrictPair f g σ) (fun b x z=>H b (f x) (g z)))
    (hconfigs:MarkedLocalConfigurationsWithSpokes r (P.comap f) ρ d Finset.univ (2*beta) (2*beta)
      (rawMarkedRestrictPair f g σ) (fun b x z=>H b (f x) (g z)))
    (hload:MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d (r+4) D p k s₀ weight (eta/2)
      (rawMarkedRestrictPair f g σ) (fun b x z=>H b (f x) (g z)))
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,((DR.comap f).degree x:ℝ)≤ζR*Fintype.card W)
    (hrow:∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤ζS*Fintype.card W)
    (hcol:∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤ζS*Fintype.card W)
    (hrowsBudget:ζR+ζS≤t/4)
    (hcycleBudget:(r+5:ℝ)*(ζR+ζS)≤beta)
    (hpathBudget:(r+7:ℝ)*ζR+(r+4:ℝ)*ζS≤beta)
    (hloadBudget:5*(r+5:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*(2*ζR+ζS)≤eta/2):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ (DR⊔markedPackingRimGraph MD).edgeFinset)
    let HA:=fun b x z=>markedDeletePhysicalSpokes H (DS⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)) b (f x) (g z);
    MarkedRowsWithSpokes (P.comap f) ρ d 1 Finset.univ p k Q S a c
      ((t/2)*Fintype.card W) σA HA∧
    MarkedLocalConfigurationsWithSpokes r (P.comap f) ρ d Finset.univ beta beta σA HA∧
    MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d (r+4) D p k s₀ weight eta σA HA :=by
  intro σA HA
  obtain ⟨hrows',hconfigs',hload'⟩:=marked_inner_profiles_after_both_packings MD A B₀ hstar f g hf P ρ d r 1
    hn D τ aLo B hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw Q S a c
    ((t/4)*Fintype.card W) (eta/2) (2*beta) (2*beta) ζR ζS hζR hζS σ H hrows hconfigs hload DR DS hrim hrow hcol
  have herror:(t/4)*Fintype.card W+1*(ζR+ζS)*Fintype.card W≤(t/2)*Fintype.card W:=by
    have hh:=mul_le_mul_of_nonneg_right hrowsBudget (Nat.cast_nonneg (α:=ℝ) (Fintype.card W))
    nlinarith only [hh]
  refine ⟨?_,?_,?_⟩
  · intro S' T' J' hS hT hJ hinj
    exact (hrows' S' T' J' hS hT hJ hinj).trans_le (by simpa only [Nat.cast_one] using herror)
  · constructor
    · intro u
      have hh:=hconfigs'.1 u
      apply le_trans _ hh
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      push_cast
      linarith only [hcycleBudget]
    · intro u j v v' hv
      have hh:=hconfigs'.2 u j v v' hv
      apply le_trans _ hh
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      push_cast
      linarith only [hpathBudget]
  · intro z
    apply (hload' z).trans
    have hb:=hloadBudget
    have he:((r+4:ℝ)+1)=(r+5:ℝ):=by ring
    rw [he]
    linarith only [hb]

end Oberwolfach
