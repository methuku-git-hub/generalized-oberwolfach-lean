module

public import Oberwolfach.MarkedInnerCompletionEstimates
public import Oberwolfach.MarkedConfigurationsAfterPhysicalDeletion

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

theorem marked_inner_profiles_after_both_packings
    (MD:Finset (MarkedWheel tail head ktail khead m₀ π₀ b₀ H₀ HK)) (A:Finset V) (B₀:Finset U)
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource A B₀)=∅)
    (f:W↪oV) (g:Z↪U) (hf:∀ x,f x∈A) (P:SimpleGraph V) (ρ:Equiv.Perm W) (d r h:ℕ)
    (hn:0<Fintype.card W) (D τ aLo B:ℝ)
    (hDlo:(Fintype.card W:ℝ)/2≤D) (hDhi:D≤2*Fintype.card W)
    (p k s₀ pstar:ℝ) (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hB:0≤B)
    (weight:(Fin (r+4+1)→W)→ℝ)
    (hw:SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τ aLo B weight)
    (Q:Z→Γ→ℝ) (S:Z→Color→ℝ) (a:Γ) (c:Color)
    (err η βC βP ζR ζS:ℝ) (hζR:0≤ζR) (hζS:0≤ζS)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hrows:MarkedRowsWithSpokes (P.comap f) ρ d h Finset.univ p k Q S a c err
      (rawMarkedRestrictPair f g σ) (fun b x z=>H b (f x) (g z)))
    (hconfigs:MarkedLocalConfigurationsWithSpokes r (P.comap f) ρ d Finset.univ βC βP
      (rawMarkedRestrictPair f g σ) (fun b x z=>H b (f x) (g z)))
    (hload:MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d (r+4) D p k s₀ weight η
      (rawMarkedRestrictPair f g σ) (fun b x z=>H b (f x) (g z)))
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,((DR.comap f).degree x:ℝ)≤ζR*Fintype.card W)
    (hrow:∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤ζS*Fintype.card W)
    (hcol:∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤ζS*Fintype.card W):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ (DR⊔markedPackingRimGraph MD).edgeFinset)
    let HA:=fun b x z=>markedDeletePhysicalSpokes H (DS⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)) b (f x) (g z);
    MarkedRowsWithSpokes (P.comap f) ρ d h Finset.univ p k Q S a c
      (err+h*(ζR+ζS)*Fintype.card W) σA HA∧
    MarkedLocalConfigurationsWithSpokes r (P.comap f) ρ d Finset.univ
      (βC-(r+5:ℕ)*(ζR+ζS)) (βP-(r+7:ℕ)*ζR-(r+4:ℕ)*ζS) σA HA∧
    MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d (r+4) D p k s₀ weight
      (η+5*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*(2*ζR+ζS)) σA HA:=by
  intro σA HA
  have he:=marked_inner_domain_restriction_ignores_deep_packing MD A B₀ hstar f g hf σ H DR DS
  have hσ:σA=rawMarkedDeleteRims (rawMarkedRestrictPair f g σ) (DR.comap f).edgeFinset:=
    he.1.trans (rawMarkedRestrictPair_deleteRims f g σ DR)
  have hH:HA=markedDeletePhysicalSpokes (fun b x z=>H b (f x) (g z)) (DS.comap (Sum.map f g)):=he.2
  rw [hσ,hH]
  constructor
  · have hrim':=markedRows_after_physical_rim_deletion (P.comap f) ρ d h Finset.univ p k Q S a c err
      (ζR*Fintype.card W) (by positivity) (rawMarkedRestrictPair f g σ) (fun b x z=>H b (f x) (g z))
      hrows (DR.comap f) hrim
    have hs':=markedRows_spoke_relation_changes (P.comap f) ρ d h Finset.univ p k Q S a c
      (err+h*(ζR*Fintype.card W)) (ζS*Fintype.card W) (by positivity)
      (rawMarkedDeleteRims (rawMarkedRestrictPair f g σ) (DR.comap f).edgeFinset)
      (fun b x z=>H b (f x) (g z))
      (markedDeletePhysicalSpokes (fun b x z=>H b (f x) (g z)) (DS.comap (Sum.map f g))) hrim'
      (fun b u=>(marked_spoke_physical_deletion_column_change (fun b x z=>H b (f x) (g z)) (DS.comap (Sum.map f g)) Finset.univ b u).trans (hcol u))
    convert hs' using 1 <;> ring
  constructor
  · exact marked_local_configurations_after_physical_deletion r (P.comap f) ρ d βC βP ζR ζS
      (rawMarkedRestrictPair f g σ) (fun b x z=>H b (f x) (g z)) hconfigs
      (DR.comap f) (DS.comap (Sum.map f g)) hrim hcol
  · have hh:=marked_local_spoke_loads_after_physical_deletion (P.comap f) ρ d (r+4) (by omega) hn
      D τ aLo B hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw η
      (ζR*Fintype.card W) (ζS*Fintype.card W) (by positivity) (by positivity)
      (rawMarkedRestrictPair f g σ) (fun b x z=>H b (f x) (g z)) hload
      (DR.comap f) (DS.comap (Sum.map f g)) hrim hrow hcol
    have hn0:(Fintype.card W:ℝ)≠0:=by exact_mod_cast Nat.ne_of_gt hn
    convert hh using 1 <;> push_cast <;> field_simp [hn0] <;> ring

end Oberwolfach
