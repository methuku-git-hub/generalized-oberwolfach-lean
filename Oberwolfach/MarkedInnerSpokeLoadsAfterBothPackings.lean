module

public import Oberwolfach.MarkedInnerCompletionEstimates

@[expose] public section

/-! Transfer the fixed root-omitted weights after both packings. The deep
packing contributes exactly zero on the original inner vertex domain,
including tested spokes that are absent. The hub domain is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color E K:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]
  {tail head:E→V} {ktail khead:K→V} {π₀:Equiv.Perm V} {m₀ b₀:ℕ} {H₀ HK:V→U→Prop}

theorem marked_inner_spoke_loads_after_both_packings
    (MD:Finset (MarkedWheel tail head ktail khead m₀ π₀ b₀ H₀ HK)) (A:Finset V) (B₀:Finset U)
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource A B₀)=∅)
    (f:W↪oV) (g:Z↪U) (hf:∀ x,f x∈A) (P:SimpleGraph V) (ρ:Equiv.Perm W) (d m:ℕ)
    (hm:3≤m) (hn:0<Fintype.card W) (D τ aLo B:ℝ)
    (hDlo:(Fintype.card W:ℝ)/2≤D) (hDhi:D≤2*Fintype.card W)
    (p k s₀ pstar:ℝ) (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hB:0≤B)
    (weight:(Fin (m+1)→W)→ℝ)
    (hw:SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τ aLo B weight)
    (eps deltaR deltaS:ℝ) (hR:0≤deltaR) (hS:0≤deltaS)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hload:MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d m D p k s₀ weight eps
      (rawMarkedRestrictPair f g σ) (fun b x z=>H b (f x) (g z)))
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x:W,((DR.neighborFinset (f x)∩Finset.univ.image f).card:ℝ)≤deltaR)
    (hspoke:∀ z:W⊕Z,((DS.neighborFinset (Sum.map f g z)∩Finset.univ.image (Sum.map f g)).card:ℝ)≤deltaS):
    MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d m D p k s₀ weight
      (eps+5*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*(2*deltaR+deltaS)/Fintype.card W)
      (rawMarkedRestrictPair f g (rawMarkedDeleteRims σ (DR⊔markedPackingRimGraph MD).edgeFinset))
      (fun b x z=>markedDeletePhysicalSpokes H (DS⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)) b (f x) (g z)) :=by
  have he:=marked_inner_domain_restriction_ignores_deep_packing MD A B₀ hstar f g hf σ H DR DS
  rw [he.1,he.2]
  exact marked_domain_spoke_loads_after_global_physical_deletion f g P ρ d m hm hn D τ aLo B
    hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw eps deltaR deltaS hR hS
    σ H hload DR DS hrim hspoke

end Oberwolfach
