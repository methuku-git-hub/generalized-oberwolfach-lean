module

public import Oberwolfach.MarkedInnerNeighbourhoodsAfterDeepPacking
public import Oberwolfach.MarkedEndpointClassSizes

@[expose] public section

/-! Endpoint classes are formed in the actual host after both earlier
packings. The second packing avoids the entire inner star, so only the
first packing enters these error budgets, including at external roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color E K:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {πD:Equiv.Perm V} {mD bD:ℕ} {H₀ HK:V→U→Prop}

theorem marked_inner_endpoint_sizes_after_packings
    (MD:Finset (MarkedWheel tail head ktail khead mD πD bD H₀ HK))
    (A:Finset V) (B:Finset U)
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource A B)=∅)
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (hh:3≤h) (hA:∀ x,π x∈A↔x∈A)
    (n:ℕ) (omega t rho:ℝ) (ho:0<omega) (ht:0<t) (hrho:0<rho) (hrho1:rho≤1)
    (r:ℕ) (hst:(r+4:ℝ)*t≤1) (hBn:omega*n≤(B.card:ℝ))
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (hq:∀ u∈B,q u g=t) (hs:∀ u∈B,s u j=(r+4:ℝ)*t)
    (errR errI δP δR δV δU:ℝ)
    (heR:0≤errR) (heI:0≤errI) (hdP:0≤δP) (hdR:0≤δR) (hdV:0≤δV) (hdU:0≤δU)
    (hparent:∀ x,|((P.neighborFinset x∩A).card:ℝ)-2*B.card/rho|≤δP)
    (hRsmall:errR+h*(δR+δU)+(6*(d:ℝ)+1)+δP≤t*omega*n/4)
    (hIsmall:errI+h*δV≤t*omega*n/4)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A (rho*((r+4:ℝ)*t)/2) (rho*t/2) q s g j errR σ H)
    (hi:MarkedIndicesWithSpokes π d h B q s g j errI σ H)
    (ER:SimpleGraph V) (ES:SimpleGraph (V⊕U))
    (hrim:∀ x,(ER.degree x:ℝ)≤δR) (hrow:∀ x,(ES.degree (Sum.inl x):ℝ)≤δV)
    (hcol:∀ u,(ES.degree (Sum.inr u):ℝ)≤δU):
    let σ':=rawMarkedDeleteRims σ (ER⊔markedPackingRimGraph MD).edgeFinset
    let H':=markedDeletePhysicalSpokes H (ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs));
    (∀ mark incoming x,(t*omega/2)*n≤
      ((markedEndpointLabels P π d A (mark,incoming,x) σ').card:ℝ)) ∧
    (∀ b x,(t*omega/2)*n≤((B.filter (H' b x)).card:ℝ)) ∧
    (∀ x,((markedEndpointLabels P π d A (true,false,x) σ').card:ℝ)+(t*omega/4)*n≤
      (B.filter (H' false x)).card):=by
  intro σ' H'
  obtain ⟨hrows,hidx⟩:=marked_inner_neighbourhoods_after_both_packings MD A B hstar P π d h hA
    (rho*((r+4:ℝ)*t)/2) (rho*t/2) q s g j errR errI δR δV δU hdR hdV hdU σ H hr hi ER ES hrim hrow hcol
  have hc:(r+5:ℕ)≥4:=by omega
  have hrc:(((r+5:ℕ):ℝ)-1)=(r+4:ℝ):=by push_cast;ring
  have hs':∀ u∈B,s u j=(((r+5:ℕ):ℝ)-1)*t:=by simpa only [hrc] using hs
  have hr':MarkedRowsWithSpokes P π d h A (rho*((((r+5:ℕ):ℝ)-1)*t)/2) (rho*t/2)
      q s g j (errR+h*(δR+δU)) σ' H':=by simpa only [hrc] using hrows
  obtain ⟨hL,hT,hgap⟩:=marked_endpoint_class_sizes P π d h hh A B hA n omega t rho ho ht hrho hrho1
    (r+5) hc (by simpa only [hrc] using hst) hBn q s g j hq hs'
    (errR+h*(δR+δU)) (errI+h*δV) δP (t*omega/8) (by positivity) (by positivity) hdP hparent
    hRsmall hIsmall le_rfl σ' H' hr' hidx
  refine ⟨hL,hT,?_⟩
  intro x
  convert hgap x using 1 <;> ring

end Oberwolfach
