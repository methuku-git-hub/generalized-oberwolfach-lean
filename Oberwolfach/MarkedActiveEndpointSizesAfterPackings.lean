module

public import Oberwolfach.MarkedInnerEndpointSizesAfterPackings
public import Oberwolfach.MarkedEndpointRestrictionCounts

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
variable {V VA U UA Γ Color E K:Type} [Fintype V] [Fintype VA] [Fintype U] [Fintype UA] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder VA] [DecidableEq U] [DecidableEq UA]
  {tail head:E→V} {ktail khead:K→V} {πD:Equiv.Perm V} {mD bD:ℕ} {H₀ HK:V→U→Prop}

theorem marked_active_endpoint_sizes_after_packings
    (MD:Finset (MarkedWheel tail head ktail khead mD πD bD H₀ HK))
    (f:VA↪oV) (g:UA↪U) (ρ:Equiv.Perm VA) (π:Equiv.Perm V)
    (hf:∀ x,f (ρ x)=π (f x)) (X:Finset VA) (Z:Finset UA)
    (hU:Fintype.card U≤Fintype.card V)
    (A:Finset V) (B:Finset U) (hAX:A=X.image f) (hBZ:B=Z.image g)
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource A B)=∅)
    (P:SimpleGraph V) (d h:ℕ) (hh:3≤h) (hA:∀ x,π x∈A↔x∈A)
    (omega t rho:ℝ) (ho:0<omega) (ht:0<t) (hrho:0<rho) (hrho1:rho≤1)
    (r:ℕ) (hst:(r+4:ℝ)*t≤1) (hBn:omega*Fintype.card V≤(B.card:ℝ))
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (c:Color)
    (hq:∀ u∈B,q u a=t) (hs:∀ u∈B,s u c=(r+4:ℝ)*t)
    (errR errI δP δR δV δU:ℝ)
    (heR:0≤errR) (heI:0≤errI) (hdP:0≤δP) (hdR:0≤δR) (hdV:0≤δV) (hdU:0≤δU)
    (hparent:∀ x,|((P.neighborFinset x∩A).card:ℝ)-2*B.card/rho|≤δP)
    (hRsmall:errR+h*(δR+δU)+(6*(d:ℝ)+1)+δP≤t*omega*Fintype.card V/4)
    (hIsmall:errI+h*δV≤t*omega*Fintype.card V/4)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A (rho*((r+4:ℝ)*t)/2) (rho*t/2) q s a c errR σ H)
    (hi:MarkedIndicesWithSpokes π d h B q s a c errI σ H)
    (ER:SimpleGraph V) (ES:SimpleGraph (V⊕U))
    (hrim:∀ x,(ER.degree x:ℝ)≤δR) (hrow:∀ x,(ES.degree (Sum.inl x):ℝ)≤δV)
    (hcol:∀ u,(ES.degree (Sum.inr u):ℝ)≤δU):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ (ER⊔markedPackingRimGraph MD).edgeFinset)
    let HA:=fun b x u=>markedDeletePhysicalSpokes H (ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)) b (f x) (g u);
    (∀ mark incoming x,(t*omega/4)*Fintype.card (VA⊕UA)≤
      ((markedEndpointLabels (P.comap f) ρ d X (mark,incoming,x) σA).card:ℝ)) ∧
    (∀ b x,(t*omega/4)*Fintype.card (VA⊕UA)≤((Z.filter (HA b x)).card:ℝ)) ∧
    (∀ x,((markedEndpointLabels (P.comap f) ρ d X (true,false,x) σA).card:ℝ)+
      (t*omega/8)*Fintype.card (VA⊕UA)≤(Z.filter (HA false x)).card) :=by
  intro σA HA
  obtain ⟨hL,hS,hgap⟩:=marked_inner_endpoint_sizes_after_packings MD A B hstar P π d h hh hA
    (Fintype.card V) omega t rho ho ht hrho hrho1 r hst hBn q s a c hq hs
    errR errI δP δR δV δU heR heI hdP hdR hdV hdU hparent hRsmall hIsmall σ H hr hi ER ES hrim hrow hcol
  have hVA:=Fintype.card_le_of_injective f f.injective
  have hUA:=Fintype.card_le_of_injective g g.injective
  have hambient:(Fintype.card (VA⊕UA):ℝ)≤2*Fintype.card V:=by
    exact_mod_cast (show Fintype.card (VA⊕UA)≤2*Fintype.card V by simp only [Fintype.card_sum];omega)
  have hsize:(t*omega/4)*Fintype.card (VA⊕UA)≤(t*omega/2)*Fintype.card V:=by
    have hh:=mul_le_mul_of_nonneg_left hambient (show 0≤t*omega/4 by positivity)
    nlinarith only [hh]
  have hgapSize:(t*omega/8)*Fintype.card (VA⊕UA)≤(t*omega/4)*Fintype.card V:=by
    have hh:=mul_le_mul_of_nonneg_left hambient (show 0≤t*omega/8 by positivity)
    nlinarith only [hh]
  have hlabel (mark incoming:Bool) (x:VA):
      (markedEndpointLabels P π d A (mark,incoming,f x)
        (rawMarkedDeleteRims σ (ER⊔markedPackingRimGraph MD).edgeFinset)).card=
      (markedEndpointLabels (P.comap f) ρ d X (mark,incoming,x) σA).card:=by
    rw [hAX]
    exact markedEndpointLabels_embedding_card f g π ρ hf P d X _ mark incoming x
  have hspoke (b:Bool) (x:VA):
      (B.filter (markedDeletePhysicalSpokes H (ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)) b (f x))).card=
      (Z.filter (HA b x)).card:=by
    rw [hBZ]
    exact markedSpokeNeighbours_embedding_card g Z _ b (f x)
  refine ⟨?_,?_,?_⟩
  · intro mark incoming x
    rw [←hlabel]
    exact hsize.trans (hL mark incoming (f x))
  · intro b x
    rw [←hspoke]
    exact hsize.trans (hS b (f x))
  · intro x
    rw [←hlabel,←hspoke]
    have hh:=hgap (f x)
    linarith only [hgapSize,hh]

end Oberwolfach
