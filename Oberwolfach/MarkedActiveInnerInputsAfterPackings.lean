module

public import Oberwolfach.MarkedInnerFactorActiveRestriction
public import Oberwolfach.MarkedInnerActiveNeighbourhoods

@[expose] public section

/-! All inner factor and neighbourhood inputs for the actual active host
follow from their original fixed-domain estimates and the first packing's
degree bounds. The deep packing avoids the inner star and adds no loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V VA W U UA Γ Color E K:Type} [Fintype V] [Fintype VA] [Fintype W] [Fintype U] [Fintype UA]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder VA] [LinearOrder W]
  [DecidableEq U] [DecidableEq UA]
  {tail head:E→V} {ktail khead:K→V} {πD:Equiv.Perm V} {mD bD:ℕ} {H₀ HK:V→U→Prop}

theorem marked_active_inner_inputs_after_packings
    (f:VA↪oV) (i:W↪oVA) (g:UA↪U) (P:SimpleGraph V)
    (π:Equiv.Perm V) (ρA:Equiv.Perm VA) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρA x)=π (f x)) (X:Finset VA) (hX:Finset.univ.image i=X) (Z:Finset UA)
    (hInv:∀ x,π x∈X.image f↔x∈X.image f)
    (MD:Finset (MarkedWheel tail head ktail khead mD πD bD H₀ HK))
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource (X.image f) (Z.image g))=∅)
    (d r h:ℕ) (hn:0<Fintype.card W) (D tau aLo B p k s₀ pstar:ℝ)
    (hDlo:(Fintype.card W:ℝ)/2≤D) (hDhi:D≤2*Fintype.card W)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hB:0≤B)
    (weight:(Fin (r+4+1)→W)→ℝ)
    (hw:SuccessorSequenceWeightConditions (P.comap (i.comp f)) ρ (3*d) D tau aLo B weight)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (c:Color)
    (t eta beta zR zS errR errI deltaR deltaV deltaU:ℝ)
    (hzR:0≤zR) (hzS:0≤zS) (hdR:0≤deltaR) (hdV:0≤deltaV) (hdU:0≤deltaU)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hfactorRows:MarkedRowsWithSpokes (P.comap (i.comp f)) ρ d 1 Finset.univ p k
      (fun u=>q (g u)) (fun u=>s (g u)) a c ((t/4)*Fintype.card W)
      (rawMarkedRestrictPair (i.comp f) g σ) (fun b x u=>H b (f (i x)) (g u)))
    (hconfigs:MarkedLocalConfigurationsWithSpokes r (P.comap (i.comp f)) ρ d Finset.univ (2*beta) (2*beta)
      (rawMarkedRestrictPair (i.comp f) g σ) (fun b x u=>H b (f (i x)) (g u)))
    (hload:MarkedLocalSpokeLoadsWithSpokes (P.comap (i.comp f)) ρ d (r+4) D p k s₀ weight (eta/2)
      (rawMarkedRestrictPair (i.comp f) g σ) (fun b x u=>H b (f (i x)) (g u)))
    (hrows:MarkedRowsWithSpokes P π d h (X.image f) p k q s a c errR σ H)
    (hindices:MarkedIndicesWithSpokes π d h (Z.image g) q s a c errI σ H)
    (ER:SimpleGraph V) (ES:SimpleGraph (V⊕U))
    (hER:∀ x,(ER.degree x:ℝ)≤deltaR)
    (hEV:∀ x,(ES.degree (Sum.inl x):ℝ)≤deltaV) (hEU:∀ u,(ES.degree (Sum.inr u):ℝ)≤deltaU)
    (hinnerR:∀ x,((ER.comap (i.comp f)).degree x:ℝ)≤zR*Fintype.card W)
    (hinnerV:∀ x,((ES.comap (Sum.map (i.comp f) g)).degree (Sum.inl x):ℝ)≤zS*Fintype.card W)
    (hinnerU:∀ u,((ES.comap (Sum.map (i.comp f) g)).degree (Sum.inr u):ℝ)≤zS*Fintype.card W)
    (hrowBudget:zR+zS≤t/4) (hcycleBudget:(r+5:ℝ)*(zR+zS)≤beta)
    (hpathBudget:(r+7:ℝ)*zR+(r+4:ℝ)*zS≤beta)
    (hloadBudget:5*(r+5:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*(2*zR+zS)≤eta/2):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ (ER⊔markedPackingRimGraph MD).edgeFinset)
    let HA:=fun b x u=>markedDeletePhysicalSpokes H (ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)) b (f x) (g u);
    MarkedRowsWithSpokes ((P.comap f).comap i) ρ d 1 Finset.univ p k (fun u=>q (g u)) (fun u=>s (g u)) a c
      ((t/2)*Fintype.card W) (rawMarkedRestrictVertices i σA) (fun b x u=>HA b (i x) u)∧
    MarkedLocalConfigurationsWithSpokes r ((P.comap f).comap i) ρ d Finset.univ beta beta
      (rawMarkedRestrictVertices i σA) (fun b x u=>HA b (i x) u)∧
    MarkedLocalSpokeLoadsWithSpokes ((P.comap f).comap i) ρ d (r+4) D p k s₀ weight eta
      (rawMarkedRestrictVertices i σA) (fun b x u=>HA b (i x) u)∧
    MarkedRowsWithSpokes (P.comap f) ρA d h X p k (fun u=>q (g u)) (fun u=>s (g u)) a c
      (errR+h*(deltaR+deltaU)) σA HA∧
    MarkedIndicesWithSpokes ρA d h Z (fun u=>q (g u)) (fun u=>s (g u)) a c
      (errI+h*deltaV) σA HA:=by
  intro σA HA
  have hinner:∀ x,(i.comp f) x∈X.image f:=by
    intro x
    apply Finset.mem_image.mpr
    refine ⟨i x,?_,rfl⟩
    rw [←hX]
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  obtain ⟨hr,hc,hl⟩:=marked_inner_factor_inputs_after_both_packings MD (X.image f) (Z.image g)
    hstar (i.comp f) g hinner P ρ d r hn D tau aLo B hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB
    weight hw (fun u=>q (g u)) (fun u=>s (g u)) a c t eta beta zR zS hzR hzS σ H
    hfactorRows hconfigs hload ER ES hinnerR hinnerV hinnerU hrowBudget hcycleBudget hpathBudget hloadBudget
  obtain ⟨hr',hc',hl'⟩:=marked_inner_factor_active_restriction f i g P ρ d r D p k s₀ t eta beta weight
    (fun u=>q (g u)) (fun u=>s (g u)) a c
    (rawMarkedDeleteRims σ (ER⊔markedPackingRimGraph MD).edgeFinset)
    (markedDeletePhysicalSpokes H (ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs))) hr hc hl
  obtain ⟨hrA,hiA⟩:=marked_inner_active_neighbourhoods f g π ρA hf X Z hInv MD hstar P d h p k q s a c
    errR errI deltaR deltaV deltaU hdR hdV hdU σ H hrows hindices ER ES hER hEV hEU
  exact ⟨hr',hc',hl',hrA,hiA⟩

end Oberwolfach
