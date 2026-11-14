module

public import Oberwolfach.MarkedInnerNeighbourhoodsAfterDeepPacking
public import Oberwolfach.MarkedNeighbourhoodEmbeddingBounds

@[expose] public section

/-! Inner estimates after both constructed packings, expressed on the
active vertex and hub types. Every active root is retained, including roots
outside the inner domains; the deep packing incurs no additional error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V VA U UA Γ Color E K:Type} [Fintype V] [Fintype VA] [Fintype U] [Fintype UA]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder VA] [DecidableEq U] [DecidableEq UA]
  {tail head:E→V} {ktail khead:K→V} {πD:Equiv.Perm V} {mD bD:ℕ} {H₀ HK:V→U→Prop}

theorem marked_inner_active_neighbourhoods
    (f:VA↪oV) (g:UA↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm VA)
    (hf:∀ x,f (ρ x)=π (f x)) (X:Finset VA) (Z:Finset UA)
    (hX:∀ x,π x∈X.image f↔x∈X.image f)
    (MD:Finset (MarkedWheel tail head ktail khead mD πD bD H₀ HK))
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource (X.image f) (Z.image g))=∅)
    (P:SimpleGraph V) (d h:ℕ) (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (c:Color)
    (errR errI δR δV δU:ℝ) (hdR:0≤δR) (hdV:0≤δV) (hdU:0≤δU)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h (X.image f) p k q s a c errR σ H)
    (hi:MarkedIndicesWithSpokes π d h (Z.image g) q s a c errI σ H)
    (ER:SimpleGraph V) (ES:SimpleGraph (V⊕U))
    (hrim:∀ x,(ER.degree x:ℝ)≤δR) (hrow:∀ x,(ES.degree (Sum.inl x):ℝ)≤δV)
    (hcol:∀ u,(ES.degree (Sum.inr u):ℝ)≤δU):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ (ER⊔markedPackingRimGraph MD).edgeFinset)
    let HA:=fun b x u=>markedDeletePhysicalSpokes H (ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)) b (f x) (g u);
    MarkedRowsWithSpokes (P.comap f) ρ d h X p k (fun u=>q (g u)) (fun u=>s (g u)) a c
      (errR+h*(δR+δU)) σA HA∧
    MarkedIndicesWithSpokes ρ d h Z (fun u=>q (g u)) (fun u=>s (g u)) a c
      (errI+h*δV) σA HA:=by
  intro σA HA
  obtain ⟨hrow',hidx'⟩:=marked_inner_neighbourhoods_after_both_packings MD (X.image f) (Z.image g)
    hstar P π d h hX p k q s a c errR errI δR δV δU hdR hdV hdU σ H hr hi ER ES hrim hrow hcol
  exact ⟨markedRowsWithSpokes_embedding f g π ρ hf P d h X p k q s a c _ _ _ hrow',
    markedIndicesWithSpokes_embedding f g π ρ hf d h Z q s a c _ _ _ hidx'⟩

end Oberwolfach
