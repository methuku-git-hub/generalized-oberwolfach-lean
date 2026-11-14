module

public import Oberwolfach.MarkedNeighbourhoodEmbeddingBounds
public import Oberwolfach.MarkedNeighbourhoodDomainRestriction
public import Oberwolfach.MarkedPhysicalDeletionRestriction

@[expose] public section

/-! Fixed-domain row and index estimates on the actual active sample after
later physical deletions. The parent event still quantifies over all roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_protected_active_neighbourhoods
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d h:ℕ)
    (A:Finset W) (A₀:Finset V) (hA:A.image f⊆A₀)
    (B:Finset Z) (B₀:Finset U) (hB:B.image g⊆B₀)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (c:Γ) (j:Color)
    (hp:0≤p∧p≤1) (hk:0≤k∧k≤1) (hq:∀ u,0≤q u c∧q u c≤1) (hs:∀ u,0≤s u j∧s u j≤1)
    (errR errI deltaR deltaV deltaU:ℝ) (hdR:0≤deltaR) (hdV:0≤deltaV) (hdU:0≤deltaU)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A₀ p k q s c j errR σ H)
    (hi:MarkedIndicesWithSpokes π d h B₀ q s c j errI σ H)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,((DR.comap f).degree x:ℝ)≤deltaR)
    (hrow:∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤deltaV)
    (hcol:∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤deltaU):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)
    let HA:=fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u);
    MarkedRowsWithSpokes (P.comap f) ρ d h A p k (fun u=>q (g u)) (fun u=>s (g u)) c j
      (errR+(A₀\A.image f).card+h*(deltaR+deltaU)) σA HA∧
    MarkedIndicesWithSpokes ρ d h B (fun u=>q (g u)) (fun u=>s (g u)) c j
      (errI+(B₀\B.image g).card+h*deltaV) σA HA:=by
  intro σA HA
  have hr₀:=markedRowsWithSpokes_domain_restriction P π d h (A.image f) A₀ hA
    p k q s c j errR hp hk hq hs σ H hr
  have hi₀:=markedIndicesWithSpokes_domain_restriction π d h (B.image g) B₀ hB
    q s c j errI hq hs σ H hi
  have hrA:=markedRowsWithSpokes_embedding f g π ρ hf P d h A p k q s c j _ σ H hr₀
  have hiA:=markedIndicesWithSpokes_embedding f g π ρ hf d h B q s c j _ σ H hi₀
  have hh:=marked_neighbourhoods_after_physical_deletion (P.comap f) ρ d h A B p k
    (fun u=>q (g u)) (fun u=>s (g u)) c j _ _ deltaR deltaV deltaU hdR hdV hdU
    (rawMarkedRestrictPair f g σ) (fun b x u=>H b (f x) (g u)) hrA hiA
    (DR.comap f) (DS.comap (Sum.map f g)) hrim hrow hcol
  have hσ:σA=rawMarkedDeleteRims (rawMarkedRestrictPair f g σ) (DR.comap f).edgeFinset:=
    rawMarkedRestrictPair_deleteRims f g σ DR
  rw [hσ]
  exact hh

end Oberwolfach
