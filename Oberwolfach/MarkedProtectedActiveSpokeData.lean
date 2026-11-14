module

public import Oberwolfach.MarkedProtectedActiveNeighbourhoods
public import Oberwolfach.MarkedSpokeIntersectionsFromNeighbourhoods

@[expose] public section

/-! Supply the sparse-intersection hypotheses for the two actual active
spoke relations, using the original all-root neighbourhood estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_protected_active_spoke_data
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d h:ℕ) (hh:3≤h)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (c:Γ) (j:Color)
    (hp:0≤p∧p≤1) (hk:0≤k∧k≤1) (hq:∀ u,0≤q u c∧q u c≤1) (hs:∀ u,0≤s u j∧s u j≤1)
    (errR errI deltaR deltaV deltaU p₀ δ:ℝ) (hdR:0≤deltaR) (hdV:0≤deltaV) (hdU:0≤deltaU)
    (density:Bool→ℝ) (hp₀:0<p₀) (hden0:∀ b,p₀≤density b) (hden1:∀ b,density b≤1) (hδ:0≤δ)
    (hden:∀ b u,(if b then q u c else s u j)=density b)
    (hRsmall:errR+(Finset.univ\Finset.univ.image f).card+h*(deltaR+deltaU)≤δ*Fintype.card W)
    (hIsmall:errI+(Finset.univ\Finset.univ.image g).card+h*deltaV≤δ*p₀^2*Fintype.card Z)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h Finset.univ p k q s c j errR σ H)
    (hi:MarkedIndicesWithSpokes π d h Finset.univ q s c j errI σ H)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,((DR.comap f).degree x:ℝ)≤deltaR)
    (hrow:∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤deltaV)
    (hcol:∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤deltaU):
    ∀ mark,SparseIntersectionData (fun x u=>markedDeletePhysicalSpokes H DS mark (f x) (g u))
      (fun _=>density mark) (fun _=>1/density mark) (max 1 (1/p₀)) δ (6*d+1):=by
  obtain ⟨hrA,hiA⟩:=marked_protected_active_neighbourhoods f g π ρ hf P d h
    Finset.univ Finset.univ (Finset.subset_univ _) Finset.univ Finset.univ (Finset.subset_univ _)
    p k q s c j hp hk hq hs errR errI deltaR deltaV deltaU hdR hdV hdU σ H hr hi DR DS hrim hrow hcol
  intro mark
  apply marked_neighbourhoods_sparse_intersection_data (P.comap f) ρ d h hh p k
    (fun u=>q (g u)) (fun u=>s (g u)) c j _ _ (density mark) p₀ δ hp₀ (hden0 mark) (hden1 mark) hδ
    hRsmall _ (rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset))
    (fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u)) mark (fun u=>hden mark (g u)) hrA hiA
  apply hIsmall.trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hp₀.le (hden0 mark) 2) hδ) (Nat.cast_nonneg _)

end Oberwolfach
