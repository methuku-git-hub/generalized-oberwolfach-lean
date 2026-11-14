module

public import Oberwolfach.MarkedNeighbourhoodEmbeddingBounds
public import Oberwolfach.MarkedSpokeToleranceMonotone

@[expose] public section
/-! Transfer a parent row estimate on the exact active vertex image to the
active induced graph, retaining arbitrary fixed parent hubs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_rows_with_spokes_order_mono
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h h':ℕ) (hh:h≤h') (A:Finset V)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color) (err:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h' A p k q s a j err σ H):
    MarkedRowsWithSpokes P π d h A p k q s a j err σ H:=by
  intro S T J hS hT hJ hinj
  exact hr S T J (hS.trans hh) (hT.trans hh) (hJ.trans hh) hinj

theorem marked_parent_to_active_rows
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d h:ℕ) (hh:1≤h)
    (I T:Finset V) (himage:Finset.univ.image f=I\T)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color) (err t:ℝ)
    (herr:err≤(t/8)*Fintype.card W)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h (I\T) p k q s a j err σ H):
    MarkedRowsWithSpokes (P.comap f) ρ d 1 Finset.univ p k
      (fun u=>q (g u)) (fun u=>s (g u)) a j ((t/8)*Fintype.card W)
      (rawMarkedRestrictPair f g σ) (fun b x u=>H b (f x) (g u)):=by
  have hr':=hr
  rw [←himage] at hr'
  have he:=markedRowsWithSpokes_embedding f g π ρ hf P d h Finset.univ p k q s a j err σ H hr'
  have he':=marked_rows_with_spokes_order_mono (P.comap f) ρ d 1 h hh Finset.univ p k
    (fun u=>q (g u)) (fun u=>s (g u)) a j err (rawMarkedRestrictPair f g σ)
    (fun b x u=>H b (f x) (g u)) he
  exact marked_rows_with_spokes_tolerance_mono (P.comap f) ρ d 1 Finset.univ p k
    (fun u=>q (g u)) (fun u=>s (g u)) a j err ((t/8)*Fintype.card W)
    (rawMarkedRestrictPair f g σ) (fun b x u=>H b (f x) (g u)) herr he'
end Oberwolfach
