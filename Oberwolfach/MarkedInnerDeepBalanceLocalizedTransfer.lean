module

public import Oberwolfach.MarkedInnerBalanceProtectedCorrection
public import Oberwolfach.MarkedFiniteBalanceTransferPhysicalChanges

@[expose] public section
/-! Transfer relative inner balance using localized changes and transfer the
separate deeper balance using an ambient cap. This avoids scaling the ambient
cap by the inner-set size. The outside-root change bounds are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_inner_deep_balance_localized_transfer
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (A T:Finset V) (B R:Finset U)
    (etaBal x ζ δR δS:ℝ) (hη:0<etaBal) (hx:0<x) (hζ:0≤ζ) (hR0:0≤δR) (hS0:0≤δS)
    (hglobalBudget:((m+4:ℕ):ℝ)*ζ≤x/4)
    (hlocalBudget:2*δR+((m+2:ℕ):ℝ)*δS≤min ((x/4)*Fintype.card V) ((etaBal/2)*A.card))
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hTypes:∀v u,¬(H false v u∧H true v u))
    (hTypes':∀v u,¬(H' false v u∧H' true v u))
    (hRgraph:∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hSgraph:∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V) (hFS:∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V)
    (hrim:∀mark v w,v∈A→w∈A→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark v w=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark v w=1))
    (hspoke:∀b v u,v∈A→u∈B→(H b v u↔H' b v u))
    (hRoutside:∀mark incoming v,v∉A→
      |(markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) mark incoming v A:ℝ)-
        (markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming v A:ℝ)|≤δR)
    (hrowOutside:∀v,v∉A→(∑u∈B,if ¬(H false v u↔H' false v u) then (1:ℝ) else 0)≤δS)
    (hmark:∀v u,H true v u↔H' true v u)
    (hnoNew:∀u v,v∈A→H' false v u→H false v u)
    (hloss:∀u,((A.filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤δS):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let S':=Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2);
    (∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B v j|≤(x/4)*Fintype.card V)→
    (∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B v j|≤(etaBal/2)*A.card)→
    (∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m T R v j|≤(x/4)*Fintype.card V)→
    ∃errI errT:ℝ,0≤errT ∧ errI≤(x/2)*Fintype.card V ∧ errT≤(x/2)*Fintype.card V ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m A B v j|≤errI) ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m T R v j|≤errT) ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m A B v j|≤etaBal*A.card) :=by
  intro E K S E' K' S' hI hIrel hT
  let eI:ℝ:=min ((x/4)*Fintype.card V) ((etaBal/2)*A.card)
  let loss:ℝ:=2*δR+((m+2:ℕ):ℝ)*δS
  let eT:ℝ:=(x/4)*Fintype.card V+((m+4:ℕ):ℝ)*ζ*Fintype.card V
  have heI:0≤eI:=by dsimp [eI];positivity
  have hzero:0≤ζ*Fintype.card V:=by positivity
  have hIold:∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B v j|≤eI:=by
    intro v j
    exact le_min (hI v j) (hIrel v j)
  have hInew:=marked_inner_balance_from_protected_correction P π d m A B eI δR δS heI hR0 hS0 σ τ H H'
    hTypes hTypes' hrim hspoke hRoutside hrowOutside hmark hnoNew hloss hIold
  have hTnew:=marked_finite_balance_transfer_after_physical_changes P π d m T R ((x/4)*Fintype.card V)
    (ζ*Fintype.card V) (ζ*Fintype.card V) (by positivity) hzero hzero σ τ H H' FR FS hTypes hTypes' hRgraph hSgraph hFR hFS hT
  have hTbound:eT≤(x/2)*Fintype.card V:=by
    dsimp [eT]
    have hh:=mul_le_mul_of_nonneg_right hglobalBudget (show (0:ℝ)≤Fintype.card V by positivity)
    nlinarith
  have hIambient:eI+loss≤(x/2)*Fintype.card V:=by
    have hh:=min_le_left ((x/4)*Fintype.card V) ((etaBal/2)*A.card)
    have hl:=hlocalBudget.trans (min_le_left _ _)
    dsimp only [eI,loss] at *
    linarith
  have hIrelative:eI+loss≤etaBal*A.card:=by
    have hh:=min_le_right ((x/4)*Fintype.card V) ((etaBal/2)*A.card)
    have hl:=hlocalBudget.trans (min_le_right _ _)
    dsimp only [eI,loss] at *
    linarith
  refine ⟨eI+loss,eT,by dsimp [eT];positivity,hIambient,hTbound,?_,?_,?_⟩
  · simpa only [loss,←add_assoc] using hInew
  · intro v j
    have hh:=hTnew v j
    convert hh using 1 <;> dsimp [eT] <;> push_cast <;> ring
  · intro v j
    exact (hInew v j).trans (by simpa only [loss,←add_assoc] using hIrelative)
end Oberwolfach
