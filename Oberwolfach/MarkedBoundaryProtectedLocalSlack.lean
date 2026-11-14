module

public import Oberwolfach.MarkedBoundaryProtectedLocalTransfer
public import Oberwolfach.MarkedBoundaryRimLocalChanges
public import Oberwolfach.MarkedBoundarySpokeLocalChanges

@[expose] public section
/-! Transfer the actual boundary tests from the protected correction using
only outside-inner rim changes and first-inner spoke losses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_boundary_protected_local_with_slack
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (I A:Finset V) (J B:Finset U)
    (hAI:A⊆I) (hBJ:B⊆J) (hπ:∀v,π v∈I↔v∈I)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (errR errI c x:ℝ) (hc:0≤c) (hx:0<x) (hcost:2*(h:ℝ)*c≤x/4)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A p k q s g j errR σ H)
    (hi:MarkedIndicesWithSpokes π d h B q s g j errI σ H)
    (herrR:0≤errR) (herrI:0≤errI)
    (hboundR:errR≤(x/4)*Fintype.card V) (hboundI:errI≤(x/4)*Fintype.card V)
    (FR:SimpleGraph V)
    (hrim:∀mark v w,v∈I→w∈I→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark v w=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark v w=1))
    (hchange:∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hFR:∀v,v∉I→(FR.degree v:ℝ)≤c*(I.card:ℝ))
    (hspoke:∀b v u,v∈I→u∈J→(H b v u↔H' b v u))
    (hrowOutside:∀v,v∉I→(∑u∈J,if ¬(H false v u↔H' false v u) then (1:ℝ) else 0)≤c*(I.card:ℝ))
    (hmark:∀v u,H true v u↔H' true v u)
    (hnoNew:∀u v,v∈I→H' false v u→H false v u)
    (hloss:∀u,((I.filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤c*(I.card:ℝ)):
    ∃eR eI:ℝ,0≤eR ∧ 0≤eI ∧ eR≤(x/2)*Fintype.card V ∧ eI≤(x/2)*Fintype.card V ∧
      MarkedRowsWithSpokes P π d h A p k q s g j eR τ H' ∧
      MarkedIndicesWithSpokes π d h B q s g j eI τ H' :=by
  let δ:ℝ:=c*(I.card:ℝ)
  have hδ:0≤δ:=by dsimp [δ];positivity
  have hcard:(I.card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ I
  have hcostn:=mul_le_mul_of_nonneg_right hcost (show (0:ℝ)≤I.card by positivity)
  have hscale:=mul_le_mul_of_nonneg_left hcard (show (0:ℝ)≤x/4 by positivity)
  have hrate:2*(h:ℝ)*δ≤(x/4)*Fintype.card V:=by dsimp [δ];nlinarith
  have hrateI:(h:ℝ)*δ≤(x/4)*Fintype.card V:=by
    have hh:0≤(h:ℝ)*δ:=by positivity
    linarith
  have hh:=marked_boundary_protected_local_transfer P π d h I A J B hAI hBJ hπ p k q s g j errR errI δ δ hδ hδ σ τ H H' hr hi FR hrim hchange hFR hspoke hrowOutside hmark hnoNew hloss
  refine ⟨errR+h*(δ+δ),errI+h*δ,?_,?_,?_,?_,hh.1,hh.2⟩
  · positivity
  · positivity
  · nlinarith [hboundR,hrate]
  · nlinarith [hboundI,hrateI]
end Oberwolfach
