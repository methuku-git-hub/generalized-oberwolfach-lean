module

public import Oberwolfach.MarkedInnerSpokeColumnFromCorrection
public import Oberwolfach.MarkedInnerChangeZeroOnProtectedRoots
public import Oberwolfach.MarkedInnerBalanceLocalizedChanges
public import Oberwolfach.MarkedRestrictedBalanceArbitraryChanges
public import Oberwolfach.MarkedRestrictedBalanceOfFinite
public import Oberwolfach.MarkedRestrictedSampleBalance

@[expose] public section
/-! Transfer the finite inner balance using changes restricted to the actual
opposite domains, rather than ambient change-graph degrees. The three local
change bounds remain explicit and must be proved for the selected correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_inner_balance_from_protected_correction
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (A:Finset V) (B:Finset U)
    (η δR δS:ℝ) (hη:0≤η) (hR0:0≤δR) (hS0:0≤δS)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hTypes:∀v u,¬(H false v u∧H true v u))
    (hTypes':∀v u,¬(H' false v u∧H' true v u))
    (hrim:∀mark x y,x∈A→y∈A→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1))
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
    (∀z i,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B z i|≤η)→
    ∀z i,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m A B z i|≤η+2*δR+(m+2:ℕ)*δS :=by
  intro E K S E' K' S' hfinite
  obtain ⟨hRzero,hrowzero,_⟩:=marked_inner_change_zero_on_protected_roots P π d A B σ τ H H' hrim hspoke
  have hR:∀mark incoming v,
      |(markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) mark incoming v A:ℝ)-
        (markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming v A:ℝ)|≤δR:=by
    intro mark incoming v
    by_cases hv:v∈A
    · rw [hRzero mark incoming v hv,sub_self,abs_zero]
      exact hR0
    · exact hRoutside mark incoming v hv
  have hrow:∀b v,(∑u∈B,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)≤δS:=by
    intro b v
    by_cases hv:v∈A
    · rw [hrowzero b v hv]
      exact hS0
    · cases b with
      | false => exact hrowOutside v hv
      | true =>
        have hz:(∑u∈B,if ¬(H true v u↔H' true v u) then (1:ℝ) else 0)=0:=by
          apply Finset.sum_eq_zero
          intro u hu
          simp [hmark v u]
        simpa only [hz] using hS0
  have hcol:=marked_inner_spoke_column_from_correction A H H' δS hS0 hmark hnoNew hloss
  exact marked_inner_balance_with_localized_changes P π d m A B η δR δS hη hR0 hS0 σ τ H H' hTypes hTypes' hR hrow hcol hfinite
end Oberwolfach
