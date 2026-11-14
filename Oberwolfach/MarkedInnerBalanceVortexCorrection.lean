module

public import Oberwolfach.MarkedInnerSpokeColumnVortexBudget
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

theorem marked_inner_balance_from_vortex_correction
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (A:Finset V) (B:Finset U)
    (D mm:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε mm) (hA:A=Q.extendedVertices 1)
    (hε:0<ε) (hmm:0<mm) (η δR cap ζ Pbudget L:ℝ) (hη:0≤η) (hR0:0≤δR) (hcap:0≤cap)
    (hζ:ζ≤cap/128) (hP:Pbudget≤cap*(ε*Fintype.card V)/128) (hL:2*L≤cap*(ε*Fintype.card V)/128)
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
    (hrowOutside:∀v,v∉A→(∑u∈B,if ¬(H false v u↔H' false v u) then (1:ℝ) else 0)≤cap*(A.card:ℝ))
    (hmark:∀v u,H true v u↔H' true v u)
    (hnoNew:∀u v,v∈A→H' false v u→H false v u)
    (hloss:∀u,((A.filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤ζ*(A.card:ℝ)+Pbudget+2*L):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let S':=Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2);
    (∀z i,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B z i|≤η)→
    ∀z i,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m A B z i|≤η+2*δR+(m+2:ℕ)*(cap*(A.card:ℝ)) :=by
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
  have hS0:0≤cap*(A.card:ℝ):=by positivity
  have hrow:∀b v,(∑u∈B,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)≤cap*(A.card:ℝ):=by
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
  have hcol:∀b u,(∑v∈A,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)≤cap*(A.card:ℝ):=by
    subst A
    exact marked_inner_spoke_column_vortex_budget P D mm β ε Q hε hmm H H' cap ζ Pbudget L hcap hζ hP hL hmark hnoNew hloss
  exact marked_inner_balance_with_localized_changes P π d m A B η δR (cap*(A.card:ℝ)) hη hR0 hS0 σ τ H H' hTypes hTypes' hR hrow hcol hfinite
end Oberwolfach
