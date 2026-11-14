module

public import Oberwolfach.MarkedLevelFiniteBalanceBound
public import Oberwolfach.MarkedFinitePhysicalIncidenceBound
public import Oberwolfach.MarkedFiniteFullBalanceBridge
public import Oberwolfach.MarkedCanonicalDeletedBalanceValues
public import Oberwolfach.MarkedFiniteDomainBalanceBounds

@[expose] public section
/-! Physical degree bounds on a correction give a balance estimate at every
root of any fixed domain, including roots outside the protected pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_correction_balance_from_physical_degrees
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (X:Finset V) (Z:Finset U) (err δ:ℝ) (hδ:0≤δ):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∀ (DA:Finset (E⊕K)) (DS:Finset (V×U)),DS⊆S→
    (∀ v,((markedSampleArcSetGraph P π d σ DA).degree v:ℝ)≤δ)→
    (∀ z,((markedFiniteSpokeGraph DS).degree z:ℝ)≤δ)→
    MarkedLevelFiniteBalanceBound P π d m X Z err σ H →
    MarkedLevelFiniteBalanceBound P π d m X Z (err+(m+2)*(4*δ))
      (rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ DA).edgeFinset)
      (markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)) := by
  intro E K S DA DS hDS hRim hSpoke hBal
  have hA:=marked_finite_physical_incidence_bound P π d σ DA δ hRim
  have hrow:∀v,((DS.filter (fun s=>s.1=v)).card:ℝ)≤4*δ:=by
    intro v
    have heq:((DS.filter (fun s=>s.1=v)).card:ℝ)=((markedFiniteSpokeGraph DS).degree (Sum.inl v):ℝ):=by
      rw [markedFiniteSpokeGraph_degree_row]
      have hh:=finite_spoke_relation_row_count (fun v u=>(v,u)∈DS) v
      simp only [Prod.mk.eta,Finset.filter_univ_mem] at hh
      calc
        _ = ∑ u,if (v,u)∈DS then (1:ℝ) else 0 := by
          convert hh using 1 <;> congr! <;> apply Subsingleton.elim
        _ = _ := Finset.sum_boole _ _
    rw [heq]; linarith [hSpoke (Sum.inl v)]
  have hcol:∀u,((DS.filter (fun s=>s.2=u)).card:ℝ)≤4*δ:=by
    intro u
    have heq:((DS.filter (fun s=>s.2=u)).card:ℝ)=((markedFiniteSpokeGraph DS).degree (Sum.inr u):ℝ):=by
      rw [markedFiniteSpokeGraph_degree_col]
      have hh:=finite_spoke_relation_col_count (fun v u=>(v,u)∈DS) u
      simp only [Prod.mk.eta,Finset.filter_univ_mem] at hh
      calc
        _ = ∑ v,if (v,u)∈DS then (1:ℝ) else 0 := by
          convert hh using 1 <;> congr! <;> apply Subsingleton.elim
        _ = _ := Finset.sum_boole _ _
    rw [heq]; linarith [hSpoke (Sum.inr u)]
  intro z i
  rw [(marked_canonical_deleted_balance_values P π d m σ H DA DS X Z z i).2,
    markedFiniteDomainBalance_sdiff _ _ _ _ _ Finset.univ DA S DS m X Z (Finset.subset_univ _) hDS]
  exact (abs_sub _ _).trans (add_le_add (hBal z i)
    (markedFiniteDomainBalance_bound (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) DA DS m X Z (4*δ) (by positivity) hA hrow hcol z i))
end Oberwolfach
