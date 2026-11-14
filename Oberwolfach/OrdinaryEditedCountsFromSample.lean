module

public import Oberwolfach.OrdinaryEditedIsolatorFromPotential
public import Oberwolfach.OrdinaryEditedTransferFromPotential
public import Oberwolfach.OrdinaryForcedRootDeletionDegree
public import Oberwolfach.OrdinarySampleEditDegrees

@[expose] public section
/-! Derive both parent configuration counts from root-omitted sampled
potentials and bounded symmetric edits, including added rim/spoke roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 2048
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_edited_configuration_counts_from_sample
    (P Q F:SimpleGraph V) (H₀ H:V→U→Prop) (r k:ℕ) (hr:3≤r) (hk:4≤k)
    (θ α β₀ β d:ℝ) (σ:Sym2 V→Bool) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (hd:0≤d) (hQP:Q≤P\F)
    (hI:∀x y,x≠y→¬F.Adj x y→β₀≤ordinaryIsolatorPotential P F H₀ k θ α x y σ)
    (hT:∀v u u',u≠u'→β₀≤transferSurvivalSum r hr P F (transferRootCompletedSpokes H₀ v) v u u' σ)
    (hR:∀v,((changed ((retainedGraph P σ).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤d)
    (hRow:∀v,((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v))).card:ℝ)≤d)
    (hCol:∀u,((changed (Finset.univ.filter (fun v=>H₀ v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤d)
    (hsmallI:8*(d+1)≤(β₀-β)*Fintype.card V)
    (hsmallT:5*(r:ℝ)^4*(d+1)≤(β₀-β)*Fintype.card V):
    (∀x y,Q.Adj x y→β*(Fintype.card V:ℝ)^(k-1)≤
      (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ)) ∧
    (∀v (i j:{u // H v u}),i.val≠j.val→β*(Fintype.card V:ℝ)^(r^2)≤
      (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ)):=by
  have hbase:=ordinary_lost_rim_degree_from_sample_edit (retainedGraph P σ) Q F d hR
  have hrow:=ordinary_lost_spoke_rows_from_sample_edit H₀ H d hRow
  have hcol:=ordinary_lost_spoke_columns_from_sample_edit H₀ H d hCol
  have hcomplete:=ordinary_completed_root_lost_spoke_column H₀ H d hcol
  have hD:∀x y,Q.Adj x y→∀v,
      (((retainedGraph P (Function.update σ s(x,y) true)\F)\Q).degree v:ℝ)≤d+1:=by
    intro x y hxy
    exact ordinary_forced_root_deletion_degree P Q F σ x y hxy.ne d hbase
  have hDbase:∀v,(((retainedGraph P σ\F)\Q).degree v:ℝ)≤d+1:=fun v=>(hbase v).trans (by linarith)
  have hrow':∀v,(∑u,bipAdj (fun v u=>H₀ v u∧¬H v u) v u)≤d+1:=fun v=>(hrow v).trans (by linarith)
  have hcol':∀u,(∑v,bipAdj (fun v u=>H₀ v u∧¬H v u) v u)≤d+1:=fun u=>(hcol u).trans (by linarith)
  constructor
  · apply ordinary_edited_isolator_count_from_potential P Q F H₀ H k hk θ α β₀ β (d+1) σ hn hu hQP
    · intro x y hxy
      exact hI x y hxy.ne (hQP hxy).2
    · exact hD
    · exact hrow'
    · exact hcol'
    · exact hsmallI
  · exact ordinary_edited_transfer_count_from_potential P Q F H₀ H r hr β₀ β (d+1) σ hn (by linarith)
      hT hDbase hcomplete hsmallT
end Oberwolfach
