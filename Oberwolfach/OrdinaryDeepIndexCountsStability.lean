module

public import Oberwolfach.EndpointDeepCountInputs
public import Oberwolfach.FixedHubDomainCounts

@[expose] public section
/-! The three-root hub common-neighborhood counts survive bounded row edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_index_counts_stability (F:SimpleGraph V) (H J:V→U→Prop)
    (B:Finset U) (pH t L ε:ℝ) (hL:0≤L) (hbudget:t+3*L≤ε*B.card)
    (hJ:∀v,((changed (B∩Finset.univ.filter (H v)) (B∩Finset.univ.filter (J v))).card:ℝ)≤L)
    (hbase:∀S:Finset V,S.card≤3→(∀v∈S,∀w∈S,¬F.Adj v w)→
      |((common B S (fun v=>Finset.univ.filter (H v))).card:ℝ)-pH^S.card*B.card|≤t):
    ∀S:Finset V,S.card≤3→(∀v∈S,∀w∈S,¬F.Adj v w)→
      (pH^S.card-ε)*B.card≤((common B S (fun v=>Finset.univ.filter (J v))).card:ℝ):=by
  intro S hS hfree
  have hnew:=target_stability (fixed_domain_neighbourhood_stability B S
    (fun v=>Finset.univ.filter (H v)) (fun v=>Finset.univ.filter (J v)) L (fun v _=>hJ v))
    (hbase S hS hfree)
  have hs:(S.card:ℝ)*L≤3*L:=mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hL
  nlinarith only [(abs_le.mp hnew).1,hs,hbudget]
end Oberwolfach
