module

public import Oberwolfach.FixedDomainNeighbourhoodStability

@[expose] public section

/-! Stability from realised neighbourhood changes restricted to the fixed
counting domain. Changes to edges outside that domain are unrestricted. Density targets and normalising domains are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_relative_counts_under_domain_changes (P Q Q' F:SimpleGraph V) (H H':V→U→Prop)
    (A:Finset V) (q p ε ε' L:ℝ) (hL:0≤L)
    (hrowbudget:ε*A.card+3*L≤ε'*A.card)
    (hindexbudget:ε*Fintype.card U+3*L≤ε'*Fintype.card U)
    (hQ:∀ v,((changed (A∩Q.neighborFinset v) (A∩Q'.neighborFinset v)).card:ℝ)≤L)
    (hHr:∀ v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (H' v))).card:ℝ)≤L)
    (hHc:∀ u,((changed (A∩Finset.univ.filter (fun v=>H v u)) (A∩Finset.univ.filter (fun v=>H' v u))).card:ℝ)≤L)
    (hrow:∀ S:Finset V,∀ J:Finset U,S.card≤2 → J.card≤1 →
      |((common (common A S (fun v=>Q.neighborFinset v)) J
        (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)-
        q^S.card*p^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε*A.card)
    (hindex:∀ S:Finset V,S.card≤3 → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
      |((common Finset.univ S (fun v=>Finset.univ.filter (H v))).card:ℝ)-p^S.card*Fintype.card U|≤ε*Fintype.card U):
    (∀ S:Finset V,∀ J:Finset U,S.card≤2 → J.card≤1 →
      |((common (common A S (fun v=>Q'.neighborFinset v)) J
        (fun u=>Finset.univ.filter (fun v=>H' v u))).card:ℝ)-
        q^S.card*p^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε'*A.card) ∧
    (∀ S:Finset V,S.card≤3 → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
      |((common Finset.univ S (fun v=>Finset.univ.filter (H' v))).card:ℝ)-p^S.card*Fintype.card U|≤ε'*Fintype.card U):=by
  constructor
  · intro S J hS hJ
    have hh:=fixed_domain_mixed_target_stability A S J
      (fun v=>Q.neighborFinset v) (fun v=>Q'.neighborFinset v)
      (fun u=>Finset.univ.filter (fun v=>H v u)) (fun u=>Finset.univ.filter (fun v=>H' v u))
      L L (q^S.card*p^J.card*(common A S (fun v=>P.neighborFinset v)).card) (ε*A.card)
      (fun v _=>hQ v) (fun u _=>hHc u) (hrow S J hS hJ)
    have hs:(S.card:ℝ)≤2:=by exact_mod_cast hS
    have hj:(J.card:ℝ)≤1:=by exact_mod_cast hJ
    have hl:=mul_le_mul_of_nonneg_right (add_le_add hs hj) hL
    linarith only [hh,hl,hrowbudget]
  · intro S hS hI
    have hh:=target_stability (neighbourhood_stability Finset.univ S
      (fun v=>Finset.univ.filter (H v)) (fun v=>Finset.univ.filter (H' v)) L (fun v _=>hHr v))
      (hindex S hS hI)
    have hs:(S.card:ℝ)≤3:=by exact_mod_cast hS
    have hl:=mul_le_mul_of_nonneg_right hs hL
    linarith only [hh,hl,hindexbudget]

end Oberwolfach
