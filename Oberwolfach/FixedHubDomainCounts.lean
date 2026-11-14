module

public import Oberwolfach.NeighbourPairDomains
public import Oberwolfach.FixedDomainNeighbourhoodStability

@[expose] public section

/-! Exact transport of neighbourhood counts to a fixed hub subtype. The
vertex domain and all external vertex roots are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem common_index_map {I J:Type} [DecidableEq I] [DecidableEq J]
    (A:Finset V) (S:Finset I) (f:I↪J) (N:J→Finset V):
    common A (S.map f) N=common A S (fun i=>N (f i)):=by
  ext v
  simp only [mem_common_iff,Finset.mem_map]
  constructor
  · intro h;exact ⟨h.1,fun i hi=>h.2 (f i) ⟨i,hi,rfl⟩⟩
  · intro h;refine ⟨h.1,?_⟩
    rintro j ⟨i,hi,rfl⟩;exact h.2 i hi

theorem common_hub_domain_card (B:Finset U) (S:Finset V) (H:V→U→Prop):
    (common Finset.univ S (fun v=>Finset.univ.filter (fun u:B=>H v u.val))).card=
      (common B S (fun v=>Finset.univ.filter (H v))).card:=by
  have h₁:common Finset.univ S (fun v=>Finset.univ.filter (fun u:B=>H v u.val))=
      Finset.univ.filter (fun u:B=>∀ v∈S,H v u.val):=by
    ext u;simp [mem_common_iff]
  have h₂:common B S (fun v=>Finset.univ.filter (H v))=
      B.filter (fun u=>∀ v∈S,H v u):=by
    ext u;simp [mem_common_iff]
  rw [h₁,h₂]
  convert finite_domain_predicate_card B (fun u=>∀ v∈S,H v u) using 1 <;> congr!

theorem fixed_domain_neighbourhood_stability {I:Type} (B:Finset U) (S:Finset I)
    (N N':I→Finset U) (L:ℝ)
    (h:∀ i∈S,((changed (B∩N i) (B∩N' i)).card:ℝ)≤L):
    |((common B S N').card:ℝ)-(common B S N).card|≤S.card*L:=by
  have hh:=neighbourhood_stability B S (fun i=>B∩N i) (fun i=>B∩N' i) L h
  simpa only [common_inter_domain B B (Finset.Subset.refl _)] using hh

theorem ordinary_two_domain_counts_under_changes (P Q Q' F:SimpleGraph V) (H H':V→U→Prop)
    (A:Finset V) (B:Finset U) (q p ε ε' L:ℝ) (hL:0≤L)
    (hrowbudget:ε*A.card+3*L≤ε'*A.card)
    (hindexbudget:ε*B.card+3*L≤ε'*B.card)
    (hQ:∀ v,((changed (A∩Q.neighborFinset v) (A∩Q'.neighborFinset v)).card:ℝ)≤L)
    (hHr:∀ v,((changed (B∩Finset.univ.filter (H v)) (B∩Finset.univ.filter (H' v))).card:ℝ)≤L)
    (hHc:∀ u∈B,((changed (A∩Finset.univ.filter (fun v=>H v u)) (A∩Finset.univ.filter (fun v=>H' v u))).card:ℝ)≤L)
    (hrow:∀ S:Finset V,∀ J:Finset U,J⊆B → S.card≤2 → J.card≤1 →
      |((common (common A S (fun v=>Q.neighborFinset v)) J
        (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)-
        q^S.card*p^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε*A.card)
    (hindex:∀ S:Finset V,S.card≤3 → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
      |((common B S (fun v=>Finset.univ.filter (H v))).card:ℝ)-p^S.card*B.card|≤ε*B.card):
    (∀ S:Finset V,∀ J:Finset U,J⊆B → S.card≤2 → J.card≤1 →
      |((common (common A S (fun v=>Q'.neighborFinset v)) J
        (fun u=>Finset.univ.filter (fun v=>H' v u))).card:ℝ)-
        q^S.card*p^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε'*A.card) ∧
    (∀ S:Finset V,S.card≤3 → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
      |((common B S (fun v=>Finset.univ.filter (H' v))).card:ℝ)-p^S.card*B.card|≤ε'*B.card):=by
  constructor
  · intro S J hJB hS hJ
    have hh:=fixed_domain_mixed_target_stability A S J
      (fun v=>Q.neighborFinset v) (fun v=>Q'.neighborFinset v)
      (fun u=>Finset.univ.filter (fun v=>H v u)) (fun u=>Finset.univ.filter (fun v=>H' v u))
      L L (q^S.card*p^J.card*(common A S (fun v=>P.neighborFinset v)).card) (ε*A.card)
      (fun v _=>hQ v) (fun u hu=>hHc u (hJB hu)) (hrow S J hJB hS hJ)
    have hs:(S.card:ℝ)≤2:=by exact_mod_cast hS
    have hj:(J.card:ℝ)≤1:=by exact_mod_cast hJ
    have hl:=mul_le_mul_of_nonneg_right (add_le_add hs hj) hL
    linarith only [hh,hl,hrowbudget]
  · intro S hS hI
    have hh:=target_stability (fixed_domain_neighbourhood_stability B S
      (fun v=>Finset.univ.filter (H v)) (fun v=>Finset.univ.filter (H' v)) L (fun v _=>hHr v))
      (hindex S hS hI)
    have hs:(S.card:ℝ)≤3:=by exact_mod_cast hS
    have hl:=mul_le_mul_of_nonneg_right hs hL
    linarith only [hh,hl,hindexbudget]

end Oberwolfach
