module

public import Oberwolfach.IndependentNeighbourhoodRetention
public import Oberwolfach.FixedDomainNeighbourhoodStability

@[expose] public section

/-! The support sizes, intersections and memberships in the boundary
reservation share the same physical-edge sample. The fixed domains precede
the sample; no independence between the resulting graph events is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem common_neighbourhood_singleton (G:SimpleGraph V) (A:Finset V) (x:V):
    common A {x} (fun v=>G.neighborFinset v)=A∩G.neighborFinset x:=by
  ext v;simp only [mem_common_iff,Finset.mem_singleton,forall_eq,Finset.mem_inter]

theorem common_neighbourhood_pair (G:SimpleGraph V) (A:Finset V) (x y:V):
    common A {x,y} (fun v=>G.neighborFinset v)=(A∩G.neighborFinset x)∩(A∩G.neighborFinset y):=by
  ext v;simp only [mem_common_iff,Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,
    forall_eq,Finset.mem_inter];tauto

theorem boundary_support_memberships (G:SimpleGraph V) (A R:Finset V) (v:V) (hv:v∈A):
    (R.filter (fun x=>v∈A∩G.neighborFinset x))=R∩G.neighborFinset v:=by
  ext x
  simp only [Finset.mem_filter,Finset.mem_inter,SimpleGraph.mem_neighborFinset,hv,true_and]
  exact and_congr_right (fun _=>G.adj_comm x v)

theorem fresh_boundary_support_common_event (ε:ℝ) (hε:0<ε) (q:ℕ):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (G:SimpleGraph V) (A R:Finset V) (τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
      1-1/(Fintype.card V:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin τ hτ hτ1)).probability
        (fun σ=>
          (∀ x,|((A∩(retainedGraph G σ).neighborFinset x).card:ℝ)-
            τ*(A∩G.neighborFinset x).card|<ε*Fintype.card V) ∧
          (∀ x y,x≠y→
            |(((A∩(retainedGraph G σ).neighborFinset x)∩(A∩(retainedGraph G σ).neighborFinset y)).card:ℝ)-
              τ^2*((A∩G.neighborFinset x)∩(A∩G.neighborFinset y)).card|<ε*Fintype.card V) ∧
          (∀ v∈A,|((R.filter (fun x=>v∈A∩(retainedGraph G σ).neighborFinset x)).card:ℝ)-
              τ*(R∩G.neighborFinset v).card|<ε*Fintype.card V)):=by
  obtain ⟨N,hN⟩:=retained_common_neighbourhoods_common_event 2 q ε hε
  refine ⟨max 2 N,?_⟩
  intro V _ _ hn G A R τ hτ hτ1
  let D:Fin 2→Finset V:=![A,R]
  have hh:=hN V (by omega) G 2 (by omega) D τ hτ hτ1
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  refine ⟨?_,?_,?_⟩
  · intro x
    have hh:=hσ 0 {x} (by simp)
    simpa only [D,Matrix.cons_val_zero,common_neighbourhood_singleton,Finset.card_singleton,pow_one] using hh
  · intro x y hxy
    have hh:=hσ 0 {x,y} (by simp [hxy])
    simpa only [D,Matrix.cons_val_zero,common_neighbourhood_pair,
      Finset.card_pair hxy] using hh
  · intro v hv
    have hh:=hσ 1 {v} (by simp)
    rw [boundary_support_memberships (retainedGraph G σ) A R v hv]
    simpa only [D,Matrix.cons_val_one,Matrix.cons_val_zero,common_neighbourhood_singleton,Finset.card_singleton,pow_one] using hh

theorem boundary_support_bounds_of_counts (G G':SimpleGraph V) (A R:Finset V) (τ ε:ℝ)
    (hτ:0≤τ)
    (hrow:∀ x,|((A∩G'.neighborFinset x).card:ℝ)-τ*(A∩G.neighborFinset x).card|<ε)
    (hpair:∀ x y,x≠y→
      |(((A∩G'.neighborFinset x)∩(A∩G'.neighborFinset y)).card:ℝ)-
        τ^2*((A∩G.neighborFinset x)∩(A∩G.neighborFinset y)).card|<ε)
    (hcol:∀ v∈A,|((R.filter (fun x=>v∈A∩G'.neighborFinset x)).card:ℝ)-
      τ*(R∩G.neighborFinset v).card|<ε):
    (∀ x,((A∩G'.neighborFinset x).card:ℝ)≤τ*A.card+ε) ∧
    (∀ x y,x≠y→(((A∩G'.neighborFinset x)∩(A∩G'.neighborFinset y)).card:ℝ)≤τ^2*A.card+ε) ∧
    (∀ v∈A,((R.filter (fun x=>v∈A∩G'.neighborFinset x)).card:ℝ)≤τ*R.card+ε):=by
  refine ⟨?_,?_,?_⟩
  · intro x
    have hc:((A∩G.neighborFinset x).card:ℝ)≤A.card:=Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)
    have hd:=(abs_lt.mp (hrow x)).2
    nlinarith only [hd,mul_le_mul_of_nonneg_left hc hτ]
  · intro x y hxy
    have hc:(((A∩G.neighborFinset x)∩(A∩G.neighborFinset y)).card:ℝ)≤A.card:=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_left.trans Finset.inter_subset_left))
    have hd:=(abs_lt.mp (hpair x y hxy)).2
    nlinarith only [hd,mul_le_mul_of_nonneg_left hc (sq_nonneg τ)]
  · intro v hv
    have hc:((R∩G.neighborFinset v).card:ℝ)≤R.card:=Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)
    have hd:=(abs_lt.mp (hcol v hv)).2
    nlinarith only [hd,mul_le_mul_of_nonneg_left hc hτ]


theorem boundary_support_estimates_after_changes (P G G':SimpleGraph V) (A R:Finset V)
    (τ ε L:ℝ)
    (hchange:∀ v,((changed (G.neighborFinset v) (G'.neighborFinset v)).card:ℝ)≤L)
    (hrow:∀ x,|((A∩G.neighborFinset x).card:ℝ)-τ*(A∩P.neighborFinset x).card|≤ε)
    (hpair:∀ x y,x≠y→
      |(((A∩G.neighborFinset x)∩(A∩G.neighborFinset y)).card:ℝ)-
        τ^2*((A∩P.neighborFinset x)∩(A∩P.neighborFinset y)).card|≤ε)
    (hcol:∀ v∈A,|((R.filter (fun x=>v∈A∩G.neighborFinset x)).card:ℝ)-
      τ*(R∩P.neighborFinset v).card|≤ε):
    (∀ x,|((A∩G'.neighborFinset x).card:ℝ)-τ*(A∩P.neighborFinset x).card|≤ε+L) ∧
    (∀ x y,x≠y→
      |(((A∩G'.neighborFinset x)∩(A∩G'.neighborFinset y)).card:ℝ)-
        τ^2*((A∩P.neighborFinset x)∩(A∩P.neighborFinset y)).card|≤ε+2*L) ∧
    (∀ v∈A,|((R.filter (fun x=>v∈A∩G'.neighborFinset x)).card:ℝ)-
      τ*(R∩P.neighborFinset v).card|≤ε+L):=by
  have hsingle (D:Finset V) (x:V):
      |((D∩G'.neighborFinset x).card:ℝ)-(D∩G.neighborFinset x).card|≤L:=by
    have hh:=neighbourhood_stability D {x} (fun v=>G.neighborFinset v) (fun v=>G'.neighborFinset v) L
      (fun v _=>hchange v)
    simpa only [common_neighbourhood_singleton,Finset.card_singleton,Nat.cast_one,one_mul] using hh
  refine ⟨?_,?_,?_⟩
  · intro x;exact target_stability (hsingle A x) (hrow x)
  · intro x y hxy
    have hh:=neighbourhood_stability A {x,y} (fun v=>G.neighborFinset v) (fun v=>G'.neighborFinset v) L
      (fun v _=>hchange v)
    have hdiff:|(((A∩G'.neighborFinset x)∩(A∩G'.neighborFinset y)).card:ℝ)-
        ((A∩G.neighborFinset x)∩(A∩G.neighborFinset y)).card|≤2*L:=by
      simpa only [common_neighbourhood_pair,Finset.card_pair hxy,Nat.cast_ofNat] using hh
    exact target_stability hdiff (hpair x y hxy)
  · intro v hv
    rw [boundary_support_memberships G' A R v hv]
    have hh:=hcol v hv
    rw [boundary_support_memberships G A R v hv] at hh
    exact target_stability (hsingle R v) hh

end Oberwolfach
