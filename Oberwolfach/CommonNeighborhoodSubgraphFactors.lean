module

public import Oberwolfach.CommonNeighborhoodConflictFreeFactors
public import Oberwolfach.RestrictedRegularSubgraphFactors

@[expose] public section
/-! Apply the regular-host two-factor construction inside the intersection
of two large sets, avoiding a further forbidden set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_subgraph_common_neighborhood_conflict_free_factors (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1) (s:ℕ) (hdivs:(m+1)∣s):
    ∃ ξ:ℝ,0<ξ ∧ ∃ k:ℕ,(m+1)∣k ∧ ∀ L t:ℝ,0≤L→0≤t→∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V] (G Q F:SimpleGraph V) (D:ℕ),
    G.IsRegularOfDegree D→Q≤G→(∀ v,((G\Q).degree v:ℝ)≤t)→(∀ v,(F.degree v:ℝ)≤L)→∀ (A₁ A₂ C T:Finset V),
    let B:=(A₁∩A₂)\C;
    N≤B.card→T⊆B→T.card=s→(∀ x∈T,∀ y∈T,¬F.Adj x y)→
    ((Finset.univ\A₁).card:ℝ)≤ξ*Fintype.card V→
    ((Finset.univ\A₂).card:ℝ)≤ξ*Fintype.card V→
    (C.card:ℝ)≤ξ*Fintype.card V→
    cycleThreshold (m+1)+α≤(D:ℝ)/Fintype.card V→
    ConflictFreeRootSeparatedCycleFactorPair (Q.induce (B:Set V)) (F.induce (B:Set V)) (T.subtype (fun v=>v∈B)) (m+1) k:=by
  obtain ⟨η,hη,k,hk,hbase⟩:=restricted_regular_subgraph_conflict_free_separated_factors m hm α hα hα1 s hdivs
  let ζ:=min (η/2) 1
  have hζ:0<ζ:=lt_min (by positivity) (by norm_num)
  refine ⟨ζ/16,by positivity,k,hk,?_⟩
  intro L t hL ht
  obtain ⟨N,hbase⟩:=hbase L hL
  obtain ⟨Nt,hNt⟩:=eventually_constant_le_linear t (η/2) (by positivity)
  refine ⟨max N Nt,?_⟩
  intro V _ _ G Q F D hreg hQ hdel hF A₁ A₂ C T B hB hTB hT hTfree h₁ h₂ hC hθ
  have hmiss:=common_domain_near_regular_budget A₁ A₂ C ζ hζ.le (min_le_right _ _) (by convert h₁ using 1 <;> ring)
    (by convert h₂ using 1 <;> ring) (by convert hC using 1 <;> ring)
  have hζle:ζ≤η/2:=min_le_left _ _
  have hmiss':((Fintype.card V-B.card:ℕ):ℝ)+t≤η*B.card:=by
    have hh:=mul_le_mul_of_nonneg_right hζle (Nat.cast_nonneg (α:=ℝ) B.card)
    have htB:=hNt B.card (by omega)
    linarith
  exact hbase V G Q F D hreg hQ hF B T t hdel (by omega) hTB hT hTfree hmiss' hθ
end Oberwolfach
