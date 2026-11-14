module

public import Oberwolfach.CommonDomainNearRegularBudget

@[expose] public section
/-! Apply the regular-host two-factor construction inside the intersection
of two large sets, avoiding a further forbidden set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def RootedCycleFactorPair {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (T:Finset V) (r k:ℕ):Prop:=
  ∃ S:Finset V,S.card=k ∧ Disjoint S T ∧
    let R:=S∪T
    let J:=G.induce (R:Set V)
    let S':Finset (R:Set V):=S.subtype (fun v=>v∈R)
    ∃ M₁ M₂:Finset (OrdinaryCycle J r),
      (∀ C∈M₁,∀ E∈M₁,C≠E→Disjoint (ordinaryCycleVertices J r C) (ordinaryCycleVertices J r E)) ∧
      M₁.biUnion (ordinaryCycleVertices J r)=Finset.univ ∧
      (∀ C∈M₂,∀ E∈M₂,C≠E→Disjoint (ordinaryCycleVertices J r C) (ordinaryCycleVertices J r E)) ∧
      M₂.biUnion (ordinaryCycleVertices J r)=S' ∧
      (∀ C∈M₁,∀ E∈M₂,Disjoint C.val.val.edgeFinset E.val.val.edgeFinset) ∧
      (∀ C∈M₁,∀ v w,C.val.val.Adj v w→v∈S' ∨ w∈S')

theorem regular_host_common_neighborhood_rooted_factors (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1) (s:ℕ) (hdivs:(m+1)∣s):
    ∃ ξ:ℝ,0<ξ ∧ ∃ k:ℕ,(m+1)∣k ∧ ∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V] (G:SimpleGraph V) (D:ℕ),
    G.IsRegularOfDegree D→∀ (A₁ A₂ C T:Finset V),
    let B:=(A₁∩A₂)\C;
    N≤B.card→T⊆B→T.card=s→
    ((Finset.univ\A₁).card:ℝ)≤ξ*Fintype.card V→
    ((Finset.univ\A₂).card:ℝ)≤ξ*Fintype.card V→
    (C.card:ℝ)≤ξ*Fintype.card V→
    cycleThreshold (m+1)+α≤(D:ℝ)/Fintype.card V→
    RootedCycleFactorPair (G.induce (B:Set V)) (T.subtype (fun v=>v∈B)) (m+1) k:=by
  obtain ⟨η,hη,k,hk,N,hbase⟩:=restricted_regular_host_rooted_two_factors m hm α hα hα1 s hdivs
  let ζ:=min η 1
  have hζ:0<ζ:=lt_min hη (by norm_num)
  refine ⟨ζ/16,by positivity,k,hk,N,?_⟩
  intro V _ _ G D hreg A₁ A₂ C T B hB hTB hT h₁ h₂ hC hθ
  have hmiss:=common_domain_near_regular_budget A₁ A₂ C ζ hζ.le (min_le_right _ _) (by convert h₁ using 1 <;> ring)
    (by convert h₂ using 1 <;> ring) (by convert hC using 1 <;> ring)
  have hζle:ζ≤η:=min_le_left _ _
  have hmiss':((Fintype.card V-B.card:ℕ):ℝ)≤η*B.card:=
    hmiss.trans (mul_le_mul_of_nonneg_right hζle (Nat.cast_nonneg _))
  exact hbase V G D hreg B T hB hTB hT hmiss' hθ
end Oberwolfach
