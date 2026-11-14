module

public import Oberwolfach.PrunedInitialIndexDensities
public import Oberwolfach.SharedVortexPermutation
public import Oberwolfach.FactorPrunedProtectedPartition

@[expose] public section
/-! The actual nonempty retained classes admit a common physical vortex and
one preserving permutation, while retaining their own factor-index sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_pruned_shared_vortex (K:ℕ) (hK:0<K) (α κL κS β ε:ℝ)
    (hα:0<α) (hL0:0<κL) (hS0:0<κS) (hb:0<β) (he:0<ε) (heq:ε<1/4)
    (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ))) (h:ℕ):
    ∃ m₀:ℕ,1≤m₀ ∧ ∀ m:ℕ,m₀≤m→∀ {W:Type} [Fintype W] {n:ℕ},m≤n→0<n→
    ∀ (classify:W→Option (Fin K)) (D:ℕ) (hEven:Even D)
      (hsize:Fintype.card W=D/2) (hDn:D≤n) (δ:ℝ) (hδ:1/2≤δ)
      (hdegree:(δ+α)*(n:ℝ)≤D),
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let cutoff:=fun j:Option (Fin K)=>if j=none then κL else κS
    let small:=fun j:Option (Fin K)=>((fibres j).card:ℝ)<cutoff j*n
    let removed:=Finset.univ.filter (fun w=>small (classify w))
    let remaining:={w:W // w∉removed}
    let cf:=fun w:remaining=>classify w.val
    let D0:=D-2*removed.card
    let fibres0:=fun j:Option (Fin K)=>Finset.univ.filter (fun w:remaining=>cf w=j)
    let C:=Finset.univ.filter (fun j=>(fibres0 j).Nonempty)
    let k:=C.card
    let e:Fin k≃↥C:=(Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm;
    let U:=fun a:Fin k=>{w:remaining // cf w=(e a).val};
    ∀ R:SimpleGraph (Fin n),R.IsRegularOfDegree D0→
    ∃ Q:∀ a:Fin k,Vortex (U a) R D0 β ε m,∃ π:Equiv.Perm (Fin n),
      (∀ a i x,π x∈(Q a).extendedVertices i↔x∈(Q a).extendedVertices i) ∧
      (∀ a b,(Q a).toVertexVortex=(Q b).toVertexVortex) ∧
      (∀ x j,0<j→j<h→(π^j) x≠x) := by
  have hr:0<2*min κL κS:=by positivity
  obtain ⟨m₀,hm₀,hv⟩:=shared_vortex_with_permutation_exists hb he heq hr h
  refine ⟨m₀,hm₀,?_⟩
  intro m hm W _ n hn hn0 classify D hEven hsize hDn δ hδ hdegree
    fibres cutoff small removed remaining cf D0 fibres0 C k e U R hR
  have hp:=factor_pruned_initial_index_densities hn0 K hK classify D hEven hsize hDn δ α κL κS
    (by linarith) hα hL0 hS0 hL hS hdegree
  obtain ⟨hD0,hEven0,hk,hkb,hdens⟩:=hp
  letI : Nonempty (Fin k):=⟨⟨0,hk⟩⟩
  have hsmall0:=factor_small_class_budget K hK classify (n:ℝ) α κL κS (by positivity) hα hL0.le hS0.le hL hS
  have hsmall:(removed.card:ℝ)≤α*n/500:=by
    simpa [fibres,cutoff,small,removed,ite_mul] using hsmall0
  have hmarg:(δ+α/2)*(n:ℝ)≤(D0:ℝ):=
    (factor_small_removal_margin D removed.card n δ α (by linarith) hα hdegree hsmall removed.card (le_refl _)).2
  have hmin:(Fintype.card (Fin n):ℝ)/2≤D0:=by
    simp only [Fintype.card_fin]
    have hnR:(0:ℝ)≤n:=by positivity
    nlinarith
  exact hv (Fin n) (Fin k) U R D0 m hR hmin (fun a=>(hdens a).1) (fun a=>(hdens a).2)
    hm (by simpa using hn)
end Oberwolfach
