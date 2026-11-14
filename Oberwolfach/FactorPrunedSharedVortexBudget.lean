module

public import Oberwolfach.FactorPrunedSharedVortex
public import Oberwolfach.SharedVortexInnerBudget

@[expose] public section
/-! Supply the protected-partition size bound using the first vortex set
of every actual retained class. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
theorem factor_pruned_shared_vortex_partition_budget (K:ℕ) (hK:0<K) (α κL κS β ε:ℝ)
    (hα:0<α) (hL0:0<κL) (hS0:0<κS) (hb:0<β) (he:0<ε) (heq:ε<1/4)
    (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ)))
    (hebudget:((K:ℝ)+1)*ε≤(α/2)/100000) (h:ℕ):
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
      (∀ x j,0<j→j<h→(π^j) x≠x) ∧
      ((∑ a:Fin k,((Q a).vertices 1).card:ℕ):ℝ)≤(α/2)/100000*n := by
  obtain ⟨m₀,hm₀,hv⟩:=factor_pruned_shared_vortex K hK α κL κS β ε
    hα hL0 hS0 hb he heq hL hS h
  refine ⟨m₀,hm₀,?_⟩
  intro m hm W _ n hn hn0 classify D hEven hsize hDn δ hδ hdegree
    fibres cutoff small removed remaining cf D0 fibres0 C k e U R hR
  obtain ⟨Q,π,hpres,heqQ,hshort⟩:=hv m hm hn hn0 classify D hEven hsize hDn δ hδ hdegree R hR
  have hh:=factor_pruned_initial_index_densities hn0 K hK classify D hEven hsize hDn δ α κL κS
    (by linarith) hα hL0 hS0 hL hS hdegree
  have hk:k≤K+1:=hh.2.2.2.1
  refine ⟨Q,π,hpres,heqQ,hshort,?_⟩
  simpa only [Fintype.card_fin] using vortex_first_level_partition_budget he.le hk hebudget Q
end Oberwolfach
