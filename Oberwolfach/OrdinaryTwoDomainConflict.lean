module

public import Oberwolfach.OrdinaryTriangleTwoDomainPermutation
public import Oberwolfach.PermutationEmbeddingWindows
public import Oberwolfach.PermutationConflictDegree
public import Oberwolfach.MappedFactorGraph
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section
/-! Enlarge the forbidden graph for the auxiliary sum domain, keeping its
restriction to the original rim vertices and controlling its maximum degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryTwoDomainConflict (F:SimpleGraph V) (σ:Equiv.Perm (V⊕U)) (b:ℕ):SimpleGraph (V⊕U):=
  F.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U)⊔permutationConflictGraph σ b

theorem ordinary_two_domain_conflict_properties
    (F:SimpleGraph V) (π:Equiv.Perm V) (σ:Equiv.Perm (V⊕U)) (b D:ℕ)
    (hcomm:∀v,Sum.inl (π v)=σ (Sum.inl v))
    (hF:permutationConflictGraph π b≤F) (hD:∀v,F.degree v≤D):
    let F':=ordinaryTwoDomainConflict (U:=U) F σ b;
    permutationConflictGraph σ b≤F' ∧
    F'.comap Sum.inl=F ∧
    (∀v,F'.degree v≤D+2*b):=by
  intro F'
  constructor
  · exact le_sup_right
  constructor
  · ext v w
    change (F.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U)).Adj (Sum.inl v) (Sum.inl w) ∨
      (permutationConflictGraph σ b).Adj (Sum.inl v) (Sum.inl w) ↔ F.Adj v w
    have hmap:(F.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U)).Adj (Sum.inl v) (Sum.inl w) ↔ F.Adj v w:=by
      change (F.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U)).Adj
        ((⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U) v) ((⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U) w) ↔ _
      exact SimpleGraph.map_adj_apply
    rw [hmap]
    constructor
    · rintro (hf|hc)
      · exact hf
      · apply hF
        refine ⟨fun h=>hc.1 (congrArg Sum.inl h),?_⟩
        exact (permutationClose_embedding Sum.inl σ π hcomm Sum.inl_injective b v w).mp hc.2
    · exact Or.inl
  · intro v
    have hdeg:=graph_degree_sup_le (F.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U)) (permutationConflictGraph σ b) v
    have hmap:=graph_map_degree_bound F (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U) D hD v
    have hconf:=permutationConflictGraph_degree_le σ b v
    have he:(ordinaryTwoDomainConflict (U:=U) F σ b).degree v≤
        (F.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U)).degree v+(permutationConflictGraph σ b).degree v:=by
      convert hdeg using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
    have hm:((F.map (⟨Sum.inl,Sum.inl_injective⟩:V↪V⊕U)).degree v)≤D:=by
      convert hmap using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
    have hc:((permutationConflictGraph σ b).degree v)≤2*b:=by
      convert hconf using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
    change (ordinaryTwoDomainConflict (U:=U) F σ b).degree v≤D+2*b
    omega
end Oberwolfach
