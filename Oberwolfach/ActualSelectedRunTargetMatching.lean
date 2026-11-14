module

public import Oberwolfach.ActualSelectedRunProperties
public import Oberwolfach.DisjointActualWalkMatching
public import Oberwolfach.SimpleWalkLengthEmbeddingGetVert

@[expose] public section
/-! Match the actual selected source runs to disjoint simple target walks,
without any extra source-disjointness assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_selected_runs_match_target_walks
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (H:SimpleGraph V)
    (u v:SelectedRunIndex data.s₂ data.d data.T→V)
    (q:∀r,H.Walk (u r) (v r)) (hq:∀r,(q r).IsPath)
    (hlen:∀r,(q r).length=(data.path (.inr r)).length)
    (hqdis:∀r s,r≠s→Disjoint (q r).support.toFinset (q s).support.toFinset):
    ∃φ:{x // x∈Finset.univ.biUnion (fun r:SelectedRunIndex data.s₂ data.d data.T=>(data.path (.inr r)).support.toFinset)}↪V,
      ∀r (k:Fin ((data.path (.inr r)).length+1)),
        φ ⟨(data.path (.inr r)).getVert k.val,
          Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,List.mem_toFinset.mpr ((data.path (.inr r)).getVert_mem_support _)⟩⟩=
          (q r).getVert k.val:=by
  classical
  have hsource:=actual_selected_runs_are_disjoint_simple_paths data
  obtain ⟨φ,hφ⟩:=disjoint_simple_walk_families_match G H
    (fun r=>data.start (.inr r)) (fun r=>data.finish (.inr r))
    (fun r=>data.path (.inr r)) hsource.1 u v q hq hlen hsource.2 hqdis
  refine ⟨φ,?_⟩
  intro r k
  have hh:=hφ r k
  simpa only [simple_walk_length_embedding_getVert] using hh
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_selected_runs_match_directed_target_walks
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (H:SimpleGraph V)
    (u v:SelectedRunIndex data.s₂ data.d data.T→V)
    (q:∀r,H.Walk (u r) (v r)) (hq:∀r,(q r).IsPath)
    (hlen:∀r,(q r).length=(data.path (.inr r)).length)
    (hqdis:∀r s,r≠s→Disjoint (q r).support.toFinset (q s).support.toFinset)
    (A:Finset (V×V)) (hdir:∀r k,k<(q r).length→((q r).getVert k,(q r).getVert (k+1))∈A):
    ∃φ:{x // x∈Finset.univ.biUnion (fun r:SelectedRunIndex data.s₂ data.d data.T=>(data.path (.inr r)).support.toFinset)}↪V,
      (∀r (k:Fin ((data.path (.inr r)).length+1)),
        φ ⟨(data.path (.inr r)).getVert k.val,
          Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,List.mem_toFinset.mpr ((data.path (.inr r)).getVert_mem_support _)⟩⟩=
          (q r).getVert k.val) ∧
      (∀r k,(hk:k<(data.path (.inr r)).length)→
        (φ ⟨(data.path (.inr r)).getVert k,Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,List.mem_toFinset.mpr ((data.path (.inr r)).getVert_mem_support _)⟩⟩,
         φ ⟨(data.path (.inr r)).getVert (k+1),Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,List.mem_toFinset.mpr ((data.path (.inr r)).getVert_mem_support _)⟩⟩)∈A):=by
  obtain ⟨φ,hφ⟩:=actual_selected_runs_match_target_walks data H u v q hq hlen hqdis
  refine ⟨φ,hφ,?_⟩
  intro r k hk
  have h₁:=hφ r ⟨k,by omega⟩
  have h₂:=hφ r ⟨k+1,by omega⟩
  dsimp only [Fin.val_mk] at h₁ h₂
  rw [h₁,h₂]
  apply hdir
  rw [hlen]
  exact hk
end Oberwolfach
