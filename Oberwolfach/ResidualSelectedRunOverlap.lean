module

public import Oberwolfach.ResidualDeletedIndexFinite

@[expose] public section
/-! The previously embedded selected runs meet the surviving vertices only
at prescribed marker vertices. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem residual_selected_run_overlap (F:SimpleGraph V) (s₁ s₂:Finset I)
    (u v:I→V) (P:∀i,F.Walk (u i) (v i)) (c d:ℕ)
    (T:I→Finset ℕ) (hT:∀i∈s₂,T i⊆Finset.range d)
    (Cset Cembed:Finset V) (hC:Cembed⊆Cset):
    let Z:=DeletedPathIndex s₁ s₂ d T
    let U:Z→V:=deletedPathStart F s₁ s₂ u v P c d T
    let W:Z→V:=deletedPathEnd F s₁ s₂ u v P c d T
    let paths:∀z:Z,F.Walk (U z) (W z):=deletedPathWalk F s₁ s₂ u v P c d T hT
    let R:=Finset.univ \ (Cset ∪ Finset.univ.biUnion (fun z=>(paths z).support.toFinset \ {U z,W z}))
    let M:=s₂.biUnion (fun i=>(Finset.range (d+1)).image (fun j=>(P i).getVert (2+c*j)))
    let A₁:=s₁.biUnion (fun i=>{(P i).getVert 2,(P i).getVert (2+c*d)})
    let A₀:=A₁∪(R∩M)
    let X:=A₀ ∪ (Finset.univ.biUnion (fun r:SelectedRunIndex s₂ d T=>(paths (.inr r)).support.toFinset)) ∪ Cembed;
    A₀⊆R→X∩R=A₀ := by
  dsimp only
  intro hA
  ext x
  constructor
  · intro hx
    obtain ⟨hxX,hxR⟩:=Finset.mem_inter.mp hx
    rcases Finset.mem_union.mp hxX with hxleft|hxC
    · rcases Finset.mem_union.mp hxleft with hxA|hxrun
      · exact hxA
      · obtain ⟨⟨i,r⟩,_,hxrun⟩:=Finset.mem_biUnion.mp hxrun
        let z:DeletedPathIndex s₁ s₂ d T:=.inr ⟨i,r⟩
        have hxnot : x∉(deletedPathWalk F s₁ s₂ u v P c d T hT z).support.toFinset \ 
            {deletedPathStart F s₁ s₂ u v P c d T z,deletedPathEnd F s₁ s₂ u v P c d T z} := by
          intro hxint
          have hd: x∈(Finset.univ.biUnion (fun z:DeletedPathIndex s₁ s₂ d T=>
            (deletedPathWalk F s₁ s₂ u v P c d T hT z).support.toFinset \ 
              {deletedPathStart F s₁ s₂ u v P c d T z,deletedPathEnd F s₁ s₂ u v P c d T z})) :=
            Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,hxint⟩
          exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_union_right _ hd)
        have hend:x∈({deletedPathStart F s₁ s₂ u v P c d T z,deletedPathEnd F s₁ s₂ u v P c d T z}:Finset V):=by
          by_contra h
          exact hxnot (Finset.mem_sdiff.mpr ⟨hxrun,h⟩)
        have hr:IsSelectedSegmentRun (T i.1) r.1.1 r.1.2 :=
          (selected_run_mem d (T i.1) (hT i.1 i.2) r.1.1 r.1.2).mp r.2
        have hab:r.1.1≤r.1.2:=hr.1
        have hb:r.1.2<d:=by
          have ht:=hT i.1 i.2 (hr.2.1 r.1.2 hr.1 le_rfl)
          simpa using ht
        have hm:x∈s₂.biUnion (fun j=>(Finset.range (d+1)).image (fun k=>(P j).getVert (2+c*k))) := by
          simp only [Finset.mem_insert,Finset.mem_singleton,z,deletedPathStart,deletedPathEnd] at hend
          apply Finset.mem_biUnion.mpr
          refine ⟨i.1,i.2,?_⟩
          rcases hend with h|h
          · exact Finset.mem_image.mpr ⟨r.1.1,Finset.mem_range.mpr (by omega),h.symm⟩
          · exact Finset.mem_image.mpr ⟨r.1.2+1,Finset.mem_range.mpr (by omega),h.symm⟩
        exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxR,hm⟩)
    · have hxC':x∈Cset:=hC hxC
      exact ((Finset.mem_sdiff.mp hxR).2 (Finset.mem_union_left _ hxC')).elim
  · intro hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hx),hA hx⟩
end Oberwolfach
