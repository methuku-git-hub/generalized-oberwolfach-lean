module

public import Oberwolfach.ResidualActualData
public import Oberwolfach.BufferedPathInteriorCompletion

@[expose] public section
/-! Final buffered-path interiors occur among the actual deleted vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_final_path_interiors_are_deleted
    {X I K J:Type} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X) (index:I→data.Z)
    (hstart:∀i,data.start (index i)=inner i 0)
    (hfinish:∀i,data.finish (index i)=inner i (Fin.last (n i)))
    (hsupport:∀i,(data.path (index i)).support=List.ofFn (inner i)):
    bufferedPathStrictInterior n inner⊆data.deletedVertices ∧
      Disjoint (bufferedPathStrictInterior n inner) data.remaining:=by
  classical
  have hsub:bufferedPathStrictInterior n inner⊆data.deletedVertices:=by
    intro x hx
    obtain ⟨i,_,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hx
    have hp0:0<p.val:=(Finset.mem_filter.mp hp).2.1
    have hpn:p.val<n i:=(Finset.mem_filter.mp hp).2.2
    have hs:inner i p∈(data.path (index i)).support.toFinset:=by
      rw [hsupport i]
      exact List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨p,rfl⟩)
    have hne0:inner i p≠data.start (index i):=by
      rw [hstart i]
      intro he
      have hh: p=0:=(inner i).injective he
      have hv:p.val=0:=by simpa only [Fin.val_zero] using congrArg Fin.val hh
      omega
    have hne1:inner i p≠data.finish (index i):=by
      rw [hfinish i]
      intro he
      have hh:p=Fin.last (n i):=(inner i).injective he
      have hv:=congrArg Fin.val hh
      simp at hv
      omega
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨index i,Finset.mem_univ _,Finset.mem_sdiff.mpr ⟨hs,?_⟩⟩
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨hne0,hne1⟩
  refine ⟨hsub,?_⟩
  apply Finset.disjoint_left.mpr
  intro x hx hr
  exact (Finset.mem_sdiff.mp hr).2 (hsub hx)
end Oberwolfach
