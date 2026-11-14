module

public import Oberwolfach.BufferedResidualAvoidsOldImage
public import Oberwolfach.RetainedMarkedRootUniformity
public import Oberwolfach.InnerRequiredRawStateCover

@[expose] public section
/-! The residual ordinary set avoids the occupied old image for the same
retained marked intervals used in the correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_buffered_residual_avoids_occupied
    {V X U:Type} [Fintype V] [Fintype X] [Fintype U]
    [DecidableEq V] [DecidableEq X] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d) (m:ℕ)
    (σ:RawIntervalFamilyOutcome V U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (w:U)
    (inner:∀i:retainedMarkedIndex π d σ false t J w,Fin ((m+1)*d+1)↪X)
    (fC:{x // x∉bufferedPathStrictInterior (fun _=>(m+1)*d) inner}→V)
    (hstart:∀i (h:inner i 0∉bufferedPathStrictInterior (fun _=>(m+1)*d) inner),fC ⟨inner i 0,h⟩=i.val)
    (hfinish:∀i (h:inner i (Fin.last ((m+1)*d))∉bufferedPathStrictInterior (fun _=>(m+1)*d) inner),fC ⟨inner i (Fin.last ((m+1)*d)),h⟩=(π^d) i.val)
    (Old:Finset X) (ψ:X→V)
    (hOld:∀x (hx:x∈Old) (h:x∉bufferedPathStrictInterior (fun _=>(m+1)*d) inner),fC ⟨x,h⟩=ψ x):
    Disjoint ((Finset.univ\(outsideBufferedPathImage (fun _=>(m+1)*d) inner fC ∪
      Finset.univ.image (fun i:retainedMarkedIndex π d σ false t J w=>(π^d) i.val)))\retainedFinalMarkedAt π d σ t J w)
      ((Old\bufferedPathStrictInterior (fun _=>(m+1)*d) inner).image ψ) :=by
  have hY:(Finset.univ.image (fun i:retainedMarkedIndex π d σ false t J w=>i.val))⊆retainedFinalMarkedAt π d σ t J w:=by
    intro x hx
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    have hm:i.val∈markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t J w=>d) Subtype.val:=by
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,?_⟩
      let j:Fin d:=⟨0,by omega⟩
      refine Finset.mem_image.mpr ⟨j,Finset.mem_univ _,?_⟩
      simp [j]
    have hh:=(retained_marked_root_membership π d hd σ false t J w i.val).mp hm
    simpa only [retainedFinalMarkedAt,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  exact buffered_residual_ordinary_avoids_old_image_of_superset (fun _=>(m+1)*d) inner fC
    (fun i=>i.val) (fun i=>(π^d) i.val) hstart hfinish Old ψ hOld _ hY
end Oberwolfach
