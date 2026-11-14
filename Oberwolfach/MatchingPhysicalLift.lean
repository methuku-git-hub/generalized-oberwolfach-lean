module

public import Oberwolfach.ResourceRootEmbedding

@[expose] public section
/-! An injective resource map transfers a matching to the physical sets of
its chosen realizations, without identifying or discarding candidates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem matching_physical_lift {C X Y W:Type} [DecidableEq C] [DecidableEq X] [DecidableEq Y]
    (S:Finset C) (R:C→Finset X) (φ:X→Y) (lift:C→W) (B:W→Finset Y)
    (hφ:Function.Injective φ)
    (hmatch:∀c∈S,∀d∈S,c≠d→Disjoint (R c) (R d))
    (hphysical:∀c∈S,B (lift c)=(R c).image φ):
    ∀c∈S,∀d∈S,c≠d→Disjoint (B (lift c)) (B (lift d)) :=by
  intro c hc d hd hcd
  rw [hphysical c hc,hphysical d hd]
  apply Finset.disjoint_left.mpr
  intro y hyc hyd
  obtain ⟨x,hxc,hxy⟩:=Finset.mem_image.mp hyc
  obtain ⟨x',hx'd,hx'y⟩:=Finset.mem_image.mp hyd
  have hxx':x=x':=hφ (hxy.trans hx'y.symm)
  subst x'
  exact (Finset.disjoint_left.mp (hmatch c hc d hd hcd)) hxc hx'd

theorem matching_physical_lift_injective_on {C X Y W:Type} [DecidableEq C] [DecidableEq X] [DecidableEq Y]
    (S:Finset C) (R:C→Finset X) (φ:X→Y) (lift:C→W) (B:W→Finset Y)
    (hφ:Function.Injective φ)
    (hmatch:∀c∈S,∀d∈S,c≠d→Disjoint (R c) (R d))
    (hphysical:∀c∈S,B (lift c)=(R c).image φ)
    (hne:∀c∈S,(R c).Nonempty):
    Set.InjOn lift (↑S:Set C) :=by
  intro c hc d hd heq
  by_contra hcd
  have hdis:=matching_physical_lift S R φ lift B hφ hmatch hphysical c hc d hd hcd
  rw [heq] at hdis
  obtain ⟨x,hx⟩:=hne d hd
  have hy:φ x∈B (lift d):=by rw [hphysical d hd];exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  exact (Finset.disjoint_left.mp hdis) hy hy
end Oberwolfach
