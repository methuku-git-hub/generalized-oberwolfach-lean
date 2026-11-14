module

public import Oberwolfach.CycleGraphFixTwo
public import Oberwolfach.OrdinaryTransferCycles

@[expose] public section
/-! An ordered representation of a fixed embedded cycle is determined by
its first directed edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordered_cycle_representation_first_edge_injective {V:Type} [Fintype V] [DecidableEq V]
    {r:ℕ} (hr:3≤r) (f g:Fin r↪V)
    (heq:(SimpleGraph.cycleGraph r).map f=(SimpleGraph.cycleGraph r).map g)
    (h0:f ⟨0,by omega⟩=g ⟨0,by omega⟩)
    (h1:f ⟨1,by omega⟩=g ⟨1,by omega⟩):f=g:=by
  have hex:∀ i:Fin r,∃ j:Fin r,f j=g i:=by
    intro i
    have hg:g i∈((SimpleGraph.cycleGraph r).map g).support:=by
      rw [cycle_map_support hr g]
      exact ⟨i,rfl⟩
    rw [←heq,cycle_map_support hr f] at hg
    exact hg
  let σ:Fin r→Fin r:=fun i=>Classical.choose (hex i)
  have hs:∀ i,f (σ i)=g i:=fun i=>Classical.choose_spec (hex i)
  have hinj:Function.Injective σ:=by
    intro i j hij
    apply g.injective
    rw [←hs i,←hs j,hij]
  have hmap:∀ i j,(SimpleGraph.cycleGraph r).Adj i j→(SimpleGraph.cycleGraph r).Adj (σ i) (σ j):=by
    intro i j hij
    have hg:(SimpleGraph.cycleGraph r).map g |>.Adj (g i) (g j):=
      SimpleGraph.map_adj_apply.mpr hij
    rw [←heq,←hs i,←hs j] at hg
    exact SimpleGraph.map_adj_apply.mp hg
  have hz:σ ⟨0,by omega⟩=⟨0,by omega⟩:=by
    apply f.injective
    rw [hs,h0]
  have ho:σ ⟨1,by omega⟩=⟨1,by omega⟩:=by
    apply f.injective
    rw [hs,h1]
  have hfix:=cycleGraph_injective_hom_fix_zero_one hr σ hinj hmap hz ho
  apply Function.Embedding.ext
  intro i
  rw [←hs i,hfix]
end Oberwolfach
