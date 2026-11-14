module

public import Oberwolfach.OrdinaryWheelResources
public import Oberwolfach.TransferCyclePositions

@[expose] public section

/-! A cycle of length at least four has no triangle. In particular its
two neighbours of a fixed root are not joined by a rim edge; this excludes
an otherwise possible collision in the transformer vertex-wheel stage. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem cycleGraph_no_triangle (r:ℕ) (hr:4≤r) (i j k:Fin r)
    (hij:(SimpleGraph.cycleGraph r).Adj i j)
    (hjk:(SimpleGraph.cycleGraph r).Adj j k)
    (hki:(SimpleGraph.cycleGraph r).Adj k i):False:=by
  have hi:=i.isLt
  have hj:=j.isLt
  have hk:=k.isLt
  rcases cycleGraph_adj_natural_cases r (by omega) i j hij with h|h|⟨h,h'⟩|⟨h,h'⟩ <;>
    rcases cycleGraph_adj_natural_cases r (by omega) j k hjk with g|g|⟨g,g'⟩|⟨g,g'⟩ <;>
    rcases cycleGraph_adj_natural_cases r (by omega) k i hki with f|f|⟨f,f'⟩|⟨f,f'⟩ <;> omega

 theorem IsEmbeddedCycle.no_triangle {V:Type} {C:SimpleGraph V} {r:ℕ}
    (hC:IsEmbeddedCycle C r) (hr:4≤r) (x y z:V)
    (hxy:C.Adj x y) (hyz:C.Adj y z):¬C.Adj z x:=by
  intro hzx
  obtain ⟨_,f,rfl⟩:=hC
  obtain ⟨i,j,hij,rfl,rfl⟩:=(SimpleGraph.map_adj f _ _ _).mp hxy
  obtain ⟨k,l,hkl,hkj,rfl⟩:=(SimpleGraph.map_adj f _ _ _).mp hyz
  have hkj':k=j:=f.injective hkj
  subst k
  have hli:(SimpleGraph.cycleGraph r).Adj l i:=SimpleGraph.map_adj_apply.mp hzx
  exact cycleGraph_no_triangle r hr i j l hij hkl hli

end Oberwolfach
