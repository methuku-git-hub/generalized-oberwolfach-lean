module

public import Oberwolfach.OrdinaryTransferCycles

@[expose] public section
/-! A cycle living in the image of an embedded rim host pulls back to an
actual cycle on the original type, with the same physical edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cycle_in_embedded_domain {V W:Type} (φ:V↪W)
    (G:SimpleGraph V) (C:SimpleGraph W) (r:ℕ)
    (hC:IsEmbeddedCycle C r) (hhost:C≤G.map φ):
    ∃D:SimpleGraph V,IsEmbeddedCycle D r ∧ D≤G ∧ D.map φ=C:=by
  obtain ⟨hr,e,he⟩:=hC
  have hrep (i:Fin r):∃v,φ v=e i:=by
    have hi:e i∈C.support:=by
      rw [he,cycle_map_support hr]
      exact ⟨i,rfl⟩
    have hi':e i∈(G.map φ).support:=SimpleGraph.support_mono hhost hi
    obtain ⟨w,hw⟩:=(G.map φ).mem_support.mp hi'
    obtain ⟨v,v',_,hv,_⟩:=(SimpleGraph.map_adj φ G _ _).mp hw
    exact ⟨v,hv⟩
  choose f hf using hrep
  let fe:Fin r↪V:=⟨f,fun i j hij=>e.injective (by rw [←hf i,←hf j,hij])⟩
  have hcompose:fe.trans φ=e:=by
    ext i
    exact hf i
  let D:SimpleGraph V:=(SimpleGraph.cycleGraph r).map fe
  have hmap:D.map φ=C:=by
    dsimp only [D]
    rw [SimpleGraph.map_map]
    change (SimpleGraph.cycleGraph r).map (fe.trans φ)=C
    rw [hcompose,←he]
  have hDG:D≤G:=by
    intro v w hvw
    have hh:(D.map φ).Adj (φ v) (φ w):=SimpleGraph.map_adj_apply.mpr hvw
    rw [hmap] at hh
    exact SimpleGraph.map_adj_apply.mp (hhost hh)
  exact ⟨D,⟨hr,fe,rfl⟩,hDG,hmap⟩
end Oberwolfach
