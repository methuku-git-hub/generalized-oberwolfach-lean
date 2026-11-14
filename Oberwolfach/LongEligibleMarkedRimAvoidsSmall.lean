module

public import Oberwolfach.LongMarkedRimComplementAvoidance

@[expose] public section
/-! Eligible ordinary and marked rims avoid every edge of the small packing. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_eligible_marked_rim_avoids_small
    {V E K:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype E] [Fintype K]
    (M:V→V→ℕ) (Small:SimpleGraph V) (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (hE:∀e,longEligibleResidualArc M Small ⊥ (tail e,head e))
    (hK:∀e,longEligibleResidualArc M Small ⊥ (ktail e,π (khead e))):
    ∀x y,Small.Adj x y→({x,y}:Finset V)∉markedPhysicalRimSet tail head ktail khead π:=by
  have hPacked:∀u:Unit,(Small.edgeFinset.image (Sym2.map (id:V→V)))⊆Small.edgeFinset:=by
    intro u e he
    obtain ⟨e',he',rfl⟩:=Finset.mem_image.mp he
    rw [Sym2.map_id]
    exact he'
  intro x y hxy
  exact long_marked_rim_complement_avoidance M Small tail head ktail khead π hE hK
    (fun _:Unit=>Small) (fun _=>id) hPacked () x y hxy
end Oberwolfach
