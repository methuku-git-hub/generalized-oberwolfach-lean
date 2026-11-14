module

public import Oberwolfach.OrderedCycleRepresentationEdges

@[expose] public section
/-! Separation depends only on the vertex set of an injectively enumerated
cycle, not on the chosen starting point or orientation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem permutationSeparated_iff_range {V I:Type} (π:Equiv.Perm V) (b:ℕ) (f:I→V)
    (hf:Function.Injective f):
    PermutationSeparated π b f ↔ ∀ x∈Set.range f,∀ y∈Set.range f,x≠y→¬PermutationClose π b x y:=by
  constructor
  · intro h x hx y hy hxy
    obtain ⟨i,rfl⟩:=hx
    obtain ⟨j,rfl⟩:=hy
    exact h i j (fun hij=>hxy (congrArg f hij))
  · intro h i j hij
    exact h (f i) ⟨i,rfl⟩ (f j) ⟨j,rfl⟩ (fun hh=>hij (hf hh))

theorem orderedCycle_separation_iff_support {V:Type} [Fintype V] [DecidableEq V]
    (H:SimpleGraph V) (n:ℕ) (hn:1≤n) (π:Equiv.Perm V) (b:ℕ)
    (f:OrderedCycleRepresentations H (n+2)):
    PermutationSeparated π b f.val ↔
      ∀ x∈H.support,∀ y∈H.support,x≠y→¬PermutationClose π b x y:=by
  rw [permutationSeparated_iff_range π b f.val f.val.injective]
  have hs:H.support=Set.range f.val:=
    (congrArg (fun G:SimpleGraph V=>G.support) f.property).trans (cycle_map_support (by omega) f.val)
  rw [hs]
end Oberwolfach
