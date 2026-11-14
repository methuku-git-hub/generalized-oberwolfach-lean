module

public import Oberwolfach.ResourceDecompositions

@[expose] public section

/-! Transport exact edge decompositions across an injective map of the
physical edge types, retaining edge-disjointness and exact coverage. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem resource_decomposition_embedding {E E' W W' : Type*}
    [DecidableEq E] [DecidableEq E'] [DecidableEq W] [DecidableEq W']
    (R : W → Finset E) (R' : W' → Finset E') (f : E → E') (g : W → W')
    (hf : Function.Injective f) (hR : ∀ w,R' (g w)=(R w).image f)
    (S : Finset E) (hS : HasResourceDecomposition R S) :
    HasResourceDecomposition R' (S.image f) := by
  obtain ⟨M,hM,rfl⟩ := hS
  refine ⟨M.image g,?_,?_⟩
  · intro a ha b hb hab
    obtain ⟨a₀,ha₀,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b₀,hb₀,rfl⟩ := Finset.mem_image.mp hb
    rw [hR,hR]
    apply Finset.disjoint_left.mpr
    intro e he hf'
    obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp he
    obtain ⟨y,hy,hye⟩ := Finset.mem_image.mp hf'
    have hxy := hf (hxe.trans hye.symm)
    subst y
    exact (Finset.disjoint_left.mp (hM a₀ ha₀ b₀ hb₀ (fun h => hab (congrArg g h)))) hx hy
  · ext e
    simp only [Finset.mem_biUnion,Finset.mem_image]
    constructor
    · rintro ⟨b,⟨a,ha,rfl⟩,he⟩
      rw [hR] at he
      obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp he
      exact ⟨x,⟨a,ha,hx⟩,hxe⟩
    · rintro ⟨x,⟨a,ha,hx⟩,hxe⟩
      refine ⟨g a,⟨a,ha,rfl⟩,?_⟩
      rw [hR]
      exact Finset.mem_image.mpr ⟨x,hx,hxe⟩

end Oberwolfach
