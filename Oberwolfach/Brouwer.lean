module

public import FixedPointTheorems.brouwer

@[expose] public section

/-! The fixed-point theorem used in the cyclic-partite argument. The imported
proof is vendored with its license and port record; it is not an axiom. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem compact_convex_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : Set V) (hconvex : Convex ℝ K) (hcompact : IsCompact K) (hne : K.Nonempty)
    (f : K → K) (hf : Continuous f) :
    ∃ x : K, f x = x :=
  brouwer_fixed_point K hconvex hcompact hne ⟨f, hf⟩

end Oberwolfach
