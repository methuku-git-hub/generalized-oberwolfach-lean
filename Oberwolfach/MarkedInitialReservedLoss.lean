module

public import Oberwolfach.MarkedInitialIndexCardBounds
public import Oberwolfach.VortexExtended
public import Oberwolfach.ActualReservedOuterCodegreeLoss

@[expose] public section
/-! The first vortex index set and a bounded reserved absorber fit the
codegree margin once epsilon is chosen below that margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_initial_reserved_loss
    (αRes:ℝ) (hαRes:0<αRes) (B:ℕ):
    ∃ N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m),
    N≤Fintype.card V→G.IsRegularOfDegree D→0<Fintype.card V→
    ∀ (αHost ρ₀:ℝ),0<αHost→0<ρ₀→
    (1/2+αHost)*Fintype.card V≤(D:ℝ)→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→
    0≤ε→ε≤αRes/2→
    ∀ C:Finset (Finset V⊕(V×U)),C.card≤B→
      ((Q.extendedIndices 1).card:ℝ)+2*C.card≤αRes*Fintype.card V:=by
  obtain ⟨N,hN⟩:=actual_reserved_outer_codegree_loss αRes hαRes B
  refine ⟨N,?_⟩
  intro V U _ _ _ _ G D m β ε Q hn hreg hV αHost ρ₀ hαHost hρ₀ hD hρlo hρhi he heRes C hC
  have hU:=marked_initial_index_card_bounds G D hreg hV αHost ρ₀ hαHost hρ₀ hD hρlo hρhi
  have hstep:((Q.extendedIndices 1).card:ℝ)≤ε*(Fintype.card U:ℝ):=by
    have hh:=(Q.extended_successor_size_bounds he 0).2
    simpa only [Nat.zero_add,Q.extendedIndices_eq (Nat.zero_le _),Q.indices_initial,Finset.card_univ] using hh
  have hUn:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hU.2
  have hInner:((Q.extendedIndices 1).card:ℝ)≤ε*(Fintype.card V:ℝ):=
    hstep.trans (mul_le_mul_of_nonneg_left hUn he)
  exact hN (Fintype.card V) hn (Q.extendedIndices 1).card C.card ε heRes hInner hC
end Oberwolfach
