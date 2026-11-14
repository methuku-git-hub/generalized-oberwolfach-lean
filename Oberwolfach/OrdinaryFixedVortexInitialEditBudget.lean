module

public import Oberwolfach.OrdinaryInitialEditUniformBudget
public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! The original vortex geometry supplies both inner-domain lower bounds
for the initial correction and finite reservoir edit cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_initial_edit_budget
    (ε ρ₀ ζ:ℝ) (hε:0<ε) (hρ₀:0<ρ₀) (hζ:0<ζ):
    ∃ξ:ℝ,0<ξ ∧ ∀C:ℝ,0≤C→∃N:ℕ,1≤N ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ) (β:ℝ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<vsize→N≤Fintype.card V→
    ∀Q:Vortex U P D β ε vsize,
      0≤10*ξ*Fintype.card V+C ∧
      10*ξ*Fintype.card V+C≤ζ*(markedVortexInnerVertices Q 0).card ∧
      10*ξ*Fintype.card V+C≤ζ*(markedVortexInnerHubs Q 0).card:=by
  obtain ⟨ξ,hξ,hmain⟩:=ordinary_initial_edit_uniform_budget ε ρ₀ ζ hε hρ₀ hζ
  refine ⟨ξ,hξ,?_⟩
  intro C hC
  obtain ⟨N,hN,hmain⟩:=hmain C hC
  refine ⟨N,hN,?_⟩
  intro V U _ _ _ _ P D vsize β hreg hn hD hρlo hρhi hβ hβ1 hvsize hnN Q
  have hgeom:=marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ₀ hρlo hρhi hβ hβ1 hε hvsize 0 Q.length_pos
  have hcard:Fintype.card (markedVortexVertexType Q 0)=Fintype.card V:=by
    change Fintype.card (Q.extendedVertices 0)=Fintype.card V
    rw [Q.extendedVertices_eq (Nat.zero_le _),Q.initial]
    simp
  have hI:(ε/2)*(Fintype.card V:ℝ)≤(markedVortexInnerVertices Q 0).card:=by simpa [hcard] using hgeom.1
  exact hmain (Fintype.card V) (markedVortexInnerVertices Q 0).card (markedVortexInnerHubs Q 0).card
    (by exact_mod_cast hnN) hI hgeom.2.1
end Oberwolfach
