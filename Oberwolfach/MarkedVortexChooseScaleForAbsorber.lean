module

public import Oberwolfach.MarkedVortexReservedCapacityFields
public import Oberwolfach.VortexPermutation

@[expose] public section
/-! Fix a terminal scale and an absorber capacity before the graph order;
the resulting vortex and permutation have the required first and final sizes. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_choose_scale_for_absorber
    (β ε ρ₀ εAbs:ℝ) (hb:0<β) (he:0<ε) (heq:ε<1/4) (hρ:0<ρ₀)
    (heAbs:ε≤εAbs) (h required:ℕ):
    ∃ m size:ℕ,1≤m ∧ required≤m ∧ size=2*m ∧
      ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
        (G:SimpleGraph V) (D:ℕ),G.IsRegularOfDegree D →
        (Fintype.card V:ℝ)/2≤D → ρ₀≤ initialIndexDensity U D → initialIndexDensity U D≤1 →
        m≤Fintype.card V →
        ∃ Q:Vortex U G D β ε m,∃ π:Equiv.Perm V,∃ L:ℕ,
          L+1=Q.length ∧
          (∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) ∧
          (∀ x k,0<k→k<h→(π^k) x≠x) ∧
          ((markedVortexInnerVertices Q 0).card:ℝ)≤εAbs*Fintype.card (markedVortexVertexType Q 0) ∧
          ((markedVortexInnerHubs Q 0).card:ℝ)≤εAbs*Fintype.card (markedVortexVertexType Q 0) ∧
          (markedVortexInnerVertices Q L).card+(markedVortexInnerHubs Q L).card≤size := by
  obtain ⟨m₀,hm₀,hvortex⟩:=vortex_with_permutation_exists hb he heq hρ h
  let m:=max m₀ required
  have hm:1≤m:=hm₀.trans (le_max_left _ _)
  refine ⟨m,2*m,hm,le_max_right _ _,rfl,?_⟩
  intro V U _ _ _ _ G D hreg hD hρlo hρhi hmn
  obtain ⟨Q,π,hpres,_,hshort⟩:=hvortex V U G D m hreg hD hρlo hρhi ((le_max_left _ _)) hmn
  let L:=Q.length-1
  have hL:L+1=Q.length:=by dsimp [L];have hh:=Q.length_pos;omega
  have hn:0<Fintype.card V:=by omega
  have hDpos:0<D:=by
    have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    exact_mod_cast (show (0:ℝ)<D by linarith)
  have hf:=marked_vortex_inner_upper_size_inputs Q hreg hn hDpos hρhi he.le εAbs heAbs 0 (by have hh:=Q.length_pos;omega) 0 (by omega)
  have ht:=marked_vortex_terminal_pair_capacity Q hreg hn hDpos hρhi he.le L hL
  exact ⟨Q,π,L,hL,hpres,hshort,hf.1,hf.2,ht⟩
end Oberwolfach
