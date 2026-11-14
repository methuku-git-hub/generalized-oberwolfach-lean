module

public import Oberwolfach.MarkedFixedVortexEventInputs

@[expose] public section
/-! The original vortex supplies the size, nesting and hub-density inputs
used by local correction at every nonterminal level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_cleanup_domain_geometry
    (β ε ρ₀:ℝ) (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (N:ℕ):
    ∃v₀:ℕ,1≤v₀ ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (i:ℕ),i<Q.length→
    let I:=markedVortexInnerVertices Q i;let T:=markedVortexDeeperVertices Q i;
    let B:=markedVortexInnerHubs Q i;let W:=markedVortexDeeperHubs Q i;
    T⊆I ∧ W⊆B ∧ N≤I.card ∧ N≤B.card ∧
      (ρ₀/8)*(I.card:ℝ)≤B.card ∧ B.card≤I.card ∧
      (T.card:ℝ)≤ε*I.card ∧ (W.card:ℝ)≤ε*B.card:=by
  obtain ⟨v₀,hv₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ N
  refine ⟨v₀,hv₀,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q i hi I T B W
  have hs:=hsize V U P D vsize hreg hn hD hρlo hρhi hv Q i hi
  have ha:=marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ₀ hρlo hρhi hβ hβ1 hε (by omega) i hi
  have hg:=marked_vortex_fixed_active_geometry Q hε.le i
  have hI:N≤I.card:=by
    have he:0≤ε*(I.card:ℝ):=by positivity
    have hh:=hs.2.1
    exact_mod_cast (show (N:ℝ)≤I.card by nlinarith only [hh,he])
  have hB:N≤B.card:=by
    have he:0≤ε*(B.card:ℝ):=by positivity
    have hh:=hs.2.2.1
    exact_mod_cast (show (N:ℝ)≤B.card by nlinarith only [hh,he])
  have hDpos:0<D:=by
    have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    exact_mod_cast (show (0:ℝ)<D by linarith)
  have hu:=Q.index_size_upper hreg hn hDpos hε.le hρhi (show i+1≤Q.length by omega)
  have hIeq:I.card=(Q.vertices (i+1)).card:=by
    rw [(marked_vortex_inner_cardinalities Q i).1,Q.extendedVertices_eq (by omega: i+1≤Q.length)]
  have hBeq:B.card=(Q.indices (i+1)).card:=by
    rw [(marked_vortex_inner_cardinalities Q i).2.2.1,Q.extendedIndices_eq (by omega: i+1≤Q.length)]
  have hBI:B.card≤I.card:=by rw [hIeq,hBeq];omega
  exact ⟨hg.1,hg.2.1,hI,hB,ha.2.1,hBI,hg.2.2.1,hg.2.2.2.1⟩
end Oberwolfach
