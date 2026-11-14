module

public import Oberwolfach.OrdinaryInnerWeightsGeneralFromDensity
public import Oberwolfach.OrdinaryVortexLevelParentDensityBalance
public import Oberwolfach.MarkedFixedVortexEventInputs

@[expose] public section
/-! Select positive bounded fractional cycle weights on every fixed vortex
inner domain, before sampling, directly from the original host margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_inner_cycle_weights
    (m:ℕ) (hm:2≤m) (α:ℝ) (hα:0<α):
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀(β ε ρ₀:ℝ),0≤β→β≤1/4→β≤α→0<ε→ε<1/4→0<ρ₀→
    ∃v₀:ℕ,1≤v₀ ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (θhost:ℝ),cycleThreshold (m+1)≤θhost→
      (θhost+α)*Fintype.card V≤D→
    ∃weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ,
    ∀i,i<Q.length→
      (∀C₀,c/((markedVortexInnerVertices Q i).card:ℝ)^(m-1)≤weight i C₀ ∧
        weight i C₀≤C/((markedVortexInnerVertices Q i).card:ℝ)^(m-1)) ∧
      (∀x y,(∑C₀,if C₀.val.val.Adj x y then weight i C₀ else 0)=
        if ((P.comap (markedVortexVertexEmbedding Q i)).induce
          ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))).Adj x y then 1 else 0):=by
  obtain ⟨c,C,hc,hC,N,hN,hweights⟩:=ordinary_inner_weights_general_from_parent_density m hm (α/2) (by positivity)
  refine ⟨c,C,hc,hC,?_⟩
  intro β ε ρ₀ hβ hβ1 hβα hε hε1 hρ₀
  obtain ⟨v₀,hv₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ N
  refine ⟨v₀,hv₀,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q θhost hthreshold hdegree
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hex:∀i,i<Q.length→∃weight:OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ,
      (∀C₀,c/((markedVortexInnerVertices Q i).card:ℝ)^(m-1)≤weight C₀ ∧
        weight C₀≤C/((markedVortexInnerVertices Q i).card:ℝ)^(m-1)) ∧
      (∀x y,(∑C₀,if C₀.val.val.Adj x y then weight C₀ else 0)=
        if ((P.comap (markedVortexVertexEmbedding Q i)).induce
          ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))).Adj x y then 1 else 0):=by
    intro i hi
    let I:=markedVortexInnerVertices Q i
    let f:=markedVortexVertexEmbedding Q i
    have hs:=hsize V U P D vsize hreg hn hD hρlo hρhi hv Q i hi
    have hN':N≤I.card:=by
      have he:0≤ε*(I.card:ℝ):=by positivity
      have hh:=hs.2.1
      exact_mod_cast (show (N:ℝ)≤I.card by nlinarith only [hh,he])
    have hfields:=ordinary_vortex_level_parent_density_balance P D vsize β ε θhost α (initialIndexDensity U D) 0
      Q hn hreg rfl hρ hβ (by norm_num) hdegree i (by omega)
    have hthreshold':cycleThreshold (m+1)+α/2≤θhost+α-β/2:=by linarith
    exact hweights (markedVortexVertexType Q i) I hN' (P.comap f) (θhost+α-β/2) hthreshold' hfields.1
  let weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
      ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ:=
    fun i=>if hi:i<Q.length then Classical.choose (hex i hi) else fun _=>0
  refine ⟨weight,?_⟩
  intro i hi
  simpa only [weight,dif_pos hi] using Classical.choose_spec (hex i hi)
end Oberwolfach
