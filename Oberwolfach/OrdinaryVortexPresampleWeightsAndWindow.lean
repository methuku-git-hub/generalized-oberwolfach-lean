module

public import Oberwolfach.OrdinaryFixedVortexHubSetupsBeforeSampling
public import Oberwolfach.OrdinaryVortexBufferedWindowPresampleAll

@[expose] public section
/-! The fixed cycle weights and the full recent-edit budget can both be selected before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_presample_weights_and_window
    (m d buffer:ℕ) (hm:2≤m) (hbuffer:2≤buffer)
    (α ε ρ₀ pmin:ℝ) (hα:0<α) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (hpmin:0<pmin) (hpmin1:pmin≤1):
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀η ζ:ℝ,0<η→0<ζ→
    ∃δ rate:ℝ,0<δ ∧ δ≤α ∧ 0<rate ∧
    ∀(β ξ b Bweight ηHub Kdom:ℝ),0≤β→β≤1/4→β≤α/8→β≤δ→
      2/ε≤Kdom→b≤c→(4*C/pmin^(3*m+1))*Kdom^m≤Bweight→ξ+2*β<ηHub→
    ∀Ccost:ℝ,0≤Ccost→∃v₀:ℕ,1≤v₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (θhost pR pH:ℝ),1/2≤θhost→cycleThreshold (m+1)≤θhost→
      (θhost+α)*Fintype.card V≤D→pmin≤pR→pR≤1→pmin≤pH→pH≤1→
      pR=initialIndexDensity U D*pH→∀cost:ℕ→ℝ,
      (∀i,i+1<Q.length→∀j∈Finset.Icc (i+2-buffer) i,0≤cost j ∧
        cost j≤4*rate*Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j)+Ccost)→
    ∃weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ,
    (∀i,i<Q.length→OrdinaryInnerHubWeightSetupGeneral m (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (weight i) pmin pR pH
        (2*pH*(markedVortexInnerHubs Q i).card/pR) β ξ (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom) ∧
    (∀i,i<Q.length→0≤ordinaryVortexWindowEditBudget d buffer cost i ∧
      ordinaryVortexWindowEditBudget d buffer cost i≤ζ*(markedVortexInnerVertices Q i).card) :=by
  obtain ⟨c,C,hc,hC,hsetup⟩:=ordinary_fixed_vortex_hub_setups_before_sampling m hm α hα
  refine ⟨c,C,hc,hC,?_⟩
  intro η ζ hη hζ
  obtain ⟨δ,rate,hδ,hδα,hrate,hwindow⟩:=ordinary_vortex_buffered_window_presample_all ε ρ₀ α pmin η ζ d buffer
    hbuffer hε hε1 hρ₀ hα hpmin hpmin1 hη hζ
  refine ⟨δ,rate,hδ,hδα,hrate,?_⟩
  intro β ξ b Bweight ηHub Kdom hβ hβ1 hβα hβδ hK hb hB hgap Ccost hCcost
  obtain ⟨v₁,hv₁,hsetup⟩:=hsetup β ε ρ₀ pmin ξ b Bweight ηHub Kdom hβ hβ1 hβα hε hε1 hρ₀ hpmin hpmin1 hK hb hB hgap d
  obtain ⟨v₂,hv₂,hwindow⟩:=hwindow β hβ hβ1 hβδ Ccost hCcost
  refine ⟨max v₁ v₂,by omega,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q π hπ θhost pR pH hθ hthreshold hdegree hpR hpR1 hpH hpH1 hpEq cost hcost
  obtain ⟨weight,hweight⟩:=hsetup V U P D vsize hreg hn hρlo hρhi (by omega) Q π hπ θhost pR pH hθ hthreshold hdegree hpR hpR1 hpH hpH1 hpEq
  refine ⟨weight,hweight,?_⟩
  exact hwindow V U P D vsize hreg hn hD hρlo hρhi (by omega) Q cost hcost
end Oberwolfach
