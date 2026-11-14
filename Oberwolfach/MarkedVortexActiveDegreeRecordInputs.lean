module

public import Oberwolfach.MarkedVortexActiveHubCardinality
public import Oberwolfach.MarkedVortexActiveDegreeFields

@[expose] public section
/-! Active degree-target bounds for the nested level record. The target
uses the same active hubs as the fixed weight condition. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε α:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_active_degree_record_inputs
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(1/2+α)*Fintype.card V≤(D:ℝ)) (hα:0<α)
    (hρ:0 < initialIndexDensity U D) (hb:0≤β) (hbα:β≤3*α/40) (hb1:β≤3/20)
    (he:0≤ε) (he1:ε≤1/4) (L:ℕ)
    (hW:∀ i≤L,0<Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
      Finset (markedVortexVertexType Q (i+1)))):
    ∀ i≤L,
      let W:=↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
        Finset (markedVortexVertexType Q (i+1)))
      let Zinner:=markedVortexInnerNonDeeperHubs Q i
      let Dactive:=2*(Zinner.card:ℝ)/initialIndexDensity U D;
      (Fintype.card W:ℝ)/2≤Dactive ∧ Dactive≤2*Fintype.card W:=by
  intro i hi W Zinner Dactive
  letI : Nonempty W:=Fintype.card_pos_iff.mp (hW i hi)
  let v:W:=Classical.choice inferInstance
  have hh:=marked_vortex_active_degree_fields Q hreg hn hD hα hρ hb hbα hb1 he he1 (i+1) v
  have ht:=marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)
  change ((Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
      Finset (markedVortexVertexType Q (i+1)))):ℝ)/2≤2*(Zinner.card:ℝ)/initialIndexDensity U D ∧
    2*(Zinner.card:ℝ)/initialIndexDensity U D≤2*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
      Finset (markedVortexVertexType Q (i+1)))
  rw [Fintype.card_coe,←ht]
  exact ⟨hh.1,hh.2.1⟩
end Oberwolfach
