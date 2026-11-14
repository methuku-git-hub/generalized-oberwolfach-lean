module

public import Oberwolfach.LongMatchingCommonEvent
public import Oberwolfach.MarkedExpandedActualSample
public import Oberwolfach.FiniteLawSupportProbabilityMono

@[expose] public section
/-! The common event in the original structural probability theorem is
    exactly the named matching event on the same expanded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_original_common_event_structural_core_projection
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (r K d size a₀ b₀ e₀ aRob bRob eRob f₀ L h:ℕ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ ρ:ℝ)
    (βevent βref εAbs εRob ζRob εRef δRef γRich tstar ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig
      ρ₀ sstar kstar τLevel:ℝ)
    (weight:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d))
    (Parent Expanded Stable Correction Good Reserve Concrete Boundary Relative:
      MarkedExpandedActualOutcome (U:=U) π d→Prop) (b:ℝ):
    let fV:=markedVortexVertexEmbedding Q
    let gV:=markedVortexHubEmbedding Q
    let ρi:=markedVortexPermutation Q π hπ
    let Aset:=markedVortexInnerVertices Q
    let Bset:=markedVortexInnerHubs Q
    let Scale:=fun i=>Fintype.card (markedVortexVertexType Q i)
    let Dlevel:=fun i=>2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρ
    let bdom:=fun i=>Function.Embedding.refl (markedVortexHubType Q i)
    let Prior:=MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L h
      βevent βref εAbs εRob ζRob εRef δRef γRich (ρ*(1/100)/2)
      (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
      P π fV gV ρi Aset Bset Scale Dlevel Dlevel bdom weight
      (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ) false false;
    b≤μ.probability (fun z=>(Prior (markedExpandedActualSelected π d z) ∧ Parent z ∧ Expanded z ∧ Stable z ∧
      Correction z ∧ Good z ∧ Reserve z ∧ Concrete z ∧ Boundary z) ∧ Relative z)→
    b≤μ.probability (fun z=>(LongMatchingCommonEvent P π Dv mm β ε Q hπ r K d size a₀ b₀ e₀ aRob bRob eRob f₀ L h
      F hF θ ρ βevent βref εAbs εRob ζRob εRef δRef γRich tstar ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig
      ρ₀ sstar kstar τLevel weight (markedExpandedActualSelected π d z) ∧ Parent z ∧ Expanded z ∧ Stable z ∧
      Correction z ∧ Good z ∧ Reserve z ∧ Concrete z ∧ Boundary z) ∧ Relative z) :=by
  intro fV gV ρi Aset Bset Scale Dlevel bdom Prior hprob
  exact hprob
end Oberwolfach
