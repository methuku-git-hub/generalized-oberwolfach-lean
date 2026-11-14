module

public import Oberwolfach.MarkedLongCommonAgreementRestrictedBalance

@[expose] public section
/-! Named common event on the actual retained sample, with the original
vortex and weight parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def LongMatchingCommonEvent
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (DQ mm:ℕ) (β εQ:ℝ) (Q:Vortex U G DQ β εQ mm)
    (hpres:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (r K d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L h:ℕ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ ρHost:ℝ)
    (βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
      εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀Event sstarEvent kstarEvent τLevelEvent:ℝ)
    (levelWeight:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false):Prop:=
  let fV:=markedVortexVertexEmbedding Q
  let gV:=markedVortexHubEmbedding Q
  let ρi:=markedVortexPermutation Q π hpres
  let Aset:=markedVortexInnerVertices Q
  let Bset:=markedVortexInnerHubs Q
  let Scale:=fun i=>Fintype.card (markedVortexVertexType Q i)
  let Dlevel:=fun i=>2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρHost
  let bdom:=fun i=>Function.Embedding.refl (markedVortexHubType Q i);
  MarkedAdaptiveAgreementProperty r d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L h
    βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich (ρHost*(1/100)/2)
    (ρHost*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent 1 ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent
    G π fV gV ρi Aset Bset Scale Dlevel Dlevel bdom levelWeight
    (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ) false false z
end Oberwolfach
