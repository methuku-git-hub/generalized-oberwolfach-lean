module

public import Oberwolfach.LongMatchingCommonEvent
public import Oberwolfach.MarkedVortexParentRecordSmallerReferenceEvent
public import Oberwolfach.MarkedExpandedActualSample

@[expose] public section
/-! The selector's adaptive agreement and parent event are available to the
matching construction at the same selected expanded sample and with the same
parent and active weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance selectedParentCommonFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_selected_parent_common_sample_bridge
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (r K d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L hNbr:ℕ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ ρHost:ℝ)
    (βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
      εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀Event sstarEvent kstarEvent τLevelEvent:ℝ)
    (levelWeight:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (hParent k₀:ℕ) (αP ρP sstarP tstarP kstarP:ℝ)
    (εAbsP ζAbsP βconfigP βCommonP εrefP δrefP δparent εBalP ζBalP:ℝ)
    (sizeP aP bP eP fP:ℕ) (sP pP kP:ℝ)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weightActive:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (hPrior:MarkedAdaptiveAgreementProperty r d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L hNbr
      βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich (ρHost*(1/100)/2)
      (ρHost*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent 1 ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent
      G π (markedVortexVertexEmbedding Q) (markedVortexHubEmbedding Q) (markedVortexPermutation Q π hπ)
      (markedVortexInnerVertices Q) (markedVortexInnerHubs Q) (fun i=>Fintype.card (markedVortexVertexType Q i))
      (fun i=>2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρHost)
      (fun i=>2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρHost)
      (fun i=>Function.Embedding.refl (markedVortexHubType Q i)) levelWeight
      (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ) false false
      (markedExpandedActualSelected π d z))
    (hGood:MarkedVortexParentRecordSmallerReferenceEvent r hParent k₀ d αP ρP sstarP tstarP kstarP
      εAbsP ζAbsP βconfigP βCommonP εrefP δrefP δparent δparent δparent δparent δparent δparent δparent δparent
      εBalP ζBalP δparent δparent δparent δparent δparent δparent
      sizeP aP bP eP fP G D m β ε Q π hπ L sP pP kP
      (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ)
      false false weightParent weightActive (markedExpandedActualSelected π d z)):
    LongMatchingCommonEvent G π D m β ε Q hπ r K d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L hNbr
      F hF θ ρHost βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
      εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀Event sstarEvent kstarEvent τLevelEvent levelWeight (markedExpandedActualSelected π d z) ∧
    MarkedVortexParentRecordSmallerReferenceEvent r hParent k₀ d αP ρP sstarP tstarP kstarP
      εAbsP ζAbsP βconfigP βCommonP εrefP δrefP δparent δparent δparent δparent δparent δparent δparent δparent
      εBalP ζBalP δparent δparent δparent δparent δparent δparent
      sizeP aP bP eP fP G D m β ε Q π hπ L sP pP kP
      (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ)
      false false weightParent weightActive (markedExpandedActualSelected π d z) :=by
  exact ⟨hPrior,hGood⟩
end Oberwolfach
