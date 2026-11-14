module

public import Oberwolfach.LongMatchingCommonEvent

@[expose] public section
/-! Extract the retained ordinary-spoke row and column losses directly from
the same common event used for the matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance commonRetainedBoundFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_matching_common_event_retained_spoke_bounds
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
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false)
    (hCommon:LongMatchingCommonEvent G π DQ mm β εQ Q hpres r K d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L h
      F hF θ ρHost βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
      εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀Event sstarEvent kstarEvent τLevelEvent levelWeight z):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false;
    (∀v,((Finset.univ.filter (fun u=>¬(H false v u↔rawMarkedPairSpokes π d z.1 false false false v u))).card:ℝ)≤
      (εNbrEvent/(2*((h:ℝ)+1)))*Fintype.card U) ∧
    (∀u,((Finset.univ.filter (fun v=>¬(H false v u↔rawMarkedPairSpokes π d z.1 false false false v u))).card:ℝ)≤
      (εNbrEvent/(2*((h:ℝ)+1)))*Fintype.card (Fin n)) :=by
  intro H
  dsimp only [LongMatchingCommonEvent,MarkedAdaptiveAgreementProperty] at hCommon
  constructor
  · intro v
    have hh:=hCommon.2.2.2.1 false v
    simpa only [H,Finset.sum_boole,iff_comm] using hh
  · intro u
    have hh:=hCommon.2.2.2.2.1 false u
    simpa only [H,Finset.sum_boole,iff_comm] using hh
end Oberwolfach
