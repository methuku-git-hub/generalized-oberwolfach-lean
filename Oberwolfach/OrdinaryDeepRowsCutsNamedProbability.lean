module

public import Oberwolfach.OrdinaryDeepRowsCutsEvent

@[expose] public section
/-! Restate the checked all-level bound using the named event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_rows_cuts_named_probability
    (n qCount D mv m K d:ℕ) (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin qCount) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (p pH pmin αcut c C b Bweight ξ ηHub Kdom a aLoad ρdeep θdeep cap eParent hParent εR εH:ℝ)
    (density tR tH:ℕ→ℝ) (s:Fin qCount→Bool→ℝ) (j:Bool)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)]
    (μ:FiniteLaw (∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e))
    (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop)
    (loss χinner χdeep χone χtwo χcut:ℝ)    (h:OrdinaryDeepRowsCutsAttachedEvent n qCount D mv m K d β ε P Q π hπ p pH pmin αcut c C b Bweight ξ ηHub Kdom a aLoad ρdeep θdeep cap eParent hParent εR εH density tR tH s j R μ ν E loss χinner χdeep χone χtwo χcut):
    ∃weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ,
    (∀i,i<Q.length→OrdinaryInnerHubWeightSetupGeneral m (P.comap (markedVortexVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (weight i) pmin (2*p) pH
      (2*pH*(markedVortexInnerHubs Q i).card/(2*p)) β ξ (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom) ∧
    let νcoins:=FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin)
    1-(loss+χinner+χdeep+χone+χtwo+χcut)≤((μ.sigma ν).prod νcoins).probability
      (OrdinaryDeepRowsCutsEvent n qCount D mv m K d β ε P Q π hπ p pH pmin αcut c C b Bweight ξ ηHub Kdom a aLoad ρdeep θdeep cap eParent hParent εR εH density tR tH s j R μ ν E loss χinner χdeep χone χtwo χcut) :=by
  exact h
end Oberwolfach
