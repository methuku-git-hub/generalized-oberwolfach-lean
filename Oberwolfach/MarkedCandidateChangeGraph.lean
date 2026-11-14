module

public import Oberwolfach.MarkedCandidateIncomingPerturbation

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V] [Nonempty V]
local instance markedChangeGraphDecEq : DecidableEq V := Classical.decEq V
local instance markedChangeGraphArcDecEq (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

/-- A physical graph which contains every changed incoming pair controls
all losses in the marked-type correction. -/
theorem marked_candidate_incoming_change_le_graph_degree
    (G Bad:SimpleGraph V) (ω:Sym2 V→Fin 6×Bool) (P:V×V→Prop)
    (T₁:Finset {e:V×V // P e})
    (hcover:∀v x,x∈changed (markedRawIncomingTails G ω v) (markedCandidateIncomingTails P T₁ v)→Bad.Adj v x):
    ∀v,((changed (markedRawIncomingTails G ω v) (markedCandidateIncomingTails P T₁ v)).card:ℝ)≤Bad.degree v :=by
  intro v
  have hsub:changed (markedRawIncomingTails G ω v) (markedCandidateIncomingTails P T₁ v)⊆Bad.neighborFinset v:=by
    intro x hx
    exact (Bad.mem_neighborFinset v x).mpr (hcover v x hx)
  exact_mod_cast Finset.card_le_card hsub
end Oberwolfach
