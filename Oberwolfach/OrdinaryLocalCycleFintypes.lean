module

public import Oberwolfach.OrdinaryHubDomainTransportExplicit

@[expose] public section
/-! Explicit finite enumerations for the two decision-instance contexts. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V:Type} [Fintype V] [DecidableEq V]
section low
attribute [local instance] Classical.propDecidable
def ordinaryLocalCycleFintypeLow (Q F:SimpleGraph V) (T:Finset V) (r:ℕ):
    Fintype (LocalOrdinaryCycle Q F T r):=inferInstance
end low
section high
attribute [local instance 100000] Classical.propDecidable
def ordinaryLocalCycleFintypeHigh (Q F:SimpleGraph V) (T:Finset V) (r:ℕ):
    Fintype (LocalOrdinaryCycle Q F T r):=inferInstance
end high
end Oberwolfach
