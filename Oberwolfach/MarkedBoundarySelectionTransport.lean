module

public import Oberwolfach.MarkedHubFactorOn
public import Oberwolfach.MarkedEndpointPairingWitness

@[expose] public section

/-! Re-express the same selected cycles and endpoint bijections on equal
finite classes. Their physical graphs remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

namespace MarkedHubFactorOn
variable {u:U} {Y Y':Finset V}
def changeSet (P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK u Y) (h:Y=Y'):
    MarkedHubFactorOn tail head ktail khead m π b H₀ HK u Y':=
  ⟨P.cycles,P.disjoint,P.covers.trans h⟩
theorem changeSet_graph (P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK u Y) (h:Y=Y'):
    (P.changeSet h).graph=P.graph:=rfl
end MarkedHubFactorOn
namespace MarkedEndpointPairing
variable {A₀ A₁ X₀ X₁ A₀' A₁' X₀' X₁':Finset V} {Y₀ Y₁ Y₀' Y₁':Finset U}
def changeSets (P:MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK π b)
    (hA₀:A₀=A₀') (hA₁:A₁=A₁') (hX₀:X₀=X₀') (hX₁:X₁=X₁') (hY₀:Y₀=Y₀') (hY₁:Y₁=Y₁'):
    MarkedEndpointPairing A₀' A₁' X₀' X₁' Y₀' Y₁' H₀ HK π b:=by
  subst A₀';subst A₁';subst X₀';subst X₁';subst Y₀';subst Y₁';exact P

theorem changeSets_graph (P:MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK π b)
    (hA₀:A₀=A₀') (hA₁:A₁=A₁') (hX₀:X₀=X₀') (hX₁:X₁=X₁') (hY₀:Y₀=Y₀') (hY₁:Y₁=Y₁'):
    (P.changeSets hA₀ hA₁ hX₀ hX₁ hY₀ hY₁).graph=P.graph:=by
  subst A₀';subst A₁';subst X₀';subst X₁';subst Y₀';subst Y₁';rfl
end MarkedEndpointPairing
end Oberwolfach
