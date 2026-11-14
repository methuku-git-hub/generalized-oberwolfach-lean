module

public import Oberwolfach.OrdinaryHubDomainTransport

@[expose] public section
/-! Transport local cycle weights across equal domains, allowing the two
sides to use different finite enumerations of the same cycle family. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
theorem ordinary_local_weights_transport_explicit (Q F:SimpleGraph V) (r:ℕ) (S T:U→U→Finset V)
    (hST:S=T)
    (fS:∀ u u',Fintype (LocalOrdinaryCycle Q F (S u u') r))
    (fT:∀ u u',Fintype (LocalOrdinaryCycle Q F (T u u') r)) (a B η:ℝ)
    (w:∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (S u u') r→ℝ)
    (hw:∀ u u' (hne:u≠u') C,a≤w u u' hne C∧w u u' hne C≤B)
    (hdeg:∀ u u' (hne:u≠u'),∀ v∈S u u',
      |1-@hypergraphWeightedDegree V _ (fS u u') _ localOrdinaryVertices (w u u' hne) v|≤η):
    ∃ w':∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (T u u') r→ℝ,
      (∀ u u' (hne:u≠u') C,a≤w' u u' hne C∧w' u u' hne C≤B) ∧
      (∀ u u' (hne:u≠u'),∀ v∈T u u',
        |1-@hypergraphWeightedDegree V _ (fT u u') _ localOrdinaryVertices (w' u u' hne) v|≤η) := by
  subst T
  have heq:fS=fT:=by funext u u';exact Subsingleton.elim _ _
  subst fT
  exact ⟨w,hw,hdeg⟩
end Oberwolfach
