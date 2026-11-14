module

public import Oberwolfach.OrdinaryLocalLoads

@[expose] public section
/-! Equivalent finite-set decision procedures give the same hub domains, and
cycle weights transport without changing degrees. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
section low
attribute [local instance] Classical.propDecidable
def ordinaryHubDomainLow (H:V→U→Prop) (u u':U):Finset V:=
  Finset.univ.filter (fun v=>H v u∧H v u')
end low
section high
attribute [local instance 100000] Classical.propDecidable
def ordinaryHubDomainHigh (H:V→U→Prop) (u u':U):Finset V:=
  Finset.univ.filter (fun v=>H v u∧H v u')
end high
attribute [local instance] Classical.propDecidable

theorem ordinary_hub_domains_equal (H:V→U→Prop):
    ordinaryHubDomainLow H=ordinaryHubDomainHigh H:=by
  funext u u'
  ext v
  simp [ordinaryHubDomainLow,ordinaryHubDomainHigh]

theorem ordinary_local_weights_transport (Q F:SimpleGraph V) (r:ℕ) (S T:U→U→Finset V)
    (hST:S=T) (a B η:ℝ)
    (w:∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (S u u') r→ℝ)
    (hw:∀ u u' (hne:u≠u') C,a≤w u u' hne C∧w u u' hne C≤B)
    (hdeg:∀ u u' (hne:u≠u'),∀ v∈S u u',
      |1-hypergraphWeightedDegree localOrdinaryVertices (w u u' hne) v|≤η):
    ∃ w':∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (T u u') r→ℝ,
      (∀ u u' (hne:u≠u') C,a≤w' u u' hne C∧w' u u' hne C≤B) ∧
      (∀ u u' (hne:u≠u'),∀ v∈T u u',
        |1-hypergraphWeightedDegree localOrdinaryVertices (w' u u' hne) v|≤η) := by
  subst T
  exact ⟨w,hw,hdeg⟩
end Oberwolfach
