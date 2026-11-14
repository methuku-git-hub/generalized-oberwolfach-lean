module

public import Oberwolfach.OrdinarySupportedHostInducedExactBalance
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! A balanced host supported on any vortex parent remains balanced and
divisible after restriction to that parent's local vertex and hub types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_supported_local_exact_balance
    (P G:SimpleGraph V) (Hs:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Vort:Vortex U P D β ε m) (r i:ℕ)
    (hsupport:ordinaryHostResources G Hs⊆ordinaryRootResources (Vort.extendedVertices i) (Vort.extendedIndices i))
    (hbal:∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card):
    let f:=markedVortexVertexEmbedding Vort i;let g:=markedVortexHubEmbedding Vort i;
    (∀v,(G.comap f).degree v=2*(Finset.univ.filter (fun u=>Hs (f v) (g u))).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>Hs (f v) (g u))).card):=by
  intro f g
  have hh:=ordinary_supported_host_induced_exact_balance G Hs (Vort.extendedVertices i) (Vort.extendedIndices i) r hsupport hbal hdiv
  constructor
  · intro v
    have hv:=hh.1 v
    convert hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro u
    have hu:=hh.2 u
    convert hu using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
