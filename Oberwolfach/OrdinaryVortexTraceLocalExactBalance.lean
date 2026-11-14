module

public import Oberwolfach.OrdinarySupportedHostInducedExactBalance
public import Oberwolfach.OrdinaryProtectedTraceInvariant
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! At a noninitial vortex level the protected trace is supported on the
current parent pair, so exact global balance and divisibility transfer to it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_trace_local_exact_balance
    (P Q G:SimpleGraph V) (H Hs:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Vort:Vortex U P D β ε m) (r i:ℕ) (cost deepCost:ℕ→ℝ)
    (A:Finset (Sym2 V⊕(V×U)))
    (htrace:OrdinaryProtectedTrace Q H (fun k=>Vort.extendedVertices (k+1)) (fun k=>Vort.extendedVertices (k+2))
      (fun k=>Vort.extendedIndices (k+1)) (fun k=>Vort.extendedIndices (k+2)) cost deepCost (i+1) A)
    (hstate:ordinaryHostResources G Hs=A)
    (hbal:∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card):
    let f:=markedVortexVertexEmbedding Vort (i+1);let g:=markedVortexHubEmbedding Vort (i+1);
    (∀v,(G.comap f).degree v=2*(Finset.univ.filter (fun u=>Hs (f v) (g u))).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>Hs (f v) (g u))).card):=by
  intro f g
  obtain ⟨R,S,hist,hroot,_⟩:=htrace
  have hroot':A⊆ordinaryRootResources (Vort.extendedVertices (i+1)) (Vort.extendedIndices (i+1)):=by
    rcases hroot with hz | hs
    · omega
    · simpa using hs
  have hsupport:ordinaryHostResources G Hs⊆ordinaryRootResources (Vort.extendedVertices (i+1)) (Vort.extendedIndices (i+1)):=by
    rw [hstate]
    exact hroot'
  have hh:=ordinary_supported_host_induced_exact_balance G Hs (Vort.extendedVertices (i+1))
    (Vort.extendedIndices (i+1)) r hsupport hbal hdiv
  constructor
  · intro v
    have hv:=hh.1 v
    convert hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro u
    have hu:=hh.2 u
    convert hu using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
