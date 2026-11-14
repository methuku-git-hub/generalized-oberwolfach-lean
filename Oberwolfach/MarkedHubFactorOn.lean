module

public import Oberwolfach.MarkedFactorPhysicalSupport

@[expose] public section

/-! An actual finite marked factor on a specified auxiliary row set,
with its unchanged cycle identifiers and associated physical graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

structure MarkedHubFactorOn (tail head:E→V) (ktail khead:K→V)
    (m:ℕ) (π:Equiv.Perm V) (b:ℕ) (H₀ HK:V→U→Prop) (u:U) (Y:Finset V) where
  cycles:Finset (HubMarkedCycle tail head ktail khead m π b H₀ HK u)
  disjoint:∀ C∈cycles,∀ D∈cycles,C≠D→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u D)
  covers:cycles.biUnion (hubMarkedCycleVertices u)=Y

namespace MarkedHubFactorOn
variable {u:U} {Y:Finset V}

def rim (P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK u Y):SimpleGraph V:=
  physicalEdgeGraph (P.cycles.biUnion (hubCyclePhysicalEdges u))

def graph (P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK u Y):SimpleGraph (V⊕U):=
  P.rim.map (Sum.inl:V→V⊕U)

theorem rim_degree (P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK u Y)
    (hsep:∀ v z,H₀ v u→HK z u→v≠π z) (v:V):P.rim.degree v≤2:=
  marked_factor_physical_degree u hsep P.cycles P.disjoint v

theorem graph_degree [Fintype U] [DecidableEq U]
    (P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK u Y)
    (hsep:∀ v z,H₀ v u→HK z u→v≠π z) (z:V⊕U):P.graph.degree z≤2:=by
  convert graph_map_degree_bound P.rim ⟨Sum.inl,Sum.inl_injective⟩ 2 (P.rim_degree hsep) z using 1 <;> congr!

theorem graph_restriction [Fintype U] [DecidableEq U]
    (P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK u Y):
    P.graph≤spanningRestriction ⊤ ((Y∪Y.image π).image (Sum.inl:V→V⊕U)):=
  marked_factor_physical_map_restriction u ⟨Sum.inl,Sum.inl_injective⟩ P.cycles Y P.covers

theorem graph_disjoint [Fintype U] [DecidableEq U]
    (P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK u Y) (F:SimpleGraph (V⊕U))
    (hF:Disjoint P.rim (F.comap (Sum.inl:V→V⊕U))):Disjoint P.graph F:=
  graph_map_disjoint_of_comap P.rim F ⟨Sum.inl,Sum.inl_injective⟩ hF

theorem spoke_once [DecidableEq U]
    (P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK u Y) (v:V) (hv:v∈Y):
    ∃! C:P.cycles,Sum.inr (v,u)∈markedWheelPhysicalResources (hubCycleWheel u C.val):=
  marked_factor_physical_spoke_once u P.cycles P.disjoint v (P.covers.symm ▸ hv)

end MarkedHubFactorOn
end Oberwolfach
