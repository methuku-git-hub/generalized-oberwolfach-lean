module

public import Oberwolfach.OrdinaryPhysicalPairMap
public import Oberwolfach.OrdinaryMappedDifferenceDegree

@[expose] public section
/-! Lift the physical leftover degree after separately proving the generic
graph difference bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U':Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

theorem ordinary_induced_packing_leftover_bound_generic
    (G D:SimpleGraph V) (H E:V→U→Prop) (φ:V↪V') (ψ:U↪U') (t:ℝ) (ht:0≤t)
    (hleft:∀a:V⊕U,(((ordinaryPhysicalGraph G H)\ordinaryPhysicalGraph D E).degree a:ℝ)≤t):
    ∀a:V'⊕U',(((ordinaryPhysicalGraph (G.map φ) (ordinaryMappedSpokes H φ ψ))\
      ordinaryPhysicalGraph (D.map φ) (ordinaryMappedSpokes E φ ψ)).degree a:ℝ)≤t:=by
  have hh:=ordinary_mapped_difference_degree_bound (ordinaryPhysicalGraph G H) (ordinaryPhysicalGraph D E)
    (φ.sumMap ψ) t ht hleft
  have he:((ordinaryPhysicalGraph G H).map (φ.sumMap ψ))\((ordinaryPhysicalGraph D E).map (φ.sumMap ψ))=
      ordinaryPhysicalGraph (G.map φ) (ordinaryMappedSpokes H φ ψ)\
        ordinaryPhysicalGraph (D.map φ) (ordinaryMappedSpokes E φ ψ):=by
    rw [←ordinary_physical_pair_map,←ordinary_physical_pair_map]
  intro a
  apply le_trans ?_ (hh a)
  have hd:=congrArg (fun S:SimpleGraph (V'⊕U')=>(S.degree a:ℝ)) he.symm
  convert le_of_eq hd using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
