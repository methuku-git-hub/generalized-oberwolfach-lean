module

public import Oberwolfach.OrdinaryBoundaryFamiliesHostDecomposition
public import Oberwolfach.OrdinaryHostResourcePhysicalDisjoint
public import Oberwolfach.OrdinaryWheelFamilies
public import Oberwolfach.OrdinaryWheelRemainders
public import Oberwolfach.PhysicalHostDegreeBounds
public import Oberwolfach.PhysicalWheelFamilies

@[expose] public section
/-! Join the hub and endpoint wheel families into one decomposition,
    preserving exact outside coverage and a physical inner-degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_combine_boundary_wheel_families_avoiding
    (r:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (W:J→OrdinaryWheel Q F H r) (C:I→OrdinaryWheel Q F H r)
    (Rdeep:SimpleGraph V) (Sdeep:V→U→Prop)
    (hW:∀a b,a≠b→Disjoint (ordinaryWheelResources (W a)) (ordinaryWheelResources (W b)))
    (hC:∀a b,a≠b→Disjoint (ordinaryWheelResources (C a)) (ordinaryWheelResources (C b)))
    (hWdec:HasOrdinaryWheelDecomposition (wheelFamilyRim W) (wheelFamilySpokes W) r)
    (hCdec:HasOrdinaryWheelDecomposition (wheelFamilyRim C) (wheelFamilySpokes C) r)
    (havoid:∀i,Disjoint (ordinaryWheelResources (C i)) (ordinaryHostResources (wheelFamilyRim W) (wheelFamilySpokes W)))
    (hWdeep:Disjoint (ordinaryPhysicalGraph (wheelFamilyRim W) (wheelFamilySpokes W)) (ordinaryPhysicalGraph Rdeep Sdeep))
    (hCdeep:∀i,Disjoint (ordinaryWheelResources (C i)) (ordinaryHostResources Rdeep Sdeep))
    (hcoverR:∀v∉X,∀w,Q.Adj v w→(wheelFamilyRim C).Adj v w)
    (hcoverS:∀v∉X,∀z,H v z→wheelFamilySpokes C v z)
    (hcoverHub:∀z∉Z,∀v,H v z→wheelFamilySpokes W v z)
    (limit rbound sbound cbound cost:ℝ)
    (hWinner:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (wheelFamilyRim W) (wheelFamilySpokes W))
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit)
    (hCrim:∀v,((wheelFamilyRim C).degree v:ℝ)≤rbound)
    (hCrow:∀v,((Finset.univ.filter (wheelFamilySpokes C v)).card:ℝ)≤sbound)
    (hCcol:∀z,((Finset.univ.filter (fun v=>wheelFamilySpokes C v z)).card:ℝ)≤cbound)
    (hcost:rbound+sbound≤cost) (hcost':cbound≤cost):
    ∃R:SimpleGraph V,∃S:V→U→Prop,
      R≤Q ∧ (∀v z,S v z→H v z) ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources R S) ∧
      HasOrdinaryWheelDecomposition R S r ∧
      (Q\R).support⊆(X:Set V) ∧ (∀v z,H v z∧¬S v z→v∈X∧z∈Z) ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit+cost) ∧
      Disjoint (ordinaryPhysicalGraph R S) (ordinaryPhysicalGraph Rdeep Sdeep):=by
  let D₀:=wheelFamilyRim W
  let E₀:=wheelFamilySpokes W
  let D₁:=wheelFamilyRim C
  let E₁:=wheelFamilySpokes C
  let Ω:=ordinaryInnerVertices X Z
  have hres:Disjoint (ordinaryHostResources D₁ E₁) (ordinaryHostResources D₀ E₀):=by
    rw [wheelFamily_resources]
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    exact (Finset.disjoint_left.mp (havoid i)) hi hf
  have hdisR:Disjoint D₀ D₁:=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    have h₁:Sum.inl s(v,w)∈ordinaryHostResources D₁ E₁:=by
      rw [ordinaryHostResources_rim];exact hvw.2
    have h₀:Sum.inl s(v,w)∈ordinaryHostResources D₀ E₀:=by
      rw [ordinaryHostResources_rim];exact hvw.1
    exact (Finset.disjoint_left.mp hres) h₁ h₀
  have hdisS:∀v z,¬(E₀ v z∧E₁ v z):=by
    rintro v z ⟨h₀,h₁⟩
    have hh₁:Sum.inr (v,z)∈ordinaryHostResources D₁ E₁:=(ordinaryHostResources_spoke D₁ E₁ v z).mpr h₁
    have hh₀:Sum.inr (v,z)∈ordinaryHostResources D₀ E₀:=(ordinaryHostResources_spoke D₀ E₀ v z).mpr h₀
    exact (Finset.disjoint_left.mp hres) hh₁ hh₀
  let R:=D₀⊔D₁
  let S:V→U→Prop:=fun v z=>E₀ v z∨E₁ v z
  have hhost:=ordinary_boundary_families_host_decomposition r Q F H W C hW hC havoid
  have hdec:HasOrdinaryWheelDecomposition R S r:=ordinary_wheel_decomposition_union D₀ D₁ E₀ E₁ r hWdec hCdec hdisR hdisS
  have hCphys:∀w:V⊕U,((ordinaryPhysicalGraph D₁ E₁).degree w:ℝ)≤cost:=
    ordinary_physical_degree_bound D₁ E₁ rbound sbound cbound cost hCrim hCrow hCcol hcost hcost'
  have hunion:ordinaryPhysicalGraph R S=ordinaryPhysicalGraph D₀ E₀⊔ordinaryPhysicalGraph D₁ E₁:=by
    ext a b
    cases a <;> cases b <;> simp [R,S,ordinaryPhysicalGraph]
  have hspan:spanningRestriction (ordinaryPhysicalGraph R S) Ω≤
      spanningRestriction (ordinaryPhysicalGraph D₀ E₀) Ω⊔ordinaryPhysicalGraph D₁ E₁:=by
    intro a b hab
    have hh:=(spanningRestriction_adj _ _ _ _).mp hab
    rw [hunion] at hh
    rcases hh.1 with h₀|h₁
    · exact Or.inl ((spanningRestriction_adj _ _ _ _).mpr ⟨h₀,hh.2.1,hh.2.2⟩)
    · exact Or.inr h₁
  have hCresdeep:Disjoint (ordinaryHostResources D₁ E₁) (ordinaryHostResources Rdeep Sdeep):=by
    rw [wheelFamily_resources]
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    exact (Finset.disjoint_left.mp (hCdeep i)) hi hf
  have hCphysdeep:Disjoint (ordinaryPhysicalGraph D₁ E₁) (ordinaryPhysicalGraph Rdeep Sdeep):=
    (ordinary_host_resource_disjoint_iff_physical D₁ Rdeep E₁ Sdeep).mp hCresdeep
  have hdeep:Disjoint (ordinaryPhysicalGraph R S) (ordinaryPhysicalGraph Rdeep Sdeep):=by
    rw [hunion]
    exact disjoint_sup_left.mpr ⟨hWdeep,hCphysdeep⟩
  refine ⟨R,S,sup_le (wheelFamily_subhost W).1 (wheelFamily_subhost C).1,
    (fun v z h=>h.elim ((wheelFamily_subhost W).2 v z) ((wheelFamily_subhost C).2 v z)),hhost,hdec,?_,?_,?_,?_⟩
  · intro v hv
    by_contra hX
    obtain ⟨w,hw⟩:=hv
    exact hw.2 (Or.inr (hcoverR v hX w hw.1))
  · intro v z hz
    constructor
    · by_contra hv
      exact hz.2 (Or.inr (hcoverS v hv z hz.1))
    · by_contra hz'
      exact hz.2 (Or.inl (hcoverHub z hz' v hz.1))
  · intro w
    have hle:((spanningRestriction (ordinaryPhysicalGraph R S) Ω).degree w:ℝ)≤
        ((spanningRestriction (ordinaryPhysicalGraph D₀ E₀) Ω).degree w:ℝ)+
          ((ordinaryPhysicalGraph D₁ E₁).degree w:ℝ):=by
      have hh: (spanningRestriction (ordinaryPhysicalGraph R S) Ω).degree w≤
          (spanningRestriction (ordinaryPhysicalGraph D₀ E₀) Ω).degree w+
            (ordinaryPhysicalGraph D₁ E₁).degree w:=
        (SimpleGraph.degree_le_of_le hspan).trans (graph_degree_sup_le _ _ w)
      exact_mod_cast hh
    exact hle.trans (add_le_add (hWinner w) (hCphys w))
  · exact hdeep
end Oberwolfach
