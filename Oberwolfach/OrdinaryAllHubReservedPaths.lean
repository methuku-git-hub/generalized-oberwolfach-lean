module

public import Oberwolfach.OrdinaryAllHubIntervalCapacity
public import Oberwolfach.LongReservedPrescribedPaths
public import Oberwolfach.RegularCycleIsomorphism

@[expose] public section
/-! Allocate a buffered source-factor path to every sampled request, and
keep every such path away from all short factor components. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_all_hub_reserved_paths
    {n K:ℕ} {U A B:Type} [Fintype U] [DecidableEq U] [Fintype A] [Fintype B]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (hn:0<n) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:0<d) (θ:ℝ) (hθ:0<θ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t) (w:U)
    (index : A ⊕ B ≃ retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t J w)
    (hcut:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K+1)≤θ/2)
    (hlarge:4*((m:ℝ)+1)/(θ*(θ/100))<(n:ℝ)^((1:ℝ)/4))
    (hcounts:∀g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g/d|<(n:ℝ)^(3/4:ℝ)/d)
    (hsupport:∀g v,rawMarkedPairSpokes π d raw g true true v w→
      ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g≠0):
    let I:={C:(F w).ConnectedComponent // K<Fintype.card C}
    let components:I↪(F w).ConnectedComponent:=Function.Embedding.subtype _;
    ∃block:A⊕B↪LongReservedBlockIndex (F w) components (m+1) d,
    ∃ext:∀a:A⊕B,Fin ((m+1)*d+5)↪Fin n,
    ∃inner:∀a:A⊕B,Fin ((m+1)*d+1)↪Fin n,
      (∀a (j:Fin ((m+1)*d+4)),(F w).Adj (ext a ⟨j.val,by omega⟩) (ext a ⟨j.val+1,by omega⟩)) ∧
      (∀a j,inner a j=ext a ⟨j.val+2,by omega⟩) ∧
      (∀a j,ext a j∈(components (block a).1).supp) ∧
      (∀a b,a≠b→Disjoint (Finset.univ.image (ext a)) (Finset.univ.image (ext b))) ∧
      (∀a j (C:(F w).ConnectedComponent),Fintype.card C≤K→ext a j∉C.supp) :=by
  intro I components
  let E:∀i:I,SimpleGraph.cycleGraph (Fintype.card (components i)) ≃g (components i).toSimpleGraph:=
    fun i=>Classical.choice (component_regular_two_cycle_iso (F w) (hF w) (components i)).2
  have hcap:=ordinary_all_hub_interval_capacity F hF hn π d m hd θ hθ raw t J w index hcut hlarge hcounts hsupport
  obtain ⟨block,ext,inner,hext,hadj,hinner,_,hmem,hdis⟩:=
    long_reserved_prescribed_paths (F w) (hF w) components E (m+1) d (fun _ : A⊕B=>d) (fun _=>le_rfl) hcap
  refine ⟨block,ext,inner,hadj,hinner,hmem,hdis,?_⟩
  intro a j C hshort hC
  have hne:components (block a).1≠C:=by
    intro heq
    have hl:K<Fintype.card (components (block a).1):=(block a).1.property
    rw [heq] at hl
    omega
  exact Set.disjoint_left.mp ((F w).pairwise_disjoint_supp_connectedComponent hne) (hmem a j) hC
end Oberwolfach
