module

public import Oberwolfach.MarkedFactorResourceDecomposition

@[expose] public section

/-! The two-factor hub trade on actual marked cycles. It uses the same
physical rim factors on both sides and changes exactly the spokes on Z. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}

 theorem marked_factor_hubs_disjoint
    (M N:Finset (MarkedCycleTuple tail head ktail khead m π b)) (u u':U) (hu:u≠u')
    (hr:Disjoint (M.biUnion (markedCyclePhysicalEdges tail head ktail khead m π b))
      (N.biUnion (markedCyclePhysicalEdges tail head ktail khead m π b))):
    Disjoint (M.biUnion (fun C=>markedCycleResourcesAtHub C u))
      (N.biUnion (fun C=>markedCycleResourcesAtHub C u')):=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  cases e with
  | inl e=>
    exact Finset.disjoint_left.mp hr ((marked_factor_at_hub_rim M u e).mp he) ((marked_factor_at_hub_rim N u' e).mp hf)
  | inr vz=>
    exact hu (((marked_factor_at_hub_spoke M u vz.1 vz.2).mp he).1.symm.trans
      ((marked_factor_at_hub_spoke N u' vz.1 vz.2).mp hf).1)

 theorem marked_hub_factor_trade (H₀ HK:V→U→Prop)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (A Z:Finset V) (hAZ:Disjoint A Z) (u u':U) (hu:u≠u')
    (M₀ M₁:Finset (MarkedCycleTuple tail head ktail khead m π b))
    (h₀:(∀ C∈M₀,∀ D∈M₀,C≠D→Disjoint (Finset.univ.image C.val) (Finset.univ.image D.val))∧
      M₀.biUnion (fun C=>Finset.univ.image C.val)=A)
    (h₁:(∀ C∈M₁,∀ D∈M₁,C≠D→Disjoint (Finset.univ.image C.val) (Finset.univ.image D.val))∧
      M₁.biUnion (fun C=>Finset.univ.image C.val)=A∪Z)
    (hdis:Disjoint (M₀.biUnion (markedCyclePhysicalEdges tail head ktail khead m π b))
      (M₁.biUnion (markedCyclePhysicalEdges tail head ktail khead m π b)))
    (hH:∀ C∈M₀∪M₁,MarkedHubCompatible H₀ HK C.val u∧MarkedHubCompatible H₀ HK C.val u'):
    let P:=M₁.biUnion (fun C=>markedCycleResourcesAtHub C u)∪M₀.biUnion (fun C=>markedCycleResourcesAtHub C u')
    let N:=M₁.biUnion (fun C=>markedCycleResourcesAtHub C u')∪M₀.biUnion (fun C=>markedCycleResourcesAtHub C u)
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) P∧
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) N∧
    ∀ e:Finset V⊕(V×U),(if e∈P then (1:ℤ) else 0)-(if e∈N then 1 else 0)=
      (if e∈Z.image (fun v=>Sum.inr (v,u)) then 1 else 0)-
      (if e∈Z.image (fun v=>Sum.inr (v,u')) then 1 else 0):=by
  dsimp only
  have h0u:=marked_factor_at_hub_decomposition H₀ HK hp M₀ u h₀.1
    (fun C hC=>(hH C (Finset.mem_union_left _ hC)).1)
  have h0u':=marked_factor_at_hub_decomposition H₀ HK hp M₀ u' h₀.1
    (fun C hC=>(hH C (Finset.mem_union_left _ hC)).2)
  have h1u:=marked_factor_at_hub_decomposition H₀ HK hp M₁ u h₁.1
    (fun C hC=>(hH C (Finset.mem_union_right _ hC)).1)
  have h1u':=marked_factor_at_hub_decomposition H₀ HK hp M₁ u' h₁.1
    (fun C hC=>(hH C (Finset.mem_union_right _ hC)).2)
  refine ⟨resource_decomposition_union _ _ _ h1u h0u' (marked_factor_hubs_disjoint M₁ M₀ u u' hu hdis.symm),
    resource_decomposition_union _ _ _ h1u' h0u (marked_factor_hubs_disjoint M₁ M₀ u' u hu.symm hdis.symm),?_⟩
  intro e
  cases e with
  | inl e=>
    simp only [Finset.mem_union,marked_factor_at_hub_rim,Finset.mem_image,Sum.inr_ne_inl,and_false,exists_false,ite_false,sub_self]
  | inr vz=>
    rcases vz with ⟨v,z⟩
    have hmem (a:U):(Sum.inr (v,z):Finset V⊕(V×U))∈Z.image (fun v=>Sum.inr (v,a))↔v∈Z∧z=a:=by
      simp only [Finset.mem_image,Sum.inr.injEq,Prod.mk.injEq]
      constructor
      · rintro ⟨v',hv',rfl,hz⟩;exact ⟨hv',hz.symm⟩
      · rintro ⟨hv,hz⟩;exact ⟨v,hv,rfl,hz.symm⟩
    simp only [Finset.mem_union,marked_factor_at_hub_spoke,h₀.2,h₁.2,Finset.mem_union,hmem]
    have hvdis:¬(v∈A∧v∈Z):=fun h=>Finset.disjoint_left.mp hAZ h.1 h.2
    have hzdis:¬(z=u∧z=u'):=fun h=>hu (h.1.symm.trans h.2)
    by_cases ha:v∈A <;> by_cases hz:v∈Z <;> by_cases hu0:z=u <;> by_cases hu1:z=u' <;>
      simp_all only [true_or,or_true,false_or,or_false,true_and,and_true,false_and,and_false,
        not_true_eq_false,not_false_eq_true,ite_true,ite_false] <;> omega

end Oberwolfach
