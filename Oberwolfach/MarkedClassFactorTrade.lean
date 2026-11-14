module

public import Oberwolfach.FixedClassMarkedCycles
public import Oberwolfach.MarkedHubFactorTrade

@[expose] public section

/-! The actual fixed-class factors, attached to two original host hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}

 theorem class_marked_factor_trade (H₀ HK:V→U→Prop)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (A B Y Z:Finset V) (hYZ:Disjoint Y Z) (u u':U) (hu:u≠u')
    (hK:∀ v∈A,HK v u∧HK v u') (hO:∀ v∈B,H₀ v u∧H₀ v u')
    (M₀ M₁:Finset (ClassMarkedCycle tail head ktail khead m π b A B))
    (h₀:(∀ C∈M₀,∀ D∈M₀,C≠D→Disjoint (classMarkedCycleVertices C) (classMarkedCycleVertices D))∧
      M₀.biUnion classMarkedCycleVertices=Y)
    (h₁:(∀ C∈M₁,∀ D∈M₁,C≠D→Disjoint (classMarkedCycleVertices C) (classMarkedCycleVertices D))∧
      M₁.biUnion classMarkedCycleVertices=Y∪Z)
    (hdis:Disjoint (M₀.biUnion (fun C=>markedCyclePhysicalEdges tail head ktail khead m π b (classMarkedCycleAsMarked C)))
      (M₁.biUnion (fun C=>markedCyclePhysicalEdges tail head ktail khead m π b (classMarkedCycleAsMarked C)))):
    let P:=M₁.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u)∪
      M₀.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u')
    let N:=M₁.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u')∪
      M₀.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u)
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) P∧
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) N∧
    ∀ e:Finset V⊕(V×U),(if e∈P then (1:ℤ) else 0)-(if e∈N then 1 else 0)=
      (if e∈Z.image (fun v=>Sum.inr (v,u)) then 1 else 0)-
      (if e∈Z.image (fun v=>Sum.inr (v,u')) then 1 else 0):=by
  let f:ClassMarkedCycle tail head ktail khead m π b A B→MarkedCycleTuple tail head ktail khead m π b:=classMarkedCycleAsMarked
  have hlift (M:Finset (ClassMarkedCycle tail head ktail khead m π b A B)) (X:Finset V)
      (hM:(∀ C∈M,∀ D∈M,C≠D→Disjoint (classMarkedCycleVertices C) (classMarkedCycleVertices D))∧
        M.biUnion classMarkedCycleVertices=X):
      (∀ C∈M.image f,∀ D∈M.image f,C≠D→Disjoint (Finset.univ.image C.val) (Finset.univ.image D.val))∧
        (M.image f).biUnion (fun C=>Finset.univ.image C.val)=X:=by
    constructor
    · intro C hC D hD hCD
      obtain ⟨C₀,hC₀,rfl⟩:=Finset.mem_image.mp hC
      obtain ⟨D₀,hD₀,rfl⟩:=Finset.mem_image.mp hD
      exact hM.1 C₀ hC₀ D₀ hD₀ (fun he=>hCD (congrArg f he))
    · rw [Finset.image_biUnion]
      exact hM.2
  have hd:Disjoint ((M₀.image f).biUnion (markedCyclePhysicalEdges tail head ktail khead m π b))
      ((M₁.image f).biUnion (markedCyclePhysicalEdges tail head ktail khead m π b)):=by
    simpa only [Finset.image_biUnion,f] using hdis
  have hc:∀ C∈M₀.image f∪M₁.image f,MarkedHubCompatible H₀ HK C.val u∧MarkedHubCompatible H₀ HK C.val u':=by
    intro C hC
    have hC':C∈(M₀∪M₁).image f:=by simpa only [Finset.image_union] using hC
    obtain ⟨C₀,_,rfl⟩:=Finset.mem_image.mp hC'
    exact ⟨⟨(hK _ C₀.property.2.1).1,fun i=>(hO _ (C₀.property.2.2 i)).1⟩,
      ⟨(hK _ C₀.property.2.1).2,fun i=>(hO _ (C₀.property.2.2 i)).2⟩⟩
  have hh:=marked_hub_factor_trade H₀ HK hp Y Z hYZ u u' hu (M₀.image f) (M₁.image f)
    (hlift M₀ Y h₀) (hlift M₁ (Y∪Z) h₁) hd hc
  simpa only [Finset.image_biUnion,f] using hh

end Oberwolfach
