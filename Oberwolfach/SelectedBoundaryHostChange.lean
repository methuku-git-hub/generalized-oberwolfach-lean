module

public import Oberwolfach.LocalFactorGraphChoice
public import Oberwolfach.EndpointPairingGraph

@[expose] public section

/-! Retype selected boundary objects in the actual remaining host. Only
membership proofs change: cycles, endpoint assignments, and physical graphs
are retained exactly. No weighting or sampled candidate is recomputed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem selected_factor_change_host (Q R F:SimpleGraph V) (T Y:Finset V) (r:ℕ)
    (D:Finset (LocalOrdinaryCycle Q F T r))
    (hD:∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E))
    (hY:D.biUnion localOrdinaryVertices=Y) (hR:localOrdinaryFactorGraph D≤R):
    ∃ f:D↪LocalOrdinaryCycle R F Y r,
      (∀ C,(f C).val.val.val=C.val.val.val.val) ∧
      let D':=Finset.univ.image f
      (∀ C∈D',∀ E∈D',C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
        D'.biUnion localOrdinaryVertices=Y ∧ localOrdinaryFactorGraph D'=localOrdinaryFactorGraph D:=by
  let f:D→LocalOrdinaryCycle R F Y r:=fun C=>⟨⟨C.val.val.val,by
    intro a b hab;exact hR ((localOrdinaryFactorGraph_adj D a b).mpr ⟨C.val,C.property,hab⟩)⟩,
      ⟨by
        intro a ha;rw [←hY]
        exact Finset.mem_biUnion.mpr ⟨C.val,C.property,Set.mem_toFinset.mpr ha⟩,
        C.val.property.2⟩⟩
  have hinj:Function.Injective f:=by
    intro C E he
    have hh:=congrArg (fun C:LocalOrdinaryCycle R F Y r=>C.val.val.val) he
    apply Subtype.ext;apply Subtype.ext;apply Subtype.ext;apply Subtype.ext
    exact hh
  let e:D↪LocalOrdinaryCycle R F Y r:=⟨f,hinj⟩
  have hverts (C:D):localOrdinaryVertices (e C)=localOrdinaryVertices C.val:=rfl
  refine ⟨e,fun _=>rfl,?_,?_,?_⟩
  · intro C hC E hE hne
    obtain ⟨c,_,rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hE
    rw [hverts,hverts]
    exact hD c.val c.property a.val a.property (fun h=>hne (congrArg e (Subtype.ext h)))
  · apply Eq.trans ?_ hY
    ext a
    simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨_,⟨C,rfl⟩,ha⟩;exact ⟨C.val,C.property,ha⟩
    · rintro ⟨C,hC,ha⟩;exact ⟨e ⟨C,hC⟩,⟨⟨C,hC⟩,rfl⟩,ha⟩
  · ext a b
    simp only [localOrdinaryFactorGraph_adj,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨_,⟨C,rfl⟩,ha⟩;exact ⟨C.val,C.property,ha⟩
    · rintro ⟨C,hC,ha⟩;exact ⟨e ⟨C,hC⟩,⟨⟨C,hC⟩,rfl⟩,ha⟩

namespace EndpointPairing
variable {Q F:SimpleGraph V} {A B:Finset V}

def changeHost (P:EndpointPairing Q F A B) (R:SimpleGraph V) (hR:P.graph≤R):
    EndpointPairing R F A B where
  disjoint_parts:=P.disjoint_parts
  left:=P.left
  right:=P.right
  adjacent:=fun u=>⟨hR ⟨u,Or.inr ⟨rfl,Or.inl rfl⟩⟩,hR ⟨u,Or.inr ⟨rfl,Or.inr rfl⟩⟩⟩
  avoid:=P.avoid
  disjoint_ranges:=P.disjoint_ranges
  cover:=P.cover

theorem changeHost_graph (P:EndpointPairing Q F A B) (R:SimpleGraph V) (hR:P.graph≤R):
    (P.changeHost R hR).graph=P.graph:=rfl

theorem changeHost_after_deletion (P:EndpointPairing Q F A B) (Z:SimpleGraph V)
    (hZ:Disjoint P.graph Z):
    ∃ P':EndpointPairing (Q\Z) F A B,P'.graph=P.graph ∧ P'.left=P.left ∧ P'.right=P.right:=by
  have hR:P.graph≤Q\Z:=by
    intro a b hab
    exact ⟨((spanningRestriction_adj Q (A∪B) a b).mp (P.graph_le hab)).1,
      fun hz=>disjoint_graphs_no_common_edge _ _ hZ a b hab hz⟩
  exact ⟨P.changeHost (Q\Z) hR,rfl,rfl,rfl⟩

end EndpointPairing
end Oberwolfach
