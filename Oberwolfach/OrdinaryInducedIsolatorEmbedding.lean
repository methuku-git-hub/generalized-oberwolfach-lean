module

public import Oberwolfach.OrdinaryIsolatorConfigurations
public import Oberwolfach.InducedSetEmbedding

@[expose] public section
/-! An ambient isolator entirely supported on two selected domains gives an
isolator in the induced host, with all density and conflict conditions kept. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryInducedIsolator (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (k:ℕ) (θ α:ℝ) (x y:A)
    (C:{C:OrdinaryIsolatorConfiguration P Q F H k θ α x.val y.val //
      C.hub∈B ∧ C.vertices.val⊆A}):
    OrdinaryIsolatorConfiguration (P.induce (A:Set V)) (Q.induce (A:Set V)) (F.induce (A:Set V))
      (fun (v:A) (u:B)=>H v.val u.val) k θ α x y := by
  let S:Finset A:=C.val.vertices.val.subtype (fun v=>v∈A)
  have he:S.image (Subtype.val:A→V)=C.val.vertices.val:=by
    ext v
    simp only [S,Finset.mem_image,Finset.mem_subtype]
    constructor
    · rintro ⟨w,hw,rfl⟩;exact hw
    · intro hv;exact ⟨⟨v,C.property.2 hv⟩,hv,rfl⟩
  have hcard:S.card=k:=by
    have hh:=congrArg Finset.card he
    rw [Finset.card_image_of_injective _ Subtype.val_injective,C.val.vertices.property] at hh
    exact hh
  let Sfixed:FixedSubset A k:=⟨S,hcard⟩
  have hemb:(inducedSetEmbedding A Sfixed).val=C.val.vertices.val:=by
    ext v
    simp only [inducedSetEmbedding,Sfixed,Finset.mem_map]
    constructor
    · rintro ⟨w,hw,rfl⟩
      have hh : w.val∈S.image (Subtype.val:A→V):=Finset.mem_image.mpr ⟨w,hw,rfl⟩
      rw [he] at hh
      exact hh
    · intro hv
      have hv' : v ∈ S.image (Subtype.val : A → V) := by rw [he]; exact hv
      obtain ⟨w,hw,hwv⟩ := Finset.mem_image.mp hv'
      exact ⟨w,hw,hwv⟩
  refine ⟨⟨C.val.hub,C.property.1⟩,Sfixed,?_,?_,?_,?_,?_⟩
  · constructor
    · simpa [Sfixed,S,Finset.mem_subtype] using C.val.endpoints.1
    · simpa [Sfixed,S,Finset.mem_subtype] using C.val.endpoints.2
  · intro v w hvw
    have hs: v.val∈C.val.vertices.val ∧ w.val∈C.val.vertices.val:=by
      have hh:=(spanningRestriction_adj (P.induce (A:Set V)) S v w).mp hvw
      exact ⟨(Finset.mem_subtype.mp hh.2.1),Finset.mem_subtype.mp hh.2.2⟩
    have hp:P.Adj v.val w.val:=((spanningRestriction_adj (P.induce (A:Set V)) S v w).mp hvw).1
    apply C.val.rim_edges
    exact (spanningRestriction_adj P C.val.vertices.val v.val w.val).mpr ⟨hp,hs.1,hs.2⟩
  · intro v hv
    exact C.val.spokes v.val (Finset.mem_subtype.mp hv)
  · intro v hv w hw
    exact C.val.independent v.val (Finset.mem_subtype.mp hv) w.val (Finset.mem_subtype.mp hw)
  · intro v hv
    have hh:=C.val.density v.val (Finset.mem_subtype.mp hv)
    have hd:=inducedSetEmbedding_degree P A Sfixed v
    rw [hemb] at hd
    rw [hd]
    exact hh

theorem ordinary_induced_isolator_injective (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (k:ℕ) (θ α:ℝ) (x y:A):
    Function.Injective (ordinaryInducedIsolator P Q F H A B k θ α x y):=by
  intro C D h
  apply Subtype.ext
  apply OrdinaryIsolatorConfiguration.encoding_injective
  have hhub:=congrArg (fun E=>E.hub.val) h
  have hs:=congrArg (fun E=>(E.vertices.val.image (Subtype.val:A→V))) h
  have he (E:{E:OrdinaryIsolatorConfiguration P Q F H k θ α x.val y.val // E.hub∈B ∧ E.vertices.val⊆A}):
      ((ordinaryInducedIsolator P Q F H A B k θ α x y E).vertices.val.image (Subtype.val:A→V))=E.val.vertices.val:=by
    ext v
    simp only [ordinaryInducedIsolator,Finset.mem_image,Finset.mem_subtype]
    constructor
    · rintro ⟨w,hw,rfl⟩;exact hw
    · intro hv;exact ⟨⟨v,E.property.2 hv⟩,hv,rfl⟩
  rw [he,he] at hs
  exact Prod.ext hhub (Subtype.ext hs)
end Oberwolfach
