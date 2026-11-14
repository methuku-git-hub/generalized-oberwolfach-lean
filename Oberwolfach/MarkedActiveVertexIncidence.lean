module

public import Oberwolfach.MarkedActiveSubhostIncidence
public import Oberwolfach.MarkedResourceEmbeddingGeometry

@[expose] public section

/-! Reindexing a typed host on smaller invariant vertex sets preserves
both physical and auxiliary incidences. In particular, restriction does
not enlarge a bound on the incidence of a specified resource set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K' : Type}
    [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [Fintype V'] [Fintype U'] [Fintype E'] [Fintype K']
    [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

def markedActiveVertexEmbedding (f : V↪V') (g : U↪U') (e : E↪E') (k : K↪K')
    (H₀ Hₖ : V→U→Prop) (H₀' Hₖ' : V'→U'→Prop)
    (h₀ : ∀ v u,H₀ v u→H₀' (f v) (g u))
    (hₖ : ∀ v u,Hₖ v u→Hₖ' (f v) (g u)) :
    MarkedActiveEdge E K H₀ Hₖ↪MarkedActiveEdge E' K' H₀' Hₖ' :=
  (e.sumMap k).sumMap
    ⟨fun vu=>⟨(f vu.val.1,g vu.val.2),vu.property.elim
      (fun h=>Or.inl (h₀ _ _ h)) (fun h=>Or.inr (hₖ _ _ h))⟩,
     fun a b h=>Subtype.ext (Prod.ext
       (f.injective (congrArg (fun vu : {vu : V'×U' // H₀' vu.1 vu.2 ∨ Hₖ' vu.1 vu.2}=>vu.val.1) h))
       (g.injective (congrArg (fun vu : {vu : V'×U' // H₀' vu.1 vu.2 ∨ Hₖ' vu.1 vu.2}=>vu.val.2) h)))⟩

theorem markedActiveVertexEmbedding_physical
    (tail head : E→V) (ktail khead : K→V)
    (tail' head' : E'→V') (ktail' khead' : K'→V')
    (ρ : Equiv.Perm V) (π : Equiv.Perm V') (f : V↪V') (g : U↪U')
    (hcomm : ∀ v,f (ρ v)=π (f v)) (e : E↪E') (k : K↪K')
    (ht : ∀ a,tail' (e a)=f (tail a)) (hh : ∀ a,head' (e a)=f (head a))
    (hkt : ∀ a,ktail' (k a)=f (ktail a)) (hkh : ∀ a,khead' (k a)=f (khead a))
    (H₀ Hₖ : V→U→Prop) (H₀' Hₖ' : V'→U'→Prop)
    (h₀ : ∀ v u,H₀ v u→H₀' (f v) (g u))
    (hₖ : ∀ v u,Hₖ v u→Hₖ' (f v) (g u))
    (a : MarkedActiveEdge E K H₀ Hₖ) :
    markedActivePhysical tail' head' ktail' khead' π H₀' Hₖ'
        (markedActiveVertexEmbedding f g e k H₀ Hₖ H₀' Hₖ' h₀ hₖ a)=
      markedResourceEmbedding f g (markedActivePhysical tail head ktail khead ρ H₀ Hₖ a) := by
  cases a with
  | inl a => cases a <;>
      simp [markedActiveVertexEmbedding,markedActivePhysical,markedPhysicalEdge,
        markedResourceEmbedding,ht,hh,hkt,hkh,hcomm]
  | inr vu => rfl

theorem markedActiveVertexEmbedding_incident
    (tail head : E→V) (ktail khead : K→V)
    (tail' head' : E'→V') (ktail' khead' : K'→V')
    (ρ : Equiv.Perm V) (π : Equiv.Perm V') (f : V↪V') (g : U↪U')
    (hcomm : ∀ v,f (ρ v)=π (f v)) (e : E↪E') (k : K↪K')
    (ht : ∀ a,tail' (e a)=f (tail a)) (hh : ∀ a,head' (e a)=f (head a))
    (hkt : ∀ a,ktail' (k a)=f (ktail a)) (hkh : ∀ a,khead' (k a)=f (khead a))
    (H₀ Hₖ : V→U→Prop) (H₀' Hₖ' : V'→U'→Prop)
    (h₀ : ∀ v u,H₀ v u→H₀' (f v) (g u))
    (hₖ : ∀ v u,Hₖ v u→Hₖ' (f v) (g u))
    (physical : Bool) (x : V⊕U) (a : MarkedActiveEdge E K H₀ Hₖ) :
    markedResourceIncident tail' head' ktail' khead' π H₀' Hₖ' physical (Sum.map f g x)
        (markedActiveVertexEmbedding f g e k H₀ Hₖ H₀' Hₖ' h₀ hₖ a) ↔
      markedResourceIncident tail head ktail khead ρ H₀ Hₖ physical x a := by
  cases x <;> cases a with
  | inl a => cases a <;> cases physical <;>
      simp [markedActiveVertexEmbedding,markedResourceIncident,ht,hh,hkt,hkh,←hcomm,f.injective.eq_iff]
  | inr vu => simp [markedActiveVertexEmbedding,markedResourceIncident,f.injective.eq_iff,g.injective.eq_iff]

theorem markedActiveVertexEmbedding_incidence_card_le
    (tail head : E→V) (ktail khead : K→V)
    (tail' head' : E'→V') (ktail' khead' : K'→V')
    (ρ : Equiv.Perm V) (π : Equiv.Perm V') (f : V↪V') (g : U↪U')
    (hcomm : ∀ v,f (ρ v)=π (f v)) (e : E↪E') (k : K↪K')
    (ht : ∀ a,tail' (e a)=f (tail a)) (hh : ∀ a,head' (e a)=f (head a))
    (hkt : ∀ a,ktail' (k a)=f (ktail a)) (hkh : ∀ a,khead' (k a)=f (khead a))
    (H₀ Hₖ : V→U→Prop) (H₀' Hₖ' : V'→U'→Prop)
    (h₀ : ∀ v u,H₀ v u→H₀' (f v) (g u))
    (hₖ : ∀ v u,Hₖ v u→Hₖ' (f v) (g u))
    (B : Finset (Finset V⊕(V×U))) (physical : Bool) (x : V⊕U) :
    ((markedIncidentEdges tail head ktail khead ρ H₀ Hₖ physical x).filter
      (fun a=>markedActivePhysical tail head ktail khead ρ H₀ Hₖ a∈B)).card ≤
    ((markedIncidentEdges tail' head' ktail' khead' π H₀' Hₖ' physical (Sum.map f g x)).filter
      (fun a=>markedActivePhysical tail' head' ktail' khead' π H₀' Hₖ' a∈
        B.image (markedResourceEmbedding f g))).card := by
  let F := markedActiveVertexEmbedding f g e k H₀ Hₖ H₀' Hₖ' h₀ hₖ
  have hphys := markedActiveVertexEmbedding_physical tail head ktail khead tail' head' ktail' khead'
    ρ π f g hcomm e k ht hh hkt hkh H₀ Hₖ H₀' Hₖ' h₀ hₖ
  have hinc := markedActiveVertexEmbedding_incident tail head ktail khead tail' head' ktail' khead'
    ρ π f g hcomm e k ht hh hkt hkh H₀ Hₖ H₀' Hₖ' h₀ hₖ physical x
  let C := (markedIncidentEdges tail head ktail khead ρ H₀ Hₖ physical x).filter
    (fun a=>markedActivePhysical tail head ktail khead ρ H₀ Hₖ a∈B)
  calc
    _ = (C.image F).card := (Finset.card_image_of_injective C F.injective).symm
    _ ≤ _ := by
      apply Finset.card_le_card
      intro a ha
      obtain ⟨b,hb,hab⟩ := Finset.mem_image.mp ha
      subst a
      obtain ⟨hbi,hba⟩ := Finset.mem_filter.mp hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · exact (hinc b).mpr (Finset.mem_filter.mp hbi).2
      · change markedActivePhysical tail' head' ktail' khead' π H₀' Hₖ' (F b)∈_
        rw [hphys]
        exact Finset.mem_image.mpr ⟨_,hba,rfl⟩

end Oberwolfach
