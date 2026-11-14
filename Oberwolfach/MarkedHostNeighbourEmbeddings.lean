module

public import Oberwolfach.MarkedEndpointAssignments
public import Oberwolfach.MarkedPhysicalEdges
public import Oberwolfach.MarkedFiniteRemainder

@[expose] public section

/-! Actual typed endpoint lists in any modified marked host. Injectivity
of ordered endpoints identifies each neighbour with its unique incident
occurrence. The resulting embeddings exhaust all occurrences at the root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K:Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]

def occurrenceRootNeighbours (f g:E→V) (v:V):Finset V:=
  Finset.univ.filter (fun x=>∃ e,f e=x∧g e=v)

def occurrenceNeighbourEquiv (f g:E→V) (hinj:Function.Injective (fun e=>(f e,g e))) (v:V):
    occurrenceRootNeighbours f g v≃{e:E // g e=v} where
  toFun x:=⟨Classical.choose ((Finset.mem_filter.mp x.property).2),
    (Classical.choose_spec ((Finset.mem_filter.mp x.property).2)).2⟩
  invFun e:=⟨f e.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.val,rfl,e.property⟩⟩
  left_inv x:=Subtype.ext (Classical.choose_spec ((Finset.mem_filter.mp x.property).2)).1
  right_inv e:=by
    apply Subtype.ext
    apply hinj
    apply Prod.ext
    · exact (Classical.choose_spec ((Finset.mem_filter.mp
        (show f e.val∈occurrenceRootNeighbours f g v from Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.val,rfl,e.property⟩)).2)).1
    · exact (Classical.choose_spec ((Finset.mem_filter.mp
        (show f e.val∈occurrenceRootNeighbours f g v from Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.val,rfl,e.property⟩)).2)).2.trans e.property.symm

def occurrenceNeighbourEmbedding (f g:E→V) (hinj:Function.Injective (fun e=>(f e,g e))) (v:V):
    occurrenceRootNeighbours f g v↪E where
  toFun x:=(occurrenceNeighbourEquiv f g hinj v x).val
  inj':=Subtype.val_injective.comp (occurrenceNeighbourEquiv f g hinj v).injective

theorem occurrenceNeighbourEmbedding_first (f g:E→V) (hinj:Function.Injective (fun e=>(f e,g e)))
    (v:V) (x:occurrenceRootNeighbours f g v):
    f (occurrenceNeighbourEmbedding f g hinj v x)=x.val:=
  (Classical.choose_spec ((Finset.mem_filter.mp x.property).2)).1

theorem occurrenceNeighbourEmbedding_root (f g:E→V) (hinj:Function.Injective (fun e=>(f e,g e)))
    (v:V) (x:occurrenceRootNeighbours f g v):
    g (occurrenceNeighbourEmbedding f g hinj v x)=v:=
  (occurrenceNeighbourEquiv f g hinj v x).property

theorem occurrenceNeighbourEmbedding_exhaustive (f g:E→V) (hinj:Function.Injective (fun e=>(f e,g e)))
    (v:V) (e:E) (he:g e=v):∃ x,occurrenceNeighbourEmbedding f g hinj v x=e:=by
  obtain ⟨x,hx⟩:=(occurrenceNeighbourEquiv f g hinj v).surjective ⟨e,he⟩
  exact ⟨x,congrArg Subtype.val hx⟩

theorem occurrenceRootNeighbours_card (f g:E→V) (hinj:Function.Injective (fun e=>(f e,g e))) (v:V):
    (occurrenceRootNeighbours f g v).card=(Finset.univ.filter (fun e=>g e=v)).card:=by
  have hh:=Fintype.card_congr (occurrenceNeighbourEquiv f g hinj v)
  calc
    _ = Fintype.card (occurrenceRootNeighbours f g v) := (Fintype.card_coe _).symm
    _ = Fintype.card {e:E // g e=v} := hh
    _ = _ := Fintype.card_subtype (fun e:E=>g e=v)

def markedNeighbourArcEmbedding (f₀ g₀:E→V) (fₖ gₖ:K→V)
    (h₀:Function.Injective (fun e=>(f₀ e,g₀ e))) (hₖ:Function.Injective (fun e=>(fₖ e,gₖ e))) (v:V):
    occurrenceRootNeighbours f₀ g₀ v⊕occurrenceRootNeighbours fₖ gₖ v↪E⊕K:=
  (occurrenceNeighbourEmbedding f₀ g₀ h₀ v).sumMap (occurrenceNeighbourEmbedding fₖ gₖ hₖ v)

theorem markedNeighbourArcEmbedding_first (f₀ g₀:E→V) (fₖ gₖ:K→V)
    (h₀:Function.Injective (fun e=>(f₀ e,g₀ e))) (hₖ:Function.Injective (fun e=>(fₖ e,gₖ e))) (v:V)
    (x:occurrenceRootNeighbours f₀ g₀ v⊕occurrenceRootNeighbours fₖ gₖ v):
    Sum.elim f₀ fₖ (markedNeighbourArcEmbedding f₀ g₀ fₖ gₖ h₀ hₖ v x)=
      taggedSubsetValue (occurrenceRootNeighbours f₀ g₀ v) (occurrenceRootNeighbours fₖ gₖ v) x:=by
  cases x with
  | inl x=>exact occurrenceNeighbourEmbedding_first f₀ g₀ h₀ v x
  | inr x=>exact occurrenceNeighbourEmbedding_first fₖ gₖ hₖ v x

theorem markedNeighbourArcEmbedding_root (f₀ g₀:E→V) (fₖ gₖ:K→V)
    (h₀:Function.Injective (fun e=>(f₀ e,g₀ e))) (hₖ:Function.Injective (fun e=>(fₖ e,gₖ e))) (v:V)
    (x:occurrenceRootNeighbours f₀ g₀ v⊕occurrenceRootNeighbours fₖ gₖ v):
    Sum.elim g₀ gₖ (markedNeighbourArcEmbedding f₀ g₀ fₖ gₖ h₀ hₖ v x)=v:=by
  cases x with
  | inl x=>exact occurrenceNeighbourEmbedding_root f₀ g₀ h₀ v x
  | inr x=>exact occurrenceNeighbourEmbedding_root fₖ gₖ hₖ v x

theorem markedNeighbourArcEmbedding_type (f₀ g₀:E→V) (fₖ gₖ:K→V)
    (h₀:Function.Injective (fun e=>(f₀ e,g₀ e))) (hₖ:Function.Injective (fun e=>(fₖ e,gₖ e))) (v:V)
    (x:occurrenceRootNeighbours f₀ g₀ v⊕occurrenceRootNeighbours fₖ gₖ v):
    (markedNeighbourArcEmbedding f₀ g₀ fₖ gₖ h₀ hₖ v x).isRight=x.isRight:=by cases x <;> rfl

theorem markedNeighbourArcEmbedding_exhaustive (f₀ g₀:E→V) (fₖ gₖ:K→V)
    (h₀:Function.Injective (fun e=>(f₀ e,g₀ e))) (hₖ:Function.Injective (fun e=>(fₖ e,gₖ e))) (v:V)
    (a:E⊕K) (ha:Sum.elim g₀ gₖ a=v):∃ x,markedNeighbourArcEmbedding f₀ g₀ fₖ gₖ h₀ hₖ v x=a:=by
  cases a with
  | inl e=>
    obtain ⟨x,hx⟩:=occurrenceNeighbourEmbedding_exhaustive f₀ g₀ h₀ v e ha
    exact ⟨Sum.inl x,congrArg Sum.inl hx⟩
  | inr e=>
    obtain ⟨x,hx⟩:=occurrenceNeighbourEmbedding_exhaustive fₖ gₖ hₖ v e ha
    exact ⟨Sum.inr x,congrArg Sum.inr hx⟩

end Oberwolfach
