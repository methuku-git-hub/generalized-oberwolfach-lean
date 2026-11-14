module

public import Oberwolfach.MarkedHostReindexing
public import Oberwolfach.MarkedDeletedHostIncidence

@[expose] public section

/-! Both physical and auxiliary incidence counts are invariant under exact
typed reindexing. All roots are retained, and the removed resource set is
compared without multiplying it by a sampling probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type}
    [Fintype V] [Fintype U] [Fintype E] [Fintype K] [Fintype E'] [Fintype K']
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
    [DecidableEq E'] [DecidableEq K']

theorem markedHostReindex_incidence_card
    (tail head:E → V) (ktail khead:K → V) (tail' head':E' → V) (ktail' khead':K' → V)
    (H₀ HK:V → U → Prop) (π:Equiv.Perm V) (e:E≃E') (k:K≃K')
    (ht:∀ a,tail' (e a)=tail a) (hh:∀ a,head' (e a)=head a)
    (hkt:∀ a,ktail' (k a)=ktail a) (hkh:∀ a,khead' (k a)=khead a)
    (hp':Function.Injective (markedPhysicalEdge tail' head' ktail' khead' π))
    (F:Finset (Finset V⊕(V×U)))
    (hF:F⊆markedFiniteResources tail head ktail khead π Finset.univ
      (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)))
    (physical:Bool) (z:V⊕U) :
    ((markedIncidentEdges tail' head' ktail' khead' π H₀ HK physical z).filter
      (fun a=>markedActivePhysical tail' head' ktail' khead' π H₀ HK a∈F)).card=
    ((markedIncidentEdges tail head ktail khead π H₀ HK physical z).filter
      (fun a=>markedActivePhysical tail head ktail khead π H₀ HK a∈F)).card := by
  apply markedActiveSubhostEmbedding_incidence_card tail' head' ktail' khead' tail head ktail khead
    π e.toEmbedding k.toEmbedding ht hh hkt hkh H₀ HK H₀ HK (fun _ _ h=>h) (fun _ _ h=>h) hp'
  rw [←marked_full_resources_active_image]
  exact hF

end Oberwolfach
