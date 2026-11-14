module

public import Oberwolfach.IndexedMarkedRealizationGeometry
public import Oberwolfach.MarkedTransformerGeometry

@[expose] public section

/-! Exclusion and monotonicity for fixed physical resources. An edge is
pulled back to its auxiliary endpoints using the injective physical map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}

theorem marked_old_resource_mono {Z Z':Finset V} {B B':Finset U}
    (hZ:Z⊆Z') (hB:B⊆B') (e:Finset V⊕(V×U))
    (he:MarkedOldResource tail head ktail khead π Z B e):
    MarkedOldResource tail head ktail khead π Z' B' e:=by
  cases e with
  | inl e=>obtain ⟨a,ha,h₁,h₂⟩:=he;exact ⟨a,ha,hZ h₁,hZ h₂⟩
  | inr vu=>exact ⟨hZ he.1,hB he.2⟩

theorem marked_old_resource_supported {Z:Finset V} {B:Finset U}
    (e:Finset V⊕(V×U)) (he:MarkedOldResource tail head ktail khead π Z B e):
    MarkedResourceSupported tail head ktail khead π Z e:=by
  cases e with
  | inl e=>exact he
  | inr vu=>exact he.1

theorem marked_supported_avoids_old
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    {X Z:Finset V} (B:Finset U) (hd:Disjoint X Z)
    (e:Finset V⊕(V×U)) (he:MarkedResourceSupported tail head ktail khead π X e):
    ¬MarkedOldResource tail head ktail khead π Z B e:=by
  intro hold
  cases e with
  | inl e=>
    obtain ⟨a,ha,hat,hah⟩:=he
    obtain ⟨a',ha',hat',hah'⟩:=hold
    have h:a=a':=hp (ha.trans ha'.symm)
    exact Finset.disjoint_left.mp hd hat (h.symm ▸ hat')
  | inr vu=>exact Finset.disjoint_left.mp hd he hold.1

theorem marked_transformer_disjoint_supported
    [Fintype V]
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (X Z W:Finset V) (B:Finset U) (T F:Finset (Finset V⊕(V×U)))
    (hX:Disjoint (X\Z) W)
    (hT:∀ e∈T,MarkedResourceSupported tail head ktail khead π X e)
    (hOld:∀ e∈T,¬MarkedOldResource tail head ktail khead π Z B e)
    (hF:∀ e∈F,MarkedOldResource tail head ktail khead π W B e):Disjoint T F:=by
  have hh:=marked_transformer_avoids_old_rows hp X ∅ Z W B T hX (by simp)
    (by simpa only [Finset.union_empty] using hT) hOld
  exact Finset.disjoint_left.mpr (fun e he hf=>hh e he (hF e hf))

end Oberwolfach
