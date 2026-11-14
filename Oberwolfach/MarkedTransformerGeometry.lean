module

public import Oberwolfach.MarkedInitialDiagramOldResources
public import Oberwolfach.MarkedForbiddenResourceRows
public import Oberwolfach.OrdinaryRawIntervalGeometry

@[expose] public section

/-! Geometric consequences used when combining marked transformers.
All statements use the fixed physical representation; marked heads are
pulled back through the permutation only at the prescribed places. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ}

theorem marked_support_rows_in_old (X Y Z W:Finset V)
    (hX:Disjoint (X\Z) W) (hY:Disjoint Y W):
    ∀ v∈X∪Y,v∈W→v∈Z:=by
  intro v hv hvW
  rcases Finset.mem_union.mp hv with hv|hv
  · by_contra hz
    exact Finset.disjoint_left.mp hX (Finset.mem_sdiff.mpr ⟨hv,hz⟩) hvW
  · exact (Finset.disjoint_left.mp hY hv hvW).elim

theorem marked_transformer_avoids_old_rows
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (X Y Z W:Finset V) (B:Finset U) (T:Finset (Finset V⊕(V×U)))
    (hX:Disjoint (X\Z) W) (hY:Disjoint Y W)
    (hT:∀ e∈T,MarkedResourceSupported tail head ktail khead π (X∪Y) e)
    (hOld:∀ e∈T,¬MarkedOldResource tail head ktail khead π Z B e):
    ∀ e∈T,¬MarkedOldResource tail head ktail khead π W B e:=by
  intro e he hold
  apply hOld e he
  have hs:=hT e he
  cases e with
  | inl e=>
    obtain ⟨a,ha,hat,hah⟩:=hs
    obtain ⟨a',ha',hat',hah'⟩:=hold
    have heq:a=a':=hp (ha.trans ha'.symm)
    subst a'
    exact ⟨a,ha,marked_support_rows_in_old X Y Z W hX hY _ hat hat',
      marked_support_rows_in_old X Y Z W hX hY _ hah hah'⟩
  | inr vu=>exact ⟨marked_support_rows_in_old X Y Z W hX hY _ hs hold.1,hold.2⟩

theorem marked_transformer_avoids_forbidden_resources
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (X Y Z W:Finset V) (B:Finset U) (T F:Finset (Finset V⊕(V×U)))
    (hX:Disjoint (X\Z) W) (hY:Disjoint Y W)
    (hT:∀ e∈T,MarkedResourceSupported tail head ktail khead π (X∪Y) e)
    (hOld:∀ e∈T,¬MarkedOldResource tail head ktail khead π Z B e)
    (hFR:markedForbiddenResourceRows π F⊆W)
    (hFH:∀ v z,Sum.inr (v,z)∈F→z∈B):Disjoint T F:=by
  have ho:=marked_transformer_avoids_old_rows hp X Y Z W B T hX hY hT hOld
  apply Finset.disjoint_left.mpr
  intro e he hf
  apply ho e he
  cases e with
  | inl e=>
    obtain ⟨a,ha,_,_⟩:=hT _ he
    have hh:=marked_forbidden_rim_endpoints F a (ha.symm ▸ hf)
    exact ⟨a,ha,hFR hh.1,hFR hh.2⟩
  | inr vu=>
    refine ⟨hFR ?_,hFH vu.1 vu.2 hf⟩
    exact Finset.mem_biUnion.mpr ⟨Sum.inr vu,hf,by simp [physicalResourceForbiddenRows]⟩

theorem marked_transformer_free_rows_separated (X Y Z:Finset V) (F:SimpleGraph V)
    (hZX:Z⊆X) (hYX:Disjoint Y X)
    (hF:permutationConflictGraph π b≤F)
    (hXX:∀ x∈X\Z,∀ y∈X\Z,x≠y→¬PermutationClose π b x y)
    (hXZ:∀ x∈X\Z,∀ y∈Z,¬PermutationClose π b x y)
    (hYY:∀ x∈Y,∀ y∈Y,¬F.Adj x y)
    (hYX':∀ x∈Y,∀ y∈X,¬F.Adj x y):
    (∀ x∈(X∪Y)\Z,∀ y∈Z,¬PermutationClose π b x y)∧
    (∀ x∈(X∪Y)\Z,∀ y∈(X∪Y)\Z,x≠y→¬PermutationClose π b x y):=by
  constructor
  · intro x hx y hy
    obtain ⟨hx,hxz⟩:=Finset.mem_sdiff.mp hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hXZ x (Finset.mem_sdiff.mpr ⟨hx,hxz⟩) y hy
    · intro hc
      have hne:x≠y:=fun he=>Finset.disjoint_left.mp hYX hx (he.symm ▸ hZX hy)
      exact hYX' x hx y (hZX hy) (hF ⟨hne,hc⟩)
  · intro x hx y hy hne
    obtain ⟨hx,hxz⟩:=Finset.mem_sdiff.mp hx
    obtain ⟨hy,hyz⟩:=Finset.mem_sdiff.mp hy
    rcases Finset.mem_union.mp hx with hx|hx <;> rcases Finset.mem_union.mp hy with hy|hy
    · exact hXX x (Finset.mem_sdiff.mpr ⟨hx,hxz⟩) y (Finset.mem_sdiff.mpr ⟨hy,hyz⟩) hne
    · intro hc;exact hYX' y hy x hx (hF ⟨hne.symm,(permutationClose_symm π b _ _).mp hc⟩)
    · intro hc;exact hYX' x hx y hy (hF ⟨hne,hc⟩)
    · intro hc;exact hYY x hx y hy (hF ⟨hne,hc⟩)

theorem permutationConflictGraph_degree (π:Equiv.Perm V) (b:ℕ) (v:V):
    (permutationConflictGraph π b).degree v≤2*b+1:=by
  rw [←SimpleGraph.card_neighborFinset_eq_degree,←Fintype.card_coe]
  let f:((permutationConflictGraph π b).neighborFinset v)→{y:V // PermutationClose π b v y}:=
    fun y=>⟨y.val,((permutationConflictGraph π b).mem_neighborFinset v y.val).mp y.property |>.2⟩
  have hf:Function.Injective f:=by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z:{y:V // PermutationClose π b v y}=>z.val) he
  exact (Fintype.card_le_of_injective f hf).trans (permutationClose_neighbour_card π b v)

end Oberwolfach
