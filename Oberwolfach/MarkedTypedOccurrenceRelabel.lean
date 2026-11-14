module

public import Oberwolfach.MarkedWheelEquivLoads
public import Oberwolfach.TypedMarkedIncidenceIndicators

@[expose] public section
/-! Exact transport of typed occurrence membership. Endpoint injectivity is
required so that the choice of an arc with given endpoints is unique. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K':Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [Fintype E] [Fintype K] [Fintype E'] [Fintype K']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V'} {ktail' khead':K'→V'}
  {m b:ℕ} {ρ:Equiv.Perm V} {π:Equiv.Perm V'} {H₀ HK:V→U→Prop} {H₀' HK':V'→U'→Prop}

theorem marked_canonical_arc_membership_relabel
    (f:V≃V') (g:U≃U') (hcomm:∀ x,f (ρ x)=π (f x))
    (e:E≃E') (k:K≃K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (hH₀:∀ x u,H₀ x u→H₀' (f x) (g u)) (hHK:∀ x u,HK x u→HK' (f x) (g u))
    (hE:Function.Injective (fun a:E=>(tail a,head a)))
    (hK:Function.Injective (fun a:K=>(ktail a,khead a)))
    (hE':Function.Injective (fun a:E'=>(tail' a,head' a)))
    (hK':Function.Injective (fun a:K'=>(ktail' a,khead' a)))
    (W:MarkedWheel tail head ktail khead m ρ b H₀ HK) (a:E⊕K) :
    let F:=markedWheelVertexEmbedding (m:=m) (b:=b) f.toEmbedding g.toEmbedding hcomm e k het heh hkt hkh hH₀ hHK
    CanonicalMarkedArcMem W.1 a ↔ CanonicalMarkedArcMem (F W).1 (Sum.map e k a) := by
  intro F
  have hh := markedCycleIncidence_vertex_embedding f.toEmbedding e k het heh hkt hkh W.1.val a
  change markedCycleIncidence tail' head' ktail' khead' m (F W).1.val (Sum.map e k a) =
    markedCycleIncidence tail head ktail khead m W.1.val a at hh
  rw [markedCycleIncidence_canonical_indicator hE' hK',
    markedCycleIncidence_canonical_indicator hE hK] at hh
  by_cases ha : CanonicalMarkedArcMem W.1 a <;>
    by_cases hb : CanonicalMarkedArcMem (F W).1 (Sum.map e k a) <;> simp_all
def markedTypedResourceEquiv (f:V≃V') (g:U≃U') (e:E≃E') (k:K≃K') :
    ((E⊕K)⊕(Bool×V×U)) ≃ ((E'⊕K')⊕(Bool×V'×U')) :=
  (e.sumCongr k).sumCongr ((Equiv.refl Bool).prodCongr (f.prodCongr g))

theorem marked_typed_occurrence_mem_relabel
    (f:V≃V') (g:U≃U') (hcomm:∀ x,f (ρ x)=π (f x))
    (e:E≃E') (k:K≃K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (hH₀:∀ x u,H₀ x u→H₀' (f x) (g u)) (hHK:∀ x u,HK x u→HK' (f x) (g u))
    (hE:Function.Injective (fun a:E=>(tail a,head a)))
    (hK:Function.Injective (fun a:K=>(ktail a,khead a)))
    (hE':Function.Injective (fun a:E'=>(tail' a,head' a)))
    (hK':Function.Injective (fun a:K'=>(ktail' a,khead' a)))
    (W:MarkedWheel tail head ktail khead m ρ b H₀ HK) (a:(E⊕K)⊕(Bool×V×U)) :
    let F:=markedWheelVertexEmbedding (m:=m) (b:=b) f.toEmbedding g.toEmbedding hcomm e k het heh hkt hkh hH₀ hHK
    a∈typedMarkedOccurrenceResources W ↔
      markedTypedResourceEquiv f g e k a∈typedMarkedOccurrenceResources (F W) := by
  intro F
  cases a with
  | inl a =>
    change Sum.inl a∈typedMarkedOccurrenceResources W ↔
      Sum.inl (Sum.map e k a)∈typedMarkedOccurrenceResources (F W)
    rw [typedMarkedOccurrenceResources_rim, typedMarkedOccurrenceResources_rim]
    exact marked_canonical_arc_membership_relabel f g hcomm e k het heh hkt hkh hH₀ hHK hE hK hE' hK' W a
  | inr a =>
    rcases a with ⟨mark,x,u⟩
    change Sum.inr (mark,x,u)∈typedMarkedOccurrenceResources W ↔
      Sum.inr (mark,f x,g u)∈typedMarkedOccurrenceResources (F W)
    rw [typedMarkedOccurrenceResources_spoke, typedMarkedOccurrenceResources_spoke]
    constructor
    · rintro ⟨i,hi⟩
      refine ⟨i, ?_⟩
      have hh := congrArg ((Equiv.refl Bool).prodCongr (f.prodCongr g)) hi
      simpa only [F,markedWheelVertexEmbedding,Function.Embedding.coeFn_mk,
        Equiv.prodCongr_apply,Equiv.refl_apply,Prod.map_apply,Function.comp_apply] using hh
    · rintro ⟨i,hi⟩
      refine ⟨i, ?_⟩
      apply ((Equiv.refl Bool).prodCongr (f.prodCongr g)).injective
      simpa only [F,markedWheelVertexEmbedding,Function.Embedding.coeFn_mk,
        Equiv.prodCongr_apply,Equiv.refl_apply,Prod.map_apply,Function.comp_apply] using hi
theorem marked_typed_occurrence_image_relabel
    (f:V≃V') (g:U≃U') (hcomm:∀ x,f (ρ x)=π (f x))
    (e:E≃E') (k:K≃K')
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (hH₀:∀ x u,H₀ x u→H₀' (f x) (g u)) (hHK:∀ x u,HK x u→HK' (f x) (g u))
    (hE:Function.Injective (fun a:E=>(tail a,head a)))
    (hK:Function.Injective (fun a:K=>(ktail a,khead a)))
    (hE':Function.Injective (fun a:E'=>(tail' a,head' a)))
    (hK':Function.Injective (fun a:K'=>(ktail' a,khead' a)))
    (W:MarkedWheel tail head ktail khead m ρ b H₀ HK) :
    let F:=markedWheelVertexEmbedding (m:=m) (b:=b) f.toEmbedding g.toEmbedding hcomm e k het heh hkt hkh hH₀ hHK
    typedMarkedOccurrenceResources (F W) =
      (typedMarkedOccurrenceResources W).image (markedTypedResourceEquiv f g e k) := by
  intro F
  let ea := markedTypedResourceEquiv f g e k
  ext y
  constructor
  · intro hy
    refine Finset.mem_image.mpr ⟨ea.symm y, ?_, ea.apply_symm_apply y⟩
    apply (marked_typed_occurrence_mem_relabel f g hcomm e k het heh hkt hkh hH₀ hHK hE hK hE' hK' W (ea.symm y)).mpr
    simpa only [ea,Equiv.apply_symm_apply] using hy
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact (marked_typed_occurrence_mem_relabel f g hcomm e k het heh hkt hkh hH₀ hHK hE hK hE' hK' W x).mp hx
end Oberwolfach
