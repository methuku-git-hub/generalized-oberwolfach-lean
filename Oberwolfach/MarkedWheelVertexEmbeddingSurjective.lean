module

public import Oberwolfach.MarkedWheelVertexEmbedding

@[expose] public section

/-! Removing vertices outside the support of a marked host preserves all
of its wheels. Both directed arc types and the hub predicate are pulled
back exactly; no physical superhost injection is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K':Type} [DecidableEq V] [DecidableEq U]
  [DecidableEq V'] [DecidableEq U']
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V'} {ktail' khead':K'→V'}
  {m b:ℕ} {ρ:Equiv.Perm V} {π:Equiv.Perm V'} {H₀ HK:V→U→Prop} {H₀' HK':V'→U'→Prop}

theorem markedWheelVertexEmbedding_surjective
    (f:V↪V') (g:U↪U') (hcomm:∀ x,f (ρ x)=π (f x))
    (e:E→E') (k:K→K') (hes:Function.Surjective e) (hks:Function.Surjective k)
    (het:∀ a,tail' (e a)=f (tail a)) (heh:∀ a,head' (e a)=f (head a))
    (hkt:∀ a,ktail' (k a)=f (ktail a)) (hkh:∀ a,khead' (k a)=f (khead a))
    (hH₀:∀ x u,H₀ x u↔H₀' (f x) (g u)) (hHK:∀ x u,HK x u↔HK' (f x) (g u))
    (hrows:∀ C:MarkedCycleTuple tail' head' ktail' khead' m π b,∀ i,C.val i∈Set.range f)
    (hhubs:∀ W:MarkedWheel tail' head' ktail' khead' m π b H₀' HK',W.2.val∈Set.range g):
    Function.Surjective (markedWheelVertexEmbedding (m:=m) (b:=b) f g hcomm e k het heh hkt hkh
      (fun x u=>(hH₀ x u).mp) (fun x u=>(hHK x u).mp)):=by
  intro W
  let C:Fin (m+1)→V:=fun i=>Classical.choose (hrows W.1 i)
  have hC:∀ i,f (C i)=W.1.val i:=fun i=>Classical.choose_spec (hrows W.1 i)
  have hCs:f∘C=W.1.val:=funext hC
  let c:MarkedCycleTuple tail head ktail khead m ρ b:=⟨C,
    (permutationSeparated_embedding_iff f ρ π hcomm b C).mp (by rw [hCs];exact W.1.property.1),
    by
      intro i
      obtain ⟨a,ht,hh⟩:=W.1.property.2.1 i
      obtain ⟨a,rfl⟩:=hes a
      exact ⟨a,f.injective ((het a).symm.trans (ht.trans (hC i.castSucc).symm)),
        f.injective ((heh a).symm.trans (hh.trans (hC i.succ).symm))⟩,
    by
      obtain ⟨a,ht,hh⟩:=W.1.property.2.2
      obtain ⟨a,rfl⟩:=hks a
      exact ⟨a,f.injective ((hkt a).symm.trans (ht.trans (hC (Fin.last m)).symm)),
        f.injective ((hkh a).symm.trans (hh.trans (hC 0).symm))⟩⟩
  obtain ⟨u,hu⟩:=hhubs W
  have hcHub:MarkedHubCompatible H₀ HK c.val u:=by
    refine ⟨(hHK _ _).mpr ?_,?_⟩
    · simpa only [c,hC,hu] using W.2.property.1
    · intro i
      apply (hH₀ _ _).mpr
      simpa only [c,hC,hu] using W.2.property.2 i
  refine ⟨⟨c,⟨u,hcHub⟩⟩,?_⟩
  have hcycle:(markedWheelVertexEmbedding (m:=m) (b:=b) f g hcomm e k het heh hkt hkh
      (fun x u=>(hH₀ x u).mp) (fun x u=>(hHK x u).mp) ⟨c,⟨u,hcHub⟩⟩).1=W.1:=
    Subtype.ext hCs
  apply Sigma.ext hcycle
  apply (Subtype.heq_iff_coe_eq (fun z=>by rw [hcycle])).mpr
  exact hu

end Oberwolfach
