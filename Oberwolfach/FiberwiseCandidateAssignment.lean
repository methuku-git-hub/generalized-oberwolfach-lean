module

public import Oberwolfach.RealizationHubCounts
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
/-! Finite candidates can be assigned injectively within their fixed key
classes when each target class has sufficient capacity. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fiberwise_injective_assignment {C D K:Type} [DecidableEq C] [DecidableEq D] [DecidableEq K]
    (A:Finset C) (B:Finset D) (f:C→K) (g:D→K)
    (hcard:∀k,(A.filter (fun c=>f c=k)).card≤(B.filter (fun d=>g d=k)).card):
    ∃h:{c // c∈A}↪{d // d∈B},∀c,g (h c).val=f c.val :=by
  let Akey:=fun k=>A.filter (fun c=>f c=k)
  let Bkey:=fun k=>B.filter (fun d=>g d=k)
  have hex:∀k,Nonempty ({c // c∈Akey k}↪{d // d∈Bkey k}):=by
    intro k
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_coe] using hcard k
  let e:=fun k=>Classical.choice (hex k)
  let v:=fun c:{c // c∈A}=>e (f c.val) ⟨c.val,Finset.mem_filter.mpr ⟨c.property,rfl⟩⟩
  let h:{c // c∈A}→{d // d∈B}:=fun c=>⟨(v c).val,(Finset.mem_filter.mp (v c).property).1⟩
  have hg:∀c,g (h c).val=f c.val:=fun c=>(Finset.mem_filter.mp (v c).property).2
  have hinj:Function.Injective h:=by
    intro c c' heq
    have hv:(v c).val=(v c').val:=congrArg Subtype.val heq
    have hk:f c.val=f c'.val:=(hg c).symm.trans (by rw [heq];exact hg c')
    have hfiber : ∀(k k':K),k=k'→∀(a:C)(b:C)(ha:a∈Akey k)(hb:b∈Akey k'),
        (e k ⟨a,ha⟩).val=(e k' ⟨b,hb⟩).val→a=b :=by
      intro k k' hkk a b ha hb hab
      subst k'
      have hpair : e k ⟨a,ha⟩ = e k ⟨b,hb⟩ := Subtype.ext hab
      have hsource := (e k).injective hpair
      exact congrArg (fun x : {x // x∈Akey k} => x.val) hsource
    apply Subtype.ext
    exact hfiber _ _ hk c.val c'.val _ _ hv
  exact ⟨⟨h,hinj⟩,hg⟩
end Oberwolfach
