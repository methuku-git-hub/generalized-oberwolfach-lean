module

public import Oberwolfach.MixedClassPhysicalView
public import Oberwolfach.ClassSharedRawProduct

@[expose] public section
/-! Combine marked and ordinary physical views with class-local interval
experiments on one common exposure. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def mixedPointwiseView {Ω E:Type} {A B:E→Type} (marked:Bool)
    (f:Ω→∀ e,A e) (g:Ω→∀ e,B e):Ω→∀ e,mixedClassState marked (A e) (B e):=by
  cases marked
  · exact g
  · exact f

theorem mixed_pointwise_law {Ω E:Type} [Fintype Ω] [Fintype E] [DecidableEq E]
    {A B:E→Type} [∀ e,Fintype (A e)] [∀ e,Fintype (B e)]
    (physical:FiniteLaw Ω) (marked:Bool) (f:Ω→∀ e,A e) (g:Ω→∀ e,B e)
    (μ:∀ e,FiniteLaw (A e)) (ν:∀ e,FiniteLaw (B e))
    (hf:physical.map f=FiniteLaw.pi μ) (hg:physical.map g=FiniteLaw.pi ν):
    physical.map (mixedPointwiseView marked f g)=FiniteLaw.pi (fun e=>mixedClassLaw marked (μ e) (ν e)):=by
  cases marked with
  | false => exact hg
  | true => exact hf

theorem mixed_class_shared_raw_product {I Ω E C:Type} [Fintype I] [DecidableEq I]
    [Fintype Ω] [Fintype E] [DecidableEq E] [Fintype C]
    {J:I→Type} [∀ i,Fintype (J i)] [∀ i,DecidableEq (J i)]
    {A B:∀ i,E→Type} [∀ i e,Fintype (A i e)] [∀ i e,Fintype (B i e)]
    {T:∀ i,J i→Type} [∀ i e,Fintype (T i e)]
    (physical:FiniteLaw Ω) (colour:Ω→C) (marked:I→Bool)
    (f:∀ i,Ω→∀ e,A i e) (g:∀ i,Ω→∀ e,B i e)
    (μ:∀ i e,FiniteLaw (A i e)) (ν:∀ i e,FiniteLaw (B i e)) (τ:∀ i e,FiniteLaw (T i e))
    (hf:∀ i,physical.map (f i)=FiniteLaw.pi (μ i))
    (hg:∀ i,physical.map (g i)=FiniteLaw.pi (ν i)):
    let S:∀ i,E⊕J i→Type:=fun i e=>
      match e with
      | Sum.inl e=>mixedClassState (marked i) (A i e) (B i e)
      | Sum.inr e=>T i e
    letI : ∀ i e,Fintype (S i e):=fun i e=>by cases e <;> dsimp [S] <;> infer_instance
    let law:∀ i e,FiniteLaw (S i e):=fun i (e:E⊕J i)=>
      match e with
      | Sum.inl e=>mixedClassLaw (marked i) (μ i e) (ν i e)
      | Sum.inr e=>τ i e
    let view:=fun i=>mixedPointwiseView (marked i) (f i) (g i)
    let noise:=fun i=>FiniteLaw.pi (fun e=>law i (Sum.inr e))
    let global:=physical.prod (FiniteLaw.pi noise);
    global.map (fun z=>colour z.1)=physical.map colour ∧
    ∀ i,global.map (fun z=>combineSumCoordinates (view i z.1) (z.2 i))=FiniteLaw.pi (law i):=by
  intro S law view noise global
  letI : ∀ i e,Fintype (S i e):=fun i e=>by cases e <;> dsimp [S] <;> infer_instance
  have hv:∀ i,physical.map (view i)=FiniteLaw.pi (fun e=>law i (Sum.inl e)):=by
    intro i
    exact mixed_pointwise_law physical (marked i) (f i) (g i) (μ i) (ν i) (hf i) (hg i)
  exact class_shared_raw_product physical colour view law hv
end Oberwolfach
