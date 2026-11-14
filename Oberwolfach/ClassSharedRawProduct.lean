module

public import Oberwolfach.ClassSharedPhysicalIndependentNoise
public import Oberwolfach.MarkedClassPhysicalProduct
public import Oberwolfach.FiniteProductSumLaw
public import Oberwolfach.FiniteProductSwap
public import Oberwolfach.FiniteLawComposition

@[expose] public section
/-! A common physical exposure, together with independent class-local
interval variables, has each class's full raw product law as a marginal. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_shared_raw_product {I Ω E C:Type} [Fintype I] [DecidableEq I]
    [Fintype Ω] [Fintype E] [DecidableEq E] [Fintype C]
    {J:I→Type} [∀ i,Fintype (J i)] [∀ i,DecidableEq (J i)]
    {S:∀ i,E⊕J i→Type} [∀ i e,Fintype (S i e)]
    (physical:FiniteLaw Ω)
    (colour:Ω→C)
    (view:∀ i,Ω→(∀ e,S i (Sum.inl e)))
    (μ:∀ i e,FiniteLaw (S i e))
    (hview:∀ i,physical.map (view i)=FiniteLaw.pi (fun e=>μ i (Sum.inl e))):
    let noise:=fun i=>FiniteLaw.pi (fun e=>μ i (Sum.inr e))
    let law:=physical.prod (FiniteLaw.pi noise);
    law.map (fun z=>colour z.1)=physical.map colour ∧
    ∀ i,law.map (fun z=>combineSumCoordinates (view i z.1) (z.2 i))=FiniteLaw.pi (μ i):=by
  intro noise law
  constructor
  · calc
      _ = (law.map Prod.fst).map colour:=by rw [finiteLaw_map_map]
      _ = _:=by rw [finiteLaw_prod_map_first]
  · intro i
    have hprod:=class_shared_physical_independent_noise physical view noise i
    have hswap:(law.map (fun z=>(z.2 i,view i z.1)))=(noise i).prod (physical.map (view i)):=by
      calc
        _ = (law.map (fun z=>(view i z.1,z.2 i))).map Prod.swap:=by rw [finiteLaw_map_map];rfl
        _ = ((physical.map (view i)).prod (noise i)).map Prod.swap:=by rw [hprod]
        _ = _:=finiteLaw_prod_swap _ _
    calc
      _ = (law.map (fun z=>(z.2 i,view i z.1))).map
          (fun z=>combineSumCoordinates z.2 z.1):=by rw [finiteLaw_map_map]
      _ = ((noise i).prod (physical.map (view i))).map
          (fun z=>combineSumCoordinates z.2 z.1):=by rw [hswap]
      _ = ((FiniteLaw.pi (fun e=>μ i (Sum.inr e))).prod (FiniteLaw.pi (fun e=>μ i (Sum.inl e)))).map
          (fun z=>combineSumCoordinates z.2 z.1):=by rw [hview i]
      _ = _:=finiteLaw_product_sum_law (μ i)
end Oberwolfach
