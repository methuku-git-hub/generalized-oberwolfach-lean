module

public import Oberwolfach.OrdinaryWheelLikelySeparateCostsCertificate

@[expose] public section
/-! Any sufficiently likely same-sample protected finish is a certificate
for the level chain; its failure bound need not have a prescribed shape. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_wheel_certificate_from_probability
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ)
    (cost deepCost localCost localDeep failure:ℝ) (μ:FiniteLaw (Sym2 (V⊕U)→Bool))
    (E:(Sym2 (V⊕U)→Bool)→Prop)
    (hn:16≤Fintype.card V) (hfailure:failure≤1/4)
    (hprob:1-failure≤μ.probability E)
    (hevent:∀σ,E σ→OrdinaryProtectedHostCoverDownResult Q F H X T Z W r localCost localDeep)
    (hcost:localCost≤cost) (hdeep:localDeep≤deepCost):
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W r cost deepCost:=by
  have hnV:0<(Fintype.card V:ℝ):=by exact_mod_cast (show 0<Fintype.card V by omega)
  have hnW:0<(Fintype.card (V⊕U):ℝ):=by
    have hh:Fintype.card V≤Fintype.card (V⊕U):=
      Fintype.card_le_of_injective (Function.Embedding.inl:V↪V⊕U) Sum.inl_injective
    exact hnV.trans_le (by exact_mod_cast hh)
  have hnonneg1:0≤(1/(Fintype.card V:ℝ)):=by positivity
  have hnonneg2:0≤(1/(Fintype.card (V⊕U):ℝ)):=by positivity
  have hnonneg3:0≤(2/(Fintype.card (V⊕U):ℝ)):=by positivity
  refine ⟨μ,E,failure,localCost,localDeep,hn,hfailure,?_,hevent,hcost,hdeep⟩
  linarith only [hprob,hnonneg1,hnonneg2,hnonneg3]
end Oberwolfach
