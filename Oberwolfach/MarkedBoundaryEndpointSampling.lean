module

public import Oberwolfach.FreshBipartitePhysicalEvent
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section

/-! The boundary coin attached to an endpoint label is its actual physical
edge. In particular an incoming marked arc has physical head pi(root),
whereas an outgoing marked arc has physical head pi(label). All five
endpoint graphs use the same hub-spoke coin at a fixed outside root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def markedBoundaryEndpointResource (π : Equiv.Perm V) (mark incoming : Bool) (x : V) :
    V⊕U→Sym2 V⊕(V×U)
  | Sum.inl z=>Sum.inl (if incoming then s(z,if mark then π x else x) else s(x,if mark then π z else z))
  | Sum.inr u=>Sum.inr (x,u)

theorem marked_boundary_endpoint_resource_injective (π : Equiv.Perm V) (mark incoming : Bool) (x : V) :
    Function.Injective (markedBoundaryEndpointResource (U:=U) π mark incoming x) := by
  intro a b he
  cases a with
  | inl a=>cases b with
    | inl b=>
      apply congrArg Sum.inl
      have hh:=Sum.inl.inj he
      cases incoming <;> cases mark
      all_goals simp only [markedBoundaryEndpointResource,Bool.false_eq_true,ite_false,ite_true] at hh
      all_goals rcases Sym2.eq_iff.mp hh with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
      all_goals first
        | exact h₂
        | exact h₂.trans h₁
        | exact h₂.symm.trans h₁
        | exact h₂.trans h₁.symm
        | exact h₂.symm.trans h₁.symm
        | exact π.injective (h₂.trans h₁)
        | exact π.injective (h₂.symm.trans h₁)
        | exact π.injective (h₂.trans h₁.symm)
        | exact π.injective (h₂.symm.trans h₁.symm)
        | exact h₁
        | exact h₁.trans h₂
        | exact h₁.trans h₂.symm
        | exact h₁.symm.trans h₂
        | exact h₁.symm.trans h₂.symm
        | exact π.injective h₂
        | exact π.injective (h₁.trans h₂)
        | exact π.injective (h₁.symm.trans h₂.symm)
    | inr b=>exact (Sum.inl_ne_inr he).elim
  | inr a=>cases b with
    | inl b=>exact (Sum.inr_ne_inl he).elim
    | inr b=>exact congrArg Sum.inr (congrArg Prod.snd (Sum.inr.inj he))

def markedBoundaryEndpointCoin (π : Equiv.Perm V) (mark incoming : Bool) (x : V) :
    V⊕U↪Sym2 (V⊕U) where
  toFun z:=ordinaryPhysicalResource (markedBoundaryEndpointResource π mark incoming x z)
  inj':=ordinaryPhysicalResource_injective.comp (marked_boundary_endpoint_resource_injective π mark incoming x)

theorem marked_boundary_endpoint_spoke_coin (π : Equiv.Perm V) (mark incoming : Bool) (x : V) (u : U) :
    markedBoundaryEndpointCoin π mark incoming x (Sum.inr u)=s(Sum.inl x,Sum.inr u) := rfl

theorem marked_boundary_endpoint_rim_coin (π : Equiv.Perm V) (mark incoming : Bool) (x z : V) :
    markedBoundaryEndpointCoin (U:=U) π mark incoming x (Sum.inl z)=
      if incoming then s(Sum.inl z,Sum.inl (if mark then π x else x))
      else s(Sum.inl x,Sum.inl (if mark then π z else z)) := by
  cases incoming <;> cases mark <;> rfl

theorem marked_boundary_endpoint_coordinate_law (π : Equiv.Perm V) (mark incoming : Bool) (x : V)
    (ρ : ℝ) (hρ : 0≤ρ) (hρ1 : ρ≤1) :
    (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin ρ hρ hρ1)).map
      (fun σ z=>σ (markedBoundaryEndpointCoin π mark incoming x z))=
      FiniteLaw.pi (fun _:V⊕U=>FiniteLaw.retentionCoin ρ hρ hρ1) :=
  finiteLaw_pi_injective_projection _ _ (markedBoundaryEndpointCoin π mark incoming x).injective

end Oberwolfach
