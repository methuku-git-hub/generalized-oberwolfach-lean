module

public import Oberwolfach.FactorOrientedCycleFamily

@[expose] public section
/-! Restrict one global injective hub-component assignment to one hub;
component identities, lengths and the original candidate indices are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def assignedComponentAtHub
    {U X A:Type} [Fintype X] [DecidableEq X] (F:U→SimpleGraph X)
    (hub:A→U) (component:∀a,(F (hub a)).ConnectedComponent) (w:U)
    (a:{a // hub a=w}):(F w).ConnectedComponent:=
  a.property ▸ component a.val

theorem assigned_components_at_hub_injective
    {U X A:Type} [Fintype X] [DecidableEq X] (F:U→SimpleGraph X)
    (hub:A→U) (component:∀a,(F (hub a)).ConnectedComponent)
    (hinj:Function.Injective (fun a=>(⟨hub a,component a⟩:Σw,(F w).ConnectedComponent))) (w:U):
    Function.Injective (assignedComponentAtHub F hub component w):=by
  intro a b he
  have ha:(⟨hub a.val,component a.val⟩:Σw,(F w).ConnectedComponent)=
      ⟨w,assignedComponentAtHub F hub component w a⟩:=by
    rcases a with ⟨a,ha⟩
    dsimp [assignedComponentAtHub]
    cases ha
    rfl
  have hb:(⟨hub b.val,component b.val⟩:Σw,(F w).ConnectedComponent)=
      ⟨w,assignedComponentAtHub F hub component w b⟩:=by
    rcases b with ⟨b,hb⟩
    dsimp [assignedComponentAtHub]
    cases hb
    rfl
  apply Subtype.ext
  apply hinj
  change (⟨hub a.val,component a.val⟩:Σw,(F w).ConnectedComponent)=⟨hub b.val,component b.val⟩
  rw [ha,hb,he]

def assignedComponentsAtHub
    {U X A:Type} [Fintype X] [DecidableEq X] (F:U→SimpleGraph X)
    (hub:A→U) (component:∀a,(F (hub a)).ConnectedComponent)
    (hinj:Function.Injective (fun a=>(⟨hub a,component a⟩:Σw,(F w).ConnectedComponent))) (w:U):
    {a // hub a=w}↪(F w).ConnectedComponent:=
  ⟨assignedComponentAtHub F hub component w,assigned_components_at_hub_injective F hub component hinj w⟩

theorem assigned_component_at_hub_card
    {U X A:Type} [Fintype X] [DecidableEq X] (F:U→SimpleGraph X)
    (hub:A→U) (component:∀a,(F (hub a)).ConnectedComponent) (w:U) (a:{a // hub a=w}):
    Fintype.card (assignedComponentAtHub F hub component w a)=Fintype.card (component a.val):=by
  rcases a with ⟨a,ha⟩
  dsimp [assignedComponentAtHub]
  cases ha
  rfl
end Oberwolfach
