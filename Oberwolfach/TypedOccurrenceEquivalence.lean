module

public import Oberwolfach.IndexedMarkedExpansionMaps

@[expose] public section

/-! Equal numbers of occurrences of each type give an actual type-preserving
bijection. These bijections identify the central expansions without losing
edge multiplicity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A A' S S' V U:Type} [Fintype A] [Fintype A']

def typedOccurrenceEquiv (j:A→Bool) (j':A'→Bool)
    (h:∀ t,Fintype.card {a:A // j a=t}=Fintype.card {a:A' // j' a=t}):A≃A':=
  (Equiv.sigmaFiberEquiv j).symm.trans
    ((Equiv.sigmaCongrRight (fun t=>Fintype.equivOfCardEq (h t))).trans (Equiv.sigmaFiberEquiv j'))

theorem typedOccurrenceEquiv_type (j:A→Bool) (j':A'→Bool)
    (h:∀ t,Fintype.card {a:A // j a=t}=Fintype.card {a:A' // j' a=t}) (a:A):
    j' (typedOccurrenceEquiv j j' h a)=j a:=by
  exact (Fintype.equivOfCardEq (h (j a)) (⟨a,rfl⟩:{a':A // j a'=j a})).property

def IndexedMarkedGraph.pullbackOccurrences (G:IndexedMarkedGraph V U A S) (τ:A'≃A) (σ:S'≃S):
    IndexedMarkedGraph V U A' S':=
  ⟨G.src∘τ,G.dst∘τ,G.row∘σ,G.hub∘σ,G.jr∘τ,G.js∘σ⟩

variable [Fintype S] [Fintype S'] [DecidableEq V] [DecidableEq U]

theorem IndexedMarkedGraph.pullbackOccurrences_balanced (G:IndexedMarkedGraph V U A S) (m:ℕ)
    (hG:G.IsBalanced m) (τ:A'≃A) (σ:S'≃S):
    (G.pullbackOccurrences τ σ).IsBalanced m:=by
  have hf:∀ (X Y Z:Type) [Fintype X] [Fintype Y] (e:X≃Y) (f:Y→Z) (z:Z)
      [DecidablePred (fun x=>f (e x)=z)] [DecidablePred (fun y=>f y=z)],
      Fintype.card {x:X // f (e x)=z}=Fintype.card {y:Y // f y=z}:=by
    intro X Y Z _ _ e f z _ _
    exact Fintype.card_congr (Equiv.subtypeEquiv e (fun _=>Iff.rfl))
  have ht:∀ (X Y:Type) [Fintype X] [Fintype Y] (e:X≃Y) (P:Y→Prop) [DecidablePred P]
      [DecidablePred (fun x=>P (e x))],Fintype.card {x:X // P (e x)}=Fintype.card {y:Y // P y}:=by
    intro X Y _ _ e P _ _
    exact Fintype.card_congr (Equiv.subtypeEquiv e (fun _=>Iff.rfl))
  constructor
  · intro v
    change Fintype.card {a:A' // G.dst (τ a)=v}=Fintype.card {a:A' // G.src (τ a)=v}
    rw [hf A' A V τ G.dst v,hf A' A V τ G.src v];exact hG.directed v
  · intro v
    change Fintype.card {a:A' // G.dst (τ a)=v}=Fintype.card {s:S' // G.row (σ s)=v}
    rw [hf A' A V τ G.dst v,hf S' S V σ G.row v];exact hG.row v
  · intro v
    change Fintype.card {a:A' // G.dst (τ a)=v∧G.jr (τ a)=true}=
      Fintype.card {s:S' // G.row (σ s)=v∧G.js (σ s)=true}
    rw [ht A' A τ (fun a=>G.dst a=v∧G.jr a=true),ht S' S σ (fun s=>G.row s=v∧G.js s=true)]
    exact hG.marked v
  · intro u
    change Fintype.card {s:S' // G.hub (σ s)=u∧G.js (σ s)=false}=
      m*Fintype.card {s:S' // G.hub (σ s)=u∧G.js (σ s)=true}
    rw [ht S' S σ (fun s=>G.hub s=u∧G.js s=false),ht S' S σ (fun s=>G.hub s=u∧G.js s=true)]
    exact hG.hub u

end Oberwolfach
