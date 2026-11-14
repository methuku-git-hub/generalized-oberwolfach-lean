module

public import Oberwolfach.DirectedIncidenceSums

@[expose] public section

/-! Incidence hub assignments remain injective after a noninjective row
map, provided that the image of every original arc has distinct ends.
Global injectivity of the row map is not assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
namespace Oberwolfach
variable {E V V' U:Type} {tail head:E→V}

 theorem directedIncidence_endpoint {v:V} (i:DirectedIncidence tail head v):
    v=head (directedIncidenceEdge i)∨v=tail (directedIncidenceEdge i):=by
  cases i with
  | inl i=>exact Or.inl i.property.symm
  | inr i=>exact Or.inr i.property.symm

 theorem directedIncidenceEdge_injective (hloop:∀ e,head e≠tail e) (v:V):
    Function.Injective (directedIncidenceEdge (tail:=tail) (head:=head) (v:=v)):=by
  intro i j hij
  cases i with
  | inl i=>
    cases j with
    | inl j=>exact congrArg Sum.inl (Subtype.ext hij)
    | inr j=>
      have he:i.val=j.val:=hij
      exact False.elim (hloop i.val (i.property.trans (he ▸ j.property.symm)))
  | inr i=>
    cases j with
    | inl j=>
      have he:i.val=j.val:=hij
      exact False.elim (hloop i.val ((he ▸ j.property).trans i.property.symm))
    | inr j=>exact congrArg Sum.inr (Subtype.ext hij)

 theorem directed_incidence_assigned_hubs_injective
    (f:V→V') (h:E→U) (hh:Function.Injective h)
    (hloop:∀ e,f (head e)≠f (tail e))
    (σ:∀ v,Equiv.Perm (DirectedIncidence tail head v)):
    Function.Injective (fun i:Σ v,DirectedIncidence tail head v=>
      (f i.1,h (directedIncidenceEdge (σ i.1 i.2)))):=by
  rintro ⟨v,i⟩ ⟨w,j⟩ he
  have hfv:f v=f w:=congrArg Prod.fst he
  have hedge:directedIncidenceEdge (σ v i)=directedIncidenceEdge (σ w j):=hh (congrArg Prod.snd he)
  have hvw:v=w:=by
    have hv:=directedIncidence_endpoint (σ v i)
    have hw:=directedIncidence_endpoint (σ w j)
    rw [←hedge] at hw
    rcases hv with hv|hv <;> rcases hw with hw|hw
    · exact hv.trans hw.symm
    · exact False.elim (hloop _ ((congrArg f hv).symm.trans (hfv.trans (congrArg f hw))))
    · exact False.elim (hloop _ ((congrArg f hw).symm.trans (hfv.symm.trans (congrArg f hv))))
    · exact hv.trans hw.symm
  subst w
  have hloop':∀ e,head e≠tail e:=fun e he=>hloop e (congrArg f he)
  have hij:i=j:=(σ v).injective (directedIncidenceEdge_injective hloop' v hedge)
  subst j
  rfl

 theorem directed_incidence_assignment_avoids_own_edge
    (hloop:∀ e,head e≠tail e) (v:V) (σ:Equiv.Perm (DirectedIncidence tail head v))
    (hσ:∀ i,σ i≠i):∀ i,directedIncidenceEdge (σ i)≠directedIncidenceEdge i:=by
  intro i he
  exact hσ i (directedIncidenceEdge_injective hloop v he)

end Oberwolfach
