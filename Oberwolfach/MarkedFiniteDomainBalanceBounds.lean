module

public import Oberwolfach.MarkedFiniteDomainBalance
public import Oberwolfach.MarkedFiniteBalanceBounds

@[expose] public section

/-! Incidence bounds on an actual deleted graph bound its contribution
on every fixed opposite-endpoint domain, including at external roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem markedFiniteDomainBalance_bound
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ) (X:Finset V) (Z:Finset U)
    (δ:ℝ) (hδ:0≤δ)
    (hA:∀ v,((A.filter (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v)).card:ℝ)≤δ)
    (hR:∀ v,((S.filter (fun s=>s.1=v)).card:ℝ)≤δ)
    (hC:∀ u,((S.filter (fun s=>s.2=u)).card:ℝ)≤δ)
    (z:V⊕U) (i:Fin 4):
    |markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i|≤(m+2)*δ:=by
  have hc {α:Type} (F G:Finset α) (h:F⊆G) (p:α→Prop) [DecidablePred p]:
      ((F.filter p).card:ℝ)≤(G.filter p).card:=by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter p h)
  cases z with
  | inl v=>
    dsimp only [markedFiniteDomainBalance]
    apply markedFiniteBalance_bound _ _ _ _ _ _ _ _ _ hδ
    · intro w;exact (hc _ A (Finset.filter_subset _ _) _).trans (hA w)
    · intro w;exact (hc _ S (Finset.filter_subset _ _) _).trans (hR w)
    · intro u;exact (hc _ S (Finset.filter_subset _ _) _).trans (hC u)
  | inr u=>
    dsimp only [markedFiniteDomainBalance]
    apply markedFiniteBalance_bound _ _ _ _ _ _ _ _ _ hδ
    · intro w;simpa using hδ
    · intro w;exact (hc _ S (Finset.filter_subset _ _) _).trans (hR w)
    · intro u;exact (hc _ S (Finset.filter_subset _ _) _).trans (hC u)

theorem markedFiniteDomainBalance_zero_of_avoids
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ) (X:Finset V) (Z:Finset U)
    (hA:∀ a∈A,Sum.elim tail ktail a∉X∧Sum.elim head khead a∉X)
    (hS:∀ s∈S,s.1∉X∧s.2∉Z) (z:V⊕U) (i:Fin 4):
    markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i=0:=by
  have hsX:S.filter (fun s=>s.1∈X)=∅:=Finset.filter_eq_empty_iff.mpr (fun s hs=>(hS s hs).1)
  have hsZ:S.filter (fun s=>s.2∈Z)=∅:=Finset.filter_eq_empty_iff.mpr (fun s hs=>(hS s hs).2)
  cases z with
  | inl v=>
    have ha:A.filter (fun a=>(if Sum.elim tail ktail a=v then Sum.elim head khead a else Sum.elim tail ktail a)∈X)=∅:=by
      apply Finset.filter_eq_empty_iff.mpr
      intro a ha
      split_ifs
      · exact (hA a ha).2
      · exact (hA a ha).1
    dsimp only [markedFiniteDomainBalance]
    rw [ha,hsZ]
    fin_cases i <;> simp [markedFiniteBalance]
  | inr u=>
    dsimp only [markedFiniteDomainBalance]
    rw [hsX]
    fin_cases i <;> simp [markedFiniteBalance]

end Oberwolfach
