module

public import Oberwolfach.MarkedPaddingPacking
public import Oberwolfach.MarkedSpokeLoadGrouping
public import Mathlib.Logic.Function.Basic

@[expose] public section

/-! Extend the old row and hub maps to the privately labelled padding
wheels. Old vertices may be identified by the map; only the new labels
have to be distinct. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype I] [DecidableEq V] [DecidableEq U]

theorem padding_row_map_extension (m:ℕ) (φ:V→V) (p p':I→(Fin m↪V)) (Z:Finset V)
    (hdis:∀ i j,i≠j→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p j)))
    (hav:∀ i k,p i k∉Z):
    ∃ φ':V→V,(∀ v∈Z,φ' v=φ v)∧∀ i k,φ' (p i k)=p' i k:=by
  let f:I×Fin m→V:=fun z=>p z.1 z.2
  let g:I×Fin m→V:=fun z=>p' z.1 z.2
  have hf:Function.Injective f:=disjoint_paths_joint_injective m p hdis
  refine ⟨Function.extend f g φ,?_,fun i k=>hf.extend_apply g φ (i,k)⟩
  intro v hv
  apply Function.extend_apply'
  rintro ⟨⟨i,k⟩,he⟩
  have he':p i k=v:=he
  exact hav i k (he'.symm ▸ hv)

theorem padding_hub_map_extension (ψ:U→U) (h:I↪U) (h':I→U) (B:Finset U)
    (hav:∀ i,h i∉B):
    ∃ ψ':U→U,(∀ u∈B,ψ' u=ψ u)∧∀ i,ψ' (h i)=h' i:=by
  refine ⟨Function.extend h h' ψ,?_,fun i=>h.injective.extend_apply h' ψ i⟩
  intro u hu
  apply Function.extend_apply'
  rintro ⟨i,he⟩
  exact hav i (he ▸ hu)

theorem padding_cycle_map_extension (m:ℕ) (φ:V→V) (v:I→V) (p p':I→(Fin m↪V))
    (Z:Finset V) (hv:∀ i,v i∈Z)
    (hdis:∀ i j,i≠j→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p j)))
    (hav:∀ i k,p i k∉Z):
    ∃ φ':V→V,(∀ z∈Z,φ' z=φ z)∧∀ i k,
      φ' (Fin.cons (α:=fun _=>V) (v i) (p i) k)=Fin.cons (α:=fun _=>V) (φ (v i)) (p' i) k:=by
  obtain ⟨φ',hφ,hp⟩:=padding_row_map_extension m φ p p' Z hdis hav
  refine ⟨φ',hφ,?_⟩
  intro i k
  refine Fin.cases ?_ (fun k=>?_) k
  · simpa only [Fin.cons_zero] using hφ (v i) (hv i)
  · simpa only [Fin.cons_succ] using hp i k

end Oberwolfach
