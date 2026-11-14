module

public import Oberwolfach.MarkedCanonicalCycleCompletion

@[expose] public section

/-! Complete the wheel after its first ordinary arc. The fixed ordinary
root need not be separated from the other old roots: only the new path
vertices are required to avoid their permutation neighbourhoods. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_prefix_cycle_completion
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (P:Finset U) (hP:P.card≤2) (W Z:Finset V) (v x z y:V)
    (hv:v∈Z) (hx:x∈Z) (hvx:¬PermutationClose π b v x) (hzy:¬PermutationClose π b z y)
    (hopen:markedArcPresent tail head ktail khead false v x)
    (hfirst:markedArcPresent tail head ktail khead false x z)
    (hclose:markedArcPresent tail head ktail khead true y v)
    (hvP:markedSpokesTo H₀ HK true P v) (hxP:markedSpokesTo H₀ HK false P x)
    (hzP:markedSpokesTo H₀ HK false P z) (hyP:markedSpokesTo H₀ HK false P y)
    (hzW:z∉W) (hyW:y∉W) (hzZ:z∉Z) (hyZ:y∉Z)
    (hzsep:∀ w∈Z,¬PermutationClose π b z w) (hysep:∀ w∈Z,¬PermutationClose π b y w)
    (hbudget:(W.card:ℝ)+(Z.card+l+4)*(2*b+1)<c):
    ∃ p:Fin (l+3)↪V,∃ C:MarkedCycleTuple tail head ktail khead (l+4) π b,
      (∀ i,C.val i=Fin.cons (α:=fun _=>V) v (Fin.cons x p) i)∧p 0=z∧p (Fin.last (l+2))=y∧
      (∀ i,p i∉W∧p i∉Z∧∀ w∈Z,¬PermutationClose π b (p i) w)∧
      ∀ u∈P,MarkedHubCompatible H₀ HK C.val u:=by
  obtain ⟨p,hp0,hpn,hpa,hpd,hps⟩:=marked_host_ordinary_path Q P hP W Z l z y hzy hzP hyP hzW hyW hzZ hyZ hzsep hysep hbudget
  have hxps:PermutationSeparated π b (Fin.cons x p):=
    permutationSeparated_cons π b x p hps
      (fun i hh=>(hpa i).2.2.2 x hx ((permutationClose_symm π b _ _).mp hh))
  have hvps:∀ i:Fin (l+4),¬PermutationClose π b v (Fin.cons (α:=fun _=>V) x p i):=by
    intro i;refine Fin.cases ?_ (fun j=>?_) i
    · exact hvx
    · exact fun hh=>(hpa j).2.2.2 v hv ((permutationClose_symm π b _ _).mp hh)
  have hc:=permutationSeparated_cons π b v (Fin.cons x p) hxps hvps
  have hpath:∀ i:Fin (l+3),∃ e,tail e=Fin.cons (α:=fun _=>V) x p i.castSucc∧head e=Fin.cons (α:=fun _=>V) x p i.succ:=by
    intro i;refine Fin.cases ?_ (fun j=>?_) i
    · simpa only [Fin.castSucc_zero,Fin.cons_zero,Fin.cons_succ,hp0,markedArcPresent,Bool.false_eq_true,ite_false] using hfirst
    · have he:j.succ.castSucc=j.castSucc.succ:=rfl
      simpa only [he,Fin.cons_succ,markedArcPresent,Bool.false_eq_true,ite_false] using hpd j
  have hcyc:=root_first_marked_cycle_from_path tail head ktail khead (l+3) (by omega)
    π b true v (Fin.cons x p) hc (by exact hopen)
    (by simpa only [show Fin.last (l+3)=(Fin.last (l+2)).succ from rfl,Fin.cons_succ,hpn,markedArcPresent,ite_true] using hclose)
    (by intro i;simpa only [Bool.true_eq_false,false_and,ite_false] using hpath i)
  have hcanon:IsMarkedCycleTuple tail head ktail khead (l+4) π b (Fin.cons (α:=fun _=>V) v (Fin.cons x p)):=by
    have hh:=(rootedCycleOrder_marked_iff true v (Fin.cons x p)).mpr hcyc
    exact hh
  let C:MarkedCycleTuple tail head ktail khead (l+4) π b:=⟨_,hcanon⟩
  refine ⟨p,C,fun _=>rfl,hp0,hpn,fun i=>(hpa i).2,?_⟩
  intro u hu
  constructor
  · exact hvP u hu
  · intro i;refine Fin.cases ?_ (fun j=>?_) i
    · exact hxP u hu
    · exact (hpa j).1 u hu

end Oberwolfach
