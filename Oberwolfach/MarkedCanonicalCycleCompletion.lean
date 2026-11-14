module

public import Oberwolfach.MarkedHostGreedyChoices
public import Oberwolfach.MarkedRootedPathCycles
public import Oberwolfach.MarkedPathParent

@[expose] public section

/-! Complete a canonical marked cycle from its marked head and two ordinary
path endpoints. The root is retained; every internal vertex is chosen from
the supplied host intersections, outside the original forbidden sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_canonical_cycle_completion
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (P:Finset U) (hP:P.card≤2) (W Z:Finset V) (v x y:V)
    (hv:v∈Z) (hxy:¬PermutationClose π b x y)
    (hopen:markedArcPresent tail head ktail khead false v x)
    (hclose:markedArcPresent tail head ktail khead true y v)
    (hvP:markedSpokesTo H₀ HK true P v)
    (hx:markedSpokesTo H₀ HK false P x) (hy:markedSpokesTo H₀ HK false P y)
    (hxW:x∉W) (hyW:y∉W) (hxZ:x∉Z) (hyZ:y∉Z)
    (hxsep:∀ z∈Z,¬PermutationClose π b x z) (hysep:∀ z∈Z,¬PermutationClose π b y z)
    (hbudget:(W.card:ℝ)+(Z.card+l+5)*(2*b+1)<c):
    ∃ p:Fin (l+4)↪V,∃ C:MarkedCycleTuple tail head ktail khead (l+4) π b,
      (∀ i,C.val i=Fin.cons (α:=fun _=>V) v p i)∧p 0=x∧p (Fin.last (l+3))=y∧
      (∀ i,p i∉W∧p i∉Z∧∀ z∈Z,¬PermutationClose π b (p i) z)∧
      ∀ u∈P,MarkedHubCompatible H₀ HK C.val u:=by
  obtain ⟨p,hp0,hpn,hpa,hpd,hps⟩:=marked_host_ordinary_path Q P hP W Z (l+1) x y hxy hx hy hxW hyW hxZ hyZ hxsep hysep
    (by convert hbudget using 1 <;> push_cast <;> ring)
  have hc:PermutationSeparated π b (Fin.cons v p):=
    permutationSeparated_cons π b v p hps
      (fun i hh=>(hpa i).2.2.2 v hv ((permutationClose_symm π b _ _).mp hh))
  have hcyc:=root_first_marked_cycle_from_path tail head ktail khead (l+3) (by omega)
    π b true v p hc (by simpa only [hp0,markedArcPresent,Bool.false_eq_true,ite_false] using hopen) (by simpa only [hpn,markedArcPresent,ite_true] using hclose)
    (by intro i;simpa only [markedArcPresent,Bool.false_eq_true,Bool.true_eq_false,false_and,ite_false] using hpd i)
  have hcanon:IsMarkedCycleTuple tail head ktail khead (l+4) π b (Fin.cons (α:=fun _=>V) v p):=by
    have hh:=(rootedCycleOrder_marked_iff true v p).mpr hcyc
    exact hh
  let C:MarkedCycleTuple tail head ktail khead (l+4) π b:=⟨_,hcanon⟩
  refine ⟨p,C,fun _=>rfl,hp0,hpn,fun i=>(hpa i).2,?_⟩
  intro u hu
  constructor
  · exact hvP u hu
  · intro i;exact (hpa i).1 u hu

end Oberwolfach
