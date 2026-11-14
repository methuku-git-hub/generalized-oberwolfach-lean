module

public import Oberwolfach.ResidualOccurrenceCardinality
public import Oberwolfach.SpokePartitionExactCounts
public import Oberwolfach.RetainedMarkedRootUniformity

@[expose] public section
/-! Balanced residual arc counts and the actual retained spoke geometry give
all exact typed divisibility identities for the same residual. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
attribute [local instance] partitionedDivisibleDecEq partitionedDivisibleArc partitionedDivisibleArcFinite
  partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_residual_balanced_divisibility
    (P:V×V→Prop) (Q:Finset (V×V)) (hP:∀a,P a↔a∈Q)
    (M:Finset {e:V×V // P e}) (π:Equiv.Perm V) (d m:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<d→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (j:Color) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g) t)
    (R:U→Finset V)
    (hsubset:∀u,markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ g t J u=>d) Subtype.val⊆R u)
    (hsize:∀u,(R u).card=(m+1)*(markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ g t J u=>d) Subtype.val).card)
    (hdegree:∀v,(Q.filter (fun a=>a.1=v)).card=(Finset.univ.filter (fun u=>v∈R u)).card ∧
      (Q.filter (fun a=>a.2=v)).card=(Finset.univ.filter (fun u=>v∈R u)).card)
    (hmarked:∀v,directedInCount P M v=d*t):
    let Y:=fun u=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ g t J u=>d) Subtype.val
    let H₀:=fun v u=>v∈R u\Y u
    MarkedRemainderDivisible
      (fun e:residualOrdinaryArc P M=>e.val.val.1) (fun e=>e.val.val.2)
      (fun e:residualMarkedArc P M=>e.val.val.1) (fun e=>π.symm e.val.val.2)
      (retainedRawMarkedSpokes π d σ g t J g j true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨retainedRawMarkedSpokes π d σ g t J g j true z.1 z.2)) m:=by
  intro Y H₀
  have hY:∀v u,v∈Y u↔retainedRawMarkedSpokes π d σ g t J g j true v u:=by
    intro v u
    exact retained_marked_root_membership π d hd σ g t J u v
  have hc:=spoke_partition_exact_counts R Y m hsubset hsize
  have hH:∀v u,¬(H₀ v u∧retainedRawMarkedSpokes π d σ g t J g j true v u):=by
    intro v u h
    exact (Finset.mem_sdiff.mp h.1).2 ((hY v u).mpr h.2)
  have hphysical:∀v,occurrenceDegree (fun e:{a:V×V // P a}=>e.val.1) v=
      occurrenceDegree (fun e:{a:V×V // P a}=>e.val.2) v:=by
    intro v
    have ht:=residual_occurrence_cardinality P Q hP Prod.fst v
    have hh:=residual_occurrence_cardinality P Q hP Prod.snd v
    have ht':occurrenceDegree (fun e:{a:V×V // P a}=>e.val.1) v=((Q.filter (fun a=>a.1=v)).card:ℝ):=by
      convert ht using 1 <;> congr! <;> exact Subsingleton.elim _ _
    have hh':occurrenceDegree (fun e:{a:V×V // P a}=>e.val.2) v=((Q.filter (fun a=>a.2=v)).card:ℝ):=by
      convert hh using 1 <;> congr! <;> exact Subsingleton.elim _ _
    rw [ht',hh',(hdegree v).1,(hdegree v).2]
  have hrow:∀v,occurrenceDegree (fun e:{a:V×V // P a}=>e.val.1) v=
      (∑u,if H₀ v u then (1:ℝ) else 0)+(∑u,if retainedRawMarkedSpokes π d σ g t J g j true v u then (1:ℝ) else 0):=by
    intro v
    have ht:=residual_occurrence_cardinality P Q hP Prod.fst v
    have ht':occurrenceDegree (fun e:{a:V×V // P a}=>e.val.1) v=((Q.filter (fun a=>a.1=v)).card:ℝ):=by
      convert ht using 1 <;> congr! <;> exact Subsingleton.elim _ _
    rw [ht',(hdegree v).1]
    have hsum:(∑u,if v∈R u then (1:ℝ) else 0)=((Finset.univ.filter (fun u=>v∈R u)).card:ℝ):=by
      convert Finset.sum_boole (R:=ℝ) (fun u=>v∈R u) Finset.univ using 1 <;> congr!
    rw [←hsum,←hc.1 v]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp_all
  have hhub:∀u,(∑v,if H₀ v u then (1:ℝ) else 0)=
      (m:ℝ)*(∑v,if retainedRawMarkedSpokes π d σ g t J g j true v u then (1:ℝ) else 0):=by
    intro u
    have h:=hc.2 u
    convert h using 1
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp_all
  have hrow' : ∀v,occurrenceDegree (fun e:{a:V×V // P a}=>e.val.1) v=
      (∑u,@ite ℝ (H₀ v u) (Classical.propDecidable _) 1 0)+(∑u,if retainedRawMarkedSpokes π d σ g t J g j true v u then (1:ℝ) else 0):=by
    convert hrow using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
  have hhub' : ∀u,(∑v,@ite ℝ (H₀ v u) (Classical.propDecidable _) 1 0)=
      (m:ℝ)*(∑v,if retainedRawMarkedSpokes π d σ g t J g j true v u then (1:ℝ) else 0):=by
    convert hhub using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
  have hfinal:=long_partitioned_residual_divisible P M π d m hd hnoshort σ g j t J H₀ hH hmarked hphysical hrow' hhub'
  convert hfinal using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
end Oberwolfach
