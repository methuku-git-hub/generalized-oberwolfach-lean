"""Extract a source-anchored inventory. References are NOT a certified dependency graph."""
from pathlib import Path
import re,json,hashlib,bisect
root=Path(__file__).resolve().parents[1]
s=(root/'source/manuscript.tex').read_text()
newlines=[m.start() for m in re.finditer('\n',s)]
def line(pos):return bisect.bisect_left(newlines,pos)+1
nodes=[]
pat=re.compile(r'\\begin\{(theorem|lemma|proposition|corollary|definition|setting|conjecture|localclaim|problem)\}(?:\[([^\n]*?)\])?')
for j,m in enumerate(pat.finditer(s)):
 end=s.index('\\end{'+m[1]+'}',m.end())+len('\\end{'+m[1]+'}')
 block=s[m.start():end]
 labels=re.findall(r'\\label\{([^}]+)\}',block)
 label=labels[0] if labels else f'unlabelled:{line(m.start())}'
 section=list(re.finditer(r'^\\section\{([^\n]+)',s[:m.start()],re.M))
 nodes.append({'label':label,'kind':m[1],'title':m[2] or label,'start_line':line(m.start()),'end_line':line(end),'statement_tex':block,'statement_refs':re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',block),'formalization':'not_formalized','proof_ranges':[]})
# Track every proof environment, including nested claims, without guessing that
# every nearby paragraph is a proof dependency.
stack=[];proofs=[]
for m in re.finditer(r'\\(begin|end)\{proof\}(?:\[([^\n]*?)\])?',s):
 if m[1]=='begin':stack.append((m.start(),m.end(),m[2],len(stack)))
 else:
  start,body,heading,depth=stack.pop();text=s[start:m.end()]
  refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',text)
  explicit=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',heading or '')
  owner=next((n['label'] for n in nodes if n['label'] in explicit),None)
  if owner is None:
   before=[n for n in nodes if n['end_line']<=line(start)]
   if before and line(start)-before[-1]['end_line']<=3:owner=before[-1]['label']
  proofs.append({'start_line':line(start),'end_line':line(m.end()),'depth':depth,'heading':heading,'owner':owner,'references':sorted(set(refs)),'sha256':hashlib.sha256(text.encode()).hexdigest(),'status':'not_line_by_line_formalized'})
for n in nodes:
 n['proof_ranges']=[[p['start_line'],p['end_line']] for p in proofs if p['owner']==n['label']]
 n['proof_reference_candidates']=sorted({r for p in proofs if p['owner']==n['label'] for r in p['references'] if r!=n['label']})
 n['scope']='proof_local' if n['kind']=='localclaim' else 'background_problem' if n['kind']=='problem' else 'public'
 if n['label'] in {'lem:pr:rt1-stability','lem:pr:wi-stability'}:
  n['formalization']='generic_lemma_checked; graph-specific callers remain open'
 if n['label']=='thm:prelim:konig':
  n['formalization']='checked_in_finite_multiplicity_representation'
 if n['label']=='lem:family:partition':
  n['formalization']='full_partition_checked_in_physical_colour_graph_representation; preparation_and_fixed_set_callers_open'
 if n['label']=='thm:prelim:max-flow-min-cut':
  n['formalization']='real_network_theorem_checked; general_integer_clause_not_formalized'
 if n['label'] in {'lem:prelim:prescribed-degrees','lem:prelim:normalized-demands'}:
  n['formalization']='real_and_integer_bipartite_forms_checked; callers_need_explicit_bridges'
 if n['label']=='lem:simp:orientation-routing':
  n['formalization']='checked_in_directed_incidence_representation'
 if n['label']=='thm:prelim:bounded-differences':
  n['formalization']='finite_categorical_version_checked_including_zero_case'
 if n['label']=='clm:partition:balanced-orientation':
  n['formalization']='checked_in_fair_unordered_pair_model_including_all_later_forbidden_graphs_and_asymptotic_margins'
public=[n for n in nodes if n['scope']=='public']
def display_status(n):
 if n['formalization'].startswith('generic_lemma_checked'):return 'Generic lemma checked'
 if n['label']=='thm:prelim:konig':return 'Multigraph theorem checked'
 if n['label']=='lem:family:partition':return 'Partition theorem checked'
 if n['label']=='thm:prelim:max-flow-min-cut':return 'Real case checked'
 if n['label'] in {'lem:prelim:prescribed-degrees','lem:prelim:normalized-demands'}:return 'Bipartite forms checked'
 if n['label']=='lem:simp:orientation-routing':return 'Incidence form checked'
 if n['label']=='thm:prelim:bounded-differences':return 'Finite case checked'
 return 'Open'
(root/'blueprint/src/inventory.tex').write_text(
 r'''\appendix
\chapter{Whole-manuscript statement inventory}
This table indexes the 137 public statement and definition environments in the
snapshot. The JSON inventory additionally records 33 proof-local claims,
one background problem and all 133 proof environments. Inclusion is not a claim
that a statement has been audited or formalised. Source line numbers refer to
the archived snapshot.
\small
\begin{longtable}{p{.69\textwidth}r >{\raggedright\arraybackslash}p{.18\textwidth}}
\toprule Source label & Line & Lean status \\ \midrule\endhead
''' + ''.join(r'\nolinkurl{'+n['label']+'} & '+str(n['start_line'])+' & '+
 display_status(n)+
 r' \\'+'\n' for n in public)+r'\bottomrule\end{longtable}'+'\n')
(root/'blueprint/manuscript_inventory.json').write_text(json.dumps({'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'warning':'An extracted reference is only a dependency candidate. Absence of a reference does not establish independence. No whole-manuscript Lean verification is claimed.','statements':nodes,'proofs':sorted(proofs,key=lambda p:p['start_line'])},indent=2)+'\n')
print('statements',len(nodes),'proofs',len(proofs),'top_level_proofs',sum(p['depth']==0 for p in proofs))
print('\n'.join(f"{n['label']} | {n['title']} | {n['start_line']} | {','.join(n['proof_reference_candidates'])}" for n in nodes if n['kind'] in ['theorem','proposition'] or 'completion:' in n['label']))
