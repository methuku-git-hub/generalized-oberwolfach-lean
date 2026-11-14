"""Prepare the website input and local source links without publishing anything.

These links show the saved Lean sources, not generated API documentation.
The verification manifest, rather than this source index, records checked claims.
"""
from pathlib import Path
import re,json,html
root=Path(__file__).resolve().parents[1]
src=root/'blueprint/src'; web=root/'blueprint/web'
body=(src/'content.tex').read_text().replace('../src/inventory','inventory-web')
(src/'content-web.tex').write_text('% Generated from content.tex by build_web_support.py\n'+body)
inv=(src/'inventory.tex').read_text()
inv=inv.replace(r'\begin{longtable}{p{.69\textwidth}r >{\raggedright\arraybackslash}p{.18\textwidth}}',r'\begin{tabular}{lll}').replace(r'\end{longtable}',r'\end{tabular}').replace(r'\endhead','')
(src/'inventory-web.tex').write_text('% Generated for the HTML renderer.\n'+inv)
source=web/'lean/source';find=web/'lean/find';source.mkdir(parents=True,exist_ok=True);find.mkdir(parents=True,exist_ok=True)
index={}
for path in sorted((root/'Oberwolfach').glob('*.lean')):
 text=path.read_text();scopes=[];depth=0
 for n,line in enumerate(text.splitlines(),1):
  # Preserve scope information outside nested Lean comments.
  clean='';i=0
  while i<len(line):
   if line[i:i+2]=='/-':depth+=1;i+=2
   elif depth and line[i:i+2]=='-/':depth-=1;i+=2
   elif not depth and line[i:i+2]=='--':break
   else:
    if not depth:clean+=line[i]
    i+=1
  clean=clean.lstrip()
  m=re.match(r'^namespace\s+([\w.]+)\s*$',clean)
  if m:scopes.append(('namespace',m[1]));continue
  m=re.match(r'^(?:noncomputable\s+)?section(?:\s+([\w.]+))?\s*$',clean)
  if m:scopes.append(('section',m[1] or ''));continue
  if re.match(r'^end(?:\s+[\w.]+)?\s*$',clean):
   if scopes:scopes.pop()
   continue
  m=re.match(r'^(?:(?:noncomputable|protected)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+([\w.\']+)',clean)
  if m:
   name='.'.join([v for k,v in scopes if k=='namespace']+[m[1]])
   index[name]=f'../source/{path.stem}.html#L{n}'
 rows='\n'.join(f'<span id="L{n}"><a href="#L{n}" class="ln">{n:4}</a> {html.escape(line)}</span>' for n,line in enumerate(text.splitlines(),1))
 page=f'''<!doctype html><html lang="en"><meta charset="utf-8"><title>{html.escape(path.name)} — Lean source</title>
<style>body{{margin:2rem;font-family:system-ui}}pre{{line-height:1.55;white-space:pre-wrap}}.ln{{color:#777;text-decoration:none}}span:target{{background:#fff1a6}}.status{{padding:1rem;background:#fff3db}}</style>
<p><a href="../../index.html">Blueprint</a> · <a href="../../dep_graph_document.html">Dependency graph</a></p>
<h1>{html.escape(path.name)}</h1><p class="status">Formalisation in progress. Theorem 1.1 is not yet proved in Lean. This page displays saved source; it is not a certificate of the main theorem.</p><pre>{rows}</pre></html>'''
 (source/(path.stem+'.html')).write_text(page)
needed={n.strip() for value in re.findall(r'\\lean\{([^}]+)\}',body) for n in value.split(',')}
missing=sorted(needed-index.keys())
if missing:raise SystemExit('Missing local source links: '+repr(missing))
(find/'index.html').write_text('''<!doctype html><html lang="en"><meta charset="utf-8"><title>Find Lean declaration</title><p id="status">Finding the source declaration…</p><script>
const index='''+json.dumps(index,ensure_ascii=False).replace('</','<\\/')+''';
function find(){let name=decodeURIComponent(location.hash.startsWith('#doc/')?location.hash.slice(5):location.hash.slice(1));if(index[name])location.replace(index[name]);else document.getElementById('status').textContent='No saved source location for '+name;}
addEventListener('hashchange',find);find();</script></html>''')
print(f'Prepared {len(index)} source declarations; all {len(needed)} blueprint links resolve locally.')
