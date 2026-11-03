import pathlib,re,hashlib,json
base=pathlib.Path('<RESEARCH_ROOT>/aim34_analytic_lean');pkg=pathlib.Path('<RESEARCH_ROOT>/cloud_lean/packages');lean=pathlib.Path('<RESEARCH_ROOT>/cloud_lean/lean-4.19.0-linux')
roots=[base]+sorted(p for p in pkg.iterdir() if p.is_dir())+[lean/'src/lean']
seen={};missing=[]
def uncomment(txt):
 out=[];i=0;depth=0
 while i<len(txt):
  if txt.startswith('/-',i):depth+=1;i+=2
  elif depth and txt.startswith('-/',i):depth-=1;i+=2
  elif depth:
   if txt[i]=='\n':out.append('\n')
   i+=1
  elif txt.startswith('--',i):
   j=txt.find('\n',i);i=len(txt) if j<0 else j
  else:out.append(txt[i]);i+=1
 return ''.join(out)
def visit(m):
 if m in seen:return
 rel=pathlib.Path(*m.split('.')).with_suffix('.lean')
 src=next((p/rel for p in roots if (p/rel).is_file()),None)
 if src is None:missing.append(m);seen[m]={'source_unresolved':True};return
 data=src.read_bytes();imports=[]
 for line in uncomment(data.decode()).splitlines():
  line=line.strip()
  if not line or line=='prelude':continue
  if line.startswith('import '):imports+=line[7:].split()
  else:break
 row={'path':str(src),'sha256':hashlib.sha256(data).hexdigest(),'imports':imports}
 if src.parent==base and src.with_suffix('.olean').exists():row['olean_sha256']=hashlib.sha256(src.with_suffix('.olean').read_bytes()).hexdigest()
 seen[m]=row
 for x in imports:visit(x)
visit('RadicalInterpolationObstruction')
receipt={'entrypoint':'RadicalInterpolationObstruction','lean_version':'4.19.0','mathlib_commit':'c44e0c8ee63ca166450922a373c7409c5d26b00b','source_count':len(seen),'unresolved_sources':missing,'modules':dict(sorted(seen.items()))}
(base/'logs/analytic_source_closure_20261023T1021.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('Explicit source import closure:',len(seen),'unresolved:',missing)
