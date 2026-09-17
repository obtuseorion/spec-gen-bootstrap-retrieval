"""Extract Aristotle's proofs from result.tar.gz and run each through leantools proofcheck."""
import json, pathlib, re, subprocess, sys, tarfile, textwrap
S=pathlib.Path(__file__).parent; ROOT=pathlib.Path('/Users/urbasekka/Documents/spec-gen-bootstrap-retrieval')
out=S/'result'; out.mkdir(exist_ok=True)
with tarfile.open(S/'result.tar.gz') as t: t.extractall(out)
files=list(out.rglob('AristotleTargets.lean')); assert files, 'no AristotleTargets.lean in result'
text=files[0].read_text(); print('result file:', files[0], len(text), 'bytes')
# split top-level declarations: theorem blocks start at '@[step]\ntheorem' and end at the next top-level decl or 'end MlKem'
blocks=re.split(r'\n(?=@\[step\]\s*\n(?:theorem|axiom)\s|axiom\s|end MlKem)', text)
results={}
for b in blocks:
    m=re.match(r'@\[step\]\s*\ntheorem\s+([\w.]+)', b)
    if not m: continue
    name=m.group(1)
    if ':= by' not in b: print(name, 'no `:= by`'); continue
    head, proof = b.split(':= by', 1)
    proof=textwrap.dedent(proof).strip('\n')
    if 'sorry' in proof: print('##', name, 'still has sorry'); results[name]='sorry'; continue
    member='MlKem.'+name[:-len('_spec')] if name.endswith('_spec') else 'MlKem.'+name
    d=S/'check'/member; (d/'specs').mkdir(parents=True, exist_ok=True); (d/'proofs').mkdir(exist_ok=True)
    (d/'specs'/f'{member}.lean').write_text(head.rstrip()+' := by sorry\n')
    (d/'proofs'/f'{member}.lean').write_text(proof+'\n')
    argv=['lake','exe','leantools','proofcheck','--project',str(ROOT/'crates/mlkem-lean'),'--namespace','MlKem','--unit',member,'--members',member,
          '--spec',str(d/'specs'),'--proof',str(d/'proofs'),'--callee-specs',str(ROOT/'corpus_store/mlkem/A/specs')]
    r=subprocess.run(argv,cwd=ROOT/'pipeline/lean_tools',capture_output=True,text=True,timeout=1800)
    try: j=json.loads(r.stdout.strip().splitlines()[-1])
    except Exception: j={'error':'no JSON: '+r.stderr[-500:]}
    summary={k:j.get(k) for k in ('kernel_ok','axioms_ok','static_ok','opaque_ok','axioms','static_violations')}
    summary['error']=(j.get('error') or '')[:300]
    print('##', name, '->', 'ACCEPTED' if all(j.get(k) for k in ('kernel_ok','axioms_ok','static_ok','opaque_ok')) else 'REJECTED', summary)
    results[name]=summary
(S/'verify.json').write_text(json.dumps(results,indent=1))
