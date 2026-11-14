"""Checks the sources of Paper A with Python 3 and a local Lean installation."""
import argparse
import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parent
FINAL='CierreDeLosSeisBloquesDelArticuloA'
DECL='ArticuloA.Historias.conclusion_del_articulo_A_para_los_tableros_fisicos'
REV='c44e0c8ee63ca166450922a373c7409c5d26b00b'

def inventory():
    files={}
    for line in (ROOT/'sources.sha256').read_text(encoding='ascii').splitlines():
        match=re.fullmatch(r'([a-f0-9]{64})  sources/([A-Za-z0-9_]+)\.lean',line)
        if not match:raise ValueError(line)
        digest,name=match.groups()
        path=ROOT/'sources'/(name+'.lean')
        if name in files or hashlib.sha256(path.read_bytes()).hexdigest()!=digest:
            raise ValueError('Source file changed or listed twice: '+name)
        files[name]=path
    if len(files)!=659 or set((ROOT/'sources').glob('*.lean'))!=set(files.values()):
        raise ValueError('Incomplete inventory')
    order=[]; visiting=set(); done=set()
    def visit(name):
        if name in done:return
        if name in visiting:raise ValueError('Import cycle at '+name)
        visiting.add(name)
        for dep in re.findall(r'^import\s+(\S+)\s*$',files[name].read_text(encoding='utf-8-sig'),re.M):
            if dep.split('.')[0] not in {'Lean','Std','Init','Mathlib'}:visit(dep)
        visiting.remove(name);done.add(name);order.append(name)
    for name in sorted(files):visit(name)
    return files,order

def main():
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--inventory-only',action='store_true',help='Only check the hashes and the import graph')
    cli.add_argument('--lean',type=Path,help='Lean 4.19.0 executable')
    cli.add_argument('--mathlib',type=Path,help='Local mathlib checkout with its dependencies already built')
    a=cli.parse_args()
    files,order=inventory()
    print(f'{len(order)} modules: source hashes and import graph checked.',flush=True)
    if a.inventory_only:return
    if a.lean is None or a.mathlib is None:cli.error('Give --lean and --mathlib.')
    compiler=a.lean.resolve(strict=True); math=a.mathlib.resolve(strict=True)
    version=subprocess.check_output([str(compiler),'--version'],text=True)
    if 'version 4.19.0,' not in version:raise ValueError(version)
    if subprocess.check_output(['git','-C',str(math),'rev-parse','HEAD'],text=True).strip()!=REV:
        raise ValueError('The mathlib revision differs from the required one.')
    print(version.strip(),REV,flush=True)
    with tempfile.TemporaryDirectory(prefix='paper-a-') as tmp:
        libs=[Path(tmp),math/'.lake/build/lib/lean']
        libs.extend(p/'.lake/build/lib/lean' for p in (math/'.lake/packages').iterdir() if p.is_dir())
        env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,libs)))
        for i,name in enumerate(order,1):
            print(f'{i}/{len(order)} {name}',flush=True)
            subprocess.run([str(compiler),'-DwarningAsError=true','-o',str(Path(tmp)/(name+'.olean')),files[name].name],
                           cwd=ROOT/'sources',env=env,check=True)
        input_text=f'import {FINAL}\n#check {DECL}\n#print axioms {DECL}\n'
        result=subprocess.run([str(compiler),'-DwarningAsError=true','--stdin'],input=input_text,
                              cwd=ROOT/'sources',env=env,encoding='utf-8',capture_output=True)
        print(result.stdout+result.stderr)
        result.check_returncode()
        if not re.search(r'\[propext,\s*Classical.choice,\s*Quot.sound\]',result.stdout):
            raise ValueError('Unexpected list of axioms for the final theorem.')

if __name__=='__main__':main()

