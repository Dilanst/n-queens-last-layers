"""Comprueba las fuentes de la formalización de «Completabilidad de las últimas capas» con Python 3 y una instalación local de Lean."""
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
    for line in (ROOT/'fuentes.sha256').read_text(encoding='ascii').splitlines():
        match=re.fullmatch(r'([a-f0-9]{64})  fuentes/([A-Za-z0-9_]+)\.lean',line)
        if not match:raise ValueError(line)
        digest,name=match.groups()
        path=ROOT/'fuentes'/(name+'.lean')
        if name in files or hashlib.sha256(path.read_bytes()).hexdigest()!=digest:
            raise ValueError('Fuente distinta o duplicada: '+name)
        files[name]=path
    if len(files)!=659 or set((ROOT/'fuentes').glob('*.lean'))!=set(files.values()):
        raise ValueError('Inventario incompleto')
    order=[]; visiting=set(); done=set()
    def visit(name):
        if name in done:return
        if name in visiting:raise ValueError('Ciclo en '+name)
        visiting.add(name)
        for dep in re.findall(r'^import\s+(\S+)\s*$',files[name].read_text(encoding='utf-8-sig'),re.M):
            if dep.split('.')[0] not in {'Lean','Std','Init','Mathlib'}:visit(dep)
        visiting.remove(name);done.add(name);order.append(name)
    for name in sorted(files):visit(name)
    return files,order

def main():
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--solo-inventario',action='store_true')
    cli.add_argument('--lean',type=Path,help='Ejecutable de Lean 4.19.0')
    cli.add_argument('--mathlib',type=Path,help='Checkout local de mathlib con sus dependencias compiladas')
    a=cli.parse_args()
    files,order=inventory()
    print(f'{len(order)} módulos con fuentes y grafo de importaciones comprobados.',flush=True)
    if a.solo_inventario:return
    if a.lean is None or a.mathlib is None:cli.error('Indique --lean y --mathlib.')
    compiler=a.lean.resolve(strict=True); math=a.mathlib.resolve(strict=True)
    version=subprocess.check_output([str(compiler),'--version'],text=True)
    if 'version 4.19.0,' not in version:raise ValueError(version)
    if subprocess.check_output(['git','-C',str(math),'rev-parse','HEAD'],text=True).strip()!=REV:
        raise ValueError('Revisión de mathlib distinta de la indicada.')
    print(version.strip(),REV,flush=True)
    with tempfile.TemporaryDirectory(prefix='completabilidad-') as tmp:
        libs=[Path(tmp),math/'.lake/build/lib/lean']
        libs.extend(p/'.lake/build/lib/lean' for p in (math/'.lake/packages').iterdir() if p.is_dir())
        env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,libs)))
        for i,name in enumerate(order,1):
            print(f'{i}/{len(order)} {name}',flush=True)
            subprocess.run([str(compiler),'-DwarningAsError=true','-o',str(Path(tmp)/(name+'.olean')),files[name].name],
                           cwd=ROOT/'fuentes',env=env,check=True)
        input_text=f'import {FINAL}\n#check {DECL}\n#print axioms {DECL}\n'
        result=subprocess.run([str(compiler),'-DwarningAsError=true','--stdin'],input=input_text,
                              cwd=ROOT/'fuentes',env=env,encoding='utf-8',capture_output=True)
        print(result.stdout+result.stderr)
        result.check_returncode()
        if not re.search(r'\[propext,\s*Classical.choice,\s*Quot.sound\]',result.stdout):
            raise ValueError('Revise la lista de axiomas del teorema final.')

if __name__=='__main__':main()

