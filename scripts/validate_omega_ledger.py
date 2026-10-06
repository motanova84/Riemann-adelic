#!/usr/bin/env python3
import argparse, json, sys
from pathlib import Path
ORDER={"FALSIFIED":0,"OPEN":1,"PREDICTED":2,"VERIFIED":3,"FORMALIZED":4,"PROVEN":5}
REQ={"id","claim","type","deps","proof","code","dataset","hash","result","status"}
def fail(m): print('ERROR:',m,file=sys.stderr); raise SystemExit(1)
def validate(p):
 d=json.loads(Path(p).read_text(encoding='utf-8')); es=d.get('entries',[])
 if d.get('ledger')!='QCAL Ω Audit Ledger' or d.get('version')!='1.0.1': fail('invalid ledger header')
 by={}
 for e in es:
  miss=REQ-e.keys()
  if miss: fail(f"{e.get('id')}: missing {sorted(miss)}")
  if e['id'] in by: fail('duplicate '+e['id'])
  if e['status'] not in ORDER: fail(f"{e['id']}: bad status")
  by[e['id']]=e
 for e in es:
  for dep in e['deps']:
   if dep.startswith('AXIOM_'): continue
   if dep not in by: fail(f"{e['id']}: unknown dependency {dep}")
   if ORDER[e['status']]>ORDER[by[dep]['status']]: fail(f"{e['id']}: inheritance violation via {dep}")
 graph={e['id']:[x for x in e['deps'] if not x.startswith('AXIOM_')] for e in es}; seen=set(); active=set()
 def dfs(n):
  if n in active: fail('dependency cycle at '+n)
  if n in seen:return
  active.add(n)
  for x in graph[n]:dfs(x)
  active.remove(n);seen.add(n)
 for n in graph:dfs(n)
 return d
def main():
 a=argparse.ArgumentParser();a.add_argument('ledger',nargs='?',default='ledger/omega.json');x=a.parse_args();d=validate(x.ledger)
 c={s:sum(e['status']==s for e in d['entries']) for s in ORDER};print('QCAL Ω Audit Ledger: PASS');print(json.dumps({'version':d['version'],'entries':len(d['entries']),'counts':c},ensure_ascii=False))
if __name__=='__main__':main()
