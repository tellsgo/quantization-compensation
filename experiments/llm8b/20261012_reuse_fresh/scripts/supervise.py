"""Run each model on an idle GPU without interrupting unrelated processes."""
from pathlib import Path
import json,os,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from core import write_json

def idle():
 raw=subprocess.check_output(['nvidia-smi','--query-gpu=index,memory.used,utilization.gpu','--format=csv,noheader,nounits'],text=True)
 return [int(r[0]) for line in raw.splitlines() if (r:=[v.strip() for v in line.split(',')]) and int(r[1])<1024 and int(r[2])<10]
def snapshot(active,pending,finished):
 d={'status':'running','pending':pending,'finished':finished,'workers':[],'heartbeat_unix':time.time()}
 for model,w in active.items():
  p=ROOT/'results'/model
  progress={x.parent.name:json.loads(x.read_text()) for x in p.glob('*/progress.json')}
  d['workers'].append({'model':model,'gpu':w['gpu'],'pid':w['process'].pid,'paths':progress})
 write_json(ROOT/'results/STATUS.json',d)
def main():
 started=time.time();pending=['qwen3','llama3'];active={};finished=[];failed=[]
 # Prevent two supervisors for the same experiment.
 lock=ROOT/'verification/supervisor.lock';fd=os.open(lock,os.O_CREAT|os.O_EXCL|os.O_WRONLY)
 os.write(fd,str(os.getpid()).encode());os.close(fd)
 try:
  while pending or active:
   for model,w in list(active.items()):
    code=w['process'].poll()
    if code is not None:
     w['log'].close();del active[model]
     if code==0:finished.append(model)
     else:failed.append({'model':model,'exit_code':code})
     print(json.dumps({'event':'worker_finished','model':model,'code':code}),flush=True)
   try:free=[g for g in idle() if g not in {w['gpu'] for w in active.values()}]
   except subprocess.CalledProcessError:free=[]
   for gpu in free:
    if not pending:break
    available=int(next(s.split()[1] for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')))*1024
    if available<24*1024**3:break
    model=pending.pop(0);log=(ROOT/'results'/f'{model}_worker.log').open('a')
    env=os.environ.copy();env['CUDA_VISIBLE_DEVICES']=str(gpu);env['TOKENIZERS_PARALLELISM']='false'
    worker=subprocess.Popen([sys.executable,str(ROOT/'src/run.py'),'--model-key',model],stdout=log,stderr=subprocess.STDOUT,cwd=ROOT,env=env)
    active[model]={'process':worker,'gpu':gpu,'log':log}
    print(json.dumps({'event':'worker_started','model':model,'gpu':gpu,'pid':worker.pid}),flush=True)
   snapshot(active,pending,finished)
   if pending or active:time.sleep(20)
  if not failed:
   subprocess.run([sys.executable,str(ROOT/'scripts/analyze.py')],cwd=ROOT,check=True)
  write_json(ROOT/'results/STATUS.json',{'status':'failed' if failed else 'complete','failed':failed,'finished':finished,'wall_seconds':time.time()-started})
 finally:lock.unlink(missing_ok=True)
if __name__=='__main__':main()
