import asyncio, json, pathlib, sys, logging
logging.getLogger('aristotle').setLevel(logging.ERROR)
from aristotlelib import Project, ProjectStatus
S=pathlib.Path(__file__).parent
pid=json.loads((S/'project.json').read_text())['project_id']
async def main():
    p=await Project.from_id(pid)
    d=p.model_dump(mode='json')
    tasks,_=await p.get_tasks(limit=3)
    tl=[]
    for t in tasks:
        td=t.model_dump(mode='json'); tl.append({k:str(td.get(k))[:120] for k in ('status','task_type','created_at','last_updated','summary','error') if k in td})
    print('status', ProjectStatus(d['status']).name, 'has_files', d.get('has_files'), 'updated', d.get('last_updated'), 'tasks', tl)
    if ProjectStatus(d['status'])==ProjectStatus.IDLE or (d.get('has_files') and ProjectStatus(d['status'])!=ProjectStatus.RUNNING):
        out=await p.get_files(destination=S/'result.tar.gz')
        print('DONE downloaded', out); sys.exit(0)
    sys.exit(3)
asyncio.run(main())
