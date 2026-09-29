#!/usr/bin/env python3
"""Summarise a dead agent's transcript from the Sept 26 coordinator session (kmit profile).
usage: dead_lane_tail.py <agentId> [n_texts=15] [n_tools=25]
Prints the agent's prompt head, its last n assistant texts, its last n tool calls, and the agentIds
of sub-agents it launched (feed those back into this script)."""
import json, sys, glob, re
D='/root/.claude-kmit/projects/-shared-lean-xv6/4a87f93d-3b6b-442a-88f3-0eae14141bc4/subagents'
aid=sys.argv[1]; nt=int(sys.argv[2]) if len(sys.argv)>2 else 15; nu=int(sys.argv[3]) if len(sys.argv)>3 else 25
f=glob.glob(f'{D}/agent-{aid}.jsonl')[0]
texts=[]; tools=[]; subs=[]; first=None
for l in open(f):
    try: d=json.loads(l)
    except Exception: continue
    c=d.get('message',{}).get('content'); ts=d.get('timestamp','')[:19]
    if first is None and d.get('type')=='user': first=c if isinstance(c,str) else json.dumps(c)[:3000]
    if not isinstance(c,list): continue
    for b in c:
        if b.get('type')=='text' and d.get('type')=='assistant': texts.append((ts,b['text']))
        elif b.get('type')=='tool_use':
            tools.append((ts,b['name'],json.dumps(b['input'])[:400]))
            if b['name'] in ('Agent','Task'): subs.append((ts,b['input'].get('description'),None))
        elif b.get('type')=='tool_result':
            s=b.get('content'); s=s if isinstance(s,str) else json.dumps(s)
            m=re.search(r'agentId: (\w+)',s)
            if m and subs and subs[-1][2] is None: subs[-1]=(subs[-1][0],subs[-1][1],m.group(1))
print('=== PROMPT (head)\n',(first or '')[:3000])
print('=== SUB-AGENTS'); [print(' ',*s) for s in subs]
print(f'=== LAST {nt} TEXTS'); [print('--',t,'\n',x[:4000]) for t,x in texts[-nt:]]
print(f'=== LAST {nu} TOOL CALLS'); [print('--',*t) for t in tools[-nu:]]
