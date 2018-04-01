import unittest, logging
import archinfo

from rop_compiler.gadget import *
import rop_compiler.classifier as classifier

class ClassifierTests(unittest.TestCase):

  def run_test(self, arch, tests):
    gadget_classifier = classifier.GadgetClassifier(arch, log_level = logging.DEBUG)
    for (expected_types, code) in tests:
      gadgets = gadget_classifier.create_gadgets_from_instructions(code, 0x40000)

      # For each returned gadget, count the number of each gadget types
      types = {}
      for g in gadgets:
        if type(g) not in types: types[type(g)] = 0
        types[type(g)] += 1
      self.assertEqual(types, expected_types)

  def test_amd64(self):
    tests = [
      ({Jump : 1},            '\xff\xe0'),                                                # jmp rax
      ({MoveReg : 2},         '\x48\x93\xc3'),                                            # xchg rbx, rax; ret
      ({MoveReg : 1},         '\x48\x89\xcb\xc3'),                                        # mov rbx,rcx; ret
      ({LoadConst : 1},       '\x48\xbb\xff\xee\xdd\xcc\xbb\xaa\x99\x88\xc3'),            # movabs rbx,0x8899aabbccddeeff; ret
      ({AddGadget : 1},       '\x48\x01\xc3\xc3'),                                        # add rbx, rax; ret
      ({LoadMem : 1},         '\x5f\xc3'),                                                # pop rdi; ret
      ({LoadMem : 1},         '\x48\x8b\x43\x08\xc3'),                                    # mov rax,QWORD PTR [rbx+0x8]; ret
      ({LoadMem : 1},         '\x48\x8b\x07\xc3'),                                        # mov rax,QWORD PTR [rdi]; ret
      ({StoreMem : 1},        '\x48\x89\x03\xc3'),                                        # mov QWORD PTR [rbx],rax; ret
      ({StoreMem : 1},        '\x48\x89\x43\x08\xc3'),                                    # mov QWORD PTR [rbx+0x8],rax; ret
      ({StoreMem : 1},        '\x48\x89\x44\x24\x08\xc3'),                                # mov QWORD PTR [rsp+0x8],rax; ret
      ({LoadAddGadget: 1},    '\x48\x03\x03\xc3'),                                        # add rax,QWORD PTR [rbx]
      ({StoreAddGadget: 1},   '\x48\x01\x43\xf8\xc3'),                                    # add QWORD PTR [rbx-0x8],rax; ret
      ({},                    '\x48\x39\xeb\xc3'),                                        # cmp rbx, rbp; ret
      ({},                    '\x5e'),                                                    # pop rsi
      ({},                    '\x8b\x04\xc5\xc0\x32\x45\x00\xc3'),                        # mov rax,QWORD PTR [rax*8+0x4532c0]
      ({LoadMem : 1, LoadConst : 1}, '\x59\x48\x89\xcb\x48\xc7\xc1\x05\x00\x00\x00\xc3'), # pop rcx; mov rbx,rcx; mov rcx,0x5; ret
      ({},                    '\x48\x8b\x85\xf0\xfd\xff\xff\x48\x83\xc0'),
#      ({LoadMemJump : 1, },   '\x5a\xfc\xff\xd0'),                                       # pop rdx, cld, call rax
      ({LoadMem : 3, LoadMultiple : 1}, '\x5f\x5e\x5a\xc3'),                              # pop rdi; pop rsi; pop rdx; ret
      ({AddConstGadget : 1},  '\x48\x05\x44\x33\x22\x11\xc3'),                            # add rax, 0x11223344; ret
      ({AddConstGadget : 1, LoadConst : 1},                                               # movabs rbx,0x1122334455667788;
        '\x48\xbb\x88\x77\x66\x55\x44\x33\x22\x11\x48\x01\xd8\xc3'),                      # add rax,rbx; ret
      ({AddConstGadget : 1}, '\x48\xff\xc0\xc3'),                                         # inc rax; ret

      ({LoadMem : 2}, '\x58\x48\x89\xc3\xc3'),                                            # pop rax; mov rbx, rax; ret
      ({LoadMem : 3, LoadMultiple : 2}, '\x59\x58\x48\x89\xc3\xc3'),                      # pop rcx; pop rax; mov rbx, rax; ret

      # Don't allow more than one read from any register but the stack
      ({} , '\x48\x8b\x19\x48\x8b\x41\x08\xc3'), # mov rbx,QWORD PTR [rcx]; mov rax,QWORD PTR [rcx+0x8]; ret
    ]
    self.run_test(archinfo.ArchAMD64(), tests)

  def test_x86(self):
    tests = [
      ({Jump : 1},           '\xff\xe0'),                  # jmp eax
      ({MoveReg : 2},        '\x93\xc3'),                  # xchg ebx, eax; ret
      ({MoveReg : 1},        '\x89\xcb\xc3'),              # mov ebx, ecx; ret
      ({LoadConst : 1},      '\xbb\xff\xee\xdd\xcc\xc3'),  # mov ebx, 0xccddeeff; ret
      ({AddGadget : 1},      '\x01\xc3\xc3'),              # add ebx, eax; ret
      ({LoadMem : 1},        '\x5f\xc3'),                  # pop edi; ret
      ({LoadMem : 1},        '\x8b\x43\x08\xc3'),          # mov eax, DWORD PTR [ebx+0x8]; ret
      ({LoadMem : 1},        '\x8b\x07\xc3'),              # mov eax, DWORD PTR [edi]; ret
      ({StoreMem : 1},       '\x89\x03\xc3'),              # mov DWORD PTR [ebx], eax; ret
      ({StoreMem : 1},       '\x89\x43\x08\xc3'),          # mov DWORD PTR [ebx+0x8], eax; ret
      ({StoreMem : 1},       '\x89\x44\x24\x04\xc3'),      # mov DWORD PTR [esp+0x4], eax; ret
      ({LoadAddGadget: 1},   '\x03\x03\xc3'),              # add eax, DWORD PTR [ebx]
      ({StoreAddGadget: 1},  '\x01\x43\xf8\xc3'),          # add DWORD PTR [ebx-0x8], eax; ret
      ({AddConstGadget : 1}, '\x4a\x89\xd0\xc3'),          # dec edx; mov eax, edx; ret
    ]
    self.run_test(archinfo.ArchX86(), tests)

  def test_arm(self):
    tests = [
      ({LoadMem     : 1}, '\x08\x80\xbd\xe8'),                 # pop {r3, pc}
      ({MoveReg     : 1}, '\x02\x00\xa0\xe1\x04\xf0\x9d\xe4'), # mov r0, r2; pop {pc}
      ({LoadMem     : 7, LoadMultiple : 1}, '\xf0\x87\xbd\xe8'), # pop {r4, r5, r6, r7, r8, r9, sl, pc}
      ({LoadMem     : 2, LoadMultiple : 1}, '\x04\xe0\x9d\xe5\x08\xd0\x8d\xe2'   # ldr lr, [sp, #4]; add sp, sp, #8
                        + '\x0c\x00\xbd\xe8\x1e\xff\x2f\xe1'), # pop {r2, r3}; bx lr
      ({LoadMemJump : 6, Jump : 1},
                          '\x1f\x40\xbd\xe8\x1c\xff\x2f\xe1'), # pop {r0, r1, r2, r3, r4, lr}; bx r12
      ({LoadMemJump : 1, Jump : 1},
                          '\x04\xe0\x9d\xe4\x13\xff\x2f\xe1'), # pop {lr}; bx r3
    ]
    self.run_test(archinfo.ArchARM(), tests)

  def test_mips(self):
    tests = [
      ({LoadMem : 1},
        '\x8f\xbf\x00\x10' + # lw ra,16(sp)
        '\x8f\xb0\x00\x08' + # lw s0,8(sp)
        '\x03\xe0\x00\x08' + # jr ra
        '\x27\xbd\x00\x20' + # addiu sp,sp,32
        '\x00\x00\x00\x00'), # nop
      ({LoadMem : 6, LoadMultiple : 1},
        '\x8f\xbf\x00\x44' + # lw ra,68(sp)
        '\x8f\xb5\x00\x3c' + # lw s5,60(sp)
        '\x8f\xb4\x00\x38' + # lw s4,56(sp)
        '\x8f\xb3\x00\x34' + # lw s3,52(sp)
        '\x8f\xb2\x00\x30' + # lw s2,48(sp)
        '\x8f\xb1\x00\x2c' + # lw s1,44(sp)
        '\x8f\xb0\x00\x28' + # lw s0,40(sp)
        '\x27\xbd\x00\x48' + # addiu sp,sp,72
        '\x03\xe0\x00\x08' + # jr ra
        '\x00\x00\x00\x00'),  # nop
      ({LoadMem : 1},
        '\x8f\xb9\x00\x08' + # lw t9,8(sp)
        '\x8f\xbf\x00\x04' + # lw ra,4(sp)
        '\x03\x20\x00\x08' + # jr t9
        '\x27\xbd\x00\x10' + # addiu sp,sp,16
        '\x00\x20\x08\x25' + # move at, at (nop)
        '\x00\x20\x08\x25' + # move at, at (nop)
        '\x00\x20\x08\x25' + # move at, at (nop)
        '\x00\x20\x08\x25' + # move at, at (nop)
        '\x00\x20\x08\x25'), # move at, at (nop)
    ]
    self.run_test(archinfo.ArchMIPS32('Iend_BE'), tests)

  def test_ppc_le(self):
    tests = [
      ({LoadMem : 1},
        '\x08\x00\xe1\x83' + # lwz r31,8(r1)
        '\x04\x00\x01\x80' + # lwz r0,4(r1)
        '\xa6\x03\x08\x7c' + # mtlr r0
        '\x10\x00\x21\x38' + # addi r1,r1,16
        '\x20\x00\x80\x4e'), # blr
    ]
    self.run_test(archinfo.ArchPPC32(), tests)

  def test_ppc_be(self):
    tests = [
      ({LoadMem: 2, LoadMultiple : 1},
        '\x80\x01\x00\x1c' + # lwz r0,28(r1)
        '\x80\x61\x00\x08' + # lwz r3,8(r1)
        '\x80\x81\x00\x0c' + # lwz r4,12(r1)
        '\x38\x21\x00\x20' + # addi r1,r1,32
        '\x7c\x08\x03\xa6' + # mtlr r0
        '\x4e\x80\x00\x20'), # blr
    ]
    self.run_test(archinfo.ArchPPC32('Iend_BE'), tests)

if __name__ == '__main__':
  unittest.main()
