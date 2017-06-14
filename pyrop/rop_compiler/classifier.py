import collections, logging, random, sys, traceback
import pyvex, archinfo

from gadget import *
import utils, extra_archinfo, validator

class GadgetClassifier(object):
  """This class is used to convert a set of instructions that represent a gadget into a Gadget class of the appropriate type"""

  """The number of times to emulate a gadget when classifying it"""
  NUM_EMULATIONS = 5

  def __init__(self, arch, validate_gadgets = False, log_level = logging.WARNING):
    logging.basicConfig(format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    self.arch = arch
    self.validate_gadgets = validate_gadgets
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.setLevel(log_level)

    # A couple helper fields
    self.sp = self.arch.registers['sp'][0]
    self.ip = self.arch.registers['ip'][0]

  def is_ignored_register(self, register):
    return self.arch.translate_register_name(register) in extra_archinfo.IGNORED_REGISTERS[self.arch.name]

  def irsb_ends_with_constant_pc(self, irsb):
    """A really bad hack to try to detect if the pc register gets set by the IRSB to a non-constant value (i.e. a jump/ret)"""
    for stmt in irsb.statements:
      # if the statement is a PUT that sets the pc register, and it's a non-constant value
      if stmt.tag == 'Ist_Put' and stmt.offset == self.arch.registers['pc'][0] and stmt.data.tag != 'Iex_Const':
        return False
    return True

  def get_irsbs(self, code, address):
    irsbs = []
    code_address = address
    while code_address <= address + len(code) - self.arch.instruction_alignment:
      try:
        irsb = pyvex.IRSB(code[code_address-address:], code_address, self.arch, opt_level=0)
        irsbs.append(irsb)
      except: # If decoding fails, we can't use this gadget
        traceback.print_exc()
        return [] # So just return an empty list

      if (self.arch.name not in extra_archinfo.ENDS_EARLY_ARCHS
        or irsb.jumpkind != 'Ijk_Boring'
        or not self.irsb_ends_with_constant_pc(irsb)):
        break

      # Find the last address that was translated (For some architectures, pyvex stops before the end of a block)
      last_addr = None
      for stmt in irsb.statements:
        if stmt.tag == 'Ist_IMark':
          last_addr = stmt.addr

      # If we couldn't get any statements from the instructions, there was a problem.
      if last_addr == None:  # So just return an empty list
        return []

      # And move the code address forward to the next untranslated instruction
      code_address = last_addr + self.arch.instruction_alignment

    return irsbs

  def get_stack_offset(self, state):
    stack_offset = 0
    if self.sp in state.out_regs and self.sp in state.in_regs:
      stack_offset = state.out_regs[self.sp] - state.in_regs[self.sp]
    if stack_offset < 0:
      stack_offset = None
    return stack_offset

  def get_new_ip_from_potential_gadget(self, possible_types):
    """Finds the offset of rip in the stack, or whether it was set via a register for a list of potential gadgets"""
    ip_in_stack_offset = ip_from_reg = None
    for (gadget_type, inputs, outputs, params, clobber) in possible_types:
      if gadget_type == LoadMem and outputs[0] == self.ip and inputs[0] == self.sp:
        ip_in_stack_offset = params[0]
      if gadget_type == MoveReg and outputs[0] == self.ip:
        ip_from_reg = inputs[0]
    return ip_in_stack_offset, ip_from_reg

  def calculate_clobber_registers(self, state, gadget_type, outputs):
    clobber = []
    for oreg in state.out_regs.keys():
      if oreg not in outputs and oreg != self.ip and oreg != self.sp and not self.is_ignored_register(oreg):
        clobber.append(oreg)
    return clobber

  def create_gadgets_from_instructions(self, code, address):
    irsbs = self.get_irsbs(code, address)
    if len(irsbs) == 0:
      return []

    possible_types = None
    stack_offsets = set()
    for i in range(self.NUM_EMULATIONS):
      state = EvaluateState(self.arch)
      evaluator = PyvexEvaluator(state, self.arch)
      if not evaluator.emulate_irsbs(irsbs):
        return []
      state = evaluator.get_state()

      # Calculate the possible types
      possible_types_this_round = self.check_execution_for_gadget_types(state)

      # Get the stack offset and clobbers register set
      stack_offsets.add(self.get_stack_offset(state))

      if possible_types == None: # For the first round, just make sure that each type only accesses acceptable regions of memory
        possible_types = []
        for possible_type_this_round in possible_types_this_round:
          if self.all_acceptable_memory_accesses(state, possible_type_this_round):
            possible_types.append(possible_type_this_round)
      else: # For each round, only keep the potential gadgets that are in each round
        new_possible_types = []
        for possible_type_this_round in possible_types_this_round:
          for possible_type in possible_types:
            if possible_type_this_round == possible_type:
              new_possible_types.append(possible_type)
        possible_types = new_possible_types

    # Get the new IP and SP values
    ip_in_stack_offset, ip_from_reg = self.get_new_ip_from_potential_gadget(possible_types)
    stack_offset = stack_offsets.pop()
    if len(stack_offsets) != 0 or stack_offset == None: # We require a constant non-negative change in the stack size
      return []

    gadgets = []
    for (gadget_type, inputs, outputs, params, clobber) in possible_types:
      if (
        # Ignore the LoadMem gadget for the IP register
        (len(outputs) > 0 and outputs[0] == self.ip and gadget_type != Jump)

        # Except for Jump, all the gadgets must load rip from the stack
        or ((ip_in_stack_offset == None and gadget_type != Jump) and not (ip_from_reg != None and gadget_type == LoadMem))

        # If the ip is outside the stack portion for the gadget, ignore the gadget
        or (ip_in_stack_offset != None and ip_in_stack_offset > stack_offset)

        # If the gadget doesn't get adjusted properly for stack base LoadMem gadgets, ignore the gadget
        or (gadget_type == LoadMem and inputs[0] == self.sp and params[0] + (self.arch.bits/8) > stack_offset)

        # We don't care about finding gadgets that only set the flags
        or (len(outputs) != 0 and all(map(self.is_ignored_register, outputs)))

        # If it's a LoadMem that results in a jmp to the load register, thus we can't actually load any value we want
        or (gadget_type == LoadMem and params[0] == ip_in_stack_offset and inputs[0] == self.sp)
        ):
        continue

      # Convert a LoadMem gadget into a LoadMemJump if the IP is set from a register
      if ip_from_reg != None and gadget_type == LoadMem:
        gadget_type = LoadMemJump
        inputs.append(ip_from_reg)

      gadget = gadget_type(self.arch, address, inputs, outputs, params, clobber, stack_offset, ip_in_stack_offset)
      if gadget != None and self.validate_gadgets:
        gadget_validator = validator.Validator(self.arch)
        if not gadget_validator.validate_gadget(gadget, irsbs):
          gadget = None

      if gadget != None:
        self.logger.debug("Found gadget: %s", str(gadget))
        gadgets.append(gadget)

    return gadgets

  def all_acceptable_memory_accesses(self, state, possible_type):
    (gadget_type, inputs, outputs, params, clobber) = possible_type

    # Always allow the LoadMem gadget for loading IP from the Stack
    if gadget_type == LoadMem and outputs[0] == self.ip and inputs[0] == self.sp:
      return True

    for mem_address, mem_value in state.in_mem.items():
      good_mem_access = False
      if not (
          # Allow the LoadMem's read
          (gadget_type == LoadMem and mem_address == state.in_regs[inputs[0]] + params[0] and state.out_regs[outputs[0]] == mem_value)

          # Allow the ArithmeticLoad's read
          or (issubclass(gadget_type, ArithmeticLoad) and mem_address == state.in_regs[inputs[0]] + params[0])

          # Allow the ArithmeticStore's read
          or (issubclass(gadget_type, ArithmeticStore) and mem_address == state.in_regs[inputs[0]] + params[0])

          # Allow loads from the SP register (i.e. pop) and only allow the parameter to be a max of 0x1000
          or (self.sp in state.in_regs and abs(mem_address - state.in_regs[self.sp]) < 0x1000)
      ):
        return False

    for mem_address, mem_value in state.out_mem.items():
      if not (
        # Allow the StoreMem's write
        (gadget_type == StoreMem and mem_address == state.in_regs[inputs[0]] + params[0] and mem_value == state.in_regs[inputs[1]])

        # Allow the ArithmeticStore's write
        or (issubclass(gadget_type, ArithmeticStore) and mem_address == state.in_regs[inputs[0]] + params[0])
      ):
        return False

    return True

  def check_execution_for_gadget_types(self, state):
    """Given the results of an emulation of a set of instructions, check the results to determine any potential gadget types and
      the associated inputs, outputs, and parameters.  This is done by checking the results to determine any of the
      preconditions that the gadget follows for this execution.  This method returns a list of the format
      (Gadget Type, list of inputs, output, list of parameters).  Note the returned potential gadgets are a superset of the
      actual gadgets, i.e. some of the returned ones are merely coincidences in the emulation, and not true gadgets."""
    possible_types = []
    all_loaded_regs = {}
    for oreg, ovalue in state.out_regs.items():
      # Check for LOAD_CONST (it'll get filtered between the multiple rounds)
      possible_types.append((LoadConst, [], [oreg], [ovalue]))

      for ireg, ivalue in state.in_regs.items():
        # Check for MoveReg
        if ovalue == ivalue:
          possible_types.append((MoveReg, [ireg], [oreg], []))

        # Check for Jump
        if oreg == self.arch.registers['ip'][0]:
          possible_types.append((Jump, [ireg], [oreg], [ovalue - ivalue]))

        # Check for Arithmetic
        if ireg != oreg: # add rbx, rax (where rbx is dst/operand 1 and rax is operand 2)
          continue

        for ireg2, ivalue2 in state.in_regs.items():
          for gadget_type in [AddGadget, SubGadget, MulGadget, AndGadget, OrGadget, XorGadget]:
            if ovalue == gadget_type.binop(ivalue, ivalue2):
              possible_types.append((gadget_type, [ireg, ireg2], [oreg], []))

        # Check for ArithmeticConst
        if oreg != self.sp:
          possible_types.append((AddConstGadget, [ireg], [oreg], [ovalue - ivalue]))

      for address, value_at_address in state.in_mem.items():
        # Check for ArithmeticLoad
        for ireg, ivalue in state.in_regs.items():
          for addr_reg, addr_reg_value in state.in_regs.items():
            for gadget_type in [LoadAddGadget, LoadSubGadget, LoadMulGadget, LoadAndGadget, LoadOrGadget, LoadXorGadget]:
              if ovalue == gadget_type.binop(ivalue, value_at_address):
                possible_types.append((gadget_type, [addr_reg, ireg], [oreg], [address - addr_reg_value]))

        # Check for LoadMem
        if ovalue == value_at_address:
          for ireg, ivalue in state.in_regs.items():
            possible_types.append((LoadMem, [ireg], [oreg], [address - ivalue]))

            # Gather all output registers for the LoadMultiple check
            if (oreg != self.ip and # We don't want to include the IP register in the LoadMultiple outputs,
              (self.ip not in state.out_regs.keys() or ovalue != state.out_regs[self.ip])): # Or a register which becomes the IP
              all_loaded_regs[oreg] = address

    # Check for LoadMultiple
    # Note: we don't bother checking that they're all being loaded via the same register since we later only allow non-LoadMem
    # reads only if they're from the stack pointer
    if len(all_loaded_regs) > 1:

      # Gather all the [address] -> register pairings
      params_to_regs = collections.defaultdict(list, {})
      for oreg, address in all_loaded_regs.items():
        params_to_regs[address].append(oreg)

      # Get all the permutations of registers we can set at once without using the same address twice
      permutations = utils.get_permutations(params_to_regs, params_to_regs.keys())
      for permutation in permutations:
        if len(permutation) > 1:
          permutation.sort() # sort to make sure they're always in the same order
          for ireg, ivalue in state.in_regs.items():
            possible_types.append((LoadMultiple, [ireg], permutation, map(lambda r: all_loaded_regs[r] - ivalue, permutation)))

    for address, value in state.out_mem.items():
      for ireg, ivalue in state.in_regs.items():
        # Check for StoreMem
        if value == ivalue:
          for addr_reg, addr_reg_value in state.in_regs.items():
            possible_types.append((StoreMem, [addr_reg, ireg], [], [address - addr_reg_value]))

        # Check for ArithmeticStore
        initial_memory_value = None
        if not address in state.in_mem.keys():
          continue

        initial_memory_value = state.in_mem[address]
        for addr_reg, addr_reg_value in state.in_regs.items():
          for gadget_type in [StoreAddGadget, StoreSubGadget, StoreMulGadget, StoreAndGadget, StoreOrGadget, StoreXorGadget]:
            if value == gadget_type.binop(initial_memory_value, ivalue):
              possible_types.append((gadget_type, [addr_reg, ireg], [], [address - addr_reg_value]))

    # Add the clobber set to the possible types
    possible_types_with_clobber = []
    for (gadget_type, inputs, outputs, params) in possible_types:
      clobber = self.calculate_clobber_registers(state, gadget_type, outputs)
      possible_types_with_clobber.append((gadget_type, inputs, outputs, params, clobber))
    return possible_types_with_clobber

class EvaluateState(object):
  def new_random_number(self):
    num = random.randint(0, 2 ** (self.arch.bits - 2))
    num = (num / self.arch.instruction_alignment) * self.arch.instruction_alignment
    return num

  def new_constant(self):
    return self.constant

  def __init__(self, arch):
    self.arch = arch
    self.in_regs = collections.defaultdict(self.new_random_number, {})
    self.in_mem  = collections.defaultdict(self.new_random_number, {})

    self.out_regs = {}
    self.out_mem = {}
    self.reset_tmps()

  def reset_tmps(self):
    self.tmps = {}

  def initialize_to_constant(self, constant = 0):
    self.constant = constant
    self.in_regs = collections.defaultdict(self.new_constant, {})
    self.in_mem  = collections.defaultdict(self.new_constant, {})

  def __str__(self):
    ireg = "IR(" + ", ".join(["{}=0x{:x}".format(
      self.arch.translate_register_name(reg), value) for reg, value in self.in_regs.items()]) + ")"
    oreg = "OR(" + ", ".join(["{}=0x{:x}".format(
      self.arch.translate_register_name(reg), value) for reg, value in self.out_regs.items()]) + ")"
    imem = "IM(" + ", ".join(["0x{:x}=0x{:x}".format(addr, value) for addr, value in self.in_mem.items()]) + ")"
    omem = "OM(" + ", ".join(["0x{:x}=0x{:x}".format(addr, value) for addr, value in self.out_mem.items()]) + ")"
    return "State({}{}{}{})".format(ireg,oreg,imem,omem)

  def set_tmp(self, tmp, value):
    self.tmps[tmp] = value

  def get_tmp(self, tmp, size):
    return utils.mask(self.tmps[tmp], size)

  def set_reg(self, reg, value):
    self.out_regs[reg] = value

  def get_reg(self, reg, size):
    if reg in self.out_regs:
      return utils.mask(self.out_regs[reg], size)
    return utils.mask(self.in_regs[reg], size)

  def set_mem(self, address, value):
    self.out_mem[address] = value

  def get_mem(self, address, size):
    if address in self.out_mem:
      return utils.mask(self.out_mem[address], size)
    return utils.mask(self.in_mem[address], size)

class PyvexEvaluator(object):

  def __init__(self, state, arch):
    self.arch = arch
    self.state = state

  def emulate_irsbs(self, irsbs):
    for irsb in irsbs:
      self.tyenv = irsb.tyenv
      self.state.reset_tmps()
      for stmt in irsb.statements:
        try:
          if hasattr(self, stmt.tag):
            getattr(self, stmt.tag)(stmt)
          else:
            self.unknown_statement(stmt)
        except Exception, e:
          traceback.print_exc()
          return False
    return True

  def get_state(self):
    return self.state

  # Statement Emulators

  def Ist_WrTmp(self, stmt):
    self.state.set_tmp(stmt.tmp, getattr(self, stmt.data.tag)(stmt.data))

  def Ist_Put(self, stmt):
    self.state.set_reg(stmt.offset, getattr(self, stmt.data.tag)(stmt.data))

  def Ist_Store(self, stmt):
    address = getattr(self, stmt.addr.tag)(stmt.addr)
    value = getattr(self, stmt.data.tag)(stmt.data)
    self.state.set_mem(address, value)

  def Ist_IMark(self, stmt): pass
  def Ist_NoOp(self, stmt):  pass
  def Ist_AbiHint(self, stmt): pass
  def Ist_Exit(self, stmt): pass

  def unknown_statement(self, stmt):
    """Raises a RuntimeError. Used to signify that the current statement is one we don't know how to emulate"""
    err_msg = "Unknown statement: {}".format(stmt.tag)
    raise RuntimeError(err_msg)

  # Expression Emulators

  def Iex_CCall(self, expr):
    # TODO we don't really deal with the flags, and I've only seen this used for x86 flags, so I'm just going to ignore this for now.
    # Perhaps, at some point in the future I'll implement this
    return 0

  def Iex_Get(self, expr):
    return self.state.get_reg(expr.offset, expr.result_size(self.tyenv))

  def Iex_RdTmp(self, argument):
    return self.state.get_tmp(argument.tmp, argument.result_size(self.tyenv))

  def Iex_Load(self, expr):
    address = getattr(self, expr.addr.tag)(expr.addr)
    return self.state.get_mem(address, expr.result_size(self.tyenv))

  def Iex_Const(self, expr):
    return getattr(self, expr.con.tag)(expr.con)

  def Ico_U8(self, constant):
    return utils.mask(constant.value, 8)

  def Ico_U16(self, constant):
    return utils.mask(constant.value, 16)

  def Ico_U32(self, constant):
    return utils.mask(constant.value, 32)

  def Ico_U64(self, constant):
    return utils.mask(constant.value, 64)

  def Iex_Unop(self, expr):
    argument = getattr(self, expr.args[0].tag)(expr.args[0])
    return getattr(self, expr.op)(argument)

  def Iop_64to32(self, argument):
    return utils.mask(argument, 32)

  def Iop_64to16(self, argument):
    return utils.mask(argument, 16)

  def Iop_64to8(self, argument):
    return utils.mask(argument, 8)

  def Iop_64to1(self, argument):
    return utils.mask(argument, 1)

  def Iop_32Uto64(self, argument):
    return utils.mask(argument)

  def Iop_16Uto64(self, argument):
    return utils.mask(argument)

  def Iop_8Uto64(self, argument):
    return utils.mask(argument)

  def Iop_1Uto64(self, argument):
    return utils.mask(argument)

  def Iop_16Uto32(self, argument):
    return utils.mask(argument, 32)

  def Iop_8Uto32(self, argument):
    return utils.mask(argument, 32)

  def Iop_1Uto32(self, argument):
    return utils.mask(argument, 32)

  def sign_convert(self, argument, to_base):
    if argument >= 0:
      return argument
    else:
      return (2 ** to_base) + argument

  def Iop_32Sto64(self, argument): return self.sign_convert(argument, 64)
  def Iop_16Sto64(self, argument): return self.sign_convert(argument, 64)
  def Iop_8Sto64(self, argument):  return self.sign_convert(argument, 64)
  def Iop_16Sto32(self, argument): return self.sign_convert(argument, 32)
  def Iop_8Sto32(self, argument):  return self.sign_convert(argument, 32)
  def Iop_8Sto16(self, argument):  return self.sign_convert(argument, 16)

  def Iex_Binop(self, expr):
    left = getattr(self, expr.args[0].tag)(expr.args[0])
    right = getattr(self, expr.args[1].tag)(expr.args[1])
    return getattr(self, expr.op)(left, right)

  def Iop_And64(self, left, right): return left & right
  def Iop_And32(self, left, right): return left & right
  def Iop_And16(self, left, right): return left & right
  def Iop_And8(self, left, right):  return left & right

  def Iop_Xor64(self, left, right): return left ^ right
  def Iop_Xor32(self, left, right): return left ^ right
  def Iop_Xor16(self, left, right): return left ^ right
  def Iop_Xor8(self, left, right):  return left ^ right

  def Iop_Or64(self, left, right): return left | right
  def Iop_Or32(self, left, right): return left | right
  def Iop_Or16(self, left, right): return left | right
  def Iop_Or8(self, left, right):  return left | right

  def Iop_Add64(self, left, right): return utils.mask(left + right)
  def Iop_Add32(self, left, right): return utils.mask(left + right, 32)
  def Iop_Add16(self, left, right): return utils.mask(left + right, 16)
  def Iop_Add8(self, left, right):  return utils.mask(left + right, 8)

  def Iop_Sub64(self, left, right): return utils.mask(left - right)
  def Iop_Sub32(self, left, right): return utils.mask(left - right, 32)
  def Iop_Sub16(self, left, right): return utils.mask(left - right, 16)
  def Iop_Sub8(self, left, right):  return utils.mask(left - right, 8)

  def Iop_Shl64(self, left, right): return utils.mask(left << right)
  def Iop_Shl32(self, left, right): return utils.mask(left << right, 32)
  def Iop_Shl16(self, left, right): return utils.mask(left << right, 16)
  def Iop_Shl8(self, left, right):  return utils.mask(left << right, 8)

  def Iop_Shr64(self, left, right): return utils.mask(left >> right)
  def Iop_Shr32(self, left, right): return utils.mask(left >> right, 32)
  def Iop_Shr16(self, left, right): return utils.mask(left >> right, 16)
  def Iop_Shr8(self, left, right):  return utils.mask(left >> right, 8)

  def Iop_CmpEQ64(self, left, right): return 1 if utils.mask(left, 64) == utils.mask(right, 64) else 0
  def Iop_CmpEQ32(self, left, right): return 1 if utils.mask(left, 32) == utils.mask(right, 32) else 0

  def Iop_CmpNE64(self, left, right): return 1 if utils.mask(left, 64) != utils.mask(right, 64) else 0
  def Iop_CmpNE32(self, left, right): return 1 if utils.mask(left, 32) != utils.mask(right, 32) else 0

if __name__ == "__main__":
  import sys
  if len(sys.argv) < 3:
    print "Usage: classifier.py architecture filename [-v]"
    sys.exit(1)

  arch = archinfo.arch_from_id(sys.argv[1]).__class__
  code = utils.get_contents(sys.argv[2])

  classifier = GadgetClassifier(arch, log_level = logging.DEBUG if len(sys.argv) > 3 else logging.WARNING)
  gadgets = classifier.create_gadgets_from_instructions(code, 0x40000)
  for g in gadgets:
    print g
