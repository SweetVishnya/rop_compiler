# This file contains a few convenience methods that wrap the ROP compiling process that can be used by exploit scripts.
import logging
import archinfo
import goal, scheduler, multifile_handler, gadget

def rop(files, libraries, goal_list, log_level = logging.WARNING, validate_gadgets = False, strategy = None, bad_bytes = None):
  """Takes a goal resolver and creates a rop chain for it.  The arguments are as follows:
  $files - a list of tuples of the form (binary filename, gadget filename, load address).  The binary filename is the name of the
    file to generate a ROP chain for.  The gadget filename is a file that has been previously generated which contains the previously
    found gadgets (using the finder.py utility script).  If a gadget file hasn't been generated before, fill in None for this argument.
    The load address of the binary is only needed for libraries and PIE binaries.
  $libraries - a list of path's to the libraries to resolve symbols in.  Primarily this is useful for libc.  This list differs from
    the files list in that the entries in this list will not be used to find gadgets (and thus their address is not needed).
  $goal_list - a list of goals to attempt to compile a ROP chain for.  See goal.py for the format of the items in this list.
  $log_level - the level of logging to display during the ROP compiling process.  Note that pyvex logs a large amount of info to
    stderr during the compilation process and will not be affected by this value (sorry).
  $validate_gadgets - whether the gadgets should be verified using z3.  While this ensures that the ROP chain will work as expected,
    it makes the finding process faster and in practice shouldn't make a difference.
  $strategy - the strategy for find gadget (see gadget.py).  This can be either FIRST, BEST, or MEDIUM; where FIRST returns the first
    gadget that matches the desired type, BEST scans the found gadgets for the best one that matches the desired type, and MEDIUM
    is a compromise between the two.  In practice, the default (MEDIUM) should work for most things.
  $bad_bytes - a list of strings that a gadget will be rejected for if it contains them
  """
  file_handler = multifile_handler.MultifileHandler(files, libraries, log_level)
  goal_resolver = goal.GoalResolver(file_handler, goal_list, log_level)

  gadgets = file_handler.find_gadgets(validate_gadgets, bad_bytes)
  if strategy != None:
    gadgets.set_strategy(strategy)
  gadget_scheduler = scheduler.Scheduler(gadgets, goal_resolver, file_handler, log_level, bad_bytes)
  return gadget_scheduler.get_chain()

def rop_to_shellcode(files, libraries, shellcode_address, log_level = logging.WARNING, validate_gadgets = False, bad_bytes = None):
  """Convience method to create a goal_resolver for a shellcode address goal then find a rop chain for it"""
  goal_list = [["shellcode", hex(shellcode_address)]]
  return rop(files, libraries, goal_list, log_level, validate_gadgets, bad_bytes)

