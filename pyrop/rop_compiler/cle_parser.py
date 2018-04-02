import logging, collections, os
import file_parser
import cle, pyvex

class CleParser(file_parser.FileParser):
  """This class parses an executable file using cle"""

  def __init__(self, filename, base_address = None, level = logging.WARNING):
    super(CleParser, self).__init__(filename, base_address, level)
    if base_address is None:
      self.ld = cle.Loader(filename)
    else:
      self.ld = cle.Loader(filename, main_opts={'custom_base_addr': base_address})

  def iter_executable_segments(self):
    """Any iterator that only returns the executable sections in the ELF file"""
    for seg in self.ld.main_object.segments:
      if seg.is_executable:
        yield seg

  def get_segment_bytes_address(self, seg):
    """Returns a segments bytes and the address of the segment"""
    return ''.join(self.ld.memory.read_bytes(seg.vaddr, seg.memsize)), seg.vaddr

  def get_symbol_address(self, name, recurse_with_imp = True):
    """Returns the address for a symbol, or None if the symbol can't be found"""
    symbol = self.ld.main_object.get_symbol(name)
    if symbol != None:
      if symbol.rebased_addr == 0: # For some symbols, it doesn't look in the plt.  Fix that up here.
        return self.ld.main_object._plt[name]
      return symbol.rebased_addr
    return None

  def get_writable_memory(self):
    return self.ld.main_object.sections_map['.data'].vaddr

  def find_symbol_in_got(self, name):
    rel = next(self.ld.find_relevant_relocations(name), None)
    if rel is None:
      return None
    return rel.rebased_addr

  @property
  def pie(self):
    return self.ld.main_object.pic

  @property
  def arch(self):
    return self.ld.main_object.arch
