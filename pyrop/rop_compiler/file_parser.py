import logging
import factories

class FileParser(object):
  """This class parses an executable file to obtain information about it"""

  def __init__(self, filename, base_address = None, level = logging.WARNING):
    logging.basicConfig(format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.setLevel(level)
    self.level = level

    self.base_address = base_address
    self.filename = filename

  def iter_executable_segments(self):
    """Any iterator that only returns the executable sections in the ELF file"""
    raise RuntimeError("Not Implemented")

  def get_segment_bytes_address(self, seg):
    """Returns a segments bytes and the address of the segment"""
    raise RuntimeError("Not Implemented")

  def get_symbol_address(self, name):
    """Returns the address for a symbol, or None if the symbol can't be found"""
    raise RuntimeError("Not Implemented")

  def get_writable_memory(self):
    """Returns a writable area of memory"""
    raise RuntimeError("Not Implemented")

  def find_symbol_in_got(self, name):
    """Find the address of a symbol in the GOT"""
    raise RuntimeError("Not Implemented")

  def get_symbols_address(self, names):
    """This function tries to resolve a series of symbols"""
    addresses = {}
    for name in names:
      try:
        address = self.get_symbol_address(name)
      except:
        address = None
      addresses[name] = address
    return addresses

  @property
  def pie(self):
    """Whether the current binary is position-independent"""
    raise RuntimeError("Not Implemented")

if __name__ == "__main__":
  import argparse

  parser = argparse.ArgumentParser(description="Resolve a symbol from the supplied binary")
  parser.add_argument('-parser_type', type=str, default="cle", help='The type of file parser (cle, pyelf, radare)')
  parser.add_argument('-base_address', type=str, default="0", help='The address the file is loaded at (in hex). Only needed'
    + ' for PIE/PIC binaries.  When creating a reusable gadgets file, do not specify')
  parser.add_argument('-v', required=False, action='store_true', help='Verbose mode')
  parser.add_argument('target', type=str, help='The file (executable/library) to find symbols in')
  parser.add_argument('symbol', nargs="*", type=str, help='The symbol to resolve')
  args = parser.parse_args()

  parser_type = factories.get_parser_from_name(args.parser_type)
  logging_level = logging.DEBUG if args.v else logging.WARNING
  parser = parser_type(args.target, int(args.base_address, 16), logging_level)
  for symbol in args.symbol:
    address = parser.get_symbol_address(symbol)
    if address != None: address = hex(address)
    print symbol, address
