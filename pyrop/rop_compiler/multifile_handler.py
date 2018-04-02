import logging
import factories

class MultifileHandler(object):
  """This class parses a set of executable file to obtain information about it"""

  def __init__(self, files, libraries, level = logging.WARNING, parser_type = None):
    logging.basicConfig(format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.setLevel(level)
    self.level = level

    self.files = []
    for binary_file, gadget_file, base_address in files:
      if gadget_file != None:
        finder = factories.get_finder_from_name("file")(binary_file, gadget_file, base_address, level, parser_type)
      else:
        finder = factories.get_finder_from_name("mem")(binary_file, base_address, level, parser_type)
      self.files.append(finder)

    parser_class = factories.get_parser_from_name(parser_type)

    self.libraries = {}
    for lib in libraries:
      self.libraries[lib] = parser_class(lib, 0, level)

  def get_symbol_address(self, symbol_name):
    """Returns the address for a symbol, or None if the symbol can't be found"""
    for finder in self.files:
      symbol_address = finder.parser.get_symbol_address(symbol_name)
      if symbol_address != None:
        return symbol_address
    return None

  def get_symbols_address(self, names):
    addresses = {}
    for name in names:
      addresses[name] = self.get_symbol_address(name)
    return addresses

  def get_writable_memory(self):
    """Returns an area of writable memory that we know the address (i.e. one of the ones specified in the files list)"""
    for finder in self.files:
      addr = finder.parser.get_writable_memory()
      if addr != None:
        return addr
    raise RuntimeError("Couldn't find a .data section when looking for writable memory")

  def find_gadgets(self, validate_gadgets = False, bad_bytes = None):
    """Finds gadgets in the specified file"""
    all_gadget_list = None
    for finder in self.files:
      new_gadget_list = finder.find_gadgets(validate_gadgets, bad_bytes)
      if all_gadget_list == None:
        all_gadget_list = new_gadget_list
      else:
        all_gadget_list.copy_gadgets(new_gadget_list)
    return all_gadget_list

  def resolve_symbol_from_got(self, base_name, target_name):
    """Gets the offset from one symbol to another in a library, and the address of the symbol in the GOT.  This info can be
      used to determine the target symbol's address if one can read the given symbol in the GOT."""

    # First, get the address of the base in the GOT
    main_binary = self.files[0].parser
    symbol_in_got = main_binary.find_symbol_in_got(base_name)

    # Now, get the offset from the base to the target in libc
    base_in_libc = target_in_libc = None
    for name, parser in self.libraries.items():
      base_in_libc = parser.get_symbol_address(base_name)
      target_in_libc = parser.get_symbol_address(target_name)
      if base_in_libc != None and target_in_libc != None:
        break

    if base_in_libc == None and target_in_libc == None:
      return (None, None)

    return symbol_in_got, (target_in_libc - base_in_libc)

  @property
  def main_arch(self):
    """Gets main binary arch"""
    return self.files[0].arch

if __name__ == "__main__":
  import argparse

  parser = argparse.ArgumentParser(description="Resolve a symbol from the supplied binary")
  parser.add_argument('-parser_type', type=str, default="cle", help='The type of file parser (cle, pyelf, radare)')
  parser.add_argument('-base_address', type=str, default="", help='The address the file is loaded at (in hex). Only needed'
    + ' for PIE/PIC binaries.  When creating a reusable gadgets file, do not specify')
  parser.add_argument('-v', required=False, action='store_true', help='Verbose mode')
  parser.add_argument('target', type=str, help='The file (executable/library) to find symbols in')
  parser.add_argument('symbol', nargs="*", type=str, help='The symbol to resolve')
  args = parser.parse_args()

  parser_type = factories.get_parser_from_name(args.parser_type)
  logging_level = logging.DEBUG if args.v else logging.WARNING
  parser = parser_type(args.target, int(args.base_address, 16) if args.base_address else None, logging_level)
  for symbol in args.symbol:
    address = parser.get_symbol_address(symbol)
    if address != None: address = hex(address)
    print symbol, address

