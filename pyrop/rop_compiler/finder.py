import logging, collections
import factories

"""A function to filter gadgets on when they are first created"""
FILTER_FUNC = None

class Finder(object):
  """This class parses a file to obtain any gadgets inside their executable sections"""

  """The maximum size in bytes of a gadget to look for"""
  MAX_GADGET_SIZE = { "X86" : 10, 'AMD64' : 10, 'MIPS64' : 36, 'MIPS32' : 36, 'PPC32' : 32, 'PPC64' : 32, 'ARM' : 20,
    'ARMEL' : 20 }

  def __init__(self, name, base_address = None, level = logging.WARNING, parser_type = None):
    logging.basicConfig(format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    self.logger = logging.getLogger(self.__class__.__name__)
    self.logger.setLevel(level)
    self.level = level

    self.base_address = base_address
    self.name = name

    self.parser = factories.get_parser_from_name(parser_type)(name, base_address, level)
    self.arch = self.parser.arch

  def find_gadgets(self, validate = False):
    """Finds gadgets in the specified file"""
    raise RuntimeError("Not Implemented")

if __name__ == "__main__":
  import argparse

  parser = argparse.ArgumentParser(description="Run the gadget locator on the supplied binary")
  parser.add_argument('filename', type=str, default=None, help='The file (executable/library) to load gadgets from')
  parser.add_argument('-o', type=str, default=None, help='File to write the gadgets to')
  parser.add_argument('-parser_type', type=str, default="cle", help='The type of file parser (cle, pyelf, radare)')
  parser.add_argument('-v', required=False, action='store_true', help='Verbose mode')
  parser.add_argument('-validate', required=False, action='store_true', help='Validate gadgets with z3')
  args = parser.parse_args()

  finder_type = factories.get_finder_from_name("mem")
  logging_level = logging.DEBUG if args.v else logging.WARNING
  parser = factories.get_parser_from_name(args.parser_type)(args.filename, 0, logging_level)
  finder = finder_type(args.filename, 0 if parser.pie else None, logging_level, args.parser_type)
  gadget_list = finder.find_gadgets(args.validate)

  if args.o == None:
    for gadget in gadget_list.foreach():
      print gadget
  else:
    fd = open(args.o, "w")
    fd.write(gadget_list.to_string())
    fd.close()

