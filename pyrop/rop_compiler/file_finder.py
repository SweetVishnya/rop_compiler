import logging, collections
import gadget as ga, finder

class FileFinder(finder.Finder):
  """This class parses an previously dumped gadget list and recreates the gadgets"""

  def __init__(self, binary_file, gadget_file, base_address = None, level = logging.WARNING, parser_type = None):
    logging.basicConfig(format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    super(FileFinder, self).__init__(binary_file, base_address, level, parser_type)
    self.fd = open(gadget_file, "rb")

  def __del__(self):
    self.fd.close()

  def find_gadgets(self, dummy = False, bad_bytes = None):
    """Restores the gadgets from the saved gadget list"""
    gadget_list = ga.from_string(self.fd.read(), self.level, self.base_address, bad_bytes, finder.FILTER_FUNC)
    self.logger.debug("Found %d (%d LoadMem) gadgets", len([x for x in gadget_list.foreach()]), len([x for x in gadget_list.foreach_type(ga.LoadMem)]))
    return gadget_list

