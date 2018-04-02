import logging, collections
import classifier as cl, gadget as ga, finder, factories, utils

class MemoryFinder(finder.Finder):
  """This class parses a file to obtain any gadgets inside their executable sections"""

  def find_gadgets(self, validate = False, bad_bytes = None):
    """Finds gadgets in the specified file"""
    gadget_list = ga.GadgetList(log_level = self.level, bad_bytes = bad_bytes)
    for segment in self.parser.iter_executable_segments():
      self.get_gadgets_for_segment(segment, gadget_list, validate, bad_bytes)
    self.logger.debug("Found %d gadgets in %s", len([x for x in gadget_list.foreach()]), self.name)
    return gadget_list

  def get_gadgets_for_segment(self, segment, gadget_list, validate, bad_bytes):
    """Iteratively step through an executable section looking for gadgets at each address"""
    data, seg_address = self.parser.get_segment_bytes_address(segment)
    if self.base_address is None and self.parser.pie:
      self.logger.warning("No base address given for library or PIE executable.  Addresses may be wrong")

    classifier = cl.GadgetClassifier(self.arch, validate, log_level = self.level)
    for i in range(0, len(data), self.arch.instruction_alignment):
      address = seg_address + i
      if bad_bytes != None and utils.address_contains_bad_byte(address, bad_bytes, self.arch):
        continue
      end = i + self.MAX_GADGET_SIZE[self.arch.name]
      code = data[i:end]
      gadgets = classifier.create_gadgets_from_instructions(code, address)
      if finder.FILTER_FUNC != None:
        gadgets = finder.FILTER_FUNC(gadgets)
      gadget_list.add_gadgets(gadgets)
