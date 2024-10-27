# @generated by PeggyGD __VERSION__.
extends Node
class_name __CLAZZ_NAME__

class Result extends RefCounted:
  var error:SyntaxError
  var value
  var expected

  func _init(value, error:SyntaxError = null, expected = null):
    self.value = value
    self.error = error
    self.expected = expected

class CacheEntry:
  var nextPos:int
  var result

  func _init(pos:int, result):
    self.nextPos = pos
    self.result = result

class SyntaxError extends RefCounted:
  var message:String
  var expected
  var found
  var location

  func _init(message:String, expected, found, location):
    self.message = message
    self.expected = expected
    self.found = found
    self.location = location

  func format(sources)->String:
    var str = "Error: " + message
    if location:
      var src = null
      for source in sources:
        if source == self.location.source:
          src = source.text.split('\n')
          break

      var s = location.start
      var offset_s = location.source.offset.call(s) if (location.source && (location.source.offset is Callable)) else s
      var loc = '%s: %d:%d' % [location.source, offset_s.line, offset_s.column]
      if src:
        var e = location.end
        var filler = "".rpad(offset_s.line.toString().length())
        var line = src[s.line - 1]
        var last = e.column if s.line == e.line else line.length() + 1
        var hatLen = (last - s.column) || 1
        str += "\n --> " + loc + "\n";
        str += filler + " |\n"
        str += offset_s.line + " | " + line + "\n"
        str += filler + " | " + "".rpad(s.column - 1)
        str += "".rpad(hatLen, "^")
      else:
        str += "\n at " + loc
    return str

  static func buildMessage(expected, found)->String:
    return "Expected " + describeExpected(expected) + " but " + describeFound(found) + " found."

  static func literalEscape(s: String)->String:
    return s\
      .replace("\\", "\\\\")\
      .replace('"',  '\\"')\
      .replace("\t", "\\t")\
      .replace("\n", "\\n")\
      .replace("\r", "\\r")

  static func classEscape(s: String)->String:
    return s\
        .replace("\\", "\\\\")\
        .replace("]", "\\]")\
        .replace("^", "\\^")\
        .replace("-", "\\-")\
        .replace("\t", "\\t")\
        .replace("\n", "\\n")\
        .replace("\r", "\\r")

  static func describeExpectation(expectation)->String:
    match expectation.type:
      'literal':
          return "\"" + literalEscape(expectation.text) + "\""
      'class':
          var escapedParts = expectation.parts.map(func(part): return classEscape(part[0]) + "-" + classEscape(part[1]) if part is Array else classEscape(part))
          return "[" + ("^" if expectation.inverted else "") + "".join(escapedParts) + "]"
      'any':
          return "any character"
      'end':
          return "end of input"
      'other':
          return expectation.description
    assert(false, 'invalid expectation type: %s' % expectation.type)
    return ''

  static func describeExpected(expected):
    var descriptions = expected.map(describeExpectation)
    descriptions.sort();
    # todo: remove duplicates
    #if descriptions.size > 0:
    #  var j=1
    #  for i in range(1, descriptions.size):
    #    if descriptions[i - 1] != descriptions[i]:
    #      descriptions[j] = descriptions[i]
    #      j += 1
    #  descriptions.length = j
    match descriptions.size():
      1:
        return descriptions[0]
      2:
        return descriptions[0] + " or " + descriptions[1]
      _:
        return ", ".join(descriptions.slice(0, -1))\
          + ", or "\
          + descriptions[descriptions.size() - 1]

  static func describeFound(found):
    return "\"" + literalEscape(found) + "\"" if found else "end of input"

class RegExp extends RefCounted:
  var r: RegEx

  func _init(pattern: String):
    r = RegEx.create_from_string(pattern)
    assert(r.is_valid())

  func test(s: String)->bool:
    return r.search(s) != null

##GLOBALS##

# ----------- Parser -------------------
const peg_FAILED := '$$FAILED$$'
var peg_source
var peg_error
var peg_startRuleFunctions
var peg_startRuleFunction
var options
var input:String
var peg_currPos:int
var peg_savedPos:int
var peg_posDetailsCache:Array
var peg_maxFailPos:int
var peg_maxFailExpected:Array
var peg_silentFails
var peg_resultsCache := {}

##TABLES##

func next()->String:
  if peg_currPos < input.length():
    return input[peg_currPos]
  return ''

func is_failed(s):
  return s is String and s == peg_FAILED

func text()->String:
  return input.substr(peg_savedPos, peg_currPos - peg_savedPos)

func offset()->int:
  return peg_savedPos

func range():
  return {
    source = peg_source,
    start = peg_savedPos,
    end = peg_currPos
  }

func location():
  return peg_computeLocation(peg_savedPos, peg_currPos)

func expected(description, location):
  location = location if location else peg_computeLocation(peg_savedPos, peg_currPos)
  assert(false, 'structural error')
  #throw peg_buildStructuredError(
  #[peg_otherExpectation(description)],
  #input.substring(peg_savedPos, peg_currPos),
  #location
  #);

func error(message, location):
  location = location if location else peg_computeLocation(peg_savedPos, peg_currPos)
  assert(false, 'simple error')
  #throw peg_buildSimpleError(message, location)

func peg_literalExpectation(text:String, ignoreCase:bool):
  return { type = "literal", text = text, ignoreCase = ignoreCase }

func peg_classExpectation(parts, inverted, ignoreCase):
  return { type = "class", parts = parts, inverted = inverted, ignoreCase = ignoreCase }

func peg_anyExpectation():
  return { type = "any" }

func peg_endExpectation():
  return { type = "end" }

func peg_otherExpectation(description):
  return { type = "other", description = description }

func peg_computePosDetails(pos):
  var details = peg_posDetailsCache[pos] if pos < peg_posDetailsCache.size() else null
  var p;

  if details:
    return details
  if pos >= peg_posDetailsCache.size():
    p = peg_posDetailsCache.size() - 1;
  else:
    p = pos - 1;
    while !peg_posDetailsCache[p]: p -= 1

  details = peg_posDetailsCache[p]
  details = {
    line= details.line,
    column= details.column
  }

  while (p < pos):
    if (input.unicode_at(p) == 10):
      details.line += 1
      details.column = 1
    else:
      details.column += 1
    p += 1
    if peg_posDetailsCache.size() <= pos:
      peg_posDetailsCache.resize(pos + 1)
    peg_posDetailsCache[pos] = details;
  return details;

func peg_computeLocation(startPos, endPos, offset: bool = false):
  var startPosDetails = peg_computePosDetails(startPos)
  var endPosDetails = peg_computePosDetails(endPos)

  var res = {
    source= peg_source,
    start= {
      offset= startPos,
      line= startPosDetails.line,
      column= startPosDetails.column
    },
    end= {
      offset= endPos,
      line= endPosDetails.line,
      column= endPosDetails.column
    }
  }
  if offset && peg_source && (peg_source.offset is Callable):
    res.start = peg_source.offset.call(res.start)
    res.end = peg_source.offset.call(res.end)
  return res

func peg_fail(expected):
  if (peg_currPos < peg_maxFailPos): return
  if (peg_currPos > peg_maxFailPos):
    peg_maxFailPos = peg_currPos
    peg_maxFailExpected = []
  peg_maxFailExpected.push_back(expected);

func peg_buildSimpleError(message, location)->SyntaxError:
  return SyntaxError.new(message, null, null, location)

func peg_buildStructuredError(expected, found, location)->SyntaxError:
  return SyntaxError.new(\
    SyntaxError.buildMessage(expected, found), \
    expected, \
    found, \
    location)

##EXPRESSIONS##

func parse(input: String, options = {})->Result:
  self.options = options
  self.input = input
  peg_currPos = options.get('peg_currPos', 0)
  peg_savedPos = peg_currPos
  peg_posDetailsCache = [{ line = 1, column = 1 }]
  peg_maxFailPos = peg_currPos
  peg_maxFailExpected = options.get('peg_maxFailExpected', [])
  peg_silentFails = options.get('peg_silentFails', 0)
  peg_source = options.get('grammarSource', '')
  peg_resultsCache.clear()
##START_RULES##

  var peg_result = peg_startRuleFunction.call();

  #if options.has('peg_library'):
    #return {
      #"peg_result": peg_result,
      #"peg_currPos": peg_currPos,
      #"peg_FAILED": peg_FAILED,
      #"peg_maxFailExpected": peg_maxFailExpected,
      #"peg_maxFailPos": peg_maxFailPos,
    #}

  if (!is_failed(peg_result) && peg_currPos == input.length()):
    return Result.new(peg_result)

  if (!is_failed(peg_result) && peg_currPos < input.length()):
    peg_fail(peg_endExpectation());

  peg_error = peg_buildStructuredError(
    peg_maxFailExpected,
    input[peg_maxFailPos] if peg_maxFailPos < input.length() else null,
    peg_computeLocation(peg_maxFailPos, peg_maxFailPos + 1) if peg_maxFailPos < input.length() else peg_computeLocation(peg_maxFailPos, peg_maxFailPos)
  );
  return Result.new(peg_result, peg_error, peg_maxFailExpected)
